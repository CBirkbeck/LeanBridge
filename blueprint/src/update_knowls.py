#!/usr/bin/env python

import os, sys, re
from pathlib import Path
from collections import defaultdict
import networkx as nx
from psycopg2 import connect
from psycopg2.sql import SQL, Identifier

KNOWL_RE = re.compile(r"""(\{\{\s*KNOWL(_INC)?\s*\(\s*['"]([a-z0-9._-]+)['"](?:\s*,\s*(?:title\s*=\s*)?("[^"]+"|'[^']+'))?\s*\)\s*\}\})""")
CURLY_RE = re.compile(r"\{\{([^\}]+)\}\}")
ITALIC_RE = re.compile(r" _([^_]+)_")
EMPH_RE = re.compile(r"\*\*([^\*]+)\*\*")
xdef = r"(?:arxiv|doi|groupprops|href|mathworld|mr|nlab|stacks|wikidata|wikipedia|zbl)"
DEFINES_RE = re.compile(r"""\{\{\s*DEFINES\s*\(\s*(?:'([^']+)'|"([^"]+)")\s*(?:,\s*(?:clarification_kid\s*=)?(?:'([^']+)'|"([^"]+)"\s*))?(?:,\s*%s+=(?:'[^']+'|"[^"]+"\s*))*(?:,\s*mathlib=(?:'([^']+)'|"([^"]+)"\s*))*(?:,\s*%s+=(?:'[^']+'|"[^"]+"\s*))*\)\s*\}\}""" % (xdef, xdef))
DELIM_RE = re.compile(r"(\\\[|\\\]|\\\(|\\\)|\$\$|\$)")
COMMENT_RE = re.compile(r"\{#[^#]+#\}")
CITE_UNDERSCORE_RE = re.compile(r"\\cite\{[^\}]+\}")
ITEMIZE_RE = re.compile(r"^\s*[\-\*]")
SUBACK_RE = re.compile(r"_(\\\w+(?:\{[^\}]+\})?)")
NOBRACE_RE = re.compile(r"\\(overline|mathbb|widehat|hat)\s*(\w+)")
LINK_RE = re.compile(r"""<a\s+href=['"]([^'"]+)['"]>([^<]+)</a>""")
# url_for('abstract.index') -> https://www.lmfdb.org/Groups/Abstract
# url_for('modcurve.index_Q',level='11',family='Xsp') -> https://beta.lmfdb.org/ModularCurves/Q?level=11&family=Xsp

def strip_macros(knowls):
    """
    INPUT:
    - knowls -- a dictionary with keys the knowl ids and values the knowl records.
    """
    doinc = set()
    def subber(match):
        if match.group(2): # KNOWL_INC; deal with this below
            return match.group(1)
        kid = match.group(3)
        if match.group(4):
            title = match.group(4)[1:-1]
        elif kid in knowls and "title" in knowls[kid]:
            title = knowls[kid]["title"]
        else:
            return ""
        # Need to mask underscores for the replacement _ with \_ below
        kid = kid.replace("_", "~U~")
        return f"\\hyperref[{kid}]{{{title}}}"
    def cite_subber(match):
        return match.group(0).replace(r"\_", "_")
    def link_subber(match):
        url = match.group(1).replace(r"\_", "_")
        text = match.group(2)
        return fr"\href{{{url}}}{{{text}}}"
    replacements = [
        (r"\\times", r"\times"),
        ("&check;", r"\checkmark"),
        ("&#1064;", r"\Sha"),
        ("&ouml;", r'\"o'),
        ("&eacute", r"\'e"),
        ("ę", r"\k{e}"),
        ("Č", r"\v{C}"),
        ("č", r"\v{c}"),
        ("−", "-"), # Replace weird unicode minus with a normal minus
    ]
    for kid, rec in knowls.items():
        content = rec["content"]
        for old, new in replacements:
            content = content.replace(old, new)
        rec["title"] = rec["title"].replace("&#1064;", r"$\Sha$")
        content = KNOWL_RE.sub(subber, content)

        # Remove comments
        content = COMMENT_RE.sub("", content)

        leanmissing = set() # Use a set so that we can easily update from inside the def_subber function
        if EMPH_RE.search(content):
            # **defined** does not include a mathlib link
            leanmissing.add(True)
        # Change **defined** to \textbf{defined}
        content = EMPH_RE.sub(r"\\textbf{\1}", content)
        def def_subber(match):
            defstr = match.group(1) or match.group(2)
            kidstr = match.group(3) or match.group(4)
            mathlib = match.group(5) or match.group(6)
            if not kidstr and not mathlib:
                leanmissing.add(True)
            return r"\textbf{%s}" % defstr
        content = DEFINES_RE.sub(def_subber, content)
        if not leanmissing:
            content = "\\leanok\n" + content

        # Underscores that are not in mathmode
        content = ITALIC_RE.sub(r" \\textit{\1}", content)
        # Other underscores that are not in mathmode
        delim_split = DELIM_RE.split(content)
        for i in range(0, len(delim_split), 4): # Every fourth entry is outside mathmode
            delim_split[i] = delim_split[i].replace("_", r"\_").replace(r"\Sha", r"$\Sha$")
        content = "".join(delim_split)
        # Switch back from \_ to _ inside cite commands
        content = CITE_UNDERSCORE_RE.sub(cite_subber, content)
        # Put underscores in knowl ids and hyperrefs back in
        content = content.replace("~U~", "_")

        # Wrap subscripts in curly braces
        content = SUBACK_RE.sub(r"_{\1}", content)
        # Wrap arguments in curly braces
        content = NOBRACE_RE.sub(r"\\\1{\2}", content)
        # Fix links
        content = LINK_RE.sub(link_subber, content)

        # Turn markdown lists into itemize
        lines = content.split("\n")
        in_itemize = False
        i = 0
        while i < len(lines):
            line = lines[i]
            if ITEMIZE_RE.match(line):
                if not in_itemize:
                    lines[i:i] = [r"\begin{itemize}"]
                    i += 1
                    in_itemize = True
                lines[i] = ITEMIZE_RE.sub(r"\\item ", line)
            else:
                if in_itemize:
                    lines[i:i] = [r"\end{itemize}"]
                    i += 1
                    in_itemize = False
            i += 1
        if in_itemize:
            lines.append(r"\end{itemize}")
        content = "\n".join(lines)

        # Prepare for knowl inclusions below
        if "KNOWL_INC" in content:
            doinc.add(kid)
        rec["content"] = content

    # Special cases
    def special_sub(kid, old, new):
        knowls[kid]["content"] = knowls[kid]["content"].replace(old, new)

    # Now deal with KNOWL_INC
    def subber_inc(match):
        assert match.group(2)
        kid = match.group(3)
        return knowls[kid]["content"]
    while doinc:
        redo = set()
        for kid in doinc:
            rec = knowls[kid]
            rec["content"] = KNOWL_RE.sub(subber_inc, rec["content"])
            if "KNOWL_INC" in rec["content"]:
                redo.add(kid)
        doinc = redo

def clean_content(kwl):
    # We should deal with things like markdown lists, jinja macros (especially KNOWL)
    content = kwl['content']
    safe_id = kwl['id'].replace("_", r"\_")
    # For now, we just add label and dependencies
    return f"\\subsection{{\\href{{https://beta.lmfdb.org/knowledge/show/{kwl['id']}}}{{{kwl['title']}}}}}\n\\begin{{definition}}\\label{{{kwl['id']}}}\n\\uses{{{','.join(kwl['links'])}}}\n{content}\n\\end{{definition}}\n\n\n"

def update_knowls(cats=["nf", "ec", "cmf"], delete_old=False):
    knowldir = Path("knowls")

    omit_verts = set([
        "field.about",
        "group.about",
        "mf.about",
        "motives.about",
        "repn.about",
        "varieties.about",
        "av.fq.abvar.data",
        "character.dirichlet.data",
        "character.dirichlet.orbit_data",
        "clusterpicture.data",
        "gg.conjugacy_classes.data",
        "gg.character_table.data",
        "gl2.subgroup_data",
        "group.small.data",
        "gsp4.subgroup_data",
        "lattice.data",
        "lf.algebra.data",
        "lf.field.data",
        "nf.field.data",
        "nf.galois_group.data",
        "nf.galois_group.gmodule",
        "st_group.data",
        "dq.charmodl.extent",
        "dq.ecnf.extent",
        "dq.hecke_algebras.extent",
        "dq.modlmf.extent",
        "dq.rep_galois_modl.extent",
        "rcs.ack.meetings",
        "rcs.cande.ec",
        "rcs.cande.ec.q",
        "rcs.cande.lattice",
        "rcs.cande.nf",
        "lmfdb.object_information",
        "lmfdb.external_definitions",
        "intro.api",
        "test.knowlparam",
        "nf.elkies",
        "nf.field.missing",
        "nf.field.link",
        "nf.galois_group.name", # Maybe relevant but includes a Python function
        "ec.isogenygraph.legend",
        "doc.secret",
        "doc.news.in_the_news",
        "doc.knowl",
        "doc.knowl.guidelines",
        "doc.macros",
        "sage.test", # Huh, I didn't know we had this
        "test.text",
    ])

    conn = connect(dbname="lmfdb", port=5432, user="lmfdb", password="lmfdb", host="devmirror.lmfdb.xyz")
    fields = ['id', 'cat', 'content', 'title', 'links', 'defines']
    selecter = SQL("SELECT DISTINCT ON (id) {0} FROM kwl_knowls WHERE status >= 0 AND type = 0 ORDER BY id, timestamp DESC").format(SQL(", ").join(map(Identifier, fields)))
    cur = conn.cursor()
    cur.execute(selecter)
    all_knowls = [dict(zip(fields, res)) for res in cur if res[0] not in omit_verts]
    old_knowls = set()
    for cat in knowldir.iterdir():
        for path in cat.iterdir():
            old_knowls.add(path.name)
    deleted_knowls = old_knowls.difference(set(rec["id"] for rec in all_knowls))
    if deleted_knowls:
        print("Warning: the following knowls have been deleted in the LMFDB:\n" + ",".join(sorted(deleted_knowls)))
        if delete_old:
            for kid in deleted_knowls:
                cat = kid.split(".")[0]
                os.remove(knowldir / cat / kid)

    # Collect definitions in a file, and only keep knowls that define something
    by_id = {rec["id"]: rec for rec in all_knowls}
    print(f"{len(by_id)} knowls before filtering")
    with open("definitions.txt", "w") as F:
        by_def = defaultdict(list)
        for kid in sorted(by_id):
            defines = by_id[kid]["defines"]
            if defines:
                _ = F.write(kid + ":\n")
                for term in defines:
                    _ = F.write("    * " + term + "\n")
                    by_def[term].append(kid)
            else:
                del by_id[kid]
        _ = F.write("\n" * 8)
        for term in sorted(by_def, key=lambda term:term.lower()):
            _ = F.write(term + ":\n")
            for kid in by_def[term]:
                _ = F.write("    * " + kid + "\n")
    print(f"{len(by_id)} knowls define something")


    # Now we trim to only things that are dependencies of knowls in the specified categories, and build a networkx DiGraph for the next step
    omit_edges = set([
        # We've manually removed some edges to prevent cycles
        ("ec.q.lmfdb_label", "ec.q.cremona_label"),
        ("ec.q.cremona_label", "ec.q.lmfdb_label"),
        ("ec.q.optimal", "ec.q.cremona_label"),
        ("nf.defining_polynomial", "nf.generator"),
        ("cmf.atkin-lehner", "cmf.fricke"),
        ("st_group.definition", "st_group.degree"),
        ("st_group.definition", "st_group.weight"),
        ("gl2.cartan", "gl2.split_cartan"),
        ("gl2.cartan", "gl2.nonsplit_cartan"),
        ("av.fq.weil_polynomial", "av.fq.l-polynomial"),
        ("nf.weil_polynomial", "av.fq.weil_polynomial"),
        ("av.simple", "av.decomposition"),
        ("nf.narrow_class_group", "nf.narrow_class_number"),
        ("cmf.twist", "cmf.twist_multiplicity"),
        ("cmf.twist", "cmf.minimal_twist"),
        ("cmf.inner_twist", "cmf.inner_twist_count"),
        ("ec.q.szpiro_ratio", "ec.q.abc_quality"),
        ("ec.q.abc_quality", "ec.q.szpiro_ratio"),
        ("nf.unit_group", "nf.fundamental_units"),
        ("nf.unit_group", "nf.rank"),
        ("nf.unit_group", "nf.regulator"),
        ("ec.padic_tate_module", "ec.galois_rep"),
        ("ec.galois_rep", "gl2.genus"),
        ("modcurve.xn", "modcurve"),
        ("g2c.aut_grp", "g2c.geom_aut_grp"),
        ("g2c.discriminant", "g2c.minimal_equation"),
        ("g2c.minimal_equation", "g2c.simple_equation"),
        ("gl2.open", "gl2.level"),
        ("av.tate_module", "av.galois_rep"),
        ("ec.mordell_weil_group", "ec.bsdconjecture"),
        ("ec.mordell_weil_group", "ec.mordell_weil_theorem"),
        ("ec.mordell_weil_group", "ec.rank"),
        ("ec.mordell_weil_group", "ec.torsion_order"),
        ("ec.mordell_weil_group", "ec.torsion_subgroup"),
        ("ec.canonical_height", "ec.regulator"),
        ("ec.analytic_sha_order", "ec.bsdconjecture"),
        ("ec.regulator", "ec.bsdconjecture"),
        ("nf.place", "nf.padic_completion"),
        ("nf.padic_completion", "nf.place"),
        ("ec.global_minimal_model", "ec.obstruction_class"),
        ("ec.global_minimal_model", "ec.semi_global_minimal_model"),
        ("ec.semi_global_minimal_model", "ec.global_minimal_model"),
        ("cmf.self_twist", "cmf.rm_form"),
        ("cmf.self_twist", "cmf.cm_form"),
        ("mf.ellitpic.self_twist", "cmf.cm_form"),
        ("lf.local_field", "lf.residue_field"),
        ("lf.local_field", "lf.padic_field"),
        ("nf.discriminant", "nf.ramified_primes"),
        ("nf.ramified_primes", "nf.discriminant"),
        ("artin", "artin.number_field"),
        ("cmf.space", "cmf.subspaces"),
        ("ec", "ec.weierstrass_coeffs"),
        ("ec.endomorphism_ring", "ec.complex_multiplication"),
        ("ec.isomorphism", "ec.weierstrass_isomorphism"),
        ("ec.isomorphism", "ec.weierstrass_coeffs"),
        ("ec.endomorphism", "ec.endomorphism_ring"),
        ("ec.endomorphism_ring", "ec.geom_endomorphism_ring"),
        ("ec.discriminant", "ec.q.minimal_weierstrass_equation"),
        ("ec.weierstrass_coeffs", "ec.discriminant"),
        ("ec.q.minimal_weierstrass_equation", "ec.q.discriminant"),
        ("ec.weierstrass_coeffs", "ec.weierstrass_isomorphism"),
        ("ec.isogeny", "ec.isogeny_class"),
        ("ag.endomorphism_ring", "ag.geom_endomorphism_ring"),
        ("av.isogeny", "av.isogeny_class"),
        ("ag.base_change", "ag.minimal_field"),
        ("ag.base_change", "ag.base_field"),
        ("ag.affine_space", "ag.dimension"),
        ("ag.projective_space", "ag.dimension"),
        ("cmf.q-expansion", "cmf.embedding"),
        ("cmf.galois_conjugate", "cmf.galois_orbit"),
        ("cmf.galois_conjugate", "cmf.coefficient_field"),
        ("cmf.galois_conjugate", "cmf.dimension"),
        ("cmf.hecke_operator", "cmf.q-expansion"),
        ("cmf.hecke_operator", "cmf.newform"),
        ("cmf.hecke_operator", "cmf.newspace"),
        ("cmf.newspace", "cmf.newform"),
        ("cmf.eisenstein_newspace", "cmf.eisenstein_newform"),
        ("lfunction", "lfunction.conductor"),
        ("lfunction", "lfunction.critical_line"),
        ("lfunction", "lfunction.critical_strip"),
        ("lfunction", "lfunction.rh"),
        ("lfunction", "lfunction.zeros"),
        ("lfunction", "lfunction.selberg_class.axioms"),
        ("lfunction", "lfunction.selbergdata"),
        ("lfunction", "lfunction.degree"),
        ("lfunction", "lfunction.spectral_parameters"),
        ("lfunction", "lfunction.root_number"),
        ("lfunction.conductor", "lfunction.dirichlet"),
        ("lfunction.functional_equation", "lfunction.selberg_class"),
        ("lfunction.functional_equation", "lfunction.selberg_class.axioms"),
        ("lfunction.functional_equation", "lfunction.sign"),
        ("lfunction.sign", "lfunction.selbergdata"),
        ("lfunction.central_point", "lfunction.normalization"),
        ("lfunction.central_point", "lfunction.motivic_weight"),
        ("lfunction.critical_line", "lfunction.normalization"),
        ("lfunction.degree", "lfunction.selbergdata"),
        ("lfunction.functional_equation", "lfunction.motivic_weight"),
        ("lfunction.functional_equation", "lfunction.selbergdata"),
        ("lfunction.functional_equation", "lfunction.signature"),
        ("lfunction.conductor", "lfunction.selbergdata"),
        ("lfunction.normalization", "lfunction.central_value"),
        ("lfunction.euler_product", "lfunction.conductor"), # circular
        ("lfunction.euler_product", "lfunction.degree"), # circular
        ("lfunction.functional_equation", "lfunction"), # circular
        ("lfunction.euler_product", "lfunction"), # circular
        ("lfunction.functional_equation", "lfunction.central_point"),
        ("lfunction.functional_equation", "lfunction.conductor"), # circular
        ("lfunction.functional_equation", "lfunction.degree"), # circular
        ("lfunction.functional_equation", "lfunction.spectral_parameters"),
        ("lfunction.gamma_factor", "lfunction.functional_equation"),
        ("cmf", "cmf.weight"), # circular
        ("cmf", "cmf.level"), # circular
        ("nf.degree", "nf"),
        ("character.dirichlet.principal", "character.dirichlet.order"),
        ("character.dirichlet", "character.dirichlet.conductor"),
        ("character.dirichlet", "character.dirichlet.primitive"),
        ("character.dirichlet.induce", "character.dirichlet.primitive"),
    ])
    edges = []
    kid_to_num = {}
    num_to_kid = {}
    by_source = defaultdict(list)
    by_target = defaultdict(list)
    next_num = 0
    keep = newkeep = set(rec["id"] for rec in by_id.values() if cats is None or rec["cat"] in cats)
    while newkeep:
        nextkeep = set()
        for kid in newkeep:
            if kid not in kid_to_num:
                kid_to_num[kid] = next_num
                num_to_kid[next_num] = kid
                next_num += 1
            source = kid_to_num[kid]
            by_id[kid]["links"] = [link for link in by_id[kid]["links"] if link in by_id and (kid, link) not in omit_edges] # link might be a top or bottom knowl, or not define anything...
            for link in by_id[kid]["links"]:
                if link not in kid_to_num:
                    kid_to_num[link] = next_num
                    num_to_kid[next_num] = link
                    next_num += 1
                if link not in keep:
                    nextkeep.add(link)
                edges.append((source, kid_to_num[link]))
                by_source[kid].append(link)
                by_target[link].append(kid)
        keep = keep.union(nextkeep)
        newkeep = copy(nextkeep)
    all_by_id = {rec["id"]: rec for rec in all_knowls}
    by_id = {rec["id"]: rec for rec in all_knowls if rec["id"] in keep}

    # Detect cycles
    G = nx.DiGraph(edges)
    cycles = list(nx.simple_cycles(G))
    if cycles:
        print(f"Warning: {len(cycles)} cycles detected and written to cycles.txt")
        with open("cycles.txt", "w") as F:
            for cyc in cycles:
                _ = F.write(" -> ".join(num_to_kid[vid] for vid in cyc + [cyc[0]]) + "\n")
    else:
        print("No cycles found")
    with open("edges.txt", "w") as F:
        _ = F.write("a:B where a is included because it is referenced by all b in B\n\n")
        for target in sorted(by_target):
            sources = sorted(by_target[target])
            _ = F.write(f"{target}: {', '.join(sources)}\n")

        _ = F.write("\n\n\n\n\nb:A where b references all a in B\n\n")
        for source in sorted(by_source):
            targets = sorted(by_source[source])
            _ = F.write(f"{source}: {', '.join(targets)}\n")

    strip_macros(all_by_id)
    for rec in all_by_id.values():
        kid = rec["id"]
        cat = kid.split(".")[0]
        assert cat == rec["cat"]
        with open(knowldir / cat / rec["id"], "w") as F:
            _ = F.write(clean_content(rec))

    skip = set([ # Temporarily skip these...
        #"character.dirichlet.jacobi_symbol",
    ])
    # Write to autogenerated files that are included into manually edited chapters
    cat_names = {
        None: "background",
        "nf": "number_fields",
        "ec": "elliptic_curves",
        "cmf": "modular_forms",
        # Add more categories here
    }
    assert all(cat in cat_names for cat in cats)
    for (cat, fname) in cat_names.items():
        with open(f"auto_{fname}.tex", "w") as F:
            # We should impose some kind of reasonable order, but that's for later
            # auto_knowls = sorted(by_id.values(), key=lambda rec: rec["id"])
            for kwl in by_id.values():
                if (cat is None and kwl["cat"] not in cats or cat is not None and kwl["cat"] == cat) and kwl["id"] not in skip:
                    _ = F.write(f"\\input{{knowls/{kwl['cat']}/{kwl['id']}}}\n")
