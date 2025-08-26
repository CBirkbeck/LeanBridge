#!/usr/bin/env python

# For now, we just pull a dump of the LMFDB's database, write to the knowls/ folder, and record the update.
# Eventually we may want something fancier.

import os, sys, re
from pathlib import Path
from collections import defaultdict
import networkx as nx

def clean_content(kwl):
    # We should deal with things like markdown lists, jinja macros (especially KNOWL)
    content = kwl['content']
    # For now, we just add label and dependencies
    return f"\\subsection{{{kwl['title']}}}\n\\begin{{definition}}\\label{{{kwl['id']}}}\n\\uses{{{','.join(kwl['links'])}}}\n{kwl['content']}\n\\end{{definition}}\n\n\n"

def update_knowls(path_to_lmfdb=None, cats=["nf", "ec", "cmf"], delete_old=False):
    if path_to_lmfdb is None:
        path_to_lmfdb = os.path.expanduser("~/lmfdb")
    sys.path.append(path_to_lmfdb)
    from lmfdb.knowledge.knowl import knowldb
    knowldir = Path("knowls")

    all_knowls = knowldb.get_all_knowls(fields=['id', 'cat', 'content', 'title', 'links', 'defines'], types=[0])
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
    # We've manually removed some edges to prevent cycles
    omit_edges = set([
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
        keep = keep.union(nextkeep)
        newkeep = copy(nextkeep)
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

    for rec in all_knowls:
        kid = rec["id"]
        cat = kid.split(".")[0]
        assert cat == rec["cat"]
        with open(knowldir / cat / rec["id"], "w") as F:
            _ = F.write(clean_content(rec))


    # Write to a file that can be manually edited
    cat_names = {
        "nf": "Number fields",
        "ec": "Elliptic curves",
        "cmf": "Modular forms",
        # Add more categories here
    }
    with open("auto_content.tex", "w") as F:
        # We should impose some kind of reasonable order, but that's for later
        _ = F.write("\n\\section{{Background}}\n")
        for kwl in all_knowls:
            if kwl["cat"] not in cats:
                _ = F.write(f"\\input{{knowls/{kwl['cat']}/{kwl['id']}}}\n")
        for cat in cats:
            _ = F.write(f"\n\n\\section{{{cat_names[cat]}}}\n")
            for kwl in all_knowls:
                if kwl["cat"] == cat:
                    _ = F.write(f"\\input{{knowls/{kwl['cat']}/{kwl['id']}}}\n")
