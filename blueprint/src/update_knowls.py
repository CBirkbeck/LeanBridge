#!/usr/bin/env python

# For now, we just pull a dump of the LMFDB's database, write to the knowls/ folder, and record the update.
# Eventually we may want something fancier.

import os, sys, re
from pathlib import Path
from collections import defaultdict

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

    cur_knowls = knowldb.get_all_knowls(fields=['id', 'cat', 'content', 'title', 'links', 'defines'], types=[0])
    old_knowls = set()
    for cat in knowldir.iterdir():
        for path in cat.iterdir():
            old_knowls.add(path.name)
    deleted_knowls = old_knowls.difference(set(rec["id"] for rec in cur_knowls))
    if deleted_knowls:
        print("Warning: the following knowls have been deleted in the LMFDB:\n" + ",".join(sorted(deleted_knowls)))
        if delete_old:
            for kid in deleted_knowls:
                cat = kid.split(".")[0]
                os.remove(knowldir / cat / kid)
    for rec in cur_knowls:
        kid = rec["id"]
        cat = kid.split(".")[0]
        assert cat == rec["cat"]
        with open(knowldir / cat / rec["id"], "w") as F:
            _ = F.write(clean_content(rec))
    # Now we trim to only things that are dependencies of knowls in the specified categories
    by_id = {rec["id"]: rec for rec in cur_knowls}
    if cats is not None:
        keep = newkeep = set(rec["id"] for rec in cur_knowls if rec["cat"] in cats)
        while newkeep:
            nextkeep = set()
            for kid in newkeep:
                for link in by_id[kid]["links"]:
                    if link in by_id and link not in keep: # link might be a top or bottom knowl...
                        nextkeep.add(link)
            keep = keep.union(nextkeep)
            newkeep = copy(nextkeep)
    by_id = {rec["id"]: rec for rec in cur_knowls if rec["id"] in keep}

    # Collect definitions in a file
    with open("definitions.txt", "w") as F:
        by_def = defaultdict(list)
        for kid in sorted(by_id):
            defines = by_id[kid]["defines"]
            if defines:
                _ = F.write(kid + ":\n")
                for term in defines:
                    _ = F.write("    * " + term + "\n")
                    by_def[term].append(kid)
        _ = F.write("\n" * 8)
        for term in sorted(by_def, key=lambda term:term.lower()):
            _ = F.write(term + ":\n")
            for kid in by_def[term]:
                _ = F.write("    * " + kid + "\n")

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
        for kwl in cur_knowls:
            if kwl["cat"] not in cats:
                _ = F.write(f"\\input{{knowls/{kwl['cat']}/{kwl['id']}}}\n")
        for cat in cats:
            _ = F.write(f"\n\n\\section{{{cat_names[cat]}}}\n")
            for kwl in cur_knowls:
                if kwl["cat"] == cat:
                    _ = F.write(f"\\input{{knowls/{kwl['cat']}/{kwl['id']}}}\n")
