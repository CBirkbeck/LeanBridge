#!/usr/bin/env python3
"""Mechanical 1:1 migration of the LMFDB-knowl LaTeX blueprint into Verso chapters.

Reads blueprint/src/{structure.json, macros/common.tex, auto_*.tex, knowls/...} and emits
blueprint-verso/LeanBridgeBlueprint/Chapters/*.lean: one module per chapter and subchapter of
structure.json, where a chapter with subchapters includes theirs.  Every referenced knowl is a
single `\\begin{definition}\\label{L}\\uses{...} BODY \\end{definition}` block; it
becomes a Verso `:::definition "L"` chunk. Its `(lean := ...)` names are the Mathlib
declarations the knowl links with `DEFINES(..., mathlib=...)` (written as `\\lean{...}` by
update_knowls.py) followed by the declarations listed for it in blueprint/src/lean_links.json
(Tau Ceti and LeanBridge ones, and Mathlib ones the knowl does not link yet), whose modules the
generated Prelude imports.
"""
import json
import re
import os
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SRC = os.path.join(ROOT, "blueprint", "src")
OUT = os.path.join(ROOT, "blueprint-verso", "LeanBridgeBlueprint", "Chapters")

# The chapters and their subchapters; a chapter without subchapters lists its knowls itself. Each
# such leaf has a list auto_<list>.tex of its knowls, written by update_knowls.py.
STRUCTURE = json.load(open(os.path.join(SRC, "structure.json")))["chapters"]
LEAVES = [leaf for chapter in STRUCTURE for leaf in chapter.get("subchapters", [chapter])]


def knowl_paths(autofile):
    paths = []
    with open(os.path.join(SRC, autofile)) as f:
        for line in f:
            m = re.search(r'\\input\{(knowls/[^}]+)\}', line)
            if m:
                paths.append(m.group(1))
    return paths


# ---- collect every defined label (for {uses}/hyperref filtering) ----
ALL_LABELS = set()
for leaf in LEAVES:
    for p in knowl_paths(f"auto_{leaf['list']}.tex"):
        fp = os.path.join(SRC, p)
        if not os.path.exists(fp):
            continue
        m = re.search(r'\\label\{([^}]+)\}', open(fp).read())
        if m:
            ALL_LABELS.add(m.group(1))

# Declarations for knowls, as {label: {declaration: module}}: Tau Ceti and LeanBridge ones, which
# the knowls themselves cannot link, and Mathlib ones for knowls that do not link them yet.
_links_path = os.path.join(SRC, "lean_links.json")
LEAN_LINKS = json.load(open(_links_path)) if os.path.exists(_links_path) else {}


def tex_prelude_block():
    """Emit macros as `\\def` (KaTeX has built-ins like \\R/\\C, so \\newcommand
    errors with 'use \\renewcommand'; \\def always overwrites)."""
    out = []
    with open(os.path.join(SRC, "macros", "common.tex")) as f:
        for line in f:
            s = line.strip()
            m = re.match(r'\\(?:new|renew)command\{(\\[A-Za-z]+)\}(?:\[(\d+)\])?\{(.*)\}$', s)
            if m:
                name, nargs, bodyx = m.group(1), m.group(2), m.group(3)
                args = ''.join(f'#{i}' for i in range(1, int(nargs) + 1)) if nargs else ''
                out.append(f'\\def{name}{args}{{{bodyx}}}')
                continue
            m = re.match(r'\\DeclareMathOperator\{(\\[A-Za-z]+)\}\{(.*)\}$', s)
            if m:
                out.append(f'\\def{m.group(1)}{{\\operatorname{{{m.group(2)}}}}}')
    # supplement: macros used in knowls but absent from common.tex
    out += [
        r'\def\Sha{\text{Ш}}',
        r'\def\smallsetminus{\setminus}',
    ]
    return "\n".join(out)


BRACED = r'([^{}]*)'  # non-nested brace content; the fixpoint loop converts inner macros first


def transform_body(body):
    """LaTeX knowl body -> Verso markup. Both math and generated inline markup
    (links, {bpref}, bold) are stashed into placeholders; literal brackets in the
    residual plain text are then escaped, and finally everything is restored. This
    keeps Verso from misreading literal `[...]` as a link or `{...}` as a directive."""
    tokens = []

    def tok(s):
        tokens.append(s)
        return f"\x00{len(tokens) - 1}\x00"

    # --- drop \cite{...} (balanced braces; keep a URL if one is embedded) ---
    out, i = [], 0
    while True:
        m = re.search(r'\\cite(?:\[[^\]]*\])?\{', body[i:])
        if not m:
            out.append(body[i:])
            break
        out.append(body[i:i + m.start()])
        j = i + m.end()
        depth, k = 1, j
        while k < len(body) and depth:
            depth += {'{': 1, '}': -1}.get(body[k], 0)
            k += 1
        h = re.search(r'href\{([^}]+)\}\{([^}]*)\}', body[j:k - 1])
        if h:
            out.append(tok(f'[{h.group(2)}]({h.group(1)})'))
        i = k
    body = ''.join(out)

    # --- collapse `$R$` nested inside \text{...} (which would break the outer
    # $...$ split); KaTeX renders \text{R-module} fine ---
    for _ in range(4):
        new = re.sub(r'(\\text\{[^{}$]*)\$([^$}]*)\$', r'\1\2', body)
        if new == body:
            break
        body = new

    # --- strip leanblueprint-only commands (status/link markers, not math content) ---
    body = re.sub(r'\\(leanok|notready|mathlibok|leanchapter)\b', '', body)
    body = re.sub(r'\\(lean|proves|alsoin|discussion)\s*\{[^}]*\}', '', body)

    # --- raw HTML links, which update_knowls.py leaves when the URL has quotes or other
    # attributes follow it; LMFDB-internal URLs become absolute ---
    def html_link(m):
        url = m.group(1).replace('\\_', '_')
        url = url.replace("{{url_for('abstract.index')}}", 'https://beta.lmfdb.org/Groups/Abstract/')
        if url.startswith('/'):
            url = 'https://beta.lmfdb.org' + url
        return tok(f'[{m.group(2)}]({url})')
    body = re.sub(r'<a\s+href="?([^"\s>]+)"?[^>]*>([^<]*)</a>', html_link, body)
    # --- Markdown headings, which Verso does not allow inside a definition, become bold lines ---
    body = re.sub(r'(?m)^[ \t]*#{1,6}[ \t]+(.+?)[ \t]*$', r'\\textbf{\1}', body)

    # --- math -> tokens ---
    def stash_math(content, display):
        c = content.strip()
        return tok(f'\n$$`{c}`\n' if display else f'$`{c}`')
    # MathJax script tags, whose underscores update_knowls.py escaped as in prose
    body = re.sub(r'<script type="math/tex(; mode=display)?">(.+?)</script>',
                  lambda m: stash_math(m.group(2).replace('\\_', '_'), bool(m.group(1))), body, flags=re.S)
    body = re.sub(r'\$\$(.+?)\$\$', lambda m: stash_math(m.group(1), True), body, flags=re.S)
    body = re.sub(r'\\\[(.+?)\\\]', lambda m: stash_math(m.group(1), True), body, flags=re.S)
    body = re.sub(r'\\\((.+?)\\\)', lambda m: stash_math(m.group(1), False), body, flags=re.S)
    body = re.sub(r'\$(.+?)\$', lambda m: stash_math(m.group(1), False), body, flags=re.S)

    # --- references and emphasis -> tokens, looped to a fixpoint so nested
    # constructs (e.g. \textbf{\hyperref[..]{..}}) fully convert; placeholders
    # contain no braces/brackets, so the inner-most match converts first. ---
    def knowl(m):
        lbl = m.group(1).replace('\\_', '_').strip()
        txt = re.sub(r"\\'?", '', m.group(2)).replace('\\_', '_').replace(';', '')
        return tok(f'{{bpref "{lbl}"}}[{txt}]' if lbl in ALL_LABELS else txt)

    def hyperref(m):
        lbl, txt = m.group(1), m.group(2)
        return tok(f'{{bpref "{lbl}"}}[{txt}]' if lbl in ALL_LABELS else txt)

    # An included knowl (KNOWL_INC) becomes a reference to it, titled by the reference itself
    def knowl_inc(m):
        lbl = m.group(1).replace('\\_', '_').strip()
        return tok(f'{{bpref "{lbl}"}}[]' if lbl in ALL_LABELS
                   else f'[{lbl}](https://beta.lmfdb.org/knowledge/show/{lbl})')

    # Raw knowl links <a ... knowl="ID">text</a>, which update_knowls.py leaves as they are
    def knowl_anchor(m):
        lbl = m.group(1).replace('\\_', '_').strip()
        txt = m.group(2).replace('\\_', '_').strip()
        return tok(f'{{bpref "{lbl}"}}[{txt}]') if lbl in ALL_LABELS else txt

    for _ in range(8):
        before = body
        body = re.sub(r"\{\{\s*KNOWL\('((?:[^'\\]|\\.)*)',\s*'((?:[^'\\]|\\.)*)'\)\s*\}\}", knowl, body)
        body = re.sub(r"\{\{\s*KNOWL\\?_INC\('((?:[^'\\]|\\.)*)'[^}]*\)\s*\}\}", knowl_inc, body)
        body = re.sub(r'<a\s[^>]*?\bknowl="([^"]+)"[^>]*>([^<]*)</a>', knowl_anchor, body)
        body = re.sub(r'\\hyperref\[([^\]]+)\]\{' + BRACED + r'\}', hyperref, body)
        body = re.sub(r'\\ref\{([^}]+)\}',
                      lambda m: tok(f'{{bpref "{m.group(1)}"}}[]') if m.group(1) in ALL_LABELS else '',
                      body)
        body = re.sub(r'\\href\{([^}]+)\}\{' + BRACED + r'\}',
                      lambda m: tok(f'[{m.group(2)}]({m.group(1)})'), body)
        # Verso convention: bold = *...*, emphasis = _..._  (NOT Markdown's **/*)
        body = re.sub(r'\\textbf\{' + BRACED + r'\}', lambda m: tok(f'*{m.group(1).strip()}*'), body)
        body = re.sub(r'\\(?:emph|textit)\{' + BRACED + r'\}', lambda m: tok(f'_{m.group(1).strip()}_'), body)
        # some knowls embed Markdown links [text](url) directly; preserve them
        # (Verso uses the same syntax), unescaping LaTeX escapes in the URL
        def mdlink(m):
            url = re.sub(r'\\([_#&%~])', r'\1', m.group(2))
            return tok(f'[{m.group(1)}]({url})')
        body = re.sub(r'\[([^\[\]]*)\]\(([^)\s]+)\)', mdlink, body)
        if body == before:
            break

    # --- lists, spacing macros ---
    body = re.sub(r'\\(begin|end)\{(itemize|enumerate)\}', '', body)
    body = re.sub(r'[ \t]*\\item\s*', '\n- ', body)
    body = body.replace('\\,', ' ').replace('\\ ', ' ').replace('\\!', '')

    # --- LaTeX accent macros in prose (author names etc.): keep the base letter ---
    body = re.sub(r"\\[vkHurcdb=.]\{([A-Za-z])\}", r'\1', body)
    body = re.sub(r"\\['\"^~`=.]\{?([A-Za-z])\}?", r'\1', body)

    # --- LaTeX quotes -> straight quotes (backtick is special in Verso) ---
    body = body.replace('``', '"').replace("''", '"').replace('`', "'")

    # --- LaTeX's escaped underscore is a literal underscore, which Verso escapes the same way;
    # without this, the escape below would turn it into an escaped backslash and an emphasis mark
    body = body.replace('\\_', tok('\\_'))

    # --- escape residual Verso/Markdown specials in plain text. All generated
    # markup ({bpref}/links/math/*bold*/_emph_) is tokenised placeholders with no
    # such chars, so every residual []{}*_ here is a literal from the source. ---
    for ch in '[]{}*_':
        body = body.replace(ch, '\\' + ch)

    # --- restore tokens (iteratively: a token may reference another) ---
    for _ in range(12):
        new = re.sub(r'\x00(\d+)\x00', lambda m: tokens[int(m.group(1))], body)
        if new == body:
            break
        body = new

    body = re.sub(r'[ \t]+\n', '\n', body)
    body = re.sub(r'\n{3,}', '\n\n', body)
    return body.strip()


def convert_knowl(path):
    txt = open(os.path.join(SRC, path)).read()
    title_m = re.search(r'\\subsection\{\\href\{([^}]+)\}\{([^}]*)\}\}', txt)
    url = title_m.group(1) if title_m else None
    title = title_m.group(2) if title_m else None
    label_m = re.search(r'\\label\{([^}]+)\}', txt)
    label = label_m.group(1)
    uses_m = re.search(r'\\uses\{([^}]*)\}', txt)
    uses = [u.strip() for u in uses_m.group(1).split(',')] if uses_m else []
    uses = [u for u in uses if u in ALL_LABELS and u != label]
    lean_m = re.search(r'\\lean\{([^}]*)\}', txt)
    decls = [d.strip() for d in lean_m.group(1).split(',') if d.strip()] if lean_m else []
    decls += [d for d in LEAN_LINKS.get(label, {}) if d not in decls]
    # body = between the (label/uses) header and \end{definition}
    body = txt.split(r'\begin{definition}', 1)[1]
    body = body.rsplit(r'\end{definition}', 1)[0]
    body = re.sub(r'\\label\{[^}]+\}', '', body, count=1)
    body = re.sub(r'\\uses\{[^}]*\}', '', body, count=1)
    body = transform_body(body)

    lead = ''
    if title:
        t = transform_body(title)
        link = f' ([LMFDB]({url}))' if url else ''
        lead = f'*{t}.*{link}\n\n'
    uses_line = ' '.join(f'{{uses "{u}"}}[]' for u in uses)
    lean = f' (lean := "{", ".join(decls)}")' if decls else ''
    chunk = f':::definition "{label}"{lean}\n{lead}{body}\n'
    if uses_line:
        chunk += f'\nDepends on: {uses_line}\n'
    chunk += ':::\n'
    return chunk


def names(xs):
    """The items as inline code: `a`, `b` and `c`."""
    xs = [f"`{x}`" for x in xs]
    return xs[0] if len(xs) == 1 else ", ".join(xs[:-1]) + " and " + xs[-1]


def leaf_intro(leaf, is_chapter):
    """The introduction of a chapter without subchapters or of a subchapter: its LMFDB categories (the
    part of the ids before the first or second dot) and the knowls placed there despite their ids."""
    cats = leaf["categories"]
    kind = ("subcategor" if all("." in c for c in cats) else "categor") + ("y" if len(cats) == 1 else "ies")
    # subcategories that have a subchapter of their own
    others = [c for other in LEAVES for c in other["categories"] if any(c.startswith(x + ".") for x in cats)]
    intro = (f"This {'chapter' if is_chapter else 'section'} lists the LMFDB definitions in the {kind} "
             f"{names(cats)}" + (f", apart from those in {names(others)}" if others else "")
             + ". Each definition links back to its LMFDB knowl.")
    wrong = leaf.get("wrong_labels", [])
    if wrong:
        intro += (f" {names(wrong)} also {'belongs' if len(wrong) == 1 else 'belong'} here, although "
                  f"{'its id puts it' if len(wrong) == 1 else 'their ids put them'} in another LMFDB category.")
    return intro


def chapter_intro(chapter):
    cats = [c for sub in chapter["subchapters"] for c in sub["categories"]]
    return (f"This chapter lists the LMFDB definitions in the categories {names(cats)}, with a section "
            "for each. Each definition links back to its LMFDB knowl.")


def verso_title(title):
    """A title as the contents of a Lean string literal holding Verso markup: Verso's markup characters
    are escaped (titles are parsed as markup, so `𝔽_q` would start an emphasis), then backslashes and
    quotes for Lean."""
    markup = re.sub(r'([_*\[\]{}`])', r'\\\1', title)
    return markup.replace('\\', '\\\\').replace('"', '\\"')


def metadata(part):
    """Verso part metadata: a tag and a page name, where structure.json gives them."""
    fields = [f'{key} := "{part[key]}"' for key in ("tag", "file") if key in part]
    return ["%%%", *fields, "%%%"] if fields else []


def lean_imports():
    """`Mathlib` for the knowls' links, then the modules of the mapped declarations in the chapters."""
    mods = {mod for label, links in LEAN_LINKS.items() if label in ALL_LABELS for mod in links.values()}
    return ["Mathlib"] + sorted(mods)


def emit_prelude():
    out = os.path.join(os.path.dirname(OUT), "Prelude.lean")
    parts = [
        "import Verso",
        "import VersoManual",
        "import VersoBlueprint",
        *[f"import {mod}" for mod in lean_imports()],
        "",
        "open Verso Verso.Genre Verso.Genre.Manual Informal",
        "",
        'tex_prelude r#"' + tex_prelude_block() + '"#',
        "",
    ]
    with open(out, "w") as f:
        f.write("\n".join(parts))
    return out


def emit_leaf(leaf, is_chapter):
    """The module of a chapter without subchapters or of a subchapter, with its definitions."""
    autofile = f"auto_{leaf['list']}.tex"
    chunks = [convert_knowl(p) for p in knowl_paths(autofile) if os.path.exists(os.path.join(SRC, p))]
    parts = [
        "import Verso",
        "import VersoManual",
        "import VersoBlueprint",
        "import LeanBridgeBlueprint.Prelude",
        "",
        "open Verso.Genre",
        "open Verso.Genre.Manual",
        "open Informal",
        "",
        f'#doc (Manual) "{verso_title(leaf["title"])}" =>',
        *metadata(leaf),
        "",
        leaf_intro(leaf, is_chapter),
        "",
    ]
    parts += chunks
    out = os.path.join(OUT, f"{leaf['module']}.lean")
    with open(out, "w") as f:
        f.write("\n".join(parts))
    return out, len(chunks)


def emit_parent(chapter):
    """The module of a chapter with subchapters, which includes theirs."""
    subs = chapter["subchapters"]
    parts = [
        "import Verso",
        "import VersoManual",
        "import VersoBlueprint",
        *[f"import LeanBridgeBlueprint.Chapters.{sub['module']}" for sub in subs],
        "",
        "open Verso.Genre",
        "open Verso.Genre.Manual",
        "open Informal",
        "",
        f'#doc (Manual) "{verso_title(chapter["title"])}" =>',
        *metadata(chapter),
        "",
        chapter_intro(chapter),
        "",
        *[f"{{include 1 LeanBridgeBlueprint.Chapters.{sub['module']}}}\n" for sub in subs],
    ]
    out = os.path.join(OUT, f"{chapter['module']}.lean")
    with open(out, "w") as f:
        f.write("\n".join(parts))
    return out


if __name__ == "__main__":
    only = sys.argv[1] if len(sys.argv) > 1 else None
    os.makedirs(OUT, exist_ok=True)
    print(f"prelude -> {emit_prelude()}")
    for chapter in STRUCTURE:
        for leaf in chapter.get("subchapters", []):
            if not only or only == leaf["module"]:
                out, n = emit_leaf(leaf, False)
                print(f"{leaf['module']}: {n} definitions -> {out}")
        if not only or only == chapter["module"]:
            if "subchapters" in chapter:
                print(f"{chapter['module']}: {len(chapter['subchapters'])} sections -> {emit_parent(chapter)}")
            else:
                out, n = emit_leaf(chapter, True)
                print(f"{chapter['module']}: {n} definitions -> {out}")
    print(f"total labels defined: {len(ALL_LABELS)}")
