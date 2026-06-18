#!/usr/bin/env python3
"""Mechanical 1:1 migration of the LMFDB-knowl LaTeX blueprint into Verso chapters.

Reads blueprint/src/{macros/common.tex, auto_*.tex, knowls/...} and emits
blueprint-verso/LeanBridgeBlueprint/Chapters/*.lean.  Every referenced knowl is a
single `\\begin{definition}\\label{L}\\uses{...} BODY \\end{definition}` block; it
becomes an informal Verso `:::definition "L"` chunk (no `(lean := )` yet).
"""
import re
import os
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SRC = os.path.join(ROOT, "blueprint", "src")
OUT = os.path.join(ROOT, "blueprint-verso", "LeanBridgeBlueprint", "Chapters")

CHAPTERS = [
    ("Background", "auto_background.tex", "Background"),
    ("NumberFields", "auto_number_fields.tex", "Number fields"),
    ("EllipticCurves", "auto_elliptic_curves.tex", "Elliptic curves"),
    ("ModularForms", "auto_modular_forms.tex", "Modular forms"),
]


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
for _, af, _ in CHAPTERS:
    for p in knowl_paths(af):
        fp = os.path.join(SRC, p)
        if not os.path.exists(fp):
            continue
        m = re.search(r'\\label\{([^}]+)\}', open(fp).read())
        if m:
            ALL_LABELS.add(m.group(1))


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

    # --- math -> tokens ---
    def stash_math(content, display):
        c = content.strip()
        return tok(f'\n$$`{c}`\n' if display else f'$`{c}`')
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

    for _ in range(8):
        before = body
        body = re.sub(r"\{\{\s*KNOWL\('((?:[^'\\]|\\.)*)',\s*'((?:[^'\\]|\\.)*)'\)\s*\}\}", knowl, body)
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
    chunk = f':::definition "{label}"\n{lead}{body}\n'
    if uses_line:
        chunk += f'\nDepends on: {uses_line}\n'
    chunk += ':::\n'
    return chunk


def chapter_intro(title):
    return f"This chapter lists the LMFDB definitions relating to *{title.lower()}*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl."


def emit_prelude():
    out = os.path.join(os.path.dirname(OUT), "Prelude.lean")
    parts = [
        "import Verso",
        "import VersoManual",
        "import VersoBlueprint",
        "",
        "open Verso Verso.Genre Verso.Genre.Manual Informal",
        "",
        'tex_prelude r#"' + tex_prelude_block() + '"#',
        "",
    ]
    with open(out, "w") as f:
        f.write("\n".join(parts))
    return out


def emit_chapter(modname, autofile, title):
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
        f'#doc (Manual) "{title}" =>',
        "",
        chapter_intro(title),
        "",
    ]
    parts += chunks
    out = os.path.join(OUT, f"{modname}.lean")
    with open(out, "w") as f:
        f.write("\n".join(parts))
    return out, len(chunks)


if __name__ == "__main__":
    only = sys.argv[1] if len(sys.argv) > 1 else None
    os.makedirs(OUT, exist_ok=True)
    print(f"prelude -> {emit_prelude()}")
    for modname, autofile, title in CHAPTERS:
        if only and modname != only:
            continue
        out, n = emit_chapter(modname, autofile, title)
        print(f"{modname}: {n} definitions -> {out}")
    print(f"total labels defined: {len(ALL_LABELS)}")
