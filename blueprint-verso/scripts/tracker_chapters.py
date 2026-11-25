"""Generate the blueprint's "Work tracker" chapter from the tracker data.

usage: python3 -I scripts/tracker_chapters.py TRACKER_HTML OUT_DIR

TRACKER_HTML is a page built by the tracker builder (its `const DATA = [...]` and `const SUB = "..."` lines are read).
Writes, as new files under OUT_DIR, `WorkTracker.lean` (the chapter) and one `WorkTracker<Section>.lean` per list: the
ten status lists of the 1725 LMFDB knowls, the LMFDB issues (knowl text errors with old and new text) and the GitHub
issues. Copy them into `LeanBridgeBlueprint/Chapters/`. Creates new files only.
"""
import json
import os
import re
import sys

src_path, out = sys.argv[1], sys.argv[2]
src = open(src_path, encoding='utf8').read()
DATA = json.loads(re.search(r'const DATA = (\[.*?\]);\n', src, re.S).group(1))
SUB = json.loads(re.search(r'const SUB = (".*?");\n', src, re.S).group(1))


def text(s):
    """Plain text for Verso: backticks become quotes, Markdown specials and backslashes are escaped, newlines go."""
    s = re.sub(r'\s+', ' ', str(s)).strip().replace('`', "'")
    s = s.replace('\\', '\\\\')
    for ch in '[]{}*_$#<>|~^':
        s = s.replace(ch, '\\' + ch)
    return s


def code(s):
    """Inline code, with a fence longer than any run of backticks inside."""
    s = re.sub(r'\s+', ' ', str(s)).strip()
    n = max([len(m) for m in re.findall(r'`+', s)] + [0]) + 1
    f = '`' * n
    pad = ' ' if s.startswith('`') or s.endswith('`') else ''
    return f + pad + s + pad + f


def block(s):
    """A fenced code block for an old or new knowl text."""
    n = max([len(m) for m in re.findall(r'`+', s)] + [2]) + 1
    f = '`' * n
    return f + '\n' + s.replace('\r\n', '\n').rstrip('\n') + '\n' + f


def link(label, url):
    return f'[{label}]({url})' if url else label


def knowl(it):
    lm = 'https://beta.lmfdb.org/knowledge/show/' + it['id']
    return link(code(it['id']), it.get('bp') or lm)


def mod_name(title):
    return 'WorkTracker' + ''.join(w.capitalize() for w in re.findall(r'[A-Za-z]+', title))


def status_item(it):
    parts = [knowl(it)]
    if it.get('t'):
        parts.append('— ' + text(it['t']) + '.')
    tags = ', '.join(text(x) for x in (it.get('e'), it.get('b')) if x)
    if tags:
        parts.append('Difficulty: ' + tags + '.')
    if it.get('bk'):
        parts.append('*Blocked by:* ' + text(it['bk']))
    if it.get('d'):
        parts.append('Declarations' + (' (' + text(it['s']) + ')' if it.get('s') else '') + ': '
                     + ', '.join(code(d) for d in it['d']) + '.')
    if it.get('iss'):
        parts.append('GitHub issues: ' + ', '.join(
            link('#' + str(n), f'https://github.com/CBirkbeck/LeanBridge/issues/{n}') for n in it['iss']) + '.')
    if it.get('x'):
        parts.append('Note: ' + text(it['x']))
    return '* ' + ' '.join(parts)


def issue_item(it):
    lines = ['* ' + knowl(it) + (' — ' + text(it['t']) + '.' if it.get('t') else '')
             + ' Kind: ' + text(', '.join(it.get('kds') or [it.get('kd', '')])) + '.'
             + (' Category: ' + text(it['cat']) + '.' if it.get('cat') else '')]
    if it.get('why'):
        lines.append('\n  ' + text(it['why']))
    for old, new in it.get('pairs') or []:
        lines.append('\n  Old:\n\n' + '\n'.join('  ' + l for l in block(old).split('\n')))
        lines.append('\n  New:\n\n' + '\n'.join('  ' + l for l in block(new).split('\n')))
    return '\n'.join(lines)


def github_item(it):
    url = f"https://github.com/CBirkbeck/LeanBridge/issues/{it['n']}"
    s = '* ' + link('#' + str(it['n']), url) + ' (' + text(it.get('state', '')) + ') — ' + text(it.get('title', '')) + '.'
    if it.get('rem'):
        s += ' Remaining: ' + text(it['rem'])
    if it.get('k'):
        s += ' Knowls: ' + ', '.join(code(k) for k in it['k']) + '.'
    return s


HEAD = 'import Verso\nimport VersoManual\nimport VersoBlueprint\n'
OPEN = '\nopen Verso.Genre\nopen Verso.Genre.Manual\n'


def new_file(name, body):
    with open(os.path.join(out, name), 'x', encoding='utf8') as f:
        f.write(body)


os.makedirs(out, exist_ok=True)
mods = []
for sec in DATA:
    title, items = sec['title'], sec['items']
    m = mod_name(title)
    mods.append((m, title, len(items)))
    if title == 'LMFDB issues':
        blurb = ('Errors found in the knowl texts while formalising them, one entry per knowl, with the exact old '
                 'and new text of each correction where there is one.')
    elif title == 'GitHub issues':
        blurb = "The project's GitHub issues, with what remains to be done for each."
    else:
        blurb = text(sec.get('blurb', ''))
    # One long list makes Lean's code generator recurse too deeply: group the entries by blueprint chapter, in parts of
    # at most CHUNK entries, each under its own heading.
    groups = {}
    for it in items:
        groups.setdefault(it.get('ch') or 'Not in the blueprint', []).append(it)
    fmt = (issue_item if title == 'LMFDB issues' else github_item if title == 'GitHub issues' else status_item)
    sep = '\n\n' if title == 'LMFDB issues' else '\n'
    chunk = 15 if title == 'LMFDB issues' else 30
    parts = []
    for ch in sorted(groups, key=lambda c: (c == 'Not in the blueprint', c)):
        g = groups[ch]
        for i in range(0, len(g), chunk):
            head = text(ch) if title != 'GitHub issues' else 'Issues'
            if len(g) > chunk:
                head += f' ({i + 1}–{min(i + chunk, len(g))} of {len(g)})'
            parts.append(f'# {head}\n\n' + sep.join(fmt(it) for it in g[i:i + chunk]))
    body = '\n\n'.join(parts)
    new_file(m + '.lean', HEAD + OPEN + f'\n#doc (Manual) "{title}" =>\n\n{len(items)} entries. {blurb}\n\n{body}\n')

chapter = HEAD + ''.join(f'import LeanBridgeBlueprint.Chapters.{m}\n' for m, _, _ in mods) + OPEN
chapter += '\n#doc (Manual) "Work tracker" =>\n\n'
chapter += text(SUB.replace(' Mathlib and Tau Ceti declarations link to their Tau Ceti Review page.', '')) + '\n\n'
chapter += ('Every LMFDB knowl, the site ones included, by its status: formalised (in Mathlib, Tau Ceti or LeanBridge), '
            'partly formalised with what still blocks it and how hard that looks, waiting for the Tau Ceti bump, or not '
            'yet formalised. Then the errors found in the knowl texts, and the GitHub issues.\n\n')
chapter += '\n'.join(f'* {text(t)}: {n}' for _, t, n in mods) + '\n\n'
chapter += '\n\n'.join(f'{{include 1 LeanBridgeBlueprint.Chapters.{m}}}' for m, _, _ in mods) + '\n'
new_file('WorkTracker.lean', chapter)
print(len(mods), 'sections;', sum(n for _, _, n in mods), 'entries')
