# `lookup` tactic — decisions where the right choice was unclear

## Clickable LMFDB link (task 2)

**Unclear:** Lean core `MessageData` has no dedicated hyperlink constructor, so "make the
link clickable in the infoview" is environment-dependent. The VS Code Lean infoview
auto-linkifies bare `http(s)://` URLs in messages, but does *not* linkify a URL wrapped in
parentheses or with trailing punctuation attached.

- Option A: keep a custom widget / `MessageData.ofWidget` to render an `<a>` tag. Heavy,
  and overkill for a one-line link.
- Option B: emit the URL bare on its own line with no surrounding punctuation, relying on
  the infoview's auto-linkification.

**Update — markdown link also failed.** Neither a bare URL nor a markdown link `[text](url)`
is linkified by the infoview for a tactic message.

**Final — ProofWidgets HTML embedded in the message.** The report is now built as a
`ProofWidgets.Html` value containing a real `<a href=...>` element and embedded into the
thrown error via `MessageData.ofHtml`, which renders the HTML (clickable anchor) in the
infoview and falls back to a plain-text `alt` everywhere else (e.g. the LSP diagnostic text).
This is distinct from the project's existing `LMFDBWidget` (which the user noted does not
help); it uses only the stock `HtmlDisplay` component that ships with ProofWidgets.

## Reporting signed-discriminant counterexamples (tasks 3 & 7)

**Unclear:** how to display the discriminant of a counterexample when the query referenced
the *signed* discriminant (`NumberField.discr F`), given the DB stores `disc_sign` and
`disc_abs` separately.

- Option A: report the two raw columns (`disc_sign = 1, disc_abs = 41`).
- Option B: report the reconstructed signed value (`discriminant = 41`) by selecting the
  SQL expression `(disc_sign * disc_abs)`.

**Chosen: Option B.** It mirrors what the user wrote in Lean (`NumberField.discr F`) and is
less confusing than exposing the storage split. `|NumberField.discr F|` still reports as
`|discriminant|` backed by `disc_abs`.
