# Lean LMFDB Bridge Project

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Zulip : Topic](https://img.shields.io/badge/Zulip-Topic-%237E57C2.svg?logo=zulip&logoColor=white)](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Tutorial.3A.20Getting.20Started.20with.20Blueprint-Driven.20Projects)
[![YouTube : Tutorial](https://img.shields.io/badge/YouTube-Tutorial-%23FF0000.svg?logo=youtube&logoColor=white)](https://youtu.be/KyuyTsLgkMY)

This repository contains a [Verso blueprint](https://github.com/leanprover/verso-blueprint) for formalizing definitions within the [L-functions and modular forms database](https://lmfdb.org).  **You can view the rendered blueprint at [cbirkbeck.github.io/LeanBridge](https://cbirkbeck.github.io/LeanBridge/).**

The process for updating the contents of this blueprint is different than most other blueprints, because it is built to improve the integration between Mathlib and the LMFDB.  While there is some framing content manually written in [content.tex](https://github.com/CBirkbeck/LeanBridge/blob/main/blueprint/src/content.tex), most of the blueprint is generated from the LMFDB's [knowl database](https://beta.lmfdb.org/knowledge/) using the [update script](https://github.com/CBirkbeck/LeanBridge/blob/main/blueprint/src/update_knowls.py), whose output [convert_knowls.py](https://github.com/CBirkbeck/LeanBridge/blob/main/blueprint-verso/scripts/convert_knowls.py) turns into the chapters of the Verso blueprint.

Thus most of the work in updating this blueprint takes the following form:

1. [Adding](https://leanprover-community.github.io/contribute/index.html) definitions and theorems to mathlib

1. Linking definitions in LMFDB knowls to mathlib using the [DEFINES macro](https://beta.lmfdb.org/knowledge/show/doc.knowl.guidelines), and linking theorems using the [cite command](https://beta.lmfdb.org/knowledge/show/doc.knowl.guidelines).  Editing and creating knowls requires an account on the LMFDB; contact David Roe or Andrew Sutherland on Zulip (either [LMFDB](https://lmfdb.zulipchat.com) or [Lean](https://leanprover.zulipchat.com)) if you want to get involved.

1. Once definitions have been added to mathlib and linked in the corresponding knowl, refresh the [knowl folder](https://github.com/CBirkbeck/LeanBridge/tree/main/blueprint/src/knowls) and the Verso chapters (see [Updating the blueprint](#updating-the-blueprint)) and make a PR to this repository.

## Linking to Mathlib

The overview above describes the workflow; this section collects the practical details for its key
step — matching an LMFDB definition or theorem to the right
[Mathlib](https://github.com/leanprover-community/mathlib4) declaration and recording the link.

### Finding the Mathlib declaration

Before defining anything yourself, check whether Mathlib already has it:

- **[Loogle](https://loogle.lean-lang.org/)** — search by name fragment, type pattern, or
  conclusion (e.g. `NumberField.discr`, `ClassGroup _`).
- **[LeanSearch](https://leansearch.net/)** — natural-language search (e.g. "discriminant of a
  number field").
- **[Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/)** — the full API, with a
  search box.
- **In the editor** — hover over a name for its type and docstring, and use `exact?` / `apply?` to
  let Lean find a matching lemma.

For example, for a number field `K`:

| LMFDB concept | Mathlib declaration |
| --- | --- |
| Degree over ℚ | `Module.finrank ℚ K` |
| Discriminant | `NumberField.discr K` |
| Ring of integers | `NumberField.RingOfIntegers K` (`𝓞 K`) |
| Class group / number | `ClassGroup (𝓞 K)` / `NumberField.classNumber K` |
| Unit rank / regulator | `NumberField.Units.rank K` / `NumberField.Units.regulator K` |
| Galois | `IsGalois ℚ K` |

If it genuinely isn't in Mathlib yet, it must first be
[added to Mathlib](https://leanprover-community.github.io/contribute/index.html).

### Recording the link

Link the declaration from the corresponding LMFDB knowl: use the `DEFINES` macro for definitions and
the `cite` command for theorems (see the LMFDB
[knowl guidelines](https://beta.lmfdb.org/knowledge/show/doc.knowl.guidelines) for the exact syntax).
Editing or creating knowls requires an LMFDB account — contact David Roe or Andrew Sutherland on
Zulip ([LMFDB](https://lmfdb.zulipchat.com) or [Lean](https://leanprover.zulipchat.com)) to get
involved. Finally, refresh the blueprint (see [Updating the blueprint](#updating-the-blueprint)) and
open a PR.

## Local setup

1. Install Lean by following the
   [Lean installation guide](https://leanprover-community.github.io/get_started.html), and clone
   this repository.

1. Download Mathlib's compiled files, then build:

   ```bash
   lake exe cache get
   lake build
   ```

   `lake build` builds [`LeanBridge.lean`](LeanBridge.lean), a curated import of the library. To
   build every hand-written module, as CI does, run `./scripts/build-modules.sh`; it leaves out the
   generated level-one certificates, the `lookup` demo (which queries the LMFDB over the network)
   and one experiment. The first build also compiles the parts of Tau Ceti that LeanBridge imports.

## Updating the blueprint

The update script downloads the knowls from a public mirror of the LMFDB database, so it needs
Python with [NetworkX](https://networkx.org) and [psycopg2](https://www.psycopg.org):

```bash
pip install networkx psycopg2-binary
cd blueprint/src
python update_knowls.py
cd ../..
python blueprint-verso/scripts/convert_knowls.py
```

`update_knowls.py` rewrites the [knowl folder](blueprint/src/knowls),
[`definitions.txt`](blueprint/src/definitions.txt), [`edges.txt`](blueprint/src/edges.txt) and the
`auto_*.tex` chapter lists. `convert_knowls.py` turns these into the chapters in
[`blueprint-verso/LeanBridgeBlueprint/Chapters`](blueprint-verso/LeanBridgeBlueprint/Chapters). To
check that the site builds, run `./scripts/ci-pages.sh` in `blueprint-verso/`; it writes the site to
`blueprint-verso/_out/site/html-multi/`.

## Repository layout

- [`LeanBridge.lean`](LeanBridge.lean): the root import of the library. Its header lists the Tau Ceti
  declarations that LeanBridge uses for LMFDB elliptic-curve knowls instead of its own copies.
- [`LeanBridge/ForMathlib`](LeanBridge/ForMathlib): declarations that belong in Mathlib, laid out as
  Mathlib's own directories.
- [`LeanBridge/LMFDB`](LeanBridge/LMFDB): LMFDB-specific material: certificates for LMFDB number
  fields and level-one newforms, and tactics that query the LMFDB.
- [`LeanBridge/IdealArithmetic`](LeanBridge/IdealArithmetic): vendored from CertifyingInvariantsNF:
  certified rings of integers, discriminants, class groups and Galois groups of number fields.
- [`LeanBridge/Lookup`](LeanBridge/Lookup): the `lookup` tactic, which searches the LMFDB for a
  counterexample to the goal.
- [`LeanBridge/Spec`](LeanBridge/Spec): specifications, with `sorry`, of objects not yet defined:
  modular curves, Shimura curves and Hilbert modular surfaces.
- [`blueprint/src`](blueprint/src): the knowls as LaTeX, the update script, and its
  `definitions.txt` and `edges.txt`.
- [`blueprint-verso`](blueprint-verso): the Verso blueprint project.
- [`scripts`](scripts): `build-modules.sh`, and the Sage scripts that generate the level-one
  certificates.
- [`widget`](widget): the JavaScript of the LMFDB search widget.
- [`home_page`](home_page): the Jekyll home page of the old LaTeX blueprint site, no longer
  deployed.
- [`.github/workflows`](.github/workflows): [`build.yml`](.github/workflows/build.yml) builds the
  Lean library with `scripts/build-modules.sh`; [`blueprint.yml`](.github/workflows/blueprint.yml)
  builds the Verso blueprint and deploys it to GitHub Pages;
  [`create-release.yml`](.github/workflows/create-release.yml) tags a release when `lean-toolchain`
  changes on `main`; [`update.yml`](.github/workflows/update.yml) updates the dependencies when run
  by hand.
