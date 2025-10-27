# Lean LMFDB Bridge Project

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Zulip : Topic](https://img.shields.io/badge/Zulip-Topic-%237E57C2.svg?logo=zulip&logoColor=white)](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Tutorial.3A.20Getting.20Started.20with.20Blueprint-Driven.20Projects)
[![YouTube : Tutorial](https://img.shields.io/badge/YouTube-Tutorial-%23FF0000.svg?logo=youtube&logoColor=white)](https://youtu.be/KyuyTsLgkMY)

This repository contains a [blueprint](https://github.com/PatrickMassot/leanblueprint/) for formalizing definitions within the [L-functions and modular forms database](https://lmfdb.org).  You can view the rendered version [here](https://cbirkbeck.github.io/LeanBridge/).

The process for updating the contents of this blueprint is different than most other blueprints, because it is built to improve the integration between Mathlib and the LMFDB.  While there is some framing content manually written in [content.tex](https://github.com/CBirkbeck/LeanBridge/blob/main/blueprint/src/content.tex), most of the blueprint is generated from the LMFDB's [knowl database](https://beta.lmfdb.org/knowledge/) using the [update script](https://github.com/CBirkbeck/LeanBridge/blob/main/blueprint/src/update_knowls.py).

Thus most of the work in updating this blueprint takes the following form:

1. [Adding](https://leanprover-community.github.io/contribute/index.html) definitions and theorems to mathlib

1. Linking definitions in LMFDB knowls to mathlib using the [DEFINES macro](https://beta.lmfdb.org/knowledge/show/doc.knowl.guidelines), and linking theorems using the [cite command](https://beta.lmfdb.org/knowledge/show/doc.knowl.guidelines).  Editing and creating knowls requires an account on the LMFDB; contact David Roe or Andrew Sutherland on Zulip (either [LMFDB](https://lmfdb.zulipchat.com) or [Lean](https://leanprover.zulipchat.com)) if you want to get involved.

1. Once definitions have been added to mathlib and linked in the corresponding knowl, run the [update script](https://github.com/CBirkbeck/LeanBridge/blob/main/blueprint/src/update_knowls.py) to update the [knowl folder](https://github.com/CBirkbeck/LeanBridge/tree/main/blueprint/src/knowls) and make a PR to this repository.

## Local setup

1. Ensure that you have a functioning Lean 4 installation. If you do not, please follow
the [Lean installation guide](https://leanprover-community.github.io/get_started.html).

1. To clone this repository to your local machine, please refer to the relevant section of the
GitHub documentation [here](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository).

1. If you don't have a Python environment, you can install one by following the instructions in the
[Python installation guide](https://www.python.org/downloads/).

1. You will need to install PyGraphViz, following the instructions in the
[installation guide](https://pygraphviz.github.io/documentation/stable/install.html).

1. If you want to run the update script, you will need to install Networkx using

```bash
pip install networkx
```

and psycopg2 using

```bash
pip install psycopg2-binary
```

1. Install LeanBlueprint by running:

```bash
pip install leanblueprint
```

If you have an existing installation of LeanBlueprint, you can upgrade to the latest version by
running:

```bash
pip install -U leanblueprint
```

1. You can use `leanblueprint` to build the blueprint locally. The available commands are:

* `leanblueprint pdf` to build the pdf version (this requires a TeX installation
  of course).
* `leanblueprint web` to build the web version
* `leanblueprint checkdecls` to check that every Lean declaration name that appear
  in the blueprint exist in the project (or in a dependency of the project such
  as Mathlib). This requires a compiled Lean project, so make sure to run `lake build` beforehand.
* `leanblueprint all` to run the previous three commands.
* `leanblueprint serve` to start a local webserver showing your local blueprint
  (this sounds silly but web browsers paranoia makes it impossible to simply
  open the generated html pages without serving them). The url you should use
  in your browser will be displayed and will probably be `http://0.0.0.0:8000/`,
  unless the port 8000 is already in use.

## Repository Layout

The template repository is organized as follows (listing the main folders and files):

- [`.github`](.github) contains GitHub-specific configuration files and workflows.
    - [`workflows`](.github/workflows) contains GitHub Actions workflow files.
        - [`build-project.yml`](.github/workflows/build-project.yml) defines the workflow for building
        the Lean project on pushes, pull requests, and manual triggers. This is a minimalistic build
        workflow which is not necessary if you decide to generate a blueprint (see instructions below)
        and can be manually disabled by clicking on the **Actions** tab, selecting **Build Project**
        in the left sidebar, then clicking the horizontal triple dots (⋯) on the right,
        and choosing **Disable workflow**.
        - [`create-release.yml`](.github/workflows/create-release.yml): defines the workflow for creating a new Git tag and GitHub release when the `lean-toolchain` file is updated in the `main` branch. Ensure the following settings are configured under **Settings > Actions > General > Workflow permissions**: "Read and write permissions" and "Allow GitHub Actions to create and approve pull requests".
        - [`update.yml`](.github/workflows/update.yml) is the dependency
        update workflow to be triggered manually by default. [It's not documented yet, but it will be soon.]
    - [`dependabot.yml`](.github/dependabot.yml) is the configuration file to automate CI dependency updates.
- [`.vscode`](.vscode) contains Visual Studio Code configuration files
    - [`extensions.json`](.vscode/extensions.json) recommends VS Code extensions for the project.
    - [`settings.json`](.vscode/settings.json) defines the project-specific settings for VS Code.
- [`Project`](Project) should contain the Lean code files.
    - [`Mathlib`](Project/Mathlib) should contain `.lean` files with declarations missing from the
    current version of Mathlib.
    - [`Example.lean`](Project/Example.lean) is a sample Lean file.
- [`scripts`](scripts) contains scripts to update Mathlib ensuring that the latest version is
fetched and integrated into the development environment.
- [`.gitignore`](.gitignore) specifies files and folders to be ignored by Git.
and environment.
- [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) should contain the code of conduct for the project.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) should provide the guidelines for contributing to the
project.
- [`lakefile.toml`](lakefile.toml) is the configuration file for the Lake build system used in
Lean projects.
- [`lean-toolchain`](lean-toolchain) specifies the Lean version and toolchain used for the project.

## Blueprint

For more details about the LeanBlueprint package and its commands, please refer to its
[documentation](https://github.com/PatrickMassot/leanblueprint/tree/master#starting-a-blueprint).

After pushing changes, please wait for the GitHub Action workflow to finish.
You can keep track of the progress in the **Actions** tab of your repository.