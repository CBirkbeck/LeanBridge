#!/usr/bin/env bash
# Builds every hand-written module of LeanBridge, as the `Build LeanBridge` workflow does. Left out:
# * the generated level-one q-expansion certificates in `LeanBridge/LMFDB/ModularForms/LevelOne/`;
# * `LeanBridge/Lookup/Demo.lean`, which queries the LMFDB over the network while elaborating;
# * the experiment in `LeanBridge/Mathlib/Units.lean/`, whose directory name is not a module path.
set -euo pipefail

cd "$(dirname "$0")/.."

mapfile -t modules < <(git ls-files 'LeanBridge/*.lean' \
  | grep -v -e '^LeanBridge/LMFDB/ModularForms/LevelOne/' -e '^LeanBridge/Lookup/Demo\.lean$' \
      -e '^LeanBridge/Mathlib/Units\.lean/' \
  | sed -e 's/\.lean$//' -e 's|/|.|g')

lake build LeanBridge "${modules[@]}"
