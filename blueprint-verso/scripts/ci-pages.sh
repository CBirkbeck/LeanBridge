#!/usr/bin/env bash

set -euo pipefail

lake build LeanBridgeBlueprint
lake env lean --run LeanBridgeBlueprintMain.lean --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
