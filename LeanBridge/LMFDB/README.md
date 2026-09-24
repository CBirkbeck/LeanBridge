# LMFDB

LMFDB-specific material, as opposed to the general declarations in `LeanBridge/ForMathlib/`:

* `ModularForms/`: q-expansion certificates for level-1 LMFDB newforms (`LevelOne/` is generated
  by `scripts/lmfdb_qexp_to_e4e6_v3.sage`) and examples of the q-expansion tools.
* `NumberFields/`: irreducibility certificates for LMFDB number-field polynomials, written by
  `IrreducibilityLeanProofWriter.sage`.
* `Tactic/`: commands that query the LMFDB (via the Python scripts here) and generate the
  certificates above.
