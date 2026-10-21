# LMFDB

LMFDB-specific material, as opposed to the general declarations in `LeanBridge/ForMathlib/`:

* `EllipticCurves/`: worked examples about specific curves: the torsion of 11.a3 computed by
  reduction, the Frey curve of `3 + 5 = 8` as a global minimal model, and point counts and the
  Hasse bound over small prime fields.
* `LocalFields/`: worked examples of ramification invariants of `p`-adic fields: `ℚ₂(√5)` and the
  family `ℚ_p(p^{1/e})`.
* `ModularForms/`: q-expansion certificates for level-1 LMFDB newforms (`LevelOne/` is generated
  by `scripts/lmfdb_qexp_to_e4e6_v3.sage`) and examples of the q-expansion tools.
* `NumberFields/`: irreducibility certificates for LMFDB number-field polynomials, written by
  `IrreducibilityLeanProofWriter.sage`.
* `Tactic/`: commands that query the LMFDB (via the Python scripts here) and generate the
  certificates above.
