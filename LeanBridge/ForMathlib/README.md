# ForMathlib

Declarations that belong in Mathlib, laid out as Mathlib's own directories so that each file names
the Mathlib file it would be upstreamed to (for example `AlgebraicGeometry/EllipticCurve/` for
Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/`).

LMFDB-specific material (certificates, generated files, examples and the tools that query the
LMFDB) lives in `LeanBridge/LMFDB/` instead.

Definitions that Tau Ceti already provides are not duplicated here: `LeanBridge.lean` imports
Tau Ceti's versions and lists which LMFDB knowl each one formalizes.
