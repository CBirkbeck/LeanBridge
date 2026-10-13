/-
Copyright (c) 2024 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.ClassGroupProject
import LeanBridge.IdealArithmetic.DedekindProject
import LeanBridge.IdealArithmetic.IdealArithmetic

/-!
# Certifying invariants of number fields

This is the `IdealArithmetic` library of
[CertifyingInvariantsNF](https://github.com/alainchmt/CertifyingInvariantsNF) by Alain Chavarri
Villarello, copied into LeanBridge from Chris Birkbeck's fork
[CBirkbeck/CertifyingInvariantsNF](https://github.com/CBirkbeck/CertifyingInvariantsNF) at commit
`7ce8d6e` (branch `galois-v431-bump`), so that it is bumped together with the rest of the project.
Besides certifying the ring of integers of a number field, it certifies the discriminant, the
signature, the structure of the class group and the class number, generators of the units modulo
`p`-th powers, and Galois groups.

Authors:
* Alain Chavarri Villarello wrote the library.
* Its `DedekindProject` part comes from
  [RingOfIntegersProject](https://github.com/alainchmt/RingOfIntegersProject), the formalization
  accompanying "Certifying rings of integers in number fields" (CPP 2025) by Anne Baanen, Alain
  Chavarri Villarello and Sander R. Dahmen.
* Chris Birkbeck added the Galois-group certification library, `LeanBridge.IdealArithmetic.Galois`.

Each file records its authors in its copyright header.

Its polynomial-list utilities are shared with the rest of LeanBridge and live in
`LeanBridge.ForMathlib`: `LeanBridge.ForMathlib.Algebra.Polynomial.PolynomialsAsLists`,
`LeanBridge.ForMathlib.FieldTheory.Finite.IrreduciblePolynomialZModp` and
`LeanBridge.ForMathlib.RingTheory.Polynomial.BrillhartIrreducibilityTest`.

This module imports the general machinery. The worked examples are in
`LeanBridge.IdealArithmetic.Examples` and `LeanBridge.IdealArithmetic.Galois.Examples`.
-/
