/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.RingTheory.AdjoinRoot

/-!
# Galois groups of number fields — definitions and scaffolding

Scaffolding for certifying the Galois group of a number field `K = ℚ[x]/(f)`, viewed via
`Polynomial.Gal f` acting on the roots through `Polynomial.Gal.galActionHom`.
See `docs/superpowers/specs/2026-06-30-galois-group-certificates-design.md` and
`.mathlib-quality/decomposition.md` (Result R1).
-/

namespace IdealArithmetic.Galois

open Polynomial

variable {F : Type*} [Field F]

/-- The defining polynomial splits over its own splitting field — packaged as the `Fact`
that `Polynomial.Gal.galActionHom` and friends require at `E = p.SplittingField`. -/
instance factSplitsSplittingField (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
  ⟨IsSplittingField.splits p.SplittingField p⟩

open scoped Classical in
/-- **F1.** The sign character of the Galois group of a polynomial: the sign of the
permutation of the roots induced by a Galois automorphism. Source: composite of
`Equiv.Perm.sign` and `Polynomial.Gal.galActionHom`. -/
noncomputable def signHom (p : F[X]) : p.Gal →* ℤˣ :=
  (Equiv.Perm.sign).comp (Polynomial.Gal.galActionHom p p.SplittingField)

end IdealArithmetic.Galois
