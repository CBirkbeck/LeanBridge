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

The sign character of the Galois group acting on the roots is Tau Ceti's `Polynomial.Gal.sign`.
-/

namespace IdealArithmetic.Galois

open Polynomial

variable {F : Type*} [Field F]

/-- The defining polynomial splits over its own splitting field — packaged as the `Fact`
that `Polynomial.Gal.galActionHom` and friends require at `E = p.SplittingField`. It is an
instance only locally (files that need it use `attribute [local instance]`): as a global instance
it would give `p.rootSet p.SplittingField` the action `Polynomial.Gal.galAction` in addition to
Mathlib's intrinsic `Polynomial.Gal.galActionAux`, and the two are different actions. Tau Ceti's
`TauCeti.factSplitsSplittingField` is kept local for the same reason. -/
local instance factSplitsSplittingField (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
  ⟨IsSplittingField.splits p.SplittingField p⟩

end IdealArithmetic.Galois
