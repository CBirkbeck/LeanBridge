import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.LinearAlgebra.IntegralLattice.Examples
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume

/-!
# Conventions for the discriminant of an integral lattice

The LMFDB's discriminant `D` of an integral lattice `L` of rank `n` is the determinant of a Gram
matrix of `L`, Tau Ceti's `TauCeti.IntegralLattice.determinant`. Tau Ceti's
`TauCeti.IntegralLattice.discriminant` is `|D|`, the LMFDB's absolute discriminant. This file names
the other conventions of the literature.

## Main definitions

* `TauCeti.IntegralLattice.wittDiscriminant` (LMFDB `lattice.discriminant`):
  `(-1) ^ (n choose 2) D`.
* `TauCeti.IntegralLattice.geometricDiscriminant` (LMFDB `lattice.discriminant`): `√|D|`.
* `TauCeti.IntegralLattice.quadraticDiscriminant` (LMFDB `lattice.discriminant`): `2 ^ (-n) D`.
* `TauCeti.IntegralLattice.halfDiscriminant` (LMFDB `lattice.discriminant`): `2 ^ (-n) D` for even
  `n` and `2 ^ (-n-1) D` for odd `n`.
* `TauCeti.IntegralLattice.twoAdicUnitDiscriminant` (LMFDB `lattice.discriminant`):
  `2 ^ (-v₂(D)) D mod 8`.

## Main results

* `TauCeti.IntegralLattice.wittDiscriminant_hyperbolicPlane`: the Witt discriminant of the
  hyperbolic plane is `1`.
-/

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The **Witt discriminant** (LMFDB `lattice.discriminant`) `(-1) ^ (n choose 2) D` of an integral
lattice of rank `n` and discriminant `D` (Tau Ceti's `TauCeti.IntegralLattice.determinant`),
the convention of Milnor–Husemoller and Lam, for which the hyperbolic plane has Witt discriminant
`1`. -/
noncomputable def wittDiscriminant : ℤ :=
  (-1) ^ (finrank ℚ V).choose 2 * L.determinant

/-- The **geometric discriminant** (LMFDB `lattice.discriminant`) `√|D|` of an integral lattice of
discriminant `D`, the convention of Borevich–Shafarevich. For a positive definite lattice it is the
covolume of any realisation of the lattice in Euclidean space
(`TauCeti.IntegralLattice.covolume_range_eq_sqrt_discriminant`). -/
noncomputable def geometricDiscriminant : ℝ :=
  √(L.discriminant : ℝ)

/-- The **quadratic discriminant** (LMFDB `lattice.discriminant`) `2 ^ (-n) D` of an integral
lattice of rank `n` and discriminant `D`, the convention of Dickson and Serre, for which the
quadratic form is `Q(v) = ⟪v, v⟫ / 2`. -/
noncomputable def quadraticDiscriminant : ℚ :=
  L.determinant / 2 ^ finrank ℚ V

open scoped Classical in
/-- The **half discriminant** (LMFDB `lattice.discriminant`) of an integral lattice of rank `n` and
discriminant `D`: `2 ^ (-n) D` when `n` is even and `2 ^ (-n-1) D` when `n` is odd, the convention
of Voight and Milnor–Husemoller. -/
noncomputable def halfDiscriminant : ℚ :=
  if Even (finrank ℚ V) then L.determinant / 2 ^ finrank ℚ V
  else L.determinant / 2 ^ (finrank ℚ V + 1)

/-- The **2-adic unit discriminant** (LMFDB `lattice.discriminant`) `2 ^ (-v₂(D)) D mod 8` of an
integral lattice of discriminant `D`, the odd part of `D` modulo `8`, the convention of O'Meara and
Earnest–Hsia. For a degenerate lattice, `D = 0` and the value is `0`. -/
noncomputable def twoAdicUnitDiscriminant : ZMod 8 :=
  (L.determinant / 2 ^ padicValInt 2 L.determinant : ℤ)

/-- **The Witt discriminant of the hyperbolic plane is `1`.** -/
lemma wittDiscriminant_hyperbolicPlane : hyperbolicPlane.wittDiscriminant = 1 := by
  rw [wittDiscriminant, hyperbolicPlane_determinant, finrank_fin_fun]
  rfl

end TauCeti.IntegralLattice
