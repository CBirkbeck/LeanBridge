import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Levels of Bianchi modular forms

The level of a Bianchi modular form over an imaginary quadratic field `K` is a congruence subgroup
of `GL₂(𝒪_K)`, most commonly `Γ₀(𝔑) = {(a, b; c, d) ∈ GL₂(𝒪_K) | c ∈ 𝔑}` for an integral ideal `𝔑`
of `𝒪_K`, whose norm is the level norm. Its intersection with `SL₂(𝒪_K)` is the corresponding
`SL₂`-level. Both are defined here over any commutative ring.

## Main definitions

* `Ideal.gamma0GL` (LMFDB `mf.bianchi.level`): the `GL₂`-level `Γ₀(𝔑)`.
* `Ideal.gamma0SL` (LMFDB `mf.bianchi.level`): the `SL₂`-level `Γ₀(𝔑) ∩ SL₂`.

## Main results

* `Ideal.mem_gamma0SL`: an element of `SL₂` lies in the `SL₂`-level exactly when its lower-left
  entry lies in `𝔑`.
-/

open Matrix

open scoped MatrixGroups

namespace Ideal

variable {R : Type*} [CommRing R] (N : Ideal R) {g : SL(2, R)}

/-- The **level** `Γ₀(𝔑)` (LMFDB `mf.bianchi.level`) of an ideal `𝔑` of a commutative ring `R`:
the matrices `(a, b; c, d)` of `GL₂(R)` with `c ∈ 𝔑`. For `R = 𝒪_K` the ring of integers of an
imaginary quadratic field, this is the `GL₂`-level of Bianchi modular forms of level `𝔑`; the
**level norm** is `Ideal.absNorm 𝔑`. The **level label** is the LMFDB's label of the ideal `𝔑`, a
database convention that is not formalised. -/
def gamma0GL : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ N}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, mul_apply, Fin.sum_univ_two] at hg hh ⊢
    exact N.add_mem (N.mul_mem_right _ hg) (N.mul_mem_left _ hh)
  one_mem' := by simp
  inv_mem' {g} hg := by
    simpa [coe_units_inv, inv_def, adjugate_fin_two] using hg

/-- The **`SL₂`-level** `Γ₀(𝔑) ∩ SL₂(R)` (LMFDB `mf.bianchi.level`) of an ideal `𝔑` of a
commutative ring `R`: the matrices `(a, b; c, d)` of `SL₂(R)` with `c ∈ 𝔑`. Being smaller than the
`GL₂`-level `Γ₀(𝔑)`, it has larger spaces of Bianchi modular forms. -/
def gamma0SL : Subgroup SL(2, R) :=
  N.gamma0GL.comap SpecialLinearGroup.toGL

/-- **Membership in the `SL₂`-level**: `(a, b; c, d) ∈ SL₂(R)` lies in `Γ₀(𝔑) ∩ SL₂(R)` exactly
when `c ∈ 𝔑`. -/
lemma mem_gamma0SL : g ∈ N.gamma0SL ↔ g 1 0 ∈ N :=
  Iff.rfl

end Ideal
