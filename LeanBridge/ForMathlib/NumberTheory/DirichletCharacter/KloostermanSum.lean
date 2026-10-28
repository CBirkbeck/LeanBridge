import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.GaussSum

/-!
# Kloosterman sums

The Kloosterman sum of a multiplicative character `χ` and an additive character `ψ` of a finite
commutative ring `R` at `a, b ∈ R` is `∑_{r ∈ Rˣ} χ(r) ψ(a r + b r⁻¹)`. For a Dirichlet character
`χ` of modulus `q` and the standard additive character `ZMod.stdAddChar` of `ZMod q`, which sends
`r` to `ζ ^ r` with `ζ = exp (2 π i / q)`, it is the Kloosterman sum `K(a, b, χ)` of the LMFDB. When
`b = 0` it is a Gauss sum.

## Main definitions

* `kloostermanSum` (LMFDB `character.dirichlet.kloosterman_sum`): the Kloosterman sum of a
  multiplicative and an additive character.

## Main results

* `DirichletCharacter.kloostermanSum_stdAddChar`: for a Dirichlet character `χ` of modulus `q`, the
  Kloosterman sum with the standard additive character is
  `K(a, b, χ) = ∑_{r ∈ (ℤ/qℤ)ˣ} χ(r) ζ ^ (a r + b r⁻¹)`, where `ζ = exp (2 π i / q)`.
* `kloostermanSum_zero_right`: the Kloosterman sum at `b = 0` is the Gauss sum of `χ` and
  `ψ.mulShift a`.
-/

open AddChar Complex MulChar
open scoped Real

section

variable {R R' : Type*} [CommRing R] [Fintype R] [DecidableEq R] [CommRing R'] (χ : MulChar R R')
  (ψ : AddChar R R') (a b : R)

/-- The **Kloosterman sum** `∑_{r ∈ Rˣ} χ(r) ψ(a r + b r⁻¹)` of a multiplicative character `χ` and
an additive character `ψ` of a finite commutative ring `R` at `a, b ∈ R`. For a Dirichlet character
`χ` of modulus `q` and the standard additive character `ZMod.stdAddChar` of `ZMod q`, it is the
**Kloosterman sum** `K(a, b, χ) = ∑_{r ∈ (ℤ/qℤ)ˣ} χ(r) ζ ^ (a r + b r⁻¹)` (LMFDB
`character.dirichlet.kloosterman_sum`), where `ζ = exp (2 π i / q)`
(`DirichletCharacter.kloostermanSum_stdAddChar`). The LMFDB takes `a` and `b` in `ℤ`; the sum only
depends on their residues modulo `q`, which are its arguments here. -/
def kloostermanSum : R' :=
  ∑ r : Rˣ, χ r * ψ (a * r + b * ↑r⁻¹)

/-- The Kloosterman sum at `b = 0` is the Gauss sum of `χ` and `ψ.mulShift a`. -/
lemma kloostermanSum_zero_right : kloostermanSum χ ψ a 0 = gaussSum χ (ψ.mulShift a) := by
  refine Fintype.sum_of_injective _ Units.val_injective _ _ (fun x hx ↦ ?_) fun r ↦ ?_
  · rw [map_nonunit χ fun h ↦ hx ⟨h.unit, rfl⟩, zero_mul]
  · rw [zero_mul, add_zero, mulShift_apply]

lemma kloostermanSum_inv : kloostermanSum χ⁻¹ ψ b a = kloostermanSum χ ψ a b := by
  refine Fintype.sum_equiv (Equiv.inv Rˣ) _ _ fun r ↦ ?_
  rw [χ.inv_apply, Ring.inverse_unit, Equiv.inv_apply, inv_inv, add_comm]

lemma kloostermanSum_zero_left : kloostermanSum χ ψ 0 b = gaussSum χ⁻¹ (ψ.mulShift b) := by
  rw [← kloostermanSum_inv, kloostermanSum_zero_right]

end

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b : ZMod q)

/-- For a Dirichlet character `χ` of modulus `q`, the Kloosterman sum with the standard additive
character is `K(a, b, χ) = ∑_{r ∈ (ℤ/qℤ)ˣ} χ(r) ζ ^ (a r + b r⁻¹)`, where `ζ = exp (2 π i / q)` and
the exponent is the residue `a r + b r⁻¹` modulo `q`, represented in `[0, q)`. -/
lemma kloostermanSum_stdAddChar : kloostermanSum χ ZMod.stdAddChar a b =
    ∑ r : (ZMod q)ˣ, χ r * cexp (2 * π * I / q) ^ (a * r + b * ↑r⁻¹).val := by
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← exp_nat_mul]
  congr 2
  ring1

end DirichletCharacter
