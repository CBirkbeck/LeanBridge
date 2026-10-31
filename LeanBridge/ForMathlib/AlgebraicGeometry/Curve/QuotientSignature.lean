import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.RegularQuotient
import LeanBridge.ForMathlib.FieldTheory.FunctionField.AutomorphismSignature
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# The signature of a finite group of automorphisms of a regular proper curve

The signature `[g₀; m₁, …, m_r]` (LMFDB `curve.highergenus.aut.signature`) of a finite group `H`
of automorphisms of a regular proper curve `X` over `k`, such as a compact Riemann surface when
`k = ℂ`, is the signature `Subgroup.signature` of `H` acting on the function field `k(X)`: `g₀` is
the genus of the quotient curve `X / H` (LMFDB `curve.highergenus.aut.quotientgenus`), whose
function field is the fixed field `k(X)^H`, and the periods `m_i` are the ramification indices of
the branch places of `k(X) / k(X)^H`, the points of `X / H` over which the projection `X ⟶ X / H`
ramifies.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.signature` (LMFDB
  `curve.highergenus.aut.signature`): the signature of a finite group of automorphisms of a regular
  proper curve.

## Main results

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.autToAlgEquiv_injective`: an automorphism of a
  regular proper curve is determined by its action on the function field.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.genus_quotient`: `g₀` is the genus of the
  quotient curve `X / H`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.two_mul_genus_sub_two_eq`: the Riemann–Hurwitz
  formula `2g - 2 = |H| (2g₀ - 2 + ∑ (1 - 1/m_i))` over an algebraically closed field of
  characteristic zero.
-/

open CategoryTheory AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.RegularProperCurveCat

variable {k : Type*} [Field k] {X : RegularProperCurveCat k} (H : Subgroup (Aut X)) [Finite H]

/-- **An automorphism of a regular proper curve is determined by its action on the function
field**, by the anti-equivalence between regular proper curves and function fields. -/
lemma autToAlgEquiv_injective : Function.Injective (autToAlgEquiv : Aut X →* _) :=
  fun _ _ h ↦ Aut.ext <| Iso.ext <| (Iso.inv_eq_inv _ _).mp <| functionFieldAlgHom_injective
    (congrArg AlgEquiv.toAlgHom h)

/-- The **signature** `[g₀; m₁, …, m_r]` (LMFDB `curve.highergenus.aut.signature`) of a finite
group `H` of automorphisms of a regular proper curve `X` over `k`, such as a compact Riemann surface
when `k = ℂ`: the signature `Subgroup.signature` of `H` acting on the function field `k(X)`, made of
the genus `g₀` of the quotient curve `X / H` (`genus_quotient`) and the ramification indices
`m₁ ≤ ⋯ ≤ m_r` of the branch points of the projection `X ⟶ X / H`. -/
noncomputable def signature : ℕ × Multiset ℕ :=
  (functionFieldSubgroup H).signature

/-- **The first entry `g₀` of the signature is the genus of the quotient curve** `X / H` (LMFDB
`curve.highergenus.aut.quotientgenus`). -/
lemma genus_quotient : genus k (quotient H).toScheme.functionField = (signature H).1 :=
  (genus_eq_of_ringEquiv (RingEquiv.refl k) (quotientFunctionFieldEquiv H).toRingEquiv
    (quotientFunctionFieldEquiv H).commutes).symm

variable [IsAlgClosed k] [CharZero k]

/-- **The Riemann–Hurwitz formula in terms of the signature**: over an algebraically closed field
of characteristic zero, such as `ℂ`, if `X` has genus `g` and `H` has signature
`[g₀; m₁, …, m_r]`, then `2g - 2 = |H| (2g₀ - 2 + ∑ (1 - 1/m_i))`. -/
lemma two_mul_genus_sub_two_eq : 2 * (genus k X.toScheme.functionField : ℚ) - 2 = Nat.card H *
    (2 * (signature H).1 - 2 + ((signature H).2.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum) := by
  rw [← Subgroup.card_map_of_injective autToAlgEquiv_injective]
  exact (functionFieldSubgroup H).two_mul_genus_sub_two_eq IsCurveOver.isFunctionField

end TauCeti.AlgebraicGeometry.RegularProperCurveCat
