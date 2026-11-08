import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.QuotientExistence
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# Cyclic trigonal curves through quotient curves

An algebraic curve `X` over a field `K` is cyclic trigonal (LMFDB `ag.cyclic_trigonal`) if its
automorphism group has a subgroup `H` of order three such that the quotient curve `X / H` is
isomorphic to the projective line `ℙ¹_K`; a generator of such a subgroup `H` is a trigonal
automorphism. This file states these definitions literally: the automorphisms of `X` are its
automorphisms as a scheme over `K` (LMFDB `g2c.aut_grp`), the quotient curve `X / H` is LeanBridge's
`AlgebraicGeometry.Scheme.IsQuotientCurve` (LMFDB `ag.quotient_curve`), which every algebraic curve
has by every finite group of automorphisms (`AlgebraicGeometry.Scheme.exists_isQuotientCurve`) and
which is unique up to unique isomorphism, and `ℙ¹_K` is Tau Ceti's projective line
`TauCeti.AlgebraicGeometry.projectiveLine K`, as a scheme over `K`.

This replaces the function-field model `AlgebraicGeometry.Scheme.IsCyclicTrigonalCurveOver` of
`LeanBridge.ForMathlib.AlgebraicGeometry.Curve.CyclicTrigonal`, which reads the automorphisms and
the quotient off the function field and so agrees with the knowl only for smooth proper curves: for
the affine line `𝔸¹` over a field with a primitive cube root of unity `ζ`, the subgroup generated
by `x ↦ ζx` has the rational function field `K(x³)` as fixed field, while the quotient curve
`𝔸¹ / H ≅ 𝔸¹` is not `ℙ¹`.

Since quotient curves are unique up to isomorphism, it does not matter which quotient curve of `X`
by `H` is compared with `ℙ¹_K` (`AlgebraicGeometry.Scheme.isCyclicTrigonalSubgroup_iff_forall`).

## Main definitions

* `AlgebraicGeometry.Scheme.projectiveLineOver`: the projective line `ℙ¹_K`, as a scheme over `K`.
* `AlgebraicGeometry.Scheme.IsCyclicTrigonalSubgroup` (LMFDB `ag.cyclic_trigonal`): a subgroup of
  order three of the automorphism group with quotient curve isomorphic to `ℙ¹_K`.
* `AlgebraicGeometry.Scheme.IsCyclicTrigonalCurve` (LMFDB `ag.cyclic_trigonal`).
* `AlgebraicGeometry.Scheme.IsTrigonalAutomorphism` (LMFDB `ag.cyclic_trigonal`).

## Main results

* `AlgebraicGeometry.Scheme.isCyclicTrigonalSubgroup_iff_forall`: a subgroup of order three is
  cyclic trigonal if and only if every quotient curve of `X` by it is isomorphic to `ℙ¹_K`.
* `AlgebraicGeometry.Scheme.IsTrigonalAutomorphism.orderOf_eq_three`: a trigonal automorphism has
  order three.
* `AlgebraicGeometry.Scheme.isCyclicTrigonalCurve_iff_exists_isTrigonalAutomorphism`: a curve is
  cyclic trigonal if and only if it has a trigonal automorphism.
-/

namespace AlgebraicGeometry.Scheme

open CategoryTheory

universe u

variable {K : Type u} [Field K] {X : Over (Spec (.of K))} {H : Subgroup (Aut X)}

variable (K) in
open TauCeti AlgebraicGeometry in
/-- The **projective line** `ℙ¹_K` over a field `K`, Tau Ceti's `projectiveLine K`, as a scheme
over `K`. -/
noncomputable abbrev projectiveLineOver : Over (Spec (.of K)) :=
  (projectiveLine K).asOver (Spec (.of K))

variable (H) in
/-- A subgroup `H` of the automorphism group of an algebraic curve `X` over `K` is a **cyclic
trigonal subgroup** (LMFDB `ag.cyclic_trigonal`) if it has order three and the quotient curve
`X / H` is isomorphic to `ℙ¹_K` over `K`: some quotient curve `π : X ⟶ Y` of `X` by `H` has
`Y ≅ ℙ¹_K`, equivalently every one has. -/
def IsCyclicTrigonalSubgroup : Prop :=
  Nat.card H = 3 ∧ ∃ (Y : Over (Spec (.of K))) (π : X ⟶ Y), IsQuotientCurve H π ∧
    Nonempty (Y ≅ projectiveLineOver K)

variable (X) in
/-- An algebraic curve `X` over `K` is a **cyclic trigonal curve** (LMFDB `ag.cyclic_trigonal`) if
some subgroup `H` of order three of its automorphism group has quotient curve `X / H` isomorphic to
`ℙ¹_K`. -/
def IsCyclicTrigonalCurve : Prop :=
  ∃ H : Subgroup (Aut X), IsCyclicTrigonalSubgroup H

/-- An automorphism `σ` of an algebraic curve `X` over `K` is a **trigonal automorphism** (LMFDB
`ag.cyclic_trigonal`) if it generates a subgroup `H` of order three of the automorphism group with
quotient curve `X / H` isomorphic to `ℙ¹_K`. -/
def IsTrigonalAutomorphism (σ : Aut X) : Prop :=
  IsCyclicTrigonalSubgroup (Subgroup.zpowers σ)

lemma IsCyclicTrigonalSubgroup.isAlgebraicCurveOver (hH : IsCyclicTrigonalSubgroup H) :
    X.left.IsAlgebraicCurveOver K :=
  hH.2.elim fun _ ⟨_, hπ, _⟩ ↦ hπ.isAlgebraicCurveOver_left

lemma IsCyclicTrigonalCurve.isAlgebraicCurveOver (hX : IsCyclicTrigonalCurve X) :
    X.left.IsAlgebraicCurveOver K :=
  hX.elim fun _ hH ↦ hH.isAlgebraicCurveOver

/-- **A subgroup of order three is cyclic trigonal if and only if every quotient curve by it is
isomorphic to `ℙ¹_K`**: the quotient curve exists and is unique up to isomorphism. -/
lemma isCyclicTrigonalSubgroup_iff_forall [X.left.IsAlgebraicCurveOver K] :
    IsCyclicTrigonalSubgroup H ↔ Nat.card H = 3 ∧ ∀ (Y : Over (Spec (.of K))) (π : X ⟶ Y),
      IsQuotientCurve H π → Nonempty (Y ≅ projectiveLineOver K) := by
  refine ⟨fun ⟨h₃, Y, π, hπ, ⟨e⟩⟩ ↦ ⟨h₃, fun Y' π' hπ' ↦ ⟨hπ'.uniqueUpToIso hπ ≪≫ e⟩⟩,
    fun ⟨h₃, h⟩ ↦ ⟨h₃, ?_⟩⟩
  have : Finite H := Nat.finite_of_card_ne_zero (h₃ ▸ three_ne_zero)
  rcases exists_isQuotientCurve H with ⟨Y, π, hπ⟩
  exact ⟨Y, π, hπ, h Y π hπ⟩

/-- **A trigonal automorphism has order three.** -/
lemma IsTrigonalAutomorphism.orderOf_eq_three {σ : Aut X} (hσ : IsTrigonalAutomorphism σ) :
    orderOf σ = 3 :=
  (Nat.card_zpowers σ).symm.trans hσ.1

/-- **An algebraic curve is cyclic trigonal if and only if it has a trigonal automorphism**: a group
of order three is cyclic, generated by any of its elements other than the identity. -/
lemma isCyclicTrigonalCurve_iff_exists_isTrigonalAutomorphism :
    IsCyclicTrigonalCurve X ↔ ∃ σ : Aut X, IsTrigonalAutomorphism σ := by
  refine ⟨fun ⟨H, hH⟩ ↦ ?_, fun ⟨σ, hσ⟩ ↦ ⟨_, hσ⟩⟩
  have : Fact (Nat.card H).Prime := ⟨hH.1 ▸ Nat.prime_three⟩
  rcases (isCyclic_of_prime_card rfl).exists_generator (α := H) with ⟨σ, hσ⟩
  have he : Subgroup.zpowers (σ : Aut X) = H := by
    rw [← H.subtype_apply, ← MonoidHom.map_zpowers, (Subgroup.eq_top_iff' _).mpr hσ,
      ← MonoidHom.range_eq_map, H.range_subtype]
  exact ⟨σ, (congrArg IsCyclicTrigonalSubgroup he).mpr hH⟩

end AlgebraicGeometry.Scheme
