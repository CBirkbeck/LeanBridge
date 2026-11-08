import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.CyclicTrigonalQuotient
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.ProjectiveLineCurve
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.QuotientSignature
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.RegularQuotientIsQuotientCurve
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
import TauCeti.FieldTheory.Galois.FixedField

/-!
# The projective line is a cyclic trigonal curve

Over a field `K` with a primitive cube root of unity `ζ`, the projective line `ℙ¹_K` is a cyclic
trigonal curve (LMFDB `ag.cyclic_trigonal`, `AlgebraicGeometry.Scheme.IsCyclicTrigonalCurve`): the
automorphism `x ↦ ζx` generates a subgroup `H` of order three of its automorphism group whose
quotient curve `ℙ¹_K / H` is isomorphic to `ℙ¹_K`, through `x ↦ x³`. This is a concrete instance of
the definition.

The automorphism `x ↦ ζx` of the rational function field `K(x)` has order three and fixed field
`K(x³)`: the fixed field contains `x³`, and both have degree three under `K(x)` (Tau Ceti's
`IntermediateField.finrank_fixedField_eq_natCard` and Mathlib's `RatFunc.finrank_eq_max_natDegree`),
while `K(x³) ≅ K(x)` since `x³` is transcendental. Through Tau Ceti's anti-equivalence between
regular proper curves and function fields, `x ↦ ζx` comes from an automorphism `σ` of `ℙ¹_K`, and
the quotient of `ℙ¹_K` by `⟨σ⟩`, the regular proper curve with function field
`K(x)^⟨σ⟩ = K(x³)` (`TauCeti.AlgebraicGeometry.RegularProperCurveCat.quotient`), is a quotient curve
(`TauCeti.AlgebraicGeometry.RegularProperCurveCat.isQuotientCurve_toQuotient`) isomorphic to
`ℙ¹_K`, since `ℙ¹_K` is a geometrically integral regular proper curve.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.isoOfAlgEquiv`: the isomorphism of regular
  proper curves induced by an isomorphism of their function fields.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.autOfAlgEquiv`: the automorphism of a regular
  proper curve induced by an automorphism of its function field.
* `RatFunc.smulXAlgEquiv`: the automorphism `x ↦ ζx` of `K(x)`.

## Main results

* `RatFunc.fixedField_zpowers_smulXAlgEquiv`: for a primitive cube root of unity `ζ`, the fixed
  field of `x ↦ ζx` is `K(x³)`.
* `AlgebraicGeometry.Scheme.isCyclicTrigonalCurve_projectiveLineOver` (LMFDB
  `ag.cyclic_trigonal`): over a field with a primitive cube root of unity, `ℙ¹` is a cyclic trigonal
  curve.
* `AlgebraicGeometry.Scheme.isCyclicTrigonalCurve_projectiveLineOver_zmod_seven`: in particular
  `ℙ¹` over `𝔽₇` is a cyclic trigonal curve.
-/

open CategoryTheory IntermediateField

open scoped Polynomial

universe u

namespace TauCeti.AlgebraicGeometry.RegularProperCurveCat

variable {k : Type u} [Field k] {X Y : RegularProperCurveCat k}

/-- The **isomorphism of regular proper curves** `X ≅ Y` induced by a `k`-isomorphism
`e : k(Y) ≃ k(X)` of their function fields, through Tau Ceti's anti-equivalence between regular
proper curves and algebraic function fields. -/
noncomputable def isoOfAlgEquiv (e : Y.toScheme.functionField ≃ₐ[k] X.toScheme.functionField) :
    X ≅ Y where
  hom := homOfAlgHom e.toAlgHom
  inv := homOfAlgHom e.symm.toAlgHom
  hom_inv_id := functionFieldAlgHom_injective <| by
    beta_reduce
    rw [functionFieldAlgHom_comp_hom, functionFieldAlgHom_homOfAlgHom,
      functionFieldAlgHom_homOfAlgHom, functionFieldAlgHom_id_hom, AlgEquiv.comp_symm]
  inv_hom_id := functionFieldAlgHom_injective <| by
    beta_reduce
    rw [functionFieldAlgHom_comp_hom, functionFieldAlgHom_homOfAlgHom,
      functionFieldAlgHom_homOfAlgHom, functionFieldAlgHom_id_hom, AlgEquiv.symm_comp]

/-- The **automorphism of a regular proper curve** `X` over `k` acting on its function field
`k(X)` by a given `k`-automorphism `e`, through
`TauCeti.AlgebraicGeometry.RegularProperCurveCat.autToAlgEquiv`. -/
noncomputable def autOfAlgEquiv (e : X.toScheme.functionField ≃ₐ[k] X.toScheme.functionField) :
    Aut X :=
  .of (isoOfAlgEquiv e.symm)

lemma autToAlgEquiv_autOfAlgEquiv (e : X.toScheme.functionField ≃ₐ[k] X.toScheme.functionField) :
    autToAlgEquiv (autOfAlgEquiv e) = e := by
  ext a
  rw [autToAlgEquiv_apply]
  exact DFunLike.congr_fun (functionFieldAlgHom_homOfAlgHom e.symm.symm.toAlgHom) a

end TauCeti.AlgebraicGeometry.RegularProperCurveCat

namespace RatFunc

variable {K : Type u} [Field K] {ζ : K}

/-- The automorphism `x ↦ ζx` of the rational function field `K(x)` over `K`, for `ζ ≠ 0`: the
automorphism of the fraction field induced by the automorphism `p(x) ↦ p(ζx)` of `K[x]`. -/
noncomputable def smulXAlgEquiv (hζ₀ : ζ ≠ 0) : RatFunc K ≃ₐ[K] RatFunc K :=
  letI : Invertible ζ := invertibleOfNonzero hζ₀
  IsFractionRing.fieldEquivOfAlgEquivHom K (RatFunc K) (Polynomial.algEquivCMulXAddC ζ 0)

lemma smulXAlgEquiv_X (hζ₀ : ζ ≠ 0) : smulXAlgEquiv hζ₀ X = C ζ * X := by
  rw [smulXAlgEquiv, IsFractionRing.fieldEquivOfAlgEquivHom_apply, ← algebraMap_X,
    IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
  simp

variable (hζ : IsPrimitiveRoot ζ 3)

lemma orderOf_smulXAlgEquiv : orderOf (smulXAlgEquiv (hζ.ne_zero three_ne_zero)) = 3 := by
  let _ : Invertible ζ := invertibleOfNonzero (hζ.ne_zero three_ne_zero)
  rw [smulXAlgEquiv, orderOf_injective _ (IsFractionRing.fieldEquivOfAlgEquivHom_injective K
    K[X] K (RatFunc K))]
  refine orderOf_eq_prime ?_ fun h ↦ hζ.ne_one (by norm_num) ?_
  · refine AlgEquiv.coe_toAlgHom_injective (Polynomial.algHom_ext ?_)
    simp [← mul_assoc, ← pow_three', ← map_pow, hζ.pow_eq_one]
  · have h₁ : (Polynomial.algEquivCMulXAddC ζ 0 Polynomial.X).coeff 1 =
        (Polynomial.X : K[X]).coeff 1 := by
      rw [h, AlgEquiv.one_apply]
    simpa using h₁

/-- **The fixed field of `x ↦ ζx` is `K(x³)`** for a primitive cube root of unity `ζ`: it contains
`x³`, and both have degree three under `K(x)`. -/
lemma fixedField_zpowers_smulXAlgEquiv : fixedField
    (Subgroup.zpowers (smulXAlgEquiv (hζ.ne_zero three_ne_zero))) =
      adjoin K {(X : RatFunc K) ^ 3} := by
  have hfin : Finite (Subgroup.zpowers (smulXAlgEquiv (hζ.ne_zero three_ne_zero))) :=
    Nat.finite_of_card_ne_zero <|
      ne_of_eq_of_ne ((Nat.card_zpowers _).trans (orderOf_smulXAlgEquiv hζ)) three_ne_zero
  have hX : (X : RatFunc K) ^ 3 ∈ fixedField
      (Subgroup.zpowers (smulXAlgEquiv (hζ.ne_zero three_ne_zero))) := by
    rw [mem_fixedField_zpowers_iff, map_pow, smulXAlgEquiv_X, mul_pow, ← map_pow, hζ.pow_eq_one,
      map_one, one_mul]
  have h₁ : Module.finrank (adjoin K {(X : RatFunc K) ^ 3}) (RatFunc K) = 3 := by
    have h : (X : RatFunc K) ^ 3 = algebraMap K[X] (RatFunc K) (Polynomial.X ^ 3) := by
      rw [map_pow, algebraMap_X]
    rw [finrank_eq_max_natDegree, h, num_algebraMap, denom_algebraMap, Polynomial.natDegree_X_pow,
      Polynomial.natDegree_one]
    rfl
  have h₂ : Module.finrank (fixedField (Subgroup.zpowers
      (smulXAlgEquiv (hζ.ne_zero three_ne_zero)))) (RatFunc K) = 3 := by
    rw [finrank_fixedField_eq_natCard, Nat.card_zpowers, orderOf_smulXAlgEquiv hζ]
  have : FiniteDimensional (adjoin K {(X : RatFunc K) ^ 3}) (RatFunc K) :=
    Module.finite_of_finrank_pos (lt_of_lt_of_eq three_pos h₁.symm)
  exact (eq_of_le_of_finrank_eq' (adjoin_simple_le_iff.mpr hX) (h₁.trans h₂.symm)).symm

end RatFunc

namespace AlgebraicGeometry.Scheme

open TauCeti AlgebraicGeometry RegularProperCurveCat

variable (K : Type u) [Field K] {ζ : K}

/-- **Over a field with a primitive cube root of unity `ζ`, the projective line `ℙ¹` is a cyclic
trigonal curve** (LMFDB `ag.cyclic_trigonal`): the automorphism `x ↦ ζx` of `ℙ¹` generates a
subgroup of order three of its automorphism group whose quotient curve is isomorphic to `ℙ¹`. -/
lemma isCyclicTrigonalCurve_projectiveLineOver (hζ : IsPrimitiveRoot ζ 3) :
    IsCyclicTrigonalCurve (projectiveLineOver K) := by
  let X₀ : RegularProperCurveCat K := .of (projectiveLine K)
  let φ : X₀.toScheme.functionField ≃ₐ[K] RatFunc K := projectiveLine.functionFieldEquiv K
  let τ : RatFunc K ≃ₐ[K] RatFunc K := RatFunc.smulXAlgEquiv (hζ.ne_zero three_ne_zero)
  let τ' : X₀.toScheme.functionField ≃ₐ[K] X₀.toScheme.functionField :=
    AlgEquiv.autCongr φ.symm τ
  let σ : Aut X₀ := autOfAlgEquiv τ'
  have hσ : orderOf σ = 3 := by
    rw [← orderOf_injective _ autToAlgEquiv_injective σ, autToAlgEquiv_autOfAlgEquiv,
      MulEquiv.orderOf_eq, RatFunc.orderOf_smulXAlgEquiv hζ]
  let H : Subgroup (Aut X₀) := Subgroup.zpowers σ
  have : Finite H :=
    Nat.finite_of_card_ne_zero (ne_of_eq_of_ne ((Nat.card_zpowers σ).trans hσ) three_ne_zero)
  have hτ' (y : X₀.toScheme.functionField) : τ' y = φ.symm (τ (φ y)) :=
    rfl
  have hfix : fixedField (functionFieldSubgroup H) =
      (fixedField (Subgroup.zpowers τ)).map φ.symm.toAlgHom := by
    rw [functionFieldSubgroup, MonoidHom.map_zpowers, autToAlgEquiv_autOfAlgEquiv]
    ext y
    rw [mem_fixedField_zpowers_iff, mem_map, hτ']
    refine ⟨fun h ↦ ⟨φ y, (mem_fixedField_zpowers_iff τ _).mpr (φ.symm_apply_eq.mp h),
      φ.symm_apply_apply y⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    rw [AlgEquiv.coe_toAlgHom, φ.apply_symm_apply, (mem_fixedField_zpowers_iff τ x).mp hx]
  let e : X₀.toScheme.functionField ≃ₐ[K] (quotient H).toScheme.functionField :=
    φ.trans <| (RatFunc.algEquivOfTranscendental _
      (RatFunc.transcendental_X.pow three_pos)).trans <|
        (equivOfEq (RatFunc.fixedField_zpowers_smulXAlgEquiv hζ).symm).trans <|
          (equivMap _ φ.symm.toAlgHom).trans <| (equivOfEq hfix.symm).trans
            (quotientFunctionFieldEquiv H).symm
  refine ⟨H.map ((toOver K).mapAut X₀), ⟨?_, _, _, isQuotientCurve_toQuotient H,
    ⟨(toOver K).mapIso (isoOfAlgEquiv e)⟩⟩⟩
  exact (Subgroup.card_map_of_injective mapAut_toOver_injective).trans
    ((Nat.card_zpowers σ).trans hσ)

/-- **The projective line over `𝔽₇` is a cyclic trigonal curve** (LMFDB `ag.cyclic_trigonal`):
`2` is a primitive cube root of unity modulo `7`. -/
lemma isCyclicTrigonalCurve_projectiveLineOver_zmod_seven :
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    IsCyclicTrigonalCurve (projectiveLineOver (ZMod 7)) :=
  have h : orderOf (2 : ZMod 7) = 3 := orderOf_eq_prime (by decide) (by decide)
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  isCyclicTrigonalCurve_projectiveLineOver (ZMod 7) (h ▸ IsPrimitiveRoot.orderOf 2)

end AlgebraicGeometry.Scheme
