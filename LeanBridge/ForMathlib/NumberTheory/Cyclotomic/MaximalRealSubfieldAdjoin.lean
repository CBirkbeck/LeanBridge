import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The maximal real subfield of a cyclotomic field

Let `ζ` be a primitive `n`-th root of unity in the `n`-th cyclotomic field `K = ℚ(ζ)`. The LMFDB
nickname `QzetaN+` names the maximal real subfield `ℚ(ζ)⁺` of `ℚ(ζ)`, which the knowl describes
equivalently as the field `ℚ(ζ + ζ⁻¹)` (LMFDB `nf.nickname`). The maximal real subfield is Mathlib's
`NumberField.maximalRealSubfield`, the subfield of the elements that are real under every complex
embedding.

The element `ζ + ζ⁻¹` is real under every complex embedding `φ`, as `φ(ζ)` lies on the unit circle,
so that `φ(ζ)⁻¹` is the complex conjugate of `φ(ζ)`. Conversely, an automorphism `σ` of `K` fixing
`ζ + ζ⁻¹` sends `ζ` to a root of `X² - (ζ + ζ⁻¹) X + 1 = (X - ζ)(X - ζ⁻¹)`: either `σ` is the
identity, or `σ(ζ) = ζ⁻¹` and `σ` is complex conjugation under every complex embedding, so that it
fixes the maximal real subfield. As `K` is Galois over `ℚ`, the maximal real subfield is contained
in `ℚ(ζ + ζ⁻¹)`. Tau Ceti's
`TauCeti.IsCyclotomicExtension.Rat.toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one`
identifies the same field as the fixed field of `ζ ↦ ζ⁻¹`.

## Main results

* `IsPrimitiveRoot.maximalRealSubfield_eq_adjoin_add_inv` (LMFDB `nf.nickname`): the maximal real
  subfield of `ℚ(ζ)` is `ℚ(ζ + ζ⁻¹)`.
-/

open ComplexConjugate IntermediateField NumberField

namespace IsPrimitiveRoot

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] {ζ : K}

lemma norm_apply_eq_one (hζ : IsPrimitiveRoot ζ n) (φ : K →+* ℂ) : ‖φ ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) (NeZero.ne n)

lemma add_inv_mem_maximalRealSubfield (hζ : IsPrimitiveRoot ζ n) :
    ζ + ζ⁻¹ ∈ maximalRealSubfield K := fun φ ↦ by
  rw [map_add, map_inv₀, Complex.inv_eq_conj (hζ.norm_apply_eq_one φ), Complex.star_def, map_add,
    Complex.conj_conj, add_comm]

variable [NumberField K] [IsCyclotomicExtension {n} ℚ K] in
/-- **The maximal real subfield of the cyclotomic field `ℚ(ζ)` is `ℚ(ζ + ζ⁻¹)`.** -/
lemma maximalRealSubfield_eq_adjoin_add_inv (hζ : IsPrimitiveRoot ζ n) :
    maximalRealSubfield K = ℚ⟮ζ + ζ⁻¹⟯.toSubfield := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  have hadj : Algebra.adjoin ℚ {ζ} = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · rw [mem_toSubfield, ← IsGalois.fixedField_fixingSubgroup ℚ⟮ζ + ζ⁻¹⟯, mem_fixedField_iff]
    intro σ hσ
    have hs : σ (ζ + ζ⁻¹) = ζ + ζ⁻¹ :=
      (mem_fixingSubgroup_iff _ σ).mp hσ _ <| mem_adjoin_simple_self ℚ _
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
    have hσ0 : σ ζ ≠ 0 := (map_ne_zero σ).mpr hζ0
    rw [map_add, map_inv₀] at hs
    have hroot : (σ ζ - ζ) * (σ ζ - ζ⁻¹) = 0 := by
      linear_combination σ ζ * hs + mul_inv_cancel₀ hζ0 - mul_inv_cancel₀ hσ0
    rcases mul_eq_zero.mp hroot with h | h
    · have hid : (σ : K →ₐ[ℚ] K) = AlgHom.id ℚ K :=
        AlgHom.ext_of_adjoin_eq_top hadj <| Set.eqOn_singleton.mpr <| sub_eq_zero.mp h
      simpa using DFunLike.congr_fun hid x
    · let φ : K →+* ℂ := Classical.choice inferInstance
      have hext : (φ.comp (σ : K →+* K)).toRatAlgHom = ((starRingEnd ℂ).comp φ).toRatAlgHom :=
        AlgHom.ext_of_adjoin_eq_top hadj <| Set.eqOn_singleton.mpr <| by
          simp [sub_eq_zero.mp h, ← Complex.inv_eq_conj (hζ.norm_apply_eq_one φ)]
      apply φ.injective
      rw [← hx φ, Complex.star_def]
      simpa using DFunLike.congr_fun hext x
  · have hle : ℚ⟮ζ + ζ⁻¹⟯ ≤ (maximalRealSubfield K).toIntermediateField fun r ↦
        (eq_ratCast (algebraMap ℚ K) r).symm ▸ SubfieldClass.ratCast_mem _ r :=
      adjoin_simple_le_iff.mpr hζ.add_inv_mem_maximalRealSubfield
    exact hle hx

end IsPrimitiveRoot
