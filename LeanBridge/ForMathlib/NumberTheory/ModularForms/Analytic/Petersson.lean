import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import TauCeti.NumberTheory.ModularForms.Petersson.Adjoint

/-!
# The Petersson scalar product of two modular forms

For modular forms `f` and `g` of weight `k` for a finite-index subgroup `Γ` of `SL₂(ℤ)`, the
LMFDB's Petersson scalar product is
`⟨f, g⟩_Γ = [SL₂(ℤ) : Γ]⁻¹ ∫_𝔉 f(z) conj(g(z)) y^k dμ`,
where `𝔉` is a fundamental domain for `Γ` and `dμ = dx dy / y²`; it exists when one of `f`, `g` is
a cusp form. Mathlib has only the integrand `UpperHalfPlane.petersson`, which conjugates the first
function, and Tau Ceti has the unnormalised pairing `CuspForm.peterssonInnerCosets` of two cusp
forms, conjugate-linear in the first argument. Here the integral is taken over the tiling of a
fundamental domain by translates of the open standard domain `𝒟ᵒ`, and shown to be the same over
every fundamental domain.

## Main definitions

* `ModularForm.peterssonScalarProduct` (LMFDB `cmf.petersson_scalar_product`).
* `ModularForm.peterssonScalarProductₛₗ`: the Petersson scalar product of a modular form and a cusp
  form, as a sesquilinear map.

## Main results

* `ModularForm.peterssonScalarProduct_eq_integral`: the Petersson scalar product is
  `[SL₂(ℤ) : Γ]⁻¹ ∫_𝔉 f(z) conj(g(z)) y^k dμ` for every fundamental domain `𝔉` of `Γ`.
* `ModularForm.integrableOn_of_isCuspForm`: the integral converges when `f` or `g` is a cusp form.
* `ModularForm.conj_peterssonScalarProduct`: Hermitian symmetry.
* `ModularForm.peterssonScalarProduct_coe_coe`: on cusp forms it is Tau Ceti's pairing, with the
  arguments swapped and divided by `[SL₂(ℤ) : Γ]`.
* `ModularForm.peterssonScalarProduct_coe_self_eq_zero`: it is positive definite on cusp forms.
-/

open MeasureTheory Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup
open scoped ComplexConjugate MatrixGroups ModularForm Pointwise

namespace ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f f' g g' : ModularForm (Γ.map (mapGL ℝ)) k) (a : ℂ)
    (c c' : CuspForm (Γ.map (mapGL ℝ)) k) {𝔉 : Set ℍ}
    (h𝔉 : IsFundamentalDomain (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) 𝔉)

/-- The **Petersson scalar product** (LMFDB `cmf.petersson_scalar_product`) of two modular forms
`f` and `g` of weight `k` for a finite-index subgroup `Γ` of `SL₂(ℤ)`:
`⟨f, g⟩_Γ = [SL₂(ℤ) : Γ]⁻¹ ∫_𝔉 f(z) conj(g(z)) y^k dμ`, where `dμ = dx dy / y²` and `𝔉` is a
fundamental domain for `Γ`, here the union of the translates `q⁻¹ 𝒟ᵒ` of the open standard domain
over the cosets `q` of `Γ·{±1}` (`peterssonScalarProduct_eq_integral` shows that any fundamental
domain gives the same value). As in the LMFDB it is linear in `f` and conjugate-linear in `g`,
the opposite of Mathlib's integrand `UpperHalfPlane.petersson` and of Tau Ceti's pairing
`CuspForm.peterssonInnerCosets`.

The integral converges when `f` or `g` is a cusp form (`integrableOn_of_isCuspForm`); otherwise
the value is that of Mathlib's Bochner integral and carries no meaning. The normalisation is the
LMFDB's `1 / [SL₂(ℤ) : Γ]`. Since `-1` acts trivially on the upper half-plane, a fundamental domain
for `Γ` is one for `Γ·{±1}`; when `-1 ∉ Γ` the index `[SL₂(ℤ) : Γ]` is twice
`[SL₂(ℤ) : Γ·{±1}]`, so that the product is then half of the volume-normalised one. -/
noncomputable def peterssonScalarProduct : ℂ :=
  (Γ.index : ℂ)⁻¹ * peterssonInner k (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, q.out⁻¹ • fdo) ⇑g ⇑f

private lemma petersson_eq (τ : ℍ) : petersson k g f τ = f τ * conj (g τ) * τ.im ^ k := by
  rw [petersson, mul_comm (conj (g τ))]

include h𝔉 in
/-- **The Petersson scalar product is an integral over any fundamental domain**: for every
fundamental domain `𝔉` of `Γ` acting on the upper half-plane,
`⟨f, g⟩_Γ = [SL₂(ℤ) : Γ]⁻¹ ∫_𝔉 f(z) conj(g(z)) y^k dμ`. -/
lemma peterssonScalarProduct_eq_integral :
    peterssonScalarProduct f g = (Γ.index : ℂ)⁻¹ * ∫ τ in 𝔉, f τ * conj (g τ) * τ.im ^ k := by
  rw [peterssonScalarProduct, peterssonInner_eq_of_isFundamentalDomain k g f
    (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ) h𝔉, peterssonInner_def]
  simp_rw [petersson_eq]

/-- **Hermitian symmetry**: `⟨g, f⟩_Γ = conj ⟨f, g⟩_Γ`. -/
lemma conj_peterssonScalarProduct :
    conj (peterssonScalarProduct f g) = peterssonScalarProduct g f := by
  rw [peterssonScalarProduct, peterssonScalarProduct, map_mul, map_inv₀, map_natCast,
    peterssonInner_conj_symm]

@[simp]
lemma peterssonScalarProduct_smul_left :
    peterssonScalarProduct (a • f) g = a * peterssonScalarProduct f g := by
  rw [peterssonScalarProduct, peterssonScalarProduct, FunLike.coe_smul, peterssonInner_smul_right,
    mul_left_comm]

@[simp]
lemma peterssonScalarProduct_smul_right :
    peterssonScalarProduct f (a • g) = conj a * peterssonScalarProduct f g := by
  rw [peterssonScalarProduct, peterssonScalarProduct, FunLike.coe_smul, peterssonInner_smul_left,
    mul_left_comm]

variable [Γ.FiniteIndex] {g} (hg : IsCuspForm g)

include h𝔉 in
/-- **The Petersson scalar product exists when one of the forms is a cusp form**: the integrand
`f(z) conj(g(z)) y^k` is then integrable over every fundamental domain of `Γ`. -/
lemma integrableOn_of_isCuspForm (h : IsCuspForm f ∨ IsCuspForm g) :
    IntegrableOn (fun τ ↦ f τ * conj (g τ) * τ.im ^ k) 𝔉 := by
  simp_rw [← petersson_eq]
  refine ((isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ).integrableOn_iff h𝔉
    (petersson_psl_smul_of_mem k g f)).mp <| integrableOn_finite_iUnion.mpr fun q ↦ ?_
  refine IntegrableOn.mono_set ?_ (Set.smul_set_mono fdo_subset_fd)
  rcases h with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact integrableOn_petersson_sl_smul_fd_right k _ g c _
  · exact integrableOn_petersson_sl_smul_fd_left k _ c f _

include hg in
lemma peterssonScalarProduct_add_left : peterssonScalarProduct (f + f') g = peterssonScalarProduct f
    g + peterssonScalarProduct f' g := by
  rw [peterssonScalarProduct, peterssonScalarProduct, peterssonScalarProduct, FunLike.coe_add,
    peterssonInner_add_right, mul_add]
  all_goals
    simp_rw [petersson_eq]
    exact integrableOn_of_isCuspForm _ (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ)
      (Or.inr hg)

include hg in
lemma peterssonScalarProduct_add_right (hg' : IsCuspForm g') : peterssonScalarProduct f (g + g') =
    peterssonScalarProduct f g + peterssonScalarProduct f g' := by
  rw [peterssonScalarProduct, peterssonScalarProduct, peterssonScalarProduct, FunLike.coe_add,
    peterssonInner_add_left, mul_add]
  all_goals
    simp_rw [petersson_eq]
    exact integrableOn_of_isCuspForm f (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ)
      (Or.inr ‹_›)

/-- **On cusp forms the Petersson scalar product is Tau Ceti's pairing**, with the arguments
swapped and divided by `[SL₂(ℤ) : Γ]`. -/
lemma peterssonScalarProduct_coe_coe : peterssonScalarProduct (c : ModularForm (Γ.map (mapGL ℝ)) k)
    c' = (Γ.index : ℂ)⁻¹ * c'.peterssonInnerCosets c := by
  rw [peterssonScalarProduct, CuspForm.peterssonInnerCosets_eq_peterssonInner]
  rfl

/-- **The Petersson scalar product is positive definite on cusp forms.** -/
lemma peterssonScalarProduct_coe_self_eq_zero :
    peterssonScalarProduct (c : ModularForm (Γ.map (mapGL ℝ)) k) c = 0 ↔ c = 0 := by
  rw [peterssonScalarProduct_coe_coe, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero,
    CuspForm.peterssonInnerCosets_self_eq_zero, or_iff_right Subgroup.index_ne_zero_of_finite]

lemma re_peterssonScalarProduct_coe_self_nonneg :
    0 ≤ (peterssonScalarProduct (c : ModularForm (Γ.map (mapGL ℝ)) k) c).re := by
  rw [peterssonScalarProduct_coe_coe, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) c.peterssonInnerCosets_self_re_nonneg

/-- The Petersson scalar product of a modular form and a cusp form, as a sesquilinear map: linear
in the modular form and conjugate-linear in the cusp form. -/
noncomputable def peterssonScalarProductₛₗ :
    ModularForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ] CuspForm (Γ.map (mapGL ℝ)) k →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f c ↦ peterssonScalarProduct f c)
    (fun f f' c ↦ peterssonScalarProduct_add_left f f' ⟨c, rfl⟩)
    (fun a f c ↦ peterssonScalarProduct_smul_left f c a)
    (fun f c c' ↦ by
      rw [← CuspForm.toModularFormₗ_eq_coe, map_add]
      exact peterssonScalarProduct_add_right f c' ⟨c, rfl⟩ ⟨c', rfl⟩)
    (fun a f c ↦ peterssonScalarProduct_smul_right f c a)

@[simp]
lemma peterssonScalarProductₛₗ_apply_apply :
    peterssonScalarProductₛₗ f c = peterssonScalarProduct f c :=
  rfl

end ModularForm
