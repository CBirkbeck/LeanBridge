import LeanBridge.ForMathlib.Analysis.Complex.UpperHalfPlane.StripIntegral
import LeanBridge.ForMathlib.MeasureTheory.Group.FundamentalDomainUnfolding
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareCuspForm
import Mathlib.NumberTheory.ModularForms.Petersson
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Unfolding the Petersson product of a Poincaré series

Let `P` be the `n`-th Poincaré series of weight `k` and multiplier `v` on `G ≤ SL(2, ℤ)` at the
cusp `s = γ_s ∞` of width `w` (LMFDB `specialfunction.poincare`), and `f` a function with
`f ∣[k] g = v(g) f` for `g ∈ G`. With `T₁(z) = e^{2πi (n/w) γ_s⁻¹ z} j(γ_s⁻¹, z)^{-k}`, the term
of `P` at the identity, the Petersson integrand `conj(P) f y^k` is the periodisation over the
cosets `G_s \ G` of `φ = conj(T₁) f y^k`: `conj(P(z)) f(z) y^k = Σ_{G_s g} φ(g z)`, since
`φ(g z) = conj(T_g(z)) f(z) y^k` for the term `T_g` of `P` at `g`, the multiplier cancelling
against its conjugate. The function `φ` is invariant under the cusp stabiliser `G_s`.
Unfolding then gives, for any fundamental domains `D` of `G` and `F` of `G_s` (which exist when
`G` acts on `ℍ` without kernel, that is `-I ∉ G`) and `φ` integrable on `F`,
`∫_D conj(P) f y^k dμ = ∫_F conj(T₁) f y^k dμ`. When `w` is the width of the cusp, `γ_s S` with
`S = {0 ≤ Re z < w}` is a fundamental domain for `G_s`, and
`∫_{γ_s S} conj(T₁) f y^k dμ = ∫_S conj(e^{2πi n z / w}) (f ∣[k] γ_s)(z) y^k dμ`, which the
Fourier expansion `(f ∣[k] γ_s)(z) = Σ_j a_j e^{2πi j z / w}` evaluates to
`w (w / 4πn)^{k-1} Γ(k - 1) a_n` for `n ≥ 1` (Iwaniec, *Topics in classical automorphic forms*,
Proposition 3.3). This is the Petersson product `⟨P, f⟩` over a fundamental domain (Tau Ceti's
`UpperHalfPlane.peterssonInner`), linear in `f`. Hence a form with no constant term orthogonal to
every `P_m`, `m ≥ 1`, is zero; with the finite dimension of the space of cusp forms, and no
definiteness of the Petersson product, this gives that the Poincaré series span it
(`PoincareSpan.lean`).

When `-I ∈ G` (as for `Γ₀(N)`), `G` acts on `ℍ` through its image in `PSL(2, ℤ)`, and the same
results hold with fundamental domains of the images of `G` and `G_s` there: the cosets `G_s \ G`
match those of the images, since `-I` lies in `G_s`.

## Main definitions

* `ModularForm.pslCuspStabilizer`: the image of `G_s` in `PSL(2, ℤ)`.

## Main results

* `ModularForm.petersson_poincareSeries_eq_tsum`: the Petersson integrand of `P` against `f` is
  the periodisation of `φ`.
* `ModularForm.setIntegral_petersson_poincareSeries`,
  `ModularForm.setIntegral_petersson_poincareSeries_psl`: the unfolding
  `∫_D conj(P) f y^k dμ = ∫_F conj(T₁) f y^k dμ`.
* `ModularForm.setIntegral_smul_set_petersson_poincareTerm_one`: the change of variables
  `z = γ_s u` on `F = γ_s S`.
* `ModularForm.isFundamentalDomain_smul_re_mem_Ico`,
  `ModularForm.isFundamentalDomain_smul_re_mem_Ico_psl`: `γ_s S` is a fundamental domain for
  `G_s`.
* `ModularForm.setIntegral_petersson_poincareSeries_eq`,
  `ModularForm.setIntegral_petersson_poincareSeries_eq_psl`:
  `⟨P, f⟩ = w (w / 4πn)^{k-1} Γ(k - 1) a_n`.
* `ModularForm.eq_zero_of_forall_setIntegral_petersson_poincareSeries_eq_zero`,
  `ModularForm.eq_zero_of_forall_setIntegral_petersson_poincareSeries_eq_zero_psl`: a form with no
  constant term orthogonal to every `P_m`, `m ≥ 1`, is zero.
-/

open UpperHalfPlane Matrix SpecialLinearGroup ModularGroup MeasureTheory Set

open scoped MatrixGroups ComplexConjugate ModularForm Pointwise

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (v : G →* Circle) (k n : ℤ) (w m : ℕ) (z : ℍ)
    (g : G) {f : ℍ → ℂ} {D F S : Set ℍ} {t : G} {a : ℕ → ℂ} {P Q : SL(2, ℤ)}

lemma petersson_poincareTerm_one_smul (hf : f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f) :
    petersson k (fun u ↦ poincareTerm γ v k n w u 1) f ((g : SL(2, ℤ)) • z) =
      conj (poincareTerm γ v k n w z g) * f z * z.im ^ k := by
  rw [← petersson_slash_SL, hf]
  simp only [petersson, SL_slash_apply, poincareTerm_smul_mul_denom]
  rw [poincareTerm_eq_denom]
  simp only [OneMemClass.coe_one, mul_one, map_one, Circle.coe_one, Pi.smul_apply, smul_eq_mul,
    map_mul, Complex.conj_conj]
  ring1

/-- **The Petersson integrand of a Poincaré series is a periodisation** (LMFDB
`specialfunction.poincare`): if `f ∣[k] g = v(g) f` for `g ∈ G`, then
`conj(P(z)) f(z) y^k = Σ_{G_s g} φ(g z)` with `φ = conj(T₁) f y^k`, `T₁` the term of `P` at the
identity. -/
lemma petersson_poincareSeries_eq_tsum (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f) :
    petersson k (poincareSeries γ v k n w) f z =
      ∑' q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)),
        petersson k (fun u ↦ poincareTerm γ v k n w u 1) f (q.out • z) := by
  simp only [Subgroup.smul_def, petersson_poincareTerm_one_smul γ v k n w z _ (hf _)]
  rw [tsum_mul_right, tsum_mul_right, ← Complex.conj_tsum]
  rfl

/-- **Unfolding the Petersson product of a Poincaré series** (LMFDB `specialfunction.poincare`):
if `f ∣[k] g = v(g) f` for `g ∈ G` and the terms of `P` are constant on the cosets `G_s g`, then
for any fundamental domains `D` of `G` and `F` of the cusp stabiliser `G_s` (which exist only when
`-I ∉ G`, `G` then acting on `ℍ` without kernel) and `φ = conj(T₁) f y^k` integrable on `F`,
`∫_D conj(P) f y^k dμ = ∫_F φ dμ`. -/
lemma setIntegral_petersson_poincareSeries (hD : IsFundamentalDomain G D volume)
    (hF : IsFundamentalDomain (cuspStabilizer G γ) F volume)
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (hφ : IntegrableOn (petersson k (fun u ↦ poincareTerm γ v k n w u 1) f) F) :
    ∫ z in D, petersson k (poincareSeries γ v k n w) f z =
      ∫ z in F, petersson k (fun u ↦ poincareTerm γ v k n w u 1) f z := by
  have hr : Function.Bijective fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      (QuotientGroup.mk (q.out)⁻¹ : G ⧸ cuspStabilizer G γ) := by
    have h : (fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
        (QuotientGroup.mk (q.out)⁻¹ : G ⧸ cuspStabilizer G γ)) =
          QuotientGroup.quotientRightRelEquivQuotientLeftRel (cuspStabilizer G γ) :=
      funext fun q ↦ by
        conv_rhs => rw [← Quotient.out_eq q]
        rfl
    rw [h]
    exact Equiv.bijective _
  simp_rw [petersson_poincareSeries_eq_tsum γ v k n w _ hf]
  refine hD.setIntegral_tsum_smul_eq hF hr (fun h x ↦ ?_) hφ
  rw [Subgroup.smul_def, Subgroup.smul_def, petersson_poincareTerm_one_smul γ v k n w x _ (hf _),
    poincareTerm_eq_of_rightRel γ v k n w x hw hv (QuotientGroup.rightRel_apply.mpr
      (by simp) : QuotientGroup.rightRel (cuspStabilizer G γ) 1 h),
    ← petersson_poincareTerm_one_smul γ v k n w x 1 (by simp)]
  simp

lemma poincareTerm_one_slash : (fun u ↦ poincareTerm γ v k n w u 1) ∣[k] γ =
    fun u : ℍ ↦ Complex.exp (2 * Real.pi * Complex.I * (n / w) * u) := by
  ext u
  rw [SL_slash_apply, poincareTerm_smul_mul_denom]
  simp

/-- **The change of variables `z = γ_s u`** (LMFDB `specialfunction.poincare`): over the
translate `γ_s S` of a set `S`, the integral of `φ = conj(T₁) f y^k` is that of
`conj(e^{2πi n u / w}) (f ∣[k] γ_s)(u) (Im u)^k` over `S`. -/
lemma setIntegral_smul_set_petersson_poincareTerm_one :
    ∫ z in γ • S, petersson k (fun u ↦ poincareTerm γ v k n w u 1) f z =
      ∫ u in S, petersson k (fun u : ℍ ↦ Complex.exp (2 * Real.pi * Complex.I * (n / w) * u))
        (f ∣[k] γ) u := by
  rw [← Set.image_smul,
    (measurePreserving_smul γ volume).setIntegral_image_emb (measurableEmbedding_const_smul γ)]
  simp_rw [← petersson_slash_SL, poincareTerm_one_slash]

lemma integrableOn_smul_set_petersson_poincareTerm_one_iff :
    IntegrableOn (petersson k (fun u ↦ poincareTerm γ v k n w u 1) f) (γ • S) ↔
      IntegrableOn (petersson k (fun u : ℍ ↦ Complex.exp (2 * Real.pi * Complex.I * (n / w) * u))
        (f ∣[k] γ)) S := by
  have h : petersson k (fun u ↦ poincareTerm γ v k n w u 1) f ∘ (γ • ·) =
      petersson k (fun u : ℍ ↦ Complex.exp (2 * Real.pi * Complex.I * (n / w) * u)) (f ∣[k] γ) :=
    funext fun u ↦ by rw [Function.comp_apply, ← petersson_slash_SL, poincareTerm_one_slash]
  rw [← Set.image_smul,
    (measurePreserving_smul γ volume).integrableOn_image (measurableEmbedding_const_smul γ), h]

lemma coe_smul_of_apply_one_zero_eq_zero (hP : P 1 0 = 0) :
    (↑(P • z) : ℂ) = z + (P 0 0 * P 0 1 : ℤ) := by
  rcases eq_T_zpow_or_eq_neg_T_zpow hP with h | h <;> nth_rw 1 [h]
  · rw [coe_T_zpow_smul_eq]
  · rw [SL_neg_smul, coe_T_zpow_smul_eq]

lemma eq_or_eq_neg_of_apply_one_zero_eq_zero (hP : P 1 0 = 0) (hQ : Q 1 0 = 0)
    (h : P 0 0 * P 0 1 = Q 0 0 * Q 0 1) : P = Q ∨ P = -Q := by
  rcases eq_T_zpow_or_eq_neg_T_zpow hP with hP' | hP' <;>
    rcases eq_T_zpow_or_eq_neg_T_zpow hQ with hQ' | hQ' <;> rw [hP', hQ', h] <;> simp

lemma coe_zpow_smul_of_coe_smul {A : SL(2, ℤ)} {c : ℝ} (hA : ∀ u : ℍ, (↑(A • u) : ℂ) = u + c)
    (j : ℤ) : (↑((A ^ j) • z) : ℂ) = z + j * c := by
  induction j generalizing z with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, mul_smul, ih, hA]
    push_cast
    ring1
  | pred i ih =>
    have h : (↑(A⁻¹ • z) : ℂ) = z - c := by
      rw [eq_sub_iff_add_eq, ← hA, smul_inv_smul]
    rw [zpow_sub_one, mul_smul, ih, h]
    push_cast
    ring1

lemma smul_mem_smul_re_mem_Ico_iff (δ : SL(2, ℤ)) :
    δ • z ∈ γ • {z : ℍ | z.re ∈ Ico 0 (w : ℝ)} ↔
      ((γ⁻¹ * δ * γ) • γ⁻¹ • z).re ∈ Ico 0 (w : ℝ) := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_smul, smul_smul, mul_assoc, mul_inv_cancel,
    mul_one]
  rfl

lemma mem_cuspStabilizer_of_eq_T_zpow
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ)) :
    t ∈ cuspStabilizer G γ := by
  rw [mem_cuspStabilizer_iff]
  rcases ht with h | h
  · rw [h, coe_T_zpow]
    simp
  · rw [h, SpecialLinearGroup.coe_neg, coe_T_zpow]
    simp

lemma smul_mem_smul_re_mem_Ico (hw₀ : 0 < w)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ)) :
    ((t ^ (-⌊(γ⁻¹ • z).re / w⌋) : G) : SL(2, ℤ)) • z ∈ γ • {z : ℍ | z.re ∈ Ico 0 (w : ℝ)} := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw₀
  have htu (u : ℍ) : (↑((γ⁻¹ * (t : SL(2, ℤ)) * γ) • u) : ℂ) = u + (w : ℝ) := by
    rcases ht with h | h <;> rw [h]
    · rw [coe_T_zpow_smul_eq]
      push_cast
      ring1
    · rw [SL_neg_smul, coe_T_zpow_smul_eq]
      push_cast
      ring1
  have hAj : γ⁻¹ * ((t ^ (-⌊(γ⁻¹ • z).re / w⌋) : G) : SL(2, ℤ)) * γ =
      (γ⁻¹ * (t : SL(2, ℤ)) * γ) ^ (-⌊(γ⁻¹ • z).re / w⌋) := by
    simpa using (conj_zpow (a := γ⁻¹) (b := (t : SL(2, ℤ))) (i := -⌊(γ⁻¹ • z).re / w⌋)).symm
  have hfl : (⌊(γ⁻¹ • z).re / w⌋ : ℝ) ≤ (γ⁻¹ • z).re / w := Int.floor_le _
  have hlt : (γ⁻¹ • z).re / w < ⌊(γ⁻¹ • z).re / w⌋ + 1 := Int.lt_floor_add_one _
  have he : (γ⁻¹ • z).re = (γ⁻¹ • z).re / w * w := by field_simp
  rw [smul_mem_smul_re_mem_Ico_iff, hAj, ← UpperHalfPlane.coe_re,
    coe_zpow_smul_of_coe_smul _ htu]
  simp only [Complex.add_re, coe_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Int.cast_neg, Complex.neg_re, Complex.intCast_re]
  constructor <;> nlinarith

variable {z} in
lemma eq_or_eq_neg_of_smul_mem_smul_re_mem_Ico (hw₀ : 0 < w)
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1) {g₁ g₂ : G}
    (hg₁ : g₁ ∈ cuspStabilizer G γ) (hg₂ : g₂ ∈ cuspStabilizer G γ)
    (h₁ : (g₁ : SL(2, ℤ)) • z ∈ γ • {z : ℍ | z.re ∈ Ico 0 (w : ℝ)})
    (h₂ : (g₂ : SL(2, ℤ)) • z ∈ γ • {z : ℍ | z.re ∈ Ico 0 (w : ℝ)}) :
    (g₁ : SL(2, ℤ)) = g₂ ∨ (g₁ : SL(2, ℤ)) = -g₂ := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw₀
  have hre {R : SL(2, ℤ)} (hR : R 1 0 = 0) :
      (R • γ⁻¹ • z).re = (γ⁻¹ • z).re + ((R 0 0 * R 0 1 : ℤ) : ℝ) := by
    rw [← UpperHalfPlane.coe_re, coe_smul_of_apply_one_zero_eq_zero _ hR]
    simp
  have hP : (γ⁻¹ * (g₁ : SL(2, ℤ)) * γ) 1 0 = 0 := (mem_cuspStabilizer_iff γ).mp hg₁
  have hQ : (γ⁻¹ * (g₂ : SL(2, ℤ)) * γ) 1 0 = 0 := (mem_cuspStabilizer_iff γ).mp hg₂
  rw [smul_mem_smul_re_mem_Ico_iff, hre hP] at h₁
  rw [smul_mem_smul_re_mem_Ico_iff, hre hQ] at h₂
  rcases (hw _ hg₁).mul_left ((γ⁻¹ * (g₁ : SL(2, ℤ)) * γ) 0 0) with ⟨p, hp⟩
  rcases (hw _ hg₂).mul_left ((γ⁻¹ * (g₂ : SL(2, ℤ)) * γ) 0 0) with ⟨q, hq⟩
  rw [hp] at h₁
  rw [hq] at h₂
  push_cast at h₁ h₂
  have h1 : (w : ℝ) * (p - q) < w * 1 := by linarith [h₁.2, h₂.1]
  have h2 : (w : ℝ) * (q - p) < w * 1 := by linarith [h₁.1, h₂.2]
  have hpq : p = q := by
    have h1' : (p : ℝ) - q < 1 := lt_of_mul_lt_mul_left h1 hw'.le
    have h2' : (q : ℝ) - p < 1 := lt_of_mul_lt_mul_left h2 hw'.le
    have h1'' : p - q < 1 := by exact_mod_cast h1'
    have h2'' : q - p < 1 := by exact_mod_cast h2'
    omega
  rcases eq_or_eq_neg_of_apply_one_zero_eq_zero hP hQ (by rw [hp, hq, hpq]) with h | h
  · exact .inl <| mul_left_cancel <| mul_right_cancel h
  · exact .inr <| mul_left_cancel <| mul_right_cancel <| h.trans <| by rw [mul_neg, neg_mul]

/-- **The translate of a vertical strip is a fundamental domain for the cusp stabiliser**: if
`-I ∉ G`, `w` divides the translations of the `γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`, and some `t ∈ G`
has `γ_s⁻¹ t γ_s = ±T^w` (so that `w` is the width of the cusp), then `γ_s S` with
`S = {0 ≤ Re z < w}` is a fundamental domain for `G_s` acting on `ℍ`. -/
lemma isFundamentalDomain_smul_re_mem_Ico (hw₀ : 0 < w) (hG : (-1 : SL(2, ℤ)) ∉ G)
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ)) :
    IsFundamentalDomain (cuspStabilizer G γ) (γ • {z : ℍ | z.re ∈ Ico 0 (w : ℝ)}) volume := by
  have htmem : t ∈ cuspStabilizer G γ := mem_cuspStabilizer_of_eq_T_zpow γ w ht
  refine .mk' (((measurableSet_Ico.preimage continuous_re.measurable).const_smul
    γ).nullMeasurableSet) fun x ↦ ⟨⟨t ^ (-⌊(γ⁻¹ • x).re / w⌋), zpow_mem htmem _⟩,
      smul_mem_smul_re_mem_Ico γ w x hw₀ ht, fun g hg ↦ ?_⟩
  rcases eq_or_eq_neg_of_smul_mem_smul_re_mem_Ico γ w hw₀ hw g.2 (zpow_mem htmem _) hg
    (smul_mem_smul_re_mem_Ico γ w x hw₀ ht) with h | h
  · exact Subtype.ext <| Subtype.ext h
  · refine (hG ?_).elim
    rw [show (-1 : SL(2, ℤ)) = ((g : G) : SL(2, ℤ)) *
        ((t ^ (-⌊(γ⁻¹ • x).re / w⌋) : G) : SL(2, ℤ))⁻¹ by rw [h, neg_mul, mul_inv_cancel]]
    exact G.mul_mem (g : G).2 (G.inv_mem (t ^ _ : G).2)

/-- **The Petersson product of a Poincaré series against a form is its `m`-th Fourier coefficient**
(LMFDB `specialfunction.poincare`), up to the factor `w (w / 4πm)^{k-1} Γ(k - 1)`: let `-I ∉ G`,
`D` be a fundamental domain for `G`, `f ∣[k] g = v(g) f` for `g ∈ G`, and the terms of the `m`-th
Poincaré series `P` be constant on the cosets `G_s g`, with `w` the width of the cusp (some
`t ∈ G` has `γ_s⁻¹ t γ_s = ±T^w`). If `(f ∣[k] γ_s)(z) = Σ_{j ≥ 0} a_j e^{2πi j z / w}` on `ℍ`
and the integrand is integrable on the strip `S = {0 ≤ Re z < w}`, then for `m ≥ 1` and `k ≥ 2`,
`∫_D conj(P) f y^k dμ = w (w / 4πm)^{k-1} Γ(k - 1) a_m`. -/
lemma setIntegral_petersson_poincareSeries_eq (hw₀ : 0 < w) (hm : 0 < m) (hk : 2 ≤ k)
    (hG : (-1 : SL(2, ℤ)) ∉ G) (hD : IsFundamentalDomain G D volume)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (ha : ∀ z : ℍ, HasSum (fun j : ℕ ↦ a j * Complex.exp (2 * Real.pi * Complex.I * (j / w) * z))
      ((f ∣[k] γ) z))
    (hint : IntegrableOn (petersson k (fun u : ℍ ↦
      Complex.exp (2 * Real.pi * Complex.I * (m / w) * u)) (f ∣[k] γ))
        {z : ℍ | z.re ∈ Ico 0 (w : ℝ)}) :
    ∫ z in D, petersson k (poincareSeries γ v k m w) f z =
      (w * (w / (4 * Real.pi * m)) ^ ((k : ℝ) - 1) * Real.Gamma (k - 1) : ℝ) * a m := by
  have hint' : IntegrableOn (petersson k (fun u : ℍ ↦
      Complex.exp (2 * Real.pi * Complex.I * ((m : ℤ) / w) * u)) (f ∣[k] γ))
        {z : ℍ | z.re ∈ Ico 0 (w : ℝ)} := by
    simpa only [Int.cast_natCast] using hint
  rw [setIntegral_petersson_poincareSeries γ v k m w hD
    (isFundamentalDomain_smul_re_mem_Ico γ w hw₀ hG hw ht) hw hv hf
    ((integrableOn_smul_set_petersson_poincareTerm_one_iff γ v k m w).mpr hint'),
    setIntegral_smul_set_petersson_poincareTerm_one]
  simp only [Int.cast_natCast]
  exact setIntegral_petersson_exp_eq w m a k hw₀ hm hk ha hint

lemma eq_zero_of_forall_mul_coeff_eq_zero (hw₀ : 0 < w) (hk : 2 ≤ k)
    (ha : ∀ z : ℍ, HasSum (fun j : ℕ ↦ a j * Complex.exp (2 * Real.pi * Complex.I * (j / w) * z))
      ((f ∣[k] γ) z)) (ha₀ : a 0 = 0)
    (h : ∀ m : ℕ, 0 < m →
      ((w * (w / (4 * Real.pi * m)) ^ ((k : ℝ) - 1) * Real.Gamma (k - 1) : ℝ) : ℂ) * a m = 0) :
    f = 0 := by
  have hk' : 0 < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw₀
  have hzero (j : ℕ) : a j = 0 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ha₀
    · have hj' : (0 : ℝ) < j := by exact_mod_cast hj
      have hc : (w * (w / (4 * Real.pi * j)) ^ ((k : ℝ) - 1) * Real.Gamma (k - 1) : ℝ) ≠ 0 :=
        (mul_pos (mul_pos hw' (Real.rpow_pos_of_pos (by positivity) _))
          (Real.Gamma_pos_of_pos hk')).ne'
      exact (mul_eq_zero.mp (h j hj)).resolve_left (Complex.ofReal_ne_zero.mpr hc)
  have hfγ : f ∣[k] γ = 0 := funext fun z ↦ (ha z).unique <| by simp [hzero]
  have hfγγ : f = (f ∣[k] γ) ∣[k] γ⁻¹ := by
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  rw [hfγγ, hfγ, SlashAction.zero_slash]

/-- **The Poincaré series detect cusp forms** (LMFDB `specialfunction.poincare`): under the
hypotheses of `setIntegral_petersson_poincareSeries_eq`, if the Fourier expansion of `f ∣[k] γ_s`
has no constant term and `f` is Petersson-orthogonal to the Poincaré series `P_m` for every
`m ≥ 1`, then `f = 0`, each product being a nonzero multiple of `a_m`. On a finite-dimensional
space of such forms this gives that the `P_m` span it, with no need for the definiteness of the
Petersson product (`span_poincareSeries_eq`). -/
lemma eq_zero_of_forall_setIntegral_petersson_poincareSeries_eq_zero (hw₀ : 0 < w) (hk : 2 ≤ k)
    (hG : (-1 : SL(2, ℤ)) ∉ G) (hD : IsFundamentalDomain G D volume)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (ha : ∀ z : ℍ, HasSum (fun j : ℕ ↦ a j * Complex.exp (2 * Real.pi * Complex.I * (j / w) * z))
      ((f ∣[k] γ) z))
    (ha₀ : a 0 = 0) (hint : ∀ m : ℕ, 0 < m → IntegrableOn (petersson k (fun u : ℍ ↦
      Complex.exp (2 * Real.pi * Complex.I * (m / w) * u)) (f ∣[k] γ))
        {z : ℍ | z.re ∈ Ico 0 (w : ℝ)})
    (horth : ∀ m : ℕ, 0 < m → ∫ z in D, petersson k (poincareSeries γ v k m w) f z = 0) :
    f = 0 :=
  eq_zero_of_forall_mul_coeff_eq_zero γ k w hw₀ hk ha ha₀ fun m hm ↦
    (setIntegral_petersson_poincareSeries_eq γ v k w m hw₀ hm hk hG hD ht hw hv hf ha
      (hint m hm)).symm.trans (horth m hm)

variable (G) in
/-- The image in `PSL(2, ℤ)` of the cusp stabiliser `G_s`, a subgroup of the image of `G`: the
group whose fundamental domains the unfolding uses when `-I ∈ G`, `-I` acting trivially on `ℍ`. -/
noncomputable def pslCuspStabilizer :
    Subgroup (G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) :=
  (cuspStabilizer G γ).map ((QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).subgroupMap G)

lemma mem_cuspStabilizer_of_mem_center {c : G} (hc : (c : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ)) :
    c ∈ cuspStabilizer G γ := by
  have hcγ : γ⁻¹ * (c : SL(2, ℤ)) * γ = c := by
    rw [Subgroup.mem_center_iff.mp hc γ⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hT : (T * (c : SL(2, ℤ))) 0 0 = ((c : SL(2, ℤ)) * T) 0 0 := by
    rw [Subgroup.mem_center_iff.mp hc T]
  rw [mem_cuspStabilizer_iff, hcγ]
  simpa [Matrix.mul_apply] using hT

lemma bijective_mk_inv_subgroupMap_out : Function.Bijective
    fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      (QuotientGroup.mk ((QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).subgroupMap G q.out)⁻¹ :
        G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) ⧸ pslCuspStabilizer G γ) := by
  have hker {a b : G} (hab : (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).subgroupMap G a =
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).subgroupMap G b)
      (hb : b ∈ cuspStabilizer G γ) : a ∈ cuspStabilizer G γ := by
    have hc : ((b⁻¹ * a : G) : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) := by
      have h : ((b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ)) = (a : SL(2, ℤ)) :=
        (congrArg Subtype.val hab).symm
      simpa using QuotientGroup.eq.mp h
    simpa using (cuspStabilizer G γ).mul_mem hb (mem_cuspStabilizer_of_mem_center γ hc)
  refine ⟨fun q q' hqq ↦ ?_, fun y ↦ ?_⟩
  · rw [QuotientGroup.eq, inv_inv, ← map_inv, ← map_mul] at hqq
    rcases Subgroup.mem_map.mp hqq with ⟨h, hh, hh'⟩
    exact (Quotient.out_equiv_out.mp (QuotientGroup.rightRel_apply.mpr (hker hh'.symm hh))).symm
  · induction y using QuotientGroup.induction_on with
    | H y =>
      rcases MonoidHom.subgroupMap_surjective _ G y with ⟨g, rfl⟩
      refine ⟨Quotient.mk _ g⁻¹, ?_⟩
      rw [QuotientGroup.eq, inv_inv, ← map_mul]
      refine Subgroup.mem_map_of_mem _ ?_
      simpa using (cuspStabilizer G γ).inv_mem
        (QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel _) g⁻¹))

/-- **Unfolding the Petersson product of a Poincaré series, through `PSL(2, ℤ)`** (LMFDB
`specialfunction.poincare`): as `setIntegral_petersson_poincareSeries`, for any `G` (`-I ∈ G`
allowed), with fundamental domains `D` of the image of `G` in `PSL(2, ℤ)` and `F` of the image of
`G_s`. -/
lemma setIntegral_petersson_poincareSeries_psl
    (hD : IsFundamentalDomain (G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D volume)
    (hF : IsFundamentalDomain (pslCuspStabilizer G γ) F volume)
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (hφ : IntegrableOn (petersson k (fun u ↦ poincareTerm γ v k n w u 1) f) F) :
    ∫ z in D, petersson k (poincareSeries γ v k n w) f z =
      ∫ z in F, petersson k (fun u ↦ poincareTerm γ v k n w u 1) f z := by
  have : Countable PSL(2, ℤ) :=
    inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel (Subgroup.center SL(2, ℤ)))))
  simp_rw [petersson_poincareSeries_eq_tsum γ v k n w _ hf]
  refine hD.setIntegral_tsum_smul_eq hF (bijective_mk_inv_subgroupMap_out γ) (fun h x ↦ ?_) hφ
  rcases h with ⟨_, h, hh, rfl⟩
  have hx : (⟨_, h, hh, rfl⟩ : pslCuspStabilizer G γ) • x = ((h : G) : SL(2, ℤ)) • x :=
    rfl
  rw [hx, petersson_poincareTerm_one_smul γ v k n w x _ (hf _),
    poincareTerm_eq_of_rightRel γ v k n w x hw hv (QuotientGroup.rightRel_apply.mpr
      (by simpa using hh) : QuotientGroup.rightRel (cuspStabilizer G γ) 1 h),
    ← petersson_poincareTerm_one_smul γ v k n w x 1 (by simp)]
  simp

/-- **The translate of a vertical strip is a fundamental domain for the cusp stabiliser in
`PSL(2, ℤ)`**: if `w` divides the translations of the `γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`, and some
`t ∈ G` has `γ_s⁻¹ t γ_s = ±T^w`, then `γ_s S` with `S = {0 ≤ Re z < w}` is a fundamental domain
for the image of `G_s` in `PSL(2, ℤ)`, whether or not `-I ∈ G`. -/
lemma isFundamentalDomain_smul_re_mem_Ico_psl (hw₀ : 0 < w)
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ)) :
    IsFundamentalDomain (pslCuspStabilizer G γ) (γ • {z : ℍ | z.re ∈ Ico 0 (w : ℝ)}) volume := by
  have htmem : t ∈ cuspStabilizer G γ := mem_cuspStabilizer_of_eq_T_zpow γ w ht
  refine .mk' (((measurableSet_Ico.preimage continuous_re.measurable).const_smul
    γ).nullMeasurableSet) fun x ↦ ⟨⟨_, Subgroup.mem_map_of_mem _ (zpow_mem htmem
      (-⌊(γ⁻¹ • x).re / w⌋))⟩, smul_mem_smul_re_mem_Ico γ w x hw₀ ht, fun h hh ↦ ?_⟩
  rcases h with ⟨_, g, hg, rfl⟩
  rcases eq_or_eq_neg_of_smul_mem_smul_re_mem_Ico γ w hw₀ hw hg (zpow_mem htmem _) hh
    (smul_mem_smul_re_mem_Ico γ w x hw₀ ht) with h | h
  · exact Subtype.ext <| congrArg ((QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).subgroupMap G) <|
      Subtype.ext h
  · refine Subtype.ext <| Subtype.ext ?_
    simp only [MonoidHom.subgroupMap_apply_coe]
    refine QuotientGroup.eq.mpr ?_
    rw [h, inv_neg, neg_mul, inv_mul_cancel]
    exact Subgroup.mem_center_iff.mpr fun g ↦ by rw [mul_neg_one, neg_one_mul]

/-- **The Petersson product of a Poincaré series against a form is its `m`-th Fourier coefficient,
through `PSL(2, ℤ)`** (LMFDB `specialfunction.poincare`): as
`setIntegral_petersson_poincareSeries_eq`, for any `G` (`-I ∈ G` allowed), with `D` a fundamental
domain of the image of `G` in `PSL(2, ℤ)`. -/
lemma setIntegral_petersson_poincareSeries_eq_psl (hw₀ : 0 < w) (hm : 0 < m) (hk : 2 ≤ k)
    (hD : IsFundamentalDomain (G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D volume)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (ha : ∀ z : ℍ, HasSum (fun j : ℕ ↦ a j * Complex.exp (2 * Real.pi * Complex.I * (j / w) * z))
      ((f ∣[k] γ) z))
    (hint : IntegrableOn (petersson k (fun u : ℍ ↦
      Complex.exp (2 * Real.pi * Complex.I * (m / w) * u)) (f ∣[k] γ))
        {z : ℍ | z.re ∈ Ico 0 (w : ℝ)}) :
    ∫ z in D, petersson k (poincareSeries γ v k m w) f z =
      (w * (w / (4 * Real.pi * m)) ^ ((k : ℝ) - 1) * Real.Gamma (k - 1) : ℝ) * a m := by
  have hint' : IntegrableOn (petersson k (fun u : ℍ ↦
      Complex.exp (2 * Real.pi * Complex.I * ((m : ℤ) / w) * u)) (f ∣[k] γ))
        {z : ℍ | z.re ∈ Ico 0 (w : ℝ)} := by
    simpa only [Int.cast_natCast] using hint
  rw [setIntegral_petersson_poincareSeries_psl γ v k m w hD
    (isFundamentalDomain_smul_re_mem_Ico_psl γ w hw₀ hw ht) hw hv hf
    ((integrableOn_smul_set_petersson_poincareTerm_one_iff γ v k m w).mpr hint'),
    setIntegral_smul_set_petersson_poincareTerm_one]
  simp only [Int.cast_natCast]
  exact setIntegral_petersson_exp_eq w m a k hw₀ hm hk ha hint

/-- **The Poincaré series detect cusp forms, through `PSL(2, ℤ)`** (LMFDB
`specialfunction.poincare`): as `eq_zero_of_forall_setIntegral_petersson_poincareSeries_eq_zero`,
for any `G` (`-I ∈ G` allowed), with `D` a fundamental domain of the image of `G` in
`PSL(2, ℤ)`. -/
lemma eq_zero_of_forall_setIntegral_petersson_poincareSeries_eq_zero_psl (hw₀ : 0 < w) (hk : 2 ≤ k)
    (hD : IsFundamentalDomain (G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D volume)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (ha : ∀ z : ℍ, HasSum (fun j : ℕ ↦ a j * Complex.exp (2 * Real.pi * Complex.I * (j / w) * z))
      ((f ∣[k] γ) z))
    (ha₀ : a 0 = 0) (hint : ∀ m : ℕ, 0 < m → IntegrableOn (petersson k (fun u : ℍ ↦
      Complex.exp (2 * Real.pi * Complex.I * (m / w) * u)) (f ∣[k] γ))
        {z : ℍ | z.re ∈ Ico 0 (w : ℝ)})
    (horth : ∀ m : ℕ, 0 < m → ∫ z in D, petersson k (poincareSeries γ v k m w) f z = 0) :
    f = 0 :=
  eq_zero_of_forall_mul_coeff_eq_zero γ k w hw₀ hk ha ha₀ fun m hm ↦
    (setIntegral_petersson_poincareSeries_eq_psl γ v k w m hw₀ hm hk hD ht hw hv hf ha
      (hint m hm)).symm.trans (horth m hm)

end ModularForm
