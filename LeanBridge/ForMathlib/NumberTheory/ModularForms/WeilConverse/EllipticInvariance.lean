import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Invariance under an elliptic element of infinite order

Let `M ∈ SL(2, ℝ)` fix a point `z₀` of the upper half plane, and put `λ = c z₀ + d`, so that `λ` and
`λ⁻¹` are the eigenvalues of `M`. If `h` is holomorphic on `ℍ` and `h ∣[k] M = h`, comparing the
leading terms of `h` at `z₀` gives `λ ^ (2 n + k) = 1`, where `n` is the order of vanishing of `h`
at `z₀`. So `h = 0` if `λ` is not a root of unity and `k > 0`. This is the last step of Weil's
converse theorem, where `M` is a rational matrix with `|tr M| < 2` and `tr M` not an integer.

## Main results

* `ModularForm.eq_zero_of_slash_eq_of_smul_eq`: a holomorphic function invariant under an element
  fixing `z₀` with `λ ^ (2 n + k) ≠ 1` for all `n : ℕ` vanishes.
* `ModularForm.zpow_ne_one_of_mul_sub_eq_one`: an eigenvalue of a matrix of determinant `1` with
  rational non-integral trace is not a root of unity.
-/

open UpperHalfPlane Filter Topology Complex

open scoped ModularForm Manifold

namespace ModularForm

variable {k : ℤ} {h : ℍ → ℂ} {M : GL (Fin 2) ℝ} {z₀ : ℍ}

lemma slash_apply_of_det_eq_one (hM : M.det.val = 1) (z : ℍ) :
    (h ∣[k] M) z = h (M • z) * denom M z ^ (-k) := by
  simp [slash_apply, σ, hM]

private lemma smul_sub_coe (hM : M.det.val = 1) (hz : M • z₀ = z₀) {w : ℂ} (hw : denom M w ≠ 0) :
    num M w / denom M w - z₀ = (w - z₀) / (denom M w * denom M z₀) := by
  have hpos : 0 < M.det.val := hM ▸ one_pos
  have hz₀ : num M z₀ / denom M z₀ = z₀ := by
    rw [← coe_smul_of_det_pos hpos, hz]
  have hd : denom M z₀ ≠ 0 := denom_ne_zero M z₀
  have hdet : (M 0 0 : ℂ) * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h1 : (M : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by simpa using hM
    rw [Matrix.det_fin_two] at h1
    exact_mod_cast h1
  have hn : num M z₀ = z₀ * denom M z₀ := (div_eq_iff hd).mp hz₀
  have he : num M w / denom M w - z₀ =
      (num M w * denom M z₀ - z₀ * denom M z₀ * denom M w) / (denom M w * denom M z₀) := by
    field_simp
  rw [he, ← hn]
  congr 1
  simp only [num, denom]
  linear_combination (w - z₀) * hdet

/-- **A holomorphic function invariant under an elliptic element of infinite order vanishes.**
Let `M` have determinant `1` and fix `z₀ ∈ ℍ`, and suppose that `λ = c z₀ + d` satisfies
`λ ^ (2 n + k) ≠ 1` for every `n : ℕ`. A holomorphic `h` with `h ∣[k] M = h` is then `0`: if `h` has
order `n` at `z₀`, the leading terms of `h(M z) = (c z + d) ^ k h(z)` give `λ ^ (2 n + k) = 1`. -/
lemma eq_zero_of_slash_eq_of_smul_eq (hh : MDiff h) (hM : M.det.val = 1) (hz : M • z₀ = z₀)
    (hl : ∀ n : ℕ, denom M z₀ ^ (2 * (n : ℤ) + k) ≠ 1) (hinv : h ∣[k] M = h) : h = 0 := by
  have hpos : 0 < M.det.val := hM ▸ one_pos
  have han : AnalyticOnNhd ℂ (h ∘ ofComplex) {w | 0 < w.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hh).analyticOnNhd isOpen_upperHalfPlaneSet
  have hU : ∀ᶠ w in 𝓝 (z₀ : ℂ), 0 < w.im := isOpen_upperHalfPlaneSet.mem_nhds z₀.2
  have hd : denom M z₀ ≠ 0 := denom_ne_zero M z₀
  have hdc : ContinuousAt (denom M) (z₀ : ℂ) := by
    unfold denom
    fun_prop
  have hnc : ContinuousAt (num M) (z₀ : ℂ) := by
    unfold num
    fun_prop
  have hφc : ContinuousAt (fun w ↦ num M w / denom M w) (z₀ : ℂ) := hnc.div hdc hd
  have hφz : num M z₀ / denom M z₀ = z₀ := by
    rw [← coe_smul_of_det_pos hpos, hz]
  have hφt : Tendsto (fun w ↦ num M w / denom M w) (𝓝 (z₀ : ℂ)) (𝓝 (z₀ : ℂ)) := by
    simpa only [ContinuousAt, hφz] using hφc
  by_cases hzero : ∀ᶠ w in 𝓝 (z₀ : ℂ), (h ∘ ofComplex) w = 0
  · have hon : Set.EqOn (h ∘ ofComplex) 0 {w : ℂ | 0 < w.im} :=
      han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_halfSpace_im_gt 0).isPreconnected z₀.2 hzero
    ext z
    simpa using hon z.2
  rcases (han z₀ z₀.2).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero with ⟨n, g, hg, hg0, hgeq⟩
  have hkey : ∀ᶠ w in 𝓝[≠] (z₀ : ℂ), (denom M w * denom M z₀)⁻¹ ^ n * g (num M w / denom M w) =
      denom M w ^ k * g w := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [hU, hgeq, hφt.eventually hgeq] with w hw hw₁ hw₂ hne
    have hwd : denom M w ≠ 0 := denom_ne_zero_of_im M hw.ne'
    have hs : ((M • (⟨w, hw⟩ : ℍ) : ℍ) : ℂ) = num M w / denom M w :=
      coe_smul_of_det_pos hpos ⟨w, hw⟩
    have htrans : h (M • (⟨w, hw⟩ : ℍ)) = denom M w ^ k * h ⟨w, hw⟩ := by
      have h1 : h (M • (⟨w, hw⟩ : ℍ)) * denom M w ^ (-k) = h ⟨w, hw⟩ := by
        rw [← slash_apply_of_det_eq_one hM ⟨w, hw⟩]
        exact congrFun hinv _
      rw [← h1, mul_comm, mul_assoc, ← zpow_add₀ hwd]
      simp
    have hH₁ : (h ∘ ofComplex) w = h ⟨w, hw⟩ := by
      simp [ofComplex_apply_of_im_pos hw]
    have hH₂ : (h ∘ ofComplex) (num M w / denom M w) = h (M • (⟨w, hw⟩ : ℍ)) := by
      rw [← hs, Function.comp_apply, ofComplex_apply]
    rw [hH₂, htrans, smul_sub_coe hM hz hwd, smul_eq_mul] at hw₂
    rw [hH₁, smul_eq_mul] at hw₁
    rw [hw₁] at hw₂
    have hne' : (w - z₀) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hne)
    refine mul_left_cancel₀ hne' ?_
    rw [div_eq_mul_inv, mul_pow] at hw₂
    linear_combination -hw₂
  have hl₁ : Tendsto (fun w ↦ (denom M w * denom M z₀)⁻¹ ^ n * g (num M w / denom M w))
      (𝓝[≠] (z₀ : ℂ)) (𝓝 ((denom M z₀ * denom M z₀)⁻¹ ^ n * g z₀)) := by
    have h1 : ContinuousAt (fun w ↦ (denom M w * denom M z₀)⁻¹ ^ n) (z₀ : ℂ) :=
      ((hdc.mul continuousAt_const).inv₀ (mul_ne_zero hd hd)).pow n
    have h2 : Tendsto (fun w ↦ g (num M w / denom M w)) (𝓝 (z₀ : ℂ)) (𝓝 (g z₀)) :=
      hg.continuousAt.tendsto.comp hφt
    exact (h1.tendsto.mul h2).mono_left nhdsWithin_le_nhds
  have hl₂ : Tendsto (fun w ↦ denom M w ^ k * g w) (𝓝[≠] (z₀ : ℂ)) (𝓝 (denom M z₀ ^ k * g z₀)) :=
    ((hdc.zpow₀ k (Or.inl hd)).tendsto.mul hg.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have heq : (denom M z₀ * denom M z₀)⁻¹ ^ n * g z₀ = denom M z₀ ^ k * g z₀ :=
    tendsto_nhds_unique (hl₁.congr' hkey) hl₂
  refine absurd ?_ (hl n)
  have h3 : (denom M z₀ * denom M z₀)⁻¹ ^ n = denom M z₀ ^ k := mul_right_cancel₀ hg0 heq
  rw [zpow_add₀ hd, ← h3, zpow_mul, zpow_natCast, ← mul_pow, zpow_two,
    mul_inv_cancel₀ (mul_ne_zero hd hd), one_pow]

/-- **An eigenvalue with non-integral rational trace is not a root of unity.** If `l` and
`l⁻¹ = t - l` are the eigenvalues of a matrix of rational trace `t` and determinant `1`, and `t` is
not an integer, then `l ^ m ≠ 1` for every `m ≠ 0`: a root of unity is an algebraic integer, so `t`
would be one. -/
lemma zpow_ne_one_of_mul_sub_eq_one {l : ℂ} {t : ℚ} (hlt : l * ((t : ℂ) - l) = 1)
    (ht : ∀ n : ℤ, t ≠ n) {m : ℤ} (hm : m ≠ 0) : l ^ m ≠ 1 := by
  intro hl
  have hl0 : l ≠ 0 := left_ne_zero_of_mul_eq_one hlt
  have hn : l ^ m.natAbs = 1 := by
    rcases m.natAbs_eq with h1 | h1
    · rw [h1, zpow_natCast] at hl
      exact hl
    · rw [h1, zpow_neg, zpow_natCast, inv_eq_one] at hl
      exact hl
  have hpos : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  have hint : IsIntegral ℤ l := IsIntegral.of_pow hpos (hn ▸ isIntegral_one)
  have hinv : (t : ℂ) - l = l ^ (m.natAbs - 1) := by
    refine mul_left_cancel₀ hl0 (hlt.trans ?_)
    rw [← pow_succ', Nat.sub_add_cancel hpos, hn]
  have htc : IsIntegral ℤ (algebraMap ℚ ℂ t) := by
    have h2 : algebraMap ℚ ℂ t = l + l ^ (m.natAbs - 1) := by
      rw [← hinv]
      simp
    rw [h2]
    exact hint.add (hint.pow _)
  rcases IsIntegrallyClosedIn.isIntegral_iff.mp (isIntegral_algebraMap_iff.mp htc) with ⟨y, hy⟩
  exact ht y (hy.symm.trans (eq_intCast (algebraMap ℤ ℚ) y))

end ModularForm
