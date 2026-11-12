import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.FiniteDimensional

/-!
# Poincaré series span the cusp forms of every multiplier

Let `G` be a subgroup of finite index of `SL(2, ℤ)`, `v : G → S¹` a multiplier (LMFDB
`mf.multipliersystem`), of finite or infinite order, `k ≥ 3`, and `s = γ_s ∞` a cusp of `G` of
width `w` with `v(h) = (±1)^k` on its stabiliser `G_s` (the corrected form of the LMFDB's
hypothesis on `v`). The general spanning theorem
`ModularForm.span_poincareSeries_eq_multiplierCuspSpace` needs three facts about the space
`S_k(G, v)` of cusp forms, which `PoincareSpanFiniteOrder.lean` proves for multipliers of finite
order. They hold for every multiplier:

* `S_k(G, v)` is finite-dimensional (`ModularForm.finiteDimensional_multiplierCuspSpace`);
* every `f ∈ S_k(G, v)` has a Fourier expansion `(f ∣[k] γ_s)(z) = Σ_{j ≥ 1} a_j e^{2πijz/w}`
  without constant term, since `f ∣[k] γ_s` is holomorphic, tends to `0` at `i∞` and has
  period `w`;
* the Petersson integrands are integrable, since `y^k |f(z)|²` is bounded on `ℍ`
  (`ModularForm.exists_norm_petersson_le`).

So the Poincaré series `P_m`, `m ≥ 1`, at `s` (LMFDB `specialfunction.poincare`) span `S_k(G, v)`,
with no hypothesis on the order of `v`.

## Main results

* `ModularForm.integrableOn_petersson_of_mem_multiplierCuspSpace`: the Petersson integrand of two
  cusp forms with a multiplier is integrable on every set of finite measure.
* `ModularForm.span_poincareSeries_eq_multiplierCuspSpace_of_finiteIndex_subgroup` (LMFDB
  `specialfunction.poincare`): the Poincaré series `P_m`, `m ≥ 1`, span `S_k(G, v)` for every
  multiplier `v`.
-/

open UpperHalfPlane Matrix SpecialLinearGroup ModularGroup MeasureTheory Set

open scoped MatrixGroups ModularForm Manifold

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} [G.FiniteIndex] (γ : SL(2, ℤ)) (v : G →* Circle) {k : ℤ} {w : ℕ}
    {t : G} {f g : ℍ → ℂ}

variable {v} in
/-- **The Petersson integrand of two cusp forms with a multiplier is integrable on every set of
finite measure**: it is continuous, and bounded by the bounds on `y^k |f(z)|²` and `y^k |g(z)|²`
of `exists_norm_petersson_le`, through `2ab ≤ a² + b²`. -/
lemma integrableOn_petersson_of_mem_multiplierCuspSpace
    (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v))
    (hg : g ∈ multiplierCuspSpace k (multiplierMapGL v)) {S : Set ℍ} (hS : volume S < ⊤) :
    IntegrableOn (petersson k f g) S := by
  rcases exists_norm_petersson_le hf with ⟨Cf, hCf⟩
  rcases exists_norm_petersson_le hg with ⟨Cg, hCg⟩
  refine IntegrableOn.of_bound hS ((petersson_continuous k hf.1.1.continuous
    hg.1.1.continuous).aestronglyMeasurable.restrict) ((Cf + Cg) / 2) (ae_of_all _ fun τ ↦ ?_)
  have him : (0 : ℝ) < τ.im ^ k := zpow_pos τ.im_pos k
  have hnorm (a b : ℍ → ℂ) : ‖petersson k a b τ‖ = ‖a τ‖ * ‖b τ‖ * τ.im ^ k := by
    simp [petersson, abs_of_pos τ.im_pos]
  have h1 : ‖f τ‖ * ‖f τ‖ * τ.im ^ k ≤ Cf := hnorm f f ▸ hCf τ
  have h2 : ‖g τ‖ * ‖g τ‖ * τ.im ^ k ≤ Cg := hnorm g g ▸ hCg τ
  rw [hnorm]
  nlinarith [mul_le_mul_of_nonneg_right (two_mul_le_add_sq ‖f τ‖ ‖g τ‖) him.le]

/-- **Poincaré series span the cusp forms of every multiplier** (LMFDB
`specialfunction.poincare`): for a subgroup `G` of finite index of `SL(2, ℤ)`, any multiplier
`v : G → S¹` (of finite or infinite order), `k ≥ 3`, and `s = γ_s ∞` a cusp of width `w` (some
`t ∈ G` has `γ_s⁻¹ t γ_s = ±T^w`, and `w` divides the translations of the `γ_s⁻¹ h γ_s = ±T^b`,
`h ∈ G_s`) with `v(h) = (±1)^k` on `G_s`, the Poincaré series `P_m`, `m ≥ 1`, at `s` span the space
`S_k(G, v)` of cusp forms of weight `k` and multiplier `v`. -/
lemma span_poincareSeries_eq_multiplierCuspSpace_of_finiteIndex_subgroup (hw₀ : 0 < w) (hk : 3 ≤ k)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k) :
    Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P} =
      multiplierCuspSpace k (multiplierMapGL v) := by
  refine span_poincareSeries_eq_multiplierCuspSpace γ v k w hw₀ hk
    (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter G) ht hw hv (fun f hf ↦ ?_)
    (fun f hf m hm ↦ ?_) (fun f hf g hg ↦ integrableOn_petersson_of_mem_multiplierCuspSpace hf hg
      (volume_iUnion_out_inv_smul_fdo_lt_top G))
  · have hF : f ∣[k] (t : SL(2, ℤ)) = ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k • f := by
      rw [← hv t (mem_cuspStabilizer_of_eq_T_zpow γ w ht)]
      exact slash_eq_smul_of_mem_multiplierCuspSpace hf t
    have hFhol : MDiff (f ∣[k] γ) := hf.1.1.slash k γ
    have hFzero : IsZeroAtImInfty (f ∣[k] γ) :=
      isZeroAtImInfty_slash_of_mem_multiplierCuspSpace γ hf
    exact ⟨_, qExpansion_slash_coeff_zero γ hw₀ hF ht hFhol hFzero,
      hasSum_qExpansion_slash γ hw₀ hF ht hFhol hFzero⟩
  · rcases exists_norm_petersson_le hf with ⟨C, hC⟩
    exact integrableOn_petersson_exp_re_mem_Ico hw₀ hm hk (hf.1.1.slash k γ).continuous
      (norm_le_of_norm_petersson_le fun τ ↦ (petersson_slash_SL k f f γ τ).symm ▸ hC _)

end ModularForm
