import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareSpanCuspForm

/-!
# Poincaré series span the cusp forms of a multiplier of finite order

Let `G` be a subgroup of finite index of `SL(2, ℤ)` and `v : G → S¹` a multiplier of finite
order, that is, with kernel of finite index in `G` (a nebentypus character, for instance). A cusp
form of weight `k` and multiplier `v` on `G` is then a cusp form of weight `k`, with trivial
multiplier, on the kernel `H = ker v`, a subgroup of finite index of `SL(2, ℤ)` with the same
cusps. So the space `S_k(G, v)` is finite-dimensional, and its elements `f` have the bound
`y^{k/2} |(f ∣[k] γ_s)(z)| ≤ C` and tend to `0` at every cusp. At the cusp `s = γ_s ∞` of width `w`
of `G`, with `v(h) = (±1)^k` on `G_s` (the corrected form of the LMFDB's hypothesis on `v`),
`f ∣[k] γ_s` has period `w`. These are the three hypotheses of
`ModularForm.span_poincareSeries_eq_multiplierCuspSpace`, so the Poincaré series `P_m`, `m ≥ 1`,
at `s` (LMFDB `specialfunction.poincare`) span `S_k(G, v)` for `k ≥ 3`, with no further
hypothesis.

## Main results

* `ModularForm.multiplierCuspSpace_le_multiplierCuspSpace_ker`: `S_k(G, v) ⊆ S_k(ker v)`.
* The instance `FiniteIndex (H.map G.subtype)` for `H` of finite index in `G` of finite index
  (such as `ker v`), and then the instance
  `FiniteDimensional ℂ (multiplierCuspSpace k (multiplierMapGL v))`.
* `ModularForm.span_poincareSeries_eq_multiplierCuspSpace_of_finiteIndex`: the Poincaré series
  `P_m`, `m ≥ 1`, span the cusp forms of weight `k ≥ 3` and multiplier `v` of finite order on `G`.
-/

open UpperHalfPlane Matrix SpecialLinearGroup ModularGroup MeasureTheory Subgroup

open scoped MatrixGroups ModularForm Manifold

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (v : G →* Circle) {k : ℤ} {w : ℕ} {t : G}

/-- **Cusp forms of a multiplier are cusp forms on its kernel**: a cusp form of weight `k` and
multiplier `v` on `G` is a cusp form of weight `k` and trivial multiplier on the kernel of `v`,
as a subgroup of `SL(2, ℤ)`. -/
lemma multiplierCuspSpace_le_multiplierCuspSpace_ker : multiplierCuspSpace k (multiplierMapGL v) ≤
    multiplierCuspSpace k (multiplierMapGL (1 : v.ker.map G.subtype →* Circle)) := by
  have hle : (v.ker.map G.subtype).map (mapGL ℝ) ≤ G.map (mapGL ℝ) :=
    Subgroup.map_mono (Subgroup.map_subtype_le _)
  refine fun f hf ↦ ⟨⟨hf.1.1, fun γ' ↦ ?_, fun hc ↦ hf.1.2.2 (hc.mono hle)⟩,
    fun hc ↦ hf.2 (hc.mono hle)⟩
  rcases γ' with ⟨_, _, ⟨g, hg, rfl⟩, rfl⟩
  have h1 : f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f :=
    multiplierMapGL_apply_mapGL v g ▸ hf.1.2.1 ⟨_, Subgroup.mem_map_of_mem _ g.2⟩
  rwa [MonoidHom.mem_ker.mp hg, Circle.coe_one] at h1

variable [G.FiniteIndex] [v.ker.FiniteIndex]

instance {H : Subgroup G} [H.FiniteIndex] : (H.map G.subtype).FiniteIndex :=
  ⟨by
    rw [index_map_subtype]
    exact mul_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩

instance : FiniteDimensional ℂ (multiplierCuspSpace k (multiplierMapGL v)) :=
  Submodule.finiteDimensional_of_le (multiplierCuspSpace_le_multiplierCuspSpace_ker v)

/-- **Poincaré series span the cusp forms of a multiplier of finite order** (LMFDB
`specialfunction.poincare`): for `G` of finite index in `SL(2, ℤ)`, `v` a multiplier on `G` whose
kernel has finite index, `k ≥ 3`, and `s = γ_s ∞` a cusp of width `w` (some `t ∈ G` has
`γ_s⁻¹ t γ_s = ±T^w`, and `w` divides the translations of the `γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s`) with
`v(h) = (±1)^k` on `G_s`, the Poincaré series `P_m`, `m ≥ 1`, at `s` span the space `S_k(G, v)` of
cusp forms of weight `k` and multiplier `v` on `G`. -/
lemma span_poincareSeries_eq_multiplierCuspSpace_of_finiteIndex (hw₀ : 0 < w) (hk : 3 ≤ k)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k) :
    Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P} =
      multiplierCuspSpace k (multiplierMapGL v) := by
  refine span_poincareSeries_eq_multiplierCuspSpace γ v k w hw₀ hk
    (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter G) ht hw hv (fun f hf ↦ ?_)
    (fun f hf m hm ↦ ?_) (fun f hf g hg ↦ ?_) <;>
    rcases mem_multiplierCuspSpace_multiplierMapGL_one_iff.mp
      (multiplierCuspSpace_le_multiplierCuspSpace_ker v hf) with ⟨f, rfl⟩
  · have hF : ⇑f ∣[k] (t : SL(2, ℤ)) = ((γ⁻¹ * (t : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k • ⇑f := by
      rw [← hv t (mem_cuspStabilizer_of_eq_T_zpow γ w ht), ← multiplierMapGL_apply_mapGL v t]
      exact hf.1.2.1 ⟨_, Subgroup.mem_map_of_mem _ t.2⟩
    have hFhol : MDiff (⇑f ∣[k] γ) := mdifferentiable_slash γ f
    have hFzero : IsZeroAtImInfty (⇑f ∣[k] γ) := CuspFormClass.zero_at_infty_slash f γ
    exact ⟨_, qExpansion_slash_coeff_zero γ hw₀ hF ht hFhol hFzero,
      hasSum_qExpansion_slash γ hw₀ hF ht hFhol hFzero⟩
  · exact integrableOn_petersson_exp_slash γ f hw₀ hm hk
  · rcases mem_multiplierCuspSpace_multiplierMapGL_one_iff.mp
      (multiplierCuspSpace_le_multiplierCuspSpace_ker v hg) with ⟨g, rfl⟩
    exact integrableOn_petersson_of_measure_lt_top k _ _ f g volume
      (volume_iUnion_out_inv_smul_fdo_lt_top G)

end ModularForm
