import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.ExponentialSum
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Holomorphy at a cusp from moderate growth

A holomorphic periodic function on the upper half plane that grows at most polynomially in `Im z` as
`Im z → ∞`, on a vertical strip, is bounded there: in the coordinate `q = e^{2πiz/p}` its
singularity at `q = 0` is removable, since `q` times a power of `log |q|` tends to `0`. So a
holomorphic function of moderate growth with a nebentypus law on `Γ₀(N)` is holomorphic at every
cusp.

## Main results

* `UpperHalfPlane.isBoundedAtImInfty_of_periodic_of_le_pow`: the boundedness at `i∞` of a
  holomorphic periodic function of polynomial growth.
* `ModularForm.isBoundedAtImInfty_slash_of_nebentypus`: moderate growth implies holomorphy at every
  cusp.
-/

open Complex Filter Topology Function Periodic CongruenceSubgroup TauCeti

open scoped Real Manifold ModularForm MatrixGroups

open UpperHalfPlane hiding I I_re I_im

open Matrix GeneralLinearGroup

namespace UpperHalfPlane

variable {h : ℍ → ℂ} {p K : ℝ} {M : ℕ}

private lemma abs_re_invQParam_le (hp : 0 < p) (q : ℂ) : |(invQParam p q).re| ≤ p := by
  have e : ((p : ℂ) / (2 * π * Complex.I)) = ((p / (2 * π) : ℝ) : ℂ) * (-Complex.I) := by
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring1
  have h1 : (invQParam p q).re = p / (2 * π) * q.arg := by
    rw [invQParam, e, mul_assoc, re_ofReal_mul]
    simp [Complex.log_im]
  have h2 : |q.arg| ≤ π := abs_arg_le_pi q
  have h3 : 0 < p / (2 * π) := by positivity
  rw [h1, abs_mul, abs_of_pos h3]
  have h4 : p / (2 * π) * π = p / 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left h2 h3.le]

/-- **A holomorphic periodic function of polynomial growth is bounded at `i∞`.** Let `h` be
holomorphic on `ℍ` with period `p > 0` and `‖h z‖ ≤ K (Im z) ^ M` for `Im z ≥ 1` and `|Re z| ≤ p`.
Then `h` is bounded as `Im z → ∞`. -/
lemma isBoundedAtImInfty_of_periodic_of_le_pow (hh : MDiff h) (hp : 0 < p)
    (hper : ∀ z : ℍ, h (p +ᵥ z) = h z)
    (hbd : ∀ z : ℍ, 1 ≤ z.im → |z.re| ≤ p → ‖h z‖ ≤ K * z.im ^ M) : IsBoundedAtImInfty h := by
  have hF : Periodic (h ∘ ofComplex) p := periodic_comp_ofComplex hper
  have hhol : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ (h ∘ ofComplex) z := by
    filter_upwards [preimage_mem_comap (Ioi_mem_atTop 0)] with z hz
    exact mdifferentiableAt_iff.mp (hh ⟨z, hz⟩)
  have hd : ∀ᶠ q in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (cuspFunction p (h ∘ ofComplex)) q :=
    eventually_differentiableAt_cuspFunction_nhds_ne_zero hp hF hhol
  have hx : Tendsto (fun q ↦ (invQParam p q).im) (𝓝[≠] (0 : ℂ)) atTop :=
    tendsto_comap_iff.mp (invQParam_tendsto hp)
  have hB : Tendsto (fun x : ℝ ↦ K * (x ^ (M : ℝ) * Real.exp (-(2 * π / p) * x))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (M : ℝ) (2 * π / p)
      (by positivity)).const_mul K
  have hG : cuspFunction p (h ∘ ofComplex) =o[𝓝[≠] 0] fun q : ℂ ↦ (q - 0)⁻¹ := by
    refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq h0
      exact absurd (inv_eq_zero.mp h0) (sub_ne_zero.mpr hq)
    refine squeeze_zero_norm' ?_ (hB.comp hx)
    filter_upwards [self_mem_nhdsWithin, hx.eventually_ge_atTop 1] with q hq hq1
    have hq0 : q ≠ 0 := hq
    have him : 0 < (invQParam p q).im := by linarith
    have h1 : cuspFunction p (h ∘ ofComplex) q = h ⟨invQParam p q, him⟩ := by
      rw [cuspFunction_eq_of_nonzero _ _ hq0, Function.comp_apply, ofComplex_apply_of_im_pos him]
    have h2 : ‖q‖ = Real.exp (-(2 * π / p) * (invQParam p q).im) := by
      have h3 : ‖qParam p (invQParam p q)‖ = ‖q‖ := by
        rw [qParam_right_inv hp.ne' hq0]
      rw [← h3, norm_qParam]
      congr 1
      ring1
    have h4 : ‖h ⟨invQParam p q, him⟩‖ ≤ K * (invQParam p q).im ^ M :=
      hbd ⟨invQParam p q, him⟩ hq1 (abs_re_invQParam_le hp q)
    simp only [sub_zero, div_inv_eq_mul, norm_mul, Function.comp_apply, Real.rpow_natCast]
    rw [h1, h2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
  have hc : (fun _ : ℂ ↦ cuspFunction p (h ∘ ofComplex) 0) =o[𝓝[≠] 0] fun q : ℂ ↦ (q - 0)⁻¹ :=
    Asymptotics.isLittleO_const_left.mpr (Or.inr
      ((tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ)).congr fun q ↦ by simp))
  have hcoe : Tendsto (fun z : ℍ ↦ (z : ℂ)) atImInfty (comap Complex.im atTop) :=
    tendsto_comap_iff.mpr tendsto_comap
  have heq : (fun z : ℍ ↦ cuspFunction p (h ∘ ofComplex) (qParam p z)) = h := by
    ext z
    rw [eq_cuspFunction hp.ne' hF, Function.comp_apply, ofComplex_apply]
  rw [IsBoundedAtImInfty, ← heq]
  exact ((Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hd
    (hG.sub hc)).comp ((qParam_tendsto hp).comp hcoe)).isBigO_one ℝ

end UpperHalfPlane

namespace ModularForm

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ} {f : ℍ → ℂ} (γ : SL(2, ℤ)) {z : ℍ}

private lemma one_le_sq_intCast {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h1 : (0 : ℤ) < n ^ 2 := by positivity
  have h2 : (1 : ℤ) ≤ n ^ 2 := h1
  exact_mod_cast h2

private lemma normSq_denom_eq :
    Complex.normSq (denom γ z) = ((γ 1 0 : ℝ) * z.re + γ 1 1) ^ 2 + ((γ 1 0 : ℝ) * z.im) ^ 2 := by
  rw [ModularGroup.denom_apply, Complex.normSq_apply]
  simp [sq]

private lemma one_le_normSq_denom (hy : 1 ≤ z.im) : 1 ≤ Complex.normSq (denom γ z) := by
  rw [normSq_denom_eq]
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hd : γ 1 1 ≠ 0 := fun hd ↦ by
      have h1 : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
      rw [Matrix.det_fin_two, hd, hc] at h1
      simp at h1
    have h2 : (1 : ℝ) ≤ (γ 1 1 : ℝ) ^ 2 := one_le_sq_intCast hd
    simpa [hc] using h2
  · have h2 : (1 : ℝ) ≤ (γ 1 0 : ℝ) ^ 2 := one_le_sq_intCast hc
    have h3 : (1 : ℝ) ≤ z.im ^ 2 := one_le_pow₀ hy
    nlinarith [sq_nonneg ((γ 1 0 : ℝ) * z.re + γ 1 1),
      mul_le_mul h2 h3 zero_le_one (sq_nonneg (γ 1 0 : ℝ))]

private lemma normSq_denom_le (hy : 1 ≤ z.im) (hx : |z.re| ≤ N) : Complex.normSq (denom γ z) ≤
      ((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) * z.im ^ 2 := by
  have h1 : |(γ 1 0 : ℝ) * z.re + γ 1 1| ≤ |(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)| := by
    refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have h2 : ((γ 1 0 : ℝ) * z.re + γ 1 1) ^ 2 ≤ (|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (1 : ℝ) ≤ z.im ^ 2 := one_le_pow₀ hy
  rw [normSq_denom_eq]
  nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg (|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|))]

variable [NeZero N] in
/-- **Moderate growth implies holomorphy at every cusp.** A holomorphic `f` on `ℍ` of moderate
growth satisfying the nebentypus law of a character on `Γ₀(N)` in weight `k > 0` has `f ∣[k] γ`
bounded at `i∞` for every `γ ∈ SL(2, ℤ)`. -/
lemma isBoundedAtImInfty_slash_of_nebentypus (hf : MDiff f) (hk : 0 < k)
    (hlaw : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ℤ) • f) (hbd : HasModerateGrowth f) :
    IsBoundedAtImInfty (f ∣[k] γ) := by
  rcases hbd with ⟨K, M, hbd⟩
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hTN : (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma N := by
    have e :
        ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] :=
      ModularGroup.coe_T_zpow N
    have h00 : (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 0 0 = 1 := congrFun (congrFun e 0) 0
    have h01 : (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 0 1 = N := congrFun (congrFun e 0) 1
    have h10 : (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 0 = 0 := congrFun (congrFun e 1) 0
    have h11 : (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 1 = 1 := congrFun (congrFun e 1) 1
    refine Gamma_mem.mpr ⟨?_, ?_, ?_, ?_⟩
    · rw [h00, Int.cast_one]
    · rw [h01, Int.cast_natCast, ZMod.natCast_self]
    · rw [h10, Int.cast_zero]
    · rw [h11, Int.cast_one]
  have hδ : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (Gamma_normal N).conj_mem _ hTN γ
  have hδ₀ : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact (Gamma_mem.mp hδ).2.2.1
  have hδ₁ : f ∣[k] (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) = f := by
    rw [hlaw _ hδ₀, (Gamma_mem.mp hδ).2.2.2]
    simp
  have hT : (f ∣[k] γ) ∣[k] upperRightHom ((N : ℤ) : ℝ) = f ∣[k] γ := by
    rw [← ModularGroup.mapGL_T_zpow_eq_upperRightHom]
    have h1 : γ * ModularGroup.T ^ (N : ℤ) = (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) * γ := by
      group
    have h2 : (f ∣[k] γ) ∣[k] (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) = f ∣[k] γ := by
      rw [← SlashAction.slash_mul, h1, SlashAction.slash_mul, hδ₁]
    exact h2
  have hper : ∀ z : ℍ, (f ∣[k] γ) ((N : ℝ) +ᵥ z) = (f ∣[k] γ) z := fun z ↦ by
    have h3 : ((f ∣[k] γ) ∣[k] upperRightHom ((N : ℤ) : ℝ)) z = (f ∣[k] γ) z := congrFun hT z
    rw [ModularForm.slash_upperRightHom_apply] at h3
    simpa using h3
  have hK : 0 ≤ K := by
    have h3 : 0 ≤ UpperHalfPlane.I.im ^ (-(M : ℝ)) := Real.rpow_nonneg UpperHalfPlane.I.im_pos.le _
    have h4 : 0 ≤ K * (1 + UpperHalfPlane.I.im ^ (-(M : ℝ))) :=
      (norm_nonneg _).trans (hbd UpperHalfPlane.I)
    exact (mul_nonneg_iff_of_pos_right (by linarith)).mp h4
  refine UpperHalfPlane.isBoundedAtImInfty_of_periodic_of_le_pow
    (K := K * (1 + ((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) ^ M)) (M := M)
    (MDifferentiable.slash hf k _) hN hper fun z hy hx ↦ ?_
  have hD1 : 1 ≤ Complex.normSq (denom γ z) := one_le_normSq_denom γ hy
  have hD2 : Complex.normSq (denom γ z) ≤
      ((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) * z.im ^ 2 :=
    normSq_denom_le γ hy hx
  have hnorm : 1 ≤ ‖denom γ z‖ := by
    rw [Complex.normSq_eq_norm_sq] at hD1
    exact (one_le_sq_iff₀ (norm_nonneg _)).mp hD1
  have hz1 : ‖denom γ z‖ ^ (-k) ≤ 1 := zpow_le_one_of_nonpos₀ hnorm (by omega)
  have him : (γ • z).im = z.im / Complex.normSq (denom γ z) :=
    ModularGroup.im_smul_eq_div_normSq γ z
  have hy0 : 0 < z.im := z.im_pos
  have hnS : 0 < Complex.normSq (denom γ z) := by linarith
  have hw : ‖f (γ • z)‖ ≤ K * (1 + (γ • z).im ^ (-(M : ℝ))) := hbd (γ • z)
  rw [him, Real.rpow_neg (div_pos hy0 hnS).le, Real.rpow_natCast, ← inv_pow, inv_div] at hw
  have h4 : Complex.normSq (denom γ z) / z.im ≤
      ((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) * z.im := by
    rw [div_le_iff₀ hy0, mul_assoc, ← sq]
    exact hD2
  have h5 : (Complex.normSq (denom γ z) / z.im) ^ M ≤
      ((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) ^ M * z.im ^ M := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (div_pos hnS hy0).le h4 M
  rw [SL_slash_apply, norm_mul, norm_zpow]
  refine (mul_le_of_le_one_right (norm_nonneg _) hz1).trans (hw.trans ?_)
  rw [mul_assoc, add_mul, one_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add (one_le_pow₀ hy) h5) hK

end ModularForm
