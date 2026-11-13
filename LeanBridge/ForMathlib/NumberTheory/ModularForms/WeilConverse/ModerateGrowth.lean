import LeanBridge.ForMathlib.NumberTheory.ModularForms.GrowthCondition
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
cusp. In weight `k`, such a law and a bound `(Im z) ^ (-s)` with `k / 2 < s < k` give the vanishing
at every cusp.

## Main results

* `UpperHalfPlane.isBoundedAtImInfty_of_periodic_of_le_pow`: the boundedness at `i∞` of a
  holomorphic periodic function of polynomial growth.
* `ModularForm.isBoundedAtImInfty_slash_of_nebentypus`: moderate growth implies holomorphy at every
  cusp.
* `ModularForm.isZeroAtImInfty_slash_of_norm_le`: a bound `(Im z) ^ (-s)` with `k / 2 < s < k` gives
  the vanishing at the cusps in weight `k`.
-/

open Complex Filter Topology Function Periodic CongruenceSubgroup

open scoped Real Manifold ModularForm MatrixGroups

open UpperHalfPlane hiding I I_re I_im

namespace UpperHalfPlane

variable {h : ℍ → ℂ} {p K : ℝ} {M : ℕ}

/-- **A holomorphic periodic function of polynomial growth is bounded at `i∞`.** Let `h` be
holomorphic on `ℍ` with period `p > 0` and `‖h z‖ ≤ K (Im z) ^ M` for `Im z ≥ 1` and `|Re z| ≤ p`.
Then `h` is bounded as `Im z → ∞`: by periodicity the bound holds whenever `Im z ≥ 1`, so `h` has
moderate growth at `i∞` (`UpperHalfPlane.isBoundedAtImInfty_of_isModerateGrowthAtImInfty`). -/
lemma isBoundedAtImInfty_of_periodic_of_le_pow (hh : MDiff h) (hp : 0 < p)
    (hper : ∀ z : ℍ, h (p +ᵥ z) = h z)
    (hbd : ∀ z : ℍ, 1 ≤ z.im → |z.re| ≤ p → ‖h z‖ ≤ K * z.im ^ M) : IsBoundedAtImInfty h := by
  have hF : Periodic (h ∘ ofComplex) p := periodic_comp_ofComplex hper
  refine isBoundedAtImInfty_of_isModerateGrowthAtImInfty hp hF hh ⟨M, .of_bound K ?_⟩
  filter_upwards [(tendsto_comap : Tendsto im atImInfty atTop).eventually_ge_atTop 1] with z hz
  have him : 0 < ((z : ℂ) - ⌊z.re / p⌋ * p).im := by
    simpa using z.im_pos
  have h₁ : h z = h ⟨(z : ℂ) - ⌊z.re / p⌋ * p, him⟩ := by
    rw [← ofComplex_apply_of_im_pos him, ← Function.comp_apply (f := h), hF.sub_int_mul_eq,
      Function.comp_apply, ofComplex_apply]
  rw [h₁, Real.norm_of_nonneg (by positivity), Real.rpow_natCast]
  simpa using hbd ⟨_, him⟩ (by simpa using hz) (abs_le.mpr
    ⟨by simpa using (Int.sub_floor_div_mul_nonneg z.re hp).trans' (neg_nonpos.mpr hp.le),
      by simpa using (Int.sub_floor_div_mul_lt z.re hp).le⟩)

end UpperHalfPlane

namespace ModularForm

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ} {f : ℍ → ℂ} (γ : SL(2, ℤ)) {z : ℍ}

private lemma one_le_sq_intCast {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h1 : (0 : ℤ) < n ^ 2 := by positivity
  have h2 : (1 : ℤ) ≤ n ^ 2 := h1
  exact_mod_cast h2

lemma normSq_denom_eq :
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

lemma normSq_denom_le (hy : 1 ≤ z.im) (hx : |z.re| ≤ N) : Complex.normSq (denom γ z) ≤
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

variable (z) in
lemma slash_apply_T_zpow_mul_smul (hlaw : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ℤ) • f) (j : ℤ) :
    (f ∣[k] γ) (ModularGroup.T ^ ((N : ℤ) * j) • z) = (f ∣[k] γ) z := by
  have e : ((ModularGroup.T ^ ((N : ℤ) * j) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, (N : ℤ) * j; 0, 1] :=
    ModularGroup.coe_T_zpow _
  have h10 : (ModularGroup.T ^ ((N : ℤ) * j) : SL(2, ℤ)) 1 0 = 0 := congrFun (congrFun e 1) 0
  have h11 : (ModularGroup.T ^ ((N : ℤ) * j) : SL(2, ℤ)) 1 1 = 1 := congrFun (congrFun e 1) 1
  have hδ : γ * ModularGroup.T ^ ((N : ℤ) * j) * γ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (Gamma_normal N).conj_mem _ (ModularGroup_T_pow_mem_Gamma N _ (dvd_mul_right _ _)) γ
  have hδ₁ : f ∣[k] (γ * ModularGroup.T ^ ((N : ℤ) * j) * γ⁻¹) = f := by
    rw [hlaw _ (Gamma0_mem.mpr (Gamma_mem.mp hδ).2.2.1), (Gamma_mem.mp hδ).2.2.2]
    simp
  have h1 : γ * ModularGroup.T ^ ((N : ℤ) * j) = γ * ModularGroup.T ^ ((N : ℤ) * j) * γ⁻¹ * γ := by
    group
  have h2 : (f ∣[k] γ) ∣[k] (ModularGroup.T ^ ((N : ℤ) * j) : SL(2, ℤ)) = f ∣[k] γ := by
    rw [← SlashAction.slash_mul, h1, SlashAction.slash_mul, hδ₁]
  have h3 : ((f ∣[k] γ) ∣[k] (ModularGroup.T ^ ((N : ℤ) * j) : SL(2, ℤ))) z = (f ∣[k] γ) z :=
    congrFun h2 z
  rw [SL_slash_apply, ModularGroup.denom_apply, h10, h11] at h3
  simpa using h3

variable [NeZero N] in
/-- **Moderate growth implies holomorphy at every cusp.** A holomorphic `f` on `ℍ` of moderate
growth satisfying the nebentypus law of a character on `Γ₀(N)` in weight `k > 0` has `f ∣[k] γ`
bounded at `i∞` for every `γ ∈ SL(2, ℤ)`. -/
lemma isBoundedAtImInfty_slash_of_nebentypus (hf : MDiff f) (hk : 0 < k)
    (hlaw : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ℤ) • f) (hbd : HasModerateGrowth f) :
    IsBoundedAtImInfty (f ∣[k] γ) := by
  rcases hbd with ⟨K, M, hbd⟩
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hper : ∀ z : ℍ, (f ∣[k] γ) ((N : ℝ) +ᵥ z) = (f ∣[k] γ) z := fun z ↦ by
    rw [← slash_apply_T_zpow_mul_smul γ z hlaw 1, mul_one, modular_T_zpow_smul, Int.cast_natCast]
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

variable [NeZero N] in
/-- **The bound `(Im z) ^ (-s)` gives the vanishing at the cusps** for `k / 2 < s < k`: if `f` has
the nebentypus law of a character on `Γ₀(N)` in weight `k`, and `|f(z)| ≤ K (Im z) ^ (-s)` on `ℍ`,
then `f ∣[k] γ` vanishes at `i∞` for every `γ ∈ SL(2, ℤ)`, since `f ∣[k] γ` is periodic and
`|f ∣[k] γ (z)| ≤ K y ^ (-s) |c z + d| ^ (2 s - k)` is `O(y ^ (s - k))` on a vertical strip. -/
lemma isZeroAtImInfty_slash_of_norm_le {K s : ℝ}
    (hlaw : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ℤ) • f) (hK0 : 0 ≤ K)
    (hbd : ∀ z : ℍ, ‖f z‖ ≤ K * z.im ^ (-s)) (h1 : (k : ℝ) / 2 < s) (h2 : s < k) :
    IsZeroAtImInfty (f ∣[k] γ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hs : 0 < s - (k : ℝ) / 2 := by linarith
  have hd : 0 < (k : ℝ) - s := by linarith
  have hC : 0 ≤ (|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2 := by positivity
  have hlim : Tendsto (fun z : ℍ ↦ K * ((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) ^
      (s - (k : ℝ) / 2) * z.im ^ (-((k : ℝ) - s))) atImInfty (nhds 0) := by
    rw [← mul_zero (K * ((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) ^
      (s - (k : ℝ) / 2))]
    exact ((tendsto_rpow_neg_atTop hd).comp (tendsto_comap (f := UpperHalfPlane.im))).const_mul _
  refine squeeze_zero_norm' ?_ hlim
  have hev : ∀ᶠ z : ℍ in atImInfty, 1 ≤ z.im := tendsto_comap.eventually_ge_atTop 1
  filter_upwards [hev] with z hy
  have hfl : (⌊z.re / N⌋ : ℝ) ≤ z.re / N := Int.floor_le _
  have hlt : z.re / N < ⌊z.re / N⌋ + 1 := Int.lt_floor_add_one _
  have hre : z.re = z.re / N * N := by field_simp
  let z₀ : ℍ := (ModularGroup.T ^ ((N : ℤ) * (-⌊z.re / N⌋))) • z
  have hz₀ : z₀ = (((N : ℤ) * (-⌊z.re / N⌋) : ℤ) : ℝ) +ᵥ z := modular_T_zpow_smul z _
  have him : z₀.im = z.im := by rw [hz₀, vadd_im]
  have hre₀ : z₀.re = z.re - N * ⌊z.re / N⌋ := by
    rw [hz₀, vadd_re]
    push_cast
    ring1
  have hx : |z₀.re| ≤ N := by
    rw [abs_le, hre₀]
    constructor <;> nlinarith
  have hy₀ : 1 ≤ z₀.im := by rwa [him]
  have hpos : 0 < normSq (denom γ z₀) := normSq_pos.mpr (denom_ne_zero γ z₀)
  have hy0 : 0 < z₀.im := z₀.im_pos
  have hnorm : ‖denom γ z₀‖ ^ (-k) = normSq (denom γ z₀) ^ (-((k : ℝ) / 2)) := by
    have hn : 0 < ‖denom γ z₀‖ := norm_pos_iff.mpr (denom_ne_zero γ z₀)
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring1
  have hfz : ‖f (γ • z₀)‖ ≤ K * (γ • z₀).im ^ (-s) := hbd (γ • z₀)
  rw [ModularGroup.im_smul_eq_div_normSq, Real.div_rpow hy0.le hpos.le, Real.rpow_neg hpos.le,
    div_inv_eq_mul] at hfz
  have hmono : normSq (denom γ z₀) ^ (s - (k : ℝ) / 2) ≤
      ((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) ^ (s - (k : ℝ) / 2) *
        (z₀.im ^ 2) ^ (s - (k : ℝ) / 2) := by
    rw [← Real.mul_rpow hC (by positivity)]
    exact Real.rpow_le_rpow hpos.le (normSq_denom_le γ hy₀ hx) hs.le
  have hz : (f ∣[k] γ) z = (f ∣[k] γ) z₀ :=
    (slash_apply_T_zpow_mul_smul γ z hlaw (-⌊z.re / N⌋)).symm
  have hD : 0 < normSq (denom γ z₀) ^ (-((k : ℝ) / 2)) := Real.rpow_pos_of_pos hpos _
  have e1 : normSq (denom γ z₀) ^ s * normSq (denom γ z₀) ^ (-((k : ℝ) / 2)) =
      normSq (denom γ z₀) ^ (s - (k : ℝ) / 2) := by
    rw [← Real.rpow_add hpos, sub_eq_add_neg]
  have e2 : (z₀.im ^ 2) ^ (s - (k : ℝ) / 2) * z₀.im ^ (-s) = z₀.im ^ (-((k : ℝ) - s)) := by
    rw [← Real.rpow_natCast z₀.im 2, ← Real.rpow_mul hy0.le, ← Real.rpow_add hy0]
    congr 1
    push_cast
    ring1
  have h5 : K * z₀.im ^ (-s) * normSq (denom γ z₀) ^ (s - (k : ℝ) / 2) ≤
      K * z₀.im ^ (-s) * (((|(γ 1 0 : ℝ)| * N + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2) ^
        (s - (k : ℝ) / 2) * (z₀.im ^ 2) ^ (s - (k : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  rw [hz, SL_slash_apply, norm_mul, norm_zpow, hnorm, ← him]
  refine (mul_le_mul_of_nonneg_right hfz hD.le).trans ?_
  have e3 : K * (z₀.im ^ (-s) * normSq (denom γ z₀) ^ s) * normSq (denom γ z₀) ^ (-((k : ℝ) / 2)) =
      K * z₀.im ^ (-s) * normSq (denom γ z₀) ^ (s - (k : ℝ) / 2) := by
    rw [← e1]
    ring1
  rw [e3]
  refine h5.trans_eq ?_
  rw [← e2]
  ring1

end ModularForm
