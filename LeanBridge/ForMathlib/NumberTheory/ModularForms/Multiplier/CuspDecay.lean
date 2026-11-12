import LeanBridge.ForMathlib.NumberTheory.ModularForms.GrowthCondition
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.CuspForm
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.NumberTheory.ModularForms.Bounds
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Cusp forms with a multiplier decay exponentially at the cusps

Let `G` be a subgroup of finite index of `SL(2, ℤ)` and `v : G → S¹` any multiplier, of finite
or infinite order. A cusp form `f` of weight `k` and multiplier `v` on `G` vanishes at every cusp,
but its translates `F = f ∣[k] γ`, `γ ∈ SL(2, ℤ)`, are in general not periodic: a translation
`z ↦ z + h` of the conjugate group `γ⁻¹ G γ` only multiplies `F` by a number `c` of absolute
value `1`. Writing `c = e^{2πiκ}` with `0 < κ ≤ 1`, the function `e^{-2πiκz/h} F(z)` is periodic,
and `e^{-2πiκz/h} F(z) e^{2πiz/h} → 0` at `i∞`, so it is bounded there by the removable
singularity of `UpperHalfPlane.isBoundedAtImInfty_of_tendsto_mul_qParam`. Hence
`F(z) = O(e^{-2πκy/h})`: cusp forms with a multiplier decay exponentially at every cusp. With the
invariance of `y^k |f(z)|²` under `G` (as `|v| = 1`), Mathlib's
`ModularGroup.exists_bound_of_subgroup_invariant` then bounds `y^k |f(z)|²` on all of `ℍ`, as
Mathlib's `CuspFormClass.petersson_bounded_left` does for the trivial multiplier.

## Main results

* `UpperHalfPlane.isBigO_exp_of_vadd_eq_mul`: a holomorphic `F` with `F(z + h) = c F(z)`,
  `|c| = 1` and `h > 0`, tending to `0` at `i∞`, is `O(e^{-2πκy/h})` for some `κ > 0`.
* `ModularForm.exists_slash_vadd_eq_mul`: the translates of a cusp form with a multiplier are
  quasi-periodic.
* `ModularForm.exists_norm_petersson_le`: for a cusp form `f` of weight `k` and multiplier `v` on
  a subgroup of finite index of `SL(2, ℤ)`, `y^k |f(z)|²` is bounded on `ℍ`.
-/

open Filter Asymptotics Function Complex Matrix SpecialLinearGroup ModularGroup TauCeti ConjAct
  Subgroup OnePoint

open UpperHalfPlane hiding I

open scoped Topology Real ModularForm Manifold MatrixGroups Pointwise

namespace UpperHalfPlane

variable {F : ℍ → ℂ} {h : ℝ} {c : ℂ}

private lemma exists_cexp_eq (hc : ‖c‖ = 1) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ cexp (2 * π * I * κ) = c := by
  have hc' : cexp (c.arg * I) = c := by
    simpa [hc] using norm_mul_exp_arg_mul_I c
  have hπ : 0 < π := Real.pi_pos
  rcases lt_or_ge 0 c.arg with hpos | hneg
  · refine ⟨c.arg / (2 * π), by positivity,
      (div_le_one (by positivity)).mpr (by linarith [arg_le_pi c]), Eq.trans ?_ hc'⟩
    congr 1
    push_cast
    field_simp
  · refine ⟨c.arg / (2 * π) + 1, ?_, ?_, Eq.trans ?_ hc'⟩
    · have h2 : 0 < (c.arg + 2 * π) / (2 * π) :=
        div_pos (by linarith [neg_pi_lt_arg c]) (by positivity)
      rwa [add_div, div_self (by positivity : (2 * π) ≠ 0)] at h2
    · linarith [div_nonpos_of_nonpos_of_nonneg hneg (by positivity : (0 : ℝ) ≤ 2 * π)]
    · push_cast
      rw [mul_add, mul_one, exp_add, exp_two_pi_mul_I, mul_one]
      congr 1
      field_simp

/-- **Quasi-periodic holomorphic functions vanishing at `i∞` decay exponentially**: if `F` is
holomorphic on `ℍ`, `F(z + h) = c F(z)` with `|c| = 1` and `h > 0`, and `F → 0` at `i∞`, then
`F(z) = O(e^{-2πκy/h})` for some `κ > 0`: with `c = e^{2πiκ}`, `0 < κ ≤ 1`, the function
`e^{-2πiκz/h} F(z)` is periodic and bounded at `i∞`. -/
lemma isBigO_exp_of_vadd_eq_mul (hh : 0 < h) (hF : MDiff F) (hc : ‖c‖ = 1)
    (hper : ∀ τ : ℍ, F (h +ᵥ τ) = c * F τ) (hzero : IsZeroAtImInfty F) :
    ∃ κ : ℝ, 0 < κ ∧ F =O[atImInfty] fun τ ↦ Real.exp (-(2 * π * κ / h) * τ.im) := by
  rcases exists_cexp_eq hc with ⟨κ, hκ, hκ1, hcκ⟩
  have hh' : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  refine ⟨κ, hκ, ?_⟩
  have hpper : Periodic ((fun τ : ℍ ↦ cexp (-(2 * π * I * κ / h) * τ) * F τ) ∘ ofComplex) h := by
    refine periodic_comp_ofComplex fun τ ↦ ?_
    rw [hper, coe_vadd, ← hcκ, ← mul_assoc, ← exp_add]
    congr 2
    field_simp
    ring1
  have hphol : MDiff fun τ : ℍ ↦ cexp (-(2 * π * I * κ / h) * τ) * F τ :=
    MDifferentiable.mul ((by fun_prop : Differentiable ℂ fun z : ℂ ↦
      cexp (-(2 * π * I * κ / h) * z)).comp_mdifferentiable mdifferentiable_coe) hF
  have hpq : Tendsto (fun τ : ℍ ↦ cexp (-(2 * π * I * κ / h) * τ) * F τ * Periodic.qParam h τ)
      atImInfty (𝓝 0) := by
    refine squeeze_zero_norm (fun τ ↦ ?_) (tendsto_zero_iff_norm_tendsto_zero.mp hzero)
    have hy : 0 < τ.im := τ.im_pos
    have hexp : Real.exp (2 * π * κ / h * τ.im) * Real.exp (-2 * π * τ.im / h) ≤ 1 := by
      rw [← Real.exp_add]
      refine Real.exp_le_one_iff.mpr ?_
      have h1 : 2 * π * κ / h * τ.im + -2 * π * τ.im / h = 2 * π * τ.im / h * (κ - 1) := by
        field_simp
        ring1
      rw [h1]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    rw [norm_mul, norm_mul, norm_exp, Periodic.norm_qParam, coe_im]
    have hre : (-(2 * π * I * κ / h) * τ : ℂ).re = 2 * π * κ / h * τ.im := by
      simp
    rw [hre, mul_comm _ ‖F τ‖, mul_assoc]
    exact mul_le_of_le_one_right (norm_nonneg _) hexp
  have hFp : F = fun τ : ℍ ↦ cexp (2 * π * I * κ / h * τ) *
      (cexp (-(2 * π * I * κ / h) * τ) * F τ) := by
    funext τ
    rw [← mul_assoc, ← exp_add, neg_mul, add_neg_cancel, exp_zero, one_mul]
  have he : (fun τ : ℍ ↦ cexp (2 * π * I * κ / h * τ)) =O[atImInfty]
      fun τ ↦ Real.exp (-(2 * π * κ / h) * τ.im) :=
    isBigO_of_le _ fun τ ↦ by
      rw [norm_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
      refine le_of_eq (congrArg Real.exp ?_)
      simp
  rw [hFp]
  simpa using he.mul (isBoundedAtImInfty_of_tendsto_mul_qParam hh hpper hphol hpq)

end UpperHalfPlane

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} {v : G →* Circle} {k : ℤ} {f : ℍ → ℂ} (γ : SL(2, ℤ))

lemma slash_eq_smul_of_mem_multiplierCuspSpace (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v))
    (g : G) : f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f :=
  multiplierMapGL_apply_mapGL v g ▸ hf.1.2.1 ⟨_, Subgroup.mem_map_of_mem _ g.2⟩

variable [G.FiniteIndex]

lemma isZeroAtImInfty_slash_of_mem_multiplierCuspSpace
    (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v)) : IsZeroAtImInfty (f ∣[k] γ) := by
  rw [← isZeroAt_infty_iff, SL_slash, ← IsZeroAt.smul_iff]
  refine hf.2 ?_
  rw [IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨γ, by simp [mapGL]⟩

/-- **The translates of a cusp form with a multiplier are quasi-periodic**: for `f` of weight `k`
and multiplier `v` on a subgroup `G` of finite index of `SL(2, ℤ)` and `γ ∈ SL(2, ℤ)`, some
`h > 0` and `c` with `|c| = 1` give `(f ∣[k] γ)(z + h) = c (f ∣[k] γ)(z)`: `h` is the width at
`∞` of `γ⁻¹ G γ` and `c` the value of `v` at `γ (1, h; 0, 1) γ⁻¹ ∈ G`. -/
lemma exists_slash_vadd_eq_mul (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v)) :
    ∃ h : ℝ, 0 < h ∧ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ τ : ℍ, (f ∣[k] γ) (h +ᵥ τ) = c * (f ∣[k] γ) τ := by
  have : (toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • (G : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl)] using!
      IsArithmetic.conj (G : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ γ)⁻¹
  set Γ' : Subgroup (GL (Fin 2) ℝ) := toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • (G : Subgroup (GL (Fin 2) ℝ))
    with hΓ'
  have hu : GeneralLinearGroup.upperRightHom Γ'.strictWidthInfty ∈ Γ' :=
    Γ'.mem_strictPeriods_iff.mp Γ'.strictWidthInfty_mem_strictPeriods
  rw [hΓ', Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv,
    toConjAct_smul] at hu
  refine ⟨Γ'.strictWidthInfty, Γ'.strictWidthInfty_pos, multiplierMapGL v ⟨_, hu⟩,
    Circle.norm_coe _, fun τ ↦ ?_⟩
  have hmul : (γ : GL (Fin 2) ℝ) * GeneralLinearGroup.upperRightHom Γ'.strictWidthInfty =
      (γ : GL (Fin 2) ℝ) * GeneralLinearGroup.upperRightHom Γ'.strictWidthInfty *
        (γ : GL (Fin 2) ℝ)⁻¹ * (γ : GL (Fin 2) ℝ) := by
    group
  refine (ModularForm.slash_upperRightHom_apply k _ _ τ).symm.trans ?_
  rw [SL_slash, ← SlashAction.slash_mul]
  nth_rw 1 [hmul]
  rw [SlashAction.slash_mul, hf.1.2.1 ⟨_, hu⟩, smul_slash]
  simp [σ]

lemma isBoundedAtImInfty_norm_petersson_smul (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v)) :
    IsBoundedAtImInfty fun τ ↦ ‖petersson k f f (γ • τ)‖ := by
  rcases exists_slash_vadd_eq_mul γ hf with ⟨h, hh, c, hc, hper⟩
  rcases UpperHalfPlane.isBigO_exp_of_vadd_eq_mul hh (hf.1.1.slash k γ) hc hper
    (isZeroAtImInfty_slash_of_mem_multiplierCuspSpace γ hf) with ⟨κ, hκ, hO⟩
  simp_rw [← petersson_slash_SL]
  have hO2 : (fun τ ↦ ‖petersson k (f ∣[k] γ) (f ∣[k] γ) τ‖) =O[atImInfty]
      fun τ : ℍ ↦ τ.im ^ (k : ℝ) * Real.exp (-(2 * (2 * π * κ / h)) * τ.im) :=
    ((hO.norm_left.mul hO.norm_left).mul (isBigO_refl (fun τ : ℍ ↦ τ.im ^ k) _)).congr
      (fun τ ↦ by simp [petersson, SL_slash, abs_of_pos τ.im_pos])
      (fun τ ↦ by
        rw [Real.rpow_intCast, ← Real.exp_add, mul_comm]
        congr 2
        ring1)
  exact (hO2.trans_tendsto <| (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k _
    (by positivity)).comp (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop)).isBigO_one ℝ

/-- **Cusp forms with a multiplier are bounded in the Petersson norm** (any multiplier, of finite
or infinite order): for `f` of weight `k` and multiplier `v` on a subgroup `G` of finite index of
`SL(2, ℤ)`, `y^k |f(z)|²` is bounded on `ℍ`. It is invariant under `G`, since `|v| = 1`, and
bounded at every cusp by the exponential decay of the translates of `f`. -/
lemma exists_norm_petersson_le (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v)) :
    ∃ C, ∀ τ, ‖petersson k f f τ‖ ≤ C := by
  have hcont : Continuous f := hf.1.1.continuous
  have hinv : ∀ g ∈ (G : Subgroup (GL (Fin 2) ℝ)), ∀ τ : ℍ,
      ‖petersson k f f (g • τ)‖ = ‖petersson k f f τ‖ := by
    rintro _ ⟨g, hg, rfl⟩ τ
    refine (congrArg norm (petersson_slash_SL k f f g τ)).symm.trans ?_
    rw [slash_eq_smul_of_mem_multiplierCuspSpace hf ⟨g, hg⟩]
    simp [petersson]
  rcases ModularGroup.exists_bound_of_subgroup_invariant (petersson_continuous k hcont hcont).norm
    (isBoundedAtImInfty_norm_petersson_smul · hf) hinv with ⟨C, hC⟩
  exact ⟨C, fun τ ↦ by simpa using hC τ⟩

lemma norm_le_of_norm_petersson_le {F : ℍ → ℂ} {C : ℝ} (hC : ∀ τ, ‖petersson k F F τ‖ ≤ C) (τ : ℍ) :
    ‖F τ‖ ≤ √C / τ.im ^ ((k : ℝ) / 2) :=
  (le_div_iff₀ (by positivity)).mpr <| Real.le_sqrt_of_sq_le <| by
    simpa [petersson, abs_of_pos τ.im_pos, ← Real.rpow_mul_natCast τ.im_pos.le, field]
      using hC τ

end ModularForm
