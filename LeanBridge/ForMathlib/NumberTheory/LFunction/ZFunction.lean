import LeanBridge.ForMathlib.NumberTheory.LFunction.LowestZero
import Mathlib.Analysis.Complex.Convex

/-!
# The Z-function of an analytic L-function

Write the completed L-function of an analytic L-function as `Λ(s) = γ(s) L(s)`, where
`γ(s) = N ^ (s / 2) L_∞(s)`; the functional equation reads `Λ(s) = ε conj (Λ (1 - conj s))`. The
Z-function is the real-valued function

`Z(t) = conj ε ^ (1 / 2) γ(1 / 2 + i t) / |γ(1 / 2 + i t)| L(1 / 2 + i t)`

of a real variable, with the square root chosen so that `Z(t) > 0` for small `t > 0`. It satisfies
`|Z(t)| = |L(1 / 2 + i t)|`, so that its zeros are the `t` such that `1 / 2 + i t` is a zero of the
L-function.

The axioms of an analytic L-function only give `Λ(s) = γ(s) L(s)` for `re s > 1`; the identity
theorem extends it to `re s > 0`, `s ≠ 1`, and in particular to the critical line.

## Main definitions

* `AnalyticLFunction.completingFactor`: the factor `γ(s) = N ^ (s / 2) L_∞(s)` with
  `Λ(s) = γ(s) L(s)`.
* `AnalyticLFunction.zFunction` (LMFDB `lfunction.zfunction`): the Z-function of an analytic
  L-function.

## Main results

* `AnalyticLFunction.completed_eq_of_re_pos`: `Λ(s) = γ(s) L(s)` for `re s > 0`, `s ≠ 1`.
* `AnalyticLFunction.ofReal_zFunction`: the Z-function is
  `±conj ε ^ (1 / 2) γ(1 / 2 + i t) / |γ(1 / 2 + i t)| L(1 / 2 + i t)`.
* `AnalyticLFunction.abs_zFunction`: `|Z(t)| = |L(1 / 2 + i t)|`.
* `AnalyticLFunction.zFunction_eq_zero_iff`: the zeros of the Z-function are the `t` such that
  `1 / 2 + i t` is a zero of the L-function.
* `AnalyticLFunction.eventually_zFunction_pos`: `Z(t) > 0` for small `t > 0`.
-/

open Complex Filter Set
open scoped ComplexConjugate Topology

lemma Complex.differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  simpa using (differentiable_Gammaℝ_inv s).fun_inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {s : ℂ} (t : ℝ)

private lemma differentiableAt_multiset_prod {m : Multiset ℂ} {f : ℂ → ℂ → ℂ}
    (h : ∀ x ∈ m, DifferentiableAt ℂ (f x) s) :
    DifferentiableAt ℂ (fun s ↦ (m.map fun x ↦ f x s).prod) s := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    simpa using (h x (Multiset.mem_cons_self x m)).fun_mul
      (ih fun y hy ↦ h y (Multiset.mem_cons_of_mem hy))

lemma SelbergData.differentiableAt_gammaFactor (D : SelbergData) (hs : 0 < s.re) :
    DifferentiableAt ℂ D.gammaFactor s := by
  refine (differentiableAt_multiset_prod fun x hx ↦ ?_).mul
    (differentiableAt_multiset_prod fun x hx ↦ ?_)
  · refine (differentiableAt_Gammaℝ_of_re_pos ?_).comp s (differentiableAt_id.add_const x)
    rcases D.re_eq_zero_or_one_of_mem_μ x hx with h | h <;> simp [h, hs, add_pos]
  · rcases D.exists_two_mul_re_eq_of_mem_ν x hx with ⟨k, hk, hx⟩
    have hre : 0 < (s + x).re := by
      rw [add_re]
      linarith [(Nat.cast_pos.mpr hk : (0 : ℝ) < k)]
    have hre₁ : 0 < (s + x + 1).re := by
      rw [add_re, one_re]
      linarith
    simp_rw [← Gammaℝ_mul_Gammaℝ_add_one]
    exact ((differentiableAt_Gammaℝ_of_re_pos hre).comp s (differentiableAt_id.add_const x)).mul
      ((differentiableAt_Gammaℝ_of_re_pos hre₁).comp s
        ((differentiableAt_id.add_const x).add_const 1))

variable (s) in
/-- The factor `γ(s) = N ^ (s / 2) L_∞(s)` of an analytic L-function with conductor `N` and gamma
factor `L_∞(s)`, so that its completion is `Λ(s) = γ(s) L(s)` (`completed_eq_of_re_pos`). -/
noncomputable def completingFactor : ℂ :=
  (L.conductor : ℂ) ^ (s / 2) * L.selbergData.gammaFactor s

lemma completingFactor_ne_zero (hs : 0 < s.re) : L.completingFactor s ≠ 0 :=
  mul_ne_zero (by simp [conductor, L.selbergData.conductor_pos.ne'])
    (L.selbergData.gammaFactor_ne_zero hs)

lemma differentiableAt_completingFactor (hs : 0 < s.re) :
    DifferentiableAt ℂ L.completingFactor s :=
  ((differentiableAt_id.div_const 2).const_cpow <| .inl <| Nat.cast_ne_zero.mpr
    L.selbergData.conductor_pos.ne').mul (L.selbergData.differentiableAt_gammaFactor hs)

lemma eqOn_completed {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) (hU₀ : U ⊆ re ⁻¹' Ioi 0)
    (hU₁ : 1 ∉ U) {z : ℂ} (hz : z ∈ U) (hz₁ : 1 < z.re) :
    EqOn L.completed (fun s ↦ L.completingFactor s * L.toFun s) U := by
  have hU' : U ⊆ {0, 1}ᶜ := fun s hs ↦ by
    rintro (rfl | rfl)
    · simpa using hU₀ hs
    · exact hU₁ hs
  refine (L.differentiableOn_completed.mono hU').analyticOnNhd hU
    |>.eqOn_of_preconnected_of_eventuallyEq ?_ hUc.isPreconnected hz ?_
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ DifferentiableAt.differentiableWithinAt <|
      (L.differentiableAt_completingFactor (hU₀ hs)).mul ?_) hU
    exact L.differentiableOn_toFun.differentiableAt <| isOpen_compl_singleton.mem_nhds
      fun h ↦ hU₁ (h ▸ hs)
  · filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (mem_Ioi.mpr hz₁ : z ∈ re ⁻¹' Ioi 1)] with s hs
    exact L.completed_eq hs

/-- The completion of an analytic L-function is `Λ(s) = γ(s) L(s)` for `re s > 0`, `s ≠ 1`, where
`γ(s) = N ^ (s / 2) L_∞(s)`. -/
lemma completed_eq_of_re_pos (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    L.completed s = L.completingFactor s * L.toFun s := by
  rcases lt_or_ge 1 s.re with h | h
  · exact L.completed_eq h
  rcases lt_or_ge (s.re - 1) s.im with h' | h'
  · refine L.eqOn_completed (U := {z | 0 < z.re} ∩ {z | -1 < z.im - z.re})
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).inter <|
        isOpen_lt continuous_const (continuous_im.sub continuous_re))
      ((convex_halfSpace_re_gt (r := 0)).inter <|
        convex_halfSpace_gt (.mk (fun x y ↦ by simp; ring1) fun c x ↦ by simp; ring1) _)
      (fun z hz ↦ hz.1) (by simp) (z := 2 + 2 * I) (by norm_num) (by norm_num) ⟨hs, by grind⟩
  · refine L.eqOn_completed (U := {z | 0 < z.re} ∩ {z | z.im + z.re < 1})
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).inter <|
        isOpen_lt (continuous_im.add continuous_re) continuous_const)
      ((convex_halfSpace_re_gt (r := 0)).inter <|
        convex_halfSpace_lt (.mk (fun x y ↦ by simp; ring1) fun c x ↦ by simp; ring1) _)
      (fun z hz ↦ hz.1) (by simp) (z := 2 - 2 * I) (by norm_num) (by norm_num)
      ⟨hs, lt_of_le_of_ne (by linarith : s.im + s.re ≤ 1) fun hi ↦ hs₁ <| Complex.ext ?_ ?_⟩ <;>
      simp <;> linarith

lemma centralPoint_add_mul_I_ne_zero : centralPoint + t * I ≠ 0 :=
  ne_of_apply_ne re <| by norm_num

lemma centralPoint_add_mul_I_ne_one : centralPoint + t * I ≠ 1 :=
  ne_of_apply_ne re <| by norm_num

lemma norm_sqrt_conj_sign : ‖conj L.sign ^ (2⁻¹ : ℂ)‖ = 1 := by
  have h : ‖conj L.sign ^ (2⁻¹ : ℂ)‖ ^ 2 = 1 ^ 2 := by
    rw [← norm_pow, cpow_ofNat_inv_pow, norm_conj, L.norm_sign, one_pow]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h

/-- The Z-function up to sign: `conj ε ^ (1 / 2) Λ(1 / 2 + i t) / |γ(1 / 2 + i t)|`, where the
square root is the principal one. -/
noncomputable def zFunctionAux : ℂ :=
  conj L.sign ^ (2⁻¹ : ℂ) * L.completed (centralPoint + t * I) /
    ‖L.completingFactor (centralPoint + t * I)‖

lemma conj_zFunctionAux : conj (L.zFunctionAux t) = L.zFunctionAux t := by
  have hΛ : conj (L.completed (centralPoint + t * I)) =
      conj L.sign * L.completed (centralPoint + t * I) := by
    simpa using congrArg conj <| L.completed_eq_sign_mul_conj_of_mem_criticalLine
      (s := centralPoint + t * I) <| by simp
  have hc : conj (conj L.sign ^ (2⁻¹ : ℂ)) * conj L.sign ^ (2⁻¹ : ℂ) = 1 := by
    rw [mul_comm, mul_conj, normSq_eq_norm_sq, L.norm_sqrt_conj_sign]
    norm_num
  rw [zFunctionAux, map_div₀, map_mul, hΛ, conj_ofReal]
  linear_combination -(conj (conj L.sign ^ (2⁻¹ : ℂ)) * L.completed (centralPoint + t * I) /
    ‖L.completingFactor (centralPoint + t * I)‖) * cpow_ofNat_inv_pow (conj L.sign) 2 +
    (conj L.sign ^ (2⁻¹ : ℂ) * L.completed (centralPoint + t * I) /
      ‖L.completingFactor (centralPoint + t * I)‖) * hc

lemma ofReal_re_zFunctionAux : ((L.zFunctionAux t).re : ℂ) = L.zFunctionAux t :=
  conj_eq_iff_re.mp <| L.conj_zFunctionAux t

lemma zFunctionAux_eq : L.zFunctionAux t = conj L.sign ^ (2⁻¹ : ℂ) *
    (L.completingFactor (centralPoint + t * I) / ‖L.completingFactor (centralPoint + t * I)‖) *
      L.toFun (centralPoint + t * I) := by
  rw [zFunctionAux, L.completed_eq_of_re_pos (by simp) (centralPoint_add_mul_I_ne_one t)]
  ring1

lemma norm_zFunctionAux : ‖L.zFunctionAux t‖ = ‖L.toFun (centralPoint + t * I)‖ := by
  rw [zFunctionAux_eq, norm_mul, norm_mul, norm_div, norm_sqrt_conj_sign, norm_real, norm_norm,
    div_self (norm_ne_zero_iff.mpr <| L.completingFactor_ne_zero <| by simp), one_mul, one_mul]

lemma continuous_zFunctionAux : Continuous L.zFunctionAux := by
  have hs : Continuous fun t : ℝ ↦ centralPoint + t * I := by
    fun_prop
  refine (continuous_const.mul ?_).div (continuous_ofReal.comp <| continuous_norm.comp ?_)
    fun t ↦ ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr <| L.completingFactor_ne_zero <| by simp
  · refine continuous_iff_continuousAt.mpr fun t ↦ ContinuousAt.comp (g := L.completed) ?_
      hs.continuousAt
    exact (L.differentiableOn_completed.differentiableAt <|
      (toFinite {0, 1}).isClosed.isOpen_compl.mem_nhds <| by
        simp [centralPoint_add_mul_I_ne_zero, centralPoint_add_mul_I_ne_one]).continuousAt
  · exact continuous_iff_continuousAt.mpr fun t ↦ ContinuousAt.comp (g := L.completingFactor)
      (L.differentiableAt_completingFactor <| by simp).continuousAt hs.continuousAt

open scoped Classical in
/-- The sign `±1` that makes the Z-function positive for small `t > 0`: `1` when
`zFunctionAux t` has positive real part for all small enough `t > 0`, and `-1` otherwise. -/
noncomputable def zFunctionSign : ℝ :=
  if ∀ᶠ t in 𝓝[>] 0, 0 < (L.zFunctionAux t).re then 1 else -1

/-- The **Z-function** (LMFDB `lfunction.zfunction`) of an analytic L-function: the real-valued
function `Z(t) = conj ε ^ (1 / 2) γ(1 / 2 + i t) / |γ(1 / 2 + i t)| L(1 / 2 + i t)`, where
`Λ(s) = γ(s) L(s)` with `γ(s) = N ^ (s / 2) L_∞(s)` and `ε` is the sign of the functional equation
(`ofReal_zFunction`). It is real because of the functional equation, `|Z(t)| = |L(1 / 2 + i t)|`
(`abs_zFunction`), and the square root of `conj ε` is chosen so that `Z(t) > 0` for small `t > 0`
(`eventually_zFunction_pos`). For the Riemann zeta function, `ζ(1 / 2) < 0` makes this the
negative of Mathlib's `hardyZ`. -/
noncomputable def zFunction : ℝ :=
  L.zFunctionSign * (L.zFunctionAux t).re

lemma abs_zFunctionSign : |L.zFunctionSign| = 1 := by
  rw [zFunctionSign]
  split_ifs <;> simp

/-- The Z-function is `Z(t) = conj ε ^ (1 / 2) γ(1 / 2 + i t) / |γ(1 / 2 + i t)| L(1 / 2 + i t)`,
where `γ(s) = N ^ (s / 2) L_∞(s)` and the square root of `conj ε` is `±` the principal one. -/
lemma ofReal_zFunction : (L.zFunction t : ℂ) = L.zFunctionSign * conj L.sign ^ (2⁻¹ : ℂ) *
    (L.completingFactor (centralPoint + t * I) / ‖L.completingFactor (centralPoint + t * I)‖) *
      L.toFun (centralPoint + t * I) := by
  rw [zFunction, ofReal_mul, ofReal_re_zFunctionAux, zFunctionAux_eq]
  ring1

/-- The Z-function has the same absolute value as the L-function on the critical line. -/
lemma abs_zFunction : |L.zFunction t| = ‖L.toFun (centralPoint + t * I)‖ := by
  rw [zFunction, abs_mul, abs_zFunctionSign, one_mul, ← L.norm_zFunctionAux t]
  exact abs_re_eq_norm.mpr <| conj_eq_iff_im.mp <| L.conj_zFunctionAux t

/-- The zeros of the Z-function are the `t` such that `1 / 2 + i t` is a zero of the L-function. -/
lemma zFunction_eq_zero_iff : L.zFunction t = 0 ↔ centralPoint + t * I ∈ L.zeros := by
  rw [← abs_eq_zero, abs_zFunction, norm_eq_zero, L.mem_zeros_iff (centralPoint_add_mul_I_ne_one t)]

open scoped Classical in
/-- The Z-function is positive for small `t > 0`. -/
lemma eventually_zFunction_pos : ∀ᶠ t in 𝓝[>] 0, 0 < L.zFunction t := by
  have ht : Tendsto (fun t : ℝ ↦ centralPoint + t * I) (𝓝[>] 0) (𝓝[≠] centralPoint) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using ((by fun_prop : Continuous fun t : ℝ ↦ centralPoint + t * I).tendsto
        0 |>.mono_left nhdsWithin_le_nhds)) <|
      eventually_nhdsWithin_of_forall fun t ht h ↦ ht.ne' <| by simpa using congrArg im h
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), (L.zFunctionAux t).re ≠ 0 :=
    (ht.eventually <| L.eventually_toFun_ne_zero <| by norm_num [centralPoint]).mono
      fun t hL h ↦ hL <| norm_eq_zero.mp <| by
        rw [← L.norm_zFunctionAux t, ← ofReal_re_zFunctionAux, h, ofReal_zero, norm_zero]
  rcases mem_nhdsGT_iff_exists_Ioo_subset.mp hne with ⟨δ, hδ, hsub⟩
  rcases (isPreconnected_Ioo.image _ (continuous_re.comp L.continuous_zFunctionAux).continuousOn)
    |>.subset_or_subset isOpen_Iio isOpen_Ioi (disjoint_left.mpr fun _ hx hx' ↦ lt_asymm hx hx')
      (by rintro _ ⟨t, ht, rfl⟩; exact lt_or_gt_of_ne (hsub ht)) with h | h
  · have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), (L.zFunctionAux t).re < 0 :=
      mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht ↦ h ⟨t, ht, rfl⟩
    have hσ : L.zFunctionSign = -1 :=
      ite_eq_right_iff.mpr fun hpos ↦ ((hpos.and hneg).exists.elim fun _ h ↦ lt_asymm h.1 h.2).elim
    filter_upwards [hneg] with t ht
    rw [zFunction, hσ]
    linarith
  · have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (L.zFunctionAux t).re :=
      mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht ↦ h ⟨t, ht, rfl⟩
    have hσ : L.zFunctionSign = 1 :=
      ite_eq_left_iff.mpr fun h ↦ absurd hpos h
    filter_upwards [hpos] with t ht
    rwa [zFunction, hσ, one_mul]

end AnalyticLFunction
