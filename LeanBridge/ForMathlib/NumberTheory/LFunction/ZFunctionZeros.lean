import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticRank
import LeanBridge.ForMathlib.NumberTheory.LFunction.ZFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The zeros of the Z-function of an analytic L-function

The Z-function of an analytic L-function `L` is
`Z(t) = ± conj ε ^ (1 / 2) γ(1 / 2 + i t) / |γ(1 / 2 + i t)| L(1 / 2 + i t)`, where
`γ(s) = N ^ (s / 2) L_∞(s)` (`AnalyticLFunction.zFunction`). The factor `γ` is holomorphic and
nonzero on the critical line, so `t ↦ |γ(1 / 2 + i t)|` is real analytic, and near a point `t₀`,
where `L(s) = (s - s₀) ^ m g(s)` with `s₀ = 1 / 2 + i t₀`, `g` holomorphic and `g(s₀) ≠ 0`, the
Z-function is `Z(t) = (t - t₀) ^ m q(t)` with `q` real analytic and `q(t₀) ≠ 0`: the complex
function `q` is real away from `t₀`, as `Z` is, hence also at `t₀`. So the Z-function is a real
analytic, in particular smooth, real-valued function, its zeros are the `t` such that
`1 / 2 + i t` is a zero of `L`, with the same multiplicities, and it changes sign at the zeros of
odd multiplicity (LMFDB `lfunction.zfunction`).

## Main results

* `AnalyticLFunction.analyticAt_zFunction`: the Z-function is real analytic.
* `AnalyticLFunction.contDiff_zFunction` (LMFDB `lfunction.zfunction`): the Z-function is smooth.
* `AnalyticLFunction.analyticOrderAt_zFunction` (LMFDB `lfunction.zfunction`): the order of the
  zero of `Z` at `t` is the order of the zero of `L` at `1 / 2 + i t`.
* `AnalyticLFunction.eventually_zFunction_mul_zFunction_neg` (LMFDB `lfunction.zfunction`): the
  Z-function changes sign at the zeros of `L(1 / 2 + i t)` of odd multiplicity.
-/

open Complex Filter Set

open scoped ComplexConjugate ContDiff Topology

namespace AnalyticLFunction

variable (L : AnalyticLFunction) (t₀ : ℝ) {s : ℂ}

lemma analyticAt_centralPoint_add_mul_I : AnalyticAt ℝ (fun t : ℝ ↦ centralPoint + t * I) t₀ :=
  analyticAt_const.add ((ofRealCLM.analyticAt t₀).mul analyticAt_const)

lemma analyticAt_comp_centralPoint_add_mul_I {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (centralPoint + t₀ * I)) :
    AnalyticAt ℝ (fun t : ℝ ↦ f (centralPoint + t * I)) t₀ :=
  hf.restrictScalars.comp_of_eq (analyticAt_centralPoint_add_mul_I t₀) rfl

private lemma analyticAt_norm_of_ne_zero {f : ℝ → ℂ} (hf : AnalyticAt ℝ f t₀) (hf₀ : f t₀ ≠ 0) :
    AnalyticAt ℝ (fun t ↦ ‖f t‖) t₀ := by
  have hre : AnalyticAt ℝ (fun t ↦ (f t).re) t₀ :=
    (reCLM.analyticAt _).comp hf
  have him : AnalyticAt ℝ (fun t ↦ (f t).im) t₀ :=
    (imCLM.analyticAt _).comp hf
  have hn : AnalyticAt ℝ (fun t ↦ normSq (f t)) t₀ :=
    (hre.fun_mul hre).fun_add (him.fun_mul him)
  have hexp : AnalyticAt ℝ (fun t ↦ Real.exp (Real.log (normSq (f t)) * (1 / 2))) t₀ :=
    ((hn.log (normSq_pos.mpr hf₀)).fun_mul analyticAt_const).rexp'
  refine hexp.congr ?_
  filter_upwards [hf.continuousAt.eventually_ne hf₀] with t ht
  rw [norm_def, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (normSq_pos.mpr ht)]

lemma analyticAt_completingFactor (hs : 0 < s.re) : AnalyticAt ℂ L.completingFactor s := by
  refine DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
    (fun z hz ↦ (L.differentiableAt_completingFactor hz).differentiableWithinAt) ?_
  exact (isOpen_lt continuous_const continuous_re).mem_nhds hs

lemma exists_zFunction_eq_pow_mul : ∃ q : ℝ → ℝ, AnalyticAt ℝ q t₀ ∧ q t₀ ≠ 0 ∧
    ∀ᶠ t in 𝓝 t₀, L.zFunction t =
      (t - t₀) ^ analyticOrderNatAt L.toFun (centralPoint + t₀ * I) * q t := by
  have h₁ : centralPoint + t₀ * I ≠ 1 :=
    centralPoint_add_mul_I_ne_one t₀
  have hord : analyticOrderAt L.toFun (centralPoint + t₀ * I) =
      analyticOrderNatAt L.toFun (centralPoint + t₀ * I) :=
    (Nat.cast_analyticOrderNatAt (L.analyticOrderAt_toFun_ne_top h₁)).symm
  generalize analyticOrderNatAt L.toFun (centralPoint + t₀ * I) = m at hord ⊢
  rcases (L.analyticAt_toFun h₁).analyticOrderAt_eq_natCast.mp hord with ⟨g, hg, hg₀, hLg⟩
  have hγ : AnalyticAt ℝ (fun t : ℝ ↦ L.completingFactor (centralPoint + t * I)) t₀ :=
    analyticAt_comp_centralPoint_add_mul_I t₀ (L.analyticAt_completingFactor (by simp))
  have hγ₀ (t : ℝ) : L.completingFactor (centralPoint + t * I) ≠ 0 :=
    L.completingFactor_ne_zero (by simp)
  -- `Z(t) = (t - t₀) ^ m Q(t)` for a real analytic `Q : ℝ → ℂ` with `Q(t₀) ≠ 0`.
  let Q : ℝ → ℂ := fun t ↦ L.zFunctionSign * conj L.sign ^ (2⁻¹ : ℂ) *
    (L.completingFactor (centralPoint + t * I) / ‖L.completingFactor (centralPoint + t * I)‖) *
      (I ^ m * g (centralPoint + t * I))
  have hQ : AnalyticAt ℝ Q t₀ := by
    refine analyticAt_const.mul (hγ.div ((ofRealCLM.analyticAt _).comp
      (analyticAt_norm_of_ne_zero t₀ hγ (hγ₀ t₀))) ?_) |>.mul
      (analyticAt_const.mul (analyticAt_comp_centralPoint_add_mul_I t₀ hg))
    simpa using hγ₀ t₀
  have hQ₀ : Q t₀ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
      (mul_ne_zero (pow_ne_zero _ I_ne_zero) ?_)
    · exact ofReal_ne_zero.mpr <| abs_ne_zero.mp <| L.abs_zFunctionSign ▸ one_ne_zero
    · exact norm_ne_zero_iff.mp (L.norm_sqrt_conj_sign ▸ one_ne_zero)
    · exact div_ne_zero (hγ₀ t₀) (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hγ₀ t₀)))
    · simpa using hg₀
  have hZ : ∀ᶠ t in 𝓝 t₀, (L.zFunction t : ℂ) = ((t - t₀ : ℝ) : ℂ) ^ m * Q t := by
    filter_upwards [(analyticAt_centralPoint_add_mul_I t₀).continuousAt.eventually hLg] with t ht
    rw [ofReal_zFunction, ht, smul_eq_mul, (by push_cast; ring1 :
      centralPoint + t * I - (centralPoint + t₀ * I) = ((t - t₀ : ℝ) : ℂ) * I), mul_pow]
    ring1
  -- `Q` is real away from `t₀`, as `Z` is, hence at `t₀`.
  have him : (Q t₀).im = 0 := by
    refine tendsto_nhds_unique (l := 𝓝[≠] t₀)
      ((continuous_im.continuousAt.comp hQ.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [nhdsWithin_le_nhds hZ, self_mem_nhdsWithin] with t ht ht₀
    have h : (L.zFunction t : ℂ).im = (((t - t₀ : ℝ) : ℂ) ^ m * Q t).im :=
      congrArg im ht
    rw [ofReal_im, ← ofReal_pow, im_ofReal_mul] at h
    exact ((mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr ht₀))).symm
  refine ⟨fun t ↦ (Q t).re, (reCLM.analyticAt _).comp hQ, fun h ↦ hQ₀ (Complex.ext h him), ?_⟩
  filter_upwards [hZ] with t ht
  have h : (L.zFunction t : ℂ).re = (((t - t₀ : ℝ) : ℂ) ^ m * Q t).re :=
    congrArg re ht
  rwa [ofReal_re, ← ofReal_pow, re_ofReal_mul] at h

/-- **The Z-function is real analytic.** -/
lemma analyticAt_zFunction : AnalyticAt ℝ L.zFunction t₀ := by
  rcases L.exists_zFunction_eq_pow_mul t₀ with ⟨q, hq, -, h⟩
  exact (((analyticAt_id.sub analyticAt_const).pow _).mul hq).congr (h.mono fun t ht ↦ ht.symm)

/-- **The Z-function is smooth** (LMFDB `lfunction.zfunction`), as it is real analytic. -/
lemma contDiff_zFunction : ContDiff ℝ ∞ L.zFunction :=
  AnalyticOnNhd.contDiff fun t _ ↦ L.analyticAt_zFunction t

/-- **The zeros of the Z-function have the multiplicities of the zeros of `L(1 / 2 + i t)`**
(LMFDB `lfunction.zfunction`): the order of vanishing of `Z` at `t` is the order of vanishing of
`L` at `1 / 2 + i t`. -/
lemma analyticOrderAt_zFunction :
    analyticOrderAt L.zFunction t₀ = analyticOrderAt L.toFun (centralPoint + t₀ * I) := by
  rcases L.exists_zFunction_eq_pow_mul t₀ with ⟨q, hq, hq₀, h⟩
  rw [← Nat.cast_analyticOrderNatAt (L.analyticOrderAt_toFun_ne_top
    (centralPoint_add_mul_I_ne_one t₀))]
  exact (L.analyticAt_zFunction t₀).analyticOrderAt_eq_natCast.mpr ⟨q, hq, hq₀, by simpa using h⟩

/-- **The Z-function changes sign at the zeros of odd multiplicity** (LMFDB `lfunction.zfunction`):
if `L` vanishes at `1 / 2 + i t₀` to odd order, then `Z(t)` and `Z(u)` have opposite signs for
`t < t₀ < u` close enough to `t₀`. -/
lemma eventually_zFunction_mul_zFunction_neg
    (h : Odd (analyticOrderNatAt L.toFun (centralPoint + t₀ * I))) :
    ∀ᶠ t in 𝓝[<] t₀, ∀ᶠ u in 𝓝[>] t₀, L.zFunction t * L.zFunction u < 0 := by
  rcases L.exists_zFunction_eq_pow_mul t₀ with ⟨q, hq, hq₀, hZ⟩
  have hpos : ∀ᶠ t in 𝓝 t₀, 0 < q t * q t₀ :=
    (hq.continuousAt.mul continuousAt_const).eventually (lt_mem_nhds (mul_self_pos.mpr hq₀))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hZ.and hpos)] with t ht ⟨hZt, hqt⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hZ.and hpos)] with u hu ⟨hZu, hqu⟩
  have h₁ : (t - t₀) ^ analyticOrderNatAt L.toFun (centralPoint + t₀ * I) < 0 :=
    h.pow_neg (sub_neg.mpr ht)
  have h₂ : 0 < (u - t₀) ^ analyticOrderNatAt L.toFun (centralPoint + t₀ * I) :=
    pow_pos (sub_pos.mpr hu) _
  have h₃ : 0 < q t * q u :=
    pos_of_mul_pos_left (by nlinarith [mul_pos hqt hqu]) (mul_self_nonneg (q t₀))
  rw [hZt, hZu]
  nlinarith [mul_neg_of_neg_of_pos h₁ h₂]

end AnalyticLFunction
