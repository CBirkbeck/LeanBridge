import LeanBridge.ForMathlib.NumberTheory.LFunction.Basic
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# The analytic rank and the leading coefficient of an analytic L-function

The analytic rank of an analytic L-function is its order of vanishing at its central point, and
its leading coefficient is the first nonzero coefficient of its Taylor expansion there. In the
analytic normalisation the central point is `s = 1 / 2`; both invariants are unchanged by passing
to the arithmetic normalisation of any weight `w`, whose central point is `(w + 1) / 2`.

## Main definitions

* `AnalyticLFunction.analyticRank` (LMFDB `lfunction.analytic_rank`).
* `AnalyticLFunction.leadingCoeff` (LMFDB `lfunction.leading_coeff`).

## Main results

* `AnalyticAt.meromorphicTrailingCoeffAt_eq_iteratedDeriv_div_factorial`: the trailing
  coefficient of an analytic function of finite order `n` is its `n`-th Taylor coefficient.
* `AnalyticLFunction.natCast_analyticRank`: the order of vanishing at the central point is finite.
* `AnalyticLFunction.iteratedDeriv_eq_zero_of_lt_analyticRank` and
  `AnalyticLFunction.iteratedDeriv_analyticRank_ne_zero`: the analytic rank is the least `r` with
  `L⁽ʳ⁾(1 / 2) ≠ 0`.
* `AnalyticLFunction.leadingCoeff_eq_iteratedDeriv`: the leading coefficient is
  `L⁽ʳ⁾(1 / 2) / r!`, where `r` is the analytic rank.
* `AnalyticLFunction.analyticOrderNatAt_arithmeticNormalization` and
  `AnalyticLFunction.meromorphicTrailingCoeffAt_arithmeticNormalization`: the analytic rank and the
  leading coefficient do not depend on the normalisation.
* `AnalyticLFunction.analyticRank_congr` and `AnalyticLFunction.leadingCoeff_congr`: they only
  depend on the Dirichlet coefficients.
-/

open scoped Nat Topology

/-- The trailing coefficient of a function analytic at `x` of finite order `n` there is its `n`-th
Taylor coefficient `f⁽ⁿ⁾(x) / n!`. -/
lemma AnalyticAt.meromorphicTrailingCoeffAt_eq_iteratedDeriv_div_factorial {f : ℂ → ℂ} {x : ℂ}
    {n : ℕ} (hf : AnalyticAt ℂ f x) (hn : analyticOrderAt f x = n) :
    meromorphicTrailingCoeffAt f x = iteratedDeriv n f x / n ! := by
  have hf₀ : AnalyticAt ℂ (fun z ↦ f (z + x)) 0 :=
    hf.comp_of_eq (analyticAt_id.add analyticAt_const) (zero_add x)
  have hd (i : ℕ) : iteratedDeriv i (fun z ↦ f (z + x)) 0 = iteratedDeriv i f x := by
    simp [iteratedDeriv_comp_add_const]
  rcases (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp hn with ⟨hlt, hne⟩
  rcases hf₀.exists_eventuallyEq_sum_add_pow_mul (n + 1) with ⟨F, hF, hfF⟩
  have h :
      meromorphicTrailingCoeffAt (fun z ↦ f (z + x)) 0 = iteratedDeriv n f x / n ! + 0 * F 0 := by
    refine AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := n) (x := 0)
      (g := fun z ↦ iteratedDeriv n f x / n ! + z * F z) (by fun_prop) ?_ ?_
    · simp only [zero_mul, add_zero]
      exact div_ne_zero hne (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hfF] with z hz
    rw [hz, Finset.sum_range_succ, Finset.sum_eq_zero fun i hi ↦ by
      rw [hd, hlt i (Finset.mem_range.mp hi), smul_zero], hd, zpow_natCast]
    ring1
  rwa [zero_mul, add_zero,
    meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt, zero_add] at h

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {L' : AnalyticLFunction} (h : ∀ n ≠ 0, L.coeff n = L'.coeff n)
  (w : ℕ) {s : ℂ} (hs : s ≠ 1) {k : ℕ}

include hs in
lemma analyticAt_toFun : AnalyticAt ℂ L.toFun s :=
  L.analyticOnNhd_toFun s hs

include hs in
lemma analyticOrderAt_toFun_ne_top : analyticOrderAt L.toFun s ≠ ⊤ := by
  rcases L.exists_toFun_ne_zero with ⟨x, hx₁, hx⟩
  have hxU : (x : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    simpa using hx₁.ne'
  refine L.analyticOnNhd_toFun.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected hxU hs ?_
  exact (L.analyticOnNhd_toFun x hxU).analyticOrderAt_eq_zero.mpr hx ▸ ENat.zero_ne_top

/-- The **analytic rank** (LMFDB `lfunction.analytic_rank`) of an analytic L-function: the order
of vanishing of its continuation at its central point `s = 1 / 2` (LMFDB
`lfunction.central_point`). It is also the order of vanishing at `(w + 1) / 2` of the arithmetic
normalisation of any weight `w` (`analyticOrderNatAt_arithmeticNormalization`). The LMFDB's stored
values are typically upper bounds believed to be tight, a convention of its data. -/
noncomputable def analyticRank : ℕ :=
  analyticOrderNatAt L.toFun (1 / 2)

/-- The **leading coefficient** (LMFDB `lfunction.leading_coeff`) of an analytic L-function: the
first nonzero coefficient `L⁽ʳ⁾(1 / 2) / r!` of the Taylor expansion of its continuation at its
central point `s = 1 / 2`, where `r` is the analytic rank (`leadingCoeff_eq_iteratedDeriv`). It is
also the leading coefficient at `(w + 1) / 2` of the arithmetic normalisation of any weight `w`
(`meromorphicTrailingCoeffAt_arithmeticNormalization`). The LMFDB defines it for arithmetic
L-functions; the definition makes sense for all. -/
noncomputable def leadingCoeff : ℂ :=
  meromorphicTrailingCoeffAt L.toFun (1 / 2)

/-- The analytic rank is the order of vanishing at the central point, which is finite. -/
lemma natCast_analyticRank : (L.analyticRank : ℕ∞) = analyticOrderAt L.toFun (1 / 2) :=
  Nat.cast_analyticOrderNatAt (L.analyticOrderAt_toFun_ne_top (by norm_num))

/-- The derivatives of order less than the analytic rank vanish at the central point. -/
lemma iteratedDeriv_eq_zero_of_lt_analyticRank (hk : k < L.analyticRank) :
    iteratedDeriv k L.toFun (1 / 2) = 0 :=
  ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (L.analyticAt_toFun (by norm_num))).mp
    L.natCast_analyticRank.symm).1 k hk

/-- The derivative of order the analytic rank does not vanish at the central point. -/
lemma iteratedDeriv_analyticRank_ne_zero : iteratedDeriv L.analyticRank L.toFun (1 / 2) ≠ 0 :=
  ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (L.analyticAt_toFun (by norm_num))).mp
    L.natCast_analyticRank.symm).2

/-- The leading coefficient is `L⁽ʳ⁾(1 / 2) / r!`, where `r` is the analytic rank. -/
lemma leadingCoeff_eq_iteratedDeriv :
    L.leadingCoeff = iteratedDeriv L.analyticRank L.toFun (1 / 2) / L.analyticRank ! :=
  (L.analyticAt_toFun (by norm_num)).meromorphicTrailingCoeffAt_eq_iteratedDeriv_div_factorial
    L.natCast_analyticRank.symm

lemma leadingCoeff_ne_zero : L.leadingCoeff ≠ 0 :=
  L.leadingCoeff_eq_iteratedDeriv ▸ div_ne_zero L.iteratedDeriv_analyticRank_ne_zero
    (Nat.cast_ne_zero.mpr L.analyticRank.factorial_ne_zero)

lemma analyticRank_eq_zero_iff : L.analyticRank = 0 ↔ L.toFun (1 / 2) ≠ 0 := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_analyticRank, Nat.cast_zero,
    (L.analyticAt_toFun (by norm_num)).analyticOrderAt_eq_zero]

/-- The analytic rank is the order of vanishing of the arithmetic normalisation of weight `w` at
its central point `(w + 1) / 2`. -/
lemma analyticOrderNatAt_arithmeticNormalization :
    analyticOrderNatAt (L.arithmeticNormalization w) ((w + 1) / 2) = L.analyticRank := by
  rw [analyticOrderNatAt, arithmeticNormalization_def, ← Function.comp_def,
    analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
  congr 2
  ring1

/-- The leading coefficient is the leading coefficient of the arithmetic normalisation of weight
`w` at its central point `(w + 1) / 2`. -/
lemma meromorphicTrailingCoeffAt_arithmeticNormalization :
    meromorphicTrailingCoeffAt (L.arithmeticNormalization w) ((w + 1) / 2) = L.leadingCoeff := by
  rw [arithmeticNormalization_def,
    meromorphicTrailingCoeffAt_fun_comp_sub_const_eq_meromorphicTrailingCoeffAt]
  congr 1
  ring1

variable (s k) in
lemma iteratedDeriv_arithmeticNormalization :
    iteratedDeriv k (L.arithmeticNormalization w) s = iteratedDeriv k L.toFun (s - w / 2) :=
  congrFun (iteratedDeriv_comp_sub_const ..) s

include h hs in
lemma eventuallyEq_toFun_of_coeff_eq : L.toFun =ᶠ[𝓝 s] L'.toFun :=
  (L.eqOn_toFun_of_coeff_eq h).eventuallyEq_of_mem <| isOpen_compl_singleton.mem_nhds hs

include h in
/-- The analytic rank only depends on the Dirichlet coefficients. -/
lemma analyticRank_congr : L.analyticRank = L'.analyticRank :=
  congrArg ENat.toNat <| analyticOrderAt_congr <| L.eventuallyEq_toFun_of_coeff_eq h (by norm_num)

include h in
/-- The leading coefficient only depends on the Dirichlet coefficients. -/
lemma leadingCoeff_congr : L.leadingCoeff = L'.leadingCoeff :=
  meromorphicTrailingCoeffAt_congr_nhdsNE <|
    (L.eventuallyEq_toFun_of_coeff_eq h (s := 1 / 2) (by norm_num)).filter_mono nhdsWithin_le_nhds

end AnalyticLFunction
