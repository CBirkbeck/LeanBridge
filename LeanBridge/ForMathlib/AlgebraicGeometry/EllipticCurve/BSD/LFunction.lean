import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticRank
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction

/-!
# The analytic rank and the special value of an elliptic curve

The L-function `L(E / K, s)` of a Weierstrass curve `E` over a number field `K` is the Dirichlet
series of Mathlib's formal L-function `WeierstrassCurve.LFunction`, in the arithmetic
normalisation of weight `1`, with central point `s = 1`. Its analytic continuation is not
formalised (for `K = ℚ` it follows from the modularity theorem), so the analytic L-function of `E`
is taken as given: an analytic L-function whose arithmetic normalisation of weight `1` has the
Dirichlet coefficients of `L(E / K, s)` (`WeierstrassCurve.IsAnalyticLFunction`). Its continuation
is determined by these coefficients, so the analytic rank and the special value of `E` are
well defined: they are those of any analytic L-function of `E` (`WeierstrassCurve.analyticRank_eq`,
`WeierstrassCurve.specialValue_eq`), with the junk value `0` if there is none.

## Main definitions

* `WeierstrassCurve.IsAnalyticLFunction`: an analytic L-function is the L-function of `E`.
* `WeierstrassCurve.analyticRank` (LMFDB `ec.q.analytic_rank`): the analytic rank of `E`.
* `WeierstrassCurve.specialValue` (LMFDB `ec.special_value`, `ec.q.special_value`): the special
  value of `E`.

## Main results

* `WeierstrassCurve.IsAnalyticLFunction.arithmeticNormalization_eq_LSeries`: an analytic
  L-function of `E` continues Mathlib's L-series `WeierstrassCurve.LSeries` of `E`.
* `WeierstrassCurve.analyticRank_eq` and `WeierstrassCurve.specialValue_eq`: the analytic rank
  and the special value of `E` are those of any analytic L-function of `E`.
* `WeierstrassCurve.analyticRank_eq_analyticOrderNatAt`: the analytic rank is the order of
  vanishing of `L(E, s)` at `s = 1`.
* `WeierstrassCurve.iteratedDeriv_eq_zero_of_lt_analyticRank`,
  `WeierstrassCurve.specialValue_eq_iteratedDeriv` and `WeierstrassCurve.specialValue_ne_zero`:
  the special value is the first nonzero value of `L⁽ʳ⁾(E, 1) / r!`.
-/

open scoped Nat

namespace WeierstrassCurve

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K) {L L' : AnalyticLFunction}
  {k : ℕ}

variable (L) in
/-- An analytic L-function `L` is the **analytic L-function of** a Weierstrass curve `W` over a
number field: its arithmetic normalisation of weight `1` is the L-series of `W`, that is, its
Dirichlet coefficients `aₙ / √n` come from the coefficients `aₙ` of `WeierstrassCurve.LFunction`.
By the modularity theorem, every elliptic curve over `ℚ` has one. -/
def IsAnalyticLFunction : Prop :=
  ∀ n, L.arithmeticCoeff 1 n = W.LFunction n

open scoped Classical in
/-- The **analytic rank** (LMFDB `ec.q.analytic_rank`) of a Weierstrass curve over a number field:
the analytic rank of its L-function `L(E, s)`, its order of vanishing at the central point
`s = 1`. It is the analytic rank of any analytic L-function of `W` (`analyticRank_eq`), and takes
the junk value `0` if `L(E, s)` has no analytic continuation of the LMFDB's form. -/
noncomputable def analyticRank : ℕ :=
  if h : ∃ L, W.IsAnalyticLFunction L then h.choose.analyticRank else 0

open scoped Classical in
/-- The **special value** (LMFDB `ec.special_value`, `ec.q.special_value`) of a Weierstrass curve
over a number field: the leading coefficient of its L-function `L(E, s)` at the central point
`s = 1`, that is, the first nonzero value of `L⁽ʳ⁾(E, 1) / r!`
(`specialValue_eq_iteratedDeriv`). It is the leading coefficient of any analytic L-function of
`W` (`specialValue_eq`), and takes the junk value `0` if `L(E, s)` has no analytic continuation of
the LMFDB's form. -/
noncomputable def specialValue : ℂ :=
  if h : ∃ L, W.IsAnalyticLFunction L then h.choose.leadingCoeff else 0

variable {W} (hL : W.IsAnalyticLFunction L)

include hL in
lemma IsAnalyticLFunction.coeff_eq (hL' : W.IsAnalyticLFunction L') {n : ℕ} (hn : n ≠ 0) :
    L.coeff n = L'.coeff n :=
  mul_right_cancel₀ ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by simp)).mpr
    (Nat.cast_ne_zero.mpr hn)) ((hL n).trans (hL' n).symm)

include hL in
/-- An analytic L-function of a Weierstrass curve `W` continues Mathlib's L-series of `W`: in the
arithmetic normalisation of weight `1`, it is `WeierstrassCurve.LSeries` for `re s > 3 / 2`. -/
lemma IsAnalyticLFunction.arithmeticNormalization_eq_LSeries {s : ℂ} (hs : 3 / 2 < s.re) :
    L.arithmeticNormalization 1 s = W.LSeries s :=
  (L.arithmeticNormalization_eq_LSeries 1 (by norm_num [hs])).trans <|
    LSeries_congr (fun {n} _ ↦ hL n) s

include hL in
/-- The analytic rank of a Weierstrass curve is the analytic rank of any of its analytic
L-functions. -/
lemma analyticRank_eq : W.analyticRank = L.analyticRank := by
  have h : ∃ L, W.IsAnalyticLFunction L :=
    ⟨L, hL⟩
  rw [analyticRank, dite_eq_left h]
  exact h.choose.analyticRank_congr fun _ ↦ h.choose_spec.coeff_eq hL

include hL in
/-- The special value of a Weierstrass curve is the leading coefficient of any of its analytic
L-functions. -/
lemma specialValue_eq : W.specialValue = L.leadingCoeff := by
  have h : ∃ L, W.IsAnalyticLFunction L :=
    ⟨L, hL⟩
  rw [specialValue, dite_eq_left h]
  exact h.choose.leadingCoeff_congr fun _ ↦ h.choose_spec.coeff_eq hL

variable (k) in
lemma iteratedDeriv_arithmeticNormalization_one :
    iteratedDeriv k (L.arithmeticNormalization 1) 1 = iteratedDeriv k L.toFun (1 / 2) := by
  rw [L.iteratedDeriv_arithmeticNormalization]
  norm_num

include hL in
/-- The analytic rank of a Weierstrass curve is the order of vanishing of its L-function at `s = 1`
in the arithmetic normalisation. -/
lemma analyticRank_eq_analyticOrderNatAt :
    W.analyticRank = analyticOrderNatAt (L.arithmeticNormalization 1) 1 := by
  rw [analyticRank_eq hL, ← L.analyticOrderNatAt_arithmeticNormalization 1]
  norm_num

include hL in
/-- The derivatives of `L(E, s)` of order less than the analytic rank vanish at `s = 1`. -/
lemma iteratedDeriv_eq_zero_of_lt_analyticRank (hk : k < W.analyticRank) :
    iteratedDeriv k (L.arithmeticNormalization 1) 1 = 0 :=
  (iteratedDeriv_arithmeticNormalization_one k).trans <|
    L.iteratedDeriv_eq_zero_of_lt_analyticRank <| analyticRank_eq hL ▸ hk

include hL in
/-- The special value of a Weierstrass curve is `L⁽ʳ⁾(E, 1) / r!`, where `r` is its analytic
rank. -/
lemma specialValue_eq_iteratedDeriv : W.specialValue = iteratedDeriv W.analyticRank
    (L.arithmeticNormalization 1) 1 / W.analyticRank ! := by
  rw [specialValue_eq hL, iteratedDeriv_arithmeticNormalization_one, analyticRank_eq hL]
  exact L.leadingCoeff_eq_iteratedDeriv

include hL in
/-- The special value of a Weierstrass curve with an analytic L-function is nonzero. -/
lemma specialValue_ne_zero : W.specialValue ≠ 0 :=
  specialValue_eq hL ▸ L.leadingCoeff_ne_zero

end WeierstrassCurve
