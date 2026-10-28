import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannHypothesis
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.EulerProduct.Basic
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# The critical line and the critical strip of an analytic L-function

In its analytic normalisation, the functional equation `Λ(s) = ε conj (Λ (1 - conj s))` of an
analytic L-function relates `s` and `1 - conj s`, the reflection in the line `re s = 1 / 2`: this
line of symmetry is its critical line, and the critical strip is the open strip `0 < re s < 1`.
To the right of the critical strip the Dirichlet series and the Euler product converge absolutely,
so the L-function does not vanish there, and its zeros `ρ` with `re ρ > 0` lie in the closure of
the critical strip. By the functional equation the completed L-function `Λ`, in which the trivial
zeros at the poles of the gamma factor are cancelled, does not vanish to the left of the critical
strip either, so its zeros lie in the closure of the critical strip. In the arithmetic
normalisation of weight `w`, whose functional equation relates `s` and `1 + w - conj s`, the
critical line is `re s = (1 + w) / 2` and the critical strip is `w / 2 < re s < w / 2 + 1`: the
translates by `w / 2`.

## Main definitions

* `AnalyticLFunction.criticalLine` and `AnalyticLFunction.arithmeticCriticalLine` (LMFDB
  `lfunction.critical_line`): the critical line in the analytic normalisation and in the
  arithmetic normalisation of weight `w`.
* `AnalyticLFunction.criticalStrip` and `AnalyticLFunction.arithmeticCriticalStrip` (LMFDB
  `lfunction.critical_strip`): the critical strip in both normalisations.

## Main results

* `AnalyticLFunction.mem_criticalLine_iff_one_sub_conj_eq` and
  `AnalyticLFunction.mem_arithmeticCriticalLine_iff_add_sub_conj_eq`: the critical line is the
  line of symmetry of the functional equation, the set of fixed points of `s ↦ 1 - conj s`, and
  of `s ↦ 1 + w - conj s` in the arithmetic normalisation of weight `w`.
* `AnalyticLFunction.completed_eq_sign_mul_conj_of_mem_criticalLine`: on the critical line, the
  functional equation reads `Λ(s) = ε conj (Λ s)`.
* `AnalyticLFunction.riemannHypothesis_iff_mem_criticalLine`: the Riemann hypothesis says that the
  zeros `ρ` with `re ρ > 0` lie on the critical line.
* `AnalyticLFunction.LSeriesSummable_arithmeticCoeff`: the Dirichlet series of the arithmetic
  normalisation of weight `w` converges absolutely to the right of its critical strip.
* `AnalyticLFunction.hasProd_tsum_term_prime_pow` and
  `AnalyticLFunction.summable_norm_tsum_term_prime_pow_sub_one`: to the right of the critical
  strip, an analytic L-function is the product of its Euler factors, which converges absolutely.
* `AnalyticLFunction.toFun_ne_zero` and `AnalyticLFunction.arithmeticNormalization_ne_zero`: an
  analytic L-function does not vanish to the right of its critical strip, in both normalisations.
* `AnalyticLFunction.mem_closure_criticalStrip`: the zeros `ρ` with `re ρ > 0` lie in the closure
  of the critical strip.
* `AnalyticLFunction.mem_closure_criticalStrip_of_completed_eq_zero`: the zeros of the completed
  L-function (the nontrivial zeros of the L-function) lie in the closure of the critical strip.
-/

open Complex LSeries Set TauCeti.LSeries
open scoped ComplexConjugate Polynomial

lemma Polynomial.eval_mul_tsum_eq_one {F : ℂ[X]} {a : ℕ → ℂ} {x : ℂ}
    (hFa : (F : PowerSeries ℂ) * PowerSeries.mk a = 1) (ha : Summable fun k ↦ ‖a k * x ^ k‖) :
    F.eval x * ∑' k, a k * x ^ k = 1 := by
  have hF : ∀ i ∉ Finset.range (F.natDegree + 1), F.coeff i * x ^ i = 0 := fun i hi ↦ by
    rw [F.coeff_eq_zero_of_natDegree_lt (by simpa using hi), zero_mul]
  have hFn : Summable fun i ↦ ‖F.coeff i * x ^ i‖ :=
    summable_of_ne_finset_zero fun i hi ↦ by rw [hF i hi, norm_zero]
  have h (n : ℕ) : ∑ kl ∈ Finset.antidiagonal n, F.coeff kl.1 * x ^ kl.1 * (a kl.2 * x ^ kl.2) =
      PowerSeries.coeff n 1 * x ^ n := by
    rw [← hFa, PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [coeff_coe, PowerSeries.coeff_mk, ← Finset.mem_antidiagonal.mp hkl, pow_add]
    ring1
  rw [eval_eq_sum_range, ← tsum_eq_sum (L := .unconditional ℕ) hF,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFn ha, tsum_congr h,
    tsum_eq_single 0 fun n hn ↦ by simp [hn]]
  simp

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {w : ℕ} {s ρ : ℂ}

/-- The **critical line** (LMFDB `lfunction.critical_line`) `re s = 1 / 2` of an analytic
L-function in its analytic normalisation: the line of symmetry of its functional equation, which
relates `s` and `1 - conj s` (`mem_criticalLine_iff_one_sub_conj_eq`). It is the same line for
every analytic L-function. -/
noncomputable def criticalLine : Set ℂ :=
  re ⁻¹' {1 / 2}

variable (w) in
/-- The **critical line** (LMFDB `lfunction.critical_line`) `re s = (1 + w) / 2` of an analytic
L-function in its arithmetic normalisation of weight `w` (for the LMFDB, its motivic weight
`AnalyticLFunction.motivicWeight`): the line of symmetry of the functional equation, which then
relates `s` and `1 + w - conj s` (`mem_arithmeticCriticalLine_iff_add_sub_conj_eq`). It is the
translate of `criticalLine` by `w / 2`. -/
noncomputable def arithmeticCriticalLine : Set ℂ :=
  re ⁻¹' {(1 + w : ℝ) / 2}

/-- The **critical strip** (LMFDB `lfunction.critical_strip`) `0 < re s < 1` of an analytic
L-function in its analytic normalisation, whose functional equation relates `s` and `1 - conj s`.
To its right the Dirichlet series and the Euler product converge absolutely
(`AnalyticLFunction.LSeriesSummable_coeff`, `summable_norm_tsum_term_prime_pow_sub_one`) and the
L-function does not vanish (`toFun_ne_zero`), so the zeros `ρ` with `re ρ > 0` lie in its closure
(`mem_closure_criticalStrip`), and so do the zeros of the completed L-function, which by the
functional equation does not vanish to the left of the strip either
(`mem_closure_criticalStrip_of_completed_eq_zero`). -/
noncomputable def criticalStrip : Set ℂ :=
  re ⁻¹' Ioo 0 1

variable (w) in
/-- The **critical strip** (LMFDB `lfunction.critical_strip`) `w / 2 < re s < w / 2 + 1` of an
analytic L-function in its arithmetic normalisation of weight `w` (for the LMFDB, its motivic
weight), whose functional equation relates `s` and `1 + w - conj s`. It is the translate of
`criticalStrip` by `w / 2`. To its right the Dirichlet series converges absolutely
(`LSeriesSummable_arithmeticCoeff`) and the L-function does not vanish
(`arithmeticNormalization_ne_zero`). -/
noncomputable def arithmeticCriticalStrip : Set ℂ :=
  re ⁻¹' Ioo (w / 2) (w / 2 + 1)

@[simp]
lemma mem_criticalLine : s ∈ criticalLine ↔ s.re = 1 / 2 :=
  Iff.rfl

@[simp]
lemma mem_arithmeticCriticalLine : s ∈ arithmeticCriticalLine w ↔ s.re = (1 + w) / 2 :=
  Iff.rfl

@[simp]
lemma mem_criticalStrip : s ∈ criticalStrip ↔ 0 < s.re ∧ s.re < 1 :=
  Iff.rfl

@[simp]
lemma mem_arithmeticCriticalStrip :
    s ∈ arithmeticCriticalStrip w ↔ w / 2 < s.re ∧ s.re < w / 2 + 1 :=
  Iff.rfl

/-- The critical line is the line of symmetry of the functional equation
`Λ(s) = ε conj (Λ (1 - conj s))`: the set of fixed points of `s ↦ 1 - conj s`. -/
lemma mem_criticalLine_iff_one_sub_conj_eq : s ∈ criticalLine ↔ 1 - conj s = s := by
  rw [mem_criticalLine, Complex.ext_iff]
  grind [sub_re, one_re, conj_re, sub_im, one_im, conj_im]

/-- In the arithmetic normalisation of weight `w`, the critical line is the line of symmetry of the
functional equation: the set of fixed points of `s ↦ 1 + w - conj s`. -/
lemma mem_arithmeticCriticalLine_iff_add_sub_conj_eq :
    s ∈ arithmeticCriticalLine w ↔ 1 + w - conj s = s := by
  rw [mem_arithmeticCriticalLine, Complex.ext_iff]
  grind [sub_re, add_re, one_re, natCast_re, conj_re, sub_im, add_im, one_im, natCast_im, conj_im]

lemma sub_mem_criticalLine_iff : s - w / 2 ∈ criticalLine ↔ s ∈ arithmeticCriticalLine w := by
  rw [mem_criticalLine, mem_arithmeticCriticalLine, sub_re, div_ofNat_re, natCast_re]
  grind

lemma sub_mem_criticalStrip_iff : s - w / 2 ∈ criticalStrip ↔ s ∈ arithmeticCriticalStrip w := by
  rw [mem_criticalStrip, mem_arithmeticCriticalStrip, sub_re, div_ofNat_re, natCast_re]
  grind

@[simp]
lemma arithmeticCriticalLine_zero : arithmeticCriticalLine 0 = criticalLine := by
  ext
  simp

@[simp]
lemma arithmeticCriticalStrip_zero : arithmeticCriticalStrip 0 = criticalStrip := by
  ext
  simp

lemma criticalLine_subset_criticalStrip : criticalLine ⊆ criticalStrip :=
  fun _ hs ↦ by norm_num [mem_criticalLine.mp hs]

lemma arithmeticCriticalLine_subset_arithmeticCriticalStrip :
    arithmeticCriticalLine w ⊆ arithmeticCriticalStrip w :=
  fun _ hs ↦ sub_mem_criticalStrip_iff.mp <| criticalLine_subset_criticalStrip <|
    sub_mem_criticalLine_iff.mpr hs

lemma one_sub_conj_mem_criticalStrip_iff : 1 - conj s ∈ criticalStrip ↔ s ∈ criticalStrip := by
  grind [mem_criticalStrip, sub_re, one_re, conj_re]

lemma closure_criticalStrip : closure criticalStrip = re ⁻¹' Icc 0 1 := by
  rw [criticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]

/-- On the critical line, the functional equation reads `Λ(s) = ε conj (Λ s)`. -/
lemma completed_eq_sign_mul_conj_of_mem_criticalLine (hs : s ∈ criticalLine) :
    L.completed s = L.sign * conj (L.completed s) := by
  have h : L.completed s = L.sign * conj (L.completed (1 - conj s)) :=
    L.completed_eq_sign_mul_conj (ne_of_apply_ne re <| Eq.trans_ne hs one_half_pos.ne')
      (ne_of_apply_ne re <| Eq.trans_ne hs one_half_lt_one.ne)
  rwa [mem_criticalLine_iff_one_sub_conj_eq.mp hs] at h

lemma completed_sub_eq_sign_mul_conj_of_mem_arithmeticCriticalLine
    (hs : s ∈ arithmeticCriticalLine w) :
    L.completed (s - w / 2) = L.sign * conj (L.completed (s - w / 2)) :=
  L.completed_eq_sign_mul_conj_of_mem_criticalLine <| sub_mem_criticalLine_iff.mpr hs

/-- The Riemann hypothesis for an analytic L-function says that its zeros `ρ` with `re ρ > 0` lie
on the critical line. -/
lemma riemannHypothesis_iff_mem_criticalLine :
    L.RiemannHypothesis ↔ ∀ ρ ∈ L.zeros, 0 < ρ.re → ρ ∈ criticalLine :=
  Iff.rfl

/-- The Dirichlet series of the arithmetic normalisation of weight `w` converges absolutely to the
right of its critical strip. -/
lemma LSeriesSummable_arithmeticCoeff (hs : w / 2 + 1 < s.re) :
    LSeriesSummable (L.arithmeticCoeff w) s := by
  refine (L.LSeriesSummable_coeff (s := s + -(w / 2)) ?_).congr fun n ↦ ?_
  · rw [add_re, neg_re, div_ofNat_re, natCast_re]
    linarith
  · rw [← term_mul_natCast_cpow_neg, neg_neg]
    rfl

lemma tsum_term_prime_pow_ne_zero (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' e : ℕ, term L.coeff s (p ^ e) ≠ 0 := by
  rcases L.exists_eulerFactor p p.prop with ⟨F, -, -, hF⟩
  have hsum : Summable fun e : ℕ ↦ ‖term L.coeff s (p ^ e)‖ :=
    (L.LSeriesSummable_coeff hs).norm.comp_injective (Nat.pow_right_injective p.prop.two_le)
  simp_rw [term_pow _ p.prop.ne_zero] at hsum ⊢
  exact right_ne_zero_of_mul_eq_one (Polynomial.eval_mul_tsum_eq_one hF hsum)

/-- To the right of its critical strip, an analytic L-function is the product of its Euler
factors `∑ₖ a_{pᵏ} p ^ (-k s)`. -/
lemma hasProd_tsum_term_prime_pow (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ, term L.coeff s (p ^ e)) (L.toFun s) :=
  L.toFun_eq_LSeries hs ▸ EulerProduct.eulerProduct_hasProd (by simp [L.coeff_one])
    (term_mul_of_coprime fun _ _ h ↦ L.coeff_mul_of_coprime h) (L.LSeriesSummable_coeff hs).norm
    (term_zero ..)

lemma tsum_term_prime_pow_eq_one_add (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' e : ℕ, term L.coeff s (p ^ e) = 1 + ∑' e : ℕ, term L.coeff s (p ^ (e + 1)) := by
  have hp : Summable fun e : ℕ ↦ term L.coeff s (p ^ e) :=
    (L.LSeriesSummable_coeff hs).comp_injective (Nat.pow_right_injective p.prop.two_le)
  rw [hp.tsum_eq_zero_add]
  simp [L.coeff_one]

/-- To the right of its critical strip, the Euler product of an analytic L-function converges
absolutely: the series `∑ₚ |Lₚ(s) - 1|` over the primes converges, where `Lₚ(s)` is the Euler
factor `∑ₖ a_{pᵏ} p ^ (-k s)`. -/
lemma summable_norm_tsum_term_prime_pow_sub_one (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ ‖∑' e : ℕ, term L.coeff s (p ^ e) - 1‖ := by
  have hinj : Function.Injective fun pe : Nat.Primes × ℕ ↦ (pe.1 : ℕ) ^ (pe.2 + 1) := by
    rintro ⟨p, e⟩ ⟨q, f⟩ h
    rcases p.prop.pow_inj q.prop h with ⟨hpq, hef⟩
    exact Prod.ext (Subtype.ext hpq) hef
  rcases (summable_prod_of_nonneg fun _ ↦ norm_nonneg _).mp
    ((L.LSeriesSummable_coeff hs).norm.comp_injective hinj) with ⟨h₁, h₂⟩
  refine h₂.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun p ↦ ?_
  rw [L.tsum_term_prime_pow_eq_one_add hs p, add_sub_cancel_left]
  exact norm_tsum_le_tsum_norm (h₁ p)

/-- An analytic L-function does not vanish to the right of its critical strip. -/
lemma toFun_ne_zero (hs : 1 < s.re) : L.toFun s ≠ 0 := by
  rw [← (L.hasProd_tsum_term_prime_pow hs).tprod_eq]
  simpa using tprod_one_add_ne_zero_of_summable
    (fun p ↦ by simpa using L.tsum_term_prime_pow_ne_zero hs p)
    (L.summable_norm_tsum_term_prime_pow_sub_one hs)

/-- In the arithmetic normalisation of weight `w`, an analytic L-function does not vanish to the
right of its critical strip. -/
lemma arithmeticNormalization_ne_zero (hs : w / 2 + 1 < s.re) : L.arithmeticNormalization w s ≠ 0 :=
  L.toFun_ne_zero <| by
    rw [sub_re, div_ofNat_re, natCast_re]
    linarith

lemma completed_ne_zero (hs : 1 < s.re) : L.completed s ≠ 0 := by
  rw [L.completed_eq hs]
  exact mul_ne_zero (mul_ne_zero (by simp [L.selbergData.conductor_pos.ne'])
    (L.selbergData.gammaFactor_ne_zero (zero_lt_one.trans hs))) (L.toFun_ne_zero hs)

lemma completed_ne_zero_of_re_neg (hs : s.re < 0) : L.completed s ≠ 0 := by
  rw [L.completed_eq_sign_mul_conj (ne_of_apply_ne re hs.ne)
    (ne_of_apply_ne re (hs.trans one_pos).ne)]
  refine mul_ne_zero (norm_ne_zero_iff.mp <| L.norm_sign.trans_ne one_ne_zero) <|
    (map_ne_zero conj).mpr <| L.completed_ne_zero ?_
  rw [sub_re, one_re, conj_re]
  linarith

lemma re_le_one_of_mem_zeros (hρ : ρ ∈ L.zeros) : ρ.re ≤ 1 :=
  not_lt.mp fun h ↦ L.toFun_ne_zero h <| (L.mem_zeros_iff <| ne_of_apply_ne re h.ne').mp hρ

/-- The zeros `ρ` with `re ρ > 0` of an analytic L-function lie in the closure of its critical
strip. -/
lemma mem_closure_criticalStrip (hρ : ρ ∈ L.zeros) (hre : 0 < ρ.re) : ρ ∈ closure criticalStrip :=
  closure_criticalStrip ▸ ⟨hre.le, L.re_le_one_of_mem_zeros hρ⟩

/-- The zeros of the completed L-function `Λ(s) = N ^ (s / 2) γ(s) L(s)`, in which the trivial zeros
of `L` at the poles of the gamma factor `γ` are cancelled, lie in the closure of the critical
strip: `Λ` does not vanish for `re s > 1`, nor, by the functional equation, for `re s < 0`. -/
lemma mem_closure_criticalStrip_of_completed_eq_zero (hρ : L.completed ρ = 0) :
    ρ ∈ closure criticalStrip :=
  closure_criticalStrip ▸ ⟨not_lt.mp fun h ↦ L.completed_ne_zero_of_re_neg h hρ,
    not_lt.mp fun h ↦ L.completed_ne_zero h hρ⟩

end AnalyticLFunction
