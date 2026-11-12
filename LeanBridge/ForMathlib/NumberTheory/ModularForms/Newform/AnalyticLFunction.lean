import LeanBridge.ForMathlib.NumberTheory.LFunction.CentralCharacter
import LeanBridge.ForMathlib.NumberTheory.LFunction.RootNumber
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.LFunctionSign
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# The analytic L-function of a newform

Let `f` be a newform of level `N`, weight `k ≥ 1` and nebentypus `χ` (Tau Ceti's
`HeckeRing.GL2.Newform`), with `q`-expansion `f = ∑ Aₙ qⁿ`. Its L-function
`L(s, f) = ∑ aₙ n ^ (-s)` in the analytic normalisation, with `aₙ = Aₙ / n ^ ((k - 1) / 2)`, is an
analytic L-function in the sense of the LMFDB (LMFDB `lfunction`, `cmf.lfunction`), of degree `2`
and conductor `N`, with the Euler factors `1 - a_p T + χ(p) T²`, the gamma factor
`Γ_ℂ(s + (k - 1) / 2)` and the sign `ε = i ^ k λ_N(f)`, where `λ_N(f)` is the Fricke
pseudo-eigenvalue of `f`. The continuation, the completion and the functional equation are those
of `LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.LFunctionSign`, built on Hecke's
functional equation in Tau Ceti.

The remaining input is the absolute convergence of the Dirichlet series for `re s > 1`, where
Hecke's bound `Aₙ = O(n ^ (k / 2))` only gives `re s > 3 / 2`. Mathlib's mean-square bound
`∑_{n < M} |Aₙ|² = O(M ^ k)` for a cusp form of weight `k`, a consequence of Parseval's identity,
and the Cauchy–Schwarz inequality give `∑_{n ≤ M} |Aₙ| = O(M ^ ((k + 1) / 2))`. So the Dirichlet
series `∑ Aₙ n ^ (-s)` of a cusp form converges absolutely for `re s > (k + 1) / 2`, and by the
identity theorem the continuation of `∑ aₙ n ^ (-s)` agrees with it for `re s > 1`.

Hence the conductor of the L-function of a newform is its level (LMFDB `lfunction.conductor`), and
its analytic rank is the analytic rank of the newform, the order of vanishing of the continuation of
`∑ Aₙ n ^ (-s)` at the central point `s = k / 2` (LMFDB `cmf.analytic_rank`). A self-dual newform
has real coefficients, so the sign of its functional equation is `(-1) ^ r`, `r` the analytic rank
(LMFDB `cmf.analytic_rank`). For trivial nebentypus the weight is even and the sign is `i ^ (-k)`
times the eigenvalue of the Fricke involution `w_N`, so that in weight `2` the analytic rank is
even exactly when `w_N f = -f`, and odd exactly when `w_N f = f` (LMFDB `cmf.fricke`). The
nebentypus is the central character of the L-function (LMFDB `lfunction.central_character`).
Newforms of positive weight exist, such as the newform `Δ` of level `1` and weight `12`
(`HeckeRing.GL2.deltaNewform`).

## Main definitions

* `AnalyticLFunction.SelbergData.newform`: the Selberg data `(2, N, (μ : ν), ε)` of the
  L-function of a newform.
* `HeckeRing.GL2.Newform.eulerPolynomial`: the Euler factor `1 - a_p T + χ(p) T²`.
* `HeckeRing.GL2.Newform.analyticLFunction` (LMFDB `cmf.lfunction`, `lfunction`): the L-function
  of a newform as an analytic L-function.

## Main results

* `CuspFormClass.LSeriesSummable_qExpansion_coeff`: the Dirichlet series of a cusp form of weight
  `k` converges absolutely for `re s > (k + 1) / 2`.
* `HeckeRing.GL2.Newform.LSeriesSummable_analyticCoeff`: the Dirichlet series of the L-function of
  a newform converges absolutely for `re s > 1`.
* `HeckeRing.GL2.Newform.analyticL_eq_LSeries`: `L(s, f) = ∑ aₙ n ^ (-s)` for `re s > 1`.
* `HeckeRing.GL2.Newform.conductor_analyticLFunction` (LMFDB `lfunction.conductor`): the conductor
  of the L-function of a newform is its level.
* `HeckeRing.GL2.Newform.analyticRank_analyticLFunction` (LMFDB `cmf.analytic_rank`): the analytic
  rank of the L-function of a newform is the analytic rank of the newform.
* `HeckeRing.GL2.Newform.IsSelfDual.rootNumber_eq_neg_one_pow_analyticRank` (LMFDB
  `cmf.analytic_rank`): the sign of a self-dual newform determines the parity of its analytic
  rank.
* `HeckeRing.GL2.Newform.rootNumber_eq_I_zpow_neg_mul_frickeSign` (LMFDB `cmf.fricke`): for trivial
  nebentypus, the sign is `i ^ (-k)` times the eigenvalue of the Fricke involution.
* `HeckeRing.GL2.Newform.isCentralCharacter_analyticLFunction` (LMFDB
  `lfunction.central_character`): the nebentypus is the central character of the L-function.
* `HeckeRing.GL2.Newform.even_analyticRank_iff_frickeSign_eq_neg_one` (LMFDB `cmf.fricke`): in
  weight `2` and trivial nebentypus, the analytic rank is even exactly when `w_N f = -f`.
* `HeckeRing.GL2.Newform.odd_analyticRank_iff_frickeSign_eq_one` (LMFDB `cmf.fricke`): in weight
  `2` and trivial nebentypus, the analytic rank is odd exactly when `w_N f = f`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.9 and
  §5.10.
-/

open UpperHalfPlane hiding I

open Complex Filter Asymptotics Finset TauCeti CongruenceSubgroup

open AnalyticLFunction (SelbergData)

open Polynomial (C X)

open scoped ComplexConjugate Polynomial PowerSeries

namespace CuspFormClass

variable {k : ℕ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ]
  [CuspFormClass F Γ (k : ℤ)] (f : F) {h : ℝ} {s : ℂ}

/-- **The Dirichlet series of a cusp form of weight `k` converges absolutely for
`re s > (k + 1) / 2`**, for its `q`-expansion in `q = exp (2 π i τ / h)` at any strict period `h`.
The mean-square bound `∑_{n < M} |Aₙ|² = O(M ^ k)` and the Cauchy–Schwarz inequality give
`∑_{1 ≤ n ≤ M} |Aₙ| = O(M ^ ((k + 1) / 2))`. -/
lemma LSeriesSummable_qExpansion_coeff (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hs : ((k : ℝ) + 1) / 2 < s.re) : LSeriesSummable (fun n ↦ (qExpansion h f).coeff n) s := by
  rcases exists_sum_range_norm_sq_qExpansion_coeff_le_of_mem_strictPeriods f hh hΓ with ⟨C, hC⟩
  have hC₀ : 0 ≤ C :=
    (sq_nonneg _).trans (by simpa using hC 1)
  refine LSeriesSummable_of_sum_norm_bigO ?_ (by positivity) hs
  refine IsBigO.of_bound √(C * 2 ^ k) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n :=
    Nat.one_le_cast.mpr hn
  rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (by positivity)]
  refine (pow_le_pow_iff_left₀ (sum_nonneg fun _ _ ↦ norm_nonneg _) (by positivity)
    two_ne_zero).mp ?_
  have h₁ : (∑ j ∈ Icc 1 n, ‖(qExpansion h f).coeff j‖) ^ 2 ≤
      n * ∑ j ∈ range (n + 1), ‖(qExpansion h f).coeff j‖ ^ 2 := by
    refine sq_sum_le_card_mul_sum_sq.trans ?_
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (fun j hj ↦ ?_)
      fun _ _ _ ↦ sq_nonneg _) (Nat.cast_nonneg n)
    simpa using Nat.lt_succ_of_le (mem_Icc.mp hj).2
  have h₂ : ((n : ℝ) ^ (((k : ℝ) + 1) / 2)) ^ 2 = (n : ℝ) ^ (k + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
    congr 1
    push_cast
    ring1
  have h₃ : ((n + 1 : ℕ) : ℝ) ^ k ≤ (2 * n) ^ k := by
    gcongr
    push_cast
    linarith
  rw [mul_pow, Real.sq_sqrt (by positivity), h₂]
  refine h₁.trans <| (mul_le_mul_of_nonneg_left ((hC (n + 1)).trans
    (mul_le_mul_of_nonneg_left h₃ hC₀)) (Nat.cast_nonneg n)).trans_eq ?_
  ring1

end CuspFormClass

namespace AnalyticLFunction.SelbergData

variable (N : ℕ) [NeZero N] (k : ℤ) (ε : ℂ)

/-- The **Selberg data** `(2, N, (μ : ν), ε)` of the L-function of a newform of level `N` and
weight `k ≥ 1`, with the sign `ε`. Its gamma factor is `Γ_ℂ(s + (k - 1) / 2)`, with the spectral
parameter `ν = (k - 1) / 2` for `k ≥ 2`; for `k = 1` it is `Γ_ℝ(s) Γ_ℝ(s + 1)`, with `μ = (0, 1)`,
since the LMFDB's normalisation asks for `re ν > 0`. -/
noncomputable def newform : SelbergData where
  conductor := N
  μ := if k ≤ 1 then {0, 1} else 0
  ν := if k ≤ 1 then 0 else {((k : ℂ) - 1) / 2}
  sign := ε
  conductor_pos := Nat.pos_of_neZero N
  re_eq_zero_or_one_of_mem_μ x hx := by
    split_ifs at hx
    · rcases Multiset.mem_cons.mp hx with rfl | hx
      · simp
      · simp [Multiset.mem_singleton.mp hx]
    · exact absurd hx (Multiset.notMem_zero x)
  exists_two_mul_re_eq_of_mem_ν x hx := by
    split_ifs at hx with h
    · exact absurd hx (Multiset.notMem_zero x)
    · refine ⟨(k - 1).toNat, by omega, ?_⟩
      have h' : (((k - 1).toNat : ℤ) : ℝ) = ((k - 1 : ℤ) : ℝ) := by
        rw [Int.toNat_of_nonneg (by omega)]
      push_cast at h'
      rw [Multiset.mem_singleton.mp hx, h', div_ofNat_re, sub_re, intCast_re, one_re]
      ring1
  im_sum_add_two_mul_sum := by
    split_ifs <;> simp

@[simp]
lemma conductor_newform : (newform N k ε).conductor = N :=
  rfl

@[simp]
lemma degree_newform : (newform N k ε).degree = 2 := by
  rw [degree, newform]
  split_ifs <;> rfl

variable {k} in
lemma gammaFactor_newform (hk : 0 < k) (s : ℂ) :
    (newform N k ε).gammaFactor s = Gammaℂ (s + ((k : ℂ) - 1) / 2) := by
  rw [gammaFactor, newform]
  split_ifs with h
  · have hk₁ : k = 1 := by
      omega
    subst hk₁
    simp [Gammaℝ_mul_Gammaℝ_add_one]
  · simp

end AnalyticLFunction.SelbergData

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) {s : ℂ} {m n p : ℕ}

lemma analyticCoeff_eq_mul_cpow_neg : f.analyticCoeff =
    fun n ↦ (qExpansion 1 f.toCuspForm).coeff n * (n : ℂ) ^ (-(((k : ℂ) - 1) / 2)) :=
  funext fun n ↦ by rw [analyticCoeff, div_eq_mul_inv, cpow_neg]

lemma LSeriesSummable_qExpansion_coeff (hk : 0 < k) (hs : ((k : ℝ) + 1) / 2 < s.re) :
    LSeriesSummable (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s := by
  lift k to ℕ using hk.le
  exact CuspFormClass.LSeriesSummable_qExpansion_coeff f.toCuspForm one_pos
    (one_mem_strictPeriods_Gamma1_map N) (by simpa using hs)

/-- **The Dirichlet series of the L-function of a newform converges absolutely for `re s > 1`**,
in the analytic normalisation `aₙ = Aₙ / n ^ ((k - 1) / 2)`. -/
lemma LSeriesSummable_analyticCoeff (hk : 0 < k) (hs : 1 < s.re) :
    LSeriesSummable f.analyticCoeff s := by
  rw [analyticCoeff_eq_mul_cpow_neg, LSeriesSummable,
    funext (LSeries.term_mul_natCast_cpow_neg _ _ s)]
  refine f.LSeriesSummable_qExpansion_coeff hk ?_
  rw [add_re, div_ofNat_re, sub_re, intCast_re, one_re]
  linarith

lemma L_eq_LSeries (hk : 0 < k) (hs : ((k : ℝ) + 1) / 2 < s.re) :
    ModularForm.L hk f.toCuspForm s = LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s := by
  have hab : LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) ≤
      (((k : ℝ) + 1) / 2 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
      f.LSeriesSummable_qExpansion_coeff hk (by simpa using hy)
  have hL : AnalyticOnNhd ℂ (ModularForm.L hk f.toCuspForm) {z : ℂ | ((k : ℝ) + 1) / 2 < z.re} :=
    fun z _ ↦ (CuspForm.differentiable_L hk f.toCuspForm).analyticAt z
  refine hL.eqOn_of_preconnected_of_eventuallyEq ((LSeries_analyticOnNhd _).mono fun z hz ↦
    hab.trans_lt (by exact_mod_cast hz)) (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ)) (by simp; linarith) ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by simp : (k : ℝ) / 2 + 1 < (((k : ℝ) / 2 + 2 : ℝ) : ℂ).re)] with z hz
  simpa using (CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hz).symm

/-- **The L-function of a newform is its Dirichlet series** for `re s > 1`:
`L(s, f) = ∑ aₙ n ^ (-s)` with `aₙ = Aₙ / n ^ ((k - 1) / 2)`. -/
lemma analyticL_eq_LSeries (hk : 0 < k) (hs : 1 < s.re) :
    f.analyticL hk s = LSeries f.analyticCoeff s := by
  rw [analyticL, f.L_eq_LSeries hk, analyticCoeff_eq_mul_cpow_neg,
    LSeries.LSeries_mul_natCast_cpow_neg]
  rw [add_re, div_ofNat_re, sub_re, intCast_re, one_re]
  linarith

lemma differentiable_analyticL (hk : 0 < k) : Differentiable ℂ (f.analyticL hk) :=
  (CuspForm.differentiable_L hk _).comp (differentiable_id.add_const _)

lemma analyticCoeff_one : f.analyticCoeff 1 = 1 := by
  rw [analyticCoeff, Nat.cast_one, one_cpow, div_one, f.isNorm]

lemma analyticCoeff_mul (h : m.Coprime n) :
    f.analyticCoeff (m * n) = f.analyticCoeff m * f.analyticCoeff n := by
  rw [analyticCoeff, analyticCoeff, analyticCoeff, ← f.toEigenform_toCuspForm,
    f.toEigenform.qExpansion_coeff_mul (by simp) h, Nat.cast_mul, natCast_mul_natCast_cpow,
    mul_div_mul_comm]

variable (p) in
/-- The **Euler factor** `1 - a_p T + χ(p) T²` of the L-function of a newform at a prime `p`, in
the analytic normalisation `a_p = A_p / p ^ ((k - 1) / 2)`, with the nebentypus `χ` extended by
`0` at the primes dividing the level. -/
noncomputable def eulerPolynomial : ℂ[X] :=
  1 - C (f.analyticCoeff p) * X + C (f.dirichletLift p) * X ^ 2

lemma analyticCoeff_prime_pow_add_two (hp : p.Prime) (r : ℕ) : f.analyticCoeff (p ^ (r + 2)) =
    f.analyticCoeff p * f.analyticCoeff (p ^ (r + 1)) -
      f.dirichletLift p * f.analyticCoeff (p ^ r) := by
  have hu : (p : ℂ) ^ (((k : ℂ) - 1) / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hp.ne_zero))
  have hpow (j : ℕ) :
      ((p ^ j : ℕ) : ℂ) ^ (((k : ℂ) - 1) / 2) = ((p : ℂ) ^ (((k : ℂ) - 1) / 2)) ^ j := by
    rw [Nat.cast_pow, ← natCast_cpow_natCast_mul, cpow_nat_mul]
  have hsq : ((p : ℂ) ^ (((k : ℂ) - 1) / 2)) ^ 2 = (p : ℂ) ^ (k - 1) := by
    rw [← cpow_nat_mul, ← cpow_intCast]
    congr 1
    push_cast
    ring1
  rw [analyticCoeff, analyticCoeff, analyticCoeff, analyticCoeff, hpow, hpow, hpow,
    ← f.toEigenform_toCuspForm, f.toEigenform.qExpansion_coeff_prime_pow_add_two (by simp) hp r,
    toEigenform_χ, ← dirichletLift_def, ← hsq]
  field_simp
  ring1

lemma eulerPolynomial_mul_mk (hp : p.Prime) :
    (f.eulerPolynomial p : ℂ⟦X⟧) * PowerSeries.mk (fun r ↦ f.analyticCoeff (p ^ r)) = 1 := by
  ext n
  rcases n with _ | _ | n
  · simp [eulerPolynomial, f.analyticCoeff_one]
  · simp [eulerPolynomial, sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul',
      f.analyticCoeff_one]
  · simp [eulerPolynomial, sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul',
      f.analyticCoeff_prime_pow_add_two hp]

lemma natDegree_eulerPolynomial_le : (f.eulerPolynomial p).natDegree ≤ 2 := by
  rw [eulerPolynomial]
  compute_degree

lemma natDegree_eulerPolynomial_eq_two_iff (hp : p.Prime) :
    (f.eulerPolynomial p).natDegree = 2 ↔ ¬p ∣ N := by
  rw [← ZMod.isUnit_prime_iff_not_dvd hp, ← MulChar.apply_ne_zero_iff (χ := f.dirichletLift)]
  refine ⟨fun h hE ↦ ?_, fun hE ↦ ?_⟩
  · have h₁ : (f.eulerPolynomial p).natDegree ≤ 1 := by
      rw [eulerPolynomial, hE, map_zero, zero_mul, add_zero]
      compute_degree
    omega
  · rw [eulerPolynomial]
    compute_degree!

/-- The **L-function of a newform** `f` of level `N` and weight `k ≥ 1` as an analytic L-function
(LMFDB `cmf.lfunction`, `lfunction`): the Dirichlet series `∑ aₙ n ^ (-s)` with
`aₙ = Aₙ / n ^ ((k - 1) / 2)`, with the Euler factors `1 - a_p T + χ(p) T²`
(`HeckeRing.GL2.Newform.eulerPolynomial`), continued by `HeckeRing.GL2.Newform.analyticL` and
completed by `Λ(s, f) = N ^ (s / 2) Γ_ℂ(s + (k - 1) / 2) L(s, f)`
(`HeckeRing.GL2.Newform.analyticCompletedL`), of conductor `N` and sign `ε = i ^ k λ_N(f)`
(`HeckeRing.GL2.Newform.rootNumber`). -/
noncomputable def analyticLFunction (hk : 0 < k) : AnalyticLFunction where
  coeff := f.analyticCoeff
  toFun := f.analyticL hk
  completed := f.analyticCompletedL
  selbergData := .newform N k f.rootNumber
  coeff_one := f.analyticCoeff_one
  coeff_mul_of_coprime := f.analyticCoeff_mul
  exists_eulerFactor p hp :=
    ⟨f.eulerPolynomial p, by simpa using f.natDegree_eulerPolynomial_le,
      by simpa using f.natDegree_eulerPolynomial_eq_two_iff hp, f.eulerPolynomial_mul_mk hp⟩
  LSeriesSummable_coeff := f.LSeriesSummable_analyticCoeff hk
  toFun_eq_LSeries := f.analyticL_eq_LSeries hk
  differentiableOn_toFun := (f.differentiable_analyticL hk).differentiableOn
  meromorphicAt_toFun := ((f.differentiable_analyticL hk).analyticAt 1).meromorphicAt
  completed_eq {s} hs := by
    rw [SelbergData.conductor_newform, SelbergData.gammaFactor_newform _ _ hk]
    refine f.analyticCompletedL_eq_cpow_mul_Gammaℂ_mul_analyticL hk fun m h ↦ ?_
    have h' : (s + ((k : ℂ) - 1) / 2).re = (-(m : ℂ)).re :=
      congrArg Complex.re h
    rw [add_re, div_ofNat_re, sub_re, intCast_re, one_re, neg_re, natCast_re] at h'
    have hk' : (1 : ℝ) ≤ k :=
      mod_cast hk
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  differentiableOn_completed := (f.differentiable_analyticCompletedL hk).differentiableOn
  completed_eq_sign_mul_conj _ _ := f.analyticCompletedL_eq_rootNumber_mul _ hk

/-- **The conductor of the L-function of a newform is its level** (LMFDB `lfunction.conductor`). -/
lemma conductor_analyticLFunction (hk : 0 < k) : (f.analyticLFunction hk).conductor = N :=
  rfl

@[simp]
lemma sign_analyticLFunction (hk : 0 < k) : (f.analyticLFunction hk).sign = f.rootNumber :=
  rfl

@[simp]
lemma degree_analyticLFunction (hk : 0 < k) : (f.analyticLFunction hk).degree = 2 :=
  SelbergData.degree_newform ..

/-- **The analytic rank of the L-function of a newform is the analytic rank of the newform**
(LMFDB `cmf.analytic_rank`, `lfunction.analytic_rank`): the order of vanishing of `L(s, f)` at
`s = 1 / 2` is the order of vanishing of the continuation of `∑ Aₙ n ^ (-s)` at `s = k / 2`. -/
lemma analyticRank_analyticLFunction (hk : 0 < k) :
    (f.analyticLFunction hk).analyticRank = f.analyticRank hk := by
  have h :
      (f.analyticLFunction hk).toFun = ModularForm.L hk f.toCuspForm ∘ (· + ((k : ℂ) - 1) / 2) :=
    rfl
  rw [AnalyticLFunction.analyticRank, analyticRank_def, analyticOrderNatAt, analyticOrderNatAt, h,
    analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
  congr 2
  ring1

variable {f} (n) in
lemma IsSelfDual.conj_analyticCoeff (hf : f.IsSelfDual) :
    conj (f.analyticCoeff n) = f.analyticCoeff n := by
  have hκ : conj (((k : ℂ) - 1) / 2) = ((k : ℂ) - 1) / 2 := by
    rw [map_div₀, map_sub, map_intCast, map_one, map_ofNat]
  have hn : conj ((n : ℂ) ^ (((k : ℂ) - 1) / 2)) = (n : ℂ) ^ (((k : ℂ) - 1) / 2) := by
    simpa [hκ] using conj_natCast_cpow_conj n (((k : ℂ) - 1) / 2)
  rw [analyticCoeff, map_div₀, (f.isSelfDual_iff_forall_conj_coeff_eq.mp hf) n, hn]

variable {f} in
/-- **The sign of a self-dual newform determines the parity of its analytic rank** (LMFDB
`cmf.analytic_rank`): the sign of the functional equation of a newform with real coefficients is
`(-1) ^ r`, where `r` is its analytic rank. -/
lemma IsSelfDual.rootNumber_eq_neg_one_pow_analyticRank (hf : f.IsSelfDual) (hk : 0 < k) :
    f.rootNumber = (-1) ^ f.analyticRank hk := by
  rw [← f.analyticRank_analyticLFunction hk]
  exact (f.analyticLFunction hk).sign_eq_neg_one_pow_analyticRank_of_selfDual fun n _ ↦
    hf.conj_analyticCoeff n

/-- **For trivial nebentypus the sign is `i ^ (-k)` times the Fricke eigenvalue** (LMFDB
`cmf.fricke`): the sign of the functional equation of the L-function of a newform
`f ∈ S_k^new(Γ₀(N))` is `i ^ (-k)` times the eigenvalue of the Fricke involution `w_N` on `f`.
The weight `k` is then even, so that `i ^ (-k) = i ^ k`. -/
lemma rootNumber_eq_I_zpow_neg_mul_frickeSign (hχ : f.χ = 1) :
    f.rootNumber = I ^ (-k) * f.frickeSign hχ := by
  have heven : Even k :=
    even_of_mem_cuspFormCharSpace_one_of_ne_zero (hχ ▸ f.mem_charSpace) f.ne_zero
  have h : I ^ k * I ^ k = 1 := by
    rw [← mul_zpow, I_mul_I, heven.neg_one_zpow]
  rw [rootNumber, f.frickePseudoEigenvalue_eq_frickeSign hχ, zpow_neg,
    inv_eq_of_mul_eq_one_right h]

/-- **The nebentypus is the central character of the L-function of a newform** (LMFDB
`lfunction.central_character`): the coefficient of `T²` of the Euler factor at `p` is
`(-1) ^ 2 χ(p)`. -/
lemma isCentralCharacter_analyticLFunction (hk : 0 < k) :
    (f.analyticLFunction hk).IsCentralCharacter f.dirichletLift := fun p hp ↦ by
  rw [(f.analyticLFunction hk).eulerFactor_eq (f.eulerPolynomial_mul_mk hp), Polynomial.coeff_coe,
    degree_analyticLFunction]
  simp [eulerPolynomial, Polynomial.coeff_one]
  rfl

end HeckeRing.GL2.Newform

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] (f : Newform N 2)

/-- **In weight `2`, the analytic rank of a newform of trivial nebentypus is even exactly when
`w_N f = -f`** (LMFDB `cmf.fricke`): the sign of the functional equation is `i ^ (-2) = -1` times
the eigenvalue of the Fricke involution `w_N`, and `(-1) ^ r`, `r` the analytic rank. -/
lemma even_analyticRank_iff_frickeSign_eq_neg_one (hχ : f.χ = 1) :
    Even (f.analyticRank two_pos) ↔ f.frickeSign hχ = -1 := by
  have h : f.rootNumber = (-1) ^ f.analyticRank two_pos :=
    (f.isSelfDual_of_χ_eq_one hχ).rootNumber_eq_neg_one_pow_analyticRank two_pos
  rw [f.rootNumber_eq_I_zpow_neg_mul_frickeSign hχ, zpow_neg, zpow_ofNat, I_sq, inv_neg, inv_one,
    neg_one_mul] at h
  refine ⟨fun he ↦ ?_, fun hε ↦ ?_⟩
  · rw [he.neg_one_pow] at h
    linear_combination -h
  · rw [hε, neg_neg] at h
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h.symm

/-- **In weight `2`, the analytic rank of a newform of trivial nebentypus is odd exactly when
`w_N f = f`** (LMFDB `cmf.fricke`), as the eigenvalue of the Fricke involution is `1` or `-1`. -/
lemma odd_analyticRank_iff_frickeSign_eq_one (hχ : f.χ = 1) :
    Odd (f.analyticRank two_pos) ↔ f.frickeSign hχ = 1 := by
  rw [← Nat.not_even_iff_odd, f.even_analyticRank_iff_frickeSign_eq_neg_one hχ]
  rcases f.frickeSign_eq_one_or_neg_one hχ with h | h <;> norm_num [h]

end HeckeRing.GL2.Newform
