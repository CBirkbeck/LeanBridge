import LeanBridge.ForMathlib.NumberTheory.LFunction.CentralCharacter
import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Primitive L-functions

An L-function is **primitive** (LMFDB `lfunction.primitive`) if it cannot be written as a product
of nontrivial L-functions, the **trivial L-function** being the constant function `1`.

For analytic L-functions (`AnalyticLFunction`), the trivial L-function `AnalyticLFunction.one` has
degree `0`, conductor `1`, sign `1` and Dirichlet coefficients `δ = (1, 0, 0, …)`, and the product
`AnalyticLFunction.mul` of two analytic L-functions is one again, with the Dirichlet convolution of
their coefficients, the product of their Euler factors, conductors and signs, and their spectral
parameters put together. An analytic L-function records, besides its Dirichlet coefficients `aₙ`,
a continuation, a completion and Selberg data, which do not enter the identity of the L-function:
`L` is trivial, or is the product of `L₁` and `L₂`, when its Dirichlet coefficients `aₙ` (`n ≥ 1`)
are those of `1`, or of `L₁ L₂`.

The degree of an analytic L-function is determined by its Dirichlet coefficients, being the degree
of its Euler factor at any prime not dividing the conductor. It is therefore additive in products,
and an analytic L-function is trivial exactly when its degree is `0`. Hence every analytic
L-function of degree `1`, such as the Riemann zeta function, is primitive, while the trivial
L-function and the products of two nontrivial ones are not.

## Main definitions

* `AnalyticLFunction.one` (LMFDB `lfunction.primitive`): the trivial L-function, the instance
  `One AnalyticLFunction`.
* `AnalyticLFunction.mul`: the product of two analytic L-functions, the instance
  `Mul AnalyticLFunction`.
* `AnalyticLFunction.IsTrivial` (LMFDB `lfunction.primitive`): an analytic L-function is the
  constant function `1`.
* `AnalyticLFunction.IsPrimitive` (LMFDB `lfunction.primitive`): an analytic L-function is
  primitive.

## Main results

* `AnalyticLFunction.IsTrivial.toFun_eq_one`: a trivial analytic L-function is the constant
  function `1`.
* `AnalyticLFunction.degree_eq_of_coeff_eq`: the degree is determined by the Dirichlet
  coefficients.
* `AnalyticLFunction.isTrivial_iff_degree_eq_zero`: an analytic L-function is trivial exactly when
  its degree is `0`.
* `AnalyticLFunction.isPrimitive_of_degree_eq_one`, `AnalyticLFunction.isPrimitive_zeta`: an
  analytic L-function of degree `1`, such as the Riemann zeta function, is primitive.
* `AnalyticLFunction.not_isPrimitive_mul`: a product of two nontrivial analytic L-functions is not
  primitive.
-/

open Complex LSeries

namespace AnalyticLFunction

variable (L L₁ L₂ : AnalyticLFunction) {L' : AnalyticLFunction} {p k : ℕ}

lemma mk_convolution_prime_pow (hp : p.Prime) (f g : ℕ → ℂ) :
    PowerSeries.mk (fun k ↦ convolution f g (p ^ k)) =
      PowerSeries.mk (fun k ↦ f (p ^ k)) * PowerSeries.mk (fun k ↦ g (p ^ k)) := by
  ext k
  rw [PowerSeries.coeff_mk, ← ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt, map_mul,
    convolution, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rcases (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)) with ⟨i, -, hi⟩
  rcases (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)) with ⟨j, -, hj⟩
  rw [hi, hj, ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt,
    ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk]
  simp [toArithmeticFunction, hp.ne_zero]

lemma isMultiplicative_toArithmeticFunction_coeff :
    (toArithmeticFunction L.coeff).IsMultiplicative := by
  refine ⟨by simp [toArithmeticFunction, L.coeff_one], fun {m n} hmn ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | -
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [toArithmeticFunction, hn, L.coeff_mul_of_coprime hmn]

/-- The **trivial L-function** (LMFDB `lfunction.primitive`), the constant function `1`: the
analytic L-function with Dirichlet coefficients `δ = (1, 0, 0, …)`, Euler factors `1`, completion
`1` and Selberg data `(1, ∅, ∅, 1)`, of degree `0`. -/
protected noncomputable def one : AnalyticLFunction where
  coeff := delta
  toFun := 1
  completed := 1
  selbergData :=
    { conductor := 1
      μ := 0
      ν := 0
      sign := 1
      conductor_pos := one_pos
      re_eq_zero_or_one_of_mem_μ x hx := absurd hx (Multiset.notMem_zero x)
      exists_two_mul_re_eq_of_mem_ν x hx := absurd hx (Multiset.notMem_zero x)
      im_sum_add_two_mul_sum := by simp }
  coeff_one := rfl
  coeff_mul_of_coprime _ := by
    simp only [delta]
    split_ifs <;> simp_all
  exists_eulerFactor p hp := by
    refine ⟨1, by simp, by simp [SelbergData.degree, hp.ne_one], ?_⟩
    ext k
    simp [delta, hp.ne_one]
  LSeriesSummable_coeff hs :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ by
      rw [delta]
      split_ifs <;> simp) hs
  toFun_eq_LSeries _ := congrFun LSeries_delta.symm _
  differentiableOn_toFun := differentiableOn_const 1
  meromorphicAt_toFun := analyticAt_const.meromorphicAt
  completed_eq _ := by
    simp [SelbergData.gammaFactor]
  differentiableOn_completed := differentiableOn_const 1
  completed_eq_sign_mul_conj _ _ := by
    simp

/-- The **product** `L₁ L₂` of two analytic L-functions: the analytic L-function with the Dirichlet
coefficients `L₁.coeff ⍟ L₂.coeff`, the Dirichlet convolution of those of `L₁` and `L₂`, the
continuation `L₁(s) L₂(s)`, the completion `Λ₁(s) Λ₂(s)`, the Euler factors `F₁,ₚ F₂,ₚ` and the
Selberg data `(N₁ N₂, μ₁ + μ₂, ν₁ + ν₂, ε₁ ε₂)`, of degree `d₁ + d₂`. -/
protected noncomputable def mul : AnalyticLFunction where
  coeff := convolution L₁.coeff L₂.coeff
  toFun := L₁.toFun * L₂.toFun
  completed := L₁.completed * L₂.completed
  selbergData :=
    { conductor := L₁.selbergData.conductor * L₂.selbergData.conductor
      μ := L₁.selbergData.μ + L₂.selbergData.μ
      ν := L₁.selbergData.ν + L₂.selbergData.ν
      sign := L₁.selbergData.sign * L₂.selbergData.sign
      conductor_pos := Nat.mul_pos L₁.selbergData.conductor_pos L₂.selbergData.conductor_pos
      re_eq_zero_or_one_of_mem_μ x hx := (Multiset.mem_add.mp hx).elim
        (L₁.selbergData.re_eq_zero_or_one_of_mem_μ x) (L₂.selbergData.re_eq_zero_or_one_of_mem_μ x)
      exists_two_mul_re_eq_of_mem_ν x hx := (Multiset.mem_add.mp hx).elim
        (L₁.selbergData.exists_two_mul_re_eq_of_mem_ν x)
        (L₂.selbergData.exists_two_mul_re_eq_of_mem_ν x)
      im_sum_add_two_mul_sum := by
        rw [Multiset.sum_add, Multiset.sum_add, mul_add, add_add_add_comm, add_im,
          L₁.selbergData.im_sum_add_two_mul_sum, L₂.selbergData.im_sum_add_two_mul_sum, add_zero] }
  coeff_one := by
    simp [convolution_def, L₁.coeff_one, L₂.coeff_one]
  coeff_mul_of_coprime hmn :=
    (L₁.isMultiplicative_toArithmeticFunction_coeff.mul
      L₂.isMultiplicative_toArithmeticFunction_coeff).map_mul_of_coprime hmn
  exists_eulerFactor p hp := by
    rcases L₁.exists_eulerFactor p hp with ⟨F₁, hF₁d, hF₁N, hF₁⟩
    rcases L₂.exists_eulerFactor p hp with ⟨F₂, hF₂d, hF₂N, hF₂⟩
    have hF₁₀ : F₁ ≠ 0 :=
      fun h ↦ left_ne_zero_of_mul_eq_one hF₁ (Polynomial.coe_eq_zero_iff.mpr h)
    have hF₂₀ : F₂ ≠ 0 :=
      fun h ↦ left_ne_zero_of_mul_eq_one hF₂ (Polynomial.coe_eq_zero_iff.mpr h)
    refine ⟨F₁ * F₂, ?_, ?_, by
      rw [Polynomial.coe_mul, mk_convolution_prime_pow hp, mul_mul_mul_comm, hF₁, hF₂, one_mul]⟩ <;>
      simp only [SelbergData.degree, Multiset.card_add, Polynomial.natDegree_mul hF₁₀ hF₂₀,
        hp.dvd_mul] at hF₁d hF₂d hF₁N hF₂N ⊢ <;>
      omega
  LSeriesSummable_coeff hs :=
    (L₁.LSeriesSummable_coeff hs).convolution (L₂.LSeriesSummable_coeff hs)
  toFun_eq_LSeries hs := by
    rw [Pi.mul_apply, L₁.toFun_eq_LSeries hs, L₂.toFun_eq_LSeries hs,
      LSeries_convolution' (L₁.LSeriesSummable_coeff hs) (L₂.LSeriesSummable_coeff hs)]
  differentiableOn_toFun := L₁.differentiableOn_toFun.mul L₂.differentiableOn_toFun
  meromorphicAt_toFun := L₁.meromorphicAt_toFun.mul L₂.meromorphicAt_toFun
  completed_eq hs := by
    rw [Pi.mul_apply, L₁.completed_eq hs, L₂.completed_eq hs]
    simp only [SelbergData.gammaFactor, Multiset.map_add, Multiset.prod_add, Nat.cast_mul,
      natCast_mul_natCast_cpow, Pi.mul_apply]
    ring1
  differentiableOn_completed := L₁.differentiableOn_completed.mul L₂.differentiableOn_completed
  completed_eq_sign_mul_conj hs₀ hs₁ := by
    rw [Pi.mul_apply, Pi.mul_apply, L₁.completed_eq_sign_mul_conj hs₀ hs₁,
      L₂.completed_eq_sign_mul_conj hs₀ hs₁, map_mul]
    ring1

noncomputable instance : One AnalyticLFunction :=
  ⟨AnalyticLFunction.one⟩

noncomputable instance : Mul AnalyticLFunction :=
  ⟨AnalyticLFunction.mul⟩

lemma one_coeff : (1 : AnalyticLFunction).coeff = delta :=
  rfl

lemma one_toFun : (1 : AnalyticLFunction).toFun = 1 :=
  rfl

lemma degree_one : (1 : AnalyticLFunction).degree = 0 :=
  rfl

lemma mul_coeff : (L₁ * L₂).coeff = convolution L₁.coeff L₂.coeff :=
  rfl

lemma mul_toFun : (L₁ * L₂).toFun = L₁.toFun * L₂.toFun :=
  rfl

lemma mul_selbergData_μ : (L₁ * L₂).selbergData.μ = L₁.selbergData.μ + L₂.selbergData.μ :=
  rfl

lemma mul_selbergData_ν : (L₁ * L₂).selbergData.ν = L₁.selbergData.ν + L₂.selbergData.ν :=
  rfl

lemma degree_mul : (L₁ * L₂).degree = L₁.degree + L₂.degree := by
  simp only [degree, SelbergData.degree, mul_selbergData_μ, mul_selbergData_ν, Multiset.card_add]
  ring1

/-- An analytic L-function is **trivial** (LMFDB `lfunction.primitive`) if it is the constant
function `1`, the trivial L-function `AnalyticLFunction.one`: if its Dirichlet coefficients `aₙ`
vanish for `n ≥ 2`, as `a₁ = 1` holds for every analytic L-function. Its continuation is then `1`
(`IsTrivial.toFun_eq_one`), and the trivial analytic L-functions are those of degree `0`
(`isTrivial_iff_degree_eq_zero`). -/
def IsTrivial : Prop :=
  ∀ n, 1 < n → L.coeff n = 0

/-- An analytic L-function is **primitive** (LMFDB `lfunction.primitive`) if it is not trivial and
cannot be written as a product of two nontrivial L-functions: whenever its Dirichlet coefficients
`aₙ` (`n ≥ 1`) are those of a product `L₁ L₂`, which are the Dirichlet convolution of the
coefficients of `L₁` and `L₂`, one of `L₁` and `L₂` is trivial. As for irreducible elements of a
monoid, and in the Selberg class, the trivial L-function itself is not primitive, a case that the
knowl's wording leaves open. -/
def IsPrimitive : Prop :=
  ¬L.IsTrivial ∧ ∀ M₁ M₂ : AnalyticLFunction, (∀ n ≠ 0, L.coeff n = (M₁ * M₂).coeff n) →
    M₁.IsTrivial ∨ M₂.IsTrivial

lemma isTrivial_one : (1 : AnalyticLFunction).IsTrivial := fun _ hn ↦
  ite_eq_right hn.ne'

variable {L} in
lemma IsTrivial.coeff_eq_one_coeff (h : L.IsTrivial) {n : ℕ} (hn : n ≠ 0) :
    L.coeff n = (1 : AnalyticLFunction).coeff n := by
  rcases eq_or_ne n 1 with rfl | hn₁
  · exact L.coeff_one
  · rw [h n (by omega), one_coeff, delta, ite_eq_right hn₁]

variable {L} in
/-- **A trivial analytic L-function is the constant function `1`**, away from `s = 1`, where its
continuation is not constrained. -/
lemma IsTrivial.toFun_eq_one (h : L.IsTrivial) {s : ℂ} (hs : s ≠ 1) : L.toFun s = 1 :=
  L.eqOn_toFun_of_coeff_eq (fun _ hn ↦ h.coeff_eq_one_coeff hn) hs

/-- **The degree is determined by the Dirichlet coefficients**: two analytic L-functions with the
same coefficients `aₙ` (`n ≥ 1`) have the same degree, the degree of their common Euler factor at a
prime that divides neither conductor. -/
lemma degree_eq_of_coeff_eq (h : ∀ n ≠ 0, L.coeff n = L'.coeff n) : L.degree = L'.degree := by
  rcases Nat.exists_infinite_primes (L.selbergData.conductor * L'.selbergData.conductor + 1) with
    ⟨p, hpN, hp⟩
  have hpL : ¬p ∣ L.selbergData.conductor :=
    Nat.not_dvd_of_pos_of_lt L.selbergData.conductor_pos
      ((Nat.le_mul_of_pos_right _ L'.selbergData.conductor_pos).trans_lt hpN)
  have hpL' : ¬p ∣ L'.selbergData.conductor :=
    Nat.not_dvd_of_pos_of_lt L'.selbergData.conductor_pos
      ((Nat.le_mul_of_pos_left _ L.selbergData.conductor_pos).trans_lt hpN)
  rcases L.exists_eulerFactor p hp with ⟨F, -, hF, hFL⟩
  rcases L'.exists_eulerFactor p hp with ⟨F', -, hF', hFL'⟩
  have hFF' : F = F' := by
    rw [← Polynomial.coe_inj, ← L.eulerFactor_eq hFL, ← L'.eulerFactor_eq hFL', eulerFactor,
      eulerFactor, funext fun k ↦ h (p ^ k) (pow_ne_zero k hp.ne_zero)]
  rw [degree, degree, ← hF.mpr hpL, ← hF'.mpr hpL', hFF']

lemma coeff_prime_pow_eq_zero_of_degree_eq_zero (h : L.degree = 0) (hp : p.Prime) (hk : k ≠ 0) :
    L.coeff (p ^ k) = 0 := by
  rcases L.exists_eulerFactor p hp with ⟨F, hFd, -, hF⟩
  rw [Polynomial.eq_C_of_natDegree_le_zero (hFd.trans_eq h), Polynomial.coe_C] at hF
  have h₀ : F.coeff 0 = 1 := by
    simpa [L.coeff_one] using congrArg (PowerSeries.coeff 0) hF
  simpa [h₀, hk] using congrArg (PowerSeries.coeff k) hF

/-- **The trivial analytic L-functions are those of degree `0`**: a trivial one has the degree `0`
of `1`, and an analytic L-function of degree `0` has Euler factors `1`, so that its coefficients
vanish at prime powers `pᵏ` with `k ≥ 1`, hence at every `n ≥ 2` by multiplicativity. -/
lemma isTrivial_iff_degree_eq_zero : L.IsTrivial ↔ L.degree = 0 := by
  refine ⟨fun h ↦ (L.degree_eq_of_coeff_eq fun _ hn ↦ h.coeff_eq_one_coeff hn).trans degree_one,
    fun h n hn ↦ ?_⟩
  rcases Nat.exists_prime_and_dvd hn.ne' with ⟨p, hp, hpn⟩
  rw [← Nat.ordProj_mul_ordCompl_eq_self n p,
    L.coeff_mul_of_coprime ((Nat.coprime_ordCompl hp (by omega)).pow_left _),
    L.coeff_prime_pow_eq_zero_of_degree_eq_zero h hp
      (hp.factorization_pos_of_dvd (by omega) hpn).ne', zero_mul]

/-- **An analytic L-function of degree `1` is primitive**: the degrees of the factors of a product
add up to `1`, so one of them has degree `0` and is trivial. -/
lemma isPrimitive_of_degree_eq_one (h : L.degree = 1) : L.IsPrimitive := by
  refine ⟨fun ht ↦ by simp [L.isTrivial_iff_degree_eq_zero.mp ht] at h, fun M₁ M₂ hM ↦ ?_⟩
  have hd : L.degree = M₁.degree + M₂.degree :=
    (L.degree_eq_of_coeff_eq hM).trans (degree_mul M₁ M₂)
  rw [M₁.isTrivial_iff_degree_eq_zero, M₂.isTrivial_iff_degree_eq_zero]
  omega

/-- **The Riemann zeta function is primitive**, being of degree `1`. -/
lemma isPrimitive_zeta : zeta.IsPrimitive :=
  zeta.isPrimitive_of_degree_eq_one degree_zeta

lemma not_isPrimitive_one : ¬(1 : AnalyticLFunction).IsPrimitive := fun h ↦
  h.1 isTrivial_one

/-- **A product of two nontrivial analytic L-functions is not primitive.** -/
lemma not_isPrimitive_mul (h₁ : ¬L₁.IsTrivial) (h₂ : ¬L₂.IsTrivial) :
    ¬(L₁ * L₂).IsPrimitive := fun h ↦
  (h.2 L₁ L₂ fun _ _ ↦ rfl).elim h₁ h₂

end AnalyticLFunction
