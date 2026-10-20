import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Normalized

/-!
# The holomorphic Eisenstein series `E_k^{χ₁, χ₂}`

For a weight `k ≥ 1` and primitive Dirichlet characters `χ₁` modulo `N₁` and `χ₂` modulo `N₂`,
the LMFDB's Eisenstein series is the function on the upper half-plane
`E_k^{χ₁, χ₂}(τ) = a₀ + ∑_{n ≥ 1} σ_{k-1}^{χ₁, χ₂}(n) qⁿ`, with constant term
`a₀ = ½ (δ_{χ₁ = 1} L(1 - k, χ₂) + δ_{k = 1} δ_{χ₂ = 1} L(0, χ₁))`,
where `q = e^{2πiτ}` and `σ_{k-1}^{χ₁, χ₂}(n) = ∑_{m ∣ n} χ₁(n/m) χ₂(m) m^{k-1}` (Tau Ceti's
`DirichletCharacter.twistedDivisorSum`). The series converges on all of `ℍ`
(`hasSum_charEisensteinSeries`).

In weight `k ≥ 3`, with the parity `χ₁(-1) χ₂(-1) = (-1)^k`, it is Tau Ceti's normalised
Eisenstein series `TauCeti.EisensteinSeries.normalizedCharEisensteinSeriesMF`, a modular form of
level `N₁ N₂` and character `χ₁ χ₂`
(`charEisensteinSeries_eq_normalizedCharEisensteinSeriesMF`). Tau Ceti identifies the nonconstant
Fourier coefficients of its series; the constant term, which Tau Ceti leaves as a lattice sum, is
identified here with `½ δ_{χ₁ = 1} L(1 - k, χ₂)` through the functional equation of Dirichlet
`L`-functions and the product of the Gauss sums of `χ₂` and `χ₂⁻¹`. The modularity of the series
in weights `1` and `2` is not proved.

## Main definitions

* `EisensteinSeries.charEisensteinCoeff`: the Fourier coefficients of `E_k^{χ₁, χ₂}`.
* `EisensteinSeries.charEisensteinSeries` (LMFDB `cmf.eisenstein_series`): the Eisenstein series
  `E_k^{χ₁, χ₂}`.

## Main results

* `EisensteinSeries.hasSum_charEisensteinSeries`: the `q`-series of `E_k^{χ₁, χ₂}` converges on
  `ℍ`.
* `EisensteinSeries.qExpansion_normalizedCharEisensteinSeriesMF`: in weight `k ≥ 3` the
  `q`-expansion of Tau Ceti's normalised series is that of `E_k^{χ₁, χ₂}`.
* `EisensteinSeries.charEisensteinSeries_eq_normalizedCharEisensteinSeriesMF`: in weight `k ≥ 3`,
  `E_k^{χ₁, χ₂}` is Tau Ceti's normalised series, a modular form.
-/

open Complex Function TauCeti.EisensteinSeries ZMod
open UpperHalfPlane hiding I re
open scoped MatrixGroups

namespace EisensteinSeries

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (k : ℕ) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (n : ℕ) (τ : ℍ)

open Classical in
/-- The Fourier coefficients of the Eisenstein series `E_k^{χ₁, χ₂}`: the constant term
`½ (δ_{χ₁ = 1} L(1 - k, χ₂) + δ_{k = 1} δ_{χ₂ = 1} L(0, χ₁))`, with Mathlib's Dirichlet
`L`-functions `DirichletCharacter.LFunction`, and the twisted divisor sums
`σ_{k-1}^{χ₁, χ₂}(n) = ∑_{m ∣ n} χ₁(n/m) χ₂(m) m^{k-1}` for `n ≥ 1`. -/
noncomputable def charEisensteinCoeff : ℂ :=
  if n = 0 then
    ((if χ₁ = 1 then χ₂.LFunction (1 - k) else 0) +
      if k = 1 ∧ χ₂ = 1 then χ₁.LFunction 0 else 0) / 2
  else χ₁.twistedDivisorSum (k - 1) χ₂ n

/-- The **Eisenstein series** `E_k^{χ₁, χ₂}` (LMFDB `cmf.eisenstein_series`) of weight `k`
attached to Dirichlet characters `χ₁` modulo `N₁` and `χ₂` modulo `N₂`, primitive in the LMFDB:
the function `τ ↦ ∑_{n ≥ 0} aₙ qⁿ` on the upper half-plane, `q = e^{2πiτ}`, with the Fourier
coefficients `aₙ = charEisensteinCoeff k χ₁ χ₂ n`: the constant term
`a₀ = ½ (δ_{χ₁ = 1} L(1 - k, χ₂) + δ_{k = 1} δ_{χ₂ = 1} L(0, χ₁))` and the twisted divisor sums
`aₙ = σ_{k-1}^{χ₁, χ₂}(n)` for `n ≥ 1`.
The series converges on `ℍ` (`hasSum_charEisensteinSeries`). In weight `k ≥ 3`, for primitive
characters of the parity of `k`, it is Tau Ceti's normalised Eisenstein series, a modular form
(`charEisensteinSeries_eq_normalizedCharEisensteinSeriesMF`). -/
noncomputable def charEisensteinSeries : ℂ :=
  ∑' n : ℕ, charEisensteinCoeff k χ₁ χ₂ n * Periodic.qParam 1 τ ^ n

lemma norm_charEisensteinCoeff_le :
    ‖charEisensteinCoeff k χ₁ χ₂ n‖ ≤ ‖charEisensteinCoeff k χ₁ χ₂ 0‖ + (n : ℝ) ^ (k - 1 + 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [charEisensteinCoeff, ite_eq_right hn]
  have h : ∑ d ∈ n.divisors, (d : ℝ) ^ (k - 1) ≤ (n : ℝ) ^ (k - 1 + 1) := by
    exact_mod_cast ArithmeticFunction.sigma_apply.symm.trans_le
      (ArithmeticFunction.sigma_le_pow_succ (k - 1) n)
  linarith [TauCeti.norm_twistedDivisorSum_le (k - 1) χ₁ χ₂ n,
    norm_nonneg (charEisensteinCoeff k χ₁ χ₂ 0)]

/-- **The `q`-series of `E_k^{χ₁, χ₂}` converges on the upper half-plane.** -/
lemma hasSum_charEisensteinSeries : HasSum
    (fun n ↦ charEisensteinCoeff k χ₁ χ₂ n * Periodic.qParam 1 τ ^ n)
    (charEisensteinSeries k χ₁ χ₂ τ) := by
  have hq : ‖Periodic.qParam 1 τ‖ < 1 := by simpa using τ.norm_qParam_lt_one 1
  refine Summable.hasSum <| Summable.of_norm_bounded
    (g := fun n : ℕ ↦ ‖charEisensteinCoeff k χ₁ χ₂ 0‖ * ‖Periodic.qParam 1 τ‖ ^ n +
      (n : ℝ) ^ (k - 1 + 1) * ‖Periodic.qParam 1 τ‖ ^ n)
    (((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left _).add
      (summable_pow_mul_geometric_of_norm_lt_one (k - 1 + 1) (by simpa using hq)))
    fun n ↦ ?_
  rw [norm_mul, norm_pow, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_charEisensteinCoeff_le k χ₁ χ₂ n) (by positivity)

variable {v : ℕ} [NeZero v] (φ : DirichletCharacter ℂ v) (hφ : φ.IsPrimitive)
    (hφk : φ (-1) = (-1) ^ k) (hk₂ : 2 ≤ k)

include hk₂ in
private lemma one_lt_re_natCast : 1 < (k : ℂ).re := by
  rw [natCast_re]
  exact_mod_cast hk₂

include hφ in
private lemma gaussSum_inv_mul_gaussSum :
    gaussSum φ⁻¹ stdAddChar * gaussSum φ stdAddChar = φ (-1) * v := by
  have hφ' : (φ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hφ
  have h : gaussSum φ⁻¹ stdAddChar * gaussSum φ⁻¹⁻¹ (stdAddChar : AddChar (ZMod v) ℂ)⁻¹ =
      Fintype.card (ZMod v) :=
    DirichletCharacter.gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive hφ'
      (ZMod.isPrimitive_stdAddChar v)
  rw [inv_inv, ZMod.card] at h
  have hshift :
      φ (-1) * gaussSum φ (stdAddChar : AddChar (ZMod v) ℂ)⁻¹ = gaussSum φ stdAddChar := by
    simpa [← AddChar.inv_mulShift] using gaussSum_mulShift φ (stdAddChar : AddChar (ZMod v) ℂ) (-1)
  rw [← hshift, mul_left_comm, h]

omit [NeZero v] in
include hφk hk₂ in
private lemma tsum_int_eq_two_mul_LSeries :
    ∑' d : ℤ, φ d * (d : ℂ) ^ (-(k : ℤ)) = 2 * LSeries (fun n ↦ φ n) k := by
  have hsum : LSeriesSummable (fun n ↦ φ n) k := φ.LSeriesSummable_of_one_lt_re
    (one_lt_re_natCast k hk₂)
  have hpos (n : ℕ) : φ n * (n : ℂ) ^ (-(k : ℤ)) = LSeries.term (fun n ↦ φ n) k n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [show k ≠ 0 by omega]
    · rw [LSeries.term, ite_eq_right hn, zpow_neg, zpow_natCast, div_eq_mul_inv, cpow_natCast]
  have hneg (n : ℕ) : φ (-(n + 1 : ℕ) : ℤ) * ((-(n + 1 : ℕ) : ℤ) : ℂ) ^ (-(k : ℤ)) =
      LSeries.term (fun n ↦ φ n) k (n + 1) := by
    rw [← hpos (n + 1)]
    push_cast
    rw [neg_eq_neg_one_mul ((n : ZMod v) + 1), map_mul, hφk, neg_eq_neg_one_mul ((n : ℂ) + 1),
      mul_zpow, zpow_neg (-1 : ℂ), zpow_natCast]
    field_simp
  have h₁ :
      HasSum (fun n : ℕ ↦ φ (n : ℤ) * ((n : ℤ) : ℂ) ^ (-(k : ℤ))) (LSeries (fun n ↦ φ n) k) := by
    have h : HasSum (LSeries.term (fun n ↦ φ n) k) (LSeries (fun n ↦ φ n) k) :=
      hsum.LSeriesHasSum
    convert h using 2 with n
    push_cast
    exact hpos n
  have h₂ : HasSum (fun n : ℕ ↦ φ (-(n + 1 : ℕ) : ℤ) * ((-(n + 1 : ℕ) : ℤ) : ℂ) ^ (-(k : ℤ)))
      (LSeries (fun n ↦ φ n) k) := by
    simp_rw [hneg]
    simpa using (hasSum_nat_add_iff' 1).mpr hsum.LSeriesHasSum
  exact (h₁.of_nat_of_neg_add_one h₂).tsum_eq.trans (two_mul _).symm

include hφ hφk hk₂ in
private lemma LFunction_one_sub_natCast : φ.LFunction (1 - k) = 2 * (v : ℂ) ^ (k - 1) *
    ((2 * Real.pi : ℂ) ^ k)⁻¹ * (k - 1).factorial * gaussSum φ stdAddChar * (-I) ^ k * LSeries
    (fun n ↦ φ⁻¹ n) k := by
  have hk' (n : ℕ) : (k : ℂ) ≠ -n := fun h ↦ by
    have hre : (k : ℂ).re = (-(n : ℂ)).re := congrArg re h
    simp at hre
    omega
  have hk1 : (k : ℂ) ≠ 1 := Nat.cast_ne_one.mpr (by omega)
  have hsq : φ (-1) * φ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hdft : (fun n : ℕ ↦ 𝓕 φ n) = (φ (-1) * gaussSum φ stdAddChar) • fun n : ℕ ↦ φ⁻¹ n := by
    funext n
    rw [hφ.fourierTransform_eq_inv_mul_gaussSum, Pi.smul_apply, smul_eq_mul,
      neg_eq_neg_one_mul (n : ZMod v), map_mul, MulChar.inv_apply_eq_inv',
      inv_eq_of_mul_eq_one_right hsq]
    ring1
  have hdft' : (fun n : ℕ ↦ 𝓕 φ (-n)) = gaussSum φ stdAddChar • fun n : ℕ ↦ φ⁻¹ n := by
    funext n
    rw [hφ.fourierTransform_eq_inv_mul_gaussSum, neg_neg, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hexp : cexp (Real.pi * I * k / 2) = I ^ k := by
    rw [show (Real.pi : ℂ) * I * k / 2 = k * (Real.pi / 2 * I) by ring1, exp_nat_mul,
      exp_pi_div_two_mul_I]
  have hexp' : cexp (-Real.pi * I * k / 2) = (-I) ^ k := by
    rw [show -(Real.pi : ℂ) * I * k / 2 = k * -(Real.pi / 2 * I) by ring1, exp_nat_mul, exp_neg,
      exp_pi_div_two_mul_I, inv_I]
  have hcast : ((k - 1 : ℕ) : ℂ) = k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hΓ : Gamma k = (k - 1).factorial := by
    rw [← Gamma_nat_eq_factorial, hcast, sub_add_cancel]
  have hIk : I ^ k * ((-1) ^ k * gaussSum φ stdAddChar * LSeries (fun n ↦ φ⁻¹ n) k) = (-I) ^ k *
      (gaussSum φ stdAddChar * LSeries (fun n ↦ φ⁻¹ n) k) := by
    rw [neg_eq_neg_one_mul I, mul_pow]
    ring1
  rw [DirichletCharacter.LFunction, ZMod.LFunction_one_sub φ hk' (Or.inr hk1),
    ZMod.dft_comp_neg, ZMod.LFunction_eq_LSeries _ (one_lt_re_natCast k hk₂),
    ZMod.LFunction_eq_LSeries _ (one_lt_re_natCast k hk₂), hdft, hdft', LSeries_smul,
    LSeries_smul, hexp, hexp', hΓ, hφk, ← hcast, cpow_natCast, cpow_neg, cpow_natCast, hIk]
  ring1

variable {N : ℕ} [NeZero N] (hk : 3 ≤ (k : ℤ)) (huv : N₁ * N₂ ∣ N)
    (hpar : χ₁ (-1) * χ₂ (-1) = (-1) ^ (k : ℤ)) (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)

include hpar hχ₁ hχ₂ in
private lemma qExpansion_normalizedCharEisensteinSeriesMF_coeff_zero :
    (qExpansion 1 (normalizedCharEisensteinSeriesMF χ₁ χ₂ hk huv)).coeff 0 = charEisensteinCoeff k
    χ₁ χ₂ 0 := by
  have hk1 : ¬(k = 1 ∧ χ₂ = 1) := fun h ↦ by omega
  rw [normalizedCharEisensteinSeriesMF, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, qExpansion_charEisensteinSeriesMF_coeff χ₁ χ₂ hk huv hpar 0,
    ite_eq_left rfl, charEisensteinCoeff, ite_eq_left rfl, ite_eq_right hk1, add_zero]
  rcases eq_or_ne N₁ 1 with rfl | hN₁
  · have hχ₁1 : χ₁ = 1 := χ₁.level_one
    have hχ₁0 : χ₁ 0 = 1 := by
      rw [hχ₁1]
      exact MulChar.one_apply (isUnit_of_subsingleton 0)
    rw [hχ₁1, MulChar.one_apply (isUnit_of_subsingleton _), one_mul, zpow_natCast] at hpar
    have hinv : χ₂⁻¹ (-1) = (-1) ^ k := by
      rw [MulChar.inv_apply_eq_inv', hpar]
      exact inv_eq_of_mul_eq_one_right (by rw [← mul_pow, neg_one_mul, neg_neg, one_pow])
    have hgg : gaussSum χ₂⁻¹ stdAddChar * gaussSum χ₂ stdAddChar = (-1) ^ k * N₂ := by
      rw [gaussSum_inv_mul_gaussSum χ₂ hχ₂, hpar]
    have hN : (N₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N₂)
    have hg : gaussSum χ₂ stdAddChar ≠ 0 :=
      right_ne_zero_of_mul (hgg ▸ mul_ne_zero (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero)) hN)
    have hg' : gaussSum χ₂⁻¹ stdAddChar = (-I) ^ k * (-I) ^ k * N₂ / gaussSum χ₂ stdAddChar := by
      rw [eq_div_iff hg, hgg, ← mul_pow, neg_mul_neg, I_mul_I]
    have hpow : (N₂ : ℂ) ^ k = N₂ ^ (k - 1) * N₂ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [ite_eq_left hχ₁1, hχ₁0, one_mul, tsum_int_eq_two_mul_LSeries k χ₂⁻¹ hinv (by omega),
      LFunction_one_sub_natCast k χ₂ hχ₂ hpar (by omega), smul_eq_mul, hg', hpow, neg_mul,
      neg_mul, ← mul_neg, mul_pow]
    have hI4 : (-I) ^ k * (-I) ^ k * (-I) ^ k * (-I) ^ k = 1 := by
      rw [← mul_pow, ← mul_pow, ← mul_pow,
        show -I * -I * -I * -I = 1 by linear_combination (I * I - 1) * I_mul_I, one_pow]
    field_simp
    linear_combination (-((k - 1).factorial * LSeries (fun n ↦ χ₂⁻¹ n) k)) * hI4
  · have hχ₁0 : χ₁ 0 = 0 := by
      have : Nontrivial (ZMod N₁) := ZMod.nontrivial_iff.mpr hN₁
      exact χ₁.map_nonunit not_isUnit_zero
    have hχ₁1 : χ₁ ≠ 1 := fun h ↦ hN₁ <| by
      rw [← hχ₁, h, DirichletCharacter.conductor_one]
    rw [hχ₁0, zero_mul, smul_zero, ite_eq_right hχ₁1, zero_div]

include hpar hχ₁ hχ₂ in
/-- **Tau Ceti's normalised Eisenstein series has the `q`-expansion of `E_k^{χ₁, χ₂}`**, in weight
`k ≥ 3`, for primitive characters `χ₁` and `χ₂` with the parity of `k`: all its Fourier
coefficients, including the constant term `½ δ_{χ₁ = 1} L(1 - k, χ₂)`, are those of the LMFDB. -/
lemma qExpansion_normalizedCharEisensteinSeriesMF : qExpansion 1
    (normalizedCharEisensteinSeriesMF χ₁ χ₂ hk huv) = PowerSeries.mk
    (charEisensteinCoeff k χ₁ χ₂) := by
  ext n
  rw [PowerSeries.coeff_mk]
  rcases eq_or_ne n 0 with rfl | hn
  · exact qExpansion_normalizedCharEisensteinSeriesMF_coeff_zero k χ₁ χ₂ hk huv hpar hχ₁ hχ₂
  · rw [qExpansion_normalizedCharEisensteinSeriesMF_coeff χ₁ χ₂ hk huv hpar hχ₂ hn,
      charEisensteinCoeff, ite_eq_right hn]

include hpar hχ₁ hχ₂ in
/-- **`E_k^{χ₁, χ₂}` is a modular form in weight `k ≥ 3`**: for primitive characters `χ₁` and
`χ₂` with the parity of `k`, it is Tau Ceti's normalised Eisenstein series, a modular form of
weight `k`, character `χ₁ χ₂` and level any multiple `N` of `N₁ N₂`. -/
lemma charEisensteinSeries_eq_normalizedCharEisensteinSeriesMF :
    charEisensteinSeries k χ₁ χ₂ = normalizedCharEisensteinSeriesMF χ₁ χ₂ hk huv := by
  funext τ
  refine (hasSum_charEisensteinSeries k χ₁ χ₂ τ).unique ?_
  simpa [qExpansion_normalizedCharEisensteinSeriesMF k χ₁ χ₂ hk huv hpar hχ₁ hχ₂] using
    ModularForm.hasSum_qExpansion (normalizedCharEisensteinSeriesMF χ₁ χ₂ hk huv) one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N) τ

end EisensteinSeries
