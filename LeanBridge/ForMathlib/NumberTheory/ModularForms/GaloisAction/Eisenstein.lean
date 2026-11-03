import Mathlib.Analysis.Fourier.ZMod
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.ConstantTerm
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The `q`-expansion of an Eisenstein series supported on a row

For a function `g` of residues modulo `N`, we compute the `q`-expansion of the Eisenstein series
`∑_{(c, d) ∈ ℤ²} g(d) (c N z + d)^(-k)` of level `Γ₁(N)` when `g(-r) = (-1)^k g(r)`.

This is Tau Ceti's computation of the `q`-expansion of the Eisenstein series with character
`TauCeti.EisensteinSeries.charEisensteinSeriesMF`, whose private steps are redone here for an
arbitrary function `g` in place of the inverse of a Dirichlet character. The same goes for the
constant term, in the form of Tau Ceti's `gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`.

## Main definitions

* `TauCeti.GaloisAction.rowWeight`: the weight `(a₀, a₁) ↦ g(a₁)` if `a₀ = 0`, and `0` otherwise.

## Main results

* `TauCeti.GaloisAction.hasSum_rowEisenstein`: the `q`-expansion of the series.
* `TauCeti.GaloisAction.hasSum_mul_zpow_sum_bernoulliFun`: its constant term, by Bernoulli
  polynomials.
-/

open Complex ZMod EisensteinSeries Function Periodic

open UpperHalfPlane hiding I

open scoped Real

namespace TauCeti.GaloisAction

variable {N K : ℕ} (g : ZMod N → ℂ)

lemma neg_one_pow_mul_self : ((-1 : ℂ) ^ K) * (-1) ^ K = 1 := by
  rw [← mul_pow]
  simp

lemma inv_neg_one_pow : ((-1 : ℂ) ^ K)⁻¹ = (-1) ^ K :=
  inv_eq_of_mul_eq_one_right neg_one_pow_mul_self

/-- The weight on residue pairs modulo `N` of the Eisenstein series supported on the row of the
pairs `(0, r)`: it sends `(0, r)` to `g(r)`, and vanishes elsewhere. -/
def rowWeight (a : Fin 2 → ZMod N) : ℂ :=
  if a 0 = 0 then g (a 1) else 0

lemma rowWeight_intCast (x : Fin 2 → ℤ) :
    rowWeight g ((↑) ∘ x) = if (N : ℤ) ∣ x 0 then g (x 1) else 0 := by
  simp [rowWeight, ZMod.intCast_zmod_eq_zero_iff_dvd]

variable (z : ℍ)

lemma tsum_row_neg (hpar : ∀ r, g (-r) = (-1) ^ K * g r) (c : ℤ) : ∑' d : ℤ,
    g d * (((N * -c : ℤ) : ℂ) * z + d) ^ (-(K : ℤ)) =
      ∑' d : ℤ, g d * (((N * c : ℤ) : ℂ) * z + d) ^ (-(K : ℤ)) := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun d ↦ ?_
  have h : ((N * -c : ℤ) : ℂ) * z + ((-d : ℤ) : ℂ) = -(((N * c : ℤ) : ℂ) * z + d) := by
    push_cast
    ring1
  rw [Equiv.neg_apply, h, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, neg_pow, mul_inv,
    inv_neg_one_pow, Int.cast_neg, hpar]
  linear_combination (g d * ((((N * c : ℤ) : ℂ) * z + d) ^ K)⁻¹) * neg_one_pow_mul_self (K := K)

variable [NeZero N]

lemma summable_rowSummand (hK : 3 ≤ (K : ℤ)) :
    Summable fun p : ℤ × ℤ ↦ (if (N : ℤ) ∣ p.1 then g p.2 else 0) * eisSummand K ![p.1, p.2] z := by
  have hW : Summable fun x : Fin 2 → ℤ ↦ rowWeight g ((↑) ∘ x) * eisSummand K x z :=
    (EisensteinSeries.summable_norm_weightedEisensteinSummand (rowWeight g) hK z).of_norm
  refine ((finTwoArrowEquiv ℤ).symm.summable_iff.mpr hW).congr fun p ↦ ?_
  rw [Function.comp_apply, finTwoArrowEquiv_symm_apply, rowWeight_intCast]
  simp

lemma summable_row (hK : 3 ≤ (K : ℤ)) :
    Summable fun c : ℤ ↦ ∑' d : ℤ, g d * (((N * c : ℤ) : ℂ) * z + d) ^ (-(K : ℤ)) := by
  refine ((summable_rowSummand g z hK).prod.comp_injective
    (mul_right_injective₀ (NeZero.ne (N : ℤ)))).congr fun c ↦ ?_
  simp [eisSummand]

lemma weightedEisensteinSeries_rowWeight_apply (hK : 3 ≤ (K : ℤ)) :
    EisensteinSeries.weightedEisensteinSeries (rowWeight g) K z =
      ∑' c : ℤ, ∑' d : ℤ, g d * (((N * c : ℤ) : ℂ) * z + d) ^ (-(K : ℤ)) := by
  have hinj : Function.Injective fun c : ℤ ↦ (N : ℤ) * c :=
    mul_right_injective₀ (NeZero.ne (N : ℤ))
  have hS : Summable fun p : ℤ × ℤ ↦
      (if (N : ℤ) ∣ p.1 then g p.2 else 0) * eisSummand K ![p.1, p.2] z :=
    summable_rowSummand g z hK
  have hsupp : Function.support (fun a ↦ ∑' d : ℤ, (if (N : ℤ) ∣ a then g d else 0) *
      eisSummand K ![a, d] z) ⊆ Set.range fun c : ℤ ↦ (N : ℤ) * c := by
    intro a ha
    by_contra h
    have hdvd : ¬(N : ℤ) ∣ a := fun ⟨c, hc⟩ ↦ h ⟨c, hc.symm⟩
    exact ha (by simp [hdvd])
  rw [EisensteinSeries.weightedEisensteinSeries_def]
  simp_rw [rowWeight_intCast]
  have hW : ∑' p : ℤ × ℤ, (if (N : ℤ) ∣ p.1 then g p.2 else 0) * eisSummand K ![p.1, p.2] z =
      ∑' x : Fin 2 → ℤ, (if (N : ℤ) ∣ x 0 then g (x 1) else 0) * eisSummand K x z := by
    simpa only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
      (finTwoArrowEquiv ℤ).symm.tsum_eq fun x : Fin 2 → ℤ ↦
        (if (N : ℤ) ∣ x 0 then g (x 1) else 0) * eisSummand K x z
  rw [← hW, hS.tsum_prod, ← hinj.tsum_eq hsupp]
  refine tsum_congr fun c ↦ ?_
  simp [eisSummand]

lemma tsum_row_pnat (hK : 2 ≤ K) (c : ℕ+) : ∑' d : ℤ,
    g d * (((N * c : ℤ) : ℂ) * z + d) ^ (-(K : ℤ)) =
      (-2 * π * I) ^ K / ((K - 1).factorial * N ^ K) * ∑' m : ℕ+,
        𝓕 g (-(m : ZMod N)) * (m : ℂ) ^ (K - 1) * cexp (2 * π * I * z) ^ (c * m : ℕ) := by
  let w : ℍ := ⟨((N * c : ℕ) : ℂ) * z, by
    simpa using mul_pos (Nat.cast_pos.mpr (mul_pos (NeZero.pos N) c.pos)) z.2⟩
  have hw : (((N * c : ℤ) : ℂ) * z) = (w : ℂ) := by
    simp [w]
  simp_rw [hw]
  rw [EisensteinSeries.qExpansion_identity_zmod g hK w]
  congr 1
  refine tsum_congr fun m ↦ ?_
  have hN : (N : ℂ) ≠ 0 := NeZero.ne (N : ℂ)
  rw [pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 2
  simp only [w]
  push_cast
  field_simp

lemma weightedEisensteinSeries_rowWeight_eq_add (hK : 3 ≤ K) (hpar : ∀ r, g (-r) = (-1) ^ K * g r) :
    EisensteinSeries.weightedEisensteinSeries (rowWeight g) K z =
      ∑' d : ℤ, g d * (d : ℂ) ^ (-(K : ℤ)) + 2 * (-2 * π * I) ^ K / ((K - 1).factorial * N ^ K) *
        ∑' c : ℕ+, ∑' m : ℕ+, 𝓕 g (-(m : ZMod N)) * (m : ℂ) ^ (K - 1) *
          cexp (2 * π * I * z) ^ (c * m : ℕ) := by
  have hK' : 3 ≤ (K : ℤ) := by exact_mod_cast hK
  have heven : Function.Even fun c : ℤ ↦
      ∑' d : ℤ, g d * (((N * c : ℤ) : ℂ) * z + d) ^ (-(K : ℤ)) :=
    fun c ↦ tsum_row_neg g z hpar c
  have hrow (c : ℕ+) : ∑' d : ℤ, g d * (((N * (c : ℤ) : ℤ) : ℂ) * z + d) ^ (-(K : ℤ)) =
      (-2 * π * I) ^ K / ((K - 1).factorial * N ^ K) * ∑' m : ℕ+,
        𝓕 g (-(m : ZMod N)) * (m : ℂ) ^ (K - 1) * cexp (2 * π * I * z) ^ (c * m : ℕ) :=
    tsum_row_pnat g z (by omega) c
  rw [weightedEisensteinSeries_rowWeight_apply g z hK',
    tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_row g z hK'), tsum_congr hrow,
    tsum_mul_left]
  simp only [Int.cast_zero, mul_zero, zero_mul, zero_add]
  ring1

/-- **The `q`-expansion of an Eisenstein series supported on a row.** For a function `g` of residues
modulo `N` with `g(-r) = (-1)^k g(r)` and a weight `k ≥ 3`, the series
`∑_{c, d} g(d) (c N z + d)^(-k)` has constant term `∑_d g(d) d^(-k)`, and `n`-th coefficient
`2 L ∑_{c m = n} 𝓕g(-m) m^(k - 1)`, with `L = (-2πi)^k / ((k - 1)! N^k)`. -/
lemma hasSum_rowEisenstein (hK : 3 ≤ K) (hpar : ∀ r, g (-r) = (-1) ^ K * g r) : HasSum (fun n : ℕ ↦
    (if n = 0 then ∑' d : ℤ, g d * (d : ℂ) ^ (-(K : ℤ))
      else 2 * (-2 * π * I) ^ K / ((K - 1).factorial * N ^ K) *
        ∑ x ∈ n.divisorsAntidiagonal, 𝓕 g (-(x.2 : ZMod N)) * (x.2 : ℂ) ^ (K - 1)) •
      qParam 1 z ^ n)
    (EisensteinSeries.weightedEisensteinSeries (rowWeight g) K z) := by
  set L : ℂ := 2 * (-2 * π * I) ^ K / ((K - 1).factorial * N ^ K)
  set a : ℕ → ℂ := fun n ↦ ∑ x ∈ n.divisorsAntidiagonal,
    𝓕 g (-(x.2 : ZMod N)) * (x.2 : ℂ) ^ (K - 1) with ha
  set q : ℂ := cexp (2 * π * I * z)
  have hq : qParam 1 z = q := by
    simp [qParam, q]
  -- the double series over `(c, m)` converges absolutely
  set f : ℕ → ℕ → ℂ := fun c m ↦ 𝓕 g (-(m : ZMod N)) * (m : ℂ) ^ (K - 1) * q ^ (c * m) with hf
  have hr : ‖‖q‖‖ < 1 := by simpa using norm_exp_two_pi_I_lt_one z
  have hfs : Summable fun p : ℕ+ × ℕ+ ↦ f p.1 p.2 := by
    refine ((summable_prod_mul_pow (K - 1) hr).mul_left (∑ j, ‖𝓕 g j‖)).of_norm_bounded fun p ↦ ?_
    simp only [hf, norm_mul, norm_pow, Complex.norm_natCast]
    have h2 : ‖𝓕 g (-(p.2 : ℕ))‖ ≤ ∑ j, ‖𝓕 g j‖ :=
      Finset.single_le_sum (f := fun j ↦ ‖𝓕 g j‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ _)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  -- regroup by `n = c m`; each group carries `q ^ n`
  have hgroup (n : ℕ+) : ∑ x ∈ (n : ℕ).divisorsAntidiagonal, f x.1 x.2 = a n * q ^ (n : ℕ) := by
    rw [ha, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [hf]
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  have H : HasSum (fun n : ℕ+ ↦ L * (a n * q ^ (n : ℕ))) (L * ∑' p : ℕ+ × ℕ+, f p.1 p.2) := by
    simpa only [hgroup] using (hfs.hasSum.sum_divisorsAntidiagonal).mul_left L
  have H' : HasSum (fun n : ℕ ↦ L * (a n * q ^ n))
      (L * ∑' p : ℕ+ × ℕ+, f p.1 p.2 + L * (a 0 * q ^ 0)) :=
    (hasSum_pnat_iff (f := fun n : ℕ ↦ L * (a n * q ^ n))).mp H
  have hconst : HasSum (fun n : ℕ ↦ if n = 0 then ∑' d : ℤ, g d * (d : ℂ) ^ (-(K : ℤ)) else 0)
      (∑' d : ℤ, g d * (d : ℂ) ^ (-(K : ℤ))) :=
    hasSum_ite_eq 0 _
  convert! H'.add hconst using 1
  · ext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [a]
    · simp [hm, hq, mul_assoc, a]
  · rw [weightedEisensteinSeries_rowWeight_eq_add g z hK hpar, ← hfs.tsum_prod]
    simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty, pow_zero, mul_one, a]
    ring1

/-- **The constant term of an Eisenstein series supported on a row, by Bernoulli polynomials**: for
a function `g` of residues modulo `N` and `k ≥ 2`, the sum `∑_{d ≠ 0} g(d) d^(-k)` is the finite sum
`-(2πi)^k / (k! N) ∑_j 𝓕g(j) B_k(j / N)`. -/
lemma hasSum_mul_zpow_sum_bernoulliFun (hK : 2 ≤ K) : HasSum
    (fun d : ℤ ↦ g d * (d : ℂ) ^ (-(K : ℤ))) ((N : ℂ)⁻¹ * (-(2 * π * I) ^ K / K.factorial) *
      ∑ j : ZMod N, 𝓕 g j * bernoulliFun K (j.val / (N : ℝ))) := by
  have hN : (N : ℂ) ≠ 0 := NeZero.ne (N : ℂ)
  have hfourier (a : ZMod N) (n : ℤ) :
      fourier n ((a.val / (N : ℝ) : ℝ) : UnitAddCircle) = stdAddChar ((n : ZMod N) * a) := by
    rw [fourier_coe_apply, stdAddChar_apply]
    have h : ((ZMod.toCircle ((n * a.val : ℤ) : ZMod N) : Circle) : ℂ) =
        cexp (2 * π * I * ((n * a.val : ℤ) : ℂ) / N) :=
      ZMod.toCircle_intCast (N := N) (n * a.val)
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at h
    rw [h]
    push_cast
    congr 1
    ring1
  have hx (a : ZMod N) : (a.val / (N : ℝ) : ℝ) ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (Nat.cast_pos.mpr (NeZero.pos N))).mpr (by exact_mod_cast (ZMod.val_lt a).le)⟩
  have hs (a : ZMod N) : HasSum (fun d : ℤ ↦ 𝓕 g a *
      (1 / (d : ℂ) ^ K * fourier d ((a.val / (N : ℝ) : ℝ) : UnitAddCircle)))
        (𝓕 g a * (-(2 * π * I) ^ K / K.factorial * bernoulliFun K (a.val / (N : ℝ)))) :=
    (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hK (hx a)).mul_left (𝓕 g a)
  have hsum : HasSum (fun d : ℤ ↦ ∑ a : ZMod N, 𝓕 g a *
      (1 / (d : ℂ) ^ K * fourier d ((a.val / (N : ℝ) : ℝ) : UnitAddCircle)))
        (∑ a : ZMod N, 𝓕 g a *
          (-(2 * π * I) ^ K / K.factorial * bernoulliFun K (a.val / (N : ℝ)))) :=
    hasSum_sum fun a _ ↦ hs a
  have hg (d : ℤ) : ∑ a : ZMod N, 𝓕 g a *
      (1 / (d : ℂ) ^ K * fourier d ((a.val / (N : ℝ) : ℝ) : UnitAddCircle)) =
      N * (g d * (d : ℂ) ^ (-(K : ℤ))) := by
    have hinv : g (d : ZMod N) =
        (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * (d : ZMod N)) • 𝓕 g j := by
      rw [← invDFT_apply, LinearEquiv.symm_apply_apply]
    rw [hinv, zpow_neg, zpow_natCast, smul_eq_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hN,
      one_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hfourier, smul_eq_mul, mul_comm (d : ZMod N)]
    ring1
  simp_rw [hg] at hsum
  have h : (N : ℂ)⁻¹ * (-(2 * π * I) ^ K / K.factorial) *
      ∑ j : ZMod N, 𝓕 g j * bernoulliFun K (j.val / (N : ℝ)) = (N : ℂ)⁻¹ * ∑ a : ZMod N,
        𝓕 g a * (-(2 * π * I) ^ K / K.factorial * bernoulliFun K (a.val / (N : ℝ))) := by
    rw [mul_assoc, Finset.mul_sum]
    exact congrArg _ <| Finset.sum_congr rfl fun a _ ↦ by ring1
  rw [h]
  convert hsum.mul_left (N : ℂ)⁻¹ using 2 with d
  rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

lemma tsum_mul_zpow_eq_sum_bernoulliFun (hK : 2 ≤ K) : ∑' d : ℤ, g d * (d : ℂ) ^ (-(K : ℤ)) =
    (N : ℂ)⁻¹ * (-(2 * π * I) ^ K / K.factorial) *
      ∑ j : ZMod N, 𝓕 g j * bernoulliFun K (j.val / (N : ℝ)) :=
  (hasSum_mul_zpow_sum_bernoulliFun g hK).tsum_eq

end TauCeti.GaloisAction
