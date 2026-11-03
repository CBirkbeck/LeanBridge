import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.HalfIntegralCuspBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraCorrespondence
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The growth of the Shimura lift

Hecke's bound `|a(n)| ≪ n ^ (k/4)` for `g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, gives the
bound `|A(n)| ≪ n ^ (l + 1/2)` for the sequence `A = Sh_t(a)`, since
`d ^ (l - 1) e ^ (l + 1/2) = (d e) ^ (l + 1/2) d ^ (-3/2)` and `∑ d ^ (-3/2)` converges. Hence
`∑ A(n) e(n w) ≪ (Im w) ^ (-M)` for every `M > l + 3/2`.

## Main results

* `ModularForm.exists_norm_shimuraCoeff_le`: the bound of the coefficients.
* `ModularForm.exists_norm_expSum_le_rpow`: the bound of an exponential sum, with a real exponent.
-/

open Complex CongruenceSubgroup Filter

open scoped Real MatrixGroups Manifold NumberTheorySymbols

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {l t : ℕ} {g : ℍ → ℂ}

private lemma norm_jacobiSym_le (a : ℤ) (b : ℕ) : ‖((J(a | b) : ℤ) : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy a b with h | h | h <;> simp [h]

lemma norm_shimuraCharacter_le (m : ℕ) : ‖shimuraCharacter χ (2 * l + 1) t m‖ ≤ 1 := by
  have e0 : (((2 * (l : ℤ) + 1 - 1) / 2 : ℤ)) = l := by omega
  rw [shimuraCharacter, e0, zpow_natCast, norm_mul, norm_mul, norm_pow]
  have h1 : ‖χ m‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have h2 : ‖((J(-1 | m) : ℤ) : ℂ)‖ ^ l ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_jacobiSym_le _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (by positivity) h1).trans h2)).trans (norm_jacobiSym_le t m)

private lemma summable_rpow_inv : Summable fun d : ℕ ↦ ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

variable [NeZero N] in
/-- **The bound of the coefficients of the Shimura lift**: `|Sh_t(a)(n)| ≤ K n ^ (l + 1/2)` for
`g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `4 ∣ N`, `t ≥ 1`. -/
lemma exists_norm_shimuraCoeff_le (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N)
    (ht : 0 < t) : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, n ≠ 0 →
      ‖shimuraCoeff χ (2 * l + 1) t (fun m ↦ (qExpansion 1 g).coeff m) n‖ ≤
        K * (n : ℝ) ^ ((l : ℝ) + 1 / 2) := by
  rcases exists_norm_coeff_qExpansion_le hg (by simp) h4 with ⟨K₀, hK₀, hK⟩
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have e0 : (((2 * (l : ℤ) + 1 - 1) / 2 : ℤ)) = l := by omega
  have hS : 0 ≤ ∑' d : ℕ, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ := tsum_nonneg fun d ↦ by positivity
  refine ⟨K₀ * (t : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) * ∑' d : ℕ, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹,
    by positivity, fun n hn ↦ ?_⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hterm : ∀ p ∈ n.divisorsAntidiagonal,
      ‖shimuraCharacter χ (2 * l + 1) t p.1 *
        (p.1 : ℂ) ^ ((((2 * (l : ℤ) + 1 - 1) / 2 : ℤ) : ℂ) - 1) *
        (qExpansion 1 g).coeff (t * p.2 ^ 2)‖ ≤
          K₀ * (t : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) * (n : ℝ) ^ ((l : ℝ) + 1 / 2) *
            ((p.1 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpn, -⟩
    have hp1 : 0 < p.1 := Nat.pos_of_ne_zero fun h ↦ hn (by rw [← hpn, h, zero_mul])
    have hp2 : 0 < p.2 := Nat.pos_of_ne_zero fun h ↦ hn (by rw [← hpn, h, mul_zero])
    have hd : (0 : ℝ) < p.1 := Nat.cast_pos.mpr hp1
    have he : (0 : ℝ) < p.2 := Nat.cast_pos.mpr hp2
    have h1 : ‖(qExpansion 1 g).coeff (t * p.2 ^ 2)‖ ≤
        K₀ * ((t * p.2 ^ 2 : ℕ) : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) :=
      hK (t * p.2 ^ 2) (mul_ne_zero ht.ne' (pow_ne_zero 2 hp2.ne'))
    have e1 : ((t * p.2 ^ 2 : ℕ) : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) =
        (t : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) * (p.2 : ℝ) ^ ((l : ℝ) + 1 / 2) := by
      push_cast
      rw [Real.mul_rpow ht'.le (by positivity), ← Real.rpow_natCast (p.2 : ℝ) 2,
        ← Real.rpow_mul he.le]
      congr 2
      push_cast
      ring1
    have e2 :
        ‖(p.1 : ℂ) ^ ((((2 * (l : ℤ) + 1 - 1) / 2 : ℤ) : ℂ) - 1)‖ = (p.1 : ℝ) ^ ((l : ℝ) - 1) := by
      rw [Complex.norm_natCast_cpow_of_pos hp1, e0]
      simp
    have e3 : (p.1 : ℝ) ^ ((l : ℝ) - 1) * (p.2 : ℝ) ^ ((l : ℝ) + 1 / 2) =
        (n : ℝ) ^ ((l : ℝ) + 1 / 2) * ((p.1 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      rw [← hpn]
      push_cast
      rw [Real.mul_rpow hd.le he.le, ← Real.rpow_neg hd.le, mul_right_comm, ← Real.rpow_add hd]
      congr 2
      ring1
    rw [norm_mul, norm_mul, e2]
    have h2 : ‖shimuraCharacter χ (2 * l + 1) t p.1‖ ≤ 1 := norm_shimuraCharacter_le p.1
    rw [e1] at h1
    have hP : 0 ≤ (p.1 : ℝ) ^ ((l : ℝ) - 1) := by positivity
    have h3 : ‖shimuraCharacter χ (2 * l + 1) t p.1‖ * (p.1 : ℝ) ^ ((l : ℝ) - 1) *
        ‖(qExpansion 1 g).coeff (t * p.2 ^ 2)‖ ≤ 1 * (p.1 : ℝ) ^ ((l : ℝ) - 1) *
          (K₀ * ((t : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) * (p.2 : ℝ) ^ ((l : ℝ) + 1 / 2))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h2 hP) h1 (norm_nonneg _) (by positivity)
    refine h3.trans_eq ?_
    linear_combination (K₀ * (t : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4)) * e3
  have e4 : ∑ p ∈ n.divisorsAntidiagonal, ((p.1 : ℝ) ^ (3 / 2 : ℝ))⁻¹ =
      ∑ d ∈ n.divisors, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    Nat.sum_divisorsAntidiagonal fun x _ ↦ ((x : ℝ) ^ (3 / 2 : ℝ))⁻¹
  rw [shimuraCoeff, LSeries.convolution_def]
  refine (norm_sum_le_of_le _ hterm).trans ?_
  have e6 : K₀ * (t : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) * (∑' d : ℕ, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹) *
      (n : ℝ) ^ ((l : ℝ) + 1 / 2) = K₀ * (t : ℝ) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) *
        (n : ℝ) ^ ((l : ℝ) + 1 / 2) * ∑' d : ℕ, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    ring1
  rw [← Finset.mul_sum, e4, e6]
  exact mul_le_mul_of_nonneg_left
    (summable_rpow_inv.sum_le_tsum n.divisors fun d _ ↦ by positivity) (by positivity)

variable [NeZero N] in
lemma hasPolyGrowth_shimuraCoeff (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N)
    (ht : 0 < t) :
    HasPolyGrowth (shimuraCoeff χ (2 * l + 1) t fun m ↦ (qExpansion 1 g).coeff m) := by
  rcases exists_norm_shimuraCoeff_le hg h4 ht with ⟨K, hK0, hK⟩
  refine ⟨K, l + 1, fun n hn ↦ (hK n hn).trans (mul_le_mul_of_nonneg_left ?_ hK0)⟩
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rw [← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_le h1 ?_
  push_cast
  linarith

private lemma rpow_mul_exp_neg_le {x M : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M) :
    x ^ M * Real.exp (-(2 * π * x)) ≤ (⌈M⌉₊).factorial * Real.exp 1 := by
  have hp : 3 < π := Real.pi_gt_three
  have h1 : x ^ M ≤ (1 + x) ^ (⌈M⌉₊ : ℝ) :=
    (Real.rpow_le_rpow hx (by linarith) hM).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil M))
  have h2 : (1 + x) ^ ⌈M⌉₊ / ((⌈M⌉₊).factorial : ℝ) ≤ Real.exp (1 + x) :=
    Real.pow_div_factorial_le_exp (1 + x) (by linarith) ⌈M⌉₊
  have hf : (0 : ℝ) < (⌈M⌉₊).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_iff₀ hf] at h2
  rw [Real.rpow_natCast] at h1
  have h3 : Real.exp (1 + x) * Real.exp (-(2 * π * x)) ≤ Real.exp 1 := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  refine (mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le).trans ?_
  have e : Real.exp (1 + x) * (⌈M⌉₊).factorial * Real.exp (-(2 * π * x)) =
      (⌈M⌉₊).factorial * (Real.exp (1 + x) * Real.exp (-(2 * π * x))) := by
    ring1
  rw [e]
  exact mul_le_mul_of_nonneg_left h3 hf.le

/-- **The bound of an exponential sum, with a real exponent**: if `c 0 = 0` and `|c n| ≤ C n ^ s`
with `s ≥ 0`, then `∑ c n e(n z) = O((Im z) ^ (-(s + 1 + ε)))` on `ℍ` for every `ε > 0`. -/
lemma exists_norm_expSum_le_rpow {c : ℕ → ℂ} {C s ε : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, n ≠ 0 → ‖c n‖ ≤ C * (n : ℝ) ^ s) (h0 : c 0 = 0) (hs : 0 ≤ s) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, ‖expSum c z‖ ≤ K * z.im ^ (-(s + 1 + ε)) := by
  have hM : 0 ≤ s + 1 + ε := by linarith
  have hZ : Summable fun n : ℕ ↦ ((n : ℝ) ^ (1 + ε))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  have hZ0 : 0 ≤ ∑' n : ℕ, ((n : ℝ) ^ (1 + ε))⁻¹ := tsum_nonneg fun n ↦ by positivity
  refine ⟨C * ((⌈s + 1 + ε⌉₊).factorial * Real.exp 1) * ∑' n : ℕ, ((n : ℝ) ^ (1 + ε))⁻¹,
    by positivity, fun z ↦ ?_⟩
  have hy : 0 < z.im := z.im_pos
  have hterm (n : ℕ) : ‖c n * cexp (2 * π * I * n * z)‖ ≤
      C * ((⌈s + 1 + ε⌉₊).factorial * Real.exp 1) * z.im ^ (-(s + 1 + ε)) *
        ((n : ℝ) ^ (1 + ε))⁻¹ := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [h0, zero_mul, norm_zero]
      positivity
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hnz : 0 < (n : ℝ) * z.im := by positivity
      have h1 : ((n : ℝ) * z.im) ^ (s + 1 + ε) * Real.exp (-(2 * π * ((n : ℝ) * z.im))) ≤
          (⌈s + 1 + ε⌉₊).factorial * Real.exp 1 :=
        rpow_mul_exp_neg_le hnz.le hM
      have e1 : Real.exp (-(2 * π * ((n : ℝ) * z.im))) = Real.exp (-(2 * π * z.im) * n) := by
        congr 1
        ring1
      have e2 : (n : ℝ) ^ s * Real.exp (-(2 * π * z.im) * n) =
          ((n : ℝ) * z.im) ^ (s + 1 + ε) * Real.exp (-(2 * π * z.im) * n) *
            (z.im ^ (-(s + 1 + ε)) * ((n : ℝ) ^ (1 + ε))⁻¹) := by
        rw [Real.mul_rpow hn'.le hy.le, Real.rpow_neg hy.le, ← Real.rpow_neg hn'.le]
        have e3 : (n : ℝ) ^ (s + 1 + ε) * (n : ℝ) ^ (-(1 + ε)) = (n : ℝ) ^ s := by
          rw [← Real.rpow_add hn']
          congr 1
          ring1
        have e4 : z.im ^ (s + 1 + ε) * (z.im ^ (s + 1 + ε))⁻¹ = 1 :=
          mul_inv_cancel₀ (by positivity)
        linear_combination (-(n : ℝ) ^ (s + 1 + ε) * (n : ℝ) ^ (-(1 + ε)) *
          Real.exp (-(2 * π * z.im) * n)) * e4 - Real.exp (-(2 * π * z.im) * n) * e3
      rw [e1] at h1
      rw [norm_mul, norm_cexp_two_pi_I_mul]
      have h2 : ‖c n‖ * Real.exp (-(2 * π * z.im) * n) ≤
          C * ((n : ℝ) ^ s * Real.exp (-(2 * π * z.im) * n)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hC n hn) (Real.exp_pos _).le
      have h3 : (n : ℝ) ^ s * Real.exp (-(2 * π * z.im) * n) ≤
          (⌈s + 1 + ε⌉₊).factorial * Real.exp 1 *
            (z.im ^ (-(s + 1 + ε)) * ((n : ℝ) ^ (1 + ε))⁻¹) := by
        rw [e2]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      refine h2.trans ((mul_le_mul_of_nonneg_left h3 hC0).trans_eq ?_)
      ring1
  have hsum : HasSum (fun n : ℕ ↦ C * ((⌈s + 1 + ε⌉₊).factorial * Real.exp 1) *
      z.im ^ (-(s + 1 + ε)) * ((n : ℝ) ^ (1 + ε))⁻¹)
        (C * ((⌈s + 1 + ε⌉₊).factorial * Real.exp 1) * z.im ^ (-(s + 1 + ε)) *
          ∑' n : ℕ, ((n : ℝ) ^ (1 + ε))⁻¹) :=
    hZ.hasSum.mul_left _
  refine (tsum_of_norm_bounded hsum hterm).trans_eq ?_
  ring1

end ModularForm
