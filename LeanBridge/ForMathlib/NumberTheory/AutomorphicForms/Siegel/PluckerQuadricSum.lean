import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.VectorKlingenBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The lattice sum over the quadric of Plücker vectors

The Plücker vectors `p ∈ ℤ⁵` of the bottom rows of the elements of `Sp(4, ℤ)` lie on the quadric
`p₀ p₄ + p₂² + p₁ p₃ = 0`. The sum `∑ ‖p‖^{-k}` over the nonzero points of this quadric converges
for `k > 3`, which is the bound that the Siegel Eisenstein series of degree `2` needs, whereas the
sum over all of `ℤ⁵` needs `k > 5`.

The points with `p₀ p₄ ≠ 0` are fibred over `q = (p₁, p₂, p₃) ∈ ℤ³`. For given `q`, the integer
`m = p₀ p₄ = -(p₂² + p₁ p₃)` is nonzero, with `|m| ≤ 2 ‖q‖²`, so that the fibre has at most
`2 d(|m|)` points, one for each divisor `p₀` of `m`, and each of them has `‖p‖ ≥ ‖q‖`. The divisor
bound `d(n)³ ≤ 8⁴ n` then gives at most `64 ‖q‖^{2/3}` points, so that the sum over a fibre is at
most `64 ‖q‖^{-10/3}`, whose sum over `ℤ³` converges. The points with `p₀ p₄ = 0` are fibred over
`(p₁, p₃, p₀ + p₄) ∈ ℤ³`, with at most four points in a fibre, as `p₂` is determined up to its sign.

## Main results

* `Nat.card_divisors_pow_three_le`: the divisor bound `d(n)³ ≤ 8⁴ n`.
* `Int.card_divisors`: an integer `z` has `2 d(|z|)` divisors.
* `summable_of_sum_fiber_le`: a nonnegative function whose sums over the fibres of a map are
  dominated by a summable function on the base is summable.
* `SiegelUpperHalfSpace.summable_norm_zpow_quadric`: the sum over the quadric converges for `k > 3`.
-/

open Finset

namespace Nat

private lemma succ_pow_three_le_two_pow (e : ℕ) : (e + 1) ^ 3 ≤ 8 * 2 ^ e := by
  rcases lt_or_ge e 4 with h | h
  · interval_cases e <;> norm_num
  · induction e, h using Nat.le_induction with
    | base => norm_num
    | succ e he ih =>
      rw [pow_succ 2 e]
      nlinarith [pow_pos (Nat.succ_pos e) 2]

private lemma succ_pow_three_le_mul_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (e + 1) ^ 3 ≤ (if p < 8 then 8 else 1) * p ^ e := by
  split_ifs with h
  · exact (succ_pow_three_le_two_pow e).trans
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hp.two_le e))
  · rw [one_mul]
    have h₁ : (e + 1) ^ 3 ≤ (2 ^ e) ^ 3 := Nat.pow_le_pow_left Nat.lt_two_pow_self 3
    have h₂ : (2 ^ e) ^ 3 = 8 ^ e := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    exact (h₁.trans_eq h₂).trans (Nat.pow_le_pow_left (not_lt.mp h) e)

/-- **The divisor bound** `d(n)³ ≤ 8⁴ n`: in the product over the primes `p` dividing `n`,
`(e + 1)³ ≤ p^e` for `p ≥ 8`, and `(e + 1)³ ≤ 8 p^e` for the four primes below `8`. -/
lemma card_divisors_pow_three_le (n : ℕ) : #n.divisors ^ 3 ≤ 4096 * n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have h₁ : ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 3 ≤
      ∏ p ∈ n.primeFactors, (if p < 8 then 8 else 1) * p ^ n.factorization p :=
    prod_le_prod fun p hp ↦ succ_pow_three_le_mul_pow (prime_of_mem_primeFactors hp) _
  have h₂ : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    prod_factorization_pow_eq_self hn
  have h₃ : ∏ p ∈ n.primeFactors, (if p < 8 then 8 else 1) ≤ 4096 := by
    have h₄ : #(n.primeFactors.filter (· < 8)) ≤ 4 := by
      refine card_le_card (t := {2, 3, 5, 7}) fun p hp ↦ ?_
      rcases mem_filter.mp hp with ⟨hp₁, hp₂⟩
      have hp₃ : p.Prime := prime_of_mem_primeFactors hp₁
      interval_cases p <;> first | decide | exact absurd hp₃ (by decide)
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    exact (Nat.pow_le_pow_right (by norm_num) h₄).trans_eq (by norm_num)
  rw [card_divisors hn, ← prod_pow]
  rw [prod_mul_distrib, h₂] at h₁
  exact h₁.trans (Nat.mul_le_mul_right n h₃)

end Nat

namespace Int

/-- **An integer `z` has `2 d(|z|)` divisors.** -/
lemma card_divisors (z : ℤ) : #z.divisors = 2 * #z.natAbs.divisors := by
  rw [divisors, card_disjUnion, card_map, card_map, two_mul]

end Int

/-- **The fibre criterion for summability**: a nonnegative function whose sums over the finite
subsets of the fibres of a map `g` are dominated by a summable function on the base is summable. -/
lemma summable_of_sum_fiber_le {α β : Type*} {f : α → ℝ} {w : β → ℝ} (g : α → β) (hf : 0 ≤ f)
    (hw : Summable w) (h : ∀ (b : β) (s : Finset α), (∀ a ∈ s, g a = b) → ∑ a ∈ s, f a ≤ w b) :
    Summable f := by
  classical
  have hw₀ (b : β) : 0 ≤ w b := by
    simpa using h b ∅ (by simp)
  refine summable_of_sum_le hf (c := ∑' b, w b) fun u ↦ ?_
  rw [← sum_fiberwise_of_maps_to (g := g) (t := u.image g) fun a ha ↦ mem_image_of_mem g ha]
  exact (sum_le_sum fun b _ ↦ h b _ fun a ha ↦ (mem_filter.mp ha).2).trans
    (hw.sum_le_tsum _ fun b _ ↦ hw₀ b)

namespace SiegelUpperHalfSpace

variable {ι : Type*} [Fintype ι] {x : ι → ℤ} {b : ℝ}

private lemma one_le_norm_of_ne_zero (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  rcases Function.ne_iff.mp hx with ⟨i, hi⟩
  have h : (1 : ℝ) ≤ ‖x i‖ := by
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h.trans (norm_le_pi_norm x i)

variable (x) in
private lemma abs_le_norm (i : ι) : |(x i : ℝ)| ≤ ‖x‖ :=
  (Int.norm_eq_abs (x i)).symm.trans_le (norm_le_pi_norm x i)

private lemma norm_le_of_forall_abs_le {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |(x i : ℝ)| ≤ r) : ‖x‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).mpr fun i ↦ (Int.norm_eq_abs (x i)).trans_le (h i)

private lemma zpow_neg_four_le {a : ℝ} (hb : 0 < b) (h : b ≤ a) : a ^ (-4 : ℤ) ≤ b ^ (-4 : ℤ) := by
  rw [zpow_neg, zpow_neg]
  exact inv_anti₀ (zpow_pos hb 4) (zpow_le_zpow_left₀ (by norm_num) hb.le h)

/-! ### The points with `p₀ p₄ ≠ 0` -/

variable {q : Fin 3 → ℤ}

private lemma two_mul_card_divisors_le :
    (2 * #(q 1 ^ 2 + q 0 * q 2).natAbs.divisors : ℝ) ≤ 64 * ‖q‖ ^ (2 / 3 : ℝ) := by
  have hm : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  have hz : |((q 1 ^ 2 + q 0 * q 2 : ℤ) : ℝ)| ≤ 2 * ‖q‖ ^ 2 := by
    have h₀ : |(q 0 : ℝ)| ≤ ‖q‖ := abs_le_norm q 0
    have h₁ : |(q 1 : ℝ)| ≤ ‖q‖ := abs_le_norm q 1
    have h₂ : |(q 2 : ℝ)| ≤ ‖q‖ := abs_le_norm q 2
    push_cast
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_pow, two_mul, pow_two ‖q‖]
    exact add_le_add (pow_two |(q 1 : ℝ)| ▸ mul_le_mul h₁ h₁ (abs_nonneg _) hm)
      (mul_le_mul h₀ h₂ (abs_nonneg _) hm)
  have hd : ((#(q 1 ^ 2 + q 0 * q 2).natAbs.divisors : ℕ) : ℝ) ^ 3 ≤
      4096 * |((q 1 ^ 2 + q 0 * q 2 : ℤ) : ℝ)| := by
    have h' : ((#(q 1 ^ 2 + q 0 * q 2).natAbs.divisors ^ 3 : ℕ) : ℝ) ≤
        ((4096 * (q 1 ^ 2 + q 0 * q 2).natAbs : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.card_divisors_pow_three_le _)
    rwa [Nat.cast_pow, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat] at h'
  refine le_of_pow_le_pow_left₀ three_ne_zero (by positivity) ?_
  have e : (64 * ‖q‖ ^ (2 / 3 : ℝ)) ^ 3 = 262144 * ‖q‖ ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (‖q‖ ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hm]
    norm_num
  rw [e, mul_pow]
  nlinarith

private lemma sum_zpow_neg_four_le {t : Finset (Fin 5 → ℤ)} {N : ℝ} (hb : 0 < b)
    (ht : ∀ a ∈ t, b ≤ ‖a‖) (hN : (#t : ℝ) ≤ N) : ∑ a ∈ t, ‖a‖ ^ (-4 : ℤ) ≤ N * b ^ (-4 : ℤ) :=
  ((sum_le_card_nsmul _ _ _ fun a ha ↦ zpow_neg_four_le hb (ht a ha)).trans_eq
    (nsmul_eq_mul _ _)).trans (mul_le_mul_of_nonneg_right hN (by positivity))

private lemma summable_quadric_main : Summable fun p : Fin 5 → ℤ ↦
    if p 0 * p 4 ≠ 0 ∧ p 0 * p 4 + p 2 ^ 2 + p 1 * p 3 = 0 then ‖p‖ ^ (-4 : ℤ) else 0 := by
  classical
  refine summable_of_sum_fiber_le (fun p ↦ ![p 1, p 2, p 3])
    (w := fun q ↦ 64 * ‖q‖ ^ (-(10 / 3) : ℝ)) (fun p ↦ ?_)
    ((summable_norm_rpow_int (by norm_num)).mul_left 64) fun q s hs ↦ ?_
  · dsimp only
    split_ifs <;> positivity
  have hq (a : Fin 5 → ℤ) (ha : a ∈ s) : a 1 = q 0 ∧ a 2 = q 1 ∧ a 3 = q 2 :=
    ⟨congrFun (hs a ha) 0, congrFun (hs a ha) 1, congrFun (hs a ha) 2⟩
  rw [← sum_filter]
  generalize ht : s.filter (fun a ↦ a 0 * a 4 ≠ 0 ∧ a 0 * a 4 + a 2 ^ 2 + a 1 * a 3 = 0) = t
  have hprod (a : Fin 5 → ℤ) (ha : a ∈ t) : a 0 * a 4 = -(q 1 ^ 2 + q 0 * q 2) := by
    rw [← ht] at ha
    rcases mem_filter.mp ha with ⟨ha₁, -, ha₂⟩
    rcases hq a ha₁ with ⟨e₁, e₂, e₃⟩
    rw [e₁, e₂, e₃] at ha₂
    linarith
  have hmem (a : Fin 5 → ℤ) (ha : a ∈ t) : a ∈ s := by
    rw [← ht] at ha
    exact (mem_filter.mp ha).1
  rcases t.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · rw [sum_empty]
    positivity
  have hz : q 1 ^ 2 + q 0 * q 2 ≠ 0 := by
    rw [← neg_ne_zero, ← hprod a₀ ha₀]
    rw [← ht] at ha₀
    exact (mem_filter.mp ha₀).2.1
  have hq₀ : q ≠ 0 := by
    rintro rfl
    simp at hz
  have hm : 0 < ‖q‖ := norm_pos_iff.mpr hq₀
  have hcard : #t ≤ 2 * #(q 1 ^ 2 + q 0 * q 2).natAbs.divisors := by
    rw [← Int.natAbs_neg, ← Int.card_divisors]
    refine card_le_card_of_injOn (fun a ↦ a 0) (fun a ha ↦ ?_) fun a ha a' ha' h ↦ ?_
    · exact Int.mem_divisors.mpr ⟨Dvd.intro _ (hprod a ha), neg_ne_zero.mpr hz⟩
    · have h₀ : a 0 = a' 0 := h
      have h₁ : a 0 ≠ 0 := left_ne_zero_of_mul <| (hprod a ha).trans_ne (neg_ne_zero.mpr hz)
      have h₂ : a 4 = a' 4 := mul_left_cancel₀ h₁ <| (hprod a ha).trans <| by
        rw [h₀, hprod a' ha']
      rcases hq a (hmem a ha) with ⟨e₁, e₂, e₃⟩
      rcases hq a' (hmem a' ha') with ⟨e₁', e₂', e₃'⟩
      ext i
      fin_cases i
      · exact h₀
      · exact e₁.trans e₁'.symm
      · exact e₂.trans e₂'.symm
      · exact e₃.trans e₃'.symm
      · exact h₂
  have hnorm (a : Fin 5 → ℤ) (ha : a ∈ t) : ‖q‖ ≤ ‖a‖ := by
    rcases hq a (hmem a ha) with ⟨e₁, e₂, e₃⟩
    have h₀ : |(q 0 : ℝ)| ≤ ‖a‖ := e₁ ▸ abs_le_norm a 1
    have h₁ : |(q 1 : ℝ)| ≤ ‖a‖ := e₂ ▸ abs_le_norm a 2
    have h₂ : |(q 2 : ℝ)| ≤ ‖a‖ := e₃ ▸ abs_le_norm a 3
    refine norm_le_of_forall_abs_le (norm_nonneg a) fun i ↦ ?_
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  have hN : (#t : ℝ) ≤ 64 * ‖q‖ ^ (2 / 3 : ℝ) :=
    (Nat.cast_le.mpr hcard).trans (by simpa using two_mul_card_divisors_le (q := q))
  have e : 64 * ‖q‖ ^ (-(10 / 3) : ℝ) = 64 * ‖q‖ ^ (2 / 3 : ℝ) * ‖q‖ ^ (-4 : ℤ) := by
    rw [mul_assoc, ← Real.rpow_intCast, ← Real.rpow_add hm]
    norm_num
  rw [e]
  exact sum_zpow_neg_four_le hm hnorm hN

/-! ### The points with `p₀ p₄ = 0` -/

private lemma summable_quadric_degenerate : Summable fun p : Fin 5 → ℤ ↦
    if p ≠ 0 ∧ p 0 * p 4 = 0 ∧ p 2 ^ 2 + p 1 * p 3 = 0 then ‖p‖ ^ (-4 : ℤ) else 0 := by
  classical
  have hw : Summable fun u : Fin 3 → ℤ ↦ 4 * ‖u‖ ^ (-4 : ℤ) := by
    refine ((summable_norm_rpow_int (r := -4) (by norm_num)).congr fun u ↦ ?_).mul_left 4
    rw [← Real.rpow_intCast]
    norm_num
  refine summable_of_sum_fiber_le (fun p ↦ ![p 1, p 3, p 0 + p 4]) (fun p ↦ ?_) hw fun u s hs ↦ ?_
  · dsimp only
    split_ifs <;> positivity
  have hq (a : Fin 5 → ℤ) (ha : a ∈ s) : a 1 = u 0 ∧ a 3 = u 1 ∧ a 0 + a 4 = u 2 :=
    ⟨congrFun (hs a ha) 0, congrFun (hs a ha) 1, congrFun (hs a ha) 2⟩
  rw [← sum_filter]
  generalize ht : s.filter (fun a ↦ a ≠ 0 ∧ a 0 * a 4 = 0 ∧ a 2 ^ 2 + a 1 * a 3 = 0) = t
  have hmem (a : Fin 5 → ℤ) (ha : a ∈ t) :
      a ∈ s ∧ a ≠ 0 ∧ a 0 * a 4 = 0 ∧ a 2 ^ 2 + a 1 * a 3 = 0 := by
    rw [← ht] at ha
    exact mem_filter.mp ha
  rcases t.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · rw [sum_empty]
    positivity
  have hu₀ : u ≠ 0 := by
    rintro rfl
    rcases hmem a₀ ha₀ with ⟨h₁, h₂, h₃, h₄⟩
    rcases hq a₀ h₁ with ⟨e₁, e₂, e₃⟩
    have e₁' : a₀ 1 = 0 := e₁
    have e₂' : a₀ 3 = 0 := e₂
    have e₃' : a₀ 0 + a₀ 4 = 0 := e₃
    rw [e₁', zero_mul, add_zero, sq_eq_zero_iff] at h₄
    refine h₂ ?_
    rcases mul_eq_zero.mp h₃ with h | h
    · ext i
      fin_cases i
      · exact h
      · exact e₁'
      · exact h₄
      · exact e₂'
      · simpa [h] using e₃'
    · ext i
      fin_cases i
      · simpa [h] using e₃'
      · exact e₁'
      · exact h₄
      · exact e₂'
      · exact h
  have hm : 0 < ‖u‖ := norm_pos_iff.mpr hu₀
  have hcard : #t ≤ 4 := by
    refine card_le_card_of_injOn (t := (univ : Finset (Bool × Bool)))
      (fun a ↦ (decide (0 ≤ a 2), decide (a 0 = 0))) (fun a _ ↦ mem_univ _) fun a ha a' ha' h ↦ ?_
    rcases Prod.ext_iff.mp h with ⟨h₁, h₂⟩
    have hs₂ : 0 ≤ a 2 ↔ 0 ≤ a' 2 := decide_eq_decide.mp h₁
    have hs₀ : a 0 = 0 ↔ a' 0 = 0 := decide_eq_decide.mp h₂
    rcases hmem a ha with ⟨has, -, h₃, h₄⟩
    rcases hmem a' ha' with ⟨has', -, h₃', h₄'⟩
    rcases hq a has with ⟨e₁, e₂, e₃⟩
    rcases hq a' has' with ⟨e₁', e₂', e₃'⟩
    have e₁₁ : a 1 = a' 1 := e₁.trans e₁'.symm
    have e₃₃ : a 3 = a' 3 := e₂.trans e₂'.symm
    have h₅ : a 2 ^ 2 = a' 2 ^ 2 := by
      rw [e₁₁, e₃₃] at h₄
      linarith
    have e₂₂ : a 2 = a' 2 := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h₅ with h₆ | h₆ <;> omega
    have e₀₄ : a 0 = a' 0 ∧ a 4 = a' 4 := by
      rcases mul_eq_zero.mp h₃ with h₆ | h₆ <;> rcases mul_eq_zero.mp h₃' with h₆' | h₆' <;> omega
    ext i
    fin_cases i
    · exact e₀₄.1
    · exact e₁₁
    · exact e₂₂
    · exact e₃₃
    · exact e₀₄.2
  have hnorm (a : Fin 5 → ℤ) (ha : a ∈ t) : ‖u‖ ≤ ‖a‖ := by
    rcases hmem a ha with ⟨has, -, h₃, -⟩
    rcases hq a has with ⟨e₁, e₂, e₃⟩
    have h₀ : |(u 0 : ℝ)| ≤ ‖a‖ := e₁ ▸ abs_le_norm a 1
    have h₁ : |(u 1 : ℝ)| ≤ ‖a‖ := e₂ ▸ abs_le_norm a 3
    have h₂ : |(u 2 : ℝ)| ≤ ‖a‖ := by
      rcases mul_eq_zero.mp h₃ with h | h
      · rw [← e₃, h, zero_add]
        exact abs_le_norm a 4
      · rw [← e₃, h, add_zero]
        exact abs_le_norm a 0
    refine norm_le_of_forall_abs_le (norm_nonneg a) fun i ↦ ?_
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  exact sum_zpow_neg_four_le hm hnorm (by exact_mod_cast hcard)

/-- **The sum over the quadric of Plücker vectors**: `∑ ‖p‖^{-k}`, over the nonzero `p ∈ ℤ⁵` with
`p₀ p₄ + p₂² + p₁ p₃ = 0`, converges for `k > 3`, in the form of a sum over an injective family of
such points. -/
lemma summable_norm_zpow_quadric {α : Type*} {k : ℤ} (hk : 3 < k) {P : α → Fin 5 → ℤ}
    (hP : Function.Injective P) (h₀ : ∀ x, P x ≠ 0)
    (hQ : ∀ x, P x 0 * P x 4 + P x 2 ^ 2 + P x 1 * P x 3 = 0) : Summable fun x ↦ ‖P x‖ ^ (-k) := by
  refine Summable.of_nonneg_of_le (fun x ↦ by positivity) (fun x ↦ ?_)
    ((summable_quadric_main.add summable_quadric_degenerate).comp_injective hP)
  have h₁ : ‖P x‖ ^ (-k) ≤ ‖P x‖ ^ (-4 : ℤ) :=
    zpow_le_zpow_right₀ (one_le_norm_of_ne_zero (h₀ x)) (by omega)
  refine h₁.trans ?_
  simp only [Function.comp_apply]
  by_cases h : P x 0 * P x 4 = 0
  · rw [ite_eq_right fun h' ↦ h'.1 h, ite_eq_left ⟨h₀ x, h, by linarith [hQ x]⟩, zero_add]
  · rw [ite_eq_left ⟨h, hQ x⟩]
    exact le_add_of_nonneg_right (by split_ifs <;> positivity)

end SiegelUpperHalfSpace
