import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.CuspIndex
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The gamma vector of a hypergeometric family

For defining parameters `(A, B)`, Möbius inversion of `x^n - 1 = ∏_{m ∣ n} Φ_m(x)` writes
`Φ_A / Φ_B = ∏_{a ∈ A} Φ_a / ∏_{b ∈ B} Φ_b` as `∏_n (x^n - 1)^{e(n)}` with
`e(n) = ∑_{a ∈ A, n ∣ a} μ(a/n) - ∑_{b ∈ B, n ∣ b} μ(b/n)`. The gamma vector `γ` lists `n` with
multiplicity `e(n)` when `e(n) > 0` and `-n` with multiplicity `-e(n)` when `e(n) < 0`, so that
`∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1) = Φ_A / Φ_B`.

## Main definitions

* `Hypergeometric.Parameters.gammaExponent`: the exponent `e(n)` of `x^n - 1`.
* `Hypergeometric.Parameters.gammaVector` (LMFDB `hgm.defining_parameters`): the list `γ`.

## Main results

* `Hypergeometric.Parameters.algebraMap_div_eq_prod_gammaExponent`: in `ℚ(x)` (over `ℤ`),
  `Φ_A / Φ_B = ∏_n (x^n - 1)^{e(n)}`.
* `Hypergeometric.Parameters.count_gammaVector_pos`,
  `Hypergeometric.Parameters.count_gammaVector_neg`: the multiplicities of `n` and `-n` in `γ` are
  the positive and negative parts of `e(n)`.
-/

open Finset Polynomial
open scoped ArithmeticFunction.Moebius

namespace Hypergeometric

variable {d : ℕ} (c : CuspIndex d) (P : Parameters d)

/-- The exponent `∑_{a ∈ C, n ∣ a} μ(a/n)` of `x^n - 1` in `Φ_C = ∏_{a ∈ C} Φ_a`. -/
def CuspIndex.gammaExponent (n : ℕ) : ℤ :=
  (c.toList.map fun a ↦ if n ∣ a then μ (a / n) else 0).sum

/-- The exponent `e(n)` of `x^n - 1` in `Φ_A / Φ_B` for defining parameters `(A, B)`. -/
def Parameters.gammaExponent (n : ℕ) : ℤ :=
  P.A.gammaExponent n - P.B.gammaExponent n

/-- The divisors of the entries of `A` and `B`, outside which `e(n)` vanishes. -/
def Parameters.gammaSupport : Finset ℕ :=
  (P.A.toList ++ P.B.toList).toFinset.biUnion Nat.divisors

/-- The **gamma vector** `γ` of defining parameters `(A, B)` (LMFDB `hgm.defining_parameters`): the
list of nonzero integers in ascending order in which `n > 0` occurs `e(n)` times when `e(n) > 0`
and `-n` occurs `-e(n)` times when `e(n) < 0`, where `e(n)` is the exponent of `x^n - 1` in
`Φ_A / Φ_B`; it is characterised by `∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1) =
Φ_A / Φ_B` (`Hypergeometric.Parameters.algebraMap_div_eq_prod_gammaExponent`). -/
def Parameters.gammaVector : List ℤ :=
  (P.gammaSupport.val.bind fun n ↦
    .replicate (P.gammaExponent n).natAbs ((P.gammaExponent n).sign * n)).sort (· ≤ ·)

variable {S : Finset ℕ}

lemma algebraMap_cyclotomic_eq_prod {a : ℕ} (ha : 0 < a) (hS : a.divisors ⊆ S) :
    algebraMap ℤ[X] (RatFunc ℤ) (cyclotomic a ℤ) =
      ∏ n ∈ S, algebraMap ℤ[X] (RatFunc ℤ) (X ^ n - 1) ^ (if n ∣ a then μ (a / n) else 0) := by
  rw [cyclotomic_eq_prod_X_pow_sub_one_pow_moebius, Nat.prod_divisorsAntidiagonal'
    (fun i j ↦ algebraMap ℤ[X] (RatFunc ℤ) (X ^ j - 1) ^ μ i)]
  have h : S.filter (· ∣ a) = a.divisors := by
    ext n
    rw [mem_filter, Nat.mem_divisors]
    exact ⟨fun h ↦ ⟨h.2, ha.ne'⟩, fun h ↦ ⟨hS <| Nat.mem_divisors.mpr h, h.1⟩⟩
  rw [← h, prod_filter]
  refine prod_congr rfl fun n _ ↦ ?_
  split_ifs <;> simp

lemma algebraMap_X_pow_sub_one_ne_zero {n : ℕ} (hn : 0 < n) :
    algebraMap ℤ[X] (RatFunc ℤ) (X ^ n - 1) ≠ 0 :=
  (map_ne_zero_iff _ <| IsFractionRing.injective ℤ[X] (RatFunc ℤ)).mpr
    (monic_X_pow_sub_one hn.ne').ne_zero

lemma algebraMap_prod_cyclotomic_eq_prod (hS : ∀ n ∈ S, 0 < n) (l : List ℕ)
    (hl : ∀ a ∈ l, 0 < a ∧ a.divisors ⊆ S) :
    algebraMap ℤ[X] (RatFunc ℤ) ((l : Multiset ℕ).map fun a ↦ cyclotomic a ℤ).prod =
      ∏ n ∈ S, algebraMap ℤ[X] (RatFunc ℤ) (X ^ n - 1) ^
        (l.map fun a ↦ if n ∣ a then μ (a / n) else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [Multiset.map_coe, Multiset.prod_coe, List.map_cons, List.prod_cons, map_mul,
      ← Multiset.prod_coe, ← Multiset.map_coe,
      ih fun b hb ↦ hl b <| List.mem_cons_of_mem a hb,
      algebraMap_cyclotomic_eq_prod (hl a List.mem_cons_self).1 (hl a List.mem_cons_self).2,
      ← prod_mul_distrib]
    refine prod_congr rfl fun n hn ↦ ?_
    rw [List.map_cons, List.sum_cons, zpow_add₀ <| algebraMap_X_pow_sub_one_ne_zero <| hS n hn]

lemma Parameters.pos_of_mem_gammaSupport {n : ℕ} (hn : n ∈ P.gammaSupport) : 0 < n := by
  rcases mem_biUnion.mp hn with ⟨a, -, ha⟩
  exact Nat.pos_of_mem_divisors ha

lemma Parameters.divisors_subset_gammaSupport {a : ℕ} (ha : a ∈ P.A.toList ++ P.B.toList) :
    a.divisors ⊆ P.gammaSupport :=
  subset_biUnion_of_mem _ <| List.mem_toFinset.mpr ha

/-- **The gamma vector's defining identity**: in the field of rational functions over `ℤ`,
`Φ_A / Φ_B = ∏_n (x^n - 1)^{e(n)}`, the product over the divisors of the entries of `A` and `B`;
`Hypergeometric.Parameters.count_gammaVector_pos` and
`Hypergeometric.Parameters.count_gammaVector_neg` turn it into the knowl's identity
`∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1) = Φ_A / Φ_B`. -/
lemma Parameters.algebraMap_div_eq_prod_gammaExponent :
    algebraMap ℤ[X] (RatFunc ℤ) ((P.A.toList : Multiset ℕ).map fun a ↦ cyclotomic a ℤ).prod /
      algebraMap ℤ[X] (RatFunc ℤ) ((P.B.toList : Multiset ℕ).map fun b ↦ cyclotomic b ℤ).prod =
        ∏ n ∈ P.gammaSupport, algebraMap ℤ[X] (RatFunc ℤ) (X ^ n - 1) ^ P.gammaExponent n := by
  rw [algebraMap_prod_cyclotomic_eq_prod (fun _ ↦ P.pos_of_mem_gammaSupport) _ fun a ha ↦
      ⟨P.A.pos a ha, P.divisors_subset_gammaSupport <| List.mem_append_left _ ha⟩,
    algebraMap_prod_cyclotomic_eq_prod (fun _ ↦ P.pos_of_mem_gammaSupport) _ fun b hb ↦
      ⟨P.B.pos b hb, P.divisors_subset_gammaSupport <| List.mem_append_right _ hb⟩,
    ← prod_div_distrib]
  refine prod_congr rfl fun n hn ↦ ?_
  rw [Parameters.gammaExponent, CuspIndex.gammaExponent, CuspIndex.gammaExponent,
    zpow_sub₀ <| algebraMap_X_pow_sub_one_ne_zero <| P.pos_of_mem_gammaSupport hn]

lemma CuspIndex.gammaExponent_eq_zero {n : ℕ} (h : ∀ a ∈ c.toList, ¬n ∣ a) :
    c.gammaExponent n = 0 :=
  List.sum_eq_zero fun x hx ↦ by
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    rw [ite_eq_right <| h a ha]

lemma Parameters.gammaExponent_eq_zero {n : ℕ} (hn : n ∉ P.gammaSupport) :
    P.gammaExponent n = 0 := by
  have h (a : ℕ) (ha : a ∈ P.A.toList ++ P.B.toList) (hna : n ∣ a) : False :=
    hn <| P.divisors_subset_gammaSupport ha <| Nat.mem_divisors.mpr
      ⟨hna, (List.mem_append.mp ha).elim (P.A.pos a) (P.B.pos a) |>.ne'⟩
  rw [Parameters.gammaExponent,
    P.A.gammaExponent_eq_zero fun a ha ↦ h a <| List.mem_append_left _ ha,
    P.B.gammaExponent_eq_zero fun b hb ↦ h b <| List.mem_append_right _ hb, sub_zero]

lemma Parameters.count_gammaVector (g : ℤ) : P.gammaVector.count g =
    ∑ m ∈ P.gammaSupport, if (P.gammaExponent m).sign * m = g then (P.gammaExponent m).natAbs
      else 0 := by
  rw [Parameters.gammaVector, ← Multiset.coe_count, Multiset.sort_eq, Multiset.count_bind]
  simp_rw [Multiset.count_replicate]
  rfl

/-- **The multiplicity of `n > 0` in the gamma vector** is the positive part of `e(n)`. -/
lemma Parameters.count_gammaVector_pos {n : ℕ} (hn : 0 < n) :
    P.gammaVector.count (n : ℤ) = (P.gammaExponent n).toNat := by
  have h (m : ℕ) : (if (P.gammaExponent m).sign * m = n then (P.gammaExponent m).natAbs else 0) =
      if m = n then (P.gammaExponent m).toNat else 0 := by
    rcases (P.gammaExponent m).sign_trichotomy with h | h | h <;> rw [h] <;>
      [rw [Int.sign_eq_one_iff_pos] at h; rw [Int.sign_eq_zero_iff_zero] at h;
        rw [Int.sign_eq_neg_one_iff_neg] at h] <;> split_ifs <;> omega
  simp_rw [count_gammaVector, h, sum_ite_eq']
  split_ifs with hS
  · rfl
  · rw [P.gammaExponent_eq_zero hS, Int.toNat_zero]

/-- **The multiplicity of `-n < 0` in the gamma vector** is the negative part of `e(n)`. -/
lemma Parameters.count_gammaVector_neg {n : ℕ} (hn : 0 < n) :
    P.gammaVector.count (-n : ℤ) = (-P.gammaExponent n).toNat := by
  have h (m : ℕ) : (if (P.gammaExponent m).sign * m = -n then (P.gammaExponent m).natAbs else 0) =
      if m = n then (-P.gammaExponent m).toNat else 0 := by
    rcases (P.gammaExponent m).sign_trichotomy with h | h | h <;> rw [h] <;>
      [rw [Int.sign_eq_one_iff_pos] at h; rw [Int.sign_eq_zero_iff_zero] at h;
        rw [Int.sign_eq_neg_one_iff_neg] at h] <;> split_ifs <;> omega
  simp_rw [count_gammaVector, h, sum_ite_eq']
  split_ifs with hS
  · rfl
  · rw [P.gammaExponent_eq_zero hS, neg_zero, Int.toNat_zero]

end Hypergeometric
