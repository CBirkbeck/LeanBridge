import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Valuation.Basic

/-!
# Two notions of equivalence for real-valued valuations

Let `v₁` and `v₂` be additive valuations of a ring `R` with values in `ℝ ∪ {∞}`, that is terms of
`AddValuation R (WithTop ℝ)`, and let `p > 1`. Set `|x|_i = p ^ (-v_i(x))`, with `|x|_i = 0` when
`v_i(x) = ∞`. The two notions of equivalence of LMFDB `nf.valuation_equivalence` agree: there is a
real `c > 0` with `|x|_1 = |x|_2 ^ c` for all `x` exactly when `v₁` and `v₂` induce the same
preorder on `R`, which is Mathlib's `AddValuation.IsEquiv` (by definition `Valuation.IsEquiv`).
Mathlib proves the analogue `AbsoluteValue.isEquiv_iff_exists_rpow_eq` for real absolute values of
a field; here `R` is any ring, and the supports of the valuations may be nonzero.

The proof compares `v(r ^ m a ^ k)` with `v(r ^ m' a ^ k')` for natural numbers `m, k, m', k'`:
equivalent valuations give the same answers, which forces `v₁(r) / v₁(a) = v₂(r) / v₂(a)`, since
otherwise a rational number lies strictly between the two ratios.

## Main definitions

* `AddValuation.rpowAbs` (LMFDB `nf.valuation_equivalence`): the real absolute value
  `|x| = p ^ (-v(x))` of a real-valued additive valuation `v`.

## Main theorems

* `AddValuation.isEquiv_iff_le_iff_le` (LMFDB `nf.valuation_equivalence`): Mathlib's equivalence,
  defined through the reversed order of `Multiplicative (WithTop ℝ)ᵒᵈ`, is the knowl's second form
  `v₁(r) ≤ v₁(s) ↔ v₂(r) ≤ v₂(s)`.
* `AddValuation.isEquiv_iff_exists_eq_mul` (LMFDB `nf.valuation_equivalence`): `v₁` and `v₂` are
  equivalent exactly when `v₁ = c v₂` for a real `c > 0`.
* `AddValuation.exists_rpowAbs_eq_rpow_iff_isEquiv` (LMFDB `nf.valuation_equivalence`): for
  `p > 1`, `|x|_1 = |x|_2 ^ c` for a real `c > 0` and all `x` exactly when `v₁` and `v₂` are
  equivalent.
-/

namespace AddValuation

variable {R : Type*} [Ring R] {v₁ v₂ : AddValuation R (WithTop ℝ)} {r a : R} {p c x₁ y₁ x₂ y₂ : ℝ}

/-- The **real absolute value** `|x| = p ^ (-v(x))` (LMFDB `nf.valuation_equivalence`) attached to
an additive valuation `v` of a ring with values in `ℝ ∪ {∞}` and a real number `p`, with `|x| = 0`
when `v(x) = ∞`. -/
noncomputable def rpowAbs (v : AddValuation R (WithTop ℝ)) (p : ℝ) (x : R) : ℝ :=
  ((v x).map fun t ↦ p ^ (-t)).untopD 0

/-- **Mathlib's equivalence of additive valuations is the knowl's second form** (LMFDB
`nf.valuation_equivalence`): `v₁` and `v₂` are equivalent exactly when `v₁(r) ≤ v₁(s)` if and only
if `v₂(r) ≤ v₂(s)`, for all `r, s`. Mathlib defines `AddValuation.IsEquiv` through the reversed
order of `Multiplicative (WithTop ℝ)ᵒᵈ`. -/
lemma isEquiv_iff_le_iff_le : v₁.IsEquiv v₂ ↔ ∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s :=
  forall_comm

lemma map_pow_mul_pow (v : AddValuation R (WithTop ℝ)) (hr : v r = x₁) (ha : v a = y₁) (m k : ℕ) :
    v (r ^ m * a ^ k) = ↑(m * x₁ + k * y₁) := by
  rw [v.map_mul, v.map_pow, v.map_pow, hr, ha, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
    ← WithTop.coe_add, nsmul_eq_mul, nsmul_eq_mul]

private lemma mul_eq_mul_of_pos (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (h : ∀ m k m' k' : ℕ, m * x₁ +
    k * y₁ ≤ m' * x₁ + k' * y₁ ↔ m * x₂ + k * y₂ ≤ m' * x₂ + k' * y₂) : x₁ * y₂ = x₂ * y₁ := by
  have hA (M : ℕ) (N : ℤ) : M * x₁ ≤ N * y₁ ↔ M * x₂ ≤ N * y₂ := by
    have hN : (N.toNat : ℝ) - (-N).toNat = N := mod_cast Int.toNat_sub_toNat_neg N
    have e (x y : ℝ) : M * x + (-N).toNat * y ≤ (0 : ℕ) * x + N.toNat * y ↔ M * x ≤ N * y := by
      rw [← hN, sub_mul, Nat.cast_zero, zero_mul, zero_add]
      constructor <;> intro <;> linarith
    rw [← e, ← e]
    exact h M (-N).toNat 0 N.toNat
  have hq (q : ℚ) : (q : ℝ) < x₁ / y₁ ↔ (q : ℝ) < x₂ / y₂ := by
    have e (x y : ℝ) (hy : 0 < y) : (q : ℝ) < x / y ↔ ¬q.den * x ≤ q.num * y := by
      rw [not_le, lt_div_iff₀ hy, Rat.cast_def, div_mul_eq_mul_div,
        div_lt_iff₀ (by exact_mod_cast q.den_pos), mul_comm x]
    rw [e x₁ y₁ hy₁, e x₂ y₂ hy₂, hA]
  rw [← div_eq_div_iff hy₁.ne' hy₂.ne']
  exact eq_of_forall_rat_lt_iff_lt hq

private lemma mul_eq_mul_of_forall_le_iff (h : ∀ m k m' k' : ℕ, m * x₁ + k * y₁ ≤ m' * x₁ +
    k' * y₁ ↔ m * x₂ + k * y₂ ≤ m' * x₂ + k' * y₂) : x₁ * y₂ = x₂ * y₁ := by
  have h₀ : 0 ≤ y₁ ↔ 0 ≤ y₂ := by
    simpa using h 0 0 0 1
  have h₁ : y₁ ≤ 0 ↔ y₂ ≤ 0 := by
    simpa using h 0 1 0 0
  rcases lt_trichotomy y₁ 0 with hy₁ | rfl | hy₁
  · have hneg : x₁ * -y₂ = x₂ * -y₁ := by
      refine mul_eq_mul_of_pos (neg_pos.2 hy₁) (neg_pos.2 <| not_le.1 <| h₀.not.1 hy₁.not_ge)
        fun m k m' k' ↦ ?_
      have e (x y : ℝ) : m * x + k * -y ≤ m' * x + k' * -y ↔ m * x + k' * y ≤ m' * x + k * y := by
        constructor <;> intro <;> linarith
      rw [e, e]
      exact h m k' m' k
    linarith
  · simp [le_antisymm (h₁.1 le_rfl) (h₀.1 le_rfl)]
  · exact mul_eq_mul_of_pos hy₁ (not_le.1 <| h₁.not.1 hy₁.not_ge) h

lemma IsEquiv.mul_eq_mul (h : v₁.IsEquiv v₂) (hr₁ : v₁ r = x₁) (ha₁ : v₁ a = y₁) (hr₂ : v₂ r = x₂)
    (ha₂ : v₂ a = y₂) : x₁ * y₂ = x₂ * y₁ :=
  mul_eq_mul_of_forall_le_iff fun m k m' k' ↦ by
    have hle : v₁ (r ^ m * a ^ k) ≤ v₁ (r ^ m' * a ^ k') ↔
        v₂ (r ^ m * a ^ k) ≤ v₂ (r ^ m' * a ^ k') :=
      isEquiv_iff_le_iff_le.1 h (r ^ m * a ^ k) (r ^ m' * a ^ k')
    rwa [v₁.map_pow_mul_pow hr₁ ha₁, v₁.map_pow_mul_pow hr₁ ha₁, v₂.map_pow_mul_pow hr₂ ha₂,
      v₂.map_pow_mul_pow hr₂ ha₂, WithTop.coe_le_coe, WithTop.coe_le_coe] at hle

/-- **Equivalent real-valued valuations are proportional** (LMFDB `nf.valuation_equivalence`): two
additive valuations `v₁, v₂` of a ring with values in `ℝ ∪ {∞}` induce the same preorder exactly
when `v₁ = c v₂` for a real `c > 0`. -/
lemma isEquiv_iff_exists_eq_mul :
    v₁.IsEquiv v₂ ↔ ∃ c : ℝ, 0 < c ∧ ∀ x, v₁ x = (v₂ x).map (c * ·) := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc, h⟩ ↦ isEquiv_iff_le_iff_le.2 fun r s ↦ ?_⟩
  · have hzero (x : R) : v₁ x = 0 ↔ v₂ x = 0 := by
      simpa using h.val_eq (s := 1)
    have htop (x : R) (hx : v₂ x = ⊤) : v₁ x = ⊤ :=
      not_ne_iff.1 fun hx' ↦ h.ne_top.1 hx' hx
    by_cases ha : ∃ a, v₂ a ≠ 0 ∧ v₂ a ≠ ⊤
    · rcases ha with ⟨a, ha₀, ha⟩
      rcases WithTop.ne_top_iff_exists.1 ha with ⟨y₂, hy₂⟩
      rcases WithTop.ne_top_iff_exists.1 (h.ne_top.2 ha) with ⟨y₁, hy₁⟩
      have hy₂₀ : y₂ ≠ 0 := by
        rintro rfl
        exact ha₀ hy₂.symm
      have hy₁₀ : y₁ ≠ 0 := by
        rintro rfl
        exact ha₀ <| (hzero a).1 hy₁.symm
      have hsign : y₁ ≤ 0 ↔ y₂ ≤ 0 := by
        simpa [← hy₁, ← hy₂] using isEquiv_iff_le_iff_le.1 h a 1
      refine ⟨y₁ / y₂, ?_, fun x ↦ ?_⟩
      · rcases hy₂₀.lt_or_gt with hy₂₀ | hy₂₀
        · exact div_pos_of_neg_of_neg (lt_of_le_of_ne (hsign.2 hy₂₀.le) hy₁₀) hy₂₀
        · exact div_pos (lt_of_le_of_ne (not_le.1 (hsign.not.2 hy₂₀.not_ge)).le hy₁₀.symm) hy₂₀
      rcases eq_or_ne (v₂ x) ⊤ with hx | hx
      · rw [htop x hx, hx, WithTop.map_top]
      rcases WithTop.ne_top_iff_exists.1 hx with ⟨x₂, hx₂⟩
      rcases WithTop.ne_top_iff_exists.1 (h.ne_top.2 hx) with ⟨x₁, hx₁⟩
      have hmul : x₁ * y₂ = x₂ * y₁ :=
        h.mul_eq_mul hx₁.symm hy₁.symm hx₂.symm hy₂.symm
      rw [← hx₁, ← hx₂, WithTop.map_coe, WithTop.coe_inj, div_mul_eq_mul_div, eq_div_iff hy₂₀]
      linarith
    · push Not at ha
      refine ⟨1, one_pos, fun x ↦ ?_⟩
      rcases eq_or_ne (v₂ x) 0 with hx | hx
      · rw [(hzero x).2 hx, hx, ← WithTop.coe_zero, WithTop.map_coe, mul_zero]
      · rw [htop x (ha x hx), ha x hx, WithTop.map_top]
  · rw [h, h]
    exact WithTop.map_le_iff _ fun {_ _} ↦ mul_le_mul_iff_right₀ hc

lemma rpowAbs_eq_rpow_iff (hp : 1 < p) (hc : 0 < c) (x : R) :
    v₁.rpowAbs p x = v₂.rpowAbs p x ^ c ↔ v₁ x = (v₂ x).map (c * ·) := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  rcases eq_or_ne (v₂ x) ⊤ with h₂ | h₂
  · rcases eq_or_ne (v₁ x) ⊤ with h₁ | h₁
    · simp [rpowAbs, h₁, h₂, Real.zero_rpow hc.ne']
    · rcases WithTop.ne_top_iff_exists.1 h₁ with ⟨s, hs⟩
      simp [rpowAbs, ← hs, h₂, Real.zero_rpow hc.ne', (Real.rpow_pos_of_pos hp₀ _).ne']
  · rcases WithTop.ne_top_iff_exists.1 h₂ with ⟨t, ht⟩
    rcases eq_or_ne (v₁ x) ⊤ with h₁ | h₁
    · rw [rpowAbs, rpowAbs, h₁, ← ht, WithTop.map_top, WithTop.map_coe, WithTop.map_coe,
        WithTop.untopD_top, WithTop.untopD_coe]
      exact iff_of_false (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hp₀ _) _).ne
        WithTop.top_ne_coe
    · rcases WithTop.ne_top_iff_exists.1 h₁ with ⟨s, hs⟩
      rw [rpowAbs, rpowAbs, ← hs, ← ht, WithTop.map_coe, WithTop.map_coe, WithTop.map_coe,
        WithTop.untopD_coe, WithTop.untopD_coe, WithTop.coe_inj, ← Real.rpow_mul hp₀.le,
        Real.rpow_right_inj hp₀ hp.ne']
      constructor <;> intro <;> linarith

/-- **Two notions of equivalence for valuations** (LMFDB `nf.valuation_equivalence`): for additive
valuations `v₁, v₂` of a ring with values in `ℝ ∪ {∞}` and a real `p > 1`, with
`|x|_i = p ^ (-v_i(x))`, there is a real `c > 0` with `|x|_1 = |x|_2 ^ c` for all `x` exactly when
`v₁` and `v₂` are equivalent, that is (`AddValuation.isEquiv_iff_le_iff_le`) when
`v₁(r) ≤ v₁(s) ↔ v₂(r) ≤ v₂(s)` for all `r, s`. -/
lemma exists_rpowAbs_eq_rpow_iff_isEquiv (hp : 1 < p) :
    (∃ c : ℝ, 0 < c ∧ ∀ x, v₁.rpowAbs p x = v₂.rpowAbs p x ^ c) ↔ v₁.IsEquiv v₂ := by
  rw [isEquiv_iff_exists_eq_mul]
  exact exists_congr fun c ↦ and_congr_right fun hc ↦ forall_congr' (rpowAbs_eq_rpow_iff hp hc)

end AddValuation
