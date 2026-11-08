import LeanBridge.ForMathlib.NumberTheory.NumberField.Ostrowski

/-!
# Archimedean and nonarchimedean absolute values

An absolute value of a field `k` (LMFDB `nf.absolute_value`) is Mathlib's `AbsoluteValue k ℝ`: a
nonnegative multiplicative function that vanishes exactly at `0` and satisfies the triangle
inequality. It is nonarchimedean when it satisfies the ultrametric inequality (Mathlib's
`IsNonarchimedean`) and archimedean otherwise. The trivial absolute value is Mathlib's
`AbsoluteValue.trivial`, which is `1` at every nonzero element. Two absolute values are equivalent
when one is a positive power of the other; Mathlib's `AbsoluteValue.IsEquiv` is this relation.

This file proves the facts that the knowl states. In characteristic `p`, every natural number `n`
satisfies `(n : k) ^ p = n`, so `v n ≤ 1`, and `v` is nonarchimedean by
`AbsoluteValue.isNonarchimedean_of_natCast_le_one`: archimedean absolute values occur only in
characteristic zero.

## Main results

* `AbsoluteValue.isNonarchimedean_of_charP`: every absolute value of a field of characteristic
  `p > 0` is nonarchimedean.
* `AbsoluteValue.charZero_of_not_isNonarchimedean`: a field with an archimedean absolute value has
  characteristic zero.
* `AbsoluteValue.isNonarchimedean_trivial`: the trivial absolute value is nonarchimedean.
* `AbsoluteValue.isEquiv_iff_exists_eq_rpow`: two absolute values `|·|₁`, `|·|₂` are equivalent if
  and only if `|x|₁ = |x|₂ ^ c` for some `c > 0` and every `x`.
* `AbsoluteValue.equivalence_exists_eq_rpow`: this relation is an equivalence relation.
-/

namespace AbsoluteValue

variable {k : Type*} [Field k] {v : AbsoluteValue k ℝ}

variable (v) in
/-- Every absolute value of a field of characteristic `p > 0` is nonarchimedean (LMFDB
`nf.absolute_value`). -/
lemma isNonarchimedean_of_charP {p : ℕ} [CharP k p] (hp : p.Prime) : IsNonarchimedean v :=
  isNonarchimedean_of_natCast_le_one fun n ↦ by
    have : Fact p.Prime := ⟨hp⟩
    have h : v n ^ p = v n := by rw [← map_pow, ← frobenius_def, map_natCast]
    by_contra! h1
    exact (lt_self_pow₀ h1 hp.one_lt).ne' h

/-- Archimedean absolute values occur only in characteristic zero (LMFDB `nf.absolute_value`): a
field with an absolute value that is not nonarchimedean has characteristic zero. -/
lemma charZero_of_not_isNonarchimedean (h : ¬IsNonarchimedean v) : CharZero k :=
  (CharP.ringChar_zero_iff_CharZero k).mp <| (CharP.char_is_prime_or_zero k _).resolve_left fun hp ↦
    h <| v.isNonarchimedean_of_charP hp

/-- The trivial absolute value, `1` at every nonzero element, is nonarchimedean (LMFDB
`nf.absolute_value`). -/
lemma isNonarchimedean_trivial {R S : Type*} [Semiring R] [DecidablePred fun x : R ↦ x = 0]
    [NoZeroDivisors R] [Semiring S] [LinearOrder S] [IsStrictOrderedRing S] :
    IsNonarchimedean (AbsoluteValue.trivial : AbsoluteValue R S) := by
  intro x y
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne (x + y) 0 with hxy | hxy <;> simp [hx, hxy]

/-- Two absolute values `|·|₁`, `|·|₂` of a field are equivalent if and only if there is a positive
real number `c` with `|x|₁ = |x|₂ ^ c` for every `x` (LMFDB `nf.absolute_value`), the form of
`AbsoluteValue.isEquiv_iff_exists_rpow_eq` that the knowl uses. -/
lemma isEquiv_iff_exists_eq_rpow {w : AbsoluteValue k ℝ} :
    v.IsEquiv w ↔ ∃ c : ℝ, 0 < c ∧ ∀ x, v x = w x ^ c := by
  rw [← (⟨.symm, .symm⟩ : w.IsEquiv v ↔ v.IsEquiv w), isEquiv_iff_exists_rpow_eq]
  simp_rw [funext_iff, eq_comm]

/-- The relation `|x|₁ = |x|₂ ^ c` for some `c > 0` and every `x` is an equivalence relation on the
absolute values of a field (LMFDB `nf.absolute_value`). -/
lemma equivalence_exists_eq_rpow :
    Equivalence fun v w : AbsoluteValue k ℝ ↦ ∃ c : ℝ, 0 < c ∧ ∀ x, v x = w x ^ c := by
  simp_rw [← isEquiv_iff_exists_eq_rpow]
  exact (inferInstance : Setoid (AbsoluteValue k ℝ)).iseqv

end AbsoluteValue
