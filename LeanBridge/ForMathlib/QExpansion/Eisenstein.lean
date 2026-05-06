import LeanBridge.ForMathlib.QExpansion.Trunc
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# `approxTo` base cases for `E₄` and `E₆`

We show that the precomputed lists `E4_qexpList N` and `E6_qexpList N` from `DeltaPoC` are
correct truncations of `qExpansion 1 ↑E₄` and `qExpansion 1 ↑E₆` respectively. These are the
base cases for the bridge from list-based computation to `qExpansion` of any polynomial in
`E₄` and `E₆`.
-/

namespace LeanBridge.QExpansion

open List PowerSeries EisensteinSeries ModularForm UpperHalfPlane
open scoped ArithmeticFunction.sigma

/-- `sigmaKK k m = σ k m`. -/
lemma sigmaKK_eq_sigma (k m : ℕ) : (sigmaKK k m : ℕ) = σ k m := by
  unfold sigmaKK
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [ArithmeticFunction.sigma]
  · simp [ArithmeticFunction.sigma_apply]

lemma approxTo_E4 (N : ℕ) :
    approxTo N (E4_qexpList N) (qExpansion 1 (↑(E (by norm_num : 3 ≤ 4)) : ℍ → ℂ)) := by
  intro m hm
  rw [E_qExpansion_coeff (by norm_num : 3 ≤ 4) ⟨2, rfl⟩ m]
  unfold E4_qexpList
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp only [List.getElem_map, List.getElem_range]
  by_cases h0 : m = 0
  · simp [h0]
  · rw [if_neg h0, if_neg h0]
    have hb : (bernoulli 4 : ℂ) = -1 / 30 := by
      have : bernoulli 4 = -1 / 30 := by decide +kernel
      exact_mod_cast this
    rw [show ((4 : ℕ) - 1 : ℕ) = 3 from rfl, ← sigmaKK_eq_sigma]
    push_cast
    rw [hb]
    ring

lemma approxTo_E6 (N : ℕ) :
    approxTo N (E6_qexpList N) (qExpansion 1 (↑(E (by norm_num : 3 ≤ 6)) : ℍ → ℂ)) := by
  intro m hm
  rw [E_qExpansion_coeff (by norm_num : 3 ≤ 6) ⟨3, rfl⟩ m]
  unfold E6_qexpList
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp only [List.getElem_map, List.getElem_range]
  by_cases h0 : m = 0
  · simp [h0]
  · rw [if_neg h0, if_neg h0]
    have hb : (bernoulli 6 : ℂ) = 1 / 42 := by
      have h : bernoulli 6 = (1 / 42 : ℚ) := by decide +kernel
      rw [h]; push_cast; rfl
    rw [show ((6 : ℕ) - 1 : ℕ) = 5 from rfl, ← sigmaKK_eq_sigma]
    push_cast
    rw [hb]
    ring

end LeanBridge.QExpansion
