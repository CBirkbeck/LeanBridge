import Mathlib.Data.Finsupp.Weight

/-!
# Exponent vectors of degree at most two

An exponent vector `d : ι →₀ ℕ` of degree at most `2` is `0`, a unit vector `single i 1` or a sum
`single i 1 + single j 1` of two of them, and the monomials `∏ₖ yₖ ^ dₖ` of the last two are `yᵢ`
and `yᵢ yⱼ`. So a polynomial of degree at most `2` is a combination of `1`, the `yᵢ` and the
products `yᵢ yⱼ`.
-/

namespace Finsupp

variable {ι R : Type*} [CommMonoid R] (y : ι → R) (i j : ι)

lemma eq_zero_or_exists_eq_single_or_exists_eq_add_single {d : ι →₀ ℕ} (hd : d.degree ≤ 2) :
    d = 0 ∨ (∃ i, d = single i 1) ∨ ∃ i j, d = single i 1 + single j 1 := by
  classical
  rcases eq_or_ne d 0 with h0 | h0
  · exact Or.inl h0
  rcases support_nonempty_iff.mpr h0 with ⟨i, hi⟩
  have hd' : d = (d - single i 1) + single i 1 :=
    (tsub_add_cancel_of_le (single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr
      (mem_support_iff.mp hi)))).symm
  have hdeg : (d - single i 1).degree ≤ 1 := by
    have h : degree d = degree (d - single i 1 + single i 1) := congrArg degree hd'
    rw [map_add, degree_single] at h
    omega
  rcases eq_or_ne (d - single i 1) 0 with h1 | h1
  · exact Or.inr (Or.inl ⟨i, by rw [hd', h1, zero_add]⟩)
  rcases support_nonempty_iff.mpr h1 with ⟨j, hj⟩
  have hd'' : d - single i 1 = (d - single i 1 - single j 1) + single j 1 :=
    (tsub_add_cancel_of_le (single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr
      (mem_support_iff.mp hj)))).symm
  have h2 : d - single i 1 - single j 1 = 0 := by
    rw [← degree_eq_zero_iff]
    have h : degree (d - single i 1) = degree (d - single i 1 - single j 1 + single j 1) :=
      congrArg degree hd''
    rw [map_add, degree_single] at h
    omega
  exact Or.inr (Or.inr ⟨j, i, by rw [hd', hd'', h2, zero_add]⟩)

lemma prod_single_one_pow : ((single i 1).prod fun k e ↦ y k ^ e) = y i := by
  rw [prod_single_index (h := fun k e ↦ y k ^ e) (pow_zero (y i)), pow_one]

lemma prod_single_one_add_single_one_pow :
    ((single i 1 + single j 1).prod fun k e ↦ y k ^ e) = y i * y j := by
  rw [prod_add_index' (h := fun k e ↦ y k ^ e) (fun k ↦ pow_zero (y k))
    (fun k _ _ ↦ pow_add (y k) _ _), prod_single_one_pow, prod_single_one_pow]

end Finsupp
