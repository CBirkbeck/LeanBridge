import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Galois extensions whose Galois group is the Klein four-group

Let `K / F` be a finite Galois extension whose Galois group is the Klein four-group, such as a
biquadratic extension of `ℚ`. Its nontrivial automorphisms are involutions and commute with each
other. Each quadratic subextension is the fixed field of a nontrivial automorphism, and an element
fixed by two distinct nontrivial automorphisms is fixed by all of them, so it lies in `F`; the
elements of `F` are fixed by every automorphism, for any extension `K / F`.
-/

open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {σ τ : Gal(K/F)} {x : K}

namespace IntermediateField

lemma apply_eq_self_of_mem_bot (hx : x ∈ (⊥ : IntermediateField F K)) : σ x = x := by
  rcases mem_bot.mp hx with ⟨q, rfl⟩
  exact σ.commutes q

variable [FiniteDimensional F K] [IsGalois F K] [IsKleinFour Gal(K/F)]

lemma exists_ne_one_forall_mem_iff (k : IntermediateField F K) (hk : finrank F k = 2) :
    ∃ σ : Gal(K/F), σ ≠ 1 ∧ ∀ x : K, x ∈ k ↔ σ x = x := by
  have hcard : Nat.card k.fixingSubgroup = 2 := by
    have h4 : finrank F k * finrank k K = 4 :=
      (finrank_mul_finrank F k K).trans <|
        (IsGalois.card_aut_eq_finrank F K).symm.trans IsKleinFour.card_four
    rw [IsGalois.card_fixingSubgroup_eq_finrank]
    rw [hk] at h4
    omega
  rcases (Nat.card_eq_two_iff' (1 : k.fixingSubgroup)).mp hcard with ⟨σ, hσ, hσ'⟩
  refine ⟨σ, fun h ↦ hσ (Subtype.ext h), fun x ↦
    ⟨(mem_fixingSubgroup_iff k σ.1).mp σ.2 x, fun hx ↦ ?_⟩⟩
  rw [← IsGalois.fixedField_fixingSubgroup k, mem_fixedField_iff]
  intro τ hτ
  rcases eq_or_ne (⟨τ, hτ⟩ : k.fixingSubgroup) 1 with h1 | h1
  · exact congrArg (· x) (congrArg Subtype.val h1)
  · exact (congrArg (· x) (congrArg Subtype.val (hσ' _ h1))).trans hx

lemma mem_bot_of_apply_eq_self (hσ : σ ≠ 1) (hτ : τ ≠ 1) (hστ : σ ≠ τ) (hx : σ x = x)
    (hx' : τ x = x) : x ∈ (⊥ : IntermediateField F K) := by
  refine (IsGalois.mem_bot_iff_fixed x).mpr fun ρ ↦ ?_
  by_cases h1 : ρ = 1
  · rw [h1, AlgEquiv.one_apply]
  by_cases h2 : ρ = σ
  · rw [h2, hx]
  by_cases h3 : ρ = τ
  · rw [h3, hx']
  rw [IsKleinFour.eq_mul_of_ne_all hσ hτ hστ h1 h2 h3, AlgEquiv.mul_apply, hx', hx]

end IntermediateField

namespace AlgEquiv

variable [IsKleinFour Gal(K/F)] (σ τ)

lemma apply_apply_of_isKleinFour : σ (σ x) = x := by
  rw [← mul_apply, IsKleinFour.mul_self, one_apply]

lemma apply_comm_of_isKleinFour : σ (τ x) = τ (σ x) := by
  rw [← mul_apply, mul_comm_of_exponent_two IsKleinFour.exponent_two, mul_apply]

end AlgEquiv
