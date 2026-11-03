import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.AmbientDensity
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.AmbientHighestWeight
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Weyl's monomial of an irreducible character of `O(d)`

Every irreducible character of the ambient group `O(d)` of a Sato–Tate group of even weight occurs
in a monomial in the elementary symmetric functions of the eigenvalues, and so it has a Weyl's
monomial (`SatoTateGroup.HasOrthogonalMonomial`), a unique one. So in even weight the order of the
rows and columns of the moment matrix is a total preorder. It is a linear order exactly when Weyl's
monomial is injective on the irreducible characters of `O(d)`, which is
`SatoTateGroup.injective_orthogonalMonomial`, the monomial being the partition labelling the
character in Weyl's classification.

## Main definitions

* `SatoTateGroup.orthogonalMonomial`: Weyl's monomial of an irreducible character of `O(d)`.

## Main results

* `SatoTateGroup.existsUnique_hasOrthogonalMonomial`: an irreducible character of `O(d)` has a
  unique Weyl's monomial.
* `SatoTateGroup.isBeforeInMomentMatrix_iff_of_even`: in even weight, the order of the rows and
  columns of the moment matrix is the order of Weyl's monomials.
* `SatoTateGroup.antisymm_isBeforeInMomentMatrix_iff`: it is antisymmetric if and only if Weyl's
  monomial is injective.
-/

open Filter Matrix MeasureTheory TauCeti

open scoped ComplexConjugate

namespace SatoTateGroup

section Monomial

variable {w d : ℕ}

lemma esymm_one_roots_charpoly (a : ambientGroup w d) :
    (a : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm 1 =
      (a : Matrix (Fin d) (Fin d) ℂ).trace := by
  rw [trace_eq_sum_roots_charpoly]
  simp [Multiset.esymm, Multiset.powersetCard_one]

lemma exists_ambientMonomial_eq_trace_pow (hd : 0 < d) (n : ℕ) : ∃ c : Fin d → ℕ,
    ∀ a : ambientGroup w d, ambientMonomial c a = (a : Matrix (Fin d) (Fin d) ℂ).trace ^ n := by
  refine ⟨Pi.single ⟨0, hd⟩ n, fun a ↦ ?_⟩
  rw [ambientMonomial, Finset.prod_eq_single (⟨0, hd⟩ : Fin d)]
  · rw [Pi.single_eq_same]
    exact congrArg (· ^ n) (esymm_one_roots_charpoly a)
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, pow_zero]
  · simp

variable (χ : IrrepClass ℂ (ambientGroup w d))

lemma exists_occursInMonomial (hF : IsUnit (ambientForm w d)) : ∃ c, OccursInMonomial χ c := by
  rcases exists_integral_trace_pow_mul_conj_ne_zero hF χ with ⟨n, hn⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hn₀ : n = 0 := by
      by_contra hne
      refine hn (integral_eq_zero_of_ae (Eventually.of_forall fun a ↦ ?_))
      have h₁ : (a : Matrix (Fin 0) (Fin 0) ℂ).trace = 0 := Finset.sum_of_isEmpty _
      simp only [h₁, zero_pow hne, zero_mul, Pi.zero_apply]
    subst hn₀
    refine ⟨Fin.elim0, fun h₀ ↦ hn ?_⟩
    simpa [ambientMonomial] using h₀
  · rcases exists_ambientMonomial_eq_trace_pow (w := w) hd n with ⟨c, hc⟩
    refine ⟨c, fun h₀ ↦ hn ?_⟩
    simpa only [hc] using h₀

lemma exists_hasOrthogonalMonomial (hF : IsUnit (ambientForm w d)) :
    ∃ c, HasOrthogonalMonomial χ c := by
  rcases exists_occursInMonomial χ hF with ⟨c₀, hc₀⟩
  rcases wellFounded_lt.has_min {x : Lex (Fin d → ℕ) | ∃ c, OccursInMonomial χ c ∧
    toLex (highestWeight c) = x} ⟨_, c₀, hc₀, rfl⟩ with ⟨_, ⟨c, hc, rfl⟩, hmin⟩
  exact ⟨c, hc, fun c' hc' ↦ not_lt.mp (hmin _ ⟨c', hc', rfl⟩)⟩

/-- **An irreducible character of `O(d)` has a unique Weyl's monomial.** -/
lemma existsUnique_hasOrthogonalMonomial (hw : Even w) : ∃! c, HasOrthogonalMonomial χ c := by
  have hF : IsUnit (ambientForm w d) := by
    rw [ambientForm_of_even hw]
    exact isUnit_one
  rcases exists_hasOrthogonalMonomial χ hF with ⟨c, hc⟩
  exact ⟨c, hc, fun c' hc' ↦ hc'.eq hc⟩

/-- **Weyl's monomial** of an irreducible character `χ` of `O(d)` (LMFDB `st_group.moment_matrix`):
its exponent vector, the unique `c` with `HasOrthogonalMonomial χ c`. -/
noncomputable def orthogonalMonomial (hw : Even w) : Fin d → ℕ :=
  (existsUnique_hasOrthogonalMonomial χ hw).choose

lemma hasOrthogonalMonomial_orthogonalMonomial (hw : Even w) :
    HasOrthogonalMonomial χ (orthogonalMonomial χ hw) :=
  (existsUnique_hasOrthogonalMonomial χ hw).choose_spec.1

end Monomial

variable {G : SatoTateGroup} (hG : Even G.weight)

/-- **In even weight, the order of the rows and columns of the moment matrix is the order of Weyl's
monomials.** -/
lemma isBeforeInMomentMatrix_iff_of_even (χ χ' : IrrepClass ℂ (ambientGroup G.weight G.degree)) :
    G.IsBeforeInMomentMatrix χ χ' ↔
      IsBeforeInDisplayOrder (orthogonalMonomial χ hG) (orthogonalMonomial χ' hG) :=
  ⟨fun h ↦ h.2 hG _ _ (hasOrthogonalMonomial_orthogonalMonomial χ hG)
      (hasOrthogonalMonomial_orthogonalMonomial χ' hG),
    fun h ↦ ⟨fun ho ↦ absurd hG (Nat.not_even_iff_odd.mpr ho), fun _ c c' hc hc' ↦ by
      rwa [hc.eq (hasOrthogonalMonomial_orthogonalMonomial χ hG),
        hc'.eq (hasOrthogonalMonomial_orthogonalMonomial χ' hG)]⟩⟩

lemma isBeforeInMomentMatrix_eq_invImage :
    G.IsBeforeInMomentMatrix = InvImage IsBeforeInDisplayOrder fun χ ↦ orthogonalMonomial χ hG :=
  funext₂ fun χ χ' ↦ propext (isBeforeInMomentMatrix_iff_of_even hG χ χ')

lemma isPreorder_isBeforeInMomentMatrix (hw : Even G.weight) :
    IsPreorder (IrrepClass ℂ (ambientGroup G.weight G.degree)) G.IsBeforeInMomentMatrix := by
  rw [isBeforeInMomentMatrix_eq_invImage hw]
  infer_instance

lemma total_isBeforeInMomentMatrix (hw : Even G.weight) : Std.Total G.IsBeforeInMomentMatrix := by
  rw [isBeforeInMomentMatrix_eq_invImage hw]
  infer_instance

/-- **In even weight, the order of the rows and columns of the moment matrix is antisymmetric if and
only if Weyl's monomial is injective on the irreducible characters of `O(d)`**, which holds
(`SatoTateGroup.injective_orthogonalMonomial`). -/
lemma antisymm_isBeforeInMomentMatrix_iff : Std.Antisymm G.IsBeforeInMomentMatrix ↔
    Function.Injective fun χ : IrrepClass ℂ (ambientGroup G.weight G.degree) ↦
      orthogonalMonomial χ hG := by
  refine ⟨fun h χ χ' he ↦ ?_, fun h ↦ ?_⟩
  · have h₁ (χ₁ χ₂ : IrrepClass ℂ (ambientGroup G.weight G.degree))
        (h₂ : orthogonalMonomial χ₁ hG = orthogonalMonomial χ₂ hG) :
        G.IsBeforeInMomentMatrix χ₁ χ₂ :=
      (isBeforeInMomentMatrix_iff_of_even hG χ₁ χ₂).mpr (h₂ ▸ .inr ⟨rfl, le_rfl⟩)
    exact h.antisymm χ χ' (h₁ χ χ' he) (h₁ χ' χ he.symm)
  · rw [isBeforeInMomentMatrix_eq_invImage hG]
    exact InvImage.antisymm h

end SatoTateGroup
