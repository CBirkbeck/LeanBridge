import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Complex embeddings of a number field and a generator

An embedding of a number field `K` (LMFDB `nf.embedding`) is a ring homomorphism `K →+* ℂ`; there
are `[K : ℚ]` of them (`NumberField.Embeddings.card`). Mathlib calls `φ` real
(`NumberField.ComplexEmbedding.IsReal`) when it equals its complex conjugate, which this file shows
is the LMFDB's condition that the image of `φ` lies in `ℝ`. For a generator `a` of `K`, with
`K = ℚ(a)`, an embedding `φ` is determined by `φ a`, which runs through the complex roots of the
minimal polynomial of `a`, and `φ` is real exactly when `φ a` is real.

## Main definitions

* `NumberField.ComplexEmbedding.equivRootSet` (LMFDB `nf.embedding`): for `K = ℚ(a)`, the bijection
  `φ ↦ φ a` between the embeddings of `K` and the complex roots of the minimal polynomial of `a`.

## Main results

* `NumberField.ComplexEmbedding.isReal_iff_range_subset` (LMFDB `nf.embedding`): an embedding is
  real exactly when its image lies in `ℝ`.
* `NumberField.ComplexEmbedding.ne_and_mk_eq_iff_eq_conjugate` (LMFDB `nf.embedding`): complex
  embeddings come in conjugate pairs, the embeddings of a complex place.
* `NumberField.ComplexEmbedding.ext_of_adjoin_eq_top`: for `K = ℚ(a)`, two embeddings that agree
  at `a` are equal.
* `NumberField.ComplexEmbedding.isReal_iff_apply_mem_range` (LMFDB `nf.embedding`): for
  `K = ℚ(a)`, an embedding `φ` is real exactly when `φ a` is real.
-/

open scoped IntermediateField

namespace NumberField.ComplexEmbedding

variable {K : Type*} [Field K] {φ ψ : K →+* ℂ}

/-- **An embedding is real exactly when its image lies in `ℝ`** (LMFDB `nf.embedding`). -/
lemma isReal_iff_range_subset : IsReal φ ↔ Set.range φ ⊆ Set.range ((↑) : ℝ → ℂ) := by
  rw [isReal_iff, Set.range_subset_iff, RingHom.ext_iff]
  refine forall_congr' fun x ↦ ?_
  rw [conjugate_coe_eq, Complex.conj_eq_iff_real]
  exact exists_congr fun _ ↦ eq_comm

/-- **Complex embeddings come in conjugate pairs** (LMFDB `nf.embedding`): for a complex embedding
`φ`, the embeddings other than `φ` that induce the same place are exactly its complex conjugate,
which is again complex (`NumberField.ComplexEmbedding.isReal_conjugate_iff`). -/
lemma ne_and_mk_eq_iff_eq_conjugate (h : ¬IsReal φ) :
    ψ ≠ φ ∧ InfinitePlace.mk ψ = InfinitePlace.mk φ ↔ ψ = conjugate φ := by
  refine ⟨fun ⟨hne, hmk⟩ ↦ ?_, ?_⟩
  · rcases InfinitePlace.mk_eq_iff.mp hmk.symm with h' | h'
    · exact absurd h'.symm hne
    · exact h'.symm
  · rintro rfl
    exact ⟨fun h' ↦ h (isReal_iff.mpr h'), InfinitePlace.mk_conjugate_eq φ⟩

variable [NumberField K] {a : K}

/-- **An embedding of `K = ℚ(a)` is determined by its value at `a`.** -/
lemma ext_of_adjoin_eq_top (ha : ℚ⟮a⟯ = ⊤) (h : φ a = ψ a) : φ = ψ := by
  have hφψ : φ.toRatAlgHom = ψ.toRatAlgHom := AlgHom.ext_of_adjoin_eq_top
    ((IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic <| .of_finite ℚ a).mp ha)
    (Set.eqOn_singleton.mpr h)
  exact RingHom.ext fun x ↦ AlgHom.congr_fun hφψ x

variable (a) in
/-- For a generator `a` of `K`, with `K = ℚ(a)`, the bijection `φ ↦ φ a` between the embeddings of
`K` and the complex roots of the minimal polynomial `f` of `a` (LMFDB `nf.embedding`): each
embedding is determined by `z = φ a`, which is a complex root of `f`, and every root arises. -/
noncomputable def equivRootSet (ha : ℚ⟮a⟯ = ⊤) : (K →+* ℂ) ≃ (minpoly ℚ a).rootSet ℂ :=
  .ofBijective (fun φ ↦ ⟨φ a, Embeddings.range_eval_eq_rootSet_minpoly K ℂ a ▸ ⟨φ, rfl⟩⟩)
    ⟨fun _ _ h ↦ ext_of_adjoin_eq_top ha congr($h.1), fun ⟨z, hz⟩ ↦ by
      rcases (Embeddings.range_eval_eq_rootSet_minpoly K ℂ a).symm ▸ hz with ⟨φ, rfl⟩
      exact ⟨φ, rfl⟩⟩

@[simp]
lemma coe_equivRootSet_apply (ha : ℚ⟮a⟯ = ⊤) (φ : K →+* ℂ) : (equivRootSet a ha φ : ℂ) = φ a :=
  rfl

/-- **An embedding of `K = ℚ(a)` is real exactly when its value at `a` is real**
(LMFDB `nf.embedding`): `φ` is real if `z = φ a ∈ ℝ` and complex if `z ∉ ℝ`. -/
lemma isReal_iff_apply_mem_range (ha : ℚ⟮a⟯ = ⊤) : IsReal φ ↔ φ a ∈ Set.range ((↑) : ℝ → ℂ) := by
  refine ⟨fun h ↦ isReal_iff_range_subset.mp h ⟨a, rfl⟩, fun ⟨r, hr⟩ ↦ isReal_iff.mpr ?_⟩
  refine ext_of_adjoin_eq_top ha ?_
  rw [conjugate_coe_eq, ← hr, Complex.conj_ofReal]

end NumberField.ComplexEmbedding
