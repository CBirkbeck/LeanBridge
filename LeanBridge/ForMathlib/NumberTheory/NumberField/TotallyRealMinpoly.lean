import LeanBridge.ForMathlib.NumberTheory.NumberField.EmbeddingGenerator
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Totally real number fields and the roots of a defining polynomial

Mathlib's `NumberField.IsTotallyReal K` says that every infinite place of `K` is real. The LMFDB
(`nf.totally_real`) writes `K = ℚ(α)`, which is always possible by the primitive element theorem
(`Field.exists_primitive_element`), with `α` of minimal polynomial `f`, monic and irreducible over
`ℚ`, and calls `K` totally real when all the complex roots of `f` are real, or equivalently when
every embedding `K → ℂ` has image in `ℝ`. This file proves that both conditions are Mathlib's; in
particular the first one does not depend on the choice of `α`.

## Main results

* `NumberField.isTotallyReal_iff_forall_range_subset` (LMFDB `nf.totally_real`): `K` is totally
  real exactly when every embedding `K → ℂ` has image in `ℝ`.
* `NumberField.isTotallyReal_iff_rootSet_minpoly_subset` (LMFDB `nf.totally_real`): for
  `K = ℚ(α)`, `K` is totally real exactly when all the complex roots of the minimal polynomial of
  `α` are real.
-/

open scoped IntermediateField

namespace NumberField

variable {K : Type*} [Field K] {α : K}

lemma isTotallyReal_iff_forall_isReal :
    IsTotallyReal K ↔ ∀ φ : K →+* ℂ, ComplexEmbedding.IsReal φ :=
  ⟨fun h ↦ h.complexEmbedding_isReal, fun h ↦ ⟨fun _ ↦ InfinitePlace.isReal_iff.mpr <| h _⟩⟩

/-- **A number field is totally real exactly when all its embeddings have real image**
(LMFDB `nf.totally_real`). -/
lemma isTotallyReal_iff_forall_range_subset :
    IsTotallyReal K ↔ ∀ φ : K →+* ℂ, Set.range φ ⊆ Set.range ((↑) : ℝ → ℂ) := by
  simp_rw [isTotallyReal_iff_forall_isReal, ComplexEmbedding.isReal_iff_range_subset]

variable [NumberField K]

/-- **A number field `K = ℚ(α)` is totally real exactly when all the complex roots of the minimal
polynomial of `α` are real** (LMFDB `nf.totally_real`). -/
lemma isTotallyReal_iff_rootSet_minpoly_subset (hα : ℚ⟮α⟯ = ⊤) :
    IsTotallyReal K ↔ (minpoly ℚ α).rootSet ℂ ⊆ Set.range ((↑) : ℝ → ℂ) := by
  rw [isTotallyReal_iff_forall_isReal, ← Embeddings.range_eval_eq_rootSet_minpoly,
    Set.range_subset_iff]
  exact forall_congr' fun _ ↦ ComplexEmbedding.isReal_iff_apply_mem_range hα

end NumberField
