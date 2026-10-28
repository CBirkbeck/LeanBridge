import Mathlib.FieldTheory.Galois.Basic
import LeanBridge.ForMathlib.NumberTheory.NumberField.Sibling

/-!
# Siblings of a transitive permutation group

A finite group `G` may act faithfully and transitively on several sets. Such an action is the
action on the cosets `G ⧸ H` of a subgroup `H` with trivial normal core, and it is determined up to
equivalence by the conjugacy class of `H`. When `G` is the Galois group of a finite Galois extension
`L / K`, the subgroup `H` corresponds to the field `L ^ H`, of degree `[G : H]` over `K`, whose
Galois closure is `L` exactly when the normal core of `H` is trivial. The other faithful transitive
actions of `G` then correspond to the sibling fields of `L ^ H`.

## Main definitions

* `Subgroup.IsSibling` (LMFDB `gg.other_representations`).

## Main results

* `IntermediateField.nonempty_algEquiv_fixedField_iff`: the fixed fields of two subgroups of
  `Gal(L/K)` are isomorphic exactly when the subgroups are conjugate.
* `IntermediateField.normalClosure_fixedField`: the normal closure of the fixed field of `H` is the
  fixed field of the normal core of `H`.
* `IntermediateField.isSibling_fixedField_iff`: the fixed fields of `H` and `H'` are sibling fields
  exactly when `H` and `H'` are not conjugate and have the same normal core.
* `IntermediateField.isSibling_fixedField_iff_isSibling`: if the normal core of `H` is trivial, the
  fixed fields of `H` and `H'` are sibling fields exactly when `H'` is a sibling of `H`.
-/

open Subgroup
open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

/-- Two subgroups `H` and `H'` of a group `G` are **siblings** (LMFDB `gg.other_representations`)
if `G` acts faithfully on `G ⧸ H` and on `G ⧸ H'`, that is, `H` and `H'` have trivial normal
cores, and the two actions are not equivalent, that is, `H` and `H'` are not conjugate.

For a transitive permutation group `G ≤ Sym(n)` with point stabilizer `H`, the siblings of `H` are
the other faithful transitive permutation representations of the abstract group `G`; for the
Galois group of a finite Galois extension they correspond to the sibling fields
(`IntermediateField.isSibling_fixedField_iff_isSibling`). The LMFDB names each of them by the label
`nTt` of its image in the symmetric group, of degree `n = [G : H']`, and writes `nTt x k` when `k`
pairwise non-conjugate siblings have the same label; these labels, a database classification of
transitive groups, are not formalised here. -/
def IsSibling (H H' : Subgroup G) : Prop :=
  H.normalCore = ⊥ ∧ H'.normalCore = ⊥ ∧ ∀ g : G, MulAut.conj g • H ≠ H'

end Subgroup

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (H H' : Subgroup Gal(L/K))

/-- **Two subfields of a Galois extension are isomorphic if and only if their fixing subgroups are
conjugate.** -/
lemma nonempty_algEquiv_fixedField_iff :
    Nonempty (fixedField H ≃ₐ[K] fixedField H') ↔ ∃ σ : Gal(L/K), MulAut.conj σ • H = H' := by
  refine ⟨fun ⟨e⟩ ↦ ⟨e.liftNormal L, ?_⟩, fun ⟨σ, hσ⟩ ↦ ⟨(fixedField H).equivMap σ |>.trans <|
    equivOfEq ?_⟩⟩
  · have hmap : (fixedField H).map (e.liftNormal L : L →ₐ[K] L) = fixedField H' := by
      ext x
      refine ⟨?_, fun hx ↦ ⟨e.symm ⟨x, hx⟩, (e.symm ⟨x, hx⟩).2, ?_⟩⟩
      · rintro ⟨y, hy, rfl⟩
        have h : e.liftNormal L y = e ⟨y, hy⟩ := e.liftNormal_commutes L ⟨y, hy⟩
        simp [h]
      · simpa using e.liftNormal_commutes L (e.symm ⟨x, hx⟩)
    have h : ((fixedField H).map (e.liftNormal L : L →ₐ[K] L)).fixingSubgroup =
        MulAut.conj (e.liftNormal L) • (fixedField H).fixingSubgroup :=
      IsGalois.map_fixingSubgroup (fixedField H) (e.liftNormal L)
    rwa [hmap, fixingSubgroup_fixedField, fixingSubgroup_fixedField, eq_comm] at h
  · rw [← IsGalois.fixedField_fixingSubgroup ((fixedField H).map _), IsGalois.map_fixingSubgroup,
      fixingSubgroup_fixedField, hσ]

/-- **The normal closure of the fixed field of a subgroup is the fixed field of its normal core.**
-/
lemma normalClosure_fixedField : normalClosure K (fixedField H) L = fixedField H.normalCore := by
  refine le_antisymm (normalClosure_le_iff_of_normal.mpr <| fixedField_le H.normalCore_le) ?_
  rw [← IsGalois.fixedField_fixingSubgroup (normalClosure K (fixedField H) L)]
  refine fixedField_le <| Subgroup.normal_le_normalCore.mpr ?_
  have h : (normalClosure K (fixedField H) L).fixingSubgroup ≤ (fixedField H).fixingSubgroup :=
    fixingSubgroup_le (le_normalClosure (fixedField H))
  rwa [fixingSubgroup_fixedField] at h

lemma nonempty_algEquiv_normalClosure_fixedField_iff :
    Nonempty (normalClosure K (fixedField H) L ≃ₐ[K] normalClosure K (fixedField H') L) ↔
      H.normalCore = H'.normalCore := by
  rw [normalClosure_fixedField, normalClosure_fixedField, nonempty_algEquiv_fixedField_iff]
  refine ⟨fun ⟨σ, hσ⟩ ↦ ?_, fun h ↦ ⟨1, by rw [map_one, one_smul, h]⟩⟩
  rw [← hσ, Normal.conj_smul_eq_self]

/-- **The fixed fields of two subgroups of a Galois group are siblings if and only if the subgroups
are not conjugate and have the same normal core**, the fixing subgroup of the common Galois
closure. -/
lemma isSibling_fixedField_iff : Algebra.IsSibling K (fixedField H) (fixedField H') ↔
    (∀ σ : Gal(L/K), MulAut.conj σ • H ≠ H') ∧ H.normalCore = H'.normalCore := by
  have : Nonempty (fixedField H →ₐ[K] L) := ⟨val _⟩
  have : Nonempty (fixedField H' →ₐ[K] L) := ⟨val _⟩
  rw [Algebra.isSibling_iff (L₁ := normalClosure K (fixedField H) L)
    (L₂ := normalClosure K (fixedField H') L), ← not_nonempty_iff,
    nonempty_algEquiv_fixedField_iff, not_exists, nonempty_algEquiv_normalClosure_fixedField_iff]

/-- **For a transitive permutation group, sibling subgroups are sibling fields**: if `H` has
trivial normal core, so that `L` is the Galois closure of `L ^ H` and `Gal(L/K)` acts faithfully
on `Gal(L/K) ⧸ H`, then the fixed fields of `H` and `H'` are sibling fields exactly when `H'` is a
sibling of `H`. -/
lemma isSibling_fixedField_iff_isSibling (hH : H.normalCore = ⊥) :
    Algebra.IsSibling K (fixedField H) (fixedField H') ↔ H.IsSibling H' := by
  rw [isSibling_fixedField_iff, Subgroup.IsSibling, hH, eq_comm (a := ⊥)]
  exact ⟨fun h ↦ ⟨rfl, h.2, h.1⟩, fun h ↦ ⟨h.2.2, h.2.1⟩⟩

end IntermediateField
