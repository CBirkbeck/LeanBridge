import LeanBridge.ForMathlib.GroupTheory.Perm.MinimalDegree
import LeanBridge.ForMathlib.GroupTheory.Sibling
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Resolvents of a Galois group

Let `L / K` be a finite Galois extension with Galois group `G`, for the LMFDB the Galois closure of
a finite separable extension. Every intermediate field of `L / K` is a resolvent field, and these
fields correspond to the subgroups of `G`. The LMFDB groups them by their Galois closures: the
Galois closure of the fixed field of a subgroup `H` is the fixed field of the normal core of `H`
(`IntermediateField.normalClosure_fixedField`), so the groups correspond to the normal subgroups
`N` of `G`, that is, to the quotients `G / N`, the **resolvents** of `G` (LMFDB `gg.resolvents`).

As representative of the resolvent `G / N` the LMFDB takes a subgroup `H` of least index `m` among
the subgroups with normal core `N` (`Subgroup.IsResolventSubgroup`), which exist
(`Subgroup.exists_isResolventSubgroup`); `m` is the minimal transitive degree of `G / N` (LMFDB
`group.transitive_degree`, `Subgroup.IsResolventSubgroup.index_eq_minTransitiveDegree`). Then `G`
acts transitively on the `m` cosets of `H` with kernel `N`
(`Subgroup.IsResolventSubgroup.ker_toPermHom`), so that `G / N`, the Galois group of the fixed field
`L ^ N`, becomes a transitive subgroup of `S_m`
(`Subgroup.IsResolventSubgroup.nonempty_quotientMulEquivRange`), and the fixed field of `H` is a
stem field for `L ^ N`: a field of degree `m` over `K` whose Galois closure is `L ^ N`
(`IntermediateField.normalClosure_fixedField_of_isResolventSubgroup`,
`IntermediateField.finrank_fixedField_of_isResolventSubgroup`). Among the subgroups `H` of least
index with normal core `N` the LMFDB picks one whose permutation representation has the least
T-number, a database numbering of the transitive groups of degree `m` (LMFDB `gg.tnumber`) which is
not formalised here.

## Main definitions

* `Subgroup.IsResolventSubgroup` (LMFDB `gg.resolvents`): a subgroup of least index with a given
  normal core.

## Main results

* `Subgroup.exists_isResolventSubgroup`: every normal subgroup has resolvent subgroups.
* `Subgroup.IsResolventSubgroup.index_eq_minTransitiveDegree`: the index of a resolvent subgroup for
  a normal subgroup `N` of a finite group `G` is the minimal transitive degree of `G / N`.
* `Subgroup.IsResolventSubgroup.ker_toPermHom`: `G` acts on the cosets of a resolvent subgroup for
  `N` with kernel `N`.
* `Subgroup.IsResolventSubgroup.nonempty_quotientMulEquivRange`: the quotient `G / N` is the
  permutation group of `G` on the cosets of a resolvent subgroup for `N`.
* `IntermediateField.normalClosure_fixedField_of_isResolventSubgroup`: the fixed field of a
  resolvent subgroup for `N` has Galois closure the fixed field of `N`.
* `IntermediateField.finrank_fixedField_of_isResolventSubgroup`: its degree is the minimal
  transitive degree of `G / N`.
-/

open MulAction

namespace Subgroup

variable {G : Type*} [Group G] (N H : Subgroup G)

/-- A subgroup `H` of `G` is a **resolvent subgroup** for `N` (LMFDB `gg.resolvents`) if its normal
core is `N` and its index is least among the subgroups of `G` with normal core `N`: for a normal
subgroup `N` of a finite group `G`, `G` then acts transitively on the cosets of `H` through a
faithful action of `G / N` of least degree. The LMFDB chooses among these subgroups one whose
permutation representation has the least T-number, a database numbering. -/
def IsResolventSubgroup : Prop :=
  H.normalCore = N ∧ ∀ K : Subgroup G, K.normalCore = N → H.index ≤ K.index

variable {N H}

/-- **`G` acts on the cosets of a resolvent subgroup for `N` with kernel `N`.** -/
lemma IsResolventSubgroup.ker_toPermHom (h : N.IsResolventSubgroup H) :
    (toPermHom G (G ⧸ H)).ker = N := by
  rw [← normalCore_eq_ker, h.1]

variable [N.Normal]

/-- **The quotient `G / N` is the permutation group of `G` on the cosets of a resolvent subgroup for
`N`**, a transitive group of degree the index of the resolvent subgroup. -/
lemma IsResolventSubgroup.nonempty_quotientMulEquivRange (h : N.IsResolventSubgroup H) :
    Nonempty (G ⧸ N ≃* (toPermHom G (G ⧸ H)).range) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq h.ker_toPermHom.symm).trans <|
    QuotientGroup.quotientKerEquivRange _⟩

variable (N) in
/-- **Every normal subgroup has resolvent subgroups.** -/
lemma exists_isResolventSubgroup : ∃ H : Subgroup G, N.IsResolventSubgroup H := by
  rcases Nat.sInf_mem (s := {m | ∃ K : Subgroup G, K.normalCore = N ∧ K.index = m})
    ⟨N.index, N, N.normalCore_eq_self, rfl⟩ with ⟨H, hH, hm⟩
  exact ⟨H, hH, fun K hK ↦ hm ▸ Nat.sInf_le ⟨K, hK, rfl⟩⟩

variable [Finite G]

variable (H) in
lemma minTransitiveDegree_le_index : Group.minTransitiveDegree (G ⧸ H.normalCore) ≤ H.index := by
  let e : G ⧸ H ≃ Fin H.index := Finite.equivFin (G ⧸ H)
  let f : G ⧸ H.normalCore →* Equiv.Perm (Fin H.index) := e.permCongrHom.toMonoidHom.comp <|
    QuotientGroup.lift _ (toPermHom G (G ⧸ H)) H.normalCore_eq_ker.le
  refine Group.minTransitiveDegree_le (f := f) Nat.card_pos (e.permCongrHom.injective.comp <|
    (QuotientGroup.injective_lift_iff _ _ _).mpr H.normalCore_eq_ker) fun i j ↦ ?_
  rcases QuotientGroup.mk_surjective (e.symm i) with ⟨a, ha⟩
  rcases QuotientGroup.mk_surjective (e.symm j) with ⟨b, hb⟩
  refine ⟨(b * a⁻¹ : G), ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.lift_mk, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply, toPermHom_apply, toPerm_apply, ← ha, Quotient.smul_mk, smul_eq_mul,
    inv_mul_cancel_right, hb, e.apply_symm_apply]

lemma IsResolventSubgroup.index_le_minTransitiveDegree (h : N.IsResolventSubgroup H) :
    H.index ≤ Group.minTransitiveDegree (G ⧸ N) := by
  rcases Group.exists_injective_isTransitive_minTransitiveDegree (G ⧸ N) with ⟨f, hf, ht⟩
  let _ : MulAction G (Fin (Group.minTransitiveDegree (G ⧸ N))) :=
    compHom _ (f.comp (QuotientGroup.mk' N))
  have : IsPretransitive G (Fin (Group.minTransitiveDegree (G ⧸ N))) := by
    refine ⟨fun i j ↦ ?_⟩
    rcases ht i j with ⟨q, hq⟩
    rcases QuotientGroup.mk_surjective q with ⟨g, rfl⟩
    exact ⟨g, hq⟩
  have hx (x : G) : x ∈ N ↔ ∀ i : Fin (Group.minTransitiveDegree (G ⧸ N)), x • i = i := by
    rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff _ hf, Equiv.ext_iff]
    rfl
  let i₀ : Fin (Group.minTransitiveDegree (G ⧸ N)) := ⟨0, Group.minTransitiveDegree_pos _⟩
  refine (h.2 (stabilizer G i₀) <| Subgroup.ext fun x ↦ ⟨fun hx' ↦ (hx x).mpr fun i ↦ ?_,
    fun hx' b ↦ ?_⟩).trans_eq ?_
  · rcases exists_smul_eq G i₀ i with ⟨b, rfl⟩
    have hb : b⁻¹ * x * b ∈ stabilizer G i₀ := by
      simpa using hx' b⁻¹
    rwa [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff] at hb
  · rw [mem_stabilizer_iff, mul_smul, mul_smul, (hx x).mp hx', smul_inv_smul]
  · rw [index_stabilizer_of_transitive, Nat.card_fin]

/-- **The index of a resolvent subgroup for `N` is the minimal transitive degree of `G ⧸ N`**
(LMFDB `group.transitive_degree`): the least index of a subgroup with normal core `N` is the least
degree of a faithful transitive permutation representation of `G ⧸ N`. -/
lemma IsResolventSubgroup.index_eq_minTransitiveDegree (h : N.IsResolventSubgroup H) :
    H.index = Group.minTransitiveDegree (G ⧸ N) :=
  h.index_le_minTransitiveDegree.antisymm <| h.1 ▸ minTransitiveDegree_le_index H

end Subgroup

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {N H : Subgroup Gal(L/K)}

/-- **The fixed field of a resolvent subgroup for `N` is a stem field for the fixed field of `N`**:
its Galois closure is the fixed field of `N`. -/
lemma normalClosure_fixedField_of_isResolventSubgroup (h : N.IsResolventSubgroup H) :
    normalClosure K (fixedField H) L = fixedField N := by
  rw [normalClosure_fixedField, h.1]

variable [N.Normal] in
/-- **The degree of the fixed field of a resolvent subgroup for `N` is the minimal transitive degree
of `Gal(L/K) ⧸ N`.** -/
lemma finrank_fixedField_of_isResolventSubgroup (h : N.IsResolventSubgroup H) :
    Module.finrank K (fixedField H) = Group.minTransitiveDegree (Gal(L/K) ⧸ N) := by
  rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField, h.index_eq_minTransitiveDegree]

end IntermediateField
