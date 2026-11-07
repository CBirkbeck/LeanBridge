import LeanBridge.ForMathlib.FieldTheory.Galois.ResolventField

/-!
# The minimal transitive degree as a least index

The minimal transitive degree of a finite group `G` (LMFDB `group.transitive_degree`,
`Group.minTransitiveDegree`) is the least degree of a faithful transitive permutation
representation of `G`. Equivalently, it is the least positive `n` such that the symmetric group
`S_n` has a transitive subgroup isomorphic to `G`; and it is the least index of a subgroup of `G`
with trivial normal core (LMFDB `group.core`), by LeanBridge's
`Subgroup.IsResolventSubgroup.index_eq_minTransitiveDegree` for the trivial normal subgroup, the
minimal transitive degree being invariant under isomorphism.

## Main results

* `Group.minTransitiveDegree_congr`: isomorphic groups have the same minimal transitive degree.
* `Group.isLeast_pretransitive_minTransitiveDegree` (LMFDB `group.transitive_degree`): the minimal
  transitive degree of `G` is the least positive `n` such that `S_n` has a transitive subgroup
  isomorphic to `G`.
* `Group.isLeast_index_minTransitiveDegree` (LMFDB `group.transitive_degree`): the minimal
  transitive degree of `G` is the least index of a subgroup of `G` with trivial normal core.
-/

open Equiv Function MulAction

namespace Group

variable {G G' : Type*} [Group G] [Group G']

/-- **Isomorphic groups have the same minimal transitive degree.** -/
lemma minTransitiveDegree_congr (e : G ≃* G') : minTransitiveDegree G = minTransitiveDegree G' := by
  refine congrArg sInf <| Set.ext fun _ ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨f, hf, ht⟩
    refine ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.injective, fun i j ↦ ?_⟩
    rcases ht i j with ⟨g, hg⟩
    exact ⟨e g, by simpa using hg⟩
  · rintro ⟨f, hf, ht⟩
    refine ⟨f.comp e.toMonoidHom, hf.comp e.injective, fun i j ↦ ?_⟩
    rcases ht i j with ⟨g, hg⟩
    exact ⟨e.symm g, by simpa using hg⟩

variable (G) [Finite G]

/-- **The minimal transitive degree of `G` is the least positive `n` such that `S_n` has a
transitive subgroup isomorphic to `G`** (LMFDB `group.transitive_degree`). -/
lemma isLeast_pretransitive_minTransitiveDegree : IsLeast {n | 0 < n ∧
    ∃ K : Subgroup (Perm (Fin n)), IsPretransitive K (Fin n) ∧ Nonempty (G ≃* K)}
    (minTransitiveDegree G) := by
  have h : {n | 0 < n ∧ ∃ K : Subgroup (Perm (Fin n)), IsPretransitive K (Fin n) ∧
      Nonempty (G ≃* K)} = {n | 0 < n ∧ ∃ f : G →* Perm (Fin n), Injective f ∧
      ∀ i j, ∃ g, f g i = j} := by
    refine Set.ext fun _ ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
    · rintro ⟨K, hK, ⟨e⟩⟩
      refine ⟨K.subtype.comp e.toMonoidHom, K.subtype_injective.comp e.injective, fun i j ↦ ?_⟩
      rcases hK.exists_smul_eq i j with ⟨k, hk⟩
      exact ⟨e.symm k, by simpa [Subgroup.smul_def] using hk⟩
    · rintro ⟨f, hf, ht⟩
      refine ⟨f.range, ⟨fun i j ↦ ?_⟩, ⟨MonoidHom.ofInjective hf⟩⟩
      rcases ht i j with ⟨g, hg⟩
      exact ⟨⟨f g, g, rfl⟩, hg⟩
  rw [h]
  exact ⟨⟨minTransitiveDegree_pos G, exists_injective_isTransitive_minTransitiveDegree G⟩,
    fun _ ⟨hn, _, hf, ht⟩ ↦ minTransitiveDegree_le hn hf ht⟩

/-- **The minimal transitive degree of `G` is the least index of a subgroup of `G` with trivial
normal core** (LMFDB `group.transitive_degree`, `group.core`): the index of a resolvent subgroup
for the trivial normal subgroup, `Subgroup.IsResolventSubgroup.index_eq_minTransitiveDegree`. -/
lemma isLeast_index_minTransitiveDegree :
    IsLeast {n | ∃ H : Subgroup G, H.normalCore = ⊥ ∧ H.index = n} (minTransitiveDegree G) := by
  rcases Subgroup.exists_isResolventSubgroup (⊥ : Subgroup G) with ⟨H, hH⟩
  have h : H.index = minTransitiveDegree G :=
    hH.index_eq_minTransitiveDegree.trans <| minTransitiveDegree_congr <| QuotientGroup.quotientBot
  exact ⟨⟨H, hH.1, h⟩, fun _ ⟨K, hK, hKn⟩ ↦ h ▸ hKn ▸ hH.2 K hK⟩

end Group
