import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Algebra.GroupAction.PermutationRepresentation

/-!
# Minimal permutation degrees of a finite group

## Main definitions

* `Group.minPermDegree` (LMFDB `group.permutation_degree`): the least degree of a faithful
  permutation representation.
* `Group.minTransitiveDegree` (LMFDB `group.transitive_degree`): the least degree of a faithful
  transitive permutation representation.

## Main results

* `Group.exists_injective_minPermDegree`: `G` embeds in `S_n` for `n` its minimal permutation
  degree.
* `Group.exists_injective_isTransitive_minTransitiveDegree`: `G` embeds in `S_n` as a transitive
  subgroup for `n` its minimal transitive degree.
-/

open Equiv Function

namespace Group

variable (G : Type*) [Group G]

/-- The **minimal permutation degree** of a finite group `G` (LMFDB `group.permutation_degree`):
the least positive integer `n` such that `G` embeds in the symmetric group `S_n`, i.e. has a
faithful permutation representation of degree `n`. For an infinite group there is no such `n`, and
the value is the junk `0`. -/
noncomputable def minPermDegree : ℕ :=
  sInf {n | 0 < n ∧ ∃ f : G →* Perm (Fin n), Injective f}

/-- The **minimal transitive degree** of a finite group `G` (LMFDB `group.transitive_degree`): the
least positive integer `n` such that `G` embeds in the symmetric group `S_n` as a transitive
subgroup, i.e. has a faithful transitive permutation representation of degree `n`. For an infinite
group there is no such `n`, and the value is the junk `0`. -/
noncomputable def minTransitiveDegree : ℕ :=
  sInf {n | 0 < n ∧ ∃ f : G →* Perm (Fin n), Injective f ∧ ∀ i j, ∃ g, f g i = j}

variable {G} {n : ℕ} {f : G →* Perm (Fin n)}

lemma minPermDegree_le (hn : 0 < n) (hf : Injective f) : minPermDegree G ≤ n :=
  Nat.sInf_le ⟨hn, f, hf⟩

lemma minTransitiveDegree_le (hn : 0 < n) (hf : Injective f) (ht : ∀ i j, ∃ g, f g i = j) :
    minTransitiveDegree G ≤ n :=
  Nat.sInf_le ⟨hn, f, hf, ht⟩

variable (G) [Finite G]

private lemma exists_regular :
    ∃ f : G →* Perm (Fin (Nat.card G)), Injective f ∧ ∀ i j, ∃ g, f g i = j := by
  let e : G ≃ Fin (Nat.card G) := Finite.equivFin G
  refine ⟨permutationRepresentation e, permutationRepresentation_injective e, fun i j ↦
    ⟨e.symm j * (e.symm i)⁻¹, ?_⟩⟩
  rw [permutationRepresentation_apply, smul_eq_mul, inv_mul_cancel_right, apply_symm_apply]

private lemma nonempty_minTransitiveDegree :
    {n | 0 < n ∧ ∃ f : G →* Perm (Fin n), Injective f ∧ ∀ i j, ∃ g, f g i = j}.Nonempty :=
  ⟨_, Nat.card_pos, exists_regular G⟩

private lemma nonempty_minPermDegree :
    {n | 0 < n ∧ ∃ f : G →* Perm (Fin n), Injective f}.Nonempty := by
  rcases exists_regular G with ⟨f, hf, -⟩
  exact ⟨_, Nat.card_pos, f, hf⟩

lemma minPermDegree_pos : 0 < minPermDegree G :=
  (Nat.sInf_mem <| nonempty_minPermDegree G).1

lemma minTransitiveDegree_pos : 0 < minTransitiveDegree G :=
  (Nat.sInf_mem <| nonempty_minTransitiveDegree G).1

/-- **`G` embeds in `S_n` for `n` its minimal permutation degree.** -/
lemma exists_injective_minPermDegree : ∃ f : G →* Perm (Fin (minPermDegree G)), Injective f :=
  (Nat.sInf_mem <| nonempty_minPermDegree G).2

/-- **`G` embeds in `S_n` as a transitive subgroup for `n` its minimal transitive degree.** -/
lemma exists_injective_isTransitive_minTransitiveDegree :
    ∃ f : G →* Perm (Fin (minTransitiveDegree G)), Injective f ∧ ∀ i j, ∃ g, f g i = j :=
  (Nat.sInf_mem <| nonempty_minTransitiveDegree G).2

lemma minPermDegree_le_minTransitiveDegree : minPermDegree G ≤ minTransitiveDegree G := by
  rcases exists_injective_isTransitive_minTransitiveDegree G with ⟨f, hf, -⟩
  exact minPermDegree_le (minTransitiveDegree_pos G) hf

end Group
