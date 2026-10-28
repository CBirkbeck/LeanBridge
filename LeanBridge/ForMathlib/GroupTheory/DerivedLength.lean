import Mathlib.Data.Fintype.Powerset
import Mathlib.GroupTheory.Solvable
import Mathlib.Order.OrderIsoNat

/-!
# The derived length of a group

The derived series (LMFDB `group.derived_series`) is Mathlib's `derivedSeries`.

## Main definitions

* `derivedLength` (LMFDB `group.derived_series`).

## Main results

* `derivedSeries_succ_derivedLength`: the derived series of a finite group is stationary from its
  derived length on.
* `derivedLength_eq_sInf_eq_bot`: the derived length of a solvable group is the least `k` with
  `G⁽ᵏ⁾ = 1`.
-/

variable (G : Type*) [Group G]

/-- The **derived length** (LMFDB `group.derived_series`) of `G`, the least `k` such that
`G⁽ᵏ⁺¹⁾ = G⁽ᵏ⁾` in the derived series `G = G⁽⁰⁾ ⊵ G⁽¹⁾ ⊵ ⋯`. Such a `k` exists for finite `G`;
otherwise this is `0` by convention. For solvable `G` it is the least `k` with `G⁽ᵏ⁾ = 1`. -/
noncomputable def derivedLength : ℕ :=
  sInf {k | derivedSeries G (k + 1) = derivedSeries G k}

variable {G}

lemma derivedSeries_eq_of_succ_eq {k : ℕ} (hk : derivedSeries G (k + 1) = derivedSeries G k)
    {n : ℕ} (hn : k ≤ n) : derivedSeries G n = derivedSeries G k := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih => rw [derivedSeries_succ, ih, ← derivedSeries_succ, hk]

/-- The derived series of a finite group is stationary from its derived length on. -/
lemma derivedSeries_succ_derivedLength [Finite G] :
    derivedSeries G (derivedLength G + 1) = derivedSeries G (derivedLength G) := by
  have hf : Finite (Subgroup G) := .of_injective _ SetLike.coe_injective
  have hw : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  rcases WellFoundedLT.antitone_chain_condition (derivedSeries_antitone G) with ⟨n, hn⟩
  exact Nat.sInf_mem (s := {k | derivedSeries G (k + 1) = derivedSeries G k})
    ⟨n, (hn (n + 1) n.le_succ).symm⟩

/-- The derived length of a solvable group is the least `k` with `G⁽ᵏ⁾ = 1`. -/
lemma derivedLength_eq_sInf_eq_bot [Group.IsSolvable G] :
    derivedLength G = sInf {k | derivedSeries G k = ⊥} := by
  rcases ‹Group.IsSolvable G›.solvable with ⟨m, hm⟩
  refine congrArg sInf <| Set.ext fun k ↦ ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩
  · rcases le_total m k with h | h
    · exact eq_bot_iff.mpr <| hm ▸ derivedSeries_antitone G h
    · exact (derivedSeries_eq_of_succ_eq hk h).symm.trans hm
  · rw [Set.mem_ofPred_eq, derivedSeries_succ, hk.out, Subgroup.commutator_bot_left]
