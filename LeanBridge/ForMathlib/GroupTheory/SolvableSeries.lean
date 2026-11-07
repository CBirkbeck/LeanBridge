import LeanBridge.ForMathlib.GroupTheory.ChiefSeries
import LeanBridge.ForMathlib.GroupTheory.DerivedLength

/-!
# Solvable groups and subnormal series with abelian factors

The LMFDB calls a group solvable (LMFDB `group.solvable`, `gg.invariants`) if it has a subnormal
series `⊥ = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₙ = ⊤` whose factors `Hᵢ₊₁ / Hᵢ` are abelian, while Mathlib's
`Group.IsSolvable` asks for the derived series to reach `⊥`. We prove that the two agree, and
deduce the criterion of LMFDB `group.derived_series`: a group is solvable if and only if its derived
series ends at `⊥` at its derived length `k`, where the inclusions `G⁽ⁱ⁺¹⁾ < G⁽ⁱ⁾` for `i < k`
are proper.

## Main results

* `Group.isSolvable_iff_exists_subnormalSeries` (LMFDB `group.solvable`, `gg.invariants`): a group
  is solvable if and only if it has a subnormal series with abelian factors.
* `Group.isSolvable_iff_derivedSeries_derivedLength_eq_bot` (LMFDB `group.derived_series`): a group
  is solvable if and only if `G⁽ᵏ⁾ = 1` for its derived length `k`.
* `Group.exists_subnormalSeries_iff_derivedSeries_derivedLength_eq_bot` (LMFDB
  `group.derived_series`): the same with solvability as in LMFDB `group.solvable`.
* `derivedSeries_succ_lt_of_lt_derivedLength` (LMFDB `group.derived_series`): the inclusions of
  the derived series below the derived length are proper.
-/

open Subgroup

variable {G : Type*} [Group G]

/-- **The inclusions of the derived series below the derived length are proper** (LMFDB
`group.derived_series`): `G⁽ⁱ⁺¹⁾ < G⁽ⁱ⁾` for `i < k`. -/
lemma derivedSeries_succ_lt_of_lt_derivedLength {i : ℕ} (hi : i < derivedLength G) :
    derivedSeries G (i + 1) < derivedSeries G i :=
  (derivedSeries_antitone G i.le_succ).lt_of_ne <| Nat.notMem_of_lt_sInf hi

namespace Group

/-- **A group is solvable if and only if it has a subnormal series with abelian factors**
(LMFDB `group.solvable`): a chain `⊥ = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₙ = ⊤`, each `Hᵢ` normal in `Hᵢ₊₁`, with
every quotient `Hᵢ₊₁ / Hᵢ` abelian. -/
lemma isSolvable_iff_exists_subnormalSeries :
    IsSolvable G ↔ ∃ s : SubnormalSeries G, ∀ i : Fin s.length, IsMulCommutative (s.factor i) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨⟨⟨n, fun j ↦ derivedSeries G j.rev, fun i ↦ ?_⟩, hn, ?_⟩, fun i ↦ ?_⟩
    · rw [Fin.rev_castSucc, Fin.rev_succ, Fin.val_succ, Fin.val_castSucc]
      exact ⟨derivedSeries_antitone G (Nat.le_succ _), (derivedSeries_normal G _).subgroupOf _⟩
    · simp [RelSeries.last]
    · refine Normal.quotient_commutative_iff_commutator_le.mpr ?_
      rw [subgroupOf, ← map_le_iff_le_comap, map_subtype_commutator]
      dsimp only
      rw [Fin.rev_castSucc, Fin.rev_succ, Fin.val_succ, Fin.val_castSucc, derivedSeries_succ]
  · rintro ⟨s, hs⟩
    have key (j : Fin (s.length + 1)) : IsSolvable (s j) := by
      induction j using Fin.induction with
      | zero =>
        rw [s.apply_zero]
        infer_instance
      | succ i ih =>
        have h1 : IsSolvable ((s i.castSucc).subgroupOf (s i.succ)) :=
          isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe (s.le_succ i)).toMonoidHom)
            (subgroupOfEquivOfLe (s.le_succ i)).injective
        have h2 : IsMulCommutative (s.factor i) := hs i
        exact isSolvable_of_subgroup_quotient ((s i.castSucc).subgroupOf (s i.succ))
    have h : IsSolvable (s (Fin.last s.length)) := key _
    rw [s.apply_last] at h
    exact isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
      topEquiv.surjective

/-- **A group is solvable if and only if `G⁽ᵏ⁾ = 1` for its derived length `k`** (LMFDB
`group.derived_series`). -/
lemma isSolvable_iff_derivedSeries_derivedLength_eq_bot :
    IsSolvable G ↔ derivedSeries G (derivedLength G) = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨_, h⟩⟩⟩
  rw [derivedLength_eq_sInf_eq_bot]
  exact Nat.sInf_mem (s := {k | derivedSeries G k = ⊥}) h.solvable

/-- **A group has a subnormal series with abelian factors if and only if `G⁽ᵏ⁾ = 1` for its
derived length `k`** (LMFDB `group.derived_series`, with solvability as in LMFDB
`group.solvable`). -/
lemma exists_subnormalSeries_iff_derivedSeries_derivedLength_eq_bot :
    (∃ s : SubnormalSeries G, ∀ i : Fin s.length, IsMulCommutative (s.factor i)) ↔
      derivedSeries G (derivedLength G) = ⊥ :=
  isSolvable_iff_exists_subnormalSeries.symm.trans isSolvable_iff_derivedSeries_derivedLength_eq_bot

end Group
