import LeanBridge.ForMathlib.GroupTheory.ChiefSeriesJordanHolder
import LeanBridge.ForMathlib.GroupTheory.TypeLength

/-!
# Composition series of finite groups and the composition length

A composition series of a group `G` is a subnormal series `1 = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₖ = G` whose factors
`Hᵢ₊₁ / Hᵢ` are simple (`Subgroup.SubnormalSeries.IsComposition`), and the number of Jordan factors
of a finite group in the LMFDB's descriptor "Non-solvable - n" (LMFDB `group.type`) is the length
`k` of such a series. Every finite group has one: a nontrivial finite group has a normal subgroup
maximal among the proper ones, by finiteness, and the quotient by it is simple, so an induction on
the order builds a composition series from the top down. By the Jordan–Hölder theorem
(`Subgroup.SubnormalSeries.IsComposition.exists_equiv_nonempty_mulEquiv_factor`) all composition
series of a group have the same length, so `Group.compositionLength`, the least length of a
composition series, is the length of each of them, and `Group.typeLength` gives a finite group that
is neither solvable nor simple the descriptor "Non-solvable - n" with `n` its number of composition
factors.

## Main results

* `Subgroup.exists_normal_isSimpleGroup_quotient`: a nontrivial finite group has a normal subgroup
  with simple quotient.
* `Subgroup.SubnormalSeries.exists_isComposition` (LMFDB `group.type`): every finite group has a
  composition series.
* `Subgroup.SubnormalSeries.IsComposition.length_eq` (LMFDB `group.type`): two composition series
  of a group have the same length.
* `Group.compositionLength_eq_length` (LMFDB `group.type`): the composition length of a group is the
  length of each of its composition series.
* `Group.typeLength_eq_nonsolvable` (LMFDB `group.type`): a finite group that is neither solvable
  nor simple has the descriptor "Non-solvable - n", `n` the length of its composition series.
-/

variable {G : Type*} [Group G]

namespace Subgroup

variable [Finite G] [Nontrivial G] in
/-- **A nontrivial finite group has a normal subgroup with simple quotient**: a normal subgroup
maximal among the proper ones, which exists by finiteness. -/
lemma exists_normal_isSimpleGroup_quotient :
    ∃ (N : Subgroup G) (_ : N.Normal), IsSimpleGroup (G ⧸ N) := by
  rcases (Set.toFinite {N : Subgroup G | N.Normal ∧ N ≠ ⊤}).exists_maximal
    ⟨⊥, inferInstance, bot_ne_top⟩ with ⟨N, ⟨hN, hNt⟩, hmax⟩
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNt
  refine ⟨N, hN, { eq_bot_or_eq_top_of_normal := fun M hM ↦ ?_ }⟩
  rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) M]
  by_cases hL : M.comap (QuotientGroup.mk' N) = ⊤
  · rw [hL, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact .inr rfl
  · have hle : M.comap (QuotientGroup.mk' N) ≤ N :=
      hmax ⟨hM.comap _, hL⟩ ((QuotientGroup.ker_mk' N).ge.trans (ker_le_comap _ M))
    exact .inl <| eq_bot_iff.mpr <| (map_mono hle).trans (QuotientGroup.map_mk'_self N).le

variable [Finite G] in
lemma exists_compositionSeries_head_eq_bot_last_eq (K : Subgroup G) :
    letI : JordanHolderLattice (Subgroup G) := jordanHolderLattice G
    ∃ s : CompositionSeries (Subgroup G), s.head = ⊥ ∧ s.last = K := by
  induction hn : Nat.card K using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    rcases eq_or_ne K ⊥ with rfl | hK
    · exact ⟨.singleton _ ⊥, rfl, rfl⟩
    have : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hK
    rcases exists_normal_isSimpleGroup_quotient (G := K) with ⟨N, hN, hs⟩
    have hNK : (N.map K.subtype).subgroupOf K = N :=
      comap_map_eq_self_of_injective K.subtype_injective N
    have hlt : Nat.card (N.map K.subtype) < n := by
      rw [card_map_of_injective K.subtype_injective, ← hn, ← card_top (G := K)]
      exact card_lt_of_lt (QuotientGroup.nontrivial_iff.mp hs.toNontrivial).lt_top
    rcases ih _ hlt _ rfl with ⟨s, hs₀, hs₁⟩
    refine ⟨s.snoc K ⟨hs₁ ▸ map_subtype_le N, ?_⟩, (s.head_snoc _ _).trans hs₀, s.last_snoc _ _⟩
    rw [hs₁, hNK]
    exact ⟨hN, hs⟩

namespace SubnormalSeries

variable {s₁ s₂ : SubnormalSeries G}

variable [Finite G] in
/-- **Every finite group has a composition series** (LMFDB `group.type`), a subnormal series with
simple factors. -/
lemma exists_isComposition : ∃ s : SubnormalSeries G, s.IsComposition := by
  rcases exists_compositionSeries_head_eq_bot_last_eq (⊤ : Subgroup G) with ⟨s, hs₀, hs₁⟩
  exact ⟨⟨s.ofLE fun p hp ↦ ⟨hp.1, hp.2.1⟩, hs₀, hs₁⟩, fun i ↦ (s.step i).2.snd⟩

/-- **Two composition series of a group have the same length** (LMFDB `group.type`), by the
Jordan–Hölder theorem. -/
lemma IsComposition.length_eq (h₁ : s₁.IsComposition) (h₂ : s₂.IsComposition) :
    s₁.length = s₂.length :=
  (h₁.exists_equiv_nonempty_mulEquiv_factor h₂).elim fun e _ ↦ Fin.equiv_iff_eq.mp ⟨e⟩

end SubnormalSeries

end Subgroup

namespace Group

open Subgroup

variable {s : SubnormalSeries G}

/-- **The composition length of a group is the length of each of its composition series**
(LMFDB `group.type`), its number of composition factors: all composition series have the same
length by the Jordan–Hölder theorem, and every finite group has one. -/
lemma compositionLength_eq_length (hs : s.IsComposition) : compositionLength G = s.length := by
  have h : {n | ∃ t : SubnormalSeries G, t.IsComposition ∧ t.length = n} = {s.length} :=
    Set.ext fun n ↦ ⟨fun ⟨t, ht, htn⟩ ↦ htn ▸ ht.length_eq hs, fun hn ↦ ⟨s, hs, hn.symm⟩⟩
  rw [compositionLength, h, csInf_singleton]

variable [Finite G] in
/-- **A finite group that is neither solvable nor simple has the descriptor "Non-solvable - n"**
(LMFDB `group.type`), `n` the length of any of its composition series, its number of composition
factors. -/
lemma typeLength_eq_nonsolvable (hG : ¬IsSolvable G) (hG' : ¬IsSimpleGroup G)
    (hs : s.IsComposition) : typeLength G = .nonsolvable s.length := by
  have hab : ¬∀ a b : G, a * b = b * a := fun h ↦ hG (isSolvable_of_comm h)
  have hc : ¬IsCyclic G := fun _ ↦ hab (IsCyclic.commGroup : CommGroup G).mul_comm
  have hn : ¬IsNilpotent G := fun _ ↦ hG inferInstance
  rw [typeLength, ite_eq_right hc, dite_eq_right hab, ite_eq_right hn, ite_eq_right hG,
    ite_eq_right hG', compositionLength_eq_length hs]

end Group
