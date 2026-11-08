import LeanBridge.ForMathlib.GroupTheory.DerivedLength
import LeanBridge.ForMathlib.GroupTheory.Isoclinism
import Mathlib.GroupTheory.Nilpotent

/-!
# Isoclinism invariants

Isoclinic groups `G` and `H` (LMFDB `group.isoclinism`) have isomorphic central quotients
`G / Z(G) ≅ H / Z(H)` and isomorphic commutator subgroups `G' ≅ H'`. Since `G` is nilpotent exactly
when `G / Z(G)` is, and then its class is one more than that of `G / Z(G)` when `G` is nontrivial,
nilpotency and the nilpotency class of nontrivial groups are isoclinism invariants. Since the
derived series of `G` from `G'` on is the derived series of `G'`, solvability and the derived
length of nontrivial solvable groups are isoclinism invariants too. Order is not: all abelian
groups are isoclinic, `C₁` and `C₂` for instance, whose central quotients and commutator subgroups
are trivial. The trivial group is the exception the LMFDB makes: it is isoclinic to `C₂`, of
nilpotency class and derived length `1`, while its own are `0`.

## Main results

* `Group.isIsoclinic_of_isMulCommutative` (LMFDB `group.isoclinism`): abelian groups are
  isoclinic.
* `Group.not_forall_nat_card_eq_of_isIsoclinic` (LMFDB `group.isoclinism`): order is not an
  isoclinism invariant.
* `Group.IsIsoclinic.isNilpotent_iff`, `Group.IsIsoclinic.nilpotencyClass_eq` (LMFDB
  `group.isoclinism`): nilpotency, and the nilpotency class of nontrivial groups, are invariant.
* `Group.IsIsoclinic.isSolvable_iff`, `Group.IsIsoclinic.derivedLength_eq` (LMFDB
  `group.isoclinism`): solvability, and the derived length of nontrivial solvable groups, are
  invariant.
-/

open Subgroup

namespace Group

variable {G H : Type*} [Group G] [Group H]

instance [IsMulCommutative G] : Subsingleton (G ⧸ center G) :=
  ⟨fun a b ↦ Quotient.inductionOn₂' a b fun x y ↦
    QuotientGroup.eq.mpr (by rw [center_eq_top]; trivial)⟩

instance [IsMulCommutative G] : Subsingleton (commutator G) := by
  rw [commutator_eq_bot]
  infer_instance

lemma bijective_one_of_subsingleton [Subsingleton G] [Subsingleton H] :
    Function.Bijective (1 : G →* H) :=
  ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

variable (G H) in
/-- **Abelian groups are isoclinic** (LMFDB `group.isoclinism`): their central quotients and
commutator subgroups are trivial. -/
lemma isIsoclinic_of_isMulCommutative [IsMulCommutative G] [IsMulCommutative H] : IsIsoclinic G H :=
  ⟨⟨.ofBijective 1 bijective_one_of_subsingleton, .ofBijective 1 bijective_one_of_subsingleton,
    fun _ _ ↦ Subsingleton.elim _ _⟩⟩

/-- **Order is not an isoclinism invariant** (LMFDB `group.isoclinism`): the trivial group and `C₂`
are isoclinic, both being abelian. -/
lemma not_forall_nat_card_eq_of_isIsoclinic :
    ¬∀ (G H : Type) [Group G] [Group H], IsIsoclinic G H → Nat.card G = Nat.card H := fun h ↦
  absurd (h Unit (Multiplicative (ZMod 2)) (isIsoclinic_of_isMulCommutative _ _)) (by simp)

lemma map_subtype_derivedSeries_commutator (n : ℕ) :
    (derivedSeries (commutator G) n).map (commutator G).subtype = derivedSeries G (n + 1) := by
  induction n with
  | zero => rw [derivedSeries_zero, ← MonoidHom.range_eq_map, range_subtype, derivedSeries_one]
  | succ n ih => rw [derivedSeries_succ, map_commutator, ih, ← derivedSeries_succ]

namespace IsIsoclinic

/-- **Nilpotency is an isoclinism invariant** (LMFDB `group.isoclinism`): `G` is nilpotent exactly
when `G / Z(G)` is. -/
lemma isNilpotent_iff (h : IsIsoclinic G H) : IsNilpotent G ↔ IsNilpotent H := by
  rcases h with ⟨e⟩
  exact ⟨fun _ ↦ of_quotient_center_nilpotent
      ((isNilpotent_congr e.centralQuotientEquiv).mp inferInstance),
    fun _ ↦ of_quotient_center_nilpotent
      ((isNilpotent_congr e.centralQuotientEquiv).mpr inferInstance)⟩

/-- **The nilpotency class of nontrivial groups is an isoclinism invariant** (LMFDB
`group.isoclinism`): it is one more than that of `G / Z(G)`, and `0` for non-nilpotent groups by
Mathlib's convention. -/
lemma nilpotencyClass_eq [Nontrivial G] [Nontrivial H] (h : IsIsoclinic G H) :
    nilpotencyClass G = nilpotencyClass H := by
  by_cases hG : IsNilpotent G
  · have hH : IsNilpotent H := h.isNilpotent_iff.mp hG
    rcases h with ⟨e⟩
    rw [nilpotencyClass_eq_quotient_center_add_one,
      nilpotencyClass_eq_quotient_center_add_one (G := H), le_antisymm
        (nilpotencyClass_le_of_surjective e.centralQuotientEquiv.symm.toMonoidHom
          e.centralQuotientEquiv.symm.surjective)
        (nilpotencyClass_le_of_surjective e.centralQuotientEquiv.toMonoidHom
          e.centralQuotientEquiv.surjective)]
  · rw [nilpotencyClass_of_not_nilpotent hG,
      nilpotencyClass_of_not_nilpotent (mt h.isNilpotent_iff.mpr hG)]

lemma derivedSeries_succ_eq_bot_iff (h : IsIsoclinic G H) (n : ℕ) :
    derivedSeries G (n + 1) = ⊥ ↔ derivedSeries H (n + 1) = ⊥ := by
  rcases h with ⟨e⟩
  rw [← map_subtype_derivedSeries_commutator, ← map_subtype_derivedSeries_commutator,
    map_eq_bot_iff_of_injective _ (subtype_injective _),
    map_eq_bot_iff_of_injective _ (subtype_injective _),
    ← map_derivedSeries_eq (f := e.commutatorEquiv.toMonoidHom) e.commutatorEquiv.surjective n,
    map_eq_bot_iff_of_injective _ e.commutatorEquiv.injective]

/-- **Solvability is an isoclinism invariant** (LMFDB `group.isoclinism`). -/
lemma isSolvable_iff (h : IsIsoclinic G H) : IsSolvable G ↔ IsSolvable H := by
  simp only [isSolvable_def]
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n + 1, ?_⟩
  · exact (h.derivedSeries_succ_eq_bot_iff n).mp
      (eq_bot_iff.mpr ((derivedSeries_antitone G n.le_succ).trans hn.le))
  · exact (h.derivedSeries_succ_eq_bot_iff n).mpr
      (eq_bot_iff.mpr ((derivedSeries_antitone H n.le_succ).trans hn.le))

/-- **The derived length of nontrivial solvable groups is an isoclinism invariant** (LMFDB
`group.isoclinism`, the solvable length): it is one more than that of `G'`. -/
lemma derivedLength_eq [Nontrivial G] [Nontrivial H] [IsSolvable G] (h : IsIsoclinic G H) :
    derivedLength G = derivedLength H := by
  have : IsSolvable H := h.isSolvable_iff.mp ‹_›
  rw [derivedLength_eq_sInf_eq_bot, derivedLength_eq_sInf_eq_bot]
  congr 1
  ext k
  rcases k with _ | k
  · simp
  · exact h.derivedSeries_succ_eq_bot_iff k

end IsIsoclinic

end Group
