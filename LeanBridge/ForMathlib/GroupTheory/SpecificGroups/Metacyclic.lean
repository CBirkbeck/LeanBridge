import LeanBridge.ForMathlib.GroupTheory.Supersolvable
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Metacyclic groups

A group `G` is metacyclic if it is an extension of a cyclic group by a cyclic group, that is, if it
has a cyclic normal subgroup `N` with cyclic quotient `G ⧸ N` (an extension of `Q` by `N` is a group
with a normal subgroup `N` and quotient `Q`, LMFDB `group.nonsplit_product`).

The knowl adds that metacyclic groups are supersolvable, hence monomial, and that Z-groups are
metacyclic but not conversely. Supersolvability, the metacyclicity of finite Z-groups and a
counterexample to the converse, the Klein four-group, are proved here; that supersolvable groups
are monomial (Huppert's theorem) is not.

## Main definitions

* `IsMetacyclic` (LMFDB `group.metacyclic`).

## Main results

* `IsMetacyclic.isSupersolvable`: metacyclic groups are supersolvable.
* `IsZGroup.isMetacyclic`: finite Z-groups are metacyclic.
* `IsKleinFour.isMetacyclic`, `IsKleinFour.not_isZGroup`: the Klein four-group is metacyclic but
  not a Z-group.
* The instance `IsMetacyclic G` for cyclic `G`.
-/

open Subgroup

variable (G : Type*) [Group G]

/-- A group `G` is **metacyclic** (LMFDB `group.metacyclic`) if it is an extension of a cyclic group
by a cyclic group: it has a cyclic normal subgroup `N` with cyclic quotient `G ⧸ N`. -/
@[mk_iff] class IsMetacyclic : Prop where
  /-- A metacyclic group has a cyclic normal subgroup with cyclic quotient. -/
  exists_normal : ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic N ∧ IsCyclic (G ⧸ N)

instance [IsCyclic G] : IsMetacyclic G :=
  ⟨⊥, inferInstance, inferInstance, isCyclic_of_surjective _ <| QuotientGroup.mk'_surjective ⊥⟩

variable {G}

/-- **Metacyclic groups are supersolvable** (LMFDB `group.metacyclic`): for a cyclic normal subgroup
`N` with cyclic quotient, `⊥ ≤ N ≤ G` is a normal series with cyclic factors. -/
lemma IsMetacyclic.isSupersolvable [h : IsMetacyclic G] : Group.IsSupersolvable G := by
  rcases h.exists_normal with ⟨N, hN, hNc, hQc⟩
  have h₀ (B : Subgroup G) (A : Subgroup B) {_ : A.Normal} (hB : B = N) : IsCyclic (B ⧸ A) := by
    subst hB
    exact isCyclic_of_surjective _ <| QuotientGroup.mk'_surjective A
  have h₁ (A B : Subgroup G) {_ : (A.subgroupOf B).Normal} (hA : A = N) (hB : B = ⊤) :
      IsCyclic (B ⧸ A.subgroupOf B) := by
    subst hA hB
    let e : G ≃* (⊤ : Subgroup G) := topEquiv.symm
    exact isCyclic_of_surjective _ <| QuotientGroup.map_surjective_of_surjective A _ e.toMonoidHom
      (QuotientGroup.mk_surjective.comp e.surjective) fun _ ↦ id
  refine ⟨NormalSeries.ofLE ⟨2, ![⊥, N, ⊤], fun i ↦ by fin_cases i <;> simp⟩
    (fun i ↦ by fin_cases i <;> simp [hN]) (by simp [RelSeries.head])
    (by simp [RelSeries.last]), Fin.forall_fin_two.mpr ⟨h₀ _ _ ?_, h₁ _ _ ?_ ?_⟩⟩
  all_goals rfl

/-- **Finite Z-groups are metacyclic** (LMFDB `group.metacyclic`): the commutator subgroup and the
abelianization of a finite Z-group are cyclic. -/
lemma IsZGroup.isMetacyclic [Finite G] [IsZGroup G] : IsMetacyclic G :=
  ⟨commutator G, inferInstance, IsZGroup.isCyclic_commutator G, IsZGroup.isCyclic_abelianization⟩

namespace IsKleinFour

variable [IsKleinFour G]

/-- **The Klein four-group is metacyclic** (LMFDB `group.metacyclic`): it is an extension of `C₂`
by `C₂`. -/
lemma isMetacyclic : IsMetacyclic G := by
  have hG : Nat.card G = 4 := card_four
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp <| hG ▸ by norm_num
  have : IsMulCommutative G := isMulCommutative
  rcases exists_ne (1 : G) with ⟨x, hx⟩
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [sq, mul_self]) hx
  refine ⟨Subgroup.zpowers x, inferInstance, inferInstance, isCyclic_of_prime_card (p := 2) ?_⟩
  have h : Nat.card G = Nat.card (G ⧸ Subgroup.zpowers x) * Nat.card (Subgroup.zpowers x) :=
    (Subgroup.zpowers x).card_eq_card_quotient_mul_card_subgroup
  rw [hG, Nat.card_zpowers, hx2] at h
  omega

/-- **The Klein four-group is not a Z-group** (LMFDB `group.metacyclic`): it is a non-cyclic
`2`-group. So the converse of `IsZGroup.isMetacyclic` fails. -/
lemma not_isZGroup : ¬IsZGroup G := by
  intro
  have h : Nat.card (⊤ : Subgroup G) = 2 ^ 2 := card_top.trans card_four
  exact not_isCyclic <| topEquiv.isCyclic.mp (IsPGroup.of_card h).isCyclic_of_isZGroup

end IsKleinFour
