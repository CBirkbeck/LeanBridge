import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.AGroup
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Metacyclic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# A-groups: closure properties, nilpotent A-groups and examples

An A-group (LMFDB `group.a_group`) is a group all of whose Sylow subgroups are abelian. Subgroups
of A-groups and quotients of finite A-groups are A-groups, and a finite nilpotent A-group is
abelian, being the product of its Sylow subgroups. So a finite A-group that is nilpotent of class
at most two modulo a normal subgroup is abelian modulo that subgroup: this is the group theory in
the proof that solvable A-groups are monomial.

## Main results

* `IsAGroup.of_injective`, `IsAGroup.of_surjective`: subgroups of A-groups and quotients of finite
  A-groups are A-groups.
* `IsAGroup.isMulCommutative_of_isNilpotent`: a finite nilpotent A-group is abelian.
* `IsAGroup.commutatorElement_mem_of_forall_commutatorElement_mem`: if all commutators
  `⁅⁅a, b⁆, c⁆` of a finite A-group lie in a normal subgroup `K`, then so do all `⁅a, b⁆`.
* `IsAGroup.of_forall_not_pow_three_dvd_card`: a finite group of cube-free order is an A-group.
* `IsKleinFour.isAGroup`, `not_forall_isZGroup_of_isAGroup` (LMFDB `group.a_group`): the Klein
  four-group is an A-group but not a Z-group, so not every finite A-group is a Z-group.
-/

open Function Subgroup

open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

namespace IsAGroup

/-- **A group that embeds in an A-group is an A-group**: a Sylow subgroup of it maps into a Sylow
subgroup of the A-group. In particular subgroups of A-groups are A-groups. -/
lemma of_injective [IsAGroup G] {f : H →* G} (hf : Injective f) : IsAGroup H := by
  refine ⟨fun p hp P ↦ ⟨⟨fun a b ↦ Subtype.ext <| hf ?_⟩⟩⟩
  rcases (P.isPGroup.map f).exists_le_sylow with ⟨Q, hQ⟩
  have : IsMulCommutative Q := isMulCommutative_sylow p hp Q
  have h : (⟨f a, hQ <| mem_map_of_mem f a.2⟩ : Q) * ⟨f b, hQ <| mem_map_of_mem f b.2⟩ =
      ⟨f b, hQ <| mem_map_of_mem f b.2⟩ * ⟨f a, hQ <| mem_map_of_mem f a.2⟩ :=
    mul_comm' _ _
  simpa using congrArg Subtype.val h

/-- **A quotient of a finite A-group is an A-group**: its Sylow subgroups are the images of those
of the group. -/
lemma of_surjective [Finite G] [IsAGroup G] {f : G →* H} (hf : Surjective f) : IsAGroup H := by
  refine ⟨fun p hp Q ↦ ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  rcases Sylow.mapSurjective_surjective hf p Q with ⟨P, rfl⟩
  have : IsMulCommutative P := isMulCommutative_sylow p hp P
  refine ⟨⟨fun a b ↦ Subtype.ext ?_⟩⟩
  rcases (Sylow.coe_mapSurjective hf P ▸ a.2 : (a : H) ∈ (P : Subgroup G).map f) with ⟨x, hx, hxa⟩
  rcases (Sylow.coe_mapSurjective hf P ▸ b.2 : (b : H) ∈ (P : Subgroup G).map f) with ⟨y, hy, hyb⟩
  have h : (⟨x, hx⟩ : P) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := mul_comm' _ _
  rw [coe_mul, coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
  exact congrArg (fun z : P ↦ f z) h

/-- **A finite nilpotent A-group is abelian**: it is the product of its Sylow subgroups. -/
lemma isMulCommutative_of_isNilpotent [Finite G] [IsAGroup G] [Group.IsNilpotent G] :
    IsMulCommutative G := by
  let e : ((p : (Nat.card G).primeFactors) → (P : Sylow p G) → P) ≃* G :=
    Sylow.directProductOfNormal fun _ ↦ inferInstance
  refine ⟨⟨fun a b ↦ e.symm.injective ?_⟩⟩
  rw [map_mul, map_mul]
  funext p P
  have : IsMulCommutative P := isMulCommutative_sylow p (Nat.prime_of_mem_primeFactors p.2) P
  exact mul_comm' _ _

/-- **A finite A-group that is nilpotent of class at most two modulo a normal subgroup `K` is
abelian modulo `K`**: if all commutators `⁅⁅a, b⁆, c⁆` lie in `K`, then so do all `⁅a, b⁆`. -/
lemma commutatorElement_mem_of_forall_commutatorElement_mem [Finite G] [IsAGroup G] (K : Subgroup G)
    [K.Normal] (h : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ K) (a b : G) : ⁅a, b⁆ ∈ K := by
  have : IsAGroup (G ⧸ K) := of_surjective <| QuotientGroup.mk'_surjective K
  have hc : commutator (G ⧸ K) ≤ center (G ⧸ K) := by
    refine commutator_le.mpr fun x _ y _ ↦ mem_center_iff.mpr fun z ↦ ?_
    rcases QuotientGroup.mk_surjective x with ⟨x, rfl⟩
    rcases QuotientGroup.mk_surjective y with ⟨y, rfl⟩
    rcases QuotientGroup.mk_surjective z with ⟨z, rfl⟩
    have h1 : QuotientGroup.mk' K ⁅⁅x, y⁆, z⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr <| h x y z
    rw [map_commutatorElement, map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_commute.mp h1).eq.symm
  have : Group.IsNilpotent (G ⧸ K) :=
    isNilpotent_of_ker_le_center Abelianization.of <| by rwa [Abelianization.ker_of]
  have : IsMulCommutative (G ⧸ K) := isMulCommutative_of_isNilpotent
  have h1 : QuotientGroup.mk' K ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact mul_comm' _ _
  exact (QuotientGroup.eq_one_iff _).mp h1

/-- **A finite group of cube-free order is an A-group**: its Sylow `p`-subgroups have order `1`,
`p` or `p ^ 2`, and groups of these orders are abelian. -/
lemma of_forall_not_pow_three_dvd_card [Finite G] (h : ∀ p : ℕ, p.Prime → ¬p ^ 3 ∣ Nat.card G) :
    IsAGroup G := by
  refine ⟨fun p hp P ↦ ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card P = p ^ (Nat.card G).factorization p := P.card_eq_multiplicity
  have hle : (Nat.card G).factorization p < 3 := by
    by_contra hk
    exact h p hp <| (pow_dvd_pow p <| not_lt.mp hk).trans <| hcard ▸ P.card_subgroup_dvd_card
  rcases Nat.lt_succ_iff_lt_or_eq.mp hle with hk | hk
  · have : IsCyclic P := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp <| by
          rw [hcard, Nat.lt_one_iff.mp hk, pow_zero]).1
        infer_instance
      · exact isCyclic_of_prime_card (p := p) <| by rw [hcard, hk, pow_one]
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq <| hk ▸ hcard

end IsAGroup

/-- **The Klein four-group is an A-group** (LMFDB `group.a_group`), being abelian. -/
lemma IsKleinFour.isAGroup [IsKleinFour G] : IsAGroup G :=
  have : IsMulCommutative G := isMulCommutative
  inferInstance

/-- **Not every finite A-group is a Z-group** (LMFDB `group.a_group`): the Klein four-group, here
the dihedral group `D₂` of order `4`, is an A-group but not a Z-group. -/
lemma not_forall_isZGroup_of_isAGroup :
    ¬∀ (G : Type) [Group G] [Finite G], IsAGroup G → IsZGroup G :=
  fun h ↦ IsKleinFour.not_isZGroup <| h (DihedralGroup 2) IsKleinFour.isAGroup
