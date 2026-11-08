import LeanBridge.ForMathlib.GroupTheory.Supersolvable
import Mathlib.GroupTheory.Nilpotent
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Finite nilpotent groups are supersolvable, and nilpotency is not closed under extensions

A finite nilpotent group `G` is supersolvable (LMFDB `group.nilpotent`, `group.supersolvable`): as
long as a normal subgroup `H` of `G` is proper, the quotient `G ⧸ H` is a nontrivial nilpotent
group, so it has a nontrivial central element `g H`, and `⟨g⟩ H` is a normal subgroup of `G`
containing `H` properly, with cyclic quotient `⟨g⟩ H ⧸ H`. Starting from `⊥`, this builds a normal
series with cyclic factors all of whose terms are normal in `G`.

Nilpotent groups are not closed under extensions (LMFDB `group.nilpotent`): the dihedral group
`D₃ ≅ S₃` of order `6` is an extension of its cyclic rotation subgroup `C₃` by `C₂`, both nilpotent,
but its centre is trivial, so it is not nilpotent.

## Main results

* `Group.IsNilpotent.isSupersolvable` (LMFDB `group.nilpotent`): a finite nilpotent group is
  supersolvable.
* `DihedralGroup.not_isNilpotent` (LMFDB `group.nilpotent`): `Dₙ` is not nilpotent for odd
  `n ≠ 1`, for instance `D₃ ≅ S₃`.
* `DihedralGroup.isNilpotent_dihedralRotations`,
  `DihedralGroup.isNilpotent_quotient_dihedralRotations` (LMFDB `group.nilpotent`): the rotation
  subgroup `Cₙ` of `Dₙ` and the quotient `Dₙ ⧸ Cₙ ≅ C₂` are nilpotent.
* `Group.not_forall_isNilpotent_of_isNilpotent_quotient` (LMFDB `group.nilpotent`): nilpotent groups
  are not closed under extensions.
-/

open Group Subgroup TauCeti

namespace Group

variable {G : Type*} [Group G]

lemma exists_relSeries_last_eq_top [Finite G] [IsNilpotent G] (H : Subgroup G)
    (s : RelSeries {p : Subgroup G × Subgroup G | ∃ x : G, p.2 = zpowers x ⊔ p.1}) (h0 : s.head = ⊥)
    (hs : s.last = H) (hn : ∀ K ∈ s, K.Normal) :
    ∃ t : RelSeries {p : Subgroup G × Subgroup G | ∃ x : G, p.2 = zpowers x ⊔ p.1},
      t.head = ⊥ ∧ t.last = ⊤ ∧ ∀ K ∈ t, K.Normal := by
  induction H using WellFoundedGT.induction generalizing s with
  | ind H ih =>
    rcases eq_or_ne H ⊤ with rfl | hH
    · exact ⟨s, h0, hs, hn⟩
    have : H.Normal := hn H (hs ▸ s.last_mem)
    have : Nontrivial (G ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
    rcases (center (G ⧸ H)).bot_or_exists_ne_one.resolve_left (IsNilpotent.center_ne_bot _) with
      ⟨q, hq, hq1⟩
    rcases QuotientGroup.mk_surjective q with ⟨g, rfl⟩
    have hK : zpowers g ⊔ H = comap (QuotientGroup.mk' H) (zpowers (g : G ⧸ H)) := by
      rw [← QuotientGroup.mk'_apply, ← MonoidHom.map_zpowers, QuotientGroup.comap_map_mk',
        sup_comm]
    have hKn : (zpowers g ⊔ H).Normal :=
      hK ▸ (normal_of_le_center <| zpowers_le.mpr hq).comap _
    have hlt : H < zpowers g ⊔ H := lt_of_le_of_ne le_sup_right fun h ↦
      hq1 <| (QuotientGroup.eq_one_iff g).mpr <| h ▸ mem_sup_left (mem_zpowers g)
    refine ih _ hlt (s.snoc (zpowers g ⊔ H) ⟨g, hs ▸ rfl⟩) (by simp [h0]) (by simp) fun L hL ↦ ?_
    rcases RelSeries.mem_snoc.mp hL with hL | rfl
    · exact hn L hL
    · exact hKn

/-- **A finite nilpotent group is supersolvable** (LMFDB `group.nilpotent`): it has a normal series
`⊥ = N₀ ≤ N₁ ≤ ⋯ ≤ Nₖ = ⊤` with cyclic factors and all terms normal in `G`, obtained by adjoining
at each step an element whose image in `G ⧸ Nᵢ` is a nontrivial central element. -/
lemma IsNilpotent.isSupersolvable [Finite G] [IsNilpotent G] : IsSupersolvable G := by
  have hb : ∀ K ∈ RelSeries.singleton {p : Subgroup G × Subgroup G | ∃ x : G, p.2 = zpowers x ⊔ p.1}
      ⊥, K.Normal := by
    rintro K ⟨i, rfl⟩
    exact (inferInstance : (⊥ : Subgroup G).Normal)
  rcases exists_relSeries_last_eq_top ⊥ _ rfl rfl hb with ⟨s, h0, h1, hn⟩
  refine ⟨⟨⟨⟨s.length, s.toFun, fun i ↦ ?_⟩, h0, h1⟩, fun i ↦ hn _ ⟨i, rfl⟩⟩, fun i ↦ ?_⟩ <;>
    rcases s.step i with ⟨x, hx⟩ <;>
    dsimp only at hx <;>
    have : ((s.toFun i.castSucc).subgroupOf (s.toFun i.succ)).Normal :=
      (hn _ ⟨_, rfl⟩).subgroupOf _
  · exact ⟨hx ▸ le_sup_right, this⟩
  · exact isCyclic_quotient_of_eq_sup (normalizer_eq_top_iff.mpr (hn _ ⟨_, rfl⟩) ▸ mem_top x)
      (hx ▸ mem_sup_left (mem_zpowers x)) hx

end Group

namespace DihedralGroup

variable {n : ℕ}

/-- **The dihedral group `Dₙ` of order `2n` is not nilpotent for odd `n ≠ 1`** (LMFDB
`group.nilpotent`), for instance `D₃ ≅ S₃`: its centre is trivial although it is nontrivial. -/
lemma not_isNilpotent (hodd : Odd n) (hn : n ≠ 1) : ¬Group.IsNilpotent (DihedralGroup n) :=
  fun _ ↦ IsNilpotent.center_ne_bot _ (center_eq_bot_of_odd_ne_one hodd hn)

/-- **The rotation subgroup `Cₙ` of `Dₙ` is nilpotent** (LMFDB `group.nilpotent`), being cyclic. -/
lemma isNilpotent_dihedralRotations : Group.IsNilpotent (dihedralRotations n) :=
  inferInstance

/-- **The quotient `Dₙ ⧸ Cₙ ≅ C₂` is nilpotent** (LMFDB `group.nilpotent`), being of order `2`.
With `DihedralGroup.isNilpotent_dihedralRotations` and `DihedralGroup.not_isNilpotent`, this shows
that an extension of nilpotent groups need not be nilpotent. -/
lemma isNilpotent_quotient_dihedralRotations :
    Group.IsNilpotent (DihedralGroup n ⧸ dihedralRotations n) := by
  have : IsCyclic (DihedralGroup n ⧸ dihedralRotations n) :=
    isCyclic_of_prime_card <| (index_eq_card _).symm.trans <| index_dihedralRotations n
  infer_instance

end DihedralGroup

/-- **Nilpotent groups are not closed under extensions** (LMFDB `group.nilpotent`): the dihedral
group `D₃ ≅ S₃` is not nilpotent, although its normal rotation subgroup `C₃` and the quotient
`D₃ ⧸ C₃ ≅ C₂` are. -/
lemma Group.not_forall_isNilpotent_of_isNilpotent_quotient : ¬∀ (G : Type) [Group G]
    (N : Subgroup G) [N.Normal], Group.IsNilpotent N → Group.IsNilpotent (G ⧸ N) →
    Group.IsNilpotent G := fun h ↦
  DihedralGroup.not_isNilpotent (n := 3) ⟨1, rfl⟩ (by decide) <| h _ (dihedralRotations 3)
    DihedralGroup.isNilpotent_dihedralRotations DihedralGroup.isNilpotent_quotient_dihedralRotations
