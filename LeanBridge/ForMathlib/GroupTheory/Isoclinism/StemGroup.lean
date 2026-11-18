import LeanBridge.ForMathlib.GroupTheory.Isoclinism.Surjective
import LeanBridge.ForMathlib.GroupTheory.StemExtension
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Stem groups in isoclinism classes

A stem group (LMFDB `group.stem_group`) is a group `S` whose centre lies in its commutator subgroup.
An isoclinism `(φ, σ)` between groups `G` and `H` (LMFDB `group.isoclinism`) maps `Z(G) ∩ G'` onto
`Z(H) ∩ H'`, since `φ (g Z(G)) = σ g Z(H)` for `g ∈ G'`. As `|G| = |G / Z(G)| |Z(G)|` and
`Z(S) = Z(S) ∩ S'`, the order of a stem group divides the order of every group isoclinic to it; so
a stem group isoclinic to a finite group is finite, and in a finite isoclinism class the stem
groups are exactly the groups of least order. The same divisibility holds for cardinalities, for
groups of every cardinality.

P. Hall's theorem says that every group is isoclinic to a stem group. Let `ε : ℤ[G] → G^ab` map
each basis element `[g]` of the free abelian group on `G` to `g G'`, and let `P ≤ G × ℤ[G]` be the
fibre product of `ε` and of the abelianization `G → G^ab`. The projection `P → G` is surjective and
its kernel meets `P'` trivially, so `P` is isoclinic to `G`. The second projection embeds
`Z(P) / (Z(P) ∩ P')` in `ℤ[G]`, so this quotient is a free abelian group (Tau Ceti's
`Module.Free.of_injective_of_projective_of_isPrincipalIdealRing`, in every rank) and `Z(P) ∩ P'`
has a complement `T` in `Z(P)`. Then `P / T` is a stem group isoclinic to `P`. The construction
works for groups of every cardinality; for a finite group `G` the stem group is finite, by the
divisibility above.

## Main definitions

* `Group.Isoclinism.centerInfCommutatorEquiv`: the isomorphism `Z(G) ∩ G' ≃* Z(H) ∩ H'` induced by
  an isoclinism.
* `Group.abelianizationPullback`: the fibre product of `G → G^ab` and `ℤ[G] → G^ab`.

## Main results

* `Group.IsStemGroup.nat_card_dvd` (LMFDB `group.stem_group`): the order of a stem group divides
  the order of every group isoclinic to it.
* `Group.IsStemGroup.lift_mk_dvd` (LMFDB `group.stem_group`): the same for cardinalities.
* `Group.IsStemGroup.finite_of_isIsoclinic` (LMFDB `group.stem_group`): a stem group isoclinic to a
  finite group is finite.
* `Group.IsStemGroup.isStemGroup_iff_nat_card_eq` (LMFDB `group.stem_group`): a finite group
  isoclinic to a stem group `S` is a stem group if and only if it has the order of `S`.
* `Group.isStemGroup_quotient`: the quotient by a complement of `Z(H) ∩ H'` in `Z(H)` is a stem
  group.
* `Group.exists_isStemGroup_isIsoclinic` (LMFDB `group.stem_group`, `group.isoclinism`): every
  group is isoclinic to a stem group (P. Hall).
* `Group.exists_finite_isStemGroup_isIsoclinic` (LMFDB `group.stem_group`, `group.isoclinism`):
  every finite group is isoclinic to a finite stem group.

## References

* P. Hall, *The classification of prime-power groups*, J. Reine Angew. Math. 182 (1940), 130–141.
* N. S. Hekster, *On the structure of n-isoclinism classes of groups*, J. Pure Appl. Algebra 40
  (1986), 63–85.
-/

universe u v

open Module Subgroup

open scoped IsMulCommutative

variable {G : Type u} {H : Type v} [Group G] [Group H]

namespace Subgroup

lemma mk_eq_mk_quotient_mul_mk (K : Subgroup G) :
    Cardinal.mk G = Cardinal.mk (G ⧸ K) * Cardinal.mk K := by
  rw [Cardinal.mk_congr (groupEquivQuotientProdSubgroup (s := K)), Cardinal.mk_prod,
    Cardinal.lift_id, Cardinal.lift_id]

lemma mk_dvd_mk_of_le {A B : Subgroup G} (hAB : A ≤ B) : Cardinal.mk A ∣ Cardinal.mk B :=
  ⟨Cardinal.mk (B ⧸ A.subgroupOf B), by
    rw [mk_eq_mk_quotient_mul_mk (A.subgroupOf B),
      Cardinal.mk_congr (subgroupOfEquivOfLe hAB).toEquiv, mul_comm]⟩

end Subgroup

namespace Group.Isoclinism

variable (e : Isoclinism G H)

lemma mk_commutatorEquiv (g : commutator G) :
    ((e.commutatorEquiv g : H) : H ⧸ center H) = e.centralQuotientEquiv (g : G) := by
  let f₁ : commutator G →* H ⧸ center H :=
    ((QuotientGroup.mk' (center H)).comp (commutator H).subtype).comp e.commutatorEquiv.toMonoidHom
  let f₂ : commutator G →* H ⧸ center H :=
    (e.centralQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center G))).comp
      (commutator G).subtype
  have hgen (x y : G) : f₁ (commutatorPairing x y) = f₂ (commutatorPairing x y) := by
    simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, subtype_apply,
      QuotientGroup.mk'_apply]
    rw [← centralCommutatorMap_mk, e.map_centralCommutatorMap, mk_centralCommutatorMap,
      mk_centralCommutatorMap, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hle : commutator G ≤ (f₁.eqLocus f₂).map (commutator G).subtype :=
    (commutator_def G).le.trans <| commutator_le.mpr fun x _ y _ ↦ mem_map.mpr ⟨_, hgen x⁻¹ y⁻¹, by
      simp [coe_commutatorPairing, commutatorElement_def]⟩
  rcases mem_map.mp (hle g.2) with ⟨g', hg', hgg'⟩
  rcases Subtype.ext hgg' with rfl
  exact hg'

lemma coe_commutatorEquiv_mem_center_iff (g : commutator G) :
    (e.commutatorEquiv g : H) ∈ center H ↔ (g : G) ∈ center G := by
  rw [← QuotientGroup.eq_one_iff, e.mk_commutatorEquiv, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff]

/-- The isomorphism `Z(G) ∩ G' ≃* Z(H) ∩ H'` induced by an isoclinism `(φ, σ)` between `G` and `H`
(LMFDB `group.isoclinism`): the restriction of `σ`. -/
def centerInfCommutatorEquiv : ↥(center G ⊓ commutator G) ≃* ↥(center H ⊓ commutator H) where
  toFun g := ⟨e.commutatorEquiv ⟨g, (mem_inf.mp g.2).2⟩, mem_inf.mpr
    ⟨(e.coe_commutatorEquiv_mem_center_iff _).mpr (mem_inf.mp g.2).1, (e.commutatorEquiv _).2⟩⟩
  invFun g := ⟨e.commutatorEquiv.symm ⟨g, (mem_inf.mp g.2).2⟩, mem_inf.mpr
    ⟨(e.symm.coe_commutatorEquiv_mem_center_iff _).mpr (mem_inf.mp g.2).1,
      (e.commutatorEquiv.symm _).2⟩⟩
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g g' := Subtype.ext <| congrArg ((↑) : commutator H → H) <|
    map_mul e.commutatorEquiv ⟨g, (mem_inf.mp g.2).2⟩ ⟨g', (mem_inf.mp g'.2).2⟩

end Group.Isoclinism

namespace Group.IsIsoclinic

lemma nat_card_quotient_center_eq (h : IsIsoclinic G H) :
    Nat.card (G ⧸ center G) = Nat.card (H ⧸ center H) :=
  h.elim fun e ↦ Nat.card_congr e.centralQuotientEquiv.toEquiv

lemma nat_card_center_inf_commutator_eq (h : IsIsoclinic G H) :
    Nat.card ↥(center G ⊓ commutator G) = Nat.card ↥(center H ⊓ commutator H) :=
  h.elim fun e ↦ Nat.card_congr e.centerInfCommutatorEquiv.toEquiv

end Group.IsIsoclinic

namespace Group.IsStemGroup

lemma nat_card_eq_mul (hG : IsStemGroup G) :
    Nat.card G = Nat.card (G ⧸ center G) * Nat.card ↥(center G ⊓ commutator G) := by
  rw [inf_eq_left.mpr hG, ← card_eq_card_quotient_mul_card_subgroup]

/-- **The order of a stem group divides the order of every group isoclinic to it** (LMFDB
`group.stem_group`): for a stem group `G`, `|G| = |G / Z(G)| |Z(G) ∩ G'|` and
`|H| = |H / Z(H)| |Z(H)|`, where `G / Z(G) ≅ H / Z(H)` and `Z(G) ∩ G' ≅ Z(H) ∩ H' ≤ Z(H)`. -/
lemma nat_card_dvd (hG : IsStemGroup G) (h : IsIsoclinic G H) : Nat.card G ∣ Nat.card H := by
  rw [hG.nat_card_eq_mul, h.nat_card_quotient_center_eq, h.nat_card_center_inf_commutator_eq,
    card_eq_card_quotient_mul_card_subgroup (center H)]
  exact mul_dvd_mul_left _ <| card_dvd_of_le inf_le_left

lemma mk_eq_mul (hG : IsStemGroup G) :
    Cardinal.mk G = Cardinal.mk (G ⧸ center G) * Cardinal.mk ↥(center G ⊓ commutator G) := by
  rw [inf_eq_left.mpr hG]
  exact mk_eq_mk_quotient_mul_mk _

/-- **The cardinality of a stem group divides that of every group isoclinic to it** (LMFDB
`group.stem_group`), in cardinal arithmetic: the divisibility of orders for groups of every
cardinality. -/
lemma lift_mk_dvd (hG : IsStemGroup G) (h : IsIsoclinic G H) :
    Cardinal.lift.{v} (Cardinal.mk G) ∣ Cardinal.lift.{u} (Cardinal.mk H) := by
  rcases h with ⟨e⟩
  rcases mk_dvd_mk_of_le (inf_le_left : center H ⊓ commutator H ≤ center H) with ⟨c, hc⟩
  rw [hG.mk_eq_mul, mk_eq_mk_quotient_mul_mk (center H), hc, Cardinal.lift_mul, Cardinal.lift_mul,
    Cardinal.lift_mul, Cardinal.lift_mk_eq'.mpr ⟨e.centralQuotientEquiv.toEquiv⟩,
    Cardinal.lift_mk_eq'.mpr ⟨e.centerInfCommutatorEquiv.toEquiv⟩, ← mul_assoc]
  exact dvd_mul_right _ _

/-- **A stem group isoclinic to a finite group is finite** (LMFDB `group.stem_group`). -/
lemma finite_of_isIsoclinic [Finite H] (hG : IsStemGroup G) (h : IsIsoclinic G H) : Finite G :=
  Nat.finite_of_card_ne_zero <| ne_zero_of_dvd_ne_zero Nat.card_pos.ne' <| hG.nat_card_dvd h

lemma nat_card_eq (hG : IsStemGroup G) (hH : IsStemGroup H) (h : IsIsoclinic G H) :
    Nat.card G = Nat.card H :=
  Nat.dvd_antisymm (hG.nat_card_dvd h) (hH.nat_card_dvd h.symm)

/-- **The stem groups of a finite isoclinism class are its groups of least order** (LMFDB
`group.stem_group`): a finite group isoclinic to a stem group `S` is a stem group if and only if
its order is that of `S`. -/
lemma isStemGroup_iff_nat_card_eq [Finite H] (hG : IsStemGroup G) (h : IsIsoclinic G H) :
    IsStemGroup H ↔ Nat.card H = Nat.card G := by
  refine ⟨fun hH ↦ hH.nat_card_eq hG h.symm, fun hcard ↦ ?_⟩
  rw [hG.nat_card_eq_mul, card_eq_card_quotient_mul_card_subgroup (center H),
    h.nat_card_quotient_center_eq, h.nat_card_center_inf_commutator_eq] at hcard
  exact inf_eq_left.mp <| eq_of_le_of_card_ge inf_le_left
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard).le

end Group.IsStemGroup

namespace Group

/-- **The quotient by a complement of `Z(H) ∩ H'` in the centre is a stem group**: if `T` is a
normal subgroup of `H` with `T ∩ H' = 1` and `Z(H) ≤ T H'`, then `H / T` is a stem group. -/
lemma isStemGroup_quotient (T : Subgroup H) [T.Normal] (hT : T ⊓ commutator H = ⊥)
    (hZ : center H ≤ T ⊔ commutator H) : IsStemGroup (H ⧸ T) := by
  have hker : (QuotientGroup.mk' T).ker ⊓ commutator H = ⊥ := by
    rwa [QuotientGroup.ker_mk']
  rw [IsStemGroup, ← map_center_eq_of_surjective (QuotientGroup.mk'_surjective T) hker,
    ← map_commutator_of_surjective (QuotientGroup.mk'_surjective T)]
  exact (map_mono hZ).trans <| by rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

variable (H) in
lemma exists_complement_center_inf_commutator
    [Projective ℤ (Additive (center H ⧸ (commutator H).subgroupOf (center H)))] :
    ∃ T : Subgroup H, T ≤ center H ∧ T ⊓ commutator H = ⊥ ∧ center H ≤ T ⊔ commutator H := by
  have hsurj : Function.Surjective (MonoidHom.toAdditive <| QuotientGroup.mk' <|
      (commutator H).subgroupOf (center H)).toIntLinearMap := by
    intro y
    rcases QuotientGroup.mk'_surjective ((commutator H).subgroupOf (center H)) y.toMul with ⟨a, ha⟩
    exact ⟨.ofMul a, congrArg Additive.ofMul ha⟩
  rcases projective_lifting_property _ LinearMap.id hsurj with ⟨s, hs⟩
  let σ : center H ⧸ (commutator H).subgroupOf (center H) →* center H :=
    MonoidHom.toAdditive.symm s.toAddMonoidHom
  have hσ (q : center H ⧸ (commutator H).subgroupOf (center H)) :
      QuotientGroup.mk' ((commutator H).subgroupOf (center H)) (σ q) = q :=
    congrArg Additive.toMul <| LinearMap.congr_fun hs <| .ofMul q
  refine ⟨σ.range.map (center H).subtype, map_subtype_le _, eq_bot_iff.mpr fun x hx ↦ ?_,
    fun z hz ↦ ?_⟩
  · rcases mem_inf.mp hx with ⟨hxT, hxc⟩
    rcases mem_map.mp hxT with ⟨_, ⟨q, rfl⟩, rfl⟩
    have hq : q = 1 := by
      rw [← hσ q, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mem_subgroupOf.mpr hxc
    simp [hq]
  · let t : center H := σ (QuotientGroup.mk' _ ⟨z, hz⟩)
    have ht : t⁻¹ * ⟨z, hz⟩ ∈ (commutator H).subgroupOf (center H) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ← QuotientGroup.mk'_apply, hσ, QuotientGroup.mk'_apply, inv_mul_cancel]
    have hzt : z = t * ↑(t⁻¹ * ⟨z, hz⟩) := by
      simp
    rw [hzt]
    exact mul_mem (mem_sup_left ⟨t, ⟨_, rfl⟩, rfl⟩) (mem_sup_right <| mem_subgroupOf.mp ht)

variable (G) in
/-- The fibre product of the abelianization `G → G^ab` and of the homomorphism `ℤ[G] → G^ab` that
maps each basis element `[g]` of the free abelian group on the elements of `G` to `g G'`: the
subgroup of pairs `(g, x)` of `G × ℤ[G]` with `g G' = ε(x)`. -/
def abelianizationPullback : Subgroup (G × Multiplicative (FreeAbelianGroup G)) :=
  (Abelianization.of.comp <| MonoidHom.fst _ _).eqLocus <|
    (AddMonoidHom.toMultiplicativeLeft <| FreeAbelianGroup.lift fun g ↦ .ofMul <|
      Abelianization.of g).comp <| MonoidHom.snd _ _

lemma mem_abelianizationPullback {p : G × Multiplicative (FreeAbelianGroup G)} :
    p ∈ abelianizationPullback G ↔ Abelianization.of p.1 =
      (FreeAbelianGroup.lift (fun g ↦ Additive.ofMul <| Abelianization.of g) p.2.toAdd).toMul :=
  Iff.rfl

lemma surjective_fst_comp_subtype_abelianizationPullback :
    Function.Surjective <| (MonoidHom.fst _ _).comp (abelianizationPullback G).subtype :=
  fun g ↦ ⟨⟨(g, .ofAdd <| FreeAbelianGroup.of g), mem_abelianizationPullback.mpr <| by simp⟩, rfl⟩

lemma ker_fst_comp_subtype_inf_commutator_abelianizationPullback :
    ((MonoidHom.fst _ _).comp (abelianizationPullback G).subtype).ker ⊓
      commutator (abelianizationPullback G) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  rcases mem_inf.mp hx with ⟨h₁, h₂⟩
  exact Subtype.ext <| Prod.ext h₁ <| Abelianization.commutator_subset_ker
    ((MonoidHom.snd _ _).comp (abelianizationPullback G).subtype) h₂

lemma isIsoclinic_abelianizationPullback : IsIsoclinic (abelianizationPullback G) G :=
  isIsoclinic_of_surjective surjective_fst_comp_subtype_abelianizationPullback
    ker_fst_comp_subtype_inf_commutator_abelianizationPullback

instance : Free ℤ (Additive (center (abelianizationPullback G) ⧸
    (commutator (abelianizationPullback G)).subgroupOf (center (abelianizationPullback G)))) := by
  let P : Subgroup (G × Multiplicative (FreeAbelianGroup G)) := abelianizationPullback G
  let q : center P →* Multiplicative (FreeAbelianGroup G) :=
    ((MonoidHom.snd _ _).comp P.subtype).comp (center P).subtype
  have hq : (commutator P).subgroupOf (center P) = q.ker := by
    refine le_antisymm (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    · exact Abelianization.commutator_subset_ker ((MonoidHom.snd _ _).comp P.subtype)
        (mem_subgroupOf.mp hz)
    · have hz₂ : ((z : P) : G × Multiplicative (FreeAbelianGroup G)).2 = 1 :=
        MonoidHom.mem_ker.mp hz
      have hz₁ : ((z : P) : G × Multiplicative (FreeAbelianGroup G)).1 ∈ commutator G := by
        rw [← Abelianization.ker_of, MonoidHom.mem_ker, mem_abelianizationPullback.mp (z : P).2,
          hz₂]
        simp
      rcases mem_map.mp <| (map_commutator_of_surjective
        surjective_fst_comp_subtype_abelianizationPullback).ge hz₁ with ⟨c, hc, hcz⟩
      have hcz' : c = z := Subtype.ext <| Prod.ext hcz <| .trans
        (Abelianization.commutator_subset_ker ((MonoidHom.snd _ _).comp P.subtype) hc) hz₂.symm
      exact mem_subgroupOf.mpr <| hcz' ▸ hc
  let F : center P ⧸ (commutator P).subgroupOf (center P) →* Multiplicative (FreeAbelianGroup G) :=
    (QuotientGroup.kerLift q).comp (QuotientGroup.quotientMulEquivOfEq hq).toMonoidHom
  have hF : Function.Injective F :=
    (QuotientGroup.kerLift_injective q).comp (MulEquiv.injective _)
  exact Free.of_injective_of_projective_of_isPrincipalIdealRing
    (MonoidHom.toAdditiveLeft F).toIntLinearMap <|
    (injective_iff_map_eq_zero _).mpr fun x hx ↦ (injective_iff_map_eq_one F).mp hF x.toMul hx

variable (G) in
/-- **P. Hall's theorem: every group is isoclinic to a stem group** (LMFDB `group.stem_group`,
`group.isoclinism`), for groups of every cardinality: a quotient of the fibre product
`abelianizationPullback G` by a complement of the intersection of its centre with its commutator
subgroup. -/
lemma exists_isStemGroup_isIsoclinic :
    ∃ (S : Type u) (_ : Group S), IsStemGroup S ∧ IsIsoclinic G S := by
  rcases exists_complement_center_inf_commutator (abelianizationPullback G) with
    ⟨T, hTZ, hT, hZ⟩
  have : T.Normal := normal_of_le_center hTZ
  exact ⟨_, inferInstance, isStemGroup_quotient T hT hZ,
    isIsoclinic_abelianizationPullback.symm.trans <| isIsoclinic_quotient T hT⟩

variable (G) in
/-- **Every finite group is isoclinic to a finite stem group** (LMFDB `group.stem_group`,
`group.isoclinism`): P. Hall's theorem for finite groups, whose stem groups are finite. -/
lemma exists_finite_isStemGroup_isIsoclinic [Finite G] :
    ∃ (S : Type u) (_ : Group S), Finite S ∧ IsStemGroup S ∧ IsIsoclinic G S := by
  rcases exists_isStemGroup_isIsoclinic G with ⟨S, _, hS, h⟩
  exact ⟨S, ‹_›, hS.finite_of_isIsoclinic h.symm, hS, h⟩

end Group
