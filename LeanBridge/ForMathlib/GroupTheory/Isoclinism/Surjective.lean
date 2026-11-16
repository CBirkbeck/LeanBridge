import LeanBridge.ForMathlib.GroupTheory.Isoclinism
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Isoclinisms induced by surjective homomorphisms

Let `f : G →* H` be a surjective homomorphism whose kernel meets the commutator subgroup `G'`
trivially. Then its kernel is central, the preimage of the centre `Z(H)` is `Z(G)`, so `f` induces
an isomorphism `G / Z(G) ≃* H / Z(H)`, and `f` maps `G'` isomorphically onto `H'`. These two
isomorphisms are compatible with the commutator maps, so they form an isoclinism (LMFDB
`group.isoclinism`). In particular a group `G` is isoclinic to its quotient by every normal subgroup
`N` with `N ∩ G' = 1`.

## Main definitions

* `Group.Isoclinism.ofSurjective`: the isoclinism induced by such a homomorphism.

## Main results

* `Group.comap_center_eq_of_surjective`: the preimage of `Z(H)` under such a homomorphism is `Z(G)`.
* `Group.isIsoclinic_of_surjective` (LMFDB `group.isoclinism`): `G` and `H` are isoclinic.
* `Group.isIsoclinic_quotient` (LMFDB `group.isoclinism`): `G` is isoclinic to `G / N` whenever
  `N ∩ G' = 1`.
-/

open Subgroup

open scoped commutatorElement

namespace Group

variable {G H : Type*} [Group G] [Group H] {f : G →* H}

/-- **The centre under a surjection whose kernel meets the commutator subgroup trivially**: if
`f : G →* H` is surjective and `ker f ∩ G' = 1`, then the preimage of `Z(H)` is `Z(G)`. -/
lemma comap_center_eq_of_surjective (hf : Function.Surjective f) (hker : f.ker ⊓ commutator G = ⊥) :
    (center H).comap f = center G := by
  refine le_antisymm (fun g hg ↦ mem_center_iff.mpr fun x ↦ ?_)
    (map_le_iff_le_comap.mp <| map_center_le_center hf)
  have hx : ⁅x, g⁆ ∈ f.ker ⊓ commutator G := by
    refine mem_inf.mpr ⟨?_, commutator_mem_commutator (mem_top x) (mem_top g)⟩
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mem_center_iff.mp (mem_comap.mp hg) (f x)
  rwa [hker, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hx

lemma map_center_eq_of_surjective (hf : Function.Surjective f) (hker : f.ker ⊓ commutator G = ⊥) :
    (center G).map f = center H := by
  rw [← comap_center_eq_of_surjective hf hker, map_comap_eq_self_of_surjective hf]

lemma center_eq_ker_of_surjective (hf : Function.Surjective f) (hker : f.ker ⊓ commutator G = ⊥) :
    center G = ((QuotientGroup.mk' <| center H).comp f).ker := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_center_eq_of_surjective hf hker]

lemma map_mem_commutator_of_surjective (hf : Function.Surjective f) (g : commutator G) :
    f.domRestrict (commutator G) g ∈ commutator H :=
  (map_commutator_of_surjective hf).le <| mem_map_of_mem f g.2

lemma bijective_codRestrict_domRestrict_commutator (hf : Function.Surjective f)
    (hker : f.ker ⊓ commutator G = ⊥) : Function.Bijective <|
      (f.domRestrict <| commutator G).codRestrict (commutator H) <|
        map_mem_commutator_of_surjective hf := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun g hg ↦ Subtype.ext ?_, fun h ↦ ?_⟩
  · have hg' : (g : G) ∈ f.ker ⊓ commutator G := ⟨congrArg Subtype.val hg, g.2⟩
    rwa [hker, mem_bot] at hg'
  · rcases mem_map.mp <| (map_commutator_of_surjective hf).ge h.2 with ⟨g, hg, hgh⟩
    exact ⟨⟨g, hg⟩, Subtype.ext hgh⟩

namespace Isoclinism

/-- The isoclinism between `G` and `H` induced by a surjective homomorphism `f : G →* H` whose
kernel meets the commutator subgroup trivially (LMFDB `group.isoclinism`): `φ (g Z(G)) = f g Z(H)`
and `σ g = f g` for `g ∈ G'`. -/
noncomputable def ofSurjective (hf : Function.Surjective f) (hker : f.ker ⊓ commutator G = ⊥) :
    Isoclinism G H where
  centralQuotientEquiv :=
    (QuotientGroup.quotientMulEquivOfEq <| center_eq_ker_of_surjective hf hker).trans <|
      QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' <| center H).comp f) <|
        (QuotientGroup.mk'_surjective _).comp hf
  commutatorEquiv := .ofBijective _ <| bijective_codRestrict_domRestrict_commutator hf hker
  map_centralCommutatorMap x y := by
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    exact Subtype.ext <| by
      simp [QuotientGroup.quotientKerEquivOfSurjective, centralCommutatorMap_mk,
        coe_commutatorPairing]

end Isoclinism

/-- **A surjection whose kernel meets the commutator subgroup trivially is an isoclinism** (LMFDB
`group.isoclinism`). -/
lemma isIsoclinic_of_surjective (hf : Function.Surjective f) (hker : f.ker ⊓ commutator G = ⊥) :
    IsIsoclinic G H :=
  ⟨.ofSurjective hf hker⟩

/-- **A group is isoclinic to its quotient by a normal subgroup meeting the commutator subgroup
trivially** (LMFDB `group.isoclinism`). -/
lemma isIsoclinic_quotient (N : Subgroup G) [N.Normal] (hN : N ⊓ commutator G = ⊥) :
    IsIsoclinic G (G ⧸ N) :=
  isIsoclinic_of_surjective (QuotientGroup.mk'_surjective N) <| by rwa [QuotientGroup.ker_mk']

end Group
