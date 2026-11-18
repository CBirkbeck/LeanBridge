import LeanBridge.ForMathlib.GroupTheory.Isoclinism.Surjective
import LeanBridge.ForMathlib.GroupTheory.SchurMultiplier.SchurCover
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.IsPerfect
import TauCeti.GroupTheory.GroupExtension.Basic

/-!
# Stem extensions of maximal size

Let `G` be a finite group, with Schur multiplier `M(G) = H₂(G, ℤ)` (Mathlib's
`groupHomology (Rep.trivial ℤ G ℤ) 2`, LMFDB `group.schur_multiplier`). For a stem extension
`1 → K → C → G → 1` (LMFDB `group.stem_extension`), the homomorphism `H₂(G, ℤ) → K ∩ C' = K` of
`MonoidHom.H2ToKerInfCommutator` is onto: `K` is a quotient of `M(G)`. So `C` is finite and
`|C| = |G| |K| ≤ |G| |M(G)|`: for a fixed `G` the order of `C` is bounded. The bound is attained by
the Schur cover `SchurCover G`, whose kernel is `M(G)`. Hence a stem extension has `C` of maximal
size exactly when `|K| = |M(G)|`, and then `H₂(G, ℤ) → K` is an isomorphism.

Two stem extensions of maximal size have isoclinic middle groups `C₁` and `C₂` (LMFDB
`group.isoclinism`). Their fibre product `P` over `G` is a central extension of `G` by `K₁ × K₂`,
so its kernel meets `P'` in a quotient of `M(G)`. The first projection maps this intersection onto
`K₁ ≅ M(G)`, as `K₁ ≤ C₁'` is the image of the part of `P'` over `K₁`; so it is injective there,
and the kernel `1 × K₂` of the projection `P → C₁` meets `P'` trivially. By
`Group.isIsoclinic_of_surjective` the group `P` is isoclinic to `C₁`, and in the same way to `C₂`.
When `G` is perfect (LMFDB `group.perfect`), so are `C₁` and `C₂`, and both projections map `P'`
isomorphically onto them: `C₁ ≅ C₂`.

## Main definitions

* `GroupExtension.IsStem.H2ToKernel`: the homomorphism `H₂(G, ℤ) → K` of a stem extension.
* `GroupExtension.IsMaximalStem`: a stem extension of `G` whose middle group has the largest order
  among the stem extensions of `G`.
* `GroupExtension.pullback`: the fibre product of two extensions of `G`.

## Main results

* `MonoidHom.nat_card_ker_inf_commutator_le` (LMFDB `group.stem_extension`): for a central
  extension `π : C → G` of a finite group, `|ker π ∩ C'| ≤ |M(G)|`.
* `GroupExtension.IsStem.surjective_H2ToKernel` (LMFDB `group.schur_multiplier`,
  `group.stem_extension`): the kernel of a stem extension is a quotient of the Schur multiplier.
* `GroupExtension.IsStem.nat_card_kernel_le` (LMFDB `group.schur_multiplier`,
  `group.stem_extension`): for a finite group `G`, the kernel of a stem extension has order at most
  `|M(G)|`.
* `GroupExtension.IsStem.finite`, `GroupExtension.IsStem.nat_card_le` (LMFDB
  `group.stem_extension`): for a finite group `G`, the middle group `C` of a stem extension is
  finite and `|C| ≤ |G| |M(G)|`.
* `SchurCover.nat_card` (LMFDB `group.stem_extension`): `|SchurCover G| = |G| |M(G)|`.
* `GroupExtension.isMaximalStem_iff` (LMFDB `group.stem_extension`): a stem extension has maximal
  size exactly when `|K| = |M(G)|`.
* `GroupExtension.IsMaximalStem.bijective_H2ToKernel` (LMFDB `group.stem_extension`,
  `group.schur_multiplier`): the kernel of a stem extension of maximal size is isomorphic to the
  Schur multiplier.
* `SchurCover.isMaximalStem_extension` (LMFDB `group.stem_extension`, `group.schur_multiplier`):
  the Schur cover is a stem extension of maximal size.
* `GroupExtension.IsMaximalStem.isIsoclinic` (LMFDB `group.stem_extension`): the middle groups of
  two stem extensions of maximal size are isoclinic.
* `GroupExtension.IsStem.isPerfect`: the middle group of a stem extension of a perfect group is
  perfect.
* `GroupExtension.IsMaximalStem.nonempty_mulEquiv` (LMFDB `group.stem_extension`): for a perfect
  group the middle groups of two stem extensions of maximal size are isomorphic.

## References

* I. Schur, *Über die Darstellung der endlichen Gruppen durch gebrochene lineare Substitutionen*,
  J. Reine Angew. Math. 127 (1904), 20–50.
* I. Schur, *Untersuchungen über die Darstellung der endlichen Gruppen durch gebrochene lineare
  Substitutionen*, J. Reine Angew. Math. 132 (1907), 85–137.
* G. Karpilovsky, *The Schur Multiplier*, London Mathematical Society Monographs 2, Oxford
  University Press (1987), Ch. 2 and 3.
-/

open Function Group Subgroup groupHomology

variable {G : Type} [Group G] {K C P K₁ C₁ K₂ C₂ : Type*} [Group K] [Group C] [Group P] [Group K₁]
  [Group C₁] [Group K₂] [Group C₂] {S : GroupExtension K C G} (S₁ : GroupExtension K₁ C₁ G)
  (S₂ : GroupExtension K₂ C₂ G)

namespace MonoidHom

variable [Finite G] in
/-- **The kernel of a central extension of a finite group meets the commutator subgroup in a group
of order at most that of the Schur multiplier**: `|ker π ∩ C'| ≤ |H₂(G, ℤ)|` for a surjective
homomorphism `π : C →* G` with central kernel (LMFDB `group.stem_extension`). -/
lemma nat_card_ker_inf_commutator_le (π : C →* G) (hπ : π.ker ≤ center C) (hsurj : Surjective π) :
    Nat.card ↥(π.ker ⊓ commutator C) ≤ Nat.card (H2 (Rep.trivial ℤ G ℤ)) :=
  (Nat.card_congr Additive.ofMul).trans_le <| Nat.card_le_card_of_surjective _ <|
    π.surjective_H2ToKerInfCommutator hπ (surjInv hsurj) (surjInv_eq hsurj)

variable [Finite G] [Finite P] in
lemma ker_inf_commutator_eq_bot {π : C →* G} {p : P →* C} (hsurj : Surjective π) (hp : Surjective p)
    (hπ : (π.comp p).ker ≤ center P) (hstem : π.ker ≤ commutator C)
    (hcard : Nat.card (H2 (Rep.trivial ℤ G ℤ)) ≤ Nat.card π.ker) : p.ker ⊓ commutator P = ⊥ := by
  let f : ↥((π.comp p).ker ⊓ commutator P) → π.ker := fun y ↦ ⟨p y, (mem_inf.mp y.2).1⟩
  have hf : Surjective f := by
    rintro ⟨k, hk⟩
    rcases mem_map.mp ((map_commutator_of_surjective hp).ge (hstem hk)) with ⟨y, hy, rfl⟩
    exact ⟨⟨y, mem_inf.mpr ⟨hk, hy⟩⟩, rfl⟩
  have hinj : Injective f := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf, le_antisymm
    (((π.comp p).nat_card_ker_inf_commutator_le hπ (hsurj.comp hp)).trans hcard)
    (Nat.card_le_card_of_surjective f hf)⟩).1
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  rcases mem_inf.mp hx with ⟨(hx₁ : p x = 1), hx₂⟩
  have hxN : x ∈ (π.comp p).ker ⊓ commutator P :=
    mem_inf.mpr ⟨by rw [mem_ker, comp_apply, hx₁, map_one], hx₂⟩
  exact mem_bot.mpr <| congrArg Subtype.val <| hinj (a₁ := ⟨x, hxN⟩) (a₂ := 1) <|
    Subtype.ext <| hx₁.trans (map_one p).symm

end MonoidHom

variable [IsPerfect C] in
lemma Group.bijective_comp_subtype_commutator {p : P →* C} (hp : Surjective p)
    (hker : p.ker ⊓ commutator P = ⊥) : Bijective (p.comp (commutator P).subtype) :=
  ((MulEquiv.subgroupCongr IsPerfect.commutator_eq_top).trans topEquiv).bijective.comp <|
    bijective_codRestrict_domRestrict_commutator hp hker

namespace GroupExtension

variable (S) in
lemma nat_card_ker_rightHom : Nat.card S.rightHom.ker = Nat.card K :=
  S.card_fiber_rightHom 1

lemma nat_card_eq_mul (E : GroupExtension K C G) : Nat.card C = Nat.card G * Nat.card K := by
  rw [card_eq_card_quotient_mul_card_subgroup E.rightHom.ker, nat_card_ker_rightHom,
    Nat.card_congr E.quotientKerRightHomEquivRight.toEquiv]

namespace IsStem

lemma ker_rightHom_le_center (hS : S.IsStem) : S.rightHom.ker ≤ center C :=
  S.range_inl_eq_ker_rightHom ▸ fun _ hx ↦ (mem_inf.mp (hS hx)).1

lemma ker_rightHom_le_commutator (hS : S.IsStem) : S.rightHom.ker ≤ commutator C :=
  S.range_inl_eq_ker_rightHom ▸ fun _ hx ↦ (mem_inf.mp (hS hx)).2

lemma ker_rightHom_inf_commutator (hS : S.IsStem) :
    S.rightHom.ker ⊓ commutator C = S.rightHom.ker :=
  inf_eq_left.mpr hS.ker_rightHom_le_commutator

/-- The homomorphism `H₂(G, ℤ) → K` of a stem extension `1 → K → C → G → 1`: the homomorphism
`MonoidHom.H2ToKerInfCommutator` onto `ker (C → G) ∩ C' = K` of a section of `C → G`. -/
noncomputable def H2ToKernel (hS : S.IsStem) : H2 (Rep.trivial ℤ G ℤ) →+ Additive K :=
  letI e : ↥(S.rightHom.ker ⊓ commutator C) ≃* K := (MulEquiv.subgroupCongr <|
    hS.ker_rightHom_inf_commutator.trans S.range_inl_eq_ker_rightHom.symm).trans
      (MonoidHom.ofInjective S.inl_injective).symm
  (MulEquiv.toAdditive e).toAddMonoidHom.comp <| S.rightHom.H2ToKerInfCommutator
    hS.ker_rightHom_le_center (surjInv S.rightHom_surjective) (surjInv_eq S.rightHom_surjective)

/-- **The kernel of a stem extension is a quotient of the Schur multiplier** (LMFDB
`group.schur_multiplier`, `group.stem_extension`): for a stem extension `1 → K → C → G → 1` of any
group `G`, the homomorphism `H₂(G, ℤ) → K` is surjective. -/
lemma surjective_H2ToKernel (hS : S.IsStem) : Surjective hS.H2ToKernel := by
  rw [H2ToKernel, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom]
  exact (MulEquiv.toAdditive _).surjective.comp (S.rightHom.surjective_H2ToKerInfCommutator _ _ _)

variable [Finite G]

/-- **The kernel of a stem extension of a finite group has order at most that of the Schur
multiplier** (LMFDB `group.schur_multiplier`, `group.stem_extension`): `|K| ≤ |H₂(G, ℤ)|` for every
stem extension `1 → K → C → G → 1`. -/
lemma nat_card_kernel_le (hS : S.IsStem) : Nat.card K ≤ Nat.card (H2 (Rep.trivial ℤ G ℤ)) := by
  have h : Nat.card ↥(S.rightHom.ker ⊓ commutator C) ≤ Nat.card (H2 (Rep.trivial ℤ G ℤ)) :=
    S.rightHom.nat_card_ker_inf_commutator_le hS.ker_rightHom_le_center S.rightHom_surjective
  rwa [hS.ker_rightHom_inf_commutator, nat_card_ker_rightHom] at h

/-- **The middle group of a stem extension of a finite group is finite** (LMFDB
`group.stem_extension`): its kernel is a quotient of the finite Schur multiplier. -/
lemma finite (hS : S.IsStem) : Finite C := by
  have : Finite (Additive K) := Finite.of_surjective _ hS.surjective_H2ToKernel
  have : Finite K := Finite.of_equiv _ Additive.toMul
  exact Nat.finite_of_card_ne_zero <| by
    rw [S.nat_card_eq_mul]
    exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-- **For a fixed finite group `G`, the order of the middle group of a stem extension is bounded**
(LMFDB `group.stem_extension`): `|C| ≤ |G| |H₂(G, ℤ)|` for every stem extension
`1 → K → C → G → 1`, whose middle group `C` is finite (`GroupExtension.IsStem.finite`). The bound
is attained by `SchurCover G` (`SchurCover.nat_card`). -/
lemma nat_card_le (hS : S.IsStem) :
    Nat.card C ≤ Nat.card G * Nat.card (H2 (Rep.trivial ℤ G ℤ)) := by
  rw [S.nat_card_eq_mul]
  exact Nat.mul_le_mul_left _ hS.nat_card_kernel_le

end IsStem

end GroupExtension

variable (G) in
/-- **The order of the Schur cover** (LMFDB `group.stem_extension`):
`|SchurCover G| = |G| |H₂(G, ℤ)|`. -/
lemma SchurCover.nat_card :
    Nat.card (SchurCover G) = Nat.card G * Nat.card (H2 (Rep.trivial ℤ G ℤ)) :=
  (SchurCover.extension G).nat_card_eq_mul.trans <| by rw [Nat.card_congr Multiplicative.toAdd]

namespace GroupExtension

variable (S) in
/-- A stem extension `1 → K → C → G → 1` **of maximal size** (LMFDB `group.stem_extension`): a stem
extension whose middle group `C` has the largest order among the middle groups of the stem
extensions of `G`. Only the stem extensions with `K' C' : Type` are compared, which loses nothing
for a finite group `G`: by `GroupExtension.isMaximalStem_iff` the condition says
`|K| = |H₂(G, ℤ)|`, and `|G| |H₂(G, ℤ)|` bounds the middle groups in every universe. -/
def IsMaximalStem : Prop :=
  S.IsStem ∧ ∀ (K' C' : Type) [Group K'] [Group C'] (S' : GroupExtension K' C' G), S'.IsStem →
    Nat.card C' ≤ Nat.card C

variable (S) [Finite G] in
/-- **A stem extension has maximal size exactly when its kernel has the order of the Schur
multiplier** (LMFDB `group.stem_extension`), for a finite group `G`. -/
lemma isMaximalStem_iff :
    S.IsMaximalStem ↔ S.IsStem ∧ Nat.card K = Nat.card (H2 (Rep.trivial ℤ G ℤ)) := by
  refine ⟨fun ⟨hS, hmax⟩ ↦ ⟨hS, le_antisymm hS.nat_card_kernel_le ?_⟩,
    fun ⟨hS, hK⟩ ↦ ⟨hS, fun K' C' _ _ S' hS' ↦ ?_⟩⟩
  · have h : Nat.card (SchurCover G) ≤ Nat.card C :=
      hmax _ _ (SchurCover.extension G) (SchurCover.isStem_extension G)
    rw [SchurCover.nat_card G, S.nat_card_eq_mul] at h
    exact Nat.le_of_mul_le_mul_left h Nat.card_pos
  · rw [S.nat_card_eq_mul, hK]
    exact hS'.nat_card_le

variable [Finite G] in
/-- **The kernel of a stem extension of maximal size is the Schur multiplier** (LMFDB
`group.stem_extension`, `group.schur_multiplier`): for a stem extension `1 → K → C → G → 1` of a
finite group `G` whose middle group `C` has maximal size, the homomorphism `H₂(G, ℤ) → K` is an
isomorphism. -/
lemma IsMaximalStem.bijective_H2ToKernel (h : S.IsMaximalStem) : Bijective h.1.H2ToKernel :=
  (Nat.bijective_iff_surjective_and_card _).mpr ⟨h.1.surjective_H2ToKernel,
    (S.isMaximalStem_iff.mp h).2.symm.trans (Nat.card_congr Additive.ofMul)⟩

/-- The fibre product of two extensions of `G`: the subgroup of the pairs `(c₁, c₂)` of `C₁ × C₂`
with the same image in `G`. -/
def pullback : Subgroup (C₁ × C₂) :=
  (S₁.rightHom.comp (MonoidHom.fst C₁ C₂)).eqLocus (S₂.rightHom.comp (MonoidHom.snd C₁ C₂))

lemma mem_pullback {x : C₁ × C₂} : x ∈ S₁.pullback S₂ ↔ S₁.rightHom x.1 = S₂.rightHom x.2 :=
  Iff.rfl

lemma surjective_pullback_fst :
    Surjective ((MonoidHom.fst C₁ C₂).comp (S₁.pullback S₂).subtype) := by
  intro c₁
  rcases S₂.rightHom_surjective (S₁.rightHom c₁) with ⟨c₂, hc₂⟩
  exact ⟨⟨(c₁, c₂), hc₂.symm⟩, rfl⟩

lemma surjective_pullback_snd :
    Surjective ((MonoidHom.snd C₁ C₂).comp (S₁.pullback S₂).subtype) := by
  intro c₂
  rcases S₁.rightHom_surjective (S₂.rightHom c₂) with ⟨c₁, hc₁⟩
  exact ⟨⟨(c₁, c₂), hc₁⟩, rfl⟩

lemma ker_pullback_le_center (h₁ : S₁.rightHom.ker ≤ center C₁) (h₂ : S₂.rightHom.ker ≤ center C₂) :
    ((S₁.rightHom.comp (MonoidHom.fst C₁ C₂)).comp (S₁.pullback S₂).subtype).ker ≤
      center (S₁.pullback S₂) := by
  intro x hx
  have hx₁ : x.1.1 ∈ S₁.rightHom.ker := hx
  have hx₂ : x.1.2 ∈ S₂.rightHom.ker := by
    rw [MonoidHom.mem_ker, ← (mem_pullback S₁ S₂).mp x.2]
    exact hx
  refine mem_center_iff.mpr fun y ↦ Subtype.ext <| Prod.ext ?_ ?_
  · exact mem_center_iff.mp (h₁ hx₁) y.1.1
  · exact mem_center_iff.mp (h₂ hx₂) y.1.2

variable {S₁ S₂} [Finite G] in
lemma IsMaximalStem.ker_pullback_fst_inf_commutator_eq_bot (h₁ : S₁.IsMaximalStem)
    (h₂ : S₂.IsMaximalStem) : ((MonoidHom.fst C₁ C₂).comp (S₁.pullback S₂).subtype).ker ⊓
      commutator (S₁.pullback S₂) = ⊥ := by
  have : Finite C₁ := h₁.1.finite
  have : Finite C₂ := h₂.1.finite
  exact MonoidHom.ker_inf_commutator_eq_bot S₁.rightHom_surjective (S₁.surjective_pullback_fst S₂)
    (S₁.ker_pullback_le_center S₂ h₁.1.ker_rightHom_le_center h₂.1.ker_rightHom_le_center)
    h₁.1.ker_rightHom_le_commutator
    (by rw [S₁.nat_card_ker_rightHom, (S₁.isMaximalStem_iff.mp h₁).2])

variable {S₁ S₂} [Finite G] in
lemma IsMaximalStem.ker_pullback_snd_inf_commutator_eq_bot (h₁ : S₁.IsMaximalStem)
    (h₂ : S₂.IsMaximalStem) : ((MonoidHom.snd C₁ C₂).comp (S₁.pullback S₂).subtype).ker ⊓
      commutator (S₁.pullback S₂) = ⊥ := by
  have : Finite C₁ := h₁.1.finite
  have : Finite C₂ := h₂.1.finite
  have h : S₂.rightHom.comp ((MonoidHom.snd C₁ C₂).comp (S₁.pullback S₂).subtype) =
      S₁.rightHom.comp ((MonoidHom.fst C₁ C₂).comp (S₁.pullback S₂).subtype) :=
    MonoidHom.ext fun x ↦ ((mem_pullback S₁ S₂).mp x.2).symm
  exact MonoidHom.ker_inf_commutator_eq_bot S₂.rightHom_surjective (S₁.surjective_pullback_snd S₂)
    (h ▸ S₁.ker_pullback_le_center S₂ h₁.1.ker_rightHom_le_center h₂.1.ker_rightHom_le_center)
    h₂.1.ker_rightHom_le_commutator
    (by rw [S₂.nat_card_ker_rightHom, (S₂.isMaximalStem_iff.mp h₂).2])

variable {S₁ S₂} [Finite G] in
/-- **The middle groups of two stem extensions of maximal size are isoclinic** (LMFDB
`group.stem_extension`, `group.isoclinism`): for stem extensions `1 → Kᵢ → Cᵢ → G → 1` of a finite
group `G` whose middle groups have maximal size, `C₁` and `C₂` are isoclinic, through the fibre
product `GroupExtension.pullback`. -/
lemma IsMaximalStem.isIsoclinic (h₁ : S₁.IsMaximalStem) (h₂ : S₂.IsMaximalStem) :
    IsIsoclinic C₁ C₂ :=
  (isIsoclinic_of_surjective (S₁.surjective_pullback_fst S₂)
    (h₁.ker_pullback_fst_inf_commutator_eq_bot h₂)).symm.trans <|
      isIsoclinic_of_surjective (S₁.surjective_pullback_snd S₂)
        (h₁.ker_pullback_snd_inf_commutator_eq_bot h₂)

variable [IsPerfect G] in
/-- **The middle group of a stem extension of a perfect group is perfect**: `C = C' K` since `G` is
perfect, and `K ≤ C'`. -/
lemma IsStem.isPerfect (hS : S.IsStem) : IsPerfect C := by
  refine ⟨eq_top_iff.mpr fun c _ ↦ ?_⟩
  have hc : S.rightHom c ∈ (commutator C).map S.rightHom := by
    rw [map_commutator_of_surjective S.rightHom_surjective, IsPerfect.commutator_eq_top]
    exact mem_top _
  rcases mem_map.mp hc with ⟨y, hy, hyc⟩
  have hk : y⁻¹ * c ∈ commutator C := hS.ker_rightHom_le_commutator <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyc, inv_mul_cancel]
  simpa using mul_mem hy hk

variable {S₁ S₂} [Finite G] [IsPerfect G] in
/-- **For a perfect group, the middle groups of two stem extensions of maximal size are isomorphic**
(LMFDB `group.stem_extension`): for stem extensions `1 → Kᵢ → Cᵢ → G → 1` of a finite perfect group
`G` whose middle groups have maximal size, `C₁ ≅ C₂`; both are isomorphic to the commutator
subgroup of the fibre product `GroupExtension.pullback`. -/
lemma IsMaximalStem.nonempty_mulEquiv (h₁ : S₁.IsMaximalStem) (h₂ : S₂.IsMaximalStem) :
    Nonempty (C₁ ≃* C₂) := by
  have : IsPerfect C₁ := h₁.1.isPerfect
  have : IsPerfect C₂ := h₂.1.isPerfect
  exact ⟨(MulEquiv.ofBijective _ (bijective_comp_subtype_commutator (S₁.surjective_pullback_fst S₂)
    (h₁.ker_pullback_fst_inf_commutator_eq_bot h₂))).symm.trans (MulEquiv.ofBijective _
      (bijective_comp_subtype_commutator (S₁.surjective_pullback_snd S₂)
        (h₁.ker_pullback_snd_inf_commutator_eq_bot h₂)))⟩

end GroupExtension

namespace SchurCover

variable (G) [Finite G] in
/-- **The Schur cover is a stem extension of maximal size** (LMFDB `group.stem_extension`,
`group.schur_multiplier`): its middle group `SchurCover G` has the largest order among the stem
extensions of the finite group `G`, and its kernel is the Schur multiplier `H₂(G, ℤ)`. -/
lemma isMaximalStem_extension : (extension G).IsMaximalStem :=
  (GroupExtension.isMaximalStem_iff _).mpr ⟨isStem_extension G, Nat.card_congr Multiplicative.toAdd⟩

end SchurCover
