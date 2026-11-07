import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Complements of the kernel of a group extension and splittings

A group `E` is an extension of `G` by `N` (LMFDB `group.nonsplit_product`) if it has a normal
subgroup isomorphic to `N` with quotient isomorphic to `G`; equivalently there is a short exact
sequence `1 → N → E → G → 1`, Mathlib's `GroupExtension N E G` (`nonempty_groupExtension_iff`).
The extension is split if the image of `N` has a complement `K` in `E` (`K ∩ N = 1` and `KN = E`),
and non-split otherwise. We prove that the complements of `N` are exactly the ranges of the
splittings `G →* E` of the extension, the homomorphic sections of the projection `E → G`
(`GroupExtension.Splitting`), so that `N` has a complement if and only if the extension splits;
every complement is isomorphic to `G` through the projection.

For a normal subgroup `H` of `G` (LMFDB `group.subgroup.complement`) this applies to the extension
`1 → H → G → G ⧸ H → 1`, `Subgroup.groupExtension`. A complement in the LMFDB's sense, a subgroup
`K` with `|H ∩ K| = 1` and `HK = G`, is Mathlib's `Subgroup.IsComplement' H K`.

## Main definitions

* `GroupExtension.complementMulEquiv` (LMFDB `group.nonsplit_product`): the isomorphism `K ≃* G`
  of a complement `K` of `N` with the quotient.
* `GroupExtension.splittingOfIsComplement'` (LMFDB `group.nonsplit_product`): the splitting with
  range a given complement.
* `Subgroup.groupExtension` (LMFDB `group.subgroup.complement`): the extension
  `1 → H → G → G ⧸ H → 1` of a normal subgroup `H`.

## Main results

* `nonempty_groupExtension_iff` (LMFDB `group.nonsplit_product`): there is a short exact sequence
  `1 → N → E → G → 1` if and only if `E` has a normal subgroup isomorphic to `N` with quotient
  isomorphic to `G`.
* `GroupExtension.isComplement'_range_inl_iff` (LMFDB `group.nonsplit_product`): the complements
  of `N` are the ranges of the splittings.
* `GroupExtension.exists_isComplement'_iff_nonempty_splitting` (LMFDB `group.nonsplit_product`):
  `N` has a complement if and only if the extension splits.
* `Subgroup.isComplement'_iff_disjoint_and_mul_eq_univ` (LMFDB `group.nonsplit_product`): `K` is a
  complement of `H` if and only if `H ∩ K = 1` and `HK = G`.
* `SemidirectProduct.isComplement'_range_inl_range_inr`: semidirect products are split extensions.
* `Subgroup.isComplement'_iff_card_inf_eq_one_and_mul_eq_univ` (LMFDB
  `group.subgroup.complement`): `K` is a complement of `H` if and only if `|H ∩ K| = 1` and
  `HK = G`.
* `Subgroup.isComplement'_iff_exists_splitting` (LMFDB `group.subgroup.complement`): the
  complements of a normal subgroup `H` are the ranges of the splittings `G ⧸ H →* G`.
* `Subgroup.exists_isComplement'_iff_nonempty_splitting` (LMFDB `group.subgroup.complement`): a
  normal subgroup `H` has a complement if and only if `1 → H → G → G ⧸ H → 1` splits.
-/

open Subgroup

open scoped Pointwise

variable {N E G : Type*} [Group N] [Group E] [Group G]

namespace Subgroup

variable {H K : Subgroup G}

/-- **Complements by intersection and product** (LMFDB `group.nonsplit_product`): `K` is a
complement of `H` if and only if `H ∩ K = 1` and `HK = G`. -/
lemma isComplement'_iff_disjoint_and_mul_eq_univ :
    H.IsComplement' K ↔ Disjoint H K ∧ (H : Set G) * (K : Set G) = Set.univ :=
  ⟨fun h ↦ ⟨h.disjoint, h.mul_eq⟩, fun h ↦ isComplement'_of_disjoint_and_mul_eq_univ h.1 h.2⟩

/-- **A complement in the sense of the LMFDB** (`group.subgroup.complement`): `K` is a complement
of `H` if and only if `|H ∩ K| = 1` and `HK = G`. -/
lemma isComplement'_iff_card_inf_eq_one_and_mul_eq_univ : H.IsComplement' K ↔
    Nat.card (H ⊓ K : Subgroup G) = 1 ∧ (H : Set G) * (K : Set G) = Set.univ := by
  rw [isComplement'_iff_disjoint_and_mul_eq_univ, card_eq_one, disjoint_iff]

end Subgroup

/-- **An extension is a normal subgroup with its quotient** (LMFDB `group.nonsplit_product`):
there is a short exact sequence `1 → N → E → G → 1` if and only if `E` has a normal subgroup
isomorphic to `N` with quotient isomorphic to `G`. -/
lemma nonempty_groupExtension_iff : Nonempty (GroupExtension N E G) ↔
    ∃ (M : Subgroup E) (_ : M.Normal), Nonempty (M ≃* N) ∧ Nonempty (E ⧸ M ≃* G) := by
  refine ⟨fun ⟨S⟩ ↦ ⟨S.inl.range, inferInstance, ⟨(MonoidHom.ofInjective S.inl_injective).symm⟩,
    ⟨S.quotientRangeInlEquivRight⟩⟩, ?_⟩
  rintro ⟨M, hM, ⟨e₁⟩, ⟨e₂⟩⟩
  refine ⟨⟨M.subtype.comp e₁.symm.toMonoidHom, e₂.toMonoidHom.comp (QuotientGroup.mk' M),
    M.subtype_injective.comp e₁.symm.injective, ?_,
    e₂.surjective.comp (QuotientGroup.mk'_surjective M)⟩⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨?_, fun hx ↦ ⟨e₁ ⟨x, hx⟩, by simp⟩⟩
  rintro ⟨n, rfl⟩
  exact (e₁.symm n).2

namespace GroupExtension

variable (S : GroupExtension N E G) {K : Subgroup E}

/-- The **isomorphism `K ≃* G`** of a complement `K` of `N` in `E` with the quotient `G` of an
extension `1 → N → E → G → 1` (LMFDB `group.nonsplit_product`): the restriction of the projection
`E → G` to `K`, through Mathlib's isomorphism `E ⧸ N ≃* K` of the quotient with a complement. -/
noncomputable def complementMulEquiv (hK : S.inl.range.IsComplement' K) : K ≃* G :=
  hK.symm.QuotientMulEquiv.symm.trans S.quotientRangeInlEquivRight

lemma complementMulEquiv_apply (hK : S.inl.range.IsComplement' K) (k : K) :
    S.complementMulEquiv hK k = S.rightHom k :=
  rfl

/-- The **splitting** `G →* E` of an extension `1 → N → E → G → 1` whose range is a given
complement `K` of `N` (LMFDB `group.nonsplit_product`): the inverse of the isomorphism
`K ≃* G`. -/
noncomputable def splittingOfIsComplement' (hK : S.inl.range.IsComplement' K) : S.Splitting where
  toMonoidHom := K.subtype.comp (S.complementMulEquiv hK).symm.toMonoidHom
  rightInverse_rightHom := (S.complementMulEquiv hK).apply_symm_apply

lemma range_splittingOfIsComplement' (hK : S.inl.range.IsComplement' K) :
    (S.splittingOfIsComplement' hK).toMonoidHom.range = K := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨S.complementMulEquiv hK ⟨x, hx⟩, ?_⟩⟩
  · rintro ⟨g, rfl⟩
    exact ((S.complementMulEquiv hK).symm g).2
  · simp [splittingOfIsComplement']

variable {S} in
lemma Splitting.isComplement'_range (s : S.Splitting) :
    S.inl.range.IsComplement' s.toMonoidHom.range := by
  refine isComplement'_of_disjoint_and_mul_eq_univ ?_ <| Set.eq_univ_of_forall fun e ↦
    Set.mem_mul.mpr ⟨e * (s (S.rightHom e))⁻¹, ?_, s (S.rightHom e), ⟨_, rfl⟩,
      inv_mul_cancel_right _ _⟩
  · rw [disjoint_def]
    rintro _ hx ⟨g, rfl⟩
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker] at hx
    rw [(s.rightHom_splitting g).symm.trans hx, map_one]
  · rw [SetLike.mem_coe, S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
      s.rightHom_splitting, mul_inv_cancel]

/-- **The complements of `N` are the ranges of the splittings** (LMFDB `group.nonsplit_product`):
for an extension `1 → N → E → G → 1`, a subgroup `K` of `E` is a complement of the image of `N` if
and only if it is the range of a homomorphic section `G →* E` of the projection. -/
lemma isComplement'_range_inl_iff :
    S.inl.range.IsComplement' K ↔ ∃ s : S.Splitting, s.toMonoidHom.range = K :=
  ⟨fun hK ↦ ⟨S.splittingOfIsComplement' hK, S.range_splittingOfIsComplement' hK⟩,
    fun ⟨s, hs⟩ ↦ hs ▸ s.isComplement'_range⟩

/-- **A split extension is one with a splitting** (LMFDB `group.nonsplit_product`): the image of
`N` has a complement in `E` if and only if the projection `E → G` has a homomorphic section. -/
lemma exists_isComplement'_iff_nonempty_splitting :
    (∃ K : Subgroup E, S.inl.range.IsComplement' K) ↔ Nonempty S.Splitting :=
  ⟨fun ⟨_, hK⟩ ↦ ⟨S.splittingOfIsComplement' hK⟩, fun ⟨s⟩ ↦ ⟨_, s.isComplement'_range⟩⟩

end GroupExtension

/-- **Semidirect products are split extensions**: the image of `G` in `N ⋊[φ] G` is a complement
of the image of `N`. -/
lemma SemidirectProduct.isComplement'_range_inl_range_inr (φ : G →* MulAut N) :
    (SemidirectProduct.inl : N →* N ⋊[φ] G).range.IsComplement' SemidirectProduct.inr.range :=
  (SemidirectProduct.inr_splitting φ).isComplement'_range

namespace Subgroup

variable (H : Subgroup G) [H.Normal] {K : Subgroup G}

/-- The **extension `1 → H → G → G ⧸ H → 1`** of `G ⧸ H` by a normal subgroup `H` of `G` (LMFDB
`group.subgroup.complement`): the inclusion of `H` and the quotient map. Tau Ceti's
`GroupExtension.ofSurjective` is the same extension with the kernel of the quotient map in place of
`H`. -/
def groupExtension : GroupExtension H G (G ⧸ H) where
  inl := H.subtype
  rightHom := QuotientGroup.mk' H
  inl_injective := H.subtype_injective
  range_inl_eq_ker_rightHom := by rw [range_subtype, QuotientGroup.ker_mk']
  rightHom_surjective := QuotientGroup.mk'_surjective H

lemma range_inl_groupExtension : H.groupExtension.inl.range = H :=
  range_subtype H

variable {H} in
/-- **The complements of a normal subgroup are the images of the splittings** (LMFDB
`group.subgroup.complement`): `K` is a complement of a normal subgroup `H` if and only if it is the
range of a splitting `G ⧸ H →* G` of `1 → H → G → G ⧸ H → 1`. -/
lemma isComplement'_iff_exists_splitting :
    H.IsComplement' K ↔ ∃ s : H.groupExtension.Splitting, s.toMonoidHom.range = K := by
  rw [← H.groupExtension.isComplement'_range_inl_iff, range_inl_groupExtension]

/-- **A normal subgroup has a complement if and only if the extension splits** (LMFDB
`group.subgroup.complement`). -/
lemma exists_isComplement'_iff_nonempty_splitting :
    (∃ K : Subgroup G, H.IsComplement' K) ↔ Nonempty H.groupExtension.Splitting := by
  rw [← H.groupExtension.exists_isComplement'_iff_nonempty_splitting, range_inl_groupExtension]

end Subgroup
