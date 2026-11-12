import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import TauCeti.GroupTheory.TriangleGroup.Polyhedral

/-!
# `PSL(2, 5)` is the alternating group `A₅`

The LMFDB writes `SL(2, 5) = C₂.A₅` (knowl `group.perfect`): `SL(2, 5)` has a normal subgroup
of order `2` with quotient `A₅`. That subgroup is the centre `{±1}`, and the quotient
`PSL(2, 5) = SL(2, 5) / {±1}` is isomorphic to `A₅`.

The isomorphism comes from the presentation `⟨x, y, z | x², y³, z⁵, zyx⟩` of `A₅` as the
icosahedral triangle group `Δ(2, 3, 5)` (Tau Ceti's `TauCeti.TriangleGroup.equivIcosahedral`).
In `SL(2, 5)` the matrices `S = !![0, -1; 1, 0]`, `T = !![0, -1; 1, 1]` and `U = !![1, 0; 1, 1]`
satisfy `S² = T³ = UTS = -1` and `U⁵ = 1`, so their classes in `PSL(2, 5)` define a homomorphism
`Δ(2, 3, 5) →* PSL(2, 5)`. It is injective, as `Δ(2, 3, 5) ≅ A₅` is simple and `S` is not
central, and so bijective, both groups having order `60`.

## Main definitions

* `Matrix.ProjectiveSpecialLinearGroup.icosahedralHom`: the homomorphism `Δ(2, 3, 5) →* PSL(2, 5)`.
* `Matrix.ProjectiveSpecialLinearGroup.twoZModFiveEquivAlternatingGroup` (LMFDB `group.perfect`):
  the isomorphism `PSL(2, 5) ≃* A₅`.

## Main results

* `Matrix.SpecialLinearGroup.center_two_zmod_five` (LMFDB `group.perfect`): the centre of
  `SL(2, 5)` is `{±1}`.
* `Matrix.SpecialLinearGroup.card_center_two_zmod_five` (LMFDB `group.perfect`): the centre of
  `SL(2, 5)` has order `2`.

## References

* J. H. Conway, R. T. Curtis, S. P. Norton, R. A. Parker and R. A. Wilson, *ATLAS of Finite
  Groups*, Clarendon Press, Oxford, 1985, for the notation `2.A₅` and the isomorphism
  `A₅ ≅ L₂(5)`.
* H. S. M. Coxeter and W. O. J. Moser, *Generators and Relations for Discrete Groups*, 4th ed.,
  Springer, 1980, for the presentation of `A₅`.
-/

open Subgroup TauCeti

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

lemma neg_one_mem_center_two_zmod_five : (-1 : SL(2, ZMod 5)) ∈ center SL(2, ZMod 5) :=
  Subgroup.mem_center_iff.mpr fun B ↦ by rw [mul_neg_one, neg_one_mul]

lemma mem_center_two_zmod_five_iff {A : SL(2, ZMod 5)} :
    A ∈ center SL(2, ZMod 5) ↔ A = 1 ∨ A = -1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases SpecialLinearGroup.mem_center_iff.mp h with ⟨r, hr, hA⟩
    have key : ∀ r : ZMod 5, r ^ Fintype.card (Fin 2) = 1 → r = 1 ∨ r = -1 := by
      decide
    rcases key r hr with rfl | rfl
    · exact .inl <| Subtype.ext <| hA.symm.trans <| by decide
    · exact .inr <| Subtype.ext <| hA.symm.trans <| by decide
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact neg_one_mem_center_two_zmod_five

/-- **The centre of `SL(2, 5)` is `{±1}`** (LMFDB `group.perfect`). -/
lemma center_two_zmod_five : center SL(2, ZMod 5) = zpowers (-1) := by
  refine le_antisymm (fun A hA ↦ ?_) (zpowers_le.mpr neg_one_mem_center_two_zmod_five)
  rcases mem_center_two_zmod_five_iff.mp hA with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _

/-- **The centre of `SL(2, 5)` has order `2`** (LMFDB `group.perfect`): it is the `C₂` of
`SL(2, 5) = C₂.A₅`. -/
lemma card_center_two_zmod_five : Nat.card (center SL(2, ZMod 5)) = 2 := by
  rw [center_two_zmod_five, Nat.card_zpowers]
  exact orderOf_eq_prime (by decide) (by decide)

lemma card_two_zmod_five : Nat.card SL(2, ZMod 5) = 120 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [card_SL_field, Fin.prod_univ_two, ZMod.card]
  rfl

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

variable {A : SL(2, ZMod 5)}

lemma card_two_zmod_five : Nat.card PSL(2, ZMod 5) = 60 := by
  have h : Nat.card SL(2, ZMod 5) = Nat.card PSL(2, ZMod 5) * Nat.card (center SL(2, ZMod 5)) :=
    card_eq_card_quotient_mul_card_subgroup _
  rw [SpecialLinearGroup.card_two_zmod_five, SpecialLinearGroup.card_center_two_zmod_five] at h
  omega

lemma coe_eq_one_iff_two_zmod_five : (A : PSL(2, ZMod 5)) = 1 ↔ A = 1 ∨ A = -1 :=
  (QuotientGroup.eq_one_iff A).trans SpecialLinearGroup.mem_center_two_zmod_five_iff

private lemma coe_pow_eq_one {n : ℕ} (h : A ^ n = 1 ∨ A ^ n = -1) : (A : PSL(2, ZMod 5)) ^ n = 1 :=
  coe_eq_one_iff_two_zmod_five.mpr h

private lemma coe_mul_mul_eq_one {B C : SL(2, ZMod 5)} (h : A * B * C = 1 ∨ A * B * C = -1) :
    (A : PSL(2, ZMod 5)) * B * C = 1 :=
  coe_eq_one_iff_two_zmod_five.mpr h

/-- The matrix `S = !![0, -1; 1, 0]` of `SL(2, 5)`, with `S² = -1`. -/
private def s : SL(2, ZMod 5) :=
  ⟨!![0, -1; 1, 0], by decide⟩

/-- The matrix `T = !![0, -1; 1, 1]` of `SL(2, 5)`, with `T³ = -1`. -/
private def t : SL(2, ZMod 5) :=
  ⟨!![0, -1; 1, 1], by decide⟩

/-- The matrix `U = !![1, 0; 1, 1]` of `SL(2, 5)`, with `U⁵ = 1` and `UTS = -1`. -/
private def u : SL(2, ZMod 5) :=
  ⟨!![1, 0; 1, 1], by decide⟩

/-- The homomorphism from the icosahedral triangle group `Δ(2, 3, 5) = ⟨x, y, z | x², y³, z⁵, zyx⟩`
to `PSL(2, 5)` sending `x`, `y` and `z` to the classes of `!![0, -1; 1, 0]`, `!![0, -1; 1, 1]` and
`!![1, 0; 1, 1]`. It is bijective. -/
def icosahedralHom : TriangleGroup 2 3 5 →* PSL(2, ZMod 5) :=
  TriangleGroup.lift s t u (coe_pow_eq_one (by decide)) (coe_pow_eq_one (by decide))
    (coe_pow_eq_one (by decide)) (coe_mul_mul_eq_one (by decide))

lemma injective_icosahedralHom : Function.Injective icosahedralHom := by
  have : IsSimpleGroup (TriangleGroup 2 3 5) := TriangleGroup.equivIcosahedral.isSimpleGroup
  refine icosahedralHom.ker_eq_bot_iff.mp <|
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal icosahedralHom.ker).resolve_right fun h ↦ ?_
  have hx : TriangleGroup.x 2 3 5 ∈ icosahedralHom.ker := h ▸ mem_top _
  rw [MonoidHom.mem_ker, icosahedralHom, TriangleGroup.lift_x, coe_eq_one_iff_two_zmod_five] at hx
  exact absurd hx (by decide)

lemma bijective_icosahedralHom : Function.Bijective icosahedralHom :=
  injective_icosahedralHom.bijective_of_nat_card_le
    (card_two_zmod_five.trans TriangleGroup.natCard_two_three_five.symm).le

/-- **`PSL(2, 5)` is isomorphic to the alternating group `A₅`** (LMFDB `group.perfect`), so that
`SL(2, 5) = C₂.A₅`, the centre of `SL(2, 5)` being `{±1}`. It is the inverse of `icosahedralHom`
followed by Tau Ceti's isomorphism `TauCeti.TriangleGroup.equivIcosahedral` of `Δ(2, 3, 5)` with
`A₅`: it maps the classes of `!![0, -1; 1, 0]` and `!![0, -1; 1, 1]` to `(0 1)(2 3)` and
`(0 4 2)`. -/
noncomputable def twoZModFiveEquivAlternatingGroup : PSL(2, ZMod 5) ≃* alternatingGroup (Fin 5) :=
  (MulEquiv.ofBijective icosahedralHom bijective_icosahedralHom).symm.trans
    TriangleGroup.equivIcosahedral

@[simp]
lemma twoZModFiveEquivAlternatingGroup_icosahedralHom (g : TriangleGroup 2 3 5) :
    twoZModFiveEquivAlternatingGroup (icosahedralHom g) = TriangleGroup.equivIcosahedral g :=
  congrArg TriangleGroup.equivIcosahedral <|
    (MulEquiv.ofBijective icosahedralHom bijective_icosahedralHom).symm_apply_apply g

end Matrix.ProjectiveSpecialLinearGroup
