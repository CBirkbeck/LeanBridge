import LeanBridge.ForMathlib.GroupTheory.Isoclinism.DihedralQuaternion
import LeanBridge.ForMathlib.GroupTheory.SchurMultiplier.MaximalStem
import Mathlib.Data.ZMod.QuotientGroup
import TauCeti.GroupTheory.GroupExtension.Of.Surjective

/-!
# The stem extensions of maximal size of the Klein four-group

Let `V = C₂ × C₂` (`Multiplicative (ZMod 2 × ZMod 2)`). For a stem extension `1 → K → C → V → 1`
(LMFDB `group.stem_extension`), the kernel `K` is central and lies in `C'`, and `C' ≤ K` since `V`
is abelian. Lift the generators of `V` to `x, y ∈ C`. Every element of `C` is one of `1, x, y, xy`
up to a central factor, so every commutator of `C` is one of the commutators of `1, x, y, xy`, which
are `1` and `t = ⁅x, y⁆` and `t⁻¹`; and `t² = ⁅x², y⁆ = 1` as `x²` is central. So `K = C' ≤ ⟨t⟩`
has order at most `2`. Applied to `SchurCover V`, this shows that the Schur multiplier of `V`
(LMFDB `group.schur_multiplier`) has order at most `2`, and the dihedral group `D₄`, a stem
extension of `V` with kernel of order `2`, shows that it has order `2`.

So the stem extensions of `V` by their centres given by `D₄ = DihedralGroup 4` and by the quaternion
group `Q₈ = QuaternionGroup 2` both have maximal size. Their middle groups are isoclinic
(`GroupExtension.IsMaximalStem.isIsoclinic`) but not isomorphic: in general the middle group of a
stem extension of maximal size is only determined up to isoclinism.

## Main definitions

* `DihedralGroup.reduceModTwoExtension`, `QuaternionGroup.reduceModTwoExtension`: the stem
  extensions `1 → C₂ → D₄ → C₂ × C₂ → 1` and `1 → C₂ → Q₈ → C₂ × C₂ → 1`.

## Main results

* `MonoidHom.nat_card_ker_le_two`: the kernel of a stem extension of `C₂ × C₂` has order at most
  `2`.
* `nat_card_H2_kleinFour` (LMFDB `group.schur_multiplier`): the Schur multiplier of `C₂ × C₂` has
  order `2`.
* `DihedralGroup.isMaximalStem_reduceModTwoExtension`,
  `QuaternionGroup.isMaximalStem_reduceModTwoExtension` (LMFDB `group.stem_extension`): both are
  stem extensions of maximal size.
* `GroupExtension.not_forall_nonempty_mulEquiv_of_isMaximalStem` (LMFDB `group.stem_extension`):
  the middle group of a stem extension of maximal size is not determined up to isomorphism.
-/

open Function Subgroup groupHomology

open scoped commutatorElement

namespace MonoidHom

variable {C : Type*} [Group C] {π : C →* Multiplicative (ZMod 2 × ZMod 2)}

/-- **The kernel of a stem extension of the Klein four-group has order at most `2`**: for a
surjective homomorphism `π : C →* C₂ × C₂` whose kernel lies in the centre and in the commutator
subgroup of `C`, all the commutators of `C` are powers of `⁅x, y⁆` for lifts `x, y` of the
generators, whose square is `1`. -/
lemma nat_card_ker_le_two (hπ : Surjective π) (hstem : π.ker ≤ center C ⊓ commutator C) :
    Nat.card π.ker ≤ 2 := by
  let a : Multiplicative (ZMod 2 × ZMod 2) := .ofAdd (1, 0)
  let b : Multiplicative (ZMod 2 × ZMod 2) := .ofAdd (0, 1)
  have hV : ∀ v : Multiplicative (ZMod 2 × ZMod 2), v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
    decide
  rcases le_inf_iff.mp hstem with ⟨hcen, hker⟩
  let x : C := surjInv hπ a
  let y : C := surjInv hπ b
  have hx : π x = a := surjInv_eq hπ a
  have hy : π y = b := surjInv_eq hπ b
  have ht : ⁅x, y⁆ ∈ center C := hcen <| by
    rw [mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have hx₂ : x * x ∈ center C := hcen <| by
    rw [mem_ker, map_mul, hx]
    decide
  have ht₂ : ⁅x, y⁆ ^ 2 = 1 := by
    have h₁ : ⁅x * x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp hx₂ y).symm
    have h₂ : ⁅x * x, y⁆ = x * ⁅x, y⁆ * x⁻¹ * ⁅x, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h₂, mem_center_iff.mp ht x, mul_inv_cancel_right] at h₁
    rw [sq, h₁]
  have hxxy : ⁅x, x * y⁆ = ⁅x, y⁆ := by
    have h : ⁅x, x * y⁆ = x * ⁅x, y⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h, mem_center_iff.mp ht x, mul_inv_cancel_right]
  have hyxy : ⁅y, x * y⁆ = ⁅y, x⁆ := by
    simp only [commutatorElement_def]
    group
  have hW : ∀ w₁ ∈ ({1, x, y, x * y} : Set C), ∀ w₂ ∈ ({1, x, y, x * y} : Set C),
      ⁅w₁, w₂⁆ ∈ zpowers ⁅x, y⁆ := by
    rintro w₁ (rfl | rfl | rfl | rfl) w₂ (rfl | rfl | rfl | rfl) <;>
      try simp only [commutatorElement_one_left, commutatorElement_one_right,
        commutatorElement_self, ← commutatorElement_inv x (x * y),
        ← commutatorElement_inv y (x * y), hxxy, hyxy, ← commutatorElement_inv x y, inv_inv]
    all_goals first
      | exact one_mem _
      | exact mem_zpowers _
      | exact inv_mem (mem_zpowers _)
  have hrep (g : C) : ∃ w ∈ ({1, x, y, x * y} : Set C), g * w⁻¹ ∈ π.ker := by
    rcases hV (π g) with h | h | h | h
    · exact ⟨1, by simp, by simp [h]⟩
    · exact ⟨x, by simp, by simp [h, hx]⟩
    · exact ⟨y, by simp, by simp [h, hy]⟩
    · exact ⟨x * y, by simp, by simp [h, hx, hy]⟩
  have hcomm : commutator C ≤ zpowers ⁅x, y⁆ := by
    rw [commutator_eq_closure, closure_le]
    rintro _ ⟨g, h, rfl⟩
    rcases hrep g with ⟨w₁, hw₁, h₁⟩
    rcases hrep h with ⟨w₂, hw₂, h₂⟩
    rw [Group.commutatorElement_eq_of_mul_inv_mem_center (hcen h₁) (hcen h₂)]
    exact hW w₁ hw₁ w₂ hw₂
  have : Finite (zpowers ⁅x, y⁆) :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, ht₂⟩).finite_zpowers
  refine (card_le_of_le (hker.trans hcomm)).trans ?_
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one ht₂)

end MonoidHom

lemma nat_card_kleinFour : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]

namespace DihedralGroup

lemma surjective_reduceModTwo : Surjective reduceModTwo :=
  (by decide : ∀ v : Multiplicative (ZMod 2 × ZMod 2), ∃ d : DihedralGroup 4, reduceModTwo d = v)

/-- The stem extension `1 → C₂ → D₄ → C₂ × C₂ → 1` of `DihedralGroup.reduceModTwo`, whose kernel is
the centre `{1, r 2}` of `D₄`. -/
def reduceModTwoExtension :
    GroupExtension reduceModTwo.ker (DihedralGroup 4) (Multiplicative (ZMod 2 × ZMod 2)) :=
  GroupExtension.ofSurjective surjective_reduceModTwo

lemma ker_reduceModTwo_le :
    reduceModTwo.ker ≤ center (DihedralGroup 4) ⊓ commutator (DihedralGroup 4) := by
  intro d hd
  rcases (by decide : ∀ d : DihedralGroup 4, reduceModTwo d = 1 → d = 1 ∨ d = r 2) d hd with
    rfl | rfl
  · exact one_mem _
  · refine mem_inf.mpr ⟨mem_center_iff.mpr (by decide), ?_⟩
    rw [← (by decide : ⁅(r 1 : DihedralGroup 4), sr 0⁆ = r 2)]
    exact commutator_mem_commutator (mem_top _) (mem_top _)

lemma isStem_reduceModTwoExtension : reduceModTwoExtension.IsStem := by
  rintro _ ⟨k, rfl⟩
  exact ker_reduceModTwo_le k.2

lemma nat_card_ker_reduceModTwo : Nat.card reduceModTwo.ker = 2 := by
  have h : Nat.card (DihedralGroup 4) =
      Nat.card (Multiplicative (ZMod 2 × ZMod 2)) * Nat.card reduceModTwo.ker :=
    reduceModTwoExtension.nat_card_eq_mul
  rw [DihedralGroup.nat_card, nat_card_kleinFour] at h
  omega

end DihedralGroup

namespace QuaternionGroup

lemma surjective_reduceModTwo : Surjective reduceModTwo :=
  (by decide : ∀ v : Multiplicative (ZMod 2 × ZMod 2), ∃ q : QuaternionGroup 2, reduceModTwo q = v)

/-- The stem extension `1 → C₂ → Q₈ → C₂ × C₂ → 1` of `QuaternionGroup.reduceModTwo`, whose kernel
is the centre `{1, a 2}` of `Q₈`. -/
def reduceModTwoExtension :
    GroupExtension reduceModTwo.ker (QuaternionGroup 2) (Multiplicative (ZMod 2 × ZMod 2)) :=
  GroupExtension.ofSurjective surjective_reduceModTwo

lemma ker_reduceModTwo_le :
    reduceModTwo.ker ≤ center (QuaternionGroup 2) ⊓ commutator (QuaternionGroup 2) := by
  intro q hq
  rcases (by decide : ∀ q : QuaternionGroup 2, reduceModTwo q = 1 → q = 1 ∨ q = a 2) q hq with
    rfl | rfl
  · exact one_mem _
  · refine mem_inf.mpr ⟨mem_center_iff.mpr (by decide), ?_⟩
    rw [← (by decide : ⁅(a 1 : QuaternionGroup 2), xa 0⁆ = a 2)]
    exact commutator_mem_commutator (mem_top _) (mem_top _)

lemma isStem_reduceModTwoExtension : reduceModTwoExtension.IsStem := by
  rintro _ ⟨k, rfl⟩
  exact ker_reduceModTwo_le k.2

lemma nat_card_ker_reduceModTwo : Nat.card reduceModTwo.ker = 2 := by
  have h : Nat.card (QuaternionGroup 2) =
      Nat.card (Multiplicative (ZMod 2 × ZMod 2)) * Nat.card reduceModTwo.ker :=
    reduceModTwoExtension.nat_card_eq_mul
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card, nat_card_kleinFour] at h
  omega

end QuaternionGroup

/-- **The Schur multiplier of the Klein four-group has order `2`** (LMFDB `group.schur_multiplier`):
`|H₂(C₂ × C₂, ℤ)| = 2`. It is at most `2` by `MonoidHom.nat_card_ker_le_two` applied to the Schur
cover, and at least `2` since `D₄` is a stem extension of `C₂ × C₂` with kernel of order `2`. -/
lemma nat_card_H2_kleinFour :
    Nat.card (H2 (Rep.trivial ℤ (Multiplicative (ZMod 2 × ZMod 2)) ℤ)) = 2 := by
  refine le_antisymm ?_ ?_
  · have h : Nat.card (SchurCover.extension (Multiplicative (ZMod 2 × ZMod 2))).rightHom.ker ≤ 2 :=
      (SchurCover.extension _).rightHom.nat_card_ker_le_two
        (SchurCover.extension _).rightHom_surjective fun _ hc ↦ SchurCover.isStem_extension _
          ((SchurCover.extension _).range_inl_eq_ker_rightHom.ge hc)
    rwa [GroupExtension.nat_card_ker_rightHom, Nat.card_congr Multiplicative.toAdd] at h
  · have h : Nat.card DihedralGroup.reduceModTwo.ker ≤
        Nat.card (H2 (Rep.trivial ℤ (Multiplicative (ZMod 2 × ZMod 2)) ℤ)) :=
      DihedralGroup.isStem_reduceModTwoExtension.nat_card_kernel_le
    rwa [DihedralGroup.nat_card_ker_reduceModTwo] at h

/-- **`D₄` is the middle group of a stem extension of maximal size of `C₂ × C₂`** (LMFDB
`group.stem_extension`). -/
lemma DihedralGroup.isMaximalStem_reduceModTwoExtension : reduceModTwoExtension.IsMaximalStem :=
  (GroupExtension.isMaximalStem_iff _).mpr ⟨isStem_reduceModTwoExtension,
    nat_card_ker_reduceModTwo.trans nat_card_H2_kleinFour.symm⟩

/-- **`Q₈` is the middle group of a stem extension of maximal size of `C₂ × C₂`** (LMFDB
`group.stem_extension`). -/
lemma QuaternionGroup.isMaximalStem_reduceModTwoExtension : reduceModTwoExtension.IsMaximalStem :=
  (GroupExtension.isMaximalStem_iff _).mpr ⟨isStem_reduceModTwoExtension,
    nat_card_ker_reduceModTwo.trans nat_card_H2_kleinFour.symm⟩

/-- **The middle group of a stem extension of maximal size is not determined up to isomorphism**
(LMFDB `group.stem_extension`): `D₄` and `Q₈` are the middle groups of two stem extensions of
maximal size of `C₂ × C₂`, and they are not isomorphic (they are isoclinic, by
`GroupExtension.IsMaximalStem.isIsoclinic`). -/
lemma GroupExtension.not_forall_nonempty_mulEquiv_of_isMaximalStem : ¬∀ (G : Type) [Group G]
    [Finite G] (K₁ C₁ K₂ C₂ : Type) [Group K₁] [Group C₁] [Group K₂] [Group C₂]
    (S₁ : GroupExtension K₁ C₁ G) (S₂ : GroupExtension K₂ C₂ G), S₁.IsMaximalStem →
    S₂.IsMaximalStem → Nonempty (C₁ ≃* C₂) := by
  intro h
  have : Fact (3 ≤ 3) := ⟨le_rfl⟩
  exact (DihedralGroup.isEmpty_mulEquiv_quaternionGroup (k := 3)).false <| Nonempty.some <|
    h _ _ _ _ _ DihedralGroup.reduceModTwoExtension QuaternionGroup.reduceModTwoExtension
      DihedralGroup.isMaximalStem_reduceModTwoExtension
      QuaternionGroup.isMaximalStem_reduceModTwoExtension
