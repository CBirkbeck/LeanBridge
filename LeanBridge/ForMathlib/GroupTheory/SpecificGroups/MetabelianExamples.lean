import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Metabelian
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Metacyclic
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# Metacyclic, dihedral, dicyclic and nilpotent of class two groups are metabelian

Metabelian groups include the metacyclic groups, among them the dihedral groups and the
(generalised) quaternion groups, and the groups whose commutator subgroup is central, among them
the extraspecial groups (LMFDB `group.metabelian`). The converse of 'metacyclic implies
metabelian' fails: the elementary abelian group `C₂³` is abelian, hence metabelian, but not
metacyclic, since a metacyclic group of exponent `2` has order at most `4`.

## Main results

* `IsMetacyclic.isMetabelian` (LMFDB `group.metabelian`): metacyclic groups are metabelian.
* `DihedralGroup.isMetacyclic`, `DihedralGroup.isMetabelian` (LMFDB `group.metabelian`): the
  dihedral groups are metacyclic, hence metabelian.
* `QuaternionGroup.isMetacyclic`, `QuaternionGroup.isMetabelian` (LMFDB `group.metabelian`): the
  dicyclic groups, the generalised quaternion groups among them, are metacyclic, hence metabelian.
* `isMetabelian_of_commutator_le_center` (LMFDB `group.metabelian`): a group whose commutator
  subgroup is central, such as an extraspecial group, is metabelian.
* `IsMetacyclic.nat_card_le_four_of_forall_sq_eq_one` (LMFDB `group.metabelian`): a metacyclic
  group of exponent dividing `2` has order at most `4`.
* `not_isMetacyclic_elementaryAbelian_two_three` (LMFDB `group.metabelian`): `C₂³` is metabelian
  but not metacyclic.
-/

open Subgroup TauCeti

variable {G : Type*} [Group G]

/-- **Metacyclic groups are metabelian** (LMFDB `group.metabelian`): a cyclic normal subgroup with
cyclic quotient is an abelian normal subgroup with abelian quotient. -/
lemma IsMetacyclic.isMetabelian [h : IsMetacyclic G] : IsMetabelian G := by
  rcases h.exists_normal with ⟨N, hN, hNc, hQc⟩
  exact (isMetabelian_iff_exists_normal G).mpr ⟨N, hN, ⟨⟨IsCyclic.commGroup.mul_comm⟩⟩,
    ⟨⟨IsCyclic.commGroup.mul_comm⟩⟩⟩

private lemma isMetacyclic_of_index_eq_two {N : Subgroup G} [hN : N.Normal] [IsCyclic N]
    (h : N.index = 2) : IsMetacyclic G :=
  ⟨N, hN, inferInstance, isCyclic_of_prime_card (p := 2) (N.index_eq_card ▸ h)⟩

/-- **The dihedral groups are metacyclic** (LMFDB `group.metabelian`): the rotations form a cyclic
normal subgroup of index `2`. -/
lemma DihedralGroup.isMetacyclic (n : ℕ) : IsMetacyclic (DihedralGroup n) :=
  have : IsCyclic (dihedralRotations n) :=
    isCyclic_of_surjective (dihedralRotationsMulEquiv n).symm.toMonoidHom
      (dihedralRotationsMulEquiv n).symm.surjective
  isMetacyclic_of_index_eq_two (index_dihedralRotations n)

/-- **The dihedral groups are metabelian** (LMFDB `group.metabelian`). -/
lemma DihedralGroup.isMetabelian (n : ℕ) : IsMetabelian (DihedralGroup n) :=
  have : IsMetacyclic (DihedralGroup n) := DihedralGroup.isMetacyclic n
  IsMetacyclic.isMetabelian

/-- **The dicyclic groups are metacyclic** (LMFDB `group.metabelian`), the generalised quaternion
groups among them: the rotations form a cyclic normal subgroup of index `2`. -/
lemma QuaternionGroup.isMetacyclic (n : ℕ) : IsMetacyclic (QuaternionGroup n) :=
  isMetacyclic_of_index_eq_two (index_quaternionRotations n)

/-- **The dicyclic groups are metabelian** (LMFDB `group.metabelian`), the generalised quaternion
groups among them. -/
lemma QuaternionGroup.isMetabelian (n : ℕ) : IsMetabelian (QuaternionGroup n) :=
  have : IsMetacyclic (QuaternionGroup n) := QuaternionGroup.isMetacyclic n
  IsMetacyclic.isMetabelian

/-- **A group whose commutator subgroup is central is metabelian** (LMFDB `group.metabelian`); this
covers the extraspecial groups, whose commutator subgroup is their centre. -/
lemma isMetabelian_of_commutator_le_center (h : commutator G ≤ center G) : IsMetabelian G :=
  ⟨⟨⟨fun x y ↦ Subtype.ext (mem_center_iff.mp (h y.2) x)⟩⟩⟩

private lemma nat_card_le_two_of_isCyclic {H : Type*} [Group H] [IsCyclic H]
    (h : ∀ g : H, g ^ 2 = 1) : Nat.card H ≤ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd two_pos (Monoid.exponent_dvd_of_forall_pow_eq_one h)

/-- **A metacyclic group of exponent dividing `2` has order at most `4`** (LMFDB
`group.metabelian`): both the cyclic normal subgroup and the cyclic quotient have order at most
`2`. -/
lemma IsMetacyclic.nat_card_le_four_of_forall_sq_eq_one [h : IsMetacyclic G]
    (h2 : ∀ g : G, g ^ 2 = 1) : Nat.card G ≤ 4 := by
  rcases h.exists_normal with ⟨N, hN, hNc, hQc⟩
  have h₁ : Nat.card N ≤ 2 := nat_card_le_two_of_isCyclic fun g ↦ Subtype.ext (by simp [h2])
  have h₂ : Nat.card (G ⧸ N) ≤ 2 := nat_card_le_two_of_isCyclic fun g ↦ by
    induction g using QuotientGroup.induction_on with
    | H g => rw [← QuotientGroup.mk_pow, h2, QuotientGroup.mk_one]
  rw [N.card_eq_card_quotient_mul_card_subgroup]
  nlinarith

/-- **`C₂³` is not metacyclic** (LMFDB `group.metabelian`), although it is abelian, hence
metabelian: the converse of `IsMetacyclic.isMetabelian` fails. -/
lemma not_isMetacyclic_elementaryAbelian_two_three :
    ¬IsMetacyclic (Multiplicative (Fin 3 → ZMod 2)) := fun h ↦ by
  have h4 := h.nat_card_le_four_of_forall_sq_eq_one fun g ↦ by
    refine Multiplicative.toAdd.injective (funext fun i ↦ ?_)
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]
  simp [Nat.card_eq_fintype_card] at h4
