import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.AGroupClosure
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.MetabelianExamples
import LeanBridge.ForMathlib.GroupTheory.SupersolvableClosure
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import TauCeti.RepresentationTheory.CharacterTable.Solvable

/-!
# Examples and non-examples of supersolvable groups

The LMFDB's knowl on supersolvable groups (LMFDB `group.supersolvable`) names `A₄`, `S₄`,
`SL₂(𝔽₃)` and `C₂ × A₄` as solvable groups that are not supersolvable, and states that
supersolvable groups are not closed under extensions, that not every supersolvable group is
nilpotent, and that not every supersolvable group is metacyclic. This file proves these
statements, together with the example of a Z-group that is not cyclic (LMFDB `group.z_group`).

A group `G` is not supersolvable as soon as, for some proper normal subgroup `Z`, no `x ∉ Z` has
all its conjugates in `⟨x⟩ Z`. For `A₄`, with `Z = 1`, and for `SL₂(𝔽₃)`, with `Z` the centre
`{±1}`, this is a finite check, done by `decide`.

## Main results

* `Group.not_isSupersolvable_of_forall_exists_conj_ne`: the criterion above.
* `alternatingGroup.not_isSupersolvable_fin_four`, `Equiv.Perm.not_isSupersolvable_fin_four`,
  `Matrix.SpecialLinearGroup.not_isSupersolvable_fin_two_zmod_three`,
  `not_isSupersolvable_prod_alternatingGroup_fin_four` (LMFDB `group.supersolvable`): `A₄`, `S₄`,
  `SL₂(𝔽₃)` and `C₂ × A₄` are not supersolvable.
* `Matrix.SpecialLinearGroup.isSolvable_fin_two_zmod_three`: `SL₂(𝔽₃)` is solvable.
* `alternatingGroup.isAGroup_fin_four`: `A₄` is an A-group.
* `Group.not_forall_isSupersolvable_of_isSolvable` (LMFDB `group.supersolvable`): not all
  solvable groups are supersolvable.
* `Group.not_forall_isSupersolvable_of_isSupersolvable_quotient` (LMFDB `group.supersolvable`):
  supersolvable groups are not closed under extensions.
* `DihedralGroup.isSupersolvable`: the dihedral groups are supersolvable.
* `Group.not_forall_isNilpotent_of_isSupersolvable` (LMFDB `group.supersolvable`): not every
  supersolvable group is nilpotent.
* `Group.not_forall_isMetacyclic_of_isSupersolvable` (LMFDB `group.supersolvable`): not every
  supersolvable group is metacyclic.
* `DihedralGroup.isZGroup_three`, `DihedralGroup.not_isCyclic_three`,
  `not_forall_isCyclic_of_isZGroup` (LMFDB `group.z_group`): `D₃ ≅ S₃` is a Z-group that is not
  cyclic, so not every finite Z-group is cyclic.
-/

open Equiv Matrix Subgroup TauCeti

open scoped MatrixGroups

private lemma squarefree_six : Squarefree 6 :=
  (Nat.squarefree_mul_iff (m := 2) (n := 3)).mpr
    ⟨by decide, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩

namespace Group

variable {G : Type*} [Group G]

/-- **A criterion for a group not to be supersolvable**: let `Z` be a proper normal subgroup of
`G` such that every `x ∉ Z` has a conjugate outside `⟨x⟩ Z`; here `xⁿ = 1` for all `x`, so that
`⟨x⟩ Z` consists of the `xᵏ z` with `k < n` and `z ∈ Z`. Then `G` is not supersolvable. -/
lemma not_isSupersolvable_of_forall_exists_conj_ne {n : ℕ} [NeZero n] (hn : ∀ x : G, x ^ n = 1)
    {Z : Subgroup G} [Z.Normal] (hZ : Z ≠ ⊤)
    (h : ∀ x ∉ Z, ∃ g : G, ∀ k : Fin n, ∀ z ∈ Z, x ^ (k : ℕ) * z ≠ g * x * g⁻¹) :
    ¬IsSupersolvable G := by
  intro hG
  rcases (hG.quotient Z).exists_notMem_normal_zpowers_sup hZ with ⟨x, hx, hxn⟩
  rcases h x hx with ⟨g, hg⟩
  rcases exists_zpow_mul_eq_of_mem_sup (normalizer_eq_top_iff.mpr ‹Z.Normal› ▸ mem_top x)
    (hxn.conj_mem x (mem_sup_left <| mem_zpowers x) g) with ⟨m, z, hz, hm⟩
  have hm0 : 0 ≤ m % (n : ℤ) := Int.emod_nonneg m <| Nat.cast_ne_zero.mpr <| NeZero.ne n
  refine hg ⟨(m % (n : ℤ)).toNat, ?_⟩ z hz ?_
  · exact (Int.toNat_lt hm0).mpr <| Int.emod_lt_of_pos m <| Nat.cast_pos.mpr <| NeZero.pos n
  · rw [← hm, zpow_eq_zpow_emod m (n := n) (by rw [zpow_natCast, hn]), ← zpow_natCast,
      Int.toNat_of_nonneg hm0]

end Group

namespace alternatingGroup

/-- **The alternating group `A₄` is not supersolvable** (LMFDB `group.supersolvable`): it has no
nontrivial cyclic normal subgroup. -/
lemma not_isSupersolvable_fin_four : ¬Group.IsSupersolvable (alternatingGroup (Fin 4)) := by
  have hd : ∀ x : alternatingGroup (Fin 4), x ≠ 1 → ∃ g : alternatingGroup (Fin 4),
      ∀ k : Fin 12, x ^ (k : ℕ) ≠ g * x * g⁻¹ := by
    decide +kernel
  have hn : ∀ x : alternatingGroup (Fin 4), x ^ 12 = 1 := by
    decide +kernel
  refine Group.not_isSupersolvable_of_forall_exists_conj_ne hn bot_ne_top fun x hx ↦ ?_
  rcases hd x fun h ↦ hx <| h ▸ one_mem _ with ⟨g, hg⟩
  exact ⟨g, fun k z hz ↦ by simpa [mem_bot.mp hz] using hg k⟩

lemma nat_card_fin_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

instance : Group.IsSolvable (alternatingGroup (Fin 4)) :=
  isSolvable <| by simp

/-- **The alternating group `A₄` is an A-group** (LMFDB `group.a_group`): its order `12` is
cube-free. -/
lemma isAGroup_fin_four : IsAGroup (alternatingGroup (Fin 4)) := by
  refine IsAGroup.of_forall_not_pow_three_dvd_card fun p hp hdvd ↦ ?_
  rw [nat_card_fin_four] at hdvd
  have hp2 : p ≤ 2 := by
    by_contra hp3
    have h27 : 3 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h12 : p ^ 3 ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h2 : p = 2 := le_antisymm hp2 hp.two_le
  rw [h2] at hdvd
  omega

end alternatingGroup

namespace Equiv.Perm

/-- **The symmetric group `S₄` is not supersolvable** (LMFDB `group.supersolvable`), since its
subgroup `A₄` is not. -/
lemma not_isSupersolvable_fin_four : ¬Group.IsSupersolvable (Perm (Fin 4)) :=
  fun h ↦ alternatingGroup.not_isSupersolvable_fin_four <| h.subgroup _

end Equiv.Perm

/-- **The group `C₂ × A₄` is not supersolvable** (LMFDB `group.supersolvable`), since its quotient
`A₄` is not. -/
lemma not_isSupersolvable_prod_alternatingGroup_fin_four :
    ¬Group.IsSupersolvable (Multiplicative (ZMod 2) × alternatingGroup (Fin 4)) :=
  fun h ↦ alternatingGroup.not_isSupersolvable_fin_four <|
    h.of_surjective (f := MonoidHom.snd _ _) Prod.snd_surjective

namespace Matrix.SpecialLinearGroup

lemma nat_card_fin_two_zmod_three : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- **The group `SL₂(𝔽₃)` is solvable** (LMFDB `group.supersolvable`), its order being
`24 = 2³ · 3`, by Burnside's theorem. -/
lemma isSolvable_fin_two_zmod_three : Group.IsSolvable SL(2, ZMod 3) :=
  isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three (a := 3) (b := 1)
    nat_card_fin_two_zmod_three

/-- **The group `SL₂(𝔽₃)` is not supersolvable** (LMFDB `group.supersolvable`): no cyclic subgroup
of its quotient by the centre `{±1}` is normal and nontrivial. -/
lemma not_isSupersolvable_fin_two_zmod_three : ¬Group.IsSupersolvable SL(2, ZMod 3) := by
  have hc : ∀ z : SL(2, ZMod 3), (∀ g : SL(2, ZMod 3), g * z = z * g) → z = 1 ∨ z = -1 := by
    decide +kernel
  have hd : ∀ x : SL(2, ZMod 3), x ≠ 1 → x ≠ -1 → ∃ g : SL(2, ZMod 3), ∀ k : Fin 12,
      x ^ (k : ℕ) ≠ g * x * g⁻¹ ∧ x ^ (k : ℕ) * -1 ≠ g * x * g⁻¹ := by
    decide +kernel
  have hn : ∀ x : SL(2, ZMod 3), x ^ 12 = 1 := by
    decide +kernel
  have h1 : ∀ g : SL(2, ZMod 3), g * -1 = -1 * g :=
    fun g ↦ (mul_neg_one g).trans (neg_one_mul g).symm
  have hx : ∃ x : SL(2, ZMod 3), x ≠ 1 ∧ x ≠ -1 := by
    decide +kernel
  refine Group.not_isSupersolvable_of_forall_exists_conj_ne hn (Z := center SL(2, ZMod 3))
    (fun htop ↦ ?_) fun x hx ↦ ?_
  · rcases hx with ⟨x, hx1, hx2⟩
    rcases hc x <| Subgroup.mem_center_iff.mp <| htop ▸ mem_top x with h | h
    exacts [hx1 h, hx2 h]
  · rcases hd x (fun h ↦ hx <| h ▸ one_mem _) fun h ↦ hx <| h ▸ Subgroup.mem_center_iff.mpr h1
      with ⟨g, hg⟩
    refine ⟨g, fun k z hz ↦ ?_⟩
    rcases hc z <| Subgroup.mem_center_iff.mp hz with rfl | rfl
    · simpa using (hg k).1
    · exact (hg k).2

end Matrix.SpecialLinearGroup

namespace Group

/-- **Not all solvable groups are supersolvable** (LMFDB `group.supersolvable`): the alternating
group `A₄` is solvable but not supersolvable. -/
lemma not_forall_isSupersolvable_of_isSolvable :
    ¬∀ (G : Type) [Group G] [Finite G], IsSolvable G → IsSupersolvable G :=
  fun h ↦ alternatingGroup.not_isSupersolvable_fin_four <| h _ inferInstance

/-- **Supersolvable groups are not closed under extensions** (LMFDB `group.supersolvable`), even
among finite groups: the alternating group `A₄` has a normal subgroup of prime index, of order `4`
or `6` and therefore supersolvable, with supersolvable quotient, but `A₄` is not supersolvable. -/
lemma not_forall_isSupersolvable_of_isSupersolvable_quotient : ¬∀ (G : Type) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal], IsSupersolvable N → IsSupersolvable (G ⧸ N) →
    IsSupersolvable G := by
  intro h
  have : Nontrivial (alternatingGroup (Fin 4)) := Finite.one_lt_card_iff_nontrivial.mp <| by
    rw [alternatingGroup.nat_card_fin_four]
    norm_num
  rcases IsSolvable.exists_normal_index_prime (alternatingGroup (Fin 4)) with ⟨N, hN, hp⟩
  have hcard : Nat.card N * N.index = 12 :=
    N.card_mul_index.trans alternatingGroup.nat_card_fin_four
  have hN4 : IsSupersolvable N := by
    rcases (⟨_, rfl⟩ : ∃ p, N.index = p) with ⟨p, hpN⟩
    rw [hpN] at hp hcard
    have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) <| Dvd.intro_left _ hcard
    have h46 : Nat.card N = 2 ^ 2 ∨ Nat.card N = 6 := by
      interval_cases p <;> first | omega | exact absurd hp (by decide)
    rcases h46 with h4 | h6
    · have : IsMulCommutative N := IsPGroup.isMulCommutative_of_card_eq_prime_sq h4
      exact isSupersolvable_of_isMulCommutative
    · exact isSupersolvable_of_squarefree_card <| h6 ▸ squarefree_six
  have : Fact (Nat.Prime N.index) := ⟨hp⟩
  have : IsCyclic (alternatingGroup (Fin 4) ⧸ N) := isCyclic_of_prime_card N.index_eq_card.symm
  exact alternatingGroup.not_isSupersolvable_fin_four <|
    h _ N hN4 isSupersolvable_of_isMulCommutative

end Group

namespace DihedralGroup

/-- **The dihedral groups are supersolvable** (LMFDB `group.supersolvable`), being metacyclic. -/
lemma isSupersolvable (n : ℕ) : Group.IsSupersolvable (DihedralGroup n) :=
  have : IsMetacyclic (DihedralGroup n) := isMetacyclic n
  IsMetacyclic.isSupersolvable

/-- **The dihedral group `D₃ ≅ S₃` is a Z-group** (LMFDB `group.z_group`): its order `6` is
squarefree. -/
lemma isZGroup_three : IsZGroup (DihedralGroup 3) :=
  IsZGroup.of_squarefree <| nat_card (n := 3) ▸ squarefree_six

/-- **The dihedral group `D₃ ≅ S₃` is not cyclic** (LMFDB `group.z_group`): it is not even
nilpotent. -/
lemma not_isCyclic_three : ¬IsCyclic (DihedralGroup 3) :=
  fun _ ↦ not_isNilpotent ⟨1, rfl⟩ (by decide) inferInstance

end DihedralGroup

/-- **Not every finite Z-group is cyclic** (LMFDB `group.z_group`): the dihedral group `D₃ ≅ S₃`
is a Z-group but is not cyclic. -/
lemma not_forall_isCyclic_of_isZGroup :
    ¬∀ (G : Type) [Group G] [Finite G], IsZGroup G → IsCyclic G :=
  fun h ↦ DihedralGroup.not_isCyclic_three <| h _ DihedralGroup.isZGroup_three

namespace Group

/-- **Not every supersolvable group is nilpotent** (LMFDB `group.supersolvable`): the dihedral
group `D₃ ≅ S₃` is supersolvable but not nilpotent. -/
lemma not_forall_isNilpotent_of_isSupersolvable :
    ¬∀ (G : Type) [Group G] [Finite G], IsSupersolvable G → IsNilpotent G :=
  fun h ↦ DihedralGroup.not_isNilpotent ⟨1, rfl⟩ (by decide) <| h _ <|
    DihedralGroup.isSupersolvable 3

/-- **Not every supersolvable group is metacyclic** (LMFDB `group.supersolvable`): the elementary
abelian group `C₂³` is abelian, hence supersolvable, but not metacyclic. -/
lemma not_forall_isMetacyclic_of_isSupersolvable :
    ¬∀ (G : Type) [Group G] [Finite G], IsSupersolvable G → IsMetacyclic G :=
  fun h ↦ not_isMetacyclic_elementaryAbelian_two_three <| h _ isSupersolvable_of_isMulCommutative

end Group
