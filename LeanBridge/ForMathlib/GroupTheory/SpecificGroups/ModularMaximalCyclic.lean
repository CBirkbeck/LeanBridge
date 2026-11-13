import Mathlib.Algebra.Group.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.LinearCombination

/-!
# The other-dihedral and semi-dihedral groups

For `k ≥ 3` the groups `OD_{2^k}` (the modular group `M_{2^k}`) and `SD_{2^k}` (the quasidihedral
group) are the semidirect products `C_{2^{k-1}} ⋊ C_2` in which the generator of `C_2` acts on
`C_{2^{k-1}}` by `x ↦ x^{2^{k-2}+1}` and `x ↦ x^{2^{k-2}-1}`. Both have order `2^k`; for `k ≥ 4`
they are non-abelian with a cyclic subgroup of index 2, and distinct from the dihedral and
generalised quaternion groups, which is the range used by the LMFDB.

## Main definitions

* `zmodPowHom`: the homomorphism `C_n → G` sending the generator to `x`, for `x ^ n = 1`.
* `ZMod.unitPowMulAut`: the action of `C_m` on `C_n` through a unit `u` of `ZMod n` with
  `u ^ m = 1`.
* `ZMod.involutionMulAut`: its case `m = 2`, the action of `C_2` on `C_n` through a unit `u` of
  `ZMod n` with `u ^ 2 = 1`.
* `OtherDihedralGroup` (LMFDB `group.other_dihedral`).
* `SemiDihedralGroup` (LMFDB `group.semi_dihedral`).
-/

open Multiplicative

/-- The homomorphism `C_n → G` sending the generator to `x`, for `x ^ n = 1`. -/
def zmodPowHom {G : Type*} [Group G] {n : ℕ} [NeZero n] (x : G) (hx : x ^ n = 1) :
    Multiplicative (ZMod n) →* G where
  toFun k := x ^ k.toAdd.val
  map_one' := by simp
  map_mul' a b := by rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

namespace ZMod

variable {m n : ℕ} (u : (ZMod n)ˣ) (v : Multiplicative (ZMod n)) [NeZero m]

/-- The automorphism `x ↦ x ^ u` of the cyclic group `Multiplicative (ZMod n)`, for a unit `u` of
`ZMod n`. -/
def unitMulAut : MulAut (Multiplicative (ZMod n)) :=
  AddEquiv.toMultiplicative <| DistribMulAction.toAddAut (ZMod n)ˣ (ZMod n) u

lemma unitMulAut_apply : unitMulAut u v = ofAdd (u * v.toAdd) :=
  rfl

lemma unitMulAut_pow_apply (k : ℕ) :
    (unitMulAut u ^ k) v = ofAdd ((u ^ k : (ZMod n)ˣ) * v.toAdd) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, unitMulAut_apply, pow_succ', Units.val_mul, mul_assoc]
    rfl

/-- The action of `C_m = Multiplicative (ZMod m)` on `C_n = Multiplicative (ZMod n)` in which the
generator acts by `v ↦ v ^ u`, for a unit `u` of `ZMod n` with `u ^ m = 1`. -/
def unitPowMulAut (hu : u ^ m = 1) :
    Multiplicative (ZMod m) →* MulAut (Multiplicative (ZMod n)) :=
  zmodPowHom (unitMulAut u) <| MulEquiv.ext fun v ↦ by
    rw [unitMulAut_pow_apply, hu, Units.val_one, one_mul]
    rfl

lemma unitPowMulAut_apply (hu : u ^ m = 1) (k : Multiplicative (ZMod m)) :
    unitPowMulAut u hu k v = ofAdd ((u ^ k.toAdd.val : (ZMod n)ˣ) * v.toAdd) :=
  unitMulAut_pow_apply u v _

/-- The action of `C_2 = Multiplicative (ZMod 2)` on `C_n = Multiplicative (ZMod n)` in which the
generator acts by `x ↦ x ^ u`, for a unit `u` of `ZMod n` with `u ^ 2 = 1`: the case `m = 2` of
`ZMod.unitPowMulAut`. -/
def involutionMulAut (hu : u ^ 2 = 1) :
    Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod n)) :=
  unitPowMulAut u hu

/-- The unit `2 ^ (k - 2) + 1` of `ZMod (2 ^ (k - 1))`, whose square is `1` when `k ≥ 3`. -/
def otherDihedralUnit (k : ℕ) [Fact (3 ≤ k)] : (ZMod (2 ^ (k - 1)))ˣ :=
  .mkOfMulEqOne (2 ^ (k - 2) + 1) (2 ^ (k - 2) + 1) <| by
    rcases Nat.exists_eq_add_of_le (Fact.out : 3 ≤ k) with ⟨j, rfl⟩
    rw [show 3 + j - 1 = j + 2 by omega, show 3 + j - 2 = j + 1 by omega]
    have h : (2 : ZMod (2 ^ (j + 2))) ^ (j + 2) = 0 := by
      exact_mod_cast natCast_self (2 ^ (j + 2))
    linear_combination (2 ^ j + 1 : ZMod (2 ^ (j + 2))) * h

/-- The unit `2 ^ (k - 2) - 1` of `ZMod (2 ^ (k - 1))`, whose square is `1` when `k ≥ 3`. -/
def semiDihedralUnit (k : ℕ) [Fact (3 ≤ k)] : (ZMod (2 ^ (k - 1)))ˣ :=
  .mkOfMulEqOne (2 ^ (k - 2) - 1) (2 ^ (k - 2) - 1) <| by
    rcases Nat.exists_eq_add_of_le (Fact.out : 3 ≤ k) with ⟨j, rfl⟩
    rw [show 3 + j - 1 = j + 2 by omega, show 3 + j - 2 = j + 1 by omega]
    have h : (2 : ZMod (2 ^ (j + 2))) ^ (j + 2) = 0 := by
      exact_mod_cast natCast_self (2 ^ (j + 2))
    linear_combination (2 ^ j - 1 : ZMod (2 ^ (j + 2))) * h

variable (k : ℕ) [Fact (3 ≤ k)]

lemma otherDihedralUnit_pow_two : otherDihedralUnit k ^ 2 = 1 :=
  Units.ext <| (pow_two _).trans (Units.mul_inv _)

lemma semiDihedralUnit_pow_two : semiDihedralUnit k ^ 2 = 1 :=
  Units.ext <| (pow_two _).trans (Units.mul_inv _)

end ZMod

open ZMod

variable (k : ℕ) [Fact (3 ≤ k)]

/-- The **other-dihedral group** `OD_{2^k}` (LMFDB `group.other_dihedral`), also called the
modular group `M_{2^k}`: the semidirect product `C_{2^{k-1}} ⋊ C_2` in which the generator of
`C_2` acts on `C_{2^{k-1}}` by `x ↦ x^{2^{k-2}+1}`, with presentation
`⟨r, s | r^{2^{k-1}} = s^2 = 1, srs = r^{2^{k-2}+1}⟩`. It is defined for `k ≥ 3`; the LMFDB uses
it for `k ≥ 4`, since `OD_8` is the dihedral group of order `8`. -/
abbrev OtherDihedralGroup : Type :=
  Multiplicative (ZMod (2 ^ (k - 1))) ⋊[involutionMulAut _ (otherDihedralUnit_pow_two k)]
    Multiplicative (ZMod 2)

/-- The **semi-dihedral group** `SD_{2^k}` (LMFDB `group.semi_dihedral`), also called the
quasidihedral group: the semidirect product `C_{2^{k-1}} ⋊ C_2` in which the generator of `C_2`
acts on `C_{2^{k-1}}` by `x ↦ x^{2^{k-2}-1}`, with presentation
`⟨r, s | r^{2^{k-1}} = s^2 = 1, srs = r^{2^{k-2}-1}⟩`. It is defined for `k ≥ 3`; the LMFDB uses
it for `k ≥ 4`, since `SD_8` is abelian. -/
abbrev SemiDihedralGroup : Type :=
  Multiplicative (ZMod (2 ^ (k - 1))) ⋊[involutionMulAut _ (semiDihedralUnit_pow_two k)]
    Multiplicative (ZMod 2)

private lemma card_semidirectProduct
    (φ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod (2 ^ (k - 1))))) :
    Nat.card (Multiplicative (ZMod (2 ^ (k - 1))) ⋊[φ] Multiplicative (ZMod 2)) = 2 ^ k := by
  have hk : 3 ≤ k := Fact.out
  rw [SemidirectProduct.card, Nat.card_congr toAdd, Nat.card_congr toAdd, Nat.card_zmod,
    Nat.card_zmod, ← pow_succ, Nat.sub_add_cancel (by omega)]

lemma OtherDihedralGroup.card : Nat.card (OtherDihedralGroup k) = 2 ^ k :=
  card_semidirectProduct k _

lemma SemiDihedralGroup.card : Nat.card (SemiDihedralGroup k) = 2 ^ k :=
  card_semidirectProduct k _
