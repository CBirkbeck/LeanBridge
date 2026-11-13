import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.CyclicIndexTwoClassification
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Multiplicity
import TauCeti.GroupTheory.SpecificGroups.Heisenberg
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

/-!
# The groups of order `p³` and the Heisenberg group

For a prime `p`, the Heisenberg group `He_p` (LMFDB `group.heisenberg`) is the group of `3 × 3`
unitriangular matrices over `𝔽_p`: Tau Ceti's `TauCeti.HeisenbergGroup (ZMod p)`, written in the
coordinates of the strictly upper triangle, is isomorphic to Tau Ceti's
`TauCeti.upperUnitriangularGroup (Fin 3) (ZMod p)`. It has order `p³` and is non-abelian, and it is
one of exactly two non-abelian groups of order `p³` up to isomorphism; for odd `p` it is the only
one of exponent `p`.

Let `G` be a non-abelian group of order `p³`. Its centre has order `p` and `G / Z(G)` has order
`p²`, so every commutator is central. If `g ^ p = 1` for every `g`, take `x`, `y` that do not
commute and `z = ⁅x, y⁆`: then `x y = z y x`, and `(a, b, c) ↦ zᶜ yᵇ xᵃ` is an isomorphism
`He_p ≃* G`. Otherwise `G` has an element `a` of order `p²`, whose cyclic subgroup has index `p`,
and an element `b` outside it acts on it by `a ↦ a ^ e` with `e ^ p ≡ 1` and `e ≢ 1` modulo `p²`,
so `e ≡ 1` modulo `p`.

* For `p = 2`, `e ≡ -1` modulo `4`, and `G` is the dihedral group `D₄` or the quaternion group
  `Q₈`, according as some element outside `⟨a⟩` is an involution. `He₂` is dihedral.
* For odd `p`, a power `b ^ j` acts by `1 + p`, and since `(u v) ^ p = u ^ p v ^ p` in `G` (the
  commutators are central of order `p`, and `p` divides `p (p - 1) / 2`), an element `c` of the
  coset of `b ^ j` has `c ^ p = 1`. Then `G` is the modular group `M_{p³} = C_{p²} ⋊ C_p`, in which
  the generator of `C_p` acts by `x ↦ x ^ (1 + p)`. It has an element of order `p²`, while `He_p`
  has exponent `p`.

## Main definitions

* `ZMod.unitPowMulAut`: the action of `C_m` on `C_n` through a unit `u` of `ZMod n` with
  `u ^ m = 1`.
* `ZMod.onePlusUnit`: the unit `1 + p` of `ZMod (p ^ 2)`.
* `ModularPCubedGroup` (LMFDB `group.heisenberg`): the modular group `M_{p³} = C_{p²} ⋊ C_p`.
* `TauCeti.HeisenbergGroup.toMatrix`: the unitriangular matrix of an element of the Heisenberg
  group.
* `TauCeti.HeisenbergGroup.mulEquivUpperUnitriangularGroup` (LMFDB `group.heisenberg`): the
  Heisenberg group is the group of `3 × 3` unitriangular matrices.

## Main results

* `TauCeti.HeisenbergGroup.natCard_zmod`, `TauCeti.HeisenbergGroup.not_isMulCommutative`
  (LMFDB `group.heisenberg`): `He_p` is a non-abelian group of order `p³`.
* `TauCeti.HeisenbergGroup.exponent_zmod` (LMFDB `group.heisenberg`): for odd `p`, `He_p` has
  exponent `p`.
* `TauCeti.HeisenbergGroup.nonempty_mulEquiv_of_exponent_eq` (LMFDB `group.heisenberg`): a
  non-abelian group of order `p³` and exponent `p` is isomorphic to `He_p`.
* `ModularPCubedGroup.natCard`, `ModularPCubedGroup.not_isMulCommutative`,
  `ModularPCubedGroup.orderOf_inl`: `M_{p³}` is a non-abelian group of order `p³` with an element of
  order `p²`.
* `TauCeti.HeisenbergGroup.nonempty_mulEquiv_or_nonempty_mulEquiv_modularPCubedGroup`,
  `TauCeti.HeisenbergGroup.isEmpty_mulEquiv_modularPCubedGroup` (LMFDB `group.heisenberg`): for
  odd `p`, a non-abelian group of order `p³` is isomorphic to `He_p` or to `M_{p³}`, which are not
  isomorphic.
* `nonempty_mulEquiv_dihedralGroup_or_nonempty_mulEquiv_quaternionGroup`: a non-abelian group of
  order `8` is isomorphic to `D₄` or to `Q₈`.
* `TauCeti.HeisenbergGroup.nonempty_mulEquiv_dihedralGroup`,
  `TauCeti.HeisenbergGroup.nonempty_mulEquiv_or_nonempty_mulEquiv_quaternionGroup`,
  `TauCeti.HeisenbergGroup.isEmpty_mulEquiv_quaternionGroup` (LMFDB `group.heisenberg`): `He₂ ≅ D₄`,
  and a non-abelian group of order `8` is isomorphic to `He₂` or to `Q₈`, which are not isomorphic.
* `TauCeti.HeisenbergGroup.exists_forall_iff_nonempty_mulEquiv` (LMFDB `group.heisenberg`): `He_p`
  is one of only two non-abelian groups of order `p³`: there is a group `K` such that the
  non-abelian groups of order `p³` not isomorphic to `He_p` are exactly the groups isomorphic to
  `K`.
-/

universe u

open Multiplicative SemidirectProduct Subgroup TauCeti

open scoped commutatorElement

variable {G : Type*} [Group G] {p : ℕ} {x y z a b g : G} {e m n : ℕ}

private lemma pow_eq_pow_of_natCast_eq {i j : ℕ} (hx : x ^ n = 1) (h : (i : ZMod n) = j) :
    x ^ i = x ^ j := by
  rw [pow_eq_pow_mod i hx, pow_eq_pow_mod j hx, (ZMod.natCast_eq_natCast_iff' i j n).mp h]

variable (n) in
private lemma mul_pow_eq_of_mul_eq (hxy : x * y = z * y * x) (hzy : Commute z y) :
    x * y ^ n = z ^ n * y ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ y, pow_succ z, ← mul_assoc, ih, mul_assoc _ x y, hxy]
    simp only [mul_assoc]
    rw [← mul_assoc (y ^ n) z, ← (hzy.pow_right n).eq, mul_assoc]

variable (m n) in
private lemma pow_mul_pow_eq_of_mul_eq (hxy : x * y = z * y * x) (hzx : Commute z x)
    (hzy : Commute z y) : x ^ m * y ^ n = z ^ (m * n) * y ^ n * x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' x, mul_assoc, ih, add_one_mul, pow_add z]
    simp only [mul_assoc]
    rw [← mul_assoc x, ← ((hzx.pow_left (m * n)).eq), mul_assoc, ← mul_assoc x,
      mul_pow_eq_of_mul_eq n hxy hzy]
    simp only [mul_assoc]

variable (n) in
private lemma mul_pow_eq_of_mul_eq' (hxy : y * x = z * x * y) (hzx : Commute z x)
    (hzy : Commute z y) : (x * y) ^ n = z ^ n.choose 2 * x ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : y ^ n * x = z ^ n * x * y ^ n := by
      simpa using pow_mul_pow_eq_of_mul_eq n 1 hxy hzy hzx
    rw [pow_succ, ih, Nat.choose_succ_succ', Nat.choose_one_right, pow_add z, pow_succ x,
      pow_succ y]
    simp only [mul_assoc]
    rw [← mul_assoc (y ^ n) x y, h1]
    simp only [mul_assoc]
    rw [(hzx.pow_pow n n).symm.left_comm, (Commute.pow_pow_self z _ n).left_comm]

variable [NeZero n] in
private lemma pow_val_add (hx : x ^ n = 1) (s t : ZMod n) :
    x ^ (s + t).val = x ^ s.val * x ^ t.val := by
  rw [← pow_add]
  exact pow_eq_pow_of_natCast_eq hx (by simp)

variable [NeZero n] in
private lemma pow_val_add_add_mul (hx : x ^ n = 1) (s t u v : ZMod n) :
    x ^ (s + t + u * v).val = x ^ s.val * x ^ t.val * x ^ (u.val * v.val) := by
  rw [← pow_add, ← pow_add]
  exact pow_eq_pow_of_natCast_eq hx (by simp)

private lemma pow_conj_pow_eq (hg : g * a * g⁻¹ = a ^ e) (j k : ℕ) :
    g ^ j * a ^ k * (g ^ j)⁻¹ = a ^ (e ^ j * k) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_inv_rev, ← mul_assoc, mul_assoc g, mul_assoc g, ih, ← conj_pow, hg,
      ← pow_mul, pow_succ' e, mul_assoc]

variable (x) [NeZero n] in
/-- The homomorphism `C_n → G` sending the generator to `x`, for `x ^ n = 1`. -/
private def zmodPowHom (hx : x ^ n = 1) : Multiplicative (ZMod n) →* G where
  toFun k := x ^ k.toAdd.val
  map_one' := by simp
  map_mul' a b := by rw [toAdd_mul, pow_val_add hx]

namespace ZMod

variable (u : (ZMod n)ˣ) (v : Multiplicative (ZMod n)) [NeZero m] (hu : u ^ m = 1)

lemma unitMulAut_pow_apply (k : ℕ) :
    (unitMulAut u ^ k) v = ofAdd ((u ^ k : (ZMod n)ˣ) * v.toAdd) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, unitMulAut_apply, pow_succ', Units.val_mul, mul_assoc]
    rfl

/-- The action of `C_m = Multiplicative (ZMod m)` on `C_n = Multiplicative (ZMod n)` in which the
generator acts by `v ↦ v ^ u`, for a unit `u` of `ZMod n` with `u ^ m = 1`. -/
def unitPowMulAut : Multiplicative (ZMod m) →* MulAut (Multiplicative (ZMod n)) :=
  zmodPowHom (unitMulAut u) <| MulEquiv.ext fun v ↦ by
    rw [unitMulAut_pow_apply, hu, Units.val_one, one_mul]
    rfl

lemma unitPowMulAut_apply (k : Multiplicative (ZMod m)) :
    unitPowMulAut u hu k v = ofAdd ((u ^ k.toAdd.val : (ZMod n)ˣ) * v.toAdd) :=
  unitMulAut_pow_apply u v _

variable (p) in
/-- The unit `1 + p` of `ZMod (p ^ 2)`, whose `p`-th power is `1`. -/
def onePlusUnit : (ZMod (p ^ 2))ˣ :=
  .mkOfMulEqOne (1 + p) (1 - p) <| by
    have h : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      exact_mod_cast natCast_self (p ^ 2)
    linear_combination -h

lemma val_onePlusUnit : (onePlusUnit p : ZMod (p ^ 2)) = 1 + p :=
  rfl

variable (p) in
lemma onePlusUnit_pow : onePlusUnit p ^ p = 1 := by
  have h : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    exact_mod_cast natCast_self (p ^ 2)
  have h2 : (p : ZMod (p ^ 2)) ^ 2 ∣ (1 + p) ^ p - 1 ^ (p - 1) * p * p - 1 ^ p :=
    sq_dvd_add_pow_sub_sub _ 1 p
  rw [h, zero_dvd_iff, one_pow, one_pow, one_mul] at h2
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, val_onePlusUnit, Units.val_one]
  linear_combination h2 + h

end ZMod

variable (p) in
/-- The **modular group `M_{p³} = C_{p²} ⋊ C_p`** (LMFDB `group.heisenberg`), in which the
generator of `C_p` acts on `C_{p²}` by `v ↦ v ^ (1 + p)`. For odd `p` it is, with the Heisenberg
group, one of the two non-abelian groups of order `p³`
(`TauCeti.HeisenbergGroup.nonempty_mulEquiv_or_nonempty_mulEquiv_modularPCubedGroup`). -/
abbrev ModularPCubedGroup [NeZero p] : Type :=
  Multiplicative (ZMod (p ^ 2)) ⋊[ZMod.unitPowMulAut (ZMod.onePlusUnit p) (ZMod.onePlusUnit_pow p)]
    Multiplicative (ZMod p)

namespace TauCeti.HeisenbergGroup

variable (p) in
/-- **The Heisenberg group `He_p` has order `p³`** (LMFDB `group.heisenberg`). -/
lemma natCard_zmod : Nat.card (HeisenbergGroup (ZMod p)) = p ^ 3 := by
  rw [card_eq, Nat.card_zmod]

/-- **The Heisenberg group is non-abelian** (LMFDB `group.heisenberg`) over a nontrivial ring:
`(1, 0, 0) (0, 1, 0) = (1, 1, 1)` and `(0, 1, 0) (1, 0, 0) = (1, 1, 0)`. -/
lemma not_isMulCommutative {R : Type*} [Ring R] [Nontrivial R] :
    ¬IsMulCommutative (HeisenbergGroup R) := fun h ↦ by
  simpa using congrArg z (mul_comm' (⟨1, 0, 0⟩ : HeisenbergGroup R) ⟨0, 1, 0⟩)

variable {R : Type*} [CommRing R] (w : HeisenbergGroup R)

/-- The unitriangular matrix `[[1, x, z], [0, 1, y], [0, 0, 1]]` of an element `(x, y, z)` of the
Heisenberg group. -/
def toMatrix : Matrix (Fin 3) (Fin 3) R :=
  !![1, w.x, w.z; 0, 1, w.y; 0, 0, 1]

lemma isUpperUnitriangular_toMatrix : (toMatrix w).IsUpperUnitriangular := by
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;>
    simp_all [toMatrix]

/-- **The Heisenberg group is the group of `3 × 3` unitriangular matrices** (LMFDB
`group.heisenberg`): `(x, y, z) ↦ [[1, x, z], [0, 1, y], [0, 0, 1]]` is an isomorphism onto Tau
Ceti's `TauCeti.upperUnitriangularGroup (Fin 3) R`. -/
noncomputable def mulEquivUpperUnitriangularGroup :
    HeisenbergGroup R ≃* upperUnitriangularGroup (Fin 3) R where
  toFun a := ⟨(isUpperUnitriangular_toMatrix a).toGL,
    UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup _⟩
  invFun g := ⟨((g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 1,
    ((g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 2,
    ((g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 2⟩
  left_inv a := by
    ext <;> simp [toMatrix]
  right_inv g := by
    refine UpperUnitriangularGroup.ext fun i j hij ↦ ?_
    fin_cases i <;> fin_cases j <;> simp_all [toMatrix]
  map_mul' a b := by
    refine UpperUnitriangularGroup.ext fun i j hij ↦ ?_
    fin_cases i <;> fin_cases j <;> simp_all [toMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring1

end TauCeti.HeisenbergGroup

namespace ModularPCubedGroup

variable (p) [NeZero p]

instance : Finite (ModularPCubedGroup p) :=
  Finite.of_equiv _ equivProd.symm

/-- **`M_{p³}` has order `p³`** (LMFDB `group.heisenberg`). -/
lemma natCard : Nat.card (ModularPCubedGroup p) = p ^ 3 := by
  rw [SemidirectProduct.card, Nat.card_congr toAdd, Nat.card_congr toAdd, Nat.card_zmod,
    Nat.card_zmod]
  ring1

/-- **`M_{p³}` has an element of order `p²`** (LMFDB `group.heisenberg`): the generator of
`C_{p²}`. -/
lemma orderOf_inl : orderOf (inl (ofAdd 1) : ModularPCubedGroup p) = p ^ 2 := by
  rw [orderOf_injective _ inl_injective, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

end ModularPCubedGroup

variable [hp : Fact p.Prime]

namespace ModularPCubedGroup

variable (p)

lemma inr_mul_inl_mul_inv (v : ZMod (p ^ 2)) :
    (inr (ofAdd 1) * inl (ofAdd v) * (inr (ofAdd 1))⁻¹ : ModularPCubedGroup p) =
      inl (ofAdd ((1 + (p : ZMod (p ^ 2))) * v)) := by
  rw [← map_inv, ← inl_aut, ZMod.unitPowMulAut_apply, toAdd_ofAdd, ZMod.val_one, pow_one,
    ZMod.val_onePlusUnit, toAdd_ofAdd]

/-- **`M_{p³}` is non-abelian** (LMFDB `group.heisenberg`): the generator of `C_p` acts on the
generator of `C_{p²}` by `v ↦ v ^ (1 + p)`, and `p ≠ 0` in `ZMod (p ^ 2)`. -/
lemma not_isMulCommutative : ¬IsMulCommutative (ModularPCubedGroup p) := fun h ↦ by
  have h1 : (inr (ofAdd 1) * inl (ofAdd 1) * (inr (ofAdd 1))⁻¹ : ModularPCubedGroup p) =
      inl (ofAdd ((1 + (p : ZMod (p ^ 2))) * 1)) :=
    inr_mul_inl_mul_inv p 1
  rw [mul_comm' (inr _), mul_inv_cancel_right, inl_injective.eq_iff, ofAdd.injective.eq_iff,
    mul_one, left_eq_add, ZMod.natCast_eq_zero_iff] at h1
  exact (Nat.le_of_dvd hp.out.pos h1).not_gt (lt_self_pow₀ hp.out.one_lt one_lt_two)

end ModularPCubedGroup

private lemma isMulCommutative_of_natCard_dvd_prime_sq {H : Type*} [Group H]
    (h : Nat.card H ∣ p ^ 2) : IsMulCommutative H := by
  rcases (Nat.dvd_prime_pow hp.out).mp h with ⟨k, hk, hcard⟩
  interval_cases k
  · have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp (hcard.trans (pow_zero p))).1
    exact isMulCommutative_iff.mpr fun a b ↦ Subsingleton.elim _ _
  · have : IsCyclic H := isCyclic_of_prime_card (hcard.trans (pow_one p))
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard

private lemma eq_top_of_not_isMulCommutative (hG : Nat.card G = p ^ 3) {H : Subgroup G}
    (hH : ¬IsMulCommutative H) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
  rcases (Nat.dvd_prime_pow hp.out).mp (hG ▸ card_subgroup_dvd_card H) with ⟨k, hk, hcard⟩
  refine H.eq_top_of_card_eq (hcard.trans (hG ▸ ?_))
  by_contra hne
  exact hH (isMulCommutative_of_natCard_dvd_prime_sq
    (hcard ▸ pow_dvd_pow p (by grind : k ≤ 2)))

private lemma natCard_center_eq_prime (hG : Nat.card G = p ^ 3) (hnc : ¬IsMulCommutative G) :
    Nat.card (center G) = p := by
  rcases IsPGroup.card_center_eq_prime_pow hG (by norm_num) with ⟨k, hk, hcard⟩
  have h : Nat.card G = Nat.card (G ⧸ center G) * Nat.card (center G) :=
    (center G).card_eq_card_quotient_mul_card_subgroup
  rw [hG, hcard] at h
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp (Dvd.intro_left _ h.symm)
  have hq : Nat.card (G ⧸ center G) = p ^ (3 - k) := by
    rw [← Nat.pow_div hk3 hp.out.pos, h, Nat.mul_div_cancel _ (pow_pos hp.out.pos k)]
  interval_cases k
  · exact hcard.trans (pow_one p)
  · have : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card (hq.trans (pow_one p))
    exact absurd (isMulCommutative_of_isCyclic_quotient_center_self G) hnc
  · have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
    exact absurd (center_eq_top_iff.mp ((center G).eq_top_of_card_eq (hcard.trans hG.symm))) hnc

variable (a b) in
private lemma commutatorElement_mem_center (hG : Nat.card G = p ^ 3) : ⁅a, b⁆ ∈ center G := by
  by_cases hnc : IsMulCommutative G
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' a b)]
    exact one_mem _
  have hq : Nat.card (G ⧸ center G) = p ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_right hp.out.pos ?_
    rw [← natCard_center_eq_prime hG hnc, ← card_eq_card_quotient_mul_card_subgroup, hG,
      natCard_center_eq_prime hG hnc]
    ring1
  have : IsMulCommutative (G ⧸ center G) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

private lemma pow_eq_one_of_mem_center (hG : Nat.card G = p ^ 3) (hnc : ¬IsMulCommutative G) {w : G}
    (hw : w ∈ center G) : w ^ p = 1 := by
  have h : (⟨w, hw⟩ : center G) ^ Nat.card (center G) = 1 := pow_card_eq_one'
  rw [natCard_center_eq_prime hG hnc] at h
  exact congrArg Subtype.val h

/-- The homomorphism `He_p → G` sending `(a, b, c)` to `zᶜ yᵇ xᵃ`, for `x`, `y` of order dividing
`p` whose commutator `z = ⁅x, y⁆` is central of order dividing `p`. -/
private def heisenbergLift (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : ⁅x, y⁆ ^ p = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) : HeisenbergGroup (ZMod p) →* G where
  toFun a := ⁅x, y⁆ ^ a.z.val * y ^ a.y.val * x ^ a.x.val
  map_one' := by simp
  map_mul' a b := by
    have hxyz : x * y = ⁅x, y⁆ * y * x := by
      rw [commutatorElement_def]
      group
    simp only [HeisenbergGroup.mul_x, HeisenbergGroup.mul_y, HeisenbergGroup.mul_z]
    rw [pow_val_add hx, pow_val_add hy, pow_val_add_add_mul hz]
    simp only [mul_assoc]
    rw [(hzx.pow_pow _ _).symm.left_comm, (hzy.pow_pow _ _).symm.left_comm,
      ← mul_assoc (x ^ a.x.val) (y ^ b.y.val), pow_mul_pow_eq_of_mul_eq _ _ hxyz hzx hzy]
    simp only [mul_assoc]
    rw [(hzy.pow_pow _ _).symm.left_comm]

private lemma nonempty_mulEquiv_heisenbergGroup_of_pow_eq_one (hG : Nat.card G = p ^ 3)
    (hnc : ¬IsMulCommutative G) (hpow : ∀ g : G, g ^ p = 1) :
    Nonempty (G ≃* HeisenbergGroup (ZMod p)) := by
  rcases not_forall.mp (mt isMulCommutative_iff.mpr hnc) with ⟨x, hx⟩
  rcases not_forall.mp hx with ⟨y, hxy⟩
  have hz : ⁅x, y⁆ ∈ center G := commutatorElement_mem_center x y hG
  let ψ : HeisenbergGroup (ZMod p) →* G := heisenbergLift (hpow x) (hpow y) (hpow _)
    (mem_center_iff.mp hz x).symm (mem_center_iff.mp hz y).symm
  have hψx : ψ ⟨1, 0, 0⟩ = x := by
    simp [ψ, heisenbergLift, ZMod.val_one]
  have hψy : ψ ⟨0, 1, 0⟩ = y := by
    simp [ψ, heisenbergLift, ZMod.val_one]
  have htop : ψ.range = ⊤ := eq_top_of_not_isMulCommutative hG fun h ↦ hxy <| by
    simpa [hψx, hψy] using congrArg Subtype.val
      (mul_comm' (⟨ψ ⟨1, 0, 0⟩, ⟨_, rfl⟩⟩ : ψ.range) ⟨ψ ⟨0, 1, 0⟩, ⟨_, rfl⟩⟩)
  exact ⟨(MulEquiv.ofBijective ψ (MonoidHom.range_eq_top.mp htop |>.bijective_of_nat_card_le
    (by rw [HeisenbergGroup.natCard_zmod, hG]))).symm⟩

private lemma exists_orderOf_eq_sq (hG : Nat.card G = p ^ 3) (hnc : ¬IsMulCommutative G)
    (h : ¬∀ g : G, g ^ p = 1) : ∃ a : G, orderOf a = p ^ 2 := by
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
  rcases not_forall.mp h with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rcases (Nat.dvd_prime_pow hp.out).mp (hG ▸ orderOf_dvd_natCard a) with ⟨k, hk, hak⟩
  interval_cases k
  · exact absurd (by rw [orderOf_eq_one_iff.mp (hak.trans (pow_zero p)), one_pow]) ha
  · exact absurd (by rw [← hak.trans (pow_one p), pow_orderOf_eq_one]) ha
  · exact hak
  · have : IsCyclic G := isCyclic_of_orderOf_eq_card a (hak.trans hG.symm)
    exact (hnc inferInstance).elim

private lemma pow_eq_pow_iff_natCast_eq (ha : orderOf a = n) (i j : ℕ) :
    a ^ i = a ^ j ↔ (i : ZMod n) = j := by
  rw [pow_eq_pow_iff_modEq, ha, ZMod.natCast_eq_natCast_iff]

private lemma index_zpowers_eq (hG : Nat.card G = p ^ 3) (ha : orderOf a = p ^ 2) :
    (zpowers a).index = p := by
  have h : Nat.card (zpowers a) * (zpowers a).index = Nat.card G := (zpowers a).card_mul_index
  rw [Nat.card_zpowers, ha, hG] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos 2) (h.trans (by ring1))

private lemma normal_zpowers (hG : Nat.card G = p ^ 3) (ha : orderOf a = p ^ 2) :
    (zpowers a).Normal :=
  normal_of_index_eq_minFac_card <| by
    rw [index_zpowers_eq hG ha, hG, hp.out.pow_minFac three_ne_zero]

variable (g) in
private lemma pow_mem_zpowers (hG : Nat.card G = p ^ 3) (ha : orderOf a = p ^ 2) :
    g ^ p ∈ zpowers a := by
  have : (zpowers a).Normal := normal_zpowers hG ha
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← index_zpowers_eq hG ha, index_eq_card]
  exact pow_card_eq_one'

variable (b) in
private lemma exists_mul_mul_inv_eq_pow (hG : Nat.card G = p ^ 3) (ha : orderOf a = p ^ 2) :
    ∃ e : ℕ, b * a * b⁻¹ = a ^ e := by
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
  rcases (Submonoid.mem_powers_iff _ _).mp <| mem_powers_iff_mem_zpowers.mpr <|
    (normal_zpowers hG ha).conj_mem a (mem_zpowers a) b with ⟨e, he⟩
  exact ⟨e, he.symm⟩

private lemma natCast_pow_eq_one (hG : Nat.card G = p ^ 3) (ha : orderOf a = p ^ 2)
    (he : b * a * b⁻¹ = a ^ e) : ((e ^ p : ℕ) : ZMod (p ^ 2)) = 1 := by
  rcases mem_zpowers_iff.mp (pow_mem_zpowers b hG ha) with ⟨k, hk⟩
  have h : b ^ p * a ^ 1 * (b ^ p)⁻¹ = a ^ (e ^ p * 1) := pow_conj_pow_eq he p 1
  rw [pow_one, mul_one, ← hk, ((Commute.refl a).zpow_left k).eq, mul_inv_cancel_right] at h
  exact ((pow_eq_pow_iff_natCast_eq ha 1 _).mp (by rw [pow_one]; exact h)).symm.trans Nat.cast_one

private lemma natCast_ne_one (hG : Nat.card G = p ^ 3) (hnc : ¬IsMulCommutative G)
    (ha : orderOf a = p ^ 2) (hb : b ∉ zpowers a) (he : b * a * b⁻¹ = a ^ e) :
    (e : ZMod (p ^ 2)) ≠ 1 := fun h ↦ by
  have hba : b * a * b⁻¹ = a := by
    rw [he, (pow_eq_pow_iff_natCast_eq ha e 1).mpr (h.trans Nat.cast_one.symm), pow_one]
  have hcent : centralizer {a} = ⊤ :=
    (isCoatom_of_index_prime (index_zpowers_eq hG ha ▸ hp.out)).2 _ <| lt_of_le_of_ne
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) fun h ↦ hb <|
        h ▸ mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hba)
  have hle : zpowers a ≤ center G := zpowers_le.mpr <| mem_center_iff.mpr fun g ↦
    mem_centralizer_singleton_iff.mp (hcent ▸ mem_top g)
  have hdvd : Nat.card (zpowers a) ∣ Nat.card (center G) := card_dvd_of_le hle
  rw [Nat.card_zpowers, ha, natCard_center_eq_prime hG hnc] at hdvd
  exact (Nat.le_of_dvd hp.out.pos hdvd).not_gt (lt_self_pow₀ hp.out.one_lt one_lt_two)

private lemma exists_pow_eq_one_add_prime (he : ((e ^ p : ℕ) : ZMod (p ^ 2)) = 1)
    (he1 : (e : ZMod (p ^ 2)) ≠ 1) : ∃ j : ℕ, ¬p ∣ j ∧ ((e ^ j : ℕ) : ZMod (p ^ 2)) = 1 + p := by
  have hp0 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    exact_mod_cast ZMod.natCast_self (p ^ 2)
  have hep : (e : ZMod p) = 1 := by
    have h : ((e ^ p : ℕ) : ZMod p) = 1 := by
      simpa using congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) he
    rwa [Nat.cast_pow, ZMod.pow_card] at h
  have hmod : e % p = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at hep
    rwa [Nat.mod_eq_of_lt hp.out.one_lt] at hep
  have hk : ((e / p : ℕ) : ZMod p) ≠ 0 := fun h ↦ he1 <| by
    rcases (ZMod.natCast_eq_zero_iff _ p).mp h with ⟨t, ht⟩
    rw [← Nat.div_add_mod e p, hmod, ht]
    push_cast
    linear_combination (t : ZMod (p ^ 2)) * hp0
  set k : ℕ := e / p
  let j : ℕ := ((k : ZMod p)⁻¹).val
  have hjk : ((j * k : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hk]
  have hjkmod : j * k % p = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at hjk
    rwa [Nat.mod_eq_of_lt hp.out.one_lt] at hjk
  refine ⟨j, fun h ↦ ?_, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff] at h
    rw [Nat.cast_mul, h, zero_mul] at hjk
    exact zero_ne_one hjk
  · have he' : (e : ZMod (p ^ 2)) = 1 + p * k := by
      rw [← Nat.div_add_mod e p, hmod]
      push_cast
      ring1
    have hjk' : (p : ZMod (p ^ 2)) * (j * k / p : ℕ) + 1 = j * k := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) (hjkmod ▸ Nat.div_add_mod (j * k) p)
    have hbin : ((p : ZMod (p ^ 2)) * k) ^ 2 ∣
        (1 + p * k) ^ j - 1 ^ (j - 1) * (p * k) * j - 1 ^ j :=
      sq_dvd_add_pow_sub_sub _ 1 j
    rw [mul_pow, hp0, zero_mul, zero_dvd_iff, one_pow, one_pow, one_mul] at hbin
    rw [Nat.cast_pow, he']
    linear_combination hbin - (p : ZMod (p ^ 2)) * hjk' + ((j * k / p : ℕ) : ZMod (p ^ 2)) * hp0

private lemma nonempty_mulEquiv_modularPCubedGroup (hp2 : p ≠ 2) (hG : Nat.card G = p ^ 3)
    (hnc : ¬IsMulCommutative G) (ha : orderOf a = p ^ 2) :
    Nonempty (G ≃* ModularPCubedGroup p) := by
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
  have ha2 : a ^ p ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hcoatom : IsCoatom (zpowers a) := isCoatom_of_index_prime (index_zpowers_eq hG ha ▸ hp.out)
  have htop {H : Subgroup G} (hH : zpowers a ≤ H) {g : G} (hg : g ∉ zpowers a) (hgH : g ∈ H) :
      H = ⊤ :=
    hcoatom.2 H (lt_of_le_of_ne hH fun h ↦ hg (h ▸ hgH))
  have : (zpowers a).Normal := normal_zpowers hG ha
  rcases IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hcoatom.1) with ⟨b, -, hb⟩
  rcases exists_mul_mul_inv_eq_pow b hG ha with ⟨e, he⟩
  rcases exists_pow_eq_one_add_prime (natCast_pow_eq_one hG ha he) (natCast_ne_one hG hnc ha hb he)
    with ⟨j, hj, hej⟩
  have hb' : b ^ j ∉ zpowers a := by
    have hord : orderOf (b : G ⧸ zpowers a) = p := orderOf_eq_prime
      (by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact pow_mem_zpowers b hG ha)
      (by rwa [Ne, QuotientGroup.eq_one_iff])
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← orderOf_dvd_iff_pow_eq_one, hord]
    exact hj
  have hconj : b ^ j * a * (b ^ j)⁻¹ = a ^ (1 + p) := by
    have h : b ^ j * a ^ 1 * (b ^ j)⁻¹ = a ^ (e ^ j * 1) := pow_conj_pow_eq he j 1
    rw [pow_one, mul_one] at h
    rw [h, pow_eq_pow_iff_natCast_eq ha]
    exact_mod_cast hej
  set b' : G := b ^ j
  rcases (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr
    (pow_mem_zpowers b' hG ha)) with ⟨s, hs⟩
  have hps : p ∣ s := by
    have h : b' ^ 1 * a ^ s * (b' ^ 1)⁻¹ = a ^ ((1 + p) ^ 1 * s) := pow_conj_pow_eq hconj 1 s
    rw [pow_one, pow_one, hs, ← pow_succ', pow_succ, mul_inv_cancel_right, ← hs,
      pow_eq_pow_iff_natCast_eq ha] at h
    have h2 : ((p * s : ℕ) : ZMod (p ^ 2)) = 0 := by
      push_cast at h ⊢
      linear_combination -h
    rw [ZMod.natCast_eq_zero_iff, pow_two] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hp.out.pos h2
  rcases hps with ⟨t, rfl⟩
  set c : G := a ^ ((p - 1) * t) * b' with hcdef
  have hcN : c ∉ zpowers a := fun h ↦ hb' ((mul_mem_cancel_left (pow_mem (mem_zpowers a) _)).mp h)
  have hc : c ^ p = 1 := by
    have hw : ⁅b', a ^ ((p - 1) * t)⁆ ∈ center G := commutatorElement_mem_center _ _ hG
    rcases hp.out.dvd_choose_self two_ne_zero (hp.out.two_le.lt_of_ne' hp2) with ⟨m, hm⟩
    rw [hcdef, mul_pow_eq_of_mul_eq' p (by rw [commutatorElement_def]; group)
      (mem_center_iff.mp hw _).symm (mem_center_iff.mp hw _).symm, hm, pow_mul,
      pow_eq_one_of_mem_center hG hnc hw, one_pow, one_mul, ← pow_mul, ← hs, ← pow_add]
    have hexp : (p - 1) * t * p + p * t = p ^ 2 * t := by
      have hp1 : 1 ≤ p := hp.out.one_le
      zify [hp1]
      ring1
    rw [hexp, pow_mul, ha2, one_pow]
  have hca : c * a * c⁻¹ = a ^ (1 + p) := by
    have h : c * a * c⁻¹ = a ^ ((p - 1) * t) * (b' * a * b'⁻¹) * (a ^ ((p - 1) * t))⁻¹ := by
      rw [hcdef]
      group
    rw [h, hconj, (Commute.pow_pow_self a _ _).eq, mul_inv_cancel_right]
  have : Fact (1 < p ^ 2) := ⟨one_lt_pow₀ hp.out.one_lt two_ne_zero⟩
  let F : ModularPCubedGroup p →* G := lift (zmodPowHom a ha2) (zmodPowHom c hc) fun g ↦ by
    refine MonoidHom.ext fun v ↦ ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, zmodPowHom,
      MonoidHom.coe_mk, OneHom.coe_mk, ZMod.unitPowMulAut_apply]
    rw [pow_conj_pow_eq hca, pow_eq_pow_iff_natCast_eq ha]
    simp [ZMod.val_onePlusUnit]
  have hFa : F (inl (ofAdd 1)) = a := by
    simp [F, zmodPowHom, ZMod.val_one]
  have hFc : F (inr (ofAdd 1)) = c := by
    simp [F, zmodPowHom, ZMod.val_one]
  have hsurj : Function.Surjective F :=
    MonoidHom.range_eq_top.mp <| htop (zpowers_le.mpr ⟨_, hFa⟩) hcN ⟨_, hFc⟩
  exact ⟨(MulEquiv.ofBijective F (hsurj.bijective_of_nat_card_le
    (by rw [ModularPCubedGroup.natCard, hG]))).symm⟩

/-- **A non-abelian group of order `8` is the dihedral group `D₄` or the quaternion group `Q₈`**:
an element `a` of order `4` generates a subgroup of index `2` on which every element outside it acts
by inversion, and the group is `C₄ ⋊ C₂` if some element outside `⟨a⟩` is an involution, and the
non-split extension `Q₈` otherwise. -/
lemma nonempty_mulEquiv_dihedralGroup_or_nonempty_mulEquiv_quaternionGroup (hG : Nat.card G = 2 ^ 3)
    (hnc : ¬IsMulCommutative G) :
    Nonempty (G ≃* DihedralGroup 4) ∨ Nonempty (G ≃* QuaternionGroup 2) := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  rcases exists_orderOf_eq_sq hG hnc fun h ↦ hnc <| isMulCommutative_iff.mpr fun a b ↦ by
    have hinv (g : G) : g⁻¹ = g := inv_eq_of_mul_eq_one_right ((sq g).symm.trans (h g))
    rw [← hinv (a * b), mul_inv_rev, hinv, hinv] with ⟨a, ha⟩
  have hN : (zpowers a).index = 2 := index_zpowers_eq hG ha
  have ha4 : orderOf a = 4 := ha
  have hconj (g : G) (hg : g ∉ zpowers a) : g * a * g⁻¹ = a ^ 3 := by
    rcases exists_mul_mul_inv_eq_pow g hG ha with ⟨e, he⟩
    have h1 : ((e ^ 2 : ℕ) : ZMod (2 ^ 2)) = 1 := natCast_pow_eq_one hG ha he
    have h2 : (e : ZMod (2 ^ 2)) ≠ 1 := natCast_ne_one hG hnc ha hg he
    rw [Nat.cast_pow] at h1
    rw [he, pow_eq_pow_iff_natCast_eq ha]
    generalize (e : ZMod (2 ^ 2)) = ε at h1 h2
    revert ε
    decide
  have hinv : ∀ g ∉ zpowers a, ∀ y ∈ zpowers a, g * y * g⁻¹ = y⁻¹ := by
    rintro g hg - ⟨k, rfl⟩
    have h4 : a ^ 4 = 1 := ha4 ▸ pow_orderOf_eq_one a
    have ha3 : a ^ 3 = a⁻¹ := eq_inv_of_mul_eq_one_left <| by
      rw [← pow_succ]
      exact h4
    simp only [← conj_zpow, hconj g hg, ha3, inv_zpow]
  by_cases hsplit : ∃ c ∉ zpowers a, c ^ 2 = 1
  · rcases hsplit with ⟨c, hc, hc2⟩
    rcases nonempty_mulEquiv_semidirectProduct_of_sq_eq_one hN ha4 hc hc2
      (DihedralGroup.neg_one_units_sq 4) (DihedralGroup.natCast_sub_one_eq_neg_one 4)
      (hconj c hc) with ⟨f⟩
    exact .inl ⟨f.trans (DihedralGroup.mulEquivSemidirectProduct 4).symm⟩
  · refine .inr (nonempty_mulEquiv_quaternionGroup_of_forall_not_isComplement' hN hinv
      (fun K hK ↦ hsplit ?_) (by rw [Nat.card_zpowers, ha4]))
    have hKcard : Nat.card K = 2 := hK.symm.index_eq_card.symm.trans hN
    have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by rw [hKcard]; norm_num)
    rcases exists_ne (1 : K) with ⟨c, hc⟩
    refine ⟨c, fun h ↦ hc (Subtype.ext (disjoint_def.mp hK.disjoint h c.2)), ?_⟩
    rw [← hKcard, ← SubgroupClass.coe_pow, pow_card_eq_one', OneMemClass.coe_one]

namespace TauCeti.HeisenbergGroup

lemma pow_prime_eq_one (hp2 : p ≠ 2) (w : HeisenbergGroup (ZMod p)) : w ^ p = 1 := by
  have hc : (p.choose 2 : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr <|
    hp.out.dvd_choose_self two_ne_zero (hp.out.two_le.lt_of_ne' hp2)
  rw [pow_eq]
  ext <;> simp [hc]

/-- **The Heisenberg group `He_p` has exponent `p` for odd `p`** (LMFDB `group.heisenberg`):
`(x, y, z) ^ p = (p x, p y, p z + (p (p - 1) / 2) x y)`, and `p` divides `p (p - 1) / 2`. -/
lemma exponent_zmod (hp2 : p ≠ 2) : Monoid.exponent (HeisenbergGroup (ZMod p)) = p := by
  refine ((Nat.dvd_prime hp.out).mp (Monoid.exponent_dvd_of_forall_pow_eq_one
    (pow_prime_eq_one hp2))).resolve_left fun h ↦ ?_
  have : Subsingleton (HeisenbergGroup (ZMod p)) := Monoid.exp_eq_one_iff.mp h
  simpa using congrArg z (Subsingleton.elim (⟨0, 0, 1⟩ : HeisenbergGroup (ZMod p)) 1)

/-- **`He_p` is the unique non-abelian group of order `p³` and exponent `p`** (LMFDB
`group.heisenberg`): for non-commuting `x`, `y` with commutator `z`, the map
`(a, b, c) ↦ zᶜ yᵇ xᵃ` is an isomorphism. With `TauCeti.HeisenbergGroup.exponent_zmod`, this
characterises `He_p` for odd `p`; for `p = 2` a group of exponent `2` is abelian. -/
lemma nonempty_mulEquiv_of_exponent_eq (hG : Nat.card G = p ^ 3) (hnc : ¬IsMulCommutative G)
    (hexp : Monoid.exponent G = p) : Nonempty (G ≃* HeisenbergGroup (ZMod p)) :=
  nonempty_mulEquiv_heisenbergGroup_of_pow_eq_one hG hnc fun g ↦ hexp ▸ Monoid.pow_exponent_eq_one g

/-- **`He_p` and `M_{p³}` are not isomorphic for odd `p`** (LMFDB `group.heisenberg`): `M_{p³}`
has an element of order `p²`, while `He_p` has exponent `p`. -/
lemma isEmpty_mulEquiv_modularPCubedGroup (hp2 : p ≠ 2) :
    IsEmpty (HeisenbergGroup (ZMod p) ≃* ModularPCubedGroup p) := by
  refine ⟨fun f ↦ ?_⟩
  have h : orderOf (f.symm (inl (ofAdd 1))) ∣ p :=
    orderOf_dvd_of_pow_eq_one (pow_prime_eq_one hp2 _)
  rw [f.symm.orderOf_eq, ModularPCubedGroup.orderOf_inl] at h
  exact (Nat.le_of_dvd hp.out.pos h).not_gt (lt_self_pow₀ hp.out.one_lt one_lt_two)

/-- **The non-abelian groups of order `p³`, `p` odd** (LMFDB `group.heisenberg`): such a group is
isomorphic to the Heisenberg group `He_p` if it has exponent `p`, and to the modular group
`M_{p³} = C_{p²} ⋊ C_p` otherwise. -/
lemma nonempty_mulEquiv_or_nonempty_mulEquiv_modularPCubedGroup (hp2 : p ≠ 2)
    (hG : Nat.card G = p ^ 3) (hnc : ¬IsMulCommutative G) :
    Nonempty (G ≃* HeisenbergGroup (ZMod p)) ∨ Nonempty (G ≃* ModularPCubedGroup p) := by
  by_cases h : ∀ g : G, g ^ p = 1
  · exact .inl (nonempty_mulEquiv_heisenbergGroup_of_pow_eq_one hG hnc h)
  · rcases exists_orderOf_eq_sq hG hnc h with ⟨a, ha⟩
    exact .inr (nonempty_mulEquiv_modularPCubedGroup hp2 hG hnc ha)

/-- **`He₂` is the dihedral group `D₄`** (LMFDB `group.heisenberg`): `a = (1, 1, 0)` has order `4`,
and the involution `c = (1, 0, 0)` outside `⟨a⟩` acts on it by inversion. -/
lemma nonempty_mulEquiv_dihedralGroup : Nonempty (HeisenbergGroup (ZMod 2) ≃* DihedralGroup 4) := by
  let a : HeisenbergGroup (ZMod 2) := ⟨1, 1, 0⟩
  let c : HeisenbergGroup (ZMod 2) := ⟨1, 0, 0⟩
  have ha : orderOf a = 4 := orderOf_eq_prime_pow (p := 2) (n := 1)
    (fun h ↦ by simpa [a, pow_eq] using congrArg z h) (by ext <;> simp <;> decide)
  have hN : (zpowers a).index = 2 := by
    have h : Nat.card (zpowers a) * (zpowers a).index = Nat.card (HeisenbergGroup (ZMod 2)) :=
      (zpowers a).card_mul_index
    rw [Nat.card_zpowers, ha, natCard_zmod] at h
    omega
  have hc : c ∉ zpowers a := fun h ↦ by
    rcases mem_zpowers_iff.mp h with ⟨k, hk⟩
    have hca : c * a = a * c := hk ▸ ((Commute.refl a).zpow_left k).eq
    simpa [a, c] using congrArg z hca
  rcases nonempty_mulEquiv_semidirectProduct_of_sq_eq_one hN ha hc
    (by ext <;> simp [c, pow_eq, (by decide : (2 : ZMod 2) = 0)]) (DihedralGroup.neg_one_units_sq 4)
    (DihedralGroup.natCast_sub_one_eq_neg_one 4) (by ext <;> simp <;> decide)
    with ⟨f⟩
  exact ⟨f.trans (DihedralGroup.mulEquivSemidirectProduct 4).symm⟩

/-- **The non-abelian groups of order `8`** (LMFDB `group.heisenberg`): such a group is isomorphic
to the Heisenberg group `He₂ ≅ D₄` or to the quaternion group `Q₈`. -/
lemma nonempty_mulEquiv_or_nonempty_mulEquiv_quaternionGroup (hG : Nat.card G = 2 ^ 3)
    (hnc : ¬IsMulCommutative G) :
    Nonempty (G ≃* HeisenbergGroup (ZMod 2)) ∨ Nonempty (G ≃* QuaternionGroup 2) :=
  (nonempty_mulEquiv_dihedralGroup_or_nonempty_mulEquiv_quaternionGroup hG hnc).imp
    (fun ⟨f⟩ ↦ ⟨f.trans nonempty_mulEquiv_dihedralGroup.some.symm⟩) id

/-- **`He₂` and `Q₈` are not isomorphic** (LMFDB `group.heisenberg`): `He₂ ≅ D₄` has `6` solutions
of `g² = 1` and `Q₈` has `2`. -/
lemma isEmpty_mulEquiv_quaternionGroup :
    IsEmpty (HeisenbergGroup (ZMod 2) ≃* QuaternionGroup 2) := by
  refine ⟨fun f ↦ absurd (nonempty_mulEquiv_dihedralGroup.some.symm.trans f).card_sq_eq_one ?_⟩
  rw [DihedralGroup.card_sq_eq_one (by norm_num), QuaternionGroup.card_sq_eq_one]
  norm_num

/-- **`He_p` is one of only two non-abelian groups of order `p³`** (LMFDB `group.heisenberg`): there
is a group `K`, the quaternion group `Q₈` for `p = 2` and the modular group `M_{p³}` for odd `p`,
such that the non-abelian groups of order `p³` not isomorphic to `He_p` are exactly the groups
isomorphic to `K`. -/
lemma exists_forall_iff_nonempty_mulEquiv : ∃ (K : Type) (_ : Group K), ∀ (H : Type u) [Group H],
    Nat.card H = p ^ 3 ∧ ¬IsMulCommutative H ∧ IsEmpty (H ≃* HeisenbergGroup (ZMod p)) ↔
      Nonempty (H ≃* K) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨QuaternionGroup 2, inferInstance, fun H _ ↦ ⟨fun ⟨hH, hnc, he⟩ ↦ ?_, ?_⟩⟩
    · exact (nonempty_mulEquiv_or_nonempty_mulEquiv_quaternionGroup hH hnc).resolve_left
        (not_nonempty_iff.mpr he)
    · rintro ⟨f⟩
      refine ⟨?_, fun h ↦ QuaternionGroup.not_isMulCommutative le_rfl f.surjective.isMulCommutative,
        ⟨fun g ↦ isEmpty_mulEquiv_quaternionGroup.false (g.symm.trans f)⟩⟩
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      rfl
  · refine ⟨ModularPCubedGroup p, inferInstance, fun H _ ↦ ⟨fun ⟨hH, hnc, he⟩ ↦ ?_, ?_⟩⟩
    · exact (nonempty_mulEquiv_or_nonempty_mulEquiv_modularPCubedGroup hp2 hH hnc).resolve_left
        (not_nonempty_iff.mpr he)
    · rintro ⟨f⟩
      refine ⟨by rw [Nat.card_congr f.toEquiv, ModularPCubedGroup.natCard],
        fun h ↦ ModularPCubedGroup.not_isMulCommutative p f.surjective.isMulCommutative,
        ⟨fun g ↦ (isEmpty_mulEquiv_modularPCubedGroup hp2).false (g.symm.trans f)⟩⟩

end TauCeti.HeisenbergGroup
