import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Rational conjugacy classes (divisions) of a group

## Main definitions

* `IsRationallyConj`, `IsRationallyConj.setoid` and `RatConjClasses` (LMFDB `group.division`).
* `Subgroup.IsMaximalCyclic` and `RatConjClasses.IsMaximal` (LMFDB `group.division_maximal`).

## Main results

* `IsRationallyConj.equivalence`: rational conjugacy is an equivalence relation.
* `RatConjClasses.isMaximal_mk_iff`: maximality of a division does not depend on the
  representative.
* `IsConj.isRationallyConj`: conjugate elements are rationally conjugate, so every division is a
  union of conjugacy classes.
-/

variable {G : Type*} [Group G] {x y z : G}

/-- Two elements `x` and `y` of `G` are **rationally conjugate** (LMFDB `group.division`) if
`y = g⁻¹ xⁿ g` for some `g ∈ G` and some `n ∈ ℤ` coprime to the order of `x`. -/
def IsRationallyConj (x y : G) : Prop :=
  ∃ n : ℤ, n.gcd (orderOf x) = 1 ∧ IsConj (x ^ n) y

/-- Conjugate elements are rationally conjugate. -/
lemma IsConj.isRationallyConj (h : IsConj x y) : IsRationallyConj x y :=
  ⟨1, Int.gcd_one_left _, (zpow_one x).symm ▸ h⟩

lemma IsConj.zpow_isConj (h : IsConj x y) (n : ℤ) : IsConj (x ^ n) (y ^ n) := by
  rcases isConj_iff.mp h with ⟨c, rfl⟩
  exact isConj_iff.mpr ⟨c, conj_zpow.symm⟩

lemma IsConj.orderOf_eq (h : IsConj x y) : orderOf x = orderOf y := by
  rcases isConj_iff.mp h with ⟨c, rfl⟩
  exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x).symm

lemma orderOf_zpow_of_gcd_eq_one {n : ℤ} (hn : n.gcd (orderOf x) = 1) :
    orderOf (x ^ n) = orderOf x := by
  rw [← orderOf_pow_natAbs]
  exact (Nat.coprime_comm.mp hn).orderOf_pow

lemma IsRationallyConj.orderOf_eq (h : IsRationallyConj x y) : orderOf x = orderOf y := by
  rcases h with ⟨n, hn, h⟩
  exact (orderOf_zpow_of_gcd_eq_one hn).symm.trans h.orderOf_eq

lemma mul_gcdA_add_mul_gcdB {n : ℤ} (hn : n.gcd (orderOf x) = 1) :
    n * n.gcdA (orderOf x) + orderOf x * n.gcdB (orderOf x) = 1 := by
  rw [← Int.gcd_eq_gcd_ab, hn, Nat.cast_one]

lemma zpow_zpow_gcdA {n : ℤ} (hn : n.gcd (orderOf x) = 1) : (x ^ n) ^ n.gcdA (orderOf x) = x := by
  rw [← zpow_mul, eq_sub_of_add_eq <| mul_gcdA_add_mul_gcdB hn, zpow_sub, zpow_one, zpow_mul,
    zpow_natCast, pow_orderOf_eq_one, one_zpow, inv_one, mul_one]

lemma zpowers_zpow_of_gcd_eq_one {n : ℤ} (hn : n.gcd (orderOf x) = 1) :
    Subgroup.zpowers (x ^ n) = Subgroup.zpowers x :=
  le_antisymm (Subgroup.zpowers_le.mpr <| zpow_mem (Subgroup.mem_zpowers x) n) <|
    Subgroup.zpowers_le.mpr ⟨_, zpow_zpow_gcdA hn⟩

lemma IsRationallyConj.refl (x : G) : IsRationallyConj x x :=
  IsConj.refl x |>.isRationallyConj

lemma IsRationallyConj.symm (h : IsRationallyConj x y) : IsRationallyConj y x := by
  have ho : orderOf x = orderOf y := h.orderOf_eq
  rcases h with ⟨n, hn, h⟩
  refine ⟨n.gcdA (orderOf x), ?_,
    (h.zpow_isConj _).symm.trans <| (congrArg (IsConj _) <| zpow_zpow_gcdA hn).mp <| .refl _⟩
  rw [← ho, ← Int.isCoprime_iff_gcd_eq_one]
  exact ⟨n, n.gcdB (orderOf x),
    mul_comm (orderOf x : ℤ) (n.gcdB (orderOf x)) ▸ mul_gcdA_add_mul_gcdB hn⟩

lemma IsRationallyConj.trans (hxy : IsRationallyConj x y) (hyz : IsRationallyConj y z) :
    IsRationallyConj x z := by
  have ho : orderOf x = orderOf y := hxy.orderOf_eq
  rcases hxy with ⟨n, hn, hxy⟩
  rcases hyz with ⟨m, hm, hyz⟩
  refine ⟨n * m, ?_, zpow_mul x n m ▸ (hxy.zpow_isConj m).trans hyz⟩
  rw [ho] at hn ⊢
  rw [← Int.isCoprime_iff_gcd_eq_one] at hn hm ⊢
  exact hn.mul_left hm

/-- Rational conjugacy is an equivalence relation. -/
lemma IsRationallyConj.equivalence : Equivalence (IsRationallyConj (G := G)) :=
  ⟨refl, symm, trans⟩

variable (G) in
/-- The **rational conjugacy** setoid (LMFDB `group.division`) on `G`. -/
def IsRationallyConj.setoid : Setoid G :=
  ⟨IsRationallyConj, equivalence⟩

variable (G) in
/-- The **divisions** or **rational conjugacy classes** (LMFDB `group.division`) of `G`, the
equivalence classes of rational conjugacy. -/
def RatConjClasses : Type _ :=
  Quotient (IsRationallyConj.setoid G)

/-- A subgroup is a **maximal cyclic subgroup** of `G` if it is cyclic and not properly contained
in a cyclic subgroup of `G`. -/
def Subgroup.IsMaximalCyclic (H : Subgroup G) : Prop :=
  Maximal (fun K : Subgroup G ↦ IsCyclic K) H

/-- The rational conjugacy class of `x`. -/
def RatConjClasses.mk (x : G) : RatConjClasses G :=
  Quotient.mk _ x

/-- A division of `G` is **maximal** (LMFDB `group.division_maximal`) if a representative
generates a maximal cyclic subgroup of `G`. -/
def RatConjClasses.IsMaximal (d : RatConjClasses G) : Prop :=
  ∃ x : G, RatConjClasses.mk x = d ∧ (Subgroup.zpowers x).IsMaximalCyclic

lemma Subgroup.isMaximalCyclic_map_iff (e : G ≃* G) (H : Subgroup G) :
    (H.map e.toMonoidHom).IsMaximalCyclic ↔ H.IsMaximalCyclic := by
  refine (MulEquiv.mapSubgroup e).toOrderEmbedding.maximal_apply_mem_iff (t := {K | IsCyclic K})
    (fun K _ ↦ (MulEquiv.mapSubgroup e).surjective K) |>.trans <| Iff.of_eq <|
    congrArg (Maximal · H) <| funext fun K ↦ propext ?_
  exact (K.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.symm

lemma IsRationallyConj.isMaximalCyclic_zpowers_iff (h : IsRationallyConj x y) :
    (Subgroup.zpowers x).IsMaximalCyclic ↔ (Subgroup.zpowers y).IsMaximalCyclic := by
  rcases h with ⟨n, hn, h⟩
  rcases isConj_iff.mp h with ⟨c, rfl⟩
  rw [← zpowers_zpow_of_gcd_eq_one hn, ← Subgroup.isMaximalCyclic_map_iff (MulAut.conj c),
    MonoidHom.map_zpowers]
  rfl

/-- Maximality of a division does not depend on the representative: the division of `x` is
maximal if and only if `x` generates a maximal cyclic subgroup. -/
lemma RatConjClasses.isMaximal_mk_iff :
    (RatConjClasses.mk x).IsMaximal ↔ (Subgroup.zpowers x).IsMaximalCyclic :=
  ⟨fun ⟨_, hy, h⟩ ↦ (Quotient.exact hy).isMaximalCyclic_zpowers_iff.mp h, fun h ↦ ⟨x, rfl, h⟩⟩
