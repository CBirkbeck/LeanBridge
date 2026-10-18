/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Algebra.Group.Subgroup.Finsupp
import LeanBridge.IdealArithmetic.ClassGroupEquiv.ClassGroupEquiv

/- # Group p-saturation

Results to prove an isomorphism between a finite group `G` and an abstract group
`(∀ i : ι , (ZMod (n i)))`

## Main definition
- `AddEquivOfGenerators`: an isomorphism `(∀ i : ι , (ZMod (n i))) ≃+ G` if the tuple
  `x` of elements in `G` is `p`-saturated for every prime `p`.
- `equivClassGroupOfSaturated` : The corresponding isomorphism between the class group
  and an abstract finite group, with the conditions for `p`-saturation stated
  in terms of integral ideals.

## Main results
- `class_number_of_saturated`: the class number of a Dedekind domain `S` given a
  tuple of ideals of `S` that is `p`-saturated for every prime `p`.  -/

lemma addOrderOf_ne_eq_addSubgroup {ι : Type*} (n : ι → ℕ) [∀ i, NeZero (n i)]
    {p : ℕ} (hpos : 1 < p) (H : AddSubgroup (∀ i : ι , (ZMod (n i))))
    (hdvd : ∀ a : ι → ℕ, (fun i => ↑(a i)) ∈ H →  (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    ∀ b ∈ H , addOrderOf b ≠ p := by
  by_contra! hc
  obtain ⟨b, hb1, hb2⟩ := hc
  rw [addOrderOf_eq_iff (by omega)] at hb2
  specialize hdvd (fun i => (b i).val)
  suffices h : b = 0 from by
    · rw [h] at hb2
      simp only [smul_zero, ne_eq, not_true_eq_false, imp_false, not_lt, nonpos_iff_eq_zero,
        true_and] at hb2
      specialize hb2 1 hpos
      contradiction
  ext i
  dsimp
  rw [← ZMod.natCast_zmod_val (b i), ZMod.natCast_eq_zero_iff]
  refine hdvd ?_ ?_ i
  · convert hb1
    exact ZMod.natCast_zmod_val (b _)
  · intro i
    rcases hb2 with ⟨hb21, hb22⟩
    apply_fun (fun f => f i) at hb21
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at hb21
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id_eq, hb21]

/-- Condition for `p` not dividing the kernel of a morphism `(∀ i : ι , (ZMod (n i))) →+ G`. -/
lemma addHom_card_ker_dvd_of_dvd {G : Type*} [AddGroup G] {ι : Type*} [Finite ι]
    {n : ι → ℕ} [∀ i, NeZero (n i)] {p : ℕ} [hp: Fact $ Nat.Prime p]
    (φ : (∀ i : ι , (ZMod (n i))) →+ G)
    (hdvd : ∀ a : ι → ℕ, φ (fun i => a i) = 0 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    ¬ p ∣ Nat.card (φ.ker) := by
  intro hc
  haveI : Fintype (φ.ker) := Fintype.ofFinite ↥φ.ker
  obtain ⟨b, hb⟩ := exists_prime_addOrderOf_dvd_card (G := φ.ker) p
    (by rw [Fintype.card_eq_nat_card] ; exact hc)
  refine addOrderOf_ne_eq_addSubgroup n (Nat.Prime.one_lt hp.out) φ.ker ?_ b.1 b.2 ?_
  · intro a ha i hi
    exact hdvd a (AddMonoidHom.mem_ker.1 ha) i hi
  · rw [AddSubgroup.addOrderOf_coe]
    exact hb

lemma addHom_injective_of_dvd {G : Type*} [AddGroup G] {ι : Type*} [Fintype ι]
    {n : ι → ℕ} [∀ i, NeZero (n i)]
    (φ : (∀ i : ι , (ZMod (n i))) →+ G)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, φ (fun i => a i) = 0 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    Function.Injective φ := by
  refine (AddMonoidHom.ker_eq_bot_iff φ).mp ?_
  rw [← AddSubgroup.card_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp
  haveI : Fact $ Nat.Prime p := {out := hp}
  by_cases hc : p ∣ ∏ i, n i
  · specialize hdvd p hp hc
    exact addHom_card_ker_dvd_of_dvd φ hdvd
  · intro hdvd
    have := dvd_trans hdvd (AddSubgroup.card_addSubgroup_dvd_card φ.ker)
    rw [Nat.card_pi] at this
    simp only [Nat.card_eq_fintype_card, ZMod.card] at this
    exact hc this

/-- For a surjective map `(∀ i : ι , (ZMod (n i))) →+ G`, the corresponding
isomorphism if the `p`-saturation condition is satisfied for every prime `p`. -/
noncomputable def EquivOfSurjectiveOfDvd {G : Type*} [AddGroup G] {ι : Type*} [Fintype ι]
    {n : ι → ℕ} [∀ i, NeZero (n i)]
    (φ : (∀ i : ι , (ZMod (n i))) →+ G) (hs : Function.Surjective φ)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, φ (fun i => a i) = 0 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    (∀ i : ι , (ZMod (n i))) ≃+ G := by
  apply AddEquiv.ofBijective φ
  constructor
  · exact addHom_injective_of_dvd φ hdvd
  · exact hs

/-- For a collection of elements `g` in `G` such that `(n i) · (g i) = 0`, the map
`(∀ i : ι , (ZMod (n i))) →+ G` that sends `(a₁ , … , aₖ)` to `a₁ · g₁ + … + aₖ · gₖ`. -/
def AddHomOfGenerators {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)]
    (h : ∀ i, (n i) • (g i) = 0) : (∀ i : ι , (ZMod (n i))) →+ G where
  toFun := by
    intro x
    exact ∑ i, (x i).val • (g i)
  map_zero' := by
    simp only [Pi.zero_apply, ZMod.val_zero, zero_smul, Finset.sum_const_zero]
  map_add' := by
    intro x y
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← add_nsmul, nsmul_eq_nsmul_iff_modEq, Nat.modEq_iff_dvd]
    refine dvd_trans (Nat.cast_dvd_cast (addOrderOf_dvd_iff_nsmul_eq_zero.2 (h i))) ?_
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp only [Pi.add_apply, ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_add', ZMod.cast_id',
      id_eq, Nat.cast_add, Int.cast_add]

lemma AddHomOfGenerators_apply {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)]
    (h : ∀ i, (n i) • (g i) = 0) (x : ∀ i : ι , (ZMod (n i))) :
    AddHomOfGenerators h x = ∑ i, (x i).val • (g i) := by rfl

lemma AddHomOfGenerators_surjective {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)]
    (h : ∀ i, (n i) • (g i) = 0) (hgen : AddSubgroup.closure (Set.range g) = ⊤) :
    Function.Surjective (AddHomOfGenerators h) := by
  intro y
  have ymem : y ∈ AddSubgroup.closure (Set.range g) := by
    rw [hgen]
    exact trivial
  obtain ⟨a, ha⟩ := AddSubgroup.exists_of_mem_closure_range g y ymem
  use (fun i => (a i))
  rw [AddHomOfGenerators_apply, ha]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← natCast_zsmul, zsmul_eq_zsmul_iff_modEq, Int.modEq_iff_dvd]
  refine dvd_trans (Nat.cast_dvd_cast (addOrderOf_dvd_iff_nsmul_eq_zero.2 (h i))) ?_
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_intCast']

/-- The isomorphism induced by `AddHomOfGenerators` and the tuple
`x` of elements in `G` if the `p`-saturation condition is satisfied for every prime `p`.-/
noncomputable def AddEquivOfGenerators {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)] (h : ∀ i, (n i) • (g i) = 0)
    (hgen : AddSubgroup.closure (Set.range g) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∑ i, (a i) • (g i) = 0 →(∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    (∀ i : ι , (ZMod (n i))) ≃+ G := by
  refine EquivOfSurjectiveOfDvd (AddHomOfGenerators h) (AddHomOfGenerators_surjective h hgen) ?_
  intro p hp hpdvd a ha
  rw [AddHomOfGenerators_apply] at ha
  apply hdvd p hp hpdvd
  rw [← ha]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← natCast_zsmul, ← natCast_zsmul, zsmul_eq_zsmul_iff_modEq, Int.modEq_iff_dvd]
  refine dvd_trans (Nat.cast_dvd_cast (addOrderOf_dvd_iff_nsmul_eq_zero.2 (h i))) ?_
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp only [Int.cast_natCast, ZMod.val_natCast, Int.natCast_emod, ZMod.intCast_mod]

lemma AddEquivOfGenerators_apply {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)] (h : ∀ i, (n i) • (g i) = 0)
    (hgen : AddSubgroup.closure (Set.range g) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∑ i, (a i) • (g i) = 0 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i)
    (x : ∀ i : ι , (ZMod (n i))) :
    AddEquivOfGenerators h hgen hdvd x = ∑ i, (x i).val • (g i) := by rfl

/-- Multiplicative version of `AddEquivOfGenerators`. -/
noncomputable def AddEquivOfGeneratorsMult {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)] (h : ∀ i, (g i) ^ (n i) = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∏ i, (g i) ^ (a i) = 1 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    (∀ i : ι , (ZMod (n i))) ≃+ Additive G := by
  refine AddEquivOfGenerators (g := g) (n := n) (G := Additive G) h ?_ hdvd
  · apply_fun Subgroup.toAddSubgroup at hgen
    rw [Subgroup.toAddSubgroup_closure, ← Equiv.image_symm_eq_preimage,
      ← Set.range_comp] at hgen
    simp only [Additive.toMul_symm_eq, map_top] at hgen
    exact hgen

lemma card_of_generators_saturated {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)] (h : ∀ i, (g i) ^ (n i) = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∏ i, (g i) ^ (a i) = 1 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    Nat.card G = ∏ i, n i := by
  rw [← Nat.card_congr (Additive.toMul (α := G)),
    Nat.card_congr (AddEquivOfGeneratorsMult h hgen hdvd).symm.toEquiv , Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

--#count_heartbeats in
/-- Version of `AddEquivOfGeneratorsMult` for the class group of a Dedekind domain `S`. -/
noncomputable def equivClassGroupOfSaturated {S : Type*} [CommRing S] [IsDomain S]
    [IsDedekindDomain S] {ι : Type*} [Fintype ι]
    {n : ι → ℕ} [∀ i, NeZero (n i)]  {I : ι → Ideal S} {I' : ι → nonZeroDivisors (Ideal (S))}
    (hI' : ∀ i, ↑(I' i) = I i) {a : ι → S} (h : ∀ i, (I i) ^ (n i) = Ideal.span {a i})
    (hgen : Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (I' i))) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
        ∀ a : ι → ℕ, ∀ b : S, ∏ i, (I i) ^ (a i) = Ideal.span {b} →
          (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    (∀ i : ι , (ZMod (n i))) ≃+ Additive (ClassGroup S) := by
  refine AddEquivOfGeneratorsMult (G := ClassGroup S) (g := (fun i => ClassGroup.mk0 (I' i)))
    (n := n) ?_ hgen ?_
  · intro i
    rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.coe_pow, hI']
    use (a i)
    exact h i
  · intro p hp hpdvd a heq
    simp_rw [← map_pow, ← map_prod] at heq
    have aux : (∏ x, I' x ^ a x) = ⟨ (∏ x, I' x ^ a x).1 , (∏ x, I' x ^ a x).2 ⟩ := rfl
    simp [hI'] at aux
    rw [aux, ClassGroup.mk0_eq_one_iff] at heq
    obtain ⟨b ,hb⟩ := heq
    specialize hdvd p hp hpdvd a b
    apply hdvd
    exact hb

@[simp]
lemma equivClassGroupOfSaturated_apply {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
    {ι : Type*} [Fintype ι]
    {n : ι → ℕ} [∀ i, NeZero (n i)]  {I : ι → Ideal S} {I' : ι → nonZeroDivisors (Ideal (S))}
    (hI' : ∀ i, ↑(I' i) = I i) {a : ι → S} (h : ∀ i, (I i) ^ (n i) = Ideal.span {a i})
    (hgen : Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (I' i))) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
        ∀ a : ι → ℕ, ∀ b : S, ∏ i, (I i) ^ (a i) = Ideal.span {b} →
          (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) (x : ∀ i : ι , (ZMod (n i))) :
    Additive.toMul (equivClassGroupOfSaturated hI' h hgen hdvd x) =
      ∏ i, ClassGroup.mk0 (I' i) ^ (x i).val := rfl

variable {K : Type*} [Field K] [NumberField K]

local notation "Oκ" => NumberField.RingOfIntegers K

/-- The class number of a number field if the `p` saturated condition is satisfied for every `p`. -/
lemma class_number_of_saturated {S : Subalgebra ℤ K} [IsDedekindDomain S]
    {ι : Type*} [Fintype ι] (heq : S = integralClosure ℤ K)
    {n : ι → ℕ} [∀ i, NeZero (n i)]  {I : ι → Ideal S} {I' : ι → nonZeroDivisors (Ideal S)}
    (hI' : ∀ i, ↑(I' i) = I i) {a : ι → S} (h : ∀ i, (I i) ^ (n i) = Ideal.span {a i})
    (hgen : Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (I' i))) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
        ∀ a : ι → ℕ, ∀ b : S, ∏ i, (I i) ^ (a i) = Ideal.span {b} →
          (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    NumberField.classNumber K =  ∏ i, n i := by
  unfold NumberField.classNumber
  have : ClassGroup S ≃* ClassGroup Oκ :=
    ClassGroup.congr (Subalgebra.equivOfEq _ _ heq).toRingEquiv
  rw [Fintype.card_eq_nat_card, ← Nat.card_congr this.toEquiv,
  ← Nat.card_congr (Additive.toMul (α := ClassGroup S)),
    Nat.card_congr (equivClassGroupOfSaturated hI' h hgen hdvd).symm.toEquiv , Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

section Principal

-- Some results specialized to the case of a cyclic class group expressed in terms of nonprincipality
-- of the powers of a generator. Somewhat redundant now, might remove.

lemma class_order_of_not_principal {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
    {n : ℕ} [NeZero n]  {I : Ideal S} {I' : nonZeroDivisors (Ideal (S))}
    (hI' : ↑I' = I) {α : S} (h : I ^ n = Ideal.span {α})
    (hdvd : ∀ p, Nat.Prime p → p ∣ n → ¬ ∃ b, I ^ (n / p) = Ideal.span {b}) :
    orderOf (ClassGroup.mk0 I') = n := by
  apply orderOf_eq_of_pow_and_pow_div_prime
  · exact Nat.pos_of_neZero n
  · rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.coe_pow, hI']
    use α
  · intro p hp hpdvd hc
    rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.coe_pow, hI'] at hc
    apply hdvd p hp hpdvd
    obtain ⟨b, hb⟩ := hc
    use b

noncomputable def equivClassGroupCyclicOfSaturated {S : Type*} [CommRing S] [IsDomain S]
    [IsDedekindDomain S] {n : ℕ} [NeZero n]  {I : Ideal S} {I' : nonZeroDivisors (Ideal (S))}
    (hI' : ↑I' = I) {α : S} (h : I ^ n = Ideal.span {α})
    (hgen : Subgroup.closure (Set.range (fun (_ : Fin 1) => ClassGroup.mk0 I')) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ n → ¬ ∃ b, I ^ (n / p) = Ideal.span {b}) :
    ZMod n ≃+ Additive (ClassGroup S) := by
  refine AddEquiv.trans ((AddEquiv.piUnique fun (j : Fin 1) ↦ ZMod n).symm) ?_
  refine equivClassGroupOfSaturated (n := fun (i : Fin 1) => n) (a := fun _ => α)
    (I := fun (i : Fin 1) => I) (I' := fun (i : Fin 1) => I') ?_ ?_ hgen ?_
  · simp only [hI', implies_true]
  · simp only [h, implies_true]
  · intro p hp hpdvd a b heq i hdvd
    obtain ⟨z, hz⟩ := hdvd
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.prod_const,
      Finset.card_singleton, pow_one] at hpdvd
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.prod_singleton] at heq
    have : (ClassGroup.mk0 I') ^ (a 0) = 1 := by
       rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.coe_pow, hI']
       exact ⟨b, heq⟩
    convert orderOf_dvd_of_pow_eq_one this
    exact (class_order_of_not_principal hI' h hdvd).symm

lemma equivClassGroupCyclicOfSaturated_apply {S : Type*} [CommRing S] [IsDomain S]
    [IsDedekindDomain S] {n : ℕ} [NeZero n]  {I : Ideal S} {I' : nonZeroDivisors (Ideal (S))}
    (hI' : ↑I' = I) {α : S} (h : I ^ n = Ideal.span {α})
    (hgen : Subgroup.closure (Set.range (fun (_ : Fin 1) => ClassGroup.mk0 I')) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ n → ¬ ∃ b, I ^ (n / p) = Ideal.span {b}) (x : ZMod n) :
    Additive.toMul (equivClassGroupCyclicOfSaturated hI' h hgen hdvd x) =
      ClassGroup.mk0 I' ^ x.val := by
  unfold equivClassGroupCyclicOfSaturated
  simp only [AddEquiv.trans_apply, equivClassGroupOfSaturated_apply, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, AddEquiv.piUnique_symm_apply, uniqueElim_const,
    Finset.prod_const, Finset.card_singleton, pow_one]

lemma class_number_of_saturated_of_cyclic {S : Subalgebra ℤ K} [IsDedekindDomain S]
    {ι : Type*} [Fintype ι] (heq : S = integralClosure ℤ K)
    {n : ℕ} [NeZero n]  {I : Ideal S} {I' : nonZeroDivisors (Ideal S)}
    (hI' : ↑I' = I) {a : S} (h : I ^ n = Ideal.span {a})
    (hgen : Subgroup.closure (Set.range (fun (_ : Fin 1) => ClassGroup.mk0 I')) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ n → ¬ ∃ b, I ^ (n / p) = Ideal.span {b}) :
    NumberField.classNumber K =  n := by
  unfold NumberField.classNumber
  have : ClassGroup S ≃* ClassGroup Oκ :=
    ClassGroup.congr (Subalgebra.equivOfEq _ _ heq).toRingEquiv
  rw [Fintype.card_eq_nat_card, ← Nat.card_congr this.toEquiv]
  rw [← Nat.card_congr (Additive.toMul (α := ClassGroup S)),
    Nat.card_congr (equivClassGroupCyclicOfSaturated  hI' h hgen hdvd).symm.toEquiv]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

end Principal
