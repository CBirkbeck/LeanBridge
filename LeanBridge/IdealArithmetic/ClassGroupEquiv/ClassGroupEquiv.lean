/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Maps between class groups

An injective morphism between domains induces a map between class groups. In particular,
class groups of isomorphic domains are isomorphic.

## Main definition
- `FractionalIdeal.mapOfInjective'`: given an injective `R →+* S`, maps
  fractional ideals of `R` to fractional ideals of `S`.
- `ClassGroup.mapOfInjective` : given an injective `R →+* S` between domains, maps
  the class group of `R` to  the class group of `S`.
- `ClassGroup.congr`: given an isomorphism `R ≃+* S`, this is the induced isomorphism
  between class groups.

## Main results
- `FractionalIdeal.mapOfInjective_apply_int'` : the application of the map
  `FractionalIdeal.mapOfInjective'` to integral ideals corresponds to `Ideal.map`.
- `ClassGroup.mapOfInjective_apply'`: the map `ClassGroup.mapOfInjective` applied to integral
  ideals of Dedekind domains.  -/

open FractionalIdeal
open Pointwise

/-- Given a fractional ideal `I` in `P` with respect to a submonoid `S₁` of `R`, express `S ·I`
  as a product of fractional ideals over a submonoid `S₂` of `S` consisting of units in `P`. -/
lemma FractionalIdeal.den_mul_self_eq_num'' {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    (S₁ : Submonoid R) (S₂ : Submonoid S) [IsLocalization S₂ P] (I : FractionalIdeal S₁ P)
    (hu : IsUnit ((algebraMap R P) ↑I.den)) :
    Submodule.span S (I : Set P) =
    FractionalIdeal.coeToSubmodule ((FractionalIdeal.spanSingleton  (S := S₂) ((hu.unit.inv) : P))
      *  FractionalIdeal.coeIdeal (Ideal.map (algebraMap R S) I.num)) := by
  have aux1 := FractionalIdeal.den_mul_self_eq_num I
  apply_fun (fun x => x.carrier) at aux1
  apply_fun Submodule.span S at aux1
  simp only [ Submodule.carrier_eq_coe, Submodule.map_coe,
    Algebra.linearMap_apply] at aux1
  have aux := Submodule.span_smul (R := S) ((I.den)) (I : Set P)
  apply_fun (fun x => (((algebraMap R S) ↑(I.den)) • x : Submodule S P))
  simp
  convert aux1
  convert aux.symm using 1
  · rw [← aux, Submodule.smul_span]
    congr
    ext x
    simp_rw [Set.mem_smul_set, Algebra.smul_def,
      Eq.symm (IsScalarTower.algebraMap_apply R S P _), ← Algebra.smul_def]
    rfl
  · rfl
  · unfold Ideal.map Ideal.span
    rw [Ideal.submodule_span_eq, IsLocalization.coeSubmodule_span,
      ← Set.image_comp, Submodule.span_mul_span, ← Submodule.span_smul (algebraMap R S (I.den )) _]
    congr
    have auxf := IsScalarTower.algebraMap_eq R S P
    apply_fun (fun x => x.toFun) at auxf
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, RingHom.coe_comp] at auxf
    rw [← auxf, Set.singleton_mul]
    ext x
    rw [Set.mem_smul_set]
    simp only [Set.mem_image, SetLike.mem_coe, exists_exists_and_eq_and, algebraMap_smul]
    simp_rw [Algebra.smul_def, ← mul_assoc, IsUnit.mul_val_inv, one_mul, Algebra.linearMap_apply]
  · refine Function.Injective.of_eq_imp_le ( f := fun x ↦ (algebraMap R S) ↑I.den • x) ?_
    intro x y hxy i hi
    have :=  hxy ▸ (Submodule.smul_mem_pointwise_smul i ((algebraMap R S) ↑I.den) x hi)
    rw [Submodule.mem_smul_pointwise_iff_exists] at this
    obtain ⟨b, hb1, hb2⟩ := this
    apply_fun (fun x => (hu.unit.inv) • x) at hb2
    simp_rw [Algebra.smul_def _ b, ← (IsScalarTower.algebraMap_apply R S P ↑I.den),
      Algebra.smul_def _ i, ← (IsScalarTower.algebraMap_apply R S P ↑I.den) , Algebra.smul_def] at hb2
    simp only [ ← mul_assoc, Algebra.algebraMap_self_apply, Units.inv_eq_val_inv, IsUnit.val_inv_mul,
      one_mul] at hb2
    rw [← hb2]
    exact hb1

/-- Maps fractional ideals with respect to submonoid of `R` to fractional ideals with respect
  to a submonoid of `S`. -/
noncomputable def FractionalIdeal.map_map {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    {S₁ : Submonoid R} {S₂ : Submonoid S} [IsLocalization S₂ P]
    (h : (algebraMap R S)'' S₁ ≤ S₂) : FractionalIdeal S₁ P →* FractionalIdeal S₂ P where
  toFun := by
    intro I
    have hu : IsUnit ((algebraMap R P) I.den) := by
      rw [← Eq.symm (IsScalarTower.algebraMap_apply R S P _)]
      refine IsLocalization.map_units _ (⟨(algebraMap R S) ↑I.den , ?_ ⟩ : S₂)
      apply h
      use I.den.1 , I.den.2
    let J := FractionalIdeal.spanSingleton  (S := S₂) hu.unit.inv
    let II := (Ideal.map (algebraMap R S) I.num : FractionalIdeal S₂ P)
    exact J * II
  map_one' := by
    dsimp
    apply_fun FractionalIdeal.coeToSubmodule
    have : (↑(1 : FractionalIdeal S₁ P) : Set P) = ↑(1 : Submodule R P) := by
      rw [← FractionalIdeal.coe_one]
      rfl
    erw [← FractionalIdeal.den_mul_self_eq_num'' S₁ S₂ 1 ]
    simp_rw [FractionalIdeal.coe_one, this,
      Submodule.one_eq_span, Submodule.span_span_of_tower]
    · exact coeToSubmodule_injective
  map_mul' := by
    dsimp
    intro x y
    apply_fun FractionalIdeal.coeToSubmodule
    nth_rw 2 [coe_mul]
    erw [← FractionalIdeal.den_mul_self_eq_num'', ← FractionalIdeal.den_mul_self_eq_num''
    , ← FractionalIdeal.den_mul_self_eq_num'']
    have : Submodule.span S (↑(x * y) : Set P) =
      Submodule.span S ((coeToSubmodule x) * (coeToSubmodule y)) := by
     congr 1
     rw [FractionalIdeal.mul_def] ; rfl
    rw [this, Submodule.mul_def, Submodule.span_span_of_tower,
      ← Submodule.span_mul_span] ; rfl
    · exact coeToSubmodule_injective

lemma FractionalIdeal.map_map_apply {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    (S₁ : Submonoid R) (S₂ : Submonoid S) [IsLocalization S₂ P]
    (h : (algebraMap R S)'' S₁ ≤ S₂)
    (I : FractionalIdeal S₁ P) : FractionalIdeal.map_map h I = Submodule.span S (I : Set P) := by
  erw [← FractionalIdeal.den_mul_self_eq_num'']

lemma FractionalIdeal.map_map_apply_int {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    (S₁ : Submonoid R) (S₂ : Submonoid S) [IsLocalization S₂ P]
    (h : (algebraMap R S)'' S₁ ≤ S₂) (I : Ideal R) :
    FractionalIdeal.map_map h (I : FractionalIdeal S₁ P) = I.map (algebraMap R S) := by
      apply_fun FractionalIdeal.coeToSubmodule
      rw [FractionalIdeal.map_map_apply, Ideal.map, coe_coeIdeal, IsLocalization.coeSubmodule_span]
      have : (↑(↑I : FractionalIdeal S₁ P) : Set P) =
        ↑(↑(↑I : FractionalIdeal S₁ P) : Submodule R P) := by rfl
      rw [this, FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule]
      simp only [Submodule.map_coe, Algebra.coe_linearMap, IsScalarTower.algebraMap_eq R S P,
        RingHom.coe_comp, ← Set.image_comp, Function.comp_def]
      exact coeToSubmodule_injective

lemma FractionalIdeal.image_nonZeroDivisors_le {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [Algebra R S] (hinj : Function.Injective (algebraMap R S)) :
    algebraMap R S '' nonZeroDivisors R ≤ nonZeroDivisors S := by
  rintro _ ⟨a, ha, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero <| (map_ne_zero_iff _ hinj).2 <| nonZeroDivisors.ne_zero ha

/-- Given an injective `R →+* S` and `P` a fraction field of `S`, map fractional ideals of `R`
  to fractional ideals of `S` (both living in `P`).  -/
noncomputable def FractionalIdeal.mapOfInjective {R S P : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [CommRing P] [Algebra R S] [Algebra R P] [Algebra S P]
    [IsScalarTower R S P] (hinj : Function.Injective (algebraMap R S)) [IsFractionRing S P] :
    FractionalIdeal (nonZeroDivisors R) P →* FractionalIdeal (nonZeroDivisors S) P :=
  FractionalIdeal.map_map (image_nonZeroDivisors_le hinj)

/-- Given an injective `R →+* S` map fractional ideals of `R` to fractional ideals of `S`.  -/
noncomputable def FractionalIdeal.mapOfInjective' {R S : Type*} (F K : Type*) [CommRing R]
    [Nontrivial R] [CommRing S] [IsDomain S] [CommRing F] [CommRing K] [Algebra R F]
    [Algebra S K] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) [IsFractionRing R F] [IsFractionRing S K] :
      FractionalIdeal (nonZeroDivisors R) F →* FractionalIdeal (nonZeroDivisors S) K := by
  letI:  Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
  let ψ : F →+* K := IsFractionRing.map hinj
  let ψa : F →ₐ[R] K := by
    refine AlgHom.mk' ψ ?_
    intro c x
    rw [Algebra.smul_def c (ψ x)]
    simp [ψ, IsFractionRing.map]
    rw [IsLocalization.map_smul, Algebra.smul_def _ _]
    rfl
  haveI : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let f : (FractionalIdeal (nonZeroDivisors R) K) →*
    (FractionalIdeal (nonZeroDivisors S) K) :=
    FractionalIdeal.mapOfInjective (hinj)
  exact
  {toFun := fun x => (f ((FractionalIdeal.map ψa) x))
   map_one' := by simp only [FractionalIdeal.map_one, map_one]
   map_mul' := by simp only [FractionalIdeal.map_mul, map_mul, implies_true]}

lemma FractionalIdeal.mapOfInjective_apply' {R S : Type*} (F K : Type*) [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [CommRing F] [CommRing K] [Algebra R F] [Algebra S K] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) [IsFractionRing R F] [IsFractionRing S K]
    (I : FractionalIdeal (nonZeroDivisors R) F) :
    FractionalIdeal.mapOfInjective' F K hinj I =
    (Submodule.span S ((IsFractionRing.map hinj)'' (↑I : Set F)) : Submodule S K) := by
  unfold mapOfInjective' mapOfInjective
  let _ : Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
  have _ : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact FractionalIdeal.map_map_apply _ _ (image_nonZeroDivisors_le hinj) _

/-- The map `FractionalIdeal.mapOfInjective'` on integral ideals is simply
  `Ideal.map (algebraMap R S)`.  -/
lemma FractionalIdeal.mapOfInjective_apply_int' {R S : Type*} (F K : Type*) [CommRing R]
    [Nontrivial R] [CommRing S] [IsDomain S] [CommRing F] [CommRing K] [Algebra R F]
    [Algebra S K] [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    [IsFractionRing R F] [IsFractionRing S K] (I : Ideal R) :
    FractionalIdeal.mapOfInjective' F K hinj I = Ideal.map (algebraMap R S) I := by
  apply_fun FractionalIdeal.coeToSubmodule
  rw [FractionalIdeal.mapOfInjective_apply', Ideal.map, coe_coeIdeal, IsLocalization.coeSubmodule_span]
  congr
  ext i
  unfold IsFractionRing.map
  simp only [Set.mem_image, SetLike.mem_coe, mem_coeIdeal, exists_exists_and_eq_and,
    IsLocalization.map_eq]
  · exact coeToSubmodule_injective

/-- Given an injective morhism ` R →+* S` between domains, this is the induced group homomorphism
  between class groups. -/
noncomputable def ClassGroup.mapOfInjective {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain R] [IsDomain S] {φ : R →+* S} (hinj : Function.Injective φ) :
    ClassGroup R →* ClassGroup S := by
  let F := FractionRing R
  let K := FractionRing S
  letI : Algebra R S := φ.toAlgebra
  letI :  Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
  letI : Module R K := Algebra.toModule
  haveI :=  IsScalarTower.of_algebraMap_eq (R := R) (S := S) (A := K) (congrFun rfl)
  let ψ : F →+* K := IsFractionRing.map hinj
  unfold ClassGroup
  let g : (FractionalIdeal (nonZeroDivisors R) F) →*
    (FractionalIdeal (nonZeroDivisors S) K) := FractionalIdeal.mapOfInjective' _ _ hinj
  refine QuotientGroup.map _ _ (Units.map g) ?_
  · intro x hx
    simp only [MonoidHom.mem_range, toPrincipalIdeal_eq_iff, Subgroup.mem_comap,
      Units.coe_map, K, F] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    use (Units.map ψ) a
    rw [← ha]
    unfold g
    have : ∀ x, (mapOfInjective' _ _ hinj).toFun x =
      (mapOfInjective' (F := (FractionRing R)) (K:= FractionRing S) hinj) x  := fun x => rfl
    rw [← this]
    unfold mapOfInjective'
    dsimp
    simp only [FractionalIdeal.map, *]
    unfold FractionalIdeal.mapOfInjective
    apply_fun FractionalIdeal.coeToSubmodule
    erw [FractionalIdeal.map_map_apply]
    simp_rw [← ha, coe_spanSingleton, Submodule.map_span]
    simp only [AlgHom.toLinearMap_apply, Set.image_singleton, *]
    rw [← @Submodule.span_span_of_tower (R := R) _ (S:= S) _ _ _ _ _ ]
    rfl
    · exact coeToSubmodule_injective

-- I need algebra instance to exist for FractionalIdeal.mapOfInjective'

def ClassGroup.mapOfInjective_apply {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    (I : (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ) :
    ClassGroup.mapOfInjective hinj (ClassGroup.mk (FractionRing R) I) =
      ClassGroup.mk (FractionRing S)
        ((Units.map (FractionalIdeal.mapOfInjective' _ (FractionRing S) hinj)) I) := by
  unfold ClassGroup.mapOfInjective
  unfold ClassGroup.mk
  simp only [canonicalEquiv_self]
  rfl

/-- In the case of Dedekind domains, the map `ClassGroup.mapOfInjective` applied to integral
  ideals. -/
lemma ClassGroup.mapOfInjective_apply' {R S : Type*} [CommRing R]
    [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    (φ : R →+* S) (hinj : Function.Injective φ)
    (I : nonZeroDivisors (Ideal R)) (J : nonZeroDivisors (Ideal S))
    (hI : ↑J = Ideal.map φ I) : ClassGroup.mapOfInjective hinj (mk0 I) = mk0 J := by
  letI : Algebra R S := φ.toAlgebra
  erw [← ClassGroup.mk_mk0 (K := FractionRing R), ClassGroup.mapOfInjective_apply hinj,
    ← ClassGroup.mk_mk0 (K := FractionRing S)]
  congr
  have : ((FractionalIdeal.mk0 (FractionRing R)) I :
    FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = I := by rfl
  erw [← Units.val_inj, Units.coe_map, this,
    FractionalIdeal.mapOfInjective_apply_int', ← hI]
  rfl

/-- Given an isomorphism between domains, the left inverse of `ClassGroup.mapOfInjective` is given
  by the map between class groups induced by the inverse of the isomorphism. -/
lemma ClassGroup.mapOfInjective_inverse_apply {R S : Type*} [CommRing R]
  [CommRing S] [IsDomain R] [IsDomain S] (φ : R ≃+* S) (I : ClassGroup R) :
  ClassGroup.mapOfInjective (φ := φ.symm.toRingHom) (RingEquiv.injective φ.symm)
    (ClassGroup.mapOfInjective (φ := φ.toRingHom) (RingEquiv.injective φ) I) = I := by
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : Algebra S R := φ.symm.toRingHom.toAlgebra
  let J := Quot.out I
  have : ClassGroup.mk (FractionRing R) J = I := by
    rw [← ClassGroup.Quot_mk_eq_mk]
    exact Quot.out_eq I
  erw [← this, ClassGroup.mapOfInjective_apply (RingEquiv.injective φ) J,
    ClassGroup.mapOfInjective_apply (RingEquiv.injective φ.symm) _]
  congr
  show ((Units.map (mapOfInjective' (FractionRing S) (FractionRing R)
    (RingEquiv.injective φ.symm))).comp
    (Units.map (mapOfInjective' (FractionRing R) (FractionRing S) (RingEquiv.injective φ)))) J = J
  rw [← Units.map_comp, ← Units.val_inj, Units.coe_map]
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  apply_fun FractionalIdeal.coeToSubmodule
  simp_rw [FractionalIdeal.mapOfInjective_apply' _ _ (RingEquiv.injective φ.symm),
    ← FractionalIdeal.coeToSet_coeToSubmodule]
  simp_rw [FractionalIdeal.mapOfInjective_apply' _ _ (RingEquiv.injective φ)]
  let φsymml : (FractionRing S) →ₛₗ[φ.symm.toRingHom] (FractionRing R) :=
    { toFun := IsFractionRing.map (j := φ.symm.toRingHom) (RingEquiv.injective φ.symm)
      map_add' := by simp only [map_add, implies_true]
      map_smul' := by
        intro x m
        simp only [IsFractionRing.map, IsLocalization.map_smul] }
  haveI : RingHomSurjective φ.symm.toRingHom := by
    refine { is_surjective := RingEquiv.surjective φ.symm }
  have := Submodule.map_coe φsymml ↑(Submodule.span S ((IsFractionRing.map (j := φ.toRingHom)
    (RingEquiv.injective φ)) '' (↑J : Set (FractionRing R))))
  erw [← this, Submodule.span_image, Submodule.span_span, ← Submodule.span_image, ← Set.image_comp]
  suffices heqid : ⇑φsymml ∘ ⇑(IsFractionRing.map
    (j := φ.toRingHom) ((RingEquiv.injective φ))) = id by
    rw [heqid]
    simp only [id_eq, Set.image_id']
    rw [← FractionalIdeal.coeToSet_coeToSubmodule J.val]
    simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  · unfold φsymml
    simp only [RingEquiv.toRingHom_eq_coe, IsFractionRing.map]
    ext x
    erw [Function.comp_apply, AddHom.coe_mk, IsLocalization.map_map]
    simp only [RingEquiv.symm_comp, IsLocalization.map_id, id_eq]
  · exact coeToSubmodule_injective

/-- Given an isomorphism between domains, this is the induced isomorphism between class groups. -/
noncomputable def ClassGroup.congr {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain R] [IsDomain S] (φ : R ≃+* S) : ClassGroup R ≃* ClassGroup S where
  toFun := ClassGroup.mapOfInjective (RingEquiv.injective φ)
  invFun := ClassGroup.mapOfInjective (RingEquiv.injective φ.symm)
  map_mul' := fun x y ↦ MonoidHom.map_mul (ClassGroup.mapOfInjective (RingEquiv.injective φ)) x y
  left_inv := by
    intro I
    exact ClassGroup.mapOfInjective_inverse_apply φ I
  right_inv := by
    intro J
    exact ClassGroup.mapOfInjective_inverse_apply φ.symm J

/-

Code for Dedekind domain case

-- We assume Dedekind domain to make the proof easier, since we can use mk0.
noncomputable def ClassGroup.map0 {R S : Type*} [CommRing R]
  [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [IsDomain R] [IsDomain S]
  (φ : R →+* S) (hinj : Function.Injective φ) : ClassGroup R →* ClassGroup S where
    toFun := by
      intro I
      choose J hJ using ClassGroup.mk0_surjective I
      have : Ideal.map φ J.val ∈ nonZeroDivisors (Ideal S) := by
        simp only [mem_nonZeroDivisors_iff_ne_zero,
        Submodule.zero_eq_bot, ne_eq]
        rw [Ideal.map_eq_bot_iff_le_ker]
        simp only [(RingHom.injective_iff_ker_eq_bot _).1 hinj, le_bot_iff]
        intro hc
        exact (mem_nonZeroDivisors_iff_ne_zero.1 J.2) hc
      exact (mk0 ⟨_, this⟩ )
    map_one' := by
      dsimp
      have := Classical.choose_spec (mk0_surjective (1  : ClassGroup R))
      erw [ClassGroup.mk0_eq_one_iff]
      apply Submodule.IsPrincipal.map_ringHom
      rw [← ClassGroup.mk0_eq_one_iff]
      exact this
    map_mul' := by
      dsimp
      intro x y
      have hxy := Classical.choose_spec (mk0_surjective (x * y  : ClassGroup R))
      have hx:= Classical.choose_spec (mk0_surjective (x  : ClassGroup R))
      have hy := Classical.choose_spec (mk0_surjective (y  : ClassGroup R))
      rw [← map_mul, ClassGroup.mk0_eq_mk0_iff]
      rw [← hx, ← hy, ← map_mul, ClassGroup.mk0_eq_mk0_iff] at hxy
      obtain ⟨a, b, ha, hb, hab⟩ := hxy
      use φ a, φ b, ((map_ne_zero_iff φ hinj).mpr ha) ,  ((map_ne_zero_iff φ hinj).mpr hb)
      apply_fun (fun I => Ideal.map φ I) at hab
      simp only [map_mul, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
        Submonoid.coe_mul, hx, hy] at hab
      convert hab

lemma ClassGroup.map0_apply {R S : Type*} [CommRing R]
  [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [IsDomain R] [IsDomain S]
  (φ : R →+* S) (hinj : Function.Injective φ)
  (I : nonZeroDivisors (Ideal R)) (J : nonZeroDivisors (Ideal S))
  (hI : ↑J = Ideal.map φ I) : ClassGroup.map0 φ hinj (mk0 I) = mk0 J := by
  have haux := Classical.choose_spec (mk0_surjective (mk0 I  : ClassGroup R))
  unfold map0
  dsimp
  rw [ClassGroup.mk0_eq_mk0_iff] at haux ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := haux
  use φ a, φ b, ((map_ne_zero_iff φ hinj).mpr ha) ,  ((map_ne_zero_iff φ hinj).mpr hb)
  apply_fun (fun I => Ideal.map φ I) at hab
  simp only [map_mul, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
        Submonoid.coe_mul, ← hI] at hab
  exact hab

noncomputable def ClassGroup.equiv0 {R S : Type*} [CommRing R]
  [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [IsDomain R] [IsDomain S] (φ : R ≃+* S) : ClassGroup R ≃* ClassGroup S := by
  refine MulEquiv.ofBijective (ClassGroup.map0 (R := R) (S := S) φ (RingEquiv.injective φ)) ?_
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      let I := Classical.choose (mk0_surjective (x  : ClassGroup R))
      have haux : Ideal.map φ I ∈ nonZeroDivisors (Ideal S) := by
        simp only [mem_nonZeroDivisors_iff_ne_zero,
        Submodule.zero_eq_bot, ne_eq]
        rw [Ideal.map_eq_bot_iff_le_ker]
        simp only [RingHom.ker_equiv, le_bot_iff]
        intro hc
        exact (mem_nonZeroDivisors_iff_ne_zero.1 I.2) hc
      have hx := Classical.choose_spec (mk0_surjective (x  : ClassGroup R))
      rw [← hx] at h
      rw [ClassGroup.map0_apply (R := R) (S := S) φ (RingEquiv.injective φ) _
        ⟨_, haux⟩  rfl , ClassGroup.mk0_eq_one_iff] at h
      obtain ⟨s, hs⟩ := h
      rw [← hx, ClassGroup.mk0_eq_one_iff]
      use φ.symm s
      apply_fun (fun I => Ideal.map φ.symm I) at hs
      erw [Ideal.map_of_equiv, Ideal.map_span, Set.image_singleton] at hs
      rw [hs]
      rfl
    ·  intro h
       simp only [h, map_one]
  · intro y
    have hy := Classical.choose_spec (mk0_surjective (y  : ClassGroup S))
    use ClassGroup.map0 φ.symm (RingEquiv.injective φ.symm) y
    rw [← hy]
    apply ClassGroup.map0_apply
    erw [Ideal.map_of_equiv, hy]

-/
