/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.IdealArithmetic.Galois.Defs
import LeanBridge.IdealArithmetic.DedekindProject.Discriminant.Discriminant

/-!
# Core Theorem 2 — discriminant square test (`disc` square ⟺ `Aₙ`)

Decomposition: `.mathlib-quality/decomposition.md`, Result R2. Source: K. Conrad,
*Galois groups as permutation groups*, Theorem 4.7 (p. 6).
-/

namespace IdealArithmetic.Galois

open Polynomial Finset Polynomial.Gal

attribute [local instance] factSplitsSplittingField

variable {F : Type*} [Field F]

private lemma prod_erase_sub_eq_neg_one_pow_mul_prod_Ioi_sq {R : Type*} [CommRing R] {n : ℕ}
    (t : Fin n → R) :
    (∏ i, ∏ j ∈ univ.erase i, (t i - t j))
      = (-1) ^ (n * (n - 1) / 2) * (∏ i, ∏ j ∈ Ioi i, (t i - t j)) ^ 2 := by
  have hsum : ∑ i : Fin n, (Finset.Ioi i).card = n * (n - 1) / 2 := by
    simp only [Fin.card_Ioi]
    exact Fin.sum_card_sub_one_sub_self
  have step1 : (∏ i, ∏ j ∈ univ.erase i, (t i - t j))
      = (∏ i, ∏ j ∈ Iio i, (t i - t j)) * (∏ i, ∏ j ∈ Ioi i, (t i - t j)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← Finset.Iio_union_Ioi i, Finset.prod_union (Finset.disjoint_Ioi_Iio i).symm]
  have step2 : (∏ i, ∏ j ∈ Iio i, (t i - t j))
      = (-1) ^ (n * (n - 1) / 2) * (∏ i, ∏ j ∈ Ioi i, (t i - t j)) := by
    have hneg : (∏ i, ∏ j ∈ Ioi i, (t j - t i))
        = ∏ i, ((-1 : R) ^ (Finset.Ioi i).card * ∏ j ∈ Ioi i, (t i - t j)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun j _ => by ring)
    rw [Finset.prod_univ_prod_Iio, hneg, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  rw [step1, step2]
  ring

private lemma map_eq_prod_X_sub_C_enum (p : F[X]) (hmonic : p.Monic)
    (e : Fin p.natDegree ≃ {x // x ∈ p.rootSet p.SplittingField}) :
    p.map (algebraMap F p.SplittingField) = ∏ i, (X - C (e i : p.SplittingField)) := by
  have hp0 : p ≠ 0 := hmonic.ne_zero
  have hqsplits : (p.map (algebraMap F p.SplittingField)).Splits :=
    IsSplittingField.splits p.SplittingField p
  have hqmonic : (p.map (algebraMap F p.SplittingField)).Monic := hmonic.map _
  have hcard : Fintype.card {x // x ∈ p.rootSet p.SplittingField} = p.natDegree := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hsep : p.Separable := (card_rootSet_eq_natDegree_iff_of_splits hp0 hqsplits).mp hcard
  have hnodup : (p.map (algebraMap F p.SplittingField)).roots.Nodup := nodup_roots hsep.map
  have hnodup' : (Finset.univ.val.map (fun i => (e i : p.SplittingField))).Nodup :=
    Finset.univ.nodup.map (fun a b h => e.injective (Subtype.ext h))
  have hmr : ∀ a : p.SplittingField,
      a ∈ (p.map (algebraMap F p.SplittingField)).roots ↔ a ∈ p.rootSet p.SplittingField := by
    intro a
    simp only [Polynomial.mem_roots', Polynomial.mem_rootSet', Polynomial.IsRoot.def,
      Polynomial.aeval_def, Polynomial.eval_map]
  have hroots : (p.map (algebraMap F p.SplittingField)).roots
      = Finset.univ.val.map (fun i => (e i : p.SplittingField)) := by
    rw [Multiset.Nodup.ext hnodup hnodup']
    intro a
    rw [Multiset.mem_map, hmr a]
    constructor
    · intro ha
      exact ⟨e.symm ⟨a, ha⟩, by simp, by simp⟩
    · rintro ⟨i, -, rfl⟩
      exact (e i).2
  rw [hqsplits.eq_prod_roots_of_monic hqmonic, hroots, Multiset.map_map,
      Finset.prod_eq_multiset_prod]
  rfl

/-- **T002 / L2.1.** Over its splitting field, the polynomial discriminant equals the squared
Vandermonde product of differences of the roots, enumerated by `e`. The discriminant is a genuine
*square* here (no leftover unit): this is exactly the bridge R2 needs to relate `IsSquare disc` to
`δ = ∏_{i<j}(eᵢ − eⱼ)` lying in the base field. Source: Conrad, *Galois groups as permutation
groups*, Def. 4.1 (p. 5). -/
theorem discr_eq_prod_roots_sub_sq [CharZero F] (p : F[X]) (hmonic : p.Monic)
    (e : Fin p.natDegree ≃ {x // x ∈ p.rootSet p.SplittingField}) :
    (algebraMap F p.SplittingField) p.discr =
      (∏ i, ∏ j ∈ Ioi i, ((e i : p.SplittingField) - (e j : p.SplittingField))) ^ 2 := by
  rw [← discriminant_map (algebraMap F p.SplittingField) p,
      map_eq_prod_X_sub_C_enum p hmonic e,
      discriminant_prod_X_sub_C Finset.univ (fun i => (e i : p.SplittingField)),
      Finset.card_univ, Fintype.card_fin,
      prod_erase_sub_eq_neg_one_pow_mul_prod_Ioi_sq,
      ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

open scoped Classical in
/-- **T003 / L2.2.** A Galois automorphism scales the Vandermonde product `δ = ∏_{i<j}(eᵢ − eⱼ)`
of root differences by the sign of the permutation it induces on the roots. This is the heart of
the discriminant test: it turns "`σ` induces an even permutation" into "`σ` fixes `δ`". Source:
Conrad, *Galois groups as permutation groups*, Thm 4.7 proof (p. 6). -/
theorem galAction_apply_prod_roots_sub (p : F[X]) (σ : p.Gal)
    (e : Fin p.natDegree ≃ {x // x ∈ p.rootSet p.SplittingField}) :
    σ (∏ i, ∏ j ∈ Ioi i, ((e i : p.SplittingField) - (e j : p.SplittingField))) =
      (Equiv.Perm.sign (galActionHom p p.SplittingField σ) : ℤ) •
        (∏ i, ∏ j ∈ Ioi i, ((e i : p.SplittingField) - (e j : p.SplittingField))) := by
  have hmaps : ∀ x : p.SplittingField,
      x ∈ p.rootSet p.SplittingField ↔ σ x ∈ p.rootSet p.SplittingField := by
    intro x
    constructor
    · intro hx
      exact Polynomial.rootSet_mapsTo σ.toAlgHom hx
    · intro hx
      have h2 := Polynomial.rootSet_mapsTo σ.symm.toAlgHom hx
      have hx' : (σ.symm.toAlgHom (σ x) : p.SplittingField) = x := σ.symm_apply_apply x
      rwa [hx'] at h2
  set ρ : Equiv.Perm {x // x ∈ p.rootSet p.SplittingField} :=
    Equiv.Perm.subtypePerm σ.toEquiv (fun x => (hmaps x).symm) with hρ
  have hact : ∀ x : {x // x ∈ p.rootSet p.SplittingField}, σ (x : p.SplittingField) = ↑(ρ x) :=
    fun _ => rfl
  have hπρ : galActionHom p p.SplittingField σ = (rootsEquivRootsAux p p.SplittingField).permCongr ρ := by
    refine Equiv.ext fun w => ?_
    simp only [Equiv.permCongr_apply, Polynomial.Gal.galActionHom, MulAction.toPermHom_apply,
      MulAction.toPerm_apply, Polynomial.Gal.smul_def]
    exact congrArg _ (Subtype.ext rfl)
  set τ : Equiv.Perm (Fin p.natDegree) := e.symm.permCongr ρ with hτ
  have hτe : ∀ i, ((ρ (e i) : {x // x ∈ p.rootSet p.SplittingField}) : p.SplittingField)
      = ↑(e (τ i)) := by
    intro i
    congr 1
    rw [hτ, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  simp_rw [map_prod, map_sub, hact, hτe]
  rw [Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod (f := fun a b => (e a : p.SplittingField) - ↑(e b))
        τ (fun i j => by ring), hτ, Equiv.Perm.sign_permCongr, hπρ, Equiv.Perm.sign_permCongr,
      zsmul_eq_mul]

open scoped Classical in
/-- **T004 / L2.3.** In characteristic ≠ 2, a Galois automorphism fixes the Vandermonde product `δ`
iff the permutation it induces on the roots is even. The Vandermonde product is nonzero because the
enumeration `e` lists *distinct* roots. Source: Conrad, *Galois groups as permutation groups*,
Thm 4.7 proof (p. 6); the char-2 obstruction is Rmk 4.8. -/
theorem fixed_prod_roots_iff_mem_alternating (p : F[X]) (h2 : (2 : F) ≠ 0) (σ : p.Gal)
    (e : Fin p.natDegree ≃ {x // x ∈ p.rootSet p.SplittingField}) :
    σ (∏ i, ∏ j ∈ Ioi i, ((e i : p.SplittingField) - (e j : p.SplittingField))) =
        (∏ i, ∏ j ∈ Ioi i, ((e i : p.SplittingField) - (e j : p.SplittingField)))
      ↔ galActionHom p p.SplittingField σ ∈ alternatingGroup _ := by
  rw [galAction_apply_prod_roots_sub p σ e, Equiv.Perm.mem_alternatingGroup]
  set δ := ∏ i, ∏ j ∈ Ioi i, ((e i : p.SplittingField) - (e j : p.SplittingField)) with hδdef
  set s := Equiv.Perm.sign (galActionHom p p.SplittingField σ) with hsdef
  have hδ0 : δ ≠ 0 := by
    rw [hδdef, Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [sub_ne_zero]
    exact fun h => (Finset.mem_Ioi.mp hj).ne (e.injective (Subtype.ext h))
  have h2E : (2 : p.SplittingField) ≠ 0 := by
    have h := (map_ne_zero_iff (algebraMap F p.SplittingField)
      (algebraMap F p.SplittingField).injective).mpr h2
    rwa [map_ofNat] at h
  constructor
  · intro h
    rcases Int.units_eq_one_or s with h1 | hm1
    · exact h1
    · exfalso
      rw [hm1, show ((-1 : ℤˣ) : ℤ) = -1 from rfl, neg_one_zsmul] at h
      have h2δ : (2 : p.SplittingField) * δ = 0 := by linear_combination -h
      exact hδ0 ((mul_eq_zero.mp h2δ).resolve_left h2E)
  · intro h
    rw [h, show ((1 : ℤˣ) : ℤ) = 1 from rfl, one_zsmul]

/-- **T005 / L2.4.** The Vandermonde product `δ` lies in the base field (viewed as the bottom
intermediate field) iff the discriminant is a square in the base field. This is where `disc = δ²`
(T002) does its work. Source: Conrad, *Galois groups as permutation groups*, Thm 4.7 (p. 6). -/
theorem prod_roots_mem_bot_iff_isSquare_discr [CharZero F] (p : F[X]) (hmonic : p.Monic)
    (e : Fin p.natDegree ≃ {x // x ∈ p.rootSet p.SplittingField}) :
    (∏ i, ∏ j ∈ Ioi i, ((e i : p.SplittingField) - (e j : p.SplittingField)))
        ∈ (⊥ : IntermediateField F p.SplittingField)
      ↔ IsSquare p.discr := by
  set δ := ∏ i, ∏ j ∈ Ioi i, ((e i : p.SplittingField) - (e j : p.SplittingField)) with hδdef
  have hdisc : (algebraMap F p.SplittingField) p.discr = δ ^ 2 :=
    discr_eq_prod_roots_sub_sq p hmonic e
  rw [IntermediateField.mem_bot]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, (algebraMap F p.SplittingField).injective ?_⟩
    rw [map_mul, hc, hdisc, sq]
  · rintro ⟨c, hc⟩
    have hsq : δ * δ =
        (algebraMap F p.SplittingField c) * (algebraMap F p.SplittingField c) := by
      rw [← sq, ← hdisc, hc, map_mul]
    rcases mul_self_eq_mul_self_iff.mp hsq with h | h
    · exact ⟨c, h.symm⟩
    · exact ⟨-c, by rw [map_neg, ← h]⟩

open scoped Classical in
/-- **T006 / Core Theorem 2 — the discriminant square test** (Conrad, *Galois groups as permutation
groups*, Thm 4.7). For a monic separable polynomial over a characteristic-zero field, the image of
the Galois group in the symmetric group on the roots lies in the alternating group iff the
discriminant is a square. This determines whether `Gal f ⊆ Aₙ` from the base-field datum `disc f`. -/
theorem range_galActionHom_le_alternatingGroup_iff [CharZero F] (p : F[X]) (hmonic : p.Monic)
    (hp : p.Separable) :
    MonoidHom.range (galActionHom p p.SplittingField) ≤ alternatingGroup _ ↔ IsSquare p.discr := by
  have : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hp
  have hcard : Fintype.card {x // x ∈ p.rootSet p.SplittingField} = p.natDegree :=
    card_rootSet_eq_natDegree hp (IsSplittingField.splits p.SplittingField p)
  let e : Fin p.natDegree ≃ {x // x ∈ p.rootSet p.SplittingField} :=
    (Fintype.equivFinOfCardEq hcard).symm
  rw [← prod_roots_mem_bot_iff_isSquare_discr p hmonic e, IsGalois.mem_bot_iff_fixed]
  constructor
  · intro h σ
    exact (fixed_prod_roots_iff_mem_alternating p two_ne_zero σ e).mpr
      (h (MonoidHom.mem_range.mpr ⟨σ, rfl⟩))
  · intro h y hy
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hy
    exact (fixed_prod_roots_iff_mem_alternating p two_ne_zero σ e).mp (h σ)

end IdealArithmetic.Galois
