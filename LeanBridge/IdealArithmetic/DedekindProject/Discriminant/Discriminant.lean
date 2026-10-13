/-
Copyright (c) 2024 Anne Baanen, Alain Chavarri Villarello, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alain Chavarri Villarello, Sander R. Dahmen
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Relation between the polynomial discriminant and algebra discriminant

We prove that the discriminant of the power basis `1, α, α^2, .., α^(n-1)` of `ℚ[α]`, where
`α` is a root of the monic polynomial `f`, is given by the discriminant polynomial of `f`.

## Main results.
- `Algebra.discr_of_isAdjoinRootMonic` : the discriminant of a a power basis `1, α, α^2, .., α^(n-1)`,
  of  `F[α]`, with `α` a a root of the monic polynomial `f`, is given by the discriminant of `f`.

## Note
This file was originally written by Anne Baanen and included an implementation of
discriminant of polynomials based on the Sylvester Matrix, described in
`https://dl.acm.org/doi/10.1145/3703595.3705874`.
The current version of this file is a refactor using the definition and results of
resultants and discriminant of polynomials that are now in `Mathlib` and authored by
Kenny Lau, Anne Baanen and Andrew Yang.

-/

open Polynomial


lemma resultant_prod_X_sub_C {K ι : Type*} [Field K] {m : ℕ} [DecidableEq ι] (f : K[X])
  (hm : f.natDegree ≤ m) (s : Finset ι) (u : ι → K) :
    resultant f (∏ i ∈ s, (X - C (u i))) m = (-1) ^ (m * s.card) * ∏ i ∈ s, eval (u i) f := by
  rw [Polynomial.resultant_prod_right _ _ _ _ hm]
  have : ∀ i, f.resultant (X - C (u i)) m = f.resultant ((X - C (u i)) ^ 1) m 1 := by
    intro i
    rw [pow_one]
    simp only [natDegree_sub_C, natDegree_X]
  simp_rw [this]
  rw [Finset.prod_congr rfl (fun i _
    => Polynomial.resultant_X_sub_C_pow_right f (u i) m 1 hm)]
  simp only [mul_one, pow_one, ← Finset.pow_card_mul_prod, pow_mul]
  simp only [leadingCoeff_X_sub_C, Finset.prod_const_one, ne_eq, one_ne_zero, not_false_eq_true]

lemma prod_X_sub_C_resultant {K ι : Type*} [Field K] {n : ℕ} [DecidableEq ι] (g : K[X])
  (hn : g.natDegree ≤ n)  (s : Finset ι) (t : ι → K) :
    resultant (∏ i ∈ s, (X - C (t i))) g ((∏ i ∈ s, (X - C (t i)))).natDegree n = ∏ i ∈ s, eval (t i) g := by
  rw [Polynomial.resultant_prod_left _ _ _ _ _ hn]
  have : ∀ i, (X - C (t i)).resultant g (X - C (t i)).natDegree n = ((X - C (t i)) ^ 1).resultant g 1 n := by
    intro i
    rw [pow_one]
    simp only [natDegree_sub_C, natDegree_X]
  simp_rw [this]
  rw [Finset.prod_congr rfl (fun i _
    => Polynomial.resultant_X_sub_C_pow_left (t i) g _ _ hn)]
  simp only [pow_one]
  simp only [leadingCoeff_X_sub_C, Finset.prod_const_one, ne_eq, one_ne_zero, not_false_eq_true]

theorem derivative_prod' {R ι : Type*} [CommRing R] [DecidableEq ι] {s : Finset ι} {f : ι → R[X]} :
    derivative (∏ i ∈ s, f i) =
      ∑ i ∈ s, (∏ i ∈ s.erase i, f i) * derivative (f i) :=
  derivative_prod

lemma derivative_prod_X_sub_C {R ι: Type*} [CommRing R] [DecidableEq ι] (s : Finset ι) (t : ι → R) :
    derivative (∏ i ∈ s, (X - C (t i))) = ∑ i ∈ s, ∏ j ∈ s.erase i, (X - C (t j)) := by
  rw [derivative_prod']
  exact Finset.sum_congr rfl (by simp)


theorem resultant_map_injective {S R : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) (f g : R[X]) :
    resultant (f.map φ) (g.map φ) = φ (resultant f g) := by
  convert Polynomial.resultant_map_map f g f.natDegree g.natDegree φ
  rw [Polynomial.natDegree_map_eq_of_injective hφ]
  rw [Polynomial.natDegree_map_eq_of_injective hφ]

lemma Polynomial.discr_def {R : Type*} [CommRing R] [IsAddTorsionFree R]
    (f : R[X]) (hf : natDegree f ≠ 0) :
    f.leadingCoeff * discr f =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * resultant f (derivative f) := by
  apply_fun ( ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2)) * · )
  dsimp
  rw [← mul_assoc, ← Polynomial.resultant_deriv,
    ← one_mul (f.resultant (derivative f) f.natDegree (f.natDegree - 1)), ← mul_assoc]
  congr
  · rw [← sq, ← pow_mul]
    simp only [even_two, Even.mul_left, Even.neg_pow, one_pow]
  · exact (Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_derivative_eq f (by omega) )).symm
  · rw [← Polynomial.natDegree_pos_iff_degree_pos]
    omega
  · refine IsUnit.mul_right_injective (M := R) ?_
    refine IsUnit.pow  (n := (f.natDegree * (f.natDegree - 1) / 2) ) ?_
    simp only [IsUnit.neg_iff, isUnit_one]

/-  We don't require the `[IsAddTorsionFree R]` if the
  degree of the derivative of `f` equals `n-1`. -/
lemma Polynomial.discr_def' {R : Type*} [CommRing R]
    (f : R[X]) (hf : natDegree f ≠ 0)
    (hdeg : (derivative f).degree = ↑(f.natDegree - 1)) :
    f.leadingCoeff * discr f =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * resultant f (derivative f) := by
  apply_fun ( ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2)) * · )
  dsimp
  rw [← mul_assoc, ← Polynomial.resultant_deriv,
    ← one_mul (f.resultant (derivative f) f.natDegree (f.natDegree - 1)), ← mul_assoc]
  congr
  · rw [← sq, ← pow_mul]
    simp only [even_two, Even.mul_left, Even.neg_pow, one_pow]
  · exact (Polynomial.natDegree_eq_of_degree_eq_some (hdeg)).symm
  · rw [← Polynomial.natDegree_pos_iff_degree_pos]
    omega
  · refine IsUnit.mul_right_injective (M := R) ?_
    refine IsUnit.pow  (n := (f.natDegree * (f.natDegree - 1) / 2) ) ?_
    simp only [IsUnit.neg_iff, isUnit_one]

@[simp]
theorem discriminant_map' {R : Type*} [CommRing R]
  [IsAddTorsionFree R] {S : Type*} [CommRing S] [IsDomain S] [IsAddTorsionFree S] (φ : R →+* S)
    (hφ : Function.Injective φ) (f : R[X]) :
    discr (f.map φ) = φ (discr f) := by
  by_cases hf0 : f.natDegree = 0
  · obtain ⟨r, hr⟩ := Polynomial.natDegree_eq_zero.1 hf0
    rw [← hr]
    simp only [map_C, discr_C, map_one]
  have hf0' : f ≠ 0 := by contrapose! hf0; simp [hf0]
  apply mul_left_cancel₀ ((leadingCoeff_ne_zero.mpr ((Polynomial.map_ne_zero_iff hφ).mpr hf0')))
  rw [Polynomial.discr_def, derivative_map, resultant_map_injective, Polynomial.leadingCoeff_map_of_injective hφ, ← map_mul,
      Polynomial.discr_def, natDegree_map_eq_of_injective hφ, map_mul, map_pow, map_neg, map_one]
  · assumption
  · assumption
  · rwa [natDegree_map_eq_of_injective hφ]

-- Less assumptions on the rings. In particular, for integer polynomials we can
-- reduce modulo p.

@[simp]
theorem discriminant_map'' {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    [IsDomain S]  (φ : R →+* S)
    (f : R[X]) (hdeg : (derivative f).degree = ↑(f.natDegree - 1))
    (h1 : φ f.leadingCoeff ≠ 0)
    (h2 : φ f.derivative.leadingCoeff ≠ 0) :
    discr (f.map φ) = φ (discr f) := by
  by_cases hf0 : f.natDegree = 0
  · obtain ⟨r, hr⟩ := Polynomial.natDegree_eq_zero.1 hf0
    rw [← hr]
    simp only [map_C, discr_C, map_one]
  have hf0' : f ≠ 0 := by contrapose! hf0; simp [hf0]
  have hf0'' : map φ f ≠ 0 := by
    rw [← Polynomial.leadingCoeff_ne_zero,
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ h1]
    exact h1
  apply mul_left_cancel₀ ((leadingCoeff_ne_zero.mpr (hf0'')))
  rw [Polynomial.discr_def', derivative_map, Polynomial.resultant_map_map, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ h1, ← map_mul,
      Polynomial.discr_def', Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h1, map_mul, map_pow, map_neg, map_one]
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq,
    Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, Order.lt_two_iff, false_or, not_le, false_and,
    or_false]
  congr
  · exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h2
  · assumption
  · assumption
  · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h1]
    assumption
  · simp
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h1,
      Polynomial.degree_map_eq_of_leadingCoeff_ne_zero _ h2]
    exact hdeg


@[simp]
theorem discriminant_map {K : Type*} [Field K] [CharZero K] {L : Type*}
  [Field L] [CharZero L] (φ : K →+* L) (f : K[X]) :
    discr (f.map φ) = φ (discr f) := by
  by_cases hf0 : f.natDegree = 0
  · obtain ⟨r, hr⟩ := Polynomial.natDegree_eq_zero.1 hf0
    rw [← hr]
    simp only [map_C, discr_C, map_one]
  have hf0' : f ≠ 0 := by contrapose! hf0; simp [hf0]
  apply mul_left_cancel₀ ((leadingCoeff_ne_zero.mpr (map_ne_zero hf0')))
  rw [Polynomial.discr_def, derivative_map, resultant_map_injective,
    leadingCoeff_map, ← map_mul, Polynomial.discr_def,
      natDegree_map, map_mul, map_pow, map_neg, map_one]
  · assumption
  · apply RingHom.injective
  · rwa [natDegree_map]


lemma Monic.discr_def {R : Type*} [CommRing R]  [IsAddTorsionFree R] (f : R[X]) (hf : Monic f) :
    discr f = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * resultant f (derivative f) := by
  by_cases hf0 : natDegree f = 0
  · obtain ⟨r, hr⟩ := Polynomial.natDegree_eq_zero.1 hf0
    rw [← hr]
    simp only [discr_C, natDegree_C, zero_tsub, mul_zero, Nat.zero_div, pow_zero, derivative_C,
      natDegree_zero, resultant_zero_right_deg, coeff_zero, mul_one]
  · conv_lhs => rw [← one_mul f.discr, ← hf.leadingCoeff, Polynomial.discr_def _ hf0]

lemma discriminant_prod_X_sub_C {K : Type*} [Field K] [CharZero K] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (t : ι → K) :
    discr (∏ i ∈ s, (X - C (t i))) = (-1) ^ (s.card * (s.card - 1) / 2) * ∏ i ∈ s, ∏ j ∈ s.erase i, (t i - t j) := by
  rw [Monic.discr_def, derivative_prod_X_sub_C, prod_X_sub_C_resultant, natDegree_finset_prod_X_sub_C_eq_card s t]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  simp [eval_finset_sum, eval_prod]
  refine Finset.sum_eq_single _
      (fun j _ hji => Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, hi⟩) (sub_self _))
      (fun h => (h hi).elim)
  · rfl
  · exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem Splits.eq_fin_prod_roots {K : Type*}[Field K]  {f : K[X]}
    (h : Splits f) :
    f = C (f.leadingCoeff) * ∏ i : Fin (Multiset.card (roots f)),
      (X - C ((roots f).toList.get (i.cast (Multiset.length_toList _).symm))) := by
  conv_lhs => rw [Polynomial.Splits.eq_prod_roots h]
  congr 1
  rw [← Fintype.prod_equiv (finCongr (Multiset.length_toList _)) _ _ (fun _ => rfl)]
  simp only [finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [← Multiset.prod_map_toList, ← Fin.prod_univ_getElem]
  simp
  refine Fin.prod_congr' (M := K[X]) (fun x => (X - C f.roots.toList[↑x])) ?_
  simp only [List.length_map, Multiset.length_toList]

lemma Finset.Iio_union_Ioi {α : Type*} [Fintype α] [LinearOrder α]
    [LocallyFiniteOrderBot α] [LocallyFiniteOrderTop α] [DecidableEq α] (a : α) :
    (Finset.Iio a) ∪ (Finset.Ioi a) = Finset.univ.erase a :=
  Finset.ext (fun _ =>
    ⟨fun h => Finset.mem_erase.mpr ⟨(Finset.mem_union.mp h).casesOn
        (fun h => (Finset.mem_Iio.mp h).ne) (fun h => (Finset.mem_Ioi.mp h).ne'), Finset.mem_univ _⟩,
      fun h => Finset.mem_union.mpr ((lt_or_gt_of_ne (Finset.mem_erase.mp h).1).imp
        Finset.mem_Iio.mpr Finset.mem_Ioi.mpr)⟩)

lemma Finset.prod_univ_prod_Iio {α R : Type*} [CommRing R][Fintype α] [LinearOrder α]
    [LocallyFiniteOrderBot α] [LocallyFiniteOrderTop α] [DecidableEq α] (f : α → R) :
    ∏ i : α, ∏ j ∈ Finset.Iio i, (f i - f j) = ∏ i : α, ∏ j ∈ Finset.Ioi i, (f j - f i) :=
  Finset.prod_comm' (by simp)

@[simps]
def List.equivFin {α : Type*} [DecidableEq α] {s : List α} (hs : s.Nodup) :
    { x // x ∈ s } ≃ Fin s.length where
  toFun x := ⟨List.idxOf (x : α) s, by
    rw [← List.IsPrefix.mem_iff_idxOf_lt_length] ; exact  x.2 ; rfl⟩
  invFun i := ⟨s.get i, List.get_mem s i⟩
  left_inv x := by ext; simp
  right_inv i := by ext; exact List.get_idxOf hs i

@[simp] lemma Multiset.nodup_toList {α : Type*} {s : Multiset α} :
    s.toList.Nodup ↔ s.Nodup := by
  rw [← Multiset.coe_toList s, Multiset.coe_nodup, Multiset.coe_toList]


@[simps!]
noncomputable def Multiset.equivFin {α : Type*} {s : Multiset α} (hs : s.Nodup) :
    { x // x ∈ s } ≃ Fin (Multiset.card s) := by
  classical
  exact ((Equiv.refl _).subtypeEquiv (by simp)).trans
    ((List.equivFin (Multiset.nodup_toList.mpr hs)).trans
    (finCongr (by simp)))

lemma Fin.sum_card_sub_one_sub_self {n : ℕ} :
    ∑ i : Fin n, (n - 1 - (i : ℕ)) = n * (n - 1) / 2 := by
  obtain (⟨⟩ | n) := n
  · simp
  · simp only [← Finset.sum_range, add_tsub_cancel_right, Finset.sum_flip (f := fun x => x),
      Finset.sum_range_id]



theorem Algebra.discr_of_isAdjoinRootMonic {K F : Type*} [Field K] [Field F] [CharZero F]
    [Algebra F K] {T : F[X]} (f : IsAdjoinRootMonic K T) (hT : Irreducible T) :
    Algebra.discr F (f.powerBasis).basis = Polynomial.discr T := by
  classical
  have hT0 : T ≠ 0 := Polynomial.Monic.ne_zero f.monic
  have hdeg : T.natDegree = (map (algebraMap F (AlgebraicClosure F)) T).natDegree := by simp
  have : FiniteDimensional F K := Module.Finite.of_basis f.powerBasis.basis
  apply RingHom.injective (algebraMap F (AlgebraicClosure F))
  let _ : Fintype (K →ₐ[F] AlgebraicClosure F) := PowerBasis.AlgHom.fintype f.powerBasis
  have nd_aroots' : (aroots (minpoly F f.root) (AlgebraicClosure F)).Nodup :=
    (nodup_aroots_iff_of_splits (minpoly.ne_zero f.isIntegral_root)
      (IsAlgClosed.splits (k := AlgebraicClosure F) _)).mpr
    (minpoly.irreducible f.isIntegral_root).separable
  have card_roots : Multiset.card (map (algebraMap F (AlgebraicClosure F)) T).roots = T.natDegree := by
    rw [← natDegree_eq_of_degree_eq_some (Polynomial.Splits.degree_eq_card_roots
      (IsAlgClosed.splits (k := AlgebraicClosure F) _ ) ?_ )]
    simp only [natDegree_map]
    simp only [ne_eq, Polynomial.map_eq_zero, hT0, not_false_eq_true]
  have card_aroots : Multiset.card (aroots T (AlgebraicClosure F)) = natDegree T := by
    rw [aroots, card_roots]
  have aux_card : f.powerBasis.dim = ((minpoly F f.root).aroots (AlgebraicClosure F)).card := by
    rw [f.minpoly_eq hT, card_aroots, f.powerBasis_dim]
  have aux_card' := aux_card
  rw [f.minpoly_eq hT, card_aroots, hdeg] at aux_card'
  let e : Fin f.powerBasis.dim ≃ (K →ₐ[F] AlgebraicClosure F) := by
    refine (finCongr ?_).trans ((Multiset.equivFin nd_aroots').symm.trans
      (PowerBasis.liftEquiv' f.powerBasis).symm)
    exact aux_card
  have e_apply : ∀ i, e i f.root =
      (T.aroots (AlgebraicClosure F)).toList.get (Fin.cast (by simp [card_aroots]) i) := by
    intro i
    simp only [e, Equiv.trans_apply, finCongr_apply]
    refine Eq.trans (congrArg Subtype.val (f.powerBasis.liftEquiv'.apply_symm_apply
        ((Multiset.equivFin nd_aroots').symm (Fin.cast aux_card i)))) ?_
    simp only [Multiset.equivFin_symm_apply_coe, Fin.val_cast, List.get_eq_getElem, f.minpoly_eq hT]
  rw [Algebra.discr_powerBasis_eq_prod _ _ _ e]
  let aux := (finCongr (natDegree_eq_of_degree_eq_some  (Polynomial.Splits.degree_eq_card_roots
    (IsAlgClosed.splits (k := AlgebraicClosure F) _ )
    (show map (algebraMap F (AlgebraicClosure F)) T ≠ 0 by simp [hT0]) )))
  · conv_rhs => rw [← discriminant_map, Splits.eq_fin_prod_roots (IsAlgClosed.splits
      ((map (algebraMap F (AlgebraicClosure F)) T)))]
    rw [leadingCoeff_map, f.monic.leadingCoeff, map_one, map_one, one_mul, discriminant_prod_X_sub_C,
        ← Fintype.prod_equiv (finCongr (natDegree_eq_of_degree_eq_some
        (Polynomial.Splits.degree_eq_card_roots _ _)))
          _ _ (fun _ => rfl)]
    conv_rhs => rw [Finset.prod_congr rfl (fun i _ => by
      rw [← Finset.prod_equiv (s := Finset.univ.erase i) aux
            (by simp [aux, -finCongr_apply])
            (fun _ _ => rfl), ← Finset.Iio_union_Ioi, Finset.prod_union]
      · exact (Finset.disjoint_Ioi_Iio _).symm)]
    simp only [IsAdjoinRootMonic.powerBasis_dim, IsAdjoinRootMonic.powerBasis_gen, pow_two,
      Finset.prod_mul_distrib, finCongr_apply, Fin.cast_cast]
    rw [mul_left_comm]
    congr 1
    · simp only [aux, finCongr_apply, Fin.cast_cast]
      rw [Finset.prod_univ_prod_Iio]
      refine Finset.prod_equiv (finCongr aux_card') ?_ ?_
      · simp
      · intro i hi
        refine Finset.prod_equiv (finCongr aux_card') ?_ ?_
        · simp only [Finset.mem_Ioi, finCongr_apply, Fin.cast_lt_cast] ; exact fun i_2 ↦ trivial
        · intro i hi
          erw [e_apply, e_apply, ← neg_sub, ← neg_one_mul]
    · have subaux :  ∏ x, ∏ x_1 ∈ Finset.Ioi x, (- ((e x_1) f.root - (e x) f.root)) =
        ∏ x, ∏ x_1 ∈ Finset.Ioi x,  ((map (algebraMap F (AlgebraicClosure F)) T).roots.toList.get
        (Fin.cast (Eq.trans (natDegree_eq_of_degree_eq_some (Splits.degree_eq_card_roots
        (IsAlgClosed.splits (k := AlgebraicClosure F) _ )
        (show map (algebraMap F (AlgebraicClosure F)) T ≠ 0
        by simp [hT0]))) (Eq.symm (Multiset.length_toList (map (algebraMap F
        (AlgebraicClosure F)) T).roots)) ) x) -
        (map (algebraMap F (AlgebraicClosure F)) T).roots.toList.get
        (Fin.cast (Eq.symm (Multiset.length_toList (map (algebraMap F (AlgebraicClosure F)) T).roots))
        (aux x_1))) := by
        simp only [aux] ; dsimp
        refine Finset.prod_equiv (finCongr aux_card') ?_ ?_
        · intro i ; simp
        · intro i hi
          refine Finset.prod_equiv (finCongr aux_card') ?_ ?_
          · simp only [Finset.mem_Ioi, finCongr_apply, Fin.cast_lt_cast] ; exact fun i_2 ↦ trivial
          · intro i hi
            erw [e_apply, e_apply, neg_sub]
            simp only [IsAdjoinRootMonic.powerBasis_dim, List.get_eq_getElem, Fin.val_cast,
              finCongr_apply]
      rw [← subaux]
      simp_rw [Finset.prod_neg, Finset.prod_mul_distrib, Fin.card_Ioi]
      simp only [Finset.prod_pow_eq_pow_sum, Fin.sum_card_sub_one_sub_self,
        Finset.card_univ, Fintype.card_fin, card_roots]
      simp_rw [aux_card', ← hdeg]
      rw [← mul_assoc, ← sq, ← pow_mul, Even.neg_one_pow (by simp only [even_two,
        Even.mul_left]), one_mul]
    · exact (IsAlgClosed.splits (k := AlgebraicClosure F) _ )
    · simp [hT0]
