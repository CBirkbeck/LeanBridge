/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.NumberTheory.KummerDedekind
import LeanBridge.IdealArithmetic.DedekindProject.Auxiliary.PolynomialBasics
import Mathlib.RingTheory.ZMod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Field.ZMod


open Ideal UniqueFactorizationMonoid Polynomial RingHom Algebra Classical


noncomputable section Adjoin

variable (R)  {S : Type*} [CommRing R]  [CommRing S] [Algebra R S]

namespace AdjoinRoot

/- A down-to-earth version of Kummer-Dedekind, for explicit computational uses. -/


lemma algHomDvd_polynomial_apply (f g h : S[X]) (hgf : g ∣ f) :
  algHomOfDvd S f g hgf (Ideal.Quotient.mk _ h) = Ideal.Quotient.mk _ h := by
  have aux1 : Ideal.Quotient.mk _ h = Polynomial.aeval (root f) h := by
    rw [aeval_eq] ; rfl
  have aux2 : Ideal.Quotient.mk _ h = Polynomial.aeval (root g) h := by
    rw [aeval_eq] ; rfl
  rw [aux1, aux2, ← Polynomial.aeval_algHom_apply,algHomOfDvd_root]

lemma algHomDvd_surjective (f g: S[X]) (hgf : g ∣ f): Function.Surjective (algHomOfDvd S f g hgf) := by
  intro y
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective y
  use AdjoinRoot.mk _ p
  erw [algHomDvd_polynomial_apply, hp]

lemma algHomDvd_ker (f g : S[X]) (hgf : g ∣ f) :
  RingHom.ker (algHomOfDvd S f g hgf) = Ideal.span {Ideal.Quotient.mk _ g} := by
  ext x
  obtain ⟨h, hy⟩ := Ideal.Quotient.mk_surjective x
  erw [← hy, mem_ker, algHomDvd_polynomial_apply, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨k, hk⟩
    simp only [hk, map_mul]
    exact dvd_mul_right _ _
  · rintro ⟨k, hk⟩
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective k
    erw [← ht, ← map_mul ((Ideal.Quotient.mk (span {f}))), Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      Ideal.mem_span_singleton] at hk
    obtain ⟨l,ls⟩ := hk
    obtain ⟨m, hm⟩ := hgf
    use t + m * l
    rw [mul_add, ← mul_assoc, ← hm, ← ls]
    ring

end AdjoinRoot

end Adjoin

-------------------------------------------

noncomputable section

variable  {R S : Type*} [CommRing R]  [CommRing S]
  [Algebra R S] [NoZeroSMulDivisors R S]
  [IsIntegrallyClosed R] {x : S} {I : Ideal R}
  (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
  [IsDomain R] [IsDomain S]

/-- Same as `quotMapEquivQuotQuotMap'` in Mathlib but without the Dedekind domain assumption for `S`. -/
noncomputable def quotMapEquivQuotQuotMap' :
    S ⧸ I.map (algebraMap R S) ≃+* (R ⧸ I)[X] ⧸ span {(minpoly R x).map (Ideal.Quotient.mk I)} :=
  (quotAdjoinEquivQuotMap hx (FaithfulSMul.algebraMap_injective
    (Algebra.adjoin R {x}) S)).symm.trans <|
    ((Algebra.adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans <|
    quotEquivOfEq (by rw [Algebra.adjoin.powerBasis'_minpoly_gen hx'])


/-- Same as `quotMapEquivQuotQuotMap_symm_apply` in Mathlib but without the Dedekind domain assumption for `S`. -/
lemma quotMapEquivQuotQuotMap_symm_apply' (Q : R[X]) :
    (quotMapEquivQuotQuotMap' hx hx').symm (Q.map (Ideal.Quotient.mk I)) = Q.aeval x := by
  apply (quotMapEquivQuotQuotMap' hx hx').injective
  rw [quotMapEquivQuotQuotMap', AlgEquiv.toRingEquiv_eq_coe, RingEquiv.symm_trans_apply,
    RingEquiv.symm_symm, RingEquiv.coe_trans, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_trans_apply, quotEquivOfEq_symm, quotEquivOfEq_mk]
  congr
  convert (adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap_symm_apply_mk I Q
  · rfl
  apply (quotAdjoinEquivQuotMap hx
    (FaithfulSMul.algebraMap_injective ((adjoin R {x})) S)).injective
  simp only [RingEquiv.apply_symm_apply, adjoin.powerBasis'_gen, quotAdjoinEquivQuotMap_apply_mk,
    coe_aeval_mk_apply]

def quotMapHom (d : (R ⧸ I)[X])
  (hd : d ∣ (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    S →+* (R ⧸ I)[X] ⧸ span {d} := by
  refine RingHom.comp ?_ (Ideal.Quotient.mk (I.map (algebraMap R S)) )
  exact RingHom.comp ((AdjoinRoot.algHomOfDvd (R ⧸ I) (S := (R ⧸ I))
    (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) d hd).toRingHom)
    (quotMapEquivQuotQuotMap' hx hx').toRingHom


lemma quotMapHom_ker (d : R[X])
  (hd : Polynomial.map (Ideal.Quotient.mk I) d ∣ (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
  RingHom.ker (quotMapHom hx hx' (d.map (Ideal.Quotient.mk I)) hd) =
    Ideal.span (I.map (algebraMap R S) ∪ {d.aeval x}) := by
  have key : RingHom.ker (quotMapHom hx hx' (d.map (Ideal.Quotient.mk I)) hd) =
      comap (Ideal.Quotient.mk (I.map (algebraMap R S)))
        (span {Ideal.Quotient.mk (I.map (algebraMap R S)) (d.aeval x)}) := by
    let ψ : S ⧸ I.map (algebraMap R S) ≃+* AdjoinRoot ((minpoly R x).map (Ideal.Quotient.mk I)) :=
      quotMapEquivQuotQuotMap' hx hx'
    have hψ : ψ.symm (AdjoinRoot.mk _ (d.map (Ideal.Quotient.mk I))) =
        Ideal.Quotient.mk (I.map (algebraMap R S)) (d.aeval x) :=
      quotMapEquivQuotQuotMap_symm_apply' hx hx' d
    have hker : RingHom.ker (AdjoinRoot.algHomOfDvd (R ⧸ I) _ _ hd) =
        span {AdjoinRoot.mk _ (d.map (Ideal.Quotient.mk I))} :=
      AdjoinRoot.algHomDvd_ker _ _ hd
    ext y
    rw [mem_comap, mem_span_singleton, ← hψ, ← map_dvd_iff ψ, RingEquiv.apply_symm_apply,
      ← mem_span_singleton, ← hker, mem_ker, mem_ker]
    rfl
  rw [key]
  refine le_antisymm ?_ ?_
  · intro y hy
    simp only [mem_comap, mem_span_singleton] at hy
    obtain ⟨t, ht⟩ := hy
    obtain ⟨l, hl⟩ := Ideal.Quotient.mk_surjective t
    rw [← hl, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ht
    rw [Set.union_singleton, Ideal.mem_span_insert]
    use l , (y - (aeval x) d * l )
    refine ⟨by simp only [span_eq, ht], by ring⟩
  · intro y hy
    rw [Set.union_singleton, Ideal.mem_span_insert] at hy
    obtain ⟨a, z, hz, hy⟩ := hy
    rw [span_eq] at hz
    rw [mem_comap, hy, map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hz, add_zero,
      mem_span_singleton]
    simp only [dvd_mul_left]

def quotMapEquiv (d : R[X])
    (hd : Polynomial.map (Ideal.Quotient.mk I) d ∣ (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    S ⧸ Ideal.span (I.map (algebraMap R S) ∪ {d.aeval x}) ≃+* (R ⧸ I)[X] ⧸ span {d.map (Ideal.Quotient.mk I)} := by
  refine RingEquiv.trans (quotEquivOfEq (quotMapHom_ker hx hx' d hd).symm) ?_
  refine RingHom.quotientKerEquivOfSurjective ?_
  unfold quotMapHom
  exact ((AdjoinRoot.algHomDvd_surjective _ _ hd).comp
    (quotMapEquivQuotQuotMap' hx hx').surjective).comp Ideal.Quotient.mk_surjective

include hx hx'

attribute [local instance] Ideal.Quotient.field

lemma ideal_span_pair_maximal (hI : IsMaximal I) (d : R[X])
    (hd : Polynomial.map (Ideal.Quotient.mk I) d ∣ (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)))
    (hirr : Irreducible (Polynomial.map (Ideal.Quotient.mk I) d)) :
    IsMaximal (Ideal.span (I.map (algebraMap R S) ∪ {d.aeval x})) := by
  refine Ideal.Quotient.maximal_of_isField _ ?_
  haveI : Fact $ Irreducible (Polynomial.map (Ideal.Quotient.mk I) d) := {out := hirr}
  refine MulEquiv.isField (Field.toIsField (R :=
    (R ⧸ I)[X] ⧸ span {Polynomial.map (Ideal.Quotient.mk I) d})) (quotMapEquiv hx hx' _ hd).toMulEquiv



end

variable {p : ℕ}  {S : Type*} [CommRing S] {x : S}
  (hx : comap (algebraMap ℤ S) (conductor ℤ x) ⊔ (span {(p : ℤ)}) = ⊤) (hx' : IsIntegral ℤ x)


lemma quotMapInt.ideal_span_eq_span (d : ℤ[X]) :
  span {↑p, (aeval x) d} = span (↑(Ideal.map (algebraMap ℤ S) (span {↑p})) ∪ {(aeval x) d}) := by
  simp only [algebraMap_int_eq, map_span, eq_intCast, Set.image_singleton, Int.cast_natCast,
  Set.union_singleton]
  rw [Set.pair_comm, Ideal.span_insert, Ideal.span_insert, span_eq]


variable  [IsDomain S] [CharZero S]

noncomputable def quotMapEquivInt (d : ℤ[X]) (d' : (ZMod p) [X]) (hdeq : d' = d.map (algebraMap ℤ (ZMod p)))
  (hd : d' ∣ (minpoly ℤ x).map (algebraMap ℤ (ZMod p))) :
  S ⧸ Ideal.span {↑p, d.aeval x} ≃+* (ZMod p)[X] ⧸ span {d'} := by
  rw [hdeq] at hd
  choose g k hgk using exists_of_dvd_mod_pi (ZMod.ker_intCastRingHom p) (ZMod.ringHom_surjective (algebraMap ℤ (ZMod p))) _ _ hd
  have := quotMapEquiv hx hx' d ?_
  swap
  rw [hgk]
  have aux : Polynomial.map (Ideal.Quotient.mk (span {(↑p : ℤ)})) ↑p = 0 := by
    rw [← pi_dvd_iff_mod_zero (π := (p : ℤ))]
    simp only [map_natCast, dvd_refl]
    simp only [mk_ker]
  simp only [map_natCast, Polynomial.map_add, Polynomial.map_mul, aux, zero_mul, add_zero,
    dvd_mul_right]
  refine RingEquiv.trans (quotEquivOfEq ?_) (RingEquiv.trans this ?_)
  · refine quotMapInt.ideal_span_eq_span d
  · convert Ideal.quotientEquiv (span {Polynomial.map (Ideal.Quotient.mk (span {↑p})) d}) (span {d'})
      (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p)) ?_
    simp only [Ideal.map_span, coe_coe, mapEquiv_apply, Set.image_singleton]
    rw [hdeq]
    congr 1
    rw [algebraMap_int_eq, Set.singleton_eq_singleton_iff, Polynomial.map_map]
    rfl

include hx hx'

lemma ideal_span_pair_maximal_int [Fact $ Nat.Prime p] (d : ℤ[X]) (d' : (ZMod p) [X])
  (hdeq : d' = d.map (algebraMap ℤ (ZMod p))) (hd : d' ∣ (minpoly ℤ x).map (algebraMap ℤ (ZMod p)))
  (hdirr : Irreducible d') : IsMaximal (span {↑p, (aeval x) d}) := by
  rw [quotMapInt.ideal_span_eq_span]
  refine ideal_span_pair_maximal hx hx' ?_ d ?_ ?_
  · exact Ideal.Quotient.maximal_of_isField _ <|
    (Int.quotientSpanNatEquivZMod p).toMulEquiv.isField (Field.toIsField _)
  · rw [← map_dvd_iff (Polynomial.mapEquiv ((Int.quotientSpanNatEquivZMod p)))]
    simp only [mapEquiv_apply, Polynomial.map_map]
    exact hdeq ▸ hd
  · rw [← MulEquiv.irreducible_iff (Polynomial.mapEquiv ((Int.quotientSpanNatEquivZMod p)))]
    simp only [mapEquiv_apply, Polynomial.map_map]
    exact hdeq ▸ hdirr


lemma card_quot_span [Fact $ Nat.Prime p]  (d : ℤ[X]) (d' : (ZMod p) [X])
  (hdeq : d' = d.map (algebraMap ℤ (ZMod p)))
  (hd : d' ∣ (minpoly ℤ x).map (algebraMap ℤ (ZMod p))) :
  Nat.card (S ⧸ Ideal.span {↑p, d.aeval x}) = p ^ d'.natDegree := by
  rw [Nat.card_eq_of_bijective (quotMapEquivInt hx hx' d d' hdeq hd)]
  show Nat.card (AdjoinRoot d') = p ^ d'.natDegree
  have hdz : d' ≠ 0 := by
    by_contra hc
    rw [hc, algebraMap_int_eq, zero_dvd_iff] at hd
    refine (Polynomial.map_monic_ne_zero (minpoly.monic hx') ) hd
  haveI : Module.Finite (ZMod p) (AdjoinRoot d') := PowerBasis.finite (AdjoinRoot.powerBasis hdz)
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Module.finrank_eq_card_basis
    (AdjoinRoot.powerBasis hdz).basis, (AdjoinRoot.powerBasis_dim hdz)]
  simp only [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]
  exact RingEquiv.bijective (quotMapEquivInt hx hx' d d' hdeq hd)






lemma prod_ideal_eq_span_singleton {n} [Fact $ Nat.Prime p]
  (d : Fin n → ℤ[X]) --(d' : Fin n → (ZMod p)[X])
  --(hdeq : ∀ i, d' i = (d i).map (algebraMap ℤ (ZMod p)))
  --(hprod : ∏ i, d' i = (minpoly ℤ x).map (algebraMap ℤ (ZMod p)))
  (I : Fin n → Ideal S) (hI : ∀ i, I i = Ideal.span {↑p, (d i).aeval x}) :
    ∏ i , I i ≤ Ideal.span {↑p, (∏ i, d i).aeval x} := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_eq_top, map_one, top_le_iff]
    refine Submodule.eq_top_iff'.mpr (Ideal.mem_of_one_mem ?_)
    refine Set.mem_of_subset_of_mem (Ideal.subset_span ) ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  | succ n hn =>
    rw [Fin.prod_univ_castSucc]
    specialize hn (fun i => d i.castSucc) (fun i => I i.castSucc) (fun i => hI _ )
    refine le_trans (Ideal.mul_mono hn (le_of_eq rfl) ) ?_
    rw [hI, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    intro x hx
    sorry
    --rcases hx with hx1 | hx2 | hx3 | hx4










  /- suffices aux : (Finset.univ (α := τ)) = ∅ ∨ ∏ i, I i ≤ Ideal.span {↑p} from by
    rw [← false_or (p := ∏ i, I i ≤ span {↑p})]
    convert aux
    rw [false_iff]
    show Finset.univ ≠ ∅
    simp only [← Finset.nonempty_iff_ne_empty, Finset.univ_nonempty] -/
  --simp_rw [hI]
  --rw [Ideal.prod_span, Ideal.span_le]
  --induction' (Finset.univ (α := τ)) using Finset.Nonempty.cons_induction with s hs
  --refine Finset.Nonempty.cons_induction (s := Finset.univ (α := τ)) ?_ ?_ ?_
  --· simp only [Finset.univ_nonempty]
  --· intro i
  --  sorry

  --· simp only [Finset.prod_empty, Set.one_subset, SetLike.mem_coe, true_or]
  --· intro a hs has

  --intro x hx
  --sorry



/- lemma prod_ideal_eq_span_singleton {τ} [Fintype τ] [Fact $ Nat.Prime p]
  (d : τ → ℤ[X])  (hdeq : ∀ i, d' i = (d i).map (algebraMap ℤ (ZMod p)))
  (d' : τ → (ZMod p)[X]) (hcoprime : Pairwise (IsCoprime) d')
  (hprod : ∏ i, d' i = (minpoly ℤ x).map (algebraMap ℤ (ZMod p)))
  (I : τ → Ideal S) (hI : ∀ i, I i = Ideal.span {↑p, d.aeval x}) : -/


  --apply?



-- (AdjoinRoot.mk (X ^ r - 1)) (AKSPolynomial n a) = (AdjoinRoot.mk (X ^ r - 1)) (AKSRightSide n a)

-- Ideal.Quotient.mk










  --swap


  --refine RingEquiv.trans (quotEquivOfEq (show ))


















#exit


def liftPolynomial (a : S) : R[X] := by
  refine (Polynomial.map_surjective (Ideal.Quotient.mk _) (Ideal.Quotient.mk_surjective)
  (Ideal.Quotient.mk_surjective ((quotMapEquivQuotQuotMap' hx hx') (Ideal.Quotient.mk _ a))).choose ).choose


lemma quotMapEquiv_apply (a : S) : (quotMapEquivQuotQuotMap' hx hx' (Ideal.Quotient.mk _ a)) =
  Ideal.Quotient.mk _ ((liftPolynomial hx hx' a).map (algebraMap R (R ⧸ I))) := by
  unfold liftPolynomial
  have aux1 := (Polynomial.map_surjective (Ideal.Quotient.mk _) (Ideal.Quotient.mk_surjective)
  (Ideal.Quotient.mk_surjective ((quotMapEquivQuotQuotMap' hx hx') (Ideal.Quotient.mk _ a))).choose ).choose_spec
  have aux2 := (Ideal.Quotient.mk_surjective ((quotMapEquivQuotQuotMap' hx hx') (Ideal.Quotient.mk _ a))).choose_spec
  erw [aux1, aux2]


lemma quotMapHom_apply (d : R[X])
  (hd : d.map (algebraMap R (R ⧸ I)) ∣ Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))
  (a : S) :
  quotMapHom hx hx' (d.map (algebraMap R (R ⧸ I))) hd a =
    Ideal.Quotient.mk _ ((liftPolynomial hx hx' a).map (algebraMap R (R ⧸ I))) := by
  unfold quotMapHom
  simp only [Quotient.algebraMap_eq, AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, coe_comp,
    coe_coe, Function.comp_apply]
  erw [quotMapEquiv_apply, AdjoinRoot.algHomDvd_polynomial_apply]
  rfl


def quotMapHomKer (d : R[X])
  (hd : d.map (algebraMap R (R ⧸ I)) ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
  RingHom.ker (quotMapHom hx hx' (d.map (algebraMap R (R ⧸ I))) hd) =
    Ideal.span (I.map (algebraMap R S) ∪ {d.aeval x}) := by
  unfold quotMapHom
  rw [← RingHom.comap_ker, ← RingHom.comap_ker]
  refine le_antisymm ?_ ?_
  · sorry
  · sorry

-- [hI : IsMaximal I]
