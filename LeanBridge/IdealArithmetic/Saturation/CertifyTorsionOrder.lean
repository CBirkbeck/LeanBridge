/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.IdealArithmetic.CertifyPrimeIdeal
import LeanBridge.IdealArithmetic.Signature.Sturm
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Results on embeddings and orders torsion subgroups

In the context of number fields, we express the number of infinite places
in terms of the degree and the number of real roots of a defining polynomial. We give
results to certify divisibility conditions on the order of the torsion subgroup.
## Main definition
- `RankUnitsCertificate`: certify the rank of the unit group from a sturm sequence.

## Main results
- `card_infinite_place_adjoin_root`: the number of infinite places in terms of the number of
  real roots and the degree of a defining polynomial.
- `prime_not_dvd_torsion_of_not_dvd`: a way to prove that a prime `p` does not divide the
  torsion order by using a witness ideal.
- `eq_card_torsion_of_pow_of_gcd `: can be used to prove the exact size of the torsion subgroup.  -/

open Classical Finset NumberField InfinitePlace Polynomial Module

/-- The real embeddings of a number field are in bijection with the real
  roots of a defining polynomial-/
noncomputable def equivRealEmbeddingsRealRoots (K : Type*) [Field K] [NumberField K] {f : ℚ[X]}
    (hf : f ≠ 0) (hr : IsAdjoinRoot K f) :
    { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } ≃ { x // x ∈ (map (algebraMap ℚ ℝ) f).roots} := by
  let i : { φ // ComplexEmbedding.IsReal φ } → ℝ :=
    fun ⟨φ, hφ⟩ => (ComplexEmbedding.IsReal.embedding hφ) hr.root
  have hmem : ∀ φ, ∀ hφ : ComplexEmbedding.IsReal φ,  i ⟨φ, hφ⟩
    ∈ (map (algebraMap ℚ ℝ) f).roots := by
    intro a ha
    simp [i, hf]
    letI aux : Algebra K ℝ := ha.embedding.toAlgebra
    rw [← RingHom.algebraMap_toAlgebra ((ComplexEmbedding.IsReal.embedding ha)),
      Polynomial.aeval_algebraMap_apply, IsAdjoinRoot.aeval_root_self hr, map_zero]
  refine Equiv.ofBijective (fun ⟨φ, hφ⟩  => ⟨i ⟨φ, hφ⟩, hmem φ hφ⟩ ) ?_
  constructor
  · rintro φ τ heq
    rw [← Subtype.val_inj] at heq ⊢
    dsimp at heq
    have aux1 := IsAdjoinRoot.eq_lift (x := i φ) (i := algebraMap ℚ ℝ) hr ?_
      (ComplexEmbedding.IsReal.embedding φ.2) (by simp) rfl
    have aux2 := IsAdjoinRoot.eq_lift (x := i τ) (i := algebraMap ℚ ℝ) hr ?_
      (ComplexEmbedding.IsReal.embedding τ.2) (by simp) rfl
    simp_rw [heq, ← aux2] at aux1
    ext x
    rw [← NumberField.ComplexEmbedding.IsReal.coe_embedding_apply φ.2 x,
      ← NumberField.ComplexEmbedding.IsReal.coe_embedding_apply τ.2 x, aux1]
    · letI aux : Algebra K ℝ := (τ.2).embedding.toAlgebra
      have : algebraMap K ℝ = (τ.2).embedding := rfl
      simp[i]
      rw [IsScalarTower.algebraMap_eq ℚ K ℝ, ← Polynomial.eval₂_map, this,
        Polynomial.eval₂_hom, Polynomial.eval_map, ← Polynomial.aeval_def,
          IsAdjoinRoot.aeval_root_self, map_zero]
    · letI aux : Algebra K ℝ := (φ.2).embedding.toAlgebra
      have : algebraMap K ℝ = (φ.2).embedding := rfl
      simp[i]
      rw [IsScalarTower.algebraMap_eq ℚ K ℝ, ← Polynomial.eval₂_map, this,
        Polynomial.eval₂_hom, Polynomial.eval_map, ← Polynomial.aeval_def,
          IsAdjoinRoot.aeval_root_self, map_zero]
  · rintro ⟨x, hx⟩
    simp at hx
    let φ := (algebraMap ℝ ℂ).comp (IsAdjoinRoot.lift hr (algebraMap ℚ ℝ) x
      (by  rw [← Polynomial.aeval_def] ; exact hx.2))
    have hφ: ComplexEmbedding.IsReal φ := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      simp [φ]
    use ⟨φ, hφ⟩
    simp [i]
    apply_fun (algebraMap ℝ ℂ)
    dsimp
    convert (NumberField.ComplexEmbedding.IsReal.coe_embedding_apply hφ hr.root)
    simp [φ]
    exact Complex.ofReal_injective

theorem nrRealPlaces_eq_nr_real_roots (K : Type*) [Field K] [NumberField K] {f : ℚ[X]}
    (hf : f ≠ 0) (hr : IsAdjoinRoot K f) :
    nrRealPlaces K = #(Multiset.toFinset (map (algebraMap ℚ ℝ) f).roots) := by
  rw [← NumberField.InfinitePlace.card_real_embeddings]
  symm ; apply Finset.card_eq_of_equiv_fintype
  simp_rw [Multiset.mem_toFinset]
  exact (equivRealEmbeddingsRealRoots K hf hr).symm

lemma card_infinite_place_eq (K : Type*) [Field K] [NumberField K] :
    Fintype.card (InfinitePlace K) = (nrRealPlaces K + Module.finrank ℚ K) / 2 := by
  rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank, ← add_assoc, ← two_mul,
    ← mul_add]
  simp[NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

/-- The number of infinite places of a number field in terms of the number of real roots
  and the degree of the polynomial. -/
lemma card_infinite_place_adjoin_root (K : Type*) [Field K] [NumberField K] (f : ℚ[X]) (hf : f ≠ 0)
    (hr : IsAdjoinRoot K f) :
    Fintype.card (InfinitePlace K) =
      (#(Multiset.toFinset (map (algebraMap ℚ ℝ) f).roots) + f.natDegree) / 2 := by
  rw [card_infinite_place_eq, nrRealPlaces_eq_nr_real_roots K hf hr]
  congr
  rw [LinearEquiv.finrank_eq ((IsAdjoinRoot.algEquiv hr (AdjoinRoot.isAdjoinRoot f)).toLinearEquiv),
    Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux hf)]
  simp

/- Note: If the torsion subgroup (which is cyclic) has cardinality divisible by `t`,
  then it has a root of order `t` and thus is a root of `Φₜ(X)`. The order of this polynomial `φ(t)`
  divides the degree `n` of `K`.
  Hence, if `p^m` divides torsion order, then `p^(m-1) * (p - 1)` divides `n`. -/

/-- If an element `x` of prime order `p` is mapped through a ring homomorphism,
  and the characteristic of the codomain does not divide `p`, then the image
  of `x` also has order `p`.  -/
lemma orderOf_prime_map  {S R : Type*} {q p : ℕ} [CommRing S] [IsDomain S] [CommRing R] [CharP R q]
  [hp : Fact $ Nat.Prime p] (hneq : ¬ q ∣ p)
  (φ : S →+* R) {x : S} (ho : orderOf x = p) : orderOf (φ x) = p := by
  rw [orderOf_eq_prime_iff] at ho ⊢
  rcases ho with ⟨ho1, ho2⟩
  rw [ne_eq, ← sub_eq_zero] at ho2
  have hec := Polynomial.cyclotomic_prime_mul_X_sub_one S p
  apply_fun (fun P => Polynomial.eval x P) at hec
  simp[ho1, ho2] at hec
  constructor
  · rw [← map_pow, ho1]
    simp
  · intro h
    apply_fun φ at hec
    rw [← Polynomial.cyclotomic.eval_apply, h,
      eval_one_cyclotomic_prime, map_zero, CharP.cast_eq_zero_iff R q p] at hec
    exact hneq hec

/-- Similar to `orderOf_prime_map` but for a general `n`. However, we include
  the assumption that `R` is a domain. -/
lemma orderOf_map_CharP  {S R : Type*} {q n : ℕ} [CommRing S] [IsDomain S]
  [CommRing R] [IsDomain R] [CharP R q] [NeZero n] (hneq : ¬ q ∣ n)
  (φ : S →+* R) {x : S} (ho : orderOf x = n) : orderOf (φ x) = n  := by
  have aux := IsPrimitiveRoot.isRoot_cyclotomic
    (Nat.pos_of_neZero _) (ho ▸ IsPrimitiveRoot.orderOf x)
  symm
  apply IsPrimitiveRoot.eq_orderOf
  haveI : NeZero (↑n : R) := by
    refine NeZero.of_not_dvd (p := q) R hneq
  rw [← Polynomial.isRoot_cyclotomic_iff]
  simp at aux ⊢
  rw [Polynomial.cyclotomic.eval_apply, aux, map_zero]

/--  If an element `x` of prime order `p ^ m` is mapped through a ring homomorphism,
  and the characteristic of the codomain does not divide `p`,
  then the image of `x` also has order `p ^ m`. -/
lemma orderOf_prime_pow_map  {S R : Type*} {q p m : ℕ} [CommRing S] [IsDomain S]
  [CommRing R] [IsDomain R] [CharP R q] [hp : Fact $ Nat.Prime p] (hneq : ¬ q ∣ p)
  (φ : S →+* R) {x : S} (ho : orderOf x = p ^ m) : orderOf (φ x) = p ^ m  := by
  refine orderOf_map_CharP (q := q) ?_ φ ho
  rcases CharP.char_is_prime_or_zero R q with h1 | h2
  · intro h
    exact hneq (Nat.Prime.dvd_of_dvd_pow h1 h)
  · rw [h2]
    intro h
    simp only [zero_dvd_iff, pow_eq_zero_iff', Nat.Prime.ne_zero hp.out, ne_eq, false_and] at h

/-- Provides a way to certify that a prime `p` does not divide the order of the torsion subgroup.
  The existance of such a certificate can be proven with Chebotarev's density theorem.   -/
lemma prime_not_dvd_torsion_of_not_dvd {S : Type*} [CommRing S] [IsDomain S] {p q : ℕ}
    [hp : Fact $ Nat.Prime p] (hq : Nat.Prime q)
    [Fintype (CommGroup.torsion Sˣ)](I : Ideal S) (hcard : Nat.card (S ⧸ I) = q)
    (hpndvd : ¬ p ∣ (q - 1)) (hneq : p ≠ q) :
     ¬ p ∣ Nat.card (CommGroup.torsion Sˣ) := by
  haveI : Fact $ Nat.Prime q := {out := hq}
  rw [Nat.card_eq_fintype_card]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hdvd
  rw [← orderOf_submonoid, ← orderOf_units] at hx
  let φ := (modIdealToZMod hq I hcard).comp (Ideal.Quotient.mk I)
  have aux : orderOf (φ ((x : Sˣ) : S)) = p := by
    refine orderOf_prime_map (q := q) ?_ φ hx
    rw [Nat.prime_dvd_prime_iff_eq hq hp.out]
    exact hneq.symm
  let y := IsOfFinOrder.unit (x := φ ((x : Sˣ) : S))
    (by by_contra hc ; rw [← orderOf_eq_zero_iff, aux] at hc ; exact Nat.Prime.ne_zero hp.out hc)
  have aux2 : orderOf y = p := by
    rw [← orderOf_units]
    simp[y, aux]
  apply hpndvd
  convert aux2 ▸ orderOf_dvd_card
  rw [(Nat.prime_iff_card_units q).1 hq]

/- Note: If we want to, this can be further generalized to any prime ideal above `q`,
  and assuming `n` does not divide `q^m - 1`, where `q^m` is the norm of this ideal.
  However, we know that is suffices to consider primes of degree 1. -/

/-- Generalization of `prime_not_dvd_torsion_of_not_dvd` assuming the torsion subgroup is cyclic. -/
lemma not_dvd_torsion_of_not_dvd {S : Type*} [CommRing S] [IsDomain S]
    {n q : ℕ} [hn : NeZero n] (hq : Nat.Prime q)
    [Fintype (CommGroup.torsion Sˣ)](hC : IsCyclic (CommGroup.torsion Sˣ))
    (I : Ideal S) (hcard : Nat.card (S ⧸ I) = q)
    (hpndvd : ¬ n ∣ q - 1) (hneq : ¬ q ∣ n) :
     ¬ n ∣ Nat.card (CommGroup.torsion Sˣ) := by
  haveI : Fact $ Nat.Prime q := {out := hq}
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 hC
  intro hdvd
  rw [← hg] at hdvd
  set x := g ^ (orderOf g / n) with hxd
  have hx := hxd ▸ orderOf_pow_orderOf_div (Nat.ne_zero_of_lt (orderOf_pos g)) hdvd
  rw [← orderOf_submonoid, ← orderOf_units] at hx
  let φ := (modIdealToZMod hq I hcard).comp (Ideal.Quotient.mk I)
  have aux : orderOf (φ ((x : Sˣ) : S)) = n := by
    refine orderOf_map_CharP (q := q) hneq φ hx
  let y := IsOfFinOrder.unit (x := φ ((x : Sˣ) : S))
    (by by_contra hc ; rw [← orderOf_eq_zero_iff, aux] at hc ; exact (NeZero.ne n) hc )
  have aux2 : orderOf y = n := by
    rw [← orderOf_units]
    simp[y, aux]
  apply hpndvd
  convert aux2 ▸ orderOf_dvd_card
  rw [(Nat.prime_iff_card_units q).1 hq]

lemma prime_pow_not_dvd_torsion_of_not_dvd {S : Type*} [CommRing S] [IsDomain S]
    {p q m : ℕ} [hp : Fact $ Nat.Prime p] (hq : Nat.Prime q)
    [Fintype (CommGroup.torsion Sˣ)](hC : IsCyclic (CommGroup.torsion Sˣ))
    (I : Ideal S) (hcard : Nat.card (S ⧸ I) = q)
    (hpndvd : ¬ p ^ m ∣ q - 1) (hneq : p ≠ q) :
     ¬ p ^ m ∣ Nat.card (CommGroup.torsion Sˣ) := by
  refine not_dvd_torsion_of_not_dvd hq hC I hcard hpndvd ?_
  intro h
  exact hneq.symm ((Nat.prime_dvd_prime_iff_eq hq hp.out).1 (Nat.Prime.dvd_of_dvd_pow hq h))

lemma dvd_of_dvd_torsion {S : Type*} [CommRing S] [IsDomain S]
    {n q : ℕ} [hn : NeZero n] (hq : Nat.Prime q)
    [Fintype (CommGroup.torsion Sˣ)](hC : IsCyclic (CommGroup.torsion Sˣ))
    (I : Ideal S) (hcard : Nat.card (S ⧸ I) = q) (hneq : ¬ q ∣ n)
    (hndd : n ∣ Nat.card (CommGroup.torsion Sˣ)) : n ∣ q - 1 := by
  revert hndd
  contrapose
  intro hpndvd
  exact not_dvd_torsion_of_not_dvd hq hC I hcard hpndvd hneq

/- Note: In the case of number fields, if there is a torsion element of order `m`, then
  its minimal poly of order `φ(m)` divides the degree `d` of the number field. In particular,
  if `p` divides `m`, then `p-1` must divide `d`. Hence, prime divisors of the size of the
  torsion group are a subset of the primes `≤ d + 1` such that `p-1 ∣ d`. -/

/-- We can certify that the size of the torsion group is exactly `n`, without explicitely
  calculating it if:
* We provide a set `M` of primes containing all the possible prime divisors of the
  torsion order (for a number field of degree `d`, this can be the primes `≤ d + 1`
  such that `p-1 ∣ d`).
* We provide a set of natural numbers `P` such that `lcm P = n` and for every `p ∈ P`
  there exists an `x` of order `p`.
* We provide a collection of prime ideals `I₁, ..., Iₘ` of degree 1 of norm
  `q₁, ..., qₘ` respectively, such that the `gcd` of the set
  `{q₁-1, ..., qₘ-1}` is `n`. -/

theorem eq_card_torsion_of_pow_of_gcd {ι : Type*} {S : Type*} [CommRing S] [IsDomain S]
    {n : ℕ} (M P : Finset ℕ) [Fintype ι] (q : ι → ℕ) (hq : ∀ i, Nat.Prime (q i))
    [Fintype (CommGroup.torsion Sˣ)](hC : IsCyclic (CommGroup.torsion Sˣ))
    (hmemd : ∀ p , Nat.Prime p → p ∣ Nat.card (CommGroup.torsion Sˣ) → p ∈ M)
    (I : ι → Ideal S) (hcard : ∀ i, Nat.card (S ⧸ (I i)) = q i)
    (hneq : ∀ i, ¬ (q i) ∈ M) (hPnz : ∀ p ∈ P, p ≠ 0)
    (hpow : ∀ p ∈ P, ∃ (x : S), orderOf x = p) (hgcd1 : Finset.lcm P id = n)
    (hgcd2 : (Finset.gcd (Finset.univ) (fun i : ι => (q i) - 1)) = n) :
    Nat.card (CommGroup.torsion Sˣ) = n := by
  apply Nat.dvd_antisymm
  · rw [← hgcd2, Finset.dvd_gcd_iff]
    simp only [mem_univ, Nat.card_eq_fintype_card, forall_const]
    intro i
    refine dvd_of_dvd_torsion (hq i) hC (I i) (hcard i) ?_ ?_
    · rw [← Nat.card_eq_fintype_card]
      intro h
      apply hneq i
      exact hmemd (q i) (hq i) h
    · rw [Nat.card_eq_fintype_card]
  · rw [← hgcd1, Finset.lcm_dvd_iff]
    intro b hbP
    obtain ⟨x, hx⟩ := hpow b hbP
    let x' := Units.ofPowEqOne x _
      ((orderOf_eq_iff (Nat.pos_of_ne_zero (hPnz b hbP))).1 hx).1 ((hPnz b hbP))
    have hmem : x' ∈ CommGroup.torsion Sˣ := by
      rw [CommGroup.mem_torsion, ← orderOf_pos_iff, ← orderOf_units]
      simp [x', hx, Nat.pos_of_ne_zero (hPnz b hbP)]
    have hord2 : orderOf (⟨x', hmem⟩ : CommGroup.torsion Sˣ) = b  := by
      simp only [Subgroup.orderOf_mk, ← orderOf_units, Units.val_ofPowEqOne, hx, x']
    rw [← hord2]
    exact orderOf_dvd_natCard _

/- NOTE: In general, I want less primes to show up in the gcd. So is something gained if i consider
  primes of degree greater than `1`? -/

open NumberField Units

/-- If `p` divides the torsion order of a number field `K`, then `p-1` divides its degree. -/
theorem prime_sub_dvd_finrank_of_prime_dvd_card_torsion {K : Type*} [Field K]
    [NumberField K] {p : ℕ} [hp : Fact $ Nat.Prime p]
    (hpdvd : p ∣ torsionOrder K) : p - 1 ∣ Module.finrank ℚ K := by
  simp [torsionOrder] at hpdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have aux : IsPrimitiveRoot ((x : (RingOfIntegers K)ˣ) : K) p := by
    erw [← orderOf_submonoid, ← orderOf_units, ← orderOf_submonoid] at hx
    rw [← hx]
    exact IsPrimitiveRoot.orderOf _
  have := Polynomial.cyclotomic_eq_minpoly_rat aux (Nat.pos_of_neZero p)
  convert minpoly.degree_dvd (x := ((x : (RingOfIntegers K)ˣ) : K)) ?_
  · rw [← this, Polynomial.natDegree_cyclotomic, Nat.totient_prime hp.out]
  · rw [← minpoly.ne_zero_iff, ← this]
    exact cyclotomic_ne_zero p ℚ

open Polynomial

/-- Certify the rank of the unit group of a number field from a Sturm sequence. -/
structure RankUnitsCertificate {K : Type*} [Field K] [NumberField K]
  (O : Subalgebra ℤ K) where
  f : ℤ[X]
  l : List ℤ
  hl : ofList l = f
  hlz : l = l.dropTrailingZeros'
  hz : l ≠ []
  hAdj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) f)
  heq : O = integralClosure ℤ K
  P : List (List ℤ)
  SB : SturmBuilderOfList P l (List.derivative l).dropTrailingZeros
  k : ℕ
  r : ℕ
  hr : signChangesNInftyOfList P - signChangesInftyOfList P = k
  hreq : (k + (l.length - 1)) / 2 = r

open NumberField

lemma card_infinitePlace_of_RankUnitsCertificate {K : Type*} [Field K] [NumberField K]
    {O : Subalgebra ℤ K} (C : RankUnitsCertificate O) : Fintype.card (InfinitePlace K) = C.r := by
  rw [card_infinite_place_adjoin_root K _ ?_ C.hAdj, ← C.hl, Polynomial.map_map]
  erw [sturm_theorem_total_map_ofList ℝ (Real.IsRealClosedField)
    (algebraMap ℤ ℝ) (Int.cast_strictMono) C.SB]
  rw [C.hr, Polynomial.natDegree_map_eq_of_injective]
  convert C.hreq
  rw [← natDegree_ofList C.l (C.hz), add_tsub_cancel_right]
  · rw [dropTrailingZeros_eq_dropTrailingZeros']
    exact C.hlz
  · exact RingHom.injective_int (algebraMap ℤ ℚ)
  · rw [Polynomial.map_ne_zero_iff (RingHom.injective_int (algebraMap ℤ ℚ)), ← C.hl ]
    intro hc
    exact (C.hz) (nil_of_ofList_eq_zero C.l
      ((dropTrailingZeros_eq_dropTrailingZeros' C.l ).symm ▸ C.hlz) hc)

lemma units_finrank_of_RankUnitsCertificate {K : Type*} [Field K] [NumberField K]
    {O : Subalgebra ℤ K} (C : RankUnitsCertificate O) :
    Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) = C.r - 1  := by
  conv =>
    left
    erw [C.heq, NumberField.Units.rank_modTorsion]
  unfold NumberField.Units.rank
  rw [card_infinitePlace_of_RankUnitsCertificate C]

lemma nrComplexPlaces_of_RankUnitsCertificate {K : Type*} [Field K] [NumberField K]
    {O : Subalgebra ℤ K} (C : RankUnitsCertificate O) :
    InfinitePlace.nrComplexPlaces K = C.r - C.k := by
  rw [← card_infinitePlace_of_RankUnitsCertificate C,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← C.hr,
      ← sturm_theorem_total_map_ofList ℝ (Real.IsRealClosedField) (algebraMap ℤ ℝ)
      (Int.cast_strictMono) C.SB, nrRealPlaces_eq_nr_real_roots K _ C.hAdj,
      add_comm, Polynomial.map_map]
  have : (algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℝ := by rfl
  rw [this, C.hl]
  simp only [algebraMap_int_eq, add_tsub_cancel_right]
  · rw [Polynomial.map_ne_zero_iff (RingHom.injective_int (algebraMap ℤ ℚ)), ← C.hl ]
    intro hc
    exact (C.hz) (nil_of_ofList_eq_zero C.l
      ((dropTrailingZeros_eq_dropTrailingZeros' C.l ).symm ▸ C.hlz) hc)
