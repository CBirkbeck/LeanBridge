/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import LeanBridge.ForMathlib.FieldTheory.Finite.IrreduciblePolynomialZModp

/-!
# Certificate for the primality of an ideal

We define a certificate for the primality of an ideal of finite norm.

## Main definition
- `PrimeIdeal`: certifying structure for prime ideals.

## Main results
- `ideal_norm_eq_prod'`: the norm of an ideal given as a lower diagonal matrix.
- `PrimeIdeal_isPrime`: an ideal with a primality certificate is prime.  -/

open Polynomial Module

/-- If `K` is an `F`-algebra of rank `n` and `f` is an irreducible polynomial over `F` with
  a zero in `K`, then `K ≃ F[X]/⟨f⟩ `. -/
noncomputable def IsAdjoinRoot_of_adjoin_root_irreducible {F K : Type*} [CommRing K] [Field F]
    [DecidableEq F] [Algebra F K] [FiniteDimensional F K] (f : F[X]) (hI : Irreducible f)
    (ha : ∃ (a : K) , Polynomial.aeval a f = 0 )
    (hr : Module.finrank F K = f.natDegree) : IsAdjoinRoot K f := by
  choose a h using ha
  have hint : IsIntegral F a := by
    use (normalize f)
    constructor
    · exact (Polynomial.monic_normalize (Irreducible.ne_zero hI))
    · rw [← Polynomial.aeval_def]
      simp only [normalize_apply, coe_normUnit, map_mul, h, aeval_C, zero_mul]
  have hmin : minpoly F a = normalize f := by
    simp only [normalize_apply, coe_normUnit]
    convert (minpoly.eq_of_irreducible hI h).symm
    refine CommGroupWithZero.coe_normUnit F (Polynomial.leadingCoeff_ne_zero.2 (
      Irreducible.ne_zero hI))
    · rw [← Module.finrank_pos_iff (R := F), hr]
      exact Irreducible.natDegree_pos hI
  have := Algebra.adjoin_isAdjoinRoot (Q := F) (K := K) (normalize f)
    (Polynomial.monic_normalize (Irreducible.ne_zero hI)) a ?_
  swap
  · rw [hmin]
    simp only [normalize_apply, coe_normUnit, Algebra.algebraMap_self, Polynomial.map_mul, map_id,
      map_C, RingHom.id_apply]
  let e : Algebra.adjoin F {a} →ₐ[F] K := Subalgebra.val _
  have heB : Function.Bijective e := by
    show Function.Bijective e.toLinearMap
    constructor
    · exact (AlgHom.injective_codRestrict _ _ _).mp fun ⦃a₁ a₂⦄ a ↦ a
    · rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
      exact (AlgHom.injective_codRestrict _ _ _).mp fun ⦃a₁ a₂⦄ a ↦ a
      rw [PowerBasis.finrank (Algebra.adjoin.powerBasis hint), hr]
      simp only [Algebra.adjoin.powerBasis_dim, hmin, normalize_apply, coe_normUnit]
      refine Polynomial.natDegree_mul_C_eq_of_mul_ne_zero ?_
      simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero, Units.ne_zero, or_false]
      exact Irreducible.ne_zero hI
  have IsA := IsAdjoinRoot.ofAlgEquiv this (AlgEquiv.ofBijective e heB)
  exact
  { map := IsA.map
    map_surjective := IsA.map_surjective
    ker_map := by
      rw [IsA.ker_map, normalize_apply, coe_normUnit]
      refine Ideal.span_singleton_mul_right_unit ?_ _
      simp only [isUnit_map_iff, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true] }

noncomputable def field_of_adjoin_root_irreducible {F K : Type*} [CommRing K] [Field F]
  [DecidableEq F] [Algebra F K] [FiniteDimensional F K] (f : F[X]) (hI : Irreducible f)
  (ha : ∃ (a : K) , Polynomial.aeval a f = 0 )
  (hr : Module.finrank F K = f.natDegree) : IsField K := by
  letI E := IsAdjoinRoot.algEquiv (IsAdjoinRoot_of_adjoin_root_irreducible f hI ha hr)
    (AdjoinRoot.isAdjoinRoot f)
  haveI : Fact $ Irreducible f := { out := hI }
  exact (MulEquiv.isField  (Semifield.toIsField (AdjoinRoot f)) E.toMulEquiv)

/-- If `O` is an `R`-algebra with a basis, and `I` is a nonzero ideal with the coordinates of
  the `ℤ`-generators given as the rows of a matrix `V`, then the `indexPID` of `I` in `O`
  is associated to the determinant of `V`.   -/
lemma ideal_index_associated_det (O R : Type*) [CommRing O]
    [CommRing R]{τ : Type*} [DecidableEq τ][Fintype τ] [IsDomain R] [IsPrincipalIdealRing R]
    [IsDomain O] [Algebra R O] (B : Basis τ R O) (I : Ideal O)
    [Module.Free R O] [Module.Finite R O] [Module.Free R I] (hI : I ≠ ⊥)
    (V : Matrix τ τ R)
    (heq : I.carrier = Submodule.span R (Set.range (fun i => B.equivFun.symm (V i)))) :
    Associated (Submodule.indexPID (I.restrictScalars R)) (V.det) := by
  let BI := BasisOfEqSpan B I hI (fun i => B.equivFun.symm (V i)) heq
  have eqV : LinearMap.toMatrix BI B (Submodule.subtype (I.restrictScalars R)) = V.transpose := by
    ext i j
    erw [Matrix.transpose_apply, LinearMap.toMatrix_apply]
    have aux : B.repr ↑(BI j) = V j := by
      apply_fun B.equivFun.symm
      rw [Basis.equivFun_symm_eq_repr_symm, LinearEquiv.symm_apply_apply,
      BasisOfEqSpan_apply B I hI (fun i => B.equivFun.symm (V i)) heq j]
      exact LinearEquiv.injective B.equivFun.symm
    exact congrFun aux i
  rw [← Matrix.det_transpose]
  convert associated_index_of_basis (I.restrictScalars R) B BI
  convert eqV.symm
  congr
  exact Subsingleton.elim _ _

/-- If `O` is an `R`-algebra with a basis, and `I` is a nonzero ideal with the coordinates of
  the `ℤ`-generators given as the rows of a matrix `V`, which is lower triangular,
  then the `indexPID` of `I` in `O` is associated to the product of the diagonal of `V`.   -/
lemma ideal_index_associated_prod {r : ℕ} (O R : Type*) [CommRing O]
    [CommRing R][IsDomain R] [IsPrincipalIdealRing R]
    [IsDomain O] [Algebra R O] (B : Basis (Fin r) R O) (I : Ideal O)
    [Module.Free R O] [Module.Finite R O] [Module.Free R I] (hI : I ≠ ⊥)
    (V : Fin r → Fin r → R) (hd : ∀ i j, i < j → V i j = 0)
    (heq : I.carrier = Submodule.span R (Set.range (fun i => B.equivFun.symm (V i)))) :
    Associated (Submodule.indexPID (I.restrictScalars R)) (∏ i, V i i) := by
  convert ideal_index_associated_det O R B I hI V heq
  symm
  refine Matrix.det_of_lowerTriangular _ ?_
  intro i j
  simp only [OrderDual.toDual_lt_toDual]
  exact hd i j

-- Note: We don't use `Ideal.absNorm` because we don't assume `O` is a Dedekind Domain. This
-- must save us time (how much?) in type class inference.

/-- If `O` is an `R`-algebra with a basis, and `I` is a nonzero ideal with the coordinates of
  the `ℤ`-generators given as the rows of a matrix `V`, which is lower triangular,
  then the cardinality of `O ⧸ I` is the absolute value of the product of the diagonal of `V`.  -/
lemma ideal_norm_eq_prod {r : ℕ} {O : Type*} [CommRing O]
    [IsDomain O] (B : Basis (Fin r) ℤ O) (I : Ideal O) (hI : I ≠ ⊥)
    (V : Fin r → Fin r → ℤ) (hd : ∀ i j, i < j → V i j = 0)
    (heq : I.carrier = Submodule.span ℤ (Set.range (fun i => B.equivFun.symm (V i)))) :
    Nat.card (O ⧸ I) = (∏ i, V i i).natAbs := by
  let BI := BasisOfEqSpan B I hI (fun i => B.equivFun.symm (V i)) heq
  haveI : Module.Finite ℤ O := Module.Finite.of_basis B
  haveI : Module.Free ℤ O := Module.Free.of_basis B
  rw [Int.natAbs_eq_iff_associated.2 (ideal_index_associated_prod O ℤ B I hI V hd heq ).symm ]
  symm
  exact indexPID_eq_index_int _ B BI

/-- A version of`ideal_norm_eq_prod` without the nonzero assumption on the ideal `I`. Instead,
  an entry of the matrix `V` is shown to be nonzero. This is easier to prove by computation. -/
lemma ideal_norm_eq_prod' {r : ℕ} {O : Type*} [CommRing O] [IsDomain O]
    (B : Basis (Fin r) ℤ O) (I : Ideal O) (V : Fin r → Fin r → ℤ) (hd : ∀ i j, i < j → V i j = 0)
    (i : Fin r) (j : Fin r) (hij : V i j ≠ 0)
    (heq : I.carrier = Submodule.span ℤ (Set.range (fun i => B.equivFun.symm (V i)))) :
    Nat.card (O ⧸ I) = (∏ i, V i i).natAbs := by
  refine ideal_norm_eq_prod B I ?_ V hd heq
  have : B.equivFun.symm (V i) ∈ I := by
    show B.equivFun.symm (V i) ∈ I.carrier
    rw [heq]
    apply Submodule.subset_span
    simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Set.mem_range, exists_apply_eq_apply]
  intro hc
  have := Ideal.mem_bot.1 (hc ▸ this)
  apply_fun B.equivFun at this
  simp only [LinearEquiv.apply_symm_apply, map_zero] at this
  apply_fun (fun f => f j) at this
  exact hij this


/-- If `K` is an algebra over a finite field `F` and has size `(#F) ^ n`, then it has
  rank `n` over `F`. -/
noncomputable def isAdjoinRoot_of_adjoin_root_irreducible_finite {F K : Type*} {n : ℕ}
  [AddCommGroup K] [Field F] [Fintype F] [DecidableEq F] [Module F K]
  (hr : Nat.card K = Fintype.card F ^ n) : Module.finrank F K = n := by
  haveI : Fintype K := by
    haveI := ((Nat.card_pos_iff (α := K)).1 ?_).2
    exact Fintype.ofFinite K
    rw [hr]
    refine pow_pos (Fintype.card_pos) _
  haveI : FiniteDimensional F K := Module.IsNoetherian.finite F K
  rw [Nat.card_eq_fintype_card, Module.card_fintype (M := K) (R := F) (Basis.ofVectorSpace F K),
    ← Module.finrank_eq_card_basis (Basis.ofVectorSpace F K) ] at hr
  apply_fun (fun x => Fintype.card F ^ x)
  dsimp
  exact hr
  refine Nat.pow_right_injective (Nat.succ_le_of_lt (Fintype.one_lt_card) )

/-- A `ZMod p` structure on `O ⧸ I` if `p ∈ I`. -/
@[reducible]
noncomputable def ZModP_algebra_of_mem {O : Type*} [CommRing O] (I : Ideal O)
  (p : ℕ) (hI : ↑p ∈ I) : Algebra (ZMod p) (O ⧸ I) := by
  refine ZMod.algebra' (O ⧸ I) (ringChar (O ⧸ I)) ?_
  erw [← ringChar.spec, Ideal.Quotient.eq_zero_iff_mem]
  exact hI

attribute [-instance]  Lean.Omega.IntList.instAdd

-- Note: we don't include computation tools as part of the parameters of the structure.

/-- This is the type of certified prime ideals above a prime number `p`. The structure bundles an
  ideal `I` with a certifificate of its primality. Even more, it proves that the residue field is
  given by adjoining a root of a polynomial `f`.

  It includes a multiplication table as data and, amongst its fields:
  * `r` : rank of `O`.
  * `n` : inertia degree / dimension of the residue field as an `F_p`-algebra.
  * `f` : polynomial such that `O⧸I` is isomorphic to `F_p[X]/(f)`.
  * `a` : represents the lift of the root of `f` in `O⧸I`.
  * `c` : represents the element `f(a)`, which lives in `I`. -/

structure CertifiedPrimeIdeal (O : Type*) (p : ℕ)  [CommRing O]  where
  r : ℕ
  n : ℕ
  hpos : 0 < n
  /-- A times table table for `O`. -/
  TT  : TimesTable (Fin r) ℤ O
  /-- The multiplication table written in terms of lists. This performs better.  -/
  T : Fin r → Fin r → List ℤ
  heq : ∀ i j , T i j = List.ofFn (TT.table i j)
  I : Ideal O
  hcard : Nat.card (O ⧸ I) = p ^ n
  /-- List representing a polynomial-/
  P : List ℤ
  /-- A polynomial over `ZMod p`. Redundant field but useful if `f` is not defeq to `ofList P`. -/
  f : Polynomial (ZMod p)
  hfeq : f = ofList (List.map (algebraMap ℤ (ZMod p)) P)
  hirr : Irreducible f
  hneq : (List.map (algebraMap ℤ (ZMod p)) P).getLastD 0 ≠ 0
  hlen : P.length = n + 1
  /-- Coordinates of the lift of an element in `O/I` which is a zero of `f`. -/
  a : Fin r → ℤ
  /-- Coordinates of `f a` in `O`. -/
  c : Fin r → ℤ
  hcmem : TT.basis.equivFun.symm c ∈ I
  /-- Coordinates of the element `1` in `O` (typically ![1,0,....,0]). -/
  z : Fin r → ℤ
  hBz : TT.basis.equivFun.symm z = 1
  hpmem : TT.basis.equivFun.symm ((p : ℤ) • z) ∈ I
  hpol : List.ofFn c = List.sum
      (List.ofFn (fun (i : Fin (n + 1)) => if i = 0 then List.mulPointwise
      (P[i]' (by rw [hlen]; exact i.isLt)) (List.ofFn z)
      else List.mulPointwise (P[i]' (by rw [hlen] ; exact i.isLt ))
      (nPow_sq_table T (List.ofFn a) i) ))

lemma CertifiedPrimeIdeal.polynomial_degree  {O : Type*} {p : ℕ} [CommRing O]
    (I : CertifiedPrimeIdeal O p) : I.f.natDegree = I.n := by
  have hPlen : I.P.length = (ofList (List.map (algebraMap ℤ (ZMod p)) I.P)).natDegree + 1 := by
    rw [natDegree_ofList]
    exact Eq.symm (List.length_map ⇑(algebraMap ℤ (ZMod p)))
    have := I.hneq
    by_contra hc
    erw [hc, List.getLastD_nil] at this
    exact this rfl
    refine eq_dropTrailingZeros_of_getLastD_ne_zero _ (I.hneq)
  rw [I.hfeq, ← Nat.succ_inj, Nat.succ_eq_add_one,  ← hPlen]
  exact I.hlen

@[reducible]
def CertifiedPrimeIdeal.residue_field_finite_dimensional {O : Type*} {p : ℕ}[Fact $ Nat.Prime p] [CommRing O]
  (I : CertifiedPrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] : FiniteDimensional (ZMod p) (O ⧸ I.I) := by
  have hcardaux :  Nat.card (O ⧸ I.I) = Fintype.card (ZMod p) ^ I.n := by
    rw [I.hcard]
    simp only [ZMod.card]
  refine FiniteDimensional.of_finrank_pos ?_
  rw [isAdjoinRoot_of_adjoin_root_irreducible_finite  hcardaux]
  exact I.hpos

lemma CertifiedPrimeIdeal.residue_field_dimension {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : CertifiedPrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] :
    Module.finrank (ZMod p) (O ⧸ I.I) = I.f.natDegree := by
  have hcardaux :  Nat.card (O ⧸ I.I) = Fintype.card (ZMod p) ^ I.n := by
    rw [I.hcard]
    simp only [ZMod.card]
  rw [CertifiedPrimeIdeal.polynomial_degree ]
  exact isAdjoinRoot_of_adjoin_root_irreducible_finite  hcardaux

lemma CertifiedPrimeIdeal.quotient_int_smul {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : CertifiedPrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] (m : ℤ) (x : O) :
    Ideal.Quotient.mk I.I (m • x) = (m : ZMod p) • Ideal.Quotient.mk I.I x := by
  simp only [zsmul_eq_mul, map_mul, map_intCast]
  rw [Algebra.smul_def]
  simp only [map_intCast]

lemma CertifiedPrimeIdeal.polynomial_aeval {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
  (I : CertifiedPrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] :
  (aeval ((Ideal.Quotient.mk I.I) (I.TT.basis.equivFun.symm I.a))) I.f = 0 := by
  have hPlen : I.P.length = (ofList (List.map (algebraMap ℤ (ZMod p)) I.P)).natDegree + 1 := by
      rw [← I.hfeq, CertifiedPrimeIdeal.polynomial_degree]
      exact I.hlen
  haveI : NeZero I.P.length := by
    rw [hPlen]
    exact Nat.instNeZeroSucc
  have aux : ∀ x , I.f.coeff x • ((Ideal.Quotient.mk I.I) (I.TT.basis.equivFun.symm I.a ^ x))
    = (Ideal.Quotient.mk I.I) ((I.P.getD x 0) • (I.TT.basis.equivFun.symm I.a ^ x)) := by
    intro x
    rw [CertifiedPrimeIdeal.quotient_int_smul]
    have : ∀ x, ((I.P.getD x 0) : ZMod p) = I.f.coeff x := by
      rw [I.hfeq]
      intro j
      simp only [ algebraMap_int_eq, Int.coe_castRingHom, coeff_ofList]
      have auxz : Int.castRingHom (ZMod p) (0 : ℤ) = 0 :=
        RingHom.map_zero (Int.castRingHom (ZMod p))
      erw [← auxz, List.getD_map I.P 0 (n := j) (Int.castRingHom (ZMod p))]
      rfl
    rw [this x]
  simp_rw [Polynomial.aeval_eq_sum_range, ← map_pow, aux, ← map_sum,
    Ideal.Quotient.eq_zero_iff_mem, I.hfeq]
  have hceq := table_polynomial_eval I.TT.table
    I.T I.TT.basis I.P I.z I.hBz I.a I.c I.TT.basis_mul_basis I.heq ?_
  convert I.hcmem
  rw [hceq, ← hPlen, Finset.sum_range]
  congr ; ext i
  congr
  simp only [List.getD_eq_getElem?_getD, Fin.is_lt, List.getElem?_eq_getElem, Option.getD_some,
    Fin.getElem_fin]
  rw [List.ofFn_congr I.hlen, I.hpol]
  congr
  refine funext ?_
  intro i
  simp only [Fin.getElem_fin, Fin.cast_eq_zero, Fin.val_cast]

noncomputable def isAdjoinRoot_quot_ofCertifiedPrimeIdeal {O : Type*} {p : ℕ}
    [Fact $ Nat.Prime p] [CommRing O] (I : CertifiedPrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] :
    IsAdjoinRoot (O ⧸ I.I) (I.f) := by
    haveI := CertifiedPrimeIdeal.residue_field_finite_dimensional I
    refine IsAdjoinRoot_of_adjoin_root_irreducible I.f I.hirr ?_ ?_
    use Ideal.Quotient.mk I.I (I.TT.basis.equivFun.symm I.a)
    · exact CertifiedPrimeIdeal.polynomial_aeval I
    · exact CertifiedPrimeIdeal.residue_field_dimension I

noncomputable def CertifiedPrimeIdeal.residue_field_is_field {O : Type*} {p : ℕ}
    [Fact $ Nat.Prime p] [CommRing O] (I : CertifiedPrimeIdeal O p) : IsField (O ⧸ I.I) := by
  have hpmem : ↑p ∈ I.I := by
    have := I.hpmem
    rw [LinearEquiv.map_smul, I.hBz] at this
    simp only [zsmul_eq_mul, Int.cast_natCast, mul_one] at this
    exact this
  haveI := ZModP_algebra_of_mem I.I p hpmem
  haveI := CertifiedPrimeIdeal.residue_field_finite_dimensional I
  refine field_of_adjoin_root_irreducible (K := O ⧸ I.I) I.f I.hirr ?_ ?_
  · use ((Ideal.Quotient.mk I.I) (I.TT.basis.equivFun.symm I.a))
    exact CertifiedPrimeIdeal.polynomial_aeval I
  · exact CertifiedPrimeIdeal.residue_field_dimension I

/-- The underlying ideal of `I : CertifiedPrimeIdeal p O` is a prime ideal. -/
lemma CertifiedPrimeIdeal.isPrime {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : CertifiedPrimeIdeal O p) : Ideal.IsPrime I.I := by
    refine Ideal.IsMaximal.isPrime ?_
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact CertifiedPrimeIdeal.residue_field_is_field I


/- A purely computational version of `CertifiedPrimeIdeal` -/
structure CertifiedPrimeIdeal' {r m : ℕ} [NeZero r] {T : Fin r → Fin r → List ℤ}
  {v : Fin m → Fin r → ℤ} {w : Fin r → Fin r → ℤ} (A : IdealEqSpanCertificate' T v w) (p : ℕ) where
  n : ℕ
  hpos : 0 < n
  hd : ∀ i j, i < j → w i j = 0
  i : Fin r := 0
  j : Fin r := 0
  hij : w i j ≠ 0 -- One of the entries of the ℤ-generators is non-zero.
  hcard : (∏ i, w i i).natAbs = p ^ n
  /-- List representing a polynomial-/
  P : List ℤ
  {u : ℕ}
  hu : NeZero u := by infer_instance
  {t : ℕ}
  {s : ℕ}
  hirr : CertificateIrreducibleZModOfList' p u t s (List.map (algebraMap ℤ (ZMod p)) P)
  hneq : (List.map (algebraMap ℤ (ZMod p)) P).getLastD 0 ≠ 0
  hlen : P.length = n + 1
  /-- Coordinates of the lift of an element in `O/I` which is a zero of `f`. -/
  a : Fin r → ℤ
  /-- Coordinates of `f a` in `O`. -/
  c : Fin r → ℤ
  g : Fin r → ℤ
  hcmem : List.ofFn c = List.sum (List.ofFn (fun k => List.mulPointwise (g k) (List.ofFn (w k))))
  /-- Coordinates of the element `1` in `O` (typically ![1,0,....,0]). -/
  z : Fin r → ℤ
  hpmem : (p : ℤ) • z = w 0 -- The first element in the provided `ℤ`-basis needs to be `p`.
  hpol : List.ofFn c = List.sum
      (List.ofFn (fun (i : Fin (n + 1)) => if i = 0 then List.mulPointwise
      (P[i]' (by rw [hlen]; exact i.isLt)) (List.ofFn z)
      else List.mulPointwise (P[i]' (by rw [hlen] ; exact i.isLt ))
      (nPow_sq_table T (List.ofFn a) i) ))


/-- Correctness of `CertifiedPrimeIdeal` . -/
lemma CertifiedPrimeIdeal'.idealNorm {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O] [IsDomain O]
  {r m : ℕ} [NeZero r] {TT  : TimesTable (Fin r) ℤ O}
  {T : Fin r → Fin r → List ℤ}
  (heq : ∀ i j , T i j = List.ofFn (TT.table i j))
  {v : Fin m → Fin r → ℤ} {w : Fin r → Fin r → ℤ} {A : IdealEqSpanCertificate' T v w}
  (C : CertifiedPrimeIdeal' A p)  :
    Nat.card (O ⧸ Ideal.span (Set.range (fun j => TT.basis.equivFun.symm (v j)))) = p ^ C.n  := by
  convert ideal_norm_eq_prod' TT.basis _ _ (C.hd) C.i C.j (C.hij) ?_
  rw [C.hcard]
  exact ideal_eq_of_IdealEqSpanCertificate' heq rfl A


/-- Correctness of `CertifiedPrimeIdeal` . -/
lemma CertifiedPrimeIdeal'.isPrime {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O] [IsDomain O]
  {r m : ℕ} [NeZero r] {TT  : TimesTable (Fin r) ℤ O}
  {T : Fin r → Fin r → List ℤ} (heq : ∀ i j , T i j = List.ofFn (TT.table i j))
  {v : Fin m → Fin r → ℤ} {w : Fin r → Fin r → ℤ}
  {I : Ideal O} (hieq : I = Ideal.span (Set.range (fun j => TT.basis.equivFun.symm (v j))))
  {A : IdealEqSpanCertificate' T v w} (C : CertifiedPrimeIdeal' A p)
  (hBz : TT.basis.equivFun.symm C.z = 1) :  Ideal.IsPrime I := by
  have : NeZero C.u := C.hu
  let CC : CertifiedPrimeIdeal O p :=
    { r := r , n := C.n, hpos := C.hpos, TT := TT
      T := T, heq := heq
      I := I, hcard := hieq ▸ CertifiedPrimeIdeal'.idealNorm heq C
      P := C.P, f := ofList (List.map (algebraMap ℤ (ZMod p)) C.P)
      hfeq := rfl, hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' C.hirr
      hneq := C.hneq, hlen := C.hlen, a := C.a, c := C.c
      hcmem := by
        refine mem_of_certificate TT.basis I w C.c ?_
        exact { hieq := ideal_eq_of_IdealEqSpanCertificate' heq hieq A
                g := C.g
                hmem := C.hcmem }
      z := C.z, hBz := hBz
      hpmem := by
        erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate' heq hieq A]
        apply Submodule.subset_span
        use 0 ; dsimp ; congr ; exact C.hpmem.symm
      hpol := C.hpol }
  exact CertifiedPrimeIdeal.isPrime CC


/-- The quotient by an ideal of norm equal to a prime `p` is isomorphic to `ZMod p`.  -/
noncomputable def modIdealEquivZMod {O : Type*} {p : ℕ} (hp : Nat.Prime p)
  [CommRing O] (I : Ideal O) (hcard : Nat.card (O ⧸ I) = p) : O ⧸ I ≃+* (ZMod p) := by
  haveI : Finite (O ⧸ I) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact Nat.Prime.ne_zero hp
  haveI : Fintype (O ⧸ I) := Fintype.ofFinite _
  exact (ZMod.ringEquivOfPrime _ hp (Eq.trans (Fintype.card_eq_nat_card ) hcard)).symm

/-- The map to `ZMod p` from the quotient by an ideal of norm equal to a prime `p`.  -/
noncomputable def modIdealToZMod {O : Type*} {p : ℕ} (hp : Nat.Prime p) [CommRing O] (I : Ideal O)
  (hcard : Nat.card (O ⧸ I) = p) : O ⧸ I →+* (ZMod p) := by
  haveI : Finite (O ⧸ I) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact Nat.Prime.ne_zero hp
  haveI : Fintype (O ⧸ I) := Fintype.ofFinite _
  exact (id (ZMod.ringEquivOfPrime _ hp
    (Eq.trans (Fintype.card_eq_nat_card ) hcard)).symm).toRingHom

/-- An ideal of norm a prime number is a prime ideal. -/
lemma prime_ideal_of_norm_prime {O : Type*} {p : ℕ} (hp : Nat.Prime p) [CommRing O] (I : Ideal O)
  (hcard : Nat.card (O ⧸ I) = p) : Ideal.IsPrime I := by
  haveI : Fact $ Nat.Prime p := {out := hp}
  refine Ideal.IsMaximal.isPrime ?_
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField (Field.toIsField (ZMod p)) (modIdealEquivZMod hp I hcard)




-- I substituted the q in dedekind criterion with algebra instance, so we can use the isScalarTower
/- A more general version of isAdjoinRoot_of_adjoin_root_irreducible_finite using the PID index.
noncomputable def quotient_finrank_of_index {O R F : Type*} {n : ℕ} [CommRing O] [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] [IsDomain O] [Algebra R O] [Field F]
    (π : R) (hp : Prime π) [Algebra R F] (hqs : Function.Surjective (algebraMap R F))
    (hqker : RingHom.ker (algebraMap R F) = Ideal.span {π} )
    [Module.Free R O] [Module.Finite R O] (I : Ideal O) (hnb : I ≠ ⊥) [hI : Module F (O ⧸ I)]
    [hS : IsScalarTower R F (O ⧸ I)]
    (hr : Associated (Submodule.indexPID (I.restrictScalars R)) (π ^ n)) :
    Module.finrank F (O ⧸ I) = n := by
    haveI : Module F (O ⧸ (I.restrictScalars R)) := hI
    haveI : IsScalarTower R F (O ⧸ (I.restrictScalars R)) := sorry
    let B' := Module.Free.chooseBasis R O
    let b' := Ideal.selfBasis B' I hnb
    let B := Basis.reindex B' (Fintype.equivFin _)
    let b := Basis.reindex b' (Fintype.equivFin _)
    let e := moduleQuotientEquivPiSpan' (I.restrictScalars R) B b
    have hpi := Associated.trans (prod_moduleSmithCoeffs_associated_index (I.restrictScalars R) B b).symm hr
    let C := moduleSmithCoeffs (I.restrictScalars R) B b
    have hs : ∀ i, IsUnit (C i) ∨ Associated (C i) π := by
      intro i
      have hdvd : C i ∣ π ^ n := by
        refine dvd_trans (Finset.dvd_prod_of_mem C (Finset.mem_univ i)) (hpi.dvd)
      obtain ⟨m, hml, hma⟩ := (dvd_prime_pow hp n).1 hdvd
      by_cases hz : m = 0
      · rw [hz] at hma
        simp only [pow_zero, associated_one_iff_isUnit] at hma
        left
        exact hma
      · by_cases ho : m = 1
        · rw [ho, pow_one] at hma
          right
          exact hma
        · exfalso
          have hpi1 : π • e.symm (fun j => if j = i then 1 else 0) ≠ 0 := by
            by_contra hc
            rw [← map_smul, (injective_iff_map_eq_zero' _).1 (LinearEquiv.injective e.symm)] at hc
            have aux := congr_fun hc i
            simp only [Pi.smul_apply, ↓reduceIte, Pi.zero_apply] at aux
            erw [Submodule.Quotient.mk_eq_zero] at aux
            simp only [smul_eq_mul, mul_one] at aux
            rw  [Ideal.span_singleton_eq_span_singleton.2 hma, Ideal.mem_span_singleton] at aux
            sorry
          apply hpi1
          have heq : (1 : F) • e.symm (fun j => if j = i then 1 else 0) = e.symm (fun j => if j = i then 1 else 0) :=
            MulAction.one_smul _
          rw [← heq, ← IsScalarTower.smul_assoc π (1 : F) _]
          have hsz : π • (1 : F) = 0 := by
            rw [Algebra.smul_def, mul_one, ← RingHom.mem_ker, hqker]
            exact Ideal.mem_span_singleton_self π
          rw [hsz, zero_smul]
    --let pb : Fin n → Fin (Fintype.card (Module.Free.ChooseBasisIndex R O)) := by
    let G := { i | ¬ IsUnit (C i) }
    haveI : Fintype G := Fintype.ofFinite ↑G
    let B := { i | IsUnit (C i) }
    haveI : Fintype B := Fintype.ofFinite ↑B
    have hcard : Fintype.card G = n := by sorry
    let equivG := Equiv.trans (finCongr hcard.symm) (Fintype.equivFin G).symm
    let f := fun (i : Fin n) => (equivG i).val
    have fI : Function.Injective f := by sorry
    let tF : ∀ i , R ⧸ Ideal.span {C (f i)} ≃+* F := by sorry
    --let i : Fin n := by sorry
    let Ba : (O ⧸ I) ≃ₗ[F] Fin n →₀ F :=
     {toFun := fun x => (Finsupp.ofSupportFinite (fun i => (tF i) ((e x) (f i))) (Set.toFinite _) )
      map_smul' := sorry
      invFun := fun c => ∑ i, (c i) • e.symm (fun j => if j = f i then 1 else 0 )
      left_inv := by
        intro x
        simp [Finsupp.ofSupportFinite]
        sorry
      right_inv := by
        intro v
        simp
        ext x
        simp [Finsupp.ofSupportFinite]
        sorry
      map_add' := sorry }
    convert Module.finrank_eq_card_basis ({repr := Ba})
    simp only [Fintype.card_fin] -/
