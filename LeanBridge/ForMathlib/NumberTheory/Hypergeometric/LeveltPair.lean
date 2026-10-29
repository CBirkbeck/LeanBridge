import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.AdjoinRoot

/-!
# Companion matrices and Levelt's theorem

The companion matrix of a monic polynomial `f = X^n + c_{n-1} X^{n-1} + ⋯ + c_0` of degree `n` is
the matrix of multiplication by `X` on `R[X] / (f)` in the basis `1, X, …, X^{n-1}`: it has `1`s
just below the diagonal, last column `(-c_0, …, -c_{n-1})` and zeros elsewhere, and its
characteristic polynomial is `f`.

Levelt's theorem describes the monodromy of the hypergeometric differential equation. Let `f` and
`g` be coprime monic polynomials of degree `n` over a field `K`. A Levelt pair is a pair `(A, B)` of
`n × n` matrices with characteristic polynomials `f` and `g` such that `A - B` has rank at most one.
The companion matrices of `f` and `g` form a Levelt pair, as they differ only in their last columns,
and every Levelt pair is simultaneously conjugate to it: there is a vector `v` with
`A^j v = B^j v` for `j < n`, and in the basis `v, A v, …, A^{n-1} v` the matrices `A` and `B` are
the companion matrices of `f` and `g`. In the notation of Beukers and Heckman, `A = h_∞` and
`B = h_0⁻¹`, where `h_∞` and `h_0` are the local monodromies at `∞` and `0` of a hypergeometric
group, and the rank condition says that the local monodromy `h_1 = A⁻¹ B` at `1` is a
pseudo-reflection.

## Main definitions

* `Polynomial.companionMatrix`: the companion matrix of a polynomial.
* `Matrix.IsLeveltPair`: a pair of matrices with characteristic polynomials `f` and `g` that differ
  by a matrix of rank at most one.

## Main results

* `Polynomial.companionMatrix_eq_leftMulMatrix`: the companion matrix of a monic polynomial `f` is
  the matrix of multiplication by `X` on `R[X] / (f)`.
* `Polynomial.charpoly_companionMatrix`: the characteristic polynomial of the companion matrix of a
  monic polynomial `f` is `f`.
* `Matrix.isLeveltPair_companionMatrix`: the companion matrices of monic `f` and `g` of degree `n`
  form a Levelt pair.
* `Matrix.IsLeveltPair.exists_conj_companionMatrix`: **Levelt's theorem**, a Levelt pair with
  coprime `f` and `g` is simultaneously conjugate to the pair of companion matrices of `f` and `g`.
* `Matrix.IsLeveltPair.exists_conj`: two Levelt pairs with the same coprime `f` and `g` are
  simultaneously conjugate.

## References

* A. H. M. Levelt, *Hypergeometric functions*, thesis, University of Amsterdam, 1961.
* F. Beukers and G. Heckman, *Monodromy for the hypergeometric function `nFn-1`*, Invent. Math. 95
  (1989), 325–354, Theorem 3.5.
-/

open Polynomial Module

namespace Polynomial

variable {R : Type*} [CommRing R] (f g : R[X]) (n : ℕ)

/-- The **companion matrix** of a polynomial `f = X^n + c_{n-1} X^{n-1} + ⋯ + c_0` of degree `n`:
the matrix of multiplication by `X` on `R[X] / (f)` in the basis `1, X, …, X^{n-1}`
(`Polynomial.companionMatrix_eq_leftMulMatrix`), whose entry `(i, j)` is `-c_i` in the last column
`j = n - 1`, `1` just below the diagonal, for `i = j + 1`, and `0` elsewhere. It is meant for monic
`f` of degree `n`, when its characteristic polynomial is `f`
(`Polynomial.charpoly_companionMatrix`). -/
def companionMatrix : Matrix (Fin n) (Fin n) R :=
  .of fun i j ↦ if (j : ℕ) + 1 = n then -f.coeff i else if (i : ℕ) = j + 1 then 1 else 0

lemma companionMatrix_apply (i j : Fin n) : f.companionMatrix n i j =
    if (j : ℕ) + 1 = n then -f.coeff i else if (i : ℕ) = j + 1 then 1 else 0 :=
  rfl

lemma companionMatrix_map {S : Type*} [CommRing S] (φ : R →+* S) :
    (f.companionMatrix n).map φ = (f.map φ).companionMatrix n := by
  ext i j
  simp only [Matrix.map_apply, companionMatrix_apply]
  split_ifs <;> simp

lemma minpolyGen_powerBasis' (hf : f.Monic) : (AdjoinRoot.powerBasis' hf).minpolyGen = f := by
  nontriviality R
  have hdeg : (X ^ f.natDegree : R[X]).degree = f.degree := by
    rw [degree_X_pow, degree_eq_natDegree hf.ne_zero]
  have hX : X ^ f.natDegree %ₘ f = X ^ f.natDegree - f := by
    rw [modByMonic_eq_of_dvd_sub hf (p₂ := X ^ f.natDegree - f) ⟨1, by ring1⟩,
      (modByMonic_eq_self_iff hf).mpr]
    exact hdeg ▸ degree_sub_lt_left hdeg (monic_X_pow _).ne_zero
      (by rw [leadingCoeff_X_pow, hf.leadingCoeff])
  have hrepr (i : Fin (AdjoinRoot.powerBasis' hf).dim) : (AdjoinRoot.powerBasis' hf).basis.repr
      ((AdjoinRoot.powerBasis' hf).gen ^ (AdjoinRoot.powerBasis' hf).dim) i = -f.coeff i := by
    have h : (AdjoinRoot.powerBasis' hf).basis.repr
        ((AdjoinRoot.powerBasis' hf).gen ^ (AdjoinRoot.powerBasis' hf).dim) i =
          (X ^ f.natDegree %ₘ f).coeff i := by
      rw [AdjoinRoot.powerBasis'_gen, ← AdjoinRoot.mk_X, ← map_pow]
      rfl
    have hi : (i : ℕ) ≠ f.natDegree := i.is_lt.ne
    rw [h, hX, coeff_sub, coeff_X_pow, ite_eq_right hi, zero_sub]
  rw [PowerBasis.minpolyGen]
  simp only [hrepr, map_neg, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  refine (hf.as_sum.trans ?_).symm
  rw [Finset.sum_range]
  rfl

/-- **The companion matrix is the matrix of multiplication by `X`** on `R[X] / (f)` in the basis
`1, X, …, X^{n-1}`, for monic `f` of degree `n`. -/
lemma companionMatrix_eq_leftMulMatrix (hf : f.Monic) : f.companionMatrix f.natDegree =
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis (AdjoinRoot.root f) := by
  rw [← AdjoinRoot.powerBasis'_gen hf, PowerBasis.leftMulMatrix, minpolyGen_powerBasis']
  rfl

/-- **The characteristic polynomial of the companion matrix** of a monic polynomial `f` of degree
`n` is `f`. -/
lemma charpoly_companionMatrix (hf : f.Monic) (hn : f.natDegree = n) :
    (f.companionMatrix n).charpoly = f := by
  subst hn
  have h : (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
      (AdjoinRoot.powerBasis' hf).gen).charpoly = minpoly R (AdjoinRoot.powerBasis' hf).gen :=
    charpoly_leftMulMatrix _
  rw [PowerBasis.leftMulMatrix, ← PowerBasis.minpolyGen_eq, minpolyGen_powerBasis'] at h
  exact h

lemma companionMatrix_sub_companionMatrix : f.companionMatrix n - g.companionMatrix n =
    Matrix.vecMulVec (fun i : Fin n ↦ g.coeff i - f.coeff i) fun j : Fin n ↦
      if (j : ℕ) + 1 = n then 1 else 0 := by
  ext i j
  simp only [Matrix.sub_apply, companionMatrix_apply, Matrix.vecMulVec_apply]
  split_ifs <;> ring1

variable [Nontrivial R] in
lemma rank_companionMatrix_sub_le_one : (f.companionMatrix n - g.companionMatrix n).rank ≤ 1 := by
  rw [companionMatrix_sub_companionMatrix]
  exact Matrix.rank_vecMulVec_le _ _

end Polynomial

namespace Matrix

variable {K : Type*} [Field K] {n : ℕ} {f g : K[X]} {A B M N : Matrix (Fin n) (Fin n) K}
  (v : Fin n → K) {P Q : GL (Fin n) K}

variable (f g A B) in
/-- A **Levelt pair** (used for LMFDB `hgm.levelt_matrices`) with characteristic polynomials `f`
and `g`: two `n × n` matrices `A` and `B` over a field with characteristic polynomials `f` and `g`
such that `A - B` has rank at most one. For coprime `f` and `g` such a pair exists and is unique up
to simultaneous conjugation (`Matrix.isLeveltPair_companionMatrix`,
`Matrix.IsLeveltPair.exists_conj`); for `n ≥ 1` the rank of `A - B` is then one. In the notation of
Beukers and Heckman, `A = h_∞` and `B = h_0⁻¹` for the local monodromies `h_∞` and `h_0` at `∞` and
`0` of a hypergeometric group, whose local monodromy `h_1 = A⁻¹ B` at `1` is then a
pseudo-reflection. -/
structure IsLeveltPair : Prop where
  /-- The characteristic polynomial of `A` is `f`. -/
  charpoly_left : A.charpoly = f
  /-- The characteristic polynomial of `B` is `g`. -/
  charpoly_right : B.charpoly = g
  /-- The matrices `A` and `B` differ by a matrix of rank at most one. -/
  rank_sub_le_one : (A - B).rank ≤ 1

/-- **The companion matrices form a Levelt pair**: the companion matrices of monic polynomials `f`
and `g` of degree `n` have characteristic polynomials `f` and `g` and differ only in their last
columns. -/
lemma isLeveltPair_companionMatrix (hf : f.Monic) (hg : g.Monic) (hfn : f.natDegree = n)
    (hgn : g.natDegree = n) : IsLeveltPair f g (f.companionMatrix n) (g.companionMatrix n) :=
  ⟨f.charpoly_companionMatrix n hf hfn, g.charpoly_companionMatrix n hg hgn,
    f.rank_companionMatrix_sub_le_one g n⟩

lemma pow_card_mulVec : (A ^ n) *ᵥ v = -∑ k : Fin n, A.charpoly.coeff k • ((A ^ (k : ℕ)) *ᵥ v) := by
  have hc : A.charpoly.coeff n = 1 := by
    simpa using A.charpoly_monic.coeff_natDegree
  have h : aeval A A.charpoly = 0 := A.aeval_self_charpoly
  rw [aeval_eq_sum_range, A.charpoly_natDegree_eq_dim, Fintype.card_fin, Finset.sum_range_succ,
    hc, one_smul] at h
  rw [eq_neg_of_add_eq_zero_right h, neg_mulVec, sum_mulVec, Finset.sum_range]
  simp only [smul_mulVec]

lemma mul_of_mul_companionMatrix (h : ∀ j < n, (B ^ j) *ᵥ v = (A ^ j) *ᵥ v) :
    B * of (fun i j : Fin n ↦ ((A ^ (j : ℕ)) *ᵥ v) i) =
      of (fun i j : Fin n ↦ ((A ^ (j : ℕ)) *ᵥ v) i) * B.charpoly.companionMatrix n := by
  ext i j
  have hl :
      (B * of fun i j : Fin n ↦ ((A ^ (j : ℕ)) *ᵥ v) i) i j = ((B ^ ((j : ℕ) + 1)) *ᵥ v) i := by
    rw [pow_succ', ← mulVec_mulVec, h j j.is_lt]
    rfl
  rw [hl, mul_apply]
  simp only [Polynomial.companionMatrix_apply]
  split_ifs with hj
  · rw [hj, pow_card_mulVec]
    simp [h, mul_comm]
  · rw [Fintype.sum_eq_single ⟨(j : ℕ) + 1, by omega⟩ fun k hk ↦ by
      rw [ite_eq_right fun hkj ↦ hk <| Fin.ext hkj, mul_zero]]
    simp [h ((j : ℕ) + 1) (by omega)]

lemma exists_ne_zero_forall_sub_mulVec_pow_mulVec (hn : n ≠ 0) (hr : (A - B).rank ≤ 1) :
    ∃ v : Fin n → K, v ≠ 0 ∧ ∀ j, j + 1 < n → (A - B) *ᵥ ((A ^ j) *ᵥ v) = 0 := by
  let Φ : (Fin n → K) →ₗ[K] Fin (n - 1) → LinearMap.range (A - B).mulVecLin :=
    LinearMap.pi fun j ↦ (A - B).mulVecLin.rangeRestrict ∘ₗ (A ^ (j : ℕ)).mulVecLin
  have hΦ : LinearMap.ker Φ ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    rw [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      finrank_fin_fun]
    exact (Nat.mul_le_mul_left (n - 1) hr).trans_lt <| by omega
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hΦ with ⟨v, hv, hv0⟩
  exact ⟨v, hv0, fun j hj ↦
    congrArg Subtype.val <| congrFun (LinearMap.mem_ker.mp hv) ⟨j, by omega⟩⟩

variable {v} in
lemma linearIndependent_pow_mulVec (hAB : IsCoprime A.charpoly B.charpoly) (hv : v ≠ 0)
    (hpow : ∀ j < n, (A ^ j) *ᵥ v = (B ^ j) *ᵥ v) :
    LinearIndependent K fun j : Fin n ↦ (A ^ (j : ℕ)) *ᵥ v := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact linearIndependent_empty_type
  have haeval (q : K[X]) (hq : q.natDegree < n) : aeval A q *ᵥ v = aeval B q *ᵥ v := by
    rw [aeval_eq_sum_range, aeval_eq_sum_range, sum_mulVec, sum_mulVec]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [smul_mulVec, smul_mulVec, hpow i ((Finset.mem_range.mp hi).trans_le hq)]
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let p : K[X] := ∑ j : Fin n, c j • X ^ (j : ℕ)
  have hpn : p.natDegree < n := by
    refine (natDegree_sum_le_of_forall_le _ _ (n := n - 1) fun j _ ↦ ?_).trans_lt (by omega)
    exact (natDegree_smul_le _ _).trans <| (natDegree_X_pow_le _).trans <| by omega
  have hpA : aeval A p *ᵥ v = 0 := by
    simpa [p, sum_mulVec, smul_mulVec] using hc
  have hmul (Z : Matrix (Fin n) (Fin n) K) (hZ : aeval Z p *ᵥ v = 0) :
      aeval Z (p * (B.charpoly / p)) *ᵥ v = 0 := by
    rw [mul_comm, map_mul, ← mulVec_mulVec, hZ, mulVec_zero]
  have hp : p = 0 := by
    by_contra hp0
    have hdiv : B.charpoly % p + p * (B.charpoly / p) = B.charpoly :=
      EuclideanDomain.mod_add_div B.charpoly p
    have hr : (B.charpoly % p).natDegree < n := by
      rcases eq_or_ne (B.charpoly % p) 0 with h0 | h0
      · rw [h0, natDegree_zero]
        omega
      · exact (natDegree_lt_natDegree h0 (degree_mod_lt _ hp0)).trans hpn
    have hrB : aeval B (B.charpoly % p) *ᵥ v = 0 := by
      have h : aeval B (B.charpoly % p + p * (B.charpoly / p)) *ᵥ v = aeval B B.charpoly *ᵥ v :=
        congrArg (fun q ↦ aeval B q *ᵥ v) hdiv
      rwa [map_add, add_mulVec, hmul B <| (haeval p hpn).symm.trans hpA, add_zero,
        aeval_self_charpoly, zero_mulVec] at h
    have hgA : aeval A B.charpoly *ᵥ v = 0 := by
      rw [← hdiv, map_add, add_mulVec, haeval _ hr, hrB, zero_add, hmul A hpA]
    rcases hAB with ⟨a, b, hab⟩
    have h : aeval A (a * A.charpoly + b * B.charpoly) *ᵥ v = aeval A 1 *ᵥ v :=
      congrArg (fun q ↦ aeval A q *ᵥ v) hab
    rw [map_add, map_mul, map_mul, aeval_self_charpoly, mul_zero, zero_add, map_one, one_mulVec,
      ← mulVec_mulVec, hgA, mulVec_zero] at h
    exact hv h.symm
  intro i
  simpa [p, Fin.val_inj] using congrArg (coeff · i) hp

lemma inv_mul_mul_eq_of_mul_eq (h : M * (P : Matrix (Fin n) (Fin n) K) = P * N) :
    (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * M * P = N := by
  rw [mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul]

lemma mul_eq_mul_of_inv_mul_mul_eq
    (h : (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * M * P = (↑Q⁻¹ : Matrix (Fin n) (Fin n) K) * N * Q) :
    M * (P * Q⁻¹ : GL (Fin n) K) = (P * Q⁻¹ : GL (Fin n) K) * N := by
  have h' : (P : Matrix (Fin n) (Fin n) K) * (P⁻¹ * M * P) * Q⁻¹ = P * (Q⁻¹ * N * Q) * Q⁻¹ :=
    congrArg (fun L ↦ (P : Matrix (Fin n) (Fin n) K) * L * (Q⁻¹ : GL (Fin n) K)) h
  simpa [mul_assoc] using h'

/-- **Levelt's theorem**: a Levelt pair `(A, B)` with coprime characteristic polynomials `f` and
`g` is simultaneously conjugate to the pair of companion matrices of `f` and `g`. -/
lemma IsLeveltPair.exists_conj_companionMatrix (h : IsLeveltPair f g A B) (hfg : IsCoprime f g) :
    ∃ P : GL (Fin n) K, (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * A * P = f.companionMatrix n ∧
      (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * B * P = g.companionMatrix n := by
  rcases h with ⟨rfl, rfl, hr⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  rcases exists_ne_zero_forall_sub_mulVec_pow_mulVec hn hr with ⟨v, hv0, hv⟩
  have hpow (j : ℕ) (hj : j < n) : (A ^ j) *ᵥ v = (B ^ j) *ᵥ v := by
    induction j with
    | zero => rw [pow_zero, pow_zero]
    | succ j ih =>
      rw [pow_succ', pow_succ', ← mulVec_mulVec, ← mulVec_mulVec, ← ih (by omega), ← sub_eq_zero,
        ← sub_mulVec]
      exact hv j hj
  have hP : IsUnit (of fun i j : Fin n ↦ ((A ^ (j : ℕ)) *ᵥ v) i) :=
    linearIndependent_col_iff_isUnit.mp <| linearIndependent_pow_mulVec hfg hv0 hpow
  exact ⟨hP.unit, inv_mul_mul_eq_of_mul_eq <| mul_of_mul_companionMatrix v fun _ _ ↦ rfl,
    inv_mul_mul_eq_of_mul_eq <| mul_of_mul_companionMatrix v fun j hj ↦ (hpow j hj).symm⟩

/-- **Levelt pairs are unique up to simultaneous conjugation**: two Levelt pairs `(A, B)` and
`(A', B')` with the same coprime characteristic polynomials `f` and `g` are simultaneously
conjugate. -/
lemma IsLeveltPair.exists_conj {A' B' : Matrix (Fin n) (Fin n) K} (h : IsLeveltPair f g A B)
    (h' : IsLeveltPair f g A' B') (hfg : IsCoprime f g) :
    ∃ P : GL (Fin n) K, (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * A * P = A' ∧
      (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * B * P = B' := by
  rcases h.exists_conj_companionMatrix hfg with ⟨P, hA, hB⟩
  rcases h'.exists_conj_companionMatrix hfg with ⟨Q, hA', hB'⟩
  exact ⟨P * Q⁻¹, inv_mul_mul_eq_of_mul_eq <| mul_eq_mul_of_inv_mul_mul_eq <| hA.trans hA'.symm,
    inv_mul_mul_eq_of_mul_eq <| mul_eq_mul_of_inv_mul_mul_eq <| hB.trans hB'.symm⟩

end Matrix
