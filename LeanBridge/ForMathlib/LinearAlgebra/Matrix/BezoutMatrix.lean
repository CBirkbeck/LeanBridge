import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The Bézout matrix of two polynomials

For polynomials `f` and `g` of degree at most `n` over a commutative ring, `f(x)g(y) − f(y)g(x)`
vanishes on the diagonal `x = y`, and the quotient `(f(x)g(y) − f(y)g(x))/(x − y)` has degree less
than `n` in each variable. Its `n × n` matrix of coefficients is the degree `n` Bézout matrix of `f`
and `g`. With `f = ∑ aₖ xᵏ` and `g = ∑ bₖ xᵏ`, its `(i, j)` entry is
`∑_{k ≤ min(i, j)} (a_{i+j+1-k} b_k - a_k b_{i+j+1-k})`.

The determinant of the Bézout matrix is the resultant, up to the sign `(-1)^(n(n-1)/2)` coming from
the order of the rows. Indeed, the Sylvester matrix of `f` and `g` consists of two lower and two
upper triangular Toeplitz blocks, the upper ones commute, so its determinant is that of
`L_g U_f - L_f U_g`, and the Bézout matrix is this matrix transposed with its rows reversed.

## Main definitions

* `Polynomial.bezoutCoeff f g i j`: the coefficient of `xⁱ yʲ` in `(f(x)g(y) − f(y)g(x))/(x − y)`.
* `Polynomial.bezoutMatrix f g n` (LMFDB `alg.bezout_matrix`): the degree `n` Bézout matrix.
* `Polynomial.sylvesterLow h n`, `Polynomial.sylvesterHigh h n`: the triangular Toeplitz blocks of
  the Sylvester matrix.

## Main results

* `Polynomial.sub_mul_sum_bezoutCoeff`, `Polynomial.sub_mul_sum_bezoutMatrix`: the defining identity
  `(x - y) ∑ c_ij xⁱ yʲ = f(x)g(y) − f(y)g(x)`, in every commutative algebra.
* `Polynomial.det_bezoutMatrix`: the determinant of the degree `n` Bézout matrix is
  `(-1)^(n(n-1)/2)` times the resultant `Polynomial.resultant f g n n`.
* `Matrix.det_fromBlocks_of_commute`: `det [[A, B], [C, D]] = det (A D - B C)` when `C` and `D`
  commute.
* `Fin.sign_revPerm`: the reversal of `Fin n` has sign `(-1)^(n(n-1)/2)`.
-/

open Equiv Finset Polynomial
open scoped Matrix

namespace Matrix

variable {m R : Type*} [Fintype m] [DecidableEq m] [CommRing R] (A B C D : Matrix m m R)
  (hCD : Commute C D)
include hCD

lemma det_fromBlocks_mul_det_of_commute :
    (fromBlocks A B C D).det * D.det = (A * D - B * C).det * D.det := by
  have h : fromBlocks A B C D * fromBlocks D 0 (-C) 1 = fromBlocks (A * D - B * C) B 0 D := by
    rw [fromBlocks_multiply, hCD.eq]
    simp [sub_eq_add_neg]
  rw [← det_fromBlocks_zero₂₁ _ B, ← h, det_mul, det_fromBlocks_zero₁₂, det_one, mul_one]

/-- **The determinant of a block matrix with commuting lower blocks**:
`det [[A, B], [C, D]] = det (A D - B C)` when `C` and `D` commute. It holds when `D` is invertible
by the Schur complement, hence in general by replacing `D` with `D + X` over `R[X]`, whose
determinant is monic. -/
lemma det_fromBlocks_of_commute : (fromBlocks A B C D).det = (A * D - B * C).det := by
  let c : Matrix m m R →+* Matrix m m R[X] := Polynomial.C.mapMatrix
  have hD : charmatrix (-D) = scalar m (X : R[X]) + c D := by
    rw [charmatrix, map_neg, sub_neg_eq_add]
  have hC : Commute (c C) (charmatrix (-D)) := by
    rw [hD]
    exact (scalar_commute _ (fun _ ↦ Commute.all _ _) _).symm.add_right (hCD.map c)
  have key : (fromBlocks (c A) (c B) (c C) (charmatrix (-D))).det =
      (c A * charmatrix (-D) - c B * c C).det :=
    (charpoly_monic (-D)).isRegular.right (det_fromBlocks_mul_det_of_commute _ _ _ _ hC)
  have e (M : Matrix m m R) : (evalRingHom 0).mapMatrix (c M) = M := by
    ext
    simp [c]
  have eD : (evalRingHom 0).mapMatrix (charmatrix (-D)) = D := by
    rw [hD, map_add, e]
    ext
    simp
  apply_fun evalRingHom 0 at key
  rwa [RingHom.map_det, RingHom.map_det, map_sub, map_mul, map_mul, e, e, e, eD,
    RingHom.mapMatrix_apply, fromBlocks_map, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, e, e, e, eD] at key

end Matrix

open Perm in
/-- **The reversal of `Fin n` has sign `(-1)^(n(n-1)/2)`**: up to a cycle of length `n + 1`, the
reversal of `Fin (n + 1)` is that of `Fin n` on the last `n` elements. -/
lemma Fin.sign_revPerm (n : ℕ) : sign (revPerm : Perm (Fin n)) = (-1) ^ n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : finRotate (n + 1) * revPerm = decomposeFin.symm (0, revPerm) := by
      ext x
      cases x using Fin.cases with
      | zero => simp
      | succ k => simp [rev_succ]
    have h' : sign (finRotate (n + 1) * revPerm) = sign (decomposeFin.symm (0, revPerm)) :=
      congrArg sign h
    rw [Perm.sign_mul, decomposeFin.symm_sign, ite_eq_left rfl, one_mul, ih, sign_finRotate,
      Nat.succ_sub_one] at h'
    rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add, ← h', ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

namespace Polynomial

variable {R : Type*} [CommRing R] (f g h : R[X]) (n i j : ℕ)

/-- The coefficient `c_ij` of `xⁱ yʲ` in the Bézoutian `(f(x)g(y) − f(y)g(x))/(x − y)` of two
polynomials `f = ∑ aₖ xᵏ` and `g = ∑ bₖ xᵏ`: `∑_{k ≤ min(i, j)} (a_{i+j+1-k} b_k - a_k b_{i+j+1-k})`
(`Polynomial.sub_mul_sum_bezoutCoeff`). It vanishes when `i` or `j` is at least an upper bound for
the degrees of `f` and `g`. -/
def bezoutCoeff : R :=
  ∑ k ∈ range (min i j + 1),
    (f.coeff (i + j + 1 - k) * g.coeff k - f.coeff k * g.coeff (i + j + 1 - k))

/-- The **degree `n` Bézout matrix** of two polynomials `f` and `g` of degree at most `n` (LMFDB
`alg.bezout_matrix`): the `n × n` matrix `(c_ij)` with
`(f(x)g(y) − f(y)g(x))/(x − y) = ∑_{0 ≤ i, j < n} c_ij xⁱ yʲ`
(`Polynomial.sub_mul_sum_bezoutMatrix`). The LMFDB knowl indexes the entries by `1 ≤ i, j ≤ n` and
writes `c_ij xⁱ yʲ`, an off-by-one slip for the exponents `i - 1` and `j - 1`: the quotient has
degree less than `n` in each variable. Its determinant is the resultant up to the sign
`(-1)^(n(n-1)/2)` (`Polynomial.det_bezoutMatrix`). -/
def bezoutMatrix : Matrix (Fin n) (Fin n) R :=
  .of fun i j ↦ bezoutCoeff f g i j

/-- The lower triangular Toeplitz block `(h_{i-j})_{j ≤ i}` of the Sylvester matrix. -/
def sylvesterLow : Matrix (Fin n) (Fin n) R :=
  .of fun i j ↦ if j ≤ i then h.coeff (i - j) else 0

/-- The upper triangular Toeplitz block `(h_{n+i-j})_{i ≤ j}` of the Sylvester matrix. -/
def sylvesterHigh : Matrix (Fin n) (Fin n) R :=
  .of fun i j ↦ if i ≤ j then h.coeff (n + i - j) else 0

lemma bezoutCoeff_comm : bezoutCoeff f g i j = bezoutCoeff f g j i := by
  rw [bezoutCoeff, bezoutCoeff, min_comm, add_comm i j]

lemma sum_Ico_bezout_eq_zero : ∑ q ∈ Ico (i + 1) (j + 1),
    (f.coeff (i + j + 1 - q) * g.coeff q - f.coeff q * g.coeff (i + j + 1 - q)) = 0 := by
  refine sum_involution (fun q _ ↦ i + j + 1 - q) (fun q hq ↦ ?_) (fun q hq h ↦ ?_)
    (fun q hq ↦ ?_) (fun q hq ↦ ?_)
  · have hq' : i + 1 ≤ q ∧ q < j + 1 := mem_Ico.mp hq
    rw [show i + j + 1 - (i + j + 1 - q) = q by omega]
    ring1
  · intro hq'
    apply h
    rw [hq']
    ring1
  · rw [mem_Ico] at hq ⊢
    omega
  · have hq' : i + 1 ≤ q ∧ q < j + 1 := mem_Ico.mp hq
    omega

lemma bezoutCoeff_eq_sum_range : bezoutCoeff f g i j = ∑ q ∈ range (j + 1),
    (f.coeff (i + j + 1 - q) * g.coeff q - f.coeff q * g.coeff (i + j + 1 - q)) := by
  rcases le_or_gt j i with h | h
  · rw [bezoutCoeff, min_eq_right h]
  · rw [bezoutCoeff, min_eq_left h.le, ← sum_range_add_sum_Ico _ (by omega : i + 1 ≤ j + 1),
      sum_Ico_bezout_eq_zero, add_zero]

lemma bezoutCoeff_zero_left :
    bezoutCoeff f g 0 j = f.coeff (j + 1) * g.coeff 0 - f.coeff 0 * g.coeff (j + 1) := by
  simp [bezoutCoeff]

lemma bezoutCoeff_zero_right :
    bezoutCoeff f g i 0 = f.coeff (i + 1) * g.coeff 0 - f.coeff 0 * g.coeff (i + 1) :=
  (bezoutCoeff_comm f g i 0).trans (bezoutCoeff_zero_left f g i)

lemma bezoutCoeff_succ_sub : bezoutCoeff f g i (j + 1) - bezoutCoeff f g (i + 1) j =
    f.coeff (i + 1) * g.coeff (j + 1) - f.coeff (j + 1) * g.coeff (i + 1) := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [bezoutCoeff, bezoutCoeff, min_eq_left (by omega), min_eq_left (by omega),
      sum_range_succ _ (i + 1), show i + (j + 1) + 1 = i + 1 + j + 1 by omega,
      show i + 1 + j + 1 - (i + 1) = j + 1 by omega]
    ring1
  · rw [bezoutCoeff, bezoutCoeff, min_eq_left (by omega), min_eq_right (by omega),
      show i + (i + 1) + 1 = i + 1 + i + 1 by omega, sub_self, sub_self]
  · rw [bezoutCoeff, bezoutCoeff, min_eq_right (by omega), min_eq_right (by omega),
      sum_range_succ _ (j + 1), show i + 1 + j + 1 = i + (j + 1) + 1 by omega,
      show i + (j + 1) + 1 - (j + 1) = i + 1 by omega]
    ring1

lemma bezoutCoeff_sub (s t : ℕ) : (if s = 0 then 0 else bezoutCoeff f g (s - 1) t) -
    (if t = 0 then 0 else bezoutCoeff f g s (t - 1)) = f.coeff s * g.coeff t -
      f.coeff t * g.coeff s := by
  rcases s with _ | s <;> rcases t with _ | t
  · simp
  · simp [bezoutCoeff_zero_left]
  · simp [bezoutCoeff_zero_right]
  · simpa using bezoutCoeff_succ_sub f g s t

lemma sylvester_submatrix : (sylvester f g n n).submatrix finSumFinEquiv finSumFinEquiv =
    Matrix.fromBlocks (sylvesterLow g n) (sylvesterLow f n) (sylvesterHigh g n)
      (sylvesterHigh f n) := by
  ext (i | i) (j | j) <;> simp [sylvester, sylvesterLow, sylvesterHigh, -Fin.natAdd_eq_addNat] <;>
    split_ifs <;> first | rfl | (exfalso; omega)

lemma sylvesterHigh_mul_comm :
    sylvesterHigh f n * sylvesterHigh g n = sylvesterHigh g n * sylvesterHigh f n := by
  have hQ (h : R[X]) (a b : Fin n) :
      sylvesterHigh h n a b = if (a : ℕ) ≤ b then h.coeff (n + a - b) else 0 :=
    rfl
  ext i j
  have h0 (a b : R[X]) (k : Fin n) (h : ¬((i : ℕ) ≤ k ∧ (k : ℕ) ≤ j)) :
      sylvesterHigh a n i k * sylvesterHigh b n k j = 0 := by
    rw [hQ, hQ]
    split_ifs <;> first | (exfalso; omega) | simp
  rw [Matrix.mul_apply, Matrix.mul_apply, ← sub_eq_zero, ← sum_sub_distrib]
  -- The reflection `k ↦ i + j - k` of `[i, j]` exchanges the terms of the two sums.
  refine sum_ninvolution
    (fun k ↦ if h : (i : ℕ) ≤ k ∧ (k : ℕ) ≤ j then ⟨i + j - k, by omega⟩ else k) (fun k ↦ ?_)
    (fun k hk ↦ ?_) (fun k ↦ mem_univ _) (fun k ↦ ?_)
  · by_cases h : (i : ℕ) ≤ k ∧ (k : ℕ) ≤ j
    · have c1 : (i : ℕ) ≤ i + j - k := by omega
      have c2 : (i : ℕ) + j - k ≤ j := by omega
      have e1 : n + (i : ℕ) - (i + j - k) = n + k - j := by omega
      have e2 : n + ((i : ℕ) + j - k) - j = n + i - k := by omega
      rw [dite_eq_left h]
      simp only [hQ, h.1, h.2, c1, c2, e1, e2]
      ring1
    · rw [dite_eq_right h, h0 f g k h, h0 g f k h, sub_self, add_zero]
  · by_cases h : (i : ℕ) ≤ k ∧ (k : ℕ) ≤ j
    · rw [dite_eq_left h]
      intro heq
      have hv : (i : ℕ) + j - k = k := Fin.ext_iff.mp heq
      have e : n + (i : ℕ) - k = n + k - j := by omega
      apply hk
      simp only [hQ, h.1, h.2, e]
      ring1
    · exact absurd (by rw [h0 f g k h, h0 g f k h, sub_self]) hk
  · by_cases h : (i : ℕ) ≤ k ∧ (k : ℕ) ≤ j
    · rw [dite_eq_left h, dite_eq_left (by dsimp only; omega)]
      ext
      dsimp only
      omega
    · rw [dite_eq_right h, dite_eq_right h]

variable {f g n} (hf : f.natDegree ≤ n) (hg : g.natDegree ≤ n)
include hf hg

variable {i} in
lemma bezoutCoeff_eq_zero_of_le_left (hi : n ≤ i) : bezoutCoeff f g i j = 0 := by
  refine sum_eq_zero fun k hk ↦ ?_
  have hkj : k ≤ j := (Nat.lt_succ_iff.mp (mem_range.mp hk)).trans (min_le_right i j)
  have hf' : f.coeff (i + j + 1 - k) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hg' : g.coeff (i + j + 1 - k) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hf', hg', zero_mul, mul_zero, sub_zero]

variable {j} in
lemma bezoutCoeff_eq_zero_of_le_right (hj : n ≤ j) : bezoutCoeff f g i j = 0 :=
  (bezoutCoeff_comm f g i j).trans (bezoutCoeff_eq_zero_of_le_left i hf hg hj)

lemma bezoutMatrix_apply_eq_sub_mul_apply (a b : Fin n) : bezoutMatrix f g n a b =
    (sylvesterLow g n * sylvesterHigh f n - sylvesterLow f n * sylvesterHigh g n) b a.rev := by
  let F : ℕ → R := fun k ↦ if k ≤ b then
    g.coeff (b - k) * f.coeff (k + a + 1) - f.coeff (b - k) * g.coeff (k + a + 1) else 0
  have hterm (k : Fin n) : sylvesterLow g n b k * sylvesterHigh f n k a.rev -
      sylvesterLow f n b k * sylvesterHigh g n k a.rev = F k := by
    simp only [sylvesterLow, sylvesterHigh, Matrix.of_apply, F, Fin.le_def, Fin.val_rev]
    split_ifs with h1 h2
    · rw [show n + ↑k - (n - (↑a + 1)) = ↑k + ↑a + 1 by omega]
    · rw [coeff_eq_zero_of_natDegree_lt (p := f) (show f.natDegree < ↑k + ↑a + 1 by omega),
        coeff_eq_zero_of_natDegree_lt (p := g) (show g.natDegree < ↑k + ↑a + 1 by omega)]
    all_goals simp
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, ← sum_sub_distrib]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range F n, ← sum_subset (range_mono (by omega : (b : ℕ) + 1 ≤ n))
    (fun k _ hk ↦ by rw [mem_range] at hk; simp only [F]; rw [ite_eq_right (by omega)]),
    bezoutMatrix, Matrix.of_apply, bezoutCoeff_eq_sum_range, ← sum_range_reflect]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mem_range] at hk
  simp only [F]
  rw [ite_eq_left (by omega), show (b : ℕ) + 1 - 1 - k = b - k by omega,
    show (a : ℕ) + b + 1 - (b - k) = k + a + 1 by omega]
  ring1

/-- **The determinant of the Bézout matrix is the resultant, up to sign**: for polynomials `f` and
`g` of degree at most `n`, the determinant of their degree `n` Bézout matrix is `(-1)^(n(n-1)/2)`
times their resultant `Polynomial.resultant f g n n`, the determinant of their Sylvester matrix.
The LMFDB knowl `alg.bezout_matrix` states that it is the resultant, leaving out the sign. -/
lemma det_bezoutMatrix : (bezoutMatrix f g n).det = (-1) ^ n.choose 2 * resultant f g n n := by
  have hB : bezoutMatrix f g n = (sylvesterLow g n * sylvesterHigh f n -
      sylvesterLow f n * sylvesterHigh g n)ᵀ.submatrix Fin.revPerm id := by
    ext i j
    rw [bezoutMatrix_apply_eq_sub_mul_apply hf hg]
    rfl
  rw [hB, Matrix.det_permute, Matrix.det_transpose, Fin.sign_revPerm, resultant,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, sylvester_submatrix,
    Matrix.det_fromBlocks_of_commute _ _ _ _ (sylvesterHigh_mul_comm g f n)]
  simp

variable {A : Type*} [CommRing A] [Algebra R A] (x y : A)

lemma mul_sum_bezoutCoeff_left :
    x * ∑ i ∈ range n, ∑ j ∈ range n, bezoutCoeff f g i j • (x ^ i * y ^ j) =
      ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
        (if s = 0 then 0 else bezoutCoeff f g (s - 1) t) • (x ^ s * y ^ t) := by
  rw [sum_range_succ', mul_sum]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, zero_smul, sum_const_zero,
    add_zero]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_range_succ, bezoutCoeff_eq_zero_of_le_right _ hf hg le_rfl, zero_smul, add_zero, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [mul_smul_comm, ← mul_assoc, ← pow_succ']

lemma mul_sum_bezoutCoeff_right :
    y * ∑ i ∈ range n, ∑ j ∈ range n, bezoutCoeff f g i j • (x ^ i * y ^ j) =
      ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
        (if t = 0 then 0 else bezoutCoeff f g s (t - 1)) • (x ^ s * y ^ t) := by
  rw [sum_range_succ, mul_sum]
  simp only [bezoutCoeff_eq_zero_of_le_left _ hf hg le_rfl, ite_self, zero_smul, sum_const_zero,
    add_zero]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_range_succ', mul_sum]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, zero_smul, add_zero]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [mul_smul_comm, mul_left_comm, ← pow_succ']

/-- **The defining identity of the Bézoutian**: for polynomials `f` and `g` of degree at most `n`
and elements `x`, `y` of a commutative algebra,
`(x - y) ∑_{i, j < n} c_ij xⁱ yʲ = f(x)g(y) − f(y)g(x)`. -/
lemma sub_mul_sum_bezoutCoeff :
    (x - y) * ∑ i ∈ range n, ∑ j ∈ range n, bezoutCoeff f g i j • (x ^ i * y ^ j) =
      aeval x f * aeval y g - aeval y f * aeval x g := by
  have hf' (z : A) : aeval z f = ∑ i ∈ range (n + 1), f.coeff i • z ^ i :=
    aeval_eq_sum_range' (Nat.lt_succ_of_le hf) z
  have hg' (z : A) : aeval z g = ∑ i ∈ range (n + 1), g.coeff i • z ^ i :=
    aeval_eq_sum_range' (Nat.lt_succ_of_le hg) z
  have h1 : aeval x f * aeval y g = ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
      (f.coeff s * g.coeff t) • (x ^ s * y ^ t) := by
    rw [hf', hg', sum_mul_sum]
    simp_rw [smul_mul_smul_comm]
  have h2 : aeval y f * aeval x g = ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
      (f.coeff t * g.coeff s) • (x ^ s * y ^ t) := by
    rw [hf', hg', sum_mul_sum, sum_comm]
    simp_rw [smul_mul_smul_comm, mul_comm (y ^ _)]
  rw [sub_mul, mul_sum_bezoutCoeff_left hf hg, mul_sum_bezoutCoeff_right hf hg, h1, h2,
    ← sum_sub_distrib, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, ← sub_smul, bezoutCoeff_sub]

/-- **The defining identity of the Bézout matrix**: for polynomials `f` and `g` of degree at most
`n` and elements `x`, `y` of a commutative algebra, the entries `c_ij` of the degree `n` Bézout
matrix satisfy `(x - y) ∑_{i, j < n} c_ij xⁱ yʲ = f(x)g(y) − f(y)g(x)`. As `x - y` is a
non-zero-divisor in the polynomial ring in `x` and `y`, this determines the matrix. -/
lemma sub_mul_sum_bezoutMatrix :
    (x - y) * ∑ i : Fin n, ∑ j : Fin n, bezoutMatrix f g n i j • (x ^ (i : ℕ) * y ^ (j : ℕ)) =
      aeval x f * aeval y g - aeval y f * aeval x g := by
  rw [← sub_mul_sum_bezoutCoeff hf hg, ← Fin.sum_univ_eq_sum_range]
  simp_rw [← Fin.sum_univ_eq_sum_range (fun j ↦ bezoutCoeff f g _ j • (x ^ _ * y ^ j))]
  rfl

end Polynomial
