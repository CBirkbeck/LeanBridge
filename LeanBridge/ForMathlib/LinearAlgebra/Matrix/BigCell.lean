import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Matrix

/-!
# The big cell of the general linear group

Gaussian elimination without row or column exchanges writes a square matrix with nonzero pivots as
`L * diagonal d * U`, with `L` lower unitriangular, `d` nowhere zero and `U` upper unitriangular:
the products of the lower unitriangular, invertible diagonal and upper unitriangular matrices form
the big cell `B⁻ B` of `GL n`. Over a nontrivially normed field the pivots are continuous near the
identity, so every matrix close enough to `1` lies in the big cell. A neighbourhood of `1`
contains a box with infinite sides, and a polynomial vanishing on such a box is zero, so the big
cell is Zariski dense: a polynomial in the matrix entries vanishing on it is zero. This is the
density statement that the theorem of the highest weight for `GL n` rests on.

## Main results

* `Matrix.eventually_exists_eq_mul_diagonal_mul`: every matrix close enough to the identity is
  `L * diagonal d * U` with `L` lower unitriangular, `d` nowhere zero and `U` upper unitriangular.
* `Matrix.eq_zero_of_forall_eval_mul_diagonal_mul`: a polynomial in the entries of a square matrix
  that vanishes on all these products is zero.
-/

open Filter Topology

namespace Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The Schur complement of the upper-left entry of a square matrix of size `n + 1`: the lower-right
block minus the product of the first column, the inverse of the upper-left entry and the first
row. It is the matrix that the first step of Gaussian elimination leaves to be factorized. -/
private def schurSucc (M : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  of fun i j ↦ M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0

private lemma tendsto_schurSucc :
    Tendsto schurSucc (𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)) (𝓝 1) := by
  have h1 : schurSucc (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) = 1 := by
    ext i j
    simp [schurSucc, one_apply]
  refine h1 ▸ tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ ?_
  have h (a b : Fin (n + 1)) : Continuous fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 ↦ M a b :=
    continuous_id.matrix_elem a b
  exact ((h _ _).continuousAt.sub (((h _ _).mul (h _ _)).continuousAt.div (h 0 0).continuousAt
    (by simp))).tendsto

/-- **Every matrix close enough to the identity lies in the big cell**: it is `L * diagonal d * U`
with `L` lower unitriangular, `d` nowhere zero and `U` upper unitriangular. Near `1` the upper-left
entry is nonzero, and clearing the first row and column leaves the Schur complement, which is again
close to `1`, so the factorization follows by induction on the size. -/
lemma eventually_exists_eq_mul_diagonal_mul : ∀ᶠ M in 𝓝 (1 : Matrix (Fin n) (Fin n) 𝕜),
    ∃ (L U : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → 𝕜), L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧
      U.IsUpperTriangular ∧ (∀ i, U i i = 1) ∧ (∀ i, d i ≠ 0) ∧ M = L * diagonal d * U := by
  induction n with
  | zero =>
    exact .of_forall fun M ↦ ⟨1, 1, 0, fun i ↦ i.elim0, finZeroElim, fun i ↦ i.elim0, finZeroElim,
      finZeroElim, Subsingleton.elim _ _⟩
  | succ n ih =>
    have h0 : ∀ᶠ M in 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜), M 0 0 ≠ 0 :=
      (continuous_id.matrix_elem 0 0).continuousAt.eventually_ne (by simp)
    filter_upwards [tendsto_schurSucc.eventually ih, h0] with M hM hM0
    rcases hM with ⟨L, U, d, hL, hL1, hU, hU1, hd, hLU⟩
    refine ⟨of (Fin.cons (Fin.cons 1 0) fun i ↦ Fin.cons (M i.succ 0 / M 0 0) (L i)),
      of (Fin.cons (Fin.cons 1 fun j ↦ M 0 j.succ / M 0 0) fun i ↦ Fin.cons 0 (U i)),
      Fin.cons (M 0 0) d, fun i j hij ↦ ?_, fun i ↦ ?_, fun i j hij ↦ ?_, fun i ↦ ?_, fun i ↦ ?_,
      ?_⟩
    · rw [OrderDual.toDual_lt_toDual] at hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl 0)
        | succ j => simp
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (Fin.not_lt_zero _)
        | succ j => simpa using hL (OrderDual.toDual_lt_toDual.2 (Fin.succ_lt_succ_iff.1 hij))
    · induction i using Fin.cases with
      | zero => simp
      | succ i => simpa using hL1 i
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl 0)
        | succ j => exact absurd hij (Fin.not_lt_zero _)
      | succ i =>
        induction j using Fin.cases with
        | zero => simp
        | succ j => simpa using hU (Fin.succ_lt_succ_iff.1 hij)
    · induction i using Fin.cases with
      | zero => simp
      | succ i => simpa using hU1 i
    · induction i using Fin.cases with
      | zero => simpa using hM0
      | succ i => simpa using hd i
    · ext i j
      rw [mul_apply, Fin.sum_univ_succ]
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp
        | succ j => simp [mul_div_cancel₀ _ hM0]
      | succ i =>
        induction j using Fin.cases with
        | zero => simp [div_mul_cancel₀ _ hM0]
        | succ j =>
          have h : M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0 = (L * diagonal d * U) i j :=
            congrFun (congrFun hLU i) j
          rw [mul_apply] at h
          simp only [mul_diagonal] at h
          simp only [mul_diagonal, of_apply, Fin.cons_succ, Fin.cons_zero, div_mul_cancel₀ _ hM0]
          linear_combination h

/-- **The big cell is Zariski dense**: a polynomial in the entries of a square matrix that vanishes
on every product `L * diagonal d * U`, with `L` lower unitriangular, `d` nowhere zero and `U` upper
unitriangular, is zero. These products contain a neighbourhood of the identity
(`Matrix.eventually_exists_eq_mul_diagonal_mul`), hence a box with infinite sides. -/
lemma eq_zero_of_forall_eval_mul_diagonal_mul {P : MvPolynomial (Fin n × Fin n) 𝕜}
    (hP : ∀ L U : Matrix (Fin n) (Fin n) 𝕜, L.IsLowerTriangular → (∀ i, L i i = 1) →
      U.IsUpperTriangular → (∀ i, U i i = 1) → ∀ d : Fin n → 𝕜, (∀ i, d i ≠ 0) →
        MvPolynomial.eval (fun p ↦ (L * diagonal d * U) p.1 p.2) P = 0) : P = 0 := by
  have hΦ :
      Continuous fun x : Fin n × Fin n → 𝕜 ↦ (of fun i j ↦ x (i, j) : Matrix (Fin n) (Fin n) 𝕜) :=
    continuous_matrix fun i j ↦ continuous_apply (i, j)
  have hN : ∀ᶠ x in 𝓝 fun p : Fin n × Fin n ↦ (1 : Matrix (Fin n) (Fin n) 𝕜) p.1 p.2,
      ∃ (L U : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → 𝕜), L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧
        U.IsUpperTriangular ∧ (∀ i, U i i = 1) ∧ (∀ i, d i ≠ 0) ∧
          (of fun i j ↦ x (i, j) : Matrix (Fin n) (Fin n) 𝕜) = L * diagonal d * U := by
    filter_upwards [(hΦ.tendsto _).eventually eventually_exists_eq_mul_diagonal_mul] with x hx
    exact hx
  rw [nhds_pi] at hN
  rcases mem_pi.1 hN with ⟨I, -, t, ht, hsub⟩
  refine MvPolynomial.funext_set t (fun p ↦ infinite_of_mem_nhds _ (ht p)) fun x hx ↦ ?_
  rcases hsub fun p _ ↦ hx p (Set.mem_univ p) with ⟨L, U, d, hL, hL1, hU, hU1, hd, hx'⟩
  rw [map_zero, ← hP L U hL hL1 hU hU1 d hd, ← hx']
  rfl

end Matrix
