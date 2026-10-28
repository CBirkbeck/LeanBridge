import LeanBridge.ForMathlib.LinearAlgebra.Matrix.BezoutMatrix
import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.CuspIndex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The degree, Bézout matrix and Bézout module of a hypergeometric family

For a list `C = [c₁, …, c_n]` of positive integers, `Φ_C = Φ_{c₁} ⋯ Φ_{c_n}` is the product of the
cyclotomic polynomials. The Bézout matrix of a hypergeometric family with defining parameters
`(A, B)` is the Bézout matrix of `Φ_A` and `Φ_B` of degree `max(deg Φ_A, deg Φ_B)`, which is the
degree `d` of the family, and its Bézout module is `ℤ^d / B ℤ^d`.

## Main definitions

* `Hypergeometric.CuspIndex.cyclotomicProd`: the polynomial `Φ_C` of a cusp-index `C`.
* `Hypergeometric.Parameters.degree` (LMFDB `hgm.degree`): the degree `∑_{a ∈ A} φ(a)`.
* `Hypergeometric.Parameters.bezoutMatrix` (LMFDB `hgm.bezout_matrix`): the Bézout matrix.
* `Hypergeometric.Parameters.bezoutDeterminant` (LMFDB `hgm.bezout_determinant`): its determinant.
* `Hypergeometric.Parameters.BezoutModule` (LMFDB `hgm.bezout_module`): the Bézout module.

## Main results

* `Hypergeometric.Parameters.degree_eq_sum_totient_B`: the degree is also `∑_{b ∈ B} φ(b)`.
* `Hypergeometric.CuspIndex.natDegree_cyclotomicProd`: `Φ_C` has degree `d`.
* `Hypergeometric.Parameters.bezoutDeterminant_eq`: the Bézout determinant is
  `(-1)^(d(d-1)/2)` times the resultant of `Φ_A` and `Φ_B`.
-/

open Polynomial

namespace Hypergeometric

variable {d : ℕ} (c : CuspIndex d) (P : Parameters d)

/-- The polynomial `Φ_C = ∏_{c ∈ C} Φ_c` of a cusp-index `C`, the product of the cyclotomic
polynomials of its entries (LMFDB `hgm.bezout_matrix`). -/
noncomputable def CuspIndex.cyclotomicProd : ℤ[X] :=
  ((c.toList : Multiset ℕ).map fun a ↦ cyclotomic a ℤ).prod

lemma CuspIndex.monic_cyclotomicProd : c.cyclotomicProd.Monic :=
  monic_multiset_prod_of_monic _ _ fun a _ ↦ cyclotomic.monic a ℤ

/-- **The polynomial `Φ_C` of a cusp-index of degree `d` has degree `d`.** -/
lemma CuspIndex.natDegree_cyclotomicProd : c.cyclotomicProd.natDegree = d := by
  rw [CuspIndex.cyclotomicProd, natDegree_multiset_prod_of_monic _ fun f hf ↦ by
    rcases Multiset.mem_map.mp hf with ⟨a, -, rfl⟩
    exact cyclotomic.monic a ℤ, Multiset.map_map]
  simpa [Function.comp_def, natDegree_cyclotomic] using c.sum_totient

/-- The **degree** of a hypergeometric family with defining parameters `(A, B)` (LMFDB
`hgm.degree`): `∑_{a ∈ A} φ(a)`, which equals `∑_{b ∈ B} φ(b)`
(`Hypergeometric.Parameters.degree_eq_sum_totient_B`) and the index `d` of `P : Parameters d`. Its
meaning as the dimension of the realisations of the motive is not available, as hypergeometric
motives are not formalised. -/
def Parameters.degree : ℕ :=
  (P.A.toList.map Nat.totient).sum

lemma Parameters.degree_eq : P.degree = d :=
  P.A.sum_totient

/-- **The degree is also the sum of the totients of the entries of `B`.** -/
lemma Parameters.degree_eq_sum_totient_B : P.degree = (P.B.toList.map Nat.totient).sum := by
  rw [P.degree_eq, P.B.sum_totient]

/-- The **Bézout matrix** of a hypergeometric family with defining parameters `(A, B)` (LMFDB
`hgm.bezout_matrix`): the Bézout matrix (LMFDB `alg.bezout_matrix`) of `Φ_A` and `Φ_B` of degree
`max(deg Φ_A, deg Φ_B)`, which is the degree `d`
(`Hypergeometric.CuspIndex.natDegree_cyclotomicProd`). -/
noncomputable def Parameters.bezoutMatrix : Matrix (Fin d) (Fin d) ℤ :=
  P.A.cyclotomicProd.bezoutMatrix P.B.cyclotomicProd d

lemma Parameters.max_natDegree_cyclotomicProd :
    max P.A.cyclotomicProd.natDegree P.B.cyclotomicProd.natDegree = d := by
  rw [P.A.natDegree_cyclotomicProd, P.B.natDegree_cyclotomicProd, max_self]

/-- The **Bézout determinant** of a hypergeometric family (LMFDB `hgm.bezout_determinant`): the
determinant of its Bézout matrix. -/
noncomputable def Parameters.bezoutDeterminant : ℤ :=
  P.bezoutMatrix.det

/-- **The Bézout determinant is the resultant up to sign**: it is `(-1)^(d(d-1)/2)` times the
resultant of `Φ_A` and `Φ_B`. -/
lemma Parameters.bezoutDeterminant_eq : P.bezoutDeterminant =
    (-1) ^ d.choose 2 * resultant P.A.cyclotomicProd P.B.cyclotomicProd d d :=
  det_bezoutMatrix P.A.natDegree_cyclotomicProd.le P.B.natDegree_cyclotomicProd.le

/-- The **Bézout module** of a hypergeometric family (LMFDB `hgm.bezout_module`): the `ℤ`-module
`ℤ^d / B ℤ^d` with relations matrix the Bézout matrix `B`, where `d` is the degree. The knowl
calls it finite; that the Bézout determinant is nonzero, as `Φ_A` and `Φ_B` are coprime, is not
proved here. -/
abbrev Parameters.BezoutModule : Type :=
  (Fin d → ℤ) ⧸ LinearMap.range P.bezoutMatrix.mulVecLin

end Hypergeometric
