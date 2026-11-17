import TauCeti.Algebra.Quaternion.BaseChange
import TauCeti.Algebra.Quaternion.SplittingCriterion
import TauCeti.NumberTheory.QuadraticForm.Global.TernaryObstruction
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.MaximalOrderConjugate

/-!
# A polarized quaternion order

A polarized order `(O, μ)` (LMFDB `shimcurve.polarized_order`, `PolarizedQuaternionOrder`) is an
order `O` of an indefinite division quaternion algebra `B` over `ℚ` with a unit `μ` of `B` such
that `μ² ∈ ℤ_{<0}` and `trd(μ x) ∈ ℤ` for all `x ∈ O`. This file gives one, so that the results
about polarized orders apply to an actual polarized order: in `B = (-1, 3 / ℚ) = ℍ[ℚ,-1,3]`, the
order `O = ℤ + ℤi + ℤj + ℤij` with `μ = i`, `μ² = -1`.

* `B` is a division algebra: by Tau Ceti's splitting criterion it is either a division algebra or
  isomorphic to `M₂(ℚ)`, and the latter happens exactly when `3 = x² + y²` for rational `x`, `y`.
  But `3` is not a sum of two rational squares, as the form `x² + y² - 3z²` is anisotropic over
  `ℚ` (Tau Ceti's `TauCeti.NumberField.QuadraticForm.anisotropic_sumTwoSquaresSubThreeSq`: it is
  anisotropic over `ℚ_3`, where the Hilbert symbol `(-1, 3)` is `-1`).
* `B` is indefinite: in `ℝ ⊗ B ≅ ℍ[ℝ,-1,3]` the elements `√3 ± j` are nonzero with product
  `3 - j² = 0`; more generally `(a, b / ℚ)` is indefinite when `b > 0`.
* `O` is an order, and `μ = i ∈ O` is a unit with `μ² = -1`; for `x ∈ O`, `trd(μ x)` is an integer,
  as `μ x ∈ O` and the reduced trace is integral on an order.

The algebra `B` is a quaternion algebra over `ℚ`: it is central simple of dimension `4`, by Tau
Ceti's instances for `ℍ[K,a,b]`, recorded here as instances for `ℍ[ℚ,-1,3]`, so that the results
on polarized orders of quaternion algebras over `ℚ` apply to it.

This polarized order also shows that the quotient `nrd(μ) / discrd(O)`, which LMFDB
`shimcurve.nrdmu` calls an integer, need not be one: in the `ℤ`-basis `1, i, j, ij` of `O` the
reduced trace form is `diag(2, -2, 6, 6)`, so that `disc(O) = 144` and `discrd(O) = 12`, while
`nrd(μ) = 1`. The polarization degree, the square-free part of `1 / 12`, is `3`, whereas the
square-free part of the numerator `1` (`PolarizedQuaternionOrder.degree`) is `1`.

## Main definitions

* `QuaternionAlgebra.Basis.negOneThree`: the quaternion basis `i`, `j`, `k = ij` of `(-1, 3 / ℚ)`
  over `ℤ`.
* `PolarizedQuaternionOrder.negOneThree` (LMFDB `shimcurve.polarized_order`): the polarized order
  `(ℤ + ℤi + ℤj + ℤij, i)` of `(-1, 3 / ℚ)`.

## Main results

* `Rat.sq_add_sq_ne_three`: `3` is not a sum of two rational squares.
* `QuaternionAlgebra.isDivision_negOne_three`: `(-1, 3 / ℚ)` is a division algebra.
* `QuaternionAlgebra.isIndefinite_of_pos`: `(a, b / ℚ)` is indefinite when `b > 0`.
* `QuaternionAlgebra.Basis.isQuaternionOrder_negOneThree`: `ℤ + ℤi + ℤj + ℤij` is an order of
  `(-1, 3 / ℚ)`.
* `QuaternionAlgebra.Basis.quaternionDiscrd_negOneThree` (LMFDB `shimcurve.disco`): its reduced
  discriminant is `12`.
* `PolarizedQuaternionOrder.polarizationDegree_negOneThree` (LMFDB `shimcurve.nrdmu`): the
  polarization degree of `(ℤ + ℤi + ℤj + ℤij, i)` is `3`.
* `PolarizedQuaternionOrder.degree_negOneThree`: the square-free part of the numerator of
  `nrd(μ) / discrd(O)` is `1` for it.
-/

open Module QuaternionAlgebra TauCeti NumberField

open LinearMap (BilinForm)

open scoped Quaternion TensorProduct

namespace Rat

/-- **`3` is not a sum of two rational squares**: `(x, y, 1)` would be a nonzero zero of the form
`x² + y² - 3z²`, which is anisotropic over `ℚ` (Tau Ceti's
`TauCeti.NumberField.QuadraticForm.anisotropic_sumTwoSquaresSubThreeSq`). -/
lemma sq_add_sq_ne_three (x y : ℚ) : x ^ 2 + y ^ 2 ≠ 3 := fun h ↦ by
  have h0 : ![x, y, 1] = 0 := QuadraticForm.anisotropic_sumTwoSquaresSubThreeSq _ (by simp [h])
  simpa using congrFun h0 2

end Rat

namespace QuaternionAlgebra

instance : IsSimpleRing ℍ[ℚ,-1,3] :=
  QuaternionAlgebra.instIsSimpleRing (-1 : ℚˣ) (Units.mk0 3 three_ne_zero)

instance : Algebra.IsCentral ℚ ℍ[ℚ,-1,3] :=
  QuaternionAlgebra.instIsCentral (-1 : ℚ) (Units.mk0 3 three_ne_zero)

/-- **`(-1, 3 / ℚ)` is a division algebra**: it is either a division algebra or `M₂(ℚ)`, and the
latter would make `3 = x² + y²` for some rational `x`, `y` (Tau Ceti's splitting criterion). -/
lemma isDivision_negOne_three : IsDivision ℍ[ℚ,-1,3] := by
  rcases QuaternionAlgebra.forall_isUnit_or_nonempty_algEquiv_matrix (-1 : ℚˣ)
    (Units.mk0 3 three_ne_zero) with h | h
  · exact h
  · rcases (QuaternionAlgebra.nonempty_algEquiv_matrix_iff_exists_eq_sq_sub_mul_sq _ _).mp h with
      ⟨x, y, hxy⟩
    exact absurd (by simpa using hxy.symm) (Rat.sq_add_sq_ne_three x y)

/-- **`(a, b / ℚ)` is indefinite when `b > 0`**: `ℝ ⊗ (a, b / ℚ) ≅ ℍ[ℝ,a,b]` is not a division
algebra, as the nonzero elements `√b ± j` have product `b - j² = 0`. -/
lemma isIndefinite_of_pos {a b : ℚ} (hb : 0 < b) : IsIndefinite ℍ[ℚ,a,b] := fun h ↦ by
  let e : ℝ ⊗[ℚ] ℍ[ℚ,a,b] ≃ₐ[ℝ] ℍ[ℝ,algebraMap ℚ ℝ a,algebraMap ℚ ℝ b] :=
    QuaternionAlgebra.baseChangeTwoParams ℚ ℝ a b
  let y : ℍ[ℝ,algebraMap ℚ ℝ a,algebraMap ℚ ℝ b] := ⟨√(b : ℝ), 0, 1, 0⟩
  let y' : ℍ[ℝ,algebraMap ℚ ℝ a,algebraMap ℚ ℝ b] := ⟨√(b : ℝ), 0, -1, 0⟩
  have hyy : y * y' = 0 := by
    ext <;> simp [y, y', Real.mul_self_sqrt (Rat.cast_nonneg.mpr hb.le)]
  have hy : e.symm y ≠ 0 := (map_ne_zero_iff e.symm e.symm.injective).mpr fun h0 ↦ by
    simpa [y] using congrArg imJ h0
  have hy' : y' ≠ 0 := fun h0 ↦ by
    simpa [y'] using congrArg imJ h0
  have hu : IsUnit y := by
    simpa using (h _ hy).map e
  exact hy' (hu.mul_right_eq_zero.mp hyy)

namespace Basis

/-- The quaternion basis `i`, `j`, `k = ij` of `(-1, 3 / ℚ)` over `ℤ`: `i² = -1`, `j² = 3`. -/
def negOneThree : Basis ℍ[ℚ,-1,3] (-1 : ℤ) 0 3 where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by ext <;> simp
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- **`ℤ + ℤi + ℤj + ℤij` is an order of `(-1, 3 / ℚ)`.** -/
lemma isQuaternionOrder_negOneThree : negOneThree.liftHom.range.IsQuaternionOrder := by
  refine negOneThree.isQuaternionOrder_range_liftHom (eq_top_iff.mpr fun x _ ↦ ?_)
  have hx :
      x = x.re • 1 + x.imI • negOneThree.i + x.imJ • negOneThree.j + x.imK • negOneThree.k := by
    ext <;> simp [negOneThree]
  rw [hx]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
  all_goals exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

lemma liftHom_negOneThree_apply (y : ℍ[ℤ,-1,0,3]) :
    negOneThree.liftHom y = ⟨y.re, y.imI, y.imJ, y.imK⟩ := by
  ext <;> simp [negOneThree, lift]

lemma liftHom_negOneThree_injective : Function.Injective negOneThree.liftHom := fun y z h ↦ by
  rw [liftHom_negOneThree_apply, liftHom_negOneThree_apply] at h
  ext
  · simpa using congrArg re h
  · simpa using congrArg imI h
  · simpa using congrArg imJ h
  · simpa using congrArg imK h

/-- **The order `ℤ + ℤi + ℤj + ℤij` of `(-1, 3 / ℚ)` has reduced discriminant `12`**: in its
`ℤ`-basis `1, i, j, ij` the reduced trace form is `diag(2, -2, 6, 6)`, of determinant `-144`. -/
lemma quaternionDiscrd_negOneThree : negOneThree.liftHom.range.quaternionDiscrd = 12 := by
  let x : Module.Basis (Fin 4) ℤ negOneThree.liftHom.range := (basisOneIJK (-1 : ℤ) 0 3).map
    (AlgEquiv.ofInjective negOneThree.liftHom liftHom_negOneThree_injective).toLinearEquiv
  have hx (k : Fin 4) : (x k : ℍ[ℚ,-1,3]) = basisOneIJK (-1 : ℚ) 0 3 k := by
    have h : (x k : ℍ[ℚ,-1,3]) = negOneThree.liftHom (basisOneIJK (-1 : ℤ) 0 3 k) := rfl
    rw [h, liftHom_negOneThree_apply]
    fin_cases k <;> ext <;> simp [basisOneIJK]
  have hm : (Matrix.of fun i j ↦ reducedTrace ℍ[ℚ,-1,3] ((x i : ℍ[ℚ,-1,3]) * x j)) =
      BilinForm.toMatrix (basisOneIJK (-1 : ℚ) 0 3) (traceForm ℍ[ℚ,-1,3]) := by
    ext i j
    rw [Matrix.of_apply, BilinForm.toMatrix_apply, traceForm_apply, hx, hx]
  have hd : negOneThree.liftHom.range.quaternionDisc = ((12 : ℤ) : ℚ) ^ 2 := by
    rw [Subalgebra.quaternionDisc_eq_quaternionDiscOfBasis (finrank_eq_four _ _ _)
      isQuaternionOrder_negOneThree x, Subalgebra.quaternionDiscOfBasis, hm,
      toMatrix_traceForm_basisOneIJK, Matrix.det_diagonal, Fin.prod_univ_four]
    norm_num
  rw [Subalgebra.quaternionDiscrd_eq_abs hd]
  norm_num

end Basis

end QuaternionAlgebra

namespace PolarizedQuaternionOrder

/-- **A polarized order** (LMFDB `shimcurve.polarized_order`): in the indefinite division quaternion
algebra `(-1, 3 / ℚ)`, the order `ℤ + ℤi + ℤj + ℤij` with the polarization `μ = i`, a unit with
`μ² = -1`, such that `trd(μ x) ∈ ℤ` for every `x` in the order. -/
def negOneThree : PolarizedQuaternionOrder ℍ[ℚ,-1,3] where
  isDivision := isDivision_negOne_three
  isIndefinite := isIndefinite_of_pos three_pos
  order := Basis.negOneThree.liftHom.range
  isQuaternionOrder := Basis.isQuaternionOrder_negOneThree
  polarization := ⟨⟨0, 1, 0, 0⟩, ⟨0, -1, 0, 0⟩, by ext <;> simp, by ext <;> simp⟩
  isPolarization := ⟨⟨-1, by norm_num, by ext <;> simp [sq]⟩, fun x hx ↦
    Subalgebra.exists_reducedTrace_eq_intCast (finrank_eq_four _ _ _)
      Basis.isQuaternionOrder_negOneThree (mul_mem Basis.negOneThree.i_mem_range_liftHom hx)⟩

lemma reducedNorm_polarization_negOneThree :
    reducedNorm ℍ[ℚ,-1,3] (negOneThree.polarization : ℍ[ℚ,-1,3]) = 1 := by
  rw [reducedNorm_quaternionAlgebra]
  simp [negOneThree]

lemma quaternionDiscrd_order_negOneThree : negOneThree.order.quaternionDiscrd = 12 :=
  Basis.quaternionDiscrd_negOneThree

/-- **The polarization degree of `(ℤ + ℤi + ℤj + ℤij, i)` is `3`** (LMFDB `shimcurve.nrdmu`): the
quotient `nrd(μ) / discrd(O) = 1 / 12` is not an integer, and its square-free part is `3`, as
`(1 / 12) / 3 = (1 / 6)²`. -/
lemma polarizationDegree_negOneThree : negOneThree.polarizationDegree = 3 := by
  refine (eq_polarizationDegree_of_isSquare _ (finrank_eq_four _ _ _) Nat.prime_three.squarefree
    ⟨1 / 6, ?_⟩).symm
  rw [reducedNorm_polarization_negOneThree, quaternionDiscrd_order_negOneThree]
  norm_num

/-- **The square-free part of the numerator of `nrd(μ) / discrd(O)` is `1` for
`(ℤ + ℤi + ℤj + ℤij, i)`**, while its polarization degree is `3`: the two notions differ when the
quotient, here `1 / 12`, is not an integer. -/
lemma degree_negOneThree : negOneThree.degree = 1 := by
  rw [degree, reducedNorm_polarization_negOneThree, quaternionDiscrd_order_negOneThree]
  norm_num

end PolarizedQuaternionOrder
