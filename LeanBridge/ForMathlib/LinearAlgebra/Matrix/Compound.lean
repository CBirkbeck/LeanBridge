import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Instances.Matrix
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# Compound matrices

The `n`th compound matrix `Cₙ(A)` of a square matrix `A`, indexed by a finite linearly ordered type
`I`, is the matrix of the map that `A` induces on the `n`th exterior power, in the basis of the
wedges `e_{i₁} ∧ ⋯ ∧ e_{iₙ}`, `i₁ < ⋯ < iₙ`, of the standard basis vectors, indexed by the
`n`-element subsets of `I`. Its entries are the `n × n` minors of `A` (Tau Ceti's
`Module.Basis.toMatrix_exteriorPower_map`), and `A ↦ Cₙ(A)` is multiplicative, by the
functoriality of the exterior power: this is the Cauchy–Binet formula. Its trace is the sum of the
principal `n × n` minors of `A`, which is the coefficient of `Xⁿ` in `det(1 + X A)` (Mathlib's
`Matrix.coeff_det_one_add_X_smul_eq_sum_minors`), the `n`th elementary symmetric function of the
eigenvalues of `A`.

## Main definitions

* `Matrix.compound`: the `n`th compound matrix, as a monoid homomorphism.

## Main results

* `Matrix.trace_compound_eq_sum`: the trace of `Cₙ(A)` is the sum of the principal `n × n` minors
  of `A`.
* `Matrix.trace_compound`: it is the coefficient of `Xⁿ` in `det(1 + X A)`.
-/

open Module Polynomial Set powersetCard

variable {R I : Type*} [CommRing R] [Fintype I] [LinearOrder I] (n : ℕ) (A : Matrix I I R)
  (s t : powersetCard I n)

namespace Matrix

/-- The `n`th **compound matrix** `Cₙ(A)` of a square matrix `A` indexed by a finite linearly
ordered type `I`: the matrix of the map induced by `A` on the `n`th exterior power, in the basis of
the wedges of the standard basis vectors indexed by the `n`-element subsets of `I`. Its entries are
the `n × n` minors of `A`. -/
noncomputable def compound : Matrix I I R →* Matrix (powersetCard I n) (powersetCard I n) R where
  toFun M := LinearMap.toMatrix ((Pi.basisFun R I).exteriorPower n)
    ((Pi.basisFun R I).exteriorPower n) (exteriorPower.map n (toLin' M))
  map_one' := by
    rw [toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]
  map_mul' M N := by
    rw [toLin'_mul, exteriorPower.map_comp,
      LinearMap.toMatrix_comp _ ((Pi.basisFun R I).exteriorPower n)]

lemma compound_apply : compound n A s t =
    (of fun i j : Fin n ↦ A (ofFinEmbEquiv.symm s j) (ofFinEmbEquiv.symm t i)).det := by
  rw [compound, MonoidHom.coe_mk, OneHom.coe_mk, Basis.toMatrix_exteriorPower_map,
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

lemma compound_apply_self :
    compound n A s s = (A.submatrix (Subtype.val : s.val → I) Subtype.val).det := by
  rw [compound_apply, ← det_transpose,
    ← det_submatrix_equiv_self (s.val.orderIsoOfFin s.prop).toEquiv, submatrix_submatrix]
  rfl

/-- **The trace of the `n`th compound matrix of `A` is the sum of the principal `n × n` minors of
`A`.** -/
lemma trace_compound_eq_sum : (compound n A).trace =
    ∑ s ∈ Finset.univ.powersetCard n, (A.submatrix (Subtype.val : s → I) Subtype.val).det := by
  rw [Finset.sum_subtype (Finset.univ.powersetCard n) (p := (· ∈ powersetCard I n))
    (fun s ↦ by simp)]
  exact Finset.sum_congr rfl fun s _ ↦ compound_apply_self n A s

/-- **The trace of the `n`th compound matrix of `A` is the coefficient of `Xⁿ` in `det(1 + X A)`**,
the `n`th elementary symmetric function of the eigenvalues of `A`. -/
lemma trace_compound : (compound n A).trace = (det (1 + (X : R[X]) • A.map C)).coeff n := by
  rw [trace_compound_eq_sum, coeff_det_one_add_X_smul_eq_sum_minors]

lemma trace_compound_neg : (compound n (-A)).trace = (-1) ^ n * (compound n A).trace := by
  rw [trace_compound_eq_sum, trace_compound_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  simp only [submatrix_neg, Pi.neg_apply, det_neg, Fintype.card_coe,
    (Finset.mem_powersetCard.mp hs).2]

end Matrix

variable [TopologicalSpace R] [IsTopologicalRing R] in
lemma Continuous.matrix_compound {X : Type*} [TopologicalSpace X] {M : X → Matrix I I R}
    (hM : Continuous M) : Continuous fun x ↦ Matrix.compound n (M x) := by
  refine continuous_matrix fun s t ↦ ?_
  simp_rw [Matrix.compound_apply]
  exact (continuous_matrix fun i j ↦ hM.matrix_elem _ _).matrix_det
