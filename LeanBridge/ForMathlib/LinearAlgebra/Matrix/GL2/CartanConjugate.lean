import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.CartanNormalizer

/-!
# Conjugates of Cartan subgroups and of their normalizers

Conjugating by `g ∈ GL₂(R)` the Cartan subgroup of a free rank-2 algebra `A` in a basis `b` gives
the Cartan subgroup of `A` in the basis `Matrix.GeneralLinearGroup.conjBasis b g`, whose change of
basis matrix to `b` is `g`: the matrix of multiplication by a unit in the new basis is its matrix
in `b` conjugated by `g`. So a conjugate of a Cartan subgroup is a Cartan subgroup, and a conjugate
of the normalizer of a Cartan subgroup of `GL₂(𝔽_p)`, in the LMFDB's convention, is the normalizer
of the conjugate Cartan subgroup.

## Main definitions

* `Matrix.GeneralLinearGroup.conjBasis`: the basis of `A` obtained from `b` by the inverse of `g`.

## Main results

* `Matrix.GeneralLinearGroup.cartanSubgroup_map_conj`: the conjugate by `g` of the Cartan subgroup
  of `A` in the basis `b` is its Cartan subgroup in the basis `conjBasis b g`.
* `Matrix.GeneralLinearGroup.IsCartanSubgroup.map_conj`: a conjugate of a Cartan subgroup is a
  Cartan subgroup.
* `Matrix.GeneralLinearGroup.IsCartanNormalizer.map_conj`: a conjugate of the normalizer of a
  Cartan subgroup of `GL₂(𝔽_p)` is the normalizer of a Cartan subgroup.
-/

open Matrix Module TauCeti

namespace Matrix.GeneralLinearGroup

section Basis

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] (b : Basis (Fin 2) R A)
  (g : GL (Fin 2) R)

/-- The basis of a free rank-2 `R`-algebra `A` obtained from the basis `b` by the inverse of the
matrix `g ∈ GL₂(R)`, so that its change of basis matrix to `b` is `g`: the matrix of an
endomorphism of `A` in this basis is its matrix in `b` conjugated by `g`. -/
noncomputable def conjBasis : Basis (Fin 2) R A :=
  b.map (toLinearEquiv b (g : Matrix (Fin 2) (Fin 2) R) (isUnits_det_units g)).symm

lemma toMatrix_conjBasis : (conjBasis b g).toMatrix b = g := by
  ext i j
  rw [Basis.toMatrix_apply, conjBasis, Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, toLinearEquiv_apply, toLin_self]
  fin_cases i <;> simp

lemma toMatrix_conjBasis_flip : b.toMatrix (conjBasis b g) = (g⁻¹ : GL (Fin 2) R) := by
  have h : b.toMatrix (conjBasis b g) * (conjBasis b g).toMatrix b = 1 :=
    b.toMatrix_mul_toMatrix_flip _
  rw [toMatrix_conjBasis] at h
  exact Units.mul_eq_one_iff_eq_inv.mp h

lemma unitsLeftMulMatrix_conjBasis (x : Aˣ) :
    unitsLeftMulMatrix (conjBasis b g) x = MulAut.conj g (unitsLeftMulMatrix b x) := by
  refine Units.ext ?_
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, coe_unitsLeftMulMatrix,
    coe_unitsLeftMulMatrix, Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
    ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := conjBasis b g) (b' := b)
      (c := conjBasis b g) (c' := b), toMatrix_conjBasis, toMatrix_conjBasis_flip]

/-- **The conjugate of a Cartan subgroup is the Cartan subgroup in another basis**: conjugating by
`g` the Cartan subgroup of `A` in the basis `b` gives its Cartan subgroup in the basis
`conjBasis b g`. -/
lemma cartanSubgroup_map_conj :
    (cartanSubgroup b).map (MulAut.conj g).toMonoidHom = cartanSubgroup (conjBasis b g) := by
  rw [cartanSubgroup, cartanSubgroup, MonoidHom.map_range]
  congr 1
  exact MonoidHom.ext fun x ↦ (unitsLeftMulMatrix_conjBasis b g x).symm

variable {C : Subgroup (GL (Fin 2) R)}

/-- **A conjugate of a Cartan subgroup is a Cartan subgroup.** -/
lemma IsCartanSubgroup.map_conj (hC : IsCartanSubgroup C) :
    IsCartanSubgroup (C.map (MulAut.conj g).toMonoidHom) := by
  rcases hC with ⟨A, _, _, _, b, rfl⟩
  exact ⟨A, inferInstance, inferInstance, inferInstance, conjBasis b g, cartanSubgroup_map_conj b g⟩

end Basis

variable {p : ℕ} [Fact p.Prime] {N : Subgroup (GL (Fin 2) (ZMod p))}

/-- **A conjugate of the normalizer of a Cartan subgroup of `GL₂(𝔽_p)` is the normalizer of a
Cartan subgroup**, in the LMFDB's convention: the normalizer of the conjugate Cartan subgroup for
`p > 2`, and a subgroup containing it with index `2` for `p = 2`. -/
lemma IsCartanNormalizer.map_conj (hN : IsCartanNormalizer N) (g : GL (Fin 2) (ZMod p)) :
    IsCartanNormalizer (N.map (MulAut.conj g).toMonoidHom) := by
  rcases hN with ⟨C, hC, h⟩
  refine ⟨C.map (MulAut.conj g).toMonoidHom, hC.map_conj g, ?_⟩
  split_ifs at h ⊢
  · exact ⟨Subgroup.map_mono h.1,
      (Subgroup.relIndex_map_map_of_injective C N (MulAut.conj g).injective).trans h.2⟩
  · rw [h, Subgroup.map_equiv_normalizer_eq]

end Matrix.GeneralLinearGroup
