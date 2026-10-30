import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SymmetricCongruence
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.UpperHalfSpace
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Defs
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The invariant measure on the Siegel upper half-space

A point `τ = X + iY` of the Siegel upper half-space `ℋ_g` is determined by its coordinates
`τ_ij = x_ij + i y_ij`, `i ≤ j`, indexed by the unordered pairs `s(i, j) ∈ Sym2 l`; they identify
`ℋ_g` with an open subset of `ℂ^{g(g + 1) / 2}`, which gives `ℋ_g` its Lebesgue measure
`dX dY = ∏_{i ≤ j} dx_ij dy_ij`. The measure `det(Y)^{-g-1} dX dY` is invariant under the action of
`Sp(2g, ℝ)`: the holomorphic map `τ ↦ γτ = (aτ + b)(cτ + d)⁻¹` has derivative
`H ↦ (cτ + d)⁻ᵀ H (cτ + d)⁻¹`, of complex determinant `det(cτ + d)^{-g-1}` on symmetric matrices,
hence of real Jacobian `|det(cτ + d)|^{-2g-2}`, while `det Im(γτ) = det(Y) |det(cτ + d)|⁻²`.

## Main definitions

* `SiegelUpperHalfSpace.toCoords`: the coordinates of a point of `ℋ_g`,
  `SiegelUpperHalfSpace.coordSet` the open set they range over, and
  `SiegelUpperHalfSpace.ofCoords` the point with given coordinates.
* The instance `MeasurableSpace (SiegelUpperHalfSpace l)`, transported from the coordinates.
* `SiegelUpperHalfSpace.moebiusCoords`: the action of `γ ∈ Sp(2g, ℝ)` in coordinates.
* `SiegelUpperHalfSpace.coordDensity`: the density `det(Y)^{-g-1}` in coordinates.
* `SiegelUpperHalfSpace.invariantMeasure`: the measure `det(Y)^{-g-1} dX dY`.

## Main results

* `SiegelUpperHalfSpace.hasFDerivAt_moebiusCoords`: the derivative of `τ ↦ γτ` is
  `H ↦ (cτ + d)⁻ᵀ H (cτ + d)⁻¹`.
* `SiegelUpperHalfSpace.det_im_smul`: `det Im(γτ) = det(Y) / |det(cτ + d)|²`.
* `SiegelUpperHalfSpace.invariantMeasure_smul`: `det(Y)^{-g-1} dX dY` is invariant under
  `Sp(2g, ℝ)`, which gives the instance
  `SMulInvariantMeasure (Matrix.symplecticGroup l ℝ) (SiegelUpperHalfSpace l) invariantMeasure`.
-/

open Matrix Complex MeasureTheory Set

open scoped ENNReal Pointwise

namespace SiegelUpperHalfSpace

variable {l : Type*} (τ : SiegelUpperHalfSpace l) (h : Sym2 l → ℂ)

variable (l) in
/-- The coordinates `h : Sym2 l → ℂ` of the points of the Siegel upper half-space: those for which
the symmetric matrix `ofSymCoords h` has positive definite imaginary part. -/
def coordSet : Set (Sym2 l → ℂ) :=
  {h | ((ofSymCoords h).map im).PosDef}

/-- The coordinates `τ_ij`, `i ≤ j`, of a point `τ` of the Siegel upper half-space, indexed by
`s(i, j) ∈ Sym2 l`. -/
noncomputable def toCoords : Sym2 l → ℂ :=
  symCoords τ.val

lemma ofSymCoords_toCoords : ofSymCoords τ.toCoords = τ.val :=
  ofSymCoords_symCoords τ.transpose_val

lemma toCoords_mem_coordSet : τ.toCoords ∈ coordSet l := by
  rw [coordSet, mem_ofPred_eq, ofSymCoords_toCoords]
  exact τ.posDef_im

/-- The point of the Siegel upper half-space with coordinates `h`. -/
def ofCoords (hh : h ∈ coordSet l) : SiegelUpperHalfSpace l :=
  ⟨ofSymCoords h, transpose_ofSymCoords h, hh⟩

lemma toCoords_ofCoords (hh : h ∈ coordSet l) : (ofCoords h hh).toCoords = h :=
  symCoords_ofSymCoords h

lemma toCoords_injective : Function.Injective (toCoords (l := l)) := fun τ τ' hττ' ↦
  SiegelUpperHalfSpace.ext <| by rw [← ofSymCoords_toCoords, hττ', ofSymCoords_toCoords]

lemma range_toCoords : range toCoords = coordSet l :=
  Subset.antisymm (range_subset_iff.mpr toCoords_mem_coordSet) fun h hh ↦
    ⟨ofCoords h hh, toCoords_ofCoords h hh⟩

noncomputable instance : MeasurableSpace (SiegelUpperHalfSpace l) :=
  MeasurableSpace.comap toCoords inferInstance

private lemma sub_conjTranspose_eq_smul {M : Matrix l l ℂ} (hM : Mᵀ = M) :
    M - Mᴴ = (2 * I) • (M.map im).map ofReal := by
  ext i j
  simp only [Matrix.sub_apply, conjTranspose_apply, IsSymm.apply hM i j, Matrix.smul_apply,
    map_apply]
  rw [star_def, sub_conj]
  push_cast
  ring1

variable [Fintype l]

lemma isOpen_coordSet : IsOpen (coordSet l) := by
  have hc : coordSet l = (fun h ↦ (ofSymCoords h).map im) ⁻¹'
      {M | ∀ x : l → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x} := by
    ext h
    have hH : ((ofSymCoords h).map im).IsHermitian := by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, ← transpose_map,
        transpose_ofSymCoords]
    simp only [coordSet, mem_ofPred_eq, mem_preimage, posDef_iff_dotProduct_mulVec, star_trivial,
      hH, true_and]
  rw [hc]
  refine TauCeti.isOpen_setOfPred_dotProduct_mulVec_pos.preimage <|
    continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  simp only [map_apply]
  fun_prop

lemma measurableEmbedding_toCoords : MeasurableEmbedding (toCoords (l := l)) where
  injective := toCoords_injective
  measurable := comap_measurable toCoords
  measurableSet_image' s hs := by
    rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨t, ht, rfl⟩
    rw [image_preimage_eq_inter_range, range_toCoords]
    exact ht.inter isOpen_coordSet.measurableSet

variable [DecidableEq l]

lemma det_map_ofReal (M : Matrix l l ℝ) : (M.map ofReal).det = (M.det : ℂ) :=
  (RingHom.map_det ofRealHom M).symm

variable (l) in
/-- The density `det(Im ofSymCoords h)^{-g-1}` on the coordinates `h` of the Siegel upper
half-space, with `g = |l|`. -/
noncomputable def coordDensity : (Sym2 l → ℂ) → ℝ≥0∞ :=
  fun h ↦ ENNReal.ofReal (((ofSymCoords h).map im).det ^ (Fintype.card l + 1))⁻¹

variable (l) in
/-- The **invariant measure** `det(Y)^{-g-1} dX dY` on the Siegel upper half-space `ℋ_g`,
`τ = X + iY`, where `dX dY = ∏_{i ≤ j} dx_ij dy_ij` is the Lebesgue measure in the coordinates
`τ_ij = x_ij + i y_ij`, `i ≤ j`, of `τ` (`SiegelUpperHalfSpace.toCoords`). It is invariant under the
action of `Sp(2g, ℝ)` (`SiegelUpperHalfSpace.invariantMeasure_smul`). -/
noncomputable def invariantMeasure : Measure (SiegelUpperHalfSpace l) :=
  (volume.withDensity (coordDensity l)).comap toCoords

lemma invariantMeasure_apply (s : Set (SiegelUpperHalfSpace l)) :
    invariantMeasure l s = ∫⁻ h in toCoords '' s, coordDensity l h := by
  rw [invariantMeasure, measurableEmbedding_toCoords.comap_apply, withDensity_apply']

variable (γ : symplecticGroup l ℝ)

private lemma fromBlocks_map_mem :
    fromBlocks ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁.map ofReal)
      ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₂.map ofReal)
      ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁.map ofReal)
      ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂.map ofReal) ∈ symplecticGroup l ℂ := by
  rw [← fromBlocks_map, fromBlocks_toBlocks]
  exact SymplecticGroup.map_mem γ.2 ofRealHom

private lemma sub_num_mul_inv_denom_mul {S : Matrix l l ℂ} (hS : Sᵀ = S)
    (hJ : IsUnit (denom γ S)) :
    (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁.map ofReal - num γ S * (denom γ S)⁻¹ *
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁.map ofReal = (denom γ S)⁻¹ᵀ := by
  rcases SymplecticGroup.fromBlocks_mem_iff.mp (fromBlocks_map_mem γ) with ⟨h1, -, h3⟩
  have hJN : (denom γ S)ᵀ * num γ S = (num γ S)ᵀ * denom γ S := by
    rw [← sub_eq_zero, transpose_denom_mul_num_sub, hS, sub_self]
  have hdet : IsUnit (denom γ S).det := (isUnit_iff_isUnit_det _).mp hJ
  rw [transpose_nonsing_inv]
  refine (inv_eq_right_inv ?_).symm
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJN, Matrix.mul_assoc _ (denom γ S),
    mul_nonsing_inv _ hdet, Matrix.mul_one]
  have h3' : ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂.map ofReal)ᵀ *
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁.map ofReal -
        ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₂.map ofReal)ᵀ *
          (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁.map ofReal = 1 := by
    simpa using congrArg transpose h3
  simp only [denom, num, transpose_add, transpose_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, h1, ← h3']
  abel

/-- The action `τ ↦ γτ = (aτ + b)(cτ + d)⁻¹` of `γ = (a, b; c, d) ∈ Sp(2g, ℝ)` in the coordinates
`Sym2 l → ℂ` of the Siegel upper half-space, extended to all coordinates by the same formula. -/
noncomputable def moebiusCoords : (Sym2 l → ℂ) → Sym2 l → ℂ :=
  fun h ↦ symCoords (num γ (ofSymCoords h) * (denom γ (ofSymCoords h))⁻¹)

lemma toCoords_smul : (γ • τ).toCoords = moebiusCoords γ τ.toCoords := by
  rw [toCoords, val_smul, moebiusCoords, ofSymCoords_toCoords]

section Derivative

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private lemma hasFDerivAt_mul_ofSymCoords_add (A B : Matrix l l ℂ) :
    HasFDerivAt (fun h ↦ A * ofSymCoords h + B) (A • LinearMap.toContinuousLinearMap ofSymCoords)
      h :=
  ((LinearMap.toContinuousLinearMap ofSymCoords).hasFDerivAt.const_mul A).add_const B

private lemma hasFDerivAt_inv_denom (hh : IsUnit (denom γ (ofSymCoords h))) :
    HasFDerivAt (fun h ↦ (denom γ (ofSymCoords h))⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℂ (Matrix l l ℂ) (denom γ (ofSymCoords h))⁻¹
        (denom γ (ofSymCoords h))⁻¹).comp ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁.map ofReal •
          LinearMap.toContinuousLinearMap ofSymCoords)) h := by
  rw [funext fun h ↦ nonsing_inv_eq_ringInverse (denom γ (ofSymCoords h)), ← hh.unit_spec,
    ← Matrix.coe_units_inv]
  exact (hasFDerivAt_ringInverse hh.unit).comp h (hasFDerivAt_mul_ofSymCoords_add h _ _)

/-- **The derivative of the action of `Sp(2g, ℝ)` on the Siegel upper half-space**: in coordinates,
the derivative of `τ ↦ γτ = (aτ + b)(cτ + d)⁻¹` at a symmetric `τ` with `cτ + d` invertible is the
congruence `H ↦ (cτ + d)⁻ᵀ H (cτ + d)⁻¹`. -/
lemma hasFDerivAt_moebiusCoords (hh : IsUnit (denom γ (ofSymCoords h))) :
    HasFDerivAt (moebiusCoords γ)
      (LinearMap.toContinuousLinearMap (congrSym (denom γ (ofSymCoords h))⁻¹)) h := by
  refine ((LinearMap.toContinuousLinearMap symCoords).hasFDerivAt.comp h
    ((hasFDerivAt_mul_ofSymCoords_add h _ _).mul' (hasFDerivAt_inv_denom h γ hh))).congr_fderiv
      (ContinuousLinearMap.ext fun k ↦ ?_)
  refine (rfl : _ = symCoords (num γ (ofSymCoords h) * -((denom γ (ofSymCoords h))⁻¹ *
    ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁.map ofReal * ofSymCoords k) *
      (denom γ (ofSymCoords h))⁻¹) + (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁.map ofReal *
        ofSymCoords k * (denom γ (ofSymCoords h))⁻¹)).trans ?_
  rw [LinearMap.coe_toContinuousLinearMap', congrSym_apply,
    ← sub_num_mul_inv_denom_mul γ (transpose_ofSymCoords h) hh]
  congr 1
  noncomm_ring

end Derivative

lemma map_im_smul : ((γ • τ).val.map im).map ofReal =
    (denom γ τ.val)⁻¹ᴴ * (τ.val.map im).map ofReal * (denom γ τ.val)⁻¹ := by
  have e : (denom γ τ.val)⁻¹ᴴ * (denom γ τ.val)ᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv _ (isUnit_det_denom γ τ), conjTranspose_one]
  have h2 : (2 * I) • ((γ • τ).val.map im).map ofReal =
      (2 * I) • ((denom γ τ.val)⁻¹ᴴ * (τ.val.map im).map ofReal * (denom γ τ.val)⁻¹) := by
    rw [← sub_conjTranspose_eq_smul (γ • τ).transpose_val, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← sub_conjTranspose_eq_smul τ.transpose_val, ← conjTranspose_denom_mul_num_sub γ τ.val,
      val_smul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, e, Matrix.one_mul,
      mul_nonsing_inv_cancel_right _ _ (isUnit_det_denom γ τ), conjTranspose_mul]
  exact smul_right_injective _ (by simp) h2

/-- **The determinant of the imaginary part of `γτ`** is
`det Im(γτ) = det(Im τ) / |det(cτ + d)|²`, from `Im(γτ) = (cτ + d)⁻ᴴ (Im τ) (cτ + d)⁻¹`. -/
lemma det_im_smul :
    ((γ • τ).val.map im).det = (τ.val.map im).det / normSq (denom γ τ.val).det := by
  have h : (((γ • τ).val.map im).map ofReal).det =
      ((denom γ τ.val)⁻¹ᴴ * (τ.val.map im).map ofReal * (denom γ τ.val)⁻¹).det :=
    congrArg det (map_im_smul τ γ)
  rw [det_mul, det_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv', det_map_ofReal,
    det_map_ofReal] at h
  have hJ : (denom γ τ.val).det ≠ 0 := (isUnit_det_denom γ τ).ne_zero
  apply ofReal_injective
  rw [h, ofReal_div, normSq_eq_conj_mul_self, star_def, map_inv₀]
  field_simp

private lemma det_congrSym_restrictScalars (A : Matrix l l ℂ) :
    ((LinearMap.toContinuousLinearMap (congrSym A)).restrictScalars ℝ).det =
      normSq A.det ^ (Fintype.card l + 1) := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.coe_toContinuousLinearMap, LinearMap.det_restrictScalars, det_congrSym,
    Algebra.norm_complex_apply, map_pow]

private lemma coordDensity_toCoords :
    coordDensity l τ.toCoords = ENNReal.ofReal ((τ.val.map im).det ^ (Fintype.card l + 1))⁻¹ := by
  rw [coordDensity, ofSymCoords_toCoords]

private lemma jacobian_mul_coordDensity :
    ENNReal.ofReal |normSq (denom γ τ.val)⁻¹.det ^ (Fintype.card l + 1)| *
      coordDensity l (moebiusCoords γ τ.toCoords) = coordDensity l τ.toCoords := by
  rw [← toCoords_smul, coordDensity_toCoords, coordDensity_toCoords, det_im_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have hN : 0 < normSq (denom γ τ.val).det := normSq_pos.mpr (isUnit_det_denom γ τ).ne_zero
  have hY : 0 < (τ.val.map im).det := τ.posDef_im.det_pos
  rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, abs_of_nonneg (by positivity), inv_pow,
    div_pow]
  field_simp

variable (s : Set (SiegelUpperHalfSpace l))

private lemma image_toCoords_smul : toCoords '' (γ • s) = moebiusCoords γ '' (toCoords '' s) := by
  rw [← image_smul, image_image, image_image]
  exact image_congr fun τ _ ↦ toCoords_smul τ γ

private lemma hasFDerivWithinAt_moebiusCoords : ∀ x ∈ toCoords '' s,
    HasFDerivWithinAt (moebiusCoords γ) ((LinearMap.toContinuousLinearMap
      (congrSym (denom γ (ofSymCoords x))⁻¹)).restrictScalars ℝ) (toCoords '' s) x := by
  rintro _ ⟨τ, -, rfl⟩
  refine ((hasFDerivAt_moebiusCoords _ γ ?_).restrictScalars ℝ).hasFDerivWithinAt
  rw [ofSymCoords_toCoords]
  exact isUnit_denom γ τ

private lemma injOn_moebiusCoords : InjOn (moebiusCoords γ) (toCoords '' s) := by
  rintro _ ⟨τ, -, rfl⟩ _ ⟨τ', -, rfl⟩ hττ'
  rw [← toCoords_smul, ← toCoords_smul] at hττ'
  rw [MulAction.injective γ (toCoords_injective hττ')]

variable {s}

lemma measurableSet_smul (hs : MeasurableSet s) : MeasurableSet (γ • s) := by
  rw [← measurableEmbedding_toCoords.measurableSet_image, image_toCoords_smul]
  exact measurable_image_of_fderivWithin (measurableEmbedding_toCoords.measurableSet_image.mpr hs)
    (hasFDerivWithinAt_moebiusCoords γ s) (injOn_moebiusCoords γ s)

lemma measurable_symplectic_smul : Measurable fun τ : SiegelUpperHalfSpace l ↦ γ • τ :=
  fun _ hs ↦ by
    rw [preimage_smul]
    exact measurableSet_smul γ⁻¹ hs

/-- **The measure `det(Y)^{-g-1} dX dY` on the Siegel upper half-space is invariant under
`Sp(2g, ℝ)`**: by the change of variables formula, since `τ ↦ γτ` has real Jacobian
`|det(cτ + d)|^{-2g-2}` (`SiegelUpperHalfSpace.hasFDerivAt_moebiusCoords`,
`SiegelUpperHalfSpace.det_congrSym`) and `det Im(γτ) = det(Im τ) |det(cτ + d)|⁻²`
(`SiegelUpperHalfSpace.det_im_smul`). -/
lemma invariantMeasure_smul (hs : MeasurableSet s) :
    invariantMeasure l (γ • s) = invariantMeasure l s := by
  have hs' : MeasurableSet (toCoords '' s) :=
    measurableEmbedding_toCoords.measurableSet_image.mpr hs
  rw [invariantMeasure_apply, invariantMeasure_apply, image_toCoords_smul,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs'
      (hasFDerivWithinAt_moebiusCoords γ s) (injOn_moebiusCoords γ s)]
  refine setLIntegral_congr_fun hs' ?_
  rintro _ ⟨τ, -, rfl⟩
  dsimp only
  rw [det_congrSym_restrictScalars, ofSymCoords_toCoords, jacobian_mul_coordDensity]

instance :
    SMulInvariantMeasure (symplecticGroup l ℝ) (SiegelUpperHalfSpace l) (invariantMeasure l) :=
  ⟨fun γ _ hs ↦ by rw [preimage_smul, invariantMeasure_smul _ hs]⟩

end SiegelUpperHalfSpace
