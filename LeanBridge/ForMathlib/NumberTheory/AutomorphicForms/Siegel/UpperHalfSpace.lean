import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.Order
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SymplecticGroup
import TauCeti.Analysis.Matrix.PosDef

/-!
# The Siegel upper half-space

The Siegel upper half-space `ℋ_g` of complex symmetric `g × g` matrices with positive definite
imaginary part, the action `τ ↦ (aτ + b)(cτ + d)⁻¹` of the real symplectic group on it, and
holomorphic functions on it. The action is well defined because, for `γ ∈ Sp(2g, ℝ)`,
`(cτ + d)ᴴ (aτ + b) - (aτ + b)ᴴ (cτ + d) = τ - τᴴ = 2i Im τ`, which makes `cτ + d` invertible and
`Im(γτ) = (cτ + d)⁻ᴴ (Im τ) (cτ + d)⁻¹`. Mathlib's `Matrix.symplecticGroup` is defined with
`J = (0, -1; 1, 0)`, the negative of the LMFDB's `J`, which gives the same group.

## Main definitions

* `SiegelUpperHalfSpace` (LMFDB `mf.siegel.halfspace`).
* `SiegelUpperHalfSpace.denom`: the automorphy factor `cτ + d`, and `SiegelUpperHalfSpace.denomGL`
  the same in `GL(g, ℂ)`.
* The instance `MulAction (Matrix.symplecticGroup l ℝ) (SiegelUpperHalfSpace l)`.
* `SiegelUpperHalfSpace.IsHolomorphic`: holomorphy of a vector-valued function on `ℋ_g`.

## Main results

* `Matrix.posDef_map_ofReal_iff`: a real matrix is positive definite exactly when it is as a
  complex matrix.
* `SiegelUpperHalfSpace.transpose_denom_mul_num_sub` and
  `SiegelUpperHalfSpace.conjTranspose_denom_mul_num_sub`: the symplectic relation in the forms
  `(cτ + d)ᵀ (aτ + b) - (aτ + b)ᵀ (cτ + d) = τ - τᵀ` and
  `(cτ + d)ᴴ (aτ + b) - (aτ + b)ᴴ (cτ + d) = τ - τᴴ`.
* `SiegelUpperHalfSpace.isUnit_denom`: `cτ + d` is invertible for `τ ∈ ℋ_g`.
* `SiegelUpperHalfSpace.denom_mul`: the cocycle relation of the automorphy factor.
-/

open Matrix Complex
open scoped ComplexOrder

variable {l : Type*} [Fintype l] [DecidableEq l]

namespace Matrix

variable {Y : Matrix l l ℝ}

omit [DecidableEq l] in
private lemma star_dotProduct_map_ofReal_mulVec (hY : Y.IsHermitian) (v : l → ℂ) :
    star v ⬝ᵥ (Y.map ((↑) : ℝ → ℂ) *ᵥ v) = (((fun i ↦ (v i).re) ⬝ᵥ (Y *ᵥ fun i ↦ (v i).re) +
      (fun i ↦ (v i).im) ⬝ᵥ (Y *ᵥ fun i ↦ (v i).im) : ℝ) : ℂ) := by
  have hs : ∀ i j, Y j i = Y i j := fun i j ↦ by simpa using hY.apply i j
  apply Complex.ext
  · simp only [dotProduct, mulVec, Pi.star_apply, map_apply, Finset.mul_sum, re_sum, ofReal_re,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp
  · simp only [dotProduct, mulVec, Pi.star_apply, map_apply, Finset.mul_sum, im_sum, ofReal_im]
    have h : ∀ x i, (star (v x) * (↑(Y x i) * v i)).im =
        Y x i * ((v x).re * (v i).im) - Y i x * ((v i).re * (v x).im) := fun x i ↦ by
      rw [hs x i]
      simp
      ring1
    simp only [h, Finset.sum_sub_distrib]
    rw [Finset.sum_comm, sub_self]

omit [DecidableEq l] in
/-- A real matrix is positive definite exactly when it is positive definite as a complex
matrix. -/
lemma posDef_map_ofReal_iff : (Y.map ((↑) : ℝ → ℂ)).PosDef ↔ Y.PosDef := by
  have hH : (Y.map ((↑) : ℝ → ℂ)).IsHermitian ↔ Y.IsHermitian := by
    rw [IsHermitian, IsHermitian, ← conjTranspose_map _ fun r ↦ (conj_ofReal r).symm,
      (map_injective ofReal_injective).eq_iff]
  rw [posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec, hH]
  refine and_congr_right fun hY ↦ ⟨fun h x hx ↦ ?_, fun h v hv ↦ ?_⟩
  · have hx' : (fun i ↦ (x i : ℂ)) ≠ 0 :=
      fun h0 ↦ hx <| funext fun i ↦ ofReal_injective <| congrFun h0 i
    simpa [star_dotProduct_map_ofReal_mulVec hY] using h hx'
  · have hq : ∀ w : l → ℝ, 0 ≤ w ⬝ᵥ (Y *ᵥ w) := fun w ↦ by
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · simpa using (h hw).le
    rw [star_dotProduct_map_ofReal_mulVec hY, zero_lt_real]
    rcases eq_or_ne (fun i ↦ (v i).re) 0 with ha | ha
    · have hb : (fun i ↦ (v i).im) ≠ 0 :=
        fun hb ↦ hv <| funext fun i ↦ Complex.ext (congrFun ha i) (congrFun hb i)
      exact add_pos_of_nonneg_of_pos (hq _) (by simpa using h hb)
    · exact add_pos_of_pos_of_nonneg (by simpa using h ha) (hq _)

end Matrix

variable (l) in
/-- The **Siegel upper half-space** `ℋ_g` (LMFDB `mf.siegel.halfspace`) of degree `g = |l|`: the
complex symmetric `g × g` matrices `τ` whose imaginary part `Im τ` is positive definite. -/
@[ext]
structure SiegelUpperHalfSpace where
  /-- The underlying complex matrix. -/
  val : Matrix l l ℂ
  transpose_val : valᵀ = val
  posDef_im : (val.map im).PosDef

namespace SiegelUpperHalfSpace

variable (γ γ' : symplecticGroup l ℝ) (M X Y : Matrix l l ℂ)

/-- The numerator `aM + b` of the action of `γ = (a, b; c, d) ∈ Sp(2g, ℝ)` on a matrix `M`. -/
noncomputable def num : Matrix l l ℂ :=
  (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁.map ofReal * M +
    (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₂.map ofReal

/-- The denominator `cM + d` of the action of `γ = (a, b; c, d) ∈ Sp(2g, ℝ)` on a matrix `M`, the
automorphy factor of Siegel modular forms. -/
noncomputable def denom : Matrix l l ℂ :=
  (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁.map ofReal * M +
    (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂.map ofReal

private lemma map_mul_fromRows : (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).map ofReal * fromRows M 1 =
    fromRows (num γ M) (denom γ M) := by
  conv_lhs => rw [← fromBlocks_toBlocks (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ)]
  rw [fromBlocks_map, fromBlocks_mul_fromRows]
  simp [num, denom]

private lemma transpose_map_mul_J_mul_map : ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).map ofReal)ᵀ * J l ℂ *
    (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).map ofReal = J l ℂ := by
  have h : ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * J l ℝ * γ).map ofRealHom = (J l ℝ).map ofRealHom :=
    congrArg (Matrix.map · ofRealHom) (SymplecticGroup.mem_iff'.mp γ.2)
  rw [Matrix.map_mul, Matrix.map_mul, map_J, transpose_map] at h
  exact h

private lemma fromRows_transpose_mul_J_mul :
    (fromRows X Y)ᵀ * J l ℂ * fromRows X Y = Yᵀ * X - Xᵀ * Y := by
  rw [transpose_fromRows, J, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

private lemma fromRows_conjTranspose_mul_J_mul :
    (fromRows X Y)ᴴ * J l ℂ * fromRows X Y = Yᴴ * X - Xᴴ * Y := by
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, J, fromCols_mul_fromBlocks,
    fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

omit [DecidableEq l] in
private lemma mul_mul_mul_mul_assoc (A : Matrix l (l ⊕ l) ℂ) (B C D : Matrix (l ⊕ l) (l ⊕ l) ℂ)
    (E : Matrix (l ⊕ l) l ℂ) : A * B * C * (D * E) = A * (B * C * D) * E := by
  simp only [Matrix.mul_assoc]

/-- The symplectic relation `γᵀ J γ = J`, written for a complex matrix `M` stacked over the
identity: `(cM + d)ᵀ (aM + b) - (aM + b)ᵀ (cM + d) = M - Mᵀ`. -/
lemma transpose_denom_mul_num_sub : (denom γ M)ᵀ * num γ M - (num γ M)ᵀ * denom γ M = M - Mᵀ := by
  rw [← fromRows_transpose_mul_J_mul, ← map_mul_fromRows, transpose_mul, mul_mul_mul_mul_assoc,
    transpose_map_mul_J_mul_map, fromRows_transpose_mul_J_mul]
  simp

/-- The symplectic relation `γᵀ J γ = J`, conjugated: for every complex matrix `M`,
`(cM + d)ᴴ (aM + b) - (aM + b)ᴴ (cM + d) = M - Mᴴ`, since `γ` is real. -/
lemma conjTranspose_denom_mul_num_sub :
    (denom γ M)ᴴ * num γ M - (num γ M)ᴴ * denom γ M = M - Mᴴ := by
  have h : ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).map ofReal)ᴴ =
      ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).map ofReal)ᵀ := by
    rw [← conjTranspose_map _ fun r ↦ (conj_ofReal r).symm, conjTranspose_eq_transpose_of_trivial,
      transpose_map]
  rw [← fromRows_conjTranspose_mul_J_mul, ← map_mul_fromRows, conjTranspose_mul,
    mul_mul_mul_mul_assoc, h, transpose_map_mul_J_mul_map, fromRows_conjTranspose_mul_J_mul]
  simp

variable {M} in
omit [Fintype l] [DecidableEq l] in
private lemma sub_conjTranspose_of_transpose_eq (hM : Mᵀ = M) :
    M - Mᴴ = (2 * I) • (M.map im).map ofReal := by
  ext i j
  have h : M j i = M i j := by rw [← transpose_apply M i j, hM]
  simp only [Matrix.sub_apply, conjTranspose_apply, h, Matrix.smul_apply, map_apply]
  rw [star_def, sub_conj]
  push_cast
  ring1

variable (τ : SiegelUpperHalfSpace l)

/-- **The automorphy factor `cτ + d` is invertible** for `τ` in the Siegel upper half-space: if
`(cτ + d) v = 0`, the symplectic relation gives `vᴴ (Im τ) v = 0`, so `v = 0`. -/
lemma isUnit_denom : IsUnit (denom γ τ.val) := by
  rw [← mulVec_injective_iff_isUnit]
  have key : ∀ u, denom γ τ.val *ᵥ u = 0 → u = 0 := fun u hu ↦ by
    by_contra hne
    have hpos : 0 < star u ⬝ᵥ ((τ.val.map im).map ofReal *ᵥ u) :=
      (posDef_map_ofReal_iff.mpr τ.posDef_im).dotProduct_mulVec_pos hne
    have h0 : star u ⬝ᵥ ((τ.val - τ.valᴴ) *ᵥ u) = 0 := by
      rw [← conjTranspose_denom_mul_num_sub γ, sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
        ← mulVec_mulVec, hu, mulVec_zero, dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hu,
        star_zero, zero_dotProduct, sub_zero]
    rw [sub_conjTranspose_of_transpose_eq τ.transpose_val, smul_mulVec, dotProduct_smul,
      smul_eq_mul] at h0
    exact hpos.ne' <| (mul_eq_zero.mp h0).resolve_left <| by simp
  exact fun v w hvw ↦ sub_eq_zero.mp <| key _ <| by rw [mulVec_sub, hvw, sub_self]

lemma isUnit_det_denom : IsUnit (denom γ τ.val).det :=
  (isUnit_iff_isUnit_det _).mp <| isUnit_denom γ τ

lemma transpose_num_mul_inv_denom :
    (num γ τ.val * (denom γ τ.val)⁻¹)ᵀ = num γ τ.val * (denom γ τ.val)⁻¹ := by
  have h : (num γ τ.val)ᵀ * denom γ τ.val = (denom γ τ.val)ᵀ * num γ τ.val := by
    rw [eq_comm, ← sub_eq_zero, transpose_denom_mul_num_sub, τ.transpose_val, sub_self]
  rw [transpose_mul, transpose_nonsing_inv]
  conv_lhs => rw [← mul_nonsing_inv_cancel_right _ (num γ τ.val)ᵀ (isUnit_det_denom γ τ), h,
    Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ <| by
      rw [det_transpose]
      exact isUnit_det_denom γ τ]

lemma posDef_im_num_mul_inv_denom : ((num γ τ.val * (denom γ τ.val)⁻¹).map im).PosDef := by
  have e : (denom γ τ.val)⁻¹ᴴ * (denom γ τ.val)ᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv _ (isUnit_det_denom γ τ), conjTranspose_one]
  have h : (2 * I) • ((num γ τ.val * (denom γ τ.val)⁻¹).map im).map ofReal =
      (2 * I) • ((denom γ τ.val)⁻¹ᴴ * (τ.val.map im).map ofReal * (denom γ τ.val)⁻¹) := by
    rw [← sub_conjTranspose_of_transpose_eq (transpose_num_mul_inv_denom γ τ), ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← sub_conjTranspose_of_transpose_eq τ.transpose_val,
      ← conjTranspose_denom_mul_num_sub γ τ.val]
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, e, Matrix.one_mul,
      mul_nonsing_inv_cancel_right _ _ (isUnit_det_denom γ τ), conjTranspose_mul]
  rw [← posDef_map_ofReal_iff, smul_right_injective _ (by simp) h]
  exact (posDef_map_ofReal_iff.mpr τ.posDef_im).conjTranspose_mul_mul_same <|
    mulVec_injective_of_isUnit <| isUnit_nonsing_inv_iff.mpr <| isUnit_denom γ τ

noncomputable instance : SMul (symplecticGroup l ℝ) (SiegelUpperHalfSpace l) where
  smul γ τ := ⟨num γ τ.val * (denom γ τ.val)⁻¹, transpose_num_mul_inv_denom γ τ,
    posDef_im_num_mul_inv_denom γ τ⟩

lemma val_smul : (γ • τ).val = num γ τ.val * (denom γ τ.val)⁻¹ :=
  rfl

private lemma fromRows_num_denom_mul : fromRows (num (γ * γ') τ.val) (denom (γ * γ') τ.val) =
    fromRows (num γ (γ' • τ).val * denom γ' τ.val) (denom γ (γ' • τ).val * denom γ' τ.val) := by
  have h : fromRows (num γ' τ.val) (denom γ' τ.val) = fromRows (γ' • τ).val 1 * denom γ' τ.val := by
    rw [fromRows_mul, Matrix.one_mul, val_smul,
      nonsing_inv_mul_cancel_right _ _ (isUnit_det_denom γ' τ)]
  have hm : ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) * γ').map ofReal =
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).map ofReal * (γ' : Matrix (l ⊕ l) (l ⊕ l) ℝ).map ofReal :=
    Matrix.map_mul (f := ofRealHom)
  rw [← map_mul_fromRows, Submonoid.coe_mul, hm, Matrix.mul_assoc, map_mul_fromRows, h,
    ← Matrix.mul_assoc, map_mul_fromRows, fromRows_mul]

lemma num_mul : num (γ * γ') τ.val = num γ (γ' • τ).val * denom γ' τ.val :=
  (fromRows_inj (fromRows_num_denom_mul γ γ' τ)).1

/-- **The cocycle relation** `denom(γγ', τ) = denom(γ, γ'τ) denom(γ', τ)` of the automorphy factor
`cτ + d`. -/
lemma denom_mul : denom (γ * γ') τ.val = denom γ (γ' • τ).val * denom γ' τ.val :=
  (fromRows_inj (fromRows_num_denom_mul γ γ' τ)).2

noncomputable instance : MulAction (symplecticGroup l ℝ) (SiegelUpperHalfSpace l) where
  one_smul τ := SiegelUpperHalfSpace.ext <| by
    rw [val_smul, num, denom, OneMemClass.coe_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁,
      toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp
  mul_smul γ γ' τ := SiegelUpperHalfSpace.ext <| by
    rw [val_smul, num_mul, denom_mul, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ _ (denom γ (γ' • τ).val)⁻¹, mul_nonsing_inv _ (isUnit_det_denom γ' τ),
      Matrix.one_mul, ← val_smul]

/-- The automorphy factor `cτ + d` of `γ = (a, b; c, d) ∈ Sp(2g, ℝ)` at `τ ∈ ℋ_g`, as an element
of `GL(g, ℂ)`. -/
noncomputable def denomGL : GL l ℂ :=
  (isUnit_denom γ τ).unit

@[simp]
lemma coe_denomGL : (denomGL γ τ : Matrix l l ℂ) = denom γ τ.val :=
  rfl

lemma denomGL_mul : denomGL (γ * γ') τ = denomGL γ (γ' • τ) * denomGL γ' τ :=
  Units.ext <| denom_mul γ γ' τ

variable (u v : SiegelUpperHalfSpace l → ℂ) (Z : l → l → ℂ) (c : ℂ)

/-- The symmetrisation `(Z + Zᵀ) / 2` of a square complex matrix given by its entries. -/
noncomputable def symmetrize : Matrix l l ℂ :=
  (2⁻¹ : ℂ) • (of Z + (of Z)ᵀ)

omit [Fintype l] [DecidableEq l] in
lemma transpose_symmetrize : (symmetrize Z)ᵀ = symmetrize Z := by
  rw [symmetrize, transpose_smul, transpose_add, transpose_transpose, add_comm]

variable (l) in
/-- The square complex matrices whose symmetrisation lies in the Siegel upper half-space. -/
def symmetrizePreimage : Set (l → l → ℂ) :=
  {Z | ((symmetrize Z).map im).PosDef}

omit [DecidableEq l] in
lemma isOpen_symmetrizePreimage : IsOpen (symmetrizePreimage l) := by
  have h : symmetrizePreimage l = (fun Z ↦ (symmetrize Z).map im) ⁻¹'
      {M | ∀ x : l → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x} := by
    ext Z
    have hH : ((symmetrize Z).map im).IsHermitian := by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, ← transpose_map,
        transpose_symmetrize]
    simp only [symmetrizePreimage, Set.mem_ofPred_eq, Set.mem_preimage,
      posDef_iff_dotProduct_mulVec, star_trivial, hH, true_and]
  rw [h]
  refine TauCeti.isOpen_setOfPred_dotProduct_mulVec_pos.preimage <|
    continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  simp only [map_apply]
  fun_prop

open scoped Classical in
/-- The extension `Z ↦ u((Z + Zᵀ) / 2)` of a complex function `u` on the Siegel upper half-space
to the square complex matrices whose symmetrisation lies in it, and `0` elsewhere. -/
noncomputable def extend : ℂ :=
  if h : ((symmetrize Z).map im).PosDef then u ⟨symmetrize Z, transpose_symmetrize Z, h⟩ else 0

omit [Fintype l] [DecidableEq l] in
private lemma extend_add : extend (u + v) = extend u + extend v := by
  ext Z
  simp only [extend, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype l] [DecidableEq l] in
private lemma extend_smul : extend (c • u) = c • extend u := by
  ext Z
  simp only [extend, Pi.smul_apply]
  split_ifs <;> simp

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : SiegelUpperHalfSpace l → V}

variable (f) in
/-- A function `f : ℋ_g → V` to a complex vector space is **holomorphic** if, for every linear
form `φ` on `V`, `φ ∘ f` is holomorphic in the `g(g + 1) / 2` entries `τ_ij` (`i ≤ j`) of `τ`:
`Z ↦ φ(f((Z + Zᵀ) / 2))` is complex differentiable on the open set (`isOpen_symmetrizePreimage`)
of the square matrices `Z` whose symmetrisation lies in `ℋ_g`. For finite-dimensional `V` this
is holomorphy of the coordinates of `f`. -/
def IsHolomorphic : Prop :=
  ∀ φ : Module.Dual ℂ V, DifferentiableOn ℂ (extend (φ ∘ f)) (symmetrizePreimage l)

omit [Fintype l] [DecidableEq l] in
lemma isHolomorphic_zero : IsHolomorphic (0 : SiegelUpperHalfSpace l → V) := fun φ ↦ by
  have h : extend (φ ∘ (0 : SiegelUpperHalfSpace l → V)) = 0 := by
    simpa using extend_smul (0 : SiegelUpperHalfSpace l → ℂ) 0
  rw [h]
  exact differentiableOn_const 0

omit [DecidableEq l] in
lemma IsHolomorphic.add (hf : IsHolomorphic f) (hg : IsHolomorphic g) :
    IsHolomorphic (f + g) := fun φ ↦ by
  have h : φ ∘ (f + g) = φ ∘ f + φ ∘ g := funext fun τ ↦ map_add φ (f τ) (g τ)
  rw [h, extend_add]
  exact (hf φ).add (hg φ)

omit [DecidableEq l] in
lemma IsHolomorphic.const_smul (hf : IsHolomorphic f) : IsHolomorphic (c • f) := fun φ ↦ by
  have h : φ ∘ (c • f) = c • (φ ∘ f) := funext fun τ ↦ map_smul φ c (f τ)
  rw [h, extend_smul]
  exact (hf φ).const_smul c

end SiegelUpperHalfSpace
