import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ProperDiscontinuity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Group.ProperlyDiscontinuous
import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus

/-!
# Fundamental domains of arithmetic subgroups on the Siegel upper half-space

An arithmetic subgroup `Γ` of `Sp(2g, ℚ)` has a measurable fundamental domain on the Siegel
upper half-space `ℋ_g`, in every degree, for the invariant measure `det(Y)^{-g-1} dX dY`. It acts
properly discontinuously (`SiegelUpperHalfSpace.properlyDiscontinuousSMul_transformationGroup`), so
by the general construction of Tau Ceti it suffices that the points with a nontrivial stabilizer
form a null set. The fixed points of `γ = (a, b; c, d)` satisfy `aZ + b = Z(cZ + d)`, whose real and
imaginary parts are polynomial equations in the coordinates of `Z = X + iY`. So they form a null
set, unless these polynomials vanish identically, in which case `γ` acts trivially.

## Main results

* `SiegelUpperHalfSpace.exists_eq_smul_one_of_forall_smul_eq`: an element of `Sp(2g, ℝ)` acting
  trivially is a scalar matrix.
* `SiegelUpperHalfSpace.invariantMeasure_setOf_smul_eq_eq_zero`: an element of `Sp(2g, ℝ)` acting
  nontrivially has a null set of fixed points.
* `SiegelUpperHalfSpace.invariantMeasure_setOf_eval_eq_zero`: a nonzero polynomial in the real
  coordinates vanishes on a null set.
* `SiegelUpperHalfSpace.exists_isFundamentalDomain`: an arithmetic subgroup has a fundamental
  domain.
* `SiegelUpperHalfSpace.isFundamentalDomain_fundamentalDomain`: the chosen fundamental domain
  `SiegelUpperHalfSpace.fundamentalDomain` of an arithmetic subgroup is one.
-/

open Complex Matrix MeasureTheory MvPolynomial Set

namespace SiegelUpperHalfSpace

variable {l : Type*}

private lemma val_eq_map_re_add (τ : SiegelUpperHalfSpace l) :
    τ.val = (τ.val.map re).map ofReal + I • (τ.val.map im).map ofReal := by
  ext i j
  simp [mul_comm I]

private lemma map_add_smul_eq_zero_iff {E F : Matrix l l ℝ} :
    E.map ofReal + I • F.map ofReal = 0 ↔ E = 0 ∧ F = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h₁ (i j : l) : ((E i j : ℂ) + I * (F i j : ℂ)) = 0 := congrFun (congrFun h i) j
    have h₂ (i j : l) : ((E i j : ℂ) + (F i j : ℂ) * I) = 0 := by
      rw [mul_comm]
      exact h₁ i j
    refine ⟨?_, ?_⟩ <;> ext i j
    · simpa using congrArg re (h₂ i j)
    · simpa using congrArg im (h₂ i j)
  · rw [h.1, h.2]
    ext i j
    simp

variable [DecidableEq l] in
/-- The point `X + i t` of `ℋ_g`, for a real symmetric `X` and `t > 0`. -/
private noncomputable def shiftPoint (X : Matrix l l ℝ) (hX : Xᵀ = X) {t : ℝ} (ht : 0 < t) :
    SiegelUpperHalfSpace l where
  val := X.map ofReal + ((t : ℂ) * I) • 1
  transpose_val := by
    rw [transpose_add, transpose_smul, transpose_one, ← transpose_map, hX]
  posDef_im := by
    have h : (X.map ofReal + ((t : ℂ) * I) • (1 : Matrix l l ℂ)).map im = t • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [h]
    exact PosDef.one.smul ht

variable [DecidableEq l] in
private lemma map_re_shiftPoint (X : Matrix l l ℝ) (hX : Xᵀ = X) {t : ℝ} (ht : 0 < t) :
    (shiftPoint X hX ht).val.map re = X := by
  ext i j
  by_cases hij : i = j <;> simp [shiftPoint, hij]

variable [DecidableEq l] in
private lemma map_im_shiftPoint (X : Matrix l l ℝ) (hX : Xᵀ = X) {t : ℝ} (ht : 0 < t) :
    (shiftPoint X hX ht).val.map im = t • 1 := by
  ext i j
  by_cases hij : i = j <;> simp [shiftPoint, hij]

variable [Fintype l]

/-- The real coordinates `(Re h, Im h)` of the coordinates `h : Sym2 l → ℂ` of `ℋ_g`. -/
private noncomputable def realCoords : (Sym2 l → ℂ) ≃L[ℝ] (Sym2 l ⊕ Sym2 l → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun h := Sum.elim (fun s ↦ (h s).re) fun s ↦ (h s).im
      invFun x s := ⟨x (.inl s), x (.inr s)⟩
      map_add' h h' := by
        ext (s | s) <;> simp
      map_smul' c h := by
        ext (s | s) <;> simp
      left_inv h := by
        ext s
        simp
      right_inv x := by
        ext (s | s) <;> simp }

private lemma volume_preimage_realCoords {A : Set (Sym2 l ⊕ Sym2 l → ℝ)} (hA : volume A = 0) :
    volume (realCoords (l := l) ⁻¹' A) = 0 := by
  have : (volume.map (realCoords (l := l))).IsAddHaarMeasure :=
    (realCoords (l := l)).isAddHaarMeasure_map volume
  have hac : (volume.map (realCoords (l := l))) ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have e : volume.map (realCoords (l := l)) A = volume (realCoords (l := l) ⁻¹' A) :=
    (realCoords (l := l)).toHomeomorph.toMeasurableEquiv.map_apply A
  rw [← e]
  exact hac hA

/-- The matrix with polynomial entries the real parts of the coordinates. -/
private noncomputable def polyX : Matrix l l (MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ) :=
  of fun i j ↦ X (.inl s(i, j))

/-- The matrix with polynomial entries the imaginary parts of the coordinates. -/
private noncomputable def polyY : Matrix l l (MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ) :=
  of fun i j ↦ X (.inr s(i, j))

/-- A real matrix as a matrix of constant polynomials. -/
private noncomputable def polyC (A : Matrix l l ℝ) :
    Matrix l l (MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ) :=
  A.map C

variable (a b c d X₀ Y₀ : Matrix l l ℝ)

/-- The real part `aX + b - X c X + Y c Y - X d` of `aZ + b - Z(cZ + d)`, for `Z = X + iY`. -/
private def realPart : Matrix l l ℝ :=
  a * X₀ + b - X₀ * (c * X₀) + Y₀ * (c * Y₀) - X₀ * d

/-- The imaginary part `aY - X c Y - Y c X - Y d` of `aZ + b - Z(cZ + d)`, for `Z = X + iY`. -/
private def imagPart : Matrix l l ℝ :=
  a * Y₀ - X₀ * (c * Y₀) - Y₀ * (c * X₀) - Y₀ * d

private lemma fixedEquation_eq : a.map ofReal * (X₀.map ofReal + I • Y₀.map ofReal) + b.map ofReal -
    (X₀.map ofReal + I • Y₀.map ofReal) *
      (c.map ofReal * (X₀.map ofReal + I • Y₀.map ofReal) + d.map ofReal) =
    (realPart a b c d X₀ Y₀).map ofReal + I • (imagPart a c d X₀ Y₀).map ofReal := by
  have h (A B : Matrix l l ℝ) : (A * B).map ofReal = A.map ofReal * B.map ofReal :=
    Matrix.map_mul (f := ofRealHom)
  have hadd (A B : Matrix l l ℝ) : (A + B).map ofReal = A.map ofReal + B.map ofReal :=
    Matrix.map_add _ (by simp) _ _
  have hsub (A B : Matrix l l ℝ) : (A - B).map ofReal = A.map ofReal - B.map ofReal :=
    Matrix.map_sub _ (by simp) _ _
  simp only [realPart, imagPart, h, hadd, hsub]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul,
    I_mul_I]
  module

variable (x : Sym2 l ⊕ Sym2 l → ℝ)

/-- The real matrix of the real parts given by real coordinates. -/
private def matX : Matrix l l ℝ :=
  of fun i j ↦ x (.inl s(i, j))

/-- The real matrix of the imaginary parts given by real coordinates. -/
private def matY : Matrix l l ℝ :=
  of fun i j ↦ x (.inr s(i, j))

private lemma matX_realCoords (τ : SiegelUpperHalfSpace l) :
    matX (realCoords τ.toCoords) = τ.val.map re := by
  ext i j
  have e : τ.toCoords s(i, j) = τ.val i j :=
    congrFun (congrFun (ofSymCoords_toCoords τ) i) j
  simp [matX, realCoords, e]

private lemma matY_realCoords (τ : SiegelUpperHalfSpace l) :
    matY (realCoords τ.toCoords) = τ.val.map im := by
  ext i j
  have e : τ.toCoords s(i, j) = τ.val i j :=
    congrFun (congrFun (ofSymCoords_toCoords τ) i) j
  simp [matY, realCoords, e]

variable [DecidableEq l]

private lemma invariantMeasure_eq_zero_of_volume {A : Set (SiegelUpperHalfSpace l)}
    (h : volume (toCoords '' A) = 0) : invariantMeasure l A = 0 := by
  rw [invariantMeasure_apply]
  exact setLIntegral_measure_zero _ _ h

private lemma mapMatrix_polyX : (MvPolynomial.eval x).mapMatrix (polyX (l := l)) = matX x := by
  ext i j
  simp [polyX, matX]

private lemma mapMatrix_polyY : (MvPolynomial.eval x).mapMatrix (polyY (l := l)) = matY x := by
  ext i j
  simp [polyY, matY]

private lemma mapMatrix_polyC (A : Matrix l l ℝ) :
    (MvPolynomial.eval x).mapMatrix (polyC A) = A := by
  ext i j
  simp [polyC]

/-- The polynomial matrix whose value is the real part `realPart`. -/
private noncomputable def polyReal : Matrix l l (MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ) :=
  polyC a * polyX + polyC b - polyX * (polyC c * polyX) + polyY * (polyC c * polyY) -
    polyX * polyC d

/-- The polynomial matrix whose value is the imaginary part `imagPart`. -/
private noncomputable def polyImag : Matrix l l (MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ) :=
  polyC a * polyY - polyX * (polyC c * polyY) - polyY * (polyC c * polyX) - polyY * polyC d

private lemma mapMatrix_polyReal :
    (MvPolynomial.eval x).mapMatrix (polyReal a b c d) = realPart a b c d (matX x) (matY x) := by
  simp only [polyReal, realPart, map_add, map_sub, map_mul, mapMatrix_polyX, mapMatrix_polyY,
    mapMatrix_polyC]

private lemma mapMatrix_polyImag :
    (MvPolynomial.eval x).mapMatrix (polyImag a c d) = imagPart a c d (matX x) (matY x) := by
  simp only [polyImag, imagPart, map_sub, map_mul, mapMatrix_polyX, mapMatrix_polyY,
    mapMatrix_polyC]

variable (γ : symplecticGroup l ℝ) (τ : SiegelUpperHalfSpace l)

private lemma num_sub_mul_denom : num γ τ.val - τ.val * denom γ τ.val =
    (realPart (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₂
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂
        (τ.val.map re) (τ.val.map im)).map ofReal +
    I • (imagPart (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂
        (τ.val.map re) (τ.val.map im)).map ofReal := by
  rw [← fixedEquation_eq, num, denom, ← val_eq_map_re_add]

private lemma smul_eq_iff_num_eq : γ • τ = τ ↔ num γ τ.val = τ.val * denom γ τ.val := by
  rw [SiegelUpperHalfSpace.ext_iff, val_smul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h₁ : num γ τ.val * (denom γ τ.val)⁻¹ * denom γ τ.val = τ.val * denom γ τ.val :=
      congrArg (· * denom γ τ.val) h
    rwa [nonsing_inv_mul_cancel_right _ _ (isUnit_det_denom γ τ)] at h₁
  · rw [h, mul_nonsing_inv_cancel_right _ _ (isUnit_det_denom γ τ)]

private lemma smul_eq_iff_parts : γ • τ = τ ↔
    (realPart (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₂
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂
        (τ.val.map re) (τ.val.map im) = 0 ∧ imagPart (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂
        (τ.val.map re) (τ.val.map im) = 0) := by
  rw [smul_eq_iff_num_eq, ← sub_eq_zero, num_sub_mul_denom, map_add_smul_eq_zero_iff]

variable {γ}

private lemma apply_eq_zero_of_commute {a : Matrix l l ℝ}
    (ha : ∀ X : Matrix l l ℝ, Xᵀ = X → a * X = X * a) {i j : l} (hij : i ≠ j) : a i j = 0 := by
  have h₁ : (a * single j j 1 : Matrix l l ℝ) i j = (single j j 1 * a : Matrix l l ℝ) i j :=
    congrFun (congrFun (ha (single j j 1) (transpose_single j j 1)) i) j
  rwa [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hij, mul_one] at h₁

private lemma apply_eq_apply_of_commute {a : Matrix l l ℝ}
    (ha : ∀ X : Matrix l l ℝ, Xᵀ = X → a * X = X * a) {i j : l} (hij : i ≠ j) : a i i = a j j := by
  have hs : (single i j (1 : ℝ) + single j i 1)ᵀ = single i j 1 + single j i 1 := by
    rw [transpose_add, transpose_single, transpose_single, add_comm]
  have h₁ : (a * (single i j 1 + single j i 1) : Matrix l l ℝ) i j =
      ((single i j 1 + single j i 1) * a : Matrix l l ℝ) i j :=
    congrFun (congrFun (ha _ hs) i) j
  rwa [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.add_apply, mul_single_apply_same,
    mul_single_apply_of_ne _ _ _ _ _ hij.symm, single_mul_apply_same,
    single_mul_apply_of_ne _ _ _ _ _ hij, mul_one, one_mul, add_zero, add_zero] at h₁

/-- **An element of `Sp(2g, ℝ)` acting trivially on `ℋ_g` is a scalar matrix.** -/
lemma exists_eq_smul_one_of_forall_smul_eq (h : ∀ τ : SiegelUpperHalfSpace l, γ • τ = τ) :
    ∃ r : ℝ, (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) = r • 1 := by
  generalize ha : (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁ = a
  generalize hb : (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₂ = b
  generalize hc : (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ = c
  generalize hd : (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂ = d
  have hfix (X : Matrix l l ℝ) (hX : Xᵀ = X) {t : ℝ} (ht : 0 < t) :
      realPart a b c d X (t • 1) = 0 ∧ imagPart a c d X (t • 1) = 0 := by
    rw [← map_re_shiftPoint X hX ht, ← map_im_shiftPoint X hX ht, ← ha, ← hb, ← hc, ← hd]
    exact (smul_eq_iff_parts γ _).mp (h _)
  have h₁ : realPart a b c d 0 ((1 : ℝ) • 1) = 0 ∧ imagPart a c d 0 ((1 : ℝ) • 1) = 0 :=
    hfix 0 transpose_zero one_pos
  have h₂ : realPart a b c d 0 ((2 : ℝ) • 1) = 0 ∧ imagPart a c d 0 ((2 : ℝ) • 1) = 0 :=
    hfix 0 transpose_zero two_pos
  simp only [realPart, imagPart, Matrix.mul_zero, Matrix.zero_mul, sub_zero, zero_add, one_smul,
    Matrix.one_mul, Matrix.mul_one] at h₁ h₂
  have hc₀ : c = 0 := by
    ext i j
    have e₁ : (b + c) i j = (0 : Matrix l l ℝ) i j := congrFun (congrFun h₁.1 i) j
    have e₂ : (b + (2 : ℝ) • (1 : Matrix l l ℝ) * (c * (2 : ℝ) • 1)) i j = (0 : Matrix l l ℝ) i j :=
      congrFun (congrFun h₂.1 i) j
    simp only [Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_apply, smul_eq_mul] at e₁ e₂
    rw [Matrix.zero_apply]
    linarith
  have hb₀ : b = 0 := by
    rw [hc₀, add_zero] at h₁
    exact h₁.1
  have hd₀ : d = a := (sub_eq_zero.mp h₁.2).symm
  have hcomm (X : Matrix l l ℝ) (hX : Xᵀ = X) : a * X = X * a := by
    have h₃ : realPart a b c d X ((1 : ℝ) • 1) = 0 := (hfix X hX one_pos).1
    simp only [realPart, hb₀, hc₀, hd₀, Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at h₃
    exact sub_eq_zero.mp h₃
  have hfrom : (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) = fromBlocks a b c d := by
    rw [← ha, ← hb, ← hc, ← hd, fromBlocks_toBlocks]
  rcases isEmpty_or_nonempty l with hl | ⟨⟨i₀⟩⟩
  · exact ⟨0, by
      ext (i | i) <;> exact isEmptyElim i⟩
  refine ⟨a i₀ i₀, ?_⟩
  have ha₀ : a = a i₀ i₀ • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = i₀
      · simp [hi]
      · simpa using apply_eq_apply_of_commute hcomm hi
    · simpa [hij] using apply_eq_zero_of_commute hcomm hij
  rw [hfrom, hb₀, hc₀, hd₀, ← fromBlocks_one, fromBlocks_smul]
  simp only [smul_zero, ← ha₀]

/-- **An element of `Sp(2g, ℝ)` acting nontrivially has a null set of fixed points**: the equation
`aZ + b = Z(cZ + d)` of a fixed point `Z = X + iY` is polynomial in the real coordinates of `Z`, so
either some polynomial is nonzero, and its zero locus is null, or every point is fixed. -/
lemma invariantMeasure_setOf_smul_eq_eq_zero (hγ : ∃ τ : SiegelUpperHalfSpace l, γ • τ ≠ τ) :
    invariantMeasure l {τ | γ • τ = τ} = 0 := by
  let P : Matrix l l (MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ) :=
    polyReal (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₂
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂
  let Q : Matrix l l (MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ) :=
    polyImag (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂
  have hP (τ : SiegelUpperHalfSpace l) : (MvPolynomial.eval (realCoords τ.toCoords)).mapMatrix P =
      realPart (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₂
        (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂
          (τ.val.map re) (τ.val.map im) := by
    rw [mapMatrix_polyReal, matX_realCoords, matY_realCoords]
  have hQ (τ : SiegelUpperHalfSpace l) : (MvPolynomial.eval (realCoords τ.toCoords)).mapMatrix Q =
      imagPart (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁
        (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₂₂
          (τ.val.map re) (τ.val.map im) := by
    rw [mapMatrix_polyImag, matX_realCoords, matY_realCoords]
  have hnull {p : MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ} (hp : p ≠ 0)
      (hfix : ∀ τ : SiegelUpperHalfSpace l, γ • τ = τ →
        MvPolynomial.eval (realCoords τ.toCoords) p = 0) :
      invariantMeasure l {τ | γ • τ = τ} = 0 := by
    refine invariantMeasure_eq_zero_of_volume <| measure_mono_null ?_
      (volume_preimage_realCoords (volume_setOfPred_eval_eq_zero p hp))
    rintro _ ⟨τ, hτ, rfl⟩
    exact hfix τ hτ
  by_cases hP₀ : P = 0
  · by_cases hQ₀ : Q = 0
    · rcases hγ with ⟨τ, hτ⟩
      refine (hτ ?_).elim
      rw [smul_eq_iff_parts, ← hP τ, ← hQ τ, hP₀, hQ₀]
      simp
    · rcases Function.ne_iff.mp hQ₀ with ⟨i, hi⟩
      rcases Function.ne_iff.mp hi with ⟨j, hj⟩
      refine hnull hj fun τ hτ ↦ ?_
      exact congrFun (congrFun ((hQ τ).trans ((smul_eq_iff_parts γ τ).mp hτ).2) i) j
  · rcases Function.ne_iff.mp hP₀ with ⟨i, hi⟩
    rcases Function.ne_iff.mp hi with ⟨j, hj⟩
    refine hnull hj fun τ hτ ↦ ?_
    exact congrFun (congrFun ((hP τ).trans ((smul_eq_iff_parts γ τ).mp hτ).1) i) j

/-- **A nonzero polynomial in the real coordinates of `ℋ_g` vanishes on a null set**, for the
invariant measure. -/
lemma invariantMeasure_setOf_eval_eq_zero {p : MvPolynomial (Sym2 l ⊕ Sym2 l) ℝ} (hp : p ≠ 0) :
    invariantMeasure l {τ | MvPolynomial.eval
      (Sum.elim (fun s ↦ (τ.toCoords s).re) fun s ↦ (τ.toCoords s).im) p = 0} = 0 := by
  refine invariantMeasure_eq_zero_of_volume <| measure_mono_null ?_
    (volume_preimage_realCoords (volume_setOfPred_eval_eq_zero p hp))
  rintro _ ⟨τ, hτ, rfl⟩
  exact hτ

variable {Γ : Subgroup (symplecticGroup l ℚ)}

private lemma invariantMeasure_compl_freeLocus :
    invariantMeasure l ((TauCeti.freeLocus (transformationGroup Γ) (SiegelUpperHalfSpace l) :
      Set (SiegelUpperHalfSpace l))ᶜ) = 0 := by
  have hsub : ((TauCeti.freeLocus (transformationGroup Γ) (SiegelUpperHalfSpace l) :
      Set (SiegelUpperHalfSpace l))ᶜ) ⊆ ⋃ g : transformationGroup Γ, {τ | g ≠ 1 ∧ g • τ = τ} := by
    intro τ hτ
    have h₁ : MulAction.stabilizer (transformationGroup Γ) τ ≠ ⊥ := hτ
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp h₁ with ⟨⟨g, hg⟩, hne⟩
    exact mem_iUnion.mpr ⟨g, fun h ↦ hne (Subtype.ext h), hg⟩
  refine measure_mono_null hsub (measure_iUnion_null fun g ↦ ?_)
  rcases eq_or_ne g 1 with rfl | hg
  · simp
  have hsub₁ : {τ | g ≠ 1 ∧ g • τ = τ} ⊆ {τ : SiegelUpperHalfSpace l | g • τ = τ} :=
    fun τ hτ ↦ hτ.2
  refine measure_mono_null hsub₁ ?_
  rcases g with ⟨_, γ, hγ, rfl⟩
  refine invariantMeasure_setOf_smul_eq_eq_zero (γ := SymplecticGroup.map (algebraMap ℚ ℝ) γ) ?_
  by_contra hall
  push Not at hall
  exact hg <| Subtype.ext <| Equiv.ext hall

/-- **An arithmetic subgroup of `Sp(2g, ℚ)` has a fundamental domain on `ℋ_g`**, in every degree,
for the invariant measure `det(Y)^{-g-1} dX dY`. -/
lemma exists_isFundamentalDomain (hΓ : SymplecticGroup.IsArithmetic Γ) :
    ∃ F, IsFundamentalDomain (transformationGroup Γ) F (invariantMeasure l) := by
  have : ProperlyDiscontinuousSMul (transformationGroup Γ) (SiegelUpperHalfSpace l) :=
    properlyDiscontinuousSMul_transformationGroup hΓ
  rcases Measure.exists_isFundamentalDomain_of_properlyDiscontinuousSMul
    (G := transformationGroup Γ) (invariantMeasure l) invariantMeasure_compl_freeLocus with
      ⟨F, -, -, hF⟩
  exact ⟨F, hF⟩

/-- **The chosen fundamental domain of an arithmetic subgroup is a fundamental domain.** -/
lemma isFundamentalDomain_fundamentalDomain (hΓ : SymplecticGroup.IsArithmetic Γ) :
    IsFundamentalDomain (transformationGroup Γ) (fundamentalDomain Γ) (invariantMeasure l) := by
  rw [fundamentalDomain, dite_eq_left (exists_isFundamentalDomain hΓ)]
  exact (exists_isFundamentalDomain hΓ).choose_spec

end SiegelUpperHalfSpace
