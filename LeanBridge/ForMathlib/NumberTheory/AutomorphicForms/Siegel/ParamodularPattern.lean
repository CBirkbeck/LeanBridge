import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularLevelRaisingEta

/-!
# The entries of the elements of the paramodular group

Roberts and Schmidt (*On modular forms for the paramodular group*, in *Automorphic forms and zeta
functions*, World Scientific 2006, §2; https://sites.math.unt.edu/~schmidt/papers/arakawa.pdf)
describe the paramodular group `K(N)` by the shape of its elements: `K(N)` consists of the elements
of `Sp(4, ℚ)` of the form `[ℤ, Nℤ, ℤ, ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, Nℤ, ℤ, ℤ; Nℤ, Nℤ, Nℤ, ℤ]` in the
coordinates `(e₁, e₂, f₁, f₂)`. This file proves this for `SiegelUpperHalfSpace.paramodularLevel`,
which is defined as the conjugate by `δ = diag(1, 1, 1, N)` of the integral isometry group of
`T = (0, d; -d, 0)`, `d = diag(1, N)`.

## Main definitions

* `SiegelUpperHalfSpace.paramodularScale`: the matrix of the scales `1`, `N`, `N⁻¹` of the entries.
* `SiegelUpperHalfSpace.IsParamodularShape`: the shape of the elements of `K(N)`.

## Main results

* `SiegelUpperHalfSpace.isParamodularShape_of_mem`: the elements of `K(N)` have this shape.
* `SiegelUpperHalfSpace.mem_paramodularLevel_of_isParamodularShape`: an element of `Sp(4, ℚ)` of
  this shape lies in `K(N)`.
* `SiegelUpperHalfSpace.mem_heckeGammaOf_paramodularLevel_iff`: the same in `GL(4, ℚ)`.
-/

open Matrix

open SymplecticGroup (paramodularDelta paramodularDeltaInv paramodularForm)

namespace SiegelUpperHalfSpace

variable (N : ℕ+)

/-- The matrix `[1, N, 1, 1; 1, 1, 1, N⁻¹; 1, N, 1, 1; N, N, N, 1]` of the scales of the entries of
the elements of the paramodular group `K(N)`, in the coordinates `(e₁, e₂, f₁, f₂)`. -/
def paramodularScale : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  fromBlocks !![1, (N : ℚ); 1, 1] !![1, 1; 1, (N : ℚ)⁻¹] !![1, (N : ℚ); (N : ℚ), (N : ℚ)]
    !![1, 1; (N : ℚ), 1]

/-- A rational matrix `X` has the **shape of the elements of the paramodular group `K(N)`**
(Roberts–Schmidt, §2): it lies in `[ℤ, Nℤ, ℤ, ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, Nℤ, ℤ, ℤ; Nℤ, Nℤ, Nℤ, ℤ]`. -/
def IsParamodularShape (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) : Prop :=
  ∃ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ, ∀ i j, X i j = paramodularScale N i j * x i j

/-- The integral matrix with entries `A(i, j) / N` for `i ∈ {e₁, f₁}`, `j ∈ {e₂, f₂}`, the other
ones being unchanged. -/
private def shapeCoords (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  fromBlocks
    !![A (.inl 0) (.inl 0), A (.inl 0) (.inl 1) / N; A (.inl 1) (.inl 0), A (.inl 1) (.inl 1)]
    !![A (.inl 0) (.inr 0), A (.inl 0) (.inr 1) / N; A (.inl 1) (.inr 0), A (.inl 1) (.inr 1)]
    !![A (.inr 0) (.inl 0), A (.inr 0) (.inl 1) / N; A (.inr 1) (.inl 0), A (.inr 1) (.inl 1)]
    !![A (.inr 0) (.inr 0), A (.inr 0) (.inr 1) / N; A (.inr 1) (.inr 0), A (.inr 1) (.inr 1)]

/-- The integral matrix with entries `N x(i, j)` for `i ∈ {e₁, f₁}`, `j ∈ {e₂, f₂}`, the other ones
being unchanged. -/
private def shapeMatrix (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  fromBlocks
    !![x (.inl 0) (.inl 0), N * x (.inl 0) (.inl 1); x (.inl 1) (.inl 0), x (.inl 1) (.inl 1)]
    !![x (.inl 0) (.inr 0), N * x (.inl 0) (.inr 1); x (.inl 1) (.inr 0), x (.inl 1) (.inr 1)]
    !![x (.inr 0) (.inl 0), N * x (.inr 0) (.inl 1); x (.inr 1) (.inl 0), x (.inr 1) (.inl 1)]
    !![x (.inr 0) (.inr 0), N * x (.inr 0) (.inr 1); x (.inr 1) (.inr 0), x (.inr 1) (.inr 1)]

variable {N}

private lemma intCast_ediv {a : ℤ} (h : (N : ℤ) ∣ a) : ((a / (N : ℤ) : ℤ) : ℚ) = a * (N : ℚ)⁻¹ := by
  rw [Int.cast_div h (by exact_mod_cast N.ne_zero), Int.cast_natCast, div_eq_mul_inv]

/-- **The elements of the paramodular group `K(N)` have the shape
`[ℤ, Nℤ, ℤ, ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, Nℤ, ℤ, ℤ; Nℤ, Nℤ, Nℤ, ℤ]`** (Roberts–Schmidt, §2). -/
lemma isParamodularShape_of_mem {X : symplecticGroup (Fin 2) ℚ} (hX : X ∈ paramodularLevel N) :
    IsParamodularShape N X := by
  rcases (SymplecticGroup.mem_paramodular_iff _).mp hX with ⟨g, hg, hXg⟩
  refine ⟨shapeCoords N g, fun i j ↦ ?_⟩
  have h₁ : (((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inl 0) (.inl 1) / (N : ℤ) : ℤ) : ℚ) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inl 0) (.inl 1) * (N : ℚ)⁻¹ :=
    intCast_ediv (dvd_apply_of_mem_paramodularGL hg (.inl rfl) (.inl rfl))
  have h₂ : (((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inl 0) (.inr 1) / (N : ℤ) : ℤ) : ℚ) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inl 0) (.inr 1) * (N : ℚ)⁻¹ :=
    intCast_ediv (dvd_apply_of_mem_paramodularGL hg (.inl rfl) (.inr rfl))
  have h₃ : (((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inl 1) / (N : ℤ) : ℤ) : ℚ) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inl 1) * (N : ℚ)⁻¹ :=
    intCast_ediv (dvd_apply_of_mem_paramodularGL hg (.inr rfl) (.inl rfl))
  have h₄ : (((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inr 1) / (N : ℤ) : ℤ) : ℚ) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inr 1) * (N : ℚ)⁻¹ :=
    intCast_ediv (dvd_apply_of_mem_paramodularGL hg (.inr rfl) (.inr rfl))
  rw [hXg]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [paramodularScale, shapeCoords, paramodularDelta, paramodularDeltaInv, Matrix.mul_apply,
      h₁, h₂, h₃, h₄] <;>
    field_simp

private lemma coe_eq_of_shape {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ}
    {x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ}
    (hx : ∀ i j, X i j = paramodularScale N i j * x i j) : X = paramodularDelta ![1, N] *
    (shapeMatrix N x).map (Int.castRingHom ℚ) * paramodularDeltaInv ![1, N] := by
  ext i j
  rw [hx]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [paramodularScale, shapeMatrix, paramodularDelta, paramodularDeltaInv,
      Matrix.mul_apply] <;>
    field_simp

/-- **An element of `Sp(4, ℚ)` of the shape
`[ℤ, Nℤ, ℤ, ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, Nℤ, ℤ, ℤ; Nℤ, Nℤ, Nℤ, ℤ]` lies in the paramodular group `K(N)`**
(Roberts–Schmidt, §2): its conjugate by `δ = diag(1, 1, 1, N)` is integral, of determinant `1`, and
an isometry of `T = -δ J δ`. -/
lemma mem_paramodularLevel_of_isParamodularShape {X : symplecticGroup (Fin 2) ℚ}
    (hX : IsParamodularShape N X) : X ∈ paramodularLevel N := by
  rcases hX with ⟨x, hx⟩
  have h₀ : (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = paramodularDelta ![1, N] *
      (shapeMatrix N x).map (Int.castRingHom ℚ) * paramodularDeltaInv ![1, N] :=
    coe_eq_of_shape hx
  have hδ (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      paramodularDeltaInv ![1, N] * (paramodularDelta ![1, N] * Y) = Y := by
    rw [← Matrix.mul_assoc, SymplecticGroup.paramodularDeltaInv_mul_paramodularDelta,
      Matrix.one_mul]
  have hδ' (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      paramodularDelta ![1, N] * (paramodularDeltaInv ![1, N] * Y) = Y := by
    rw [← Matrix.mul_assoc, SymplecticGroup.paramodularDelta_mul_paramodularDeltaInv,
      Matrix.one_mul]
  have h₁ : (shapeMatrix N x).map (Int.castRingHom ℚ) =
      paramodularDeltaInv ![1, N] * X * paramodularDelta ![1, N] := by
    rw [h₀]
    simp only [Matrix.mul_assoc, hδ, SymplecticGroup.paramodularDeltaInv_mul_paramodularDelta,
      Matrix.mul_one]
  have hdet : IsUnit (shapeMatrix N x).det := by
    have h₂ : (((shapeMatrix N x).det : ℤ) : ℚ) = 1 := by
      rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det, RingHom.mapMatrix_apply, h₁, det_mul,
        det_mul, mul_right_comm, ← det_mul,
        SymplecticGroup.paramodularDeltaInv_mul_paramodularDelta, det_one, one_mul]
      exact SymplecticGroup.det_eq_one X.2
    rw [Int.cast_eq_one.mp h₂]
    exact isUnit_one
  have hT : (shapeMatrix N x)ᵀ * paramodularForm ![1, N] * shapeMatrix N x =
      paramodularForm ![1, N] := by
    refine Matrix.map_injective (Int.cast_injective (α := ℚ)) ?_
    have e (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) :
        Y.map Int.cast = Y.map (Int.castRingHom ℚ) :=
      rfl
    have hJ : (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ * (J (Fin 2) ℚ *
        (X * paramodularDelta ![1, N])) = J (Fin 2) ℚ * paramodularDelta ![1, N] := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, SymplecticGroup.mem_iff'.mp X.2]
    have hF : (paramodularForm ![1, N]).map (Int.castRingHom ℚ) =
        -(paramodularDelta ![1, N] * J (Fin 2) ℚ * paramodularDelta ![1, N]) := by
      rw [SymplecticGroup.paramodularDelta_mul_J_mul_paramodularDelta, neg_neg]
    simp only [e, Matrix.map_mul, transpose_map, h₁, hF, transpose_mul,
      SymplecticGroup.transpose_paramodularDelta, SymplecticGroup.transpose_paramodularDeltaInv,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hδ, hδ', hJ]
  let g : GL (Fin 2 ⊕ Fin 2) ℤ := ((isUnit_iff_isUnit_det _).mpr hdet).unit
  have hgv : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) = shapeMatrix N x :=
    IsUnit.unit_spec _
  have hg : g ∈ SymplecticGroup.paramodularGL ![1, N] :=
    (congrArg (fun A ↦ Aᵀ * paramodularForm ![1, N] * A) hgv).trans hT
  exact (SymplecticGroup.mem_paramodular_iff _).mpr ⟨g, hg, hgv ▸ h₀⟩

/-- **The elements of `K(N)` in `GL(4, ℚ)`** are the symplectic matrices of the shape
`[ℤ, Nℤ, ℤ, ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, Nℤ, ℤ, ℤ; Nℤ, Nℤ, Nℤ, ℤ]`. -/
lemma mem_heckeGammaOf_paramodularLevel_iff {Y : GL (Fin 2 ⊕ Fin 2) ℚ} : Y ∈
    heckeGammaOf (paramodularLevel N) ↔
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) ∈ symplecticGroup (Fin 2) ℚ ∧
        IsParamodularShape N Y := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X.2, isParamodularShape_of_mem hX⟩
  · exact ⟨⟨Y, h₁⟩, mem_paramodularLevel_of_isParamodularShape h₂, Units.ext rfl⟩

end SiegelUpperHalfSpace
