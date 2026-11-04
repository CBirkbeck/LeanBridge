import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularLevelRaisingThetaPrime
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularPattern
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ScalarSimilitude

/-!
# The Atkin–Lehner elements of the paramodular group

Roberts and Schmidt (*On modular forms for the paramodular group*, in *Automorphic forms and zeta
functions*, World Scientific 2006, §2; https://sites.math.unt.edu/~schmidt/papers/arakawa.pdf)
define the Atkin–Lehner elements of the paramodular group `K(N)`, for a prime `p` with `p^j` the
exact power of `p` dividing `N`, as the matrices `u_p = γ_p diag(p^j, p^j, 1, 1)` for
`γ_p ∈ Sp(4, ℤ)` with `γ_p ≡ (0, w; -w, 0)` modulo `p^j` and `γ_p ≡ 1` modulo `N / p^j`, where
`w = (0, 1; 1, 0)`. They state that `u_p` normalizes `K(N)`, that `u_p² ∈ p^j K(N)`, and that a
different choice of `γ_p` multiplies `u_p` from the left by an element of `Γ(N) ⊆ K(N)`.

This file proves this, for `N = q M` with `q`, `M` coprime (`q = p^j` for Roberts and Schmidt). Such
elements can be taken in the image of the embedding `Ξ : M₂(R) → M₄(R)`,
`(a, b; c, d) ↦ (a 1₂, b w; c w, d 1₂)`, which is multiplicative and has multiplier the determinant;
the classical Atkin–Lehner matrices `U = (q² a, M b; q M c, q d)` of `Γ₀(N)`, of determinant `q`,
are sent to elements normalizing `K(N)`, and `Ξ(T) ∈ K(N)` for `T ∈ Γ₀(N)`. In particular
`diag(p, p, 1, 1) = Ξ(diag(p, 1))`, and `Ξ(U) diag(p, p, 1, 1) Ξ(U')` is a scalar multiple of an
element of `K(N)`, for the classical Atkin–Lehner matrices `U` of level `N`, `U'` of level `Np`.

## Main definitions

* `SiegelUpperHalfSpace.xiMatrix`: the embedding `Ξ : M₂(R) → M₄(R)`.
* `SiegelUpperHalfSpace.xiSp`: the element `Ξ(T)` of `Sp(4, ℚ)` for `T ∈ SL(2, ℤ)`.
* `SiegelUpperHalfSpace.AtkinLehnerParam`: the parameters of the matrices
  `U = (q² a, M b; q M c, q d)` of determinant `q`.
* `SiegelUpperHalfSpace.AtkinLehnerParam.matrix`, `SiegelUpperHalfSpace.AtkinLehnerParam.matrixInv`:
  the matrix `U` and its inverse.
* `SiegelUpperHalfSpace.AtkinLehnerParam.gl`, `SiegelUpperHalfSpace.AtkinLehnerParam.gsp`: the
  element `Ξ(U)` of `GL(4, ℚ)`, of `GSp(4, ℚ)⁺`.
* `SiegelUpperHalfSpace.AtkinLehnerParam.squareMatrix`,
  `SiegelUpperHalfSpace.AtkinLehnerParam.productMatrix`: the matrices `U² / q` and
  `U diag(p, 1) U' / (q p)` of `Γ₀(N)`.
* `SiegelUpperHalfSpace.AtkinLehnerParam.gamma`: the element `γ` of `Sp(4, ℤ)` with
  `Ξ(U) = γ diag(q, q, 1, 1)`.
* `SiegelUpperHalfSpace.AtkinLehnerParam.ofCoprime`: explicit parameters for coprime `q`, `M`.
* `SiegelUpperHalfSpace.IsAtkinLehnerElementAt`: the Atkin–Lehner elements `γ diag(q, q, 1, 1)` of
  Roberts and Schmidt.

## Main results

* `SiegelUpperHalfSpace.xiSp_mem_paramodularLevel`: `Ξ(T) ∈ K(N)` for `T ∈ Γ₀(N)`.
* `SiegelUpperHalfSpace.isParamodularShape_xiMatrix_mul_mul_xiMatrix`: `Ξ(U) X Ξ(U)⁻¹` has the shape
  of the elements of `K(N)` if `X` has.
* `SiegelUpperHalfSpace.AtkinLehnerParam.conj_mem`,
  `SiegelUpperHalfSpace.AtkinLehnerParam.inv_conj_mem`: `Ξ(U)` normalizes `K(N)`.
* `SiegelUpperHalfSpace.mul_mul_mem_symplecticGroup`: conjugation by a similitude preserves
  `Sp(4, ℚ)`.
* `SiegelUpperHalfSpace.AtkinLehnerParam.gl_mul_self`: `Ξ(U)² ∈ q K(N)`.
* `SiegelUpperHalfSpace.AtkinLehnerParam.gl_mul_thetaPrimeDiag_mul_gl`:
  `Ξ(U) diag(p, p, 1, 1) Ξ(U') ∈ (q p) K(N)`, for `U`, `U'` of levels `N = q M`, `N p = (q p) M`.
* `SiegelUpperHalfSpace.isAtkinLehnerElementAt_ofCoprime`: `Ξ(U)` is an Atkin–Lehner element of
  Roberts and Schmidt, for the explicit parameters.
* `SiegelUpperHalfSpace.IsAtkinLehnerElementAt.mul_inv_mem`: two Atkin–Lehner elements differ by an
  element of `K(N)` on the left.
-/

open Matrix

namespace SiegelUpperHalfSpace

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The embedding `Ξ : M₂(R) → M₄(R)`, `(a, b; c, d) ↦ (a 1₂, b w; c w, d 1₂)`, for
`w = (0, 1; 1, 0)`, in the coordinates `(e₁, e₂, f₁, f₂)`: `Ξ(A)` acts by `A` on the bases
`(e₁, f₂)` and `(e₂, f₁)`. It is multiplicative, and its multiplier is the determinant. -/
def xiMatrix (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  fromBlocks (A 0 0 • 1) (A 0 1 • !![0, 1; 1, 0]) (A 1 0 • !![0, 1; 1, 0]) (A 1 1 • 1)

lemma xiMatrix_mul (A B : Matrix (Fin 2) (Fin 2) R) :
    xiMatrix (A * B) = xiMatrix A * xiMatrix B := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [xiMatrix, Matrix.mul_apply]

lemma xiMatrix_one : xiMatrix (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [xiMatrix]

lemma xiMatrix_smul (s : R) (A : Matrix (Fin 2) (Fin 2) R) : xiMatrix (s • A) = s • xiMatrix A := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [xiMatrix]

lemma map_xiMatrix (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) :
    (xiMatrix A).map f = xiMatrix (A.map f) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [xiMatrix]

lemma transpose_xiMatrix_mul_J_mul (A : Matrix (Fin 2) (Fin 2) R) :
    (xiMatrix A)ᵀ * J (Fin 2) R * xiMatrix A = A.det • J (Fin 2) R := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [xiMatrix, J, Matrix.mul_apply, det_fin_two] <;> ring1

lemma coe_thetaPrimeDiag (p : ℕ+) :
    ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
      xiMatrix !![(p : ℚ), 0; 0, 1] := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [thetaPrimeDiag, diagSimilitude, xiMatrix]

variable (N : ℕ+)

/-- The element `Ξ(T)` of `Sp(4, ℚ)` for `T ∈ SL(2, ℤ)`. -/
def xiSp (T : Matrix (Fin 2) (Fin 2) ℤ) (h : T.det = 1) : symplecticGroup (Fin 2) ℚ :=
  ⟨xiMatrix (T.map (Int.cast : ℤ → ℚ)), by
    have h' : (T.map (Int.cast : ℤ → ℚ)).det = 1 := by
      have e : T.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix T :=
        rfl
      rw [e, ← RingHom.map_det, h, map_one]
    rw [SymplecticGroup.mem_iff', transpose_xiMatrix_mul_J_mul, h', one_smul]⟩

lemma coe_xiSp (T : Matrix (Fin 2) (Fin 2) ℤ) (h : T.det = 1) :
    (xiSp T h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = xiMatrix (T.map (Int.cast : ℤ → ℚ)) :=
  rfl

/-- **`Ξ(T)` lies in the paramodular group `K(N)`**, for `T ∈ Γ₀(N)`. -/
lemma xiSp_mem_paramodularLevel {T : Matrix (Fin 2) (Fin 2) ℤ} (h : T.det = 1)
    (hN : (N : ℤ) ∣ T 1 0) : xiSp T h ∈ paramodularLevel N := by
  rcases hN with ⟨γ, hγ⟩
  exact mem_paramodularLevel_of_isParamodularShape
    ⟨fromBlocks !![T 0 0, 0; 0, T 0 0] !![0, T 0 1; T 0 1, 0] !![0, γ; γ, 0] !![T 1 1, 0; 0, T 1 1],
      fun i j ↦ by
        rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
          simp [xiSp, xiMatrix, paramodularScale, hγ]⟩

/-- **Conjugation by a similitude preserves `Sp(4, ℚ)`**: if `U V = 1` and `Uᵀ J U = r J`, `r ≠ 0`,
then `U X V` is symplectic for `X` symplectic. -/
lemma mul_mul_mem_symplecticGroup {U V X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ} {r : ℚ}
    (hr : r ≠ 0) (hUV : U * V = 1) (hU : Uᵀ * J (Fin 2) ℚ * U = r • J (Fin 2) ℚ)
    (hX : X ∈ symplecticGroup (Fin 2) ℚ) : U * X * V ∈ symplecticGroup (Fin 2) ℚ := by
  have h₁ : Vᵀ * J (Fin 2) ℚ * V = r⁻¹ • J (Fin 2) ℚ := by
    have h₂ : Vᵀ * (Uᵀ * J (Fin 2) ℚ * U) * V = J (Fin 2) ℚ := by
      have h₃ : Vᵀ * (Uᵀ * J (Fin 2) ℚ * U) * V = (U * V)ᵀ * J (Fin 2) ℚ * (U * V) := by
        simp only [transpose_mul, Matrix.mul_assoc]
      rw [h₃, hUV, transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hU, Matrix.mul_smul, Matrix.smul_mul] at h₂
    exact (eq_inv_smul_iff₀ hr).mpr h₂
  have h₄ : (U * X * V)ᵀ * J (Fin 2) ℚ * (U * X * V) =
      Vᵀ * (Xᵀ * (Uᵀ * J (Fin 2) ℚ * U) * X) * V := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [SymplecticGroup.mem_iff', h₄, hU, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, SymplecticGroup.mem_iff'.mp hX, h₁, smul_smul, mul_inv_cancel₀ hr, one_smul]

lemma val_spRatToGL (γ : symplecticGroup (Fin 2) ℚ) :
    (spRatToGL (Fin 2) γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = γ :=
  rfl

variable (q M p : ℕ+)

/-- **The Atkin–Lehner matrices normalize the shape of `K(N)`**: for `N = q M`,
`U = (q² a, M b; q M c, q d)` with the inverse `V = (d, -M b / q; -M c, q a)` (when
`q² a d - M² b c = 1`) and `X` of the shape of `K(N)`, the matrix `Ξ(U) X Ξ(V)` has the shape of
`K(N)`. -/
lemma isParamodularShape_xiMatrix_mul_mul_xiMatrix (a b c d : ℤ)
    {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ} (hX : IsParamodularShape (q * M) X) :
    IsParamodularShape (q * M) (xiMatrix !![(q : ℚ) ^ 2 * a, M * b; q * M * c, q * d] * X *
      xiMatrix !![(d : ℚ), -(M / q) * b; -M * c, q * a]) := by
  rcases hX with ⟨x, hx⟩
  let Q : ℤ := (q : ℕ)
  let R : ℤ := (M : ℕ)
  let m : ℤ := Q * R
  refine ⟨fromBlocks
    !![Q ^ 2 * a * d * x (.inl 0) (.inl 0) - Q ^ 2 * R * a * c * x (.inl 0) (.inr 1) +
        R * m * b * d * x (.inr 1) (.inl 0) - R ^ 2 * b * c * x (.inr 1) (.inr 1),
      Q ^ 2 * a * d * x (.inl 0) (.inl 1) - Q * a * c * x (.inl 0) (.inr 0) +
        R * b * d * x (.inr 1) (.inl 1) - R ^ 2 * b * c * x (.inr 1) (.inr 0);
      Q ^ 2 * a * d * x (.inl 1) (.inl 0) - Q * a * c * x (.inl 1) (.inr 1) +
        R * b * d * x (.inr 0) (.inl 0) - R ^ 2 * b * c * x (.inr 0) (.inr 1),
      Q ^ 2 * a * d * x (.inl 1) (.inl 1) - Q ^ 2 * R * a * c * x (.inl 1) (.inr 0) +
        R * m * b * d * x (.inr 0) (.inl 1) - R ^ 2 * b * c * x (.inr 0) (.inr 0)]
    !![-Q * R * m * a * b * x (.inl 0) (.inl 1) + Q ^ 3 * a ^ 2 * x (.inl 0) (.inr 0) -
        R ^ 3 * b ^ 2 * x (.inr 1) (.inl 1) + Q * R * m * a * b * x (.inr 1) (.inr 0),
      -Q * R * a * b * x (.inl 0) (.inl 0) + Q ^ 3 * a ^ 2 * x (.inl 0) (.inr 1) -
        R ^ 3 * b ^ 2 * x (.inr 1) (.inl 0) + Q * R * a * b * x (.inr 1) (.inr 1);
      -Q * R * a * b * x (.inl 1) (.inl 1) + Q ^ 3 * a ^ 2 * x (.inl 1) (.inr 0) -
        R ^ 3 * b ^ 2 * x (.inr 0) (.inl 1) + Q * R * a * b * x (.inr 0) (.inr 0),
      -Q * R * m * a * b * x (.inl 1) (.inl 0) + Q ^ 3 * a ^ 2 * x (.inl 1) (.inr 1) -
        R ^ 3 * b ^ 2 * x (.inr 0) (.inl 0) + Q * R * m * a * b * x (.inr 0) (.inr 1)]
    !![m * c * d * x (.inl 1) (.inl 0) - R * c ^ 2 * x (.inl 1) (.inr 1) +
        Q * d ^ 2 * x (.inr 0) (.inl 0) - m * c * d * x (.inr 0) (.inr 1),
      c * d * x (.inl 1) (.inl 1) - R * c ^ 2 * x (.inl 1) (.inr 0) +
        Q * d ^ 2 * x (.inr 0) (.inl 1) - c * d * x (.inr 0) (.inr 0);
      c * d * x (.inl 0) (.inl 0) - R * c ^ 2 * x (.inl 0) (.inr 1) +
        Q * d ^ 2 * x (.inr 1) (.inl 0) - c * d * x (.inr 1) (.inr 1),
      m * c * d * x (.inl 0) (.inl 1) - R * c ^ 2 * x (.inl 0) (.inr 0) +
        Q * d ^ 2 * x (.inr 1) (.inl 1) - m * c * d * x (.inr 1) (.inr 0)]
    !![-R ^ 2 * b * c * x (.inl 1) (.inl 1) + Q ^ 2 * R * a * c * x (.inl 1) (.inr 0) -
        R * m * b * d * x (.inr 0) (.inl 1) + Q ^ 2 * a * d * x (.inr 0) (.inr 0),
      -R ^ 2 * b * c * x (.inl 1) (.inl 0) + Q * a * c * x (.inl 1) (.inr 1) -
        R * b * d * x (.inr 0) (.inl 0) + Q ^ 2 * a * d * x (.inr 0) (.inr 1);
      -R ^ 2 * b * c * x (.inl 0) (.inl 1) + Q * a * c * x (.inl 0) (.inr 0) -
        R * b * d * x (.inr 1) (.inl 1) + Q ^ 2 * a * d * x (.inr 1) (.inr 0),
      -R ^ 2 * b * c * x (.inl 0) (.inl 0) + Q ^ 2 * R * a * c * x (.inl 0) (.inr 1) -
        R * m * b * d * x (.inr 1) (.inl 0) + Q ^ 2 * a * d * x (.inr 1) (.inr 1)], fun i j ↦ ?_⟩
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.ne_zero
  have hM : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr M.ne_zero
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, xiMatrix, hx, paramodularScale, Q, R, m] <;>
    field_simp <;> ring1

/-- The **parameters** `(a, b, c, d)`, with `q² a d - M² b c = 1`, of a classical Atkin–Lehner
matrix `U = (q² a, M b; q M c, q d)` of determinant `q`, for the factorization `N = q M`. Its image
`Ξ(U)` in `GSp(4, ℚ)⁺` normalizes the paramodular group `K(N)`. -/
structure AtkinLehnerParam where
  /-- The parameter `a`. -/
  a : ℤ
  /-- The parameter `b`. -/
  b : ℤ
  /-- The parameter `c`. -/
  c : ℤ
  /-- The parameter `d`. -/
  d : ℤ
  /-- The determinant condition. -/
  det_eq : (q : ℤ) ^ 2 * a * d - (M : ℤ) ^ 2 * b * c = 1

/-- The **Atkin–Lehner elements** of Roberts and Schmidt (*On modular forms for the paramodular
group*, §2) of the factorization `N = q M`, `q = p^j` the exact power of `p` dividing `N`: the
elements `u = γ diag(q, q, 1, 1)` for `γ ∈ Sp(4, ℤ)` with `γ ≡ (0, w; -w, 0)` modulo `q` and `γ ≡ 1`
modulo `M`, where `w = (0, 1; 1, 0)`. -/
def IsAtkinLehnerElementAt (u : gspPlusGL (Fin 2)) : Prop :=
  ∃ γ : symplecticGroup (Fin 2) ℤ,
    (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) =
        fromBlocks 0 !![0, 1; 1, 0] (-!![0, 1; 1, 0]) 0 ∧
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.cast : ℤ → ZMod M) = 1 ∧
        u = spToGSpPlusGL (SymplecticGroup.map (Int.castRingHom ℚ) γ) * thetaPrimeDiag q

variable {q M}

namespace AtkinLehnerParam

variable (A : AtkinLehnerParam q M)

/-- The classical Atkin–Lehner matrix `U = (q² a, M b; q M c, q d)`. -/
def matrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(q : ℚ) ^ 2 * A.a, M * A.b; q * M * A.c, q * A.d]

/-- The inverse `(d, -M b / q; -M c, q a)` of the classical Atkin–Lehner matrix. -/
def matrixInv : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(A.d : ℚ), -(M / q) * A.b; -M * A.c, q * A.a]

private lemma cast_det_eq : (q : ℚ) ^ 2 * A.a * A.d - (M : ℚ) ^ 2 * A.b * A.c = 1 := by
  exact_mod_cast A.det_eq

lemma matrix_mul_matrixInv : A.matrix * A.matrixInv = 1 := by
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.ne_zero
  have hdet : (q : ℚ) ^ 2 * A.a * A.d - (M : ℚ) ^ 2 * A.b * A.c = 1 := A.cast_det_eq
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, matrixInv, Matrix.mul_apply]
  · linear_combination hdet
  · field_simp
    ring1
  · ring1
  · field_simp
    linear_combination hdet

lemma matrixInv_mul_matrix : A.matrixInv * A.matrix = 1 :=
  mul_eq_one_comm.mp A.matrix_mul_matrixInv

lemma det_matrix : A.matrix.det = q := by
  have hdet : (q : ℚ) ^ 2 * A.a * A.d - (M : ℚ) ^ 2 * A.b * A.c = 1 := A.cast_det_eq
  rw [matrix, det_fin_two_of]
  linear_combination (q : ℚ) * hdet

/-- The Atkin–Lehner element `Ξ(U)` of `GL(4, ℚ)`. -/
def gl : GL (Fin 2 ⊕ Fin 2) ℚ where
  val := xiMatrix A.matrix
  inv := xiMatrix A.matrixInv
  val_inv := by rw [← xiMatrix_mul, matrix_mul_matrixInv, xiMatrix_one]
  inv_val := by rw [← xiMatrix_mul, matrixInv_mul_matrix, xiMatrix_one]

lemma coe_gl : (A.gl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = xiMatrix A.matrix :=
  rfl

lemma transpose_gl_mul_J_mul : (A.gl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ * J (Fin 2) ℚ *
    A.gl = (q : ℚ) • J (Fin 2) ℚ := by
  rw [coe_gl, transpose_xiMatrix_mul_J_mul, det_matrix]

/-- The Atkin–Lehner element `Ξ(U)` of `GSp(4, ℚ)⁺`, of multiplier `q`. -/
def gsp : gspPlusGL (Fin 2) :=
  ⟨A.gl, q, by positivity, A.transpose_gl_mul_J_mul⟩

@[simp]
lemma coe_gsp : (A.gsp : GL (Fin 2 ⊕ Fin 2) ℚ) = A.gl :=
  rfl

variable {x : GL (Fin 2 ⊕ Fin 2) ℚ}

/-- **`Ξ(U)` normalizes the paramodular group `K(N)`**, for `N = q M`: if `x ∈ K(N)`, then
`Ξ(U) x Ξ(U)⁻¹ ∈ K(N)`, being symplectic and of the shape of `K(N)`. -/
lemma conj_mem (hx : x ∈ heckeGammaOf (paramodularLevel (q * M))) :
    A.gl * x * A.gl⁻¹ ∈ heckeGammaOf (paramodularLevel (q * M)) := by
  rw [mem_heckeGammaOf_paramodularLevel_iff] at hx ⊢
  exact ⟨mul_mul_mem_symplecticGroup (r := (q : ℚ)) (Nat.cast_ne_zero.mpr q.ne_zero)
    (Units.mul_inv A.gl) A.transpose_gl_mul_J_mul hx.1,
    isParamodularShape_xiMatrix_mul_mul_xiMatrix q M A.a A.b A.c A.d hx.2⟩

/-- The matrix `T = U² / q ∈ Γ₀(q M)` for the Atkin–Lehner matrix `U`. -/
def squareMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) ^ 3 * A.a ^ 2 + (M : ℤ) ^ 2 * A.b * A.c, (M : ℤ) * A.b * (q * A.a + A.d);
    (q : ℤ) * M * A.c * (q * A.a + A.d), (M : ℤ) ^ 2 * A.b * A.c + q * A.d ^ 2]

lemma det_squareMatrix : A.squareMatrix.det = 1 := by
  rw [squareMatrix, det_fin_two_of]
  linear_combination ((q : ℤ) ^ 2 * A.a * A.d - (M : ℤ) ^ 2 * A.b * A.c + 1) * A.det_eq

lemma dvd_squareMatrix : ((q * M : ℕ+) : ℤ) ∣ A.squareMatrix 1 0 :=
  ⟨A.c * (q * A.a + A.d), by simp [squareMatrix, mul_assoc]⟩

/-- **`Ξ(U)² ∈ q K(N)`** (Roberts–Schmidt, §2, `u_p² ∈ p^j Γ^para(N)`), for `N = q M`. -/
lemma gl_mul_self :
    A.gl * A.gl = scalarGL q * spRatToGL (Fin 2) (xiSp A.squareMatrix A.det_squareMatrix) := by
  have h : A.matrix * A.matrix = (q : ℚ) • A.squareMatrix.map (Int.cast : ℤ → ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, squareMatrix, Matrix.mul_apply] <;> ring1
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_gl, coe_scalarGL, val_spRatToGL, coe_xiSp, ← xiMatrix_mul,
    h, xiMatrix_smul, Matrix.smul_mul, Matrix.one_mul]

private lemma inv_mul_mul_eq {G : Type*} [Group G] {u y w z : G} (hz : ∀ g, z * g = g * z)
    (h : u * u = z * w) : u⁻¹ * y * u = w⁻¹ * (u * y * u⁻¹) * w := by
  have hw : w = z⁻¹ * (u * u) := eq_inv_mul_of_mul_eq h.symm
  have hzy : z * (u * y * u⁻¹) * z⁻¹ = u * y * u⁻¹ := by
    rw [hz, mul_inv_cancel_right]
  have hy : w⁻¹ * (u * y * u⁻¹) * w = (u * u)⁻¹ * (z * (u * y * u⁻¹) * z⁻¹) * (u * u) := by
    rw [hw]
    group
  rw [hy, hzy]
  group

/-- **`Ξ(U)⁻¹` normalizes the paramodular group `K(N)`**, for `N = q M`: conjugating by `Ξ(U)⁻¹` is
the same as conjugating by `Ξ(U)` and then by an element of `K(N)`, since `Ξ(U)² ∈ q K(N)`. -/
lemma inv_conj_mem (hx : x ∈ heckeGammaOf (paramodularLevel (q * M))) :
    A.gl⁻¹ * x * A.gl ∈ heckeGammaOf (paramodularLevel (q * M)) := by
  have hw : spRatToGL (Fin 2) (xiSp A.squareMatrix A.det_squareMatrix) ∈
      heckeGammaOf (paramodularLevel (q * M)) :=
    ⟨_, xiSp_mem_paramodularLevel (q * M) A.det_squareMatrix A.dvd_squareMatrix, rfl⟩
  rw [inv_mul_mul_eq (scalarGL_mul_comm q) A.gl_mul_self]
  exact mul_mem (mul_mem (inv_mem hw) (A.conj_mem hx)) hw

variable {p} (A' : AtkinLehnerParam (q * p) M)

/-- The matrix `T = U diag(p, 1) U' / (q p) ∈ Γ₀(q M)`, for the Atkin–Lehner matrices `U` of
`q M` and `U'` of `(q p) M`. -/
def productMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(p : ℤ) ^ 2 * q ^ 3 * A.a * A'.a + (M : ℤ) ^ 2 * A.b * A'.c,
    (M : ℤ) * (q * A.a * A'.b + A.b * A'.d);
    (q : ℤ) * M * ((p : ℤ) ^ 2 * q * A.c * A'.a + A.d * A'.c),
    (M : ℤ) ^ 2 * A.c * A'.b + q * A.d * A'.d]

lemma det_productMatrix : (A.productMatrix A').det = 1 := by
  have h' : ((q : ℤ) * p) ^ 2 * A'.a * A'.d - (M : ℤ) ^ 2 * A'.b * A'.c = 1 := by
    simpa using A'.det_eq
  rw [productMatrix, det_fin_two_of]
  linear_combination (((q : ℤ) * p) ^ 2 * A'.a * A'.d - (M : ℤ) ^ 2 * A'.b * A'.c) * A.det_eq + h'

lemma dvd_productMatrix : ((q * M : ℕ+) : ℤ) ∣ A.productMatrix A' 1 0 :=
  ⟨(p : ℤ) ^ 2 * q * A.c * A'.a + A.d * A'.c, by simp [productMatrix]⟩

/-- **`Ξ(U) diag(p, p, 1, 1) Ξ(U') ∈ (q p) K(N)`**, for the Atkin–Lehner matrices `U` of `N = q M`
and `U'` of `N p = (q p) M`. -/
lemma gl_mul_thetaPrimeDiag_mul_gl : A.gl * (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * A'.gl =
    scalarGL (q * p) * spRatToGL (Fin 2) (xiSp (A.productMatrix A') (A.det_productMatrix A')) := by
  have h : A.matrix * !![(p : ℚ), 0; 0, 1] * A'.matrix =
      ((q * p : ℕ+) : ℚ) • (A.productMatrix A').map (Int.cast : ℤ → ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, productMatrix, Matrix.mul_apply] <;> ring1
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_gl, coe_gl, coe_thetaPrimeDiag, coe_scalarGL,
    val_spRatToGL, coe_xiSp, ← xiMatrix_mul, ← xiMatrix_mul, h, xiMatrix_smul, Matrix.smul_mul,
    Matrix.one_mul]

/-- The element `γ = Ξ(q a, M b; M c, q d)` of `Sp(4, ℤ)`, with `Ξ(U) = γ diag(q, q, 1, 1)`. -/
def gamma : symplecticGroup (Fin 2) ℤ :=
  ⟨xiMatrix !![(q : ℤ) * A.a, M * A.b; M * A.c, q * A.d], by
    have h : (q : ℤ) * A.a * (q * A.d) - M * A.b * (M * A.c) = 1 := by
      linear_combination A.det_eq
    rw [SymplecticGroup.mem_iff', transpose_xiMatrix_mul_J_mul, det_fin_two_of, h, one_smul]⟩

lemma coe_gamma : (A.gamma : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) =
    xiMatrix !![(q : ℤ) * A.a, M * A.b; M * A.c, q * A.d] :=
  rfl

lemma gsp_eq : A.gsp = spToGSpPlusGL (SymplecticGroup.map (Int.castRingHom ℚ) A.gamma) *
    thetaPrimeDiag q := by
  have h : A.matrix = !![(q : ℚ) * A.a, M * A.b; M * A.c, q * A.d] * !![(q : ℚ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Matrix.mul_apply] <;> ring1
  refine Subtype.ext <| Units.ext ?_
  rw [Submonoid.coe_mul, Units.val_mul, coe_gsp, coe_gl, coe_thetaPrimeDiag, coe_spToGSpPlusGL,
    val_spRatToGL, SymplecticGroup.coe_map_apply, coe_gamma, map_xiMatrix, ← xiMatrix_mul, h]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma bezout (h : Nat.Coprime q M) : (q : ℤ) * Nat.gcdA q M + M * Nat.gcdB q M = 1 := by
  have e : ((q : ℕ).gcd M : ℤ) = q * Nat.gcdA q M + M * Nat.gcdB q M :=
    Nat.gcd_eq_gcd_ab q M
  rw [h.gcd_eq_one] at e
  exact_mod_cast e.symm

/-- **Explicit parameters** of an Atkin–Lehner matrix for coprime `q`, `M`, from a Bézout identity
`q x + M y = 1`: writing `α = q x`, `β = M y`, the matrix `(α, β; β (2β - 3), α (3 - 2α))` has
determinant `1` and is congruent to `(0, 1; -1, 0)` modulo `q` and to `1` modulo `M`, so that its
image under `Ξ` is an element `γ_p` of Roberts and Schmidt. -/
def ofCoprime (h : Nat.Coprime q M) : AtkinLehnerParam q M where
  a := Nat.gcdA q M
  b := Nat.gcdB q M
  c := Nat.gcdB q M * (2 * M * Nat.gcdB q M - 3)
  d := Nat.gcdA q M * (3 - 2 * q * Nat.gcdA q M)
  det_eq := by
    linear_combination ((q : ℤ) * Nat.gcdA q M + M * Nat.gcdB q M + 1 -
      2 * ((q : ℤ) * Nat.gcdA q M) ^ 2 + 2 * ((q : ℤ) * Nat.gcdA q M) * (M * Nat.gcdB q M) -
        2 * ((M : ℤ) * Nat.gcdB q M) ^ 2) * bezout h

end AtkinLehnerParam

/-- **The elements `Ξ(U)` of the explicit parameters are Atkin–Lehner elements.** -/
lemma isAtkinLehnerElementAt_ofCoprime (h : Nat.Coprime q M) :
    IsAtkinLehnerElementAt q M (AtkinLehnerParam.ofCoprime h).gsp := by
  have hb : (q : ℤ) * Nat.gcdA q M + M * Nat.gcdB q M = 1 := AtkinLehnerParam.bezout h
  have hb₁ : ((M : ℕ) : ZMod q) * (Nat.gcdB q M : ZMod q) = 1 := by
    have e : (((q : ℤ) * Nat.gcdA q M + M * Nat.gcdB q M : ℤ) : ZMod q) = ((1 : ℤ) : ZMod q) :=
      congrArg (Int.cast : ℤ → ZMod q) hb
    push_cast at e
    rwa [ZMod.natCast_self, zero_mul, zero_add] at e
  have hb₂ : ((q : ℕ) : ZMod M) * (Nat.gcdA q M : ZMod M) = 1 := by
    have e : (((q : ℤ) * Nat.gcdA q M + M * Nat.gcdB q M : ℤ) : ZMod M) = ((1 : ℤ) : ZMod M) :=
      congrArg (Int.cast : ℤ → ZMod M) hb
    push_cast at e
    rwa [ZMod.natCast_self, zero_mul, add_zero] at e
  refine ⟨(AtkinLehnerParam.ofCoprime h).gamma, ?_, ?_, AtkinLehnerParam.gsp_eq _⟩
  · have e : (AtkinLehnerParam.ofCoprime h).gamma.1.map (Int.cast : ℤ → ZMod q) =
        (AtkinLehnerParam.ofCoprime h).gamma.1.map (Int.castRingHom (ZMod q)) :=
      rfl
    rw [e, AtkinLehnerParam.coe_gamma, map_xiMatrix]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [xiMatrix, AtkinLehnerParam.ofCoprime, hb₁]
    all_goals linear_combination (2 * ((M : ℕ) : ZMod q) * (Nat.gcdB q M : ZMod q) - 1) * hb₁
  · have e : (AtkinLehnerParam.ofCoprime h).gamma.1.map (Int.cast : ℤ → ZMod M) =
        (AtkinLehnerParam.ofCoprime h).gamma.1.map (Int.castRingHom (ZMod M)) :=
      rfl
    rw [e, AtkinLehnerParam.coe_gamma, map_xiMatrix]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [xiMatrix, AtkinLehnerParam.ofCoprime, hb₂]
    all_goals linear_combination (1 - 2 * ((q : ℕ) : ZMod M) * (Nat.gcdA q M : ZMod M)) * hb₂

private lemma dvd_sub_of_map_eq_one {n : ℕ} {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ}
    (h : A.map (Int.cast : ℤ → ZMod n) = 1) (i j : Fin 2 ⊕ Fin 2) :
    (n : ℤ) ∣ (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) i j - A i j := by
  have e : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod n)) =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.cast : ℤ → ZMod n) :=
    (Matrix.map_one _ Int.cast_zero Int.cast_one).symm
  rw [e] at h
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun (congrFun h i) j)

private lemma mem_Gamma_mul {g : symplecticGroup (Fin 2) ℤ} (hc : Nat.Coprime q M)
    (hq : g ∈ SymplecticGroup.Gamma (Fin 2) q) (hM : g ∈ SymplecticGroup.Gamma (Fin 2) M) :
    g ∈ SymplecticGroup.Gamma (Fin 2) (q * M : ℕ+) := by
  rw [SymplecticGroup.mem_Gamma_iff] at hq hM ⊢
  have e : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod (q * M : ℕ+))) =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.cast : ℤ → ZMod (q * M : ℕ+)) :=
    (Matrix.map_one _ Int.cast_zero Int.cast_one).symm
  rw [e]
  ext i j
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_
  have hd : ((q : ℕ) : ℤ) * (M : ℕ) ∣
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) i j -
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) i j :=
    (Nat.isCoprime_iff_coprime.mpr hc).mul_dvd (dvd_sub_of_map_eq_one hq i j)
      (dvd_sub_of_map_eq_one hM i j)
  simpa using hd

private lemma mul_inv_mem_Gamma {n : ℕ} {γ δ : symplecticGroup (Fin 2) ℤ}
    (h : (δ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.cast : ℤ → ZMod n) =
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.cast : ℤ → ZMod n)) :
    δ * γ⁻¹ ∈ SymplecticGroup.Gamma (Fin 2) n := by
  have e : SymplecticGroup.map (Int.castRingHom (ZMod n)) δ =
      SymplecticGroup.map (Int.castRingHom (ZMod n)) γ :=
    Subtype.ext h
  rw [SymplecticGroup.Gamma, MonoidHom.mem_ker, map_mul, map_inv, e, mul_inv_cancel]

/-- **Two Atkin–Lehner elements differ by an element of `K(N)`** (Roberts–Schmidt, §2: "a different
choice of `γ_p` results in multiplying `u_p` from the left with an element of the principal
congruence subgroup `Γ(N)`"), for `N = q M`, `q`, `M` coprime: if `u = γ D` and `v = δ D` are two
of them, `δ γ⁻¹ ≡ 1` modulo `q` and modulo `M`. -/
lemma IsAtkinLehnerElementAt.mul_inv_mem {u v : gspPlusGL (Fin 2)} (hc : Nat.Coprime q M)
    (hu : IsAtkinLehnerElementAt q M u) (hv : IsAtkinLehnerElementAt q M v) :
    (v : GL (Fin 2 ⊕ Fin 2) ℚ) * (u : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ ∈
      heckeGammaOf (paramodularLevel (q * M)) := by
  rcases hu with ⟨γ, hq, hM, rfl⟩
  rcases hv with ⟨δ, hq', hM', rfl⟩
  have hd (i : Fin 2) : ((![1, q * M] : Fin 2 → ℕ+) i : ℕ) ∣ (q * M : ℕ+) := by
    fin_cases i <;> simp
  refine ⟨SymplecticGroup.map (Int.castRingHom ℚ) (δ * γ⁻¹),
    SymplecticGroup.isCongruenceOfLevel_paramodular hd ⟨_, mem_Gamma_mul hc
      (mul_inv_mem_Gamma (hq'.trans hq.symm)) (mul_inv_mem_Gamma (hM'.trans hM.symm)), rfl⟩, ?_⟩
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_spToGSpPlusGL, coe_spToGSpPlusGL, map_mul, map_mul,
    map_inv, map_inv]
  group

end SiegelUpperHalfSpace
