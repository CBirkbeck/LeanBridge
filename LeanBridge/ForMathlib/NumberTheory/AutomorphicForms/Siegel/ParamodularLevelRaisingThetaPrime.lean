import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularLevelRaisingCuspForms

/-!
# The level raising operator `θ_p` of Roberts and Schmidt

Roberts and Schmidt (*On modular forms for the paramodular group*, in *Automorphic forms and zeta
functions*, World Scientific 2006, §4, equation (10);
https://sites.math.unt.edu/~schmidt/papers/arakawa.pdf) define the level raising operator
`θ_p F = ∑_γ F ∣_k diag(1, 1, p⁻¹, p⁻¹) ι(γ)` from `M_k(K(M))` to `M_k(K(Mp))`, the sum running over
`γ ∈ Γ₀(p) \ SL(2, ℤ)`, where `ι(a, b; c, d)` is `(a, b; c, d)` acting on the coordinates
`(e₁, f₁)` and trivially on `(e₂, f₂)`. This file proves that, for a prime `p`, the double coset
`K(M) diag(p, p, 1, 1) K(Mp)` is the disjoint union of the `p + 1` right cosets
`K(M) diag(p, p, 1, 1) ι(γ)`, `γ = (1, 0; c, 1)` for `0 ≤ c < p` and `γ = (0, -1; 1, 0)`, so that
the double coset operator `SiegelUpperHalfSpace.levelRaisingThetaPrime` is
`F ↦ ∑_γ F ∣_ρ diag(p, p, 1, 1) ι(γ)`, the operator `θ_p` of Roberts and Schmidt. The matrix
`diag(p, p, 1, 1)` is `p diag(1, 1, p⁻¹, p⁻¹)`; Roberts and Schmidt normalise the slash operator by
`λ(g)^k`, so that scalar matrices act trivially, while `SiegelUpperHalfSpace.gspSlash` carries the
factor `r^(2k - 3)` for `ρ = det^k`, so for that `ρ` their `θ_p` is `p^(3 - k)` times
`levelRaisingThetaPrime` (`SiegelUpperHalfSpace.rsTheta_eq_smul_levelRaisingThetaPrime`). Their
`θ'_p = u_p θ_p u_p` is shown in the same paper (equation (16)) to be the trace from `K(M) ∩ K(Mp)`
to `K(Mp)`, which is `SiegelUpperHalfSpace.levelRaisingTheta`
(`SiegelUpperHalfSpace.rsThetaPrime_eq_levelRaisingTheta`, for `ρ = det^k` and `M = q M₀` with `q p`
and `M₀` coprime, in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularRobertsSchmidt`): the names
`θ` and `θ'` of the two existing operators are swapped with respect to Roberts and Schmidt.

The file then proves that `θ_p` maps the cusp forms `S_ρ(K(M))` to `S_ρ(K(Mp))` when the slash
operator preserves holomorphy: each term is `(F ∣ diag(p, p, 1, 1)) ∣ ι(γ)`, and
`diag(p, p, 1, 1)`, which acts by `τ ↦ pτ`, preserves the vanishing of the Siegel operator and
normalises `Sp(4, ℚ)`.

## Main definitions

* `SiegelUpperHalfSpace.iotaMatrix`, `SiegelUpperHalfSpace.iotaGL`: `ι(a, b; c, d)` in `GL(4, ℤ)`.
* `SiegelUpperHalfSpace.spToGSpPlusGL`: `Sp(4, ℚ)` inside `GSp(4, ℚ)⁺`.
* `SiegelUpperHalfSpace.thetaIota`, `SiegelUpperHalfSpace.thetaIotaSp`: `ι(γ)` for the
  representatives `γ` of `Γ₀(p) \ SL(2, ℤ)`.
* `SiegelUpperHalfSpace.thetaRep`: the representatives `diag(p, p, 1, 1) ι(γ)` of the right cosets
  of `K(M) diag(p, p, 1, 1) K(Mp)`.
* `SiegelUpperHalfSpace.thetaPrimeDiagConj`: the conjugation of `Sp(4, ℚ)` by `diag(p, p, 1, 1)`.

## Main results

* `SiegelUpperHalfSpace.thetaPrimeDiag_mul_mul_inv_mem_heckeGammaOf`: `diag(p, p, 1, 1)`
  conjugates the elements of `K(Mp)` with `(f₁, e₁)`-entry divisible by `p` into `K(M)`.
* `SiegelUpperHalfSpace.doubleCoset_thetaPrimeDiag`:
  `K(M) diag(p, p, 1, 1) K(Mp) = ⋃_γ K(M) diag(p, p, 1, 1) ι(γ)`.
* `SiegelUpperHalfSpace.thetaRep_injective`: these right cosets are pairwise distinct.
* `SiegelUpperHalfSpace.coe_levelRaisingThetaPrime`: `levelRaisingThetaPrime` is the operator
  `θ_p` of Roberts and Schmidt, `F ↦ ∑_γ F ∣_ρ diag(p, p, 1, 1) ι(γ)`.
* `SiegelUpperHalfSpace.SiegelOperatorVanishes.heckeMonoidSlash_thetaPrimeDiag`,
  `SiegelUpperHalfSpace.IsCuspForm.heckeMonoidSlash_thetaPrimeDiag`: the slash operator of
  `diag(p, p, 1, 1)` preserves the vanishing of the Siegel operator and cusp forms.
* `SiegelUpperHalfSpace.levelRaisingThetaPrime_mem_paramodularCuspForms`: `θ_p` maps `S_ρ(K(M))`
  to `S_ρ(K(Mp))` when the slash operator preserves holomorphy.
-/

open Filter Matrix Sum

open scoped Pointwise Topology

namespace SiegelUpperHalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (M p : ℕ+)

/-- The integral matrix `ι(a, b; c, d)` of `(a, b; c, d)`, acting on the coordinates `(e₁, f₁)`
and trivially on `(e₂, f₂)`. -/
def iotaMatrix (a b c d : ℤ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  fromBlocks (diagonal ![a, 1]) (diagonal ![b, 0]) (diagonal ![c, 0]) (diagonal ![d, 1])

lemma iotaMatrix_mul (a b c d a' b' c' d' : ℤ) : iotaMatrix a b c d * iotaMatrix a' b' c' d' =
    iotaMatrix (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [iotaMatrix, Matrix.mul_apply]

lemma iotaMatrix_one : iotaMatrix 1 0 0 1 = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [iotaMatrix]

/-- `ι(a, b; c, d)` as an element of `GL(4, ℤ)`, for `ad - bc = 1`. -/
def iotaGL {a b c d : ℤ} (h : a * d - b * c = 1) : GL (Fin 2 ⊕ Fin 2) ℤ where
  val := iotaMatrix a b c d
  inv := iotaMatrix d (-b) (-c) a
  val_inv := by
    rw [iotaMatrix_mul, ← iotaMatrix_one]
    congr 1
    · linear_combination h
    · ring1
    · ring1
    · linear_combination h
  inv_val := by
    rw [iotaMatrix_mul, ← iotaMatrix_one]
    congr 1
    · linear_combination h
    · ring1
    · ring1
    · linear_combination h

lemma iotaGL_mem_paramodularGL (N : ℕ+) {a b c d : ℤ} (h : a * d - b * c = 1) :
    iotaGL h ∈ SymplecticGroup.paramodularGL ![1, N] := by
  have e : (iotaMatrix a b c d)ᵀ * SymplecticGroup.paramodularForm ![1, N] * iotaMatrix a b c d =
      SymplecticGroup.paramodularForm ![1, N] := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [iotaMatrix, SymplecticGroup.paramodularForm, Matrix.mul_apply] <;> linarith
  exact e

/-- `ι(γ)` in `GL(4, ℤ)` for the representatives `γ = (1, 0; c, 1)`, `0 ≤ c < p`, and
`γ = (0, -1; 1, 0)` of `Γ₀(p) \ SL(2, ℤ)`. -/
def thetaIota : Option (Fin p) → GL (Fin 2 ⊕ Fin 2) ℤ
  | some c => iotaGL (a := 1) (b := 0) (c := c) (d := 1) (by ring1)
  | none => iotaGL (a := 0) (b := -1) (c := 1) (d := 0) (by norm_num)

lemma thetaIota_mem_paramodularGL (N : ℕ+) (i : Option (Fin p)) :
    thetaIota p i ∈ SymplecticGroup.paramodularGL ![1, N] := by
  cases i <;> exact iotaGL_mem_paramodularGL N (by norm_num)

/-- The matrix `E = diag(p, p, 1, p)`. -/
private def thetaConj : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  diagonal (Sum.elim ![(p : ℚ), p] ![1, (p : ℚ)])

/-- The matrix `E⁻¹ = diag(p⁻¹, p⁻¹, 1, p⁻¹)`. -/
private def thetaConjInv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  diagonal (Sum.elim ![(p : ℚ)⁻¹, (p : ℚ)⁻¹] ![1, (p : ℚ)⁻¹])

/-- The matrix `diag(p⁻¹, p⁻¹, 1, 1)`, the inverse of `diag(p, p, 1, 1)`. -/
private def thetaPrimeDiagInv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  diagonal (Sum.elim ![(p : ℚ)⁻¹, (p : ℚ)⁻¹] ![1, 1])

private lemma thetaPrimeDiag_mul_paramodularDelta :
    ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) *
      SymplecticGroup.paramodularDelta ![1, M * p] =
        SymplecticGroup.paramodularDelta ![1, M] * thetaConj p := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [thetaPrimeDiag, diagSimilitude, thetaConj, SymplecticGroup.paramodularDelta]

private lemma coe_thetaPrimeDiag_inv :
    (((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = thetaPrimeDiagInv p :=
  Units.inv_eq_of_mul_eq_one_right <| by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [thetaPrimeDiag, diagSimilitude, thetaPrimeDiagInv]

private lemma paramodularDeltaInv_mul_thetaPrimeDiagInv :
    SymplecticGroup.paramodularDeltaInv ![1, M * p] * thetaPrimeDiagInv p =
      thetaConjInv p * SymplecticGroup.paramodularDeltaInv ![1, M] := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [thetaPrimeDiagInv, thetaConjInv, SymplecticGroup.paramodularDeltaInv]

private lemma thetaConj_mul_thetaConjInv : thetaConj p * thetaConjInv p = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [thetaConj, thetaConjInv]

private lemma thetaConjInv_mul_thetaConj : thetaConjInv p * thetaConj p = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [thetaConj, thetaConjInv]

private lemma transpose_thetaConj : (thetaConj p)ᵀ = thetaConj p :=
  diagonal_transpose _

private lemma transpose_thetaConjInv : (thetaConjInv p)ᵀ = thetaConjInv p :=
  diagonal_transpose _

private lemma thetaConjInv_mul_paramodularForm :
    thetaConjInv p * (SymplecticGroup.paramodularForm ![1, M * p]).map (Int.castRingHom ℚ) *
      ((p : ℚ) • thetaConjInv p) =
        (SymplecticGroup.paramodularForm ![1, M]).map (Int.castRingHom ℚ) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [thetaConjInv, SymplecticGroup.paramodularForm] <;>
    field_simp

/-- The integral conjugate `E A E⁻¹` of an integral matrix `A` with `p ∣ A (f₁, j)` for `j ≠ f₁`,
for `E = diag(p, p, 1, p)`. -/
private def thetaConjInt (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  of fun i j ↦
    Sum.elim ![(p : ℤ), p] ![1, (p : ℤ)] i * A i j / Sum.elim ![(p : ℤ), p] ![1, (p : ℤ)] j

private lemma map_thetaConjInt {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ}
    (hA : ∀ j, j ≠ .inr 0 → (p : ℤ) ∣ A (.inr 0) j) : (thetaConjInt p A).map (Int.castRingHom ℚ) =
    thetaConj p * A.map (Int.castRingHom ℚ) * thetaConjInv p := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [thetaConjInt, thetaConj, thetaConjInv, hA] <;> field_simp

/-- **`diag(p, p, 1, 1)` conjugates the elements of `K(Mp)` with `(f₁, e₁)`-entry divisible by `p`
into `K(M)`**: writing `γ = δ g δ⁻¹` with `g` in the integral isometry group of `T_{Mp}`, the
conjugate is `δ' (E g E⁻¹) δ'⁻¹` with `E = diag(p, p, 1, p)`, and `E g E⁻¹` is integral, of
determinant `±1`, and an isometry of `T_M`. -/
lemma thetaPrimeDiag_mul_mul_inv_mem_heckeGammaOf {g : GL (Fin 2 ⊕ Fin 2) ℤ}
    (hg : g ∈ SymplecticGroup.paramodularGL ![1, M * p])
    (hp : (p : ℤ) ∣ (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inl 0)) :
    (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) *
        spRatToGL (Fin 2) (SymplecticGroup.paramodularConj ![1, M * p] ⟨g, hg⟩) *
      (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ ∈ heckeGammaOf (paramodularLevel M) := by
  have hdvd : ∀ j, j ≠ .inr 0 →
      (p : ℤ) ∣ (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) j := by
    have hMp : (p : ℤ) ∣ ((M * p : ℕ+) : ℤ) :=
      Dvd.intro_left (M : ℤ) (by push_cast; ring1)
    rintro (j | j) hj <;> fin_cases j
    · exact hp
    · exact hMp.trans (dvd_apply_of_mem_paramodularGL hg (.inr rfl) (.inl rfl))
    · exact absurd rfl hj
    · exact hMp.trans (dvd_apply_of_mem_paramodularGL hg (.inr rfl) (.inr rfl))
  have hA : (thetaConjInt p g).map (Int.castRingHom ℚ) =
      thetaConj p * (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) *
        thetaConjInv p :=
    map_thetaConjInt p hdvd
  have hdet : IsUnit (thetaConjInt p g).det := by
    have h : (((thetaConjInt p g).det : ℤ) : ℚ) =
        (((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).det : ℤ) : ℚ) := by
      rw [← eq_intCast (Int.castRingHom ℚ), ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det,
        RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hA, det_mul, det_mul,
        mul_right_comm, ← det_mul, thetaConj_mul_thetaConjInv, det_one, one_mul]
    rw [Int.cast_inj.mp h]
    exact isUnits_det_units g
  have hgq : ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ))ᵀ *
      (SymplecticGroup.paramodularForm ![1, M * p]).map (Int.castRingHom ℚ) *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) =
      (SymplecticGroup.paramodularForm ![1, M * p]).map (Int.castRingHom ℚ) := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (Matrix.map · (Int.castRingHom ℚ)) hg
  have hgq' (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ))ᵀ *
        ((SymplecticGroup.paramodularForm ![1, M * p]).map (Int.castRingHom ℚ) *
          ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) * X)) =
      (SymplecticGroup.paramodularForm ![1, M * p]).map (Int.castRingHom ℚ) * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgq]
  have hEE (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      thetaConj p * (thetaConjInv p * X) = X := by
    rw [← Matrix.mul_assoc, thetaConj_mul_thetaConjInv, Matrix.one_mul]
  have hEE' (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      thetaConjInv p * (thetaConj p * X) = X := by
    rw [← Matrix.mul_assoc, thetaConjInv_mul_thetaConj, Matrix.one_mul]
  have hT : (thetaConjInt p g)ᵀ * SymplecticGroup.paramodularForm ![1, M] * thetaConjInt p g =
      SymplecticGroup.paramodularForm ![1, M] := by
    refine Matrix.map_injective (Int.cast_injective (α := ℚ)) ?_
    have e (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) :
        X.map Int.cast = X.map (Int.castRingHom ℚ) :=
      rfl
    simp only [e, Matrix.map_mul, transpose_map, hA, ← thetaConjInv_mul_paramodularForm M p,
      transpose_mul, transpose_thetaConj, transpose_thetaConjInv, Matrix.mul_assoc, hEE, hEE',
      Matrix.smul_mul, Matrix.mul_smul, hgq']
  let g' : GL (Fin 2 ⊕ Fin 2) ℤ := ((isUnit_iff_isUnit_det _).mpr hdet).unit
  have hg'v : (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) = thetaConjInt p g :=
    IsUnit.unit_spec _
  have hg' : g' ∈ SymplecticGroup.paramodularGL ![1, M] :=
    (congrArg (fun A ↦ Aᵀ * SymplecticGroup.paramodularForm ![1, M] * A) hg'v).trans hT
  refine ⟨SymplecticGroup.paramodularConj ![1, M] ⟨g', hg'⟩, ⟨⟨g', hg'⟩, rfl⟩, Units.ext ?_⟩
  have hL : ((spRatToGL (Fin 2) (SymplecticGroup.paramodularConj ![1, M] ⟨g', hg'⟩) :
      GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
        SymplecticGroup.paramodularDelta ![1, M] * (thetaConjInt p g).map (Int.castRingHom ℚ) *
          SymplecticGroup.paramodularDeltaInv ![1, M] := by
    rw [← hg'v]
    rfl
  have hR : ((spRatToGL (Fin 2) (SymplecticGroup.paramodularConj ![1, M * p] ⟨g, hg⟩) :
      GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
        SymplecticGroup.paramodularDelta ![1, M * p] *
          (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) *
            SymplecticGroup.paramodularDeltaInv ![1, M * p] :=
    rfl
  have hD (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) *
        (SymplecticGroup.paramodularDelta ![1, M * p] * X) =
          SymplecticGroup.paramodularDelta ![1, M] * (thetaConj p * X) := by
    rw [← Matrix.mul_assoc, thetaPrimeDiag_mul_paramodularDelta, Matrix.mul_assoc]
  rw [hL, Units.val_mul, Units.val_mul, hR, coe_thetaPrimeDiag_inv, hA]
  simp only [Matrix.mul_assoc, paramodularDeltaInv_mul_thetaPrimeDiagInv, hD]

lemma paramodularDelta_mul_iotaMatrix (N : ℕ+) (a b c d : ℤ) :
    SymplecticGroup.paramodularDelta ![1, N] * (iotaMatrix a b c d).map (Int.castRingHom ℚ) *
      SymplecticGroup.paramodularDeltaInv ![1, N] =
        (iotaMatrix a b c d).map (Int.castRingHom ℚ) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [iotaMatrix, SymplecticGroup.paramodularDelta, SymplecticGroup.paramodularDeltaInv,
      Matrix.mul_apply]

lemma paramodularDelta_mul_thetaIota (N : ℕ+) (i : Option (Fin p)) :
    SymplecticGroup.paramodularDelta ![1, N] *
      (thetaIota p i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) *
        SymplecticGroup.paramodularDeltaInv ![1, N] =
      (thetaIota p i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  cases i <;> exact paramodularDelta_mul_iotaMatrix N _ _ _ _

/-- An element `γ` of `Sp(4, ℚ)` as an element of `GSp(4, ℚ)⁺ ⊆ GL(4, ℚ)`. -/
def spToGSpPlusGL (γ : symplecticGroup (Fin 2) ℚ) : gspPlusGL (Fin 2) :=
  ⟨spRatToGL (Fin 2) γ, (ofSp γ).2⟩

lemma coe_spToGSpPlusGL (γ : symplecticGroup (Fin 2) ℚ) :
    (spToGSpPlusGL γ : GL (Fin 2 ⊕ Fin 2) ℚ) = spRatToGL (Fin 2) γ :=
  rfl

/-- `ι(γ)` for the representatives `γ` of `Γ₀(p) \ SL(2, ℤ)` (`SiegelUpperHalfSpace.thetaIota`),
as an element of `Sp(4, ℚ)`. -/
def thetaIotaSp (i : Option (Fin p)) : symplecticGroup (Fin 2) ℚ :=
  SymplecticGroup.paramodularConj ![1, 1] ⟨thetaIota p i, thetaIota_mem_paramodularGL p 1 i⟩

lemma coe_thetaIotaSp (i : Option (Fin p)) :
    (thetaIotaSp p i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
      (thetaIota p i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) :=
  paramodularDelta_mul_thetaIota p 1 i

lemma paramodularConj_thetaIota (N : ℕ+) (i : Option (Fin p)) :
    SymplecticGroup.paramodularConj ![1, N] ⟨thetaIota p i, thetaIota_mem_paramodularGL p N i⟩ =
      thetaIotaSp p i :=
  Subtype.ext <| (paramodularDelta_mul_thetaIota p N i).trans (coe_thetaIotaSp p i).symm

lemma thetaIotaSp_mem_paramodularLevel (N : ℕ+) (i : Option (Fin p)) :
    thetaIotaSp p i ∈ paramodularLevel N :=
  ⟨_, paramodularConj_thetaIota p N i⟩

/-- The representative `diag(p, p, 1, 1) ι(γ)` of a right coset of `K(M) diag(p, p, 1, 1) K(Mp)`,
for the representatives `γ = (1, 0; c, 1)`, `0 ≤ c < p`, and `γ = (0, -1; 1, 0)` of
`Γ₀(p) \ SL(2, ℤ)`, as an element of `GSp(4, ℚ)⁺`. -/
def thetaRep (i : Option (Fin p)) : gspPlusGL (Fin 2) :=
  thetaPrimeDiag p * spToGSpPlusGL (thetaIotaSp p i)

lemma coe_thetaRep (i : Option (Fin p)) : (thetaRep p i : GL (Fin 2 ⊕ Fin 2) ℚ) =
    (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * spRatToGL (Fin 2) (thetaIotaSp p i) :=
  rfl

/-- The index of the representative `γ` of `Γ₀(p) \ SL(2, ℤ)` with `p ∣ (g ι(γ)⁻¹)(f₁, e₁)`, for an
integral matrix `g`: `γ = (0, -1; 1, 0)` if `p ∣ g(f₁, f₁)`, and otherwise `γ = (1, 0; c, 1)` with
`c ≡ g(f₁, e₁) / g(f₁, f₁) mod p`. -/
private def thetaIotaIndex (g : GL (Fin 2 ⊕ Fin 2) ℤ) : Option (Fin p) :=
  if (p : ℤ) ∣ (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inr 0) then none
  else some ⟨(((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inl 0) : ZMod p) *
    ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inr 0) : ZMod p)⁻¹).val,
      ZMod.val_lt _⟩

private lemma dvd_mul_thetaIota_inv (hp : (p : ℕ).Prime) (g : GL (Fin 2 ⊕ Fin 2) ℤ) :
    (p : ℤ) ∣ ((g * (thetaIota p (thetaIotaIndex p g))⁻¹ : GL (Fin 2 ⊕ Fin 2) ℤ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inl 0) := by
  rw [thetaIotaIndex]
  split_ifs with h
  · simpa [thetaIota, iotaGL, iotaMatrix, Matrix.mul_apply] using h
  · have hp' : Fact (p : ℕ).Prime := ⟨hp⟩
    have hne : ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inr 0) : ZMod p) ≠ 0 :=
      fun h0 ↦ h <| (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [thetaIota, iotaGL, iotaMatrix, ZMod.natCast_val, Units.inv_mk, Units.val_mul,
      Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, Fin.sum_univ_two,
      diagonal_apply_eq, cons_val_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true,
      diagonal_apply_ne, mul_zero, add_zero, fromBlocks_apply₂₁, mul_neg, Int.cast_add,
      Int.cast_neg, Int.cast_mul, ZMod.intCast_cast, ZMod.cast_id', id_eq]
    rw [mul_left_comm, mul_inv_cancel₀ hne, mul_one, add_neg_cancel]

private lemma coe_spRatToGL (γ : symplecticGroup (Fin 2) ℚ) :
    ((spRatToGL (Fin 2) γ : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = γ :=
  rfl

private lemma paramodularConj_apply_inr_zero {N : ℕ+} {g : GL (Fin 2 ⊕ Fin 2) ℤ}
    (hg : g ∈ SymplecticGroup.paramodularGL ![1, N]) {j : Fin 2 ⊕ Fin 2}
    (hj : j = .inl 0 ∨ j = .inr 0) :
    ((spRatToGL (Fin 2) (SymplecticGroup.paramodularConj ![1, N] ⟨g, hg⟩) :
      GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inr 0) j =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) j := by
  rw [coe_spRatToGL]
  rcases hj with rfl | rfl <;>
    simp [SymplecticGroup.paramodularConj, SymplecticGroup.paramodularDelta,
      SymplecticGroup.paramodularDeltaInv, Matrix.mul_apply]

/-- **The double coset `K(M) diag(p, p, 1, 1) K(Mp)` is the union of the `p + 1` right cosets
`K(M) diag(p, p, 1, 1) ι(γ)`**, for the representatives `γ = (1, 0; c, 1)`, `0 ≤ c < p`, and
`γ = (0, -1; 1, 0)` of `Γ₀(p) \ SL(2, ℤ)`: an element `γ'` of `K(Mp)` lies in
`diag(p, p, 1, 1)⁻¹ K(M) diag(p, p, 1, 1) ι(γ)` as soon as the `(f₁, e₁)`-entry of `γ' ι(γ)⁻¹` is
divisible by `p`, and one of the `γ` achieves this. -/
lemma doubleCoset_thetaPrimeDiag (hp : (p : ℕ).Prime) :
    DoubleCoset.doubleCoset (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)
      (heckeGammaOf (paramodularLevel M) : Set (GL (Fin 2 ⊕ Fin 2) ℚ))
        (heckeGammaOf (paramodularLevel (M * p))) =
      ⋃ i, MulOpposite.op (thetaRep p i : GL (Fin 2 ⊕ Fin 2) ℚ) •
        (heckeGammaOf (paramodularLevel M) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) := by
  ext x
  rw [DoubleCoset.mem_doubleCoset, Set.mem_iUnion]
  constructor
  · rintro ⟨h₁, hh₁, h₂, ⟨-, ⟨⟨g, hg⟩, rfl⟩, rfl⟩, rfl⟩
    have hi : (p : ℤ) ∣ ((g * (thetaIota p (thetaIotaIndex p g))⁻¹ : GL (Fin 2 ⊕ Fin 2) ℤ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inl 0) :=
      dvd_mul_thetaIota_inv p hp g
    generalize thetaIotaIndex p g = i at hi
    have hg' : g * (thetaIota p i)⁻¹ ∈ SymplecticGroup.paramodularGL ![1, M * p] :=
      mul_mem hg (inv_mem (thetaIota_mem_paramodularGL p (M * p) i))
    have hconj : SymplecticGroup.paramodularConj ![1, M * p] ⟨_, hg'⟩ =
        SymplecticGroup.paramodularConj ![1, M * p] ⟨g, hg⟩ * (thetaIotaSp p i)⁻¹ := by
      rw [← paramodularConj_thetaIota p (M * p) i, ← map_inv, ← map_mul]
      rfl
    refine ⟨i, Set.mem_smul_set.mpr ⟨h₁ * ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) *
      spRatToGL (Fin 2) (SymplecticGroup.paramodularConj ![1, M * p] ⟨_, hg'⟩) *
        (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹),
      mul_mem hh₁ (thetaPrimeDiag_mul_mul_inv_mem_heckeGammaOf M p hg' hi), ?_⟩⟩
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hconj, map_mul, map_inv, coe_thetaRep]
    group
  · rintro ⟨i, hi⟩
    rcases Set.mem_smul_set.mp hi with ⟨y, hy, rfl⟩
    refine ⟨y, hy, spRatToGL (Fin 2) (thetaIotaSp p i),
      ⟨_, thetaIotaSp_mem_paramodularLevel p (M * p) i, rfl⟩, ?_⟩
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, coe_thetaRep, mul_assoc]

/-- **The right cosets `K(M) diag(p, p, 1, 1) ι(γ)` are pairwise distinct**: if
`y diag(p, p, 1, 1) ι(γ') = diag(p, p, 1, 1) ι(γ)` with `y ∈ K(M)`, the `(f₁, e₁)`- and
`(f₁, f₁)`-entries of `y` are integers, and comparing the `(f₁, e₁)`- and `(f₁, f₁)`-entries of
both sides forces `γ = γ'`. -/
lemma thetaRep_injective (hp : (p : ℕ).Prime) :
    Function.Injective fun i ↦ MulOpposite.op (thetaRep p i : GL (Fin 2 ⊕ Fin 2) ℚ) •
      (heckeGammaOf (paramodularLevel M) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) := by
  intro i j hij
  have hi : (thetaRep p i : GL (Fin 2 ⊕ Fin 2) ℚ) ∈
      MulOpposite.op (thetaRep p j : GL (Fin 2 ⊕ Fin 2) ℚ) •
        (heckeGammaOf (paramodularLevel M) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) := by
    refine (congrArg (_ ∈ ·) hij).mp (Set.mem_smul_set.mpr ⟨1, one_mem _, ?_⟩)
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul]
  rcases Set.mem_smul_set.mp hi with ⟨-, ⟨-, ⟨⟨g, hg⟩, rfl⟩, rfl⟩, hy⟩
  rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, coe_thetaRep, coe_thetaRep] at hy
  have h1 : ((spRatToGL (Fin 2) (SymplecticGroup.paramodularConj ![1, M] ⟨g, hg⟩) *
      ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * spRatToGL (Fin 2) (thetaIotaSp p j)) :
        GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inr 0) (.inl 0) =
      (((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * spRatToGL (Fin 2) (thetaIotaSp p i) :
        GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inr 0) (.inl 0) := by
    rw [hy]
  have h2 : ((spRatToGL (Fin 2) (SymplecticGroup.paramodularConj ![1, M] ⟨g, hg⟩) *
      ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * spRatToGL (Fin 2) (thetaIotaSp p j)) :
        GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inr 0) (.inr 0) =
      (((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * spRatToGL (Fin 2) (thetaIotaSp p i) :
        GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inr 0) (.inr 0) := by
    rw [hy]
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h1 h2
  rw [paramodularConj_apply_inr_zero hg (.inl rfl),
    paramodularConj_apply_inr_zero hg (.inr rfl)] at h1 h2
  generalize (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inl 0) = x at h1 h2
  generalize (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inr 0) = y at h1 h2
  have hp1 : ((p : ℕ) : ℤ) ≠ 1 := by
    have h : 1 < (p : ℕ) := hp.one_lt
    omega
  rcases i with _ | a <;> rcases j with _ | b <;>
    simp only [thetaPrimeDiag, diagSimilitude, Units.mk0_one, TauCeti.diagGL_apply, ↓reduceIte,
      elim_inl, Units.val_mk0, coe_spRatToGL, coe_thetaIotaSp, thetaIota, iotaGL, iotaMatrix,
      Int.coe_castRingHom, map_apply, fromBlocks_apply₁₁, diagonal_apply_eq, cons_val_zero,
      Int.cast_zero, mul_zero, inl.injEq, ne_eq, one_ne_zero, not_false_eq_true, diagonal_apply_ne,
      add_zero, reduceCtorEq, fromBlocks_apply₂₁, Int.cast_one, mul_one, elim_inr, Units.val_one,
      inr.injEq, zero_add, Rat.intCast_eq_one_iff, fromBlocks_apply₁₂, Int.cast_neg, mul_neg,
      fromBlocks_apply₂₂, neg_zero, neg_eq_zero, mul_eq_zero, Int.cast_eq_zero, Nat.cast_eq_zero,
      PNat.ne_zero, zero_mul, one_mul] at h1 h2
  · rfl
  · rw [h2, Int.cast_zero, zero_mul, add_zero] at h1
    exact absurd (Int.eq_one_of_mul_eq_one_left (by positivity) (by exact_mod_cast h1)) hp1
  · refine absurd (Int.eq_one_of_mul_eq_one_left (a := -x) (by positivity) ?_) hp1
    rw [neg_mul]
    exact_mod_cast h2
  · rw [h2, Int.cast_one, one_mul] at h1
    have h : x * (p : ℕ) + (b : ℕ) = ((a : ℕ) : ℤ) := by
      exact_mod_cast h1
    have ha : ((a : ℕ) : ℤ) < (p : ℕ) := by
      exact_mod_cast a.isLt
    have hb : ((b : ℕ) : ℤ) < (p : ℕ) := by
      exact_mod_cast b.isLt
    have hx : x = 0 := by
      rcases lt_trichotomy x 0 with hx | hx | hx
      · nlinarith
      · exact hx
      · nlinarith
    rw [hx, zero_mul, zero_add] at h
    exact congrArg some (Fin.ext (by exact_mod_cast h.symm))

/-- **The level raising operator `θ_p` of Roberts and Schmidt**: the double coset operator
`SiegelUpperHalfSpace.levelRaisingThetaPrime` of `K(M) diag(p, p, 1, 1) K(Mp)` is
`F ↦ ∑_γ F ∣_ρ diag(p, p, 1, 1) ι(γ)` over the representatives `γ = (1, 0; c, 1)`, `0 ≤ c < p`,
and `γ = (0, -1; 1, 0)` of `Γ₀(p) \ SL(2, ℤ)` (Roberts–Schmidt, equation (10)). -/
lemma coe_levelRaisingThetaPrime (hp : (p : ℕ).Prime)
    (F : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M))) :
    (levelRaisingThetaPrime ρ M p F : SiegelUpperHalfSpace (Fin 2) → V) =
      ∑ i, heckeMonoidSlash ρ (thetaRep p i) F := by
  rw [levelRaisingThetaPrime,
    doubleCosetOperator_eq_sum ρ _ (thetaRep p) ?_ (thetaRep_injective M p hp)]
  rw [← HeckeCoset.rep_def, HeckeCoset.doubleCoset_rep_mk]
  exact doubleCoset_thetaPrimeDiag M p hp

lemma gspDenom_thetaPrimeDiag (τ : SiegelUpperHalfSpace (Fin 2)) :
    gspDenom (submonoidToGSpPlus (thetaPrimeDiag p)) τ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gspDenom, submonoidToGSpPlus, thetaPrimeDiag, diagSimilitude, toBlocks₂₁,
      Matrix.mul_apply]

lemma gspSmul_thetaPrimeDiag (τ : SiegelUpperHalfSpace (Fin 2)) :
    (gspSmul (submonoidToGSpPlus (thetaPrimeDiag p)) τ).val = (p : ℂ) • τ.val := by
  rw [gspSmul_val, gspDenom_thetaPrimeDiag, inv_one, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gspNum, submonoidToGSpPlus, thetaPrimeDiag, diagSimilitude, Matrix.mul_apply]

/-- **The slash operator of `diag(p, p, 1, 1)` preserves the vanishing of the Siegel operator**:
`(G ∣_ρ diag(p, p, 1, 1))(τ) = c G(pτ)` for a constant `c`, and `p diag(τ', it) = diag(pτ', ipt)`
with `pt → ∞` as `t → ∞`. -/
lemma SiegelOperatorVanishes.heckeMonoidSlash_thetaPrimeDiag {G : SiegelUpperHalfSpace (Fin 2) → V}
    (hG : SiegelOperatorVanishes G) :
    SiegelOperatorVanishes (heckeMonoidSlash ρ (thetaPrimeDiag p) G) := fun τ' φ ↦ by
  let τ'' : UpperHalfPlane := .mk ((p : ℂ) * τ') (by
    simpa using mul_pos (by positivity : (0 : ℝ) < p) τ'.im_pos)
  let s : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ) := fun t ↦
    ⟨(p : ℝ) * t, mul_pos (by positivity : (0 : ℝ) < p) t.2⟩
  have hs : Tendsto s atTop atTop := tendsto_atTop.mpr fun b ↦ eventually_atTop.mpr ⟨b,
    fun a ha ↦ Subtype.coe_le_coe.mp <| (Subtype.coe_le_coe.mpr ha).trans <|
      le_mul_of_one_le_left a.2.le (by exact_mod_cast (one_le : (1 : ℕ+) ≤ p))⟩
  have hpt (t : Set.Ioi (0 : ℝ)) :
      gspSmul (submonoidToGSpPlus (thetaPrimeDiag p)) (diagPoint τ' t) = diagPoint τ'' (s t) := by
    refine SiegelUpperHalfSpace.ext ?_
    rw [gspSmul_thetaPrimeDiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagPoint, τ'', s, mul_assoc]
  have hden (τ : SiegelUpperHalfSpace (Fin 2)) :
      gspDenomGL (submonoidToGSpPlus (thetaPrimeDiag p)) τ = 1 :=
    Units.ext <| by rw [coe_gspDenomGL, gspDenom_thetaPrimeDiag, Units.val_one]
  simpa [heckeMonoidSlash, gspSlash, hden, hpt] using ((hG τ'' φ).comp hs).const_mul _

/-- The conjugate `diag(p, p, 1, 1) γ diag(p, p, 1, 1)⁻¹` of `γ ∈ Sp(4, ℚ)`, in `Sp(4, ℚ)`. -/
def thetaPrimeDiagConj (γ : symplecticGroup (Fin 2) ℚ) : symplecticGroup (Fin 2) ℚ :=
  ⟨((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * spRatToGL (Fin 2) γ *
    (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ), by
    have hD (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
        ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ *
          (J (Fin 2) ℚ * ((thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * X)) =
            (p : ℚ) • (J (Fin 2) ℚ * X) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.smul_mul]
      congr 1
      ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
        simp [thetaPrimeDiag, diagSimilitude, J]
    have hDinv : (thetaPrimeDiagInv p)ᵀ * (J (Fin 2) ℚ * thetaPrimeDiagInv p) =
        (p : ℚ)⁻¹ • J (Fin 2) ℚ := by
      ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
        simp [thetaPrimeDiagInv, J, Matrix.mul_apply]
    have hγ (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ * (J (Fin 2) ℚ * (γ * X)) =
          J (Fin 2) ℚ * X := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, SymplecticGroup.mem_iff'.mp γ.2]
    rw [SymplecticGroup.mem_iff', Units.val_mul, Units.val_mul, coe_thetaPrimeDiag_inv]
    simp only [transpose_mul, Matrix.mul_assoc, coe_spRatToGL, hD, Matrix.mul_smul, hγ, hDinv,
      smul_smul]
    rw [mul_inv_cancel₀ (by positivity), one_smul]⟩

lemma spRatToGL_thetaPrimeDiagConj (γ : symplecticGroup (Fin 2) ℚ) :
    spRatToGL (Fin 2) (thetaPrimeDiagConj p γ) = (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) *
      spRatToGL (Fin 2) γ * (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ :=
  Units.ext rfl

/-- **The slash operator of `diag(p, p, 1, 1)` preserves cusp forms**: for `γ ∈ Sp(4, ℚ)`,
`F ∣ diag(p, p, 1, 1) ∣ γ = F ∣ γ' ∣ diag(p, p, 1, 1)` with
`γ' = diag(p, p, 1, 1) γ diag(p, p, 1, 1)⁻¹ ∈ Sp(4, ℚ)`, whose Siegel operator vanishes. -/
lemma IsCuspForm.heckeMonoidSlash_thetaPrimeDiag {f : SiegelUpperHalfSpace (Fin 2) → V}
    (hf : IsCuspForm ρ f) : IsCuspForm ρ (heckeMonoidSlash ρ (thetaPrimeDiag p) f) := fun γ ↦ by
  have h : thetaPrimeDiag p * spToGSpPlusGL γ =
      spToGSpPlusGL (thetaPrimeDiagConj p γ) * thetaPrimeDiag p :=
    Subtype.ext <| by
      rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_spToGSpPlusGL, coe_spToGSpPlusGL,
        spRatToGL_thetaPrimeDiagConj, inv_mul_cancel_right]
  rw [← heckeMonoidSlash_eq_slash ρ _ (coe_spToGSpPlusGL γ), ← heckeMonoidSlash_mul, h,
    heckeMonoidSlash_mul, heckeMonoidSlash_eq_slash ρ _ (coe_spToGSpPlusGL _)]
  exact (hf (thetaPrimeDiagConj p γ)).heckeMonoidSlash_thetaPrimeDiag ρ p

private lemma isCuspForm_sum {ι : Type*} (s : Finset ι) {f : ι → SiegelUpperHalfSpace (Fin 2) → V}
    (hf : ∀ i ∈ s, IsCuspForm ρ (f i)) : IsCuspForm ρ (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (IsCuspForm ρ)
    (fun _ _ hg hg' γ ↦ by
      rw [slash_add]
      exact (hg γ).add (hg' γ))
    (fun γ ↦ by
      rw [slash_zero]
      exact siegelOperatorVanishes_zero) hf

/-- **The level raising operator `θ_p` maps `S_ρ(K(M))` to `S_ρ(K(Mp))`** when the slash
operator of `GSp(4, ℚ)⁺` preserves holomorphy, as it does for the holomorphic representations `ρ`
of the LMFDB: `θ_p F = ∑_γ (F ∣_ρ diag(p, p, 1, 1)) ∣_ρ ι(γ)` is `K(Mp)`-invariant, holomorphic,
and a cusp form, the slash operator of `diag(p, p, 1, 1)` preserving cusp forms. -/
lemma levelRaisingThetaPrime_mem_paramodularCuspForms (hp : (p : ℕ).Prime)
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f))
    {F : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M))}
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → V) ∈ paramodularCuspForms ρ M) :
    (levelRaisingThetaPrime ρ M p F : SiegelUpperHalfSpace (Fin 2) → V) ∈
      paramodularCuspForms ρ (M * p) := by
  refine ⟨(mem_modularForms_iff_slashInvariantsOf ρ _ _).mpr
    ⟨?_, fun γ hγ ↦ (levelRaisingThetaPrime ρ M p F).2 γ hγ⟩, ?_⟩ <;>
  rw [coe_levelRaisingThetaPrime ρ M p hp]
  · exact Finset.sum_induction _ IsHolomorphic (fun _ _ ↦ IsHolomorphic.add) isHolomorphic_zero
      fun _ _ ↦ hρ _ _ hF.1.1
  · refine isCuspForm_sum ρ _ fun i _ ↦ ?_
    rw [thetaRep, heckeMonoidSlash_mul, heckeMonoidSlash_eq_slash ρ _ (coe_spToGSpPlusGL _)]
    exact (hF.2.heckeMonoidSlash_thetaPrimeDiag ρ p).slash ρ (thetaIotaSp p i)

end SiegelUpperHalfSpace
