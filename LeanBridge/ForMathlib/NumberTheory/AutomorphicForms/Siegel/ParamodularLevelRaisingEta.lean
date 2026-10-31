import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularLevelRaising

/-!
# The level raising operator `η` is a slash operator

The level raising operator `η` of Roberts and Schmidt from paramodular forms of level `M` to those
of level `Mp²` is the double coset operator of `K(M) η K(Mp²)`, `η = diag(1, p, 1, p⁻¹)`
(`SiegelUpperHalfSpace.levelRaisingEta`). This file proves that `η K(Mp²) η⁻¹ ⊆ K(M)`, so that the
double coset is the single right coset `K(M) η` and `η` is the slash operator
`F ↦ F ∣_ρ diag(1, p, 1, p⁻¹)`, that is `(ηF)(τ, z, ω) = ρ(diag(1, p)) F(τ, pz, p²ω)`. In terms of
the integral isometry groups `Γ(T_N)` of `T_N = (0, d; -d, 0)`, `d = diag(1, N)`, whose conjugates
by `δ_N = diag(1, 1, 1, N)` are the `K(N)`, this is the inclusion `D Γ(T_{Mp²}) D⁻¹ ⊆ Γ(T_M)` for
`D = diag(1, p, 1, p)`: an element `g` of `Γ(T_N)` has its entries `(1, 2)`, `(1, 4)`, `(3, 2)`
and `(3, 4)` divisible by `N`, read off from `T_N g = g⁻ᵀ T_N`.

## Main results

* `SiegelUpperHalfSpace.etaDiag_mul_mul_inv_mem_heckeGammaOf`:
  `diag(1, p, 1, p⁻¹) K(Mp²) diag(1, p, 1, p⁻¹)⁻¹ ⊆ K(M)`.
* `SiegelUpperHalfSpace.doubleCoset_etaDiag`: `K(M) η K(Mp²) = K(M) η`.
* `SiegelUpperHalfSpace.coe_levelRaisingEta`: the level raising operator `η` is the slash operator
  of `diag(1, p, 1, p⁻¹)`.
-/

open Matrix

open scoped Pointwise

namespace SiegelUpperHalfSpace

variable {N : ℕ+} {g : GL (Fin 2 ⊕ Fin 2) ℤ}

private lemma paramodularForm_mul_eq (hg : g ∈ SymplecticGroup.paramodularGL ![1, N]) :
    SymplecticGroup.paramodularForm ![1, N] * (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) =
      (↑g⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)ᵀ *
        SymplecticGroup.paramodularForm ![1, N] := by
  have h : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)ᵀ *
      SymplecticGroup.paramodularForm ![1, N] * g = SymplecticGroup.paramodularForm ![1, N] :=
    hg
  rw [eq_comm]
  nth_rewrite 1 [← h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one,
    Matrix.one_mul]

lemma dvd_apply_of_mem_paramodularGL (hg : g ∈ SymplecticGroup.paramodularGL ![1, N])
    {i j : Fin 2 ⊕ Fin 2} (hi : i = .inl 0 ∨ i = .inr 0) (hj : j = .inl 1 ∨ j = .inr 1) :
    (N : ℤ) ∣ (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) i j := by
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · have h : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inl 0) (.inl 1) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)⁻¹ (.inr 1) (.inr 0) * N := by
      simpa [Matrix.mul_apply, SymplecticGroup.paramodularForm] using
        congrFun (congrFun (paramodularForm_mul_eq hg) (.inr 0)) (.inl 1)
    exact Dvd.intro_left _ h.symm
  · have h : -(g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inl 0) (.inr 1) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)⁻¹ (.inl 1) (.inr 0) * N := by
      simpa [Matrix.mul_apply, SymplecticGroup.paramodularForm] using
        congrFun (congrFun (paramodularForm_mul_eq hg) (.inr 0)) (.inr 1)
    exact dvd_neg.mp (Dvd.intro_left _ h.symm)
  · have h : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inl 1) =
        -((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)⁻¹ (.inr 1) (.inl 0) * N) := by
      simpa [Matrix.mul_apply, SymplecticGroup.paramodularForm] using
        congrFun (congrFun (paramodularForm_mul_eq hg) (.inl 0)) (.inl 1)
    rw [h]
    exact dvd_neg.mpr (Dvd.intro_left _ rfl)
  · have h : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (.inr 0) (.inr 1) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)⁻¹ (.inl 1) (.inl 0) * N := by
      simpa [Matrix.mul_apply, SymplecticGroup.paramodularForm] using
        congrFun (congrFun (paramodularForm_mul_eq hg) (.inl 0)) (.inr 1)
    exact Dvd.intro_left _ h.symm

variable (M p : ℕ+)

/-- The matrix `D = diag(1, p, 1, p)`. -/
private def etaConj : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  diagonal (Sum.elim ![1, (p : ℚ)] ![1, (p : ℚ)])

/-- The matrix `D⁻¹ = diag(1, p⁻¹, 1, p⁻¹)`. -/
private def etaConjInv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  diagonal (Sum.elim ![1, (p : ℚ)⁻¹] ![1, (p : ℚ)⁻¹])

/-- The matrix `diag(1, p⁻¹, 1, p)`, the inverse of `η`. -/
private def etaDiagInv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  diagonal (Sum.elim ![1, (p : ℚ)⁻¹] ![1, (p : ℚ)])

private lemma etaDiag_mul_paramodularDelta :
    ((etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) *
      SymplecticGroup.paramodularDelta ![1, M * p * p] =
        SymplecticGroup.paramodularDelta ![1, M] * etaConj p := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [etaDiag, diagSimilitude, etaConj, SymplecticGroup.paramodularDelta]
  field_simp

private lemma coe_etaDiag_inv :
    (((etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = etaDiagInv p :=
  Units.inv_eq_of_mul_eq_one_right <| by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [etaDiag, diagSimilitude, etaDiagInv]

private lemma paramodularDeltaInv_mul_etaDiagInv :
    SymplecticGroup.paramodularDeltaInv ![1, M * p * p] * etaDiagInv p =
      etaConjInv p * SymplecticGroup.paramodularDeltaInv ![1, M] := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [etaDiagInv, etaConjInv, SymplecticGroup.paramodularDeltaInv]
  field_simp

private lemma etaConj_mul_etaConjInv : etaConj p * etaConjInv p = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [etaConj, etaConjInv]

private lemma etaConjInv_mul_etaConj : etaConjInv p * etaConj p = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [etaConj, etaConjInv]

private lemma transpose_etaConj : (etaConj p)ᵀ = etaConj p :=
  diagonal_transpose _

private lemma transpose_etaConjInv : (etaConjInv p)ᵀ = etaConjInv p :=
  diagonal_transpose _

private lemma etaConjInv_mul_paramodularForm :
    etaConjInv p * (SymplecticGroup.paramodularForm ![1, M * p * p]).map (Int.castRingHom ℚ) *
      etaConjInv p = (SymplecticGroup.paramodularForm ![1, M]).map (Int.castRingHom ℚ) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [etaConjInv, SymplecticGroup.paramodularForm] <;>
    field_simp

/-- The integral conjugate `D A D⁻¹` of an integral matrix `A` with `p ∣ A i j` for
`i ∈ {1, 3}` and `j ∈ {2, 4}`, for `D = diag(1, p, 1, p)`. -/
private def etaConjInt (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  of fun i j ↦
    Sum.elim ![1, (p : ℤ)] ![1, (p : ℤ)] i * A i j / Sum.elim ![1, (p : ℤ)] ![1, (p : ℤ)] j

private lemma map_etaConjInt {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ}
    (hA : ∀ i j, (i = .inl 0 ∨ i = .inr 0) → (j = .inl 1 ∨ j = .inr 1) → (p : ℤ) ∣ A i j) :
    (etaConjInt p A).map (Int.castRingHom ℚ) =
      etaConj p * A.map (Int.castRingHom ℚ) * etaConjInv p := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [etaConjInt, etaConj, etaConjInv, hA] <;> field_simp

/-- **`η = diag(1, p, 1, p⁻¹)` conjugates `K(Mp²)` into `K(M)`**: for `γ ∈ K(Mp²)`, `ηγη⁻¹ ∈ K(M)`.
Writing `γ = δ g δ⁻¹` with `g` in the integral isometry group of `T_{Mp²}`, `ηγη⁻¹` is
`δ' (D g D⁻¹) δ'⁻¹` with `D = diag(1, p, 1, p)`, and `D g D⁻¹` is integral, of determinant `±1`,
and an isometry of `T_M`. -/
lemma etaDiag_mul_mul_inv_mem_heckeGammaOf {x : GL (Fin 2 ⊕ Fin 2) ℚ}
    (hx : x ∈ heckeGammaOf (paramodularLevel (M * p * p))) :
    (etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * x * (etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ ∈
      heckeGammaOf (paramodularLevel M) := by
  rcases hx with ⟨γ, hγ, rfl⟩
  rcases (SymplecticGroup.mem_paramodular_iff _).mp hγ with ⟨g, hg, hγg⟩
  have hdvd : ∀ i j, (i = .inl 0 ∨ i = .inr 0) → (j = .inl 1 ∨ j = .inr 1) →
      (p : ℤ) ∣ (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) i j := fun _ _ hi hj ↦
    (Dvd.intro_left ((M * p : ℕ+) : ℤ) (by push_cast; ring1)).trans
      (dvd_apply_of_mem_paramodularGL hg hi hj)
  have hA : (etaConjInt p g).map (Int.castRingHom ℚ) =
      etaConj p * (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) *
        etaConjInv p :=
    map_etaConjInt p hdvd
  have hdet : IsUnit (etaConjInt p g).det := by
    have h : (((etaConjInt p g).det : ℤ) : ℚ) =
        (((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).det : ℤ) : ℚ) := by
      rw [← eq_intCast (Int.castRingHom ℚ), ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det,
        RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hA, det_mul, det_mul,
        mul_right_comm, ← det_mul, etaConj_mul_etaConjInv, det_one, one_mul]
    rw [Int.cast_inj.mp h]
    exact isUnits_det_units g
  have hgq : ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ))ᵀ *
      (SymplecticGroup.paramodularForm ![1, M * p * p]).map (Int.castRingHom ℚ) *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) =
      (SymplecticGroup.paramodularForm ![1, M * p * p]).map (Int.castRingHom ℚ) := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (Matrix.map · (Int.castRingHom ℚ)) hg
  have hgq' (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ))ᵀ *
        ((SymplecticGroup.paramodularForm ![1, M * p * p]).map (Int.castRingHom ℚ) *
          ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (Int.castRingHom ℚ) * X)) =
      (SymplecticGroup.paramodularForm ![1, M * p * p]).map (Int.castRingHom ℚ) * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgq]
  have hDD (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) : etaConj p * (etaConjInv p * X) = X := by
    rw [← Matrix.mul_assoc, etaConj_mul_etaConjInv, Matrix.one_mul]
  have hDD' (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      etaConjInv p * (etaConj p * X) = X := by
    rw [← Matrix.mul_assoc, etaConjInv_mul_etaConj, Matrix.one_mul]
  have hT : (etaConjInt p g)ᵀ * SymplecticGroup.paramodularForm ![1, M] * etaConjInt p g =
      SymplecticGroup.paramodularForm ![1, M] := by
    refine Matrix.map_injective (Int.cast_injective (α := ℚ)) ?_
    have e (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) :
        X.map Int.cast = X.map (Int.castRingHom ℚ) :=
      rfl
    simp only [e, Matrix.map_mul, transpose_map, hA, ← etaConjInv_mul_paramodularForm M p,
      transpose_mul, transpose_etaConj, transpose_etaConjInv, Matrix.mul_assoc, hDD, hDD', hgq']
  let g' : GL (Fin 2 ⊕ Fin 2) ℤ := ((isUnit_iff_isUnit_det _).mpr hdet).unit
  have hg'v : (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) = etaConjInt p g :=
    IsUnit.unit_spec _
  have hg' : g' ∈ SymplecticGroup.paramodularGL ![1, M] :=
    (congrArg (fun A ↦ Aᵀ * SymplecticGroup.paramodularForm ![1, M] * A) hg'v).trans hT
  refine ⟨SymplecticGroup.paramodularConj ![1, M] ⟨g', hg'⟩, ⟨⟨g', hg'⟩, rfl⟩, Units.ext ?_⟩
  have hL : ((spRatToGL (Fin 2) (SymplecticGroup.paramodularConj ![1, M] ⟨g', hg'⟩) :
      GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
        SymplecticGroup.paramodularDelta ![1, M] * (etaConjInt p g).map (Int.castRingHom ℚ) *
          SymplecticGroup.paramodularDeltaInv ![1, M] := by
    rw [← hg'v]
    rfl
  have hR : ((spRatToGL (Fin 2) γ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = γ :=
    rfl
  have hη (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) :
      ((etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) *
        (SymplecticGroup.paramodularDelta ![1, M * p * p] * X) =
          SymplecticGroup.paramodularDelta ![1, M] * (etaConj p * X) := by
    rw [← Matrix.mul_assoc, etaDiag_mul_paramodularDelta, Matrix.mul_assoc]
  rw [hL, Units.val_mul, Units.val_mul, hR, coe_etaDiag_inv, hA, hγg]
  simp only [Matrix.mul_assoc, paramodularDeltaInv_mul_etaDiagInv, hη]

/-- **The double coset `K(M) η K(Mp²)` is the single right coset `K(M) η`**, for
`η = diag(1, p, 1, p⁻¹)`, since `η K(Mp²) η⁻¹ ⊆ K(M)`. -/
lemma doubleCoset_etaDiag :
    DoubleCoset.doubleCoset (etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)
      (heckeGammaOf (paramodularLevel M) : Set (GL (Fin 2 ⊕ Fin 2) ℚ))
        (heckeGammaOf (paramodularLevel (M * p * p))) =
      MulOpposite.op (etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) •
        (heckeGammaOf (paramodularLevel M) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) := by
  ext x
  rw [DoubleCoset.mem_doubleCoset, Set.mem_smul_set]
  constructor
  · rintro ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    refine ⟨h₁ * ((etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * h₂ * (etaDiag p : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹),
      mul_mem hh₁ (etaDiag_mul_mul_inv_mem_heckeGammaOf M p hh₂), ?_⟩
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    group
  · rintro ⟨h₁, hh₁, rfl⟩
    exact ⟨h₁, hh₁, 1, one_mem _, by
      rw [mul_one, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)

/-- **The level raising operator `η` is the slash operator of `diag(1, p, 1, p⁻¹)`**:
`ηF = F ∣_ρ diag(1, p, 1, p⁻¹)`, that is `(ηF)(τ, z, ω) = ρ(diag(1, p)) F(τ, pz, p²ω)`, the double
coset `K(M) diag(1, p, 1, p⁻¹) K(Mp²)` being a single right coset. -/
lemma coe_levelRaisingEta
    (F : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M))) :
    (levelRaisingEta ρ M p F : SiegelUpperHalfSpace (Fin 2) → V) =
      heckeMonoidSlash ρ (etaDiag p) F := by
  rw [levelRaisingEta, doubleCosetOperator_eq_sum ρ _ (fun _ : Unit ↦ etaDiag p) ?_
    (Function.injective_of_subsingleton _), Fintype.sum_unique]
  rw [← HeckeCoset.rep_def, HeckeCoset.doubleCoset_rep_mk, Set.iUnion_const]
  exact doubleCoset_etaDiag M p

end SiegelUpperHalfSpace
