import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GaloisOrbit

/-!
# Fourier coefficients of Siegel modular forms under the Levi subgroup

The elements `(U, 0; 0, U⁻ᵀ)` of `Γ ⊆ Sp(2g, ℚ)`, with `U ∈ GL(g, ℤ)`, act on `ℋ_g` by
`τ ↦ U τ Uᵀ` with automorphy factor `U⁻ᵀ`, so the transformation law of a Siegel modular form `f`
and the uniqueness of Fourier expansions give `a(Uᵀ n U) = ρ(Uᵀ) a(n)` for the Fourier coefficients
`a` of `f`. This is the computation at the heart of Koecher's principle
(`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.KoecherPrinciple`).

## Main definitions

* `SymplecticGroup.levi`: the Levi embedding `U ↦ (U, 0; 0, U⁻ᵀ)` of `GL(g, R)` in `Sp(2g, R)`.
* `SiegelUpperHalfSpace.leviRat`: the image `(U, 0; 0, U⁻ᵀ)` in `Sp(2g, ℚ)` of `U ∈ GL(g, ℤ)`.
* `SiegelUpperHalfSpace.dualLevi`: the bijection `n ↦ Uᵀ n U` of the dual lattice `L_Γ^∨`.
* `SiegelUpperHalfSpace.basePoint`: the point `i 1_g` of the Siegel upper half-space.
* `SiegelUpperHalfSpace.transposeGL`: the transpose `Dᵀ` of `D ∈ GL(g, ℤ)`.

## Main results

* `SiegelUpperHalfSpace.apply_dualLevi`: `a(Uᵀ n U) = ρ(Uᵀ) a(n)`.
* `SiegelUpperHalfSpace.apply_dualLevi_transposeGL`: `a(D n Dᵀ) = ρ(D) a(n)`.
-/

open Complex Matrix Module

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]

variable (l R) in
/-- The **Levi embedding** `U ↦ (U, 0; 0, U⁻ᵀ)` of `GL(g, R)` in `Sp(2g, R)`, whose image is the
Levi subgroup of the Siegel parabolic subgroup. -/
def levi : GL l R →* symplecticGroup l R where
  toFun U := ⟨fromBlocks U 0 0 (U⁻¹ : GL l R).valᵀ, fromBlocks_mem_iff.mpr ⟨by simp, by simp, by
    rw [transpose_zero, Matrix.zero_mul, sub_zero, ← transpose_mul, Units.inv_mul, transpose_one]⟩⟩
  map_one' := Subtype.ext <| by simp
  map_mul' U V := Subtype.ext <| by simp [fromBlocks_multiply]

lemma coe_levi (U : GL l R) :
    (levi l R U : Matrix (l ⊕ l) (l ⊕ l) R) = fromBlocks U 0 0 (U⁻¹ : GL l R).valᵀ :=
  rfl

end SymplecticGroup

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] {Γ : Subgroup (symplecticGroup l ℚ)} (U : GL l ℤ)
    {S : Type*} [CommRing S] (τ τ' : SiegelUpperHalfSpace l) {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL l ℂ) V) {f : SiegelUpperHalfSpace l → V}
    {a : dualLattice Γ → V}

/-- The image `(U, 0; 0, U⁻ᵀ)` in `Sp(2g, ℚ)` of `U ∈ GL(g, ℤ)`. -/
noncomputable abbrev leviRat : symplecticGroup l ℚ :=
  SymplecticGroup.map (Int.castRingHom ℚ) (SymplecticGroup.levi l ℤ U)

lemma leviRat_mem_integral : leviRat U ∈ SymplecticGroup.integral l :=
  ⟨SymplecticGroup.levi l ℤ U, trivial, rfl⟩

private lemma map_mul_map_inv :
    (U : Matrix l l ℤ).map (Int.cast : ℤ → S) * (U : Matrix l l ℤ)⁻¹.map Int.cast = 1 := by
  have h : ((U : Matrix l l ℤ) * (U⁻¹ : GL l ℤ).val).map (Int.castRingHom S) = 1 := by
    rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [Matrix.map_mul, coe_units_inv] at h

private lemma map_inv_mul_map :
    (U : Matrix l l ℤ)⁻¹.map (Int.cast : ℤ → S) * (U : Matrix l l ℤ).map Int.cast = 1 := by
  have h : ((U⁻¹ : GL l ℤ).val * (U : Matrix l l ℤ)).map (Int.castRingHom S) = 1 := by
    rw [Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [Matrix.map_mul, coe_units_inv] at h

private lemma coe_map_leviRat :
    (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = fromBlocks
      ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℝ)) 0 0
        ((U : Matrix l l ℤ)⁻¹ᵀ.map (Int.cast : ℤ → ℝ)) := by
  rw [SymplecticGroup.coe_map_apply, SymplecticGroup.coe_map_apply, SymplecticGroup.coe_levi,
    coe_units_inv]
  simp [fromBlocks_map]

private lemma num_levi : num (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ.val =
    (U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ) * τ.val := by
  rw [num, coe_map_leviRat]
  simp [Function.comp_def]

lemma denom_leviRat : denom (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ.val =
    (U : Matrix l l ℤ)⁻¹ᵀ.map (Int.cast : ℤ → ℂ) := by
  rw [denom, coe_map_leviRat]
  simp [Function.comp_def]

private lemma val_smul_levi : (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ).val =
    (U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ) * τ.val * ((U : Matrix l l ℤ).map Int.cast)ᵀ := by
  have h :
      ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ))ᵀ * (U : Matrix l l ℤ)⁻¹ᵀ.map Int.cast = 1 := by
    rw [transpose_map, ← transpose_mul, map_inv_mul_map, transpose_one]
  rw [val_smul, num_levi, denom_leviRat, inv_eq_left_inv h]

private lemma denomGL_levi : denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ =
    denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ' :=
  Units.ext <| by rw [coe_denomGL, coe_denomGL, denom_leviRat, denom_leviRat]

private lemma coe_leviRat : (leviRat U : Matrix (l ⊕ l) (l ⊕ l) ℚ) = fromBlocks
    ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ)) 0 0
      ((U : Matrix l l ℤ)⁻¹ᵀ.map (Int.cast : ℤ → ℚ)) := by
  rw [SymplecticGroup.coe_map_apply, SymplecticGroup.coe_levi, coe_units_inv]
  simp [fromBlocks_map]

private lemma coe_leviRat_inv : (((leviRat U)⁻¹ : symplecticGroup l ℚ) : Matrix (l ⊕ l) (l ⊕ l) ℚ) =
    fromBlocks ((U : Matrix l l ℤ)⁻¹.map (Int.cast : ℤ → ℚ)) 0 0
      ((U : Matrix l l ℤ)ᵀ.map (Int.cast : ℤ → ℚ)) := by
  rw [← map_inv, ← map_inv, SymplecticGroup.coe_map_apply, SymplecticGroup.coe_levi, inv_inv,
    coe_units_inv]
  simp [fromBlocks_map]

variable {U}

private lemma mul_mul_transpose_mem_translationLattice (hU : leviRat U ∈ Γ) {s : Matrix l l ℚ}
    (hs : s ∈ translationLattice Γ) : (U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ) * s *
      ((U : Matrix l l ℤ).map Int.cast)ᵀ ∈ translationLattice Γ := by
  rcases hs with ⟨hs, γ, hγ, hγs⟩
  refine ⟨by rw [transpose_mul, transpose_mul, transpose_transpose, hs, Matrix.mul_assoc],
    leviRat U * γ * (leviRat U)⁻¹, Γ.mul_mem (Γ.mul_mem hU hγ) (Γ.inv_mem hU), ?_⟩
  rw [Submonoid.coe_mul, Submonoid.coe_mul, hγs, coe_leviRat, coe_leviRat_inv]
  simp [fromBlocks_multiply, map_mul_map_inv, transpose_map, ← transpose_mul]

private lemma transpose_mul_mul_mem_dualLattice (hU : leviRat U ∈ Γ) {n : Matrix l l ℚ}
    (hn : n ∈ dualLattice Γ) : ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ))ᵀ * n *
      (U : Matrix l l ℤ).map Int.cast ∈ dualLattice Γ := by
  refine ⟨by rw [transpose_mul, transpose_mul, transpose_transpose, hn.1, Matrix.mul_assoc],
    fun s hs ↦ ?_⟩
  rcases hn.2 _ (mul_mul_transpose_mem_translationLattice hU hs) with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [← hz, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]

private lemma leviRat_inv_mem (hU : leviRat U ∈ Γ) : leviRat U⁻¹ ∈ Γ := by
  simpa [leviRat] using Γ.inv_mem hU

private lemma transpose_mul_mul_map_inv (n : Matrix l l S) :
    ((U : Matrix l l ℤ)⁻¹.map (Int.cast : ℤ → S))ᵀ *
      (((U : Matrix l l ℤ).map Int.cast)ᵀ * n * (U : Matrix l l ℤ).map Int.cast) *
        (U : Matrix l l ℤ)⁻¹.map Int.cast = n := by
  have h : ((U : Matrix l l ℤ)⁻¹.map (Int.cast : ℤ → S))ᵀ *
      (((U : Matrix l l ℤ).map Int.cast)ᵀ * n * (U : Matrix l l ℤ).map Int.cast) *
        (U : Matrix l l ℤ)⁻¹.map Int.cast = ((U : Matrix l l ℤ).map Int.cast *
          (U : Matrix l l ℤ)⁻¹.map Int.cast)ᵀ * n *
            ((U : Matrix l l ℤ).map Int.cast * (U : Matrix l l ℤ)⁻¹.map Int.cast) := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [h, map_mul_map_inv, transpose_one, Matrix.one_mul, Matrix.mul_one]

variable (hU : leviRat U ∈ Γ) (n : dualLattice Γ)

variable (U) in
/-- The bijection `n ↦ Uᵀ n U` of the dual lattice `L_Γ^∨`, for `U ∈ GL(g, ℤ)` with
`(U, 0; 0, U⁻ᵀ) ∈ Γ`. -/
def dualLevi : dualLattice Γ ≃ dualLattice Γ where
  toFun n := ⟨_, transpose_mul_mul_mem_dualLattice hU n.2⟩
  invFun n := ⟨_, transpose_mul_mul_mem_dualLattice (leviRat_inv_mem hU) n.2⟩
  left_inv n := Subtype.ext <| by
    simpa using transpose_mul_mul_map_inv (n : Matrix l l ℚ)
  right_inv n := Subtype.ext <| by
    simpa using transpose_mul_mul_map_inv (U := U⁻¹) (n : Matrix l l ℚ)

lemma coe_dualLevi : (dualLevi U hU n : Matrix l l ℚ) =
    ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ))ᵀ * (n : Matrix l l ℚ) *
      (U : Matrix l l ℤ).map Int.cast :=
  rfl

private lemma fourierExp_smul_levi :
    fourierExp n (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ) =
      fourierExp (dualLevi U hU n) τ := by
  have hc : (Rat.castHom ℂ) ∘ (Int.cast : ℤ → ℚ) = (Int.cast : ℤ → ℂ) :=
    funext fun z ↦ map_intCast (Rat.castHom ℂ) z
  rw [fourierExp, fourierExp, val_smul_levi, coe_dualLevi]
  congr 2
  rw [← Rat.coe_castHom, Matrix.map_mul, Matrix.map_mul, transpose_map, Matrix.map_map, hc]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ))ᵀ]
  simp only [Matrix.mul_assoc]

/-- **The Fourier coefficients under the Levi subgroup**: for `f ∈ M_ρ(Γ)` with Fourier coefficients
`a`, and `(U, 0; 0, U⁻ᵀ) ∈ Γ`, one has `a(Uᵀ n U) = ρ(Uᵀ) a(n)`, as `ρ(Uᵀ)` is the inverse of the
automorphy factor `U⁻ᵀ`. -/
lemma apply_dualLevi (hΓ : SymplecticGroup.IsArithmetic Γ) (hf : f ∈ modularForms ρ Γ 1)
    (ha : HasSiegelFourierExpansion Γ f a) : a (dualLevi U hU n) =
      ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ)⁻¹ (a n) := by
  have h₁ : HasSiegelFourierExpansion Γ
      (fun τ ↦ f (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ))
        (fun m ↦ a ((dualLevi U hU).symm m)) := fun τ φ ↦ by
    rw [← (dualLevi U hU).hasSum_iff]
    refine (ha (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ) φ).congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, Equiv.symm_apply_apply, fourierExp_smul_levi τ hU]
  have h₂ : HasSiegelFourierExpansion Γ
      (fun τ ↦ f (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ)) (fun m ↦
        ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ) (a m)) :=
    fun τ₁ φ ↦ by
      have h : f (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ₁) =
          ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ₁) (f τ₁) := by
        simpa using hf.2 ⟨leviRat U, hU⟩ τ₁
      beta_reduce
      rw [h, denomGL_levi U τ₁ τ]
      exact ha τ₁ (φ ∘ₗ ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ))
  have h₃ : a n = ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ)
      (a (dualLevi U hU n)) := by
    simpa using congrFun (h₁.unique_of_isArithmetic hΓ h₂) (dualLevi U hU n)
  rw [h₃, ← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply]

/-- The point `i 1_g` of the Siegel upper half-space. -/
noncomputable def basePoint : SiegelUpperHalfSpace l where
  val := I • 1
  transpose_val := by
    rw [transpose_smul, transpose_one]
  posDef_im := by
    convert PosDef.one (n := l) (R := ℝ)
    ext i j
    rcases eq_or_ne i j with rfl | hij <;> simp [*]

/-- The transpose `Dᵀ` of `D ∈ GL(g, ℤ)`. -/
def transposeGL (D : GL l ℤ) : GL l ℤ where
  val := D.valᵀ
  inv := (D⁻¹).valᵀ
  val_inv := by rw [← transpose_mul, Units.inv_mul, transpose_one]
  inv_val := by rw [← transpose_mul, Units.mul_inv, transpose_one]

/-- **The Fourier coefficients under the Levi subgroup, in terms of `D = Uᵀ`**: for `U = Dᵀ` with
`(U, 0; 0, U⁻ᵀ) ∈ Γ`, one has `a(D n Dᵀ) = ρ(D) a(n)`. -/
lemma apply_dualLevi_transposeGL (D : GL l ℤ) (hD : leviRat (transposeGL D) ∈ Γ)
    (hΓ : SymplecticGroup.IsArithmetic Γ) (hf : f ∈ modularForms ρ Γ 1)
    (ha : HasSiegelFourierExpansion Γ f a) :
    a (dualLevi (transposeGL D) hD n) = ρ (GeneralLinearGroup.map (Int.castRingHom ℂ) D) (a n) := by
  rw [apply_dualLevi basePoint ρ hD n hΓ hf ha]
  congr 2
  refine inv_eq_of_mul_eq_one_left (Units.ext ?_)
  have h : ((GeneralLinearGroup.map (Int.castRingHom ℂ) D : GL l ℂ) : Matrix l l ℂ) =
      (D : Matrix l l ℤ).map Int.cast :=
    rfl
  have e : ((transposeGL D : GL l ℤ) : Matrix l l ℤ)⁻¹ᵀ = (D : Matrix l l ℤ)⁻¹ := by
    have h₂ : ((transposeGL D : GL l ℤ) : Matrix l l ℤ) = (D : Matrix l l ℤ)ᵀ :=
      rfl
    rw [h₂, transpose_nonsing_inv, transpose_transpose]
  rw [Units.val_mul, h, coe_denomGL, denom_leviRat, e, map_mul_map_inv, Units.val_one]

end SiegelUpperHalfSpace
