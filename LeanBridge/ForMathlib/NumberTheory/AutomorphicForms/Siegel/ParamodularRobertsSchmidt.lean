import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularAtkinLehner
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularNewEigenform

/-!
# The level raising operators of Roberts and Schmidt

Roberts and Schmidt (*On modular forms for the paramodular group*, in *Automorphic forms and zeta
functions*, World Scientific 2006, §2, §4; https://sites.math.unt.edu/~schmidt/papers/arakawa.pdf)
normalise the slash operator of `GSp(4, ℚ)⁺` of weight `k` so that scalar matrices act trivially,
`(F ∣_k g)(Z) = λ(g)^k det(CZ + D)^(-k) F(g⟨Z⟩)`, and define, for a prime `p`, the level raising
operators
* `η_p F = F ∣_k η_p⁻¹`, `η_p = diag(1, p⁻¹, 1, p)`, from level `N` to `Np²` (their (7));
* `θ_p F = ∑_γ F ∣_k diag(1, 1, p⁻¹, p⁻¹) ι(γ)`, `γ ∈ Γ₀(p) \ SL(2, ℤ)`, from level `N` to `Np`
  (their (10));
* `θ'_p = u_p ∘ θ_p ∘ u_p`, from level `N` to `Np` (their (14)), with the Atkin–Lehner involutions
  `u_p F = F ∣_k u_p` of levels `N` and `Np`, and they state
  `θ'_p F = η_p F + ∑_{c ∈ ℤ/pℤ} F ∣_k [1, , , ; , 1, , c p⁻¹ N⁻¹; , , 1, ; , , , 1]` (their (16)),
  these matrices being representatives of `K(N) ∩ K(Np) \ K(Np)`.

This file formalises these operators with their normalisation and identifies them with the double
coset operators of LeanBridge. The slash operator `SiegelUpperHalfSpace.gspSlash` for `ρ = det^k`
carries the factor `λ(g)^(2k - 3)`, so that Roberts and Schmidt's is `λ(g)^(3 - k)` times it. So
`θ_p` is `p^(3 - k)` times `SiegelUpperHalfSpace.levelRaisingThetaPrime` (the double coset operator
of `K(N) diag(p, p, 1, 1) K(Np)`), while `η_p` is `SiegelUpperHalfSpace.levelRaisingEta` and `θ'_p`
is the trace `SiegelUpperHalfSpace.levelRaisingTheta`, of `K(N) K(Np)`, with no scalar factor.

The proof of `θ'_p = levelRaisingTheta`: the map `x ↦ (q p)⁻¹ Ξ(U) x Ξ(U')`, for Atkin–Lehner
elements `Ξ(U)`, `Ξ(U')` of levels `N = q M` and `Np`, sends the double coset
`K(N) diag(p, p, 1, 1) K(Np)` onto `K(N) K(Np)` and right cosets of `K(N)` to right cosets of
`K(N)`, since `Ξ(U)`, `Ξ(U')` normalize `K(N)`, `K(Np)` and
`(q p)⁻¹ Ξ(U) diag(p, p, 1, 1) Ξ(U') ∈ K(N)`. Their (16) is then the coset decomposition of
`K(N) K(Np)`, proved on the entries of the elements of `K(Np)`.

## Main definitions

* `SiegelUpperHalfSpace.rsSlash`: the slash operator of Roberts and Schmidt.
* `SiegelUpperHalfSpace.scalarGSp`, `SiegelUpperHalfSpace.scalarInvGSp`: scalar matrices in
  `GSp(4, ℚ)⁺`.
* `SiegelUpperHalfSpace.rsThetaDiag`: the similitude `diag(1, 1, p⁻¹, p⁻¹)`.
* `SiegelUpperHalfSpace.rsTheta`, `SiegelUpperHalfSpace.rsEta`, `SiegelUpperHalfSpace.rsThetaPrime`:
  the operators `θ_p`, `η_p`, `θ'_p` of Roberts and Schmidt.
* `SiegelUpperHalfSpace.AtkinLehnerParam.traceRep`: the representatives
  `(q p)⁻¹ Ξ(U) diag(p, p, 1, 1) ι(γ) Ξ(U')` of `K(N) \ K(N) K(Np)`.
* `SiegelUpperHalfSpace.traceTranslation`, `SiegelUpperHalfSpace.traceWeyl`,
  `SiegelUpperHalfSpace.thetaTraceRep`: the representatives of `K(N) \ K(N) K(Np)` of (16).

## Main results

* `SiegelUpperHalfSpace.doubleCoset_one_eq_iUnion`, `SiegelUpperHalfSpace.injective_op_mul_smul`:
  right coset decompositions under a normalizing pair.
* `SiegelUpperHalfSpace.rsSlash_eq_zpow_smul`: the scalar normalisation of the slash operator.
* `SiegelUpperHalfSpace.rsSlash_mul`, `SiegelUpperHalfSpace.rsSlash_scalarGSp`: it is a right action
  of `GSp(4, ℚ)⁺`, trivial on scalar matrices.
* `SiegelUpperHalfSpace.rsTheta_eq_smul_levelRaisingThetaPrime`: `θ_p` is `p^(3 - k)` times the
  double coset operator of `K(N) diag(p, p, 1, 1) K(Np)`.
* `SiegelUpperHalfSpace.rsEta_eq_levelRaisingEta`: `η_p` is the double coset operator of
  `K(N) diag(1, p, 1, p⁻¹) K(Np²)`.
* `SiegelUpperHalfSpace.IsAtkinLehnerElementAt.rsSlash_eq`,
  `SiegelUpperHalfSpace.IsAtkinLehnerElementAt.rsSlash_rsSlash`: the Atkin–Lehner operators are well
  defined involutions on the `K(N)`-invariant functions.
* `SiegelUpperHalfSpace.AtkinLehnerParam.coe_levelRaisingTheta_eq_sum_traceRep`: the trace is the
  sum over the images of the right cosets of `K(N) diag(p, p, 1, 1) K(Np)`.
* `SiegelUpperHalfSpace.rsThetaPrime_eq_levelRaisingTheta`: `θ'_p = u_p ∘ θ_p ∘ u_p` is the trace.
* `SiegelUpperHalfSpace.exists_mul_thetaTraceRep_inv_mem`: the coset decomposition of (16).
* `SiegelUpperHalfSpace.coe_levelRaisingTheta_eq_add_sum`,
  `SiegelUpperHalfSpace.rsThetaPrime_eq_rsEta_add_sum`: their equation (16).
* `SiegelUpperHalfSpace.mem_levelRaisingModularImage_levelRaisingThetaPrime_iff`,
  `SiegelUpperHalfSpace.mem_levelRaisingModularImage_levelRaisingTheta_iff`,
  `SiegelUpperHalfSpace.mem_levelRaisingModularImage_levelRaisingEta_iff`: the images of the double
  coset operators on paramodular forms are those of `θ_p`, `θ'_p`, `η_p`.
* `SiegelUpperHalfSpace.isNotLevelRaised_detPowerRep_iff`: the condition
  `SiegelUpperHalfSpace.IsNotLevelRaised` of the paramodular newforms, stated with the operators of
  Roberts and Schmidt.
-/

open Matrix hiding inv_zpow' zpow_neg one_zpow

open DoubleCoset

open scoped Pointwise

namespace SiegelUpperHalfSpace

section Coset

variable {G ι : Type*} [Group G] {κ κ' : Subgroup G} {D v w : G} {a : ι → G}

/-- **The translate of a double coset decomposition by a normalizing pair**: if `v`, `w` normalize
`κ`, `κ'` and `v D w ∈ κ`, then `x ↦ v x w` maps `κ D κ' = ⋃ᵢ κ aᵢ` to `κ κ' = ⋃ᵢ κ (v aᵢ w)`. -/
lemma doubleCoset_one_eq_iUnion (hv : ∀ x ∈ κ, v * x * v⁻¹ ∈ κ) (hw : ∀ x ∈ κ', w * x * w⁻¹ ∈ κ')
    (hw' : ∀ x ∈ κ', w⁻¹ * x * w ∈ κ') (hmem : v * D * w ∈ κ)
    (hc : doubleCoset D (κ : Set G) κ' = ⋃ i, MulOpposite.op (a i) • (κ : Set G)) :
    doubleCoset 1 (κ : Set G) κ' = ⋃ i, MulOpposite.op (v * a i * w) • (κ : Set G) := by
  ext x
  rw [mem_doubleCoset, Set.mem_iUnion]
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have hz : D * (w * k₂ * w⁻¹) ∈ doubleCoset D (κ : Set G) κ' :=
      mem_doubleCoset.mpr ⟨1, one_mem _, _, hw _ hk₂, by rw [one_mul]⟩
    rw [hc, Set.mem_iUnion] at hz
    rcases hz with ⟨i, hi⟩
    rcases Set.mem_smul_set.mp hi with ⟨y, hy, hyi⟩
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at hyi
    have ha : a i = y⁻¹ * (D * (w * k₂ * w⁻¹)) :=
      eq_inv_mul_of_mul_eq hyi
    refine ⟨i, Set.mem_smul_set.mpr ⟨k₁ * (v * D * w)⁻¹ * (v * y * v⁻¹), mul_mem (mul_mem hk₁
      (inv_mem hmem)) (hv _ hy), ?_⟩⟩
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, ha]
    group
  · rintro ⟨i, hi⟩
    rcases Set.mem_smul_set.mp hi with ⟨y, hy, rfl⟩
    have hai : a i ∈ doubleCoset D (κ : Set G) κ' := by
      rw [hc]
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_smul_set.mpr ⟨1, one_mem _, by
        rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul]⟩⟩
    rcases mem_doubleCoset.mp hai with ⟨y', hy', z, hz, hyz⟩
    refine ⟨y * (v * y' * v⁻¹) * (v * D * w), mul_mem (mul_mem hy (hv _ hy')) hmem, w⁻¹ * z * w,
      hw' _ hz, ?_⟩
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hyz]
    group

/-- **The right cosets stay distinct under a normalizing pair**: if `v⁻¹` normalizes `κ` and the
right cosets `κ aᵢ` are pairwise distinct, so are the `κ (v aᵢ w)`. -/
lemma injective_op_mul_smul (hv : ∀ x ∈ κ, v⁻¹ * x * v ∈ κ)
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) • (κ : Set G)) :
    Function.Injective fun i ↦ MulOpposite.op (v * a i * w) • (κ : Set G) := by
  intro i j hij
  refine hinj <| (rightCoset_eq_iff κ).mpr ?_
  have h : v * a j * w * (v * a i * w)⁻¹ ∈ κ :=
    (rightCoset_eq_iff κ).mp hij
  have e : a j * (a i)⁻¹ = v⁻¹ * (v * a j * w * (v * a i * w)⁻¹) * v := by
    group
  rw [e]
  exact hv _ h

end Coset

variable (k : ℤ)

lemma slashExponent_detPowerRep : slashExponent (TauCeti.detPowerRep ℂ 2 k) = 2 * k - 3 := by
  rw [slashExponent, Representation.highestWeight_detPowerRep]
  simp

/-- The **slash operator of Roberts and Schmidt** (*On modular forms for the paramodular group*, §2)
of weight `k` by `g = (A, B; C, D) ∈ GSp(4, ℚ)⁺`, of multiplier `λ(g)`:
`(F ∣_k g)(Z) = λ(g)^k det(CZ + D)^(-k) F(g⟨Z⟩)`, normalised so that scalar matrices act
trivially. -/
noncomputable def rsSlash (g : gspPlusGL (Fin 2)) :
    (SiegelUpperHalfSpace (Fin 2) → ℂ) →ₗ[ℂ] SiegelUpperHalfSpace (Fin 2) → ℂ where
  toFun F τ := (multiplier (submonoidToGSpPlus g) : ℂ) ^ k *
    (gspDenom (submonoidToGSpPlus g) τ).det ^ (-k) * F (gspSmul (submonoidToGSpPlus g) τ)
  map_add' F G := by
    ext τ
    simp [mul_add]
  map_smul' c F := by
    ext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring1

variable (p : ℕ+) (g h u u' : gspPlusGL (Fin 2)) (F : SiegelUpperHalfSpace (Fin 2) → ℂ)

/-- **The scalar normalisation of the slash operator**: the slash operator of Roberts and Schmidt is
`λ(g)^(3 - k)` times `SiegelUpperHalfSpace.gspSlash`, which for `ρ = det^k` carries the factor
`λ(g)^(2k - 3)`. -/
lemma rsSlash_eq_zpow_smul : rsSlash k g F = ((multiplier (submonoidToGSpPlus g) : ℂ) ^ (3 - k)) •
    heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 k) g F := by
  have hr : (multiplier (submonoidToGSpPlus g) : ℂ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (multiplier_pos _).ne'
  ext τ
  have e : (multiplier (submonoidToGSpPlus g) : ℂ) ^ k =
      (multiplier (submonoidToGSpPlus g) : ℂ) ^ (3 - k) *
        (multiplier (submonoidToGSpPlus g) : ℂ) ^ (2 * k - 3) := by
    rw [← zpow_add₀ hr]
    congr 1
    ring1
  simp only [rsSlash, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, heckeMonoidSlash, gspSlash,
    slashExponent_detPowerRep, TauCeti.detPowerRep_apply, map_inv, inv_zpow', zpow_neg,
    Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply,
    coe_gspDenomGL, e]
  ring1

lemma multiplier_submonoidToGSpPlus_mul : multiplier (submonoidToGSpPlus (g * h)) =
    multiplier (submonoidToGSpPlus g) * multiplier (submonoidToGSpPlus h) := by
  have e : submonoidToGSpPlus (g * h) = submonoidToGSpPlus g * submonoidToGSpPlus h :=
    Subtype.ext rfl
  rw [e, multiplier_mul]

/-- **The slash operator of Roberts and Schmidt is a right action**: `F ∣ gh = (F ∣ g) ∣ h`. -/
lemma rsSlash_mul : rsSlash k (g * h) F = rsSlash k h (rsSlash k g F) := by
  rw [rsSlash_eq_zpow_smul, rsSlash_eq_zpow_smul, rsSlash_eq_zpow_smul, map_smul,
    heckeMonoidSlash_mul, multiplier_submonoidToGSpPlus_mul, Rat.cast_mul, mul_zpow, smul_smul,
    mul_comm]

lemma rsSlash_of_multiplier_eq_one (h₁ : multiplier (submonoidToGSpPlus g) = 1) :
    rsSlash k g F = heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 k) g F := by
  rw [rsSlash_eq_zpow_smul, h₁, Rat.cast_one, one_zpow, one_smul]

variable (s : ℕ+)

lemma transpose_scalarGL_mul_J_mul : (scalarGL s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ *
    J (Fin 2) ℚ * scalarGL s = (s : ℚ) ^ 2 • J (Fin 2) ℚ := by
  rw [coe_scalarGL, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, sq]

lemma coe_scalarGL_inv :
    (((scalarGL s)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
      (s : ℚ)⁻¹ • 1 :=
  Units.inv_eq_of_mul_eq_one_right <| by
    rw [coe_scalarGL, smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
      s.ne_zero), one_smul]

lemma transpose_scalarGL_inv_mul_J_mul :
    (((scalarGL s)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ *
      J (Fin 2) ℚ * ((scalarGL s)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) = (s : ℚ)⁻¹ ^ 2 • J (Fin 2) ℚ := by
  rw [coe_scalarGL_inv, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, sq]

/-- The scalar matrix `s` in `GSp(4, ℚ)⁺`, of multiplier `s²`. -/
def scalarGSp : gspPlusGL (Fin 2) :=
  ⟨scalarGL s, (s : ℚ) ^ 2, by positivity, transpose_scalarGL_mul_J_mul s⟩

/-- The scalar matrix `s⁻¹` in `GSp(4, ℚ)⁺`, of multiplier `s⁻²`. -/
def scalarInvGSp : gspPlusGL (Fin 2) :=
  ⟨(scalarGL s)⁻¹, (s : ℚ)⁻¹ ^ 2, by positivity, transpose_scalarGL_inv_mul_J_mul s⟩

lemma multiplier_scalarGSp : multiplier (submonoidToGSpPlus (scalarGSp s)) = (s : ℚ) ^ 2 :=
  multiplier_eq _ (transpose_scalarGL_mul_J_mul s)

lemma multiplier_scalarInvGSp : multiplier (submonoidToGSpPlus (scalarInvGSp s)) = (s : ℚ)⁻¹ ^ 2 :=
  multiplier_eq _ (transpose_scalarGL_inv_mul_J_mul s)

lemma scalarGSp_mul_scalarInvGSp : scalarGSp s * scalarInvGSp s = 1 :=
  Subtype.ext <| mul_inv_cancel (scalarGL s)

lemma scalarGSp_one : scalarGSp 1 = 1 :=
  Subtype.ext <| Units.ext <| by
    rw [Submonoid.coe_one, Units.val_one]
    exact (coe_scalarGL 1).trans (by simp)

lemma gspDenom_scalarGSp (τ : SiegelUpperHalfSpace (Fin 2)) :
    gspDenom (submonoidToGSpPlus (scalarGSp s)) τ = (s : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gspDenom, submonoidToGSpPlus, scalarGSp, coe_scalarGL, toBlocks₂₁, toBlocks₂₂,
      Matrix.mul_apply]

lemma gspSmul_scalarGSp (τ : SiegelUpperHalfSpace (Fin 2)) :
    gspSmul (submonoidToGSpPlus (scalarGSp s)) τ = τ := by
  have hs : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.ne_zero
  have hinv : ((s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ = (s : ℂ)⁻¹ • 1 :=
    inv_eq_left_inv <| by
      rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ hs, one_smul]
  have hnum : gspNum (submonoidToGSpPlus (scalarGSp s)) τ = (s : ℂ) • τ.val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gspNum, submonoidToGSpPlus, scalarGSp, coe_scalarGL, toBlocks₁₁, toBlocks₁₂,
        Matrix.mul_apply]
  refine SiegelUpperHalfSpace.ext ?_
  rw [gspSmul_val, gspDenom_scalarGSp, hnum, hinv, smul_mul_smul_comm, Matrix.mul_one,
    mul_inv_cancel₀ hs, one_smul]

/-- **Scalar matrices act trivially** for the slash operator of Roberts and Schmidt. -/
lemma rsSlash_scalarGSp : rsSlash k (scalarGSp s) F = F := by
  have hs : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.ne_zero
  ext τ
  have hdet : ((s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = (s : ℂ) ^ 2 := by
    rw [det_smul, det_one, mul_one, Fintype.card_fin]
  have hk : (((s : ℂ)) ^ 2) ^ k * ((s : ℂ) ^ 2) ^ (-k) = 1 := by
    rw [← zpow_add₀ (pow_ne_zero 2 hs), add_neg_cancel, zpow_zero]
  simp only [rsSlash, LinearMap.coe_mk, AddHom.coe_mk, multiplier_scalarGSp, gspDenom_scalarGSp,
    gspSmul_scalarGSp, hdet]
  push_cast
  rw [hk, one_mul]

lemma rsSlash_one : rsSlash k 1 F = F := by
  rw [← scalarGSp_one, rsSlash_scalarGSp]

lemma rsSlash_scalarInvGSp : rsSlash k (scalarInvGSp s) F = F := by
  have h₁ : rsSlash k (scalarGSp s * scalarInvGSp s) F = F := by
    rw [scalarGSp_mul_scalarInvGSp, rsSlash_one]
  rwa [rsSlash_mul, rsSlash_scalarGSp] at h₁

/-- The similitude `diag(1, 1, p⁻¹, p⁻¹)` of Roberts and Schmidt's definition of `θ_p`, their
(10). -/
def rsThetaDiag : gspPlusGL (Fin 2) :=
  diagSimilitude (fun _ ↦ 1) (fun _ ↦ (p : ℚ)⁻¹) (p : ℚ)⁻¹ (by positivity) fun _ ↦ one_mul _

lemma thetaPrimeDiag_eq : thetaPrimeDiag p = scalarGSp p * rsThetaDiag p :=
  Subtype.ext <| Units.ext <| by
    rw [Submonoid.coe_mul, Units.val_mul]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [thetaPrimeDiag, rsThetaDiag, diagSimilitude, scalarGSp, coe_scalarGL]

lemma multiplier_of_mem {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)} {x : gspPlusGL (Fin 2)}
    (hx : (x : GL (Fin 2 ⊕ Fin 2) ℚ) ∈ heckeGammaOf Γ) : multiplier (submonoidToGSpPlus x) = 1 := by
  rcases hx with ⟨γ, -, hγ⟩
  have e : ((submonoidToGSpPlus x : gspPlus (Fin 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
      γ :=
    congrArg Units.val hγ.symm
  refine multiplier_eq _ ?_
  rw [one_smul, e]
  exact SymplecticGroup.mem_iff'.mp γ.2

lemma multiplier_spToGSpPlusGL (γ : symplecticGroup (Fin 2) ℚ) :
    multiplier (submonoidToGSpPlus (spToGSpPlusGL γ)) = 1 :=
  multiplier_of_mem (Γ := ⊤) ⟨γ, trivial, rfl⟩

lemma multiplier_thetaPrimeDiag : multiplier (submonoidToGSpPlus (thetaPrimeDiag p)) = p := by
  refine multiplier_eq _ ?_
  have e : ((submonoidToGSpPlus (thetaPrimeDiag p) : gspPlus (Fin 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) = xiMatrix !![(p : ℚ), 0; 0, 1] :=
    coe_thetaPrimeDiag p
  rw [e, transpose_xiMatrix_mul_J_mul, det_fin_two_of, mul_one, zero_mul, sub_zero]

lemma multiplier_thetaRep (i : Option (Fin p)) :
    multiplier (submonoidToGSpPlus (thetaRep p i)) = p := by
  rw [thetaRep, multiplier_submonoidToGSpPlus_mul, multiplier_thetaPrimeDiag,
    multiplier_spToGSpPlusGL, mul_one]

variable {F}

lemma rsSlash_of_mem {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)}
    [Fact (SymplecticGroup.IsArithmetic Γ)]
    (hF : F ∈ slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2)) (heckeGammaOf Γ))
    {x : gspPlusGL (Fin 2)} (hx : (x : GL (Fin 2 ⊕ Fin 2) ℚ) ∈ heckeGammaOf Γ) :
    rsSlash k x F = F := by
  rw [rsSlash_of_multiplier_eq_one k x F (multiplier_of_mem hx)]
  exact hF x hx

variable (F)

/-- The **level raising operator `θ_p`** of Roberts and Schmidt (*On modular forms for the
paramodular group*, §4, equation (10)): `θ_p F = ∑_γ F ∣_k diag(1, 1, p⁻¹, p⁻¹) ι(γ)`, over the
representatives `γ` of `Γ₀(p) \ SL(2, ℤ)`, with their slash operator. -/
noncomputable def rsTheta : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  ∑ i, rsSlash k (rsThetaDiag p * spToGSpPlusGL (thetaIotaSp p i)) F

/-- The **level raising operator `η_p`** of Roberts and Schmidt (§4, equation (7)):
`η_p F = F ∣_k η_p⁻¹`, for `η_p = diag(1, p⁻¹, 1, p)`, with their slash operator. -/
noncomputable def rsEta : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  rsSlash k (etaDiag p) F

/-- The **level raising operator `θ'_p = u_p ∘ θ_p ∘ u_p`** of Roberts and Schmidt (§4, equation
(14)), where `u_p F = F ∣_k u_p` for the Atkin–Lehner elements `u` of the level of `F` and `u'` of
that level times `p`. -/
noncomputable def rsThetaPrime : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  rsSlash k u' (rsTheta k p (rsSlash k u F))

lemma rsSlash_thetaRep (i : Option (Fin p)) : rsSlash k (thetaRep p i) F =
    rsSlash k (rsThetaDiag p * spToGSpPlusGL (thetaIotaSp p i)) F := by
  rw [thetaRep, thetaPrimeDiag_eq, mul_assoc, rsSlash_mul, rsSlash_scalarGSp]

variable (M : ℕ+)

/-- **The scalar normalisation of `θ_p`**: the operator `θ_p` of Roberts and Schmidt is `p^(3 - k)`
times the double coset operator of `K(M) diag(p, p, 1, 1) K(Mp)`. -/
lemma rsTheta_eq_smul_levelRaisingThetaPrime (hp : (p : ℕ).Prime)
    (G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel M))) : rsTheta k p G = (p : ℂ) ^ (3 - k) •
    (levelRaisingThetaPrime (TauCeti.detPowerRep ℂ 2 k) M p G :
      SiegelUpperHalfSpace (Fin 2) → ℂ) := by
  rw [coe_levelRaisingThetaPrime _ M p hp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← rsSlash_thetaRep, rsSlash_eq_zpow_smul, multiplier_thetaRep, Rat.cast_natCast]

lemma multiplier_etaDiag : multiplier (submonoidToGSpPlus (etaDiag p)) = 1 :=
  multiplier_eq _ <| by
    rw [one_smul]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [submonoidToGSpPlus, etaDiag, diagSimilitude, J, Matrix.mul_apply]

/-- **The operator `η_p` of Roberts and Schmidt** is the double coset operator of
`K(M) diag(1, p, 1, p⁻¹) K(Mp²)`, the similitude being symplectic. -/
lemma rsEta_eq_levelRaisingEta
    (G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel M))) :
    rsEta k p G = levelRaisingEta (TauCeti.detPowerRep ℂ 2 k) M p G := by
  rw [coe_levelRaisingEta, rsEta, rsSlash_of_multiplier_eq_one k _ _ (multiplier_etaDiag p)]

variable {q : ℕ+} {p M F u u'}

/-- **Two Atkin–Lehner elements act in the same way** on the `K(N)`-invariant functions
(Roberts–Schmidt, §2: "the action of `u_p` on modular forms for `Γ(N)` is unambiguously
defined"). -/
lemma IsAtkinLehnerElementAt.rsSlash_eq (hc : Nat.Coprime q M) (hu : IsAtkinLehnerElementAt q M u)
    (hu' : IsAtkinLehnerElementAt q M u')
    (hF : F ∈ slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel (q * M)))) : rsSlash k u' F = rsSlash k u F := by
  have hmem : (u' : GL (Fin 2 ⊕ Fin 2) ℚ) * (u : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ ∈
      heckeGammaOf (paramodularLevel (q * M)) :=
    hu.mul_inv_mem hc hu'
  have e : u' = ⟨_, heckeGammaOf_le_gspPlusGL _ hmem⟩ * u :=
    Subtype.ext (inv_mul_cancel_right _ _).symm
  rw [e, rsSlash_mul, rsSlash_of_mem k hF hmem]

namespace AtkinLehnerParam

variable (A : AtkinLehnerParam q M) (A' : AtkinLehnerParam (q * p) M)

lemma multiplier_gsp : multiplier (submonoidToGSpPlus A.gsp) = q :=
  multiplier_eq _ A.transpose_gl_mul_J_mul

lemma rsSlash_gsp_mem (hF : F ∈ slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel (q * M)))) : rsSlash k A.gsp F ∈
    slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel (q * M))) := by
  intro x hx
  have hmem : A.gl * x * A.gl⁻¹ ∈ heckeGammaOf (paramodularLevel (q * M)) :=
    A.conj_mem hx
  have e : A.gsp * ⟨x, heckeGammaOf_le_gspPlusGL _ hx⟩ =
      ⟨_, heckeGammaOf_le_gspPlusGL _ hmem⟩ * A.gsp :=
    Subtype.ext <| (inv_mul_cancel_right _ _).symm
  rw [← rsSlash_of_multiplier_eq_one k _ _ (multiplier_of_mem hx), ← rsSlash_mul, e, rsSlash_mul,
    rsSlash_of_mem k hF hmem]

/-- The representatives `(q p)⁻¹ Ξ(U) diag(p, p, 1, 1) ι(γ) Ξ(U')` of the right cosets of `K(N)` in
`K(N) K(Np)`, for `N = q M`, with `Ξ(U)`, `Ξ(U')` Atkin–Lehner elements of levels `N`, `Np`. -/
def traceRep (i : Option (Fin p)) : gspPlusGL (Fin 2) :=
  scalarInvGSp (q * p) * A.gsp * thetaRep p i * A'.gsp

lemma multiplier_traceRep (i : Option (Fin p)) :
    multiplier (submonoidToGSpPlus (A.traceRep A' i)) = 1 := by
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.ne_zero
  rw [traceRep, multiplier_submonoidToGSpPlus_mul, multiplier_submonoidToGSpPlus_mul,
    multiplier_submonoidToGSpPlus_mul, multiplier_scalarInvGSp, multiplier_gsp, multiplier_thetaRep,
    multiplier_gsp]
  push_cast
  field_simp

lemma rsSlash_traceRep (i : Option (Fin p)) : rsSlash k (A.traceRep A' i) F =
    rsSlash k A'.gsp (rsSlash k (rsThetaDiag p * spToGSpPlusGL (thetaIotaSp p i))
      (rsSlash k A.gsp F)) := by
  rw [traceRep, rsSlash_mul, rsSlash_mul, rsSlash_mul, rsSlash_scalarInvGSp, rsSlash_thetaRep]

private lemma scalar_inv_conj (w x : GL (Fin 2 ⊕ Fin 2) ℚ) :
    (scalarGL s)⁻¹ * w * x * ((scalarGL s)⁻¹ * w)⁻¹ = w * x * w⁻¹ := by
  have h : (scalarGL s)⁻¹ * (w * x * w⁻¹) * scalarGL s = w * x * w⁻¹ := by
    rw [mul_assoc, ← scalarGL_mul_comm, inv_mul_cancel_left]
  rw [← h]
  group

private lemma scalar_inv_inv_conj (w x : GL (Fin 2 ⊕ Fin 2) ℚ) :
    ((scalarGL s)⁻¹ * w)⁻¹ * x * ((scalarGL s)⁻¹ * w) = w⁻¹ * x * w := by
  have h : scalarGL s * x * (scalarGL s)⁻¹ = x := by
    rw [scalarGL_mul_comm, mul_inv_cancel_right]
  have e : ((scalarGL s)⁻¹ * w)⁻¹ * x * ((scalarGL s)⁻¹ * w) =
      w⁻¹ * (scalarGL s * x * (scalarGL s)⁻¹) * w := by
    group
  rw [e, h]

private lemma scalar_inv_mul_mem :
    (scalarGL (q * p))⁻¹ * A.gl * (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * A'.gl ∈
      heckeGammaOf (paramodularLevel (q * M)) := by
  have e : (scalarGL (q * p))⁻¹ * A.gl * (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ) * A'.gl =
      spRatToGL (Fin 2) (xiSp (A.productMatrix A') (A.det_productMatrix A')) := by
    rw [mul_assoc, mul_assoc, ← mul_assoc A.gl, gl_mul_thetaPrimeDiag_mul_gl, inv_mul_cancel_left]
  rw [e]
  exact ⟨_, xiSp_mem_paramodularLevel (q * M) _ (A.dvd_productMatrix A'), rfl⟩

lemma doubleCoset_one_eq_iUnion_traceRep (hp : (p : ℕ).Prime) :
    doubleCoset (1 : GL (Fin 2 ⊕ Fin 2) ℚ)
      (heckeGammaOf (paramodularLevel (q * M)) : Set (GL (Fin 2 ⊕ Fin 2) ℚ))
        (heckeGammaOf (paramodularLevel (q * M * p))) =
      ⋃ i, MulOpposite.op (A.traceRep A' i : GL (Fin 2 ⊕ Fin 2) ℚ) •
        (heckeGammaOf (paramodularLevel (q * M)) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) := by
  have e : q * M * p = q * p * M := mul_right_comm _ _ _
  refine SiegelUpperHalfSpace.doubleCoset_one_eq_iUnion (v := (scalarGL (q * p))⁻¹ * A.gl)
    (w := A'.gl) (D := (thetaPrimeDiag p : GL (Fin 2 ⊕ Fin 2) ℚ))
    (a := fun i ↦ (thetaRep p i : GL (Fin 2 ⊕ Fin 2) ℚ)) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    (fun x hx ↦ ?_) (A.scalar_inv_mul_mem A') (doubleCoset_thetaPrimeDiag _ p hp)
  · rw [scalar_inv_conj]
    exact A.conj_mem hx
  · rw [e] at hx ⊢
    exact A'.conj_mem hx
  · rw [e] at hx ⊢
    exact A'.inv_conj_mem hx

lemma traceRep_injective (hp : (p : ℕ).Prime) : Function.Injective fun i ↦ MulOpposite.op
    (A.traceRep A' i : GL (Fin 2 ⊕ Fin 2) ℚ) •
      (heckeGammaOf (paramodularLevel (q * M)) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) :=
  injective_op_mul_smul (v := (scalarGL (q * p))⁻¹ * A.gl) (w := A'.gl)
    (a := fun i ↦ (thetaRep p i : GL (Fin 2 ⊕ Fin 2) ℚ)) (fun x hx ↦ by
      rw [scalar_inv_inv_conj]
      exact A.inv_conj_mem hx) (thetaRep_injective _ p hp)

/-- **The trace is the sum over the representatives** `(q p)⁻¹ Ξ(U) diag(p, p, 1, 1) ι(γ) Ξ(U')`:
`x ↦ (q p)⁻¹ Ξ(U) x Ξ(U')` maps the double coset `K(N) diag(p, p, 1, 1) K(Np) = ⋃_γ K(N) D ι(γ)` to
`K(N) K(Np)`, right cosets to right cosets, since `Ξ(U)`, `Ξ(U')` normalize `K(N)`, `K(Np)` and
`(q p)⁻¹ Ξ(U) D Ξ(U') ∈ K(N)`. -/
lemma coe_levelRaisingTheta_eq_sum_traceRep {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) ℂ) V) (hp : (p : ℕ).Prime)
    (G : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel (q * M)))) :
    (levelRaisingTheta ρ (q * M) p G : SiegelUpperHalfSpace (Fin 2) → V) =
      ∑ i, heckeMonoidSlash ρ (A.traceRep A' i) G := by
  rw [levelRaisingTheta, doubleCosetOperator_eq_sum ρ _ (A.traceRep A') ?_
    (A.traceRep_injective A' hp)]
  rw [← HeckeCoset.rep_def, HeckeCoset.doubleCoset_rep_mk]
  exact A.doubleCoset_one_eq_iUnion_traceRep A' hp

lemma rsThetaPrime_gsp_eq (hp : (p : ℕ).Prime)
    (G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel (q * M)))) : rsThetaPrime k p A.gsp A'.gsp G =
    levelRaisingTheta (TauCeti.detPowerRep ℂ 2 k) (q * M) p G := by
  rw [A.coe_levelRaisingTheta_eq_sum_traceRep A' _ hp, rsThetaPrime, rsTheta, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← rsSlash_traceRep, rsSlash_of_multiplier_eq_one k _ _ (A.multiplier_traceRep A' i)]

end AtkinLehnerParam

/-- **The relation `θ'_p = u_p θ_p u_p` of Roberts and Schmidt** (*On modular forms for the
paramodular group*, §4, equations (14) and (16)): for a prime `p`, `N = q M` with `q p` and `M`
coprime (`q = p^j`, `p^j` the exact power of `p` dividing `N`, for Roberts and Schmidt) and any
Atkin–Lehner elements `u` of level `N`, `u'` of level `Np`, the operator
`F ↦ ((F ∣_k u) ∣ θ_p) ∣_k u'`, for their slash operator, is the trace `K(N) K(Np)`, that is
`SiegelUpperHalfSpace.levelRaisingTheta`, with no scalar factor. -/
lemma rsThetaPrime_eq_levelRaisingTheta (hp : (p : ℕ).Prime) (hc : Nat.Coprime (q * p : ℕ+) M)
    (hu : IsAtkinLehnerElementAt q M u) (hu' : IsAtkinLehnerElementAt (q * p) M u')
    (G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel (q * M)))) :
    rsThetaPrime k p u u' G = levelRaisingTheta (TauCeti.detPowerRep ℂ 2 k) (q * M) p G := by
  have hq : Nat.Coprime q M :=
    hc.coprime_dvd_left (Dvd.intro _ rfl)
  let A : AtkinLehnerParam q M := AtkinLehnerParam.ofCoprime hq
  let A' : AtkinLehnerParam (q * p) M := AtkinLehnerParam.ofCoprime hc
  let G₀ : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel (q * M))) :=
    ⟨rsSlash k A.gsp G, A.rsSlash_gsp_mem k G.2⟩
  have hT : rsTheta k p (rsSlash k A.gsp G) ∈
      slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
        (heckeGammaOf (paramodularLevel (q * p * M))) := by
    rw [mul_right_comm q p M]
    have e : rsTheta k p (rsSlash k A.gsp G) = (p : ℂ) ^ (3 - k) •
        (levelRaisingThetaPrime (TauCeti.detPowerRep ℂ 2 k) (q * M) p G₀ :
          SiegelUpperHalfSpace (Fin 2) → ℂ) :=
      rsTheta_eq_smul_levelRaisingThetaPrime k p (q * M) hp G₀
    rw [e]
    exact Submodule.smul_mem _ _ (levelRaisingThetaPrime _ (q * M) p G₀).2
  rw [rsThetaPrime, IsAtkinLehnerElementAt.rsSlash_eq k hq (isAtkinLehnerElementAt_ofCoprime hq) hu
    G.2, IsAtkinLehnerElementAt.rsSlash_eq k hc (isAtkinLehnerElementAt_ofCoprime hc) hu' hT]
  exact A.rsThetaPrime_gsp_eq k A' hp G

/-- The symplectic matrix `[1, , , ; , 1, , t; , , 1, ; , , , 1]`, in the coordinates
`(e₁, e₂, f₁, f₂)`, of Roberts and Schmidt's (16). -/
def traceTranslation (t : ℚ) : symplecticGroup (Fin 2) ℚ :=
  ⟨fromBlocks 1 !![0, 0; 0, t] 0 1, by
    rw [SymplecticGroup.mem_iff']
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [J, Matrix.mul_apply]⟩

/-- The symplectic matrix `[1, , , ; , , , -N⁻¹; , , 1, ; , N, , ]`, in the coordinates
`(e₁, e₂, f₁, f₂)`, an element of `K(N)`. -/
def traceWeyl (N : ℕ+) : symplecticGroup (Fin 2) ℚ :=
  ⟨fromBlocks !![1, 0; 0, 0] !![0, 0; 0, -(N : ℚ)⁻¹] !![0, 0; 0, (N : ℚ)] !![1, 0; 0, 0], by
    rw [SymplecticGroup.mem_iff']
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [J, Matrix.mul_apply]⟩

variable (N : ℕ+) (p)

lemma traceTranslation_mem (c : ℤ) : traceTranslation ((c : ℚ) * (N : ℚ)⁻¹) ∈ paramodularLevel N :=
  mem_paramodularLevel_of_isParamodularShape ⟨fromBlocks 1 !![0, 0; 0, c] 0 1, fun i j ↦ by
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [traceTranslation, paramodularScale, mul_comm]⟩

lemma traceWeyl_mem : traceWeyl N ∈ paramodularLevel N :=
  mem_paramodularLevel_of_isParamodularShape
    ⟨fromBlocks !![1, 0; 0, 0] !![0, 0; 0, -1] !![0, 0; 0, 1] !![1, 0; 0, 0], fun i j ↦ by
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [traceWeyl, paramodularScale]⟩

lemma spToGSpPlusGL_traceWeyl_mul :
    spToGSpPlusGL (traceWeyl (N * p)) = spToGSpPlusGL (traceWeyl N) * etaDiag p :=
  Subtype.ext <| Units.ext <| by
    rw [Submonoid.coe_mul, Units.val_mul, coe_spToGSpPlusGL, coe_spToGSpPlusGL, val_spRatToGL,
      val_spRatToGL]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [traceWeyl, etaDiag, diagSimilitude, Matrix.mul_apply, mul_comm]

variable {p} in
lemma mem_heckeGammaOf_of_mem_mul {X : GL (Fin 2 ⊕ Fin 2) ℚ}
    (hX : X ∈ heckeGammaOf (paramodularLevel (N * p))) {z : ℤ}
    (hz : (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) = (N : ℚ)⁻¹ * z) :
    X ∈ heckeGammaOf (paramodularLevel N) := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr N.ne_zero
  rw [mem_heckeGammaOf_paramodularLevel_iff] at hX ⊢
  rcases hX.2 with ⟨x, hx⟩
  refine ⟨hX.1, fromBlocks !![x (.inl 0) (.inl 0), p * x (.inl 0) (.inl 1);
    x (.inl 1) (.inl 0), x (.inl 1) (.inl 1)] !![x (.inl 0) (.inr 0), x (.inl 0) (.inr 1);
    x (.inl 1) (.inr 0), z] !![x (.inr 0) (.inl 0), p * x (.inr 0) (.inl 1);
    p * x (.inr 1) (.inl 0), p * x (.inr 1) (.inl 1)] !![x (.inr 0) (.inr 0), x (.inr 0) (.inr 1);
    p * x (.inr 1) (.inr 0), x (.inr 1) (.inr 1)], fun i j ↦ ?_⟩
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    first
    | exact hz
    | (simp [hx, paramodularScale]; try ring1)

variable {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ} (i : Fin 2 ⊕ Fin 2) (t : ℚ)

variable {N} in
lemma mul_traceTranslation_apply_inl :
    (X * (traceTranslation t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)) i (.inl 1) =
      X i (.inl 1) := by
  simp [traceTranslation, Matrix.mul_apply]

lemma mul_traceTranslation_apply_inr :
    (X * (traceTranslation t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)) i (.inr 1) =
      X i (.inr 1) + X i (.inl 1) * t := by
  simp [traceTranslation, Matrix.mul_apply, add_comm]

lemma mul_traceWeyl_apply_inl :
    (X * (traceWeyl N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)) i (.inl 1) =
      X i (.inr 1) * N := by
  simp [traceWeyl, Matrix.mul_apply]

/-- The representatives of the right cosets of `K(N) ∩ K(Np)` in `K(Np)` of Roberts and Schmidt's
(16): the matrices `[1, , , ; , 1, , c p⁻¹ N⁻¹; , , 1, ; , , , 1]`, `0 ≤ c < p`, and the element
`[1, , , ; , , , -p⁻¹ N⁻¹; , , 1, ; , N p, , ]` of `K(Np)`. -/
def thetaTraceRep : Option (Fin p) → gspPlusGL (Fin 2)
  | some c => spToGSpPlusGL (traceTranslation (((c : ℕ) : ℤ) * ((N * p : ℕ+) : ℚ)⁻¹))
  | none => spToGSpPlusGL (traceWeyl (N * p))

lemma thetaTraceRep_mem (j : Option (Fin p)) : (thetaTraceRep p N j : GL (Fin 2 ⊕ Fin 2) ℚ) ∈
    heckeGammaOf (paramodularLevel (N * p)) := by
  rcases j with _ | c
  · exact ⟨_, traceWeyl_mem _, rfl⟩
  · exact ⟨_, traceTranslation_mem _ _, rfl⟩

private lemma coe_mul_inv_mul {x a : GL (Fin 2 ⊕ Fin 2) ℚ} :
    ((x * a⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) * a = x :=
  (Units.val_mul _ _).symm.trans (congrArg Units.val (inv_mul_cancel_right x a))

variable (x : GL (Fin 2 ⊕ Fin 2) ℚ)

private lemma mul_inv_none_apply :
    ((x * (thetaTraceRep p N none : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) * ((N * p : ℕ+) : ℚ) =
        (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) :=
  (mul_traceWeyl_apply_inl (N * p) _).symm.trans (congrFun (congrFun coe_mul_inv_mul _) _)

private lemma mul_inv_some_apply_inl (c : Fin p) :
    ((x * (thetaTraceRep p N (some c) : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) =
        (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) :=
  (mul_traceTranslation_apply_inl _ _).symm.trans (congrFun (congrFun coe_mul_inv_mul _) _)

private lemma mul_inv_some_apply_inr (c : Fin p) :
    ((x * (thetaTraceRep p N (some c) : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) +
        ((x * (thetaTraceRep p N (some c) : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) *
            (((c : ℕ) : ℤ) * ((N * p : ℕ+) : ℚ)⁻¹) =
      (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) :=
  (mul_traceTranslation_apply_inr _ _).symm.trans (congrFun (congrFun coe_mul_inv_mul _) _)

variable {x}

/-- **The coset decomposition of Roberts and Schmidt's (16)**: for `g ∈ K(Np)`, with
`(e₂, e₂)`-entry `y` and `(e₂, f₂)`-entry `w / (Np)`, `g` lies in the coset of
`[1, , , ; , , , -p⁻¹ N⁻¹; , , 1, ; , N p, , ]` if `p ∣ y`, and in that of
`[1, , , ; , 1, , c p⁻¹ N⁻¹; , , 1, ; , , , 1]` if `p ∣ w - c y`. -/
lemma exists_mul_thetaTraceRep_inv_mem (hp : (p : ℕ).Prime)
    (hx : x ∈ heckeGammaOf (paramodularLevel (N * p))) :
    ∃ j, x * (thetaTraceRep p N j : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ ∈
      heckeGammaOf (paramodularLevel N) := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr N.ne_zero
  have hp₀ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.ne_zero
  rcases (mem_heckeGammaOf_paramodularLevel_iff.mp hx).2 with ⟨m, hm⟩
  have h₂₂ : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) =
      m (.inl 1) (.inl 1) := by
    simp [hm, paramodularScale]
  have h₂₄ : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) =
      ((N * p : ℕ+) : ℚ)⁻¹ * m (.inl 1) (.inr 1) := by
    simp [hm, paramodularScale]
  by_cases hd : (p : ℤ) ∣ m (.inl 1) (.inl 1)
  · rcases hd with ⟨z, hz⟩
    refine ⟨none, mem_heckeGammaOf_of_mem_mul N (mul_mem hx (inv_mem (thetaTraceRep_mem p N none)))
      (z := z) ?_⟩
    have h : ((x * (thetaTraceRep p N none : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) * ((N * p : ℕ+) : ℚ) =
          (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) :=
      mul_inv_none_apply p N x
    rw [h₂₂, hz] at h
    generalize ((x * (thetaTraceRep p N none : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) = y at h ⊢
    push_cast at h
    field_simp
    exact mul_left_cancel₀ hp₀ (by linear_combination h)
  · have : Fact (p : ℕ).Prime := ⟨hp⟩
    have hne : (m (.inl 1) (.inl 1) : ZMod p) ≠ 0 :=
      fun h ↦ hd <| (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    let c : Fin p := ⟨((m (.inl 1) (.inr 1) : ZMod p) * (m (.inl 1) (.inl 1) : ZMod p)⁻¹).val,
      ZMod.val_lt _⟩
    have hc : (p : ℤ) ∣ m (.inl 1) (.inr 1) - ((c : ℕ) : ℤ) * m (.inl 1) (.inl 1) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [c, ZMod.natCast_val, ZMod.cast_id', id_eq]
      rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, sub_self]
    rcases hc with ⟨z, hz⟩
    have hz' : (m (.inl 1) (.inr 1) : ℚ) - (((c : ℕ) : ℚ)) * m (.inl 1) (.inl 1) = p * z := by
      exact_mod_cast hz
    refine ⟨some c, mem_heckeGammaOf_of_mem_mul N (mul_mem hx (inv_mem (thetaTraceRep_mem p N _)))
      (z := z) ?_⟩
    have h : ((x * (thetaTraceRep p N (some c) : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ :
        GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) +
          ((x * (thetaTraceRep p N (some c) : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) *
              (((c : ℕ) : ℤ) * ((N * p : ℕ+) : ℚ)⁻¹) =
        (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) :=
      mul_inv_some_apply_inr p N x c
    rw [mul_inv_some_apply_inl, h₂₂, h₂₄] at h
    generalize ((x * (thetaTraceRep p N (some c) : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) = y at h ⊢
    push_cast at h
    field_simp at h ⊢
    exact mul_left_cancel₀ hp₀ (by linear_combination h + hz')

lemma eq_of_mul_thetaTraceRep_inv_mem (hp : (p : ℕ).Prime) {a b : Option (Fin p)}
    (hab : (thetaTraceRep p N b : GL (Fin 2 ⊕ Fin 2) ℚ) *
      (thetaTraceRep p N a : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ ∈ heckeGammaOf (paramodularLevel N)) :
    a = b := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr N.ne_zero
  have hp₀ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.ne_zero
  have hp₁ : ((p : ℕ) : ℤ) ≠ 1 := by
    have h₁ : 1 < (p : ℕ) := hp.one_lt
    omega
  have hp₂ (z : ℤ) : (z : ℚ) * p ≠ 1 := fun e ↦ hp₁ <|
    Int.eq_one_of_mul_eq_one_left (a := z) (b := ((p : ℕ) : ℤ)) (by positivity) (by
      exact_mod_cast e)
  rcases (mem_heckeGammaOf_paramodularLevel_iff.mp hab).2 with ⟨m, hm⟩
  have h₂₄ : ((((thetaTraceRep p N b : GL (Fin 2 ⊕ Fin 2) ℚ) *
      (thetaTraceRep p N a : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹ : GL (Fin 2 ⊕ Fin 2) ℚ)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) =
      (N : ℚ)⁻¹ * m (.inl 1) (.inr 1) := by
    simp [hm, paramodularScale]
  rcases a with _ | c <;> rcases b with _ | c'
  · rfl
  · have e : _ * ((N * p : ℕ+) : ℚ) = _ :=
      mul_inv_none_apply p N (thetaTraceRep p N (some c') : GL (Fin 2 ⊕ Fin 2) ℚ)
    rw [h₂₄] at e
    refine absurd ?_ (hp₂ (m (.inl 1) (.inr 1)))
    have e₁ : ((thetaTraceRep p N (some c') : GL (Fin 2 ⊕ Fin 2) ℚ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) = 1 := by
      simp [thetaTraceRep, coe_spToGSpPlusGL, val_spRatToGL, traceTranslation]
    rw [e₁] at e
    push_cast at e
    field_simp at e
    exact e
  · have e₁ : _ = _ :=
      mul_inv_some_apply_inl p N (thetaTraceRep p N none : GL (Fin 2 ⊕ Fin 2) ℚ) c
    have e₂ : _ + _ * _ = _ :=
      mul_inv_some_apply_inr p N (thetaTraceRep p N none : GL (Fin 2 ⊕ Fin 2) ℚ) c
    have e₃ : ((thetaTraceRep p N none : GL (Fin 2 ⊕ Fin 2) ℚ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) = 0 := by
      simp [thetaTraceRep, coe_spToGSpPlusGL, val_spRatToGL, traceWeyl]
    have e₄ : ((thetaTraceRep p N none : GL (Fin 2 ⊕ Fin 2) ℚ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) = -((N * p : ℕ+) : ℚ)⁻¹ := by
      simp [thetaTraceRep, coe_spToGSpPlusGL, val_spRatToGL, traceWeyl]
    rw [e₁, e₃, zero_mul, add_zero, h₂₄, e₄] at e₂
    refine absurd ?_ (hp₂ (-m (.inl 1) (.inr 1)))
    push_cast at e₂ ⊢
    field_simp at e₂
    linear_combination -e₂
  · have e₁ : _ = _ :=
      mul_inv_some_apply_inl p N (thetaTraceRep p N (some c') : GL (Fin 2 ⊕ Fin 2) ℚ) c
    have e₂ : _ + _ * _ = _ :=
      mul_inv_some_apply_inr p N (thetaTraceRep p N (some c') : GL (Fin 2 ⊕ Fin 2) ℚ) c
    have e₃ : ((thetaTraceRep p N (some c') : GL (Fin 2 ⊕ Fin 2) ℚ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inl 1) = 1 := by
      simp [thetaTraceRep, coe_spToGSpPlusGL, val_spRatToGL, traceTranslation]
    have e₄ : ((thetaTraceRep p N (some c') : GL (Fin 2 ⊕ Fin 2) ℚ) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inl 1) (.inr 1) =
          ((c' : ℕ) : ℤ) * ((N * p : ℕ+) : ℚ)⁻¹ := by
      simp [thetaTraceRep, coe_spToGSpPlusGL, val_spRatToGL, traceTranslation]
    rw [e₁, e₃, one_mul, h₂₄, e₄] at e₂
    push_cast at e₂
    field_simp at e₂
    have e₅ : m (.inl 1) (.inr 1) * (p : ℕ) + ((c : ℕ) : ℤ) = ((c' : ℕ) : ℤ) := by
      exact_mod_cast e₂
    have hd : ((p : ℕ) : ℤ) ∣ ((c' : ℕ) : ℤ) - ((c : ℕ) : ℤ) :=
      ⟨m (.inl 1) (.inr 1), by linear_combination -e₅⟩
    have hc : (c : ℕ) < p :=
      c.isLt
    have hc' : (c' : ℕ) < p :=
      c'.isLt
    have e₆ : ((c' : ℕ) : ℤ) - ((c : ℕ) : ℤ) = 0 :=
      Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
    exact congrArg some (Fin.ext (by omega))

lemma doubleCoset_one_eq_iUnion_thetaTraceRep (hp : (p : ℕ).Prime) :
    doubleCoset (1 : GL (Fin 2 ⊕ Fin 2) ℚ)
      (heckeGammaOf (paramodularLevel N) : Set (GL (Fin 2 ⊕ Fin 2) ℚ))
        (heckeGammaOf (paramodularLevel (N * p))) =
      ⋃ j, MulOpposite.op (thetaTraceRep p N j : GL (Fin 2 ⊕ Fin 2) ℚ) •
        (heckeGammaOf (paramodularLevel N) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) := by
  ext x
  rw [mem_doubleCoset, Set.mem_iUnion]
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    rcases exists_mul_thetaTraceRep_inv_mem p N hp hk₂ with ⟨j, hj⟩
    refine ⟨j, Set.mem_smul_set.mpr ⟨k₁ * (k₂ * (thetaTraceRep p N j : GL (Fin 2 ⊕ Fin 2) ℚ)⁻¹),
      mul_mem hk₁ hj, ?_⟩⟩
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    group
  · rintro ⟨j, hj⟩
    rcases Set.mem_smul_set.mp hj with ⟨y, hy, rfl⟩
    exact ⟨y, hy, _, thetaTraceRep_mem p N j, by
      rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_one]⟩

lemma thetaTraceRep_injective (hp : (p : ℕ).Prime) : Function.Injective fun j ↦ MulOpposite.op
    (thetaTraceRep p N j : GL (Fin 2 ⊕ Fin 2) ℚ) •
      (heckeGammaOf (paramodularLevel N) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) :=
  fun _ _ hij ↦ eq_of_mul_thetaTraceRep_inv_mem p N hp ((rightCoset_eq_iff _).mp hij)

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)

/-- **The trace `K(N) K(Np)`** is
`F ↦ F ∣_ρ diag(1, p, 1, p⁻¹) + ∑_c F ∣_ρ [1, , , ; , 1, , c p⁻¹ N⁻¹; , , 1, ; , , , 1]`
(Roberts–Schmidt, the right-hand side of (16)), the first term being the slash operator of
`[1, , , ; , , , -p⁻¹ N⁻¹; , , 1, ; , N p, , ] ∈ K(N) diag(1, p, 1, p⁻¹)`. -/
lemma coe_levelRaisingTheta_eq_add_sum (hp : (p : ℕ).Prime)
    (G : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel N))) :
    (levelRaisingTheta ρ N p G : SiegelUpperHalfSpace (Fin 2) → V) =
      heckeMonoidSlash ρ (etaDiag p) G + ∑ c : Fin p, heckeMonoidSlash ρ
        (spToGSpPlusGL (traceTranslation (((c : ℕ) : ℤ) * ((N * p : ℕ+) : ℚ)⁻¹))) G := by
  rw [levelRaisingTheta, doubleCosetOperator_eq_sum ρ _ (thetaTraceRep p N) ?_
    (thetaTraceRep_injective p N hp), Fintype.sum_option]
  · have hG : heckeMonoidSlash ρ (spToGSpPlusGL (traceWeyl N)) G = G :=
      G.2 _ ⟨_, traceWeyl_mem N, rfl⟩
    rw [thetaTraceRep, spToGSpPlusGL_traceWeyl_mul, heckeMonoidSlash_mul, hG]
    rfl
  · rw [← HeckeCoset.rep_def, HeckeCoset.doubleCoset_rep_mk]
    exact doubleCoset_one_eq_iUnion_thetaTraceRep p N hp

variable {p}

/-- **Roberts and Schmidt's equation (16)**: for a prime `p`, `N = q M` with `q p` and `M` coprime
and Atkin–Lehner elements `u` of level `N` and `u'` of level `Np`,
`θ'_p F = η_p F + ∑_{c ∈ ℤ/pℤ} F ∣_k [1, , , ; , 1, , c p⁻¹ N⁻¹; , , 1, ; , , , 1]`. -/
lemma rsThetaPrime_eq_rsEta_add_sum (hp : (p : ℕ).Prime) (hc : Nat.Coprime (q * p : ℕ+) M)
    (hu : IsAtkinLehnerElementAt q M u) (hu' : IsAtkinLehnerElementAt (q * p) M u')
    (G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel (q * M)))) : rsThetaPrime k p u u' G = rsEta k p G +
    ∑ c : Fin p, rsSlash k
      (spToGSpPlusGL (traceTranslation (((c : ℕ) : ℤ) * ((q * M * p : ℕ+) : ℚ)⁻¹))) G := by
  rw [rsThetaPrime_eq_levelRaisingTheta k hp hc hu hu' G,
    coe_levelRaisingTheta_eq_add_sum p (q * M) _ hp, rsEta,
    rsSlash_of_multiplier_eq_one k _ _ (multiplier_etaDiag p)]
  refine congrArg _ (Finset.sum_congr rfl fun c _ ↦ ?_)
  rw [rsSlash_of_multiplier_eq_one k _ _ (multiplier_spToGSpPlusGL _)]

/-- **The Atkin–Lehner operators are involutions** on the `K(N)`-invariant functions
(Roberts–Schmidt, §2), since `u² ∈ q K(N)` and scalar matrices act trivially. -/
lemma IsAtkinLehnerElementAt.rsSlash_rsSlash (hc : Nat.Coprime q M)
    (hu : IsAtkinLehnerElementAt q M u)
    (hF : F ∈ slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel (q * M)))) : rsSlash k u (rsSlash k u F) = F := by
  let A : AtkinLehnerParam q M := AtkinLehnerParam.ofCoprime hc
  have hA : IsAtkinLehnerElementAt q M A.gsp := isAtkinLehnerElementAt_ofCoprime hc
  have e : A.gsp * A.gsp = scalarGSp q *
      spToGSpPlusGL (xiSp A.squareMatrix A.det_squareMatrix) :=
    Subtype.ext A.gl_mul_self
  rw [hA.rsSlash_eq k hc hu hF, hA.rsSlash_eq k hc hu (A.rsSlash_gsp_mem k hF), ← rsSlash_mul, e,
    rsSlash_mul, rsSlash_scalarGSp]
  exact rsSlash_of_mem k hF ⟨_, xiSp_mem_paramodularLevel (q * M) _ A.dvd_squareMatrix, rfl⟩

variable (f : SiegelUpperHalfSpace (Fin 2) → ℂ)

private lemma mem_levelRaisingModularImage_iff {K : ℕ+}
    (T : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
      (heckeGammaOf (paramodularLevel M)) →ₗ[ℂ] slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k)
        (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel K))) : f ∈
    levelRaisingModularImage (TauCeti.detPowerRep ℂ 2 k) T ↔
      ∃ G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
        (heckeGammaOf (paramodularLevel M)),
        (G : SiegelUpperHalfSpace (Fin 2) → ℂ) ∈
          modularForms (TauCeti.detPowerRep ℂ 2 k) (paramodularLevel M) 1 ∧
          (T G : SiegelUpperHalfSpace (Fin 2) → ℂ) = f :=
  Iff.rfl

/-- **The image of `levelRaisingThetaPrime` is that of the operator `θ_p` of Roberts and Schmidt**,
the two differing by the nonzero scalar `p^(3 - k)`. -/
lemma mem_levelRaisingModularImage_levelRaisingThetaPrime_iff (hp : (p : ℕ).Prime) : f ∈
    levelRaisingModularImage (TauCeti.detPowerRep ℂ 2 k)
        (levelRaisingThetaPrime (TauCeti.detPowerRep ℂ 2 k) M p) ↔
      ∃ G ∈ modularForms (TauCeti.detPowerRep ℂ 2 k) (paramodularLevel M) 1, rsTheta k p G = f := by
  have hp₀ : (p : ℂ) ^ (3 - k) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr p.ne_zero)
  rw [mem_levelRaisingModularImage_iff]
  constructor
  · rintro ⟨G, hG, rfl⟩
    refine ⟨((p : ℂ) ^ (3 - k))⁻¹ • (G : SiegelUpperHalfSpace (Fin 2) → ℂ),
      Submodule.smul_mem _ _ hG, ?_⟩
    have e : rsTheta k p ((((p : ℂ) ^ (3 - k))⁻¹ • G :
        slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
          (heckeGammaOf (paramodularLevel M))) : SiegelUpperHalfSpace (Fin 2) → ℂ) = _ :=
      rsTheta_eq_smul_levelRaisingThetaPrime k p M hp (((p : ℂ) ^ (3 - k))⁻¹ • G)
    rw [map_smul, Submodule.coe_smul, Submodule.coe_smul, smul_smul, mul_inv_cancel₀ hp₀,
      one_smul] at e
    exact e
  · rintro ⟨G, hG, rfl⟩
    let G' : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (gspPlusGL (Fin 2))
        (heckeGammaOf (paramodularLevel M)) :=
      ⟨G, modularForms_le_slashInvariantsOf _ _ hG⟩
    refine ⟨(p : ℂ) ^ (3 - k) • G', Submodule.smul_mem _ _ hG, ?_⟩
    rw [map_smul]
    exact (rsTheta_eq_smul_levelRaisingThetaPrime k p M hp G').symm

/-- **The image of the trace is that of the operator `θ'_p` of Roberts and Schmidt.** -/
lemma mem_levelRaisingModularImage_levelRaisingTheta_iff (hp : (p : ℕ).Prime)
    (hc : Nat.Coprime (q * p : ℕ+) M) (hu : IsAtkinLehnerElementAt q M u)
    (hu' : IsAtkinLehnerElementAt (q * p) M u') : f ∈
    levelRaisingModularImage (TauCeti.detPowerRep ℂ 2 k)
        (levelRaisingTheta (TauCeti.detPowerRep ℂ 2 k) (q * M) p) ↔
      ∃ G ∈ modularForms (TauCeti.detPowerRep ℂ 2 k) (paramodularLevel (q * M)) 1,
        rsThetaPrime k p u u' G = f := by
  rw [mem_levelRaisingModularImage_iff]
  constructor
  · rintro ⟨G, hG, rfl⟩
    exact ⟨G, hG, rsThetaPrime_eq_levelRaisingTheta k hp hc hu hu' G⟩
  · rintro ⟨G, hG, rfl⟩
    exact ⟨⟨G, modularForms_le_slashInvariantsOf _ _ hG⟩, hG,
      (rsThetaPrime_eq_levelRaisingTheta k hp hc hu hu' _).symm⟩

/-- **The image of `levelRaisingEta` is that of the operator `η_p` of Roberts and Schmidt.** -/
lemma mem_levelRaisingModularImage_levelRaisingEta_iff : f ∈
    levelRaisingModularImage (TauCeti.detPowerRep ℂ 2 k)
        (levelRaisingEta (TauCeti.detPowerRep ℂ 2 k) M p) ↔
      ∃ G ∈ modularForms (TauCeti.detPowerRep ℂ 2 k) (paramodularLevel M) 1, rsEta k p G = f := by
  rw [mem_levelRaisingModularImage_iff]
  constructor
  · rintro ⟨G, hG, rfl⟩
    exact ⟨G, hG, rsEta_eq_levelRaisingEta k p M G⟩
  · rintro ⟨G, hG, rfl⟩
    exact ⟨⟨G, modularForms_le_slashInvariantsOf _ _ hG⟩, hG,
      (rsEta_eq_levelRaisingEta k p M _).symm⟩

private lemma exists_atkinLehner_factorization (hp : (p : ℕ).Prime) :
    ∃ (j : ℕ) (M₀ : ℕ+), M = p ^ j * M₀ ∧ ¬(p : ℕ) ∣ M₀ := by
  rcases Nat.exists_eq_pow_mul_and_not_dvd M.ne_zero p hp.ne_one with ⟨j, m, hm, hM⟩
  let M₀ : ℕ+ := ⟨m, Nat.pos_of_ne_zero fun h ↦ hm (h ▸ dvd_zero _)⟩
  have e : (M₀ : ℕ) = m := rfl
  exact ⟨j, M₀, PNat.eq (by rw [PNat.mul_coe, PNat.pow_coe, e, hM]), hm⟩

private lemma coprime_pow_mul {j : ℕ} {M₀ : ℕ+} (hp : (p : ℕ).Prime) (hM₀ : ¬(p : ℕ) ∣ M₀) :
    Nat.Coprime (p ^ j * p : ℕ+) M₀ := by
  have h : Nat.Coprime p M₀ := hp.coprime_iff_not_dvd.mpr hM₀
  simpa using (h.pow_left j).mul_left h

/-- **The condition of not being obtained by level raising, with the operators of Roberts and
Schmidt**: for `ρ = det^k`, a function `f` satisfies `SiegelUpperHalfSpace.IsNotLevelRaised` if and
only if, for every prime `p`, it is not of the form `θ_p G` or `θ'_p G = u_p θ_p u_p G` for `G` a
paramodular form of level `N / p`, and not of the form `η_p G` for `G` a paramodular form of level
`N / p²`, with the slash operator and the Atkin–Lehner elements of Roberts and Schmidt. -/
lemma isNotLevelRaised_detPowerRep_iff : IsNotLevelRaised (TauCeti.detPowerRep ℂ 2 k) N f ↔
    (∀ p : ℕ+, (p : ℕ).Prime → ∀ M : ℕ+, M * p = N →
      (∀ G ∈ modularForms (TauCeti.detPowerRep ℂ 2 k) (paramodularLevel M) 1, rsTheta k p G ≠ f) ∧
      ∀ (j : ℕ) (M₀ : ℕ+) (u u' : gspPlusGL (Fin 2)), M = p ^ j * M₀ → ¬(p : ℕ) ∣ M₀ →
        IsAtkinLehnerElementAt (p ^ j) M₀ u → IsAtkinLehnerElementAt (p ^ j * p) M₀ u' →
          ∀ G ∈ modularForms (TauCeti.detPowerRep ℂ 2 k) (paramodularLevel M) 1,
            rsThetaPrime k p u u' G ≠ f) ∧
      ∀ p : ℕ+, (p : ℕ).Prime → ∀ M : ℕ+, M * p * p = N →
        ∀ G ∈ modularForms (TauCeti.detPowerRep ℂ 2 k) (paramodularLevel M) 1,
          rsEta k p G ≠ f := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun p hp M hM ↦ ⟨fun G hG hf ↦ (h₁ p hp M hM).1
      ((mem_levelRaisingModularImage_levelRaisingThetaPrime_iff k f hp).mpr ⟨G, hG, hf⟩), ?_⟩,
      fun p hp M hM G hG hf ↦ h₂ p hp M hM
        ((mem_levelRaisingModularImage_levelRaisingEta_iff k f).mpr ⟨G, hG, hf⟩)⟩
    rintro j M₀ u u' rfl hM₀ hu hu' G hG hf
    exact (h₁ p hp _ hM).2 ((mem_levelRaisingModularImage_levelRaisingTheta_iff k f hp
      (coprime_pow_mul hp hM₀) hu hu').mpr ⟨G, hG, hf⟩)
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun p hp M hM ↦ ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩, fun p hp M hM hf ↦ ?_⟩
    · rcases (mem_levelRaisingModularImage_levelRaisingThetaPrime_iff k f hp).mp hf with
        ⟨G, hG, hfG⟩
      exact (h₁ p hp M hM).1 G hG hfG
    · rcases exists_atkinLehner_factorization hp (M := M) with ⟨j, M₀, rfl, hM₀⟩
      have hc : Nat.Coprime (p ^ j * p : ℕ+) M₀ := coprime_pow_mul hp hM₀
      have hc₀ : Nat.Coprime (p ^ j : ℕ+) M₀ :=
        hc.coprime_dvd_left (Dvd.intro _ rfl)
      rcases (mem_levelRaisingModularImage_levelRaisingTheta_iff k f hp hc
        (isAtkinLehnerElementAt_ofCoprime hc₀) (isAtkinLehnerElementAt_ofCoprime hc)).mp hf with
        ⟨G, hG, hfG⟩
      exact (h₁ p hp _ hM).2 j M₀ _ _ rfl hM₀ (isAtkinLehnerElementAt_ofCoprime hc₀)
        (isAtkinLehnerElementAt_ofCoprime hc) G hG hfG
    · rcases (mem_levelRaisingModularImage_levelRaisingEta_iff k f).mp hf with ⟨G, hG, hfG⟩
      exact h₂ p hp M hM G hG hfG

end SiegelUpperHalfSpace
