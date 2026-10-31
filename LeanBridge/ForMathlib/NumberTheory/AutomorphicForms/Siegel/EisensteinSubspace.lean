import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoSubspaces
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SiegelEisensteinSeries

/-!
# The subspace of Siegel Eisenstein series

The vector-valued Siegel Eisenstein series of weight `ρ` and degree `g` attached to a vector
`v ∈ V` is `E(v)(Z) = ∑_{(C, D)} ρ(CZ + D)⁻¹ v`, summed over the right cosets of the Siegel
parabolic subgroup `P = {(A, B; 0, D)}` in `Sp(2g, ℤ)`. For `γ ∈ P`, `ρ(C_{γδ}Z + D_{γδ})⁻¹ v =
ρ(C_δ Z + D_δ)⁻¹ ρ(D_γ)⁻¹ v`, so the terms only depend on the cosets when `v` is fixed by
`ρ(GL(g, ℤ))`. The subspace `E_{j,k}(Γ₂)` of the LMFDB knowl `mf.siegel.subspace.degree.two` is
spanned by these series for `ρ = ρ_{k,j} = det^k ⊗ Sym^j`; for scalar weight `ρ = det^k` and
`v = 1` they are the Siegel Eisenstein series `ψ_k` of
`SiegelUpperHalfSpace.siegelEisensteinSeries`, and `1` is invariant for even `k`. That the series
converge for `k > g + 1` (to Siegel modular forms), that `E_{j,k}(Γ₂)` vanishes for `j > 0`, and
the decompositions of the knowl are not proved here.

## Main definitions

* `SiegelUpperHalfSpace.vectorSiegelEisensteinTerm`: the term `ρ(CZ + D)⁻¹ v`.
* `SiegelUpperHalfSpace.IsGLIntInvariant`: `v` is fixed by `ρ(GL(g, ℤ))`.
* `SiegelUpperHalfSpace.IsVectorSiegelEisensteinSeries`: `F` is the Siegel Eisenstein series of
  `v`.
* `SiegelUpperHalfSpace.siegelEisensteinSubspace` (LMFDB `mf.siegel.subspace.degree.two`): the
  space of Siegel Eisenstein series of weight `ρ` on `Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.siegelEisensteinSubspaceKJ` (LMFDB `mf.siegel.subspace.degree.two`): the
  space `E_{j,k}(Γ₂)`.

## Main results

* `SiegelUpperHalfSpace.vectorSiegelEisensteinTerm_mul`: for invariant `v`, the terms only depend
  on the cosets of the Siegel parabolic subgroup.
* `SiegelUpperHalfSpace.IsVectorSiegelEisensteinSeries.unique`: the Siegel Eisenstein series of
  `v` is unique.
* `SiegelUpperHalfSpace.isGLIntInvariant_detPowerRep_one`: `1` is invariant under `det^k` for even
  `k`.
* `SiegelUpperHalfSpace.isVectorSiegelEisensteinSeries_detPowerRep_iff`: in scalar weight `k`,
  `F` is the Siegel Eisenstein series of `1` exactly when `F(Z) = ∑ det(CZ + D)^{-k}`, the series of
  `SiegelUpperHalfSpace.siegelEisensteinSeries`.
-/

open Module

open Matrix hiding mul_inv_rev inv_zpow'

open scoped TensorProduct

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL l ℂ) V) (v : V) (Z : SiegelUpperHalfSpace l)
    (δ : symplecticGroup l ℤ)

/-- The term `ρ(CZ + D)⁻¹ v` of the vector-valued Siegel Eisenstein series of `v ∈ V`, for
`δ = (A, B; C, D) ∈ Sp(2g, ℤ)` and `Z ∈ ℋ_g`. -/
noncomputable def vectorSiegelEisensteinTerm : V :=
  ρ (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z)⁻¹ v

/-- The vector `v ∈ V` is **invariant under `GL(g, ℤ)`**: `ρ(D) v = v` for every `D ∈ GL(g, ℤ)`,
which makes the terms of its Siegel Eisenstein series only depend on the cosets of the Siegel
parabolic subgroup (`SiegelUpperHalfSpace.vectorSiegelEisensteinTerm_mul`). -/
def IsGLIntInvariant : Prop :=
  ∀ D : GL l ℤ, ρ (GeneralLinearGroup.map (Int.castRingHom ℂ) D) v = v

private lemma denomGL_siegelParabolic (γ : SymplecticGroup.siegelParabolic l ℤ) :
    denomGL (SymplecticGroup.map (Int.castRingHom ℝ) (γ : symplecticGroup l ℤ)) Z =
      GeneralLinearGroup.map (Int.castRingHom ℂ)
        ((isUnit_iff_isUnit_det _).mpr (SymplecticGroup.isUnit_det_toBlocks₂₂ γ)).unit := by
  have hC (i j : l) : (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ) (.inr i) (.inl j) = 0 :=
    congrFun (congrFun γ.2 i) j
  ext i j
  simp [denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, hC]

variable {ρ v}

/-- **The terms of the Siegel Eisenstein series of an invariant vector only depend on the coset
`Pδ`** of the Siegel parabolic subgroup `P`: for `γ = (A, B; 0, D) ∈ P`,
`ρ(C_{γδ}Z + D_{γδ})⁻¹ v = ρ(C_δ Z + D_δ)⁻¹ ρ(D)⁻¹ v`. -/
lemma vectorSiegelEisensteinTerm_mul (hv : IsGLIntInvariant ρ v)
    (γ : SymplecticGroup.siegelParabolic l ℤ) :
    vectorSiegelEisensteinTerm ρ v Z ((γ : symplecticGroup l ℤ) * δ) =
      vectorSiegelEisensteinTerm ρ v Z δ := by
  rw [vectorSiegelEisensteinTerm, vectorSiegelEisensteinTerm, map_mul, denomGL_mul, mul_inv_rev,
    map_mul, End.mul_apply, denomGL_siegelParabolic, ← map_inv, hv]

lemma vectorSiegelEisensteinTerm_out (hv : IsGLIntInvariant ρ v) :
    vectorSiegelEisensteinTerm ρ v Z (⟦δ⟧ : SymplecticGroup.SiegelParabolicCosets l).out =
      vectorSiegelEisensteinTerm ρ v Z δ := by
  have h : δ * (⟦δ⟧ : SymplecticGroup.SiegelParabolicCosets l).out⁻¹ ∈
      SymplecticGroup.siegelParabolic l ℤ :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out δ)
  conv_rhs => rw [← inv_mul_cancel_right δ (⟦δ⟧ : SymplecticGroup.SiegelParabolicCosets l).out]
  exact (vectorSiegelEisensteinTerm_mul Z _ hv ⟨_, h⟩).symm

variable (ρ v) in
/-- The function `F : ℋ_g → V` is the **vector-valued Siegel Eisenstein series** of `v ∈ V`:
`F(Z) = ∑_{(C, D)} ρ(CZ + D)⁻¹ v`, the sum over the right cosets of the Siegel parabolic subgroup
`{(A, B; 0, D)}` of `Sp(2g, ℤ)` converging unconditionally, with chosen representatives (for `v`
invariant under `GL(g, ℤ)` the terms do not depend on them,
`SiegelUpperHalfSpace.vectorSiegelEisensteinTerm_mul`). As for
`SiegelUpperHalfSpace.HasSiegelFourierExpansion`, the sum is taken coordinatewise, through every
linear form on `V`. -/
def IsVectorSiegelEisensteinSeries (F : SiegelUpperHalfSpace l → V) : Prop :=
  ∀ (Z : SiegelUpperHalfSpace l) (φ : Dual ℂ V), HasSum
    (fun x : SymplecticGroup.SiegelParabolicCosets l ↦ φ (vectorSiegelEisensteinTerm ρ v Z x.out))
      (φ (F Z))

/-- **The Siegel Eisenstein series of `v` is unique**, linear forms separating the points of
`V`. -/
lemma IsVectorSiegelEisensteinSeries.unique {F G : SiegelUpperHalfSpace l → V}
    (hF : IsVectorSiegelEisensteinSeries ρ v F) (hG : IsVectorSiegelEisensteinSeries ρ v G) :
    F = G := by
  funext Z
  rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  rw [map_sub, (hF Z φ).unique (hG Z φ), sub_self]

variable (ρ) in
/-- The space of **Siegel Eisenstein series** of weight `ρ` on `Sp(2g, ℤ)` (LMFDB
`mf.siegel.subspace.degree.two`): the span of the vector-valued Siegel Eisenstein series
`E(v)(Z) = ∑ ρ(CZ + D)⁻¹ v` of the vectors `v ∈ V` invariant under `GL(g, ℤ)`, where the series
converge (`SiegelUpperHalfSpace.IsVectorSiegelEisensteinSeries`). -/
def siegelEisensteinSubspace : Submodule ℂ (SiegelUpperHalfSpace l → V) :=
  Submodule.span ℂ {F | ∃ v, IsGLIntInvariant ρ v ∧ IsVectorSiegelEisensteinSeries ρ v F}

/-- The space `E_{j,k}(Γ₂)` of **Siegel Eisenstein series of degree `2`** (LMFDB
`mf.siegel.subspace.degree.two`) and weight `ρ_{k,j} = det^k ⊗ Sym^j`
(`SiegelUpperHalfSpace.rhoKJ`) on `Γ₂ = Sp(4, ℤ)`, spanned by the vector-valued Siegel Eisenstein
series of the vectors of `Sym^j(ℂ²)` invariant under `GL(2, ℤ)`. For `j = 0` and even `k > 3` it
is spanned by `ψ_k`; that it vanishes for `j > 0` is not proved here. -/
noncomputable abbrev siegelEisensteinSubspaceKJ (k : ℤ) (j : ℕ) :
    Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) :=
  siegelEisensteinSubspace (rhoKJ k j)

end SiegelUpperHalfSpace

/-! ### Scalar weight -/

namespace SiegelUpperHalfSpace

variable {n : ℕ} {k : ℤ}

/-- **In scalar weight `k`, `1` is invariant under `GL(g, ℤ)` for even `k`**, as `det D = ±1`. -/
lemma isGLIntInvariant_detPowerRep_one (hk : Even k) :
    IsGLIntInvariant (TauCeti.detPowerRep ℂ n k) 1 := by
  intro D
  have hD : IsUnit (D : Matrix (Fin n) (Fin n) ℤ).det := (isUnit_iff_isUnit_det _).mp D.isUnit
  have hm : ((GeneralLinearGroup.map (Int.castRingHom ℂ) D : GL (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) = (Int.castRingHom ℂ).mapMatrix (D : Matrix (Fin n) (Fin n) ℤ) :=
    rfl
  rw [TauCeti.detPowerRep_apply, mul_one, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply, hm, ← RingHom.map_det]
  rcases Int.isUnit_iff.mp hD with h | h <;> simp [h, hk.neg_one_zpow]

lemma vectorSiegelEisensteinTerm_detPowerRep (Z : SiegelUpperHalfSpace (Fin n))
    (δ : symplecticGroup (Fin n) ℤ) :
    vectorSiegelEisensteinTerm (TauCeti.detPowerRep ℂ n k) 1 Z δ = siegelEisensteinTerm k Z δ := by
  rw [vectorSiegelEisensteinTerm, TauCeti.detPowerRep_apply, mul_one, map_inv, inv_zpow',
    Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, coe_denomGL,
    siegelEisensteinTerm]

/-- **In scalar weight `k`, the Siegel Eisenstein series of `1` is the series of `ψ_k`**: `F` is
the Siegel Eisenstein series of `1` for `ρ = det^k` exactly when
`F(Z) = ∑_{(C, D)} det(CZ + D)^{-k}` for every `Z`, the series whose sum is
`SiegelUpperHalfSpace.siegelEisensteinSeries`. -/
lemma isVectorSiegelEisensteinSeries_detPowerRep_iff (F : SiegelUpperHalfSpace (Fin n) → ℂ) :
    IsVectorSiegelEisensteinSeries (TauCeti.detPowerRep ℂ n k) 1 F ↔ ∀ Z,
      HasSum (fun x : SymplecticGroup.SiegelParabolicCosets (Fin n) ↦
        siegelEisensteinTerm k Z x.out) (F Z) := by
  simp only [IsVectorSiegelEisensteinSeries, vectorSiegelEisensteinTerm_detPowerRep]
  refine ⟨fun h Z ↦ h Z LinearMap.id, fun h Z φ ↦ ?_⟩
  have hφ (x : ℂ) : φ x = φ 1 * x := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hφ (F Z)]
  exact ((h Z).mul_left (φ 1)).congr_fun fun x ↦ hφ _

end SiegelUpperHalfSpace
