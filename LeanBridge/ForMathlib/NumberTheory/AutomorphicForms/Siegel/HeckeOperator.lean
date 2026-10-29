import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.HeckeRing

/-!
# Hecke operators on Siegel modular forms

The slash operator of `GSp(2g, ℚ)⁺` is a right action. For a Hecke pair `(Γ, Δ)` in `GL(2g, ℚ)`
with `Δ ≤ GSp(2g, ℚ)⁺`, such as `(Sp(2g, ℤ), S)` with `S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)` or
`(Γ, S_Γ)` for an arithmetic subgroup `Γ` of `Sp(2g, ℚ)` (of level `N`, say), a double coset
`ΓαΓ = ⊔ᵢ Γαᵢ` with `α ∈ Δ` acts on `Γ`-invariant functions by `F ↦ ∑ᵢ F ∣_ρ αᵢ`. The sum does
not depend on the representatives `αᵢ` and is again `Γ`-invariant, since right multiplication by
`γ ∈ Γ` permutes the right cosets `Γαᵢ`; extending linearly gives the action of the Hecke algebra
`𝓗(Γ)`. It preserves holomorphy, hence `M_ρ(Γ)`, as soon as the slash operator does.

## Main definitions

* `SiegelUpperHalfSpace.slashInvariantsOf`: the `Γ`-invariant functions `F : ℋ_g → V`, and
  `SiegelUpperHalfSpace.slashInvariants` those for `Γ = Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.heckeOperator` (LMFDB `mf.siegel.hecke_operator`): the Hecke operator
  `F ↦ ∑ᵢ F ∣_ρ αᵢ` of a double coset `ΓαΓ = ⊔ᵢ Γαᵢ`.
* `SiegelUpperHalfSpace.heckeAlgebraActionOf`: the action of the Hecke algebra `𝓗(Γ)`, and
  `SiegelUpperHalfSpace.heckeAlgebraAction` that for `Γ = Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.IsHeckeEigenform` (LMFDB `mf.siegel.hecke_operator`): Hecke eigenforms.

## Main results

* `SiegelUpperHalfSpace.gspSlash_mul`: the slash operator is a right action of `GSp(2g, ℚ)⁺`.
* `SiegelUpperHalfSpace.mem_modularForms_iff_slashInvariantsOf`: for an arithmetic subgroup `Γ`
  of `Sp(2g, ℚ)`, `M_ρ(Γ)` consists of the holomorphic `Γ`-invariant functions, and
  `SiegelUpperHalfSpace.mem_modularForms_iff_slashInvariants` for `Γ = Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.heckeOperator_eq_sum`: the Hecke operator is the sum over any family of
  representatives of the right cosets of the double coset.
* `SiegelUpperHalfSpace.heckeOperator_mem_modularForms_of_isArithmetic`: the Hecke operators
  preserve `M_ρ(Γ)` when the slash operator preserves holomorphy, and
  `SiegelUpperHalfSpace.heckeOperator_mem_modularForms` for `Γ = Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.isHeckeEigenform_const_of_isArithmetic`: nonzero constants are Hecke
  eigenforms of trivial weight, and `SiegelUpperHalfSpace.isHeckeEigenform_const` for
  `Γ = Sp(2g, ℤ)`.
-/

open Matrix hiding mul_inv_rev

open DoubleCoset Complex Module MulAction

open scoped Pointwise

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] [Nonempty l] (α β : gspPlus l)

lemma multiplier_mul : multiplier (α * β) = multiplier α * multiplier β :=
  multiplier_eq _ <| by
    have h : ((α * β : gspPlus l) : Matrix (l ⊕ l) (l ⊕ l) ℚ)ᵀ * J l ℚ * (α * β : gspPlus l) =
        (β : Matrix (l ⊕ l) (l ⊕ l) ℚ)ᵀ * ((α : Matrix (l ⊕ l) (l ⊕ l) ℚ)ᵀ * J l ℚ * α) * β := by
      simp only [Submonoid.coe_mul, transpose_mul, Matrix.mul_assoc]
    rw [h, transpose_mul_J_mul, Matrix.mul_smul, Matrix.smul_mul, transpose_mul_J_mul, smul_smul]

lemma toSp_mul : toSp (α * β) = toSp α * toSp β := by
  ext : 1
  simp only [toSp, Submonoid.coe_mul, multiplier_mul, Rat.cast_mul,
    Real.sqrt_mul (Rat.cast_nonneg.mpr (multiplier_pos α).le), mul_inv, Matrix.map_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]

variable (τ : SiegelUpperHalfSpace l)

lemma gspSmul_mul : gspSmul (α * β) τ = gspSmul α (gspSmul β τ) := by
  rw [gspSmul, gspSmul, gspSmul, toSp_mul, mul_smul]

lemma gspDenomGL_mul : gspDenomGL (α * β) τ = gspDenomGL α (gspSmul β τ) * gspDenomGL β τ := by
  ext : 1
  rw [Units.val_mul, coe_gspDenomGL, coe_gspDenomGL, coe_gspDenomGL, gspDenom_eq, gspDenom_eq,
    gspDenom_eq, toSp_mul, denom_mul, multiplier_mul, Rat.cast_mul,
    Real.sqrt_mul (Rat.cast_nonneg.mpr (multiplier_pos α).le), ofReal_mul, gspSmul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

variable {n : ℕ} [NeZero n] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℂ) V) (f : SiegelUpperHalfSpace (Fin n) → V)

/-- **The slash operator is a right action of `GSp(2g, ℚ)⁺`**: `f ∣ αβ = (f ∣ α) ∣ β`, by the
multiplicativity of the multiplier and the cocycle relation of the automorphy factor. -/
lemma gspSlash_mul (α β : gspPlus (Fin n)) :
    gspSlash ρ (α * β) f = gspSlash ρ β (gspSlash ρ α f) := by
  ext τ
  simp only [gspSlash, gspDenomGL_mul, gspSmul_mul, multiplier_mul, mul_inv_rev, map_mul,
    End.mul_apply, map_smul, smul_smul, Rat.cast_mul, mul_zpow, mul_comm]

variable {Δ : Submonoid (GL (Fin n ⊕ Fin n) ℚ)} [Fact (Δ ≤ gspPlusGL (Fin n))]

/-- An element of a submonoid `Δ` of `GSp(2g, ℚ)⁺` in `GL(2g, ℚ)`, as an element of the monoid
`GSp(2g, ℚ)⁺` of matrices. -/
def submonoidToGSpPlus (x : Δ) : gspPlus (Fin n) :=
  ⟨(x : GL (Fin n ⊕ Fin n) ℚ), Fact.out (p := Δ ≤ gspPlusGL (Fin n)) x.2⟩

/-- The slash operator `f ↦ f ∣_ρ α` of an element `α` of a submonoid `Δ` of `GSp(2g, ℚ)⁺`, such
as `S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)`, as a linear map. -/
noncomputable def heckeMonoidSlash (x : Δ) :
    (SiegelUpperHalfSpace (Fin n) → V) →ₗ[ℂ] SiegelUpperHalfSpace (Fin n) → V where
  toFun f := gspSlash ρ (submonoidToGSpPlus x) f
  map_add' f g := by
    ext τ
    simp [gspSlash]
  map_smul' c f := by
    ext τ
    simp [gspSlash, smul_comm c]

lemma heckeMonoidSlash_mul (x y : Δ) :
    heckeMonoidSlash ρ (x * y) f = heckeMonoidSlash ρ y (heckeMonoidSlash ρ x f) :=
  gspSlash_mul ρ f (submonoidToGSpPlus x) (submonoidToGSpPlus y)

variable (Δ) in
/-- The space of functions `F : ℋ_g → V` invariant under the slash operator of a subgroup `Γ` of
`GL(2g, ℚ)`, for a Hecke pair `(Γ, Δ)` with `Δ ≤ GSp(2g, ℚ)⁺`. -/
def slashInvariantsOf (Γ : Subgroup (GL (Fin n ⊕ Fin n) ℚ)) [IsHeckeTriple Δ Γ Γ] :
    Submodule ℂ (SiegelUpperHalfSpace (Fin n) → V) where
  carrier := {f | ∀ γ (hγ : γ ∈ Γ),
    heckeMonoidSlash ρ (⟨γ, IsHeckeTriple.left_le (H₂ := Γ) hγ⟩ : Δ) f = f}
  add_mem' hf hg γ hγ := by
    rw [map_add, hf γ hγ, hg γ hγ]
  zero_mem' γ hγ :=
    map_zero _
  smul_mem' c f hf γ hγ := by
    rw [map_smul, hf γ hγ]

/-- The space of functions `F : ℋ_g → V` invariant under the slash operator of `Sp(2g, ℤ)`. -/
abbrev slashInvariants : Submodule ℂ (SiegelUpperHalfSpace (Fin n) → V) :=
  slashInvariantsOf ρ (heckeMonoid (Fin n)) (heckeGamma (Fin n))

/-- **For an arithmetic subgroup `Γ` of `Sp(2g, ℚ)`, `M_ρ(Γ)` consists of the holomorphic
`Γ`-invariant functions.** -/
lemma mem_modularForms_iff_slashInvariantsOf (Γ : Subgroup (symplecticGroup (Fin n) ℚ))
    [Fact (SymplecticGroup.IsArithmetic Γ)] :
    f ∈ modularForms ρ Γ 1 ↔
      IsHolomorphic f ∧ f ∈ slashInvariantsOf ρ (heckeMonoidOf Γ) (heckeGammaOf Γ) := by
  rw [mem_modularForms_iff_slash]
  refine and_congr_right fun _ ↦ ⟨fun h γ hγ ↦ ?_, fun h γ ↦ ?_⟩
  · rcases hγ with ⟨γ, hγ, rfl⟩
    have h' : gspSlash ρ (ofSp γ) f = f := by
      simpa only [MonoidHom.one_apply, Units.val_one, one_smul, ← gspSlash_ofSp] using
        h ⟨γ, hγ⟩
    exact h'
  · rw [MonoidHom.one_apply, Units.val_one, one_smul, ← gspSlash_ofSp]
    exact h _ ⟨γ, γ.2, rfl⟩

/-- **`M_ρ(Sp(2g, ℤ))` consists of the holomorphic `Sp(2g, ℤ)`-invariant functions.** -/
lemma mem_modularForms_iff_slashInvariants :
    f ∈ modularForms ρ (SymplecticGroup.integral (Fin n)) 1 ↔
      IsHolomorphic f ∧ f ∈ slashInvariants ρ := by
  rw [mem_modularForms_iff_slash]
  refine and_congr_right fun _ ↦ ⟨fun h γ hγ ↦ ?_, fun h γ ↦ ?_⟩
  · rcases hγ with ⟨γ, -, rfl⟩
    have h' : gspSlash ρ (ofSp (SymplecticGroup.map (Int.castRingHom ℚ) γ)) f = f := by
      simpa only [MonoidHom.one_apply, Units.val_one, one_smul, ← gspSlash_ofSp] using
        h ⟨_, γ, trivial, rfl⟩
    exact h'
  · rcases γ with ⟨-, γ, -, rfl⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul, ← gspSlash_ofSp]
    exact h _ ⟨γ, trivial, rfl⟩

variable {Γ : Subgroup (GL (Fin n ⊕ Fin n) ℚ)} [IsHeckeTriple Δ Γ Γ]

variable {ρ f} in
private lemma heckeMonoidSlash_eq_of_mul_inv_mem (hf : f ∈ slashInvariantsOf ρ Δ Γ) {x y : Δ}
    (h : (y : GL (Fin n ⊕ Fin n) ℚ) * (x : GL (Fin n ⊕ Fin n) ℚ)⁻¹ ∈ Γ) :
    heckeMonoidSlash ρ x f = heckeMonoidSlash ρ y f := by
  have hy : y = ⟨_, IsHeckeTriple.left_le (H₂ := Γ) h⟩ * x :=
    Subtype.ext <| (inv_mul_cancel_right _ _).symm
  rw [hy, heckeMonoidSlash_mul, hf _ h]

variable (D : HeckeCoset Δ Γ Γ)

attribute [local instance] Fintype.ofFinite

/-- The representative `δ τᵥ⁻¹` of the `v`-th right coset `Γ δ τᵥ⁻¹` of the double coset
`D = Γ δ Γ`, as an element of `Δ`. -/
noncomputable def heckeRep (v : DecompQuotient Γ Γ (D.out : GL _ ℚ)⁻¹) : Δ :=
  ⟨rightCosetRep D v, rightCosetRep_mem D D.out.2 (IsHeckeTriple.left_le (H₂ := Γ)) v⟩

/-- The **Hecke operator** (LMFDB `mf.siegel.hecke_operator`) of a double coset
`D = ΓαΓ = ⊔ᵢ Γαᵢ` of a Hecke pair `(Γ, Δ)` with `Δ ≤ GSp(2g, ℚ)⁺`, such as `Γ = Sp(2g, ℤ)` and
`Δ = S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)`, or an arithmetic subgroup `Γ` of `Sp(2g, ℚ)` (of level `N`) and
`Δ = S_Γ`, on the `Γ`-invariant functions: `F ↦ F ∣_ρ D = ∑ᵢ F ∣_ρ αᵢ`, with the normalised slash
operator `gspSlash`. It is defined with chosen representatives `αᵢ`, but does not depend on them
(`heckeOperator_eq_sum`); its value is again `Γ`-invariant, since right multiplication by `γ ∈ Γ`
permutes the right cosets `Γαᵢ`. -/
noncomputable def heckeOperator : End ℂ (slashInvariantsOf ρ Δ Γ) where
  toFun f := ⟨∑ v, heckeMonoidSlash ρ (heckeRep D v) f, fun γ hγ ↦ by
    rw [map_sum]
    refine Fintype.sum_equiv (toPerm (⟨γ, hγ⟩ : Γ)⁻¹) _ _ fun v ↦ ?_
    rw [← heckeMonoidSlash_mul]
    refine heckeMonoidSlash_eq_of_mul_inv_mem f.2 ?_
    rcases exists_mem_out_mul_inv_eq_mul_rightCosetRep D (mul_mem (inv_mem hγ) v.out.2) with
      ⟨γ₁, hγ₁, hsplit⟩
    have hmk : (QuotientGroup.mk ⟨γ⁻¹ * (v.out : GL _ ℚ), mul_mem (inv_mem hγ) v.out.2⟩ :
        DecompQuotient Γ Γ (D.out : GL _ ℚ)⁻¹) = (⟨γ, hγ⟩ : Γ)⁻¹ • v :=
      Quotient.mk_smul_out _ (⟨γ, hγ⟩ : Γ)⁻¹ v
    have hprod : rightCosetRep D v * γ = γ₁ * rightCosetRep D ((⟨γ, hγ⟩ : Γ)⁻¹ • v) := by
      simpa only [hmk, mul_inv_rev, inv_inv, ← mul_assoc, rightCosetRep_def] using hsplit
    simpa [heckeRep, hprod, mul_assoc] using inv_mem hγ₁⟩
  map_add' f g := Subtype.ext <| by
    simp [Finset.sum_add_distrib]
  map_smul' c f := Subtype.ext <| by
    simp [Finset.smul_sum]

lemma coe_heckeOperator (F : slashInvariantsOf ρ Δ Γ) :
    (heckeOperator ρ D F : SiegelUpperHalfSpace (Fin n) → V) =
      ∑ v, heckeMonoidSlash ρ (heckeRep D v) F :=
  rfl

/-- **The Hecke operator does not depend on the representatives**: for any family `(aᵢ)` in `Δ`
whose right cosets `Γaᵢ` are pairwise distinct and cover `D = ΓαΓ`,
`F ∣_ρ D = ∑ᵢ F ∣_ρ aᵢ`. -/
lemma heckeOperator_eq_sum {ι : Type*} [Fintype ι] (a : ι → Δ)
    (hcover : doubleCoset (D.out : GL (Fin n ⊕ Fin n) ℚ) (Γ : Set (GL (Fin n ⊕ Fin n) ℚ)) Γ =
      ⋃ i, MulOpposite.op (a i : GL (Fin n ⊕ Fin n) ℚ) • (Γ : Set (GL (Fin n ⊕ Fin n) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i : GL (Fin n ⊕ Fin n) ℚ) •
      (Γ : Set (GL (Fin n ⊕ Fin n) ℚ)))
    (F : slashInvariantsOf ρ Δ Γ) :
    (heckeOperator ρ D F : SiegelUpperHalfSpace (Fin n) → V) =
      ∑ i, heckeMonoidSlash ρ (a i) F := by
  rcases exists_bijective_rightCosetRep_smul_eq D (fun i ↦ (a i : GL (Fin n ⊕ Fin n) ℚ)) hcover
    hinj with ⟨φ, hφ, h⟩
  exact (Fintype.sum_bijective φ hφ _ _ fun i ↦
    heckeMonoidSlash_eq_of_mul_inv_mem F.2 ((rightCoset_eq_iff _).mp (h i))).symm

lemma isHolomorphic_heckeOperator
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f)) {F : slashInvariantsOf ρ Δ Γ}
    (hF : IsHolomorphic (F : SiegelUpperHalfSpace (Fin n) → V)) :
    IsHolomorphic (heckeOperator ρ D F : SiegelUpperHalfSpace (Fin n) → V) := by
  rw [coe_heckeOperator]
  exact Finset.sum_induction _ IsHolomorphic (fun _ _ ↦ IsHolomorphic.add) isHolomorphic_zero
    fun v _ ↦ hρ _ _ hF

/-- **The Hecke operators preserve `M_ρ(Γ)`** for an arithmetic subgroup `Γ` of `Sp(2g, ℚ)`, such
as a congruence subgroup of level `N`, when the slash operator of `GSp(2g, ℚ)⁺` preserves
holomorphy, as it does for the holomorphic finite-dimensional representations `ρ` of the LMFDB. -/
lemma heckeOperator_mem_modularForms_of_isArithmetic {Γ₀ : Subgroup (symplecticGroup (Fin n) ℚ)}
    [Fact (SymplecticGroup.IsArithmetic Γ₀)]
    (E : HeckeCoset (heckeMonoidOf Γ₀) (heckeGammaOf Γ₀) (heckeGammaOf Γ₀))
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f))
    {F : slashInvariantsOf ρ (heckeMonoidOf Γ₀) (heckeGammaOf Γ₀)}
    (hF : (F : SiegelUpperHalfSpace (Fin n) → V) ∈ modularForms ρ Γ₀ 1) :
    (heckeOperator ρ E F : SiegelUpperHalfSpace (Fin n) → V) ∈ modularForms ρ Γ₀ 1 := by
  rw [mem_modularForms_iff_slashInvariantsOf] at hF ⊢
  exact ⟨isHolomorphic_heckeOperator ρ E hρ hF.1, (heckeOperator ρ E F).2⟩

/-- **The Hecke operators preserve `M_ρ(Sp(2g, ℤ))`** when the slash operator of `GSp(2g, ℚ)⁺`
preserves holomorphy, as it does for the holomorphic finite-dimensional representations `ρ` of the
LMFDB. -/
lemma heckeOperator_mem_modularForms
    (E : HeckeCoset (heckeMonoid (Fin n)) (heckeGamma (Fin n)) (heckeGamma (Fin n)))
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f)) {F : slashInvariants ρ}
    (hF : (F : SiegelUpperHalfSpace (Fin n) → V) ∈
      modularForms ρ (SymplecticGroup.integral (Fin n)) 1) :
    (heckeOperator ρ E F : SiegelUpperHalfSpace (Fin n) → V) ∈
      modularForms ρ (SymplecticGroup.integral (Fin n)) 1 := by
  rw [mem_modularForms_iff_slashInvariants] at hF ⊢
  exact ⟨isHolomorphic_heckeOperator ρ E hρ hF.1, (heckeOperator ρ E F).2⟩

variable (Δ Γ) in
/-- The action of the Hecke algebra `𝓗(Γ)` of a Hecke pair `(Γ, Δ)` with `Δ ≤ GSp(2g, ℚ)⁺`, such
as that of an arithmetic subgroup `Γ` of `Sp(2g, ℚ)` (`siegelHeckeRingOf`), on the `Γ`-invariant
functions, the linear extension of `F ↦ F ∣_ρ ΓαΓ`: `F ∣_ρ ∑ⱼ cⱼ Dⱼ = ∑ⱼ cⱼ F ∣_ρ Dⱼ`
(LMFDB `mf.siegel.hecke_operator`). -/
noncomputable def heckeAlgebraActionOf : HeckeRing Δ Γ ℂ →ₗ[ℂ] End ℂ (slashInvariantsOf ρ Δ Γ) :=
  Finsupp.linearCombination ℂ (heckeOperator ρ)

lemma heckeAlgebraActionOf_single (c : ℂ) :
    heckeAlgebraActionOf ρ Δ Γ (HeckeCosetModule.single ℂ D c) = c • heckeOperator ρ D :=
  Finsupp.linearCombination_single ℂ c D

/-- The action of the Hecke algebra `𝓗(Γ)` of `Γ = Sp(2g, ℤ)` on the `Γ`-invariant functions
(LMFDB `mf.siegel.hecke_operator`). -/
noncomputable abbrev heckeAlgebraAction :
    siegelHeckeRing (Fin n) →ₗ[ℂ] End ℂ (slashInvariants ρ) :=
  heckeAlgebraActionOf ρ (heckeMonoid (Fin n)) (heckeGamma (Fin n))

lemma heckeAlgebraAction_single
    (E : HeckeCoset (heckeMonoid (Fin n)) (heckeGamma (Fin n)) (heckeGamma (Fin n))) (c : ℂ) :
    heckeAlgebraAction ρ (HeckeCosetModule.single ℂ E c) = c • heckeOperator ρ E :=
  heckeAlgebraActionOf_single ρ E c

/-- A **Hecke eigenform** (LMFDB `mf.siegel.hecke_operator`) of weight `ρ` for a Hecke pair
`(Γ, Δ)`, such as `Γ = Sp(2g, ℤ)` with `Δ = S`, or an arithmetic subgroup `Γ` of `Sp(2g, ℚ)` with
`Δ = S_Γ`: a nonzero holomorphic `Γ`-invariant function `F` (an element of `M_ρ(Γ)`,
`mem_modularForms_iff_slashInvariantsOf`) which is an eigenvector of every Hecke operator
`F ↦ F ∣_ρ ΓαΓ`, `α ∈ Δ`; these span the Hecke algebra `𝓗(Γ)`, so `F` is a simultaneous
eigenvector of `𝓗(Γ)`. -/
def IsHeckeEigenform (F : slashInvariantsOf ρ Δ Γ) : Prop :=
  IsHolomorphic (F : SiegelUpperHalfSpace (Fin n) → V) ∧ F ≠ 0 ∧
    ∀ D, ∃ c : ℂ, heckeOperator ρ D F = c • F

lemma isHeckeEigenform_const_of_mem {v : V} (hv : v ≠ 0)
    (hmem : Function.const _ v ∈
      slashInvariantsOf (Representation.trivial ℂ (GL (Fin n) ℂ) V) Δ Γ) :
    IsHeckeEigenform (Representation.trivial ℂ (GL (Fin n) ℂ) V) ⟨Function.const _ v, hmem⟩ := by
  have hτ : ((I • 1 : Matrix (Fin n) (Fin n) ℂ).map im).PosDef := by
    convert PosDef.one (n := Fin n) (R := ℝ)
    ext i j
    rcases eq_or_ne i j with rfl | hij <;> simp [one_apply, *]
  have h (α : gspPlus (Fin n)) :
      gspSlash (Representation.trivial ℂ (GL (Fin n) ℂ) V) α (Function.const _ v) =
        ((multiplier α : ℂ) ^ slashExponent (Representation.trivial ℂ (GL (Fin n) ℂ) V)) •
          Function.const _ v := by
    ext τ
    simp [gspSlash]
  refine ⟨(const_mem_modularForms (SymplecticGroup.integral (Fin n)) v).1,
    fun h ↦ hv <| congrFun (congrArg Subtype.val h) ⟨I • 1, by simp, hτ⟩,
    fun D ↦ ⟨∑ w, (multiplier (submonoidToGSpPlus (heckeRep D w)) : ℂ) ^
      slashExponent (Representation.trivial ℂ (GL (Fin n) ℂ) V), Subtype.ext ?_⟩⟩
  rw [coe_heckeOperator]
  simp only [heckeMonoidSlash, LinearMap.coe_mk, AddHom.coe_mk, h, Finset.sum_smul,
    Submodule.coe_sum, Submodule.coe_smul]

/-- **Nonzero constants are Hecke eigenforms of trivial weight** for an arithmetic subgroup `Γ` of
`Sp(2g, ℚ)`, with eigenvalue `∑ᵢ r(αᵢ) ^ e` on `ΓαΓ = ⊔ᵢ Γαᵢ`, where `e` is the exponent of the
multiplier in the slash operator; so `IsHeckeEigenform` is not vacuous. -/
lemma isHeckeEigenform_const_of_isArithmetic (Γ₀ : Subgroup (symplecticGroup (Fin n) ℚ))
    [Fact (SymplecticGroup.IsArithmetic Γ₀)] {v : V} (hv : v ≠ 0) :
    IsHeckeEigenform (Representation.trivial ℂ (GL (Fin n) ℂ) V) ⟨Function.const _ v,
      ((mem_modularForms_iff_slashInvariantsOf _ _ Γ₀).mp (const_mem_modularForms _ v)).2⟩ :=
  isHeckeEigenform_const_of_mem hv _

/-- **Nonzero constants are Hecke eigenforms of trivial weight** for `Sp(2g, ℤ)`, with eigenvalue
`∑ᵢ r(αᵢ) ^ e` on `ΓαΓ = ⊔ᵢ Γαᵢ`, where `e` is the exponent of the multiplier in the slash
operator; so `IsHeckeEigenform` is not vacuous. -/
lemma isHeckeEigenform_const {v : V} (hv : v ≠ 0) :
    IsHeckeEigenform (Representation.trivial ℂ (GL (Fin n) ℂ) V) ⟨Function.const _ v,
      ((mem_modularForms_iff_slashInvariants _ _).mp (const_mem_modularForms _ v)).2⟩ :=
  isHeckeEigenform_const_of_mem hv _

end SiegelUpperHalfSpace
