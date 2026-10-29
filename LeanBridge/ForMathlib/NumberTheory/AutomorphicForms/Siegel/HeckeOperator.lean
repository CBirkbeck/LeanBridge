import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.HeckeRing
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.Level

/-!
# Hecke operators on Siegel modular forms

The slash operator of `GSp(2g, ℚ)⁺` is a right action, and a double coset `ΓαΓ = ⊔ᵢ Γαᵢ` of
`Γ = Sp(2g, ℤ)` with `α ∈ S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)` acts on `Γ`-invariant functions by
`F ↦ ∑ᵢ F ∣_ρ αᵢ`. The sum does not depend on the representatives `αᵢ` and is again
`Γ`-invariant, since right multiplication by `γ ∈ Γ` permutes the right cosets `Γαᵢ`; extending
linearly gives the action of the Hecke algebra `𝓗(Γ)`. It preserves holomorphy, hence
`M_ρ(Γ)`, as soon as the slash operator does.

## Main definitions

* `SiegelUpperHalfSpace.slashInvariants`: the `Γ`-invariant functions `F : ℋ_g → V`.
* `SiegelUpperHalfSpace.heckeOperator` (LMFDB `mf.siegel.hecke_operator`): the Hecke operator
  `F ↦ ∑ᵢ F ∣_ρ αᵢ` of a double coset `ΓαΓ = ⊔ᵢ Γαᵢ`.
* `SiegelUpperHalfSpace.heckeAlgebraAction`: the action of the Hecke algebra `𝓗(Γ)`.
* `SiegelUpperHalfSpace.IsHeckeEigenform` (LMFDB `mf.siegel.hecke_operator`): Hecke eigenforms.

## Main results

* `SiegelUpperHalfSpace.gspSlash_mul`: the slash operator is a right action of `GSp(2g, ℚ)⁺`.
* `SiegelUpperHalfSpace.mem_modularForms_iff_slashInvariants`: `M_ρ(Sp(2g, ℤ))` consists of the
  holomorphic `Γ`-invariant functions.
* `SiegelUpperHalfSpace.heckeOperator_eq_sum`: the Hecke operator is the sum over any family of
  representatives of the right cosets of the double coset.
* `SiegelUpperHalfSpace.heckeOperator_mem_modularForms`: the Hecke operators preserve `M_ρ(Γ)`
  when the slash operator preserves holomorphy.
* `SiegelUpperHalfSpace.isHeckeEigenform_const`: nonzero constants are Hecke eigenforms of
  trivial weight.
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

/-- The slash operator `f ↦ f ∣_ρ α` of an element `α` of `S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)`, as a
linear map. -/
noncomputable def heckeMonoidSlash (x : heckeMonoid (Fin n)) :
    (SiegelUpperHalfSpace (Fin n) → V) →ₗ[ℂ] SiegelUpperHalfSpace (Fin n) → V where
  toFun f := gspSlash ρ (heckeMonoidToGSpPlus x) f
  map_add' f g := by
    ext τ
    simp [gspSlash]
  map_smul' c f := by
    ext τ
    simp [gspSlash, smul_comm c]

lemma heckeMonoidSlash_mul (x y : heckeMonoid (Fin n)) :
    heckeMonoidSlash ρ (x * y) f = heckeMonoidSlash ρ y (heckeMonoidSlash ρ x f) :=
  gspSlash_mul ρ f (heckeMonoidToGSpPlus x) (heckeMonoidToGSpPlus y)

/-- The space of functions `F : ℋ_g → V` invariant under the slash operator of `Sp(2g, ℤ)`. -/
def slashInvariants : Submodule ℂ (SiegelUpperHalfSpace (Fin n) → V) where
  carrier := {f | ∀ γ (hγ : γ ∈ heckeGamma (Fin n)),
    heckeMonoidSlash ρ ⟨γ, heckeGamma_le_heckeMonoid hγ⟩ f = f}
  add_mem' hf hg γ hγ := by
    rw [map_add, hf γ hγ, hg γ hγ]
  zero_mem' γ hγ :=
    map_zero _
  smul_mem' c f hf γ hγ := by
    rw [map_smul, hf γ hγ]

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

variable {ρ f} in
private lemma heckeMonoidSlash_eq_of_mul_inv_mem (hf : f ∈ slashInvariants ρ)
    {x y : heckeMonoid (Fin n)} (h : (y : GL (Fin n ⊕ Fin n) ℚ) * (x : GL (Fin n ⊕ Fin n) ℚ)⁻¹ ∈
      heckeGamma (Fin n)) :
    heckeMonoidSlash ρ x f = heckeMonoidSlash ρ y f := by
  have hy : y = ⟨_, heckeGamma_le_heckeMonoid h⟩ * x :=
    Subtype.ext <| (inv_mul_cancel_right _ _).symm
  rw [hy, heckeMonoidSlash_mul, hf _ h]

variable (D : HeckeCoset (heckeMonoid (Fin n)) (heckeGamma (Fin n)) (heckeGamma (Fin n)))

attribute [local instance] Fintype.ofFinite

/-- The representative `δ τᵥ⁻¹` of the `v`-th right coset `Γ δ τᵥ⁻¹` of the double coset
`D = Γ δ Γ`, as an element of `S`. -/
noncomputable def heckeRep
    (v : DecompQuotient (heckeGamma (Fin n)) (heckeGamma (Fin n)) (D.out : GL _ ℚ)⁻¹) :
    heckeMonoid (Fin n) :=
  ⟨rightCosetRep D v, rightCosetRep_mem D D.out.2 heckeGamma_le_heckeMonoid v⟩

/-- The **Hecke operator** (LMFDB `mf.siegel.hecke_operator`) of a double coset
`D = ΓαΓ = ⊔ᵢ Γαᵢ` of `Γ = Sp(2g, ℤ)`, `α ∈ S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)`, on the `Γ`-invariant
functions: `F ↦ F ∣_ρ D = ∑ᵢ F ∣_ρ αᵢ`, with the normalised slash operator `gspSlash`. It is
defined with chosen representatives `αᵢ`, but does not depend on them
(`heckeOperator_eq_sum`); its value is again `Γ`-invariant, since right multiplication by `γ ∈ Γ`
permutes the right cosets `Γαᵢ`. -/
noncomputable def heckeOperator : End ℂ (slashInvariants ρ) where
  toFun f := ⟨∑ v, heckeMonoidSlash ρ (heckeRep D v) f, fun γ hγ ↦ by
    rw [map_sum]
    refine Fintype.sum_equiv (toPerm (⟨γ, hγ⟩ : heckeGamma (Fin n))⁻¹) _ _ fun v ↦ ?_
    rw [← heckeMonoidSlash_mul]
    refine heckeMonoidSlash_eq_of_mul_inv_mem f.2 ?_
    rcases exists_mem_out_mul_inv_eq_mul_rightCosetRep D (mul_mem (inv_mem hγ) v.out.2) with
      ⟨γ₁, hγ₁, hsplit⟩
    have hmk : (QuotientGroup.mk ⟨γ⁻¹ * (v.out : GL _ ℚ), mul_mem (inv_mem hγ) v.out.2⟩ :
        DecompQuotient (heckeGamma (Fin n)) (heckeGamma (Fin n)) (D.out : GL _ ℚ)⁻¹) =
          (⟨γ, hγ⟩ : heckeGamma (Fin n))⁻¹ • v :=
      Quotient.mk_smul_out _ (⟨γ, hγ⟩ : heckeGamma (Fin n))⁻¹ v
    have hprod : rightCosetRep D v * γ =
        γ₁ * rightCosetRep D ((⟨γ, hγ⟩ : heckeGamma (Fin n))⁻¹ • v) := by
      simpa only [hmk, mul_inv_rev, inv_inv, ← mul_assoc, rightCosetRep_def] using hsplit
    simpa [heckeRep, hprod, mul_assoc] using inv_mem hγ₁⟩
  map_add' f g := Subtype.ext <| by
    simp [Finset.sum_add_distrib]
  map_smul' c f := Subtype.ext <| by
    simp [Finset.smul_sum]

lemma coe_heckeOperator (F : slashInvariants ρ) :
    (heckeOperator ρ D F : SiegelUpperHalfSpace (Fin n) → V) =
      ∑ v, heckeMonoidSlash ρ (heckeRep D v) F :=
  rfl

/-- **The Hecke operator does not depend on the representatives**: for any family `(aᵢ)` in `S`
whose right cosets `Γaᵢ` are pairwise distinct and cover `D = ΓαΓ`,
`F ∣_ρ D = ∑ᵢ F ∣_ρ aᵢ`. -/
lemma heckeOperator_eq_sum {ι : Type*} [Fintype ι] (a : ι → heckeMonoid (Fin n))
    (hcover : doubleCoset (D.out : GL (Fin n ⊕ Fin n) ℚ)
      (heckeGamma (Fin n) : Set (GL (Fin n ⊕ Fin n) ℚ)) (heckeGamma (Fin n)) =
        ⋃ i, MulOpposite.op (a i : GL (Fin n ⊕ Fin n) ℚ) •
          (heckeGamma (Fin n) : Set (GL (Fin n ⊕ Fin n) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i : GL (Fin n ⊕ Fin n) ℚ) •
      (heckeGamma (Fin n) : Set (GL (Fin n ⊕ Fin n) ℚ)))
    (F : slashInvariants ρ) :
    (heckeOperator ρ D F : SiegelUpperHalfSpace (Fin n) → V) =
      ∑ i, heckeMonoidSlash ρ (a i) F := by
  rcases exists_bijective_rightCosetRep_smul_eq D (fun i ↦ (a i : GL (Fin n ⊕ Fin n) ℚ)) hcover
    hinj with ⟨φ, hφ, h⟩
  exact (Fintype.sum_bijective φ hφ _ _ fun i ↦
    heckeMonoidSlash_eq_of_mul_inv_mem F.2 ((rightCoset_eq_iff _).mp (h i))).symm

/-- **The Hecke operators preserve `M_ρ(Sp(2g, ℤ))`** when the slash operator of `GSp(2g, ℚ)⁺`
preserves holomorphy, as it does for the holomorphic finite-dimensional representations `ρ` of the
LMFDB. -/
lemma heckeOperator_mem_modularForms
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f)) {F : slashInvariants ρ}
    (hF : (F : SiegelUpperHalfSpace (Fin n) → V) ∈
      modularForms ρ (SymplecticGroup.integral (Fin n)) 1) :
    (heckeOperator ρ D F : SiegelUpperHalfSpace (Fin n) → V) ∈
      modularForms ρ (SymplecticGroup.integral (Fin n)) 1 := by
  rw [mem_modularForms_iff_slashInvariants] at hF ⊢
  refine ⟨?_, (heckeOperator ρ D F).2⟩
  rw [coe_heckeOperator]
  exact Finset.sum_induction _ IsHolomorphic (fun _ _ ↦ IsHolomorphic.add) isHolomorphic_zero
    fun v _ ↦ hρ _ _ hF.1

/-- The action of the Hecke algebra `𝓗(Γ)` of `Γ = Sp(2g, ℤ)` on the `Γ`-invariant functions,
the linear extension of `F ↦ F ∣_ρ ΓαΓ`: `F ∣_ρ ∑ⱼ cⱼ Dⱼ = ∑ⱼ cⱼ F ∣_ρ Dⱼ`
(LMFDB `mf.siegel.hecke_operator`). -/
noncomputable def heckeAlgebraAction :
    siegelHeckeRing (Fin n) →ₗ[ℂ] End ℂ (slashInvariants ρ) :=
  Finsupp.linearCombination ℂ (heckeOperator ρ)

lemma heckeAlgebraAction_single (c : ℂ) :
    heckeAlgebraAction ρ (HeckeCosetModule.single ℂ D c) = c • heckeOperator ρ D :=
  Finsupp.linearCombination_single ℂ c D

/-- A **Hecke eigenform** (LMFDB `mf.siegel.hecke_operator`) of weight `ρ` on `Sp(2g, ℤ)`: a
nonzero `F ∈ M_ρ(Sp(2g, ℤ))` (a holomorphic `Γ`-invariant function) which is an eigenvector of
every Hecke operator `F ↦ F ∣_ρ ΓαΓ`, `α ∈ S`; these span the Hecke algebra `𝓗(Γ)`, so `F` is
a simultaneous eigenvector of `𝓗(Γ)`. -/
def IsHeckeEigenform (F : slashInvariants ρ) : Prop :=
  IsHolomorphic (F : SiegelUpperHalfSpace (Fin n) → V) ∧ F ≠ 0 ∧
    ∀ D, ∃ c : ℂ, heckeOperator ρ D F = c • F

/-- **Nonzero constants are Hecke eigenforms of trivial weight**, with eigenvalue `∑ᵢ r(αᵢ) ^ e`
on `ΓαΓ = ⊔ᵢ Γαᵢ`, where `e` is the exponent of the multiplier in the slash operator; so
`IsHeckeEigenform` is not vacuous. -/
lemma isHeckeEigenform_const {v : V} (hv : v ≠ 0) :
    IsHeckeEigenform (Representation.trivial ℂ (GL (Fin n) ℂ) V) ⟨Function.const _ v,
      ((mem_modularForms_iff_slashInvariants _ _).mp (const_mem_modularForms _ v)).2⟩ := by
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
  refine ⟨((mem_modularForms_iff_slashInvariants _ _).mp (const_mem_modularForms _ v)).1,
    fun h ↦ hv <| congrFun (congrArg Subtype.val h) ⟨I • 1, by simp, hτ⟩,
    fun D ↦ ⟨∑ w, (multiplier (heckeMonoidToGSpPlus (heckeRep D w)) : ℂ) ^
      slashExponent (Representation.trivial ℂ (GL (Fin n) ℂ) V), Subtype.ext ?_⟩⟩
  rw [coe_heckeOperator]
  simp only [heckeMonoidSlash, LinearMap.coe_mk, AddHom.coe_mk, h, Finset.sum_smul,
    Submodule.coe_sum, Submodule.coe_smul]

end SiegelUpperHalfSpace
