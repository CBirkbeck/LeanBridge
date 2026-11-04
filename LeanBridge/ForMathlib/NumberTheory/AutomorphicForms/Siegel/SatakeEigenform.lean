import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeTheorem

/-!
# Satake parameters and Euler factors of Siegel eigenforms in every degree

A Hecke eigenform `F` of level `Sp(2g, ℤ)` has an eigencharacter `λ_F` on the local Hecke algebra
`𝓗_p` at every prime `p`, which does not vanish at the scalar `T_0(p²) = Γ (p 1_{2g}) Γ`: its
Hecke operator is the slash operator of `p 1_{2g}`, which fixes every point of the Siegel upper
half-space and is invertible
(`SiegelUpperHalfSpace.IsHeckeEigenform.eigenvalue_elementaryCoset_two_ne_zero`). So by Satake's
theorem (`SiegelUpperHalfSpace.exists_satakeMap_eq_of_ne_zero`) `λ_F` is a Satake map `ω_α`, and
`α` is a Satake parameter of `F`
(`SiegelUpperHalfSpace.IsHeckeEigenform.exists_satakeParameter`): every Siegel eigenform has Satake
parameters at every prime, the statement `SiegelUpperHalfSpace.SatakeParametersExist`
(`SiegelUpperHalfSpace.satakeParametersExist`).

At two Satake parameters `α, β` of one eigenform the Satake maps agree, so the evaluations at `α`
and `β` agree on the image of the universal Satake map, the Weyl-invariant Laurent polynomials of
the cone. The coefficients of the universal spinor Euler factor and those of the universal standard
Euler factor times `t^g`, `t = x₀² ∏_i x_i`, are such polynomials, and `t` is a unit; so the spinor
and the standard Euler factors at `α` and `β` are equal: the statement
`SiegelUpperHalfSpace.EulerFactorsWellDefined` (`SiegelUpperHalfSpace.eulerFactorsWellDefined`).
In particular a Miyawaki lift of type II (`SiegelUpperHalfSpace.IsMiyawakiLiftTypeII`) has the
knowl's standard and spinor Euler factors at every Satake parameter, not only at one.

## Main results

* `SiegelUpperHalfSpace.IsHeckeEigenform.eigenvalue_elementaryCoset_two_ne_zero`: a Hecke
  eigenform has a nonzero eigenvalue at `T_0(p²)`.
* `SiegelUpperHalfSpace.IsHeckeEigenform.exists_satakeParameter`: a Hecke eigenform for `𝓗_p` has
  Satake parameters at `p`.
* `SiegelUpperHalfSpace.SiegelEigenform.exists_satakeParameter`,
  `SiegelUpperHalfSpace.satakeParametersExist`: every Siegel eigenform has Satake parameters at
  every prime.
* `SiegelUpperHalfSpace.spinorEulerFactor_eq_of_satakeMap_eq`,
  `SiegelUpperHalfSpace.standardEulerFactor_eq_of_satakeMap_eq`: the Euler factors are functions of
  the Satake map.
* `SiegelUpperHalfSpace.SiegelEigenform.isEulerFactor_unique`,
  `SiegelUpperHalfSpace.eulerFactorsWellDefined`: the Euler factors of a Siegel eigenform are well
  defined.
* `SiegelUpperHalfSpace.IsMiyawakiLiftTypeII.standardEulerFactor_eq`,
  `SiegelUpperHalfSpace.IsMiyawakiLiftTypeII.spinorEulerFactor_eq`: the Euler factors of a
  Miyawaki lift of type II at every Satake parameter.
-/

open DoubleCoset Module MonoidAlgebra Polynomial

open HeckeCosetModule (single)

open scoped Pointwise

namespace SiegelUpperHalfSpace

variable {n : ℕ} (p : ℕ)

attribute [local instance] Fintype.ofFinite

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) ℂ) V}

/-! ### Slash operators of scalars -/

lemma eq_zero_of_gspSlash_eq_zero_of_smul_eq {β : gspPlus (Fin n)} (hβ : ∀ τ, gspSmul β τ = τ)
    {f : SiegelUpperHalfSpace (Fin n) → V} (h : gspSlash ρ β f = 0) : f = 0 := by
  funext τ
  have h' : ((multiplier β : ℂ) ^ slashExponent ρ) • ρ (gspDenomGL β τ)⁻¹ (f (gspSmul β τ)) = 0 :=
    congrFun h τ
  rw [hβ] at h'
  rcases smul_eq_zero.mp h' with h₁ | h₁
  · exact absurd h₁ (zpow_ne_zero _ (Rat.cast_ne_zero.mpr (multiplier_pos β).ne'))
  · have h₂ : ρ (gspDenomGL β τ) (ρ (gspDenomGL β τ)⁻¹ (f τ)) = f τ := by
      rw [← End.mul_apply, ← map_mul, mul_inv_cancel, map_one, End.one_apply]
    rw [← h₂, h₁, map_zero, Pi.zero_apply]

variable [Fact p.Prime] in
lemma gspSmul_elementaryDiag_two (τ : SiegelUpperHalfSpace (Fin n)) :
    gspSmul (submonoidToGSpPlus (elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun)) τ = τ := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hden : gspDenom (submonoidToGSpPlus (elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun)) τ =
      (p : ℂ) • 1 := by
    ext i j
    simp [gspDenom, submonoidToGSpPlus, coe_elementaryDiag_two, Matrix.toBlocks₂₁,
      Matrix.toBlocks₂₂, Matrix.one_apply, Matrix.mul_apply, apply_ite (Rat.cast : ℚ → ℂ)]
  have hnum : gspNum (submonoidToGSpPlus (elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun)) τ =
      (p : ℂ) • τ.val := by
    ext i j
    simp [gspNum, submonoidToGSpPlus, coe_elementaryDiag_two, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.mul_apply, Matrix.one_apply, apply_ite (Rat.cast : ℚ → ℂ)]
  have hinv : ((p : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ = (p : ℂ)⁻¹ • 1 :=
    Matrix.inv_eq_left_inv <| by
      rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ hp, one_smul]
  refine SiegelUpperHalfSpace.ext ?_
  rw [gspSmul_val, hden, hnum, hinv, smul_mul_smul_comm, Matrix.mul_one, mul_inv_cancel₀ hp,
    one_smul]

variable [NeZero n]

/-! ### Local and global Hecke operators -/

lemma heckeOperator_heckeMonoidAt_eq {F : SiegelUpperHalfSpace (Fin n) → V}
    (hF : F ∈ slashInvariants ρ)
    (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n))) :
    (heckeOperator ρ D ⟨F, fun γ hγ ↦ hF γ hγ⟩ : SiegelUpperHalfSpace (Fin n) → V) =
      heckeOperator ρ (HeckeCoset.mk (heckeGamma (Fin n)) (heckeGamma (Fin n))
        ⟨(D.out : GL (Fin n ⊕ Fin n) ℚ), heckeMonoidAt_le_heckeMonoid p D.out.2⟩) ⟨F, hF⟩ := by
  have hmem : ((HeckeCoset.mk (heckeGamma (Fin n)) (heckeGamma (Fin n))
      (⟨(D.out : GL (Fin n ⊕ Fin n) ℚ), heckeMonoidAt_le_heckeMonoid p D.out.2⟩ :
        heckeMonoid (Fin n))).rep : GL (Fin n ⊕ Fin n) ℚ) ∈
          doubleCoset (D.out : GL (Fin n ⊕ Fin n) ℚ) (heckeGamma (Fin n) : Set _)
            (heckeGamma (Fin n)) :=
    HeckeCoset.rep_mk_mem_doubleCoset (⟨(D.out : GL (Fin n ⊕ Fin n) ℚ),
      heckeMonoidAt_le_heckeMonoid p D.out.2⟩ : heckeMonoid (Fin n))
  rw [heckeOperator_eq_sum ρ _ (fun v ↦ (⟨rightCosetRep D v,
    heckeMonoidAt_le_heckeMonoid p (heckeRep D v).2⟩ : heckeMonoid (Fin n)))
    ((doubleCoset_eq_of_mem hmem).trans (doubleCoset_eq_iUnion_rightCosetRep D))
    (op_rightCosetRep_smul_injective D) ⟨F, hF⟩]
  rfl

/-! ### The Hecke operator `T_0(p²)` -/

variable [Fact p.Prime]

lemma heckeOperator_elementaryCoset_two
    (F : slashInvariantsOf ρ (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n))) :
    (heckeOperator ρ (elementaryCoset p 2 (fun _ ↦ 1) one_le_two_fun) F :
      SiegelUpperHalfSpace (Fin n) → V) =
        heckeMonoidSlash ρ (elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun) F := by
  have hcover : doubleCoset ((elementaryCoset (n := n) p 2 (fun _ ↦ 1) one_le_two_fun).rep :
      GL (Fin n ⊕ Fin n) ℚ) (heckeGamma (Fin n) : Set (GL (Fin n ⊕ Fin n) ℚ)) (heckeGamma (Fin n)) =
        ⋃ _ : Unit, MulOpposite.op ((elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun :
          heckeMonoidAt (Fin n) p) : GL (Fin n ⊕ Fin n) ℚ) •
            (heckeGamma (Fin n) : Set (GL (Fin n ⊕ Fin n) ℚ)) := by
    have hm : ((elementaryCoset (n := n) p 2 (fun _ ↦ 1) one_le_two_fun).rep :
        GL (Fin n ⊕ Fin n) ℚ) ∈ doubleCoset ((elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun :
          heckeMonoidAt (Fin n) p) : GL (Fin n ⊕ Fin n) ℚ) (heckeGamma (Fin n) : Set _)
            (heckeGamma (Fin n)) :=
      HeckeCoset.rep_mk_mem_doubleCoset _
    rw [Set.iUnion_const, doubleCoset_eq_of_mem hm]
    ext x
    rw [mem_rightCoset_iff]
    constructor
    · intro hx
      rcases mem_doubleCoset.mp hx with ⟨γ, hγ, γ', hγ', rfl⟩
      rw [mul_assoc γ, elementaryDiag_two_mul_comm p γ', ← mul_assoc, mul_inv_cancel_right]
      exact mul_mem hγ hγ'
    · intro hx
      exact mem_doubleCoset.mpr ⟨x * ((elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun :
        heckeMonoidAt (Fin n) p) : GL (Fin n ⊕ Fin n) ℚ)⁻¹, hx, 1, one_mem _, by group⟩
  rw [heckeOperator_eq_sum ρ _ (fun _ : Unit ↦ elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun)
    hcover (Function.injective_of_subsingleton _) F, Fintype.sum_unique]

/-- **A Hecke eigenform does not vanish under `T_0(p²)`** (LMFDB `mf.siegel.lift`, through the
Satake parameters): its eigenvalue at `T_0(p²) = Γ (p 1_{2g}) Γ` is nonzero, the Hecke operator
being the invertible slash operator of the scalar `p 1_{2g}`. -/
lemma IsHeckeEigenform.eigenvalue_elementaryCoset_two_ne_zero
    {F : slashInvariantsOf ρ (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n))}
    (hF : IsHeckeEigenform ρ F) :
    hF.eigenvalue (elementaryCoset p 2 (fun _ ↦ 1) one_le_two_fun) ≠ 0 := by
  intro h
  have h₁ : heckeMonoidSlash ρ (elementaryDiag p 2 (fun _ ↦ 1) one_le_two_fun)
      (F : SiegelUpperHalfSpace (Fin n) → V) = 0 := by
    rw [← heckeOperator_elementaryCoset_two p F, hF.heckeOperator_eq, h, zero_smul,
      Submodule.coe_zero]
  exact hF.2.1 (Subtype.ext
    (eq_zero_of_gspSlash_eq_zero_of_smul_eq (gspSmul_elementaryDiag_two p) h₁))

/-! ### Existence of Satake parameters -/

/-- **Satake parameters exist** (LMFDB `mf.siegel.lift`): a Hecke eigenform for the local Hecke
algebra `𝓗_p` of `Sp(2g, ℤ)` has Satake parameters at `p`. -/
lemma IsHeckeEigenform.exists_satakeParameter
    {F : slashInvariantsOf ρ (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n))}
    (hF : IsHeckeEigenform ρ F) : ∃ (α₀ : ℂˣ) (α : Fin n → ℂˣ),
      IsSatakeParameter p ρ (F : SiegelUpperHalfSpace (Fin n) → V) α₀ α := by
  rcases exists_satakeMap_eq_of_ne_zero p (f := hF.eigencharacter)
    (fun D c ↦ by rw [hF.eigencharacter_single, hF.eigencharacter_single, one_mul])
    (by rw [hF.eigencharacter_single, one_mul]; exact hF.eigenvalue_elementaryCoset_two_ne_zero p)
    with ⟨α₀, α, h⟩
  exact ⟨α₀, α, (isSatakeParameter_iff p ρ hF).mpr h.symm⟩

/-- **Satake parameters exist for the Siegel eigenforms** (LMFDB `mf.siegel.lift`): a Siegel
eigenform has Satake parameters at every prime. -/
lemma SiegelEigenform.exists_satakeParameter (G : SiegelEigenform) :
    ∃ α₀ α, IsSatakeParameter p G.ρ (G.form : SiegelUpperHalfSpace (Fin G.degree) → G.V) α₀ α := by
  have hG : IsHeckeEigenform G.ρ (⟨G.form, fun γ hγ ↦ G.form.2 γ hγ⟩ :
      slashInvariantsOf G.ρ (heckeMonoidAt (Fin G.degree) p) (heckeGamma (Fin G.degree))) :=
    ⟨G.isHeckeEigenform.1, fun h ↦ G.isHeckeEigenform.2.1 (Subtype.ext (congrArg Subtype.val h)),
      fun D ↦ ⟨G.isHeckeEigenform.eigenvalue _, Subtype.ext
        ((heckeOperator_heckeMonoidAt_eq p G.form.2 D).trans
          (congrArg Subtype.val (G.isHeckeEigenform.heckeOperator_eq _)))⟩⟩
  exact hG.exists_satakeParameter p

/-- **Satake parameters exist in every degree** (LMFDB `mf.siegel.lift`): the statement
`SiegelUpperHalfSpace.SatakeParametersExist`, by Satake's theorem. -/
lemma satakeParametersExist : SatakeParametersExist :=
  fun G q _ ↦ G.exists_satakeParameter q

/-! ### Uniqueness of the Euler factors -/

lemma IsSatakeParameter.satakeMap_eq_satakeMap {f : SiegelUpperHalfSpace (Fin n) → V} {α₀ β₀ : ℂˣ}
    {α β : Fin n → ℂˣ} (hα : IsSatakeParameter p ρ f α₀ α) (hβ : IsSatakeParameter p ρ f β₀ β) :
    satakeMap p α₀ α = satakeMap p β₀ β := by
  rcases hα with ⟨_, hf₀, hα⟩
  rcases hβ with ⟨_, -, hβ⟩
  have e (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n))) :
      satakeMap p α₀ α (single ℂ D 1) = satakeMap p β₀ β (single ℂ D 1) :=
    smul_left_injective ℂ hf₀ ((hα D).symm.trans (hβ D))
  refine RingHom.ext fun T ↦ ?_
  induction T using HeckeCosetModule.induction_linear with
  | h0 => rw [map_zero, map_zero]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  | hsingle D c =>
    rw [← HeckeCosetModule.smul_single_one ℂ D c, map_smul_of_map_single p
      (fun D c ↦ by rw [satakeMap_single, satakeMap_single, one_smul, smul_eq_mul]),
      map_smul_of_map_single p (fun D c ↦ by rw [satakeMap_single, satakeMap_single, one_smul,
        smul_eq_mul]), e]

variable {p} {α₀ β₀ : ℂˣ} {α β : Fin n → ℂˣ}

lemma satakeEval_eq_of_satakeMap_eq (h : satakeMap p α₀ α = satakeMap p β₀ β) {f : SatakeLaurent n}
    (hf : f ∈ weylInvariants n) (hc : f ∈ coneAlgebra n) :
    satakeEval α₀ α f = satakeEval β₀ β f := by
  rcases (exists_satakeMapUniv_eq_iff p).mpr ⟨hf, hc⟩ with ⟨T, rfl⟩
  rw [satakeEval_satakeMapUniv, satakeEval_satakeMapUniv, h]

/-- **The spinor Euler factor is a function of the Satake map** (LMFDB `mf.siegel.lift`): the
coefficients of the universal spinor Euler factor are in the image of the universal Satake map. -/
lemma spinorEulerFactor_eq_of_satakeMap_eq (h : satakeMap p α₀ α = satakeMap p β₀ β) :
    spinorEulerFactor (α₀ : ℂ) (fun i ↦ (α i : ℂ)) =
      spinorEulerFactor (β₀ : ℂ) fun i ↦ (β i : ℂ) := by
  rw [← map_satakeEval_spinorPolyUniv, ← map_satakeEval_spinorPolyUniv]
  ext k
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  exact satakeEval_eq_of_satakeMap_eq h (coeff_spinorPolyUniv_mem_weylInvariants k)
    (coeff_spinorPolyUniv_mem_coneAlgebra k)

/-- **The standard Euler factor is a function of the Satake map** (LMFDB `mf.siegel.lift`): the
coefficients of the universal standard Euler factor times `t^g`, `t = x₀² ∏_i x_i`, are in the image
of the universal Satake map, and `t` is a unit. -/
lemma standardEulerFactor_eq_of_satakeMap_eq (h : satakeMap p α₀ α = satakeMap p β₀ β) :
    standardEulerFactor (fun i ↦ (α i : ℂ)) = standardEulerFactor fun i ↦ (β i : ℂ) := by
  have ht :
      satakeEval α₀ α (single (scalarWeight n) 1) = satakeEval β₀ β (single (scalarWeight n) 1) :=
    satakeEval_eq_of_satakeMap_eq h single_scalarWeight_mem_weylInvariants
      (single_mem_coneAlgebra scalarWeight_mem_satakeCone 1)
  have hP : (C (single (scalarWeight n) 1 ^ n) * standardPolyUniv n).map
      (satakeEval α₀ α : SatakeLaurent n →+* ℂ) =
        (C (single (scalarWeight n) 1 ^ n) * standardPolyUniv n).map
          (satakeEval β₀ β : SatakeLaurent n →+* ℂ) := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact satakeEval_eq_of_satakeMap_eq h (coeff_C_pow_mul_standardPolyUniv_mem_weylInvariants k)
      (coeff_mem_coneAlgebra C_pow_mul_standardPolyUniv_mem_liftsRing k)
  simp only [Polynomial.map_mul, map_C, RingHom.coe_coe, map_pow,
    map_satakeEval_standardPolyUniv, Polynomial.map_pow] at hP
  rw [← ht] at hP
  refine mul_left_cancel₀ (pow_ne_zero _ (C_ne_zero.mpr ?_)) hP
  rw [satakeEval_single, one_mul]
  exact Units.ne_zero _

/-- **The Euler factors of a Siegel eigenform are unique** (LMFDB `mf.siegel.lift`): two Euler
factors of one kind of a Siegel eigenform at `p` are equal. -/
lemma SiegelEigenform.isEulerFactor_unique (G : SiegelEigenform) (t : EulerFactorKind) {Q Q' : ℂ[X]}
    (hQ : G.IsEulerFactor t p Q) (hQ' : G.IsEulerFactor t p Q') : Q = Q' := by
  rcases hQ with ⟨β₀, β, hβ, rfl⟩
  rcases hQ' with ⟨γ₀, γ, hγ, rfl⟩
  have h : satakeMap p β₀ β = satakeMap p γ₀ γ := hβ.satakeMap_eq_satakeMap p hγ
  rcases t with - | -
  · exact spinorEulerFactor_eq_of_satakeMap_eq h
  · exact standardEulerFactor_eq_of_satakeMap_eq h

/-- **The Euler factors of a Siegel eigenform are well defined in every degree** (LMFDB
`mf.siegel.lift`): the statement `SiegelUpperHalfSpace.EulerFactorsWellDefined`. -/
lemma eulerFactorsWellDefined : EulerFactorsWellDefined :=
  fun G t _ _ _ _ hQ hQ' ↦ G.isEulerFactor_unique t hQ hQ'

/-! ### The Euler factors of a Miyawaki lift of type II -/

section Miyawaki

open HeckeRing GL2

variable {k : ℤ} {f : Newform 1 (2 * k - 2)} {g : Newform 1 (k - 2)}
    {F : SiegelUpperHalfSpace (Fin 3) → ℂ} {γ₀ : ℂˣ} {γ : Fin 3 → ℂˣ}

/-- **The standard Euler factor of a Miyawaki lift of type II** (LMFDB
`mf.siegel.lift.miyawaki2`): at every Satake parameter of `F` at `p`, the standard Euler factor is
`Q_p(f, p^{1-k} X) Q_p(f, p^{2-k} X) Q_p^st(g, X)`. -/
lemma IsMiyawakiLiftTypeII.standardEulerFactor_eq (hF : IsMiyawakiLiftTypeII f g F)
    (hγ : IsSatakeParameter p (TauCeti.detPowerRep ℂ 3 k) F γ₀ γ) :
    standardEulerFactor (fun i ↦ (γ i : ℂ)) = f.miyawaki2StandardEulerFactor g p := by
  rcases hF.2.2.2 p with ⟨α₀, α, hα, h, -⟩
  exact (standardEulerFactor_eq_of_satakeMap_eq (hα.satakeMap_eq_satakeMap p hγ)).symm.trans h

/-- **The spinor Euler factor of a Miyawaki lift of type II** (LMFDB `mf.siegel.lift.miyawaki2`):
at every Satake parameter of `F` at `p`, the spinor Euler factor is
`Q_p(g, p^{k-1} X) Q_p(g, p^{k-2} X) Q_p(f ⊗ g, X)`. -/
lemma IsMiyawakiLiftTypeII.spinorEulerFactor_eq (hF : IsMiyawakiLiftTypeII f g F)
    (hγ : IsSatakeParameter p (TauCeti.detPowerRep ℂ 3 k) F γ₀ γ) :
    spinorEulerFactor (γ₀ : ℂ) (fun i ↦ (γ i : ℂ)) = f.miyawaki2SpinorEulerFactor g p := by
  rcases hF.2.2.2 p with ⟨α₀, α, hα, -, h⟩
  exact (spinorEulerFactor_eq_of_satakeMap_eq (hα.satakeMap_eq_satakeMap p hγ)).symm.trans h

end Miyawaki

end SiegelUpperHalfSpace
