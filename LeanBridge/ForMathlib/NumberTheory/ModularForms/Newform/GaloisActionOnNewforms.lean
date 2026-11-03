import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NewformSubspace
import TauCeti.NumberTheory.MulChar.GaloisOrbit

/-!
# The action of the automorphisms of `ℂ` on newforms and cusp forms

The Galois conjugate of a newform is a newform (`HeckeRing.GL2.Newform.exists_isGaloisConjugateBy`),
so the group of automorphisms of `ℂ` acts on the newforms of a given level and weight, through the
coefficients of their `q`-expansions (LMFDB `cmf.newspaces`). The orbits are the Galois orbits.

The same automorphisms act semilinearly on `S_k(Γ₁(N))`, so that they map `S_k^{new}(N, χ)` onto
`S_k^{new}(N, σ ∘ χ)`, which are then Galois conjugate (LMFDB `cmf.decomposition.new.gamma1`).

## Main definitions

* The instance `MulAction Gal(ℂ/ℚ) (Newform N k)`: the action on newforms (LMFDB `cmf.newspaces`).
* The instance `MulAction Gal(algebraicClosure ℚ ℂ/ℚ) (Newform N k)`: the action of the absolute
  Galois group of `ℚ` on newforms (LMFDB `cmf.newspaces`).
* `HeckeRing.GL2.Newform.extendAut`: an automorphism of `ℂ` extending an automorphism of the field
  of algebraic numbers.
* `TauCeti.GaloisAction.conjCusp`: the semilinear action on `S_k(Γ₁(N))`.

## Main results

* `HeckeRing.GL2.Newform.orbit_eq_galoisOrbit`: the orbits of the action are the Galois orbits.
* `HeckeRing.GL2.Newform.coeff_smul_algebraicClosure`,
  `HeckeRing.GL2.Newform.orbit_algebraicClosure_eq_galoisOrbit`: the absolute Galois group of `ℚ`
  acts on the coefficients of the `q`-expansions, with the Galois orbits as orbits.
* `HeckeRing.GL2.Newform.exists_isEmbedding`: each embedding of the coefficient field of `f` gives a
  newform `ι(f)` (LMFDB `cmf.embedding`).
* `TauCeti.GaloisAction.conjCusp_mem_cuspFormsNew_inf_cuspFormCharSpace_iff`: the conjugation by `σ`
  maps `S_k^{new}(N, χ)` onto `S_k^{new}(N, σ ∘ χ)` (LMFDB `cmf.decomposition.new.gamma1`).
* `HeckeRing.GL2.Newform.exists_conjCusp_mem_iff_of_mem_galoisOrbit`: the spaces of newforms of two
  characters in the same Galois orbit are Galois conjugate (LMFDB `cmf.decomposition.new.gamma1`).
* `HeckeRing.GL2.Newform.image_smul_setOf_χ_eq`,
  `HeckeRing.GL2.Newform.finrank_cuspFormsNew_inf_cuspFormCharSpace_comp`: then `σ` maps the
  newforms of nebentypus `χ` onto those of nebentypus `σ ∘ χ`, and the two spaces have the same
  dimension (LMFDB `cmf.decomposition.new.gamma1`).
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Module GaloisAction Matrix SpecialLinearGroup Algebra

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k} (σ : Gal(ℂ/ℚ))

@[nolint defsWithUnderscore]
noncomputable instance : MulAction Gal(ℂ/ℚ) (Newform N k) where
  smul σ f := (exists_isGaloisConjugateBy f σ).choose
  one_smul f := (exists_isGaloisConjugateBy f 1).choose_spec.unique f.isGaloisConjugateBy_one
  mul_smul σ τ f := (exists_isGaloisConjugateBy f (σ * τ)).choose_spec.unique <|
    (exists_isGaloisConjugateBy f τ).choose_spec.trans (exists_isGaloisConjugateBy _ σ).choose_spec

variable (f) in
lemma isGaloisConjugateBy_smul : f.IsGaloisConjugateBy σ (σ • f) :=
  (exists_isGaloisConjugateBy f σ).choose_spec

lemma smul_eq_iff : σ • f = g ↔ f.IsGaloisConjugateBy σ g :=
  ⟨fun h ↦ h ▸ f.isGaloisConjugateBy_smul σ, (f.isGaloisConjugateBy_smul σ).unique⟩

variable (f) in
lemma coeff_smul (n : ℕ) :
    (qExpansion 1 (σ • f).toCuspForm).coeff n = σ ((qExpansion 1 f.toCuspForm).coeff n) :=
  (f.isGaloisConjugateBy_smul σ).coeff n

variable (f) in
/-- **The orbits of the action of the automorphisms of `ℂ` on newforms are the Galois orbits.** -/
lemma orbit_eq_galoisOrbit : MulAction.orbit Gal(ℂ/ℚ) f = f.galoisOrbit :=
  Set.ext fun _ ↦ exists_congr fun _ ↦ smul_eq_iff _

/-- **Each embedding of the coefficient field gives a newform** (LMFDB `cmf.embedding`): for every
embedding `ι : ℚ(f) → ℂ`, the series `∑ ι(aₙ) qⁿ` is the `q`-expansion of a newform of the level and
weight of `f`. -/
lemma exists_isEmbedding (ι : CoefficientField f →ₐ[ℚ] ℂ) : ∃ g : Newform N k, f.IsEmbedding g ι :=
  (f.galoisOrbitEmbedding_surjective ι).elim fun x hx ↦ ⟨x, hx ▸ isEmbedding_galoisOrbitEmbedding x⟩

end HeckeRing.GL2.Newform

namespace TauCeti.GaloisAction

open HeckeRing GL2

variable (σ τ : Gal(ℂ/ℚ)) {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- The **conjugation by an automorphism `σ` of `ℂ`** on `S_k(Γ₁(N))`: it applies `σ` to the
coefficients of the `q`-expansion of a cusp form. It is semilinear, by `conjCusp_smul`. -/
noncomputable def conjCusp :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k ≃+ CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  haveI hspec (s : Gal(ℂ/ℚ)) (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
      ∃ F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        qExpansion 1 F = PowerSeries.map (s : ℂ →+* ℂ) (qExpansion 1 x) ∧ ∀ d : (ZMod N)ˣ,
          qExpansion 1 (diamondOpCusp k d F) =
            PowerSeries.map (s : ℂ →+* ℂ) (qExpansion 1 (diamondOpCusp k d x)) :=
    exists_cuspForm_Gamma1_qExpansion_eq_map (s : ℂ →+* ℂ) x
  { toFun x := (hspec σ x).choose
    invFun x := (hspec σ⁻¹ x).choose
    left_inv x := CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N) <| by
      beta_reduce
      rw [(hspec σ⁻¹ _).choose_spec.1, (hspec σ x).choose_spec.1]
      ext n
      simp
    right_inv x := CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N) <| by
      beta_reduce
      rw [(hspec σ _).choose_spec.1, (hspec σ⁻¹ x).choose_spec.1]
      ext n
      simp
    map_add' x y := CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N) <| by
      beta_reduce
      rw [(hspec σ _).choose_spec.1, FunLike.coe_add, FunLike.coe_add,
        ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map N),
        ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map N),
        (hspec σ x).choose_spec.1, (hspec σ y).choose_spec.1, map_add] }

variable {x y : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}

variable (x) in
lemma qExpansion_conjCusp :
    qExpansion 1 (conjCusp σ x) = PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion 1 x) :=
  (exists_cuspForm_Gamma1_qExpansion_eq_map (σ : ℂ →+* ℂ) x).choose_spec.1

variable (x) in
lemma qExpansion_diamondOpCusp_conjCusp (d : (ZMod N)ˣ) : qExpansion 1
    (diamondOpCusp k d (conjCusp σ x)) =
      PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion 1 (diamondOpCusp k d x)) :=
  (exists_cuspForm_Gamma1_qExpansion_eq_map (σ : ℂ →+* ℂ) x).choose_spec.2 d

lemma conjCusp_eq_iff :
    conjCusp σ x = y ↔ qExpansion 1 y = PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion 1 x) :=
  ⟨fun h ↦ h ▸ qExpansion_conjCusp σ x, fun h ↦
    CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N) <|
      (qExpansion_conjCusp σ x).trans h.symm⟩

variable (x) in
lemma conjCusp_smul (c : ℂ) : conjCusp σ (c • x) = σ c • conjCusp σ x := by
  refine (conjCusp_eq_iff σ).mpr ?_
  rw [FunLike.coe_smul, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
    (one_mem_strictPeriods_Gamma1_map N), ModularForm.qExpansion_smul one_pos
    (one_mem_strictPeriods_Gamma1_map N), qExpansion_conjCusp, map_smul_powerSeries]
  rfl

variable (x) in
lemma conjCusp_mul_apply : conjCusp (σ * τ) x = conjCusp σ (conjCusp τ x) := by
  refine (conjCusp_eq_iff (σ * τ)).mpr ?_
  rw [qExpansion_conjCusp, qExpansion_conjCusp]
  ext n
  simp

lemma conjCusp_toCuspForm (f : Newform N k) : conjCusp σ f.toCuspForm = (σ • f).toCuspForm :=
  (conjCusp_eq_iff σ).mpr (f.isGaloisConjugateBy_smul σ)

lemma conjCusp_mem_cuspFormsNew (hx : x ∈ cuspFormsNew N k) : conjCusp σ x ∈ cuspFormsNew N k := by
  rw [← Newform.span_range_toCuspForm_eq_cuspFormsNew] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨f, rfl⟩
    exact Submodule.subset_span ⟨σ • f, (conjCusp_toCuspForm σ f).symm⟩
  | zero => simp
  | add x y _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | smul c x _ ihx =>
    rw [conjCusp_smul]
    exact Submodule.smul_mem _ _ ihx

lemma conjCusp_mem_cuspFormCharSpace (hx : x ∈ cuspFormCharSpace k χ) :
    conjCusp σ x ∈ cuspFormCharSpace k ((Units.map (σ : ℂ →* ℂ)).comp χ) :=
  mem_cuspFormCharSpace_of_qExpansion_diamond_eq_map (σ : ℂ →+* ℂ) hx (qExpansion_conjCusp σ x)
    (qExpansion_diamondOpCusp_conjCusp σ x)

/-- **The spaces of newforms of `χ` and `σ ∘ χ` are Galois conjugate**
(LMFDB `cmf.decomposition.new.gamma1`): the conjugation by an automorphism `σ` of `ℂ` maps
`S_k^{new}(N, χ)` onto `S_k^{new}(N, σ ∘ χ)`. -/
lemma conjCusp_mem_cuspFormsNew_inf_cuspFormCharSpace_iff : conjCusp σ x ∈
    cuspFormsNew N k ⊓ cuspFormCharSpace k ((Units.map (σ : ℂ →* ℂ)).comp χ) ↔
      x ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k χ := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ⟨conjCusp_mem_cuspFormsNew σ hx.1,
    conjCusp_mem_cuspFormCharSpace σ hx.2⟩⟩
  have hinv : conjCusp σ⁻¹ (conjCusp σ x) = x := by
    rw [← conjCusp_mul_apply, inv_mul_cancel]
    exact (conjCusp_eq_iff 1).mpr <| by
      ext n
      simp
  have hχ : (Units.map ((σ⁻¹ : Gal(ℂ/ℚ)) : ℂ →* ℂ)).comp
      ((Units.map (σ : ℂ →* ℂ)).comp χ) = χ := by
    ext u
    simp
  exact ⟨hinv ▸ conjCusp_mem_cuspFormsNew σ⁻¹ hx.1,
    hinv ▸ hχ ▸ conjCusp_mem_cuspFormCharSpace σ⁻¹ hx.2⟩

end TauCeti.GaloisAction

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (σ : Gal(ℂ/ℚ)) {f : Newform N k} (χ : (ZMod N)ˣ →* ℂˣ)

/-- **The spaces of newforms of two characters in the same Galois orbit are Galois conjugate**
(LMFDB `cmf.decomposition.new.gamma1`): an automorphism of `ℂ` maps one onto the other. -/
lemma exists_conjCusp_mem_iff_of_mem_galoisOrbit {ψ ψ' : DirichletCharacter ℂ N}
    (h : ψ' ∈ ψ.galoisOrbit) : ∃ σ : Gal(ℂ/ℚ), ∀ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      conjCusp σ x ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k ψ'.toUnitHom ↔
        x ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k ψ.toUnitHom := by
  rcases MulChar.mem_galoisOrbit_iff_exists_algHom.mp h with ⟨ι, hι⟩
  have hc : Countable (IntermediateField.adjoin ℚ (Set.range ψ)) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (IntermediateField.cardinalMk_adjoin_le ℚ _).trans <|
      sup_le (sup_le Cardinal.mk_le_aleph0 (Set.finite_range ψ).countable.le_aleph0) le_rfl
  rcases IntermediateField.exists_algEquiv_apply_eq_of_countable ι with ⟨σ, hσ⟩
  refine ⟨σ, fun x ↦ ?_⟩
  have hχ : ψ'.toUnitHom = (Units.map (σ : ℂ →* ℂ)).comp ψ.toUnitHom := by
    ext u
    simp only [MonoidHom.comp_apply]
    exact (hι u).trans (hσ _).symm
  rw [hχ]
  exact conjCusp_mem_cuspFormsNew_inf_cuspFormCharSpace_iff σ

/-- **The conjugation by `σ` maps the newforms of nebentypus `χ` onto those of nebentypus
`σ ∘ χ`** (LMFDB `cmf.decomposition.new.gamma1`). -/
lemma image_smul_setOf_χ_eq :
    (σ • ·) '' {f : Newform N k | f.χ = χ} = {g | g.χ = (Units.map (σ : ℂ →* ℂ)).comp χ} := by
  refine Set.ext fun g ↦ ⟨?_, fun hg ↦ ⟨σ⁻¹ • g, ?_, smul_inv_smul σ g⟩⟩
  · rintro ⟨f, hf, rfl⟩
    exact (f.isGaloisConjugateBy_smul σ).χ_eq.trans (congrArg (Units.map (σ : ℂ →* ℂ)).comp hf)
  · refine (g.isGaloisConjugateBy_smul σ⁻¹).χ_eq.trans ?_
    rw [Set.mem_ofPred_eq.mp hg]
    ext u
    simp

/-- **Galois conjugate characters have spaces of newforms of the same dimension**
(LMFDB `cmf.decomposition.new.gamma1`). -/
lemma finrank_cuspFormsNew_inf_cuspFormCharSpace_comp : finrank ℂ
    ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k ((Units.map (σ : ℂ →* ℂ)).comp χ)) =
      finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) := by
  rw [← span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace,
    ← span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace, finrank_span_image_toCuspForm,
    finrank_span_image_toCuspForm, ← image_smul_setOf_χ_eq σ χ,
    Set.ncard_image_of_injective _ (MulAction.injective σ)]

variable (f) in
lemma qExpansion_coeff_mem_algebraicClosure (n : ℕ) :
    (qExpansion 1 f.toCuspForm).coeff n ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.mpr <|
    (isAlgebraic_algHom_iff (CoefficientField f).val Subtype.val_injective).mpr <|
      IsAlgebraic.isAlgebraic (⟨_, f.qExpansion_coeff_mem_coefficientField n⟩ : CoefficientField f)

instance : Countable (algebraicClosure ℚ ℂ) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ)).trans <|
    sup_le Cardinal.mk_le_aleph0 le_rfl

/-- An automorphism of `ℂ` extending an automorphism of the field of algebraic numbers. -/
noncomputable def extendAut (τ : Gal(algebraicClosure ℚ ℂ/ℚ)) : Gal(ℂ/ℚ) :=
  (IntermediateField.exists_algEquiv_apply_eq_of_countable
    ((algebraicClosure ℚ ℂ).val.comp τ.toAlgHom)).choose

lemma extendAut_apply (τ : Gal(algebraicClosure ℚ ℂ/ℚ)) (x : algebraicClosure ℚ ℂ) :
    extendAut τ x = τ x :=
  (IntermediateField.exists_algEquiv_apply_eq_of_countable
    ((algebraicClosure ℚ ℂ).val.comp τ.toAlgHom)).choose_spec x

@[nolint defsWithUnderscore]
noncomputable instance : MulAction Gal(algebraicClosure ℚ ℂ/ℚ) (Newform N k) where
  smul τ f := extendAut τ • f
  one_smul f := by
    refine Newform.ext <| CuspForm.qExpansion_injective one_pos
      (one_mem_strictPeriods_Gamma1_map N) <| PowerSeries.ext fun n ↦ ?_
    exact (coeff_smul f _ n).trans
      (extendAut_apply 1 ⟨_, f.qExpansion_coeff_mem_algebraicClosure n⟩)
  mul_smul τ τ' f := by
    refine Newform.ext <| CuspForm.qExpansion_injective one_pos
      (one_mem_strictPeriods_Gamma1_map N) <| PowerSeries.ext fun n ↦ ?_
    refine (coeff_smul f _ n).trans <| Eq.symm <| (coeff_smul _ _ n).trans ?_
    exact (congrArg _ ((coeff_smul f _ n).trans (extendAut_apply τ'
      ⟨_, f.qExpansion_coeff_mem_algebraicClosure n⟩))).trans <|
        (extendAut_apply τ _).trans (extendAut_apply (τ * τ') _).symm

variable (f) in
/-- **The absolute Galois group of `ℚ` acts on newforms through the coefficients of their
`q`-expansions** (LMFDB `cmf.newspaces`): the coefficients of `τ • f` are the images by `τ` of those
of `f`, which are algebraic numbers. -/
lemma coeff_smul_algebraicClosure (τ : Gal(algebraicClosure ℚ ℂ/ℚ)) (n : ℕ) :
    (qExpansion 1 (τ • f).toCuspForm).coeff n = τ ⟨_, f.qExpansion_coeff_mem_algebraicClosure n⟩ :=
  (coeff_smul f _ n).trans (extendAut_apply τ ⟨_, f.qExpansion_coeff_mem_algebraicClosure n⟩)

variable (f) in
/-- **The orbits of the absolute Galois group of `ℚ` on newforms are the Galois orbits**
(LMFDB `cmf.newspaces`). -/
lemma orbit_algebraicClosure_eq_galoisOrbit :
    MulAction.orbit Gal(algebraicClosure ℚ ℂ/ℚ) f = f.galoisOrbit := by
  refine Set.ext fun g ↦ ⟨?_, fun ⟨σ, hσ⟩ ↦ ⟨σ.restrictNormal (algebraicClosure ℚ ℂ), ?_⟩⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨extendAut τ, f.isGaloisConjugateBy_smul (extendAut τ)⟩
  · refine Newform.ext <| CuspForm.qExpansion_injective one_pos
      (one_mem_strictPeriods_Gamma1_map N) <| PowerSeries.ext fun n ↦ ?_
    exact (f.coeff_smul_algebraicClosure _ n).trans <| (σ.restrictNormal_commutes
      (algebraicClosure ℚ ℂ) ⟨_, f.qExpansion_coeff_mem_algebraicClosure n⟩).trans (hσ.coeff n).symm

end HeckeRing.GL2.Newform
