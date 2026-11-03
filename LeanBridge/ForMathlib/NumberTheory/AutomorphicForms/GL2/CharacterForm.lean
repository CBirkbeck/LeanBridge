import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.BaseChange
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.Twist

/-!
# Hecke operators on twists, and the automorphic forms `χ ∘ det`

For every Hecke character `χ` and every finite place `v`, `T_v (φ ⊗ χ) = χ(v) (T_v φ) ⊗ χ`, since
every Hecke representative at `v` has determinant `ϖ`. A Hecke character `χ` is unramified at `v`
when its conductor exponent `χ.conductorExponent v` (Tau Ceti) vanishes; the twist by `χ` of a
function spherical at such a place is spherical.

The constant function `1` on `GL₂(𝔸_F)` is a Hecke eigenform of level `1` over every number field
`F`, with `T_v 1 = (N(v) + 1) 1`, hence so is its twist `χ ∘ det`, of level the finite conductor of
`χ`. These are concrete objects satisfying all the conditions of `AdelicGL2.IsAutomorphicForm` and
`AdelicGL2.IsHeckeEigenform`, though not cuspidal. Their Euler factor is
`(1 - N(v)^{1/2} χ(v) T)(1 - N(v)^{-1/2} χ(v) T)`.

The form `1` over `K` is the base change of the form `1` over any subfield of `K`, so that
`AdelicGL2.IsBaseChangeOf` and `AdelicGL2.IsBaseChange` are not vacuous.

## Main results

* `AdelicGL2.heckeOp_twist`: `T_v (φ ⊗ χ) = χ(v) (T_v φ) ⊗ χ`.
* `AdelicGL2.IsSphericalAt.twist`: the twist by an unramified character of a spherical function is
  spherical.
* `AdelicGL2.isAutomorphicForm_one`: the constant function `1` is an automorphic form.
* `AdelicGL2.isAutomorphicForm_charDet`: `χ ∘ det` is an automorphic form.
* `AdelicGL2.heckeOp_one`: `T_v 1 = (N(v) + 1) 1`.
* `AdelicGL2.isHeckeEigenform_one`: `1` is a Hecke eigenform of level `1`.
* `AdelicGL2.isHeckeEigenform_charDet`: `χ ∘ det` is a Hecke eigenform.
* `AdelicGL2.not_isCuspidal_one`: the form `1` is not cuspidal, so cuspidality is a real condition.
* `AdelicGL2.isBaseChangeOf_one` (LMFDB `mf.base_change`): `1` over `K` is a base change of `1`
  over `F`.
* `AdelicGL2.isBaseChange_one` (LMFDB `mf.base_change`): `1` over `K` is a base change.
-/

open Filter IsDedekindDomain HeightOneSpectrum Matrix NumberField Polynomial TauCeti
  GlobalNumberFields ValuationSubring

open mixedEmbedding (mixedSpace)

open scoped AdeleRing MatrixGroups Classical

namespace AdelicGL2

variable {F : Type*} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {χ : HeckeCharacter F}
  {ω : HeckeCharacter F} {φ : AdelicGL2 F → ℂ}

lemma mem_unitFiltration_zero {u : (v.adicCompletion F)ˣ}
    (hu : Valued.v (u : v.adicCompletion F) = 1) : u ∈ unitFiltration (v.adicCompletion F) 0 := by
  rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff]
  refine ⟨hu, ?_⟩
  simpa using (Valuation.map_sub Valued.v _ _).trans (max_le hu.le (map_one _).le)

lemma finiteComponent_eq_one_of_conductorExponent_eq_zero (hχ : χ.conductorExponent v = 0)
    {u : (v.adicCompletion F)ˣ} (hu : Valued.v (u : v.adicCompletion F) = 1) :
    χ.finiteComponent v u = 1 :=
  (χ.conductorExponent_eq_zero_iff v).mp hχ u (mem_unitFiltration_zero hu)

lemma conductorExponent_eq_zero_of_forall
    (h : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      χ.finiteComponent v u = 1) : χ.conductorExponent v = 0 :=
  (χ.conductorExponent_eq_zero_iff v).mpr fun u hu ↦ h u <| by
    rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff] at hu
    exact hu.1

variable (v) in
lemma ofFiniteIdele_det_localGL (m : GL (Fin 2) (v.adicCompletion F)) :
    IdeleGroup.ofFiniteIdele (𝓞 F) F (GeneralLinearGroup.det (localGL v m)) =
      IdeleGroup.ofAdicCompletion (𝓞 F) F v (GeneralLinearGroup.det m) := by
  refine IdeleGroup.ext (fun w ↦ ?_) fun w ↦ ?_
  · simp only [InfinitePlace.ideleInfiniteCoord_ofAdicCompletion]
    exact Units.ext rfl
  · refine Units.ext ?_
    have h : ((w.ideleFiniteCoord (IdeleGroup.ofFiniteIdele (𝓞 F) F
        (GeneralLinearGroup.det (localGL v m))) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
        (atPlace w (localGL v m) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)).det :=
      RingHom.map_det (evalRingHom w) (localGL v m).val
    rw [h]
    rcases eq_or_ne w v with rfl | hw
    · simp
    · rw [atPlace_localGL_of_ne hw, w.ideleFiniteCoord_ofAdicCompletion_of_ne hw]
      simp

variable (v χ) in
lemma charDet_ofFin_localGL (m : GL (Fin 2) (v.adicCompletion F)) :
    charDet χ (ofFin F (localGL v m)) = χ.finiteComponent v (GeneralLinearGroup.det m) := by
  rw [charDet, det_ofFin, ofFiniteIdele_det_localGL]
  rfl

private lemma det_mem_units {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ (v.adicCompletionIntegers F).gl2) :
    Valued.v ((GeneralLinearGroup.det k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
  have h₁ : Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≤ 1 :=
    (mem_adicCompletionIntegers _ _ v).mp (Subring.det_mem_of_mem_gl hk)
  have h₂ : Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det⁻¹ ≤ 1 :=
    (mem_adicCompletionIntegers _ _ v).mp (det_gl2_inv_mem hk)
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr k.det_ne_zero))] at h₂
  exact h₁.antisymm h₂

/-- **The twist by an unramified character of a spherical function is spherical.** -/
lemma IsSphericalAt.twist (hχ : χ.conductorExponent v = 0) (h : IsSphericalAt v φ) :
    IsSphericalAt v (twist χ φ) := fun k hk g ↦ by
  rw [AdelicGL2.twist, charDet_mul, charDet_ofFin_localGL,
    finiteComponent_eq_one_of_conductorExponent_eq_zero hχ (det_mem_units hk), Units.val_one,
    mul_one, h k hk]
  rfl

lemma det_heckeRep {ι : Type*} (ϖ : (v.adicCompletion F)ˣ) (r : ι → v.adicCompletion F)
    (o : Option ι) : GeneralLinearGroup.det (heckeRep ϖ r o) = ϖ := by
  refine Units.ext ?_
  cases o <;> simp [heckeRep, GeneralLinearGroup.det]

variable (φ) in
/-- **The Hecke operator on a twist**: `T_v (φ ⊗ χ) = χ(v) (T_v φ) ⊗ χ` for every Hecke character
`χ`, every Hecke representative at `v` having determinant the chosen uniformizer. -/
lemma heckeOp_twist : heckeOp v (twist χ φ) = (characterAt v χ : ℂ) • twist χ (heckeOp v φ) := by
  ext g
  simp only [heckeOp, heckeSum, one_mul, twist, charDet_mul, charDet_ofFin_localGL, det_heckeRep,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [characterAt]
  ring1

lemma heckeOp_twist_of_eq {a : ℂ} (h : heckeOp v φ = a • φ) :
    heckeOp v (twist χ φ) = ((characterAt v χ : ℂ) * a) • twist χ φ := by
  rw [heckeOp_twist, h, mul_smul]
  congr 1
  exact map_smul (twistₗ χ) a φ

private lemma lieDeriv_const (b : Fin 3) (y : mixedSpace F) (c : ℂ) :
    lieDeriv b y (fun _ : AdelicGL2 F ↦ c) = 0 :=
  funext fun _ ↦ deriv_const _ _

private lemma casimirOf_const {D : Fin 3 → (AdelicGL2 F → ℂ) → AdelicGL2 F → ℂ}
    (hD : ∀ b, IsSmoothOperator (D b)) (hc : ∀ b c, D b (fun _ ↦ c) = 0) (c : ℂ) :
    casimirOf D (fun _ : AdelicGL2 F ↦ c) = 0 := by
  have h0 (b : Fin 3) : D b 0 = 0 := (hD b).map_zero
  simp only [casimirOf, hc, h0]
  simp

/-- **The constant function `1` is an automorphic form** on `GL(2)` over every number field, with
trivial central character. -/
lemma isAutomorphicForm_one : IsAutomorphicForm (1 : HeckeCharacter F) (fun _ ↦ 1) where
  left_invariant _ _ := rfl
  central _ _ := by
    simp
  smooth := isSmoothAtInfinity_const 1
  exists_openSubgroup := ⟨⊤, fun _ _ _ ↦ rfl⟩
  kFinite := by
    have hle : kInfSpan (fun _ : AdelicGL2 F ↦ (1 : ℂ)) ≤
        Submodule.span ℂ {fun _ : AdelicGL2 F ↦ (1 : ℂ)} :=
      Submodule.span_mono (Set.range_subset_iff.mpr fun _ ↦ rfl)
    exact Submodule.finiteDimensional_of_le hle
  casimirFinite := by
    have hs : ∀ ψ ∈ Submodule.span ℂ {fun _ : AdelicGL2 F ↦ (1 : ℂ)}, ∃ c : ℂ, ψ = fun _ ↦ c := by
      intro ψ hψ
      rcases Submodule.mem_span_singleton.mp hψ with ⟨c, rfl⟩
      exact ⟨c, funext fun _ ↦ by simp⟩
    refine ⟨Submodule.span ℂ {fun _ : AdelicGL2 F ↦ (1 : ℂ)}, inferInstance,
      Submodule.mem_span_singleton_self _, fun ψ hψ ↦ ?_, fun v ψ hψ ↦ ?_, fun v ψ hψ ↦ ?_,
        fun v ψ hψ ↦ ?_⟩
    · rcases hs ψ hψ with ⟨c, rfl⟩
      exact isSmoothAtInfinity_const c
    · rcases hs ψ hψ with ⟨c, rfl⟩
      rw [casimirReal, casimirOf_const (fun b ↦ isSmoothOperator_lieDeriv b _)
        (fun b ↦ lieDeriv_const b _)]
      exact zero_mem _
    · rcases hs ψ hψ with ⟨c, rfl⟩
      rw [casimirHolo, casimirOf_const (fun b ↦ isSmoothOperator_lieDerivHolo b v)
        (fun b c ↦ by simp [lieDerivHolo, lieDeriv_const])]
      exact zero_mem _
    · rcases hs ψ hψ with ⟨c, rfl⟩
      rw [casimirAntiholo, casimirOf_const (fun b ↦ isSmoothOperator_lieDerivAntiholo b v)
        (fun b c ↦ by simp [lieDerivAntiholo, lieDeriv_const])]
      exact zero_mem _
  moderateGrowth _ := ⟨1, 0, fun _ ↦ by simp⟩

variable (χ) in
lemma twist_one : twist χ (fun _ ↦ 1) = charDet χ :=
  funext fun _ ↦ mul_one _

variable (χ) in
/-- **`χ ∘ det` is an automorphic form** with central character `χ²`, for every Hecke character
`χ`. -/
lemma isAutomorphicForm_charDet : IsAutomorphicForm (χ ^ 2) (charDet χ) := by
  have h : IsAutomorphicForm (1 * χ ^ 2) (twist χ fun _ ↦ 1) := isAutomorphicForm_one.twist χ
  have he : (1 : HeckeCharacter F) * χ ^ 2 = χ ^ 2 := ContinuousMonoidHom.ext fun _ ↦ by
    simp
  rwa [twist_one, he] at h

variable (v) in
lemma card_residue : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

variable (v) in
/-- **`T_v 1 = (N(v) + 1) 1`.** -/
lemma heckeOp_one : heckeOp v (fun _ : AdelicGL2 F ↦ (1 : ℂ)) =
    ((Ideal.absNorm v.asIdeal : ℂ) + 1) • fun _ ↦ 1 := by
  ext g
  simp [heckeOp, heckeSum, card_residue]

private lemma isSphericalAt_one : IsSphericalAt v (fun _ ↦ 1) :=
  fun _ _ _ ↦ rfl

/-- **The constant function `1` is a Hecke eigenform of level `1`.** -/
lemma isHeckeEigenform_one : IsHeckeEigenform (1 : HeckeCharacter F) ⊤ (fun _ ↦ 1) where
  isAutomorphicForm := isAutomorphicForm_one
  level_ne_bot := top_ne_bot
  ne_zero := fun h ↦ one_ne_zero (congrFun h 1)
  spherical _ _ := isSphericalAt_one
  exists_eigenvalue v _ := ⟨_, heckeOp_one v⟩

lemma conductorExponent_eq_zero_of_not_le (hv : ¬χ.finiteConductor ≤ v.asIdeal) :
    χ.conductorExponent v = 0 :=
  not_not.mp ((χ.dvd_finiteConductor_iff v).not.mp fun h ↦ hv (Ideal.le_of_dvd h))

variable (χ) in
/-- **`χ ∘ det` is a Hecke eigenform**, of level the finite conductor of `χ`. -/
lemma isHeckeEigenform_charDet : IsHeckeEigenform (χ ^ 2) χ.finiteConductor (charDet χ) where
  isAutomorphicForm := isAutomorphicForm_charDet χ
  level_ne_bot := χ.finiteConductor_ne_bot
  ne_zero := fun h ↦ charDet_ne_zero χ 1 (congrFun h 1)
  spherical _ hv := twist_one χ ▸ isSphericalAt_one.twist (conductorExponent_eq_zero_of_not_le hv)
  exists_eigenvalue v _ := ⟨_, twist_one χ ▸ heckeOp_twist_of_eq (heckeOp_one v)⟩

variable (v) in
private lemma eulerFactor_one : eulerFactor v (1 : HeckeCharacter F) (fun _ ↦ 1) =
    (1 - C ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) * X) *
      (1 - C (((Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ : ℝ) : ℂ) * X) := by
  have hv : ¬(⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := fun h ↦ v.isPrime.ne_top (top_le_iff.mp h)
  have hs : Real.sqrt (Ideal.absNorm v.asIdeal) ≠ 0 := Real.sqrt_ne_zero'.mpr <|
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))
  have hsC : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsqC : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) = Ideal.absNorm v.asIdeal := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg (Ideal.absNorm v.asIdeal))
  have he : (Ideal.absNorm v.asIdeal : ℂ) + 1 = heckeEigenvalue v (fun _ : AdelicGL2 F ↦ (1 : ℂ)) :=
    isHeckeEigenform_one.eq_heckeEigenvalue hv (heckeOp_one v)
  rw [eulerFactor, ← he, characterAt, HeckeCharacter.finiteComponent_one]
  have h₁ : (((Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ : ℝ) : ℂ) *
      ((Ideal.absNorm v.asIdeal : ℂ) + 1) = ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) +
        (((Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ : ℝ) : ℂ) := by
    rw [← hsqC, Complex.ofReal_inv]
    field_simp
  have h₂ : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) *
      (((Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_inv]
    exact mul_inv_cancel₀ hsC
  rw [h₁, C_add]
  have h₃ : C ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) *
      C (((Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← C_mul, h₂, C_1]
  have h₄ : (((1 : (v.adicCompletion F)ˣ →ₜ* ℂˣ) (uniformizer v) : ℂˣ) : ℂ) = 1 := rfl
  rw [h₄, C_1]
  linear_combination (-(X : ℂ[X]) ^ 2) * h₃

/-- **The form `1` is not cuspidal**, as its constant term is the volume of `𝔸_F / F`:
cuspidality is a real condition. -/
lemma not_isCuspidal_one : ¬IsCuspidal (fun _ : AdelicGL2 F ↦ (1 : ℂ)) := fun h ↦ by
  have he : constantTerm (fun _ : AdelicGL2 F ↦ (1 : ℂ)) 1 = 0 := h 1
  rw [constantTerm, MeasureTheory.integral_const, Complex.real_smul, mul_one,
    Complex.ofReal_eq_zero, MeasureTheory.measureReal_eq_zero_iff] at he
  exact isOpen_univ.measure_ne_zero _ Set.univ_nonempty he

variable {K : Type*} [Field K] [NumberField K] [Algebra F K]

/-- **The form `1` over `K` is the base change of the form `1` over `F`** (LMFDB
`mf.base_change`): `L_𝔮(1, T) = (1 - N(𝔮)^{1/2} T)(1 - N(𝔮)^{-1/2} T) = L_𝔭^{(r)}(1, T)`, since
`N(𝔮) = N(𝔭)^r`. -/
lemma isBaseChangeOf_one (𝔑 : Ideal (𝓞 F)) :
    IsBaseChangeOf 𝔑 (1 : HeckeCharacter F) (fun _ ↦ 1) (1 : HeckeCharacter K) (fun _ ↦ 1) := by
  refine Eventually.of_forall fun 𝔮 h𝔮 h𝔮₀ _ ↦ ?_
  let w : HeightOneSpectrum (𝓞 K) := ⟨𝔮, h𝔮, h𝔮₀⟩
  have hs : Real.sqrt (Ideal.absNorm (w.under (𝓞 F)).asIdeal) ≠ 0 := Real.sqrt_ne_zero'.mpr <|
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (w.under (𝓞 F)).ne_bot))
  have hu : 𝔮.comap (algebraMap (𝓞 F) (𝓞 K)) = (w.under (𝓞 F)).asIdeal := rfl
  have hw : 𝔮 = w.asIdeal := rfl
  rw [hu, hw, eulerFactorOfIdeal_eq, eulerFactorOfIdeal_eq, eulerFactor_one, eulerFactor_one,
    rootPowers_mul _ _ (Complex.ofReal_ne_zero.mpr hs)
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero hs)), absNorm_eq_pow F w, Nat.cast_pow,
    sqrt_pow_eq (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_pow,
    inv_pow]

/-- **The form `1` over `K` is a base change** from every proper subfield of `K` (LMFDB
`mf.base_change`). -/
lemma isBaseChange_one {K₀ : Subfield K} (h : K₀ ≠ ⊤) :
    IsBaseChange (1 : HeckeCharacter K) (fun _ ↦ 1) :=
  ⟨K₀, h, ⊤, 1, fun _ ↦ 1, isHeckeEigenform_one, isBaseChangeOf_one ⊤⟩

end AdelicGL2
