import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.Hecke
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.InfinityType
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic

/-!
# Twists of automorphic forms on `GL₂(𝔸_F)` by Hecke characters

The **twist** of a function `φ` on `GL₂(𝔸_F)` by a Hecke character `χ` of `F` (Tau Ceti's
`TauCeti.GlobalNumberFields.HeckeCharacter`, a continuous character of the idele class group) is
`φ ⊗ χ : g ↦ χ(det g) φ(g)`. If `φ` is an automorphic form with central character `ω`, then
`φ ⊗ χ` is one with central character `ω χ²`, cuspidal if `φ` is. At a place `v` where `φ` is
spherical and `χ` is unramified, `φ ⊗ χ` is spherical and `T_v (φ ⊗ χ) = χ(v) (T_v φ) ⊗ χ`.

In particular the function `χ ∘ det` is an automorphic form, with central character `χ²`.

## Main definitions

* `AdelicGL2.charDet`: the function `χ ∘ det`.
* `AdelicGL2.twist`: the twist `φ ⊗ χ`.
* `AdelicGL2.ideleOfMixed`: the idele with a given unit of `E` as infinite component.

## Main results

* `AdelicGL2.isSmoothAtInfinity_charDet`: `χ ∘ det` is smooth in the archimedean variable.
* `AdelicGL2.hasModerateGrowth_charDet`: `χ ∘ det` has moderate growth.
* `AdelicGL2.IsAutomorphicForm.twist`: the twist of an automorphic form with central character `ω`
  is automorphic with central character `ω χ²`.
* `AdelicGL2.IsCuspidal.twist`: the twist of a cuspidal function is cuspidal.
-/

open Filter IsDedekindDomain HeightOneSpectrum Matrix NumberField InfinitePlace Completion TauCeti
  GlobalNumberFields

open mixedEmbedding (mixedSpace)

open scoped AdeleRing MatrixGroups Classical

namespace AdelicGL2

variable {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F) (g g' : AdelicGL2 F)

variable (F) in
/-- The idele with the given unit of the mixed space as infinite component, and `1` at the finite
places. -/
noncomputable def ideleOfMixed : (mixedSpace F)ˣ →* IdeleGroup (𝓞 F) F :=
  (IdeleGroup.ofInfiniteIdele (𝓞 F) F).comp
    (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.toMonoidHom)

private lemma mixed_fst_det :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (GeneralLinearGroup.det g : 𝔸[F]).1 =
      (toInf F g : Matrix (Fin 2) (Fin 2) (mixedSpace F)).det :=
  RingHom.map_det ((RingHom.fst _ _).comp (adeleEquiv F : 𝔸[F] →+* mixedSpace F × 𝔸ᶠ[F])) g.val

private lemma snd_det :
    (GeneralLinearGroup.det g : 𝔸[F]).2 = (toFin F g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]).det :=
  RingHom.map_det ((RingHom.snd _ _).comp (adeleEquiv F : 𝔸[F] →+* mixedSpace F × 𝔸ᶠ[F])) g.val

lemma det_ofInf (x : GL (Fin 2) (mixedSpace F)) :
    GeneralLinearGroup.det (ofInf F x) = ideleOfMixed F (GeneralLinearGroup.det x) := by
  refine Units.ext (Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective ?_) ?_)
  · rw [mixed_fst_det, toInf_ofInf]
    exact (RingEquiv.apply_symm_apply _ _).symm
  · rw [snd_det, toFin_ofInf]
    simp [ideleOfMixed]

lemma det_ofFin (y : GL (Fin 2) 𝔸ᶠ[F]) :
    GeneralLinearGroup.det (ofFin F y) =
      IdeleGroup.ofFiniteIdele (𝓞 F) F (GeneralLinearGroup.det y) := by
  refine Units.ext (Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective ?_) ?_)
  · rw [mixed_fst_det, toInf_ofFin, Units.val_one, det_one]
    exact (map_one _).symm
  · rw [snd_det, toFin_ofFin]
    rfl

/-- The function **`χ ∘ det`** on `GL₂(𝔸_F)`, for a Hecke character `χ` of `F`. -/
noncomputable def charDet : ℂ :=
  (χ (QuotientGroup.mk (GeneralLinearGroup.det g)) : ℂ)

/-- The **twist** `φ ⊗ χ : g ↦ χ(det g) φ(g)` of a function on `GL₂(𝔸_F)` by a Hecke character. -/
noncomputable def twist (φ : AdelicGL2 F → ℂ) : AdelicGL2 F → ℂ :=
  fun g ↦ charDet χ g * φ g

lemma charDet_mul : charDet χ (g * g') = charDet χ g * charDet χ g' := by
  simp [charDet]

lemma charDet_ne_zero : charDet χ g ≠ 0 :=
  Units.ne_zero _

lemma charDet_one : charDet χ (1 : AdelicGL2 F) = 1 := by
  simp [charDet]

lemma charDet_ofGlobal (γ : GL (Fin 2) F) : charDet χ (ofGlobal F γ) = 1 := by
  have h : GeneralLinearGroup.det (ofGlobal F γ) ∈ IdeleGroup.principalSubgroup (𝓞 F) F :=
    ⟨GeneralLinearGroup.det γ, Units.ext (RingHom.map_det (algebraMap F 𝔸[F]) γ.val)⟩
  rw [charDet, (QuotientGroup.eq_one_iff _).mpr h, map_one, Units.val_one]

lemma charDet_scalar (z : IdeleGroup (𝓞 F) F) :
    charDet χ (scalar F z) = (χ (QuotientGroup.mk z) : ℂ) ^ 2 := by
  simp [charDet, scalar]

lemma charDet_sl2Exp (b : Fin 3) (w : mixedSpace F) : charDet χ (ofInf F (sl2Exp b w)) = 1 := by
  rw [charDet, det_ofInf, det_sl2Exp]
  simp

/-! ### Smoothness of `χ ∘ det` -/

private lemma apply_ideleOfMixed (z : (mixedSpace F)ˣ) :
    (χ (QuotientGroup.mk (ideleOfMixed F z)) : ℂ) =
      ∏ w, (χ.infiniteComponent w (w.ideleInfiniteCoord (ideleOfMixed F z)) : ℂ) := by
  have hf : IdeleGroup.toFiniteIdele (𝓞 F) F (ideleOfMixed F z) = 1 := by
    simp [ideleOfMixed]
  have h : (∏ w : InfinitePlace F, IdeleGroup.ofCompletion (𝓞 F) F w
      (w.ideleInfiniteCoord (ideleOfMixed F z))) *
        IdeleGroup.ofFiniteIdele (𝓞 F) F (IdeleGroup.toFiniteIdele (𝓞 F) F (ideleOfMixed F z)) =
      ideleOfMixed F z :=
    IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele (ideleOfMixed F z)
  rw [hf, map_one, mul_one] at h
  conv_lhs => rw [← h]
  rw [QuotientGroup.mk_prod, map_prod, Units.coe_prod]
  rfl

private lemma contDiffAt_ofReal_cpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f x) (hx : 0 < f x) (s : ℂ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y ↦ ((f y : ℝ) : ℂ) ^ s) x := by
  have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y ↦ Complex.exp (((Real.log (f y) : ℝ) : ℂ) * s)) x :=
    (Complex.contDiff_exp.contDiffAt (x := _)).comp x
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((Real.contDiffAt_log.mpr hx.ne').comp x hf)).mul contDiffAt_const)
  refine hl.congr_of_eventuallyEq ?_
  filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.ofReal_log hy.le]

private lemma contDiffAt_realFun (s : ℂ) (ε : ZMod 2) {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℝ ↦ ((|y| : ℝ) : ℂ) ^ s * (SignType.sign y : ℂ) ^ ε.val) x := by
  refine (contDiffAt_ofReal_cpow (contDiffAt_abs hx) (abs_pos.mpr hx) s).mul ?_
  refine (contDiffAt_const (c := ((SignType.sign x : ℂ) ^ ε.val))).congr_of_eventuallyEq ?_
  rcases lt_or_gt_of_ne hx with h | h
  · filter_upwards [Iio_mem_nhds h] with y hy
    rw [sign_neg (Set.mem_Iio.mp hy), sign_neg h]
  · filter_upwards [Ioi_mem_nhds h] with y hy
    rw [sign_pos (Set.mem_Ioi.mp hy), sign_pos h]

private lemma contDiffAt_complexFun (s : ℂ) (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℂ ↦ ((‖y‖ : ℝ) : ℂ) ^ s * (y / (‖y‖ : ℂ)) ^ k) z := by
  have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ ↦ ‖y‖) z := contDiffAt_norm ℝ hz
  have hd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ ↦ y / (‖y‖ : ℂ)) z := by
    simp only [div_eq_mul_inv]
    exact contDiffAt_id.mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp z hn).inv
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)))
  have hd₀ : z / (‖z‖ : ℂ) ≠ 0 :=
    div_ne_zero hz (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))
  refine (contDiffAt_ofReal_cpow hn (norm_pos_iff.mpr hz) s).mul ?_
  rcases k with n | n
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hd.pow n
  · simp only [zpow_negSucc]
    exact (hd.pow (n + 1)).inv (pow_ne_zero _ hd₀)

/-- The local factor at the infinite place `w` of the function `z ↦ χ(z)` on the units of the mixed
space, as a function on the whole mixed space. -/
private noncomputable def localFun (w : InfinitePlace F) (z : mixedSpace F) : ℂ :=
  if h : w.IsReal then
    ((|z.1 ⟨w, h⟩| : ℝ) : ℂ) ^ (χ.infinityType.realExponent ⟨w, h⟩) *
      (SignType.sign (z.1 ⟨w, h⟩) : ℂ) ^ (χ.infinityType.realParity ⟨w, h⟩).val
  else
    ((‖z.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩‖ : ℝ) : ℂ) ^
        (χ.infinityType.complexExponent ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩) *
      (z.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩ /
        (‖z.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩‖ : ℂ)) ^
          (χ.infinityType.complexAngularFrequency ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩)

private lemma contDiffOn_localFun (w : InfinitePlace F) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (localFun χ w) {z | IsUnit z} := by
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases h : w.IsReal
  · have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : mixedSpace F ↦ z.1 ⟨w, h⟩) :=
      contDiff_pi.mp contDiff_fst (⟨w, h⟩ : {w : InfinitePlace F // w.IsReal})
    have h₀ : z.1 ⟨w, h⟩ ≠ 0 :=
      (IsUnit.map ((Pi.evalMonoidHom (fun _ ↦ ℝ) (⟨w, h⟩ : {w : InfinitePlace F // w.IsReal})).comp
        (MonoidHom.fst _ _)) hz).ne_zero
    refine ((contDiffAt_realFun (χ.infinityType.realExponent ⟨w, h⟩)
      (χ.infinityType.realParity ⟨w, h⟩) h₀).comp z hc.contDiffAt).congr_of_eventuallyEq
        (Eventually.of_forall fun y ↦ ?_)
    simp only [localFun, h, ↓reduceDIte, Function.comp_def]
  · have hw : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp h
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : mixedSpace F ↦ z.2 ⟨w, hw⟩) :=
      contDiff_pi.mp contDiff_snd (⟨w, hw⟩ : {w : InfinitePlace F // w.IsComplex})
    have h₀ : z.2 ⟨w, hw⟩ ≠ 0 :=
      (IsUnit.map ((Pi.evalMonoidHom (fun _ ↦ ℂ)
        (⟨w, hw⟩ : {w : InfinitePlace F // w.IsComplex})).comp (MonoidHom.snd _ _)) hz).ne_zero
    refine ((contDiffAt_complexFun (χ.infinityType.complexExponent ⟨w, hw⟩)
      (χ.infinityType.complexAngularFrequency ⟨w, hw⟩) h₀).comp z
        hc.contDiffAt).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
    simp only [localFun, h, ↓reduceDIte, Function.comp_def]

private lemma coord_real (z : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    continuousMulEquivRealOfIsReal w.2
      ((w.1.ideleInfiniteCoord (ideleOfMixed F z) : w.1.Completionˣ) : w.1.Completion) =
        (z : mixedSpace F).1 w := by
  rw [← (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (z : mixedSpace F),
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact continuousMulEquivRealOfIsReal_apply w.2 _

private lemma coord_complex (z : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    continuousMulEquivComplexOfIsComplex w.2
      ((w.1.ideleInfiniteCoord (ideleOfMixed F z) : w.1.Completionˣ) : w.1.Completion) =
        (z : mixedSpace F).2 w := by
  rw [← (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (z : mixedSpace F),
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact continuousMulEquivComplexOfIsComplex_apply w.2 _

private lemma infiniteComponent_eq_localFun (z : (mixedSpace F)ˣ) (w : InfinitePlace F) :
    (χ.infiniteComponent w (w.ideleInfiniteCoord (ideleOfMixed F z)) : ℂ) =
      localFun χ w (z : mixedSpace F) := by
  by_cases h : w.IsReal
  · let x : ℝˣ := Units.map (continuousMulEquivRealOfIsReal h).toMulEquiv.toMonoidHom
      (w.ideleInfiniteCoord (ideleOfMixed F z))
    have hx : (x : ℝ) = (z : mixedSpace F).1 ⟨w, h⟩ := coord_real z ⟨w, h⟩
    have hu : w.ideleInfiniteCoord (ideleOfMixed F z) =
        (Units.mapContinuousMulEquiv (continuousMulEquivRealOfIsReal h)).symm x :=
      (ContinuousMulEquiv.symm_apply_apply _ _).symm
    have hc : ((χ.realComponent ⟨w, h⟩ x : ℂˣ) : ℂ) = ((realUnitsCharacter
        (χ.infinityType.realExponent ⟨w, h⟩) (χ.infinityType.realParity ⟨w, h⟩) x : ℂˣ) : ℂ) :=
      congrArg (fun ψ : ℝˣ →ₜ* ℂˣ ↦ (ψ x : ℂ)) (χ.realComponent_eq ⟨w, h⟩)
    simp only [HeckeCharacter.realComponent_apply, coe_realUnitsCharacter_apply, ← hu, hx] at hc
    simpa only [localFun, h, ↓reduceDIte] using hc
  · have hw : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp h
    let x : ℂˣ := Units.map (continuousMulEquivComplexOfIsComplex hw).toMulEquiv.toMonoidHom
      (w.ideleInfiniteCoord (ideleOfMixed F z))
    have hx : (x : ℂ) = (z : mixedSpace F).2 ⟨w, hw⟩ := coord_complex z ⟨w, hw⟩
    have hu : w.ideleInfiniteCoord (ideleOfMixed F z) =
        (Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex hw)).symm x :=
      (ContinuousMulEquiv.symm_apply_apply _ _).symm
    have hc : ((χ.complexComponent ⟨w, hw⟩ x : ℂˣ) : ℂ) = ((complexUnitsCharacter
        (χ.infinityType.complexExponent ⟨w, hw⟩) (χ.infinityType.complexAngularFrequency ⟨w, hw⟩)
          x : ℂˣ) : ℂ) :=
      congrArg (fun ψ : ℂˣ →ₜ* ℂˣ ↦ (ψ x : ℂ)) (χ.complexComponent_eq ⟨w, hw⟩)
    simp only [HeckeCharacter.complexComponent_apply, coe_complexUnitsCharacter_apply, ← hu,
      hx] at hc
    simpa only [localFun, h, ↓reduceDIte] using hc

/-- **`χ ∘ det` is smooth in the archimedean variable**, for every Hecke character `χ`: by the
classification of the continuous characters of `ℝˣ` and `ℂˣ`. -/
lemma isSmoothAtInfinity_charDet : IsSmoothAtInfinity (charDet χ) := fun g ↦ by
  have hdet : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun m : Fin 2 → Fin 2 → mixedSpace F ↦ (of m).det) := by
    simp only [det_fin_two, of_apply]
    exact ((contDiff_apply_apply ℝ 0 0).mul (contDiff_apply_apply ℝ 1 1)).sub
      ((contDiff_apply_apply ℝ 0 1).mul (contDiff_apply_apply ℝ 1 0))
  have hp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : mixedSpace F ↦ ∏ w, localFun χ w z)
      {z | IsUnit z} :=
    contDiffOn_prod fun w _ ↦ contDiffOn_localFun χ w
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun m : Fin 2 → Fin 2 → mixedSpace F ↦ charDet χ g * ∏ w, localFun χ w (of m).det)
      {m | IsUnit (of m)} :=
    contDiffOn_const.mul (hp.comp hdet.contDiffOn fun m hm ↦ (isUnit_iff_isUnit_det _).mp hm)
  refine hc.congr fun m hm ↦ ?_
  have he : charDet χ (ofInf F (IsUnit.unit hm)) = ∏ w, localFun χ w (of m).det := by
    rw [charDet, det_ofInf, apply_ideleOfMixed]
    simp only [infiniteComponent_eq_localFun, GeneralLinearGroup.val_det_apply, IsUnit.unit_spec]
  rw [extendGL_of_isUnit _ hm, charDet_mul, he]

/-! ### Moderate growth of `χ ∘ det` -/

private lemma rpow_le_pow_of_le {y T r : ℝ} {m : ℕ} (hy : 0 < y) (h₁ : y ≤ T) (h₂ : y⁻¹ ≤ T)
    (hT : 1 ≤ T) (hr : |r| ≤ m) : y ^ r ≤ T ^ m := by
  have hend : T ^ |r| ≤ T ^ m :=
    (Real.rpow_le_rpow_of_exponent_le hT hr).trans_eq (Real.rpow_natCast T m)
  rcases le_total 1 y with hy₁ | hy₁
  · exact ((Real.rpow_le_rpow_of_exponent_le hy₁ (le_abs_self r)).trans
      (Real.rpow_le_rpow hy.le h₁ (abs_nonneg r))).trans hend
  · have hinv : 1 ≤ y⁻¹ := (one_le_inv₀ hy).mpr hy₁
    have he : y ^ r = y⁻¹ ^ (-r) := by
      rw [Real.inv_rpow hy.le, Real.rpow_neg hy.le, inv_inv]
    rw [he]
    exact ((Real.rpow_le_rpow_of_exponent_le hinv (neg_le_abs r)).trans
      (Real.rpow_le_rpow (inv_nonneg.mpr hy.le) h₂ (abs_nonneg r))).trans hend

private lemma norm_apply_le_infHeight (x : GL (Fin 2) (mixedSpace F)) (i j : Fin 2) :
    ‖(x : Matrix (Fin 2) (Fin 2) (mixedSpace F)) i j‖ ≤ infHeight x := by
  let f : Fin 2 → Fin 2 → ℝ := fun a b ↦ ‖(x : Matrix (Fin 2) (Fin 2) (mixedSpace F)) a b‖ +
    ‖((x⁻¹ : GL (Fin 2) (mixedSpace F)) : Matrix (Fin 2) (Fin 2) (mixedSpace F)) a b‖
  have hf (a b : Fin 2) : 0 ≤ f a b := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have h₂ : f i j ≤ ∑ b, f i b := Finset.single_le_sum (fun b _ ↦ hf i b) (Finset.mem_univ j)
  have h₃ : ∑ b, f i b ≤ ∑ a, ∑ b, f a b := Finset.single_le_sum (f := fun a ↦ ∑ b, f a b)
    (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ hf a b) (Finset.mem_univ i)
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans
    (h₂.trans (h₃.trans (le_add_of_nonneg_left zero_le_one)))

private lemma norm_inv_apply_le_infHeight (x : GL (Fin 2) (mixedSpace F)) (i j : Fin 2) :
    ‖((x⁻¹ : GL (Fin 2) (mixedSpace F)) : Matrix (Fin 2) (Fin 2) (mixedSpace F)) i j‖ ≤
      infHeight x := by
  have he : infHeight x⁻¹ = infHeight x := by
    rw [infHeight, infHeight, inv_inv]
    exact congrArg (1 + ·) <|
      Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ add_comm _ _
  exact he ▸ norm_apply_le_infHeight x⁻¹ i j

private lemma norm_det_le_of_apply_le {A : Matrix (Fin 2) (Fin 2) (mixedSpace F)} {h : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ h) : ‖A.det‖ ≤ 2 * h ^ 2 := by
  have hh : 0 ≤ h := (norm_nonneg _).trans (hA 0 0)
  rw [det_fin_two]
  refine (norm_sub_le _ _).trans ?_
  have h₁ : ‖A 0 0 * A 1 1‖ ≤ h * h :=
    (norm_mul_le _ _).trans (mul_le_mul (hA 0 0) (hA 1 1) (norm_nonneg _) hh)
  have h₂ : ‖A 0 1 * A 1 0‖ ≤ h * h :=
    (norm_mul_le _ _).trans (mul_le_mul (hA 0 1) (hA 1 0) (norm_nonneg _) hh)
  nlinarith

private lemma norm_coord_le (z : (mixedSpace F)ˣ) (w : InfinitePlace F) :
    ‖((w.ideleInfiniteCoord (ideleOfMixed F z) : w.Completionˣ) : w.Completion)‖ ≤
      ‖(z : mixedSpace F)‖ := by
  by_cases h : w.IsReal
  · have he : extensionEmbeddingOfIsReal h
        ((w.ideleInfiniteCoord (ideleOfMixed F z) : w.Completionˣ) : w.Completion) =
          (z : mixedSpace F).1 ⟨w, h⟩ := by
      simpa only [continuousMulEquivRealOfIsReal_apply] using coord_real z ⟨w, h⟩
    rw [← (isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero (map_zero _), he]
    exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
  · have hw : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp h
    have he : extensionEmbedding w
        ((w.ideleInfiniteCoord (ideleOfMixed F z) : w.Completionˣ) : w.Completion) =
          (z : mixedSpace F).2 ⟨w, hw⟩ := by
      simpa only [continuousMulEquivComplexOfIsComplex_apply] using coord_complex z ⟨w, hw⟩
    rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), he]
    exact (norm_le_pi_norm _ _).trans (norm_snd_le _)

/-- **`χ ∘ det` has moderate growth**, for every Hecke character `χ`. -/
lemma hasModerateGrowth_charDet : HasModerateGrowth (charDet χ) := fun y ↦ by
  let m : ℕ := ⌈|χ.shift|⌉₊
  let c : ℕ := Fintype.card (InfinitePlace F)
  refine ⟨‖charDet χ (ofFin F y)‖ * (5 ^ 2) ^ (m * c), 2 * 2 * m * c, fun x ↦ ?_⟩
  rw [charDet_mul, norm_mul, mul_comm, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  set h := infHeight x
  have hh₁ : 1 ≤ h := one_le_infHeight x
  set z : (mixedSpace F)ˣ := GeneralLinearGroup.det x with hz
  have hz₁ : ‖(z : mixedSpace F)‖ ≤ 2 * h ^ 2 :=
    norm_det_le_of_apply_le (norm_apply_le_infHeight x)
  have hz₂ : ‖((z⁻¹ : (mixedSpace F)ˣ) : mixedSpace F)‖ ≤ 2 * h ^ 2 := by
    rw [hz, ← map_inv]
    exact norm_det_le_of_apply_le (norm_inv_apply_le_infHeight x)
  have hT : 5 * h ^ 2 = 1 * h ^ 2 + 4 * h ^ 2 := by ring1
  have hsq : 1 ≤ h ^ 2 := one_le_pow₀ hh₁
  have hlocal (w : InfinitePlace F) : ‖(χ.infiniteComponent w
      (w.ideleInfiniteCoord (ideleOfMixed F z)) : ℂ)‖ ≤ ((5 * h ^ 2) ^ 2) ^ m := by
    rw [HeckeCharacter.norm_infiniteComponent_apply, completionNormalizedAbsValue_apply]
    set u : w.Completionˣ := w.ideleInfiniteCoord (ideleOfMixed F z)
    have hu₀ : 0 < ‖(u : w.Completion)‖ := norm_pos_iff.mpr u.ne_zero
    have hu₁ : ‖(u : w.Completion)‖ ≤ 5 * h ^ 2 :=
      (norm_coord_le z w).trans (by linarith)
    have hu₂ : ‖(u : w.Completion)‖⁻¹ ≤ 5 * h ^ 2 := by
      have hi : ‖((w.ideleInfiniteCoord (ideleOfMixed F z⁻¹) : w.Completionˣ) : w.Completion)‖ ≤
          ‖((z⁻¹ : (mixedSpace F)ˣ) : mixedSpace F)‖ :=
        norm_coord_le z⁻¹ w
      rw [map_inv, map_inv, Units.val_inv_eq_inv_val, norm_inv] at hi
      exact hi.trans (by linarith)
    have hT₁ : 1 ≤ 5 * h ^ 2 := by linarith
    have hmult : w.mult ≤ 2 := by
      rw [InfinitePlace.mult]
      split_ifs <;> norm_num
    have hm : ‖(u : w.Completion)‖ ^ w.mult ≤ (5 * h ^ 2) ^ 2 :=
      (pow_le_pow_left₀ hu₀.le hu₁ _).trans (pow_le_pow_right₀ hT₁ hmult)
    have hm' : (‖(u : w.Completion)‖ ^ w.mult)⁻¹ ≤ (5 * h ^ 2) ^ 2 := by
      rw [← inv_pow]
      exact (pow_le_pow_left₀ (inv_nonneg.mpr hu₀.le) hu₂ _).trans (pow_le_pow_right₀ hT₁ hmult)
    exact rpow_le_pow_of_le (pow_pos hu₀ _) hm hm' (one_le_pow₀ hT₁) (Nat.le_ceil _)
  have hprod : ‖charDet χ (ofInf F x)‖ ≤ (((5 * h ^ 2) ^ 2) ^ m) ^ c := by
    rw [charDet, det_ofInf, apply_ideleOfMixed, norm_prod]
    refine (Finset.prod_le_prod₀ (fun w _ ↦ norm_nonneg _) fun w _ ↦ hlocal w).trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ]
  refine hprod.trans_eq ?_
  ring1

/-! ### The twist of an automorphic form -/

lemma exists_openSubgroup_charDet : ∃ U : OpenSubgroup (GL (Fin 2) 𝔸ᶠ[F]),
    ∀ u ∈ U, charDet χ (ofFin F u) = 1 := by
  rcases χ.exists_modulus_finitePart_eq_one with ⟨𝔪, h𝔪⟩
  let f : GL (Fin 2) 𝔸ᶠ[F] →* IdeleGroup (𝓞 F) F :=
    (IdeleGroup.ofFiniteIdele (𝓞 F) F).comp GeneralLinearGroup.det
  have hf : Continuous f := (Continuous.units_map _ (continuous_const.prodMk continuous_id)).comp
    GeneralLinearGroup.continuous_det
  refine ⟨⟨(ideleCongruenceSubgroup 𝔪).comap f, (isOpen_ideleCongruenceSubgroup 𝔪).preimage hf⟩,
    fun u hu ↦ ?_⟩
  have hf' : IdeleGroup.toFiniteIdele (𝓞 F) F (f u) = GeneralLinearGroup.det u :=
    IdeleGroup.toFiniteIdele_ofFiniteIdele _ _ _
  have h : χ (QuotientGroup.mk (IdeleGroup.ofFiniteIdele (𝓞 F) F (GeneralLinearGroup.det u))) =
      1 := by
    rw [← hf']
    exact h𝔪 (f u) hu
  rw [charDet, det_ofFin, h, Units.val_one]

variable {χ} {ω : HeckeCharacter F} {φ : AdelicGL2 F → ℂ}

variable (χ) in
/-- The twist as a linear map on functions. -/
noncomputable def twistₗ : (AdelicGL2 F → ℂ) →ₗ[ℂ] AdelicGL2 F → ℂ where
  toFun := twist χ
  map_add' _ _ := funext fun _ ↦ mul_add _ _ _
  map_smul' _ _ := funext fun _ ↦ mul_left_comm _ _ _

lemma IsSmoothOnGL.mul {Φ₁ Φ₂ : GL (Fin 2) (mixedSpace F) → ℂ} (h₁ : IsSmoothOnGL Φ₁)
    (h₂ : IsSmoothOnGL Φ₂) : IsSmoothOnGL (Φ₁ * Φ₂) :=
  (ContDiffOn.mul h₁ h₂).congr fun m hm ↦ by
    simp only [extendGL_of_isUnit _ hm, Pi.mul_apply]

lemma IsSmoothAtInfinity.twist (h : IsSmoothAtInfinity φ) : IsSmoothAtInfinity (twist χ φ) :=
  fun g ↦ (isSmoothAtInfinity_charDet χ g).mul (h g)

variable (χ φ) in
lemma lieDeriv_twist (b : Fin 3) (y : mixedSpace F) :
    lieDeriv b y (twist χ φ) = twist χ (lieDeriv b y φ) :=
  funext fun g ↦ by
    simp only [lieDeriv, twist, charDet_mul, charDet_sl2Exp, mul_one]
    exact deriv_const_mul_field _

lemma HasModerateGrowth.mul {φ₁ φ₂ : AdelicGL2 F → ℂ} (h₁ : HasModerateGrowth φ₁)
    (h₂ : HasModerateGrowth φ₂) : HasModerateGrowth (φ₁ * φ₂) := fun y ↦ by
  rcases h₁ y with ⟨C₁, n₁, hC₁⟩
  rcases h₂ y with ⟨C₂, n₂, hC₂⟩
  refine ⟨|C₁| * |C₂|, n₁ + n₂, fun x ↦ ?_⟩
  have hp : 0 ≤ infHeight x := (zero_le_one).trans (one_le_infHeight x)
  rw [Pi.mul_apply, norm_mul, pow_add, mul_mul_mul_comm]
  exact mul_le_mul ((hC₁ x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hp _)))
    ((hC₂ x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hp _))) (norm_nonneg _)
    (mul_nonneg (abs_nonneg _) (pow_nonneg hp _))

variable (χ) in
/-- **The twist of an automorphic form is an automorphic form**: `φ ⊗ χ` has central character
`ω χ²`. -/
lemma IsAutomorphicForm.twist (h : IsAutomorphicForm ω φ) :
    IsAutomorphicForm (ω * χ ^ 2) (twist χ φ) where
  left_invariant γ g := by
    simp only [AdelicGL2.twist, charDet_mul, charDet_ofGlobal, one_mul, h.left_invariant]
  central z g := by
    simp only [AdelicGL2.twist, charDet_mul, charDet_scalar, h.central]
    simp only [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val]
    ring1
  smooth := h.smooth.twist
  exists_openSubgroup := by
    rcases h.exists_openSubgroup with ⟨U, hU⟩
    rcases exists_openSubgroup_charDet χ with ⟨V, hV⟩
    refine ⟨U ⊓ V, fun u hu g ↦ ?_⟩
    rw [AdelicGL2.twist, charDet_mul, hV u hu.2, mul_one, hU u hu.1]
    rfl
  kFinite := IsKFinite.map (twistₗ χ) (fun k ↦ ⟨charDet χ (ofInf F (Unitary.toUnits k)),
    funext fun g ↦ by
      simp only [twistₗ, LinearMap.coe_mk, AddHom.coe_mk, AdelicGL2.twist,
        AdelicGL2.rightTranslate, charDet_mul, Pi.smul_apply, smul_eq_mul]
      ring1⟩) h.kFinite
  casimirFinite := IsCasimirFinite.map (twistₗ χ) (fun _ hψ ↦ hψ.twist)
    (fun b y ψ ↦ lieDeriv_twist χ ψ b y) h.casimirFinite
  moderateGrowth := (hasModerateGrowth_charDet χ).mul h.moderateGrowth

variable (χ φ) in
lemma constantTerm_twist : constantTerm (twist χ φ) g = charDet χ g * constantTerm φ g := by
  have h (a : 𝔸[F]) : charDet χ (unipotent a) = 1 := by
    have hd : GeneralLinearGroup.det (unipotent a) = 1 := by
      refine Units.ext ?_
      simp [unipotent, GeneralLinearGroup.det, GeneralLinearGroup.upperRightHom]
    rw [charDet, hd]
    simp
  simp only [constantTerm, twist, charDet_mul, h, one_mul]
  exact MeasureTheory.integral_const_mul _ _

variable (χ) in
/-- **The twist of a cusp form is a cusp form.** -/
lemma IsCuspidal.twist (h : IsCuspidal φ) : IsCuspidal (twist χ φ) := fun g ↦ by
  rw [constantTerm_twist, h g, mul_zero]

end AdelicGL2
