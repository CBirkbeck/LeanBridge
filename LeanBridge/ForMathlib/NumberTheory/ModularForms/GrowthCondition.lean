import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The growth condition of modular forms

A modular form `f` on the upper half-plane satisfies a growth condition which restricts the growth
of `f(z)`, `z = x + iy`, as `y → ∞` (LMFDB `mf.growth_condition`), after moving any cusp to `∞`.
The condition that covers both holomorphic forms and Maass forms is **moderate growth**:
`f(z) = O(y^a)` as `y → ∞` for some real `a`. For a holomorphic periodic function it is equivalent
to boundedness as `y → ∞`, the condition in Mathlib's definition of modular forms: in the
coordinate `q = e^{2πiz/h}`, `q` times a power of `log |q|` tends to `0`, so the singularity of the
cusp function at `q = 0` is removable. Hence the modular forms of weight `k` for an arithmetic
subgroup `Γ` are exactly the holomorphic functions `f` with `f ∣[k] γ = f` for `γ ∈ Γ` whose
translates `f ∣[k] γ`, `γ ∈ SL(2, ℤ)`, have moderate growth at `i∞`.

LeanBridge's `UpperHalfPlane.isBoundedAtImInfty_of_periodic_of_le_pow` (in the files on Weil's
converse theorem) is the same removable singularity under a pointwise bound on a vertical strip;
here the hypothesis is the asymptotic bound along `atImInfty`, the filter of Mathlib's
`UpperHalfPlane.IsBoundedAtImInfty`.

## Main definitions

* `UpperHalfPlane.IsModerateGrowthAtImInfty` (LMFDB `mf.growth_condition`): moderate growth at
  `i∞`.

## Main results

* `UpperHalfPlane.isBoundedAtImInfty_of_tendsto_mul_qParam`: a holomorphic `h`-periodic function
  `f` with `f(z) e^{2πiz/h} → 0` at `i∞` is bounded there.
* `UpperHalfPlane.isBoundedAtImInfty_of_isModerateGrowthAtImInfty`: a holomorphic periodic function
  of moderate growth at `i∞` is bounded there.
* `UpperHalfPlane.isModerateGrowthAtImInfty_iff_isBoundedAtImInfty` (LMFDB `mf.growth_condition`):
  for holomorphic periodic functions, moderate growth at `i∞` is boundedness there.
* `ModularForm.exists_coe_eq_iff_forall_isModerateGrowthAtImInfty` (LMFDB `mf.growth_condition`):
  for an arithmetic subgroup `Γ`, a holomorphic function invariant under the weight `k` action of
  `Γ` is a modular form exactly when it has moderate growth at every cusp.
-/

open UpperHalfPlane Filter Asymptotics Function Complex OnePoint Matrix SpecialLinearGroup ConjAct
  Subgroup

open scoped Topology Real ModularForm Manifold MatrixGroups Pointwise

namespace UpperHalfPlane

variable {f : ℍ → ℂ} {h a : ℝ}

variable (f) in
/-- A function `f` on the upper half-plane has **moderate growth at `i∞`** (LMFDB
`mf.growth_condition`) if `f(z) = O(y^a)` as `y = Im z → ∞`, for some real `a`. This is the growth
condition of Maass forms at a cusp moved to `∞`; for holomorphic periodic functions, such as the
translates of modular forms, it is equivalent to boundedness
(`isModerateGrowthAtImInfty_iff_isBoundedAtImInfty`). -/
def IsModerateGrowthAtImInfty : Prop :=
  ∃ a : ℝ, f =O[atImInfty] fun z ↦ z.im ^ a

lemma IsBoundedAtImInfty.isModerateGrowthAtImInfty (hf : IsBoundedAtImInfty f) :
    IsModerateGrowthAtImInfty f :=
  ⟨0, hf.trans (isBigO_of_le _ fun z ↦ by simp)⟩

lemma tendsto_mul_qParam (hh : 0 < h) (hf : f =O[atImInfty] fun z ↦ z.im ^ a) :
    Tendsto (fun z : ℍ ↦ f z * Periodic.qParam h z) atImInfty (𝓝 0) := by
  have hq : (fun z : ℍ ↦ Periodic.qParam h z) =O[atImInfty]
      fun z ↦ Real.exp (-(2 * π / h) * z.im) :=
    isBigO_of_le _ fun z ↦ by
      rw [Periodic.norm_qParam, Real.norm_of_nonneg (Real.exp_pos _).le, coe_im]
      exact le_of_eq (congrArg Real.exp (by ring1))
  exact (hf.mul hq).trans_tendsto <|
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a (2 * π / h) (by positivity)).comp
      (tendsto_comap : Tendsto im atImInfty atTop)

/-- **A holomorphic periodic function `f` with `f(z) e^{2πiz/h} → 0` at `i∞` is bounded there**:
if `f` is holomorphic on `ℍ` and `h`-periodic with `h > 0`, its cusp function `F`, with
`f(z) = F(e^{2πiz/h})`, then satisfies `q F(q) → 0` as `q → 0`, so `F` extends holomorphically to
`0` (Riemann's removable singularity theorem), and `f` tends to `F(0)` at `i∞`. -/
lemma isBoundedAtImInfty_of_tendsto_mul_qParam (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hf : Tendsto (fun z : ℍ ↦ f z * Periodic.qParam h z) atImInfty (𝓝 0)) :
    IsBoundedAtImInfty f := by
  have hd : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1 \ {0}) := by
    rintro q ⟨hq, hq0⟩
    exact (Periodic.qParam_right_inv hh.ne' hq0 ▸ hfper.differentiableAt_cuspFunction hh.ne' <|
      UpperHalfPlane.mdifferentiableAt_iff.mp <| hfhol ⟨_, Periodic.im_invQParam_pos_of_norm_lt_one
        hh (mem_ball_zero_iff.mp hq) hq0⟩).differentiableWithinAt
  have ho : cuspFunction h f =o[𝓝[≠] 0] fun q ↦ q⁻¹ := by
    refine isLittleO_iff_tendsto' (eventually_nhdsWithin_of_forall fun q hq h0 ↦
      absurd (inv_eq_zero.mp h0) hq) |>.mpr <| (hf.comp <|
        tendsto_comap_im_ofComplex.comp (Periodic.invQParam_tendsto hh)).congr' ?_
    filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds 0 one_pos),
      self_mem_nhdsWithin] with q hq hq0
    rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
    simp only [Function.comp_apply]
    rw [ofComplex_apply_of_im_pos (Periodic.im_invQParam_pos_of_norm_lt_one hh
      (mem_ball_zero_iff.mp hq.2) hq0), coe_mk, Periodic.qParam_right_inv hh.ne' hq0,
      div_inv_eq_mul]
  have hc : (fun _ ↦ cuspFunction h f 0) =o[𝓝[≠] (0 : ℂ)] fun q ↦ q⁻¹ :=
    isLittleO_const_left.mpr (Or.inr tendsto_norm_inv_nhdsNE_zero_atTop)
  have h0 : cuspFunction h f 0 = limUnder (𝓝[≠] 0) (cuspFunction h f) :=
    Periodic.cuspFunction_zero_eq_limUnder_nhds_ne h (f ∘ ofComplex)
  have hdiff : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) := by
    rw [← update_eq_self 0 (cuspFunction h f), h0]
    exact differentiableOn_update_limUnder_of_isLittleO (Metric.ball_mem_nhds 0 one_pos) hd
      (by simpa only [sub_zero] using ho.sub hc)
  refine Tendsto.isBigO_one ℝ (c := cuspFunction h f 0) <|
    ((hdiff.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt.tendsto.comp
      (qParam_tendsto_atImInfty hh)).congr fun z ↦ ?_
  exact eq_cuspFunction z hh.ne' hfper

/-- **A holomorphic periodic function of moderate growth at `i∞` is bounded there**: if `f` is
holomorphic on `ℍ`, `h`-periodic with `h > 0` and `f(z) = O(y^a)` as `y → ∞`, then
`f(z) e^{2πiz/h} → 0`, so `f` is bounded at `i∞` by
`isBoundedAtImInfty_of_tendsto_mul_qParam`. -/
lemma isBoundedAtImInfty_of_isModerateGrowthAtImInfty (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hf : IsModerateGrowthAtImInfty f) :
    IsBoundedAtImInfty f :=
  hf.elim fun _ ha ↦ isBoundedAtImInfty_of_tendsto_mul_qParam hh hfper hfhol
    (tendsto_mul_qParam hh ha)

/-- **For holomorphic periodic functions, moderate growth at `i∞` is boundedness there** (LMFDB
`mf.growth_condition`): so the growth condition `f(z) = O(y^a)` of Maass forms, read on holomorphic
forms, is the boundedness at the cusps of Mathlib's modular forms. -/
lemma isModerateGrowthAtImInfty_iff_isBoundedAtImInfty (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) :
    IsModerateGrowthAtImInfty f ↔ IsBoundedAtImInfty f :=
  ⟨isBoundedAtImInfty_of_isModerateGrowthAtImInfty hh hfper hfhol,
    IsBoundedAtImInfty.isModerateGrowthAtImInfty⟩

end UpperHalfPlane

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} {f : ℍ → ℂ}

lemma isModerateGrowthAtImInfty_slash_iff (hf : ∀ g ∈ Γ, f ∣[k] g = f) (hfhol : MDiff f)
    (γ : SL(2, ℤ)) : IsModerateGrowthAtImInfty (f ∣[k] γ) ↔ IsBoundedAtImInfty (f ∣[k] γ) := by
  have : (toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl)] using! IsArithmetic.conj Γ (mapGL ℚ γ)⁻¹
  rw [SL_slash]
  exact isModerateGrowthAtImInfty_iff_isBoundedAtImInfty
    (toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ).strictWidthInfty_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex
      (SlashInvariantForm.translate (⟨f, hf⟩ : SlashInvariantForm Γ k) γ)
      (toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ).strictWidthInfty_mem_strictPeriods)
    (hfhol.slash k γ)

/-- **Modular forms are the holomorphic invariant functions of moderate growth at the cusps**
(LMFDB `mf.growth_condition`): for an arithmetic subgroup `Γ` of `GL(2, ℝ)`, a holomorphic function
`f` with `f ∣[k] g = f` for every `g ∈ Γ` is a modular form of weight `k` for `Γ` exactly when
`f ∣[k] γ` has moderate growth at `i∞` for every `γ ∈ SL(2, ℤ)`, that is, at every cusp. -/
lemma exists_coe_eq_iff_forall_isModerateGrowthAtImInfty (hf : ∀ g ∈ Γ, f ∣[k] g = f)
    (hfhol : MDiff f) :
    (∃ F : ModularForm Γ k, ⇑F = f) ↔ ∀ γ : SL(2, ℤ), IsModerateGrowthAtImInfty (f ∣[k] γ) := by
  refine ⟨?_, fun h ↦ ⟨⟨⟨f, hf⟩, hfhol, fun hc ↦ ?_⟩, rfl⟩⟩
  · rintro ⟨F, rfl⟩ γ
    exact (ModularFormClass.bdd_at_infty_slash F γ).isModerateGrowthAtImInfty
  · rw [IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    exact (isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
      (isModerateGrowthAtImInfty_slash_iff hf hfhol γ).mp (h γ)

end ModularForm
