import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Dimension
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbitLabel
import Mathlib.NumberTheory.LSeries.Injectivity
import TauCeti.NumberTheory.ModularForms.LFunction.Basic

/-!
# Invariants of Galois orbits of newforms

The Galois conjugates of a newform being newforms, and its coefficient field a number field, in
every weight, the following hold.

* The trace of `a₁` from the coefficient field of `f` down to `ℚ` is the dimension of the newform,
  so the trace bound (LMFDB `cmf.trace_bound`) is `1` when the dimensions distinguish the Galois
  orbits of a space of newforms.
* Distinct embeddings of a newform have distinct `L`-functions, and two embeddings have the same
  Dirichlet character exactly when they agree on the field of values of the nebentypus
  (LMFDB `cmf.embedding`).

## Main results

* `HeckeRing.GL2.Newform.coeffTrace_one_eq_dimension`,
  `HeckeRing.GL2.Newform.traceBound_eq_one_of_dimension`: the trace of `a₁` is the dimension, and
  the trace bound is `1` when the dimensions distinguish the Galois orbits of the space.
* `HeckeRing.GL2.Newform.LSeries_coeff_injective`, `HeckeRing.GL2.Newform.IsEmbedding.LSeries_ne`:
  distinct newforms of a given level and weight, and distinct embeddings of a newform, have distinct
  `L`-functions.
* `HeckeRing.GL2.Newform.IsEmbedding.χ_eq_iff`,
  `HeckeRing.GL2.Newform.IsEmbedding.dirichletLift_mem_galoisOrbit`: the embeddings of a newform
  fall into blocks by the embedding of the field of values of its nebentypus that they induce, and
  the characters of two blocks are Galois conjugate.
-/

open UpperHalfPlane TauCeti CongruenceSubgroup LSeries Matrix SpecialLinearGroup

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g g' : Newform N k} {χ : (ZMod N)ˣ →* ℂˣ}
  {ι ι' : CoefficientField f →ₐ[ℚ] ℂ}

variable (f) in
/-- **The trace of `a₁ = 1` is the dimension of the newform** (LMFDB `cmf.trace_bound`). -/
lemma coeffTrace_one_eq_dimension : f.coeffTrace 1 = f.dimension := by
  rw [coeffTrace_one, dimension_eq_finrank]

/-- **The trace bound is `1` when the dimensions distinguish the Galois orbits** of the newforms of
nebentypus `χ` (LMFDB `cmf.trace_bound`). -/
lemma traceBound_eq_one_of_dimension (h : ∀ f g : Newform N k, f.χ = χ → g.χ = χ →
    f.dimension = g.dimension → f.IsGaloisConjugate g) : traceBound N k χ = 1 :=
  traceBound_eq_one fun f g hf hg hfg ↦ h f g hf hg <| by
    rw [dimension_eq_finrank, dimension_eq_finrank, hfg]

variable (g) in
lemma abscissaOfAbsConv_coeff_lt_top :
    abscissaOfAbsConv (fun n ↦ (qExpansion 1 g.toCuspForm).coeff n) < ⊤ := by
  have h : abscissaOfAbsConv (fun n ↦ (qExpansion ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty
      g.toCuspForm).coeff n) ≤ (((k : ℝ) / 2 : ℝ) : EReal) + 1 :=
    CuspForm.abscissaOfAbsConv_qExpansion_coeff_le g.toCuspForm
  rw [strictWidthInfty_Gamma1] at h
  exact h.trans_lt (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top 1))

/-- **Distinct newforms of a given level and weight have distinct `L`-functions**
(LMFDB `cmf.embedding`). -/
lemma LSeries_coeff_injective : Function.Injective fun g : Newform N k ↦
    LSeries fun n ↦ (qExpansion 1 g.toCuspForm).coeff n := by
  intro g g' h
  have hcoeff : ∀ n ≠ 0,
      (qExpansion 1 g.toCuspForm).coeff n = (qExpansion 1 g'.toCuspForm).coeff n :=
    (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top (abscissaOfAbsConv_coeff_lt_top g)
      (abscissaOfAbsConv_coeff_lt_top g')).mp h
  refine Newform.ext <| CuspForm.qExpansion_injective one_pos
    (one_mem_strictPeriods_Gamma1_map N) <| PowerSeries.ext fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [CuspFormClass.qExpansion_coeff_zero _ one_pos (one_mem_strictPeriods_Gamma1_map N),
      CuspFormClass.qExpansion_coeff_zero _ one_pos (one_mem_strictPeriods_Gamma1_map N)]
  · exact hcoeff n hn

/-- **Distinct embeddings of a newform have distinct `L`-functions** (LMFDB `cmf.embedding`). -/
lemma IsEmbedding.LSeries_ne (hι : f.IsEmbedding g ι) (hι' : f.IsEmbedding g' ι') (hne : ι ≠ ι') :
    (LSeries fun n ↦ (qExpansion 1 g.toCuspForm).coeff n) ≠
      LSeries fun n ↦ (qExpansion 1 g'.toCuspForm).coeff n := fun h ↦
  hne <| hι.algHom_eq <| (LSeries_coeff_injective h).symm ▸ hι'

/-- **The embeddings of a newform fall into blocks with the same Dirichlet character**
(LMFDB `cmf.embedding`): two embeddings of a newform have the same nebentypus exactly when they
induce the same embedding of the field of values of its nebentypus. -/
lemma IsEmbedding.χ_eq_iff (hι : f.IsEmbedding g ι) (hι' : f.IsEmbedding g' ι') : g.χ = g'.χ ↔
    ι.comp (IntermediateField.inclusion (CharacterField_le_CoefficientField f)) =
      ι'.comp (IntermediateField.inclusion (CharacterField_le_CoefficientField f)) := by
  refine ⟨fun h ↦ IntermediateField.algHom_ext_of_eq_adjoin ℚ (CharacterField_def f.χ) ?_,
    fun h ↦ MonoidHom.ext fun u ↦ Units.ext ?_⟩
  · rintro _ ⟨u, rfl⟩
    have h₁ : (g.χ u : ℂ) = ι ⟨f.χ u, char_mem_CoefficientField f u⟩ := hι.χ_apply u
    have h₂ : (g'.χ u : ℂ) = ι' ⟨f.χ u, char_mem_CoefficientField f u⟩ := hι'.χ_apply u
    rw [h] at h₁
    exact h₁.symm.trans h₂
  · rw [hι.χ_apply, hι'.χ_apply]
    exact DFunLike.congr_fun h ⟨f.χ u, char_mem_CharacterField f.χ u⟩

/-- **The character of an embedding of a newform is Galois conjugate to its nebentypus**
(LMFDB `cmf.embedding`). -/
lemma IsEmbedding.dirichletLift_mem_galoisOrbit (hι : f.IsEmbedding g ι) :
    g.dirichletLift ∈ f.dirichletLift.galoisOrbit :=
  (IntermediateField.exists_algEquiv_apply_eq_of_countable ι).elim fun _ hσ ↦
    (hι.isGaloisConjugateBy hσ).dirichletLift_mem_galoisOrbit

end HeckeRing.GL2.Newform
