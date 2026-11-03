import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.CoefficientIntegrality
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisActionOnNewforms
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbitLabel
import Mathlib.NumberTheory.LSeries.Injectivity
import TauCeti.NumberTheory.ModularForms.LFunction.Basic

/-!
# Invariants of Galois orbits of newforms, in every weight

The Galois conjugates of a newform being newforms, and its coefficient field a number field, in
every weight, the following results of `Newform/TraceBoundExists.lean`,
`Newform/GaloisOrbitLabel.lean` and `Newform/Embedding.lean` hold without assumption.

* The trace of the coefficient `aₙ` from the coefficient field of `f` down to `ℚ` is an integer, the
  sum of `aₙ` over the Galois orbit of `f`. The traces of finitely many coefficients distinguish
  the Galois orbits, so that the trace bound (LMFDB `cmf.trace_bound`) is the least such number of
  coefficients. The trace of `a₁` is the dimension of the newform.
* Distinct Galois orbits in a space of newforms thus have distinct trace sequences, and the letter
  labels (LMFDB `cmf.hecke_galois_orbit`) of the `m` orbits of a space are the letter codes of
  `0, …, m - 1`.
* Distinct embeddings of a newform have distinct `L`-functions, and two embeddings have the same
  Dirichlet character exactly when they agree on the field of values of the nebentypus
  (LMFDB `cmf.embedding`).

## Main results

* `HeckeRing.GL2.Newform.coeffTrace_eq_sum_galoisOrbit`: `Tr(aₙ(f))` is the sum of `aₙ` over the
  Galois orbit.
* `HeckeRing.GL2.Newform.exists_int_coeffTrace_of_newform`: the traces of the coefficients are
  integers.
* `HeckeRing.GL2.Newform.isGaloisConjugate_of_forall_coeffTrace_eq`: newforms whose coefficients
  have the same traces are Galois conjugate.
* `HeckeRing.GL2.Newform.exists_tracesDistinguish`,
  `HeckeRing.GL2.Newform.traceBound_pos_of_newform`,
  `HeckeRing.GL2.Newform.tracesDistinguish_traceBound`: the trace bound exists.
* `HeckeRing.GL2.Newform.coeffTrace_one_eq_dimension`,
  `HeckeRing.GL2.Newform.traceBound_eq_one_of_dimension`: the trace of `a₁` is the dimension, and
  the trace bound is `1` when the dimensions distinguish the Galois orbits of the space.
* `HeckeRing.GL2.NewformOrbit.traceSeq_injective`, `HeckeRing.GL2.NewformOrbit.labelIndex_eq_iff`,
  `HeckeRing.GL2.NewformOrbit.letterLabel_eq_iff`, `HeckeRing.GL2.NewformOrbit.image_labelIndex`:
  distinct orbits of a space have distinct trace sequences, positions and labels, and the positions
  of the `m` orbits of a space are `0, …, m - 1`.
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

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k} (χ : (ZMod N)ˣ →* ℂˣ)

variable (f) in
/-- **The trace of a coefficient is its sum over the Galois orbit**, in every weight:
`Tr_{ℚ(f)/ℚ}(aₙ(f)) = ∑_{g ∈ [f]} aₙ(g)`. -/
lemma coeffTrace_eq_sum_galoisOrbit (n : ℕ) : (f.coeffTrace n : ℂ) =
    ∑ g ∈ f.finite_galoisOrbit.toFinset, (qExpansion 1 g.toCuspForm).coeff n := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), coeffTrace, trace_eq_sum_embeddings]
  symm
  refine Finset.sum_bij (fun g hg ↦ f.galoisOrbitEmbedding ⟨g, by simpa using hg⟩)
    (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro g _ g' _ h
    simpa using f.galoisOrbitEmbedding_injective h
  · intro ι _
    rcases f.galoisOrbitEmbedding_bijective.2 ι with ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, by simpa using hg, rfl⟩
  · intro g hg
    exact (isEmbedding_galoisOrbitEmbedding ⟨g, by simpa using hg⟩).coeff n

variable (f) in
/-- **The traces of the coefficients of a newform are integers**, in every weight
(LMFDB `cmf.hecke_galois_orbit`): the coefficients are algebraic integers. -/
lemma exists_int_coeffTrace_of_newform (n : ℕ) : ∃ m : ℤ, f.coeffTrace n = m := by
  have hn : IsIntegral ℤ (f.orbitQExpansion.coeff n) :=
    (isIntegral_algHom_iff (CoefficientField f).val.toIntAlgHom Subtype.val_injective).mp <| by
      simpa using f.isIntegral_coeff n
  rcases IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hn) with ⟨m, hm⟩
  exact ⟨m, by rw [coeffTrace, ← hm, eq_intCast]⟩

/-- **The traces of the coefficients distinguish the Galois orbits**, in every weight: newforms `f`
and `g` with `Tr(aₙ(f)) = Tr(aₙ(g))` for all `n ≥ 1` are Galois conjugate. Otherwise the sums of
their Galois orbits would have the same `q`-expansion, against the linear independence of
newforms. -/
lemma isGaloisConjugate_of_forall_coeffTrace_eq (h : ∀ n, 0 < n → f.coeffTrace n = g.coeffTrace n) :
    f.IsGaloisConjugate g := by
  classical
  let : Fintype (Newform N k) := Fintype.ofFinite _
  let L : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] PowerSeries ℂ :=
    { toFun x := qExpansion 1 x
      map_add' x y := ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map N) x y
      map_smul' a x :=
        ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N) a x }
  have hL : LinearIndependent ℂ fun x : Newform N k ↦ L x.toCuspForm :=
    linearIndependent_toCuspForm.map' L <| LinearMap.ker_eq_bot.mpr <|
      CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N)
  by_contra hfg
  have hc : ((if f ∈ f.finite_galoisOrbit.toFinset then 1 else 0) -
      if f ∈ g.finite_galoisOrbit.toFinset then 1 else 0 : ℂ) = 0 :=
    Fintype.linearIndependent_iff.mp hL (fun x ↦
      (if x ∈ f.finite_galoisOrbit.toFinset then 1 else 0) -
        if x ∈ g.finite_galoisOrbit.toFinset then 1 else 0) ?_ f
  · simp [mem_galoisOrbit, isGaloisConjugate_comm, hfg, IsGaloisConjugate.refl] at hc
  · refine PowerSeries.ext fun n ↦ ?_
    simp only [sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib,
      Finset.sum_ite_mem, Finset.univ_inter, map_sub, map_sum, map_zero]
    rcases n with _ | n
    · simp [L, CuspFormClass.qExpansion_coeff_zero _ one_pos (one_mem_strictPeriods_Gamma1_map N)]
    · rw [sub_eq_zero]
      exact (f.coeffTrace_eq_sum_galoisOrbit _).symm.trans <| by
        rw [h _ n.succ_pos, g.coeffTrace_eq_sum_galoisOrbit]
        rfl

/-- **The trace bound exists**, in every weight: the traces of the first `m` coefficients
distinguish the Galois orbits of newforms of nebentypus `χ` for some `m ≥ 1`. So `traceBound N k χ`
is the least such `m`, and not the junk value `0`. -/
lemma exists_tracesDistinguish : ∃ m, 0 < m ∧ TracesDistinguishNewforms N k χ m := by
  let : Fintype (Newform N k) := Fintype.ofFinite _
  have hn : ∀ p : Newform N k × Newform N k,
      ∃ n, 0 < n ∧ (p.1.IsGaloisConjugate p.2 ∨ p.1.coeffTrace n ≠ p.2.coeffTrace n) := by
    intro p
    by_cases hp : p.1.IsGaloisConjugate p.2
    · exact ⟨1, one_pos, .inl hp⟩
    · have hne : ¬∀ n, 0 < n → p.1.coeffTrace n = p.2.coeffTrace n :=
        fun H ↦ hp <| isGaloisConjugate_of_forall_coeffTrace_eq H
      push Not at hne
      rcases hne with ⟨n, hn, hne⟩
      exact ⟨n, hn, .inr hne⟩
  choose F hF0 hF using hn
  refine ⟨Finset.univ.sup F + 1, Nat.succ_pos _, fun f g _ _ hfg ↦ ?_⟩
  rcases hF (f, g) with h | h
  · exact h
  · exact absurd (hfg _ ⟨hF0 (f, g), (Finset.le_sup (Finset.mem_univ (f, g))).trans
      (Nat.le_succ _)⟩) h

/-- **The trace bound is positive** (LMFDB `cmf.trace_bound`). -/
lemma traceBound_pos_of_newform : 0 < traceBound N k χ :=
  traceBound_pos (exists_tracesDistinguish χ)

/-- **The traces of the coefficients `aₙ` for `n` up to the trace bound distinguish the Galois
orbits** of the newforms of nebentypus `χ` (LMFDB `cmf.trace_bound`). -/
lemma tracesDistinguish_traceBound : TracesDistinguishNewforms N k χ (traceBound N k χ) :=
  tracesDistinguishNewforms_traceBound (exists_tracesDistinguish χ)

variable (f) in
/-- **The trace of `a₁ = 1` is the dimension of the newform** (LMFDB `cmf.trace_bound`). -/
lemma coeffTrace_one_eq_dimension : f.coeffTrace 1 = f.dimension := by
  rw [coeffTrace_one, dimension_eq_finrank_coefficientField]

variable {χ} in
/-- **The trace bound is `1` when the dimensions distinguish the Galois orbits** of the newforms of
nebentypus `χ` (LMFDB `cmf.trace_bound`). -/
lemma traceBound_eq_one_of_dimension (h : ∀ f g : Newform N k, f.χ = χ → g.χ = χ →
    f.dimension = g.dimension → f.IsGaloisConjugate g) : traceBound N k χ = 1 :=
  traceBound_eq_one fun f g hf hg hfg ↦ h f g hf hg <| by
    rw [dimension_eq_finrank_coefficientField, dimension_eq_finrank_coefficientField, hfg]

end HeckeRing.GL2.Newform

namespace HeckeRing.GL2.NewformOrbit

variable {N : ℕ} [NeZero N] {k : ℤ} (O : NewformOrbit N k) {O' : NewformOrbit N k}

/-- **Distinct newform orbits have distinct trace sequences**, in every weight. -/
lemma traceSeq_injective : Function.Injective (traceSeq (N := N) (k := k)) := by
  intro O O'
  induction O using Quotient.inductionOn with | h f =>
  induction O' using Quotient.inductionOn with | h g =>
  intro h
  refine Quotient.sound <| Newform.isGaloisConjugate_of_forall_coeffTrace_eq fun n hn ↦ ?_
  have hfg : f.coeffTrace (n - 1 + 1) = g.coeffTrace (n - 1 + 1) :=
    congrFun (toLex.injective h) (n - 1)
  rwa [Nat.sub_add_cancel hn] at hfg

/-- **Distinct newform orbits of a space have distinct positions**, in every weight. -/
lemma labelIndex_eq_iff (h : O'.characterOrbit = O.characterOrbit) :
    O'.labelIndex = O.labelIndex ↔ O' = O := by
  refine ⟨fun hO ↦ ?_, fun hO ↦ hO ▸ rfl⟩
  rcases lt_trichotomy O'.traceSeq O.traceSeq with hlt | heq | hgt
  · exact absurd hO (labelIndex_lt_labelIndex O h hlt).ne
  · exact traceSeq_injective heq
  · exact absurd hO (labelIndex_lt_labelIndex O' h.symm hgt).ne'

/-- **Distinct newform orbits of a space have distinct letter labels**, in every weight
(LMFDB `cmf.hecke_galois_orbit`). -/
lemma letterLabel_eq_iff (h : O'.characterOrbit = O.characterOrbit) :
    O'.letterLabel = O.letterLabel ↔ O' = O :=
  DirichletCharacter.letterCode_injective.eq_iff.trans <| labelIndex_eq_iff O h

/-- **The positions of the newform orbits of a space are `0, …, m - 1`**, where `m` is the number of
orbits of the space, in every weight (LMFDB `cmf.hecke_galois_orbit`). -/
lemma image_labelIndex : labelIndex ''
    {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit} =
      Set.Iio {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit}.ncard := by
  have hmaps : Set.MapsTo labelIndex {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit}
      (Set.Iio {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit}.ncard) :=
    fun O' hO' ↦ (labelIndex_lt_ncard O').trans_eq <| by rw [Set.mem_ofPred_eq.mp hO']
  have hinj : Set.InjOn labelIndex {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit} :=
    fun O₁ h₁ O₂ h₂ h ↦ (labelIndex_eq_iff O₂
      ((Set.mem_ofPred_eq.mp h₁).trans (Set.mem_ofPred_eq.mp h₂).symm)).mp h
  refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr hmaps) ?_ (Set.toFinite _)
  rw [hinj.ncard_image, Set.ncard_Iio_nat]

end HeckeRing.GL2.NewformOrbit

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g g' : Newform N k} {ι ι' : CoefficientField f →ₐ[ℚ] ℂ}

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
