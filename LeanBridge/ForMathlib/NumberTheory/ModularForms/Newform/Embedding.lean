import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.ComplexAutomorphism
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisConjugate

/-!
# The `q`-expansion of a newform orbit and the embeddings of a newform

The coefficients `aₙ` of a newform `f` generate its coefficient field `K = ℚ(f)`, Tau Ceti's
`TauCeti.CoefficientField f`, a number field in weight at least two. The LMFDB `q`-expansion of the
newform orbit `[f]` (LMFDB `cmf.q-expansion`) is `∑ aₙ qⁿ` with coefficients in `K`, forgetting the
embedding `K ⊆ ℂ`, and each embedding `ι : K → ℂ` gives an *embedding* `ι(f) = ∑ ι(aₙ) qⁿ` of
`f` (LMFDB `cmf.embedding`).

Tau Ceti's newforms are complex, i.e. already embedded. Here `K` is the subfield `ℚ(f) ⊆ ℂ` viewed
as an abstract field, which is well defined on the orbit up to the isomorphisms
`IsGaloisConjugateBy.coefficientFieldEquiv`, and `ι(f)` is a complex newform `g` with `bₙ = ι(aₙ)`.
That such a newform exists for every `ι` is the theorem that Galois conjugates of newforms are
newforms, which is not proved here.

## Main definitions

* `HeckeRing.GL2.Newform.orbitQExpansion`: the `q`-expansion `∑ aₙ qⁿ ∈ K⟦q⟧` of the newform orbit
  of `f`, with coefficients in its coefficient field `K` (LMFDB `cmf.q-expansion`).
* `HeckeRing.GL2.Newform.IsEmbedding`: `g` is the embedding `ι(f)` of `f` by `ι : K → ℂ`
  (LMFDB `cmf.embedding`).

## Main results

* `HeckeRing.GL2.Newform.map_orbitQExpansion`: the embedding `K ⊆ ℂ` maps the `q`-expansion of the
  orbit to that of `f`.
* `HeckeRing.GL2.Newform.IsGaloisConjugateBy.map_orbitQExpansion`: the orbit `q`-expansion is the
  same for Galois conjugate newforms, up to the isomorphism of their coefficient fields.
* `HeckeRing.GL2.Newform.isGaloisConjugate_iff_exists_isEmbedding`: Galois conjugates of `f` are
  exactly its embeddings, by the extension of embeddings of countable subfields of `ℂ` to
  automorphisms of `ℂ`; equivalently, Galois conjugacy through `Gal(ℂ/ℚ)` is conjugacy through
  embeddings of the coefficient field.
* `HeckeRing.GL2.Newform.IsEmbedding.unique`, `HeckeRing.GL2.Newform.IsEmbedding.algHom_eq`: an
  embedding `ι` determines the newform `ι(f)` of a given level and weight, and conversely.
* `HeckeRing.GL2.Newform.IsEmbedding.χ_apply`: the nebentypus of `ι(f)` is `ι ∘ χ`, so that the
  embeddings of `f` fall into blocks by the embedding of the character field that they induce.
-/

open UpperHalfPlane TauCeti Cardinal

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {σ : Gal(ℂ/ℚ)} {f : Newform N k}

instance : Countable (CoefficientField f) := by
  rw [CoefficientField_def, ← mk_le_aleph0_iff]
  exact (IntermediateField.cardinalMk_adjoin_le ℚ _).trans <|
    sup_le (sup_le mk_le_aleph0 (Set.countable_range _).le_aleph0) le_rfl

variable (f) in
lemma qExpansion_coeff_mem_coefficientField (n : ℕ) :
    (qExpansion 1 f.toCuspForm).coeff n ∈ CoefficientField f := by
  rcases n with _ | n
  · rw [CuspFormClass.qExpansion_coeff_zero f.toCuspForm one_pos
      (one_mem_strictPeriods_Gamma1_map N)]
    exact zero_mem _
  · exact coeff_mem_CoefficientField f n.succPNat

variable (f) in
/-- The **`q`-expansion of the newform orbit** of `f` (LMFDB `cmf.q-expansion`): the `q`-expansion
`∑ aₙ qⁿ` of `f`, with coefficients in its coefficient field `K = ℚ(f)` regarded as an abstract
field, without its embedding into `ℂ`. The LMFDB defines it as the `q`-expansion of any newform in
the orbit; it does not depend on that newform up to the isomorphism of coefficient fields
(`IsGaloisConjugateBy.map_orbitQExpansion`). -/
noncomputable def orbitQExpansion : PowerSeries (CoefficientField f) :=
  PowerSeries.mk fun n ↦ ⟨_, f.qExpansion_coeff_mem_coefficientField n⟩

@[simp]
lemma coe_coeff_orbitQExpansion (n : ℕ) :
    (f.orbitQExpansion.coeff n : ℂ) = (qExpansion 1 f.toCuspForm).coeff n := by
  simp [orbitQExpansion]

variable (f) in
/-- **The orbit `q`-expansion recovers the `q`-expansion of `f`** through the embedding
`ℚ(f) ⊆ ℂ`. -/
lemma map_orbitQExpansion :
    PowerSeries.map (CoefficientField f).val f.orbitQExpansion = qExpansion 1 f.toCuspForm := by
  ext n
  simp

section

variable {N' : ℕ} [NeZero N'] {k' : ℤ} {g : Newform N' k'}

/-- **The orbit `q`-expansion is the same along the orbit**: if `g = σ(f)`, the isomorphism
`ℚ(f) ≃ ℚ(g)` induced by `σ` maps the `q`-expansion of the orbit of `f` to that of the orbit of
`g`. -/
lemma IsGaloisConjugateBy.map_orbitQExpansion (hfg : f.IsGaloisConjugateBy σ g) :
    PowerSeries.map hfg.coefficientFieldEquiv f.orbitQExpansion = g.orbitQExpansion := by
  ext n
  simp [hfg.coeff]

variable (f g) in
/-- For an embedding `ι : ℚ(f) → ℂ` of the coefficient field of the newform `f`, the newform `g` is
the **embedding** `ι(f)` of `f` (LMFDB `cmf.embedding`) if its `q`-expansion is `∑ ι(aₙ) qⁿ`, the
`q`-expansion of the orbit of `f` with `ι` applied to its coefficients. -/
def IsEmbedding (ι : CoefficientField f →ₐ[ℚ] ℂ) : Prop :=
  qExpansion 1 g.toCuspForm = PowerSeries.map ι f.orbitQExpansion

variable {ι ι' : CoefficientField f →ₐ[ℚ] ℂ}

lemma isEmbedding_iff : f.IsEmbedding g ι ↔ ∀ n : ℕ, (qExpansion 1 g.toCuspForm).coeff n =
    ι (f.orbitQExpansion.coeff n) := by
  simp [IsEmbedding, PowerSeries.ext_iff]

lemma IsEmbedding.coeff (hι : f.IsEmbedding g ι) (n : ℕ) :
    (qExpansion 1 g.toCuspForm).coeff n = ι (f.orbitQExpansion.coeff n) :=
  isEmbedding_iff.mp hι n

lemma IsGaloisConjugateBy.isEmbedding (hfg : f.IsGaloisConjugateBy σ g) :
    f.IsEmbedding g ((σ : ℂ →ₐ[ℚ] ℂ).comp (CoefficientField f).val) :=
  isEmbedding_iff.mpr fun n ↦ by simp [hfg.coeff]

lemma IsEmbedding.isGaloisConjugateBy (hι : f.IsEmbedding g ι)
    (hσ : ∀ x : CoefficientField f, σ x = ι x) : f.IsGaloisConjugateBy σ g :=
  isGaloisConjugateBy_iff.mpr fun n ↦ by rw [hι.coeff, ← hσ, coe_coeff_orbitQExpansion]

lemma IsEmbedding.isGaloisConjugate (hι : f.IsEmbedding g ι) : f.IsGaloisConjugate g :=
  (IntermediateField.exists_algEquiv_apply_eq_of_countable ι).elim fun _ hσ ↦
    (hι.isGaloisConjugateBy hσ).isGaloisConjugate

/-- **The Galois conjugates of `f` are its embeddings**: `g` is Galois conjugate to `f`, by an
automorphism of `ℂ`, exactly when it is the embedding `ι(f)` for some embedding `ι` of the
coefficient field of `f`. Every embedding of the countable field `ℚ(f)` extends to an automorphism
of `ℂ`, by `IntermediateField.exists_algEquiv_apply_eq_of_countable`. -/
lemma isGaloisConjugate_iff_exists_isEmbedding : f.IsGaloisConjugate g ↔ ∃ ι, f.IsEmbedding g ι :=
  ⟨fun ⟨_, hσ⟩ ↦ ⟨_, hσ.isEmbedding⟩, fun ⟨_, hι⟩ ↦ hι.isGaloisConjugate⟩

/-- **The newform `ι(f)` determines `ι`**: two embeddings of the coefficient field giving the same
newform are equal, as they agree on the coefficients that generate it. -/
lemma IsEmbedding.algHom_eq (hι : f.IsEmbedding g ι) (hι' : f.IsEmbedding g ι') : ι = ι' :=
  IntermediateField.algHom_ext_of_eq_adjoin ℚ (CoefficientField_def f) <| by
    rintro _ ⟨n, rfl⟩
    have h : f.orbitQExpansion.coeff n = ⟨_, coeff_mem_CoefficientField f n⟩ :=
      Subtype.ext (coe_coeff_orbitQExpansion n)
    rw [← h, ← hι.coeff, ← hι'.coeff]

/-- **The embedding `ι` determines the newform `ι(f)`**: at most one newform of a given level and
weight is the embedding `ι(f)`. -/
lemma IsEmbedding.unique {g' : Newform N' k'} (hι : f.IsEmbedding g ι) (hι' : f.IsEmbedding g' ι) :
    g = g' :=
  Newform.ext <| CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N') <|
    hι.trans hι'.symm

end

variable {g : Newform N k} {ι : CoefficientField f →ₐ[ℚ] ℂ}

/-- **The nebentypus of `ι(f)` is `ι ∘ χ`**: the embedding `ι(f)` of a newform `f` of nebentypus
`χ` has nebentypus `ι ∘ χ`, which only depends on the embedding of the character field `ℚ(χ)`
induced by `ι`. -/
lemma IsEmbedding.χ_apply (hι : f.IsEmbedding g ι) (u : (ZMod N)ˣ) :
    (g.χ u : ℂ) = ι ⟨f.χ u, char_mem_CoefficientField f u⟩ :=
  (IntermediateField.exists_algEquiv_apply_eq_of_countable ι).elim fun _ hσ ↦ by
    rw [(hι.isGaloisConjugateBy hσ).χ_apply, ← hσ]

end HeckeRing.GL2.Newform
