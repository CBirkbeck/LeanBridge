import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Embedding
import TauCeti.NumberTheory.ModularForms.Newforms.NumberField
import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis

/-!
# Galois orbits of newforms

The Galois orbit `[f] = {σ(f)}` of a newform `f` (LMFDB `cmf.galois_orbit`) is the set of its
Galois conjugates. Here it is the set of newforms of the level and weight of `f` that are Galois
conjugate to `f`. Every Galois conjugate `σ(f)` is a newform of the same level and weight, so this
is the LMFDB orbit; but that theorem is not proved here, so it is only known that the orbit consists
of the conjugates `σ(f)` that are newforms.

Galois orbits of newforms are also called newform orbits, and the LMFDB calls them newforms:
`HeckeRing.GL2.NewformOrbit N k` is the type of Galois orbits of newforms of level `N` and weight
`k`.

The LMFDB states that `[f]` has as many elements as the degree of the coefficient field `ℚ(f)`. Its
elements are the embeddings `ι(f)` of `f`, for distinct embeddings `ι : ℚ(f) → ℂ`, so in weight at
least two, where `ℚ(f)` is a number field, there are at most `[ℚ(f) : ℚ]` of them, with equality as
soon as every Galois conjugate of `f` is a newform.

## Main definitions

* `HeckeRing.GL2.Newform.galoisOrbit`: the Galois orbit of a newform (LMFDB `cmf.galois_orbit`).
* `HeckeRing.GL2.Newform.galoisOrbitRel`: Galois conjugacy, as an equivalence relation on newforms
  of a given level and weight.
* `HeckeRing.GL2.NewformOrbit`: the type of newform orbits (LMFDB `cmf.galois_orbit`), and
  `HeckeRing.GL2.Newform.newformOrbit`, the newform orbit of a newform.
* `HeckeRing.GL2.Newform.galoisOrbitEmbedding`: the embedding `ι : ℚ(f) → ℂ` with `g = ι(f)`, for
  `g` in the Galois orbit of `f`.

## Main results

* `HeckeRing.GL2.Newform.finite_galoisOrbit`: Galois orbits are finite.
* `HeckeRing.GL2.Newform.galoisOrbitEmbedding_injective`: distinct elements of the Galois orbit of
  `f` are embeddings of `f` by distinct embeddings of its coefficient field.
* `HeckeRing.GL2.Newform.ncard_galoisOrbit_le`: in weight at least two, the Galois orbit of `f` has
  at most `[ℚ(f) : ℚ]` elements.
* `HeckeRing.GL2.Newform.ncard_galoisOrbit_eq`: it has exactly `[ℚ(f) : ℚ]` elements if every
  Galois conjugate `σ(f)` is a newform.
-/

open UpperHalfPlane TauCeti

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k}

namespace Newform

variable (hk : 2 ≤ k) (hf : ∀ σ : Gal(ℂ/ℚ), ∃ g : Newform N k, f.IsGaloisConjugateBy σ g)

variable (f) in
/-- The **Galois orbit** `[f]` of a newform `f` (LMFDB `cmf.galois_orbit`): the set of newforms of
the same level and weight that are Galois conjugate to `f`. Galois conjugates of `f` are newforms
of its level and weight, so this is the LMFDB orbit `{σ(f) : σ ∈ Gal(ℚ̄/ℚ)}`, but that theorem is
not proved here. -/
def galoisOrbit : Set (Newform N k) :=
  {g | f.IsGaloisConjugate g}

variable (x : f.galoisOrbit)

lemma mem_galoisOrbit : g ∈ f.galoisOrbit ↔ f.IsGaloisConjugate g :=
  Iff.rfl

variable (f) in
lemma self_mem_galoisOrbit : f ∈ f.galoisOrbit :=
  IsGaloisConjugate.refl f

variable (f) in
lemma conj_mem_galoisOrbit : f.conj ∈ f.galoisOrbit :=
  f.isGaloisConjugate_conj

lemma galoisOrbit_eq_iff : f.galoisOrbit = g.galoisOrbit ↔ f.IsGaloisConjugate g :=
  ⟨fun h ↦ h.symm.subset g.self_mem_galoisOrbit, fun h ↦ Set.ext fun _ ↦ ⟨h.symm.trans, h.trans⟩⟩

lemma disjoint_galoisOrbit (h : ¬f.IsGaloisConjugate g) : Disjoint f.galoisOrbit g.galoisOrbit :=
  Set.disjoint_left.mpr fun _ hf hg ↦ h (hf.trans hg.symm)

variable (f) in
/-- **Galois orbits are finite**, as there are finitely many newforms of a given level and
weight. -/
lemma finite_galoisOrbit : f.galoisOrbit.Finite :=
  Set.toFinite _

variable (N k) in
/-- Galois conjugacy, as an equivalence relation on the newforms of level `N` and weight `k`. Its
classes are the Galois orbits. -/
def galoisOrbitRel : Setoid (Newform N k) where
  r f g := f.IsGaloisConjugate g
  iseqv := ⟨IsGaloisConjugate.refl, IsGaloisConjugate.symm, IsGaloisConjugate.trans⟩

lemma galoisOrbitRel_iff : galoisOrbitRel N k f g ↔ f.IsGaloisConjugate g :=
  Iff.rfl

variable (f) in
/-- The embedding `ι : ℚ(f) → ℂ` of the coefficient field of `f` such that `x = ι(f)`, for `x` in
the Galois orbit of `f`. -/
noncomputable def galoisOrbitEmbedding : CoefficientField f →ₐ[ℚ] ℂ :=
  (isGaloisConjugate_iff_exists_isEmbedding.mp x.2).choose

lemma isEmbedding_galoisOrbitEmbedding : f.IsEmbedding x.1 (f.galoisOrbitEmbedding x) :=
  (isGaloisConjugate_iff_exists_isEmbedding.mp x.2).choose_spec

variable (f) in
/-- **Distinct Galois conjugates come from distinct embeddings** of the coefficient field. -/
lemma galoisOrbitEmbedding_injective : Function.Injective f.galoisOrbitEmbedding :=
  fun g g' h ↦ Subtype.ext <| (isEmbedding_galoisOrbitEmbedding g).unique <|
    h ▸ isEmbedding_galoisOrbitEmbedding g'

include hf in
lemma galoisOrbitEmbedding_surjective : Function.Surjective f.galoisOrbitEmbedding := by
  intro ι
  rcases IntermediateField.exists_algEquiv_apply_eq_of_countable ι with ⟨σ, hσ⟩
  rcases hf σ with ⟨g, hg⟩
  refine ⟨⟨g, hg.isGaloisConjugate⟩, (isEmbedding_galoisOrbitEmbedding _).algHom_eq ?_⟩
  exact isEmbedding_iff.mpr fun n ↦ by rw [hg.coeff, ← coe_coeff_orbitQExpansion, hσ]

variable (f) in
include hk in
/-- **A Galois orbit has at most `[ℚ(f) : ℚ]` elements**: in weight at least two, where the
coefficient field `ℚ(f)` is a number field, the Galois orbit of `f` has at most as many elements as
`ℚ(f)` has embeddings into `ℂ`. -/
lemma ncard_galoisOrbit_le : f.galoisOrbit.ncard ≤ Module.finrank ℚ (CoefficientField f) := by
  have : NumberField (CoefficientField f) := numberField_CoefficientField f hk
  rw [← AlgHom.card ℚ (CoefficientField f) ℂ, ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective _ f.galoisOrbitEmbedding_injective

include hk hf in
/-- **A Galois orbit has `[ℚ(f) : ℚ]` elements** in weight at least two, if every Galois conjugate
of `f` is a newform, as is always the case (a theorem not proved here). -/
lemma ncard_galoisOrbit_eq : f.galoisOrbit.ncard = Module.finrank ℚ (CoefficientField f) := by
  have : NumberField (CoefficientField f) := numberField_CoefficientField f hk
  rw [← AlgHom.card ℚ (CoefficientField f) ℂ, ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
  exact Nat.card_eq_of_bijective _ ⟨f.galoisOrbitEmbedding_injective,
    galoisOrbitEmbedding_surjective hf⟩

end Newform

variable (N k) in
/-- The type of **newform orbits** of level `N` and weight `k` (LMFDB `cmf.galois_orbit`): the
Galois orbits of newforms, which the LMFDB calls newforms. -/
abbrev NewformOrbit : Type :=
  Quotient (Newform.galoisOrbitRel N k)

variable (f) in
/-- The newform orbit of a newform. -/
abbrev Newform.newformOrbit : NewformOrbit N k :=
  Quotient.mk _ f

lemma Newform.newformOrbit_eq_iff : f.newformOrbit = g.newformOrbit ↔ f.IsGaloisConjugate g :=
  Quotient.eq

end HeckeRing.GL2
