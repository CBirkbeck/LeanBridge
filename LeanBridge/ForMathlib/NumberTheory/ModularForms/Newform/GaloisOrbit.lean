import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.ComplexAutomorphismFixedField
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Embedding
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisConjugateExists
import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis

/-!
# Galois orbits of newforms

The Galois orbit `[f] = {σ(f)}` of a newform `f` (LMFDB `cmf.galois_orbit`) is the set of its
Galois conjugates. Here it is the set of newforms of the level and weight of `f` that are Galois
conjugate to `f`. Every Galois conjugate `σ(f)` is a newform of the same level and weight
(`HeckeRing.GL2.Newform.exists_isGaloisConjugateBy`), so this is the LMFDB orbit.

Galois orbits of newforms are also called newform orbits, and the LMFDB calls them newforms:
`HeckeRing.GL2.NewformOrbit N k` is the type of Galois orbits of newforms of level `N` and weight
`k`.

The elements of `[f]` are the embeddings `ι(f)` of `f`, for the embeddings `ι : ℚ(f) → ℂ`, as Galois
conjugates of `f` are newforms. There are finitely many newforms, so the coefficient field `ℚ(f)`
has finitely many embeddings into `ℂ`, and it is a number field, in every weight: Tau Ceti proves it
in weight at least two, through modular symbols. So `[f]` has `[ℚ(f) : ℚ]` elements, as the LMFDB
states.

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
* `HeckeRing.GL2.Newform.galoisOrbitEmbedding_injective`,
  `HeckeRing.GL2.Newform.galoisOrbitEmbedding_surjective`: the elements of the Galois orbit of `f`
  are the embeddings of `f` by the embeddings of its coefficient field, without repetition.
* `HeckeRing.GL2.Newform.numberField_coefficientField`: the coefficient field of a newform is a
  number field, in every weight.
* `HeckeRing.GL2.Newform.ncard_galoisOrbit_eq`: the Galois orbit of `f` has `[ℚ(f) : ℚ]` elements.
-/

open TauCeti

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k}

namespace Newform

variable (f) in
/-- The **Galois orbit** `[f]` of a newform `f` (LMFDB `cmf.galois_orbit`): the set of newforms of
the same level and weight that are Galois conjugate to `f`. Galois conjugates of `f` are newforms of
its level and weight (`exists_isGaloisConjugateBy`), so this is the LMFDB orbit
`{σ(f) : σ ∈ Gal(ℚ̄/ℚ)}` (`orbit_algebraicClosure_eq_galoisOrbit`, in
`Newform/GaloisActionOnNewforms.lean`). -/
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

variable (f) in
/-- **Every embedding of the coefficient field comes from a Galois conjugate**, as it extends to an
automorphism `σ` of `ℂ`, and `σ(f)` is a newform. -/
lemma galoisOrbitEmbedding_surjective : Function.Surjective f.galoisOrbitEmbedding := by
  intro ι
  rcases IntermediateField.exists_algEquiv_apply_eq_of_countable ι with ⟨σ, hσ⟩
  rcases exists_isGaloisConjugateBy f σ with ⟨g, hg⟩
  refine ⟨⟨g, hg.isGaloisConjugate⟩, (isEmbedding_galoisOrbitEmbedding _).algHom_eq ?_⟩
  exact isEmbedding_iff.mpr fun n ↦ by rw [hg.coeff, ← coe_coeff_orbitQExpansion, hσ]

variable (f) in
/-- **The coefficient field of a newform is a number field**, in every weight. It has finitely many
embeddings into `ℂ`, since each of them gives a newform of the level and weight of `f`. -/
lemma numberField_coefficientField : NumberField (CoefficientField f) :=
  have : Finite (CoefficientField f →ₐ[ℚ] ℂ) :=
    Finite.of_surjective _ f.galoisOrbitEmbedding_surjective
  { to_charZero := inferInstance
    to_finiteDimensional := IntermediateField.finiteDimensional_of_finite_algHom }

instance : NumberField (CoefficientField f) :=
  f.numberField_coefficientField

variable (f) in
/-- **A Galois orbit has `[ℚ(f) : ℚ]` elements**, in every weight (LMFDB `cmf.galois_orbit`,
`cmf.galois_conjugate`). -/
lemma ncard_galoisOrbit_eq : f.galoisOrbit.ncard = Module.finrank ℚ (CoefficientField f) := by
  rw [← AlgHom.card ℚ (CoefficientField f) ℂ, ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
  exact Nat.card_eq_of_bijective _ ⟨f.galoisOrbitEmbedding_injective,
    f.galoisOrbitEmbedding_surjective⟩

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
