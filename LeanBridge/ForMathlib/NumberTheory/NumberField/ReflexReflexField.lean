import LeanBridge.ForMathlib.NumberTheory.NumberField.ReflexField

/-!
# The reflex field of the reflex field

A CM type `Φ` of a CM field `K` is induced from a subfield `M` of `K` when it consists of the
embeddings of `K` whose restrictions to `M` lie in a CM type of `M`. The reflex field of the reflex
field of `Φ` is the smallest subfield of `K` from which `Φ` is induced, the field of definition of
`Φ`; this is the third of the LMFDB's descriptions of it, the one that names it as a subfield of
`K`. We define it as the intersection of the subfields from which `Φ` is induced.

## Main definitions

* `NumberField.CMType.induce`: the CM type induced along a ring homomorphism.
* `NumberField.CMType.IsInducedFrom`: `Φ` is induced from a CM type of a subfield.
* `NumberField.CMType.reflexReflexField` (LMFDB `nf.reflex_reflex_field`).

## Main results

* `NumberField.CMType.isInducedFrom_top`: a CM type is induced from the whole field.
* `NumberField.CMType.IsInducedFrom.mono`: a CM type induced from a subfield is induced from every
  larger subfield.
* `NumberField.CMType.reflexReflexField_le`: the reflex field of the reflex field lies in every
  subfield from which `Φ` is induced.

That `Φ` is induced from its reflex field of the reflex field, and that this field is the reflex
field of the reflex CM type of `Φ` (the LMFDB's definition), are not proved here: both rest on
Galois theory in a Galois closure of `K`.
-/

namespace NumberField.CMType

variable {K : Type*} [Field K] (Φ : CMType K) {M M' : Subfield K}

/-- The CM type of a field `L` **induced** by a CM type `Φ` of `K` along a ring homomorphism
`g : K → L`: the complex embeddings of `L` whose composite with `g` lies in `Φ`. For a normal
closure `L` of `K` this is the CM type `Φ_L` of the LMFDB knowl `nf.reflex_reflex_field`. -/
def induce {L : Type*} [Field L] (g : K →+* L) : CMType L :=
  ⟨{χ | χ.comp g ∈ Φ.1}, fun χ ↦ Φ.2 (χ.comp g)⟩

variable (M) in
/-- A CM type `Φ` of `K` is **induced** from the subfield `M` of `K` when there is a CM type `Ψ` of
`M` such that `Φ` consists of the complex embeddings of `K` whose restriction to `M` lies in
`Ψ`. -/
def IsInducedFrom : Prop :=
  ∃ Ψ : CMType M, ∀ φ : K →+* ℂ, φ ∈ Φ.1 ↔ φ.comp M.subtype ∈ Ψ.1

/-- A CM type is induced from the whole field. -/
lemma isInducedFrom_top : Φ.IsInducedFrom ⊤ :=
  ⟨Φ.induce Subfield.topEquiv.symm.toRingHom, fun _ ↦ Iff.rfl⟩

/-- A CM type induced from a subfield is induced from every larger subfield. -/
lemma IsInducedFrom.mono (h : Φ.IsInducedFrom M) (hM : M ≤ M') : Φ.IsInducedFrom M' :=
  h.elim fun Ψ hΨ ↦ ⟨Ψ.induce (Subfield.inclusion hM), hΨ⟩

/-- The **reflex field of the reflex field** of a CM type `Φ` of `K` (LMFDB
`nf.reflex_reflex_field`): the smallest subfield of `K` from which `Φ` is induced, the field of
definition of `Φ`, defined as the intersection of the subfields from which `Φ` is induced. That `Φ`
is induced from this intersection rests on Galois theory in a Galois closure of `K` and is not
proved here.

The LMFDB knowl calls this field the *largest* subfield from which `Φ` is induced; since a CM type
induced from a subfield is induced from every larger subfield (`IsInducedFrom.mono`), the field of
definition is the smallest such subfield. -/
noncomputable def reflexReflexField : Subfield K :=
  sInf {M | Φ.IsInducedFrom M}

/-- The reflex field of the reflex field lies in every subfield from which `Φ` is induced. -/
lemma reflexReflexField_le (h : Φ.IsInducedFrom M) : Φ.reflexReflexField ≤ M :=
  sInf_le h

end NumberField.CMType
