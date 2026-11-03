import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NewformSubspace

/-!
# Dimensions of newforms and of spaces of newforms

The dimension of a space of modular forms (LMFDB `cmf.dimension`) is its dimension as a complex
vector space, Mathlib's `Module.finrank ℂ`. For the space `S_k^{new}(N, χ)` of newforms of
nebentypus `χ`, this is also the dimension of the vector space spanned by its eigenforms over `ℚ`,
or over any subfield of `ℂ`: the newforms are linearly independent over `ℂ`. Over the character
field `ℚ(χ)`, this is the relative dimension of `S_k^{new}(N, χ)`.

The dimension of a newform `f` is the dimension of its newform subspace `V_f`, equivalently the
size of its Galois orbit, and its relative dimension is the dimension of the `χ`-part of `V_f`,
equivalently the number of Galois conjugates of `f` with the nebentypus `χ` of `f`. The LMFDB states
that the dimension is the degree `[ℚ(f) : ℚ]` of the coefficient field, and that the relative
dimension is `[ℚ(f) : ℚ(χ)]` (LMFDB `cmf.relative_dimension`). Both hold in every weight: the first
is `HeckeRing.GL2.Newform.dimension_eq_finrank`, and the second is
`HeckeRing.GL2.Newform.relativeDimension_eq_finrank`, in `Newform/RationalStructure.lean`.

## Main definitions

* `HeckeRing.GL2.Newform.dimension`: the dimension of a newform (LMFDB `cmf.dimension`).
* `HeckeRing.GL2.Newform.relativeDimension`: the relative dimension of a newform
  (LMFDB `cmf.dimension`).

## Main results

* `HeckeRing.GL2.Newform.finrank_span_toCuspForm_eq_finrank`: the dimension of the space spanned by
  the newforms of nebentypus `χ` over a subfield `K ⊆ ℂ`, such as `ℚ` or `ℚ(χ)`, is the complex
  dimension of `S_k^{new}(N, χ)`.
* `HeckeRing.GL2.Newform.dimension_eq_ncard_galoisOrbit`: the dimension of `f` is the size of its
  Galois orbit.
* `HeckeRing.GL2.Newform.dimension_eq_finrank`: the dimension of `f` is the degree of its
  coefficient field, in every weight.
* `HeckeRing.GL2.Newform.relativeDimension_eq_ncard`: the relative dimension of `f` is the number of
  its Galois conjugates of nebentypus `χ`.
-/

open TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k}

/-- **The eigenforms of `S_k^{new}(N, χ)` span a space of its dimension over any subfield of `ℂ`**:
over `ℚ` (`K = ⊥`) this is the dimension of the space of newforms of nebentypus `χ`
(LMFDB `cmf.dimension`), and over the character field `ℚ(χ)` its relative dimension. -/
lemma finrank_span_toCuspForm_eq_finrank (K : IntermediateField ℚ ℂ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.finrank K (Submodule.span K ((fun g : Newform N k ↦ g.toCuspForm) '' {g | g.χ = χ})) =
    Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) := by
  rw [← span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace, finrank_span_image_toCuspForm,
    finrank_span_set_eq_ncard
      ((linearIndependent_toCuspForm.restrict_scalars' K).linearIndepOn _).id_image,
    Set.ncard_image_of_injective _ linearIndependent_toCuspForm.injective]

variable (f) in
/-- The **dimension** of a newform `f` (LMFDB `cmf.dimension`): the dimension of its newform
subspace `V_f`, equivalently the size of its Galois orbit (`dimension_eq_ncard_galoisOrbit`). It is
the degree `[ℚ(f) : ℚ]` of the coefficient field of `f` (`dimension_eq_finrank`). -/
noncomputable def dimension : ℕ :=
  Module.finrank ℂ f.newformSubspace

variable (f) in
/-- **The dimension of a newform is the size of its Galois orbit.** -/
lemma dimension_eq_ncard_galoisOrbit : f.dimension = f.galoisOrbit.ncard :=
  f.finrank_newformSubspace

variable (f) in
lemma dimension_pos : 0 < f.dimension :=
  f.dimension_eq_ncard_galoisOrbit ▸ (Set.ncard_pos f.finite_galoisOrbit).mpr
    ⟨f, f.self_mem_galoisOrbit⟩

lemma IsGaloisConjugate.dimension_eq (hfg : f.IsGaloisConjugate g) : f.dimension = g.dimension := by
  rw [dimension, dimension, hfg.newformSubspace_eq]

variable (f) in
/-- **The dimension of a newform is the degree of its coefficient field**, in every weight
(LMFDB `cmf.decomposition.new.gamma0chi`, `cmf.dimension`). -/
lemma dimension_eq_finrank : f.dimension = Module.finrank ℚ (CoefficientField f) :=
  f.dimension_eq_ncard_galoisOrbit.trans f.ncard_galoisOrbit_eq

variable (f) in
/-- The **relative dimension** of a newform `f` of nebentypus `χ` (LMFDB `cmf.dimension`): the
dimension of the `χ`-part `V_f ∩ S_k(N, χ)` of its newform subspace, equivalently the number of
Galois conjugates of `f` with nebentypus `χ` (`relativeDimension_eq_ncard`). The LMFDB defines it
as the dimension over the character field `ℚ(χ)` of the rational structure of `V_f`; both are the
degree `[ℚ(f) : ℚ(χ)]` (LMFDB `cmf.relative_dimension`), by `relativeDimension_eq_finrank` and
`finrank_rationalPiece`, in `Newform/RationalStructure.lean`. -/
noncomputable def relativeDimension : ℕ :=
  Module.finrank ℂ ↥(f.newformSubspace ⊓ cuspFormCharSpace k f.χ)

variable (f) in
/-- **The relative dimension of a newform is the number of its Galois conjugates with the same
nebentypus.** -/
lemma relativeDimension_eq_ncard : f.relativeDimension = {g ∈ f.galoisOrbit | g.χ = f.χ}.ncard := by
  rw [relativeDimension, newformSubspace, span_image_toCuspForm_inf_cuspFormCharSpace,
    finrank_span_image_toCuspForm]

variable (f) in
lemma relativeDimension_le_dimension : f.relativeDimension ≤ f.dimension :=
  f.relativeDimension_eq_ncard ▸ f.dimension_eq_ncard_galoisOrbit ▸
    Set.ncard_le_ncard (Set.sep_subset _ _) f.finite_galoisOrbit

end HeckeRing.GL2.Newform
