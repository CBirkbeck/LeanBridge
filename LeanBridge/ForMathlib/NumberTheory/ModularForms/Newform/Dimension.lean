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
that the dimension is the degree `[ℚ(f) : ℚ]` of the coefficient field; it is at most that degree in
weight at least two, with equality as soon as every Galois conjugate of `f` is a newform. Likewise
the relative dimension is then `[ℚ(f) : ℚ(χ)]` (LMFDB `cmf.relative_dimension`), which is not proved
here.

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
* `HeckeRing.GL2.Newform.dimension_le_finrank`, `HeckeRing.GL2.Newform.dimension_eq_finrank`: in
  weight at least two, the dimension of `f` is at most the degree of its coefficient field, with
  equality if every Galois conjugate of `f` is a newform.
* `HeckeRing.GL2.Newform.relativeDimension_eq_ncard`: the relative dimension of `f` is the number of
  its Galois conjugates of nebentypus `χ`.
-/

open UpperHalfPlane TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k} (hk : 2 ≤ k)

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
the degree `[ℚ(f) : ℚ]` of the coefficient field of `f` as soon as every Galois conjugate of `f` is
a newform (`dimension_eq_finrank`). -/
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
include hk in
/-- **The dimension of a newform is at most the degree of its coefficient field**, in weight at
least two. -/
lemma dimension_le_finrank : f.dimension ≤ Module.finrank ℚ (CoefficientField f) :=
  f.dimension_eq_ncard_galoisOrbit ▸ f.ncard_galoisOrbit_le hk

include hk in
/-- **The dimension of a newform is the degree of its coefficient field** in weight at least two,
if every Galois conjugate of `f` is a newform, as is always the case (a theorem not proved
here). -/
lemma dimension_eq_finrank (hf : ∀ σ : Gal(ℂ/ℚ), ∃ g : Newform N k, f.IsGaloisConjugateBy σ g) :
    f.dimension = Module.finrank ℚ (CoefficientField f) :=
  f.dimension_eq_ncard_galoisOrbit ▸ ncard_galoisOrbit_eq hk hf

variable (f) in
/-- The **relative dimension** of a newform `f` of nebentypus `χ` (LMFDB `cmf.dimension`): the
dimension of the `χ`-part `V_f ∩ S_k(N, χ)` of its newform subspace, equivalently the number of
Galois conjugates of `f` with nebentypus `χ` (`relativeDimension_eq_ncard`). The LMFDB defines it
as the dimension over the character field `ℚ(χ)` of the rational structure of `V_f`; both are the
degree `[ℚ(f) : ℚ(χ)]` (LMFDB `cmf.relative_dimension`) as soon as every Galois conjugate of `f` is
a newform, which is not proved here. -/
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
