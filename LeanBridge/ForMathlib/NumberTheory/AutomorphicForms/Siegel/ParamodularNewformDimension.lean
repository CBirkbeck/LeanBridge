import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularNewform
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Dimensions of paramodular newforms

The dimension of a space of Siegel modular forms (LMFDB `mf.siegel.dimension`) is its dimension as
a complex vector space, Mathlib's `Module.finrank ℂ`. The dimension of a paramodular newform `F` is
the dimension of its newform subspace `V_F`, the span of its Galois conjugates
(`SiegelUpperHalfSpace.newformSubspace`), and its relative dimension is the dimension of the
`χ`-part `V_F ∩ S_ρ(K(N), χ)` of `V_F` for the character `χ` of `F`, which counts the Galois
conjugates of `F` with the character `χ` when these are linearly independent (not proved here). The
paramodular forms of the LMFDB have trivial character, so `ℚ(χ) = ℚ` and the relative dimension of
`F`, as that of the new subspace `S_ρ^new(K(N))`, is its dimension; the new subspace with a
nontrivial character is not defined here.

The knowl states that the dimension of `F` is the number of its Galois conjugates and the degree
`[ℚ(F) : ℚ]` of its coefficient field. Here the dimension is proved to be an invariant of the
Galois orbit, independent of the normalisation of `F` (which the knowl fixes by `a_1 = 1`, not
defined for Siegel modular forms), at most the number of Galois conjugates, and equal to it when
these are linearly independent, which is at most `[ℚ(F) : ℚ]` when the coefficient field `ℚ(F)` is
a number field, and positive then; the linear independence of the Galois conjugates of a newform
(for a normalisation of `F` making `ℚ(F)` its Hecke field) and the equality with `[ℚ(F) : ℚ]` are
not proved. The relative dimension is proved to be the dimension when the Galois conjugates of `F`
are cusp forms on `K(N)` with the character of `F`, as they are for the trivial character.

## Main definitions

* `SiegelUpperHalfSpace.newformDimension` (LMFDB `mf.siegel.dimension`): the dimension of a
  paramodular newform.
* `SiegelUpperHalfSpace.newformRelativeDimension` (LMFDB `mf.siegel.dimension`): its relative
  dimension.

## Main results

* `SiegelUpperHalfSpace.ncard_isGaloisConjugate_le`: on an arithmetic subgroup, a function whose
  coefficient field `K` is a number field has at most `[K : ℚ]` Galois conjugates.
* `SiegelUpperHalfSpace.newformSubspace_eq_of_isGaloisConjugate`: Galois conjugate forms have the
  same newform subspace, and `SiegelUpperHalfSpace.newformDimension_eq_of_isGaloisConjugate` the
  same dimension.
* `SiegelUpperHalfSpace.newformSubspace_smul`, `SiegelUpperHalfSpace.newformDimension_smul`: the
  newform subspace and the dimension do not depend on the normalisation of the form.
* `SiegelUpperHalfSpace.newformDimension_le_ncard`: the dimension of a form is at most the number
  of its Galois conjugates, and `SiegelUpperHalfSpace.newformDimension_eq_ncard` equal to it when
  they are linearly independent.
* `SiegelUpperHalfSpace.newformDimension_le_finrank`: it is at most the degree of the coefficient
  field when this is a number field.
* `SiegelUpperHalfSpace.newformDimension_pos`: it is then positive for a nonzero form with a
  Fourier expansion, the newform subspace being finite-dimensional (the instance
  `FiniteDimensional ℂ (newformSubspace N B f)`).
* `SiegelUpperHalfSpace.newformRelativeDimension_eq_newformDimension`: the relative dimension is
  the dimension when the Galois conjugates are cusp forms on `K(N)` with the same character.
* `SiegelUpperHalfSpace.finrank_span_eq_finrank_paramodularNewSubspace`: a basis of
  `S_ρ^new(K(N))` spans a space of its dimension over any subfield of `ℂ`, such as `ℚ` or `ℚ(χ)`.
-/

open Module

namespace SiegelUpperHalfSpace

section Conjugates

variable {l : Type*} [Fintype l] [DecidableEq l] {Γ : Subgroup (Matrix.symplecticGroup l ℚ)}
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] {B : Basis ι ℂ V} {σ τ : Gal(ℂ/ℚ)}
    {f g : SiegelUpperHalfSpace l → V}

private lemma IsGaloisConjugateBy.of_eqOn (hσ : IsGaloisConjugateBy Γ B σ f g)
    (hστ : ∀ x ∈ vectorCoefficientField Γ B f, σ x = τ x) : IsGaloisConjugateBy Γ B τ f g := by
  rcases hσ with ⟨a, a', ha, ha', h⟩
  exact ⟨a, a', ha, ha', fun n i ↦ (h n i).trans <| hστ _ <| Subfield.subset_closure
    ⟨a, ha, n, i, rfl⟩⟩

lemma IsGaloisConjugateBy.const_smul (hσ : IsGaloisConjugateBy Γ B σ f g) (c : ℂ) :
    IsGaloisConjugateBy Γ B σ (c • f) (σ c • g) := by
  rcases hσ with ⟨a, a', ha, ha', h⟩
  exact ⟨c • a, σ c • a', ha.const_smul Γ c, ha'.const_smul Γ (σ c), fun n i ↦ by
    simp [h]⟩

variable (Γ B f) in
/-- The restriction to the coefficient field `K` of `f` of an automorphism `σ` of `ℂ` with
`c = σ(f)`, for a Galois conjugate `c` of `f`. -/
private noncomputable def conjugateRestriction (c : {g | IsGaloisConjugate Γ B f g}) :
    vectorCoefficientField Γ B f →ₐ[ℚ] ℂ :=
  ((c.2.choose : ℂ →+* ℂ).comp (vectorCoefficientField Γ B f).subtype).toRatAlgHom

private lemma conjugateRestriction_injective (hΓ : SymplecticGroup.IsArithmetic Γ) :
    Function.Injective (conjugateRestriction Γ B f) := by
  rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
  exact Subtype.ext <| (hg.choose_spec.of_eqOn fun x hx ↦ DFunLike.congr_fun h ⟨x, hx⟩).unique hΓ
    hg'.choose_spec

variable (B f) in
lemma finite_isGaloisConjugate (hΓ : SymplecticGroup.IsArithmetic Γ)
    [FiniteDimensional ℚ (vectorCoefficientField Γ B f)] : {g | IsGaloisConjugate Γ B f g}.Finite :=
  Set.finite_coe_iff.mp <| Finite.of_injective _ <| conjugateRestriction_injective hΓ

variable (B f) in
/-- **A form has at most `[K : ℚ]` Galois conjugates**, on an arithmetic subgroup `Γ`, when its
coefficient field `K` is a number field: a Galois conjugate `σ(f)` only depends on the restriction
of `σ` to `K`, Fourier expansions on `Γ` being unique, and there are `[K : ℚ]` embeddings of `K`
into `ℂ`. -/
lemma ncard_isGaloisConjugate_le (hΓ : SymplecticGroup.IsArithmetic Γ)
    [FiniteDimensional ℚ (vectorCoefficientField Γ B f)] :
    {g | IsGaloisConjugate Γ B f g}.ncard ≤ finrank ℚ (vectorCoefficientField Γ B f) := by
  rw [← AlgHom.card ℚ _ ℂ, ← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective _ <| conjugateRestriction_injective hΓ

end Conjugates

variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (N : ℕ+) (ψ : paramodularLevel N →* ℂˣ) (B : Basis ι ℂ V) (f : SiegelUpperHalfSpace (Fin 2) → V)
    {g : SiegelUpperHalfSpace (Fin 2) → V}

/-- The **dimension** of a paramodular newform `f` of level `N` (LMFDB `mf.siegel.dimension`),
relative to a basis `B` of `V`: the dimension of its newform subspace `V_f`, the span of its Galois
conjugates (`SiegelUpperHalfSpace.newformSubspace`). It is an invariant of the Galois orbit
(`newformDimension_eq_of_isGaloisConjugate`), does not depend on the normalisation of `f`
(`newformDimension_smul`), is at most the number of Galois conjugates of `f`
(`newformDimension_le_ncard`), and equal to it when they are linearly independent
(`newformDimension_eq_ncard`), and at most the degree of the coefficient field of `f` when this is
a number field (`newformDimension_le_finrank`). The knowl states that it is equal to both, which
is not proved here. -/
noncomputable def newformDimension : ℕ :=
  finrank ℂ (newformSubspace N B f)

/-- The **relative dimension** of a paramodular newform `f` of level `N` with character `ψ` (LMFDB
`mf.siegel.dimension`), relative to a basis `B` of `V`: the dimension of the `ψ`-part
`V_f ∩ S_ρ(K(N), ψ)` of its newform subspace `V_f`. The LMFDB defines it as the dimension of `V_f`
over the field `ℚ(ψ)` generated by the values of `ψ`, the number of Galois conjugates of `f` with
the same character `ψ` (LMFDB `mf.siegel.label`): a conjugate `σ(f)` has the character `σ ∘ ψ`, and
the `σ(f)` with `σ ∘ ψ = ψ` span the `ψ`-part when the Galois conjugates of `f` are linearly
independent, facts which are not proved here. For the trivial character of the paramodular forms of
the LMFDB, `ℚ(ψ) = ℚ` and the relative dimension is the dimension
`SiegelUpperHalfSpace.newformDimension` as soon as the Galois conjugates of `f` are cusp forms on
`K(N)` (`SiegelUpperHalfSpace.newformRelativeDimension_eq_newformDimension`). -/
noncomputable def newformRelativeDimension : ℕ :=
  finrank ℂ ↥(newformSubspace N B f ⊓ cuspForms ρ (paramodularLevel N) ψ)

variable {N B f}

/-- **Galois conjugate forms have the same newform subspace**, Galois conjugacy being an
equivalence relation on the paramodular group, which is arithmetic. -/
lemma newformSubspace_eq_of_isGaloisConjugate (hfg : IsGaloisConjugate (paramodularLevel N) B f g) :
    newformSubspace N B f = newformSubspace N B g :=
  congrArg (Submodule.span ℂ) <| Set.ext fun _ ↦ ⟨hfg.symm.trans Fact.out, hfg.trans Fact.out⟩

/-- **The dimension of a newform is an invariant of its Galois orbit.** -/
lemma newformDimension_eq_of_isGaloisConjugate
    (hfg : IsGaloisConjugate (paramodularLevel N) B f g) :
    newformDimension N B f = newformDimension N B g := by
  rw [newformDimension, newformDimension, newformSubspace_eq_of_isGaloisConjugate hfg]

variable {c : ℂ}

private lemma smul_mem_newformSubspace (hc : c ≠ 0)
    (hg : IsGaloisConjugate (paramodularLevel N) B (c • f) g) : g ∈ newformSubspace N B f := by
  rcases hg with ⟨σ, hσ⟩
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have h : IsGaloisConjugateBy (paramodularLevel N) B σ f ((σ c)⁻¹ • g) := by
    simpa [hc] using hσ.const_smul c⁻¹
  rw [← smul_inv_smul₀ hσc g]
  exact Submodule.smul_mem _ _ <| Submodule.subset_span <| h.isGaloisConjugate

/-- **The newform subspace does not depend on the normalisation**: `c f` and `f` have the same
newform subspace for `c ≠ 0`, the Galois conjugates of `c f` being the `σ(c) σ(f)`. So the
dimension of a newform does not depend on the normalisation `a_1 = 1` of the knowl, which is not
defined for Siegel modular forms. -/
lemma newformSubspace_smul (hc : c ≠ 0) : newformSubspace N B (c • f) = newformSubspace N B f :=
  le_antisymm (Submodule.span_le.mpr fun _ hg ↦ smul_mem_newformSubspace hc hg) <|
    Submodule.span_le.mpr fun _ hg ↦ smul_mem_newformSubspace (inv_ne_zero hc) <| by
      rwa [inv_smul_smul₀ hc]

/-- **The dimension of a newform does not depend on its normalisation.** -/
lemma newformDimension_smul (hc : c ≠ 0) :
    newformDimension N B (c • f) = newformDimension N B f := by
  rw [newformDimension, newformDimension, newformSubspace_smul hc]

/-- **The dimension of a newform is at most the number of its Galois conjugates**, when this is
finite. -/
lemma newformDimension_le_ncard (hf : {g | IsGaloisConjugate (paramodularLevel N) B f g}.Finite) :
    newformDimension N B f ≤ {g | IsGaloisConjugate (paramodularLevel N) B f g}.ncard :=
  finrank_span_le_ncard _ hf

/-- **The dimension of a newform is the number of its Galois conjugates** when these are linearly
independent, as for a newform whose Fourier coefficients lie in its Hecke field, its distinct
Galois conjugates being eigenforms with distinct Hecke eigenvalues (not proved here). -/
lemma newformDimension_eq_ncard
    (hf : LinearIndepOn ℂ id {g | IsGaloisConjugate (paramodularLevel N) B f g}) :
    newformDimension N B f = {g | IsGaloisConjugate (paramodularLevel N) B f g}.ncard :=
  finrank_span_set_eq_ncard hf

/-- **The dimension of a newform is at most the degree of its coefficient field**, when this is a
number field. -/
lemma newformDimension_le_finrank
    [FiniteDimensional ℚ (vectorCoefficientField (paramodularLevel N) B f)] :
    newformDimension N B f ≤ finrank ℚ (vectorCoefficientField (paramodularLevel N) B f) :=
  (newformDimension_le_ncard <| finite_isGaloisConjugate B f Fact.out).trans <|
    ncard_isGaloisConjugate_le B f Fact.out

instance [FiniteDimensional ℚ (vectorCoefficientField (paramodularLevel N) B f)] :
    FiniteDimensional ℂ (newformSubspace N B f) :=
  FiniteDimensional.span_of_finite ℂ <| finite_isGaloisConjugate B f Fact.out

/-- **The dimension of a nonzero form with a Fourier expansion is positive** when its coefficient
field is a number field, its newform subspace being finite-dimensional and containing it. -/
lemma newformDimension_pos [FiniteDimensional ℚ (vectorCoefficientField (paramodularLevel N) B f)]
    {a : dualLattice (paramodularLevel N) → V}
    (ha : HasSiegelFourierExpansion (paramodularLevel N) f a) (hf : f ≠ 0) :
    0 < newformDimension N B f :=
  Submodule.one_le_finrank_iff.mpr <| (Submodule.ne_bot_iff _).mpr
    ⟨f, self_mem_newformSubspace N B f ha, hf⟩

lemma newformRelativeDimension_le_newformDimension
    [FiniteDimensional ℚ (vectorCoefficientField (paramodularLevel N) B f)] :
    newformRelativeDimension ρ N ψ B f ≤ newformDimension N B f :=
  Submodule.finrank_mono inf_le_left

/-- **The relative dimension of a newform is its dimension** when its Galois conjugates are cusp
forms on `K(N)` with its character `ψ`, as for the trivial character of the paramodular forms of the
LMFDB, whose character field is `ℚ`. -/
lemma newformRelativeDimension_eq_newformDimension
    (hf : {g | IsGaloisConjugate (paramodularLevel N) B f g} ⊆ cuspForms ρ (paramodularLevel N) ψ) :
    newformRelativeDimension ρ N ψ B f = newformDimension N B f :=
  congrArg (fun W : Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → V) ↦ finrank ℂ W) <|
    inf_eq_left.mpr <| Submodule.span_le.mpr hf

variable (b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) in
/-- **A basis of `S_ρ^new(K(N))` spans a space of the same dimension over any subfield of `ℂ`**
(LMFDB `mf.siegel.dimension`): if a set `E` of forms, such as the newforms, is linearly independent
over `ℂ` and spans `S_ρ^new(K(N))`, as the knowl states for the newforms (not proved here), then
for every subfield `K` of `ℂ` the `K`-span of `E` has dimension `dim_ℂ S_ρ^new(K(N))` over `K`.
For `K = ℚ` this is the knowl's description of the dimension of `S_ρ^new(K(N))`, and for the
character field `K = ℚ(χ)` that of its relative dimension, which for the trivial character of the
paramodular forms of the LMFDB is its dimension. -/
lemma finrank_span_eq_finrank_paramodularNewSubspace (K : IntermediateField ℚ ℂ)
    {E : Set (SiegelUpperHalfSpace (Fin 2) → V)} (hE : LinearIndepOn ℂ id E)
    (hspan : Submodule.span ℂ E = paramodularNewSubspace ρ N b) :
    finrank K (Submodule.span K E) = finrank ℂ (paramodularNewSubspace ρ N b) := by
  rw [← hspan, finrank_span_set_eq_ncard hE,
    finrank_span_set_eq_ncard (LinearIndependent.restrict_scalars' K hE)]

end SiegelUpperHalfSpace
