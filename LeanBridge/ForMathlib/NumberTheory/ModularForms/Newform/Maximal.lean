import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Dimension
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign

/-!
# Maximal and largest newforms

A newform is maximal (LMFDB `cmf.maximal`) if its Galois orbit spans the ambient subspace containing
it: for trivial nebentypus its Atkin–Lehner subspace, the subspace of `S_k(Γ₀(N))ⁿᵉʷ` with the same
Atkin–Lehner signs `ε_Q` at all the exact divisors `Q ∥ N`, and otherwise the whole space of
newforms `S_k^{new}(N, [χ])` of the Galois orbit `[χ]` of its nebentypus. It is the largest newform
of its ambient subspace if its dimension is larger than that of every other newform there.

Both ambient subspaces are spanned by the newforms that they contain, as the newforms are a basis of
the new subspace on which the Atkin–Lehner operators act diagonally; they are defined here as the
span of these newforms, the newforms of trivial nebentypus with the Atkin–Lehner signs of `f`,
respectively the newforms whose nebentypus is a Galois conjugate `σ ∘ χ` of that of `f`.

## Main definitions

* `HeckeRing.GL2.Newform.ambientNewforms`: the newforms of the ambient subspace of a newform.
* `HeckeRing.GL2.Newform.ambientSubspace`: the ambient subspace of a newform.
* `HeckeRing.GL2.Newform.IsMaximal`: maximal newforms (LMFDB `cmf.maximal`).
* `HeckeRing.GL2.Newform.IsLargest`: largest newforms (LMFDB `cmf.maximal`).

## Main results

* `HeckeRing.GL2.Newform.isMaximal_iff`: `f` is maximal exactly when its Galois orbit consists of
  all the newforms of its ambient subspace.
* `HeckeRing.GL2.Newform.IsMaximal.isLargest`: a maximal newform is the largest in its ambient
  subspace.
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups TauCeti.ExactDivisor

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}

open scoped Classical in
variable (f) in
/-- The newforms of the **ambient subspace** of a newform `f` (LMFDB `cmf.maximal`): if `f` has
trivial nebentypus, the newforms of trivial nebentypus with the same Atkin–Lehner signs as `f` at
every exact divisor `Q ∥ N`; otherwise, the newforms whose nebentypus is a Galois conjugate
`σ ∘ χ` of the nebentypus `χ` of `f`. -/
noncomputable def ambientNewforms : Set (Newform N k) :=
  if hf : f.χ = 1 then
    {g | ∃ hg : g.χ = 1, ∀ (Q : ℕ) (hQ : Q ∥ N), g.atkinLehnerSign hg hQ = f.atkinLehnerSign hf hQ}
  else {g | ∃ σ : Gal(ℂ/ℚ), g.χ = (Units.map (σ : ℂ →* ℂ)).comp f.χ}

variable (f) in
/-- The **ambient subspace** of a newform `f` (LMFDB `cmf.maximal`): for trivial nebentypus, its
Atkin–Lehner subspace of `S_k(Γ₀(N))ⁿᵉʷ`, the forms with the Atkin–Lehner signs of `f`; otherwise
the space of newforms `S_k^{new}(N, [χ])` of the Galois orbit of its nebentypus `χ`. Both are the
span of the newforms that they contain, `ambientNewforms f`. -/
noncomputable def ambientSubspace : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' f.ambientNewforms)

variable (f) in
lemma self_mem_ambientNewforms : f ∈ f.ambientNewforms := by
  by_cases hf : f.χ = 1
  · simp [ambientNewforms, hf]
  · simpa [ambientNewforms, hf] using ⟨1, rfl⟩

variable (f) in
/-- A newform is **maximal** (LMFDB `cmf.maximal`) if its Galois orbit spans its ambient subspace:
its newform subspace is its Atkin–Lehner subspace when its nebentypus is trivial, and the whole
space of newforms `S_k^{new}(N, [χ])` otherwise. -/
def IsMaximal : Prop :=
  f.newformSubspace = f.ambientSubspace

variable (f) in
/-- A newform is the **largest** newform in its ambient subspace (LMFDB `cmf.maximal`) if its
dimension is larger than that of every newform of its ambient subspace that is not Galois conjugate
to it. -/
def IsLargest : Prop :=
  ∀ g ∈ f.ambientNewforms, ¬f.IsGaloisConjugate g → g.dimension < f.dimension

/-- **A newform is maximal exactly when its Galois orbit is the set of newforms of its ambient
subspace**, newforms being linearly independent. -/
lemma isMaximal_iff : f.IsMaximal ↔ f.galoisOrbit = f.ambientNewforms :=
  span_image_toCuspForm_inj

/-- **A maximal newform is the largest in its ambient subspace**: there is no other newform
there. -/
lemma IsMaximal.isLargest (hf : f.IsMaximal) : f.IsLargest :=
  fun _ hg hfg ↦ (hfg ((isMaximal_iff.mp hf).symm.subset hg)).elim

end HeckeRing.GL2.Newform
