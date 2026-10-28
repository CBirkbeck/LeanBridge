import Mathlib.Algebra.Group.Conj

/-!
# Refined passports

Let `G` be a group of automorphisms of a compact Riemann surface `X` of genus `g`, and let
`(s₁, …, sₙ)` be a generating vector of the action, with `Cᵢ` the conjugacy class of `sᵢ` in `G`.
The refined passport of the action is the tuple `(g, G, (C₁, …, Cₙ))`.

The group `G` is the ambient type, so the refined passport records the genus and the vector of
conjugacy classes. The generating vector (LMFDB `curve.highergenus.aut.generatingvector`), the
images of standard generators under the monodromy representation, is taken as given.

## Main definitions

* `RefinedPassport` (LMFDB `curve.highergenus.aut.refinedpassport`).
* `RefinedPassport.ofGeneratingVector` (LMFDB `curve.highergenus.aut.refinedpassport`): the refined
  passport of a generating vector.
-/

variable (G : Type*) [Monoid G] (n : ℕ)

/-- A **refined passport** (LMFDB `curve.highergenus.aut.refinedpassport`) of length `n` for a group
`G`: a genus `g` together with a vector `(C₁, …, Cₙ)` of conjugacy classes of `G`, the group `G`
itself being fixed. Some authors call it a ramification type `(g, G, 𝒞)`. -/
@[ext]
structure RefinedPassport where
  /-- The genus `g` of the curve. -/
  genus : ℕ
  /-- The vector `(C₁, …, Cₙ)` of conjugacy classes. -/
  classes : Fin n → ConjClasses G

namespace RefinedPassport

variable {G n}

/-- The **refined passport** `(g, G, (C₁, …, Cₙ))` (LMFDB `curve.highergenus.aut.refinedpassport`)
of a generating vector `(s₁, …, sₙ)` of a group `G` of automorphisms of a compact Riemann surface of
genus `g`, where `Cᵢ` is the conjugacy class of `sᵢ`. -/
def ofGeneratingVector (g : ℕ) (s : Fin n → G) : RefinedPassport G n :=
  ⟨g, fun i ↦ ConjClasses.mk (s i)⟩

variable (g : ℕ) (s : Fin n → G)

@[simp]
lemma genus_ofGeneratingVector : (ofGeneratingVector g s).genus = g :=
  rfl

@[simp]
lemma classes_ofGeneratingVector (i : Fin n) :
    (ofGeneratingVector g s).classes i = ConjClasses.mk (s i) :=
  rfl

lemma ofGeneratingVector_eq_ofGeneratingVector_iff {t : Fin n → G} :
    ofGeneratingVector g s = ofGeneratingVector g t ↔ ∀ i, IsConj (s i) (t i) := by
  simp [RefinedPassport.ext_iff, funext_iff, ConjClasses.mk_eq_mk_iff_isConj]

end RefinedPassport
