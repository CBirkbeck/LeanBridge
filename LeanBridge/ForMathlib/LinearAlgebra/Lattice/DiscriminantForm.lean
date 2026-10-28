import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Bilinear
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic

/-!
# The torsion quadratic form and Gram matrices of a discriminant group

The discriminant group `L^∨ / L` of an integral lattice `L` (Tau Ceti's
`TauCeti.IntegralLattice.DiscriminantGroup`) carries the torsion bilinear form
`B_L(u + L, v + L) = B(u, v) + ℤ` (Tau Ceti's `TauCeti.IntegralLattice.discriminantPairing`), and,
for even `L`, the torsion quadratic form. Tau Ceti's
`TauCeti.IntegralLattice.discriminantQuadraticMap` is the half-norm `u + L ↦ B(u, u) / 2 + ℤ` with
values in `ℚ / ℤ`; the LMFDB's torsion quadratic form is twice it, `u + L ↦ B(u, u) + 2ℤ` with
values in `ℚ / 2ℤ`. That the discriminant form is an invariant of the genus, and with the signature
determines it, is not formalised.

## Main definitions

* `TauCeti.IntegralLattice.torsionQuadraticForm` (LMFDB `lattice.discriminant_group`).
* `TauCeti.IntegralLattice.IsDiscriminantGramMatrix` (LMFDB `lattice.discriminant_group`).

## Main results

* `TauCeti.IntegralLattice.isDiscriminantGramMatrix_form`: the matrix of the values of the form on
  representatives of generators of `L^∨ / L` is a Gram matrix of the discriminant form.
-/

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V) (hL : L.IsEven)

/-- The **torsion quadratic form** (LMFDB `lattice.discriminant_group`)
`Q_L : L^∨ / L → ℚ / 2ℤ`, `u + L ↦ B(u, u) + 2ℤ`, of an even integral lattice `L`: twice Tau Ceti's
half-norm form `TauCeti.IntegralLattice.discriminantQuadraticMap` with values in `ℚ / ℤ`. -/
noncomputable def torsionQuadraticForm : QuadraticMap ℤ L.DiscriminantGroup (AddCircle (2 : ℚ)) :=
  (AddCircle.equivAddCircle 1 2 one_ne_zero two_ne_zero).toIntLinearEquiv.toLinearMap
    |>.compQuadraticMap (L.discriminantQuadraticMap hL)

lemma torsionQuadraticForm_mk (x : L.dualCarrier) :
    L.torsionQuadraticForm hL (Submodule.Quotient.mk x) = (L.form x x : AddCircle (2 : ℚ)) := by
  rw [torsionQuadraticForm, LinearMap.compQuadraticMap_apply, discriminantQuadraticMap_mk]
  simp [AddCircle.equivAddCircle_apply_mk]

variable {ι : Type*}

open scoped Classical in
/-- A rational matrix `M` is a **Gram matrix** (LMFDB `lattice.discriminant_group`) of the
discriminant form of an integral lattice `L` on a family `u` of generators of `L^∨ / L` if its
off-diagonal entries `M i j` are representatives of `B_L(u i, u j) ∈ ℚ / ℤ`, and its diagonal
entries `M i i` are representatives of `Q_L(u i) ∈ ℚ / 2ℤ` if `L` is even, and of
`B_L(u i, u i) ∈ ℚ / ℤ` if `L` is odd. -/
def IsDiscriminantGramMatrix (u : ι → L.DiscriminantGroup) (M : Matrix ι ι ℚ) : Prop :=
  Submodule.span ℤ (Set.range u) = ⊤ ∧
    (∀ i j, i ≠ j → (M i j : AddCircle (1 : ℚ)) = L.discriminantPairing (u i) (u j)) ∧
    ∀ i, if h : L.IsEven then (M i i : AddCircle (2 : ℚ)) = L.torsionQuadraticForm h (u i)
      else (M i i : AddCircle (1 : ℚ)) = L.discriminantPairing (u i) (u i)

/-- **The values of the form on representatives of generators give a Gram matrix of the discriminant
form.** -/
lemma isDiscriminantGramMatrix_form (x : ι → L.dualCarrier)
    (hx : Submodule.span ℤ (Set.range (L.carrierInDual.mkQ ∘ x)) = ⊤) :
    L.IsDiscriminantGramMatrix (L.carrierInDual.mkQ ∘ x) fun i j ↦ L.form (x i) (x j) := by
  refine ⟨hx, fun i j _ ↦ (L.discriminantPairing_mk _ _).symm, fun i ↦ ?_⟩
  split_ifs with h
  · exact (L.torsionQuadraticForm_mk h _).symm
  · exact (L.discriminantPairing_mk _ _).symm

end TauCeti.IntegralLattice
