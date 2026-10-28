import LeanBridge.ForMathlib.LinearAlgebra.Lattice.OrthogonalDecomposition
import TauCeti.LinearAlgebra.IntegralLattice.Signature

/-!
# Additively indecomposable integral lattices

A positive definite integral lattice `L` with bilinear form `B` is additively indecomposable (LMFDB
`lattice.additively_indecomposable`) if `B` is not the sum of two nonzero positive semidefinite
symmetric integral forms on `L`, that is, `L` is not the sum of two nonzero positive semidefinite
integral lattices on the same group. As for orthogonal indecomposability, the zero lattice is not
indecomposable.

An orthogonal decomposition `L = L₁ ⊕ L₂` into nonzero summands writes `B` as the sum of the forms
`B(π₁ x, π₁ y)` and `B(π₂ x, π₂ y)` of the two projections, which are positive semidefinite and
nonzero, so an additively indecomposable lattice is orthogonally indecomposable. The converse for
unimodular lattices and the theorem of Mordell and Ko that `ℤ`, `E₆`, `E₇` and `E₈` are the only
additively indecomposable lattices of rank at most `8` are not formalised.

## Main definitions

* `TauCeti.IntegralLattice.IsAdditivelyIndecomposable` (LMFDB `lattice.additively_indecomposable`).

## Main results

* `TauCeti.IntegralLattice.IsAdditivelyIndecomposable.isOrthogonallyIndecomposable`: an additively
  indecomposable lattice is orthogonally indecomposable.
-/

open LinearMap (BilinForm)

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

variable (L) in
/-- A positive definite integral lattice `L` is **additively indecomposable** (LMFDB
`lattice.additively_indecomposable`) if it is nonzero and its integral form is not the sum of two
nonzero symmetric positive semidefinite integral bilinear forms on `L`. -/
def IsAdditivelyIndecomposable : Prop :=
  L.IsPosDef ∧ Nontrivial L ∧ ∀ B₁ B₂ : BilinForm ℤ L, B₁.IsSymm → B₂.IsSymm →
    (∀ x, 0 ≤ B₁ x x) → (∀ x, 0 ≤ B₂ x x) → B₁ + B₂ = L.integralForm → B₁ = 0 ∨ B₂ = 0

lemma integralForm_pos (hL : L.IsPosDef) {x : L} (hx : x ≠ 0) : 0 < L.integralForm x x := by
  have h : (0 : ℚ) < L.integralForm x x := by
    rw [integralForm_cast]
    exact hL (x : V) fun h ↦ hx (Subtype.ext h)
  exact_mod_cast h

lemma integralForm_nonneg (hL : L.IsPosDef) (x : L) : 0 ≤ L.integralForm x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (integralForm_pos hL hx).le

lemma eq_bot_of_compl₁₂_eq_zero (hL : L.IsPosDef) {S : Submodule ℤ L} {p : L →ₗ[ℤ] L}
    (hp : ∀ x ∈ S, p x = x) (h : L.integralForm.compl₁₂ p p = 0) : S = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ by_contra fun hne ↦ (integralForm_pos hL hne).ne' ?_
  rw [← hp x hx, ← LinearMap.compl₁₂_apply, h, LinearMap.zero_apply, LinearMap.zero_apply]

/-- **An additively indecomposable lattice is orthogonally indecomposable**: an orthogonal
decomposition `L = S ⊕ T` writes the form as the sum of the forms of the two projections. -/
lemma IsAdditivelyIndecomposable.isOrthogonallyIndecomposable (h : L.IsAdditivelyIndecomposable) :
    L.IsOrthogonallyIndecomposable := by
  refine L.isOrthogonallyIndecomposable_iff.mpr ⟨h.2.1, fun S T hST horth ↦ ?_⟩
  let p : L →ₗ[ℤ] L := S.projection T hST
  let q : L →ₗ[ℤ] L := T.projection S hST.symm
  have hsymm : L.integralForm.IsSymm := L.isSymm_integralForm
  have hsum : L.integralForm.compl₁₂ p p + L.integralForm.compl₁₂ q q = L.integralForm := by
    ext x y
    have hpq (z : L) : p z + q z = z := Submodule.projection_add_projection_eq_self hST z
    have hpy : L.integralForm (p x) (q y) = 0 :=
      horth _ (Submodule.projection_apply_mem _ _) _ (Submodule.projection_apply_mem _ _)
    have hqx : L.integralForm (q x) (p y) = 0 := hsymm.eq (q x) (p y) ▸
      horth _ (Submodule.projection_apply_mem _ _) _ (Submodule.projection_apply_mem _ _)
    conv_rhs => rw [← hpq x, ← hpq y]
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, map_add, hpy, hqx]
    ring1
  rcases h.2.2 _ _ ⟨fun x y ↦ hsymm.eq (p x) (p y)⟩ ⟨fun x y ↦ hsymm.eq (q x) (q y)⟩
    (fun x ↦ integralForm_nonneg h.1 (p x)) (fun x ↦ integralForm_nonneg h.1 (q x)) hsum
    with h0 | h0
  · exact Or.inl <| eq_bot_of_compl₁₂_eq_zero h.1
      (fun x hx ↦ Submodule.projection_apply_of_mem_left hST hx) h0
  · exact Or.inr <| eq_bot_of_compl₁₂_eq_zero h.1
      (fun x hx ↦ Submodule.projection_apply_of_mem_left hST.symm hx) h0

end TauCeti.IntegralLattice
