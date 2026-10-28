import Mathlib.Algebra.DirectSum.Module
import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Isometry

/-!
# Orthogonal decompositions of integral lattices

An orthogonal decomposition (LMFDB `lattice.orthogonal_decomposition`) of an integral lattice `L`
with bilinear form `B` is a direct sum decomposition `L = L₁ ⊕ ⋯ ⊕ L_r` such that
`B(x_i, x_j) = 0` for `x_i ∈ L_i`, `x_j ∈ L_j` and `i ≠ j`; equivalently, a Gram matrix of `L` is
block diagonal in a suitable basis. The lattice `L` is (orthogonally) indecomposable if it has no
non-trivial orthogonal decomposition, that is none with two nonzero summands. As usual, and as
the uniqueness statement below requires, the zero lattice is not indecomposable. A nonzero lattice
is indecomposable exactly when it has no orthogonal decomposition `L = L₁ ⊕ L₂` into two nonzero
summands (`isOrthogonallyIndecomposable_iff`); for such a decomposition, Tau Ceti's
`TauCeti.IntegralLattice.orthogonalSumIsometryOfIsCompl` identifies `L` with the orthogonal sum of
the lattices `L₁` and `L₂`.

The knowl attributes to Kneser the theorem that every lattice has an orthogonal decomposition into
indecomposable summands which is unique up to ordering and isometry of the summands. Existence
holds by induction on the rank, and uniqueness holds for definite lattices, but not for indefinite
ones: with `U` the hyperbolic plane, which is indecomposable, `U ⊕ ⟨-1⟩ ≅ ⟨1⟩ ⊕ ⟨-1⟩ ⊕ ⟨-1⟩`.
Neither statement is formalised here.

## Main definitions

* `TauCeti.IntegralLattice.IsOrthogonalDecomposition` (LMFDB `lattice.orthogonal_decomposition`).
* `TauCeti.IntegralLattice.IsOrthogonallyIndecomposable` (LMFDB
  `lattice.orthogonal_decomposition`).

## Main results

* `TauCeti.IntegralLattice.isOrthogonallyIndecomposable_iff`: a lattice is indecomposable exactly
  when it is nonzero and has no orthogonal decomposition into two nonzero summands.
-/

open LinearMap (BilinForm)

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- An **orthogonal decomposition** (LMFDB `lattice.orthogonal_decomposition`) of an integral
lattice `L`, with integral bilinear form `B`: a family of submodules `L₁, …, L_r` of its carrier
such that `L` is their internal direct sum `L₁ ⊕ ⋯ ⊕ L_r` and `B(x_i, x_j) = 0` for `x_i ∈ L_i`,
`x_j ∈ L_j` and `i ≠ j`. -/
def IsOrthogonalDecomposition {r : ℕ} (S : Fin r → Submodule ℤ L) : Prop :=
  DirectSum.IsInternal S ∧ Pairwise fun i j ↦ ∀ x ∈ S i, ∀ y ∈ S j, L.integralForm x y = 0

/-- An integral lattice `L` is (orthogonally) **indecomposable** (LMFDB
`lattice.orthogonal_decomposition`) if it is nonzero and has no non-trivial orthogonal
decomposition: at most one summand of each of its orthogonal decompositions is nonzero. -/
def IsOrthogonallyIndecomposable : Prop :=
  Nontrivial L ∧ ∀ (r : ℕ) (S : Fin r → Submodule ℤ L), L.IsOrthogonalDecomposition S →
    ∀ i j, S i ≠ ⊥ → S j ≠ ⊥ → i = j

/-- **A lattice is indecomposable exactly when it is nonzero and has no orthogonal decomposition
into two nonzero summands.** -/
lemma isOrthogonallyIndecomposable_iff : L.IsOrthogonallyIndecomposable ↔ Nontrivial L ∧
    ∀ S T : Submodule ℤ L, IsCompl S T → (∀ x ∈ S, ∀ y ∈ T, L.integralForm x y = 0) →
      S = ⊥ ∨ T = ⊥ := by
  refine ⟨fun h ↦ ⟨h.1, fun S T hST horth ↦ ?_⟩, fun h ↦ ⟨h.1, fun r S hS i j hi hj ↦ ?_⟩⟩
  · by_contra! hne
    have hint : DirectSum.IsInternal ![S, T] :=
      (DirectSum.isInternal_submodule_iff_isCompl ![S, T] zero_ne_one
        (by ext k; fin_cases k <;> simp)).mpr hST
    have horth' : Pairwise fun i j ↦ ∀ x ∈ ![S, T] i, ∀ y ∈ ![S, T] j, L.integralForm x y = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      · exact horth
      · exact fun x hx y hy ↦ (L.isSymm_integralForm.eq x y).trans (horth y hy x hx)
    exact zero_ne_one (h.2 2 ![S, T] ⟨hint, horth'⟩ 0 1 hne.1 hne.2)
  · by_contra hij
    have hT : (⨆ (k) (_ : k ≠ i), S k) ≤ L.integralForm.orthogonal (S i) :=
      iSup₂_le fun k hk y hy ↦ BilinForm.mem_orthogonal_iff.mpr fun x hx ↦
        hS.2 (Ne.symm hk) x hx y hy
    have hcompl : IsCompl (S i) (⨆ (k) (_ : k ≠ i), S k) := by
      refine ⟨hS.1.submodule_iSupIndep i, codisjoint_iff.mpr ?_⟩
      rw [← iSup_split_single S i]
      exact hS.1.submodule_iSup_eq_top
    rcases h.2 _ _ hcompl fun x hx y hy ↦ BilinForm.mem_orthogonal_iff.mp (hT hy) x hx
      with h' | h'
    · exact hi h'
    · exact hj (eq_bot_iff.mpr (h' ▸ le_iSup₂ (f := fun k (_ : k ≠ i) ↦ S k) j (Ne.symm hij)))

end TauCeti.IntegralLattice
