import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Basic

/-!
# Similarity of integral lattices

Lattices `L` and `M` are similar (LMFDB `lattice.similarity`) if `L` is isometric to `αM` for a real
constant `α ≠ 0`. Scaling the vectors of `M` by `α` multiplies its bilinear form by `α²`, so for
integral lattices, whose forms are rational, `L` and `M` are similar exactly when there is a
rational linear equivalence of the ambient spaces carrying `L` onto `M` and multiplying the form by
a positive rational constant `c`, namely `c = α⁻²`. This is the definition used here; it makes
sense in rational spaces, where `αM` need not. Similarity is an equivalence relation. The
preservation of well-roundedness, eutaxy, perfection and density, and the uniqueness of a
primitive integral lattice in a similarity class, are not formalised.

## Main definitions

* `TauCeti.IntegralLattice.IsSimilar` (LMFDB `lattice.similarity`).

## Main results

* `TauCeti.IntegralLattice.Isometry.isSimilar`: isometric lattices are similar.
* `TauCeti.IntegralLattice.IsSimilar.symm` and `TauCeti.IntegralLattice.IsSimilar.trans`:
  similarity is symmetric and transitive.
-/

namespace TauCeti.IntegralLattice

variable {V W U : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  [AddCommGroup U] [Module ℚ U] {L : IntegralLattice V} {M : IntegralLattice W}
  {N : IntegralLattice U}

variable (L M) in
/-- Integral lattices `L` and `M` are **similar** (LMFDB `lattice.similarity`) if `L` is isometric
to `αM` for a real constant `α ≠ 0`: some rational linear equivalence `e` of the ambient spaces
carries the carrier of `L` onto that of `M` and satisfies `B_M(e x, e y) = c B_L(x, y)` for a
positive rational constant `c`, which is `α⁻²`. -/
def IsSimilar : Prop :=
  ∃ c : ℚ, 0 < c ∧ ∃ e : V ≃ₗ[ℚ] W, L.carrier.map (e.restrictScalars ℤ).toLinearMap = M.carrier ∧
    ∀ x y, M.form (e x) (e y) = c * L.form x y

lemma IsSimilar.refl : L.IsSimilar L :=
  ⟨1, one_pos, .refl ℚ V, by simp, by simp⟩

/-- **Isometric lattices are similar.** -/
lemma Isometry.isSimilar (e : L.Isometry M) : L.IsSimilar M :=
  ⟨1, one_pos, e, e.map_carrier, fun x y ↦ by simp⟩

/-- **Similarity is symmetric.** -/
lemma IsSimilar.symm (h : L.IsSimilar M) : M.IsSimilar L := by
  rcases h with ⟨c, hc, e, he, hf⟩
  refine ⟨c⁻¹, inv_pos.mpr hc, e.symm, ?_, fun x y ↦ ?_⟩
  · rw [← he, ← Submodule.map_comp]
    exact (congrArg (L.carrier.map ·) (LinearMap.ext e.symm_apply_apply)).trans L.carrier.map_id
  · have h : M.form x y = c * L.form (e.symm x) (e.symm y) := by
      simpa using hf (e.symm x) (e.symm y)
    rw [h, inv_mul_cancel_left₀ hc.ne']

/-- **Similarity is transitive.** -/
lemma IsSimilar.trans (h : L.IsSimilar M) (h' : M.IsSimilar N) : L.IsSimilar N := by
  rcases h with ⟨c, hc, e, he, hf⟩
  rcases h' with ⟨c', hc', e', he', hf'⟩
  refine ⟨c' * c, mul_pos hc' hc, e.trans e', ?_, fun x y ↦ ?_⟩
  · rw [← he', ← he, ← Submodule.map_comp]
    rfl
  · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hf', hf, mul_assoc]

end TauCeti.IntegralLattice
