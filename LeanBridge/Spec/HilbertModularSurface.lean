import Mathlib

/-!
# Specification ("def-wanted") for Hilbert modular surfaces

Tau-Ceti-style spec: properties any correct construction must satisfy, as `sorry`-ed
goals — not a construction.

For a real quadratic field `F` with the two real embeddings `σ₁, σ₂ : F ↪ ℝ`, the
**Hilbert modular group** `SL(2, 𝒪_F)` acts on `ℍ × ℍ` by `γ · (z₁, z₂) = (σ₁(γ)·z₁, σ₂(γ)·z₂)`.
The **Hilbert modular surface** is the (compactified) quotient `SL(2, 𝒪_F) \ (ℍ × ℍ)` — a
complex surface, singular at finitely many cusps and elliptic points.

The field `F`, the embeddings, and the homomorphism `SL(2, 𝒪_F) → SL(2,ℝ) × SL(2,ℝ)` are
themselves def-wanted; we package "‍`Γ ≤ SL(2,ℝ) × SL(2,ℝ)` is the image of a Hilbert
modular group" as the opaque predicate `IsHilbertModular`.
-/

namespace LeanBridge.Spec.HilbertModularSurface

open UpperHalfPlane Matrix
open scoped MatrixGroups

/-- Orbit relation of `Γ ≤ SL(2,ℝ) × SL(2,ℝ)` on `ℍ × ℍ`, acting component-wise. -/
def OrbitRel (Γ : Subgroup (SL(2, ℝ) × SL(2, ℝ))) (z w : ℍ × ℍ) : Prop :=
  ∃ γ ∈ Γ, (γ.1 • z.1, γ.2 • z.2) = w

/-- **Wanted data.** `Γ` is the image of a Hilbert modular group `SL(2, 𝒪_F)` (for a real
quadratic field `F`) under its two real embeddings into `SL(2,ℝ) × SL(2,ℝ)`. -/
opaque IsHilbertModular (Γ : Subgroup (SL(2, ℝ) × SL(2, ℝ))) : Prop

/-- **Spec of the (compactified) Hilbert modular surface** `X = Γ \ (ℍ × ℍ)^*`.

`X` is compact; the open part `Y = range ι` is dense and open and is the quotient
`Γ \ (ℍ × ℍ)`; the complement (cusps) is finite. A complete spec further asks for the
structure of a normal projective complex surface (with quotient singularities resolved),
the cusp count `= |Γ \ ℙ¹(F)|`, and the volume/Euler-characteristic formula. -/
structure IsHilbertModularSurface (Γ : Subgroup (SL(2, ℝ) × SL(2, ℝ)))
    (X : Type) [TopologicalSpace X] (ι : ℍ × ℍ → X) : Prop where
  compactSpace : CompactSpace X
  continuous_incl : Continuous ι
  isOpenMap_incl : IsOpenMap ι
  denseRange_incl : DenseRange ι
  incl_eq_iff : ∀ z w : ℍ × ℍ, ι z = ι w ↔ OrbitRel Γ z w
  cusps_finite : (Set.range ι)ᶜ.Finite

/-- **Wanted (existence).** A Hilbert modular `Γ` has a compact Hilbert modular surface. -/
theorem wanted_isHilbertModularSurface (Γ : Subgroup (SL(2, ℝ) × SL(2, ℝ)))
    (_h : IsHilbertModular Γ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (ι : ℍ × ℍ → X), IsHilbertModularSurface Γ X ι := by
  sorry

end LeanBridge.Spec.HilbertModularSurface
