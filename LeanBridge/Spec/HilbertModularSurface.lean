import Mathlib

/-!
# Specification ("def-wanted") for Hilbert modular surfaces

Tau-Ceti-style spec: properties any correct construction must satisfy, as `sorry`-ed
goals — not a construction.

Per the LMFDB (`hmsurface.hmsurface`): for a real quadratic field `F`, a congruence
subgroup `Γ < GL₂⁺(F)` acts on `ℍ × ℍ` via the two real embeddings of `F`
(`γ · (z₁, z₂) = (σ₁(γ)·z₁, σ₂(γ)·z₂)`). The projective surface with complex points
`Γ \ (ℍ × ℍ)` is canonically defined over the reflex field of `F`; the **Hilbert modular
surface** `X(Γ)` is its **minimal desingularization** — smooth, projective, geometrically
integral. It parametrizes abelian surfaces with real multiplication by `F` together with
level structure.

The basic case `Γ = SL(2, 𝒪_F)` is the prototype modelled below. The field `F`, the
embeddings, and the homomorphism into `SL(2,ℝ) × SL(2,ℝ)` are themselves def-wanted; we
package "‍`Γ` is (the image of) such a Hilbert modular group" as the opaque predicate
`IsHilbertModular`. (A full spec would also record the minimal-desingularization and
moduli properties; those are deferred until the prerequisite algebraic-geometry API
exists, as for the modular-curve spec.)
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
