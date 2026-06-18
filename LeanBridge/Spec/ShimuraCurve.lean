import Mathlib

/-!
# Specification ("def-wanted") for Shimura curves

Tau-Ceti-style spec: we do not construct Shimura curves; we record the properties any
correct construction must satisfy, as `sorry`-ed goals (goals, not proofs).

A **Shimura curve** is the quotient `Γ \ ℍ` where `Γ ≤ SL(2,ℝ)` is the image of the
norm-1 units of a maximal order in an *indefinite* quaternion algebra `B/ℚ` (split at
the archimedean place, via `B ⊗ ℝ ≅ M₂(ℝ)`). When `B` is a division algebra the quotient
is **compact with no cusps** — the key contrast with modular curves.

The quaternion algebra, its maximal order, the unit group, and the splitting
`B ⊗ ℝ ≅ M₂(ℝ)` are *all* themselves def-wanted; we package "‍`Γ` arises this way" as the
opaque predicate `IsQuaternionic` to be supplied later.
-/

namespace LeanBridge.Spec.ShimuraCurve

open UpperHalfPlane Matrix
open scoped MatrixGroups

/-- Orbit relation of `Γ ≤ SL(2,ℝ)` on `ℍ`. -/
def OrbitRel (Γ : Subgroup SL(2, ℝ)) (z w : ℍ) : Prop := ∃ γ ∈ Γ, γ • z = w

/-- **Wanted data.** `Γ ≤ SL(2,ℝ)` is (the image of) the norm-1 unit group of a maximal
order in an indefinite quaternion *division* algebra over `ℚ`. Supplying this means
constructing the quaternion algebra, the order, its units, and the real splitting. -/
opaque IsQuaternionic (Γ : Subgroup SL(2, ℝ)) : Prop

/-- **Spec of a (compact) Shimura curve** `X = Γ \ ℍ`. As `Γ` is cocompact (division case),
`ι` is already surjective — there are no cusps to adjoin. A complete spec also asks for a
compact-Riemann-surface structure with `ι` holomorphic, and the genus via the
Riemann–Hurwitz/area formula; these are recorded as further goals. -/
structure IsShimuraCurve (Γ : Subgroup SL(2, ℝ))
    (X : Type) [TopologicalSpace X] (ι : ℍ → X) : Prop where
  compactSpace : CompactSpace X
  continuous_incl : Continuous ι
  isOpenMap_incl : IsOpenMap ι
  surjective_incl : Function.Surjective ι
  incl_eq_iff : ∀ z w : ℍ, ι z = ι w ↔ OrbitRel Γ z w

/-- **Wanted (existence).** A quaternionic `Γ` has a compact Shimura curve `Γ \ ℍ`. -/
theorem wanted_isShimuraCurve (Γ : Subgroup SL(2, ℝ)) (_h : IsQuaternionic Γ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (ι : ℍ → X), IsShimuraCurve Γ X ι := by
  sorry

/-- **Wanted (uniqueness).** The Shimura curve is unique up to homeomorphism over the
projection, hence well defined. -/
theorem wanted_isShimuraCurve_unique (Γ : Subgroup SL(2, ℝ))
    {X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂]
    {ι₁ : ℍ → X₁} {ι₂ : ℍ → X₂}
    (_h₁ : IsShimuraCurve Γ X₁ ι₁) (_h₂ : IsShimuraCurve Γ X₂ ι₂) :
    ∃ e : X₁ ≃ₜ X₂, ⇑e ∘ ι₁ = ι₂ := by
  sorry

end LeanBridge.Spec.ShimuraCurve
