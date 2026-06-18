import Mathlib

/-!
# Specification ("def-wanted") for modular curves

This file follows the **Tau Ceti roadmap** convention: it does *not* construct the
modular curve (the genuinely hard part — a coarse moduli space / compact Riemann
surface / smooth projective curve). Instead it records, as Lean target signatures
with `sorry`, the properties that **any** correct construction must satisfy. The
`sorry`s here are *goals, not proofs*: a contributor supplies the object and
discharges the specification, or supplies a candidate definition and checks it
against the spec.

The point: pin down *what the definition must satisfy* so the creative/hard step
(finding the right definition) has a precise, machine-checkable target, without us
having to commit to the construction up front.

## Layers of the spec
1. `IsOpenModularCurve` — the open curve `Y(Γ) = Γ \ ℍ` as a topological quotient.
2. `IsModularCurve` — the compactified curve `X(Γ)`: compact, `Y(Γ)` dense open,
   finitely many cusps.
3. Refinements (analytic/algebraic structure, genus formula, moduli property)
   are flagged as further `sorry` goals to be added as the analytic-geometry API
   in mathlib matures.
-/

namespace LeanBridge.Spec.ModularCurve

open UpperHalfPlane Matrix
open scoped MatrixGroups

/-- Two points of `ℍ` are `Γ`-equivalent when one is carried to the other by some
`γ ∈ Γ ≤ SL(2, ℤ)`. The modular curve is the quotient of `ℍ` by this relation. -/
def OrbitRel (Γ : Subgroup SL(2, ℤ)) (z w : ℍ) : Prop := ∃ γ ∈ Γ, γ • z = w

/-- **Spec of the open modular curve** `Y(Γ) = Γ \ ℍ`.

A type `Y` together with a projection `π : ℍ → Y` *models* the open modular curve of
`Γ` exactly when `π` realises `Y` as the topological quotient of `ℍ` by the `Γ`-action:
it is a continuous open surjection that identifies precisely the `Γ`-equivalent points. -/
structure IsOpenModularCurve (Γ : Subgroup SL(2, ℤ))
    (Y : Type) [TopologicalSpace Y] (π : ℍ → Y) : Prop where
  continuous_proj : Continuous π
  isOpenMap_proj : IsOpenMap π
  surjective_proj : Function.Surjective π
  /-- `π` separates exactly the `Γ`-orbits. -/
  proj_eq_iff : ∀ z w : ℍ, π z = π w ↔ OrbitRel Γ z w

/-- **Spec of the (compactified) modular curve** `X(Γ)`.

`X` with `ι : ℍ → X` models `X(Γ)` when `X` is compact, the open part `Y(Γ) = range ι`
is dense and open and is the quotient `Γ \ ℍ`, and the complement (the **cusps**) is
finite. A complete spec also asks for a compact-Riemann-surface / smooth-projective-curve
structure on `X`, a bijection `cusps ≃ Γ \ ℙ¹(ℚ)`, and the standard genus formula; those
refinements are recorded as separate goals below. -/
structure IsModularCurve (Γ : Subgroup SL(2, ℤ))
    (X : Type) [TopologicalSpace X] (ι : ℍ → X) : Prop where
  compactSpace : CompactSpace X
  continuous_incl : Continuous ι
  isOpenMap_incl : IsOpenMap ι
  denseRange_incl : DenseRange ι
  incl_eq_iff : ∀ z w : ℍ, ι z = ι w ↔ OrbitRel Γ z w
  /-- the cusps `X(Γ) ∖ Y(Γ)` form a finite set. -/
  cusps_finite : (Set.range ι)ᶜ.Finite

/-- **Wanted (existence).** Every finite-index `Γ ≤ SL(2, ℤ)` has an open modular curve.
Discharging this `sorry` means constructing `Γ \ ℍ` with the quotient topology and
verifying the four fields of `IsOpenModularCurve`. -/
theorem wanted_isOpenModularCurve (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (π : ℍ → Y), IsOpenModularCurve Γ Y π := by
  sorry

/-- **Wanted (uniqueness).** The open modular curve is unique up to homeomorphism
compatible with the projections — this is what makes it well defined. -/
theorem wanted_isOpenModularCurve_unique (Γ : Subgroup SL(2, ℤ))
    {Y₁ Y₂ : Type} [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    {π₁ : ℍ → Y₁} {π₂ : ℍ → Y₂}
    (_h₁ : IsOpenModularCurve Γ Y₁ π₁) (_h₂ : IsOpenModularCurve Γ Y₂ π₂) :
    ∃ e : Y₁ ≃ₜ Y₂, ⇑e ∘ π₁ = π₂ := by
  sorry

/-- **Wanted (compactification).** Every finite-index `Γ` has a compact modular curve
`X(Γ)` containing `Y(Γ)` as a dense open subset with finite complement. -/
theorem wanted_isModularCurve (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (X : Type) (_ : TopologicalSpace X) (ι : ℍ → X), IsModularCurve Γ X ι := by
  sorry

/-!
## Further refinements (to add as mathlib's complex-geometry API grows)

* **Analytic structure.** `X(Γ)` carries a compact Riemann surface structure for which
  `ι` is holomorphic and biholomorphic onto `Y(Γ)`.
* **Cusp count.** `cusps ≃ Γ \ ℙ¹(ℚ)` (the `Γ`-orbits of the rational boundary points).
* **Genus formula.** `genus (X Γ) = 1 + d/12 − e₂/4 − e₃/3 − e∞/2`, where `d = [SL(2,ℤ) : Γ]`
  and `e₂, e₃, e∞` count elliptic points of order 2, 3 and cusps.
* **Moduli property (level `N`).** `X(Γ(N))` is the coarse moduli space of elliptic
  curves with full level-`N` structure: there is a natural bijection between
  `Y(Γ(N))(ℂ)` and isomorphism classes of pairs `(E, (P, Q))` where `(P, Q)` is a
  symplectic basis of `E[N]`.

Each becomes its own `IsModularCurve`-style field or `wanted_*` goal once the
prerequisite mathlib API (`compact Riemann surface`, moduli of elliptic curves) exists.
-/

end LeanBridge.Spec.ModularCurve
