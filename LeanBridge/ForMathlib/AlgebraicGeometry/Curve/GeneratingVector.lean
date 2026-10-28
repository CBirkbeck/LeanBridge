import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Monodromy
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.StandardGenerators

/-!
# Generating vectors of a group of automorphisms of a Riemann surface

Let `G` be a finite group of automorphisms of a compact Riemann surface `X`, let `φ : X → Y = X/G`
be the natural projection, `B ⊆ Y` its set of branch points and `y₀ ∈ Y - B`. The monodromy of the
covering `X - φ⁻¹(B) → Y - B` is a homomorphism `ρ : π₁(Y - B, y₀) → S_d` to the permutations of
the fibre `φ⁻¹(y₀)`, of `d = |G|` points, whose image is the monodromy group. A generating vector
of `G` is the family `(ρ(γ_b))_{b ∈ B}` of the images of standard generators `(γ_b)_{b ∈ B}` of
`π₁(Y - B, y₀)` (LMFDB `curve.highergenus.aut.generators`); it generates the monodromy group.

As in `LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Monodromy`, `X` is any locally compact
Hausdorff space with a continuous action of a finite group `G`. The complex structure of `Y = X/G`,
needed for the standard generators, is given as a `ChartedSpace ℂ` instance on the space of orbits;
for a compact Riemann surface it is the quotient Riemann surface. A generating vector is a
`B`-indexed family, the LMFDB's list being the family in the order of `B` in which the standard
generators multiply to `1`. The LMFDB takes `Y` of genus `0`, as in the knowl of standard
generators, so no hyperbolic generators `a_i, b_i` occur.

## Main definitions

* `MulAction.IsGeneratingVector` (LMFDB `curve.highergenus.aut.generatingvector`): generating
  vectors of `G`.
-/

open TauCeti RiemannSurface

namespace MulAction

variable (G X : Type*) [Group G] [MulAction G X] [Finite G] [TopologicalSpace X]
  [ContinuousConstSMul G X] [T2Space X] [LocallyCompactSpace X]
  [ChartedSpace ℂ (orbitRel.Quotient G X)]

/-- A **generating vector** (LMFDB `curve.highergenus.aut.generatingvector`) of a finite group `G`
acting on a space `X`, such as a group of automorphisms of a compact Riemann surface, at a base
point `y₀` of `Y - B`, where `Y = X/G` and `B` is the set of branch points of `φ : X → Y`: a family
`(ρ(γ_b))_{b ∈ B}` of permutations of the fibre `φ⁻¹(y₀)` that are the images of standard
generators `(γ_b)_{b ∈ B}` of `π₁(Y - B, y₀)` under the monodromy `ρ` of `X - φ⁻¹(B) → Y - B`. -/
def IsGeneratingVector (y₀ : ↥(branchPoints G X)ᶜ)
    (v : branchPoints G X → Equiv.Perm (unbranchedProjection G X ⁻¹' {y₀})) : Prop :=
  ∃ γ, IsStandardGeneratingSystem y₀ γ ∧
    ∀ b, (isCoveringMap_unbranchedProjection G X).monodromyPerm y₀ (γ b) = v b

end MulAction
