import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Monodromy

/-!
# The signature of a group of automorphisms of a Riemann surface

Let `G` be a finite group of automorphisms of a compact Riemann surface `X`, let `φ : X → Y = X/G`
be the natural projection, `g₀` the genus of `Y` and `B = {y₁, …, y_r}` the set of branch points
of `φ`. For standard generators `γ₁, …, γ_r` of `π₁(Y - B, y₀)` at the points of `B`, lifting
`γ_i` to `X - φ⁻¹(B)` permutes the fibre `φ⁻¹(y₀)`; with `m₁ ≤ ⋯ ≤ m_r` the orders of these
permutations, the signature (LMFDB `curve.highergenus.aut.signature`) of the action is
`[g₀; m₁, …, m_r]`.

Here the list `m₁ ≤ ⋯ ≤ m_r` is the multiset of the orders of the monodromy permutations
(`MulAction.monodromyGroup`) of a family `(γ_b)_{b ∈ B}` meant to be standard generators
(`TauCeti.RiemannSurface.IsStandardGeneratingSystem`). The complex structure of `Y`, which is not
constructed here, is taken as given, and so is its genus `g₀`, since the genus of a compact Riemann
surface is not available (the LMFDB quotient genus is formalised for function fields, as Tau
Ceti's `TauCeti.genus`). That the periods do not depend on the choice of standard generators, as
a change of path conjugates a standard generator, and that each `m_i` is the order of the
stabiliser of a point over `y_i`, are not formalised.

## Main definitions

* `MulAction.signaturePeriods` (LMFDB `curve.highergenus.aut.signature`): the periods
  `m₁, …, m_r`.
* `MulAction.signature` (LMFDB `curve.highergenus.aut.signature`): the signature `[g₀; m₁, …, m_r]`.

## Main results

* `MulAction.card_signaturePeriods`: there is one period for each branch point.
-/

namespace MulAction

variable (G X : Type*) [Group G] [MulAction G X] [Finite G] [TopologicalSpace X]
  [ContinuousConstSMul G X] [T2Space X] [LocallyCompactSpace X] [Finite (branchPoints G X)]
  {y₀ : ↥(branchPoints G X)ᶜ} (γ : branchPoints G X → FundamentalGroup ↥(branchPoints G X)ᶜ y₀)

/-- The **periods** `m₁ ≤ ⋯ ≤ m_r` of the signature (LMFDB `curve.highergenus.aut.signature`) of a
finite group `G` acting on a space `X`, such as a group of automorphisms of a compact Riemann
surface, relative to a family `(γ_b)_{b ∈ B}` of elements of `π₁(Y - B, y₀)`, where `Y = X/G` and
`B` is the finite set of branch points: the multiset of the orders of the monodromy permutations of
the fibre over `y₀` given by the `γ_b`. The LMFDB takes for `γ` standard generators
(`TauCeti.RiemannSurface.IsStandardGeneratingSystem`, for a complex structure on `Y`). -/
noncomputable def signaturePeriods : Multiset ℕ :=
  letI : Fintype (branchPoints G X) := Fintype.ofFinite _
  Finset.univ.val.map fun b ↦
    orderOf ((isCoveringMap_unbranchedProjection G X).monodromyPerm y₀ (γ b))

/-- The **signature** `[g₀; m₁, …, m_r]` (LMFDB `curve.highergenus.aut.signature`) of a finite group
`G` acting on a space `X`, such as a group of automorphisms of a compact Riemann surface: the genus
`g₀` of the quotient `Y = X/G`, which is supplied, and the periods `m₁ ≤ ⋯ ≤ m_r`
(`MulAction.signaturePeriods`) relative to standard generators `γ` of `π₁(Y - B, y₀)`. -/
noncomputable def signature (g₀ : ℕ) : ℕ × Multiset ℕ :=
  (g₀, signaturePeriods G X γ)

/-- **There is one period for each branch point.** -/
lemma card_signaturePeriods : (signaturePeriods G X γ).card = Nat.card (branchPoints G X) := by
  simp [signaturePeriods]

end MulAction
