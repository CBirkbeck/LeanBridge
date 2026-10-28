import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Signature

/-!
# The dimension of a family of curves with given signature

Let `G` be a group of automorphisms of a curve `X` over `ℂ`, with signature `[g₀; m₁, …, m_r]`
(`MulAction.signature`): `g₀` is the genus of the quotient `X/G` and `r` the number of branch points
of `X → X/G`. The dimension of the family of curves with this signature is `3g₀ + r - 3`, the
dimension of the moduli space of genus `g₀` curves with `r` marked points. It is defined here as
this number, an integer since it is `-3` for `g₀ = r = 0`; its meaning as the dimension of a locus
in the moduli space of curves is not formalised.

## Main definitions

* `MulAction.signatureDimension` (LMFDB `curve.highergenus.aut.dimension`): the dimension
  `3g₀ + r - 3` attached to a signature `[g₀; m₁, …, m_r]`.

## Main results

* `MulAction.signatureDimension_signature`: for a group action, the dimension is `3g₀ + r - 3` with
  `r` the number of branch points.
-/

namespace MulAction

/-- The **dimension** (LMFDB `curve.highergenus.aut.dimension`) of the family of curves with a given
signature `[g₀; m₁, …, m_r]`, written as the pair `(g₀, {m₁, …, m_r})` as in `MulAction.signature`:
the integer `3g₀ + r - 3`. -/
def signatureDimension (σ : ℕ × Multiset ℕ) : ℤ :=
  3 * σ.1 + σ.2.card - 3

variable (G X : Type*) [Group G] [MulAction G X] [Finite G] [TopologicalSpace X]
  [ContinuousConstSMul G X] [T2Space X] [LocallyCompactSpace X] [Finite (branchPoints G X)]
  {y₀ : ↥(branchPoints G X)ᶜ} (γ : branchPoints G X → FundamentalGroup ↥(branchPoints G X)ᶜ y₀)

/-- **The dimension of the family of curves with the signature of a group action** is `3g₀ + r - 3`,
where `g₀` is the genus of the quotient and `r` the number of branch points. -/
lemma signatureDimension_signature (g₀ : ℕ) :
    signatureDimension (signature G X γ g₀) = 3 * g₀ + Nat.card (branchPoints G X) - 3 := by
  simp [signatureDimension, signature, card_signaturePeriods]

end MulAction
