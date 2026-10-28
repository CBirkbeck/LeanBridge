import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.ComplexMultiplication
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Jacobian

/-!
# Abelian varieties and curves of `GL₂`-type

A simple abelian variety `A` over a field `K` is of `GL₂`-type if its endomorphism algebra
`End(A) ⊗ ℚ` is commutative of dimension `dim A` over `ℚ`; then it is a number field `E`, and the
rational Tate module `V_ℓ(A)` is free of rank `2` over `E ⊗ ℚ_ℓ` for `ℓ` different from the
characteristic, so that the `ℓ`-adic Galois representation of `A` takes values in
`GL₂(E ⊗ ℚ_ℓ)` (this is not formalised). An abelian variety is of `GL₂`-type if it is isogenous over
`K` to a product of pairwise non-isogenous simple abelian varieties of `GL₂`-type, and a curve is of
`GL₂`-type if its Jacobian is.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.IsSimpleGL2Type` (LMFDB `g2c.gl2type`): simple abelian
  varieties of `GL₂`-type.
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsGL2Type` (LMFDB `g2c.gl2type`): abelian varieties of
  `GL₂`-type.
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsCurveGL2Type` (LMFDB `g2c.gl2type`): curves of
  `GL₂`-type.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] (A : AbelianVariety K)

/-- A simple abelian variety `A` over `K` is **of `GL₂`-type** (LMFDB `g2c.gl2type`) if its
endomorphism algebra `End(A) ⊗ ℚ` is commutative and has dimension `dim A` as a `ℚ`-vector space.
The endomorphisms are those defined over `K`. -/
def IsSimpleGL2Type : Prop :=
  A.IsSimple ∧ (∀ x y : A.EndAlgebra, x * y = y * x) ∧
    (Module.finrank ℚ A.EndAlgebra : WithBot ℕ∞) = A.dim

/-- An abelian variety `A` over `K` is **of `GL₂`-type** (LMFDB `g2c.gl2type`) if it is isogenous
over `K` to a product `B₁ × ⋯ × Bₘ` of pairwise non-isogenous simple abelian varieties of
`GL₂`-type. -/
def IsGL2Type : Prop :=
  ∃ (m : ℕ) (B : Fin m → AbelianVariety K), (∀ i, (B i).IsSimpleGL2Type) ∧
    Pairwise (fun i j ↦ ¬IsIsogenous (B i) (B j)) ∧ IsIsogenous A (∏ᶜ B)

variable {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of K))] [GeometricallyConnected (X ↘ Spec (.of K))]

variable (K X) in
/-- A smooth proper geometrically connected curve `X` over `K` is **of `GL₂`-type** (LMFDB
`g2c.gl2type`) if it has a Jacobian `J` (`IsJacobian`) of `GL₂`-type. -/
def IsCurveGL2Type : Prop :=
  ∃ J : AbelianVariety K, J.IsJacobian X ∧ J.IsGL2Type

end TauCeti.AlgebraicGeometry.AbelianVariety
