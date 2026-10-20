import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Automorphism

/-!
# Genus 2 curves

Every smooth projective geometrically integral curve of genus two over a field `K` is defined by a
Weierstrass equation `y² + h(x)y = f(x)` with `deg h ≤ 3`, `deg f ≤ 6` and nonzero discriminant.
We take such an equation as the definition of a genus 2 curve, when `K` has characteristic not two,
and check that its function field has genus two and is hyperelliptic.

## Main definitions

* `GenusTwoCurve` (LMFDB `g2c.g2curve`): genus 2 curves, given by their Weierstrass equations.

## Main results

* `GenusTwoCurve.genus_functionField`: a genus 2 curve has genus two.
* `GenusTwoCurve.isHyperellipticFunctionField`: a genus 2 curve is hyperelliptic.
* `GenusTwoCurve.orderOf_hyperellipticInvolution` and `GenusTwoCurve.nontrivial_algEquiv`
  (LMFDB `g2c.aut_grp`): the hyperelliptic involution of a genus 2 curve has order two, so its
  automorphism group is never trivial.
-/

variable {K : Type*} [Field K] [Invertible (2 : K)]

variable (K) in
/-- A **genus 2 curve** over a field `K` of characteristic not two (LMFDB `g2c.g2curve`), given by a
Weierstrass equation `y² + h(x)y = f(x)` with `deg h ≤ 3`, `deg f ≤ 6` and nonzero discriminant.
Its function field `K(x, y)` has genus two (`GenusTwoCurve.genus_functionField`), and `x` exhibits
it as a hyperelliptic function field (`GenusTwoCurve.isHyperellipticFunctionField`). -/
structure GenusTwoCurve extends HyperellipticEquation 2 K where
  /-- The discriminant of the Weierstrass equation of a genus 2 curve is nonzero. -/
  discriminant_ne_zero : toHyperellipticEquation.discriminant ≠ 0

namespace GenusTwoCurve

variable (C : GenusTwoCurve K)

instance : Fact (Irreducible C.equationPolynomial) :=
  ⟨HyperellipticEquation.irreducible_equationPolynomial C.discriminant_ne_zero⟩

/-- **A genus 2 curve has genus two**: its function field has genus two. -/
lemma genus_functionField : TauCeti.genus K C.FunctionField = 2 :=
  HyperellipticEquation.genus_functionField C.discriminant_ne_zero

/-- **A genus 2 curve is hyperelliptic**: `K(x)` is a rational subfield of index two of its
function field. -/
lemma isHyperellipticFunctionField : TauCeti.IsHyperellipticFunctionField K C.FunctionField :=
  HyperellipticEquation.isHyperellipticFunctionField C.discriminant_ne_zero le_rfl

/-- **The hyperelliptic involution of a genus 2 curve has order two.** -/
lemma orderOf_hyperellipticInvolution : orderOf C.hyperellipticInvolution = 2 :=
  HyperellipticEquation.orderOf_hyperellipticInvolution C.discriminant_ne_zero

/-- **The automorphism group of a genus 2 curve is never trivial.** -/
lemma nontrivial_algEquiv : Nontrivial (C.FunctionField ≃ₐ[K] C.FunctionField) :=
  HyperellipticEquation.nontrivial_algEquiv C.discriminant_ne_zero

end GenusTwoCurve
