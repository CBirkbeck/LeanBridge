import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.FunctionField

/-!
# The hyperelliptic involution

The automorphism group `Aut(X)` of a curve `X` over `K` acts on its function field by pull-back,
which identifies `Aut(X)` with the opposite of the group of `K`-automorphisms of the function field.
The curve defined by a Weierstrass equation `y² + h(x)y = f(x)` has the hyperelliptic involution
`(x, y) ↦ (x, -y - h(x))`, which is not the identity when the discriminant is nonzero, so the
automorphism group of a genus 2 curve is never trivial.

## Main definitions

* `HyperellipticEquation.hyperellipticInvolutionHom`: the `K(x)`-algebra endomorphism
  `y ↦ -y - h(x)` of the function field.
* `HyperellipticEquation.hyperellipticInvolution` (LMFDB `g2c.aut_grp`): the hyperelliptic
  involution, as a `K`-automorphism of the function field.

## Main results

* `HyperellipticEquation.hyperellipticInvolution_mul_self`: the hyperelliptic involution is an
  involution.
* `HyperellipticEquation.hyperellipticInvolution_ne_one`: it is not the identity when the
  discriminant is nonzero.
* `HyperellipticEquation.orderOf_hyperellipticInvolution`: it has order two.
* `HyperellipticEquation.nontrivial_algEquiv`: the automorphism group is nontrivial.
-/

open Polynomial

namespace HyperellipticEquation

variable {g : ℕ} {K : Type*} [Field K] (E : HyperellipticEquation g K)

/-- The `K(x)`-algebra endomorphism `y ↦ -y - h(x)` of the function field of a Weierstrass equation
`y² + h(x)y = f(x)`. -/
noncomputable def hyperellipticInvolutionHom : E.FunctionField →ₐ[RatFunc K] E.FunctionField :=
  AdjoinRoot.liftAlgHom E.equationPolynomial (Algebra.ofId _ _)
    (-E.y - algebraMap (RatFunc K) E.FunctionField (algebraMap K[X] _ E.h)) <|
    (E.aeval_equationPolynomial _).trans <| by linear_combination E.y_sq_add

lemma hyperellipticInvolutionHom_y : E.hyperellipticInvolutionHom E.y = -E.y - algebraMap (RatFunc
    K) E.FunctionField (algebraMap K[X] _ E.h) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma hyperellipticInvolutionHom_comp_self :
    E.hyperellipticInvolutionHom.comp E.hyperellipticInvolutionHom = AlgHom.id _ _ := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, ← y, hyperellipticInvolutionHom_y, map_sub, map_neg,
    hyperellipticInvolutionHom_y, AlgHom.commutes, AlgHom.id_apply]
  ring1

/-- The **hyperelliptic involution** `(x, y) ↦ (x, -y - h(x))` of the curve defined by a Weierstrass
equation `y² + h(x)y = f(x)` (LMFDB `g2c.aut_grp`), as an automorphism of its function field over
`K` fixing `K(x)`; the LMFDB writes it `(x, y) ↦ (x, -y)`, for equations with `h = 0`. The
automorphism group `Aut(X)` of the curve is the opposite of the group of `K`-automorphisms of its
function field, on which automorphisms act by pull-back. -/
noncomputable def hyperellipticInvolution : E.FunctionField ≃ₐ[K] E.FunctionField :=
  (AlgEquiv.ofAlgHom E.hyperellipticInvolutionHom E.hyperellipticInvolutionHom
    E.hyperellipticInvolutionHom_comp_self E.hyperellipticInvolutionHom_comp_self).restrictScalars K

lemma hyperellipticInvolution_y : E.hyperellipticInvolution E.y = -E.y - algebraMap (RatFunc K)
    E.FunctionField (algebraMap K[X] _ E.h) :=
  E.hyperellipticInvolutionHom_y

lemma hyperellipticInvolution_algebraMap (r : RatFunc K) : E.hyperellipticInvolution (algebraMap
    (RatFunc K) E.FunctionField r) = algebraMap (RatFunc K) E.FunctionField r :=
  E.hyperellipticInvolutionHom.commutes r

/-- **The hyperelliptic involution is an involution.** -/
lemma hyperellipticInvolution_mul_self :
    E.hyperellipticInvolution * E.hyperellipticInvolution = 1 :=
  AlgEquiv.ext fun x ↦ AlgHom.congr_fun E.hyperellipticInvolutionHom_comp_self x

variable [Invertible (2 : K)] {E} (hE : E.discriminant ≠ 0)

include hE

/-- **The hyperelliptic involution of an equation with nonzero discriminant is not the identity**:
it fixes `y` only if `w = 2y + h(x)` vanishes, but `w² = 4f + h²` is nonzero. -/
lemma hyperellipticInvolution_ne_one : E.hyperellipticInvolution ≠ 1 := by
  have : Fact (Irreducible E.equationPolynomial) := ⟨irreducible_equationPolynomial hE⟩
  intro h
  have hy : E.hyperellipticInvolution E.y = E.y := by rw [h, AlgEquiv.one_apply]
  have hw : E.w = 0 := by
    rw [hyperellipticInvolution_y] at hy
    rw [w]
    linear_combination -hy
  have hF : E.simplifiedPolynomial = 0 := by
    have h₀ : algebraMap (RatFunc K) E.FunctionField (algebraMap K[X] _ E.simplifiedPolynomial) =
        algebraMap (RatFunc K) E.FunctionField (algebraMap K[X] _ 0) := by
      rw [← E.w_sq, hw, map_zero, map_zero, zero_pow two_ne_zero]
    exact IsFractionRing.injective K[X] (RatFunc K) ((algebraMap (RatFunc K) _).injective h₀)
  rcases natDegree_simplifiedPolynomial_eq hE with h | h <;> simp [hF] at h

/-- **The hyperelliptic involution has order two** when the discriminant is nonzero. -/
lemma orderOf_hyperellipticInvolution : orderOf E.hyperellipticInvolution = 2 :=
  orderOf_eq_prime (by rw [sq, hyperellipticInvolution_mul_self])
    (hyperellipticInvolution_ne_one hE)

/-- **The automorphism group of the function field of an equation with nonzero discriminant is
nontrivial**: it contains the hyperelliptic involution. -/
lemma nontrivial_algEquiv : Nontrivial (E.FunctionField ≃ₐ[K] E.FunctionField) :=
  ⟨⟨E.hyperellipticInvolution, 1, hyperellipticInvolution_ne_one hE⟩⟩

end HyperellipticEquation
