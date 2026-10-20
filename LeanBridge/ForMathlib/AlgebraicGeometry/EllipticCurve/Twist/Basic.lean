import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic

/-!
# Twists of elliptic curves

A twist of an elliptic curve `W` over a field `K` is a curve over `K` which is isomorphic to `W`
over an algebraic closure `K̄` of `K`. Two elliptic curves are twists of each other exactly when
they have the same `j`-invariant.

When `j(W) ∉ {0, 1728}`, the twists of `W` are `W` and its quadratic twists
`WeierstrassCurve.quadraticTwist` by the separable quadratic extensions `L/K`, two of which are
isomorphic over `K` exactly when the extensions are equal: this is Tau Ceti's
`WeierstrassCurve.exists_smul_eq_or_exists_smul_eq_quadraticTwist_of_j_eq` and
`WeierstrassCurve.exists_smul_quadraticTwist_eq_quadraticTwist_iff`. In characteristic not `2`
these extensions are the `K(√d)` for `d` in `K*/(K*)²`. The quartic twists of the curves with
`j`-invariant `1728` and the sextic twists of the curves with `j`-invariant `0` are in
`LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Twist.QuarticSextic`. In general, Tau Ceti's
`WeierstrassCurve.VariableChange.twistCohomologyClass` attaches to a twist its class in
`H¹(Gal(K̄/K), Aut W)`, and twists with the same class are isomorphic over `K`.

## Main definitions

* `WeierstrassCurve.IsTwist` (LMFDB `ec.twists`): the curves are isomorphic over `K̄`.

## Main results

* `WeierstrassCurve.isTwist_iff_j_eq`: two elliptic curves are twists of each other exactly when
  they have the same `j`-invariant.
* `WeierstrassCurve.isTwist_quadraticTwist`: a quadratic twist of an elliptic curve is a twist.
-/

namespace WeierstrassCurve

variable {K : Type*} [Field K] {W W' W'' : WeierstrassCurve K}

variable (W W') in
/-- A Weierstrass curve `W'` over a field `K` is a **twist** (LMFDB `ec.twists`) of `W` if it is
isomorphic to `W` over an algebraic closure `K̄` of `K`: a change of variables over `K̄` carries
`W` to `W'`. Two elliptic curves are twists of each other exactly when they have the same
`j`-invariant (`isTwist_iff_j_eq`). -/
def IsTwist : Prop :=
  ∃ C : VariableChange (AlgebraicClosure K), C • W.map (algebraMap K (AlgebraicClosure K)) =
    W'.map (algebraMap K (AlgebraicClosure K))

variable (h : W.IsTwist W')

variable (W) in
@[refl]
lemma IsTwist.refl : W.IsTwist W :=
  ⟨1, one_smul _ _⟩

include h in
@[symm]
lemma IsTwist.symm : W'.IsTwist W :=
  h.elim fun C hC ↦ ⟨C⁻¹, hC ▸ inv_smul_smul C _⟩

include h in
@[trans]
lemma IsTwist.trans (h' : W'.IsTwist W'') : W.IsTwist W'' :=
  h.elim fun C hC ↦ h'.elim fun C' hC' ↦ ⟨C' * C, by rw [mul_smul, hC, hC']⟩

lemma isTwist_smul (C : VariableChange K) : W.IsTwist (C • W) :=
  ⟨C.map (algebraMap K (AlgebraicClosure K)), by rw [map_variableChange]⟩

variable [W.IsElliptic]

/-- **Two elliptic curves are twists of each other exactly when they have the same
`j`-invariant**: over the algebraically closed field `K̄`, curves with the same `j`-invariant are
isomorphic. -/
lemma isTwist_iff_j_eq [W'.IsElliptic] : W.IsTwist W' ↔ W.j = W'.j := by
  refine ⟨fun ⟨C, hC⟩ ↦ (algebraMap K (AlgebraicClosure K)).injective ?_, fun h ↦
    exists_variableChange_of_j_eq _ _ <| by rw [map_j, map_j, h]⟩
  simp only [← map_j, ← hC, variableChange_j]

/-- **A quadratic twist of an elliptic curve is a twist**: it has the same `j`-invariant. -/
lemma isTwist_quadraticTwist (L : Type*) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L] : W.IsTwist (W.quadraticTwist L) :=
  isTwist_iff_j_eq.mpr (W.j_quadraticTwist L).symm

end WeierstrassCurve
