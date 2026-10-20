import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Basic

/-!
# `ℚ`-curves

An elliptic curve `W` over a number field `K` is a `ℚ`-curve if it is isogenous, over an algebraic
closure `K̄` of `K`, to each of its Galois conjugates. The Galois conjugates of `W` are the curves
`W^σ = W.map σ` for the embeddings `σ : K → K̄`, and `W` itself is `W^ι` for the inclusion
`ι : K → K̄`. The isogenies need not be defined over `K`.

## Main definitions

* `WeierstrassCurve.IsQCurve` (LMFDB `ec.q_curve`): the curve is isogenous over `K̄` to each of its
  Galois conjugates.

## Main results

* `WeierstrassCurve.isQCurve_baseChange`: the base change of a curve over `ℚ` is a `ℚ`-curve.
* `WeierstrassCurve.isQCurve_of_j_eq_ratCast`: an elliptic curve with rational `j`-invariant is a
  `ℚ`-curve.
-/

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- An elliptic curve `W` over a number field `K` is a **`ℚ`-curve** (LMFDB `ec.q_curve`) if it is
isogenous over an algebraic closure `K̄` of `K` to each of its Galois conjugates: for every
embedding `σ : K → K̄`, the curves `W^ι` and `W^σ` over `K̄` are isogenous, where `ι : K → K̄` is
the inclusion. The isogenies need not be defined over `K`. -/
def IsQCurve : Prop :=
  ∀ σ : K →+* AlgebraicClosure K, (W.map (algebraMap K (AlgebraicClosure K))).IsIsogenous
    (W.map σ)

/-- **The base change of a curve over `ℚ` is a `ℚ`-curve**: all its Galois conjugates are equal to
it. -/
lemma isQCurve_baseChange [CharZero K] (E : WeierstrassCurve ℚ) : (E.baseChange K).IsQCurve :=
  fun σ ↦ by
    rw [baseChange, map_map, map_map, Subsingleton.elim (σ.comp _) ((algebraMap K _).comp _)]

/-- **An elliptic curve with rational `j`-invariant is a `ℚ`-curve**: its Galois conjugates have
the same `j`-invariant, so they are isomorphic to it over the algebraically closed field `K̄`. -/
lemma isQCurve_of_j_eq_ratCast [W.IsElliptic] {q : ℚ} (hj : W.j = q) : W.IsQCurve :=
  fun σ ↦ by
    rcases exists_variableChange_of_j_eq (W.map (algebraMap K (AlgebraicClosure K))) (W.map σ)
      (by rw [map_j, map_j, hj, map_ratCast, map_ratCast]) with ⟨C, hC⟩
    exact hC ▸ isIsogenous_smul_self _ C

end WeierstrassCurve
