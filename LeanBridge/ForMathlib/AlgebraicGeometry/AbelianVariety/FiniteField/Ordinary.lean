import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.FiniteField.PRank

/-!
# Ordinary abelian varieties

An abelian variety of dimension `g` over a finite field `𝔽_q`, `q = p ^ r`, is ordinary if its
`p`-rank is `g`, the largest possible value.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.IsOrdinary` (LMFDB `av.fq.ordinary`).

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.isOrdinary_congr`: being ordinary only depends on the
  isomorphism class of the abelian variety.
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsOrdinary.pCorank_eq_zero`: an ordinary abelian
  variety has `p`-corank `0`.
-/

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open CategoryTheory

universe u

variable {K : Type u} [Field K] {A B : AbelianVariety K}

variable (A) in
/-- An abelian variety `A` of dimension `g` over a field `K` of characteristic `p > 0` is
**ordinary** (LMFDB `av.fq.ordinary`) if its `p`-rank
(`TauCeti.AlgebraicGeometry.AbelianVariety.pRank`) is `g`.

The LMFDB considers finite fields `K = 𝔽_q`, `q = p ^ r`. For an elliptic curve this agrees with
Tau Ceti's `WeierstrassCurve.IsOrdinary`, a nonzero geometric `p`-torsion point (not formalised
here). -/
def IsOrdinary : Prop :=
  (A.pRank : WithBot ℕ∞) = A.dim

/-- Being ordinary only depends on the isomorphism class of the abelian variety. -/
lemma isOrdinary_congr (e : A ≅ B) : A.IsOrdinary ↔ B.IsOrdinary := by
  rw [IsOrdinary, IsOrdinary, pRank_congr e, dim_eq_of_iso e]

/-- An ordinary abelian variety has `p`-corank `0`. -/
lemma IsOrdinary.pCorank_eq_zero (hA : A.IsOrdinary) : A.pCorank = 0 := by
  rw [pCorank, Nat.cast_injective <| (finrank_tangentSpace_eq_dim A).trans hA.symm, Nat.sub_self]

end TauCeti.AlgebraicGeometry.AbelianVariety
