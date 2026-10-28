import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Iso
import TauCeti.AlgebraicGeometry.AbelianVariety.TangentSpace

/-!
# The `p`-rank of an abelian variety

The `p`-rank of an abelian variety `A` of dimension `g` over a field `K` of characteristic `p > 0`
is the dimension over `𝔽_p` of its geometric `p`-torsion `A(K̄)[p]`, the `p`-torsion of the group of
points of `A` over an algebraic closure `K̄` of `K`, and its `p`-corank is `g` minus its `p`-rank.
The LMFDB considers abelian varieties over finite fields `𝔽_q`, `q = p ^ r`, for which `K̄` is an
algebraic closure `𝔽̄_p` of `𝔽_p`. The `p`-rank is at most `g`, with equality if and only if `A` is
ordinary, and it is the number of roots of the Weil polynomial of `A` that are `p`-adic units
(`Polynomial.pRank`); none of these facts is formalised here.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.GeometricPoint`: the group `A(K̄)` of points of `A`
  over the algebraic closure `K̄` of `K`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.pRank` (LMFDB `av.fq.p_rank`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.pCorank` (LMFDB `av.fq.p_rank`).

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.pRank_congr` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.pCorank_congr`: the `p`-rank and the `p`-corank only
  depend on the isomorphism class of the abelian variety.
-/

open CategoryTheory AlgebraicGeometry AddSubgroup MonObj

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] (A : AbelianVariety K) {B : AbelianVariety K} (e : A ≅ B)

/-- The **geometric points** `A(K̄)` of an abelian variety `A` over `K`: its points over the
algebraic closure `K̄` of `K`, the morphisms `Spec K̄ ⟶ A` over `Spec K`, a commutative group under
the group law of `A`. -/
abbrev GeometricPoint : Type u :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) ⟶ A.toOver

/-- The **`p`-rank** (LMFDB `av.fq.p_rank`) of an abelian variety `A` over a field `K` of
characteristic `p > 0`: the dimension over `𝔽_p` of the `p`-torsion `A(K̄)[p]` of its geometric
points. The LMFDB considers finite fields `K = 𝔽_q`, `q = p ^ r`, and writes `A(𝔽̄_p)[p]`; here `p`
is the characteristic `ringChar K` of `K`, and the definition is meaningless in characteristic
`0`. The group `A(K̄)[p]` is finite, of order at most `p ^ g` (not formalised here), so
`Module.finrank` is its dimension. -/
noncomputable def pRank : ℕ :=
  letI : Module (ZMod (ringChar K)) (torsionBy (Additive A.GeometricPoint) (ringChar K)) :=
    torsionBy.zmodModule
  Module.finrank (ZMod (ringChar K)) (torsionBy (Additive A.GeometricPoint) (ringChar K))

/-- The **`p`-corank** (LMFDB `av.fq.p_rank`) of an abelian variety `A` of dimension `g` over a
field `K` of characteristic `p > 0`: the difference `g - p-rank` between `g` and its `p`-rank
(`TauCeti.AlgebraicGeometry.AbelianVariety.pRank`). Here `g` is the dimension of the tangent space
of `A` at the origin, which is the dimension of `A`
(`TauCeti.AlgebraicGeometry.AbelianVariety.finrank_tangentSpace_eq_dim`). -/
noncomputable def pCorank : ℕ :=
  Module.finrank K A.TangentSpace - A.pRank

variable {A}

include e in
/-- The `p`-rank only depends on the isomorphism class of the abelian variety. -/
lemma pRank_congr : A.pRank = B.pRank := by
  have _ : IsMonHom (isoToOver e).hom := isoToOver_hom e ▸ inferInstance
  let f : torsionBy (Additive A.GeometricPoint) (ringChar K) ≃+
      torsionBy (Additive B.GeometricPoint) (ringChar K) :=
    (Hom.mulEquivCongrRight (isoToOver e) _).toAdditive.torsionByCongr (ringChar K)
  let _ : Module (ZMod (ringChar K)) (torsionBy (Additive A.GeometricPoint) (ringChar K)) :=
    torsionBy.zmodModule
  let _ : Module (ZMod (ringChar K)) (torsionBy (Additive B.GeometricPoint) (ringChar K)) :=
    torsionBy.zmodModule
  exact LinearEquiv.finrank_eq { f with map_smul' := ZMod.map_smul f }

include e in
/-- The `p`-corank only depends on the isomorphism class of the abelian variety. -/
lemma pCorank_congr : A.pCorank = B.pCorank :=
  congrArg₂ (· - ·) (Nat.cast_injective <| (finrank_tangentSpace_eq_dim A).trans <|
    (dim_eq_of_iso e).trans (finrank_tangentSpace_eq_dim B).symm) (pRank_congr e)

end TauCeti.AlgebraicGeometry.AbelianVariety
