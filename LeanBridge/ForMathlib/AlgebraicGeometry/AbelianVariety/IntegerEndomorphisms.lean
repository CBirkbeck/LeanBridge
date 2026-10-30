import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.AbelianVariety.End.BaseChange
import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Iso

/-!
# Abelian varieties with endomorphism ring `ℤ`

An abelian variety `A` over a field `K` has endomorphism ring `ℤ` if its endomorphisms are the
multiplications `[n]` by the integers `n`, and these are distinct: the canonical ring homomorphism
`ℤ → End(A)` (Tau Ceti's `TauCeti.AlgebraicGeometry.AbelianVariety.End`) is bijective. The LMFDB
uses this condition over `K` and over an algebraic closure `K̄` of `K`:

* an abelian surface `A` over `ℚ` is of paramodular type if `End(A) = ℤ` (LMFDB
  `g2c.paramodular_conjecture`). The paramodular conjecture of Brumer and Kramer predicts, for
  each of them, a paramodular newform whose level is the conductor of `A`; it is not formalised, as
  neither paramodular newforms nor the conductors of abelian varieties are available;
* a genus `2` curve is generic if the geometric endomorphism ring `End(J_K̄)` of its Jacobian `J` is
  `ℤ` (LMFDB `g2c.maximal_galois_rep`); its mod-`ℓ` Galois images can then be all of
  `GSp(4, 𝔽_ℓ)` (`TauCeti.AlgebraicGeometry.AbelianVariety.HasMaximalTorsionImage`).

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.HasIntEndomorphismRing`: `End(A) = ℤ`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasIntGeometricEndomorphismRing` (LMFDB
  `g2c.maximal_galois_rep`): `End(A_K̄) = ℤ`, the generic case.
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsParamodularType` (LMFDB `g2c.paramodular_conjecture`):
  abelian surfaces with `End(A) = ℤ`.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.hasIntEndomorphismRing_congr`,
  `TauCeti.AlgebraicGeometry.AbelianVariety.hasIntGeometricEndomorphismRing_congr` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.isParamodularType_congr`: these conditions only depend
  on the isomorphism class of the abelian variety.
-/

open CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.AbelianVariety

variable {K : Type u} [Field K] {A B : AbelianVariety K}

variable (A) in
/-- An abelian variety `A` over `K` has **endomorphism ring `ℤ`** if the canonical ring
homomorphism `ℤ → End(A)`, `n ↦ [n]`, is bijective: the endomorphisms of `A` defined over `K` are
the multiplications by integers, and these are distinct (so `A` is nonzero). -/
def HasIntEndomorphismRing : Prop :=
  Function.Bijective (Int.castRingHom (End A))

variable (A) in
/-- An abelian variety `A` over `K` has **geometric endomorphism ring `ℤ`** (LMFDB
`g2c.maximal_galois_rep`, LMFDB `ag.geom_endomorphism_ring`) if its base change `A_K̄` to an
algebraic closure `K̄` of `K` has endomorphism ring `ℤ`. The LMFDB calls a genus `2` curve, or its
Jacobian, **generic** in this case; the Sato–Tate group of its Jacobian is then `USp(4)` (LMFDB
`g2c.st_group`, not formalised). -/
def HasIntGeometricEndomorphismRing : Prop :=
  (A.baseChange (AlgebraicClosure K)).HasIntEndomorphismRing

variable (A) in
/-- An abelian variety `A` is of **paramodular type** (LMFDB `g2c.paramodular_conjecture`) if it is
an abelian surface, of dimension `2`, with endomorphism ring `ℤ` over its base field: these are
the abelian surfaces over `ℚ` to which the paramodular conjecture of Brumer and Kramer attaches a
paramodular newform, of level the conductor of `A` (not formalised). -/
def IsParamodularType : Prop :=
  A.dim = 2 ∧ A.HasIntEndomorphismRing

/-- **Having endomorphism ring `ℤ` only depends on the isomorphism class**: an isomorphism `A ≅ B`
conjugates `End(A)` isomorphically onto `End(B)`, compatibly with the multiplications by
integers. -/
lemma hasIntEndomorphismRing_congr (e : A ≅ B) :
    A.HasIntEndomorphismRing ↔ B.HasIntEndomorphismRing := by
  have h :
      (End.congr e : End A →+* End B).comp (Int.castRingHom (End A)) = Int.castRingHom (End B) :=
    RingHom.ext_int _ _
  rw [HasIntEndomorphismRing, HasIntEndomorphismRing, ← h, RingHom.coe_comp,
    RingEquiv.coe_toRingHom, (End.congr e).bijective.of_comp_iff']

/-- **Having geometric endomorphism ring `ℤ` only depends on the isomorphism class**. -/
lemma hasIntGeometricEndomorphismRing_congr (e : A ≅ B) :
    A.HasIntGeometricEndomorphismRing ↔ B.HasIntGeometricEndomorphismRing :=
  hasIntEndomorphismRing_congr <| (baseChangeFunctor (AlgebraicClosure K)).mapIso e

/-- **Being of paramodular type only depends on the isomorphism class**. -/
lemma isParamodularType_congr (e : A ≅ B) : A.IsParamodularType ↔ B.IsParamodularType := by
  rw [IsParamodularType, IsParamodularType, dim_eq_of_iso e, hasIntEndomorphismRing_congr e]

end TauCeti.AlgebraicGeometry.AbelianVariety
