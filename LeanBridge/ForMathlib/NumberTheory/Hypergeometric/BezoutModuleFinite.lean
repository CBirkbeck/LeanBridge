import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.BezoutModule
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The Bézout module of a hypergeometric family is finite

The defining parameters `(A, B)` of a hypergeometric family have no common entries, and distinct
cyclotomic polynomials are coprime over `ℚ`, so `Φ_A` and `Φ_B` are coprime over `ℚ`. Their
resultant is therefore nonzero, and so is the Bézout determinant, which is the resultant up to
sign. Hence the Bézout module `ℤ^d / B ℤ^d` is finite: its order is the absolute value of the
Bézout determinant.

## Main results

* `Hypergeometric.Parameters.bezoutDeterminant_ne_zero`: the Bézout determinant is nonzero.
* `Hypergeometric.Parameters.card_bezoutModule`: the Bézout module has order `|det B|`.
* The instance `Finite P.BezoutModule` (LMFDB `hgm.bezout_module`): the Bézout module is finite.
-/

open Polynomial

namespace Hypergeometric.Parameters

variable {d : ℕ} (P : Parameters d)

lemma isCoprime_map_cyclotomicProd : IsCoprime (P.A.cyclotomicProd.map (Int.castRingHom ℚ))
    (P.B.cyclotomicProd.map (Int.castRingHom ℚ)) := by
  simp only [CuspIndex.cyclotomicProd, Polynomial.map_multiset_prod, Multiset.map_map,
    Function.comp_def, map_cyclotomic]
  refine Multiset.prod_induction (IsCoprime · _) _ (fun _ _ ↦ IsCoprime.mul_left)
    isCoprime_one_left fun f hf ↦ ?_
  rcases Multiset.mem_map.mp hf with ⟨a, ha, rfl⟩
  refine Multiset.prod_induction (IsCoprime _ ·) _ (fun _ _ ↦ IsCoprime.mul_right)
    isCoprime_one_right fun g hg ↦ ?_
  rcases Multiset.mem_map.mp hg with ⟨b, hb, rfl⟩
  exact cyclotomic.isCoprime_rat fun hab ↦
    P.disjoint (Multiset.mem_coe.mp ha) (hab ▸ Multiset.mem_coe.mp hb)

lemma natDegree_map_cyclotomicProd (c : CuspIndex d) :
    (c.cyclotomicProd.map (Int.castRingHom ℚ)).natDegree = d := by
  rw [c.monic_cyclotomicProd.natDegree_map, c.natDegree_cyclotomicProd]

/-- **The Bézout determinant of a hypergeometric family is nonzero**: up to sign it is the
resultant of `Φ_A` and `Φ_B`, which are coprime over `ℚ` as `A` and `B` have no common entries. -/
lemma bezoutDeterminant_ne_zero : P.bezoutDeterminant ≠ 0 := by
  rw [bezoutDeterminant_eq]
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) fun h ↦
    resultant_ne_zero _ _ P.isCoprime_map_cyclotomicProd ?_
  rw [natDegree_map_cyclotomicProd, natDegree_map_cyclotomicProd, resultant_map_map, h, map_zero]

/-- **The Bézout module has order `|det B|`**, the absolute value of the Bézout determinant. -/
lemma card_bezoutModule : Nat.card P.BezoutModule = P.bezoutDeterminant.natAbs := by
  rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _
    (Matrix.mulVec_injective_of_det_ne_zero P.bezoutDeterminant_ne_zero)), bezoutDeterminant,
    ← LinearMap.det_toLin']
  rfl

instance : Finite P.BezoutModule :=
  Nat.finite_of_card_ne_zero <| by
    rw [card_bezoutModule]
    exact Int.natAbs_ne_zero.mpr P.bezoutDeterminant_ne_zero

end Hypergeometric.Parameters
