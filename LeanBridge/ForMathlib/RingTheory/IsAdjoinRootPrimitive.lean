import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Every root of a defining polynomial generates the field

A defining polynomial of a number field `K` (LMFDB `nf.defining_polynomial`) is a polynomial
`f ∈ ℚ[x]` with `K ≅ ℚ[x] / (f)`, that is a presentation `IsAdjoinRoot K f`, or equivalently an
irreducible `f` with `K ≅ ℚ(a)` for a root `a` of `f`. The presentation singles out one root of `f`
in `K`, which generates `K` (`IsAdjoinRoot.primitive_element_root`). This file shows that every
root of `f` in `K` generates `K`: its minimal polynomial is `f` divided by its leading coefficient,
of degree `[K : ℚ]`. Everything holds over any base field `F`.

## Main results

* `IsAdjoinRoot.nonempty_iff` (LMFDB `nf.defining_polynomial`): `K ≅ F[x] / (f)` exactly when `f`
  is irreducible and `K = F(a)` for a root `a ∈ K` of `f`.
* `IsAdjoinRoot.primitive_element_of_aeval_eq_zero` (LMFDB `nf.defining_polynomial`): a root
  `a ∈ K` of `f` is a generator of `K` (LMFDB `nf.generator`), that is `F(a) = K`.
-/

open Polynomial

open scoped IntermediateField

namespace IsAdjoinRoot

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {f : F[X]} {a : K}

lemma finrank_eq_natDegree (h : IsAdjoinRoot K f) : Module.finrank F K = f.natDegree :=
  h.adjoinRootAlgEquiv.toLinearEquiv.finrank_eq.symm.trans finrank_quotient_span_eq_natDegree

lemma finiteDimensional (h : IsAdjoinRoot K f) : FiniteDimensional F K :=
  (AdjoinRoot.powerBasis h.irreducible.ne_zero).finite.equiv h.adjoinRootAlgEquiv.toLinearEquiv

/-- **The two forms of a defining polynomial agree** (LMFDB `nf.defining_polynomial`):
`K ≅ F[x] / (f)` exactly when `f` is irreducible and `K = F(a)` for a root `a ∈ K` of `f`. -/
lemma nonempty_iff :
    Nonempty (IsAdjoinRoot K f) ↔ Irreducible f ∧ ∃ a : K, aeval a f = 0 ∧ F⟮a⟯ = ⊤ := by
  refine ⟨fun ⟨h⟩ ↦ ⟨h.irreducible, h.root, h.aeval_root_self, h.primitive_element_root⟩, ?_⟩
  rintro ⟨hf, a, ha, hgen⟩
  let h : IsAdjoinRoot K (minpoly F a) :=
    mkOfPrimitiveElement (IsAlgebraic.isIntegral ⟨f, hf.ne_zero, ha⟩) hgen
  refine ⟨{ map := h.map, map_surjective := h.map_surjective, ker_map := ?_ }⟩
  rw [h.ker_map, ← minpoly.eq_of_irreducible hf ha, Ideal.span_singleton_mul_right_unit]
  exact isUnit_C.mpr <| isUnit_iff_ne_zero.mpr <| inv_ne_zero <| leadingCoeff_ne_zero.mpr hf.ne_zero

/-- **Every root of a defining polynomial generates the field** (LMFDB `nf.defining_polynomial`):
if `K ≅ F[x] / (f)`, then `F(a) = K` for every root `a ∈ K` of `f`, not only for the root that the
presentation singles out. -/
lemma primitive_element_of_aeval_eq_zero (h : IsAdjoinRoot K f) (ha : aeval a f = 0) :
    F⟮a⟯ = ⊤ := by
  have : FiniteDimensional F K := h.finiteDimensional
  rw [Field.primitive_element_iff_minpoly_natDegree_eq,
    ← minpoly.eq_of_irreducible h.irreducible ha, natDegree_mul_leadingCoeff_self_inv,
    h.finrank_eq_natDegree]

end IsAdjoinRoot
