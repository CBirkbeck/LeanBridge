import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Trace.Defs
import LeanBridge.ForMathlib.RingTheory.Artinian.Module

/-!
# The trace form of a reduced finite algebra in characteristic zero

Let `K` be a commutative algebra of finite dimension over a field `F` of characteristic zero. If `K`
is reduced, for instance an étale algebra over `ℚ`, a finite product of number fields, then its
trace form `(x, y) ↦ Tr_{K/F}(x y)` is nondegenerate. Indeed `K` is the product of its residue
fields `K ⧸ 𝔐` (`IsArtinianRing.equivPi`), so for `x ≠ 0` there is `y` such that `x y` is a nonzero
idempotent `e`, and multiplication by `e` is a nonzero projection of `K`, whose trace is its rank,
nonzero in characteristic zero. Mathlib proves the nondegeneracy for finite separable extensions of
fields (`traceForm_nondegenerate`). Tau Ceti's main branch, not its pin, proves it for every étale
algebra over a field (`TauCeti.Algebra.etale_iff_traceForm_nondegenerate`): this file is to give way
to it at the bump.

## Main results

* `traceForm_nondegenerate_of_isReduced`: the trace form of a reduced finite-dimensional commutative
  algebra over a field of characteristic zero is nondegenerate.
-/

open IsArtinianRing LinearMap

variable (F K : Type*) [Field F] [CharZero F] [CommRing K] [Algebra F K] [Module.Finite F K]
  [IsReduced K]

open Ideal in
/-- **The trace form of a reduced finite-dimensional commutative algebra over a field of
characteristic zero is nondegenerate**, for instance that of an étale `ℚ`-algebra: for `x ≠ 0`,
some `x y` is a nonzero idempotent, whose trace is the rank of a nonzero projection. -/
lemma traceForm_nondegenerate_of_isReduced : (Algebra.traceForm F K).Nondegenerate := by
  have : IsArtinianRing K := isArtinian_of_tower F inferInstance
  have hsep (x : K) (hx : ∀ y, Algebra.traceForm F K x y = 0) : x = 0 := by
    by_contra hx0
    have h𝔐 : ∃ 𝔐 : MaximalSpectrum K, x ∉ 𝔐.asIdeal := by
      by_contra! h
      exact hx0 <| ext_mk fun 𝔐 ↦ (Quotient.eq_zero_iff_mem.mpr (h 𝔐)).trans (map_zero _).symm
    rcases h𝔐 with ⟨𝔐, hx𝔐⟩
    rcases 𝔐.isMaximal.exists_inv hx𝔐 with ⟨y, i, hi, hyi⟩
    have hxy : x * single 𝔐 (y : K ⧸ 𝔐.asIdeal) = single 𝔐 1 := by
      rw [single_mk, ← mul_assoc, ← single_mk, mul_comm x y, eq_sub_of_add_eq hyi, map_sub, map_one,
        Quotient.eq_zero_iff_mem.mpr hi, sub_zero]
    have he : IsIdempotentElem (single 𝔐 (1 : K ⧸ 𝔐.asIdeal)) := by
      rw [IsIdempotentElem, ← single_mul, mul_one]
    have he0 : single 𝔐 (1 : K ⧸ 𝔐.asIdeal) ≠ 0 := fun h ↦ one_ne_zero <|
      (mk_single_self (1 : K ⧸ 𝔐.asIdeal)).symm.trans <| by rw [h, map_zero]
    have htr : trace F K (Algebra.lmul F K (single 𝔐 1)) = 0 := by
      rw [← Algebra.trace_apply, ← hxy, ← Algebra.traceForm_apply]
      exact hx _
    have hne : Algebra.lmul F K (single 𝔐 1) ≠ 0 := fun h ↦ he0 (by simpa using congrArg (· 1) h)
    exact hne ((IsIdempotentElem.trace_eq_zero_iff (he.map (Algebra.lmul F K))).mp htr)
  exact ⟨hsep, fun y hy ↦ hsep y fun x ↦ ((Algebra.traceForm_isSymm F).eq y x).trans (hy x)⟩
