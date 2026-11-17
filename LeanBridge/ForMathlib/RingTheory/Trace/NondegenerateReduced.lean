import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Trace.Defs

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

open LinearMap

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
      refine hx0 ((IsArtinianRing.equivPi K).injective (funext fun 𝔐 ↦ ?_))
      rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply]
      exact Quotient.eq_zero_iff_mem.mpr (h 𝔐)
    rcases h𝔐 with ⟨𝔐, hx𝔐⟩
    rcases 𝔐.isMaximal.exists_inv hx𝔐 with ⟨y, i, hi, hyi⟩
    classical
    let e : K := (IsArtinianRing.equivPi K).symm (Pi.single 𝔐 1)
    have hxy : x * (IsArtinianRing.equivPi K).symm (Pi.single 𝔐 (y : K ⧸ 𝔐.asIdeal)) = e := by
      refine (IsArtinianRing.equivPi K).injective (funext fun 𝔐' ↦ ?_)
      rw [map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
        IsArtinianRing.equivPi_apply]
      by_cases h : 𝔐' = 𝔐
      · subst h
        rw [Pi.single_eq_same, Pi.single_eq_same, mul_comm, ← map_mul, eq_sub_of_add_eq hyi,
          map_sub, map_one, Quotient.eq_zero_iff_mem.mpr hi, sub_zero]
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]
    have he : IsIdempotentElem e := by
      simp only [e, IsIdempotentElem, ← map_mul, ← Pi.single_mul, mul_one]
    have he0 : e ≠ 0 := fun h ↦ by
      have h1 : (Pi.single 𝔐 1 : ∀ 𝔐' : MaximalSpectrum K, K ⧸ 𝔐'.asIdeal) 𝔐 =
          IsArtinianRing.equivPi K 0 𝔐 :=
        congrFun ((IsArtinianRing.equivPi K).symm_apply_eq.mp h) 𝔐
      rw [Pi.single_eq_same, map_zero, Pi.zero_apply] at h1
      exact one_ne_zero h1
    have htr : trace F K (Algebra.lmul F K e) = 0 := by
      rw [← Algebra.trace_apply, ← hxy, ← Algebra.traceForm_apply]
      exact hx _
    have hne : Algebra.lmul F K e ≠ 0 := fun h ↦ he0 (by simpa using congrArg (· 1) h)
    exact hne ((IsIdempotentElem.trace_eq_zero_iff (he.map (Algebra.lmul F K))).mp htr)
  exact ⟨hsep, fun y hy ↦ hsep y fun x ↦ ((Algebra.traceForm_isSymm F).eq y x).trans (hy x)⟩
