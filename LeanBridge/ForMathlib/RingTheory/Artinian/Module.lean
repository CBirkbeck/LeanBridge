import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# The components of an element of a reduced Artinian ring

A reduced commutative Artinian ring `A` is the product of its residue fields `A ⧸ 𝔐`, for `𝔐`
running over its finitely many maximal ideals (Mathlib's `IsArtinianRing.equivPi`). The components
of `x ∈ A` are its images in the `A ⧸ 𝔐`, and `IsArtinianRing.single 𝔐 x` is the element with
component `x` at `𝔐` and `0` elsewhere. Two elements with the same components are equal, `single 𝔐`
is additive and multiplicative, the elements `single 𝔐 1` have sum `1`, and an element is integral
over a ring `R` exactly when all its components are.

## Main definitions

* `IsArtinianRing.single`: the element of a reduced Artinian ring with a single nonzero component.

## Main results

* `IsArtinianRing.isIntegral_iff_forall_isIntegral_mk`: an element of a reduced Artinian ring is
  integral exactly when its components are.
-/

open Polynomial

namespace IsArtinianRing

variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]

open Classical in
/-- The element of a reduced Artinian ring `A` with component `x` at the maximal ideal `𝔐` and `0`
at the others, in the decomposition of `A` into the product of its residue fields
(`IsArtinianRing.equivPi`). -/
noncomputable def single (𝔐 : MaximalSpectrum A) (x : A ⧸ 𝔐.asIdeal) : A :=
  (equivPi A).symm (Pi.single 𝔐 x)

variable {𝔐 : MaximalSpectrum A}

lemma mk_single_self (x : A ⧸ 𝔐.asIdeal) : ((single 𝔐 x : A) : A ⧸ 𝔐.asIdeal) = x := by
  classical
  exact (congrFun ((equivPi A).apply_symm_apply (Pi.single 𝔐 x)) 𝔐).trans (Pi.single_eq_same _ _)

lemma mk_single_of_ne {𝔐' : MaximalSpectrum A} (h : 𝔐' ≠ 𝔐) (x : A ⧸ 𝔐.asIdeal) :
    ((single 𝔐 x : A) : A ⧸ 𝔐'.asIdeal) = 0 := by
  classical
  exact (congrFun ((equivPi A).apply_symm_apply (Pi.single 𝔐 x)) 𝔐').trans
    (Pi.single_eq_of_ne h _)

lemma ext_mk {x y : A} (h : ∀ 𝔐 : MaximalSpectrum A, (x : A ⧸ 𝔐.asIdeal) = y) : x = y :=
  (equivPi A).injective <| funext h

lemma single_mul (x y : A ⧸ 𝔐.asIdeal) : single 𝔐 (x * y) = single 𝔐 x * single 𝔐 y := by
  classical
  simp only [single, Pi.single_mul, map_mul]

lemma single_add (x y : A ⧸ 𝔐.asIdeal) : single 𝔐 (x + y) = single 𝔐 x + single 𝔐 y := by
  classical
  simp only [single, Pi.single_add, map_add]

lemma single_zero : single 𝔐 (0 : A ⧸ 𝔐.asIdeal) = 0 := by
  classical
  simp only [single, Pi.single_zero, map_zero]

lemma single_mk (x : A) : single 𝔐 (x : A ⧸ 𝔐.asIdeal) = x * single 𝔐 1 := by
  refine ext_mk fun 𝔐' ↦ ?_
  rw [map_mul]
  by_cases h : 𝔐' = 𝔐
  · subst h
    rw [mk_single_self, mk_single_self, mul_one]
  · rw [mk_single_of_ne h, mk_single_of_ne h, mul_zero]

lemma sum_single_one [Fintype (MaximalSpectrum A)] : ∑ 𝔐 : MaximalSpectrum A, single 𝔐 1 = 1 := by
  classical
  simp only [single, ← map_sum, Finset.univ_sum_single]
  exact map_one _

open Ideal in
/-- **An element of a reduced Artinian ring is integral exactly when its components are**, the
components of `x` being its images in the residue fields of `A`: `x` is a root of the product of
monic polynomials annihilating them. -/
lemma isIntegral_iff_forall_isIntegral_mk {R : Type*} [CommRing R] [Algebra R A] (x : A) :
    IsIntegral R x ↔ ∀ 𝔐 : MaximalSpectrum A, IsIntegral R (x : A ⧸ 𝔐.asIdeal) := by
  refine ⟨fun hx 𝔐 ↦ hx.map (Quotient.mkₐ R 𝔐.asIdeal), fun h ↦ ?_⟩
  have hfin : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  choose p hp hpx using h
  refine ⟨∏ 𝔐, p 𝔐, monic_prod_of_monic _ _ fun 𝔐 _ ↦ hp 𝔐, ?_⟩
  refine (equivPi A).injective <| funext fun 𝔐 ↦ ?_
  rw [map_zero, Pi.zero_apply, equivPi_apply, hom_eval₂, eval₂_finsetProd, ← Quotient.algebraMap_eq]
  exact Finset.prod_eq_zero (Finset.mem_univ 𝔐) (hpx 𝔐)

lemma isIntegral_single {R : Type*} [CommRing R] [Algebra R A] {x : A ⧸ 𝔐.asIdeal}
    (hx : IsIntegral R x) : IsIntegral R (single 𝔐 x) := by
  refine (isIntegral_iff_forall_isIntegral_mk _).mpr fun 𝔐' ↦ ?_
  by_cases h : 𝔐' = 𝔐
  · subst h
    rwa [mk_single_self]
  · rw [mk_single_of_ne h]
    exact isIntegral_zero

end IsArtinianRing
