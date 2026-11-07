import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Algebraic closures are the minimal algebraically closed extensions

The LMFDB (`nf.algebraic_closure`) defines an algebraic closure of a field `K` as a minimal
algebraically closed field extension of `K`, and Mathlib's `IsAlgClosure K L` as an algebraically
closed extension `L` of `K` that is algebraic over `K` (Stacks 09GS). This file proves that the two
agree: an algebraically closed extension `L` of `K` is algebraic over `K` exactly when no
intermediate field `K ⊆ E ⊊ L` is algebraically closed. An algebraic closure is unique up to
isomorphism (`IsAlgClosure.equiv`), but not up to a unique one: when `K` is not separably closed,
as a number field is not, an algebraic closure has nontrivial automorphisms over `K`. The algebraic
closure of a number field is isomorphic to the field `algebraicClosure ℚ ℂ` of algebraic numbers in
`ℂ`.

## Main definitions

* `NumberField.ringEquivAlgebraicClosure` (LMFDB `nf.algebraic_closure`): an isomorphism between
  an algebraic closure of a number field and the field of algebraic numbers in `ℂ`.

## Main results

* `isAlgClosure_iff_forall_isAlgClosed_eq_top` (LMFDB `nf.algebraic_closure`): an algebraically
  closed extension `L` of `K` is an algebraic closure of `K` exactly when it is minimal, that is
  when the only algebraically closed intermediate field of `L / K` is `L`.
* `nontrivial_algEquiv_of_not_isSepClosed` (LMFDB `nf.algebraic_closure`): an algebraic closure of
  a field that is not separably closed has a nontrivial automorphism, so the isomorphism between two
  algebraic closures is not unique.
* `NumberField.not_isSepClosed`: a number field is not separably closed.
-/

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Algebraic closures are the minimal algebraically closed extensions**
(LMFDB `nf.algebraic_closure`): an algebraically closed extension `L` of `K` is algebraic over `K`
exactly when no intermediate field of `L / K` other than `L` is algebraically closed. -/
lemma isAlgClosure_iff_forall_isAlgClosed_eq_top [IsAlgClosed L] :
    IsAlgClosure K L ↔ ∀ E : IntermediateField K L, IsAlgClosed E → E = ⊤ := by
  refine ⟨fun h E hE ↦ ?_, fun h ↦ ⟨‹_›, (algebraicClosure.eq_top_iff K L).mp (h _ ?_)⟩⟩
  · have : Algebra.IsAlgebraic E L := .tower_top (K := K) E
    refine eq_top_iff.mpr fun x _ ↦ ?_
    rcases (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := E)).2 x with ⟨y, rfl⟩
    exact y.2
  · exact IsAlgClosure.isAlgClosed K

/-- **Algebraic closures are unique only up to non-unique isomorphism**
(LMFDB `nf.algebraic_closure`): an algebraic closure `L` of a field `K` that is not separably closed
has an automorphism over `K` other than the identity, which sends a separable element of `L` outside
`K` to another root of its minimal polynomial. -/
lemma nontrivial_algEquiv_of_not_isSepClosed [IsAlgClosure K L] (hK : ¬IsSepClosed K) :
    Nontrivial (L ≃ₐ[K] L) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hx : ∃ x : L, IsSeparable K x ∧ x ∉ (algebraMap K L).range := by
    by_contra! h
    refine hK (IsSepClosed.of_exists_root K fun p _ hp hsep ↦ ?_)
    rcases IsAlgClosed.exists_aeval_eq_zero L p (degree_pos_of_irreducible hp).ne' with ⟨y, hy⟩
    rcases h y (hsep.of_dvd <| minpoly.dvd K y hy) with ⟨k, rfl⟩
    rw [aeval_algebraMap_apply, map_eq_zero_iff _ (algebraMap K L).injective,
      coe_aeval_eq_eval] at hy
    exact ⟨k, hy⟩
  rcases hx with ⟨x, hsep, hx⟩
  have hint : IsIntegral K x := hsep.isIntegral
  have h2 : 2 ≤ (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff hint).mpr hx
  have hcard : Fintype.card ((minpoly K x).rootSet L) = (minpoly K x).natDegree :=
    card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)
  have hxroot : x ∈ (minpoly K x).rootSet L :=
    (mem_rootSet_of_ne (minpoly.ne_zero hint)).mpr (minpoly.aeval K x)
  have h1 : 1 < Fintype.card ((minpoly K x).rootSet L) := by omega
  rcases Fintype.exists_ne_of_one_lt_card h1 ⟨x, hxroot⟩ with ⟨⟨y, hy⟩, hne⟩
  have hmin : minpoly K x = minpoly K y := minpoly.eq_of_irreducible_of_monic
    (minpoly.irreducible hint) ((mem_rootSet_of_ne (minpoly.ne_zero hint)).mp hy)
    (minpoly.monic hint)
  rcases (Normal.minpoly_eq_iff_mem_orbit L).mp hmin with ⟨σ, hσ⟩
  refine ⟨σ, 1, fun h ↦ hne (Subtype.ext ?_)⟩
  subst h
  simpa using hσ

/-- **A number field is not separably closed**: it would contain a root of the cyclotomic
polynomial `Φ_p`, separable of degree `p - 1` over `ℚ`, for every prime `p`. -/
lemma NumberField.not_isSepClosed [NumberField K] : ¬IsSepClosed K := by
  intro hK
  rcases Nat.exists_infinite_primes (Module.finrank ℚ K + 2) with ⟨p, hp, hpp⟩
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hpp.pos
  have hdeg : ((cyclotomic p ℚ).map (algebraMap ℚ K)).degree ≠ 0 := by
    rw [degree_map, degree_cyclotomic, Nat.totient_prime hpp]
    exact_mod_cast (by omega : p - 1 ≠ 0)
  rcases IsSepClosed.exists_root _ hdeg hirr.separable.map with ⟨ζ, hζ⟩
  have hmin : cyclotomic p ℚ = minpoly ℚ ζ := minpoly.eq_of_irreducible_of_monic hirr
    (by rwa [aeval_def, eval₂_eq_eval_map]) (cyclotomic.monic p ℚ)
  have hle : (minpoly ℚ ζ).natDegree ≤ Module.finrank ℚ K := minpoly.natDegree_le ζ
  rw [← hmin, natDegree_cyclotomic, Nat.totient_prime hpp] at hle
  omega

/-- An algebraic closure `L` of a number field `K`, usually written `ℚ̄`, is isomorphic to the field
`algebraicClosure ℚ ℂ` of algebraic numbers in `ℂ` (LMFDB `nf.algebraic_closure`): both are
algebraic closures of `ℚ`. -/
noncomputable def NumberField.ringEquivAlgebraicClosure [NumberField K] [IsAlgClosure K L] :
    L ≃+* algebraicClosure ℚ ℂ :=
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsAlgClosure ℚ L := .ofAlgebraic ℚ K L
  (IsAlgClosure.equiv ℚ L (algebraicClosure ℚ ℂ)).toRingEquiv
