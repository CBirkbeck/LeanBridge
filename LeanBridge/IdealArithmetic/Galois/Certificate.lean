/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.IdealArithmetic.Galois.Dedekind
import LeanBridge.IdealArithmetic.Galois.SeparableReduction
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# Frobenius cycle-type certificate (Dedekind's theorem, user-facing form)

This is the reflective certificate layer over Core Theorem 1 (`Dedekind.lean`). A
`FrobeniusCycleTypeCertificate f` bundles the data a user actually has: a prime `p` not dividing
`disc f`, and an explicit factorisation of `f mod p` into monic irreducibles. From it,
`exists_partition_eq_of_certificate` produces an arithmetic Frobenius `σ` whose cycle-type partition
on the roots of `f` is exactly the multiset of degrees of the given factors.

Everything structural is derived from `p ∤ disc f` via `separable_map_of_discr_ne_zero`
(both `f mod p` and `f/ℚ` separable), `IsGalois.of_separable_splitting_field`, and the
`IsGaloisGroup` chain for `Algebra.IsInvariant` of the ring of integers. The only instance the
caller must supply is the splitting `Fact` (`factSplitsSplittingField _`), which is already needed
to state `galActionHom`.

See `.mathlib-quality/tickets.md`, T013.
-/

open scoped Classical
open Polynomial NumberField UniqueFactorizationMonoid

namespace IdealArithmetic.Galois

/-- **R3 certificate (user-facing).** For a monic `f ∈ ℤ[X]` of positive degree, a certificate
that the Frobenius cycle type at `p` is the given factor-degree list: a prime `p ∤ disc f`, plus a
multiset of irreducible factors of `f mod p` whose product is `f mod p`. -/
structure FrobeniusCycleTypeCertificate (f : ℤ[X]) where
  /-- The rational prime at which `f` is reduced. -/
  p : ℕ
  /-- `p` is prime. -/
  hp : p.Prime
  /-- `p` does not divide `disc f`. -/
  hdisc : (Int.castRingHom (ZMod p)) f.discr ≠ 0
  /-- The claimed factors of `f mod p`. -/
  factors : Multiset (ZMod p)[X]
  /-- Every claimed factor is irreducible. -/
  hirr : ∀ q ∈ factors, Irreducible q
  /-- The claimed factors multiply to `f mod p`. -/
  hprod : factors.prod = f.map (Int.castRingHom (ZMod p))

/-- **T013.** A `FrobeniusCycleTypeCertificate` for a monic `f` of positive degree yields an
arithmetic Frobenius `σ` whose cycle-type partition on the roots of `f` is exactly the multiset
of degrees of the certificate's factors. -/
theorem exists_partition_eq_of_certificate (f : ℤ[X]) (hf : f.Monic) (hdeg : f.natDegree ≠ 0)
    [Fact (((f.map (Int.castRingHom ℚ)).map
      (algebraMap ℚ (f.map (Int.castRingHom ℚ)).SplittingField)).Splits)]
    (cert : FrobeniusCycleTypeCertificate f) :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      (Polynomial.Gal.galActionHom (f.map (Int.castRingHom ℚ))
        (f.map (Int.castRingHom ℚ)).SplittingField σ).partition.parts
        = cert.factors.map Polynomial.natDegree := by
  have : Fact cert.p.Prime := ⟨cert.hp⟩
  have hsepf : (f.map (Int.castRingHom (ZMod cert.p))).Separable :=
    separable_map_of_discr_ne_zero f hf hdeg (Int.castRingHom (ZMod cert.p)) cert.hdisc
  have hdiscℚ : (Int.castRingHom ℚ) f.discr ≠ 0 := fun h =>
    cert.hdisc (by rw [(map_eq_zero_iff _ (RingHom.injective_int _)).mp h, map_zero])
  have hsepℚ : (f.map (Int.castRingHom ℚ)).Separable :=
    separable_map_of_discr_ne_zero f hf hdeg (Int.castRingHom ℚ) hdiscℚ
  have : IsSplittingField ℚ (f.map (Int.castRingHom ℚ)).SplittingField
      (f.map (Int.castRingHom ℚ)) :=
    Polynomial.IsSplittingField.splittingField _
  have : IsGalois ℚ (f.map (Int.castRingHom ℚ)).SplittingField :=
    IsGalois.of_separable_splitting_field hsepℚ
  have : NumberField (f.map (Int.castRingHom ℚ)).SplittingField := splittingField_numberField _
  have : IsGaloisGroup ((f.map (Int.castRingHom ℚ)).SplittingField ≃ₐ[ℚ]
      (f.map (Int.castRingHom ℚ)).SplittingField) ℚ (f.map (Int.castRingHom ℚ)).SplittingField :=
    IsGaloisGroup.of_isGalois ℚ (f.map (Int.castRingHom ℚ)).SplittingField
  have : Algebra.IsInvariant ℤ (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField)
      ((f.map (Int.castRingHom ℚ)).SplittingField ≃ₐ[ℚ]
        (f.map (Int.castRingHom ℚ)).SplittingField) := IsGaloisGroup.isInvariant
  obtain ⟨σ, hσ⟩ := exists_galActionHom_partition_eq_factor_degrees cert.p f hf hsepf
  refine ⟨σ, ?_⟩
  rw [hσ, ← cert.hprod, normalizedFactors_prod_map_natDegree cert.factors cert.hirr]

end IdealArithmetic.Galois
