import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Points of an affine variety and maximal ideals of its coordinate ring

Let `K` be an algebraically closed field, such as `ℂ`, and let `I` be an ideal of the polynomial
ring `K[X_s : s ∈ σ]` in finitely many variables. The points of the affine variety
`V(I) ⊆ K^σ` cut out by `I` are in bijection with the maximal ideals of its coordinate ring
`K[X] ⧸ I`: a point `x` corresponds to the ideal of the functions vanishing at `x`, the kernel of
the evaluation at `x`. This is Hilbert's Nullstellensatz, in Mathlib's form
`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`, together with the correspondence between
the ideals of `K[X] ⧸ I` and the ideals of `K[X]` containing `I`.

The LMFDB says that the points on a curve over `ℂ` are in bijection with the prime ideals of its
coordinate ring (LMFDB `nf.picture`). This holds for the points of the curve as a scheme, the prime
spectrum of its coordinate ring (`PrimeSpectrum`, `AlgebraicGeometry.Spec`), which include the
generic point: the zero ideal of the coordinate ring of an irreducible curve is prime. The points
of the curve in `ℂ^σ` are the closed points among them, and correspond to the maximal ideals: for
these points the bijection is the one above, for every affine variety.

## Main definitions

* `MvPolynomial.zeroLocusToMaximalSpectrum`: the maximal ideal of the coordinate ring `K[X] ⧸ I`
  of the functions vanishing at a point of `V(I)`.

## Main results

* `MvPolynomial.bijective_zeroLocusToMaximalSpectrum` (LMFDB `nf.picture`): over an algebraically
  closed field, the points of `V(I)` are in bijection with the maximal ideals of `K[X] ⧸ I`.
-/

namespace MvPolynomial

variable {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))

/-- The evaluation at a point `x` of the zero locus of `I`, as a map from the coordinate ring
`K[X] ⧸ I`. -/
noncomputable def evalZeroLocus (x : zeroLocus K I) : MvPolynomial σ K ⧸ I →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (aeval x.1) x.2

/-- The maximal ideal of the coordinate ring `K[X] ⧸ I` of the functions vanishing at a point `x`
of the zero locus of `I`: the kernel of the evaluation at `x`. -/
noncomputable def zeroLocusToMaximalSpectrum (x : zeroLocus K I) :
    MaximalSpectrum (MvPolynomial σ K ⧸ I) :=
  ⟨RingHom.ker (evalZeroLocus I x),
    RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap K _ c, AlgHom.commutes _ c⟩⟩

lemma mk_mem_zeroLocusToMaximalSpectrum_iff (x : zeroLocus K I) (p : MvPolynomial σ K) :
    Ideal.Quotient.mk I p ∈ (zeroLocusToMaximalSpectrum I x).asIdeal ↔ aeval x.1 p = 0 :=
  Iff.rfl

variable [IsAlgClosed K] [Finite σ]

/-- **The points of an affine variety over an algebraically closed field are in bijection with the
maximal ideals of its coordinate ring**: the map sending a point `x` of `V(I)` to the maximal ideal
of `K[X] ⧸ I` of the functions vanishing at `x` is bijective. -/
lemma bijective_zeroLocusToMaximalSpectrum : Function.Bijective (zeroLocusToMaximalSpectrum I) := by
  refine ⟨fun x y hxy ↦ Subtype.ext <| funext fun s ↦ ?_, fun m ↦ ?_⟩
  · have h : Ideal.Quotient.mk I (X s - C (y.1 s)) ∈ (zeroLocusToMaximalSpectrum I y).asIdeal :=
      (mk_mem_zeroLocusToMaximalSpectrum_iff I y _).mpr <| by simp
    rw [← hxy, mk_mem_zeroLocusToMaximalSpectrum_iff] at h
    simpa [sub_eq_zero] using h
  · have hm : (m.asIdeal.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    rcases isMaximal_iff_eq_vanishingIdeal_singleton.mp hm with ⟨x, hx⟩
    have hxI : x ∈ zeroLocus K I := fun p hp ↦ by
      have h : p ∈ m.asIdeal.comap (Ideal.Quotient.mk I) := by
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      rwa [hx, mem_vanishingIdeal_singleton_iff] at h
    refine ⟨⟨x, hxI⟩, MaximalSpectrum.ext <| Ideal.ext fun q ↦ ?_⟩
    rcases Ideal.Quotient.mk_surjective q with ⟨p, rfl⟩
    rw [mk_mem_zeroLocusToMaximalSpectrum_iff, ← mem_vanishingIdeal_singleton_iff, ← hx,
      Ideal.mem_comap]

end MvPolynomial
