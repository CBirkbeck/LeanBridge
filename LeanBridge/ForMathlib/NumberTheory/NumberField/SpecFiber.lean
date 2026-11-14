import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Over

/-!
# The fibres of `Spec 𝓞_F → Spec ℤ`

For a ring homomorphism `R → S`, the fibre of the map `Spec S → Spec R` over a prime `𝔭` of `R` is
the set of the primes of `S` lying over `𝔭`, Mathlib's `Ideal.primesOver`. For the ring of integers
`𝓞_F` of a number field `F` and a rational prime `p`, the fibre of `Spec 𝓞_F → Spec ℤ` above `p`
is therefore the set of primes of `𝓞_F` lying above `p` (LMFDB `nf.picture`), both as the preimage
of the point `(p)` and as the underlying set of the scheme-theoretic fibre
(`AlgebraicGeometry.Scheme.Hom.range_fiberι`).

## Main results

* `PrimeSpectrum.preimage_comap_singleton_eq_primesOver`: the fibre of `Spec S → Spec R` over `𝔭`
  is the set of primes of `S` lying over `𝔭`.
* `NumberField.range_fiberι_spec_map_algebraMap_int` (LMFDB `nf.picture`): the scheme-theoretic
  fibre of `Spec 𝓞_F → Spec ℤ` above a rational prime `p` has the primes of `𝓞_F` lying above `p`
  as its points.
-/

open AlgebraicGeometry

namespace PrimeSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **The fibre of `Spec S → Spec R` over a prime `𝔭` is the set of primes of `S` lying over
`𝔭`.** -/
lemma preimage_comap_singleton_eq_primesOver (𝔭 : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {𝔭} = {P | P.asIdeal ∈ 𝔭.asIdeal.primesOver S} :=
  Set.ext fun P ↦
    ⟨fun h ↦ ⟨P.isPrime, ⟨congrArg asIdeal h.symm⟩⟩, fun h ↦ PrimeSpectrum.ext h.2.over.symm⟩

end PrimeSpectrum

namespace NumberField

variable (F : Type) [Field F] {p : ℕ}

/-- **The fibre of `Spec 𝓞_F → Spec ℤ` above a rational prime `p` is the set of the primes of `𝓞_F`
lying above `p`**: the points of the scheme-theoretic fibre over the point `(p)` of `Spec ℤ`. -/
lemma range_fiberι_spec_map_algebraMap_int (hp : (Ideal.span {(p : ℤ)}).IsPrime) :
    Set.range ((Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝓞 F)))).fiberι ⟨_, hp⟩) =
      {P | P.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F)} :=
  ((Spec.map _).range_fiberι _).trans <| PrimeSpectrum.preimage_comap_singleton_eq_primesOver _

end NumberField
