import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Weak equivalence of fractional ideals

Two fractional ideals `I` and `J` of a commutative ring `R` are weakly equivalent if their
localisations `I_𝔭` and `J_𝔭` are isomorphic `R_𝔭`-modules at every maximal ideal `𝔭` of `R`. The
LMFDB uses this for the fractional ideals of the orders `R` of the étale algebra `ℚ[F]` of an
isogeny class of abelian varieties over `𝔽_q` (LMFDB `av.fq.endomorphism_ring_notation`); weak
equivalence classes are also called local isomorphism classes, or genera. The LMFDB's remark that
weakly equivalent fractional ideals of such an order have the same multiplier ring,
`(I : I) = (J : J)`, is not formalised here.

## Main definitions

* `FractionalIdeal.WeaklyEquivalent` (LMFDB `av.weak_equivalence_class`,
  `av.fq.weak_equivalence_class`): `I` and `J` are weakly equivalent.
* `FractionalIdeal.weakEquivalenceSetoid`: weak equivalence as an equivalence relation.
* `FractionalIdeal.WeakEquivalenceClass` (LMFDB `av.fq.weak_equivalence_class`): the weak
  equivalence classes of fractional ideals.

## Main results

* `FractionalIdeal.weaklyEquivalent_iff_tensorProduct`: weak equivalence in terms of the base
  changes `I ⊗_R R_𝔭`, as the LMFDB states it.
* `FractionalIdeal.weaklyEquivalent_of_linearEquiv`: isomorphic fractional ideals are weakly
  equivalent.
-/

open scoped TensorProduct

namespace FractionalIdeal

variable {R : Type*} [CommRing R] {S : Submonoid R} {K : Type*} [CommRing K] [Algebra R K]
  {I J L : FractionalIdeal S K}

variable (I J) in
/-- Two fractional ideals `I` and `J` of a commutative ring `R` are **weakly equivalent** (LMFDB
`av.weak_equivalence_class`, `av.fq.weak_equivalence_class`) if their localisations
`I_𝔭 ≅ I ⊗_R R_𝔭` and `J_𝔭` are isomorphic `R_𝔭`-modules for every maximal ideal `𝔭` of `R`. The
LMFDB considers the fractional ideals of an order `R` of an étale `ℚ`-algebra `K`, the finitely
generated `R`-submodules of `K` containing a non-zero-divisor; such ideals are also called locally
isomorphic, or said to be in the same genus. -/
def WeaklyEquivalent : Prop :=
  ∀ (𝔭 : Ideal R) [𝔭.IsMaximal], Nonempty (LocalizedModule 𝔭.primeCompl (I : Submodule R K)
    ≃ₗ[Localization.AtPrime 𝔭] LocalizedModule 𝔭.primeCompl (J : Submodule R K))

lemma WeaklyEquivalent.refl : I.WeaklyEquivalent I :=
  fun _ _ ↦ ⟨LinearEquiv.refl _ _⟩

lemma WeaklyEquivalent.symm (hIJ : I.WeaklyEquivalent J) : J.WeaklyEquivalent I :=
  fun 𝔭 _ ↦ (hIJ 𝔭).map LinearEquiv.symm

lemma WeaklyEquivalent.trans (hIJ : I.WeaklyEquivalent J) (hJL : J.WeaklyEquivalent L) :
    I.WeaklyEquivalent L :=
  fun 𝔭 _ ↦ ⟨(hIJ 𝔭).some.trans (hJL 𝔭).some⟩

/-- Two fractional ideals `I` and `J` are weakly equivalent if and only if the base changes
`I ⊗_R R_𝔭` and `J ⊗_R R_𝔭` are isomorphic `R_𝔭`-modules for every maximal ideal `𝔭`, as the LMFDB
states it. -/
lemma weaklyEquivalent_iff_tensorProduct : I.WeaklyEquivalent J ↔ ∀ (𝔭 : Ideal R) [𝔭.IsMaximal],
    Nonempty (Localization.AtPrime 𝔭 ⊗[R] (I : Submodule R K) ≃ₗ[Localization.AtPrime 𝔭]
    Localization.AtPrime 𝔭 ⊗[R] (J : Submodule R K)) := by
  let e (𝔭 : Ideal R) [𝔭.IsMaximal] (I : FractionalIdeal S K) :
      Localization.AtPrime 𝔭 ⊗[R] (I : Submodule R K) ≃ₗ[Localization.AtPrime 𝔭]
      LocalizedModule 𝔭.primeCompl (I : Submodule R K) :=
    (IsLocalizedModule.isBaseChange 𝔭.primeCompl (Localization.AtPrime 𝔭)
      (LocalizedModule.mkLinearMap 𝔭.primeCompl (I : Submodule R K))).equiv
  refine forall_congr' fun 𝔭 ↦ forall_congr' fun _ ↦ ⟨.map fun φ ↦ ?_, .map fun ψ ↦ ?_⟩
  · exact ((e 𝔭 I).trans φ).trans (e 𝔭 J).symm
  · exact ((e 𝔭 I).symm.trans ψ).trans (e 𝔭 J)

/-- Isomorphic fractional ideals are weakly equivalent. -/
lemma weaklyEquivalent_of_linearEquiv (e : (I : Submodule R K) ≃ₗ[R] J) : I.WeaklyEquivalent J :=
  fun 𝔭 _ ↦ ⟨IsLocalizedModule.mapEquiv 𝔭.primeCompl (LocalizedModule.mkLinearMap _ _)
    (LocalizedModule.mkLinearMap _ _) (Localization.AtPrime 𝔭) e⟩

variable (S K)

/-- **Weak equivalence** of fractional ideals (`FractionalIdeal.WeaklyEquivalent`) as an
equivalence relation. -/
def weakEquivalenceSetoid : Setoid (FractionalIdeal S K) where
  r := WeaklyEquivalent
  iseqv := ⟨fun _ ↦ .refl, .symm, .trans⟩

/-- The **weak equivalence classes** (LMFDB `av.fq.weak_equivalence_class`) of fractional ideals:
the classes of fractional ideals up to weak equivalence (`FractionalIdeal.WeaklyEquivalent`), also
called local isomorphism classes, or genera. Mathlib's fractional ideals include some, such as the
zero ideal, that the LMFDB excludes (its fractional ideals contain a non-zero-divisor), so this type
also has their classes. -/
def WeakEquivalenceClass : Type _ :=
  Quotient (weakEquivalenceSetoid S K)

end FractionalIdeal
