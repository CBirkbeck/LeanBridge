import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Characters of integral extensions

Let `B` be a commutative algebra over an algebraically closed field `K`, integral over a subalgebra
`A`. The kernel of a `K`-algebra homomorphism `φ : A → K` is a maximal ideal, so by lying over it is
the contraction of a maximal ideal `Q` of `B`; the field `B ⧸ Q` is integral over `K`, hence is `K`,
and `B → B ⧸ Q ≃ K` extends `φ` (`Subalgebra.exists_algHom_eq_of_isIntegral`).

## Main results

* `Subalgebra.exists_algHom_eq_of_isIntegral`: characters extend along integral extensions.
-/

namespace Subalgebra

open Ideal Polynomial in
/-- **Characters extend along integral extensions** (lying over and the Nullstellensatz): if a
commutative algebra `B` over an algebraically closed field `K` is integral over a subalgebra `A`,
every `K`-algebra homomorphism `A → K` is the restriction of one `B → K`. -/
lemma exists_algHom_eq_of_isIntegral {K B : Type*} [Field K] [IsAlgClosed K] [CommRing B]
    [Algebra K B] (A : Subalgebra K B) (hA : ∀ x : B, IsIntegral A x) (φ : A →ₐ[K] K) :
    ∃ ψ : B →ₐ[K] K, ∀ x : A, ψ x = φ x := by
  have hB : Algebra.IsIntegral A B := ⟨hA⟩
  have hmax : (RingHom.ker φ).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective φ fun c ↦ ⟨algebraMap K A c, φ.commutes c⟩
  rcases exists_ideal_over_maximal_of_isIntegral (S := B) (RingHom.ker φ) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
    exact bot_le) with ⟨Q, hQ, hQP⟩
  have hcomp (a : A) : algebraMap B (B ⧸ Q) a = algebraMap K (B ⧸ Q) (φ a) := by
    rw [Quotient.algebraMap_eq, ← Quotient.mk_algebraMap, Quotient.mk_eq_mk_iff_sub_mem]
    have h : a - algebraMap K A (φ a) ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self]
    rw [← hQP, mem_under] at h
    simpa using h
  have hint : (algebraMap K (B ⧸ Q)).IsIntegral := fun x ↦ by
    rcases Quotient.mkₐ_surjective K Q x with ⟨b, rfl⟩
    rcases hA b with ⟨f, hf, hfb⟩
    refine ⟨f.map (φ : A →+* K), hf.map _, ?_⟩
    have e : (algebraMap K (B ⧸ Q)).comp (φ : A →+* K) =
        (algebraMap B (B ⧸ Q)).comp (algebraMap A B) :=
      RingHom.ext fun a ↦ (hcomp a).symm
    rw [Quotient.mkₐ_eq_mk, ← Quotient.algebraMap_eq, eval₂_map, e, ← hom_eval₂, hfb, map_zero]
  let e : K ≃ₐ[K] B ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ Q))
    (IsAlgClosed.ringHom_bijective_of_isIntegral _ hint)
  refine ⟨e.symm.toAlgHom.comp (Quotient.mkₐ K Q), fun a ↦ ?_⟩
  rw [AlgHom.comp_apply, Quotient.mkₐ_eq_mk, ← Quotient.algebraMap_eq, hcomp,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_eq]
  rfl

end Subalgebra
