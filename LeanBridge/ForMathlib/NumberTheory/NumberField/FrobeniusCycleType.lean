import TauCeti.FieldTheory.Normal.Embeddings
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.SplittingType

/-!
# Frobenius cycle types

Let `K / F` be a finite extension of number fields and `L / F` a finite Galois extension into which
`K` embeds. The Galois group `Gal(L/F)` permutes the `F`-embeddings `K → L` by postcomposition,
which embeds it into the symmetric group on `[K : F]` letters. If `p` is a prime of `F` unramified
in `L`, the Frobenius elements at the primes of `L` above `p` are conjugate, so their images have
one cycle type: the Frobenius cycle type of `p` in `K`. It is the multiset of residue degrees of
the primes of `K` above `p`, which is how we define it, so that it involves no choices; Tau Ceti's
`Ideal.fullCycleType_toPerm_quotient_eq_map_inertiaDeg`, the decomposition-orbit form of the
splitting law, identifies it with the cycle type of a Frobenius element. The LMFDB takes `F = ℚ`.

## Main definitions

* `NumberField.frobeniusCycleType` (LMFDB `nf.frobenius_cycle_types`).

## Main results

* `NumberField.fullCycleType_toPerm_eq_frobeniusCycleType`: the cycle type of a Frobenius element
  at an unramified prime of `L` above `p`, acting on the embeddings `K → L`, is the Frobenius cycle
  type of `p` in `K`.
* `NumberField.frobeniusCycleType_congr`: isomorphic extensions have the same Frobenius cycle
  types.
-/

open Equiv Ideal MulAction TauCeti.FieldTheory

namespace NumberField

variable {F : Type*} [Field F] (K : Type*) [Field K] [NumberField K] [Algebra F K] (p : Ideal (𝓞 F))
  [p.IsMaximal] {K' L : Type*} [Field K'] [NumberField K'] [Algebra F K'] [Field L] [NumberField L]
  [Algebra F L] [IsGalois F L]

/-- The **Frobenius cycle type** of a prime `p` of `F` in a finite extension `K / F` of number
fields (LMFDB `nf.frobenius_cycle_types`, where `F = ℚ`): the multiset of the residue degrees of the
primes of `K` above `p`.

The LMFDB defines it for the primes `p` unramified in `K`. When `p` is unramified in a Galois
extension `L / F` containing a copy of `K`, this is the cycle type, fixed points included, of the
permutation of the embeddings `K → L` induced by a Frobenius element at any prime of `L` above `p`
(`fullCycleType_toPerm_eq_frobeniusCycleType`), which is the LMFDB's definition. That theorem shows
in particular that the LMFDB's definition does not depend on the choices of `L`, of the prime of
`L` and of the Frobenius element. For a ramified `p` the multiset of residue degrees, which no
longer sums to `[K : F]`, is a value outside the LMFDB's definition. -/
noncomputable def frobeniusCycleType : Multiset ℕ :=
  (Finset.univ : Finset (p.primesOver (𝓞 K))).val.map fun P ↦ P.1.inertiaDeg (𝓞 F)

variable {K} (e : K ≃ₐ[F] K')

omit [NumberField K] [NumberField K'] in
private lemma inertiaDeg_comap_mapAlgEquiv (P : p.primesOver (𝓞 K')) :
    (P.1.comap (RingOfIntegers.mapAlgEquiv e)).inertiaDeg (𝓞 F) = P.1.inertiaDeg (𝓞 F) := by
  rw [p.inertiaDeg_eq_of_isMaximal, p.inertiaDeg_eq_of_isMaximal]
  exact Quotient.algEquivOfEqComap p (RingOfIntegers.mapAlgEquiv e) rfl |>.toLinearEquiv.finrank_eq

include e in
/-- Isomorphic extensions of `F` have the same Frobenius cycle types. -/
lemma frobeniusCycleType_congr : frobeniusCycleType K p = frobeniusCycleType K' p := by
  let eP : p.primesOver (𝓞 K') ≃ p.primesOver (𝓞 K) :=
    { toFun P := ⟨P.1.comap (RingOfIntegers.mapAlgEquiv e), inferInstance, inferInstance⟩
      invFun P := ⟨P.1.comap (RingOfIntegers.mapAlgEquiv e).symm, inferInstance, inferInstance⟩
      left_inv _ := by
        ext x
        simp
      right_inv _ := by
        ext x
        simp }
  rw [frobeniusCycleType, ← Multiset.map_univ_val_equiv eP, Multiset.map_map]
  exact Multiset.map_congr rfl fun P _ ↦ inertiaDeg_comap_mapAlgEquiv p e P

open scoped Classical in
/-- **Frobenius cycle types.** Let `L / F` be a finite Galois extension into which `K` embeds, and
`σ ∈ Gal(L/F)` a Frobenius element at a prime `Q` of `L` above `p` unramified over `F`. Then the
cycle type, fixed points included, of the permutation of the embeddings `K → L` induced by `σ` is
the multiset of the residue degrees of the primes of `K` above `p`. -/
lemma fullCycleType_toPerm_eq_frobeniusCycleType [NumberField F] (φ : K →ₐ[F] L) (Q : Ideal (𝓞 L))
    [Q.IsPrime] [Q.LiesOver p] [Algebra.IsUnramifiedAt (𝓞 F) Q] {σ : L ≃ₐ[F] L}
    (hσ : IsArithFrobAt (𝓞 F) σ Q) :
    (MulAction.toPerm σ : Equiv.Perm (K →ₐ[F] L)).fullCycleType = frobeniusCycleType K p := by
  have h : (MulAction.toPerm σ : Equiv.Perm (K →ₐ[F] L)) =
      (fixingSubgroupQuotientEquivAlgHom φ).permCongr (MulAction.toPerm σ) := by
    ext ψ : 1
    rcases (fixingSubgroupQuotientEquivAlgHom φ).surjective ψ with ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with | H g => ?_
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, MulAction.toPerm_apply,
      MulAction.toPerm_apply, Quotient.smul_mk, fixingSubgroupQuotientEquivAlgHom_mk,
      fixingSubgroupQuotientEquivAlgHom_mk]
    rfl
  rw [h, Perm.fullCycleType_permCongr, fullCycleType_toPerm_quotient_eq_map_inertiaDeg p Q _ hσ]
  exact (congrArg (fun E : IntermediateField F L ↦ frobeniusCycleType E p)
    (IsGalois.fixedField_fixingSubgroup φ.fieldRange)).trans
    (frobeniusCycleType_congr p φ.equivFieldRange).symm

end NumberField
