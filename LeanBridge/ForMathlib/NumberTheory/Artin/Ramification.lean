import LeanBridge.ForMathlib.NumberTheory.Artin.Basic
import LeanBridge.ForMathlib.NumberTheory.NumberField.InertiaFixedField
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Ramified and unramified primes of an Artin representation

A prime `p` is ramified for an Artin representation `ρ` of `Gal(ℚ̄/ℚ)` (LMFDB
`artin.ramified_primes`) if it is ramified in its Artin field `K`, the fixed field of `ker ρ`, and
unramified (LMFDB `artin.unramified_primes`) otherwise. Equivalently, `p` is unramified exactly when
the inertia group in `Gal(ℚ̄/ℚ)` of a prime of `ℚ̄` above `p`, any one of them, lies in `ker ρ`:
restriction maps it onto the inertia group in `Gal(K/ℚ)` of the prime of `K` below it
(`Ideal.map_inertia_restrictNormalHom`), which is trivial exactly when that prime is unramified.
Read in `Gal(K/ℚ)`, through which `ρ` factors, the criterion says that the inertia group of a prime
of `K` above `p` is contained in the kernel of the induced representation, which is faithful: its
inverse image in `Gal(ℚ̄/ℚ)` lies in `ker ρ`.

## Main results

* `Representation.IsArtin.isUnramifiedIn_artinField_iff_forall` and
  `Representation.IsArtin.isUnramifiedIn_artinField_iff_exists` (LMFDB `artin.unramified_primes`):
  `p` is unramified exactly when the inertia groups of all, equivalently of some, of the primes of
  `ℚ̄` above `p` lie in `ker ρ`.
* `Representation.IsArtin.isUnramifiedIn_artinField_iff_forall_comap` and
  `Representation.IsArtin.isUnramifiedIn_artinField_iff_exists_comap` (LMFDB
  `artin.unramified_primes`): `p` is unramified exactly when, for all, equivalently for some, of
  the primes of the Artin field above `p`, the inverse images in `Gal(ℚ̄/ℚ)` of their inertia groups
  lie in `ker ρ`.
* `Representation.IsArtin.not_isUnramifiedIn_artinField_iff_exists` and
  `Representation.IsArtin.not_isUnramifiedIn_artinField_iff_forall` (LMFDB
  `artin.ramified_primes`): `p` is ramified exactly when the inertia group of some, equivalently of
  every, prime of `ℚ̄` above `p` is not contained in `ker ρ`.
-/

open Algebra IntermediateField NumberField

namespace Representation.IsArtin

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ Gal(AlgebraicClosure ℚ/ℚ) V} {p : ℕ}

lemma isMaximal_span_natCast (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

/-- **A prime is unramified for an Artin representation exactly when the inertia groups above it
lie in its kernel** (LMFDB `artin.unramified_primes`): `p` is unramified in the Artin field of `ρ`
exactly when the inertia group in `Gal(ℚ̄/ℚ)` of every prime of `ℚ̄` above `p` lies in `ker ρ`. -/
lemma isUnramifiedIn_artinField_iff_forall (h : ρ.IsArtin) (hp : p.Prime) :
    Algebra.IsUnramifiedIn (𝓞 ρ.artinField) (Ideal.span {(p : ℤ)}) ↔
      ∀ P : Ideal (𝓞 (AlgebraicClosure ℚ)), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
        P.inertia Gal(AlgebraicClosure ℚ/ℚ) ≤ ρ.ker := by
  have : FiniteDimensional ℚ ρ.artinField := h.finiteDimensional
  have : IsGalois ℚ ρ.artinField := h.isGalois
  have : NumberField ρ.artinField := .of_module_finite ℚ _
  have : (Ideal.span {(p : ℤ)}).IsMaximal := isMaximal_span_natCast hp
  rw [ρ.artinField.isUnramifiedIn_iff_forall_inertia_le, h.fixingSubgroup_artinField]

/-- **A prime is unramified for an Artin representation exactly when the inertia group of one prime
above it lies in its kernel** (LMFDB `artin.unramified_primes`): the primes of `ℚ̄` above `p` are
conjugate. -/
lemma isUnramifiedIn_artinField_iff_exists (h : ρ.IsArtin) (hp : p.Prime) :
    Algebra.IsUnramifiedIn (𝓞 ρ.artinField) (Ideal.span {(p : ℤ)}) ↔
      ∃ P : Ideal (𝓞 (AlgebraicClosure ℚ)), P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
        P.inertia Gal(AlgebraicClosure ℚ/ℚ) ≤ ρ.ker := by
  have : FiniteDimensional ℚ ρ.artinField := h.finiteDimensional
  have : IsGalois ℚ ρ.artinField := h.isGalois
  have : NumberField ρ.artinField := .of_module_finite ℚ _
  have : (Ideal.span {(p : ℤ)}).IsMaximal := isMaximal_span_natCast hp
  rw [ρ.artinField.isUnramifiedIn_iff_exists_inertia_le, h.fixingSubgroup_artinField]

lemma comap_inertia_le_ker_iff (h : ρ.IsArtin) (Q : Ideal (𝓞 ρ.artinField)) :
    haveI : Normal ℚ ρ.artinField := h.isGalois.to_normal
    (Q.inertia Gal(ρ.artinField/ℚ)).comap (AlgEquiv.restrictNormalHom ρ.artinField) ≤ ρ.ker ↔
      Q.inertia Gal(ρ.artinField/ℚ) = ⊥ := by
  have : IsGalois ℚ ρ.artinField := h.isGalois
  rw [← h.fixingSubgroup_artinField, ← restrictNormalHom_ker, ← MonoidHom.comap_bot,
    Subgroup.comap_le_comap_of_surjective (AlgEquiv.restrictNormalHom_surjective _), le_bot_iff]

/-- **A prime is unramified for an Artin representation exactly when the inertia groups of the
primes of the Artin field above it, read in `Gal(ℚ̄/ℚ)`, lie in its kernel** (LMFDB
`artin.unramified_primes`): `p` is unramified in the Artin field `K` of `ρ` exactly when, for every
prime of `K` above `p`, the inverse image in `Gal(ℚ̄/ℚ)` of its inertia group in `Gal(K/ℚ)` lies in
`ker ρ`, that is, its inertia group lies in the kernel of the representation of `Gal(K/ℚ)` through
which `ρ` factors. -/
lemma isUnramifiedIn_artinField_iff_forall_comap (h : ρ.IsArtin) (hp : p.Prime) :
    haveI : Normal ℚ ρ.artinField := h.isGalois.to_normal
    Algebra.IsUnramifiedIn (𝓞 ρ.artinField) (Ideal.span {(p : ℤ)}) ↔
      ∀ Q : Ideal (𝓞 ρ.artinField), Q.IsPrime → Q.LiesOver (Ideal.span {(p : ℤ)}) →
        (Q.inertia Gal(ρ.artinField/ℚ)).comap (AlgEquiv.restrictNormalHom ρ.artinField) ≤
          ρ.ker := by
  have : FiniteDimensional ℚ ρ.artinField := h.finiteDimensional
  have : IsGalois ℚ ρ.artinField := h.isGalois
  have : NumberField ρ.artinField := .of_module_finite ℚ _
  have : (Ideal.span {(p : ℤ)}).IsMaximal := isMaximal_span_natCast hp
  simp_rw [h.comap_inertia_le_ker_iff,
    Ideal.isUnramifiedIn_iff_forall_inertia_eq_bot (G := Gal(ρ.artinField/ℚ))]
  exact ⟨fun h Q hQ hQp ↦ h Q ⟨hQ, hQp⟩, fun h Q hQ ↦ h Q hQ.1 hQ.2⟩

/-- **A prime is unramified for an Artin representation exactly when the inertia group of one prime
of the Artin field above it, read in `Gal(ℚ̄/ℚ)`, lies in its kernel** (LMFDB
`artin.unramified_primes`): the primes of the Artin field above `p` are conjugate, and so are their
inertia groups. -/
lemma isUnramifiedIn_artinField_iff_exists_comap (h : ρ.IsArtin) (hp : p.Prime) :
    haveI : Normal ℚ ρ.artinField := h.isGalois.to_normal
    Algebra.IsUnramifiedIn (𝓞 ρ.artinField) (Ideal.span {(p : ℤ)}) ↔
      ∃ Q : Ideal (𝓞 ρ.artinField), Q.IsPrime ∧ Q.LiesOver (Ideal.span {(p : ℤ)}) ∧
        (Q.inertia Gal(ρ.artinField/ℚ)).comap (AlgEquiv.restrictNormalHom ρ.artinField) ≤
          ρ.ker := by
  have : FiniteDimensional ℚ ρ.artinField := h.finiteDimensional
  have : IsGalois ℚ ρ.artinField := h.isGalois
  have : NumberField ρ.artinField := .of_module_finite ℚ _
  have : (Ideal.span {(p : ℤ)}).IsMaximal := isMaximal_span_natCast hp
  rw [h.isUnramifiedIn_artinField_iff_forall_comap hp]
  refine ⟨fun hQ ↦ ?_, fun ⟨Q, _, _, hQ⟩ Q' _ _ ↦ ?_⟩
  · rcases Ideal.nonempty_primesOver (S := 𝓞 ρ.artinField) (Ideal.span {(p : ℤ)}) with
      ⟨Q, hQ', hQp⟩
    exact ⟨Q, hQ', hQp, hQ Q hQ' hQp⟩
  rcases IsInvariant.exists_smul_of_under_eq ℤ (𝓞 ρ.artinField) Gal(ρ.artinField/ℚ) Q Q'
    ((Ideal.over_def Q (Ideal.span {(p : ℤ)})).symm.trans
      (Ideal.over_def Q' (Ideal.span {(p : ℤ)}))) with ⟨τ, rfl⟩
  rw [h.comap_inertia_le_ker_iff] at hQ ⊢
  rw [Ideal.inertia_smul, hQ, Subgroup.map_bot]

/-- **A prime is ramified for an Artin representation exactly when the inertia group of some prime
above it is not contained in its kernel** (LMFDB `artin.ramified_primes`). -/
lemma not_isUnramifiedIn_artinField_iff_exists (h : ρ.IsArtin) (hp : p.Prime) :
    ¬Algebra.IsUnramifiedIn (𝓞 ρ.artinField) (Ideal.span {(p : ℤ)}) ↔
      ∃ P : Ideal (𝓞 (AlgebraicClosure ℚ)), P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
        ¬P.inertia Gal(AlgebraicClosure ℚ/ℚ) ≤ ρ.ker := by
  simp_rw [h.isUnramifiedIn_artinField_iff_forall hp, not_forall, exists_prop]

/-- **A prime is ramified for an Artin representation exactly when the inertia group of every prime
above it is not contained in its kernel** (LMFDB `artin.ramified_primes`). -/
lemma not_isUnramifiedIn_artinField_iff_forall (h : ρ.IsArtin) (hp : p.Prime) :
    ¬Algebra.IsUnramifiedIn (𝓞 ρ.artinField) (Ideal.span {(p : ℤ)}) ↔
      ∀ P : Ideal (𝓞 (AlgebraicClosure ℚ)), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
        ¬P.inertia Gal(AlgebraicClosure ℚ/ℚ) ≤ ρ.ker := by
  simp_rw [h.isUnramifiedIn_artinField_iff_exists hp, not_exists, not_and]

end Representation.IsArtin
