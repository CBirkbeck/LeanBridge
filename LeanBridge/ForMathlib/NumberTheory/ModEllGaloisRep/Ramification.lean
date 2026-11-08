import LeanBridge.ForMathlib.NumberTheory.Artin.Basic
import LeanBridge.ForMathlib.NumberTheory.NumberField.InertiaFixedField

/-!
# Ramified primes of a mod-`ℓ` Galois representation

A prime `𝔭` of a number field `K` is ramified for a mod-`ℓ` Galois representation
`ρ : Gal(K̄/K) → G(𝔽_ℓ)` (LMFDB `modlgal.ramified`) if it is ramified in the splitting field `L`
of `ρ`, the fixed field of its kernel, a finite Galois extension of `K` since the kernel is open.
Equivalently, the inertia group in `Gal(K̄/K)` of a prime of `K̄` above `𝔭` is not contained in the
kernel of `ρ`: restriction maps it onto the inertia group of the prime of `L` below it
(`Ideal.map_inertia_restrictNormalHom`), which is trivial exactly when that prime is unramified.
The primes of `K̄` above `𝔭` are conjugate, so it does not matter which one is taken. Only the
kernel of `ρ` enters, so the results hold for a continuous homomorphism to any group, in
particular to the `𝔽_ℓ`-points `G(𝔽_ℓ)` of any algebraic group `G`, not only `GL_n`.

## Main results

* `MonoidHom.isUnramifiedIn_fixedField_ker_iff_forall` (LMFDB `modlgal.ramified`): `𝔭` is
  unramified in the fixed field of `ker ρ` exactly when the inertia groups of all the primes of
  `K̄` above `𝔭` lie in `ker ρ`.
* `MonoidHom.isUnramifiedIn_fixedField_ker_iff_exists` (LMFDB `modlgal.ramified`): the same with
  one prime of `K̄` above `𝔭`.
* `MonoidHom.not_isUnramifiedIn_fixedField_ker_iff_exists` and
  `MonoidHom.not_isUnramifiedIn_fixedField_ker_iff_forall` (LMFDB `modlgal.ramified`): `𝔭` is
  ramified exactly when the inertia group of some, equivalently of every, prime of `K̄` above `𝔭`
  is not contained in `ker ρ`.
-/

open IntermediateField NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H]
  {ρ : Gal(AlgebraicClosure K/K) →* H} (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]

/-- **A prime is unramified for `ρ` exactly when the inertia groups above it lie in `ker ρ`**
(LMFDB `modlgal.ramified`): for a continuous homomorphism `ρ` from `Gal(K̄/K)` to a group, a
prime `𝔭` of `K` is unramified in the fixed field of `ker ρ` exactly when the inertia group in
`Gal(K̄/K)` of every prime of `K̄` above `𝔭` is contained in `ker ρ`. -/
lemma isUnramifiedIn_fixedField_ker_iff_forall
    (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))) :
    Algebra.IsUnramifiedIn (𝓞 (fixedField ρ.ker)) 𝔭 ↔ ∀ P : Ideal (𝓞 (AlgebraicClosure K)),
      P.IsPrime → P.LiesOver 𝔭 → P.inertia Gal(AlgebraicClosure K/K) ≤ ρ.ker := by
  have : FiniteDimensional K (fixedField ρ.ker) := ρ.finiteDimensional_fixedField_ker hρ
  have : IsGalois K (fixedField ρ.ker) := ρ.isGalois_fixedField_ker hρ
  have : NumberField (fixedField ρ.ker) := .of_module_finite K _
  rw [(fixedField ρ.ker).isUnramifiedIn_iff_forall_inertia_le 𝔭, ρ.fixingSubgroup_fixedField_ker hρ]

/-- **A prime is unramified for `ρ` exactly when the inertia group of one prime above it lies in
`ker ρ`** (LMFDB `modlgal.ramified`): the primes of `K̄` above `𝔭` are conjugate. -/
lemma isUnramifiedIn_fixedField_ker_iff_exists
    (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))) :
    Algebra.IsUnramifiedIn (𝓞 (fixedField ρ.ker)) 𝔭 ↔ ∃ P : Ideal (𝓞 (AlgebraicClosure K)),
      P.IsPrime ∧ P.LiesOver 𝔭 ∧ P.inertia Gal(AlgebraicClosure K/K) ≤ ρ.ker := by
  have : FiniteDimensional K (fixedField ρ.ker) := ρ.finiteDimensional_fixedField_ker hρ
  have : IsGalois K (fixedField ρ.ker) := ρ.isGalois_fixedField_ker hρ
  have : NumberField (fixedField ρ.ker) := .of_module_finite K _
  rw [(fixedField ρ.ker).isUnramifiedIn_iff_exists_inertia_le 𝔭, ρ.fixingSubgroup_fixedField_ker hρ]

/-- **A prime is ramified for `ρ` exactly when the inertia group of some prime above it is not
contained in `ker ρ`** (LMFDB `modlgal.ramified`). -/
lemma not_isUnramifiedIn_fixedField_ker_iff_exists
    (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))) :
    ¬Algebra.IsUnramifiedIn (𝓞 (fixedField ρ.ker)) 𝔭 ↔ ∃ P : Ideal (𝓞 (AlgebraicClosure K)),
      P.IsPrime ∧ P.LiesOver 𝔭 ∧ ¬P.inertia Gal(AlgebraicClosure K/K) ≤ ρ.ker := by
  simp_rw [isUnramifiedIn_fixedField_ker_iff_forall 𝔭 hρ, not_forall, exists_prop]

/-- **A prime is ramified for `ρ` exactly when the inertia group of every prime above it is not
contained in `ker ρ`** (LMFDB `modlgal.ramified`). -/
lemma not_isUnramifiedIn_fixedField_ker_iff_forall
    (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))) :
    ¬Algebra.IsUnramifiedIn (𝓞 (fixedField ρ.ker)) 𝔭 ↔ ∀ P : Ideal (𝓞 (AlgebraicClosure K)),
      P.IsPrime → P.LiesOver 𝔭 → ¬P.inertia Gal(AlgebraicClosure K/K) ≤ ρ.ker := by
  simp_rw [isUnramifiedIn_fixedField_ker_iff_exists 𝔭 hρ, not_exists, not_and]

end MonoidHom
