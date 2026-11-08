import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import LeanBridge.ForMathlib.NumberTheory.RamificationInertia.AbsoluteGaloisInertia
import TauCeti.FieldTheory.KrullTopology
import TauCeti.NumberTheory.RamificationInertia.Unramified

/-!
# Inertia groups of the absolute Galois group and ramification in finite Galois subextensions

Let `K` be a field of characteristic zero, `K̄` its algebraic closure and `G = Gal(K̄/K)`, acting on
the ring `𝓞 K̄` of algebraic integers of `K̄`. For a finite Galois extension `L` of `K` inside `K̄`,
restriction `G → Gal(L/K)` maps the inertia group of a prime `P` of `𝓞 K̄` onto the inertia group
of the prime `P ∩ 𝓞 L` of `𝓞 L`. Its kernel `Gal(K̄/L)` is a profinite group acting continuously on
the discrete ring `𝓞 K̄` with invariants `𝓞 L`, so this is
`Ideal.map_inertia_of_surjective_of_profinite`. Hence the inertia group of `P` lies in `Gal(K̄/L)`
exactly when the inertia group of `P ∩ 𝓞 L` in `Gal(L/K)` is trivial, and a prime of a base below
`𝓞 L` is unramified in `L` exactly when the inertia groups of all, equivalently of some, of the
primes of `K̄` above it lie in `Gal(K̄/L)`.

## Main results

* `Ideal.map_inertia_restrictNormalHom`: restriction maps the inertia group of `P` in `Gal(K̄/K)`
  onto the inertia group of `P ∩ 𝓞 L` in `Gal(L/K)`.
* `Ideal.inertia_le_fixingSubgroup_iff`: the inertia group of `P` lies in `Gal(K̄/L)` exactly when
  that of `P ∩ 𝓞 L` in `Gal(L/K)` is trivial.
* `IntermediateField.isUnramifiedIn_iff_forall_inertia_le` and
  `IntermediateField.isUnramifiedIn_iff_exists_inertia_le`: a prime is unramified in `L` exactly
  when the inertia groups of all, equivalently of some, of the primes of `K̄` above it lie in
  `Gal(K̄/L)`.
-/

open Algebra Ideal IntermediateField MulAction NumberField

variable {K : Type*} [Field K] (L : IntermediateField K (AlgebraicClosure K))

namespace Ideal

variable (P : Ideal (𝓞 (AlgebraicClosure K))) [P.IsPrime]

lemma isOpen_stabilizer_fixingSubgroup (b : 𝓞 (AlgebraicClosure K)) :
    IsOpen (stabilizer L.fixingSubgroup b : Set L.fixingSubgroup) := by
  have h : IsOpen {σ : Gal(AlgebraicClosure K/K) | σ (b : AlgebraicClosure K) = b} :=
    (IsIntegral.isIntegral (R := K) (b : AlgebraicClosure K)).isLocallyConstant_apply
      |>.isOpen_fiber _
  have heq : (stabilizer L.fixingSubgroup b : Set L.fixingSubgroup) = Subtype.val ⁻¹'
      {σ : Gal(AlgebraicClosure K/K) | σ (b : AlgebraicClosure K) = b} := by
    ext σ
    exact RingOfIntegers.ext_iff
  rw [heq]
  exact h.preimage continuous_subtype_val

variable [CharZero K] in
lemma isInvariant_fixingSubgroup :
    Algebra.IsInvariant (𝓞 L) (𝓞 (AlgebraicClosure K)) L.fixingSubgroup where
  isInvariant b hb := by
    have hbL : (b : AlgebraicClosure K) ∈ fixedField L.fixingSubgroup := fun σ ↦
      congrArg Subtype.val (hb σ)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hbL
    refine ⟨⟨⟨_, hbL⟩, ?_⟩, Subtype.ext rfl⟩
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L (AlgebraicClosure K))
      (algebraMap L (AlgebraicClosure K)).injective).mp b.2

variable [CharZero K] [FiniteDimensional K L] [Normal K L] in
/-- **Restriction maps inertia groups onto inertia groups**: for a finite Galois extension `L` of
`K` inside `K̄`, restriction `Gal(K̄/K) → Gal(L/K)` maps the inertia group of a prime `P` of `𝓞 K̄`
onto the inertia group of `P ∩ 𝓞 L`. -/
lemma map_inertia_restrictNormalHom :
    (P.inertia Gal(AlgebraicClosure K/K)).map (AlgEquiv.restrictNormalHom L) =
      (P.under (𝓞 L)).inertia Gal(L/K) := by
  let : TopologicalSpace (𝓞 (AlgebraicClosure K)) := ⊥
  have : DiscreteTopology (𝓞 (AlgebraicClosure K)) := ⟨rfl⟩
  have : CompactSpace L.fixingSubgroup :=
    isCompact_iff_compactSpace.mp (L.fixingSubgroup_isClosed).isCompact
  have : ContinuousSMul L.fixingSubgroup (𝓞 (AlgebraicClosure K)) :=
    continuousSMul_iff_stabilizer_isOpen.mpr (isOpen_stabilizer_fixingSubgroup L)
  have : Algebra.IsInvariant (𝓞 L) (𝓞 (AlgebraicClosure K)) L.fixingSubgroup :=
    isInvariant_fixingSubgroup L
  refine map_inertia_of_surjective_of_profinite _ L.fixingSubgroup _ P
    (AlgEquiv.restrictNormalHom_surjective _) (restrictNormalHom_ker L).ge fun σ x ↦ ?_
  exact Subtype.ext (AlgEquiv.restrictNormal_commutes σ L x)

variable [CharZero K] [FiniteDimensional K L] [Normal K L] in
/-- **The inertia group of a prime of `K̄` lies in `Gal(K̄/L)` exactly when that of the prime of `L`
below it is trivial**, for a finite Galois extension `L` of `K` inside `K̄`. -/
lemma inertia_le_fixingSubgroup_iff : P.inertia Gal(AlgebraicClosure K/K) ≤ L.fixingSubgroup ↔
    (P.under (𝓞 L)).inertia Gal(L/K) = ⊥ := by
  rw [← map_inertia_restrictNormalHom, Subgroup.map_eq_bot_iff, restrictNormalHom_ker]

end Ideal

namespace IntermediateField

variable [CharZero K] [FiniteDimensional K L] [IsGalois K L] {R : Type*} [CommRing R] [IsDomain R]
  [Algebra R (𝓞 L)] [Algebra R (𝓞 (AlgebraicClosure K))]
  [IsScalarTower R (𝓞 L) (𝓞 (AlgebraicClosure K))] [Module.Finite R (𝓞 L)] [Module.Flat R (𝓞 L)]
  [IsGaloisGroup Gal(L/K) R (𝓞 L)] (𝔭 : Ideal R) [𝔭.IsMaximal]

/-- **A prime is unramified in `L` exactly when the inertia groups of the primes of `K̄` above it
lie in `Gal(K̄/L)`**, for a finite Galois extension `L` of `K` inside `K̄` whose ring of integers
is finite, flat and Galois over a base `R`. -/
lemma isUnramifiedIn_iff_forall_inertia_le : Algebra.IsUnramifiedIn (𝓞 L) 𝔭 ↔
    ∀ P : Ideal (𝓞 (AlgebraicClosure K)), P.IsPrime → P.LiesOver 𝔭 →
      P.inertia Gal(AlgebraicClosure K/K) ≤ L.fixingSubgroup := by
  rw [isUnramifiedIn_iff_forall_inertia_eq_bot (G := Gal(L/K)) 𝔭]
  refine ⟨fun h P _ _ ↦ (inertia_le_fixingSubgroup_iff L P).mpr
    (h _ ⟨inferInstance, inferInstance⟩), fun h Q ⟨_, _⟩ ↦ ?_⟩
  rcases nonempty_primesOver (S := 𝓞 (AlgebraicClosure K)) Q with ⟨P, _, hPQ⟩
  have : P.LiesOver 𝔭 := LiesOver.trans P Q 𝔭
  rw [hPQ.over]
  exact (inertia_le_fixingSubgroup_iff L P).mp (h P inferInstance this)

variable [Algebra.IsIntegral R (𝓞 (AlgebraicClosure K))]
  [FaithfulSMul R (𝓞 (AlgebraicClosure K))] in
/-- **A prime is unramified in `L` exactly when the inertia group of some prime of `K̄` above it
lies in `Gal(K̄/L)`**, for a finite Galois extension `L` of `K` inside `K̄` whose ring of integers
is finite, flat and Galois over a base `R`: the primes of `L` above it are conjugate. -/
lemma isUnramifiedIn_iff_exists_inertia_le : Algebra.IsUnramifiedIn (𝓞 L) 𝔭 ↔
    ∃ P : Ideal (𝓞 (AlgebraicClosure K)), P.IsPrime ∧ P.LiesOver 𝔭 ∧
      P.inertia Gal(AlgebraicClosure K/K) ≤ L.fixingSubgroup := by
  refine ⟨fun h ↦ ?_, fun ⟨P, _, _, hle⟩ ↦ ?_⟩
  · rcases nonempty_primesOver (S := 𝓞 (AlgebraicClosure K)) 𝔭 with ⟨P, hP, hP𝔭⟩
    exact ⟨P, hP, hP𝔭, (L.isUnramifiedIn_iff_forall_inertia_le 𝔭).mp h P hP hP𝔭⟩
  rw [isUnramifiedIn_iff_forall_inertia_eq_bot (G := Gal(L/K)) 𝔭]
  rintro Q ⟨_, _⟩
  have h₀ : (P.under (𝓞 L)).inertia Gal(L/K) = ⊥ := (inertia_le_fixingSubgroup_iff L P).mp hle
  rcases IsInvariant.exists_smul_of_under_eq R (𝓞 L) Gal(L/K) (P.under (𝓞 L)) Q
    ((over_def (P.under (𝓞 L)) 𝔭).symm.trans (over_def Q 𝔭)) with ⟨τ, rfl⟩
  rw [inertia_smul, h₀, Subgroup.map_bot]

end IntermediateField
