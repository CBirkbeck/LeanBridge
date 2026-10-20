import TauCeti.NumberTheory.NumberField.Index.CommonIndexDivisor
import TauCeti.NumberTheory.NumberField.Monogenic

/-!
# The index of a number field

Tau Ceti defines the index `[𝓞 K : ℤ[θ]]` of an integral primitive element `θ` of a number field `K`
(`TauCeti.NumberField.IntegralPrimitiveElement.index`) and the common index divisors of `K`, the
primes dividing all of these indices (`TauCeti.NumberField.IsCommonIndexDivisor`). This file
defines their greatest common divisor, the index of `K`.

## Main definitions

* `NumberField.fieldIndex` (LMFDB `nf.zk_index`).

## Main results

* `NumberField.nonempty_integralPrimitiveElement`: every number field has an integral primitive
  element.
* `NumberField.dvd_fieldIndex_iff`: the index of `K` is the greatest common divisor of the indices
  `[𝓞 K : ℤ[θ]]`, in the sense of divisibility.
* `NumberField.fieldIndex_pos`: the index of `K` is positive.
* `NumberField.isCommonIndexDivisor_iff_dvd_fieldIndex`: the common index divisors are the
  divisors of the index of `K`.
* `NumberField.fieldIndex_eq_one_of_isMonogenic`: a monogenic field has index `1`.
-/

open TauCeti.NumberField IntermediateField

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

/-- Every number field has an integral primitive element: a primitive element scaled by a nonzero
integer to become an algebraic integer. -/
lemma nonempty_integralPrimitiveElement : Nonempty (IntegralPrimitiveElement K) := by
  rcases Field.exists_primitive_element ℚ K with ⟨α, hα⟩
  rcases ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr
    (IsAlgebraic.of_finite ℚ α)).exists_integral_multiple with ⟨y, hy, hint⟩
  refine ⟨⟨⟨y • α, hint⟩, ?_⟩⟩
  rw [← adjoin_eq_top_iff_of_isAlgebraic fun x _ ↦ IsAlgebraic.of_finite ℚ x, eq_top_iff, ← hα,
    adjoin_simple_le_iff]
  have h : (y : ℚ)⁻¹ • (y • α) = α := by
    rw [← Int.cast_smul_eq_zsmul ℚ, inv_smul_smul₀ (Int.cast_ne_zero.mpr hy)]
  exact (congrArg (· ∈ ℚ⟮y • α⟯) h).mp (smul_mem _ (mem_adjoin_simple_self ℚ _))

/-- The **index** of a number field `K` (LMFDB `nf.zk_index`): the greatest common divisor of the
indices `[𝓞 K : ℤ[θ]]` of the algebraic integers `θ` with `K = ℚ(θ)`, defined as the largest
natural number dividing all of them (`dvd_fieldIndex_iff` shows that it is their greatest common
divisor in the sense of divisibility as well). -/
noncomputable def fieldIndex : ℕ :=
  sSup {d | ∀ θ : IntegralPrimitiveElement K, d ∣ θ.index}

private lemma bddAbove_setOf_dvd_index :
    BddAbove {d | ∀ θ : IntegralPrimitiveElement K, d ∣ θ.index} := by
  rcases nonempty_integralPrimitiveElement K with ⟨θ⟩
  exact ⟨θ.index, fun _ hd ↦ Nat.le_of_dvd θ.index_pos (hd θ)⟩

private lemma fieldIndex_mem : fieldIndex K ∈ {d | ∀ θ : IntegralPrimitiveElement K, d ∣ θ.index} :=
  Nat.sSup_mem ⟨1, fun θ ↦ one_dvd θ.index⟩ (bddAbove_setOf_dvd_index K)

lemma fieldIndex_dvd_index (θ : IntegralPrimitiveElement K) : fieldIndex K ∣ θ.index :=
  fieldIndex_mem K θ

/-- The index of a number field is positive. -/
lemma fieldIndex_pos : 0 < fieldIndex K := by
  rcases nonempty_integralPrimitiveElement K with ⟨θ⟩
  exact Nat.pos_of_dvd_of_pos (fieldIndex_dvd_index K θ) θ.index_pos

/-- The index of `K` is the greatest common divisor of the indices of the integral primitive
elements of `K`: it is divisible by every common divisor of them. -/
lemma dvd_fieldIndex_iff : d ∣ fieldIndex K ↔ ∀ θ : IntegralPrimitiveElement K, d ∣ θ.index := by
  refine ⟨fun h θ ↦ h.trans (fieldIndex_dvd_index K θ), fun h ↦ ?_⟩
  rcases nonempty_integralPrimitiveElement K with ⟨θ⟩
  have hle : d.lcm (fieldIndex K) ≤ fieldIndex K :=
    le_csSup (bddAbove_setOf_dvd_index K) fun θ ↦ Nat.lcm_dvd (h θ) (fieldIndex_dvd_index K θ)
  exact (d.dvd_lcm_left _).trans <| dvd_of_eq <| hle.antisymm <| Nat.le_of_dvd
    (Nat.lcm_pos (Nat.pos_of_dvd_of_pos (h θ) θ.index_pos) (fieldIndex_pos K))
    (Nat.dvd_lcm_right _ _)

/-- The common index divisors of `K` are the divisors of the index of `K`. -/
lemma isCommonIndexDivisor_iff_dvd_fieldIndex : IsCommonIndexDivisor d K ↔ d ∣ fieldIndex K :=
  isCommonIndexDivisor_iff.trans (dvd_fieldIndex_iff K).symm

/-- A monogenic number field, one with `𝓞 K = ℤ[θ]`, has index `1`. -/
lemma fieldIndex_eq_one_of_isMonogenic (h : IsMonogenic K) : fieldIndex K = 1 := by
  rcases isMonogenic_iff_exists_index_eq_one.mp h with ⟨θ, hθ⟩
  exact Nat.dvd_one.mp (hθ ▸ fieldIndex_dvd_index K θ)

end NumberField
