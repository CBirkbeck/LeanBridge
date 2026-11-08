import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.RingHom
import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
import TauCeti.NumberTheory.LocalField.IntegerRing.Basic
import TauCeti.NumberTheory.LocalField.Padic

/-!
# Nonarchimedean local fields of characteristic zero are `p`-adic fields

A `p`-adic field (LMFDB `lf.padic_field`) is a finite extension of `ℚ_p`, equivalently a
nonarchimedean local field of characteristic zero. Tau Ceti shows that a finite extension of `ℚ_p`
is a nonarchimedean local field (`TauCeti.finiteExtension_isNonarchimedeanLocalField`, with the
compatible valuation `TauCeti.algebraicExtension_valuativeExtension`), of characteristic zero
(`TauCeti.FinitePadicExtension.charZero`). This file proves the converse: a nonarchimedean local
field `K` of characteristic zero, with residue characteristic `p`, is a finite extension of `ℚ_p`
whose valuation extends the `p`-adic one, a `TauCeti.FinitePadicExtension K p`.

The construction is algebraic. As `p` lies in the maximal ideal `𝓂_K`, the reductions
`ℤ_p → ℤ / p ^ n → 𝒪_K / 𝓂_K ^ n` are compatible, and `𝒪_K` is `𝓂_K`-adically complete, so they
lift to a ring map `ℤ_p → 𝒪_K` (Mathlib's `IsAdicComplete.liftRingHom`). It is injective because
`p ^ n ≠ 0` in `K`, so it extends to the fraction field `ℚ_p`, and an element of `ℚ_p` is integral
exactly when its image is: the inverse of a non-integral element lies in `p ℤ_p`, which maps into
`𝓂_K`. Finiteness of `K` over `ℚ_p` is then Tau Ceti's `TauCeti.finite_of_valuativeExtension`.

## Main definitions

* `IsNonarchimedeanLocalField.padicIntToQuotient`: the reductions `ℤ_p → 𝒪_K / 𝓂_K ^ n`.
* `IsNonarchimedeanLocalField.padicIntToIntegerRing`: their lift `ℤ_p → 𝒪_K`.
* `IsNonarchimedeanLocalField.padicToField`: its extension `ℚ_p → K`.
* `IsNonarchimedeanLocalField.finitePadicExtension` (LMFDB `lf.padic_field`): the structure of a
  finite extension of `ℚ_p` on a nonarchimedean local field of characteristic zero.

## Main theorems

* `IsNonarchimedeanLocalField.nonempty_finitePadicExtension_ringChar` (LMFDB `lf.padic_field`): a
  nonarchimedean local field of characteristic zero is a finite extension of `ℚ_p`, for `p` its
  residue characteristic.
-/

open ValuativeRel IsLocalRing Ideal TauCeti

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

lemma natCast_ringChar_mem_maximalIdeal : (ringChar 𝓀[K] : 𝒪[K]) ∈ 𝓂[K] := by
  rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]

lemma isAdicComplete_maximalIdeal : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  infer_instance

variable (p : ℕ) [Fact p.Prime] (hp : (p : 𝒪[K]) ∈ 𝓂[K])

/-- The reduction `ℤ_p → ℤ / p ^ n → 𝒪_K / 𝓂_K ^ n` of `p`-adic integers into the quotients of the
ring of integers of a nonarchimedean local field `K` whose maximal ideal contains `p`. -/
noncomputable def padicIntToQuotient (n : ℕ) : ℤ_[p] →+* 𝒪[K] ⧸ 𝓂[K] ^ n :=
  (ZMod.castHom ((ringChar.spec (𝒪[K] ⧸ 𝓂[K] ^ n) (p ^ n)).1 <| by
    rw [Nat.cast_pow, ← map_natCast (algebraMap 𝒪[K] (𝒪[K] ⧸ 𝓂[K] ^ n)), ← map_pow,
      Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem]
    exact pow_mem_pow hp n) (𝒪[K] ⧸ 𝓂[K] ^ n)).comp (PadicInt.toZModPow n)

lemma factorPow_comp_padicIntToQuotient {m n : ℕ} (hle : m ≤ n) :
    (Quotient.factorPow 𝓂[K] hle).comp (padicIntToQuotient K p hp n) =
    padicIntToQuotient K p hp m := by
  rw [padicIntToQuotient, padicIntToQuotient, ← PadicInt.zmod_cast_comp_toZModPow m n hle,
    ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact RingHom.ext_zmod _ _

/-- The ring map `ℤ_p → 𝒪_K` into the ring of integers of a nonarchimedean local field `K` whose
maximal ideal contains `p`: the lift of the reductions `ℤ_p → 𝒪_K / 𝓂_K ^ n` through the
`𝓂_K`-adic completeness of `𝒪_K`. -/
noncomputable def padicIntToIntegerRing : ℤ_[p] →+* 𝒪[K] :=
  haveI : IsAdicComplete 𝓂[K] 𝒪[K] := isAdicComplete_maximalIdeal K
  IsAdicComplete.liftRingHom 𝓂[K] (padicIntToQuotient K p hp)
    (factorPow_comp_padicIntToQuotient K p hp)

lemma padicIntToIntegerRing_mem_maximalIdeal {z : ℤ_[p]} (hz : z ∈ maximalIdeal ℤ_[p]) :
    padicIntToIntegerRing K p hp z ∈ 𝓂[K] := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hz
  rcases hz with ⟨y, rfl⟩
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_right _ _ hp

lemma padicIntToIntegerRing_injective [CharZero K] :
    Function.Injective (padicIntToIntegerRing K p hp) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ by_contra fun hz₀ ↦ ?_
  rw [PadicInt.unitCoeff_spec hz₀, map_mul, map_pow, map_natCast] at hz
  have hp₀ : (p : 𝒪[K]) ^ z.valuation ≠ 0 :=
    pow_ne_zero _ fun h ↦ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero : (p : K) ≠ 0)
      (congrArg Subtype.val h)
  exact hp₀ <|
    ((PadicInt.unitCoeff hz₀).isUnit.map (padicIntToIntegerRing K p hp)).mul_right_eq_zero.1 hz

variable [CharZero K]

/-- The ring map `ℚ_p → K` into a nonarchimedean local field `K` of characteristic zero whose
maximal ideal contains `p`: the extension of `IsNonarchimedeanLocalField.padicIntToIntegerRing` to
the fraction field `ℚ_p` of `ℤ_p`. -/
noncomputable def padicToField : ℚ_[p] →+* K :=
  IsFractionRing.lift (A := ℤ_[p]) (g := (algebraMap 𝒪[K] K).comp (padicIntToIntegerRing K p hp))
    (Subtype.val_injective.comp (padicIntToIntegerRing_injective K p hp))

lemma padicToField_coe (z : ℤ_[p]) :
    padicToField K p hp z = (padicIntToIntegerRing K p hp z : K) :=
  IsFractionRing.lift_algebraMap _ z

open Valuation in
lemma padicToField_vle_one_iff (c : ℚ_[p]) : padicToField K p hp c ≤ᵥ 1 ↔ c ≤ᵥ 1 := by
  rw [(valuation ℚ_[p]).vle_one_iff, ← Valuation.mem_integer_iff, Padic.integerRing_eq_subring p]
  constructor
  · intro h
    by_contra hc
    rw [PadicInt.mem_subring_iff, not_le] at hc
    have hc₀ : c ≠ 0 := by
      rintro rfl
      norm_num at hc
    have hz : ‖c⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hc
    let z : ℤ_[p] := ⟨c⁻¹, (PadicInt.mem_subring_iff p).2 hz.le⟩
    have hm : padicIntToIntegerRing K p hp z ∈ 𝓂[K] :=
      padicIntToIntegerRing_mem_maximalIdeal K p hp
        ((IsLocalRing.mem_maximalIdeal _).2 (PadicInt.mem_nonunits.2 hz))
    have hcoe : padicToField K p hp c⁻¹ = padicIntToIntegerRing K p hp z :=
      padicToField_coe K p hp z
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Integer.not_isUnit_iff_valuation_lt_one,
      ← (valuation K).vlt_one_iff, ← hcoe, map_inv₀, inv_vlt_one ((map_ne_zero _).2 hc₀)] at hm
    exact (not_vle.2 hm) h
  · intro h
    let z : ℤ_[p] := ⟨c, h⟩
    have hcoe : padicToField K p hp c = padicIntToIntegerRing K p hp z :=
      padicToField_coe K p hp z
    rw [hcoe, (valuation K).vle_one_iff, ← Valuation.mem_integer_iff]
    exact (padicIntToIntegerRing K p hp z).2

lemma valuativeExtension_padicToField :
    letI : Algebra ℚ_[p] K := (padicToField K p hp).toAlgebra
    ValuativeExtension ℚ_[p] K := by
  let : Algebra ℚ_[p] K := (padicToField K p hp).toAlgebra
  refine ⟨fun a b ↦ ?_⟩
  rcases eq_or_ne b 0 with rfl | hb
  · rw [map_zero, vle_zero_iff, vle_zero_iff, RingHom.algebraMap_toAlgebra,
      map_eq_zero_iff _ (padicToField K p hp).injective]
  · rw [← div_vle_one_iff hb, ← div_vle_one_iff ((map_ne_zero _).2 hb), ← map_div₀,
      RingHom.algebraMap_toAlgebra]
    exact padicToField_vle_one_iff K p hp (a / b)

/-- **A nonarchimedean local field of characteristic zero is a `p`-adic field** (LMFDB
`lf.padic_field`): for a prime `p` in the maximal ideal of `𝒪_K` (the residue characteristic,
`IsNonarchimedeanLocalField.natCast_ringChar_mem_maximalIdeal`), the map
`IsNonarchimedeanLocalField.padicToField` makes `K` a finite extension of `ℚ_p` whose valuation
extends the `p`-adic one. -/
@[instance_reducible]
noncomputable def finitePadicExtension : FinitePadicExtension K p :=
  letI : Algebra ℚ_[p] K := (padicToField K p hp).toAlgebra
  haveI : ValuativeExtension ℚ_[p] K := valuativeExtension_padicToField K p hp
  haveI : Module.Finite ℚ_[p] K := finite_of_valuativeExtension ℚ_[p] K
  FinitePadicExtension.ofInstances K p

/-- **Nonarchimedean local fields of characteristic zero are `p`-adic fields** (LMFDB
`lf.padic_field`): a nonarchimedean local field of characteristic zero is a finite extension of
`ℚ_p`, compatibly with the valuations, for `p` its residue characteristic. -/
lemma nonempty_finitePadicExtension_ringChar :
    haveI : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩
    Nonempty (FinitePadicExtension K (ringChar 𝓀[K])) :=
  have : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩
  ⟨finitePadicExtension K (ringChar 𝓀[K]) (natCast_ringChar_mem_maximalIdeal K)⟩

end IsNonarchimedeanLocalField
