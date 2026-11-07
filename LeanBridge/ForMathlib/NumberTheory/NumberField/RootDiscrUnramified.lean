import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.NumberTheory.NumberField.Discriminant.Ramification

/-!
# The root discriminant in an unramified extension

The root discriminant of a number field `K` of degree `n` and discriminant `D` is
`rd(K) = |D| ^ (1 / n)` (LMFDB `nf.root_discriminant`, Mathlib's `NumberField.rootDiscr`). The LMFDB
notes that it does not change in an unramified extension `L / K`. Indeed the relative discriminant
of `L / K` is then the unit ideal, since a prime dividing it is ramified in `L`
(`TauCeti.NumberField.dvd_relDiscr_iff_exists_one_lt_ramificationIdx`), so the tower formula for
discriminants (`TauCeti.relDiscr_tower`) gives `|d_L| = |d_K| ^ [L : K]`, while
`[L : ℚ] = [K : ℚ] [L : K]`. Only the finite primes matter: the statement holds as soon as every
maximal ideal of `𝓞 L` has ramification index `1` over `𝓞 K`, whatever happens at the infinite
places.

## Main results

* `NumberField.abs_discr_eq_pow_of_ramificationIdx_eq_one`: `|d_L| = |d_K| ^ [L : K]` when `L / K`
  is unramified at every finite prime.
* `NumberField.rootDiscr_eq_of_ramificationIdx_eq_one` (LMFDB `nf.root_discriminant`):
  `rd(K) = rd(L)` when `L / K` is unramified at every finite prime.
-/

open Module TauCeti

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

lemma relDiscr_eq_top_of_ramificationIdx_eq_one
    (h : ∀ P : Ideal (𝓞 L), P.IsMaximal → P.ramificationIdx (𝓞 K) = 1) :
    relDiscr (𝓞 K) (𝓞 L) = ⊤ := by
  by_contra hne
  rcases Ideal.exists_le_maximal _ hne with ⟨p, hp, hle⟩
  have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  rcases (NumberField.dvd_relDiscr_iff_exists_one_lt_ramificationIdx hp0).mp
    (Ideal.dvd_iff_le.mpr hle) with ⟨P, hP⟩
  exact hP.ne' <| h P <| P.2.1.isMaximal <| Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P.1

/-- **The discriminant in an extension unramified at every finite prime**: `|d_L| = |d_K| ^ [L : K]`
when every maximal ideal of `𝓞 L` has ramification index `1` over `𝓞 K`. -/
lemma abs_discr_eq_pow_of_ramificationIdx_eq_one
    (h : ∀ P : Ideal (𝓞 L), P.IsMaximal → P.ramificationIdx (𝓞 K) = 1) :
    |discr L| = |discr K| ^ finrank K L := by
  have htower : relDiscr ℤ (𝓞 L) =
      relDiscr ℤ (𝓞 K) ^ finrank (𝓞 K) (𝓞 L) * Ideal.relNorm ℤ (relDiscr (𝓞 K) (𝓞 L)) :=
    relDiscr_tower
  rw [relDiscr_eq_top_of_ramificationIdx_eq_one h, Ideal.relNorm_top, Ideal.mul_top,
    NumberField.relDiscr_int_ringOfIntegers, NumberField.relDiscr_int_ringOfIntegers,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at htower
  rw [← abs_pow, Int.abs_eq_natAbs, Int.abs_eq_natAbs, htower]

/-- **The root discriminant does not change in an unramified extension**
(LMFDB `nf.root_discriminant`): `rd(K) = rd(L)` when every maximal ideal of `𝓞 L` has ramification
index `1` over `𝓞 K`. -/
lemma rootDiscr_eq_of_ramificationIdx_eq_one
    (h : ∀ P : Ideal (𝓞 L), P.IsMaximal → P.ramificationIdx (𝓞 K) = 1) :
    rootDiscr K = rootDiscr L := by
  rw [rootDiscr_def, rootDiscr_def, abs_discr_eq_pow_of_ramificationIdx_eq_one h, Int.cast_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← finrank_mul_finrank ℚ K L]
  congr 1
  have hL : (finrank K L : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  push_cast
  field_simp

end NumberField
