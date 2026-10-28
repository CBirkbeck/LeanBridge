import TauCeti.NumberTheory.LocalField.DeepUnits.Basic
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# The `p`-adic (Iwasawa) logarithm on a finite extension of `ℚ_p`

Let `K` be a finite extension of `ℚ_p` with absolute ramification index `e`. The `p`-adic logarithm
is the series `log (1 + z) = ∑_{n ≥ 1} (-1) ^ (n + 1) z ^ n / n` (Mathlib's `NormedSpace.log`,
whose convergence on `U(K, 1)` is `TauCeti.hasSum_log_of_mem_unitFiltration_one`), extended to `Kˣ`
by `log_p p = 0` and `log_p ζ = 0` for roots of unity `ζ`.

We define the extension through Tau Ceti's `exists_forall_pow_eq_mem_unitFiltration_mul_zpow`:
there is `M ≠ 0` such that every `u : Kˣ` satisfies `u ^ M = w * p ^ k` for a deep unit `w`, on
which the logarithm is a homomorphism; then `log_p u = log w / M`.

## Main definitions

* `IsNonarchimedeanLocalField.primeUnit`: `p` as a unit of `K`.
* `IsNonarchimedeanLocalField.iwasawaLogExponent`, `IsNonarchimedeanLocalField.iwasawaLogUnit`: the
  exponent `M` and the deep unit `w`.
* `IsNonarchimedeanLocalField.iwasawaLog` (LMFDB `lf.log`).

## Main theorems

* `IsNonarchimedeanLocalField.iwasawaLog_mul`: `log_p` is a homomorphism `Kˣ → K`.
* `IsNonarchimedeanLocalField.iwasawaLog_primeUnit`: `log_p p = 0`.
* `IsNonarchimedeanLocalField.iwasawaLog_eq_zero_of_pow_eq_one`: `log_p ζ = 0` for roots of unity.
* `IsNonarchimedeanLocalField.iwasawaLog_of_mem_unitFiltration`: `log_p` is the logarithm series on
  the deep units `U(K, i)` with `e < (p - 1) i`, in particular on `U(K, 1) = 1 + 𝔪` when
  `e < p - 1`.
* `IsNonarchimedeanLocalField.iwasawaLog_eq_of_pow_eq`: `log_p u = log w / M` for any
  `u ^ M = w * p ^ k` with `w` a deep unit, so `log_p` does not depend on the choices made.

The image statement `log_p (1 + 𝔪) = 𝔪` for `e < p - 1` is Tau Ceti's
`TauCeti.deepUnitExpLogEquiv` at depth `1`.
-/

open ValuativeRel NormedSpace TauCeti

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]

/-- The prime `p` as a unit of a finite extension `K` of `ℚ_p`. -/
noncomputable def primeUnit : Kˣ :=
  Units.mk0 (p : K) (NeZero.ne _)

lemma normalizedValuation_primeUnit_ne_one : normalizedValuation K (primeUnit p) ≠ 1 := by
  rw [primeUnit, normalizedValuation_natCast, Ne, ← ofAdd_zero,
    Multiplicative.ofAdd.injective.eq_iff,
    natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat K p p (NeZero.ne p),
    padicValNat_self, mul_one, Nat.cast_eq_zero]
  exact (absoluteRamificationIndex_pos K p).ne'

lemma exists_iwasawaLogExponent : ∃ M : ℕ, M ≠ 0 ∧ ∀ u : Kˣ, ∃ w ∈ unitFiltration K
    (absoluteRamificationIndex K p + 1), ∃ k : ℤ, u ^ M = w * primeUnit p ^ k :=
  exists_forall_pow_eq_mem_unitFiltration_mul_zpow _ <| normalizedValuation_primeUnit_ne_one p

lemma absoluteRamificationIndex_lt :
    absoluteRamificationIndex K p < (p - 1) * (absoluteRamificationIndex K p + 1) := by
  have h : 1 ≤ p - 1 := Nat.le_sub_one_of_lt (Fact.out : p.Prime).one_lt
  nlinarith

/-- The exponent `M ≠ 0` used to define the Iwasawa logarithm: `u ^ M` is a deep unit times a power
of `p` for every `u : Kˣ`. -/
noncomputable def iwasawaLogExponent : ℕ :=
  (exists_iwasawaLogExponent (K := K) p).choose

/-- The deep unit `w` with `u ^ M = w * p ^ k`, for the exponent `M = iwasawaLogExponent p`. -/
noncomputable def iwasawaLogUnit (u : Kˣ) : Kˣ :=
  ((exists_iwasawaLogExponent (K := K) p).choose_spec.2 u).choose

/-- The **`p`-adic logarithm** (LMFDB `lf.log`) on a finite extension `K` of `ℚ_p`, extended to `Kˣ`
by `log_p p = 0` and `log_p ζ = 0` for roots of unity (Iwasawa's normalisation): `log w / M`, where
`u ^ M = w * p ^ k` with `w` a deep unit, on which the series
`log w = ∑ (-1) ^ (n + 1) (w - 1) ^ n / n` converges and is a homomorphism. The value does not
depend on the choices (`iwasawaLog_eq_of_pow_eq`). The LMFDB knowl writes the series with
`(-1) ^ n`, a sign error. -/
noncomputable def iwasawaLog (u : Kˣ) : K :=
  log (iwasawaLogUnit p u : K) / iwasawaLogExponent (K := K) p

lemma iwasawaLogExponent_ne_zero : iwasawaLogExponent (K := K) p ≠ 0 :=
  (exists_iwasawaLogExponent (K := K) p).choose_spec.1

lemma iwasawaLogUnit_mem (u : Kˣ) :
    iwasawaLogUnit p u ∈ unitFiltration K (absoluteRamificationIndex K p + 1) :=
  ((exists_iwasawaLogExponent (K := K) p).choose_spec.2 u).choose_spec.1

lemma exists_pow_iwasawaLogExponent (u : Kˣ) :
    ∃ k : ℤ, u ^ iwasawaLogExponent (K := K) p = iwasawaLogUnit p u * primeUnit p ^ k :=
  ((exists_iwasawaLogExponent (K := K) p).choose_spec.2 u).choose_spec.2

lemma eq_of_mul_zpow_eq {w w' : Kˣ} (hw : w ∈ unitFiltration K 0) (hw' : w' ∈ unitFiltration K 0)
    {k k' : ℤ} (h : w * primeUnit p ^ k = w' * primeUnit p ^ k') : w = w' := by
  have hv : Multiplicative.toAdd (normalizedValuation K (w * primeUnit p ^ k)) =
      Multiplicative.toAdd (normalizedValuation K (w' * primeUnit p ^ k')) := by
    rw [h]
  rw [← ker_normalizedValuation] at hw hw'
  simp only [map_mul, map_zpow, MonoidHom.mem_ker.mp hw, MonoidHom.mem_ker.mp hw', one_mul,
    toAdd_zpow, smul_eq_mul] at hv
  have hc : Multiplicative.toAdd (normalizedValuation K (primeUnit p)) ≠ 0 :=
    normalizedValuation_primeUnit_ne_one p
  rw [mul_right_cancel₀ hc hv] at h
  exact mul_right_cancel h

lemma iwasawaLog_eq {u w : Kˣ} (hw : w ∈ unitFiltration K 0) {k : ℤ}
    (h : u ^ iwasawaLogExponent (K := K) p = w * primeUnit p ^ k) :
    iwasawaLog p u = log (w : K) / iwasawaLogExponent (K := K) p := by
  rcases exists_pow_iwasawaLogExponent p u with ⟨k', hk'⟩
  rw [iwasawaLog, eq_of_mul_zpow_eq p (unitFiltration_antitone (Nat.zero_le _)
    (iwasawaLogUnit_mem p u)) hw (hk'.symm.trans h)]

/-- The Iwasawa logarithm is a homomorphism `Kˣ → K`. -/
lemma iwasawaLog_mul (u v : Kˣ) : iwasawaLog p (u * v) = iwasawaLog p u + iwasawaLog p v := by
  rcases exists_pow_iwasawaLogExponent p u with ⟨k, hk⟩
  rcases exists_pow_iwasawaLogExponent p v with ⟨k', hk'⟩
  have hu : iwasawaLogUnit p u ∈ unitFiltration K (absoluteRamificationIndex K p + 1) :=
    iwasawaLogUnit_mem p u
  have hv : iwasawaLogUnit p v ∈ unitFiltration K (absoluteRamificationIndex K p + 1) :=
    iwasawaLogUnit_mem p v
  rw [iwasawaLog_eq p (unitFiltration_antitone (Nat.zero_le _) (mul_mem hu hv))
    (k := k + k') (by rw [mul_pow, hk, hk', zpow_add, mul_mul_mul_comm]), Units.val_mul,
    log_mul_of_mem_unitFiltration (absoluteRamificationIndex_lt p) hu hv, add_div, iwasawaLog,
    iwasawaLog]

lemma iwasawaLog_one : iwasawaLog p (1 : Kˣ) = 0 := by
  rw [iwasawaLog_eq p (one_mem _) (k := 0) (by rw [one_pow, zpow_zero, one_mul]), Units.val_one,
    log_one, zero_div]

lemma iwasawaLog_pow (u : Kˣ) (n : ℕ) : iwasawaLog p (u ^ n) = n * iwasawaLog p u := by
  induction n with
  | zero => rw [pow_zero, iwasawaLog_one, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, iwasawaLog_mul, ih, Nat.cast_succ, add_one_mul]

lemma iwasawaLog_primeUnit_zpow (k : ℤ) : iwasawaLog p (primeUnit p ^ k : Kˣ) = 0 := by
  rw [iwasawaLog_eq p (one_mem _) (k := k * iwasawaLogExponent (K := K) p)
    (by rw [one_mul, zpow_mul, zpow_natCast]), Units.val_one, log_one, zero_div]

/-- **`log_p p = 0`**. -/
lemma iwasawaLog_primeUnit : iwasawaLog p (primeUnit p : Kˣ) = 0 := by
  rw [← zpow_one (primeUnit p), iwasawaLog_primeUnit_zpow]

/-- **`log_p ζ = 0` for a root of unity `ζ`**. -/
lemma iwasawaLog_eq_zero_of_pow_eq_one {ζ : Kˣ} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    iwasawaLog p ζ = 0 := by
  have : CharZero K := FinitePadicExtension.charZero K p
  have h : iwasawaLog p (ζ ^ n) = n * iwasawaLog p ζ := iwasawaLog_pow p ζ n
  rw [hζ, iwasawaLog_one] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Nat.cast_ne_zero.mpr hn)

lemma log_pow_of_mem_unitFiltration {i : ℕ} (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) (n : ℕ) : log ((u ^ n : Kˣ) : K) = n * log (u : K) := by
  induction n with
  | zero => rw [pow_zero, Units.val_one, log_one, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, log_mul_of_mem_unitFiltration hi (pow_mem hu n) hu, ih,
      Nat.cast_succ, add_one_mul]

/-- **The Iwasawa logarithm is the logarithm series on deep units**: on `U(K, i)` with
`e < (p - 1) i`, `log_p u = ∑ (-1) ^ (n + 1) (u - 1) ^ n / n`. -/
lemma iwasawaLog_of_mem_unitFiltration {i : ℕ} (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) : iwasawaLog p u = log (u : K) := by
  have : CharZero K := FinitePadicExtension.charZero K p
  rw [iwasawaLog_eq p (unitFiltration_antitone (Nat.zero_le _) (pow_mem hu _)) (k := 0)
    (by rw [zpow_zero, mul_one]), log_pow_of_mem_unitFiltration p hi hu,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (iwasawaLogExponent_ne_zero p))]

/-- **The Iwasawa logarithm does not depend on the choices made**: whenever `u ^ M = w * p ^ k`
with `M ≠ 0` and `w` a deep unit in `U(K, i)` with `e < (p - 1) i`, `log_p u = log w / M`. -/
lemma iwasawaLog_eq_of_pow_eq {i : ℕ} (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u w : Kˣ} (hw : w ∈ unitFiltration K i) {M : ℕ} (hM : M ≠ 0) {k : ℤ}
    (h : u ^ M = w * primeUnit p ^ k) : iwasawaLog p u = log (w : K) / M := by
  have : CharZero K := FinitePadicExtension.charZero K p
  have hu : (M : K) * iwasawaLog p u = log (w : K) := by
    rw [← iwasawaLog_pow, h, iwasawaLog_mul, iwasawaLog_primeUnit_zpow, add_zero,
      iwasawaLog_of_mem_unitFiltration p hi hw]
  rw [← hu, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hM)]

end IsNonarchimedeanLocalField
