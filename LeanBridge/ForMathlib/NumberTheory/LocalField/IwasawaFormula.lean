import LeanBridge.ForMathlib.NumberTheory.LocalField.IwasawaLogarithm
import LeanBridge.ForMathlib.NumberTheory.LocalField.PadicField
import TauCeti.NumberTheory.LocalField.Logarithm
import TauCeti.Topology.Algebra.ValuativeRel.HasSum

/-!
# The `p`-adic logarithm is a homomorphism on all principal units

Let `K` be a finite extension of `ℚ_p` with absolute ramification index `e`. The logarithm series
`log (1 + z) = ∑_{n ≥ 1} (-1) ^ (n + 1) z ^ n / n` (Mathlib's `NormedSpace.log`) converges on the
principal units `U(K, 1) = 1 + 𝔪` (Tau Ceti's `TauCeti.hasSum_log_of_mem_unitFiltration_one`). Tau
Ceti proves `log (u w) = log u + log w` only on the deep units `U(K, i)` with `e < (p - 1) i`,
through the exponential. We prove it on all of `U(K, 1)` with Iwasawa's formula
`log u = lim_{k → ∞} (u ^ p ^ k - 1) / p ^ k`, as the TODO list of `NormedSpace.log` suggests.
Binomially, `(u ^ N - 1) / N = ∑_{j ≥ 1} C(N - 1, j - 1) (u - 1) ^ j / j` for `N = p ^ k`. As
`k → ∞`, `C(p ^ k - 1, j - 1) = (-1) ^ (j - 1) ∏_{i = 1}^{j - 1} (1 - p ^ k / i)` tends `p`-adically
to `(-1) ^ (j - 1)`, while every term stays bounded by the corresponding term of the logarithm
series, so the sums tend to `log u`. Then
`(u w) ^ N - 1 = (u ^ N - 1) + (w ^ N - 1) + (u ^ N - 1) (w ^ N - 1)` and `p ^ k → 0` give
`log (u w) = log u + log w`.

Hence LeanBridge's Iwasawa logarithm `IsNonarchimedeanLocalField.iwasawaLog` (LMFDB `lf.log`),
defined as the homomorphism `Kˣ → K` with `log_p p = 0` that agrees with the series on deep units,
agrees with the series on all of `1 + 𝔪`, also when `e ≥ p - 1` (already for `ℚ_2`); and it is the
only homomorphism `Kˣ → K` that does and vanishes at `p`.

## Main results

* `IsNonarchimedeanLocalField.tendsto_pow_sub_one_div`: Iwasawa's formula
  `log u = lim_{k → ∞} (u ^ p ^ k - 1) / p ^ k` on `U(K, 1)`.
* `IsNonarchimedeanLocalField.log_mul_of_mem_unitFiltration_one` (LMFDB `lf.log`): the logarithm
  series is a homomorphism on `U(K, 1) = 1 + 𝔪`.
* `IsNonarchimedeanLocalField.iwasawaLog_of_mem_unitFiltration_one` (LMFDB `lf.log`): the Iwasawa
  logarithm is the logarithm series on `U(K, 1) = 1 + 𝔪`.
* `IsNonarchimedeanLocalField.eq_iwasawaLog` (LMFDB `lf.log`): the Iwasawa logarithm is the only
  homomorphism `Kˣ → K` that extends the logarithm series on `1 + 𝔪` and vanishes at `p`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 5, §1, for the `p`-adic
  logarithm and its extension with `log_p p = 0`.
-/

open Filter Finset Topology ValuativeRel NormedSpace TauCeti

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] {u w : Kˣ} (p n m : ℕ)

variable [CharZero K] in
private lemma natCast_choose_succ :
    (n.choose (m + 1) : K) = n.choose m * (((n + 1 : ℕ) : K) / (m + 1) - 1) := by
  rcases le_or_gt m n with h | h
  · have h' : (n.choose (m + 1) : K) * (m + 1) = n.choose m * ((n : K) - m) := by
      rw [← Nat.cast_sub h]
      exact_mod_cast Nat.choose_succ_right_eq n m
    field_simp
    push_cast
    linear_combination h'
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

variable [TopologicalSpace K]

variable [CharZero K] in
private lemma hasSum_choose (z : K) :
    HasSum (fun j : ℕ ↦ (n.choose (j - 1) : K) * (-1) ^ (j + 1) * ((-1) ^ (j + 1) / j * z ^ j))
      (((z + 1) ^ (n + 1) - 1) / (n + 1 : ℕ)) := by
  have h0 (j : ℕ) (hj : j ∉ range (n + 2)) :
      (n.choose (j - 1) : K) * (-1) ^ (j + 1) * ((-1) ^ (j + 1) / j * z ^ j) = 0 := by
    rw [mem_range] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]
  convert (hasSum_sum_of_ne_finset_zero h0 : HasSum _ _) using 1
  rw [sum_range_succ', Nat.cast_zero, div_zero, zero_mul, mul_zero, add_zero,
    div_eq_iff (Nat.cast_ne_zero.mpr n.succ_ne_zero), add_pow, sum_range_succ', sum_mul]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine sum_congr rfl fun i _ ↦ ?_
  have h : ((n : K) + 1) * n.choose i = (n + 1).choose (i + 1) * ((i : K) + 1) :=
    mod_cast Nat.add_one_mul_choose_eq n i
  field_simp
  rw [← pow_mul, pow_mul', neg_one_sq, one_pow, Nat.add_sub_cancel]
  push_cast
  linear_combination -z ^ (i + 1) * h

variable [ValuativeRel K] [IsNonarchimedeanLocalField K]

lemma tendsto_of_hasSum_of_valuation_le {f : ℕ → ℕ → K} {g : ℕ → K} {S : ℕ → K} {s : K}
    (hf : ∀ k, HasSum (f k) (S k)) (hg : HasSum g s) (hlim : ∀ j, Tendsto (f · j) atTop (𝓝 (g j)))
    (hle : ∀ k j, valuation K (f k j) ≤ valuation K (g j)) : Tendsto S atTop (𝓝 s) := by
  refine (IsValuativeTopology.hasBasis_nhds s).tendsto_right_iff.mpr fun γ _ ↦ ?_
  rcases eventually_atTop.mp <| (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff.mp
    hg.summable.tendsto_atTop_zero γ trivial with ⟨J, hJ⟩
  filter_upwards [(eventually_all_finset (range J)).mpr fun j _ ↦
    (IsValuativeTopology.hasBasis_nhds (g j)).tendsto_right_iff.mp (hlim j) γ trivial] with k hk
  refine valuation_lt_of_hasSum ((hf k).sub hg) γ fun j ↦ ?_
  rcases lt_or_ge j J with hj | hj
  · exact hk j (mem_range.mpr hj)
  · exact (Valuation.map_sub _ _ _).trans_lt (max_lt ((hle k j).trans_lt (hJ j hj)) (hJ j hj))

variable [Fact p.Prime] [FinitePadicExtension K p]

lemma valuation_natCast_prime_lt_one : valuation K (p : K) < 1 := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
  rw [valuation_natCast_eq_pow_mul_padicValNat p hπ (Fact.out : p.Prime).ne_zero, padicValNat_self,
    mul_one]
  exact pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hπ)
    (absoluteRamificationIndex_pos K p).ne'

lemma tendsto_natCast_prime_pow : Tendsto (fun k : ℕ ↦ (p : K) ^ k) atTop (𝓝 0) := by
  refine (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff.mpr fun γ _ ↦ ?_
  rcases exists_pow_lt₀ (valuation_natCast_prime_lt_one p) γ with ⟨M, hM⟩
  filter_upwards [eventually_ge_atTop M] with k hk
  rw [map_pow]
  exact (pow_le_pow_right_of_le_one' (valuation_natCast_prime_lt_one p).le hk).trans_lt hM

private lemma tendsto_natCast_choose :
    Tendsto (fun k : ℕ ↦ ((p ^ k - 1).choose m : K)) atTop (𝓝 ((-1) ^ m)) := by
  have : CharZero K := FinitePadicExtension.charZero K p
  induction m with
  | zero => simp
  | succ m ih =>
    have h (k : ℕ) : ((p ^ k - 1 + 1 : ℕ) : K) = (p : K) ^ k := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos), Nat.cast_pow]
    simp_rw [natCast_choose_succ, h]
    simpa [pow_succ] using ih.mul (((tendsto_natCast_prime_pow p).div_const _).sub_const 1)

/-- **Iwasawa's formula**: on a finite extension `K` of `ℚ_p`, every principal unit
`u ∈ U(K, 1) = 1 + 𝔪` satisfies `log u = lim_{k → ∞} (u ^ p ^ k - 1) / p ^ k`, where `log` is the
logarithm series `∑_{n ≥ 1} (-1) ^ (n + 1) (u - 1) ^ n / n`. -/
lemma tendsto_pow_sub_one_div (hu : u ∈ unitFiltration K 1) :
    Tendsto (fun k : ℕ ↦ ((u : K) ^ p ^ k - 1) / (p : K) ^ k) atTop (𝓝 (log (u : K))) := by
  have : CharZero K := FinitePadicExtension.charZero K p
  refine tendsto_of_hasSum_of_valuation_le (f := fun k j ↦ ((p ^ k - 1).choose (j - 1) : K) *
    (-1) ^ (j + 1) * ((-1) ^ (j + 1) / j * ((u : K) - 1) ^ j)) (fun k ↦ ?_)
    (hasSum_log_of_mem_unitFiltration_one p hu) (fun j ↦ ?_) fun k j ↦ ?_
  · convert hasSum_choose (p ^ k - 1) ((u : K) - 1) using 1
    rw [sub_add_cancel, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos),
      Nat.cast_pow]
  · rcases eq_or_ne j 0 with rfl | hj
    · simp
    · have h :
          Tendsto (fun k : ℕ ↦ ((p ^ k - 1).choose (j - 1) : K) * (-1) ^ (j + 1)) atTop (𝓝 1) := by
        convert (tendsto_natCast_choose p (j - 1)).mul_const ((-1 : K) ^ (j + 1)) using 2
        rw [← pow_add, show j - 1 + (j + 1) = 2 * j by omega, pow_mul, neg_one_sq, one_pow]
      simpa using h.mul_const ((-1) ^ (j + 1) / j * ((u : K) - 1) ^ j)
  · rw [map_mul, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, mul_one]
    exact mul_le_of_le_one_left zero_le ((Valuation.mem_integer_iff _ _).mp (natCast_mem _ _))

lemma tendsto_mul_pow_sub_one_div (hu : u ∈ unitFiltration K 1) (hw : w ∈ unitFiltration K 1) :
    Tendsto (fun k : ℕ ↦ (((u * w : Kˣ) : K) ^ p ^ k - 1) / (p : K) ^ k) atTop
      (𝓝 (log (u : K) + log (w : K))) := by
  have : CharZero K := FinitePadicExtension.charZero K p
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  convert ((tendsto_pow_sub_one_div p hu).add (tendsto_pow_sub_one_div p hw)).add
    ((tendsto_pow_sub_one_div p hu).mul ((tendsto_natCast_prime_pow p).mul
      (tendsto_pow_sub_one_div p hw))) using 2
  · rw [Units.val_mul]
    field_simp
    ring1
  · rw [zero_mul, mul_zero, add_zero]

variable [CharZero K] in
/-- **The logarithm series is a homomorphism on the principal units** (LMFDB `lf.log`): on a
nonarchimedean local field `K` of characteristic zero, that is a finite extension of `ℚ_p`,
`log (u w) = log u + log w` for all `u, w ∈ U(K, 1) = 1 + 𝔪`, where `log` is the logarithm series
`∑_{n ≥ 1} (-1) ^ (n + 1) (u - 1) ^ n / n`. Tau Ceti's `TauCeti.log_mul_of_mem_unitFiltration`
needs `u, w ∈ U(K, i)` with `e < (p - 1) i`. -/
lemma log_mul_of_mem_unitFiltration_one (hu : u ∈ unitFiltration K 1)
    (hw : w ∈ unitFiltration K 1) : log ((u : K) * w) = log (u : K) + log (w : K) := by
  have : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩
  let _ : FinitePadicExtension K (ringChar 𝓀[K]) :=
    finitePadicExtension K _ (natCast_ringChar_mem_maximalIdeal K)
  exact tendsto_nhds_unique (tendsto_pow_sub_one_div (ringChar 𝓀[K]) (mul_mem hu hw))
    (tendsto_mul_pow_sub_one_div (ringChar 𝓀[K]) hu hw)

variable [CharZero K] in
lemma log_pow_of_mem_unitFiltration_one (hu : u ∈ unitFiltration K 1) :
    log ((u ^ n : Kˣ) : K) = n * log (u : K) := by
  induction n with
  | zero => rw [pow_zero, Units.val_one, log_one, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, log_mul_of_mem_unitFiltration_one (pow_mem hu n) hu, ih,
      Nat.cast_succ, add_one_mul]

/-- **The Iwasawa logarithm is the logarithm series on the principal units** (LMFDB `lf.log`): on
a finite extension `K` of `ℚ_p`, `log_p u = ∑_{n ≥ 1} (-1) ^ (n + 1) (u - 1) ^ n / n` for every
`u ∈ U(K, 1) = 1 + 𝔪`, whatever the absolute ramification index `e`; LeanBridge's
`IsNonarchimedeanLocalField.iwasawaLog_of_mem_unitFiltration` needs `e < p - 1` for this. -/
lemma iwasawaLog_of_mem_unitFiltration_one (hu : u ∈ unitFiltration K 1) :
    iwasawaLog p u = log (u : K) := by
  have : CharZero K := FinitePadicExtension.charZero K p
  rw [iwasawaLog_eq p (unitFiltration_antitone (Nat.zero_le 1) (pow_mem hu _)) (k := 0)
    (by rw [zpow_zero, mul_one]), log_pow_of_mem_unitFiltration_one _ hu,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (iwasawaLogExponent_ne_zero p))]

/-- **The Iwasawa logarithm is the only extension of the logarithm series** (LMFDB `lf.log`): on a
finite extension `K` of `ℚ_p`, a homomorphism `f : Kˣ → K` that agrees with the logarithm series
on `U(K, 1) = 1 + 𝔪` and vanishes at `p` is the Iwasawa logarithm `log_p`. Such an `f` also
vanishes at the roots of unity, as `K` has characteristic zero. -/
lemma eq_iwasawaLog {f : Kˣ → K} (hf : ∀ u v, f (u * v) = f u + f v) (hp : f (primeUnit p) = 0)
    (hlog : ∀ u ∈ unitFiltration K 1, f u = log (u : K)) : f = iwasawaLog p := by
  have : CharZero K := FinitePadicExtension.charZero K p
  let F : Kˣ →* Multiplicative K := MonoidHom.mk' (fun v ↦ .ofAdd (f v)) fun v v' ↦ by
    rw [hf, ofAdd_add]
  refine funext fun u ↦ ?_
  rcases exists_pow_iwasawaLogExponent p u with ⟨k, hk⟩
  have h : (F (u ^ iwasawaLogExponent (K := K) p)).toAdd =
      (F (iwasawaLogUnit p u * primeUnit p ^ k)).toAdd :=
    congrArg (fun v ↦ (F v).toAdd) hk
  simp only [map_mul, map_pow, map_zpow] at h
  rw [iwasawaLog, eq_div_iff (Nat.cast_ne_zero.mpr (iwasawaLogExponent_ne_zero p)), mul_comm,
    ← hlog _ (unitFiltration_antitone (Nat.le_add_left 1 _) (iwasawaLogUnit_mem p u))]
  simpa [F, hp] using h

end IsNonarchimedeanLocalField
