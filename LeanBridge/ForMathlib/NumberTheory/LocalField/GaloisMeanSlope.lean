import LeanBridge.ForMathlib.NumberTheory.LocalField.SlopeContentDegree
import TauCeti.NumberTheory.LocalField.Different.Hilbert
import TauCeti.NumberTheory.LocalField.Discriminant.Basic

/-!
# The Galois mean slope as a weighted average

Let `L / K` be a finite Galois extension of nonarchimedean local fields, of degree `n`, with
ramification index `e`, lower ramification groups `G_j` of orders `g_j` and Herbrand function `φ`.
The **Galois mean slope** (LMFDB `lf.galois_mean_slope`, for `K = ℚ_p`) is the rational number
`α = δ / n` with `δ` the discriminant exponent, so that the discriminant ideal is `𝓂_K ^ (n α)`.

Since `δ = f d` with `d = ∑_{j ≥ 0} (g_j - 1)` the different exponent (Hilbert's formula, Tau Ceti),
`α = d / e`, and an Abel summation with `φ(j) - φ(j - 1) = g_j / g_0` gives
`α = ∑_{j = 1}^{T} (1 / g_{j + 1} - 1 / g_j) (1 + φ(j)) + (1 / g_1 - 1 / g_0)`,
for `T` the largest lower jump. The `1 + φ(j)` are the wild Artin slopes, with multiplicity
`log_p (g_j / g_{j + 1})`, and `1 / g_1 - 1 / g_0 = p ^ (-k) (t - 1) / t` for the tame degree `t`
and the number `k` of wild slopes. The weights `1 / g_{j + 1} - 1 / g_j` and `1 / g_1 = p ^ (-k)`
are nonnegative and sum to `1`, so `α` is a weighted average of the wild Artin slopes and of
`(t - 1) / t`.

## Main definitions

* `IsNonarchimedeanLocalField.galoisMeanSlope` (LMFDB `lf.galois_mean_slope`): `δ / n`.

## Main theorems

* `IsNonarchimedeanLocalField.galoisMeanSlope_eq` (LMFDB `lf.galois_mean_slope`): the weighted
  average formula.
* `IsNonarchimedeanLocalField.one_div_sub_one_div_nonneg` and
  `IsNonarchimedeanLocalField.sum_one_div_sub_one_div_add_one_div` (LMFDB `lf.galois_mean_slope`):
  its weights are nonnegative and sum to `1`.
* `IsNonarchimedeanLocalField.one_div_sub_one_div_eq_tameDegree` (LMFDB `lf.galois_mean_slope`):
  its tame term is `p ^ (-k) (t - 1) / t`.
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

variable [IsGalois K L] in
/-- The **Galois mean slope** (LMFDB `lf.galois_mean_slope`) of a finite Galois extension `L / K`
of nonarchimedean local fields: `δ / [L : K]`, for `δ` the discriminant exponent, so that the
discriminant ideal of `L / K` is `𝓂_K ^ ([L : K] α)` (`(p ^ ([L : K] α))` for `K = ℚ_p`). -/
noncomputable def galoisMeanSlope : ℚ :=
  (discriminantExponent K L : ℚ) / Module.finrank K L

variable [IsGalois K L] in
lemma galoisMeanSlope_nonneg : 0 ≤ galoisMeanSlope K L :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

variable [Module.Finite K L]

/-- The order of the `j`-th lower ramification group, as a real number. -/
local notation "g" j => (Nat.card (lowerRamificationGroup K L (j : ℕ)) : ℝ)

lemma natCast_natCard_lowerRamificationGroup_ne_zero (j : ℤ) :
    (Nat.card (lowerRamificationGroup K L j) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.2 Nat.card_pos.ne'

lemma lowerRamificationGroup_largestLowerJump_toNat_add_one :
    lowerRamificationGroup K L ((largestLowerJump K L).toNat + 1 : ℕ) = ⊥ :=
  lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (by omega)

/-- **The weights of the Galois mean slope are nonnegative** (LMFDB `lf.galois_mean_slope`): with
`g_j` the order of the `j`-th lower ramification group, `1 / g_{j + 1} - 1 / g_j ≥ 0`. -/
lemma one_div_sub_one_div_nonneg (j : ℕ) : 0 ≤ 1 / (g (j + 1)) - 1 / (g j) := by
  have hle :
      Nat.card (lowerRamificationGroup K L (j + 1 : ℕ)) ≤ Nat.card (lowerRamificationGroup K L j) :=
    Subgroup.card_le_of_le (lowerRamificationGroup_antitone K L (by omega))
  exact sub_nonneg.2 (one_div_le_one_div_of_le (mod_cast Nat.card_pos) (mod_cast hle))

/-- **The weights of the Galois mean slope sum to `1`** (LMFDB `lf.galois_mean_slope`): with `g_j`
the order of the `j`-th lower ramification group and `T` the largest lower jump, the weights
`1 / g_{j + 1} - 1 / g_j` of the wild Artin slopes `1 + φ(j)`, `1 ≤ j ≤ T`, and the weight
`1 / g_1` of the tame term sum to `1`. -/
lemma sum_one_div_sub_one_div_add_one_div :
    ∑ i ∈ range (largestLowerJump K L).toNat, (1 / (g (i + 2)) - 1 / (g (i + 1))) +
      1 / (g 1) = 1 := by
  have hs : ∑ i ∈ range (largestLowerJump K L).toNat, (1 / (g (i + 2)) - 1 / (g (i + 1))) =
      1 / (g ((largestLowerJump K L).toNat + 1)) - 1 / (g 1) :=
    sum_range_sub (fun i ↦ 1 / (g (i + 1))) _
  rw [hs, lowerRamificationGroup_largestLowerJump_toNat_add_one, Subgroup.card_bot, Nat.cast_one,
    div_one, sub_add_cancel]

variable [IsGalois K L]

lemma finrank_mul_galoisMeanSlope :
    (Module.finrank K L : ℚ) * galoisMeanSlope K L = discriminantExponent K L :=
  mul_div_cancel₀ _ (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

lemma abel_sum (N : ℕ) : ∑ i ∈ range N, (1 / (g (i + 2)) - 1 / (g (i + 1))) *
    (1 + herbrand K L ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩) =
      (1 + herbrand K L ⟨(N : ℕ), Nat.cast_mem_ramificationIndexDomain N⟩) / (g (N + 1)) -
        1 / (g 1) - N / (g 0) := by
  induction N with
  | zero =>
    rw [herbrand_of_coe_le_zero K L (by simp)]
    simp
  | succ N ih =>
    rw [sum_range_succ, ih, coe_herbrand_of_coe_eq_natCast K L (N + 1)
      (u := ⟨((N + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (N + 1)⟩) rfl,
      coe_herbrand_of_coe_eq_natCast K L N
      (u := ⟨(N : ℝ), Nat.cast_mem_ramificationIndexDomain N⟩) rfl, sum_Icc_succ_top (by omega)]
    have h₀ : (g 0) ≠ 0 := natCast_natCard_lowerRamificationGroup_ne_zero K L _
    have h₁ : (g (N + 1)) ≠ 0 := natCast_natCard_lowerRamificationGroup_ne_zero K L _
    have h₂ : (g (N + 2)) ≠ 0 := natCast_natCard_lowerRamificationGroup_ne_zero K L _
    have h₁₂ : (N : ℤ) + 1 + 1 = N + 2 := by
      ring1
    push_cast at h₀ h₁ h₂ ⊢
    rw [h₁₂]
    field_simp
    ring1

lemma sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (T : ℕ) :
    ∑ i ∈ Icc 1 T, f i = ∑ i ∈ range T, f (i + 1) := by
  induction T with
  | zero => rfl
  | succ T ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- **The Galois mean slope as a weighted average** (LMFDB `lf.galois_mean_slope`): with `g_j` the
order of the `j`-th lower ramification group, `T` the largest lower jump and `φ` the Herbrand
function, `α = ∑_{j = 1}^{T} (1 / g_{j + 1} - 1 / g_j) (1 + φ(j)) + (1 / g_1 - 1 / g_0)`. The
`1 + φ(j)` are the wild Artin slopes (`IsNonarchimedeanLocalField.wildArtinSlopesOfIsGalois`, with
multiplicity `log_p (g_j / g_{j + 1})`), and `1 / g_1 - 1 / g_0 = p ^ (-k) (t - 1) / t` for the
tame degree `t` and the number `k` of wild slopes, with `1 / g_1 = p ^ (-k)`. The weights
`1 / g_{j + 1} - 1 / g_j` and `1 / g_1` are nonnegative with sum `1`, so `α` is a weighted average
of the wild Artin slopes and of `(t - 1) / t`. -/
lemma galoisMeanSlope_eq : (galoisMeanSlope K L : ℝ) =
    ∑ i ∈ range (largestLowerJump K L).toNat, (1 / (g (i + 2)) - 1 / (g (i + 1))) *
      (1 + herbrand K L ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩) +
        (1 / (g 1) - 1 / (g 0)) := by
  have hsupp : Function.support
      (fun i : ℕ ↦ Nat.card (lowerRamificationGroup K L i) - 1) ⊆
        ↑(range ((largestLowerJump K L).toNat + 1)) := by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [coe_range, Set.mem_Iio]
    by_contra h
    exact hi (by rw [lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (by omega),
      Subgroup.card_bot, Nat.sub_self])
  have hd : differentExponent K L = ∑ i ∈ range ((largestLowerJump K L).toNat + 1),
      (Nat.card (lowerRamificationGroup K L i) - 1) := by
    rw [differentExponent_eq_finsum_lowerRamificationGroup, finsum_eq_sum_of_support_subset _ hsupp]
  have hf : (inertiaDegree K L : ℝ) ≠ 0 := by
    exact_mod_cast (inertiaDegree_pos (K := K) (L := L)).ne'
  have h₀ : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 :=
    natCast_natCard_lowerRamificationGroup_ne_zero K L 0
  rw [abel_sum, galoisMeanSlope, discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    ← ramificationIndex_mul_inertiaDegree, hd, coe_herbrand_of_coe_eq_natCast K L _
    (u := ⟨((largestLowerJump K L).toNat : ℝ), Nat.cast_mem_ramificationIndexDomain _⟩) rfl,
    lowerRamificationGroup_largestLowerJump_toNat_add_one,
    Subgroup.card_bot, sum_range_succ', sum_Icc_one_eq_sum_range,
    ← natCard_lowerRamificationGroup_zero K L]
  have hcast (j : ℤ) : ((Nat.card (lowerRamificationGroup K L j) - 1 : ℕ) : ℝ) =
      (Nat.card (lowerRamificationGroup K L j) : ℝ) - 1 := by
    rw [Nat.cast_sub Nat.card_pos, Nat.cast_one]
  push_cast
  simp only [hcast]
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  field_simp
  ring1

/-- **The tame term of the Galois mean slope** (LMFDB `lf.galois_mean_slope`): the last term of
`IsNonarchimedeanLocalField.galoisMeanSlope_eq` is `p ^ (-k) (t - 1) / t`, for the tame degree `t`
and the number `k` of wild Artin slopes. -/
lemma one_div_sub_one_div_eq_tameDegree : 1 / (g 1) - 1 / (g 0) = ((tameDegree K L : ℝ) - 1) /
    (tameDegree K L * ringChar 𝓀[K] ^ Multiset.card (wildArtinSlopesOfIsGalois K L)) := by
  have hp : 0 < ringChar 𝓀[K] := (CharP.prime_ringChar 𝓀[K]).pos
  have ht : (tameDegree K L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ordCompl_pos _ ramificationIndex_pos.ne').ne'
  have he : (ramificationIndex K L : ℝ) =
      ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K]) * tameDegree K L := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
  rw [card_wildArtinSlopesOfIsGalois, Nat.cast_one, Nat.cast_zero,
    natCard_lowerRamificationGroup_one, natCard_lowerRamificationGroup_zero, he]
  push_cast
  field_simp

end IsNonarchimedeanLocalField
