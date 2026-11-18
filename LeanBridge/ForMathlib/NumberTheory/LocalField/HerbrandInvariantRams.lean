import LeanBridge.ForMathlib.NumberTheory.LocalField.HerbrandInvariantFamily
import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex

/-!
# Means, small and tiny rams and compatibility of Herbrand invariants

For a Herbrand invariant `I = (r_1, …, r_w)_ε^f` at a prime `p`, given as data
(`IsNonarchimedeanLocalField.HerbrandInvariant`), we define its means `m_k`, its small rams
`r_k^* = (p - 1) r_k / (ε p ^ k)` and tiny rams `r_k' = r_k / (ε p ^ k)`, the geometric and
arithmetic rams relative to an absolute ramification index `e_K`, compatibility of a `p`-adic field
with `I`, and the sets `𝓡_k^z` of LMFDB `lf.rams` as the knowl writes them. The sets of possible
rams, with the arithmetic ram `p z / (p - 1)` in `𝓡_1^z`, are
`IsNonarchimedeanLocalField.HerbrandInvariant.possibleRamSet`, in
`LeanBridge.ForMathlib.NumberTheory.LocalField.PossibleRamSet`.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.mean` (LMFDB `lf.herbrand_invariant`): the means.
* `IsNonarchimedeanLocalField.HerbrandInvariant.smallRam` (LMFDB `lf.rams`): the small rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.tinyRam` (LMFDB `lf.rams`): the tiny rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsGeometricRam` (LMFDB `lf.herbrand_invariant`).
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsArithmeticRam` (LMFDB `lf.herbrand_invariant`).
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsCompatible` (LMFDB `lf.herbrand_invariant`):
  compatibility with a ramification index `e_K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsCompatibleWith` (LMFDB `lf.herbrand_invariant`):
  compatibility with a `p`-adic field `K`, which depends only on `e_K` by definition.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ramSet` (LMFDB `lf.rams`): the sets `𝓡_k^z`, as
  the knowl writes them.

## Main theorems

* `IsNonarchimedeanLocalField.HerbrandInvariant.smallRam_eq_mean_sub_mean`: `r_k^* = m_k - m_{k-1}`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.tinyRam_eq_swanSlope_sub_mean`: `r_k' = s_k - m_k`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ram_lt_iff_le_ramCountLT` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.ram_le_iff_le_ramCountLT_add_ramMultiplicity`: the
  rams equal to a ram `b` are the `r_j` with `c < j ≤ c + d`, for the number `c` of rams smaller
  than `b` and the multiplicity `d` of `b`.
-/

open Finset

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p)

/-- The `k`-th **mean** `m_k` of a Herbrand invariant `I = (r_1, …, r_w)_ε^f` (LMFDB
`lf.herbrand_invariant`, `lf.means`): `m_k = ∑_{j = 1}^k (p - 1) r_j / (ε p ^ j)`, so `m_0 = 0`. -/
def mean (k : ℕ) : ℚ :=
  ∑ j ∈ Icc 1 k, (p - 1) * I.ram j / (I.ε * p ^ j)

/-- The `k`-th **small ram** `r_k^* = (p - 1) r_k / (ε p ^ k)` (LMFDB `lf.rams`). -/
def smallRam (k : ℕ) : ℚ :=
  (p - 1) * I.ram k / (I.ε * p ^ k)

/-- The `k`-th **tiny ram** `r_k' = r_k / (ε p ^ k)` (LMFDB `lf.rams`). -/
def tinyRam (k : ℕ) : ℚ :=
  I.ram k / (I.ε * p ^ k)

/-- **Small rams are differences of means**: `r_{k + 1}^* = m_{k + 1} - m_k`. -/
lemma smallRam_eq_mean_sub_mean (k : ℕ) : I.smallRam (k + 1) = I.mean (k + 1) - I.mean k := by
  rw [mean, mean, sum_Icc_succ_top <| Nat.le_add_left 1 k, add_sub_cancel_left, smallRam]

/-- **Tiny rams are Swan slopes minus means**: `r_k' = s_k - m_k`. -/
lemma tinyRam_eq_swanSlope_sub_mean (hp : p ≠ 0) (k : ℕ) :
    I.tinyRam k = I.swanSlope k - I.mean k := by
  have hε : (I.ε : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr I.ε_pos.ne'
  have hp' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  induction k with
  | zero => simp [tinyRam, swanSlope, mean, I.ram_zero]
  | succ k ih =>
    have hs : I.swanSlope (k + 1) = I.swanSlope k + (I.ram (k + 1) - I.ram k) / (I.ε * p ^ k) :=
      sum_range_succ _ _
    have hm : I.mean (k + 1) = I.mean k + I.smallRam (k + 1) :=
      sum_Icc_succ_top (Nat.le_add_left 1 k) _
    rw [hs, hm, sub_eq_iff_eq_add.mp ih.symm, tinyRam, tinyRam, smallRam]
    field_simp
    ring1

/-- The number of `j ∈ [1, w]` with `r_j = b`: the multiplicity of `b` as a ram. -/
def ramMultiplicity (b : ℚ) : ℕ :=
  #{j ∈ Icc 1 I.w | I.ram j = b}

/-- The number of `j ∈ [1, w]` with `r_j < b`. -/
def ramCountLT (b : ℚ) : ℕ :=
  #{j ∈ Icc 1 I.w | I.ram j < b}

/-- The bound `p ^ (d_1 + ⋯ + d_{i - 1} + 1) ε e_K / (p - 1)` for the ram `b = b_i` of LMFDB
`lf.herbrand_invariant`, relative to an absolute ramification index `e_K`. -/
def ramBound (eK : ℕ) (b : ℚ) : ℚ :=
  p ^ (I.ramCountLT b + 1) * I.ε * eK / (p - 1)

/-- A ram `b` of a Herbrand invariant `I` is **geometric** (LMFDB `lf.herbrand_invariant`) relative
to an absolute ramification index `e_K` if, with `d` its multiplicity, `(p ^ d - 1) b` is an integer
not divisible by `p` and `b < p ^ (d_1 + ⋯ + d_{i - 1} + 1) ε e_K / (p - 1)`. -/
def IsGeometricRam (eK : ℕ) (b : ℚ) : Prop :=
  b ∈ (Icc 1 I.w).image I.ram ∧ ((p ^ I.ramMultiplicity b - 1) * b).den = 1 ∧
    ¬(p : ℤ) ∣ ((p ^ I.ramMultiplicity b - 1) * b).num ∧ b < I.ramBound eK b

/-- A ram `b` of a Herbrand invariant `I` is **arithmetic** (LMFDB `lf.herbrand_invariant`)
relative to an absolute ramification index `e_K` if it has multiplicity `1` and
`b = p ^ (d_1 + ⋯ + d_{i - 1} + 1) ε e_K / (p - 1)` (then `(p - 1) b` is an integer). -/
def IsArithmeticRam (eK : ℕ) (b : ℚ) : Prop :=
  b ∈ (Icc 1 I.w).image I.ram ∧ I.ramMultiplicity b = 1 ∧ b = I.ramBound eK b

/-- A Herbrand invariant `I` is **compatible** (LMFDB `lf.herbrand_invariant`) with an absolute
ramification index `e_K` if each of its distinct rams is geometric or arithmetic. -/
def IsCompatible (eK : ℕ) : Prop :=
  ∀ b ∈ (Icc 1 I.w).image I.ram, I.IsGeometricRam eK b ∨ I.IsArithmeticRam eK b

/-- A `p`-adic field `K` is **compatible** with a Herbrand invariant `I` (LMFDB
`lf.herbrand_invariant`) if `I` is compatible with its absolute ramification index `e_K`; so
compatibility depends only on `e_K`. -/
def IsCompatibleWith (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Fact p.Prime] [TauCeti.FinitePadicExtension K p] : Prop :=
  I.IsCompatible (TauCeti.absoluteRamificationIndex K p)

variable (p) in
/-- The set `𝓡_k^z` of LMFDB `lf.rams` as the knowl writes it: the positive rationals `α` with
denominator dividing `p ^ k - 1` and numerator prime to `p`, with `α < p z / (p - 1)` if `k > 1` and
`α ≤ p z / (p - 1)` if `k = 1`. For a natural number `z` the boundary value `p z / (p - 1)` is not
in it, its numerator being divisible by `p`, although it is the arithmetic ram of LMFDB
`lf.herbrand_invariant` and occurs; the set of possible rams is
`IsNonarchimedeanLocalField.HerbrandInvariant.possibleRamSet`, which adds it for `k = 1`. -/
def ramSet (k : ℕ) (z : ℚ) : Set ℚ :=
  {α | 0 < α ∧ α.den ∣ p ^ k - 1 ∧ ¬(p : ℤ) ∣ α.num ∧
    if k = 1 then α ≤ p * z / (p - 1) else α < p * z / (p - 1)}

variable {j : ℕ} {b : ℚ}

private lemma apply_iff_le_card_filter {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ ⦃i j : ℕ⦄, i ≤ j → P j → P i) {w : ℕ} (hj₀ : 1 ≤ j) (hj : j ≤ w) :
    P j ↔ j ≤ #{i ∈ Icc 1 w | P i} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hsub : Icc 1 j ⊆ {i ∈ Icc 1 w | P i} := fun i hi ↦ mem_filter.mpr
      ⟨mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans hj⟩, hP (mem_Icc.mp hi).2 h⟩
    simpa using card_le_card hsub
  · by_contra hP'
    have hsub : {i ∈ Icc 1 w | P i} ⊆ Icc 1 (j - 1) := fun i hi ↦ by
      rw [mem_filter, mem_Icc] at hi
      exact mem_Icc.mpr ⟨hi.1.1, Nat.le_sub_one_of_lt <| lt_of_not_ge fun hji ↦ hP' <| hP hji hi.2⟩
    have hle : #{i ∈ Icc 1 w | P i} ≤ j - 1 :=
      (card_le_card hsub).trans_eq <| by rw [Nat.card_Icc, Nat.add_sub_cancel]
    omega

variable (b) in
lemma card_filter_ram_le :
    #{j ∈ Icc 1 I.w | I.ram j ≤ b} = I.ramCountLT b + I.ramMultiplicity b := by
  rw [ramCountLT, ramMultiplicity,
    ← card_union_of_disjoint (disjoint_filter.mpr fun _ _ h h' ↦ h.ne h'), ← filter_or]
  exact congrArg card <| filter_congr fun _ _ ↦ le_iff_lt_or_eq

variable (b) in
lemma ramCountLT_add_ramMultiplicity_le : I.ramCountLT b + I.ramMultiplicity b ≤ I.w :=
  (I.card_filter_ram_le b).symm.trans_le <|
    (card_filter_le _ _).trans_eq <| by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- **The rams smaller than `b`**: for `1 ≤ j ≤ w`, `r_j < b` exactly when `j` is at most the
number `c` of rams smaller than `b`. -/
lemma ram_lt_iff_le_ramCountLT (hj₀ : 1 ≤ j) (hj : j ≤ I.w) : I.ram j < b ↔ j ≤ I.ramCountLT b :=
  apply_iff_le_card_filter (fun _ _ h h' ↦ (I.monotone_ram h).trans_lt h') hj₀ hj

/-- **The rams at most `b`**: for `1 ≤ j ≤ w`, `r_j ≤ b` exactly when `j ≤ c + d`, for the number
`c` of rams smaller than `b` and the multiplicity `d` of `b`. So the rams equal to `b` are the
`r_j` with `c < j ≤ c + d`. -/
lemma ram_le_iff_le_ramCountLT_add_ramMultiplicity (hj₀ : 1 ≤ j) (hj : j ≤ I.w) :
    I.ram j ≤ b ↔ j ≤ I.ramCountLT b + I.ramMultiplicity b := by
  rw [← I.card_filter_ram_le b]
  exact apply_iff_le_card_filter (fun _ _ h h' ↦ (I.monotone_ram h).trans h') hj₀ hj

lemma ram_eq_of_ramCountLT_lt (hj : I.ramCountLT b < j)
    (hj' : j ≤ I.ramCountLT b + I.ramMultiplicity b) : I.ram j = b := by
  have hw : j ≤ I.w := hj'.trans <| I.ramCountLT_add_ramMultiplicity_le b
  exact ((I.ram_le_iff_le_ramCountLT_add_ramMultiplicity (by omega) hw).mpr hj').antisymm <|
    not_lt.mp fun h ↦ hj.not_ge <| (I.ram_lt_iff_le_ramCountLT (by omega) hw).mp h

lemma ramMultiplicity_pos (hb : b ∈ (Icc 1 I.w).image I.ram) : 0 < I.ramMultiplicity b := by
  rcases mem_image.mp hb with ⟨k, hk, rfl⟩
  rw [ramMultiplicity, card_pos]
  exact ⟨k, mem_filter.mpr ⟨hk, rfl⟩⟩

end IsNonarchimedeanLocalField.HerbrandInvariant
