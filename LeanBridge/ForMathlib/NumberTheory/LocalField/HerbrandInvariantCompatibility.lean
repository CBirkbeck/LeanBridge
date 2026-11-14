import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeConverse

/-!
# The three representations of a Herbrand invariant, and compatibility

Let `I = (r_1, …, r_w)_ε^f` be a Herbrand invariant at a prime `p`
(`IsNonarchimedeanLocalField.HerbrandInvariant`), with Swan slopes `s_k` and means `m_k`. This file
proves the four relations of LMFDB `lf.herbrand_invariant` between the three representations
`[s_1, …, s_w]_ε^f`, `(r_1, …, r_w)_ε^f` and `⟨m_1, …, m_w⟩_ε^f`, and that an admissible invariant
satisfies the compatibility conditions of that knowl.

Let `b_1 < ⋯ < b_t` be the distinct rams, `d_i` the multiplicity of `b_i`, and `e₀` a natural
number, the valuation of `p` in the base field. LMFDB `lf.herbrand_invariant` calls `I` compatible
with `e₀` if for each `i`, `(p ^ d_i - 1) b_i` is an integer and either it is prime to `p` and
`b_i < p ^ (d_1 + ⋯ + d_{i - 1} + 1) ε e₀ / (p - 1)` (a geometric ram), or `d_i = 1` and
`b_i = p ^ (d_1 + ⋯ + d_{i - 1} + 1) ε e₀ / (p - 1)` (an arithmetic ram). The Herbrand invariants of
the extensions of a `p`-adic field are admissible for `e₀`
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible`, Monge's conditions at the vertices of
the ramification polygon), and we derive compatibility from admissibility.

Write `c = d_1 + ⋯ + d_{i - 1}` and `d = d_i`, so that `r_{c + 1} = ⋯ = r_{c + d} = b_i`, and
`c` and `c + d` are vertices. With `e = ε p ^ w`, the means satisfy
`e m_{c + d} - e m_c = p ^ (w - c - d) (p ^ d - 1) b_i`. At a vertex `k`, admissibility makes
`e m_k` an integer divisible by `p ^ (w - k)`, and exactly divisible by it unless the small ram
`r_k^*` is `e₀`. So `(p ^ d - 1) b_i` is an integer, prime to `p` unless `r_{c + d}^* = e₀`; and
`r_{c + 1}^* ≤ e₀`, with `r_{c + d}^* = r_{c + 1}^* / p ^ (d - 1)`, gives the two cases.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.mean_eq_sum_ram`,
  `IsNonarchimedeanLocalField.HerbrandInvariant.ram_succ_eq`,
  `IsNonarchimedeanLocalField.HerbrandInvariant.swanSlope_succ_eq` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.mean_eq_sum_swanSlope` (LMFDB
  `lf.herbrand_invariant`): the relations between the rams, the means and the Swan slopes.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ram_lt_iff_le_ramCountLT` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.ram_le_iff_le_ramCountLT_add_ramMultiplicity`: the
  rams equal to a ram `b` are the `r_j` with `c < j ≤ c + d`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mul_mean_add_sub_mul_mean`: the means across a
  block of equal rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible.exists_mul_mean_eq` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible.exists_mul_mean_eq_of_smallRam_ne`:
  the divisibility of `e m_k` at the vertices.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible.den_pow_ramMultiplicity_sub_one_mul`
  (LMFDB `lf.herbrand_invariant`): `(p ^ d_i - 1) b_i` is an integer.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible.isCompatible` (LMFDB
  `lf.herbrand_invariant`): an admissible Herbrand invariant is compatible.

## References

* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, Lemma 2 and p. 8.
-/

open Finset

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p) {e₀ c d j k : ℕ} {b : ℚ}

variable (k) in
/-- **The means in terms of the rams** (LMFDB `lf.herbrand_invariant`):
`m_k = ∑_{j = 1}^k (p - 1) / (ε p ^ j) r_j`. -/
lemma mean_eq_sum_ram : I.mean k = ∑ j ∈ Icc 1 k, (p - 1) / (I.ε * p ^ j) * I.ram j :=
  sum_congr rfl fun _ _ ↦ mul_div_right_comm _ _ _

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

lemma pos_of_mem_image_ram (hb : b ∈ (Icc 1 I.w).image I.ram) : 0 < b := by
  rcases mem_image.mp hb with ⟨k, hk, rfl⟩
  exact (I.zero_lt_ram_one <| (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2).trans_le <|
    I.monotone_ram (mem_Icc.mp hk).1

lemma isVertex_ramCountLT (hb : b ∈ (Icc 1 I.w).image I.ram) : I.IsVertex (I.ramCountLT b) := by
  have hd : 0 < I.ramMultiplicity b := I.ramMultiplicity_pos hb
  have hcd : I.ramCountLT b + I.ramMultiplicity b ≤ I.w := I.ramCountLT_add_ramMultiplicity_le b
  refine .inr ?_
  rw [I.ram_eq_of_ramCountLT_lt (Nat.lt_succ_self _) (by omega)]
  rcases Nat.eq_zero_or_pos (I.ramCountLT b) with h | h
  · rw [h, I.ram_zero]
    exact I.pos_of_mem_image_ram hb
  · exact (I.ram_lt_iff_le_ramCountLT h (by omega)).mpr le_rfl

lemma isVertex_ramCountLT_add_ramMultiplicity (hb : b ∈ (Icc 1 I.w).image I.ram) :
    I.IsVertex (I.ramCountLT b + I.ramMultiplicity b) := by
  have hd : 0 < I.ramMultiplicity b := I.ramMultiplicity_pos hb
  rcases (I.ramCountLT_add_ramMultiplicity_le b).eq_or_lt with h | h
  · exact .inl h
  · refine .inr <| not_le.mp fun hle ↦ ?_
    rw [I.ram_eq_of_ramCountLT_lt (by omega) le_rfl] at hle
    have hle' : I.ramCountLT b + I.ramMultiplicity b + 1 ≤ I.ramCountLT b + I.ramMultiplicity b :=
      (I.ram_le_iff_le_ramCountLT_add_ramMultiplicity (by omega) h).mp hle
    omega

variable [Fact p.Prime]

private lemma one_lt_natCast_prime : (1 : ℚ) < p :=
  Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt

variable (k) in
/-- **The rams in terms of the means** (LMFDB `lf.herbrand_invariant`):
`r_k = ε p ^ k (m_k - m_{k - 1}) / (p - 1)` for `k ≥ 1`. -/
lemma ram_succ_eq : I.ram (k + 1) = I.ε * p ^ (k + 1) * (I.mean (k + 1) - I.mean k) / (p - 1) := by
  have hp₀ : (p : ℚ) ≠ 0 := natCast_prime_pos.ne'
  have hp₁ : (p : ℚ) - 1 ≠ 0 := (sub_pos.mpr one_lt_natCast_prime).ne'
  have hε : (I.ε : ℚ) ≠ 0 := I.natCast_ε_pos.ne'
  rw [← I.smallRam_eq_mean_sub_mean, smallRam]
  field_simp

variable (k) in
/-- **The Swan slopes in terms of the means** (LMFDB `lf.herbrand_invariant`, `lf.means`):
`s_k = (p m_k - m_{k - 1}) / (p - 1)` for `k ≥ 1`. -/
lemma swanSlope_succ_eq : I.swanSlope (k + 1) = (p * I.mean (k + 1) - I.mean k) / (p - 1) := by
  have ht : I.tinyRam (k + 1) = I.swanSlope (k + 1) - I.mean (k + 1) :=
    I.tinyRam_eq_swanSlope_sub_mean (Fact.out : p.Prime).ne_zero (k + 1)
  have hs : I.smallRam (k + 1) = I.mean (k + 1) - I.mean k := I.smallRam_eq_mean_sub_mean k
  rw [tinyRam] at ht
  rw [smallRam, mul_div_assoc, ht] at hs
  rw [eq_div_iff (sub_pos.mpr one_lt_natCast_prime).ne']
  linear_combination hs

variable (k) in
/-- **The means in terms of the Swan slopes** (LMFDB `lf.herbrand_invariant`):
`m_k = ∑_{j = 1}^k (p - 1) / p ^ (k + 1 - j) s_j`. -/
lemma mean_eq_sum_swanSlope :
    I.mean k = ∑ j ∈ Icc 1 k, (p - 1) / p ^ (k + 1 - j) * I.swanSlope j := by
  have hp₀ : (p : ℚ) ≠ 0 := natCast_prime_pos.ne'
  have hp₁ : (p : ℚ) - 1 ≠ 0 := (sub_pos.mpr one_lt_natCast_prime).ne'
  induction k with
  | zero => rw [I.mean_zero, Icc_eq_empty (by omega), sum_empty]
  | succ k ih =>
    have hsum :
        ∑ j ∈ Icc 1 k, (p - 1) / (p : ℚ) ^ (k + 1 + 1 - j) * I.swanSlope j = I.mean k / p := by
      rw [ih, sum_div]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [Nat.sub_add_comm <| (mem_Icc.mp hj).2.trans k.le_succ, pow_succ]
      field_simp
    rw [sum_Icc_succ_top (Nat.le_add_left 1 k), hsum, I.swanSlope_succ_eq k,
      Nat.add_sub_cancel_left, pow_one]
    field_simp
    ring1

/-- **The means across a block of equal rams**: if `r_{c + 1} = ⋯ = r_{c + d} = b`, then
`e m_{c + d} - e m_c = p ^ (w - c - d) (p ^ d - 1) b`, for `e = ε p ^ w`. -/
lemma mul_mean_add_sub_mul_mean (hcd : c + d ≤ I.w) (hram : ∀ i, c < i → i ≤ c + d → I.ram i = b) :
    (I.ramificationIndex : ℚ) * I.mean (c + d) - I.ramificationIndex * I.mean c =
      p ^ (I.w - (c + d)) * ((p ^ d - 1) * b) := by
  induction d with
  | zero => rw [Nat.add_zero, sub_self, pow_zero, sub_self, zero_mul, mul_zero]
  | succ d ih =>
    have hpow : (p : ℚ) ^ (I.w - (c + d)) = p ^ (I.w - (c + d + 1)) * p := by
      rw [← pow_succ, (by omega : I.w - (c + d + 1) + 1 = I.w - (c + d))]
    have ih' : (I.ramificationIndex : ℚ) * I.mean (c + d) - I.ramificationIndex * I.mean c =
        p ^ (I.w - (c + d)) * ((p ^ d - 1) * b) :=
      ih (by omega) fun i hi hi' ↦ hram i hi (by omega)
    rw [← add_assoc, I.mean_succ, mul_add, I.mul_smallRam_eq (by omega),
      hram (c + d + 1) (by omega) le_rfl]
    linear_combination ih' + ((p : ℚ) ^ d - 1) * b * hpow

lemma smallRam_add_one_eq (hd : 0 < d) (hram : ∀ i, c < i → i ≤ c + d → I.ram i = b) :
    I.smallRam (c + 1) = p ^ (d - 1) * I.smallRam (c + d) := by
  have hp₀ : (p : ℚ) ≠ 0 := natCast_prime_pos.ne'
  have hε : (I.ε : ℚ) ≠ 0 := I.natCast_ε_pos.ne'
  rw [smallRam, smallRam, hram (c + 1) (by omega) (by omega), hram (c + d) (by omega) le_rfl,
    (by omega : c + d = c + 1 + (d - 1)), pow_add (p : ℚ) (c + 1) (d - 1)]
  field_simp

variable {I}

/-- **The means at the vertices are multiples of powers of `p`**: if `I` is admissible and `k` is
a vertex, then `e m_k` is a natural number divisible by `p ^ (w - k)`. -/
lemma IsAdmissible.exists_mul_mean_eq (hadm : I.IsAdmissible e₀) (hk : k ≤ I.w)
    (hv : I.IsVertex k) : ∃ B : ℕ, (I.ramificationIndex : ℚ) * I.mean k = p ^ (I.w - k) * B := by
  induction k with
  | zero => exact ⟨0, by rw [I.mean_zero, mul_zero, Nat.cast_zero, mul_zero]⟩
  | succ k ih =>
    have hk' : k < I.w := hk
    by_cases hd : (I.smallRam (k + 1)).den = 1
    · have hs : I.smallRam (k + 1) = e₀ := hadm.smallRam_eq hk' hv hd
      have hpow : (p : ℚ) ^ (I.w - k) = p ^ (I.w - (k + 1)) * p := by
        rw [← pow_succ, (by omega : I.w - (k + 1) + 1 = I.w - k)]
      have hw : (p : ℚ) ^ I.w = p ^ (I.w - (k + 1)) * p ^ (k + 1) := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      rcases ih hk'.le <| isVertex_of_smallRam_eq hadm hk' hs with ⟨B, hB⟩
      refine ⟨p * B + I.ε * p ^ (k + 1) * e₀, ?_⟩
      rw [I.mean_succ, hs, mul_add, hB, hpow, ramificationIndex]
      push_cast
      rw [hw]
      ring1
    · rcases hadm.exists_pointIndex_eq hk' hv hd with ⟨σ, hσ, hidx⟩
      have hdvd : p ^ (I.w - (k + 1)) ∣ σ := hidx ▸ I.pow_dvd_of_pointIndex
      rcases hdvd with ⟨B, rfl⟩
      exact ⟨B, by rw [← hσ, Nat.cast_mul, Nat.cast_pow]⟩

/-- **The means at the vertices with a small ram other than `e₀`**: if `I` is admissible for
`e₀`, and `k ≥ 1` is a vertex with `r_k^* ≠ e₀`, then `e m_k` is a natural number exactly divisible
by `p ^ (w - k)`. -/
lemma IsAdmissible.exists_mul_mean_eq_of_smallRam_ne (hadm : I.IsAdmissible e₀) (hk₀ : k ≠ 0)
    (hk : k ≤ I.w) (hv : I.IsVertex k) (hs : I.smallRam k ≠ e₀) :
    ∃ A : ℕ, (I.ramificationIndex : ℚ) * I.mean k = p ^ (I.w - k) * A ∧ ¬p ∣ A := by
  rcases Nat.exists_eq_succ_of_ne_zero hk₀ with ⟨k, rfl⟩
  have hk' : k < I.w := hk
  rcases hadm.exists_pointIndex_eq hk' hv fun hd ↦ hs <| hadm.smallRam_eq hk' hv hd with
    ⟨σ, hσ, hidx⟩
  have hi₀ : σ % I.ramificationIndex ≠ 0 := fun h₀ ↦ by
    rw [h₀, I.pointIndex_zero] at hidx
    omega
  have hvp : padicValNat p (σ % I.ramificationIndex) = I.w - (k + 1) := by
    rw [pointIndex, padicValNat_gcd_pow hi₀] at hidx
    rcases le_total (padicValNat p (σ % I.ramificationIndex)) I.w with h | h
    · rw [min_eq_left h] at hidx
      omega
    · rw [min_eq_right h] at hidx
      omega
  have hdvd : p ^ (I.w - (k + 1)) ∣ σ := hidx ▸ I.pow_dvd_of_pointIndex
  have he : p ^ (I.w - (k + 1) + 1) ∣ I.ramificationIndex :=
    (pow_dvd_pow p (by omega)).mul_left I.ε
  rcases hdvd with ⟨A, rfl⟩
  refine ⟨A, by rw [← hσ, Nat.cast_mul, Nat.cast_pow],
    fun hA ↦ pow_succ_padicValNat_not_dvd (p := p) hi₀ ?_⟩
  rw [hvp]
  exact (Nat.dvd_mod_iff he).mpr <| pow_succ p _ ▸ mul_dvd_mul_left _ hA

lemma IsAdmissible.exists_pow_sub_one_mul_eq (hadm : I.IsAdmissible e₀) (hcd : c + d ≤ I.w)
    (hram : ∀ i, c < i → i ≤ c + d → I.ram i = b) (hvc : I.IsVertex c) {A : ℕ}
    (hA : (I.ramificationIndex : ℚ) * I.mean (c + d) = p ^ (I.w - (c + d)) * A) :
    ∃ B : ℕ, ((p : ℚ) ^ d - 1) * b = A - p ^ d * B := by
  rcases hadm.exists_mul_mean_eq (by omega) hvc with ⟨B, hB⟩
  have hp₀ : (p : ℚ) ^ (I.w - (c + d)) ≠ 0 := pow_ne_zero _ natCast_prime_pos.ne'
  have hpow : (p : ℚ) ^ (I.w - c) = p ^ (I.w - (c + d)) * p ^ d := by
    rw [← pow_add, (by omega : I.w - (c + d) + d = I.w - c)]
  have hblock : (I.ramificationIndex : ℚ) * I.mean (c + d) - I.ramificationIndex * I.mean c =
      p ^ (I.w - (c + d)) * ((p ^ d - 1) * b) :=
    I.mul_mean_add_sub_mul_mean hcd hram
  rw [hA, hB, hpow] at hblock
  refine ⟨B, mul_left_cancel₀ hp₀ ?_⟩
  linear_combination -hblock

lemma IsAdmissible.den_pow_sub_one_mul (hadm : I.IsAdmissible e₀) (hcd : c + d ≤ I.w)
    (hram : ∀ i, c < i → i ≤ c + d → I.ram i = b) (hvc : I.IsVertex c) (hvcd : I.IsVertex (c + d)) :
    (((p : ℚ) ^ d - 1) * b).den = 1 := by
  rcases hadm.exists_mul_mean_eq hcd hvcd with ⟨A, hA⟩
  rcases hadm.exists_pow_sub_one_mul_eq hcd hram hvc hA with ⟨B, hB⟩
  have h : ((p : ℚ) ^ d - 1) * b = ((A - p ^ d * B : ℤ) : ℚ) := by exact_mod_cast hB
  rw [h, Rat.den_intCast]

lemma IsAdmissible.not_dvd_num_of_smallRam_lt (hadm : I.IsAdmissible e₀) (hd : 0 < d)
    (hcd : c + d ≤ I.w) (hram : ∀ i, c < i → i ≤ c + d → I.ram i = b) (hvc : I.IsVertex c)
    (hvcd : I.IsVertex (c + d)) (hlt : I.smallRam (c + 1) < e₀) :
    ¬(p : ℤ) ∣ (((p : ℚ) ^ d - 1) * b).num := by
  have hle : I.smallRam (c + d) ≤ I.smallRam (c + 1) := by
    rw [I.smallRam_add_one_eq hd hram]
    exact le_mul_of_one_le_left (I.smallRam_nonneg _) <| one_le_pow₀ one_le_natCast_prime
  rcases hadm.exists_mul_mean_eq_of_smallRam_ne (by omega) hcd hvcd (hle.trans_lt hlt).ne with
    ⟨A, hA, hpA⟩
  rcases hadm.exists_pow_sub_one_mul_eq hcd hram hvc hA with ⟨B, hB⟩
  have h : ((p : ℚ) ^ d - 1) * b = ((A - p ^ d * B : ℤ) : ℚ) := by exact_mod_cast hB
  have hpd : (p : ℤ) ∣ p ^ d * B := (dvd_pow_self _ hd.ne').mul_right _
  rw [h, Rat.num_intCast]
  exact fun hdvd ↦ hpA <| Int.natCast_dvd_natCast.mp <| (dvd_sub_left hpd).mp hdvd

lemma IsAdmissible.eq_one_of_smallRam_eq (hadm : I.IsAdmissible e₀) (hd : 0 < d) (hcd : c + d ≤ I.w)
    (hram : ∀ i, c < i → i ≤ c + d → I.ram i = b) (hvc : I.IsVertex c) (hvcd : I.IsVertex (c + d))
    (heq : I.smallRam (c + 1) = e₀) : d = 1 := by
  by_contra hd₁
  have hp₀ : (p : ℚ) ≠ 0 := natCast_prime_pos.ne'
  have hε : (I.ε : ℚ) ≠ 0 := I.natCast_ε_pos.ne'
  have he₀ : (0 : ℚ) < e₀ := heq ▸ smallRam_pos (by omega)
  have hx : (e₀ : ℚ) = p ^ (d - 1) * I.smallRam (c + d) := heq ▸ I.smallRam_add_one_eq hd hram
  have hne : I.smallRam (c + d) ≠ e₀ := fun h ↦
    (lt_mul_of_one_lt_left he₀ <| one_lt_pow₀ one_lt_natCast_prime (by omega)).ne <| h ▸ hx
  rcases hadm.exists_mul_mean_eq_of_smallRam_ne (by omega) hcd hvcd hne with ⟨A, hA, hpA⟩
  rcases hadm.exists_pow_sub_one_mul_eq hcd hram hvc hA with ⟨B, hB⟩
  have hb : ((p : ℚ) - 1) * b = e₀ * I.ε * p ^ (c + 1) := by
    rw [← heq, smallRam, hram (c + 1) (by omega) (by omega)]
    field_simp
  have hG : (p : ℚ) ^ d - 1 = (∑ i ∈ range d, (p : ℚ) ^ i) * (p - 1) := (geom_sum_mul _ _).symm
  have hA' : A = p ^ d * B + (∑ i ∈ range d, p ^ i) * (e₀ * I.ε * p ^ (c + 1)) := by
    have h : (A : ℚ) = p ^ d * B + (∑ i ∈ range d, (p : ℚ) ^ i) * (e₀ * I.ε * p ^ (c + 1)) := by
      linear_combination -hB + b * hG + (∑ i ∈ range d, (p : ℚ) ^ i) * hb
    exact_mod_cast h
  exact hpA <| hA' ▸ dvd_add ((dvd_pow_self p hd.ne').mul_right B)
    (((dvd_pow_self p c.succ_ne_zero).mul_left _).mul_left _)

/-- **`(p ^ d - 1) b` is an integer** (LMFDB `lf.herbrand_invariant`): if `I` is admissible and
`b` is a ram of `I` of multiplicity `d`, then `(p ^ d - 1) b` is an integer. -/
lemma IsAdmissible.den_pow_ramMultiplicity_sub_one_mul (hadm : I.IsAdmissible e₀)
    (hb : b ∈ (Icc 1 I.w).image I.ram) : (((p : ℚ) ^ I.ramMultiplicity b - 1) * b).den = 1 :=
  hadm.den_pow_sub_one_mul (I.ramCountLT_add_ramMultiplicity_le b)
    (fun _ ↦ I.ram_eq_of_ramCountLT_lt) (I.isVertex_ramCountLT hb)
    (I.isVertex_ramCountLT_add_ramMultiplicity hb)

/-- **An admissible Herbrand invariant is compatible** (LMFDB `lf.herbrand_invariant`): if
`I = (r_1, …, r_w)_ε^f` is admissible for `e₀` (as the Herbrand invariant of an extension of a
`p`-adic field with `v(p) = e₀` is), then every distinct ram `b` of `I`, of multiplicity `d` and
with `c` rams smaller than it, is geometric or arithmetic: `(p ^ d - 1) b` is an integer prime to
`p` and `b < p ^ (c + 1) ε e₀ / (p - 1)`, or `d = 1` and `b = p ^ (c + 1) ε e₀ / (p - 1)`. -/
lemma IsAdmissible.isCompatible (hadm : I.IsAdmissible e₀) : I.IsCompatible e₀ := by
  intro b hb
  have hd : 0 < I.ramMultiplicity b := I.ramMultiplicity_pos hb
  have hcd : I.ramCountLT b + I.ramMultiplicity b ≤ I.w := I.ramCountLT_add_ramMultiplicity_le b
  have hvc : I.IsVertex (I.ramCountLT b) := I.isVertex_ramCountLT hb
  have hvcd : I.IsVertex (I.ramCountLT b + I.ramMultiplicity b) :=
    I.isVertex_ramCountLT_add_ramMultiplicity hb
  have hp₁ : (0 : ℚ) < p - 1 := sub_pos.mpr one_lt_natCast_prime
  have hden : (0 : ℚ) < I.ε * p ^ (I.ramCountLT b + 1) :=
    mul_pos I.natCast_ε_pos <| pow_pos natCast_prime_pos _
  have hx : I.smallRam (I.ramCountLT b + 1) = (p - 1) * b / (I.ε * p ^ (I.ramCountLT b + 1)) := by
    rw [smallRam, I.ram_eq_of_ramCountLT_lt (Nat.lt_succ_self _) (by omega)]
  rcases (hadm.smallRam_le (k := I.ramCountLT b) (by omega)).lt_or_eq with hlt | heq
  · refine .inl ⟨hb, hadm.den_pow_ramMultiplicity_sub_one_mul hb,
      hadm.not_dvd_num_of_smallRam_lt hd hcd (fun _ ↦ I.ram_eq_of_ramCountLT_lt) hvc hvcd hlt, ?_⟩
    rw [hx, div_lt_iff₀ hden] at hlt
    rw [ramBound, lt_div_iff₀ hp₁]
    linarith
  · refine .inr ⟨hb,
      hadm.eq_one_of_smallRam_eq hd hcd (fun _ ↦ I.ram_eq_of_ramCountLT_lt) hvc hvcd heq, ?_⟩
    rw [hx, div_eq_iff hden.ne'] at heq
    rw [ramBound, eq_div_iff hp₁.ne']
    linarith

end IsNonarchimedeanLocalField.HerbrandInvariant
