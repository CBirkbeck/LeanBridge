import LeanBridge.ForMathlib.NumberTheory.LocalField.CompatibleAdmissible

/-!
# The sets of possible rams

LMFDB `lf.rams` enumerates the possible rams over a `p`-adic field `K` through the sets `𝓡_k^z`:
with `𝓡_k^∞` the set of positive rationals with denominator dividing `p ^ k - 1` and numerator prime
to `p`, it sets `𝓡_k^z = {α ∈ 𝓡_k^∞ : α < p z / (p - 1)}` for `k > 1` and
`𝓡_1^z = {α ∈ 𝓡_1^∞ : α ≤ p z / (p - 1)}`
(`IsNonarchimedeanLocalField.HerbrandInvariant.ramSet`). As written, the boundary value
`p z / (p - 1)` never lies in `𝓡_1^z` when `z` is a positive integer, since its numerator is
divisible by `p`, so the `≤` of `𝓡_1^z` is a `<`. But `p z / (p - 1)` is the arithmetic ram of LMFDB
`lf.herbrand_invariant`, which occurs: the knowl means
`𝓡_1^z = {α ∈ 𝓡_1^∞ : α < p z / (p - 1)} ∪ {p z / (p - 1)}`.

This file defines the corrected sets
(`IsNonarchimedeanLocalField.HerbrandInvariant.possibleRamSet`), compares them with the sets of the
knowl as written, and proves that a Herbrand invariant `I = (r_1, …, r_w)_ε^f` is compatible with
`e₀`, in the sense of LMFDB `lf.herbrand_invariant`, if and only if each of its distinct rams `b`,
of multiplicity `d` and with `c` rams smaller than it, lies in `𝓡_d^{e₀ ε p ^ c}`. For strictly
increasing rams this says that `r_k` lies in `𝓡_1^{e₀ ε p ^ (k - 1)}`, as in the knowl.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.possibleRamSet` (LMFDB `lf.rams`): the sets `𝓡_k^z`,
  with the arithmetic ram `p z / (p - 1)` in `𝓡_1^z`.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.mem_possibleRamSet_iff`: the conditions on the
  denominator and the numerator of `α` say that `(p ^ k - 1) α` is an integer prime to `p`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.natCast_mul_div_notMem_ramSet`: the set `𝓡_1^z` of
  the knowl as written does not contain `p z / (p - 1)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ramSet_eq_setOf`: the sets of the knowl as written
  are defined by the strict bound `α < p z / (p - 1)`, also when `k = 1`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.possibleRamSet_eq_ramSet_union`: the corrected set
  is the set of the knowl as written together with `p z / (p - 1)` when `k = 1`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isGeometricRam_or_isArithmeticRam_iff`: a ram is
  geometric or arithmetic exactly when it lies in its set of possible rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isCompatible_iff_forall_mem_possibleRamSet` (LMFDB
  `lf.rams`): compatibility in terms of the sets `𝓡_d^{e₀ ε p ^ c}`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isCompatible_iff_of_ram_lt` (LMFDB `lf.rams`): the
  case of strictly increasing rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isCompatible_iff_of_forall_ram_eq` (LMFDB
  `lf.rams`): the case of `w` equal rams and tame degree `1`.
-/

open Finset

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} {I : HerbrandInvariant p} {e₀ k n : ℕ} {z α b : ℚ}

variable (p k z) in
/-- The set `𝓡_k^z` of **possible rams** (LMFDB `lf.rams`, corrected at the boundary): the positive
rationals `α` with denominator dividing `p ^ k - 1`, numerator prime to `p` and
`α < p z / (p - 1)`, together with `p z / (p - 1)` if `k = 1` and it is positive. The knowl's
`𝓡_1^z = {α ∈ 𝓡_1^∞ : α ≤ p z / (p - 1)}` asks for a numerator prime to `p` at the boundary too,
which excludes it (`natCast_mul_div_notMem_ramSet`), although `p z / (p - 1)` is the arithmetic ram
of LMFDB `lf.herbrand_invariant`. -/
def possibleRamSet : Set ℚ :=
  {α | 0 < α ∧ (α.den ∣ p ^ k - 1 ∧ ¬(p : ℤ) ∣ α.num ∧ α < p * z / (p - 1) ∨
    k = 1 ∧ α = p * z / (p - 1))}

private lemma natCast_den_mul_mul (c : ℕ) : ((b.den * c : ℕ) : ℚ) * b = ((c * b.num : ℤ) : ℚ) := by
  push_cast
  linear_combination (c : ℚ) * Rat.mul_den_eq_num b

lemma den_natCast_mul_eq_one_iff : ((n : ℚ) * b).den = 1 ↔ b.den ∣ n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h₁ : (((n : ℚ) * b).num : ℚ) = n * b := (Rat.den_eq_one_iff _).mp h
    have h₂ : ((n : ℚ) * b).num * (b.den : ℤ) = n * b.num := by
      have h₃ : (((n : ℚ) * b).num : ℚ) * b.den = n * b.num := by
        rw [h₁, mul_assoc, Rat.mul_den_eq_num]
      exact_mod_cast h₃
    have h₄ : b.den ∣ n * b.num.natAbs := by
      rw [← Int.natAbs_natCast n, ← Int.natAbs_mul, ← h₂, Int.natAbs_mul, Int.natAbs_natCast]
      exact dvd_mul_left _ _
    exact b.reduced.symm.dvd_of_dvd_mul_right h₄
  · rintro ⟨c, rfl⟩
    rw [natCast_den_mul_mul, Rat.den_intCast]

variable [Fact p.Prime]

lemma natCast_dvd_num_natCast_mul_iff (hn : ¬p ∣ n) (hb : b.den ∣ n) :
    (p : ℤ) ∣ ((n : ℚ) * b).num ↔ (p : ℤ) ∣ b.num := by
  rcases hb with ⟨c, rfl⟩
  have hpc : ¬(p : ℤ) ∣ c := fun h ↦ hn <| (Int.natCast_dvd_natCast.mp h).mul_left _
  rw [natCast_den_mul_mul, Rat.num_intCast, (Nat.prime_iff_prime_int.mp Fact.out).dvd_mul,
    or_iff_right hpc]

lemma not_dvd_pow_sub_one (hk : k ≠ 0) : ¬p ∣ p ^ k - 1 :=
  fun h ↦ (Fact.out : p.Prime).one_lt.ne' <| Nat.dvd_one.mp <| (Nat.dvd_sub_iff_right
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos) (dvd_pow_self p hk)).mp h

/-- **The sets of possible rams through `(p ^ k - 1) α`**: for `k ≥ 1`, a rational `α` lies in
`𝓡_k^z` if and only if it is positive and either `(p ^ k - 1) α` is an integer prime to `p` and
`α < p z / (p - 1)`, or `k = 1` and `α = p z / (p - 1)`. These are the conditions for a geometric
and for an arithmetic ram of LMFDB `lf.herbrand_invariant`. -/
lemma mem_possibleRamSet_iff (hk : k ≠ 0) : α ∈ possibleRamSet p k z ↔
    0 < α ∧ ((((p : ℚ) ^ k - 1) * α).den = 1 ∧ ¬(p : ℤ) ∣ (((p : ℚ) ^ k - 1) * α).num ∧
      α < p * z / (p - 1) ∨ k = 1 ∧ α = p * z / (p - 1)) := by
  have hcast : (p : ℚ) ^ k - 1 = (p ^ k - 1 : ℕ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos), Nat.cast_pow, Nat.cast_one]
  rw [hcast, den_natCast_mul_eq_one_iff]
  exact and_congr_right fun _ ↦ or_congr_left <| and_congr_right fun hden ↦
    and_congr_left fun _ ↦ (natCast_dvd_num_natCast_mul_iff (not_dvd_pow_sub_one hk) hden).not.symm

variable (n) in
/-- **The boundary value is not in the set `𝓡_1^z` of the knowl as written** (LMFDB `lf.rams`): for
a natural number `z`, the number `p z / (p - 1)` does not lie in `𝓡_1^z`, defined by
`α ≤ p z / (p - 1)` with a numerator prime to `p`, since its numerator is divisible by `p`. -/
lemma natCast_mul_div_notMem_ramSet : (p * n / (p - 1) : ℚ) ∉ ramSet p 1 n := by
  have hp₁ : (p : ℚ) - 1 ≠ 0 := (sub_pos.mpr one_lt_natCast_prime).ne'
  rintro ⟨-, -, hnum, -⟩
  refine hnum ?_
  have h₁ : (p * n / (p - 1) : ℚ).num * ((p : ℤ) - 1) = p * (n * (p * n / (p - 1) : ℚ).den) := by
    have h₂ : ((p * n / (p - 1) : ℚ).num : ℚ) * (p - 1) = p * (n * (p * n / (p - 1) : ℚ).den) := by
      rw [← Rat.mul_den_eq_num]
      field_simp
    exact_mod_cast h₂
  refine ((Nat.prime_iff_prime_int.mp Fact.out).dvd_mul.mp ⟨_, h₁⟩).resolve_right fun h ↦ ?_
  have h₃ : (p : ℤ) = 1 :=
    Int.eq_one_of_dvd_one (Int.natCast_nonneg p) ((dvd_sub_right dvd_rfl).mp h)
  exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast h₃)

variable (n) in
/-- **The sets of the knowl as written have a strict bound** (LMFDB `lf.rams`): for a natural number
`z`, the set `𝓡_k^z` of LMFDB `lf.rams` as written consists of the positive rationals `α` with
denominator dividing `p ^ k - 1` and numerator prime to `p` such that `α < p z / (p - 1)`, also
when `k = 1`. -/
lemma ramSet_eq_setOf : ramSet p k n =
    {α : ℚ | 0 < α ∧ α.den ∣ p ^ k - 1 ∧ ¬(p : ℤ) ∣ α.num ∧ α < p * n / (p - 1)} := by
  ext α
  by_cases hk : k = 1
  · subst hk
    refine ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, ?_⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2.1, ?_⟩⟩
    · have hle : α ≤ p * n / (p - 1) := by simpa using h.2.2.2
      exact hle.lt_of_ne fun heq ↦ natCast_mul_div_notMem_ramSet n (heq ▸ h)
    · simpa using h.2.2.2.le
  · simp [ramSet, hk]

variable (n) in
/-- **The corrected sets and the sets of the knowl as written** (LMFDB `lf.rams`): for a natural
number `z`, the set `𝓡_k^z` of possible rams is the set of the knowl as written together with, for
`k = 1`, the arithmetic ram `p z / (p - 1)`. -/
lemma possibleRamSet_eq_ramSet_union :
    possibleRamSet p k n = ramSet p k n ∪ {α : ℚ | k = 1 ∧ 0 < α ∧ α = p * n / (p - 1)} := by
  rw [ramSet_eq_setOf]
  ext α
  simp only [possibleRamSet, Set.mem_ofPred_eq, Set.mem_union]
  tauto

/-- **A ram is geometric or arithmetic exactly when it lies in its set of possible rams** (LMFDB
`lf.rams`, `lf.herbrand_invariant`): a ram `b` of `I = (r_1, …, r_w)_ε^f`, of multiplicity `d` and
with `c` rams smaller than it, is geometric or arithmetic relative to `e₀` if and only if it lies in
`𝓡_d^{e₀ ε p ^ c}`. -/
lemma isGeometricRam_or_isArithmeticRam_iff (hb : b ∈ (Icc 1 I.w).image I.ram) :
    I.IsGeometricRam e₀ b ∨ I.IsArithmeticRam e₀ b ↔
      b ∈ possibleRamSet p (I.ramMultiplicity b) (e₀ * I.ε * p ^ I.ramCountLT b) := by
  have hb₀ : 0 < b := I.pos_of_mem_image_ram hb
  have hbound : I.ramBound e₀ b = p * (e₀ * I.ε * p ^ I.ramCountLT b) / (p - 1) := by
    rw [ramBound]
    ring1
  rw [mem_possibleRamSet_iff (I.ramMultiplicity_pos hb).ne', IsGeometricRam, IsArithmeticRam,
    hbound]
  exact ⟨fun h ↦ ⟨hb₀, h.imp (fun hg ↦ hg.2) fun ha ↦ ha.2⟩,
    fun h ↦ h.2.imp (fun hg ↦ ⟨hb, hg⟩) fun ha ↦ ⟨hb, ha⟩⟩

variable (I e₀) in
/-- **Compatibility through the sets of possible rams** (LMFDB `lf.rams`): a Herbrand invariant
`I = (r_1, …, r_w)_ε^f` is compatible with `e₀` if and only if each of its distinct rams `b`, of
multiplicity `d` and with `c` rams smaller than it, lies in `𝓡_d^{e₀ ε p ^ c}`: the rams are
chosen block by block, the block of `b` from the set attached to the degree `ε p ^ c` reached by
the smaller rams. -/
lemma isCompatible_iff_forall_mem_possibleRamSet : I.IsCompatible e₀ ↔
    ∀ b ∈ (Icc 1 I.w).image I.ram,
      b ∈ possibleRamSet p (I.ramMultiplicity b) (e₀ * I.ε * p ^ I.ramCountLT b) :=
  forall₂_congr fun _ hb ↦ isGeometricRam_or_isArithmeticRam_iff hb

/-- **Compatibility for strictly increasing rams** (LMFDB `lf.rams`): a Herbrand invariant
`I = (r_1, …, r_w)_ε^f` with `r_1 < ⋯ < r_w` is compatible with `e₀` if and only if `r_k` lies in
`𝓡_1^{e₀ ε p ^ (k - 1)}` for `1 ≤ k ≤ w`. -/
lemma isCompatible_iff_of_ram_lt (hI : ∀ j < I.w, I.ram j < I.ram (j + 1)) :
    I.IsCompatible e₀ ↔ ∀ k ∈ Icc 1 I.w, I.ram k ∈ possibleRamSet p 1 (e₀ * I.ε * p ^ (k - 1)) := by
  rw [isCompatible_iff_forall_mem_possibleRamSet, forall_mem_image]
  refine forall₂_congr fun k hk ↦ ?_
  rw [ramCountLT_ram_of_ram_lt hI (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1) (mem_Icc.mp hk).2,
    ramMultiplicity_ram_of_ram_lt hI (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1)
      (mem_Icc.mp hk).2]

/-- **Compatibility when all the rams are equal** (LMFDB `lf.rams`): a Herbrand invariant with tame
degree `1` whose `w ≥ 1` rams are all equal to `α` is compatible with `e₀` if and only if `α` lies
in `𝓡_w^{e₀}`. -/
lemma isCompatible_iff_of_forall_ram_eq (hw : I.w ≠ 0) (hε : I.ε = 1)
    (hram : ∀ k ∈ Icc 1 I.w, I.ram k = α) : I.IsCompatible e₀ ↔ α ∈ possibleRamSet p I.w e₀ := by
  have hmult : I.ramMultiplicity α = I.w := by
    rw [ramMultiplicity, filter_true_of_mem hram, Nat.card_Icc, Nat.add_sub_cancel]
  have hcount : I.ramCountLT α = 0 :=
    card_eq_zero.mpr <| filter_eq_empty_iff.mpr fun k hk ↦ (hram k hk).not_lt
  have h₁ : 1 ∈ Icc 1 I.w := mem_Icc.mpr ⟨le_rfl, Nat.one_le_iff_ne_zero.mpr hw⟩
  have hz : (e₀ : ℚ) * I.ε * p ^ I.ramCountLT α = e₀ := by
    rw [hcount, hε, Nat.cast_one, mul_one, pow_zero, mul_one]
  rw [isCompatible_iff_forall_mem_possibleRamSet, forall_mem_image]
  refine ⟨fun h ↦ ?_, fun h k hk ↦ ?_⟩
  · have h' : α ∈ possibleRamSet p (I.ramMultiplicity α) (e₀ * I.ε * p ^ I.ramCountLT α) :=
      hram 1 h₁ ▸ h h₁
    rwa [hmult, hz] at h'
  · rw [hram k hk, hmult, hz]
    exact h

end IsNonarchimedeanLocalField.HerbrandInvariant
