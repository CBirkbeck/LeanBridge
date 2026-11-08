import Mathlib.RingTheory.Radical.NatInt
import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Abc
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Radical.Ideal

/-!
# The modified Szpiro conjecture implies the abc conjecture

Tau Ceti proves that the abc conjecture implies the modified Szpiro conjecture
(`TauCeti.AbcConjecture.algorithmicModifiedSzpiroConjecture`) and that Szpiro's conjecture implies
the abc conjecture with exponent `3 / 2`
(`TauCeti.AlgorithmicSzpiroConjecture.abcConjectureWithExponent`). This file proves the converse
of the first, so the two conjectures are equivalent, as the LMFDB
knowl `ec.q.abc_quality` states (Oesterlé).

For coprime `a + b = c` the Frey curve `y² = x (x - a) (x + b)` has `c₄ = 16 (a² + a b + b²)` and
`a² + a b + b² = (a² + b² + c²) / 2 ≥ max (|a|, |b|, |c|)² / 2`. Its conductor is at most
`2¹¹ rad (a b c)` and its minimal model has `c₄` equal to that of the Frey equation, or to it
divided by `2⁴` after a reordering making the curve semistable at `2`; either way `|c₄| ≥ a² + a b
+ b²` (`TauCeti.exists_sq_add_mul_add_sq_le_abs_c₄_reducedMinimalModel`). So the modified Szpiro
bound `|c₄|³ ≪ N ^ (6 + 6 ε)` gives `max (|a|, |b|, |c|) ^ 6 ≪ rad (a b c) ^ (6 + 6 ε)`.

Two private lemmas of Tau Ceti's `TauCeti/AlgebraicGeometry/EllipticCurve/FreyCurve/Abc.lean` are
re-proved here, since private declarations cannot be used outside their module:
`exists_pair_of_sixteen_dvd`, with the extra invariant `A'² + A' B' + B'² = A² + A B + B²` of the
signed reordering, and the conductor half of `natAbs_sq_eq_and_absNorm_algorithmicConductor_le`.

The modified Szpiro conjecture is Tau Ceti's bound form, `max (|c₄|³, c₆²) ≤ C N ^ (6 + ε)`. The
LMFDB knowl `ec.q.szpiro_ratio` states it as the finiteness of the curves of Szpiro ratio above
`6 + ε`; the equivalence of the two forms is not proved here.

## Main results

* `TauCeti.exists_sq_add_mul_add_sq_le_abs_c₄_reducedMinimalModel`: for coprime `A`, `B` with
  `A B (A + B) ≠ 0`, some elliptic curve over `ℚ` has conductor at most `2¹¹ rad (A B (A + B))`
  and reduced minimal model with `|c₄| ≥ A² + A B + B²`.
* `TauCeti.AlgorithmicModifiedSzpiroConjecture.abcConjecture` (LMFDB `ec.q.abc_quality`): the
  modified Szpiro conjecture implies the abc conjecture.
* `TauCeti.abcConjecture_iff_algorithmicModifiedSzpiroConjecture` (LMFDB `ec.q.abc_quality`): the
  two are equivalent.

## References

* J. Oesterlé, *Nouvelles approches du « théorème » de Fermat*, Séminaire Bourbaki 694 (1988),
  Astérisque 161–162 (1988), 165–186.
-/

open WeierstrassCurve UniqueFactorizationMonoid

namespace TauCeti

lemma exists_pair_of_sixteen_dvd_mul_mul_add {A B : ℤ} (hAB : IsCoprime A B)
    (h16 : 16 ∣ A * B * (A + B)) : ∃ A' B' : ℤ, IsCoprime A' B' ∧ 4 ∣ A' + 1 ∧ 16 ∣ B' ∧
      A' * B' * (A' + B') = A * B * (A + B) ∧
        A' ^ 2 + A' * B' + B' ^ 2 = A ^ 2 + A * B + B ^ 2 := by
  have key {X Y : ℤ} (hXY : IsCoprime X Y) (hY : 16 ∣ Y) : ∃ A' B' : ℤ, IsCoprime A' B' ∧
      4 ∣ A' + 1 ∧ 16 ∣ B' ∧ A' * B' * (A' + B') = X * Y * (X + Y) ∧
        A' ^ 2 + A' * B' + B' ^ 2 = X ^ 2 + X * Y + Y ^ 2 := by
    have hX : ¬2 ∣ X := fun h2 ↦ Int.prime_two.not_dvd_one
      (hXY.isUnit_of_dvd' h2 (dvd_trans ⟨8, by norm_num⟩ hY)).dvd
    by_cases h4 : 4 ∣ X + 1
    · exact ⟨X, Y, hXY, h4, hY, rfl, rfl⟩
    · exact ⟨-(X + Y), Y, by simpa using (hXY.add_mul_left_left 1).neg_left, by omega, hY,
        by ring1, by ring1⟩
  have hodd {x : ℤ} (hx : ¬2 ∣ x) : IsCoprime (16 : ℤ) x :=
    (Int.prime_two.coprime_iff_not_dvd.mpr hx).pow_left (m := 4)
  have hnot : ¬(2 ∣ A ∧ 2 ∣ B) := fun hAB2 ↦
    Int.prime_two.not_dvd_one (hAB.isUnit_of_dvd' hAB2.1 hAB2.2).dvd
  by_cases hB : 2 ∣ B
  · have hA : ¬2 ∣ A := fun hA ↦ hnot ⟨hA, hB⟩
    have h16A : IsCoprime (16 : ℤ) (A * (A + B)) := hodd (by rw [Int.prime_two.dvd_mul]; omega)
    exact key hAB (h16A.dvd_of_dvd_mul_left (by convert h16 using 1; ring1))
  by_cases hA : 2 ∣ A
  · rcases key hAB.symm <| (hodd (x := B * (A + B)) (by
      rw [Int.prime_two.dvd_mul]; omega)).dvd_of_dvd_mul_left (by convert h16 using 1; ring1) with
      ⟨A', B', h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨A', B', h₁, h₂, h₃, by rw [h₄]; ring1, by rw [h₅]; ring1⟩
  · have hcop : IsCoprime A (-(B + A)) := by
      simpa using (hAB.add_mul_left_right 1).neg_right
    rcases key hcop <| dvd_neg.2 ((hodd (x := A * B) (by
      rw [Int.prime_two.dvd_mul]; omega)).dvd_of_dvd_mul_left (add_comm A B ▸ h16)) with
      ⟨A', B', h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨A', B', h₁, h₂, h₃, by rw [h₄]; ring1, by rw [h₅]; ring1⟩

lemma absNorm_algorithmicConductor_freyCurve_le {A B : ℤ} (hAB : IsCoprime A B) (hA : 4 ∣ A + 1)
    (hB : 16 ∣ B) (hP : A * B * (A + B) ≠ 0) [((freyCurve A B).baseChange ℚ).IsElliptic] :
    Ideal.absNorm (algorithmicConductor ℤ ((freyCurve A B).baseChange ℚ)) ≤
      radical (A * B * (A + B)).natAbs := by
  rcases (show (2 : ℤ) ^ 8 ∣ (A * B * (A + B)) ^ 2 by
    rw [show (2 : ℤ) ^ 8 = 16 ^ 2 by norm_num]
    exact pow_dvd_pow_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hB A) _) 2) with ⟨d, hd⟩
  have hd₂ : Ideal.span {d} ∣ Ideal.span {A * B * (A + B)} ^ 2 := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨2 ^ 8, by rw [hd]; ring1⟩
  have hN : algorithmicConductor ℤ ((freyCurve A B).baseChange ℚ) ∣
      Ideal.span {radical (A * B * (A + B))} := by
    rw [(isSemistable_iff_algorithmicConductor_eq_radical _).1
      (isSemistable_freyCurve (F := ℚ) hA hB hAB),
      minimalDiscriminantIdeal_freyCurve hA hB hAB (by rw [← hd]; ring1), ← radical_span_singleton]
    exact (radical_dvd_radical hd₂ (pow_ne_zero 2 (by simpa using hP))).trans
      (radical_pow _ two_ne_zero).dvd
  have hle : Ideal.absNorm (algorithmicConductor ℤ ((freyCurve A B).baseChange ℚ)) ≤
      (radical (A * B * (A + B))).natAbs :=
    Int.absNorm_le_natAbs_of_dvd_span_singleton radical_ne_zero hN
  rwa [← Int.radical_natAbs_eq_radical, Int.natAbs_natCast] at hle

lemma c₄_reducedMinimalModel_eq_of_isGlobalMinimal {E W : WeierstrassCurve ℚ} [E.IsElliptic]
    [W.IsElliptic] (hW : IsGlobalMinimal ℤ W) {D : VariableChange ℚ} (hD : D • E = W) :
    (reducedMinimalModel E).c₄ = W.c₄ := by
  rcases exists_smul_eq_reducedMinimalModel E with ⟨C, hC⟩
  have hCD : (C * D⁻¹) • W = reducedMinimalModel E := by rw [mul_smul, ← hD, inv_smul_smul, hC]
  rcases hW.exists_baseChange_eq_of_smul_eq (isReducedMinimal_reducedMinimalModel E).isGlobalMinimal
    _ hCD with ⟨C₀, hC₀⟩
  rw [← hCD, variableChange_c₄, ← hC₀]
  rcases Int.units_eq_one_or C₀.u with hu | hu <;>
    norm_num [VariableChange.baseChange, hu]

/-- **Some elliptic curve of a coprime pair has small conductor and large `c₄`.** For coprime
integers `A` and `B` with `A B (A + B) ≠ 0` there is an elliptic curve `E` over `ℚ`, the Frey curve
of `A` and `B` or of a reordering of `A`, `B`, `-(A + B)` with signs changed, whose algorithmic
conductor has norm at most `2¹¹ rad (A B (A + B))` and whose reduced minimal model has
`|c₄| ≥ A² + A B + B²`. -/
lemma exists_sq_add_mul_add_sq_le_abs_c₄_reducedMinimalModel {A B : ℤ} (hAB : IsCoprime A B)
    (hP : A * B * (A + B) ≠ 0) : ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic),
      Ideal.absNorm (algorithmicConductor ℤ E) ≤ 2 ^ 11 * radical (A * B * (A + B)).natAbs ∧
        ((A ^ 2 + A * B + B ^ 2 : ℤ) : ℚ) ≤ |(reducedMinimalModel E).c₄| := by
  by_cases h16 : 16 ∣ A * B * (A + B)
  · -- the semistable case: the model at `2` has `c₄ = A'² + A' B' + B'² = A² + A B + B²`
    rcases exists_pair_of_sixteen_dvd_mul_mul_add hAB h16 with ⟨A', B', hAB', hA', hB', hprod, hc⟩
    rcases hA' with ⟨α, hα⟩
    rcases hB' with ⟨β, rfl⟩
    rcases (show A' = 4 * α - 1 by omega) with rfl
    have hP' : (4 * α - 1) * (16 * β) * (4 * α - 1 + 16 * β) ≠ 0 := hprod ▸ hP
    have : ((freyCurve (4 * α - 1) (16 * β)).baseChange ℚ).IsElliptic :=
      isElliptic_baseChange_freyCurve hP'
    have hE : (⟨Units.mk0 2 two_ne_zero, 0, 1, 0⟩ : VariableChange ℚ) •
        (freyCurve (4 * α - 1) (16 * β)).baseChange ℚ = (freyCurveModel α β).baseChange ℚ := by
      simpa [baseChange] using smul_freyCurve_eq_freyCurveModel two_ne_zero (α : ℚ) β
    have : ((freyCurveModel α β).baseChange ℚ).IsElliptic := hE ▸ inferInstance
    refine ⟨(freyCurve (4 * α - 1) (16 * β)).baseChange ℚ, inferInstance, ?_, ?_⟩
    · rw [← hprod]
      exact (absNorm_algorithmicConductor_freyCurve_le hAB' ⟨α, hα⟩ ⟨β, rfl⟩ hP').trans
        (Nat.le_mul_of_pos_left _ (by norm_num))
    · rw [c₄_reducedMinimalModel_eq_of_isGlobalMinimal
        (isGlobalMinimal_baseChange_freyCurveModel hAB') hE, ← hc]
      simp only [baseChange, map_c₄, freyCurveModel_c₄]
      push_cast
      exact le_abs_self _
  · -- the minimal case: the Frey equation is globally minimal, with `c₄ = 16 (A² + A B + B²)`
    have : ((freyCurve A B).baseChange ℚ).IsElliptic := isElliptic_baseChange_freyCurve hP
    refine ⟨(freyCurve A B).baseChange ℚ, inferInstance, ?_, ?_⟩
    · have hle : Ideal.absNorm (algorithmicConductor ℤ ((freyCurve A B).baseChange ℚ)) ≤
          (2 ^ 11 * radical (A * B * (A + B))).natAbs :=
        Int.absNorm_le_natAbs_of_dvd_span_singleton (by simp)
          (algorithmicConductor_freyCurve_dvd hAB h16)
      rwa [Int.natAbs_mul, ← Int.radical_natAbs_eq_radical, Int.natAbs_natCast] at hle
    · rw [c₄_reducedMinimalModel_eq_of_isGlobalMinimal
        (isGlobalMinimal_baseChange_freyCurve hAB h16) (one_smul _ _)]
      simp only [baseChange, map_c₄, freyCurve_c₄]
      push_cast
      have hx : (0 : ℚ) ≤ A ^ 2 + A * B + B ^ 2 := by
        nlinarith [sq_nonneg ((A : ℚ) + B), sq_nonneg (A : ℚ), sq_nonneg (B : ℚ)]
      exact (le_mul_of_one_le_left hx (by norm_num)).trans (le_abs_self _)

/-- **The modified Szpiro conjecture implies the abc conjecture** (Oesterlé). For coprime positive
integers `a + b = c`, the curve of `TauCeti.exists_sq_add_mul_add_sq_le_abs_c₄_reducedMinimalModel`
has `c² ≤ 2 (a² + a b + b²) ≤ 2 |c₄|` and conductor `N ≤ 2¹¹ rad (a b c)`, so the modified Szpiro
bound `|c₄|³ ≤ K N ^ (6 + 6 ε)` gives `c⁶ ≪ rad (a b c) ^ (6 + 6 ε)`. -/
lemma AlgorithmicModifiedSzpiroConjecture.abcConjecture (h : AlgorithmicModifiedSzpiroConjecture) :
    AbcConjecture := by
  refine abcConjecture_iff_nat.2 fun ε hε ↦ ?_
  rcases h (6 * ε) (by positivity) with ⟨K, hK⟩
  refine ⟨(8 * max K 0 * (2 ^ 11 : ℝ) ^ (6 + 6 * ε)) ^ (1 / 6 : ℝ), fun a b c ha hb hab habc ↦ ?_⟩
  rcases exists_sq_add_mul_add_sq_le_abs_c₄_reducedMinimalModel (A := a) (B := b)
    (Nat.Coprime.isCoprime hab) (by positivity) with ⟨E, _, hN, hc₄⟩
  rw [← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_mul, Int.natAbs_natCast, habc] at hN
  have h6 : (0 : ℝ) ≤ 6 + 6 * ε := by positivity
  have hR : (0 : ℝ) ≤ ((radical (a * b * c) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN' : (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ (6 + 6 * ε) ≤
      (2 ^ 11 * ((radical (a * b * c) : ℕ) : ℝ)) ^ (6 + 6 * ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hN) h6
  -- `c² ≤ 2 (a² + a b + b²)` and `a² + a b + b² ≤ |c₄|`
  have hc : (c : ℝ) ^ 2 ≤ 2 * ((a : ℝ) ^ 2 + a * b + b ^ 2) := by
    rw [← habc, Nat.cast_add]
    nlinarith [sq_nonneg (a : ℝ), sq_nonneg (b : ℝ)]
  have hc₄' : (a : ℝ) ^ 2 + a * b + b ^ 2 ≤ |((reducedMinimalModel E).c₄ : ℝ)| :=
    mod_cast hc₄
  have hc6 : (c : ℝ) ^ 6 ≤ 8 * |((reducedMinimalModel E).c₄ : ℝ)| ^ 3 := by
    have h1 : ((c : ℝ) ^ 2) ^ 3 ≤ (2 * ((a : ℝ) ^ 2 + a * b + b ^ 2)) ^ 3 :=
      pow_le_pow_left₀ (sq_nonneg _) hc 3
    have h2 : ((a : ℝ) ^ 2 + a * b + b ^ 2) ^ 3 ≤ |((reducedMinimalModel E).c₄ : ℝ)| ^ 3 :=
      pow_le_pow_left₀ (by positivity) hc₄' 3
    rw [← pow_mul, mul_pow] at h1
    norm_num at h1
    linarith
  -- so `c⁶ ≤ 8 K N ^ (6 + 6 ε) ≤ (C rad (a b c) ^ (1 + ε))⁶`
  have hC6 : ((8 * max K 0 * (2 ^ 11 : ℝ) ^ (6 + 6 * ε)) ^ (1 / 6 : ℝ)) ^ 6 =
      8 * max K 0 * (2 ^ 11 : ℝ) ^ (6 + 6 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hR6 : (((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)) ^ 6 =
      ((radical (a * b * c) : ℕ) : ℝ) ^ (6 + 6 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    congr 1
    push_cast
    ring1
  have hKN : K * (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ (6 + 6 * ε) ≤ max K 0 *
      ((2 ^ 11 : ℝ) ^ (6 + 6 * ε) * ((radical (a * b * c) : ℕ) : ℝ) ^ (6 + 6 * ε)) := by
    rw [← Real.mul_rpow (by norm_num) hR]
    exact mul_le_mul (le_max_left K 0) hN' (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (le_max_right K 0)
  refine (pow_le_pow_iff_left₀ (Nat.cast_nonneg c) (by positivity) (by norm_num : 6 ≠ 0)).1 ?_
  rw [mul_pow, hC6, hR6]
  refine hc6.trans ((mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (hK E))
    (by norm_num)).trans ?_)
  linarith

/-- **The abc conjecture and the modified Szpiro conjecture are equivalent** (Oesterlé; LMFDB
`ec.q.abc_quality`), the modified Szpiro conjecture being stated against the conductor of Tate's
algorithm. -/
lemma abcConjecture_iff_algorithmicModifiedSzpiroConjecture :
    AbcConjecture ↔ AlgorithmicModifiedSzpiroConjecture :=
  ⟨AbcConjecture.algorithmicModifiedSzpiroConjecture,
    AlgorithmicModifiedSzpiroConjecture.abcConjecture⟩

end TauCeti
