import LeanBridge.ForMathlib.NumberTheory.LocalField.HerbrandInvariantCompatibility

/-!
# A compatible Herbrand invariant is admissible

Let `I = (r_1, …, r_w)_ε^f` be a Herbrand invariant at a prime `p`, with means `m_k`, and `e₀` a
natural number, the valuation of `p` in the base field. LMFDB `lf.herbrand_invariant` calls `I`
compatible with `e₀` (`IsNonarchimedeanLocalField.HerbrandInvariant.IsCompatible`) if each distinct
ram `b`, of multiplicity `d` and with `c` rams smaller than it, is geometric (`(p ^ d - 1) b` is an
integer prime to `p` and `b < p ^ (c + 1) ε e₀ / (p - 1)`) or arithmetic (`d = 1` and
`b = p ^ (c + 1) ε e₀ / (p - 1)`). The Herbrand invariants of the extensions of a `p`-adic field
are admissible (`IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible`, Monge's conditions at
the vertices of the ramification polygon), and an admissible invariant is compatible
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible.isCompatible`).

This file proves the converse: a compatible invariant is admissible. So compatibility, which is
stated in terms of the rams alone, is equivalent to the conditions under which Monge's
semicanonical polynomials have the ramification polygon of `I`, and it is sufficient for `I` to be
the Herbrand invariant of an extension (LMFDB `lf.rams`).

Write `e = ε p ^ w`. A vertex `k ≥ 1` of `I` ends the block `r_{c + 1} = ⋯ = r_{c + d} = b` of its
ram `b = r_k`, so `k = c + d`, and `c` is a vertex. Since
`e m_{c + d} - e m_c = p ^ (w - c - d) (p ^ d - 1) b`, induction over the vertices gives
`e m_k = p ^ (w - k) (p ^ d B + N)` with `e m_c = p ^ (w - c) B` and `N = (p ^ d - 1) b`, a natural
number, which is prime to `p` when `b` is geometric. So at a geometric vertex `e m_k` is an integer
of index `k`, and its small ram `r_k^* = (p - 1) b / (ε p ^ k)` is not an integer, while at an
arithmetic vertex `r_k^* = e₀`.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.IsCompatible.exists_mul_mean_eq` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.IsCompatible.exists_mul_mean_eq_of_isGeometricRam`:
  the divisibility of `e m_k` at the vertices of a compatible invariant.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsCompatible.isAdmissible` (LMFDB `lf.rams`,
  `lf.herbrand_invariant`): a compatible Herbrand invariant is admissible.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isAdmissible_iff_isCompatible`: admissibility and
  compatibility are equivalent.

## References

* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, Lemma 2 and §2.2.
-/

open Finset

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} {I : HerbrandInvariant p} {e₀ k : ℕ} {b : ℚ}

lemma IsGeometricRam.not_dvd_of_pow_sub_one_mul_eq (hg : I.IsGeometricRam e₀ b) {N : ℕ}
    (hN : ((p : ℚ) ^ I.ramMultiplicity b - 1) * b = N) : ¬p ∣ N := by
  refine fun hdvd ↦ hg.2.2.1 ?_
  rw [hN, Rat.num_natCast]
  exact Int.natCast_dvd_natCast.mpr hdvd

variable [Fact p.Prime]

lemma IsCompatible.exists_pow_ramMultiplicity_sub_one_mul_eq (h : I.IsCompatible e₀)
    (hb : b ∈ (Icc 1 I.w).image I.ram) : ∃ N : ℕ, ((p : ℚ) ^ I.ramMultiplicity b - 1) * b = N := by
  have hp₁ : (0 : ℚ) < p - 1 := sub_pos.mpr one_lt_natCast_prime
  rcases h b hb with ⟨-, hden, -, -⟩ | ⟨-, hd, heq⟩
  · have hb₀ : 0 ≤ b := (I.pos_of_mem_image_ram hb).le
    exact exists_natCast_of_den_eq_one (mul_nonneg (sub_nonneg.mpr <|
      one_le_pow₀ one_le_natCast_prime) hb₀) hden
  · have heq' : b = p ^ (I.ramCountLT b + 1) * I.ε * e₀ / (p - 1) := heq
    rw [eq_div_iff hp₁.ne'] at heq'
    refine ⟨p ^ (I.ramCountLT b + 1) * I.ε * e₀, ?_⟩
    rw [hd, pow_one, mul_comm, heq']
    push_cast
    rfl

private lemma mul_mean_eq_of_isVertex (hk : k ≤ I.w) (hv : I.IsVertex k) {B N : ℕ}
    (hB : (I.ramificationIndex : ℚ) * I.mean (I.ramCountLT (I.ram k)) =
      p ^ (I.w - I.ramCountLT (I.ram k)) * B)
    (hN : ((p : ℚ) ^ I.ramMultiplicity (I.ram k) - 1) * I.ram k = N) : (I.ramificationIndex : ℚ) *
    I.mean k = p ^ (I.w - k) * (p ^ I.ramMultiplicity (I.ram k) * B + N : ℕ) := by
  have hcd : I.ramCountLT (I.ram k) + I.ramMultiplicity (I.ram k) = k :=
    hv.ramCountLT_add_ramMultiplicity hk
  have hblock : (I.ramificationIndex : ℚ) *
      I.mean (I.ramCountLT (I.ram k) + I.ramMultiplicity (I.ram k)) -
        I.ramificationIndex * I.mean (I.ramCountLT (I.ram k)) =
      p ^ (I.w - (I.ramCountLT (I.ram k) + I.ramMultiplicity (I.ram k))) *
        ((p ^ I.ramMultiplicity (I.ram k) - 1) * I.ram k) :=
    I.mul_mean_add_sub_mul_mean (by omega) fun _ ↦ I.ram_eq_of_ramCountLT_lt
  have hpow : (p : ℚ) ^ (I.w - I.ramCountLT (I.ram k)) =
      p ^ (I.w - k) * p ^ I.ramMultiplicity (I.ram k) := by
    rw [← pow_add, (by omega : I.w - k + I.ramMultiplicity (I.ram k) =
      I.w - I.ramCountLT (I.ram k))]
  rw [hcd] at hblock
  push_cast
  linear_combination hblock + hB + (p : ℚ) ^ (I.w - k) * hN + (B : ℚ) * hpow

/-- **The means at the vertices of a compatible invariant are multiples of powers of `p`**: if `I`
is compatible with `e₀` and `k` is a vertex, then `e m_k` is a natural number divisible by
`p ^ (w - k)`. -/
lemma IsCompatible.exists_mul_mean_eq (h : I.IsCompatible e₀) (hk : k ≤ I.w) (hv : I.IsVertex k) :
    ∃ B : ℕ, (I.ramificationIndex : ℚ) * I.mean k = p ^ (I.w - k) * B := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · exact ⟨0, by rw [I.mean_zero, mul_zero, Nat.cast_zero, mul_zero]⟩
    · have hb : I.ram k ∈ (Icc 1 I.w).image I.ram := ram_mem_image hk₀.ne' hk
      have hcd : I.ramCountLT (I.ram k) + I.ramMultiplicity (I.ram k) = k :=
        hv.ramCountLT_add_ramMultiplicity hk
      have hd : 0 < I.ramMultiplicity (I.ram k) := I.ramMultiplicity_pos hb
      rcases ih _ (by omega) (by omega) (I.isVertex_ramCountLT hb) with ⟨B, hB⟩
      rcases h.exists_pow_ramMultiplicity_sub_one_mul_eq hb with ⟨N, hN⟩
      exact ⟨_, mul_mean_eq_of_isVertex hk hv hB hN⟩

/-- **The means at the geometric vertices of a compatible invariant**: if `I` is compatible with
`e₀`, and `k ≥ 1` is a vertex whose ram `r_k` is geometric, then `e m_k` is a natural number exactly
divisible by `p ^ (w - k)`. -/
lemma IsCompatible.exists_mul_mean_eq_of_isGeometricRam (h : I.IsCompatible e₀) (hk₀ : k ≠ 0)
    (hk : k ≤ I.w) (hv : I.IsVertex k) (hg : I.IsGeometricRam e₀ (I.ram k)) :
    ∃ A : ℕ, (I.ramificationIndex : ℚ) * I.mean k = p ^ (I.w - k) * A ∧ ¬p ∣ A := by
  have hb : I.ram k ∈ (Icc 1 I.w).image I.ram := ram_mem_image hk₀ hk
  have hcd : I.ramCountLT (I.ram k) + I.ramMultiplicity (I.ram k) = k :=
    hv.ramCountLT_add_ramMultiplicity hk
  have hd : 0 < I.ramMultiplicity (I.ram k) := I.ramMultiplicity_pos hb
  rcases h.exists_mul_mean_eq (by omega) (I.isVertex_ramCountLT hb) with ⟨B, hB⟩
  rcases h.exists_pow_ramMultiplicity_sub_one_mul_eq hb with ⟨N, hN⟩
  exact ⟨_, mul_mean_eq_of_isVertex hk hv hB hN, fun hA ↦ hg.not_dvd_of_pow_sub_one_mul_eq hN <|
    (Nat.dvd_add_right <| (dvd_pow_self p hd.ne').mul_right B).mp hA⟩

lemma IsArithmeticRam.smallRam_eq (ha : I.IsArithmeticRam e₀ (I.ram k)) (hk : k ≤ I.w)
    (hv : I.IsVertex k) : I.smallRam k = e₀ := by
  have hp₀ : (p : ℚ) ≠ 0 := natCast_prime_pos.ne'
  have hp₁ : (p : ℚ) - 1 ≠ 0 := (sub_pos.mpr one_lt_natCast_prime).ne'
  have hε : (I.ε : ℚ) ≠ 0 := I.natCast_ε_pos.ne'
  have hcd : I.ramCountLT (I.ram k) + I.ramMultiplicity (I.ram k) = k :=
    hv.ramCountLT_add_ramMultiplicity hk
  have hd : I.ramMultiplicity (I.ram k) = 1 := ha.2.1
  have heq : I.ram k = p ^ (I.ramCountLT (I.ram k) + 1) * I.ε * e₀ / (p - 1) := ha.2.2
  rw [(by omega : I.ramCountLT (I.ram k) + 1 = k), eq_div_iff hp₁] at heq
  rw [smallRam, mul_comm, heq]
  field_simp

lemma IsGeometricRam.den_smallRam_ne_one (hg : I.IsGeometricRam e₀ (I.ram k)) (hk₀ : k ≠ 0) :
    (I.smallRam k).den ≠ 1 := by
  intro hd
  have hden : (I.ε : ℚ) * p ^ k ≠ 0 := (mul_pos I.natCast_ε_pos <| pow_pos natCast_prime_pos k).ne'
  rcases exists_natCast_of_den_eq_one (I.smallRam_nonneg k) hd with ⟨z, hz⟩
  rw [smallRam, div_eq_iff hden] at hz
  have hG : (∑ i ∈ range (I.ramMultiplicity (I.ram k)), (p : ℚ) ^ i) * (p - 1) =
      p ^ I.ramMultiplicity (I.ram k) - 1 :=
    geom_sum_mul _ _
  have hN : ((p : ℚ) ^ I.ramMultiplicity (I.ram k) - 1) * I.ram k =
      ((∑ i ∈ range (I.ramMultiplicity (I.ram k)), p ^ i) * z * I.ε * p ^ k : ℕ) := by
    push_cast
    linear_combination (∑ i ∈ range (I.ramMultiplicity (I.ram k)), (p : ℚ) ^ i) * hz -
      I.ram k * hG
  exact hg.not_dvd_of_pow_sub_one_mul_eq hN <| (dvd_pow_self p hk₀).mul_left _

/-- **A compatible Herbrand invariant is admissible** (LMFDB `lf.rams`, `lf.herbrand_invariant`): if
every distinct ram `b` of `I = (r_1, …, r_w)_ε^f`, of multiplicity `d` and with `c` rams smaller
than it, is geometric (`(p ^ d - 1) b` is an integer prime to `p` and
`b < p ^ (c + 1) ε e₀ / (p - 1)`) or arithmetic (`d = 1` and `b = p ^ (c + 1) ε e₀ / (p - 1)`), then
`I` satisfies Monge's conditions at the vertices of its ramification polygon: the small rams are at
most `e₀`, an integral small ram at a vertex is `e₀`, and at the other vertices `k` the number
`e m_k` is an integer of index `k`. -/
lemma IsCompatible.isAdmissible (h : I.IsCompatible e₀) : I.IsAdmissible e₀ where
  smallRam_le {k} hk := by
    have hp₁ : (0 : ℚ) < p - 1 := sub_pos.mpr one_lt_natCast_prime
    have hε : (0 : ℚ) < I.ε := I.natCast_ε_pos
    have hden : (0 : ℚ) < I.ε * p ^ (k + 1) := mul_pos hε <| pow_pos natCast_prime_pos _
    have hb : I.ram (k + 1) ∈ (Icc 1 I.w).image I.ram := ram_mem_image k.succ_ne_zero hk
    have hc : I.ramCountLT (I.ram (k + 1)) + 1 ≤ k + 1 := Nat.succ_le_of_lt <| not_le.mp <|
      (I.ram_lt_iff_le_ramCountLT (Nat.le_add_left 1 k) hk).not.mp (lt_irrefl _)
    have hpow : (p : ℚ) ^ (I.ramCountLT (I.ram (k + 1)) + 1) ≤ p ^ (k + 1) :=
      pow_le_pow_right₀ one_le_natCast_prime hc
    have hle : I.ram (k + 1) ≤ p ^ (I.ramCountLT (I.ram (k + 1)) + 1) * I.ε * e₀ / (p - 1) := by
      rcases h _ hb with hg | ha
      · exact hg.2.2.2.le
      · exact ha.2.2.le
    rw [le_div_iff₀ hp₁] at hle
    rw [smallRam, div_le_iff₀ hden]
    linarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hε.le (Nat.cast_nonneg e₀))]
  smallRam_eq {k} hk hv hd := by
    rcases h _ (ram_mem_image k.succ_ne_zero hk) with hg | ha
    · exact absurd hd (hg.den_smallRam_ne_one k.succ_ne_zero)
    · exact ha.smallRam_eq hk hv
  exists_pointIndex_eq {k} hk hv hd := by
    rcases h _ (ram_mem_image k.succ_ne_zero hk) with hg | ha
    · rcases h.exists_mul_mean_eq_of_isGeometricRam k.succ_ne_zero hk hv hg with ⟨A, hA, hpA⟩
      have he : p ^ (I.w - (k + 1)) ∣ I.ramificationIndex :=
        (pow_dvd_pow p (Nat.sub_le _ _)).mul_left _
      have he' : p ^ (I.w - (k + 1) + 1) ∣ I.ramificationIndex :=
        (pow_dvd_pow p (by omega)).mul_left _
      have hdvd : p ^ (I.w - (k + 1)) ∣ p ^ (I.w - (k + 1)) * A % I.ramificationIndex :=
        (Nat.dvd_mod_iff he).mpr (dvd_mul_right _ _)
      have hndvd : ¬p ^ (I.w - (k + 1) + 1) ∣ p ^ (I.w - (k + 1)) * A % I.ramificationIndex :=
        fun hdvd' ↦ hpA <| (Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : p.Prime).pos _)).mp <|
          pow_succ p _ ▸ (Nat.dvd_mod_iff he').mp hdvd'
      have hi₀ : p ^ (I.w - (k + 1)) * A % I.ramificationIndex ≠ 0 :=
        fun h₀ ↦ hndvd (h₀ ▸ dvd_zero _)
      have hval : padicValNat p (p ^ (I.w - (k + 1)) * A % I.ramificationIndex) = I.w - (k + 1) :=
        ((padicValNat_dvd_iff_le hi₀).mp hdvd).antisymm' <| Nat.le_of_lt_succ <| not_le.mp
          fun hle ↦ hndvd <| (padicValNat_dvd_iff_le hi₀).mpr hle
      refine ⟨p ^ (I.w - (k + 1)) * A, by rw [hA, Nat.cast_mul, Nat.cast_pow], ?_⟩
      rw [pointIndex, padicValNat_gcd_pow hi₀, hval, min_eq_left (Nat.sub_le _ _)]
      omega
    · rw [ha.smallRam_eq hk hv] at hd
      exact absurd (Rat.den_natCast e₀) hd

variable (I e₀) in
/-- **Admissibility and compatibility are equivalent**: a Herbrand invariant satisfies Monge's
conditions at the vertices of its ramification polygon, for `e₀ = v(p)`, if and only if each of its
distinct rams is geometric or arithmetic in the sense of LMFDB `lf.herbrand_invariant`. -/
lemma isAdmissible_iff_isCompatible : I.IsAdmissible e₀ ↔ I.IsCompatible e₀ :=
  ⟨IsAdmissible.isCompatible, IsCompatible.isAdmissible⟩

end IsNonarchimedeanLocalField.HerbrandInvariant
