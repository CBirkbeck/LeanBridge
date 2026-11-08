import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor

/-!
# The exponent of the conductor at additive reduction away from `2` and `3`

Tau Ceti's `WeierstrassCurve.algorithmicOggExponent` is the exponent `f = v(Δ_min) − m + 1` read off
Tate's algorithm, `m` being the number of components of the reduction symbol at which the algorithm
stops. It is `0` at good, `1` at multiplicative and at least `2` at additive reduction. This file
proves that it is exactly `2` at additive reduction when the residue characteristic is neither `2`
nor `3` (Silverman, *Advanced Topics*, IV.9 and the table of IV.9.4): at every additive symbol the
discriminant of the equation on which the algorithm stops has valuation exactly `m + 1`.

Writing `ϖ` for the uniformiser, the stopping conditions express the discriminant
`Δ = -b₂² b₈ - 8 b₄³ - 27 b₆² + 9 b₂ b₄ b₆` as `ϖ ^ (m + 1) (u + ϖ y)` with `u` a unit times a
power of `2` or `3`: `u = -27 · 16 a₆'²` at `II`, `-8 b₄'³` at `III` and `III*`, `-27 b₆'²` at `IV`,
`IV*` and `II*`, sixteen times the discriminant of the residue cubic at `I₀*`, and, at `Iₙ*`,
`-b₂'³ b₆'` at an odd stage (for `4 Δ`) and `b₂'² (a₄'² - 4 a₂' a₆')` at an even stage, the primes
denoting the coefficients divided by the powers of `ϖ` the stopping conditions provide.

## Main results

* `WeierstrassCurve.IsTateTerminal.not_pow_componentCount_add_two_dvd_Δ`: at an additive symbol
  with `m` components, `ϖ ^ (m + 2)` does not divide the discriminant when `ϖ` divides neither `2`
  nor `3`.
* `WeierstrassCurve.algorithmicOggExponent_eq_two`: the algorithmic Ogg exponent is `2` at additive
  reduction when `2` and `3` are units.
* `WeierstrassCurve.count_algorithmicConductor_eq_two` (LMFDB `ec.conductor_valuation`,
  `ec.conductor`): the exponent of a prime not above `2` or `3` in the algorithmic conductor is `2`
  at additive reduction.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

open IsDedekindDomain IsDiscreteValuationRing IsLocalRing TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] {ϖ : R}

lemma not_dvd_of_not_pow_succ_dvd_pow_mul {a : R} {k : ℕ} (h : ¬ϖ ^ (k + 1) ∣ ϖ ^ k * a) : ¬ϖ ∣ a :=
  fun ha ↦ h <| pow_succ ϖ k ▸ mul_dvd_mul_left (ϖ ^ k) ha

variable [IsDomain R]

lemma not_pow_succ_dvd_of_pow_succ_dvd_sub {x u : R} (hϖ : Prime ϖ) (k : ℕ)
    (hx : ϖ ^ (k + 1) ∣ x - ϖ ^ k * u) (hu : ¬ϖ ∣ u) : ¬ϖ ^ (k + 1) ∣ x := by
  rintro ⟨z, rfl⟩
  rcases hx with ⟨y, hy⟩
  exact hu ⟨z - y, mul_left_cancel₀ (pow_ne_zero k hϖ.ne_zero) <| by linear_combination -hy⟩

/-- **At an additive symbol the discriminant has valuation exactly `m + 1` away from `2` and `3`**:
if Tate's algorithm stops on `W` at a symbol other than `Iₙ`, with `m` components, and the prime
`ϖ` divides neither `2` nor `3`, then `ϖ ^ (m + 2)` does not divide `Δ`. Together with
`WeierstrassCurve.IsTateTerminal.pow_componentCount_add_one_dvd_Δ` this is the table
`v(Δ) = 2, 3, 4, 6, 6 + n, 8, 9, 10` at `II, III, IV, I₀*, Iₙ*, IV*, III*, II*`. -/
lemma IsTateTerminal.not_pow_componentCount_add_two_dvd_Δ {W : WeierstrassCurve R} (hϖ : Prime ϖ)
    (h2 : ¬ϖ ∣ 2) (h3 : ¬ϖ ∣ 3) {s : ReductionSymbol} (h : W.IsTateTerminal ϖ s)
    (hs : ∀ n, s ≠ .I n) : ¬ϖ ^ (s.componentCount + 2) ∣ W.Δ := by
  have hmul {a b : R} (ha : ¬ϖ ∣ a) (hb : ¬ϖ ∣ b) : ¬ϖ ∣ a * b :=
    fun hab ↦ (hϖ.dvd_or_dvd hab).elim ha hb
  have hpow {a : R} (n : ℕ) (ha : ¬ϖ ∣ a) : ¬ϖ ∣ a ^ n := fun hn ↦ ha (hϖ.dvd_of_dvd_pow hn)
  match s, h with
  | .I n, _ => exact absurd rfl (hs n)
  | .II, ⟨⟨B₂, hB₂⟩, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, hn⟩ =>
    have hA₆ : ¬ϖ ∣ A₆ := not_dvd_of_not_pow_succ_dvd_pow_mul (k := 1) <| by rwa [pow_one, ← h₆]
    refine not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ 2 (u := -(2 ^ 4 * 3 ^ 3 * A₆ ^ 2))
      ⟨-27 * (ϖ * A₃ ^ 4 + 8 * A₃ ^ 2 * A₆) - B₂ ^ 2 * (W.a₁ ^ 2 * A₆ + 4 * W.a₂ * A₆ -
        ϖ * W.a₁ * A₃ * A₄ + ϖ * W.a₂ * A₃ ^ 2 - ϖ * A₄ ^ 2) - 8 * (2 * A₄ + W.a₁ * A₃) ^ 3 +
        9 * B₂ * (2 * A₄ + W.a₁ * A₃) * (ϖ * A₃ ^ 2 + 4 * A₆), ?_⟩ ?_
    · rw [Δ, hB₂, b₄, b₆, b₈, h₃, h₄, h₆]
      ring1
    · exact dvd_neg.not.mpr <| hmul (hmul (hpow 4 h2) (hpow 3 h3)) (hpow 2 hA₆)
  | .III, ⟨⟨B₂, hB₂⟩, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, hn⟩ =>
    have hb₈ : W.b₈ = ϖ ^ 2 * (W.a₁ ^ 2 * A₆ + 4 * W.a₂ * A₆ - W.a₁ * A₃ * A₄ + W.a₂ * A₃ ^ 2 -
        A₄ ^ 2) := by
      rw [b₈, h₃, h₄, h₆]
      ring1
    have hB₈ : ¬ϖ ∣ W.a₁ ^ 2 * A₆ + 4 * W.a₂ * A₆ - W.a₁ * A₃ * A₄ + W.a₂ * A₃ ^ 2 - A₄ ^ 2 :=
      not_dvd_of_not_pow_succ_dvd_pow_mul (hb₈ ▸ hn)
    have hrel : (2 * A₄ + W.a₁ * A₃) ^ 2 + 2 ^ 2 * (W.a₁ ^ 2 * A₆ + 4 * W.a₂ * A₆ -
        W.a₁ * A₃ * A₄ + W.a₂ * A₃ ^ 2 - A₄ ^ 2) = ϖ * (B₂ * (A₃ ^ 2 + 4 * A₆)) := by
      rw [b₂] at hB₂
      linear_combination (A₃ ^ 2 + 4 * A₆) * hB₂
    have hB₄ : ¬ϖ ∣ 2 * A₄ + W.a₁ * A₃ := fun hB ↦ hmul (hpow 2 h2) hB₈ <|
      (dvd_add_right (dvd_pow hB two_ne_zero)).mp (hrel ▸ dvd_mul_right ϖ _)
    refine not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ 3 (u := -(2 ^ 3 * (2 * A₄ + W.a₁ * A₃) ^ 3))
      ⟨-(B₂ ^ 2 * (W.a₁ ^ 2 * A₆ + 4 * W.a₂ * A₆ - W.a₁ * A₃ * A₄ + W.a₂ * A₃ ^ 2 - A₄ ^ 2)) -
        27 * (A₃ ^ 2 + 4 * A₆) ^ 2 + 9 * B₂ * (2 * A₄ + W.a₁ * A₃) * (A₃ ^ 2 + 4 * A₆), ?_⟩ ?_
    · rw [Δ, hB₂, hb₈, b₄, b₆, h₃, h₄, h₆]
      ring1
    · exact dvd_neg.not.mpr <| hmul (hpow 3 h2) (hpow 3 hB₄)
  | .IV, ⟨⟨B₂, hB₂⟩, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, ⟨C₈, hC₈⟩, hn⟩ =>
    have hb₆ : W.b₆ = ϖ ^ 2 * (A₃ ^ 2 + 4 * A₆) := by
      rw [b₆, h₃, h₆]
      ring1
    have hB₆ : ¬ϖ ∣ A₃ ^ 2 + 4 * A₆ := not_dvd_of_not_pow_succ_dvd_pow_mul (hb₆ ▸ hn)
    have hb₄ : W.b₄ = ϖ * (2 * A₄ + W.a₁ * A₃) := by
      rw [b₄, h₃, h₄]
      ring1
    have hrel : ϖ ^ 2 * ((2 * A₄ + W.a₁ * A₃) ^ 2 - ϖ * (B₂ * (A₃ ^ 2 + 4 * A₆) - 4 * C₈)) = 0 := by
      have hr : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := W.b_relation
      rw [hC₈, hB₂, hb₆, hb₄] at hr
      linear_combination hr
    rcases hϖ.dvd_of_dvd_pow (n := 2) (sub_eq_zero.mp ((mul_eq_zero.mp hrel).resolve_left
      (pow_ne_zero 2 hϖ.ne_zero)) ▸ dvd_mul_right ϖ _) with ⟨B₄, hB₄⟩
    refine not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ 4 (u := -(3 ^ 3 * (A₃ ^ 2 + 4 * A₆) ^ 2))
      ⟨-(B₂ ^ 2 * C₈) - 8 * ϖ * B₄ ^ 3 + 9 * B₂ * B₄ * (A₃ ^ 2 + 4 * A₆), ?_⟩ ?_
    · rw [Δ, hB₂, hC₈, hb₆, hb₄, hB₄]
      ring1
    · exact dvd_neg.not.mpr <| hmul (hpow 3 h3) (hpow 2 hB₆)
  | .IStar 0, ⟨h₁, ⟨A₂, h₂⟩, h₃, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, hn⟩ =>
    have hdisc : (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr = ϖ ^ 6 * (Cubic.mk 1 A₂ A₄ A₆).discr := by
      rw [h₂, h₄, h₆, Cubic.discr, Cubic.discr]
      ring1
    have hD : ¬ϖ ∣ (Cubic.mk 1 A₂ A₄ A₆).discr := not_dvd_of_not_pow_succ_dvd_pow_mul (hdisc ▸ hn)
    rcases W.exists_Δ_eq_pow_six_mul ϖ A₂ A₄ A₆ h₁ h₂ h₃ h₄ h₆ with ⟨d, hd, y, hy⟩
    refine not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ 6 (u := 2 ^ 4 * (Cubic.mk 1 A₂ A₄ A₆).discr)
      ⟨y, ?_⟩ (hmul (hpow 4 h2) hD)
    rw [hd]
    linear_combination ϖ ^ 6 * hy
  | .IStar (n + 1), .inl ⟨k, hk, hW, hb₆⟩ =>
    subst hk
    rcases isTateOddStage_iff.mp hW with
      ⟨⟨A₁, h₁⟩, ⟨A₂, h₂⟩, hn₂, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩⟩
    have hA₂ : ¬ϖ ∣ A₂ := not_dvd_of_not_pow_succ_dvd_pow_mul (k := 1) <| by rwa [pow_one, ← h₂]
    have hB₂ : ¬ϖ ∣ 2 ^ 2 * A₂ + ϖ * A₁ ^ 2 :=
      fun hB ↦ hmul (hpow 2 h2) hA₂ ((dvd_add_left (dvd_mul_right ϖ _)).mp hB)
    have hb₆' : W.b₆ = ϖ ^ (2 * k + 4) * (A₃ ^ 2 + 4 * A₆) := by
      rw [b₆, h₃, h₆]
      ring1
    have hB₆ : ¬ϖ ∣ A₃ ^ 2 + 4 * A₆ := not_dvd_of_not_pow_succ_dvd_pow_mul (hb₆' ▸ hb₆)
    have h4Δ : ¬ϖ ^ (2 * k + 7 + 1) ∣ 4 * W.Δ := not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ
      (2 * k + 7) (u := -((2 ^ 2 * A₂ + ϖ * A₁ ^ 2) ^ 3 * (A₃ ^ 2 + 4 * A₆)))
      ⟨(2 ^ 2 * A₂ + ϖ * A₁ ^ 2) ^ 2 * (2 * A₄ + A₁ * A₃) ^ 2 -
        32 * ϖ ^ (k + 1) * (2 * A₄ + A₁ * A₃) ^ 3 - 108 * ϖ ^ (2 * k) * (A₃ ^ 2 + 4 * A₆) ^ 2 +
        36 * ϖ ^ k * (2 ^ 2 * A₂ + ϖ * A₁ ^ 2) * (2 * A₄ + A₁ * A₃) * (A₃ ^ 2 + 4 * A₆), by
      rw [Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃, h₄, h₆]
      ring1⟩ (dvd_neg.not.mpr <| hmul (hpow 3 hB₂) hB₆)
    exact fun hΔ ↦ h4Δ (dvd_mul_of_dvd_right hΔ 4)
  | .IStar (n + 1), .inr ⟨k, hk, hW, hd⟩ =>
    subst hk
    rcases isTateEvenStage_iff.mp hW with
      ⟨⟨A₁, h₁⟩, ⟨A₂, h₂⟩, hn₂, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩⟩
    have hA₂ : ¬ϖ ∣ A₂ := not_dvd_of_not_pow_succ_dvd_pow_mul (k := 1) <| by rwa [pow_one, ← h₂]
    have hB₂ : ¬ϖ ∣ 2 ^ 2 * A₂ + ϖ * A₁ ^ 2 :=
      fun hB ↦ hmul (hpow 2 h2) hA₂ ((dvd_add_left (dvd_mul_right ϖ _)).mp hB)
    have hdisc : discrim W.a₂ W.a₄ W.a₆ = ϖ ^ (2 * k + 6) * (A₄ ^ 2 - 4 * A₂ * A₆) := by
      rw [discrim, h₂, h₄, h₆]
      ring1
    have hD : ¬ϖ ∣ A₄ ^ 2 - 4 * A₂ * A₆ := not_dvd_of_not_pow_succ_dvd_pow_mul (hdisc ▸ hd)
    refine not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ (2 * k + 8)
      (u := (2 ^ 2 * A₂ + ϖ * A₁ ^ 2) ^ 2 * (A₄ ^ 2 - 4 * A₂ * A₆))
      ⟨-((2 ^ 2 * A₂ + ϖ * A₁ ^ 2) ^ 2 * (A₁ ^ 2 * A₆ - A₁ * A₃ * A₄ + A₂ * A₃ ^ 2)) -
        8 * ϖ ^ k * (2 * A₄ + ϖ * A₁ * A₃) ^ 3 - 27 * ϖ ^ (2 * k + 1) * (ϖ * A₃ ^ 2 + 4 * A₆) ^ 2 +
        9 * ϖ ^ k * (2 ^ 2 * A₂ + ϖ * A₁ ^ 2) * (2 * A₄ + ϖ * A₁ * A₃) * (ϖ * A₃ ^ 2 + 4 * A₆),
        ?_⟩ (hmul (hpow 2 hB₂) hD)
    rw [Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃, h₄, h₆]
    ring1
  | .IVStar, ⟨⟨A₁, h₁⟩, ⟨A₂, h₂⟩, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, hn⟩ =>
    have hb₆ : W.b₆ = ϖ ^ 4 * (A₃ ^ 2 + 4 * A₆) := by
      rw [b₆, h₃, h₆]
      ring1
    have hB₆ : ¬ϖ ∣ A₃ ^ 2 + 4 * A₆ := not_dvd_of_not_pow_succ_dvd_pow_mul (hb₆ ▸ hn)
    refine not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ 8 (u := -(3 ^ 3 * (A₃ ^ 2 + 4 * A₆) ^ 2))
      ⟨-(ϖ * (A₁ ^ 2 + 4 * A₂) ^ 2 * (A₁ ^ 2 * A₆ + 4 * A₂ * A₆ - A₁ * A₃ * A₄ + A₂ * A₃ ^ 2 -
        A₄ ^ 2)) - 8 * (2 * A₄ + A₁ * A₃) ^ 3 +
        9 * (A₁ ^ 2 + 4 * A₂) * (2 * A₄ + A₁ * A₃) * (A₃ ^ 2 + 4 * A₆), ?_⟩
      (dvd_neg.not.mpr <| hmul (hpow 3 h3) (hpow 2 hB₆))
    rw [Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃, h₄, h₆]
    ring1
  | .IIIStar, ⟨⟨A₁, h₁⟩, ⟨A₂, h₂⟩, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, hn⟩ =>
    have hA₄ : ¬ϖ ∣ A₄ := not_dvd_of_not_pow_succ_dvd_pow_mul (h₄ ▸ hn)
    have hB₄ : ¬ϖ ∣ 2 * A₄ + ϖ * A₁ * A₃ := fun hB ↦ hmul h2 hA₄ <|
      (dvd_add_left (dvd_mul_of_dvd_left (dvd_mul_right ϖ A₁) A₃)).mp hB
    refine not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ 9 (u := -(2 ^ 3 * (2 * A₄ + ϖ * A₁ * A₃) ^ 3))
      ⟨-((A₁ ^ 2 + 4 * A₂) ^ 2 * (ϖ * A₁ ^ 2 * A₆ + 4 * ϖ * A₂ * A₆ - ϖ * A₁ * A₃ * A₄ +
        ϖ ^ 2 * A₂ * A₃ ^ 2 - A₄ ^ 2)) - 27 * (ϖ * A₃ ^ 2 + 4 * A₆) ^ 2 +
        9 * (A₁ ^ 2 + 4 * A₂) * (2 * A₄ + ϖ * A₁ * A₃) * (ϖ * A₃ ^ 2 + 4 * A₆), ?_⟩
      (dvd_neg.not.mpr <| hmul (hpow 3 h2) (hpow 3 hB₄))
    rw [Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃, h₄, h₆]
    ring1
  | .IIStar, ⟨⟨A₁, h₁⟩, ⟨A₂, h₂⟩, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, hn⟩ =>
    have hA₆ : ¬ϖ ∣ A₆ := not_dvd_of_not_pow_succ_dvd_pow_mul (h₆ ▸ hn)
    have hB₆ : ¬ϖ ∣ ϖ * A₃ ^ 2 + 2 ^ 2 * A₆ :=
      fun hB ↦ hmul (hpow 2 h2) hA₆ ((dvd_add_right (dvd_mul_right ϖ _)).mp hB)
    refine not_pow_succ_dvd_of_pow_succ_dvd_sub hϖ 10
      (u := -(3 ^ 3 * (ϖ * A₃ ^ 2 + 2 ^ 2 * A₆) ^ 2))
      ⟨-((A₁ ^ 2 + 4 * A₂) ^ 2 * (A₁ ^ 2 * A₆ + 4 * A₂ * A₆ - ϖ * A₁ * A₃ * A₄ +
        ϖ * A₂ * A₃ ^ 2 - ϖ * A₄ ^ 2)) - 8 * ϖ * (2 * A₄ + A₁ * A₃) ^ 3 +
        9 * (A₁ ^ 2 + 4 * A₂) * (2 * A₄ + A₁ * A₃) * (ϖ * A₃ ^ 2 + 2 ^ 2 * A₆), ?_⟩
      (dvd_neg.not.mpr <| hmul (hpow 3 h3) (hpow 2 hB₆))
    rw [Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃, h₄, h₆]
    ring1

/-- **The algorithmic Ogg exponent is `2` at additive reduction in residue characteristic at least
`5`** (Silverman, *Advanced Topics*, IV.9): if `2` and `3` are units of `R` and a minimal equation
of `E` has additive reduction, then `v(Δ_min) = m + 1` for the symbol at which Tate's algorithm
stops, so `f = v(Δ_min) − m + 1 = 2`. -/
lemma algorithmicOggExponent_eq_two [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (h2 : IsUnit (2 : R))
    (h3 : IsUnit (3 : R)) (E : WeierstrassCurve K) [E.IsElliptic]
    (ha : (E.minimal R).HasAdditiveReduction R) : E.algorithmicOggExponent R = 2 := by
  rcases E.exists_isTateTerminal_reductionSymbol R with ⟨W', D, ϖ, hmin, hD, hϖ, h⟩
  have hs : ∀ n, E.reductionSymbol R ≠ .I n := (forall_reductionSymbol_ne_I_iff E).2 ha
  have hnd (u : R) (hu : IsUnit u) : ¬ϖ ∣ u := fun hd ↦ hϖ.not_isUnit (isUnit_of_dvd_unit hd hu)
  have hv : (E.localMinimalDiscriminantValuation R : ℕ∞) = addVal R W'.Δ :=
    E.localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_baseChange R D hD
  have hlow : (((E.reductionSymbol R).componentCount + 1 : ℕ) : ℕ∞) ≤
      E.localMinimalDiscriminantValuation R := by
    rw [hv, ← hϖ.addVal_pow]
    exact addVal_le_iff_dvd.mpr (h.pow_componentCount_add_one_dvd_Δ hϖ.prime hs)
  have hup : ¬(((E.reductionSymbol R).componentCount + 2 : ℕ) : ℕ∞) ≤
      E.localMinimalDiscriminantValuation R := by
    rw [hv, ← hϖ.addVal_pow]
    exact fun hle ↦ h.not_pow_componentCount_add_two_dvd_Δ hϖ.prime (hnd 2 h2) (hnd 3 h3) hs
      (addVal_le_iff_dvd.mp hle)
  have key : (E.algorithmicOggExponent R : ℤ) =
      (E.reductionSymbol R).algorithmicOggExponent (E.localMinimalDiscriminantValuation R) :=
    E.natCast_algorithmicOggExponent
  rw [ReductionSymbol.algorithmicOggExponent_eq] at key
  norm_cast at hlow hup
  omega

/-- **The exponent of a prime not above `2` or `3` in the conductor is `2` at additive reduction**
(LMFDB `ec.conductor_valuation`, `ec.conductor`): for an elliptic curve over the fraction field of a
Dedekind domain `O`, such as a number field, and a height-one prime `v` of `O` containing neither
`2` nor `3`, at which a minimal equation has additive reduction, `v` occurs with exponent `2` in
Tau Ceti's algorithmic conductor `∏ᵥ 𝔭ᵥ ^ fᵥ`. -/
lemma count_algorithmicConductor_eq_two (O : Type*) [CommRing O] [IsDedekindDomain O]
    [∀ v : HeightOneSpectrum O, PerfectField (ResidueField (Localization.AtPrime v.asIdeal))]
    {F : Type*} [Field F] [Algebra O F] [IsFractionRing O F] (E : WeierstrassCurve F) [E.IsElliptic]
    (v : HeightOneSpectrum O) (h2 : (2 : O) ∉ v.asIdeal) (h3 : (3 : O) ∉ v.asIdeal)
    (ha : (E.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
      (Localization.AtPrime v.asIdeal)) :
    (Associates.mk v.asIdeal).count (Associates.mk (algorithmicConductor O E)).factors = 2 := by
  rw [count_algorithmicConductor]
  refine algorithmicOggExponent_eq_two ?_ ?_ E ha
  · rw [← map_ofNat (algebraMap O (Localization.AtPrime v.asIdeal)) 2]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ v.asIdeal 2).mpr h2
  · rw [← map_ofNat (algebraMap O (Localization.AtPrime v.asIdeal)) 3]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ v.asIdeal 3).mpr h3

end WeierstrassCurve
