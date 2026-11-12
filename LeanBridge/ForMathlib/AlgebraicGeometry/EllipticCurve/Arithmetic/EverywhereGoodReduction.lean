import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor

/-!
# There is no elliptic curve over `ℤ`

A Weierstrass equation with coefficients in `ℤ` never has discriminant `±1` (Tate): there is no
elliptic curve over `ℤ`. Equivalently, every elliptic curve over `ℚ` has bad reduction at some
prime, so that the norm `N` of its conductor exceeds `1`. This is the condition under which the
Szpiro ratios `log |Δ_min| / log N` and `log max (|c₄|³, c₆²) / log N` of LMFDB `ec.q.szpiro_ratio`
are defined; the conductor is Tau Ceti's algorithmic conductor
`WeierstrassCurve.algorithmicConductor`.

The proof is elementary. Suppose that `Δ = ±1`, so that `c₄³ - c₆² = 1728 Δ = ±12³`. If `a₁` is
even, then `Δ ≡ -27 b₆² (mod 8)`, which is not `±1` modulo `8`. So `a₁` is odd, and
`c₄ = b₂² - 24 b₄ ≡ 1 (mod 8)`. If `3 ∤ c₄`, the factors `c₄ ∓ 12` and `c₄² ± 12 c₄ + 144` of `c₆²`
are coprime, so `c₄ ∓ 12` is a square up to sign, but it is `5` modulo `8`. If `3 ∣ c₄`, then
`3 ∣ b₂`, so that `c₄ = 3 c` and `c₆ = 27 g` with `c³ - 27 g² = ±64`. Then `c ∓ 4 = 9 t` and
`t (27 t² ± 36 t + 16) = g²`, with coprime factors, the second one positive; so `t` is a square,
but `t ≡ 7 (mod 8)`.

## Main results

* `WeierstrassCurve.not_isElliptic_int`: no Weierstrass equation over `ℤ` has discriminant `±1`.
* `WeierstrassCurve.one_lt_absNorm_algorithmicConductor` (LMFDB `ec.q.szpiro_ratio`): the
  algorithmic conductor of an elliptic curve over `ℚ` has norm greater than `1`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, 2009,
  Chapter VIII, exercises (Tate's argument).
-/

namespace WeierstrassCurve

/-- **There is no elliptic curve over `ℤ`** (Tate): the discriminant of a Weierstrass equation with
integral coefficients is never `±1`. -/
lemma not_isElliptic_int (W : WeierstrassCurve ℤ) : ¬W.IsElliptic := by
  intro hW
  have hsq (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
    have h₀ : 0 ≤ x % 8 := Int.emod_nonneg x (by norm_num)
    have h₈ : x % 8 < 8 := Int.emod_lt_of_pos x (by norm_num)
    rw [sq, Int.mul_emod]
    interval_cases x % 8 <;> simp
  have hs : W.Δ = 1 ∨ W.Δ = -1 := Int.isUnit_iff.mp hW.isUnit
  have hs2 : W.Δ ^ 2 = 1 := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  rcases Int.even_or_odd' W.a₁ with ⟨k, hk | hk⟩
  · -- `a₁ = 2 k`: then `Δ ≡ -27 b₆² (mod 8)`, which is not `±1`
    have h8 : (8 : ℤ) ∣ W.Δ + 27 * W.b₆ ^ 2 := ⟨-2 * (k ^ 2 + W.a₂) ^ 2 * W.b₈ -
        8 * (W.a₄ + k * W.a₃) ^ 3 + 9 * (k ^ 2 + W.a₂) * (W.a₄ + k * W.a₃) * W.b₆, by
      simp only [Δ, b₂, b₄, hk]
      ring1⟩
    have hb : W.b₆ ^ 2 % 8 = 0 ∨ W.b₆ ^ 2 % 8 = 1 ∨ W.b₆ ^ 2 % 8 = 4 := hsq W.b₆
    generalize W.b₆ ^ 2 = x at h8 hb
    omega
  -- `a₁ = 2 k + 1`: then `c₄ ≡ 1 (mod 8)`
  have h8 : (8 : ℤ) ∣ W.c₄ - 1 := ⟨k ^ 2 + k + W.a₂ + 2 * (k ^ 2 + k + W.a₂) ^ 2 - 3 * W.b₄, by
    simp only [c₄, b₂, hk]
    ring1⟩
  have hrel : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 := W.c_relation
  by_cases h3 : (3 : ℤ) ∣ W.c₄
  · -- `3 ∣ c₄`: then `3 ∣ b₂`, so `c₄ = 3 c` and `c₆ = 27 g` with `c³ - 27 g² = 64 Δ`
    have hb₂ : (3 : ℤ) ∣ W.b₂ := by
      refine Int.prime_three.dvd_of_dvd_pow (n := 2) ?_
      have h : W.b₂ ^ 2 = W.c₄ + 24 * W.b₄ := by
        simp only [c₄]
        ring1
      rw [h]
      exact dvd_add h3 (dvd_mul_of_dvd_left (by norm_num) _)
    rcases hb₂ with ⟨β, hβ⟩
    have hc : W.c₄ = 3 * (3 * β ^ 2 - 8 * W.b₄) := by
      rw [c₄, hβ]
      ring1
    have hg : W.c₆ = 27 * (-β ^ 3 + 4 * β * W.b₄ - 8 * W.b₆) := by
      rw [c₆, hβ]
      ring1
    generalize 3 * β ^ 2 - 8 * W.b₄ = c at hc
    generalize -β ^ 3 + 4 * β * W.b₄ - 8 * W.b₆ = g at hg
    have h64 : c ^ 3 - 27 * g ^ 2 = 64 * W.Δ := by
      refine mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) ?_
      rw [hc, hg] at hrel
      linear_combination -hrel
    -- `A = c - 4 Δ` and `B = A² + 12 Δ A + 48` have `A B = 27 g²`, so `9 ∣ A`
    have hAB :
        (c - 4 * W.Δ) * ((c - 4 * W.Δ) ^ 2 + 12 * W.Δ * (c - 4 * W.Δ) + 48) = 27 * g ^ 2 := by
      linear_combination h64 + (128 * W.Δ - 48 * c) * hs2
    have h9 : (9 : ℤ) ∣ c - 4 * W.Δ := by
      generalize c - 4 * W.Δ = A at hAB ⊢
      have hval : ((A : ZMod 27).val : ℤ) = A % 27 := ZMod.val_intCast A
      rcases hs with h | h
      · have key : ∀ x : ZMod 27, x * (x ^ 2 + 12 * x + 48) = 0 → x.val % 9 = 0 := by decide
        have hA : A * (A ^ 2 + 12 * A + 48) = 27 * g ^ 2 := by
          rw [h] at hAB
          linear_combination hAB
        have hz : (A : ZMod 27) * ((A : ZMod 27) ^ 2 + 12 * A + 48) = 27 * (g : ZMod 27) ^ 2 :=
          mod_cast congrArg (Int.cast : ℤ → ZMod 27) hA
        rw [show (27 : ZMod 27) = 0 from rfl, zero_mul] at hz
        have hA9 : (A : ZMod 27).val % 9 = 0 := key _ hz
        omega
      · have key : ∀ x : ZMod 27, x * (x ^ 2 - 12 * x + 48) = 0 → x.val % 9 = 0 := by decide
        have hA : A * (A ^ 2 - 12 * A + 48) = 27 * g ^ 2 := by
          rw [h] at hAB
          linear_combination hAB
        have hz : (A : ZMod 27) * ((A : ZMod 27) ^ 2 - 12 * A + 48) = 27 * (g : ZMod 27) ^ 2 :=
          mod_cast congrArg (Int.cast : ℤ → ZMod 27) hA
        rw [show (27 : ZMod 27) = 0 from rfl, zero_mul] at hz
        have hA9 : (A : ZMod 27).val % 9 = 0 := key _ hz
        omega
    -- with `A = 9 t`: `t (27 t² + 36 Δ t + 16) = g²`, coprime factors, and `t ≡ 7 (mod 8)`
    rcases h9 with ⟨t, ht⟩
    rw [ht] at hAB
    have htw : t * (27 * t ^ 2 + 36 * W.Δ * t + 16) = g ^ 2 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hAB)
    have ht8 : t % 8 = 7 := by omega
    have hcop : IsCoprime t (27 * t ^ 2 + 36 * W.Δ * t + 16) := by
      have h2 : IsCoprime (2 : ℤ) t := Int.prime_two.coprime_iff_not_dvd.mpr (by omega)
      have h16 : IsCoprime t 16 := by simpa using (h2.pow_left (m := 4)).symm
      convert h16.add_mul_left_right (27 * t + 36 * W.Δ) using 1
      ring1
    rcases Int.sq_of_isCoprime hcop htw with ⟨u, hu | hu⟩
    · have hu8 : u ^ 2 % 8 = 0 ∨ u ^ 2 % 8 = 1 ∨ u ^ 2 % 8 = 4 := hsq u
      generalize u ^ 2 = x at hu hu8
      omega
    · have hw : 0 < 27 * t ^ 2 + 36 * W.Δ * t + 16 := by
        nlinarith [sq_nonneg (3 * t + 2 * W.Δ)]
      have ht0 : t = 0 := by
        nlinarith [sq_nonneg u, sq_nonneg g]
      omega
  · -- `3 ∤ c₄`: `A = c₄ - 12 Δ` and `B = c₄² + 12 Δ c₄ + 144` are coprime with `A B = c₆²`, so
    -- `A` is a square up to sign, but `A ≡ 5 (mod 8)`
    have hAB : (W.c₄ - 12 * W.Δ) * (W.c₄ ^ 2 + 12 * W.Δ * W.c₄ + 144) = W.c₆ ^ 2 := by
      linear_combination -hrel - 144 * W.c₄ * hs2
    have hcop : IsCoprime (W.c₄ - 12 * W.Δ) (W.c₄ ^ 2 + 12 * W.Δ * W.c₄ + 144) := by
      have h2 : IsCoprime (2 : ℤ) (W.c₄ - 12 * W.Δ) :=
        Int.prime_two.coprime_iff_not_dvd.mpr (by omega)
      have h3' : IsCoprime (3 : ℤ) (W.c₄ - 12 * W.Δ) :=
        Int.prime_three.coprime_iff_not_dvd.mpr (by omega)
      have h432 : IsCoprime (W.c₄ - 12 * W.Δ) 432 := by
        simpa using ((h2.pow_left (m := 4)).mul_left (h3'.pow_left (m := 3))).symm
      convert h432.add_mul_left_right (W.c₄ + 24 * W.Δ) using 1
      linear_combination 288 * hs2
    rcases Int.sq_of_isCoprime hcop hAB with ⟨u, hu⟩
    have hu8 : u ^ 2 % 8 = 0 ∨ u ^ 2 % 8 = 1 ∨ u ^ 2 % 8 = 4 := hsq u
    generalize u ^ 2 = x at hu hu8
    omega

/-- **Every elliptic curve over `ℚ` has bad reduction at some prime** (Tate; LMFDB
`ec.q.szpiro_ratio`): the norm `N` of its algorithmic conductor exceeds `1`, so that its Szpiro
ratios are defined. Otherwise no prime would divide the discriminant of the integral model of its
reduced minimal model, which would then be an elliptic curve over `ℤ`. -/
lemma one_lt_absNorm_algorithmicConductor (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    1 < Ideal.absNorm (algorithmicConductor ℤ E) := by
  have hmin : IsGlobalMinimal ℤ (reducedMinimalModel E) :=
    (isReducedMinimal_reducedMinimalModel E).isGlobalMinimal
  have : IsIntegral ℤ (reducedMinimalModel E) := hmin.isIntegral
  rcases exists_smul_eq_reducedMinimalModel E with ⟨C, hC⟩
  have hN : algorithmicConductor ℤ E = algorithmicConductor ℤ (reducedMinimalModel E) := by
    have h : algorithmicConductor ℤ (C • E) = algorithmicConductor ℤ E :=
      algorithmicConductor_smul ℤ C E
    simp only [hC] at h
    exact h.symm
  have h0 : Ideal.absNorm (algorithmicConductor ℤ E) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (algorithmicConductor_ne_bot ℤ E)
  refine lt_of_not_ge fun hle ↦ not_isElliptic_int (integralModel ℤ (reducedMinimalModel E)) ⟨?_⟩
  rw [Int.isUnit_iff_natAbs_eq]
  by_contra hne
  rcases Nat.exists_prime_and_dvd hne with ⟨p, hp, hpΔ⟩
  have hpN : p ∣ Ideal.absNorm (algorithmicConductor ℤ E) := hN ▸
    (hmin.dvd_absNorm_algorithmicConductor_iff (baseChange_integralModel_eq ℤ _) hp).mpr
      (Int.natCast_dvd.mpr hpΔ)
  exact hp.one_lt.not_ge ((Nat.le_of_dvd (by omega) hpN).trans hle)

end WeierstrassCurve
