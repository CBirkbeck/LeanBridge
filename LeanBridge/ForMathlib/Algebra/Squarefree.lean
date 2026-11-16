import Mathlib.Data.Nat.Prime.Int
import TauCeti.Algebra.Squarefree

/-!
# Prime divisors of squarefree integers

Elementary facts on the prime divisors of squarefree integers. A prime `p` with `p ∣ D` and
`p² ∤ D` divides every integer `E = D s²` with `s` rational. A prime dividing a squarefree integer
`a` divides `b` or `c` whenever `a b c` is a square. A positive squarefree integer other than `1`
whose only prime divisor is `2` is `2`.
-/

namespace Int

variable {p : ℕ}

lemma dvd_of_eq_mul_sq {E D : ℤ} {s : ℚ} (h : (E : ℚ) = D * s ^ 2) (hp : p.Prime)
    (hpD : (p : ℤ) ∣ D) (hpD2 : ¬(p : ℤ) ^ 2 ∣ D) : (p : ℤ) ∣ E := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have key : E * (s.den : ℤ) ^ 2 = D * s.num ^ 2 := by
    have h1 : (s.num : ℚ) = s * s.den := (Rat.mul_den_eq_num s).symm
    have h2 : (E : ℚ) * (s.den : ℚ) ^ 2 = D * (s.num : ℚ) ^ 2 := by
      rw [h, h1]
      ring1
    exact_mod_cast h2
  by_cases hden : (p : ℤ) ∣ s.den
  · have hnum : ¬(p : ℤ) ∣ s.num := fun hnum ↦ hp.ne_one <| Nat.eq_one_of_dvd_coprimes s.reduced
      (Int.ofNat_dvd_left.mp hnum) (Int.natCast_dvd_natCast.mp hden)
    have hcop : IsCoprime ((p : ℤ) ^ 2) (s.num ^ 2) :=
      ((Prime.coprime_iff_not_dvd hp').mpr hnum).pow
    exact absurd (hcop.dvd_of_dvd_mul_right (key ▸ (pow_dvd_pow_of_dvd hden 2).mul_left E)) hpD2
  · rcases hp'.dvd_or_dvd (key ▸ hpD.mul_right _ : (p : ℤ) ∣ E * (s.den : ℤ) ^ 2) with h | h
    · exact h
    · exact absurd (hp'.dvd_of_dvd_pow h) hden

lemma not_dvd_of_isSquare_mul {a b c : ℤ} (ha : Squarefree a) (hsq : IsSquare (a * b * c))
    (hp : p.Prime) (hpb : ¬(p : ℤ) ∣ b) (hpc : ¬(p : ℤ) ∣ c) : ¬(p : ℤ) ∣ a := by
  intro hpa
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hsq with ⟨m, hm⟩
  have hpm : (p : ℤ) ∣ m := hp'.dvd_of_dvd_pow (n := 2) <| by
    rw [sq, ← hm]
    exact (hpa.mul_right b).mul_right c
  have hp2 : (p : ℤ) * p ∣ a * (b * c) := by
    rw [← mul_assoc, hm]
    exact mul_dvd_mul hpm hpm
  have hbc : IsCoprime (p : ℤ) (b * c) :=
    ((Prime.coprime_iff_not_dvd hp').mpr hpb).mul_right ((Prime.coprime_iff_not_dvd hp').mpr hpc)
  exact hp'.not_isUnit (ha _ ((hbc.mul_left hbc).dvd_of_dvd_mul_right hp2))

lemma eq_two_of_squarefree {d : ℤ} (hd : Squarefree d) (hpos : 0 < d) (hne : d ≠ 1)
    (h2 : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p = 2) : d = 2 := by
  lift d to ℕ using hpos.le
  have hd' : Squarefree d := Int.squarefree_natCast.mp hd
  by_contra hne2
  have h3 : 2 < d := by omega
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt h3 with h4 | ⟨p, hp, hpd, hodd⟩
  · exact absurd (hd' 2 (by simpa using h4)) (by decide)
  · rcases hodd with ⟨k, rfl⟩
    have h : 2 * k + 1 = 2 := h2 _ hp (Int.natCast_dvd_natCast.mpr hpd)
    omega

end Int
