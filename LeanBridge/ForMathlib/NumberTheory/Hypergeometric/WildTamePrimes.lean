import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.CuspIndex
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Wild and tame primes of hypergeometric families and motives

A prime `p` is wild for a hypergeometric family `H(A, B)` if it divides an entry of `A` or of `B`,
and tame for the motive `H(A, B, t)` if it is not wild and `v_p(t) ≠ 0` or `v_p(t - 1) ≠ 0`.

## Main definitions

* `Hypergeometric.Parameters.IsWildPrime` (LMFDB `hgm.wild`): wild primes.
* `Hypergeometric.Parameters.IsTamePrime` (LMFDB `hgm.tame`): tame primes.

## Main results

* `Hypergeometric.Parameters.isTamePrime_iff_padicValRat`: for `t ≠ 1`, the valuation condition
  in terms of `padicValRat`.
-/

namespace Hypergeometric.Parameters

variable {d : ℕ} (P : Parameters d) (p : ℕ) (t : ℚ)

/-- A prime `p` is **wild** for a hypergeometric family `H(A, B)` (LMFDB `hgm.wild`) if it divides
an entry of `A` or of `B`. -/
def IsWildPrime : Prop :=
  p.Prime ∧ ∃ a ∈ P.A.toList ++ P.B.toList, p ∣ a

/-- A prime `p` is **tame** for a hypergeometric motive `H(A, B, t)`, `t ∈ ℚ^×` (LMFDB `hgm.tame`),
if it is not wild and `v_p(t) ≠ 0` or `v_p(t - 1) ≠ 0`. The valuations are written through
divisibility of numerators and denominators, so that `v_p(0) = ∞ ≠ 0` for `t = 1` as in the knowl,
whereas Mathlib's `padicValRat p 0` is `0` (`Hypergeometric.Parameters.isTamePrime_iff_padicValRat`
compares the two for `t ≠ 1`). Hence for `t = 1` every prime that is not wild is tame, as the
knowl's text literally says; for `t = 0`, outside the knowl's range `t ∈ ℚ^×`, so is every such
prime, a junk value. -/
def IsTamePrime : Prop :=
  p.Prime ∧ ¬P.IsWildPrime p ∧ ((p : ℤ) ∣ t.num ∨ p ∣ t.den ∨ (p : ℤ) ∣ (t - 1).num)

lemma padicValRat_ne_zero_iff {q : ℚ} (hq : q ≠ 0) (hp : p.Prime) :
    padicValRat p q ≠ 0 ↔ (p : ℤ) ∣ q.num ∨ p ∣ q.den := by
  have : Fact p.Prime := ⟨hp⟩
  have hc : ¬(p ∣ q.num.natAbs ∧ p ∣ q.den) := fun h ↦
    hp.one_lt.ne' <| Nat.eq_one_of_dvd_one <| q.reduced ▸ Nat.dvd_gcd h.1 h.2
  rw [padicValRat, padicValInt, Int.natCast_dvd,
    dvd_iff_padicValNat_ne_zero <| Int.natAbs_ne_zero.mpr <| Rat.num_ne_zero.mpr hq,
    dvd_iff_padicValNat_ne_zero q.den_nz] at *
  omega

/-- **Tameness through `padicValRat`**: for `t ∉ {0, 1}`, a prime `p` is tame for `H(A, B, t)` if
and only if it is not wild and `v_p(t) ≠ 0` or `v_p(t - 1) ≠ 0`. -/
lemma isTamePrime_iff_padicValRat (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hp : p.Prime) :
    P.IsTamePrime p t ↔ ¬P.IsWildPrime p ∧ (padicValRat p t ≠ 0 ∨ padicValRat p (t - 1) ≠ 0) := by
  rw [IsTamePrime, padicValRat_ne_zero_iff p ht₀ hp,
    padicValRat_ne_zero_iff p (sub_ne_zero.mpr ht₁) hp, ← Nat.cast_one, Rat.sub_natCast_den]
  tauto

end Hypergeometric.Parameters
