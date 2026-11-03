import LeanBridge.ForMathlib.NumberTheory.LocalField.JumpFiltration
import LeanBridge.ForMathlib.NumberTheory.LocalField.JumpSet

/-!
# The jump set of a `p`-adic field: Miki's existence and Pagano's independence theorems

Let `K` be a `p`-adic field containing a primitive `p`-th root of unity `ζ`, `e = v_K(p)`,
`e' = e / (p - 1)`, `r = v_p(e)` and `ρ(x) = min(px, x + e)`. This file makes the jump set of `K`
(LMFDB `lf.jump_set`) a function of `K`, `IsNonarchimedeanLocalField.jumpSet`.

The committed relation `IsNonarchimedeanLocalField.IsJumpSet` of `JumpSet.lean` follows the knowl:
`u` is the extended jump sequence of a factorisation `ζ = α₀^{p^r} ⋯ α_r` into Miki factors. This is
not a function of `K`. Over `K = ℚ₂[x]/(x⁴ + 2x³ + 2x² + 2)`, with `π = x`, `e = 4`, `r = 2` and
`ρ(1, 2, 3, 5, 7) = (2, 4, 6, 9, 11)`, we have `(1 + π)⁴ = -1 + 2π³ + 4π² + 4π`, so
`-1 = (1 + π)⁴ α₂` for the principal unit `α₂ = (1 - 2π³ - 4π² - 4π)⁻¹` of depth `7`, a
factorisation with `α₁ = 1` and the sequence `[1, ρ(1), 7] = [1, 2, 7]`, which is the jump set of
this field in the LMFDB (label `2.1.4.6a2.1`). For `c = 1 + π⁵`, of depth `5`, we also have
`-1 = (1 + π)⁴ (c⁻¹)² (α₂ c²)`, where `α₂ c²` still has depth `7`, with the increasing sequence
`[1, 5, 7]`. The missing condition is (C.1) of Pagano (*Jump sets in local fields*,
arXiv:1810.09975, §1.2, J. Algebra 593 (2022)): `ρ(a) ≤ b` for `a < b` in the jump set, that is
`ρ(uᵢ) ≤ u_{i+1}`, which `[1, 5, 7]` violates. It says that the levels of the factors
`αᵢ^{p^{r-i}}` strictly increase with `i`. Pagano, §1.4, quotes Miki's Lemma 17 for an element
`(I_K, β_K)` of the set of extended jump sets, so with this condition, and it is what the sentence
of the knowl "these values are independent of the choice of `α₀, …, α_r`" needs. This example is
checked by hand, not formalised.

So the jump set is defined here through the *reduced* Miki factorisations
(`IsNonarchimedeanLocalField.IsReducedMikiFactorisation`). The principal units of `K` with the unit
filtration form a filtered group with Pagano's shift
(`IsNonarchimedeanLocalField.jumpFiltrationOfRoot`), so the theorems of `JumpFiltration.lean` apply:
every primitive `p`-th root of unity of `K` has a reduced Miki factorisation
(`IsNonarchimedeanLocalField.exists_isReducedMikiFactorisation`, Miki's existence theorem) and its
extended jump sequence does not depend on the factorisation or the root of unity
(`IsNonarchimedeanLocalField.jumpSequence_eq_of_isReducedMikiFactorisation`, the independence the
knowl attributes to Pagano, which is the uniqueness in Miki's Lemma 17). The ingredients on `K` are
the expansion
`(1 + t) ^ p = 1 + t ^ p + p t + p t ^ 2 r`, the perfectness of the residue field, the relation
`Z ^ (p - 1) ≡ -p / π ^ e` for `ζ = 1 + π ^ e' Z`, the fixed points `F_p` of the Frobenius of the
residue field and Tau Ceti's theorem that the `p`-th power maps `U(K, a)` onto `U(K, a + e)` for
`a > e'`.

The knowl also states that the jump set determines the structure of the principal units of `K` as a
filtered `ℤ_p`-module (Pagano, Theorem 1.5). No definition or statement here depends on this
description, and it is not proved here.

## Main definitions

* `IsNonarchimedeanLocalField.rootLevel`: the level `e' = e / (p - 1)` of a primitive `p`-th root of
  unity.
* `IsNonarchimedeanLocalField.principalRoot`: a primitive `p`-th root of unity as a principal unit.
* `IsNonarchimedeanLocalField.jumpFiltrationOfRoot`: the principal units as a filtered group with
  Pagano's shift.
* `IsNonarchimedeanLocalField.IsReducedMikiFactorisation` (LMFDB `lf.jump_set`): the factorisations
  of `ζ` defining the jump set.
* `IsNonarchimedeanLocalField.IsPaganoJumpSet` (LMFDB `lf.jump_set`): `u` is the jump set of `K`.
* `IsNonarchimedeanLocalField.jumpSet` (LMFDB `lf.jump_set`): the jump set of `K`.

## Main results

* `IsNonarchimedeanLocalField.exists_isReducedMikiFactorisation`: Miki's existence theorem.
* `IsNonarchimedeanLocalField.jumpSequence_eq_of_isReducedMikiFactorisation`: the independence of
  the factorisation.
* `IsNonarchimedeanLocalField.isPaganoJumpSet_iff`: the jump set is well defined.
* `IsNonarchimedeanLocalField.jumpSet_eq_map`: the jump set is the extended jump sequence of every
  reduced Miki factorisation.
* `IsNonarchimedeanLocalField.jumpSet_eq_nil`: without a primitive `p`-th root of unity the jump set
  is not defined.
* `IsNonarchimedeanLocalField.length_jumpSet`, `IsNonarchimedeanLocalField.pos_of_mem_jumpSet`,
  `IsNonarchimedeanLocalField.pairwise_lt_jumpSet`: the jump set is an increasing sequence of
  `r + 1` positive integers.
* `IsNonarchimedeanLocalField.IsReducedMikiFactorisation.jumpSequence_pos`,
  `IsNonarchimedeanLocalField.IsReducedMikiFactorisation.jumpSequence_lt_succ`,
  `IsNonarchimedeanLocalField.IsReducedMikiFactorisation.pow_mul_jumpSequence_zero`: positivity,
  monotonicity and the first term `e' / p ^ r` of the extended jump sequence.
* `IsNonarchimedeanLocalField.IsPaganoJumpSet.isJumpSet`: the jump set satisfies the committed
  relation.
* `IsNonarchimedeanLocalField.unitDepth_eq_rootLevel`: the depth of a primitive `p`-th root of unity
  is `e / (p - 1)`.
-/

open Finset IsLocalRing TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField

section Ring

variable {R : Type*} [CommRing R] {π P x y z ζ : R} {p e' a : ℕ}

lemma dvd_coe_mul_inv_sub_one {d : R} {w v : Rˣ} (h : d ∣ (w : R) - v) :
    d ∣ ((w * v⁻¹ : Rˣ) : R) - 1 := by
  have heq : ((w * v⁻¹ : Rˣ) : R) - 1 = ((w : R) - v) * ((v⁻¹ : Rˣ) : R) := by
    rw [Units.val_mul, sub_mul, Units.mul_inv]
  rw [heq]
  exact h.mul_right _

lemma exists_one_add_pow_eq (hp : p.Prime) (t : R) :
    ∃ r, (1 + t) ^ p = 1 + t ^ p + p * t + p * t ^ 2 * r := by
  rcases Nat.exists_eq_add_of_le' hp.two_le with ⟨m, rfl⟩
  have hc (k : ℕ) (hk : k ∈ range m) : m + 2 ∣ (m + 2).choose (k + 2) :=
    hp.dvd_choose_self (k + 1).succ_ne_zero (Nat.add_lt_add_right (mem_range.mp hk) 2)
  refine ⟨∑ k ∈ range m, t ^ k * (((m + 2).choose (k + 2) / (m + 2) : ℕ) : R), ?_⟩
  rw [add_comm 1 t, add_pow, sum_range_succ', sum_range_succ', sum_range_succ]
  simp only [one_pow, mul_one, Nat.choose_zero_right, zero_add, Nat.choose_one_right,
    Nat.choose_self, mul_sum]
  have hs : ∑ k ∈ range m, t ^ (k + 2) * (((m + 2).choose (k + 2) : ℕ) : R) = ∑ k ∈ range m,
      ((m + 2 : ℕ) : R) * t ^ 2 * (t ^ k * (((m + 2).choose (k + 2) / (m + 2) : ℕ) : R)) := by
    refine sum_congr rfl fun k hk ↦ ?_
    conv_lhs => rw [← Nat.mul_div_cancel' (hc k hk), Nat.cast_mul]
    ring1
  rw [hs]
  ring1

lemma exists_one_add_mul_pow_eq (Z : R) (b : ℕ) (he : 1 ≤ e') :
    ∃ q, (1 + π ^ e' * Z) ^ b = 1 + b * (π ^ e' * Z) + π ^ (e' + 1) * q := by
  rcases Nat.exists_eq_add_of_le' he with ⟨f, rfl⟩
  induction b with
  | zero => exact ⟨0, by simp⟩
  | succ b ih =>
    rcases ih with ⟨q, hq⟩
    refine ⟨q + b * π ^ f * Z ^ 2 + π ^ (f + 1) * q * Z, ?_⟩
    rw [pow_succ, hq]
    push_cast
    ring1

variable [Fact p.Prime]

lemma exists_pow_sub_one_eq (hP : (p : R) = π ^ ((p - 1) * e') * P) (s : R) : ∃ r,
    (1 + π ^ a * s) ^ p - 1 = π ^ (p * a) * s ^ p +
      π ^ ((p - 1) * e' + a) * (P * s + π ^ a * (P * s ^ 2 * r)) := by
  rcases exists_one_add_pow_eq (Fact.out : p.Prime) (π ^ a * s) with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  rw [hr, hP, pow_add, mul_comm p a, pow_mul]
  ring1

lemma pow_jumpShift_dvd_pow_sub_one (hP : (p : R) = π ^ ((p - 1) * e') * P) (hx : π ^ a ∣ x - 1) :
    π ^ jumpShift p e' a ∣ x ^ p - 1 := by
  rcases hx with ⟨s, hs⟩
  rw [sub_eq_iff_eq_add'] at hs
  rcases exists_pow_sub_one_eq (a := a) hP s with ⟨r, hr⟩
  rw [hs, hr]
  refine dvd_add ((pow_dvd_pow π (min_le_left _ _)).mul_right _) ((pow_dvd_pow π ?_).mul_right _)
  rw [add_comm]
  exact min_le_right _ _

lemma exists_add_eq_of_lt (h : a < e') : ∃ d, 1 ≤ d ∧ (p - 1) * e' + a = p * a + d := by
  have hp : p * a = a + (p - 1) * a :=
    mul_eq_add_sub_one_mul
  have hlt : (p - 1) * a < (p - 1) * e' :=
    Nat.mul_lt_mul_of_pos_left h (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  exact ⟨(p - 1) * e' - (p - 1) * a, by omega, by omega⟩

lemma exists_add_eq_of_gt (h : e' < a) : ∃ d, 1 ≤ d ∧ p * a = (p - 1) * e' + a + d := by
  have hp : p * a = a + (p - 1) * a :=
    mul_eq_add_sub_one_mul
  have hlt : (p - 1) * e' < (p - 1) * a :=
    Nat.mul_lt_mul_of_pos_left h (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  exact ⟨(p - 1) * a - (p - 1) * e', by omega, by omega⟩

lemma exists_pow_dvd_sub_pow (hP : (p : R) = π ^ ((p - 1) * e') * P) (h : a < e')
    (hs : ∀ s : R, ∃ θ, π ∣ s - θ ^ p) (hx : π ^ (p * a) ∣ x - 1) :
    ∃ y, π ^ a ∣ y - 1 ∧ π ^ (p * a + 1) ∣ x - y ^ p := by
  rcases hx with ⟨s, hs'⟩
  rw [sub_eq_iff_eq_add'] at hs'
  rcases hs s with ⟨θ, hθ⟩
  rcases exists_add_eq_of_lt (p := p) h with ⟨d, hd, hd'⟩
  rcases exists_pow_sub_one_eq (a := a) hP θ with ⟨r, hr⟩
  refine ⟨1 + π ^ a * θ, ⟨θ, add_sub_cancel_left _ _⟩, ?_⟩
  have heq : x - (1 + π ^ a * θ) ^ p = π ^ (p * a) *
      (s - θ ^ p - π ^ d * (P * θ + π ^ a * (P * θ ^ 2 * r))) := by
    have hr' : (1 + π ^ a * θ) ^ p = 1 + (π ^ (p * a) * θ ^ p +
        π ^ ((p - 1) * e' + a) * (P * θ + π ^ a * (P * θ ^ 2 * r))) :=
      eq_add_of_sub_eq' hr
    rw [hs', hr', hd', pow_add π (p * a) d]
    ring1
  rw [heq, pow_succ]
  exact mul_dvd_mul_left _ (dvd_sub hθ (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _))

lemma dvd_sub_one_of_pow_eq_one (hπ : Prime π) (hp : π ∣ p) (hζ : ζ ^ p = 1) : π ∣ ζ - 1 := by
  rcases exists_one_add_pow_eq (Fact.out : p.Prime) (ζ - 1) with ⟨r, hr⟩
  rw [add_sub_cancel, hζ] at hr
  have h : (ζ - 1) ^ p = -(p * ((ζ - 1) + (ζ - 1) ^ 2 * r)) := by
    linear_combination -hr
  have hdvd : π ∣ (ζ - 1) ^ p := by
    rw [h]
    exact (hp.mul_right _).neg_right
  exact hπ.dvd_of_dvd_pow hdvd

lemma exists_pow_sub_one_eq_of_self (hP : (p : R) = π ^ ((p - 1) * e') * P) (s : R) : ∃ r,
    (1 + π ^ e' * s) ^ p - 1 = π ^ (p * e') * (s ^ p + (P * s + π ^ e' * (P * s ^ 2 * r))) := by
  rcases exists_pow_sub_one_eq (a := e') hP s with ⟨r, hr⟩
  have he : (p - 1) * e' + e' = p * e' := by
    rw [add_comm]
    exact mul_eq_add_sub_one_mul.symm
  rw [he, ← mul_add] at hr
  exact ⟨r, hr⟩

variable [IsDomain R]

lemma pow_succ_dvd_sub_one (hπ : Prime π) (hP : (p : R) = π ^ ((p - 1) * e') * P) (hPu : IsUnit P)
    (ha : a ≠ e') (hx : π ^ a ∣ x - 1) (h : π ^ (jumpShift p e' a + 1) ∣ x ^ p - 1) :
    π ^ (a + 1) ∣ x - 1 := by
  rcases hx with ⟨s, hs⟩
  rw [hs, pow_succ]
  refine mul_dvd_mul_left _ ?_
  rw [sub_eq_iff_eq_add'] at hs
  rcases exists_pow_sub_one_eq (a := a) hP s with ⟨r, hr⟩
  rw [hs, hr] at h
  rcases lt_or_gt_of_ne ha with hlt | hlt
  · rcases exists_add_eq_of_lt (p := p) hlt with ⟨d, hd, hd'⟩
    have heq : π ^ (p * a) * s ^ p + π ^ ((p - 1) * e' + a) * (P * s + π ^ a * (P * s ^ 2 * r)) =
        π ^ (p * a) * (s ^ p + π ^ d * (P * s + π ^ a * (P * s ^ 2 * r))) := by
      rw [hd', pow_add π (p * a) d]
      ring1
    rw [heq, jumpShift_of_le hlt.le, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero),
      dvd_add_left (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _)] at h
    exact hπ.dvd_of_dvd_pow h
  · rcases exists_add_eq_of_gt (p := p) hlt with ⟨d, hd, hd'⟩
    have heq : π ^ (p * a) * s ^ p + π ^ ((p - 1) * e' + a) * (P * s + π ^ a * (P * s ^ 2 * r)) =
        π ^ (a + (p - 1) * e') * (π ^ d * s ^ p + (π ^ a * (P * s ^ 2 * r) + P * s)) := by
      rw [hd', add_comm a, pow_add π _ d]
      ring1
    rw [heq, jumpShift_of_ge hlt.le, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero),
      dvd_add_right (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _),
      dvd_add_right (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _), hPu.dvd_mul_left] at h
    exact h

lemma exists_natCast_pow_dvd_sub_pow (hπ : Prime π) (hP : (p : R) = π ^ ((p - 1) * e') * P)
    (he : 1 ≤ e') (hζ : ζ ^ p = 1) (hζ₁ : π ^ e' ∣ ζ - 1) (hζ₂ : ¬π ^ (e' + 1) ∣ ζ - 1)
    (hfix : ∀ A Z : R, ¬π ∣ Z → π ∣ A ^ p - Z ^ (p - 1) * A → ∃ b : ℕ, π ∣ A - b * Z)
    (hz : π ^ e' ∣ z - 1) (h : π ^ (p * e' + 1) ∣ z ^ p - 1) :
    ∃ b : ℕ, π ^ (e' + 1) ∣ z - ζ ^ b := by
  rcases hζ₁ with ⟨Z, hZ⟩
  rcases hz with ⟨A, hA⟩
  have hZπ : ¬π ∣ Z := fun hd ↦ hζ₂ <| by
    rw [hZ, pow_succ]
    exact mul_dvd_mul_left _ hd
  rw [sub_eq_iff_eq_add'] at hZ hA
  have hdvd₀ : π ∣ π ^ e' :=
    dvd_pow_self π (by omega)
  rcases exists_pow_sub_one_eq_of_self hP Z with ⟨r, hr⟩
  rcases exists_pow_sub_one_eq_of_self hP A with ⟨r', hr'⟩
  rw [← hZ, hζ, sub_self] at hr
  have hZ₀ : Z ^ p + (P * Z + π ^ e' * (P * Z ^ 2 * r)) = 0 :=
    (mul_eq_zero.mp hr.symm).resolve_left (pow_ne_zero _ hπ.ne_zero)
  have hZd : π ∣ Z ^ p + P * Z := by
    have hsum : Z ^ p + P * Z = -(π ^ e' * (P * Z ^ 2 * r)) := by
      linear_combination hZ₀
    rw [hsum]
    exact (hdvd₀.mul_right _).neg_right
  rw [hA, hr', pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)] at h
  have hAd : π ∣ A ^ p + P * A := by
    have hsum : A ^ p + P * A = A ^ p + (P * A + π ^ e' * (P * A ^ 2 * r')) -
        π ^ e' * (P * A ^ 2 * r') := by
      ring1
    rw [hsum]
    exact dvd_sub h (hdvd₀.mul_right _)
  have hp : Z ^ p = Z ^ (p - 1) * Z := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  have hfixd : π ∣ A ^ p - Z ^ (p - 1) * A := by
    have hprod : Z * (A ^ p - Z ^ (p - 1) * A) = Z * (A ^ p + P * A) - A * (Z ^ p + P * Z) := by
      rw [hp]
      ring1
    exact (hπ.dvd_or_dvd (hprod ▸ dvd_sub (hAd.mul_left _) (hZd.mul_left _))).resolve_left hZπ
  rcases hfix A Z hZπ hfixd with ⟨b, hb⟩
  rcases exists_one_add_mul_pow_eq (π := π) Z b he with ⟨q, hq⟩
  refine ⟨b, ?_⟩
  rw [hZ, hA, hq]
  have heq : 1 + π ^ e' * A - (1 + b * (π ^ e' * Z) + π ^ (e' + 1) * q) =
      π ^ e' * (A - b * Z) - π ^ (e' + 1) * q := by
    ring1
  rw [heq, pow_succ]
  exact dvd_sub (mul_dvd_mul_left _ hb) (dvd_mul_right _ _)

lemma mul_eq_of_pow_eq_one {e : ℕ} (hπ : Prime π) (hP : (p : R) = π ^ e * P) (hPu : IsUnit P)
    (he : 1 ≤ e') (hζ : ζ ^ p = 1) (hζ₁ : π ^ e' ∣ ζ - 1) (hζ₂ : ¬π ^ (e' + 1) ∣ ζ - 1) :
    (p - 1) * e' = e := by
  rcases hζ₁ with ⟨Z, hZ⟩
  have hZπ : ¬π ∣ Z := fun hd ↦ hζ₂ <| by
    rw [hZ, pow_succ]
    exact mul_dvd_mul_left _ hd
  have hZ₀ : Z ≠ 0 := fun h₀ ↦ hZπ (h₀ ▸ dvd_zero π)
  have ht : ζ - 1 ≠ 0 := by
    rw [hZ]
    exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hZ₀
  rcases exists_one_add_pow_eq (Fact.out : p.Prime) (ζ - 1) with ⟨r, hr⟩
  rw [add_sub_cancel, hζ] at hr
  have hp : p = (p - 1) + 1 :=
    (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm
  have hkey : (ζ - 1) ^ (p - 1) = π ^ e * (-(P * (1 + (ζ - 1) * r))) := by
    refine mul_left_cancel₀ ht ?_
    have hpow : (ζ - 1) * (ζ - 1) ^ (p - 1) = (ζ - 1) ^ p := by
      rw [← pow_succ', ← hp]
    rw [hpow]
    linear_combination -hr + (-(ζ - 1) * (1 + (ζ - 1) * r)) * hP
  have htπ : π ∣ ζ - 1 := by
    rw [hZ]
    exact Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _
  have hWπ : ¬π ∣ -(P * (1 + (ζ - 1) * r)) := by
    rw [dvd_neg, hPu.dvd_mul_left]
    intro hd
    refine hπ.not_isUnit (isUnit_of_dvd_one ?_)
    have h₁ : (1 : R) = 1 + (ζ - 1) * r - (ζ - 1) * r := by
      ring1
    rw [h₁]
    exact dvd_sub hd (htπ.mul_right _)
  rw [hZ, mul_pow, ← pow_mul] at hkey
  rcases lt_trichotomy (e' * (p - 1)) e with hlt | heq | hlt
  · rcases Nat.exists_eq_add_of_lt hlt with ⟨k, hk⟩
    have h₁ : π ^ (e' * (p - 1)) * Z ^ (p - 1) =
        π ^ (e' * (p - 1)) * (π * (π ^ k * -(P * (1 + π ^ e' * Z * r)))) := by
      rw [hkey, hk]
      ring1
    refine absurd (hπ.dvd_of_dvd_pow (Dvd.intro _ (mul_left_cancel₀ (pow_ne_zero _ hπ.ne_zero)
      h₁).symm)) hZπ
  · rw [mul_comm]
    exact heq
  · rcases Nat.exists_eq_add_of_lt hlt with ⟨k, hk⟩
    have h₁ : π ^ e * -(P * (1 + π ^ e' * Z * r)) = π ^ e * (π * (π ^ k * Z ^ (p - 1))) := by
      rw [← hkey, hk]
      ring1
    exact absurd (Dvd.intro _ (mul_left_cancel₀ (pow_ne_zero _ hπ.ne_zero) h₁).symm)
      (by rwa [hZ] at hWπ)

end Ring

lemma exists_natCast_eq_of_pow_eq_self {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {t : k} (h : t ^ p = t) : ∃ b : ℕ, t = b := by
  have ht : t ∈ (ZMod.castHom (m := p) dvd_rfl k).fieldRange := by
    rw [ZMod.fieldRange_castHom_eq_bot p]
    exact (Subfield.mem_bot_iff_pow_eq_self k p).mpr h
  rcases ht with ⟨z, rfl⟩
  exact ⟨z.val, by simp⟩

section Field

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {π : 𝒪[K]}

lemma mem_unitFiltration_iff_pow_dvd (hπ : Irreducible π) (x : unitFiltration K 1) (n : ℕ) :
    (x : Kˣ) ∈ unitFiltration K n ↔ π ^ n ∣ (unitFiltrationToIntegerUnits 1 x : 𝒪[K]) - 1 := by
  rcases n with _ | n
  · simpa using unitFiltration_antitone (K := K) (Nat.zero_le 1) x.2
  · have hmap : Units.map (Subring.subtype 𝒪[K]).toMonoidHom (unitFiltrationToIntegerUnits 1 x) =
        (x : Kˣ) :=
      Units.ext rfl
    rw [← hmap, mem_unitFiltration_succ_congr, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]

variable {p : ℕ} {α : ℕ → K} {ζ ζ' : K}

lemma exists_units_coe_eq (hp : p ≠ 0) (hζ : ζ ^ p = 1) : ∃ u : 𝒪[K]ˣ, ((u : 𝒪[K]) : K) = ζ := by
  have h₀ : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp] at hζ
    exact zero_ne_one hζ
  have hv : valuation K ζ = 1 :=
    (pow_eq_one_iff.mp (by rw [← map_pow, hζ, map_one])).resolve_right hp
  rcases mem_unitFiltration_iff_exists.mp ((mem_unitFiltration_zero (Units.mk0 ζ h₀)).mpr hv) with
    ⟨u, -, hu⟩
  exact ⟨u, hu⟩

lemma coe_jumpProd (δ : ℕ → unitFiltration K 1) (j : ℕ) :
    (((JumpFiltration.jumpProd p δ j : unitFiltration K 1) : Kˣ) : K) = ∏ l ∈ range j,
      ((δ l : Kˣ) : K) ^ p ^ l := by
  rw [JumpFiltration.jumpProd]
  exact map_prod ((Units.coeHom K).comp (unitFiltration K 1).subtype) _ _

variable [Fact p.Prime] [FinitePadicExtension K p]

local notation "rK" => padicValNat p (absoluteRamificationIndex K p)

variable (p) in
lemma exists_natCast_eq_pow_mul (hπ : Irreducible π) :
    ∃ P : 𝒪[K], IsUnit P ∧ (p : 𝒪[K]) = π ^ absoluteRamificationIndex K p * P := by
  have hpK : (p : K) ≠ 0 :=
    NeZero.ne _
  have hspan : Ideal.span {(p : 𝒪[K])} = 𝓂[K] ^ natCastValuation K p hpK :=
    span_natCast_eq_maximalIdeal_pow K p hpK
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton,
    ← absoluteRamificationIndex_eq_natCastValuation K p] at hspan
  rcases hspan.symm with ⟨u, hu⟩
  exact ⟨u, u.isUnit, hu.symm⟩

lemma exists_dvd_sub_pow (hπ : Irreducible π) (s : 𝒪[K]) : ∃ θ, π ∣ s - θ ^ p := by
  have hc : CharP 𝓀[K] p :=
    charP_residueField K p
  have he : ExpChar 𝓀[K] p :=
    .prime Fact.out
  rcases surjective_frobenius 𝓀[K] p (residue 𝒪[K] s) with ⟨y, hy⟩
  rcases residue_surjective y with ⟨θ, rfl⟩
  refine ⟨θ, (hπ.residue_eq_zero_iff_dvd _).mp ?_⟩
  rw [map_sub, map_pow, ← hy, frobenius_def, sub_self]

lemma exists_natCast_dvd_sub_mul (hπ : Irreducible π) (A Z : 𝒪[K]) (hZ : ¬π ∣ Z)
    (h : π ∣ A ^ p - Z ^ (p - 1) * A) : ∃ b : ℕ, π ∣ A - b * Z := by
  have hc : CharP 𝓀[K] p :=
    charP_residueField K p
  have hZ₀ : residue 𝒪[K] Z ≠ 0 :=
    fun h₀ ↦ hZ ((hπ.residue_eq_zero_iff_dvd _).mp h₀)
  have h' : residue 𝒪[K] A ^ p = residue 𝒪[K] Z ^ (p - 1) * residue 𝒪[K] A := by
    rw [← map_pow, ← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub]
    exact (hπ.residue_eq_zero_iff_dvd _).mpr h
  have hp : p = p - 1 + 1 :=
    (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm
  rcases exists_natCast_eq_of_pow_eq_self (p := p)
    (t := residue 𝒪[K] A / residue 𝒪[K] Z) (by
      rw [div_pow, h', div_eq_div_iff (pow_ne_zero _ hZ₀) hZ₀]
      conv_rhs => rw [hp, pow_succ]
      ring1) with ⟨b, hb⟩
  refine ⟨b, (hπ.residue_eq_zero_iff_dvd _).mp ?_⟩
  rw [div_eq_iff hZ₀] at hb
  rw [map_sub, map_mul, map_natCast, hb, sub_self]

lemma exists_level_of_isPrimitiveRoot (hπ : Irreducible π) {u : 𝒪[K]ˣ}
    (hζ : IsPrimitiveRoot ((u : 𝒪[K]) : K) p) : ∃ n, 1 ≤ n ∧ π ^ n ∣ (u : 𝒪[K]) - 1 ∧
      ¬π ^ (n + 1) ∣ (u : 𝒪[K]) - 1 ∧ (p - 1) * n = absoluteRamificationIndex K p := by
  have hu : (u : 𝒪[K]) ^ p = 1 :=
    Subtype.ext (by simpa using hζ.pow_eq_one)
  have hne : (u : 𝒪[K]) - 1 ≠ 0 := by
    intro h
    refine hζ.ne_one (Fact.out : p.Prime).one_lt ?_
    rw [sub_eq_zero.mp h]
    rfl
  rcases exists_natCast_eq_pow_mul (K := K) p hπ with ⟨P, hPu, hP⟩
  have he : absoluteRamificationIndex K p ≠ 0 :=
    (absoluteRamificationIndex_pos K p).ne'
  have hd : π ∣ (u : 𝒪[K]) - 1 := by
    refine dvd_sub_one_of_pow_eq_one hπ.prime ?_ hu
    rw [hP]
    exact Dvd.dvd.mul_right (dvd_pow_self π he) _
  rcases IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπ with ⟨n, w, hw⟩
  have hn₁ : π ^ n ∣ (u : 𝒪[K]) - 1 := by
    rw [hw]
    exact dvd_mul_left _ _
  have hn₂ : ¬π ^ (n + 1) ∣ (u : 𝒪[K]) - 1 := by
    rw [hw, pow_succ, mul_comm (w : 𝒪[K]), mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)]
    exact fun h ↦ hπ.not_isUnit (isUnit_of_dvd_unit h w.isUnit)
  have hn : 1 ≤ n := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    exact hn₂ (by simpa using hd)
  exact ⟨n, hn, hn₁, hn₂, mul_eq_of_pow_eq_one hπ.prime hP hPu hn hu hn₁ hn₂⟩

variable (K p) in
/-- The **level** `e' = e / (p - 1)` of a primitive `p`-th root of unity `ζ` of a `p`-adic field of
absolute ramification index `e`: `v_K(ζ - 1) = e'` (`unitDepth_eq_rootLevel`), the level at which
the shift `ρ(x) = min(px, x + e)` of the jump set of `K` (LMFDB `lf.jump_set`) changes its form. -/
noncomputable def rootLevel : ℕ :=
  absoluteRamificationIndex K p / (p - 1)

lemma rootLevel_eq_of_mul_eq {n : ℕ} (hn : (p - 1) * n = absoluteRamificationIndex K p) :
    rootLevel K p = n := by
  rw [rootLevel, ← hn, Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)]

lemma sub_one_mul_rootLevel (hζ : IsPrimitiveRoot ζ p) :
    (p - 1) * rootLevel K p = absoluteRamificationIndex K p := by
  rcases exists_units_coe_eq (Fact.out : p.Prime).ne_zero hζ.pow_eq_one with ⟨u, rfl⟩
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
  rcases exists_level_of_isPrimitiveRoot hπ hζ with ⟨n, -, -, -, hn⟩
  rw [rootLevel_eq_of_mul_eq hn, hn]

lemma exists_natCast_eq_pow_sub_one_mul (hζ : IsPrimitiveRoot ζ p) (hπ : Irreducible π) :
    ∃ P : 𝒪[K], IsUnit P ∧ (p : 𝒪[K]) = π ^ ((p - 1) * rootLevel K p) * P := by
  rw [sub_one_mul_rootLevel hζ]
  exact exists_natCast_eq_pow_mul p hπ

lemma exists_rep_eq_of_dvd_sub_one (hπ : Irreducible π) {y : 𝒪[K]} (h : π ∣ y - 1) :
    ∃ g : unitFiltration K 1, (unitFiltrationToIntegerUnits 1 g : 𝒪[K]) = y := by
  have hy : IsUnit y := by
    refine (residue_ne_zero_iff_isUnit y).mp fun h₀ ↦ hπ.not_isUnit (isUnit_of_dvd_one ?_)
    have h₁ : (1 : 𝒪[K]) = y - (y - 1) := by
      ring1
    rw [h₁]
    exact dvd_sub ((hπ.residue_eq_zero_iff_dvd _).mp h₀) h
  rcases hy with ⟨u, rfl⟩
  have hmem : Units.map (Subring.subtype 𝒪[K]).toMonoidHom u ∈ unitFiltration K (0 + 1) := by
    rw [mem_unitFiltration_succ_congr, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, zero_add, pow_one]
    exact h
  exact ⟨⟨_, hmem⟩, rfl⟩

lemma exists_coe_eq_of_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ p) :
    ∃ g : unitFiltration K 1, ((g : Kˣ) : K) = ζ := by
  rcases exists_units_coe_eq (Fact.out : p.Prime).ne_zero hζ.pow_eq_one with ⟨u, rfl⟩
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
  rcases exists_level_of_isPrimitiveRoot hπ hζ with ⟨n, hn, hn₁, -⟩
  rcases exists_rep_eq_of_dvd_sub_one hπ (dvd_trans (dvd_pow_self π (by omega)) hn₁) with ⟨g, hg⟩
  exact ⟨g, congrArg (fun y : 𝒪[K] ↦ (y : K)) hg⟩

/-- The **principal unit** given by a primitive `p`-th root of unity of a `p`-adic field. -/
noncomputable def principalRoot (hζ : IsPrimitiveRoot ζ p) : unitFiltration K 1 :=
  (exists_coe_eq_of_isPrimitiveRoot hζ).choose

lemma coe_principalRoot (hζ : IsPrimitiveRoot ζ p) : ((principalRoot hζ : Kˣ) : K) = ζ :=
  (exists_coe_eq_of_isPrimitiveRoot hζ).choose_spec

lemma isPrimitiveRoot_coe_principalRoot (hζ : IsPrimitiveRoot ζ p) : IsPrimitiveRoot
    (((unitFiltrationToIntegerUnits 1 (principalRoot hζ) : 𝒪[K]ˣ) : 𝒪[K]) : K) p := by
  rwa [coe_unitFiltrationToIntegerUnits, coe_principalRoot]

lemma one_le_rootLevel (hζ : IsPrimitiveRoot ζ p) (hπ : Irreducible π) : 1 ≤ rootLevel K p := by
  rcases exists_level_of_isPrimitiveRoot hπ (isPrimitiveRoot_coe_principalRoot hζ) with
    ⟨n, hn, -, -, hn'⟩
  rwa [rootLevel_eq_of_mul_eq hn']

lemma pow_rootLevel_dvd (hζ : IsPrimitiveRoot ζ p) (hπ : Irreducible π) :
    π ^ rootLevel K p ∣ (unitFiltrationToIntegerUnits 1 (principalRoot hζ) : 𝒪[K]) - 1 := by
  rcases exists_level_of_isPrimitiveRoot hπ (isPrimitiveRoot_coe_principalRoot hζ) with
    ⟨n, -, hn, -, hn'⟩
  rwa [rootLevel_eq_of_mul_eq hn']

lemma not_pow_succ_rootLevel_dvd (hζ : IsPrimitiveRoot ζ p) (hπ : Irreducible π) :
    ¬π ^ (rootLevel K p + 1) ∣ (unitFiltrationToIntegerUnits 1 (principalRoot hζ) : 𝒪[K]) - 1 := by
  rcases exists_level_of_isPrimitiveRoot hπ (isPrimitiveRoot_coe_principalRoot hζ) with
    ⟨n, -, -, hn, hn'⟩
  rwa [rootLevel_eq_of_mul_eq hn']

lemma exists_eq_pow_of_rootLevel_lt (hζ : IsPrimitiveRoot ζ p) {a : ℕ} (ha : rootLevel K p < a)
    {x : unitFiltration K 1} (h : (x : Kˣ) ∈ unitFiltration K (jumpShift p (rootLevel K p) a)) :
    ∃ y : unitFiltration K 1, (y : Kˣ) ∈ unitFiltration K a ∧ x = y ^ p := by
  have hpK : (p : K) ≠ 0 :=
    NeZero.ne _
  have he : natCastValuation K p hpK = (p - 1) * rootLevel K p := by
    rw [sub_one_mul_rootLevel hζ, absoluteRamificationIndex_eq_natCastValuation]
  have hi : natCastValuation K p hpK < (p - 1) * a := by
    rw [he]
    exact Nat.mul_lt_mul_of_pos_left ha (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  rw [jumpShift_of_ge ha.le, ← he, ← map_powMonoidHom_unitFiltration_of_prime Fact.out hpK hi] at h
  rcases h with ⟨y, hy, hyx⟩
  have hy₁ : y ∈ unitFiltration K 1 :=
    unitFiltration_antitone (Nat.one_le_of_lt ha) hy
  exact ⟨⟨y, hy₁⟩, hy, Subtype.ext hyx.symm⟩

/-- **The filtered group of principal units** of a `p`-adic field `K` containing a primitive `p`-th
root of unity `ζ`: the principal units with the unit filtration and the element `ζ`, a filtered
group with Pagano's shift `ρ_{e,p}`, `e = (p - 1) e'` the absolute ramification index of `K`
(Pagano, *Jump sets in local fields*, §1.2 and §5; LMFDB `lf.jump_set`). -/
noncomputable def jumpFiltrationOfRoot (hζ : IsPrimitiveRoot ζ p) :
    JumpFiltration (unitFiltration K 1) p (rootLevel K p) where
  U n := (unitFiltration K n).subgroupOf (unitFiltration K 1)
  succ_le n x hx :=
    unitFiltration_antitone n.le_succ hx
  one_eq_top :=
    Subgroup.subgroupOf_self _
  eq_one_of_forall_mem {x} h := by
    have hmem : (x : Kˣ) ∈ ⨅ i, unitFiltration K i :=
      Subgroup.mem_iInf.mpr h
    rw [iInf_unitFiltration, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  pow_mem {a x} h := by
    rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
    rcases exists_natCast_eq_pow_sub_one_mul hζ hπ with ⟨P, -, hP⟩
    rw [Subgroup.mem_subgroupOf] at h ⊢
    rw [mem_unitFiltration_iff_pow_dvd hπ] at h ⊢
    rw [map_pow, Units.val_pow_eq_pow_val]
    exact pow_jumpShift_dvd_pow_sub_one hP h
  mem_succ_of_pow_mem {a x} ha h h' := by
    rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
    rcases exists_natCast_eq_pow_sub_one_mul hζ hπ with ⟨P, hPu, hP⟩
    rw [Subgroup.mem_subgroupOf] at h h' ⊢
    rw [mem_unitFiltration_iff_pow_dvd hπ] at h h' ⊢
    rw [map_pow, Units.val_pow_eq_pow_val] at h'
    exact pow_succ_dvd_sub_one hπ.prime hP hPu ha h h'
  exists_eq_pow_mul {a x} ha ha₁ h := by
    rw [Subgroup.mem_subgroupOf] at h
    rcases lt_or_gt_of_ne ha with hlt | hlt
    · rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
      rcases exists_natCast_eq_pow_sub_one_mul hζ hπ with ⟨P, -, hP⟩
      rw [mem_unitFiltration_iff_pow_dvd hπ, jumpShift_of_le hlt.le] at h
      rcases exists_pow_dvd_sub_pow hP hlt (exists_dvd_sub_pow hπ) h with ⟨y, hy, hxy⟩
      rcases exists_rep_eq_of_dvd_sub_one hπ
        (dvd_trans (dvd_pow_self π (Nat.one_le_iff_ne_zero.mp ha₁)) hy) with ⟨g, rfl⟩
      refine ⟨g, ?_, x * (g ^ p)⁻¹, ?_, (mul_inv_cancel_comm_assoc _ _).symm⟩
      · rwa [Subgroup.mem_subgroupOf, mem_unitFiltration_iff_pow_dvd hπ]
      · rw [Subgroup.mem_subgroupOf, mem_unitFiltration_iff_pow_dvd hπ, jumpShift_of_le hlt.le,
          map_mul, map_inv, map_pow]
        refine dvd_coe_mul_inv_sub_one ?_
        rwa [Units.val_pow_eq_pow_val]
    · rcases exists_eq_pow_of_rootLevel_lt hζ hlt h with ⟨y, hy, rfl⟩
      exact ⟨y, hy, 1, one_mem _, (mul_one _).symm⟩
  exists_eq_pow {a x} ha h := by
    rcases exists_eq_pow_of_rootLevel_lt hζ ha h with ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  ζ := principalRoot hζ
  ζ_mem := by
    rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
    rw [Subgroup.mem_subgroupOf, mem_unitFiltration_iff_pow_dvd hπ]
    exact pow_rootLevel_dvd hζ hπ
  ζ_notMem := by
    rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
    rw [Subgroup.mem_subgroupOf, mem_unitFiltration_iff_pow_dvd hπ]
    exact not_pow_succ_rootLevel_dvd hζ hπ
  ζ_pow := by
    refine Subtype.ext (Units.ext ?_)
    simpa [coe_principalRoot] using hζ.pow_eq_one
  exists_eq_ζ_pow_mul {z} hz h := by
    rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
    rcases exists_natCast_eq_pow_sub_one_mul hζ hπ with ⟨P, -, hP⟩
    rw [Subgroup.mem_subgroupOf] at hz h
    rw [mem_unitFiltration_iff_pow_dvd hπ] at hz h
    rw [map_pow, Units.val_pow_eq_pow_val] at h
    have hu : (unitFiltrationToIntegerUnits 1 (principalRoot hζ) : 𝒪[K]) ^ p = 1 :=
      Subtype.ext (by simpa [coe_principalRoot] using hζ.pow_eq_one)
    rcases exists_natCast_pow_dvd_sub_pow hπ.prime hP (one_le_rootLevel hζ hπ) hu
      (pow_rootLevel_dvd hζ hπ) (not_pow_succ_rootLevel_dvd hζ hπ) (exists_natCast_dvd_sub_mul hπ)
      hz h with ⟨b, hb⟩
    refine ⟨b, z * (principalRoot hζ ^ b)⁻¹, ?_, (mul_inv_cancel_comm_assoc _ _).symm⟩
    rw [Subgroup.mem_subgroupOf, mem_unitFiltration_iff_pow_dvd hπ, map_mul, map_inv, map_pow]
    refine dvd_coe_mul_inv_sub_one ?_
    rwa [Units.val_pow_eq_pow_val]

lemma le_unitDepth_iff_of_ne_zero {x : unitFiltration K 1} (hx : x ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    (n : ℤ) ≤ unitDepth ((x : Kˣ) : K) ↔ (x : Kˣ) ∈ unitFiltration K n := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
  have hne : ((x : Kˣ) : K) - 1 ≠ 0 := fun h ↦
    hx (Subtype.ext (Units.ext (sub_eq_zero.mp h)))
  rw [unitDepth, dite_eq_right hne, le_toAdd_normalizedValuation_iff_valuation_le_zpow
    (normalizedValuation_irreducible hπ), zpow_natCast, Units.val_mk0,
    mem_unitFiltration_iff_valuation_sub_one_le hn hπ, Units.val_mk0]

lemma one_le_unitDepth {x : unitFiltration K 1} (hx : x ≠ 1) : 1 ≤ unitDepth ((x : Kˣ) : K) :=
  (le_unitDepth_iff_of_ne_zero (n := 1) hx one_ne_zero).mpr x.2

lemma unitDepth_coe_nonneg (x : unitFiltration K 1) : 0 ≤ unitDepth ((x : Kˣ) : K) := by
  by_cases hx : x = 1
  · simp [hx, unitDepth]
  · exact zero_le_one.trans (one_le_unitDepth hx)

variable {g : unitFiltration K 1} {n i : ℕ} {u v : List ℤ}

lemma unitDepth_eq_of_isLevel (hζ : IsPrimitiveRoot ζ p)
    (h : (jumpFiltrationOfRoot hζ).IsLevel g n) : unitDepth ((g : Kˣ) : K) = n := by
  have hg : g ≠ 1 :=
    h.ne_one
  have hn : n ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp h.pos
  have h₁ : (n : ℤ) ≤ unitDepth ((g : Kˣ) : K) :=
    (le_unitDepth_iff_of_ne_zero hg hn).mpr h.1
  have h₂ : ¬((n + 1 : ℕ) : ℤ) ≤ unitDepth ((g : Kˣ) : K) := fun h' ↦
    h.2 ((le_unitDepth_iff_of_ne_zero hg n.succ_ne_zero).mp h')
  push_cast at h₂
  omega

lemma exists_coe_eq_of_unitDepth_pos {x : K} (hx : x ≠ 1) (h : 0 < unitDepth x) :
    ∃ g : unitFiltration K 1, ((g : Kˣ) : K) = x := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
  have hne : x - 1 ≠ 0 :=
    sub_ne_zero.mpr hx
  rw [unitDepth, dite_eq_right hne] at h
  have hle : valuation K (x - 1) ≤ valuation K (π : K) := by
    simpa using (le_toAdd_normalizedValuation_iff_valuation_le_zpow
      (normalizedValuation_irreducible hπ) 1 (Units.mk0 (x - 1) hne)).mp h
  have hlt : valuation K (x - 1) < 1 :=
    hle.trans_lt (Valuation.integer.v_irreducible_lt_one hπ)
  have hv : valuation K (1 + (x - 1)) = 1 :=
    (valuation K).map_one_add_of_lt hlt
  rw [add_sub_cancel] at hv
  have hx₀ : x ≠ 0 := by
    rintro rfl
    simp at hv
  refine ⟨⟨Units.mk0 x hx₀, ?_⟩, rfl⟩
  rw [mem_unitFiltration_iff_valuation_sub_one_le one_ne_zero hπ, Units.val_mk0, pow_one]
  exact hle

lemma exists_coe_eq_of_pow_eq (x : unitFiltration K 1) {y : K} (hy : y ^ p = ((x : Kˣ) : K)) :
    ∃ g : unitFiltration K 1, ((g : Kˣ) : K) = y := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨π, hπ⟩
  have hc : CharP 𝓀[K] p :=
    charP_residueField K p
  have hp : p ≠ 0 :=
    (Fact.out : p.Prime).ne_zero
  have hy₀ : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hp] at hy
    exact (x : Kˣ).ne_zero hy.symm
  have hx₀ : valuation K ((x : Kˣ) : K) = 1 :=
    (mem_unitFiltration_zero (x : Kˣ)).mp (unitFiltration_antitone (Nat.zero_le 1) x.2)
  have hv : valuation K y = 1 :=
    (pow_eq_one_iff.mp (by rw [← map_pow, hy, hx₀])).resolve_right hp
  rcases mem_unitFiltration_iff_exists.mp ((mem_unitFiltration_zero (Units.mk0 y hy₀)).mpr hv) with
    ⟨u, -, hu⟩
  rw [Units.val_mk0] at hu
  subst hu
  have hpow : (u : 𝒪[K]) ^ p = (unitFiltrationToIntegerUnits 1 x : 𝒪[K]) :=
    Subtype.ext (by simpa using hy)
  have hx₁ : π ∣ (unitFiltrationToIntegerUnits 1 x : 𝒪[K]) - 1 := by
    simpa using (mem_unitFiltration_iff_pow_dvd hπ x 1).mp x.2
  have hres : (residue 𝒪[K] (u : 𝒪[K]) - 1) ^ p = 0 := by
    rw [sub_pow_char, one_pow, ← map_pow, hpow, ← map_one (residue 𝒪[K]), ← map_sub,
      (hπ.residue_eq_zero_iff_dvd _).mpr hx₁]
  have hd : π ∣ (u : 𝒪[K]) - 1 := by
    refine (hπ.residue_eq_zero_iff_dvd _).mp ?_
    rw [map_sub, map_one]
    exact pow_eq_zero_iff hp |>.mp hres
  rcases exists_rep_eq_of_dvd_sub_one hπ hd with ⟨g, hg⟩
  exact ⟨g, congrArg (fun y : 𝒪[K] ↦ (y : K)) hg⟩

lemma exists_coe_eq_of_isMikiFactor {x : K} (h : IsMikiFactor p x) :
    ∃ g : unitFiltration K 1, ((g : Kˣ) : K) = x := by
  rcases h with rfl | ⟨hx, hpos, -⟩
  · exact ⟨1, rfl⟩
  · exact exists_coe_eq_of_unitDepth_pos hx hpos

lemma coe_ne_one_iff : ((g : Kˣ) : K) ≠ 1 ↔ g ≠ 1 :=
  not_congr ⟨fun h ↦ Subtype.ext (Units.ext h), fun h ↦ by simp [h]⟩

lemma natCast_absoluteRamificationIndex (hζ : IsPrimitiveRoot ζ p) :
    (absoluteRamificationIndex K p : ℤ) = ((p : ℤ) - 1) * rootLevel K p := by
  rw [← sub_one_mul_rootLevel hζ, Nat.cast_mul, Nat.cast_sub (Fact.out : p.Prime).one_le,
    Nat.cast_one]

lemma sub_pos_natCast_prime : (0 : ℤ) < (p : ℤ) - 1 := by
  have h₁ : 1 < p := (Fact.out : p.Prime).one_lt
  omega

lemma isMikiAt_of_isMikiFactor (hζ : IsPrimitiveRoot ζ p) (hg : g ≠ 1)
    (h : IsMikiFactor p ((g : Kˣ) : K)) :
    (jumpFiltrationOfRoot hζ).IsMikiAt g (unitDepth ((g : Kˣ) : K)).toNat := by
  have hl : (jumpFiltrationOfRoot hζ).IsLevel g ((jumpFiltrationOfRoot hζ).level g) :=
    (jumpFiltrationOfRoot hζ).isLevel_level hg
  rw [unitDepth_eq_of_isLevel hζ hl, Int.toNat_natCast]
  refine ⟨hl, ?_⟩
  rcases h with h | ⟨-, -, h⟩
  · exact absurd h (coe_ne_one_iff.mpr hg)
  have hp : (0 : ℤ) < (p : ℤ) - 1 :=
    sub_pos_natCast_prime
  rw [unitDepth_eq_of_isLevel hζ hl, natCast_absoluteRamificationIndex hζ] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine .inl ⟨fun hd ↦ h₂ (by exact_mod_cast hd), ?_⟩
    have h₃ : ((jumpFiltrationOfRoot hζ).level g : ℤ) < p * rootLevel K p := by
      refine lt_of_mul_lt_mul_right ?_ hp.le
      linarith
    exact_mod_cast h₃
  · refine .inr ⟨?_, fun y hy ↦ h₂ ⟨((y : Kˣ) : K), ?_⟩⟩
    · have h₃ : ((jumpFiltrationOfRoot hζ).level g : ℤ) = p * rootLevel K p := by
        refine mul_right_cancel₀ hp.ne' ?_
        linarith
      exact_mod_cast h₃
    · rw [hy]
      simp

lemma isMikiFactor_of_isMikiAt (hζ : IsPrimitiveRoot ζ p)
    (h : (jumpFiltrationOfRoot hζ).IsMikiAt g n) : IsMikiFactor p ((g : Kˣ) : K) := by
  have hdepth : unitDepth ((g : Kˣ) : K) = n :=
    unitDepth_eq_of_isLevel hζ h.1
  have hg : g ≠ 1 :=
    h.1.ne_one
  have hp : (0 : ℤ) < (p : ℤ) - 1 :=
    sub_pos_natCast_prime
  refine .inr ⟨coe_ne_one_iff.mpr hg, zero_lt_one.trans_le (one_le_unitDepth hg), ?_⟩
  rw [hdepth, natCast_absoluteRamificationIndex hζ]
  rcases h.2 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine .inl ⟨?_, fun hd ↦ h₁ (by exact_mod_cast hd)⟩
    have h₃ : (n : ℤ) < p * rootLevel K p := by
      exact_mod_cast h₂
    linarith [mul_lt_mul_of_pos_right h₃ hp]
  · refine .inr ⟨?_, ?_⟩
    · rw [h₁]
      push_cast
      ring1
    · rintro ⟨y, hy⟩
      rcases exists_coe_eq_of_pow_eq g hy with ⟨y', rfl⟩
      exact h₂ y' (Subtype.ext (Units.ext (by simpa using hy.symm)))

lemma jumpRho_natCast (hζ : IsPrimitiveRoot ζ p) (t : ℕ) :
    jumpRho K p (t : ℤ) = jumpShift p (rootLevel K p) t := by
  rw [jumpRho, jumpShift, sub_one_mul_rootLevel hζ]
  push_cast
  rfl

variable (p) in
lemma exists_isJumpBase_pow_mul (hζ : IsPrimitiveRoot ζ p) :
    ∃ m, IsJumpBase p (rootLevel K p) m ∧ p ^ rK * m = rootLevel K p := by
  have hp : p.Prime :=
    Fact.out
  have hpos : 0 < p - 1 :=
    Nat.sub_pos_of_lt hp.one_lt
  have he : (p - 1) * rootLevel K p = absoluteRamificationIndex K p :=
    sub_one_mul_rootLevel hζ
  have hne : rootLevel K p ≠ 0 := by
    intro h
    rw [h, mul_zero] at he
    exact (absoluteRamificationIndex_pos K p).ne he
  have hval : rK = padicValNat p (rootLevel K p) := by
    rw [← he, padicValNat.mul hpos.ne' hne, padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt hpos (Nat.sub_lt hp.pos one_pos)), zero_add]
  rw [hval]
  rcases pow_padicValNat_dvd (p := p) (n := rootLevel K p) with ⟨m, hm⟩
  have hmul : p ^ padicValNat p (rootLevel K p) * m = rootLevel K p :=
    hm.symm
  refine ⟨m, ⟨fun hd ↦ pow_succ_padicValNat_not_dvd (p := p) hne ?_, ?_⟩, hmul⟩
  · rw [pow_succ]
    conv_rhs => rw [← hmul]
    exact mul_dvd_mul_left _ hd
  · have hle : m ≤ rootLevel K p :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Dvd.intro_left _ hmul)
    exact hle.trans_lt (lt_prime_mul (Nat.pos_of_ne_zero hne))

variable (p α ζ) in
/-- A **reduced Miki factorisation** (LMFDB `lf.jump_set`; Miki, Lemma 17, as quoted by Pagano,
*Jump sets in local fields*, §1.4) of an element `ζ` of a `p`-adic field: a Miki factorisation
`ζ = α₀^{p^r} ⋯ α_r` whose extended jump sequence satisfies `ρ(uᵢ) ≤ u_{i+1}`, condition (C.1) of
Pagano's definition of a jump set (§1.2: `ρ(a) ≤ b` for `a < b` in the set). This condition is what
makes the sequence unique. The knowl omits it: for `K = ℚ₂[x]/(x⁴ + 2x³ + 2x² + 2)` with `π = x`,
`e = 4`, `r = 2`, `-1 = (1 + π)⁴ α₂` with `α₂ = (1 - 2π³ - 4π² - 4π)⁻¹` of depth `7`, a
factorisation with the sequence `[1, 2, 7]`, which is the jump set of this field in the LMFDB (label
`2.1.4.6a2.1`), and for `c = 1 + π⁵` also `-1 = (1 + π)⁴ (c⁻¹)² (α₂ c²)`, with the sequence
`[1, 5, 7]` and `ρ(5) = 9 > 7`. This example is not formalised. -/
def IsReducedMikiFactorisation : Prop :=
  IsMikiFactorisation p α ζ ∧ ∀ i < rK, jumpRho K p (jumpSequence p α i) ≤ jumpSequence p α (i + 1)

lemma jumpSequence_nonneg (hζ : IsPrimitiveRoot ζ p) {k : ℕ}
    (h : ∀ i ≤ k, ∃ g : unitFiltration K 1, ((g : Kˣ) : K) = α i) (hi : i ≤ k) :
    0 ≤ jumpSequence p α i := by
  induction i with
  | zero =>
    rcases h 0 hi with ⟨g, hg⟩
    rw [jumpSequence, ← hg]
    exact unitDepth_coe_nonneg g
  | succ i ih =>
    by_cases hα : α (i + 1) = 1
    · rw [jumpSequence_succ_of_eq_one p hα]
      rcases Int.eq_ofNat_of_zero_le (ih (Nat.le_of_succ_le hi)) with ⟨n, hn⟩
      rw [hn, jumpRho_natCast hζ]
      exact Int.natCast_nonneg _
    · rcases h (i + 1) hi with ⟨g, hg⟩
      rw [jumpSequence, ite_eq_right hα, ← hg]
      exact unitDepth_coe_nonneg g

lemma toNat_jumpRho (hζ : IsPrimitiveRoot ζ p) {x : ℤ} (hx : 0 ≤ x) :
    (jumpRho K p x).toNat = jumpShift p (rootLevel K p) x.toNat := by
  rcases Int.eq_ofNat_of_zero_le hx with ⟨n, rfl⟩
  rw [jumpRho_natCast hζ]
  simp

lemma jumpSequence_of_ne_one (hα : α i ≠ 1) : jumpSequence p α i = unitDepth (α i) := by
  rcases i with _ | i
  · rfl
  · rw [jumpSequence, ite_eq_right hα]

lemma exists_isMikiData_of_isReducedMikiFactorisation (hζ : IsPrimitiveRoot ζ p)
    (hζ' : IsPrimitiveRoot ζ' p) {c : ℕ} (hc : ζ' ^ c = ζ)
    (hα : IsReducedMikiFactorisation p α ζ') :
    ∃ δ, (jumpFiltrationOfRoot hζ).IsMikiData δ (fun l ↦ (jumpSequence p α (rK - l)).toNat) rK := by
  have hcop : p.Coprime c :=
    ((hζ'.pow_iff_coprime (Fact.out : p.Prime).pos c).mp (hc ▸ hζ)).symm
  rcases hα with ⟨⟨hprod, hmiki⟩, hord⟩
  have hl : ∀ i, ∃ g : unitFiltration K 1, i ≤ rK → ((g : Kˣ) : K) = α i := by
    intro i
    by_cases hi : i ≤ rK
    · rcases exists_coe_eq_of_isMikiFactor (hmiki i hi) with ⟨g, hg⟩
      exact ⟨g, fun _ ↦ hg⟩
    · exact ⟨1, fun h ↦ absurd h hi⟩
  choose g hg using hl
  have hnn : ∀ i ≤ rK, 0 ≤ jumpSequence p α i := fun _ hi ↦
    jumpSequence_nonneg hζ (fun i hi ↦ ⟨g i, hg i hi⟩) hi
  have hsub (l : ℕ) : ((g (rK - l) : Kˣ) : K) = α (rK - l) :=
    hg _ (Nat.sub_le _ _)
  refine ⟨fun l ↦ g (rK - l) ^ c, ?_, fun l _ ↦ ?_, fun l hl h ↦ ?_, fun l hl ↦ ?_⟩
  · refine Subtype.ext (Units.ext ?_)
    rw [coe_jumpProd, ← prod_range_reflect]
    refine (coe_principalRoot hζ).trans ?_
    rw [← hc, hprod, ← prod_pow]
    refine prod_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ rK :=
      Nat.lt_succ_iff.mp (mem_range.mp hi)
    have h₁ : rK + 1 - 1 - i = rK - i := by
      omega
    have h₂ : rK - (rK - i) = i := by
      omega
    simp only [h₁, h₂, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg i hi']
    rw [pow_right_comm]
  · by_cases hgl : g (rK - l) = 1
    · exact .inl ((congrArg (· ^ c) hgl).trans (one_pow c))
    · have hα : α (rK - l) ≠ 1 := by
        rw [← hsub]
        exact coe_ne_one_iff.mpr hgl
      refine .inr ?_
      simp only [jumpSequence_of_ne_one hα]
      rw [← hsub]
      exact (isMikiAt_of_isMikiFactor hζ hgl
        (by rw [hsub]; exact hmiki _ (Nat.sub_le _ _))).pow_of_coprime hcop
  · have hgl : g (rK - l) = 1 := by
      by_contra hgl
      exact ((((jumpFiltrationOfRoot hζ).isLevel_level hgl).pow_of_coprime hcop).ne_one h)
    have hs : rK - l = rK - (l + 1) + 1 := by
      omega
    have hα : α (rK - (l + 1) + 1) = 1 := by
      rw [← hs, ← hsub, hgl]
      rfl
    simp only [hs]
    rw [jumpSequence_succ_of_eq_one p hα, toNat_jumpRho hζ (hnn _ (by omega))]
  · have hs : rK - (l + 1) + 1 = rK - l := by
      omega
    have h₁ : jumpRho K p (jumpSequence p α (rK - (l + 1))) ≤ jumpSequence p α (rK - l) := by
      rw [← hs]
      exact hord (rK - (l + 1)) (by omega)
    rw [← toNat_jumpRho hζ (hnn _ (by omega))]
    exact Int.toNat_le_toNat h₁

variable (p) in
lemma exists_isJumpBase_iterate (hζ : IsPrimitiveRoot ζ p) :
    ∃ m, IsJumpBase p (rootLevel K p) m ∧ (jumpShift p (rootLevel K p))^[rK] m = rootLevel K p := by
  rcases exists_isJumpBase_pow_mul p hζ with ⟨m, hm, hmul⟩
  exact ⟨m, hm, (iterate_jumpShift_of_pow_mul_le hmul.le).trans hmul⟩

lemma IsReducedMikiFactorisation.jumpSequence_nonneg (hα : IsReducedMikiFactorisation p α ζ')
    (hζ : IsPrimitiveRoot ζ p) (hi : i ≤ rK) : 0 ≤ jumpSequence p α i :=
  IsNonarchimedeanLocalField.jumpSequence_nonneg hζ
    (fun i hi ↦ exists_coe_eq_of_isMikiFactor (hα.1.2 i hi)) hi

/-- **Miki's existence theorem** for a `p`-adic field (Miki, *On the ramification numbers of cyclic
`p`-extensions over local fields*, Lemma 17, as quoted by Pagano, *Jump sets in local fields*, §1.4;
LMFDB `lf.jump_set`): a primitive `p`-th root of unity `ζ` of a `p`-adic field has a reduced Miki
factorisation. -/
lemma exists_isReducedMikiFactorisation (hζ : IsPrimitiveRoot ζ p) :
    ∃ α : ℕ → K, IsReducedMikiFactorisation p α ζ := by
  rcases exists_isJumpBase_iterate p hζ with ⟨m, hm, hr⟩
  rcases (jumpFiltrationOfRoot hζ).exists_forall_isMikiData hm hr with ⟨γ, hγ⟩
  let α : ℕ → K := fun i ↦ ((γ (rK - i) : Kˣ) : K)
  have hnn : ∀ i ≤ rK, 0 ≤ jumpSequence p α i := fun _ hi ↦
    jumpSequence_nonneg hζ (fun i _ ↦ ⟨γ (rK - i), rfl⟩) hi
  have hsub {i : ℕ} (hi : i ≤ rK) : α (rK - i) = ((γ i : Kˣ) : K) := by
    simp only [α, Nat.sub_sub_self hi]
  have h₁ : ∀ l ≤ rK, γ l ≠ 1 →
      (jumpSequence p α (rK - l)).toNat = (jumpFiltrationOfRoot hζ).level (γ l) := by
    intro l hl hg
    have hα : α (rK - l) ≠ 1 := by
      rw [hsub hl]
      exact coe_ne_one_iff.mpr hg
    rw [jumpSequence_of_ne_one hα, hsub hl,
      unitDepth_eq_of_isLevel hζ ((jumpFiltrationOfRoot hζ).isLevel_level hg), Int.toNat_natCast]
  have h₂ : ∀ l < rK, γ l = 1 → (jumpSequence p α (rK - l)).toNat =
      jumpShift p (rootLevel K p) (jumpSequence p α (rK - (l + 1))).toNat := by
    intro l hl hg
    have hs : rK - l = rK - (l + 1) + 1 := by
      omega
    have hα : α (rK - (l + 1) + 1) = 1 := by
      rw [← hs, hsub hl.le, hg]
      rfl
    rw [hs, jumpSequence_succ_of_eq_one p hα, toNat_jumpRho hζ (hnn _ (by omega))]
  have hdata :
      (jumpFiltrationOfRoot hζ).IsMikiData γ (fun l ↦ (jumpSequence p α (rK - l)).toNat) rK :=
    hγ _ h₁ h₂
  refine ⟨α, ⟨?_, fun i hi ↦ ?_⟩, fun i hi ↦ ?_⟩
  · have h₃ : ((principalRoot hζ : Kˣ) : K) = _ :=
      congrArg (fun x : unitFiltration K 1 ↦ ((x : Kˣ) : K)) hdata.prod_eq
    rw [coe_jumpProd, coe_principalRoot hζ, ← prod_range_reflect] at h₃
    rw [h₃]
    refine prod_congr rfl fun i hi ↦ ?_
    have h₄ : rK + 1 - 1 - i = rK - i := by
      omega
    rw [h₄]
  · rcases hdata.eq_one_or _ (Nat.sub_le rK i) with h | h
    · refine .inl ?_
      simp only [α, h]
      rfl
    · exact isMikiFactor_of_isMikiAt hζ h
  · have hs : rK - (i + 1) + 1 = rK - i := by
      omega
    have h₃ : jumpShift p (rootLevel K p) (jumpSequence p α i).toNat ≤
        (jumpSequence p α (i + 1)).toNat := by
      simpa only [hs, Nat.sub_sub_self (hi : i + 1 ≤ rK), Nat.sub_sub_self hi.le] using
        hdata.shift_le (rK - (i + 1)) (by omega)
    rw [← toNat_jumpRho hζ (hnn i hi.le)] at h₃
    have h₄ : 0 ≤ jumpSequence p α (i + 1) :=
      hnn (i + 1) hi
    have h₅ : 0 ≤ jumpRho K p (jumpSequence p α i) := by
      rcases Int.eq_ofNat_of_zero_le (hnn i hi.le) with ⟨n, hn⟩
      rw [hn, jumpRho_natCast hζ]
      exact Int.natCast_nonneg _
    omega

/-- **The independence of the jump set of the factorisation** (LMFDB `lf.jump_set`; the uniqueness
of Miki, Lemma 17, as quoted by Pagano, *Jump sets in local fields*, §1.4): the extended jump
sequence of a reduced Miki factorisation of a primitive `p`-th root of unity of a `p`-adic field
depends neither on the factorisation nor on the root of unity. -/
lemma jumpSequence_eq_of_isReducedMikiFactorisation {β : ℕ → K} (hζ : IsPrimitiveRoot ζ p)
    (hζ' : IsPrimitiveRoot ζ' p) (hα : IsReducedMikiFactorisation p α ζ)
    (hβ : IsReducedMikiFactorisation p β ζ') (hi : i ≤ rK) :
    jumpSequence p α i = jumpSequence p β i := by
  rcases exists_isJumpBase_iterate p hζ with ⟨m, hm, hr⟩
  have hp : NeZero p :=
    ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases hζ'.eq_pow_of_pow_eq_one hζ.pow_eq_one with ⟨c, -, hc⟩
  rcases exists_isMikiData_of_isReducedMikiFactorisation hζ hζ (pow_one ζ) hα with ⟨γ, hγ⟩
  rcases exists_isMikiData_of_isReducedMikiFactorisation hζ hζ' hc hβ with ⟨δ, hδ⟩
  have h₁ : (jumpSequence p α i).toNat = (jumpSequence p β i).toNat := by
    simpa only [Nat.sub_sub_self hi] using hγ.eq hδ hm hr (Nat.sub_le rK i)
  have h₂ : 0 ≤ jumpSequence p α i :=
    hα.jumpSequence_nonneg hζ hi
  have h₃ : 0 ≤ jumpSequence p β i :=
    hβ.jumpSequence_nonneg hζ hi
  omega

lemma IsReducedMikiFactorisation.exists_isMikiData (hζ : IsPrimitiveRoot ζ p)
    (hα : IsReducedMikiFactorisation p α ζ) :
    ∃ δ, (jumpFiltrationOfRoot hζ).IsMikiData δ (fun l ↦ (jumpSequence p α (rK - l)).toNat) rK :=
  exists_isMikiData_of_isReducedMikiFactorisation hζ hζ (pow_one ζ) hα

/-- **The extended jump sequence of a reduced Miki factorisation consists of positive integers**
(LMFDB `lf.jump_set`). -/
lemma IsReducedMikiFactorisation.jumpSequence_pos (hζ : IsPrimitiveRoot ζ p)
    (hα : IsReducedMikiFactorisation p α ζ) (hi : i ≤ rK) : 0 < jumpSequence p α i := by
  rcases exists_isJumpBase_iterate p hζ with ⟨m, hm, hr⟩
  rcases hα.exists_isMikiData hζ with ⟨δ, hδ⟩
  have h₁ : 1 ≤ (jumpSequence p α i).toNat := by
    simpa only [Nat.sub_sub_self hi] using hδ.one_le hm hr (Nat.sub_le rK i)
  omega

/-- **The extended jump sequence of a reduced Miki factorisation is strictly increasing** (LMFDB
`lf.jump_set`). -/
lemma IsReducedMikiFactorisation.jumpSequence_lt_succ (hζ : IsPrimitiveRoot ζ p)
    (hα : IsReducedMikiFactorisation p α ζ) (hi : i < rK) :
    jumpSequence p α i < jumpSequence p α (i + 1) := by
  rcases exists_isJumpBase_iterate p hζ with ⟨m, hm, hr⟩
  rcases hα.exists_isMikiData hζ with ⟨δ, hδ⟩
  have hs : rK - (rK - (i + 1) + 1) = i := by
    omega
  have h₁ : (jumpSequence p α i).toNat < (jumpSequence p α (i + 1)).toNat := by
    simpa only [hs, Nat.sub_sub_self (hi : i + 1 ≤ rK)] using
      hδ.lt_succ hm hr (l := rK - (i + 1)) (by omega)
  have h₂ : 0 < jumpSequence p α i :=
    hα.jumpSequence_pos hζ hi.le
  have h₃ : 0 < jumpSequence p α (i + 1) :=
    hα.jumpSequence_pos hζ hi
  omega

/-- **The first term of the extended jump sequence** of a reduced Miki factorisation is
`e' / p ^ r`, for `e' = e / (p - 1)` and `r = v_p(e)`, which is the admissibility of the jump set
(Pagano, *Jump sets in local fields*, Theorem 1.6). -/
lemma IsReducedMikiFactorisation.pow_mul_jumpSequence_zero (hζ : IsPrimitiveRoot ζ p)
    (hα : IsReducedMikiFactorisation p α ζ) : p ^ rK * jumpSequence p α 0 = rootLevel K p := by
  rcases exists_isJumpBase_pow_mul p hζ with ⟨m, hm, hmul⟩
  have hr : (jumpShift p (rootLevel K p))^[rK] m = rootLevel K p := by
    rw [iterate_jumpShift_of_pow_mul_le hmul.le, hmul]
  rcases hα.exists_isMikiData hζ with ⟨δ, hδ⟩
  have h₁ : (jumpSequence p α 0).toNat = m := by
    simpa only [Nat.sub_self] using
      hδ.eq_top hm ((iterate_jumpShift_of_pow_mul_le hmul.le).trans hmul)
  have h₂ : 0 < jumpSequence p α 0 :=
    hα.jumpSequence_pos hζ (Nat.zero_le _)
  have h₃ : jumpSequence p α 0 = m := by
    omega
  rw [h₃]
  exact_mod_cast hmul

/-- **The depth of a primitive `p`-th root of unity** `ζ` of a `p`-adic field is
`e' = e / (p - 1)`. -/
lemma unitDepth_eq_rootLevel (hζ : IsPrimitiveRoot ζ p) : unitDepth ζ = rootLevel K p := by
  have h : ((principalRoot hζ : Kˣ) : K) = ζ :=
    coe_principalRoot hζ
  rw [← h]
  exact unitDepth_eq_of_isLevel hζ
    ⟨(jumpFiltrationOfRoot hζ).ζ_mem, (jumpFiltrationOfRoot hζ).ζ_notMem⟩

variable (K p) in
/-- `w` is the **jump set** of a `p`-adic field `K` containing a primitive `p`-th root of unity, in
the sense of Pagano and Miki (LMFDB `lf.jump_set`): the extended jump sequence `[u₀, …, u_r]`,
`r = v_p(e)`, of a reduced Miki factorisation of a primitive `p`-th root of unity of `K`. Miki's
existence theorem and the independence of the factorisation show that `K` has exactly one
(`isPaganoJumpSet_iff`). As a set, it is the extended jump set of Pagano's §1.2, by condition (C.1)
and its §1.4: `I_K` is the set of the `uᵢ` with `αᵢ ≠ 1` and `β_K(uᵢ) = r - i + 1`. -/
def IsPaganoJumpSet (w : List ℤ) : Prop :=
  ∃ ζ : K, IsPrimitiveRoot ζ p ∧ ∃ β : ℕ → K, IsReducedMikiFactorisation p β ζ ∧
    (List.range (rK + 1)).map (jumpSequence p β) = w

variable (K p) in
open Classical in
/-- The **jump set** of a `p`-adic field `K` (LMFDB `lf.jump_set`; Pagano, *Jump sets in local
fields*): the increasing sequence `[u₀, …, u_r]` of `r + 1` positive integers, `r = v_p(e)`, which
is the extended jump sequence of every reduced Miki factorisation of every primitive `p`-th root of
unity of `K`, and the empty list if `K` does not contain a primitive `p`-th root of unity, in which
case the jump set of `K` is not defined. -/
noncomputable def jumpSet : List ℤ :=
  if h : ∃ w, IsPaganoJumpSet K p w then h.choose else []

lemma exists_isPaganoJumpSet (hζ : IsPrimitiveRoot ζ p) : ∃ w, IsPaganoJumpSet K p w := by
  rcases exists_isReducedMikiFactorisation hζ with ⟨α, hα⟩
  exact ⟨_, ζ, hζ, α, hα, rfl⟩

lemma IsPaganoJumpSet.eq (hu : IsPaganoJumpSet K p u) (hv : IsPaganoJumpSet K p v) : u = v := by
  rcases hu with ⟨ζ₁, hζ₁, β₁, hβ₁, rfl⟩
  rcases hv with ⟨ζ₂, hζ₂, β₂, hβ₂, rfl⟩
  refine List.map_congr_left fun i hi ↦ ?_
  exact jumpSequence_eq_of_isReducedMikiFactorisation hζ₁ hζ₂ hβ₁ hβ₂
    (Nat.lt_succ_iff.mp (List.mem_range.mp hi))

lemma isPaganoJumpSet_jumpSet (hζ : IsPrimitiveRoot ζ p) : IsPaganoJumpSet K p (jumpSet K p) := by
  rw [jumpSet, dite_eq_left (exists_isPaganoJumpSet hζ)]
  exact (exists_isPaganoJumpSet hζ).choose_spec

/-- **The jump set of a `p`-adic field containing a primitive `p`-th root of unity is well defined**
(LMFDB `lf.jump_set`): by Miki's existence theorem and the independence of the factorisation, `u` is
the extended jump sequence of a reduced Miki factorisation of a primitive `p`-th root of unity of
`K` if and only if it is the jump set of `K`. -/
lemma isPaganoJumpSet_iff (hζ : IsPrimitiveRoot ζ p) : IsPaganoJumpSet K p u ↔ u = jumpSet K p :=
  ⟨fun hu ↦ hu.eq (isPaganoJumpSet_jumpSet hζ), fun hu ↦ hu ▸ isPaganoJumpSet_jumpSet hζ⟩

/-- **The jump set of `K` is the extended jump sequence of each reduced Miki factorisation** of each
primitive `p`-th root of unity of `K`. -/
lemma jumpSet_eq_map (hζ : IsPrimitiveRoot ζ p) (hα : IsReducedMikiFactorisation p α ζ) :
    jumpSet K p = (List.range (rK + 1)).map (jumpSequence p α) :=
  ((isPaganoJumpSet_iff hζ).mp ⟨ζ, hζ, α, hα, rfl⟩).symm

/-- **A `p`-adic field without a primitive `p`-th root of unity** has the empty jump set: its jump
set is not defined. -/
lemma jumpSet_eq_nil (h : ∀ ζ : K, ¬IsPrimitiveRoot ζ p) : jumpSet K p = [] := by
  refine dite_eq_right ?_
  rintro ⟨u, ζ, hζ, -⟩
  exact h ζ hζ

/-- **The jump set has `r + 1` terms**, for `r = v_p(e)`. -/
lemma length_jumpSet (hζ : IsPrimitiveRoot ζ p) : (jumpSet K p).length = rK + 1 := by
  rcases exists_isReducedMikiFactorisation hζ with ⟨α, hα⟩
  rw [jumpSet_eq_map hζ hα, List.length_map, List.length_range]

/-- **The terms of the jump set are positive** (LMFDB `lf.jump_set`). -/
lemma pos_of_mem_jumpSet (hζ : IsPrimitiveRoot ζ p) {t : ℤ} (ht : t ∈ jumpSet K p) : 0 < t := by
  rcases exists_isReducedMikiFactorisation hζ with ⟨α, hα⟩
  rw [jumpSet_eq_map hζ hα] at ht
  rcases List.mem_map.mp ht with ⟨i, hi, rfl⟩
  exact hα.jumpSequence_pos hζ (Nat.lt_succ_iff.mp (List.mem_range.mp hi))

/-- **The jump set is strictly increasing** (LMFDB `lf.jump_set`). -/
lemma pairwise_lt_jumpSet (hζ : IsPrimitiveRoot ζ p) : (jumpSet K p).Pairwise (· < ·) := by
  rcases exists_isReducedMikiFactorisation hζ with ⟨α, hα⟩
  rw [jumpSet_eq_map hζ hα, List.pairwise_map]
  have hlt : ∀ i j, j ≤ rK → i < j → jumpSequence p α i < jumpSequence p α j := by
    intro i j
    induction j with
    | zero => exact fun _ h ↦ absurd h (Nat.not_lt_zero i)
    | succ j ih =>
      intro hj hij
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | rfl
      · exact (ih (Nat.le_of_succ_le hj) h).trans
          (hα.jumpSequence_lt_succ hζ (Nat.lt_of_succ_le hj))
      · exact hα.jumpSequence_lt_succ hζ (Nat.lt_of_succ_le hj)
  refine (List.pairwise_lt_range (n := rK + 1)).imp_of_mem fun {i j} _ hj h ↦ ?_
  exact hlt i j (Nat.lt_succ_iff.mp (List.mem_range.mp hj)) h

/-- **The jump set satisfies the committed relation** `IsNonarchimedeanLocalField.IsJumpSet`: it is
the extended jump sequence of a Miki factorisation of a primitive `p`-th root of unity. -/
lemma IsPaganoJumpSet.isJumpSet (hu : IsPaganoJumpSet K p u) : IsJumpSet K p u := by
  rcases hu with ⟨ζ, hζ, β, hβ, rfl⟩
  exact ⟨ζ, hζ, β, hβ.1, rfl⟩

end Field

end IsNonarchimedeanLocalField
