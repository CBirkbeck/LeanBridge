import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.CongruentNumber.Curve
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated

/-!
# The torsion of the congruent number curves

For a nonzero integer `n`, the only rational points of finite order of the congruent number curve
`E_n : y² = x³ - n² x` are the point at infinity and the three points `(0, 0)` and `(± n, 0)` of
order `2` (LMFDB `ec.congruent_number_curve`). Hence a positive integer `n` is congruent if and
only if `E_n(ℚ)` is infinite, that is, if and only if the rank of `E_n(ℚ)` is positive: a triangle
gives a point with `y ≠ 0`, which has infinite order.

The proof is the classical one by reduction. Over a finite field `F` of odd characteristic in which
`-1` is not a square, the curve `y² = f(x)` with `f(x) = x³ - m² x` odd has `#F + 1` points: for
every `x` exactly two of the `y` with `y² = f(x)` or `y² = f(-x) = -f(x)` exist. For a prime
`p ≡ 3 mod 4` not dividing `n`, `E_n` has good reduction at `p`, and reduction is injective on the
torsion of `E_n(ℚ)` (Tau Ceti's `WeierstrassCurve.Affine.Point.card_torsion_dvd_card_reduction`),
so that its order divides `p + 1`. By Dirichlet's theorem there are such primes `p ≡ 3 mod 8`,
which bound the `2`-part of the order by `4`, and such primes `p ≡ 2 q + 1 mod 4 q` for every odd
prime `q`, which exclude `q`. So the torsion has at most `4` points, and the four points of order
dividing `2` are all of them.

## Main results

* `WeierstrassCurve.card_point_congruentNumberCurve`: over a finite field of odd characteristic in
  which `-1` is not a square, `E_m` has `#F + 1` points for `m ≠ 0`.
* `WeierstrassCurve.card_torsion_congruentNumberCurve_dvd_add_one`: the order of the torsion of
  `E_n(ℚ)` divides `p + 1` for every prime `p ≡ 3 mod 4` not dividing `n`.
* `WeierstrassCurve.card_torsion_congruentNumberCurve_dvd_four`: it divides `4`.
* `WeierstrassCurve.isOfFinAddOrder_congruentNumberCurve_iff`: the points of finite order of
  `E_n(ℚ)` are the point at infinity and the points `(x, 0)`.
* `Rat.isCongruentNumber_iff_infinite`: a positive integer `n` is congruent if and only if
  `E_n(ℚ)` is infinite.
* `Rat.isCongruentNumber_iff_finrank_pos`: a positive integer `n` is congruent if and only if the
  rank of `E_n(ℚ)` is positive.
* `WeierstrassCurve.finrank_congruentNumberCurve_six_pos`: `E_6` has positive rank.
-/

open Finset WeierstrassCurve Affine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

namespace FiniteField

lemma card_sq_eq_add_card_sq_eq_neg (hF : ringChar F ≠ 2) (h : ¬IsSquare (-1 : F)) (c : F) :
    #{y : F | y ^ 2 = c} + #{y : F | y ^ 2 = -c} = 2 := by
  have h₁ : (#{y : F | y ^ 2 = c} : ℤ) = quadraticChar F c + 1 := by
    simpa only [Set.toFinset_ofPred] using quadraticChar_card_sqrts hF c
  have hχ : quadraticChar F (-c) = -quadraticChar F c := by
    rw [neg_eq_neg_one_mul c, map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr h, neg_one_mul]
  have h₂ : (#{y : F | y ^ 2 = -c} : ℤ) = -quadraticChar F c + 1 := by
    simpa only [Set.toFinset_ofPred, hχ] using quadraticChar_card_sqrts hF (-c)
  omega

lemma card_sq_eq_apply_of_odd (hF : ringChar F ≠ 2) (h : ¬IsSquare (-1 : F)) (f : F → F)
    (hf : ∀ x, f (-x) = -f x) : #{xy : F × F | xy.2 ^ 2 = f xy.1} = Fintype.card F := by
  have hsum : #{xy : F × F | xy.2 ^ 2 = f xy.1} = ∑ x : F, #{y : F | y ^ 2 = f x} := by
    simp only [card_filter, Fintype.sum_prod_type]
  have hneg : ∑ x : F, #{y : F | y ^ 2 = f (-x)} = ∑ x : F, #{y : F | y ^ 2 = f x} :=
    Equiv.sum_comp (Equiv.neg F) fun x ↦ #{y : F | y ^ 2 = f x}
  have htwo : ∑ x : F, (#{y : F | y ^ 2 = f x} + #{y : F | y ^ 2 = f (-x)}) = ∑ _x : F, 2 :=
    sum_congr rfl fun x _ ↦ by
      rw [hf]
      exact card_sq_eq_add_card_sq_eq_neg hF h (f x)
  rw [sum_add_distrib, hneg, sum_const, card_univ, smul_eq_mul] at htwo
  omega

end FiniteField

namespace WeierstrassCurve

/-- **The congruent number curve has `#F + 1` points over a finite field `F` in which `-1` is not a
square**, of characteristic other than `2`, when `m ≠ 0`: the polynomial `x³ - m² x` is odd, so
that for each `x` there are exactly two solutions `y` of `y² = x³ - m² x` or `y² = (-x)³ - m² (-x)`.
-/
lemma card_point_congruentNumberCurve (hF : ringChar F ≠ 2) (h : ¬IsSquare (-1 : F)) {m : F}
    (hm : m ≠ 0) : Nat.card (congruentNumberCurve m).toAffine.Point = Fintype.card F + 1 := by
  have h₂ : (2 : F) ≠ 0 :=
    Ring.two_ne_zero hF
  have : (congruentNumberCurve m).IsElliptic :=
    isElliptic_congruentNumberCurve m h₂.isUnit hm.isUnit
  classical
  rw [Nat.card_congr ((congruentNumberCurve m).toAffine.pointEquiv.trans (Equiv.refl (Option _))),
    Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_subtype,
    ← FiniteField.card_sq_eq_apply_of_odd hF h (fun x ↦ x ^ 3 - m ^ 2 * x) fun x ↦ by ring1]
  simp only [equation_congruentNumberCurve_iff]

lemma map_congruentNumberCurve {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : R) :
    (congruentNumberCurve n).map f = congruentNumberCurve (f n) := by
  ext <;> simp

lemma isOfFinAddOrder_some_congruentNumberCurve {K : Type*} [Field K] [DecidableEq K] {m x : K}
    (h : (congruentNumberCurve m).toAffine.Nonsingular x 0) : IsOfFinAddOrder (Point.some x 0 h) :=
  isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, two_pos, by
    rw [two_nsmul]
    exact Point.add_self_of_Y_eq (by simp)⟩

variable {n : ℤ}

/-- **The torsion of `E_n(ℚ)` has order dividing `p + 1`** for every prime `p ≡ 3 mod 4` not
dividing `n`: `E_n` has good reduction at `p`, reduction is injective on the torsion, as `p` is
odd, and the reduced curve has `p + 1` points. -/
lemma card_torsion_congruentNumberCurve_dvd_add_one {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hpn : ¬(p : ℤ) ∣ n) :
    Nat.card (AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point) ∣ p + 1 := by
  classical
  have : Fact p.Prime :=
    ⟨hp⟩
  have hp₂ : 2 ≤ p :=
    hp.two_le
  have hp' : Prime (p : ℤ) :=
    Nat.prime_iff_prime_int.mp hp
  let v : IsDedekindDomain.HeightOneSpectrum ℤ :=
    ⟨Ideal.span {(p : ℤ)}, (Ideal.span_singleton_prime hp'.ne_zero).mpr hp', by simp [hp.ne_zero]⟩
  have hv : v.asIdeal = Ideal.span {(p : ℤ)} :=
    rfl
  have hΔ : (congruentNumberCurve n).Δ ∉ v.asIdeal := by
    rw [hv, Ideal.mem_span_singleton, Δ_congruentNumberCurve]
    intro hd
    rcases hp'.dvd_or_dvd hd with h | h
    · have h64 : p ∣ 2 ^ 6 := by
        exact_mod_cast h
      have h2 : p ≤ 2 :=
        Nat.le_of_dvd two_pos (hp.dvd_of_dvd_pow h64)
      omega
    · exact hpn (hp'.dvd_of_dvd_pow h)
  have hu (q : ℕ) (hq : q.Prime) : (q : ℤ) ∉ v.asIdeal ^ (q - 1) := by
    rw [hv, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hd
    have hd' : p ^ (q - 1) ∣ q := by
      exact_mod_cast hd
    have hq₂ : 2 ≤ q :=
      hq.two_le
    rcases (Nat.dvd_prime hq).mp hd' with h | h
    · rw [Nat.pow_eq_one] at h
      omega
    have hpq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq).mp (h ▸ dvd_pow_self p (by omega))
    subst hpq
    have h1 : p - 1 = 1 :=
      Nat.pow_right_injective hp₂ (h.trans (pow_one p).symm)
    omega
  have : (integralModel (v.valuation ℚ).valuationSubring
      ((congruentNumberCurve n).baseChange ℚ)).IsElliptic :=
    isElliptic_integralModel_baseChange _ v hΔ
  have hE : (congruentNumberCurve n).baseChange ℚ = congruentNumberCurve (n : ℚ) := by
    rw [baseChange, map_congruentNumberCurve, algebraMap_int_eq, eq_intCast]
  rw [← hE]
  refine (Point.card_torsion_dvd_card_reduction v hu).trans ?_
  rw [card_point_reduction_baseChange (congruentNumberCurve n) v p hv, map_congruentNumberCurve,
    eq_intCast, card_point_congruentNumberCurve (by rw [ZMod.ringChar_zmod_n]; omega)
    (ZMod.exists_sq_eq_neg_one_iff.not.mpr (by omega))
    ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).not.mpr hpn), ZMod.card]

/-- **The torsion of `E_n(ℚ)` has order dividing `4`**, for `n ≠ 0`: by Dirichlet's theorem, there
are primes `p ≡ 3 mod 8` not dividing `n`, for which `4 ∥ p + 1`, and, for every odd prime `q`,
primes `p ≡ 2 q + 1 mod 4 q` not dividing `n`, for which `q ∤ p + 1`. -/
lemma card_torsion_congruentNumberCurve_dvd_four (hn : n ≠ 0) :
    Nat.card (AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point) ∣ 4 := by
  have hgood (p : ℕ) (hpn : n.natAbs < p) : ¬(p : ℤ) ∣ n := fun h ↦
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natCast_dvd.mp h)).not_gt hpn
  have hodd (q : ℕ) (hq : q.Prime) (hq₂ : q ≠ 2)
      (hqT : q ∣ Nat.card (AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point)) :
      False := by
    have hq2 : 2 ≤ q :=
      hq.two_le
    have hq₁ : q % 2 = 1 :=
      Nat.odd_iff.mp (hq.odd_of_ne_two hq₂)
    have hunit : IsUnit ((2 * q + 1 : ℕ) : ZMod (4 * q)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr <|
        ((Nat.coprime_two_right.mpr (odd_two_mul_add_one q)).pow_right 2).mul_right <|
        (Nat.coprime_mul_right_add_left 1 q 2).mpr (Nat.coprime_one_left q)
    have : NeZero (4 * q) :=
      ⟨by omega⟩
    rcases Nat.forall_exists_prime_gt_and_eq_mod hunit n.natAbs with ⟨p, hpn, hp, hpq⟩
    have hmod : p ≡ 2 * q + 1 [MOD 4 * q] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hpq
    have h4 : p % 4 = 3 := by
      have h' : p % 4 = (2 * q + 1) % 4 :=
        hmod.of_mul_right q
      omega
    have hq' : p + 1 ≡ 2 [MOD q] :=
      ((hmod.of_mul_left 4).add_right 1).trans <| by
        rw [Nat.ModEq, add_assoc, Nat.mul_add_mod_self_right]
    have h2 : q ≤ 2 :=
      Nat.le_of_dvd two_pos <| Nat.modEq_zero_iff_dvd.mp <| hq'.symm.trans <|
        Nat.modEq_zero_iff_dvd.mpr <|
        hqT.trans (card_torsion_congruentNumberCurve_dvd_add_one hp h4 (hgood p hpn))
    omega
  rcases Nat.forall_exists_prime_gt_and_eq_mod ((ZMod.isUnit_iff_coprime 3 8).mpr (by norm_num))
    n.natAbs with ⟨p, hpn, hp, hp8⟩
  have h8 : p % 8 = 3 :=
    (ZMod.natCast_eq_natCast_iff p 3 8).mp hp8
  have hT : Nat.card (AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point) ∣
      (p + 1) / 4 * 4 := by
    rw [Nat.div_mul_cancel (by omega)]
    exact card_torsion_congruentNumberCurve_dvd_add_one hp (by omega) (hgood p hpn)
  refine (Nat.coprime_of_dvd fun k hk hkT hkm ↦ ?_).dvd_of_dvd_mul_left hT
  rcases eq_or_ne k 2 with rfl | hk₂
  · omega
  · exact hodd k hk hk₂ hkT

lemma y_eq_zero_of_isOfFinAddOrder_congruentNumberCurve (hn : n ≠ 0) {x y : ℚ}
    {h : (congruentNumberCurve (n : ℚ)).toAffine.Nonsingular x y}
    (hP : IsOfFinAddOrder (Point.some x y h)) : y = 0 := by
  by_contra hy
  have hn' : (n : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr hn
  have hnz (z : ℚ) (hz : z = 0 ∨ z = n ∨ z = -n) :
      (congruentNumberCurve (n : ℚ)).toAffine.Nonsingular z 0 := by
    refine nonsingular_congruentNumberCurve_of_equation hn' ?_
    rw [equation_congruentNumberCurve_iff]
    rcases hz with rfl | rfl | rfl <;> ring1
  have hT : Nat.card (AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point) ∣ 4 :=
    card_torsion_congruentNumberCurve_dvd_four hn
  have hfin : (AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point :
      Set (congruentNumberCurve (n : ℚ)).toAffine.Point).Finite :=
    Set.finite_coe_iff.mp <| Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos hT four_pos).ne'
  have hS : ({0, .some 0 0 (hnz 0 (.inl rfl)), .some n 0 (hnz n (.inr (.inl rfl))),
      .some (-n) 0 (hnz (-n) (.inr (.inr rfl))), .some x y h} :
      Set (congruentNumberCurve (n : ℚ)).toAffine.Point) ⊆
      AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point := by
    simp [Set.insert_subset_iff, AddCommGroup.mem_torsion,
      isOfFinAddOrder_some_congruentNumberCurve, hP]
  have hcard : 5 ≤ (AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point :
      Set (congruentNumberCurve (n : ℚ)).toAffine.Point).ncard := by
    have hnn : (n : ℚ) ≠ -n := fun h ↦
      hn' (by linarith)
    refine le_of_eq_of_le ?_ (Set.ncard_le_ncard hS hfin)
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair] <;> simp [hn', hn'.symm, Ne.symm hy, hnn]
  have h4 : (AddCommGroup.torsion (congruentNumberCurve (n : ℚ)).toAffine.Point :
      Set (congruentNumberCurve (n : ℚ)).toAffine.Point).ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.le_of_dvd four_pos hT
  omega

/-- **The torsion of `E_n(ℚ)`** (LMFDB `ec.congruent_number_curve`): for a nonzero integer `n`, the
rational points of finite order of `E_n` are the point at infinity and the points `(x, 0)`, which
are the points `(0, 0)` and `(± n, 0)` of order `2`
(`eq_zero_or_eq_or_eq_neg_of_equation_congruentNumberCurve`). -/
lemma isOfFinAddOrder_congruentNumberCurve_iff (hn : n ≠ 0)
    (P : (congruentNumberCurve (n : ℚ)).toAffine.Point) :
    IsOfFinAddOrder P ↔ P = 0 ∨ ∃ x h, P = Point.some x 0 h := by
  refine ⟨fun hP ↦ ?_, ?_⟩
  · rcases P with _ | ⟨x, y, h⟩
    · exact .inl rfl
    rcases y_eq_zero_of_isOfFinAddOrder_congruentNumberCurve hn hP with rfl
    exact .inr ⟨x, h, rfl⟩
  · rintro (rfl | ⟨x, h, rfl⟩)
    · exact IsOfFinAddOrder.zero
    · exact isOfFinAddOrder_some_congruentNumberCurve h

end WeierstrassCurve

namespace Rat

variable {n : ℤ}

/-- **A positive integer `n` is congruent if and only if `E_n(ℚ)` is infinite** (LMFDB
`ec.congruent_number_curve`): a point `(x, y)` with `y ≠ 0`, which a triangle gives, has infinite
order. -/
lemma isCongruentNumber_iff_infinite (hn : 0 < n) :
    (n : ℚ).IsCongruentNumber ↔ Infinite (congruentNumberCurve (n : ℚ)).toAffine.Point := by
  have hn' : (0 : ℚ) < n :=
    Int.cast_pos.mpr hn
  refine ⟨fun h ↦ ?_, isCongruentNumber_of_infinite hn'⟩
  rcases (isCongruentNumber_iff_exists_equation hn').mp h with ⟨x, y, hxy, hy⟩
  rw [← not_finite_iff_infinite]
  intro hfin
  exact hy (y_eq_zero_of_isOfFinAddOrder_congruentNumberCurve hn.ne'
    (h := nonsingular_congruentNumberCurve_of_equation hn'.ne' hxy) (isOfFinAddOrder_of_finite _))

/-- **A positive integer `n` is congruent if and only if `E_n(ℚ)` has positive rank** (LMFDB
`ec.congruent_number_curve`, `ec.rank`): the rank of the finitely generated group `E_n(ℚ)` is
positive exactly when `E_n(ℚ)` has a point of infinite order. -/
lemma isCongruentNumber_iff_finrank_pos (hn : 0 < n) : (n : ℚ).IsCongruentNumber ↔
    0 < Module.finrank ℤ (congruentNumberCurve (n : ℚ)).toAffine.Point := by
  have hn' : (0 : ℚ) < n :=
    Int.cast_pos.mpr hn
  have : (congruentNumberCurve (n : ℚ)).IsElliptic :=
    isElliptic_congruentNumberCurve _ (isUnit_iff_ne_zero.mpr two_ne_zero) hn'.ne'.isUnit
  rw [Nat.pos_iff_ne_zero, Ne, Module.finrank_eq_zero_iff_isTorsion,
    ← isAddTorsion_iff_isTorsion_int]
  refine ⟨fun h htors ↦ ?_, fun h ↦ ?_⟩
  · rcases (isCongruentNumber_iff_exists_equation hn').mp h with ⟨x, y, hxy, hy⟩
    exact hy (y_eq_zero_of_isOfFinAddOrder_congruentNumberCurve hn.ne'
      (h := nonsingular_congruentNumberCurve_of_equation hn'.ne' hxy) (htors _))
  rcases not_forall.mp h with ⟨P, hP⟩
  rcases P with _ | ⟨x, y, hxy⟩
  · exact absurd IsOfFinAddOrder.zero hP
  refine isCongruentNumber_of_equation hn' hxy.1 fun hy ↦ hP ?_
  subst hy
  exact isOfFinAddOrder_some_congruentNumberCurve hxy

end Rat

namespace WeierstrassCurve

/-- **`E_6` has positive rank**, `6` being congruent; the knowl states that its rank is `1`. -/
lemma finrank_congruentNumberCurve_six_pos :
    0 < Module.finrank ℤ (congruentNumberCurve (6 : ℚ)).toAffine.Point := by
  simpa using (Rat.isCongruentNumber_iff_finrank_pos (n := 6) (by norm_num)).mp
    (by simpa using Rat.isCongruentNumber_six)

end WeierstrassCurve
