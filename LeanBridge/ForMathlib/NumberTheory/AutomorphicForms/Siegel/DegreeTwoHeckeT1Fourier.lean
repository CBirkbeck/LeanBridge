import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoHeckeTpFourier
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The Fourier coefficients of `F ∣ T_1(p²)` in degree `2`

Let `G(Z) = ∑ a(n, r, m) e^{2πi(nτ + rz + mω)}` on `ℋ₂`, the series converging absolutely. The
Hecke operator `T_1(p²)` of `Γ = Sp(4, ℤ)` is the sum of the slash operators of the
`p⁴ + p³ + p² + p` Borel normal forms `SiegelUpperHalfSpace.t1Rep`, with multiplier `p²`, in five
families with the same `D`. Summing the phases `e^{2πi tr(TX)}` over each family and reindexing,
`G ∣ T_1(p²)` in weight `det^κ` is the Fourier series with the coefficients
`SiegelUpperHalfSpace.heckeT₁Coeff`. The family with `D = p 1₂` and the rank-one translations
`X = l v vᵀ/p`, `l ∈ 𝔽_p^×`, `v ∈ P¹(𝔽_p)`, gives the character sum
`∑_v ∑_l e(l Q(v)/p) = p ν - p - 1`, with `ν` the number of roots of `Q = [N, R, M]` on `P¹(𝔽_p)`
(`SiegelUpperHalfSpace.t1RootCount`); the other four families give the forms `Q ∘ g_ℓ` on the
sublattices of index `p` and their quotients by `p²`. The formula was checked numerically against
the sum over the cosets on the Fourier coefficients of `χ₁₀` at `p = 2, 3`.

## Main definitions

* `SiegelUpperHalfSpace.t1RootCount`: the number of roots of `[N, R, M]` on `P¹(𝔽_p)`.
* `SiegelUpperHalfSpace.heckeT₁Coeff`: the Fourier coefficients of `G ∣ T_1(p²)`.

## Main results

* `SiegelUpperHalfSpace.hasSum_heckeOperator_T₁`: `G ∣ T_1(p²)` is the Fourier series with the
  coefficients `SiegelUpperHalfSpace.heckeT₁Coeff`.
-/

open Complex Real

namespace SiegelUpperHalfSpace

local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ

local notation "GL₄" => GL (Fin 2 ⊕ Fin 2) ℚ

local notation "Γ₂" => heckeGamma (Fin 2)

variable (p : ℕ) [Fact p.Prime] (κ : ℤ) (a : ℤ × ℤ × ℤ → ℂ)

/-- The number of lines `v ∈ P¹(𝔽_p)` on which the binary quadratic form `[N, R, M]` of
`T = (N, R, M)` vanishes modulo `p`, with `v = (0, 1)` and `v = (1, a)`. -/
def t1RootCount (T : ℤ × ℤ × ℤ) : ℕ :=
  (Finset.univ.filter fun v : Option (ZMod p) ↦ (T.1 : ZMod p) * (lineVec v 0 * lineVec v 0) +
    T.2.1 * (lineVec v 0 * lineVec v 1) + T.2.2 * (lineVec v 1 * lineVec v 1) = 0).card

/-- The **Fourier coefficient of `G ∣ T_1(p²)`** at `T = (N, R, M)`, in weight `det^κ`, for a
Fourier series `G` with coefficients `a`: `p^{3κ-6} (a(N/p², R/p, M) +
∑_{c mod p} a(N, (R + 2cN)/p, (M + Rc + Nc²)/p²)) + p^{2κ-6} (p ν - p - 1) a(N, R, M) +
p^{κ-3} (a(N, pR, p²M) + ∑_{x mod p} a(p²N, p(R + 2xN), M + Rx + Nx²))`, each term being `0` where
its argument is not integral, with `ν` the number of roots of `[N, R, M]` on `P¹(𝔽_p)`
(`SiegelUpperHalfSpace.t1RootCount`). -/
noncomputable def heckeT₁Coeff (T : ℤ × ℤ × ℤ) : ℂ :=
  (p : ℂ) ^ (3 * κ - 6) * ((if (p : ℤ) ^ 2 ∣ T.1 ∧ (p : ℤ) ∣ T.2.1 then
    a (T.1 / p ^ 2, T.2.1 / p, T.2.2) else 0) +
    ∑ c : Fin p, if (p : ℤ) ∣ T.2.1 + 2 * c * T.1 ∧ (p : ℤ) ^ 2 ∣ T.2.2 + T.2.1 * c + T.1 * c ^ 2
      then a (T.1, (T.2.1 + 2 * c * T.1) / p, (T.2.2 + T.2.1 * c + T.1 * c ^ 2) / p ^ 2) else 0) +
  (p : ℂ) ^ (2 * κ - 6) * (p * t1RootCount p T - p - 1) * a T +
  (p : ℂ) ^ (κ - 3) * (a (T.1, p * T.2.1, p ^ 2 * T.2.2) +
    ∑ x : Fin p, a (p ^ 2 * T.1, p * (T.2.1 + 2 * x * T.1), T.2.2 + T.2.1 * x + T.1 * x ^ 2))

variable {p κ a} {G : SiegelUpperHalfSpace (Fin 2) → ℂ} (Z : SiegelUpperHalfSpace (Fin 2))

lemma sum_units_stdAddChar_mul (q : ZMod p) :
    ∑ l : (ZMod p)ˣ, ZMod.stdAddChar ((l : ZMod p) * q) = (if q = 0 then (p : ℂ) else 0) - 1 := by
  have h : ∑ x : ZMod p, ZMod.stdAddChar (x * q) = ZMod.stdAddChar ((0 : ZMod p) * q) +
      ∑ x : {x : ZMod p // x ≠ 0}, ZMod.stdAddChar ((x : ZMod p) * q) :=
    Fintype.sum_eq_add_sum_subtype_ne _ 0
  rw [AddChar.sum_mulShift q (ZMod.isPrimitive_stdAddChar p), ZMod.card, zero_mul,
    AddChar.map_zero_eq_one, Nat.cast_ite, Nat.cast_zero] at h
  rw [Fintype.sum_equiv unitsEquivNeZero (fun l : (ZMod p)ˣ ↦ ZMod.stdAddChar ((l : ZMod p) * q))
    (fun x : {x : ZMod p // x ≠ 0} ↦ ZMod.stdAddChar ((x : ZMod p) * q)) fun _ ↦ rfl]
  linear_combination -h

lemma cexp_rankOne_phase (T : ℤ × ℤ × ℤ) (l : (ZMod p)ˣ) (v : Option (ZMod p)) :
    cexp (2 * π * I * ((T.1 * (((l * lineVec v 0 * lineVec v 0 : ZMod p).val : ℚ) / p) +
      T.2.1 * (((l * lineVec v 0 * lineVec v 1 : ZMod p).val : ℚ) / p) +
        T.2.2 * (((l * lineVec v 1 * lineVec v 1 : ZMod p).val : ℚ) / p) : ℚ) : ℂ)) =
      ZMod.stdAddChar ((l : ZMod p) * ((T.1 : ZMod p) * (lineVec v 0 * lineVec v 0) +
        (T.2.1 : ZMod p) * (lineVec v 0 * lineVec v 1) +
          (T.2.2 : ZMod p) * (lineVec v 1 * lineVec v 1))) := by
  have e : ((T.1 * ((l : ZMod p) * lineVec v 0 * lineVec v 0).val +
      T.2.1 * ((l : ZMod p) * lineVec v 0 * lineVec v 1).val +
        T.2.2 * ((l : ZMod p) * lineVec v 1 * lineVec v 1).val : ℤ) : ZMod p) =
      (l : ZMod p) * ((T.1 : ZMod p) * (lineVec v 0 * lineVec v 0) +
        (T.2.1 : ZMod p) * (lineVec v 0 * lineVec v 1) +
          (T.2.2 : ZMod p) * (lineVec v 1 * lineVec v 1)) := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring1
  rw [ZMod.stdAddChar_apply, ← e, ZMod.toCircle_intCast]
  congr 1
  push_cast
  ring1

lemma sum_rankOne_cexp (T : ℤ × ℤ × ℤ) :
    ∑ s : (ZMod p)ˣ × Option (ZMod p),
      cexp (2 * π * I * ((T.1 * (((s.1 * lineVec s.2 0 * lineVec s.2 0 : ZMod p).val : ℚ) / p) +
        T.2.1 * (((s.1 * lineVec s.2 0 * lineVec s.2 1 : ZMod p).val : ℚ) / p) +
          T.2.2 * (((s.1 * lineVec s.2 1 * lineVec s.2 1 : ZMod p).val : ℚ) / p) : ℚ) : ℂ)) =
      p * t1RootCount p T - p - 1 := by
  simp only [cexp_rankOne_phase]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [sum_units_stdAddChar_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, Fintype.card_option, ZMod.card, t1RootCount]
  ring1

lemma coe_t1RepΔ_eq_borelNF (i : T1Index p) : ((t1RepΔ i : GL₄) : M₄) =
    borelNF ((p : ℚ) ^ 2) ((p : ℚ) ^ (t1Exp i).1) ((p : ℚ) ^ (t1Exp i).2) (t1Data i).1
      (t1Data i).2.1 (t1Data i).2.2.1 (t1Data i).2.2.2 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [coe_t1RepΔ, t1Rep, coe_borelNFGL (pow_ne_zero 2 hp) (pow_ne_zero _ hp) (pow_ne_zero _ hp)]

lemma hasSum_heckeMonoidSlash_t1RepΔ_inl
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (3 * κ - 6) * (if (p : ℤ) ^ 2 ∣ N.1 ∧ (p : ℤ) ∣ N.2.1
      then a (N.1 / p ^ 2, N.2.1 / p, N.2.2) else 0) * liftExp 1 N.1 N.2.1 N.2.2 Z)
        (heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (t1RepΔ (.inl () : T1Index p)) G Z) := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ ((p : ℂ) ^ 2) ^ (2 * κ - 3) * (p : ℂ) ^ (-κ) * a T *
      borelExp ((p : ℚ) ^ 2) 1 p 0 T Z)
      (heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (t1RepΔ (.inl () : T1Index p)) G Z) := by
    simpa only [t1Exp, t1Data, pow_zero, pow_one, one_mul, Rat.cast_pow, Rat.cast_natCast,
      mul_zero, add_zero, Rat.cast_zero, Complex.exp_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_unit, one_smul, mul_one] using hasSum_sum_heckeMonoidSlash Z κ (S := Unit)
        (x := fun _ ↦ t1RepΔ (.inl ())) (y := fun _ ↦ (0, 0, 0))
        (fun _ ↦ coe_t1RepΔ_eq_borelNF _) (pow_ne_zero _ hp) (pow_ne_zero _ hp) hG
  refine hasSum_of_ne_zero_bij' h (fun N ↦ (N.1 / p ^ 2, N.2.1 / p, N.2.2))
    (fun N ↦ (p : ℤ) ^ 2 ∣ N.1 ∧ (p : ℤ) ∣ N.2.1) ?_ ?_ ?_ ?_
  · rintro ⟨-, -, M⟩ ⟨⟨n, rfl⟩, ⟨r, rfl⟩⟩ ⟨-, -, M'⟩ ⟨⟨n', rfl⟩, ⟨r', rfl⟩⟩ h
    simp only [Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp'),
      Prod.mk.injEq] at h
    rw [h.1, h.2.1, h.2.2]
  · intro N hN
    rw [ite_eq_right hN, mul_zero, zero_mul]
  · rintro ⟨-, -, M⟩ ⟨⟨n, rfl⟩, ⟨r, rfl⟩⟩
    rw [ite_eq_left ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩]
    simp only [Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp')]
    rw [borelExp_eq_liftExp Z (N := p ^ 2 * n) (R := p * r) (M := M) (by push_cast; ring1)
      (by push_cast; field_simp; ring1) (by push_cast; field_simp; ring1)]
    have e : ((p : ℂ) ^ 2) ^ (2 * κ - 3) * (p : ℂ) ^ (-κ) = (p : ℂ) ^ (3 * κ - 6) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hpC]
      exact congrArg _ (by push_cast; ring1)
    linear_combination (a (n, r, M) * liftExp 1 (p ^ 2 * n) (p * r) M Z) * e
  · rintro T -
    exact ⟨(p ^ 2 * T.1, p * T.2.1, T.2.2), ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, by
      simp only [Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp')]⟩

lemma coe_t1RepΔ_inr_inl (c : Fin p) :
    ((t1RepΔ (.inr (.inl c)) : GL₄) : M₄) = borelNF ((p : ℚ) ^ 2) p 1 (c : ℕ) 0 0 0 := by
  rw [coe_t1RepΔ_eq_borelNF]
  simp [t1Exp, t1Data]

lemma hasSum_heckeMonoidSlash_t1RepΔ_inr_inl (c : Fin p)
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (3 * κ - 6) *
      (if (p : ℤ) ∣ N.2.1 + 2 * c * N.1 ∧ (p : ℤ) ^ 2 ∣ N.2.2 + N.2.1 * c + N.1 * c ^ 2 then
        a (N.1, (N.2.1 + 2 * c * N.1) / p, (N.2.2 + N.2.1 * c + N.1 * c ^ 2) / p ^ 2) else 0) *
          liftExp 1 N.1 N.2.1 N.2.2 Z)
      (heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (t1RepΔ (.inr (.inl c))) G Z) := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ ((p : ℂ) ^ 2) ^ (2 * κ - 3) * (p : ℂ) ^ (-κ) * a T *
      borelExp ((p : ℚ) ^ 2) p 1 (c : ℕ) T Z)
      (heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (t1RepΔ (.inr (.inl c))) G Z) := by
    simpa only [mul_one, Rat.cast_pow, Rat.cast_natCast, mul_zero, add_zero, Rat.cast_zero,
      Complex.exp_zero, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul] using
        hasSum_sum_heckeMonoidSlash Z κ (S := Unit) (x := fun _ ↦ t1RepΔ (.inr (.inl c)))
          (y := fun _ ↦ (0, 0, 0)) (fun _ ↦ coe_t1RepΔ_inr_inl c) hp one_ne_zero hG
  refine hasSum_of_ne_zero_bij' h
    (fun N ↦ (N.1, (N.2.1 + 2 * c * N.1) / p, (N.2.2 + N.2.1 * c + N.1 * c ^ 2) / p ^ 2))
    (fun N ↦ (p : ℤ) ∣ N.2.1 + 2 * c * N.1 ∧ (p : ℤ) ^ 2 ∣ N.2.2 + N.2.1 * c + N.1 * c ^ 2)
    ?_ ?_ ?_ ?_
  · rintro ⟨N, R, M⟩ ⟨⟨r, hr⟩, ⟨m, hm⟩⟩ ⟨N', R', M'⟩ ⟨⟨r', hr'⟩, ⟨m', hm'⟩⟩ h
    simp only at hr hm hr' hm'
    simp only [hr, hm, hr', hm', Int.mul_ediv_cancel_left _ hp',
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp')] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    have hR : R = R' := by linarith
    subst hR
    have hM : M = M' := by linarith
    rw [hM]
  · intro N hN
    rw [ite_eq_right hN, mul_zero, zero_mul]
  · rintro ⟨N, R, M⟩ ⟨⟨r, hr⟩, ⟨m, hm⟩⟩
    simp only at hr hm ⊢
    have hrQ : (R : ℚ) + 2 * ((c : ℕ) : ℚ) * N = p * r := by exact_mod_cast hr
    have hmQ : (M : ℚ) + R * (c : ℕ) + N * ((c : ℕ) : ℚ) ^ 2 = p ^ 2 * m := by exact_mod_cast hm
    rw [ite_eq_left ⟨Dvd.intro r hr.symm, Dvd.intro m hm.symm⟩]
    simp only [hr, hm, Int.mul_ediv_cancel_left _ hp',
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp')]
    have hp2 : (p : ℚ) ^ 2 * 1 ≠ 0 := by simp [hp]
    have hp2' : (p : ℚ) ^ 2 * 1 ^ 2 ≠ 0 := by simp [hp]
    rw [borelExp_eq_liftExp Z (N := N) (R := R) (M := M) (by push_cast; field_simp)
      (by push_cast; rw [div_eq_iff hp2]; linear_combination -(p : ℚ) ^ 2 * hrQ)
      (by push_cast; rw [div_eq_iff hp2']; linear_combination (p : ℚ) ^ 2 * ((c : ℕ) * hrQ - hmQ))]
    have e : ((p : ℂ) ^ 2) ^ (2 * κ - 3) * (p : ℂ) ^ (-κ) = (p : ℂ) ^ (3 * κ - 6) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hpC]
      exact congrArg _ (by push_cast; ring1)
    linear_combination (a (N, r, m) * liftExp 1 N R M Z) * e
  · rintro T -
    refine ⟨(T.1, p * T.2.1 - 2 * c * T.1, T.1 * c ^ 2 - p * c * T.2.1 + p ^ 2 * T.2.2),
      ⟨⟨T.2.1, by ring1⟩, ⟨T.2.2, by ring1⟩⟩, ?_⟩
    have e₁ : p * T.2.1 - 2 * c * T.1 + 2 * c * T.1 = (p : ℤ) * T.2.1 := by ring1
    have e₂ : T.1 * c ^ 2 - p * c * T.2.1 + p ^ 2 * T.2.2 + (p * T.2.1 - 2 * c * T.1) * c +
        T.1 * c ^ 2 = (p : ℤ) ^ 2 * T.2.2 := by
      ring1
    simp only [e₁, e₂, Int.mul_ediv_cancel_left _ hp',
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp')]

lemma coe_t1RepΔ_rankOne (l : (ZMod p)ˣ) (v : Option (ZMod p)) :
    ((t1RepΔ (.inr (.inr (.inl (l, v)))) : GL₄) : M₄) = borelNF ((p : ℚ) ^ 2) p p 0
      (((l * lineVec v 0 * lineVec v 0 : ZMod p).val : ℚ) / p)
      (((l * lineVec v 0 * lineVec v 1 : ZMod p).val : ℚ) / p)
      (((l * lineVec v 1 * lineVec v 1 : ZMod p).val : ℚ) / p) := by
  rw [coe_t1RepΔ_eq_borelNF]
  simp only [t1Exp, t1Data, pow_one]

lemma hasSum_sum_heckeMonoidSlash_t1RepΔ_rankOne
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (2 * κ - 6) * (p * t1RootCount p N - p - 1) * a N *
      liftExp 1 N.1 N.2.1 N.2.2 Z)
      (∑ s : (ZMod p)ˣ × Option (ZMod p), heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (t1RepΔ (.inr (.inr (.inl s)))) G Z) := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ (((p : ℚ) ^ 2 : ℚ) : ℂ) ^ (2 * κ - 3) *
      ((p * p : ℚ) : ℂ) ^ (-κ) * a T * borelExp ((p : ℚ) ^ 2) p p 0 T Z *
        (p * t1RootCount p T - p - 1))
      (∑ s : (ZMod p)ˣ × Option (ZMod p), heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (t1RepΔ (.inr (.inr (.inl s)))) G Z) := by
    simpa only [sum_rankOne_cexp] using hasSum_sum_heckeMonoidSlash Z κ
      (y := fun s : (ZMod p)ˣ × Option (ZMod p) ↦
        ((((s.1 * lineVec s.2 0 * lineVec s.2 0 : ZMod p).val : ℚ) / p),
          (((s.1 * lineVec s.2 0 * lineVec s.2 1 : ZMod p).val : ℚ) / p),
            (((s.1 * lineVec s.2 1 * lineVec s.2 1 : ZMod p).val : ℚ) / p)))
      (fun s ↦ coe_t1RepΔ_rankOne s.1 s.2) hp hp hG
  refine h.congr_fun fun N ↦ ?_
  rw [borelExp_eq_liftExp Z (N := N.1) (R := N.2.1) (M := N.2.2) (by field_simp)
    (by field_simp; ring1) (by field_simp; ring1)]
  have e : ((p : ℂ) ^ 2) ^ (2 * κ - 3) * ((p : ℂ) * p) ^ (-κ) = (p : ℂ) ^ (2 * κ - 6) := by
    rw [mul_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hpC, ← zpow_add₀ hpC]
    exact congrArg _ (by push_cast; ring1)
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  linear_combination (-(p * t1RootCount p N - p - 1) * a N * liftExp 1 N.1 N.2.1 N.2.2 Z) * e

lemma sum_fin_cexp_mul_div_four {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (T : ℤ × ℤ × ℤ) :
    ∑ s : Fin n × Fin m, cexp (2 * π * I * ((T.1 * 0 + T.2.1 * ((s.1 : ℕ) / n : ℚ) +
      T.2.2 * ((s.2 : ℕ) / m : ℚ) : ℚ) : ℂ)) =
        (if (n : ℤ) ∣ T.2.1 then (n : ℂ) else 0) * (if (m : ℤ) ∣ T.2.2 then (m : ℂ) else 0) := by
  rw [← sum_fin_cexp_mul_div hn T.2.1, ← sum_fin_cexp_mul_div hm T.2.2, Fintype.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t₀ _ ↦ Finset.sum_congr rfl fun t₁ _ ↦ ?_
  rw [mul_zero, zero_add, Rat.cast_add, mul_add, Complex.exp_add]

lemma sum_fin_cexp_mul_div_five {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (T : ℤ × ℤ × ℤ) :
    ∑ s : Fin n × Fin m, cexp (2 * π * I * ((T.1 * ((s.2 : ℕ) / m : ℚ) +
      T.2.1 * ((s.1 : ℕ) / n : ℚ) + T.2.2 * 0 : ℚ) : ℂ)) =
        (if (n : ℤ) ∣ T.2.1 then (n : ℂ) else 0) * (if (m : ℤ) ∣ T.1 then (m : ℂ) else 0) := by
  rw [← sum_fin_cexp_mul_div hn T.2.1, ← sum_fin_cexp_mul_div hm T.1, Fintype.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t₀ _ ↦ Finset.sum_congr rfl fun t₁ _ ↦ ?_
  rw [mul_zero, add_zero, Rat.cast_add, mul_add, Complex.exp_add, mul_comm]

lemma coe_t1RepΔ_four (b : Fin p) (w : Fin (p ^ 2)) :
    ((t1RepΔ (.inr (.inr (.inr (.inl (b, w))))) : GL₄) : M₄) =
      borelNF ((p : ℚ) ^ 2) p ((p : ℚ) ^ 2) 0 0 ((b : ℕ) / p) ((w : ℕ) / (p ^ 2 : ℕ)) := by
  rw [coe_t1RepΔ_eq_borelNF]
  simp [t1Exp, t1Data]

lemma hasSum_sum_heckeMonoidSlash_t1RepΔ_four
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (κ - 3) * a (N.1, p * N.2.1, p ^ 2 * N.2.2) *
      liftExp 1 N.1 N.2.1 N.2.2 Z)
      (∑ s : Fin p × Fin (p ^ 2), heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (t1RepΔ (.inr (.inr (.inr (.inl s))))) G Z) := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ (((p : ℚ) ^ 2 : ℚ) : ℂ) ^ (2 * κ - 3) *
      ((p * p ^ 2 : ℚ) : ℂ) ^ (-κ) * a T * borelExp ((p : ℚ) ^ 2) p ((p : ℚ) ^ 2) 0 T Z *
        ((if (p : ℤ) ∣ T.2.1 then (p : ℂ) else 0) *
          if ((p ^ 2 : ℕ) : ℤ) ∣ T.2.2 then ((p ^ 2 : ℕ) : ℂ) else 0))
      (∑ s : Fin p × Fin (p ^ 2), heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (t1RepΔ (.inr (.inr (.inr (.inl s))))) G Z) := by
    simpa only [sum_fin_cexp_mul_div_four hp₀ (pow_ne_zero 2 hp₀)] using
      hasSum_sum_heckeMonoidSlash Z κ (y := fun s : Fin p × Fin (p ^ 2) ↦
        (0, ((s.1 : ℕ) / p : ℚ), ((s.2 : ℕ) / (p ^ 2 : ℕ) : ℚ)))
        (fun s ↦ coe_t1RepΔ_four s.1 s.2) hp (pow_ne_zero 2 hp) hG
  refine hasSum_of_ne_zero_bij' h (fun N ↦ (N.1, p * N.2.1, p ^ 2 * N.2.2)) (fun _ ↦ True)
    ?_ ?_ ?_ ?_
  · rintro ⟨N, R, M⟩ - ⟨N', R', M'⟩ - h
    simp only [Prod.mk.injEq] at h
    rw [h.1, mul_left_cancel₀ hp' h.2.1, mul_left_cancel₀ (pow_ne_zero 2 hp') h.2.2]
  · intro N hN
    exact absurd trivial hN
  · rintro ⟨N, R, M⟩ -
    have h₂ : ((p ^ 2 : ℕ) : ℤ) ∣ p ^ 2 * M := ⟨M, by push_cast; ring1⟩
    rw [ite_eq_left (dvd_mul_right (p : ℤ) R), ite_eq_left h₂]
    rw [borelExp_eq_liftExp Z (N := N) (R := R) (M := M) (by push_cast; field_simp)
      (by push_cast; field_simp; ring1) (by push_cast; field_simp; ring1)]
    have h3 : (p : ℂ) * p ^ 2 = (p : ℂ) ^ (3 : ℤ) := by
      rw [zpow_ofNat]
      ring1
    have e : ((p : ℂ) ^ 2) ^ (2 * κ - 3) * ((p : ℂ) * p ^ 2) ^ (-κ) * (p * p ^ 2) =
        (p : ℂ) ^ (κ - 3) := by
      rw [h3, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hpC, ← zpow_add₀ hpC]
      exact congrArg _ (by push_cast; ring1)
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Nat.cast_pow]
    linear_combination (a (N, p * R, p ^ 2 * M) * liftExp 1 N R M Z) * e
  · intro T hT
    have hdvd : (p : ℤ) ∣ T.2.1 ∧ (p : ℤ) ^ 2 ∣ T.2.2 := by
      by_contra hdvd
      refine hT ?_
      rcases not_and_or.mp hdvd with hd | hd
      · rw [ite_eq_right hd, zero_mul, mul_zero]
      · have hd' : ¬((p ^ 2 : ℕ) : ℤ) ∣ T.2.2 := by exact_mod_cast hd
        rw [ite_eq_right hd', mul_zero, mul_zero]
    rcases hdvd with ⟨⟨r, hr⟩, ⟨m, hm⟩⟩
    exact ⟨(T.1, r, m), trivial, by rw [← hr, ← hm]⟩

lemma coe_t1RepΔ_five (x s : Fin p) (w : Fin (p ^ 2)) :
    ((t1RepΔ (.inr (.inr (.inr (.inr (x, s, w))))) : GL₄) : M₄) =
      borelNF ((p : ℚ) ^ 2) ((p : ℚ) ^ 2) p (p * (x : ℕ)) ((w : ℕ) / (p ^ 2 : ℕ)) ((s : ℕ) / p)
        0 := by
  rw [coe_t1RepΔ_eq_borelNF]
  simp [t1Exp, t1Data]

lemma hasSum_sum_heckeMonoidSlash_t1RepΔ_five (x : Fin p)
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (κ - 3) *
      a (p ^ 2 * N.1, p * (N.2.1 + 2 * x * N.1), N.2.2 + N.2.1 * x + N.1 * x ^ 2) *
        liftExp 1 N.1 N.2.1 N.2.2 Z)
      (∑ s : Fin p × Fin (p ^ 2), heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (t1RepΔ (.inr (.inr (.inr (.inr (x, s)))))) G Z) := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ (((p : ℚ) ^ 2 : ℚ) : ℂ) ^ (2 * κ - 3) *
      ((p ^ 2 * p : ℚ) : ℂ) ^ (-κ) * a T *
        borelExp ((p : ℚ) ^ 2) ((p : ℚ) ^ 2) p (p * (x : ℕ)) T Z *
          ((if (p : ℤ) ∣ T.2.1 then (p : ℂ) else 0) *
            if ((p ^ 2 : ℕ) : ℤ) ∣ T.1 then ((p ^ 2 : ℕ) : ℂ) else 0))
      (∑ s : Fin p × Fin (p ^ 2), heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (t1RepΔ (.inr (.inr (.inr (.inr (x, s)))))) G Z) := by
    simpa only [sum_fin_cexp_mul_div_five hp₀ (pow_ne_zero 2 hp₀)] using
      hasSum_sum_heckeMonoidSlash Z κ (y := fun s : Fin p × Fin (p ^ 2) ↦
        (((s.2 : ℕ) / (p ^ 2 : ℕ) : ℚ), ((s.1 : ℕ) / p : ℚ), 0))
        (fun s ↦ coe_t1RepΔ_five x s.1 s.2) (pow_ne_zero 2 hp) hp hG
  refine hasSum_of_ne_zero_bij' h
    (fun N ↦ (p ^ 2 * N.1, p * (N.2.1 + 2 * x * N.1), N.2.2 + N.2.1 * x + N.1 * x ^ 2))
    (fun _ ↦ True) ?_ ?_ ?_ ?_
  · rintro ⟨N, R, M⟩ - ⟨N', R', M'⟩ - h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨h₁, h₂, h₃⟩
    have hN : N = N' := mul_left_cancel₀ (pow_ne_zero 2 hp') h₁
    subst hN
    have hR : R = R' := by
      have h₂' : R + 2 * (x : ℤ) * N = R' + 2 * (x : ℤ) * N := mul_left_cancel₀ hp' h₂
      linarith
    subst hR
    have hM : M = M' := by linarith
    rw [hM]
  · intro N hN
    exact absurd trivial hN
  · rintro ⟨N, R, M⟩ -
    have h₂ : ((p ^ 2 : ℕ) : ℤ) ∣ p ^ 2 * N := ⟨N, by push_cast; ring1⟩
    rw [ite_eq_left (dvd_mul_right (p : ℤ) (R + 2 * x * N)), ite_eq_left h₂]
    rw [borelExp_eq_liftExp Z (N := N) (R := R) (M := M) (by push_cast; field_simp)
      (by push_cast; field_simp; ring1) (by push_cast; field_simp; ring1)]
    have h3 : (p : ℂ) ^ 2 * p = (p : ℂ) ^ (3 : ℤ) := by
      rw [zpow_ofNat]
      ring1
    have e : ((p : ℂ) ^ 2) ^ (2 * κ - 3) * ((p : ℂ) ^ 2 * p) ^ (-κ) * (p * p ^ 2) =
        (p : ℂ) ^ (κ - 3) := by
      rw [mul_comm (p : ℂ) (p ^ 2), h3, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hpC,
        ← zpow_add₀ hpC]
      exact congrArg _ (by push_cast; ring1)
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Nat.cast_pow]
    linear_combination
      (a (p ^ 2 * N, p * (R + 2 * x * N), M + R * x + N * x ^ 2) * liftExp 1 N R M Z) * e
  · intro T hT
    have hdvd : (p : ℤ) ∣ T.2.1 ∧ (p : ℤ) ^ 2 ∣ T.1 := by
      by_contra hdvd
      refine hT ?_
      rcases not_and_or.mp hdvd with hd | hd
      · rw [ite_eq_right hd, zero_mul, mul_zero]
      · have hd' : ¬((p ^ 2 : ℕ) : ℤ) ∣ T.1 := by exact_mod_cast hd
        rw [ite_eq_right hd', mul_zero, mul_zero]
    rcases hdvd with ⟨⟨r, hr⟩, ⟨n, hn⟩⟩
    refine ⟨(n, r - 2 * x * n, T.2.2 - (r - 2 * x * n) * x - n * x ^ 2), trivial, ?_⟩
    have e : T.2.2 - (r - 2 * x * n) * x - n * x ^ 2 + (r - 2 * x * n) * x + n * x ^ 2 = T.2.2 := by
      ring1
    simp only [e, sub_add_cancel, ← hr, ← hn]

/-- **The Fourier coefficients of `G ∣ T_1(p²)`**: if `G(W) = ∑ a(T) e^{2πi tr(TW)}` on `ℋ₂`, the
series converging absolutely, then `G ∣ T_1(p²)` in weight `det^κ` is the Fourier series with the
coefficients `SiegelUpperHalfSpace.heckeT₁Coeff`. -/
lemma hasSum_heckeOperator_T₁
    {F : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 κ) (heckeMonoidAt (Fin 2) p) Γ₂}
    (hF : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W)
      ((F : SiegelUpperHalfSpace (Fin 2) → ℂ) W)) :
    HasSum (fun T ↦ heckeT₁Coeff p κ a T * liftExp 1 T.1 T.2.1 T.2.2 Z)
      ((heckeOperator (TauCeti.detPowerRep ℂ 2 κ) (heckeCosetDiag p 0 1 0) F :
        SiegelUpperHalfSpace (Fin 2) → ℂ) Z) := by
  have h₂ : HasSum (fun N : ℤ × ℤ × ℤ ↦ ∑ c : Fin p, (p : ℂ) ^ (3 * κ - 6) *
      (if (p : ℤ) ∣ N.2.1 + 2 * c * N.1 ∧ (p : ℤ) ^ 2 ∣ N.2.2 + N.2.1 * c + N.1 * c ^ 2 then
        a (N.1, (N.2.1 + 2 * c * N.1) / p, (N.2.2 + N.2.1 * c + N.1 * c ^ 2) / p ^ 2) else 0) *
          liftExp 1 N.1 N.2.1 N.2.2 Z)
      (∑ c : Fin p, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (t1RepΔ (.inr (.inl c)))
        (F : SiegelUpperHalfSpace (Fin 2) → ℂ) Z) :=
    hasSum_sum fun c _ ↦ hasSum_heckeMonoidSlash_t1RepΔ_inr_inl Z c hF
  have h₅ : HasSum (fun N : ℤ × ℤ × ℤ ↦ ∑ x : Fin p, (p : ℂ) ^ (κ - 3) *
      a (p ^ 2 * N.1, p * (N.2.1 + 2 * x * N.1), N.2.2 + N.2.1 * x + N.1 * x ^ 2) *
        liftExp 1 N.1 N.2.1 N.2.2 Z)
      (∑ s : Fin p × Fin p × Fin (p ^ 2), heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (t1RepΔ (.inr (.inr (.inr (.inr s))))) (F : SiegelUpperHalfSpace (Fin 2) → ℂ) Z) := by
    rw [Fintype.sum_prod_type]
    exact hasSum_sum fun x _ ↦ hasSum_sum_heckeMonoidSlash_t1RepΔ_five Z x hF
  rw [heckeOperator_T₁_eq_sum, Finset.sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique]
  refine ((hasSum_heckeMonoidSlash_t1RepΔ_inl Z hF).add (h₂.add
    ((hasSum_sum_heckeMonoidSlash_t1RepΔ_rankOne Z hF).add
      ((hasSum_sum_heckeMonoidSlash_t1RepΔ_four Z hF).add h₅)))).congr_fun fun T ↦ ?_
  simp only [heckeT₁Coeff, add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
  ring1

end SiegelUpperHalfSpace
