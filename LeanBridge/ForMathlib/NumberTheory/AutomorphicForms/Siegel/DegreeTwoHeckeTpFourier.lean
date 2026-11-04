import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeFourier
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoBorelSlash

/-!
# The Fourier coefficients of `F ∣ T(p)` in degree `2`

Let `G(Z) = ∑ a(n, r, m) e^{2πi(nτ + rz + mω)}` on `ℋ₂`, the series converging absolutely. The
Hecke operator `T(p) = Γ diag(1, 1, p, p) Γ` of `Γ = Sp(4, ℤ)` is the sum of the slash operators of
the `1 + p + p² + p³` Borel normal forms `SiegelUpperHalfSpace.tpRep`, in four families with the
same `D`. Summing the phases `e^{2πi tr(TX)}` over each family and reindexing, `G ∣ T(p)` in weight
`det^κ` is the Fourier series with the coefficients (`SiegelUpperHalfSpace.heckeTpCoeff`)
`p^{2κ-3} a(N/p) + p^{κ-2} (a(N/p, R, pM) + ∑_{c mod p} a(pN, R + 2cN, (M + Rc + Nc²)/p)) +
a(pN, pR, pM)` at `(N, R, M)`, a term being `0` where its argument is not integral. In the language
of binary quadratic forms `Q = [N, R, M]`, the middle terms are `a(Q ∘ g/p)` over the `p + 1`
sublattices `g ℤ²` of index `p`. This is Andrianov's formula for `T(p)` in degree `2`.

## Main definitions

* `SiegelUpperHalfSpace.heckeTpCoeff`: the Fourier coefficients of `G ∣ T(p)`.

## Main results

* `SiegelUpperHalfSpace.hasSum_heckeOperator_Tp`: `G ∣ T(p)` is the Fourier series with the
  coefficients `SiegelUpperHalfSpace.heckeTpCoeff`.
-/

open Complex Real

namespace SiegelUpperHalfSpace

local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ

local notation "GL₄" => GL (Fin 2 ⊕ Fin 2) ℚ

local notation "Γ₂" => heckeGamma (Fin 2)

variable (p : ℕ) (κ : ℤ) (a : ℤ × ℤ × ℤ → ℂ)

/-- The **Fourier coefficient of `G ∣ T(p)`** at `T = (N, R, M)`, in weight `det^κ`, for a Fourier
series `G` with coefficients `a`:
`p^{2κ-3} a(N/p, R/p, M/p) + p^{κ-2} (a(N/p, R, pM) + ∑_{c mod p} a(pN, R + 2cN, (M + Rc + Nc²)/p))
+ a(pN, pR, pM)`, each term being `0` where its argument is not integral. -/
noncomputable def heckeTpCoeff (T : ℤ × ℤ × ℤ) : ℂ :=
  (p : ℂ) ^ (2 * κ - 3) * (if (p : ℤ) ∣ T.1 ∧ (p : ℤ) ∣ T.2.1 ∧ (p : ℤ) ∣ T.2.2 then
    a (T.1 / p, T.2.1 / p, T.2.2 / p) else 0) +
  (p : ℂ) ^ (κ - 2) * ((if (p : ℤ) ∣ T.1 then a (T.1 / p, T.2.1, p * T.2.2) else 0) +
    ∑ c : Fin p, if (p : ℤ) ∣ T.2.2 + T.2.1 * c + T.1 * c ^ 2 then
      a (p * T.1, T.2.1 + 2 * c * T.1, (T.2.2 + T.2.1 * c + T.1 * c ^ 2) / p) else 0) +
  a (p * T.1, p * T.2.1, p * T.2.2)

variable {p κ a} {G : SiegelUpperHalfSpace (Fin 2) → ℂ} (Z : SiegelUpperHalfSpace (Fin 2))

lemma hasSum_of_ne_zero_bij' {f g : ℤ × ℤ × ℤ → ℂ} {s : ℂ} (hf : HasSum f s)
    (j : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ) (P : ℤ × ℤ × ℤ → Prop) (hj : Set.InjOn j {N | P N})
    (hg : ∀ N, ¬P N → g N = 0) (hfg : ∀ N, P N → f (j N) = g N)
    (hsupp : ∀ T, f T ≠ 0 → ∃ N, P N ∧ j N = T) : HasSum g s :=
  hasSum_of_ne_zero_bij hf j (hj.mono fun N hN ↦ not_not.mp fun h ↦ hN (hg N h))
    (fun N hN ↦ hfg N (not_not.mp fun h ↦ hN (hg N h))) fun T hT ↦ by
      rcases hsupp T hT with ⟨N, hN, rfl⟩
      exact ⟨N, (hfg N hN).symm ▸ hT, rfl⟩

lemma sum_fin_cexp_mul_div {n : ℕ} (hn : n ≠ 0) (m : ℤ) :
    ∑ t : Fin n, cexp (2 * π * I * ((m * ((t : ℕ) / n : ℚ) : ℚ) : ℂ)) =
      if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun t ↦ cexp (2 * π * I * ((m * ((t : ℕ) / n : ℚ) : ℚ) : ℂ))) n,
    ← UpperHalfPlane.sum_range_exp_two_pi_I_mul_div hn m]
  refine Finset.sum_congr rfl fun t _ ↦ congrArg cexp ?_
  push_cast
  ring1

variable [Fact p.Prime]

lemma coe_tpRepΔ_eq_borelNF (i : TpIndex p) : ((tpRepΔ i : GL₄) : M₄) =
    borelNF ((p : ℚ) ^ 1) ((p : ℚ) ^ (tpExp i).1) ((p : ℚ) ^ (tpExp i).2) (tpData i).1
      (tpData i).2.1 (tpData i).2.2.1 (tpData i).2.2.2 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [coe_tpRepΔ, tpRep, coe_borelNFGL (pow_ne_zero 1 hp) (pow_ne_zero _ hp) (pow_ne_zero _ hp)]

lemma hasSum_heckeMonoidSlash_tpRepΔ_inl
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (2 * κ - 3) * (if (p : ℤ) ∣ N.1 ∧ (p : ℤ) ∣ N.2.1 ∧
      (p : ℤ) ∣ N.2.2 then a (N.1 / p, N.2.1 / p, N.2.2 / p) else 0) * liftExp 1 N.1 N.2.1 N.2.2 Z)
        (heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (tpRepΔ (.inl () : TpIndex p)) G Z) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (2 * κ - 3) * a T * borelExp p 1 1 0 T Z)
      (heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (tpRepΔ (.inl () : TpIndex p)) G Z) := by
    simpa only [tpExp, tpData, pow_zero, pow_one, mul_one, Rat.cast_one, one_zpow,
      Rat.cast_natCast, mul_zero, add_zero, Rat.cast_zero, Complex.exp_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_unit, one_smul] using hasSum_sum_heckeMonoidSlash Z κ
        (S := Unit) (x := fun _ ↦ tpRepΔ (.inl ())) (y := fun _ ↦ (0, 0, 0))
        (fun _ ↦ coe_tpRepΔ_eq_borelNF _) (pow_ne_zero _ hp) (pow_ne_zero _ hp) hG
  refine hasSum_of_ne_zero_bij' h (fun N ↦ (N.1 / p, N.2.1 / p, N.2.2 / p))
    (fun N ↦ (p : ℤ) ∣ N.1 ∧ (p : ℤ) ∣ N.2.1 ∧ (p : ℤ) ∣ N.2.2) ?_ ?_ ?_ ?_
  · rintro ⟨-, -, -⟩ ⟨⟨n, rfl⟩, ⟨r, rfl⟩, ⟨m, rfl⟩⟩ ⟨-, -, -⟩ ⟨⟨n', rfl⟩, ⟨r', rfl⟩, ⟨m', rfl⟩⟩ h
    simp only [Int.mul_ediv_cancel_left _ hp', Prod.mk.injEq] at h
    rw [h.1, h.2.1, h.2.2]
  · intro N hN
    rw [ite_eq_right hN, mul_zero, zero_mul]
  · rintro ⟨-, -, -⟩ ⟨⟨n, rfl⟩, ⟨r, rfl⟩, ⟨m, rfl⟩⟩
    rw [ite_eq_left ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩]
    simp only [Int.mul_ediv_cancel_left _ hp']
    exact congrArg _ (borelExp_eq_liftExp Z (by push_cast; ring1) (by push_cast; ring1)
      (by push_cast; ring1))
  · rintro T -
    exact ⟨(p * T.1, p * T.2.1, p * T.2.2),
      ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩, by
        simp only [Int.mul_ediv_cancel_left _ hp']⟩

lemma coe_tpRepΔ_inr_inl (t : Fin p) :
    ((tpRepΔ (.inr (.inl t)) : GL₄) : M₄) = borelNF p 1 p 0 0 0 ((t : ℕ) / p) := by
  rw [coe_tpRepΔ_eq_borelNF]
  simp [tpExp, tpData]

lemma hasSum_sum_heckeMonoidSlash_tpRepΔ_inr_inl
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (κ - 2) * (if (p : ℤ) ∣ N.1 then
      a (N.1 / p, N.2.1, p * N.2.2) else 0) * liftExp 1 N.1 N.2.1 N.2.2 Z)
        (∑ t : Fin p, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (tpRepΔ (.inr (.inl t)))
          G Z) := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ ((p : ℚ) : ℂ) ^ (2 * κ - 3) * ((1 * p : ℚ) : ℂ) ^ (-κ) *
      a T * borelExp p 1 p 0 T Z * if (p : ℤ) ∣ T.2.2 then (p : ℂ) else 0)
      (∑ t : Fin p, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (tpRepΔ (.inr (.inl t))) G Z) := by
    simpa only [mul_zero, zero_add, sum_fin_cexp_mul_div hp₀] using
      hasSum_sum_heckeMonoidSlash Z κ (y := fun t : Fin p ↦ (0, 0, ((t : ℕ) / p : ℚ)))
        coe_tpRepΔ_inr_inl one_ne_zero hp hG
  refine hasSum_of_ne_zero_bij' h (fun N ↦ (N.1 / p, N.2.1, p * N.2.2)) (fun N ↦ (p : ℤ) ∣ N.1)
    ?_ ?_ ?_ ?_
  · rintro ⟨-, R, M⟩ ⟨n, rfl⟩ ⟨-, R', M'⟩ ⟨n', rfl⟩ h
    simp only [Int.mul_ediv_cancel_left _ hp', Prod.mk.injEq] at h
    rw [h.1, h.2.1, mul_left_cancel₀ hp' h.2.2]
  · intro N hN
    rw [ite_eq_right hN, mul_zero, zero_mul]
  · rintro ⟨-, R, M⟩ ⟨n, rfl⟩
    rw [ite_eq_left (dvd_mul_right _ _), ite_eq_left (dvd_mul_right _ _)]
    simp only [Int.mul_ediv_cancel_left _ hp']
    rw [borelExp_eq_liftExp Z (N := p * n) (R := R) (M := M) (by push_cast; ring1)
      (by field_simp; ring1) (by push_cast; field_simp; ring1)]
    have e : (p : ℂ) ^ (2 * κ - 3) * (p : ℂ) ^ (-κ) * p = (p : ℂ) ^ (κ - 2) := by
      rw [← zpow_add₀ hpC, ← zpow_add_one₀ hpC]
      exact congrArg _ (by ring1)
    simp only [one_mul, Rat.cast_natCast]
    linear_combination (a (n, R, p * M) * liftExp 1 (p * n) R M Z) * e
  · intro T hT
    have hm : (p : ℤ) ∣ T.2.2 := by
      by_contra hm
      exact hT (by rw [ite_eq_right hm, mul_zero])
    rcases hm with ⟨m, hm⟩
    exact ⟨(p * T.1, T.2.1, m), dvd_mul_right _ _, by
      simp only [Int.mul_ediv_cancel_left _ hp', ← hm]⟩

lemma coe_tpRepΔ_inr_inr_inl (c t : Fin p) : ((tpRepΔ (.inr (.inr (.inl (c, t)))) : GL₄) : M₄) =
    borelNF p p 1 (c : ℕ) ((t : ℕ) / p) 0 0 := by
  rw [coe_tpRepΔ_eq_borelNF]
  simp [tpExp, tpData]

lemma hasSum_sum_heckeMonoidSlash_tpRepΔ_inr_inr_inl (c : Fin p)
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ (p : ℂ) ^ (κ - 2) *
      (if (p : ℤ) ∣ N.2.2 + N.2.1 * c + N.1 * c ^ 2 then
        a (p * N.1, N.2.1 + 2 * c * N.1, (N.2.2 + N.2.1 * c + N.1 * c ^ 2) / p) else 0) *
          liftExp 1 N.1 N.2.1 N.2.2 Z)
      (∑ t : Fin p, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (tpRepΔ (.inr (.inr (.inl (c, t))))) G Z) := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ ((p : ℚ) : ℂ) ^ (2 * κ - 3) * ((p * 1 : ℚ) : ℂ) ^ (-κ) *
      a T * borelExp p p 1 (c : ℕ) T Z * if (p : ℤ) ∣ T.1 then (p : ℂ) else 0)
      (∑ t : Fin p, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (tpRepΔ (.inr (.inr (.inl (c, t))))) G Z) := by
    simpa only [mul_zero, add_zero, sum_fin_cexp_mul_div hp₀] using
      hasSum_sum_heckeMonoidSlash Z κ (y := fun t : Fin p ↦ (((t : ℕ) / p : ℚ), 0, 0))
        (coe_tpRepΔ_inr_inr_inl c) hp one_ne_zero hG
  refine hasSum_of_ne_zero_bij' h
    (fun N ↦ (p * N.1, N.2.1 + 2 * c * N.1, (N.2.2 + N.2.1 * c + N.1 * c ^ 2) / p))
    (fun N ↦ (p : ℤ) ∣ N.2.2 + N.2.1 * c + N.1 * c ^ 2) ?_ ?_ ?_ ?_
  · rintro ⟨N, R, M⟩ ⟨m, hm⟩ ⟨N', R', M'⟩ ⟨m', hm'⟩ h
    simp only at hm hm'
    simp only [hm, hm', Int.mul_ediv_cancel_left _ hp', Prod.mk.injEq] at h
    have hN : N = N' := mul_left_cancel₀ hp' h.1
    subst hN
    have hR : R = R' := by linarith [h.2.1]
    subst hR
    rw [h.2.2] at hm
    have hM : M = M' := by linarith
    rw [hM]
  · intro N hN
    rw [ite_eq_right hN, mul_zero, zero_mul]
  · rintro ⟨N, R, M⟩ ⟨m, hm⟩
    simp only at hm ⊢
    have hmQ : (M : ℚ) + R * (c : ℕ) + N * ((c : ℕ) : ℚ) ^ 2 = p * m := by exact_mod_cast hm
    rw [ite_eq_left (dvd_mul_right (p : ℤ) N), ite_eq_left (Dvd.intro m hm.symm)]
    simp only [hm, Int.mul_ediv_cancel_left _ hp']
    rw [borelExp_eq_liftExp Z (N := N) (R := R) (M := M) (by push_cast; field_simp)
      (by push_cast; field_simp; ring1) (by push_cast; field_simp; linear_combination -hmQ)]
    have e : (p : ℂ) ^ (2 * κ - 3) * (p : ℂ) ^ (-κ) * p = (p : ℂ) ^ (κ - 2) := by
      rw [← zpow_add₀ hpC, ← zpow_add_one₀ hpC]
      exact congrArg _ (by ring1)
    simp only [mul_one, Rat.cast_natCast]
    linear_combination (a (p * N, R + 2 * c * N, m) * liftExp 1 N R M Z) * e
  · intro T hT
    have hn : (p : ℤ) ∣ T.1 := by
      by_contra hn
      exact hT (by rw [ite_eq_right hn, mul_zero])
    rcases hn with ⟨n, hn⟩
    refine ⟨(n, T.2.1 - 2 * c * n, n * c ^ 2 - T.2.1 * c + p * T.2.2), ⟨T.2.2, by ring1⟩, ?_⟩
    have e : n * c ^ 2 - T.2.1 * c + p * T.2.2 + (T.2.1 - 2 * c * n) * c + n * c ^ 2 =
        (p : ℤ) * T.2.2 := by
      ring1
    simp only [e, Int.mul_ediv_cancel_left _ hp', ← hn, sub_add_cancel]

lemma coe_tpRepΔ_inr_inr_inr (t₀ t₁ t₂ : Fin p) :
    ((tpRepΔ (.inr (.inr (.inr (t₀, t₁, t₂)))) : GL₄) : M₄) =
      borelNF p p p 0 ((t₀ : ℕ) / p) ((t₁ : ℕ) / p) ((t₂ : ℕ) / p) := by
  rw [coe_tpRepΔ_eq_borelNF]
  simp [tpExp, tpData]

lemma sum_fin_cexp_mul_div_three {n : ℕ} (hn : n ≠ 0) (T : ℤ × ℤ × ℤ) :
    ∑ s : Fin n × Fin n × Fin n, cexp (2 * π * I * ((T.1 * ((s.1 : ℕ) / n : ℚ) +
      T.2.1 * ((s.2.1 : ℕ) / n : ℚ) + T.2.2 * ((s.2.2 : ℕ) / n : ℚ) : ℚ) : ℂ)) =
        (if (n : ℤ) ∣ T.1 then (n : ℂ) else 0) * (if (n : ℤ) ∣ T.2.1 then (n : ℂ) else 0) *
          (if (n : ℤ) ∣ T.2.2 then (n : ℂ) else 0) := by
  rw [← sum_fin_cexp_mul_div hn T.1, ← sum_fin_cexp_mul_div hn T.2.1,
    ← sum_fin_cexp_mul_div hn T.2.2, Fintype.sum_mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t₀ _ ↦ ?_
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t₁ _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t₂ _ ↦ ?_
  rw [Rat.cast_add, Rat.cast_add, mul_add, mul_add, Complex.exp_add, Complex.exp_add]

lemma hasSum_sum_heckeMonoidSlash_tpRepΔ_inr_inr_inr
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun N : ℤ × ℤ × ℤ ↦ a (p * N.1, p * N.2.1, p * N.2.2) * liftExp 1 N.1 N.2.1 N.2.2 Z)
      (∑ s : Fin p × Fin p × Fin p, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (tpRepΔ (.inr (.inr (.inr s)))) G Z) := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ ((p : ℚ) : ℂ) ^ (2 * κ - 3) * ((p * p : ℚ) : ℂ) ^ (-κ) *
      a T * borelExp p p p 0 T Z * ((if (p : ℤ) ∣ T.1 then (p : ℂ) else 0) *
        (if (p : ℤ) ∣ T.2.1 then (p : ℂ) else 0) * (if (p : ℤ) ∣ T.2.2 then (p : ℂ) else 0)))
      (∑ s : Fin p × Fin p × Fin p, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (tpRepΔ (.inr (.inr (.inr s)))) G Z) := by
    simpa only [sum_fin_cexp_mul_div_three hp₀] using hasSum_sum_heckeMonoidSlash Z κ
      (y := fun s : Fin p × Fin p × Fin p ↦ (((s.1 : ℕ) / p : ℚ), ((s.2.1 : ℕ) / p : ℚ),
        ((s.2.2 : ℕ) / p : ℚ))) (fun s ↦ coe_tpRepΔ_inr_inr_inr s.1 s.2.1 s.2.2) hp hp hG
  refine hasSum_of_ne_zero_bij' h (fun N ↦ (p * N.1, p * N.2.1, p * N.2.2)) (fun _ ↦ True)
    ?_ ?_ ?_ ?_
  · rintro ⟨N, R, M⟩ - ⟨N', R', M'⟩ - h
    simp only [Prod.mk.injEq] at h
    rw [mul_left_cancel₀ hp' h.1, mul_left_cancel₀ hp' h.2.1, mul_left_cancel₀ hp' h.2.2]
  · intro N hN
    exact absurd trivial hN
  · rintro ⟨N, R, M⟩ -
    rw [ite_eq_left (dvd_mul_right _ _), ite_eq_left (dvd_mul_right _ _),
      ite_eq_left (dvd_mul_right _ _)]
    rw [borelExp_eq_liftExp Z (N := N) (R := R) (M := M) (by push_cast; field_simp)
      (by push_cast; field_simp; ring1) (by push_cast; field_simp; ring1)]
    have h3 : (p : ℂ) * p * p = (p : ℂ) ^ (3 : ℤ) := by
      rw [zpow_ofNat]
      ring1
    have e : (p : ℂ) ^ (2 * κ - 3) * ((p : ℂ) * p) ^ (-κ) * (p * p * p) = 1 := by
      rw [mul_zpow, ← zpow_add₀ hpC, ← zpow_add₀ hpC, h3, ← zpow_add₀ hpC, ← zpow_zero (p : ℂ)]
      exact congrArg _ (by ring1)
    simp only [Rat.cast_mul, Rat.cast_natCast]
    linear_combination (a (p * N, p * R, p * M) * liftExp 1 N R M Z) * e
  · intro T hT
    have hdvd : (p : ℤ) ∣ T.1 ∧ (p : ℤ) ∣ T.2.1 ∧ (p : ℤ) ∣ T.2.2 := by
      by_contra hdvd
      refine hT ?_
      simp only [not_and_or] at hdvd
      rcases hdvd with hd | hd | hd <;> simp [hd]
    rcases hdvd with ⟨⟨n, hn⟩, ⟨r, hr⟩, ⟨m, hm⟩⟩
    exact ⟨(n, r, m), trivial, by rw [← hn, ← hr, ← hm]⟩

/-- **The Fourier coefficients of `G ∣ T(p)`**: if `G(W) = ∑ a(T) e^{2πi tr(TW)}` on `ℋ₂`, the
series converging absolutely, then `G ∣ T(p)` in weight `det^κ` is the Fourier series with the
coefficients `SiegelUpperHalfSpace.heckeTpCoeff`. -/
lemma hasSum_heckeOperator_Tp
    {F : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 κ) (heckeMonoidAt (Fin 2) p) Γ₂}
    (hF : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W)
      ((F : SiegelUpperHalfSpace (Fin 2) → ℂ) W)) :
    HasSum (fun T ↦ heckeTpCoeff p κ a T * liftExp 1 T.1 T.2.1 T.2.2 Z)
      ((heckeOperator (TauCeti.detPowerRep ℂ 2 κ) (heckeCosetDiag p 0 0 1) F :
        SiegelUpperHalfSpace (Fin 2) → ℂ) Z) := by
  have h₃ : HasSum (fun N : ℤ × ℤ × ℤ ↦ ∑ c : Fin p, (p : ℂ) ^ (κ - 2) *
      (if (p : ℤ) ∣ N.2.2 + N.2.1 * c + N.1 * c ^ 2 then
        a (p * N.1, N.2.1 + 2 * c * N.1, (N.2.2 + N.2.1 * c + N.1 * c ^ 2) / p) else 0) *
          liftExp 1 N.1 N.2.1 N.2.2 Z)
      (∑ s : Fin p × Fin p, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ)
        (tpRepΔ (.inr (.inr (.inl s)))) (F : SiegelUpperHalfSpace (Fin 2) → ℂ) Z) := by
    rw [Fintype.sum_prod_type]
    exact hasSum_sum fun c _ ↦ hasSum_sum_heckeMonoidSlash_tpRepΔ_inr_inr_inl Z c hF
  rw [heckeOperator_Tp_eq_sum, Finset.sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fintype.sum_unique]
  refine ((hasSum_heckeMonoidSlash_tpRepΔ_inl Z hF).add
    ((hasSum_sum_heckeMonoidSlash_tpRepΔ_inr_inl Z hF).add
      (h₃.add (hasSum_sum_heckeMonoidSlash_tpRepΔ_inr_inr_inr Z hF)))).congr_fun fun T ↦ ?_
  simp only [heckeTpCoeff, add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
  ring1

end SiegelUpperHalfSpace
