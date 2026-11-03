import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftIndexRaising

/-!
# Holomorphy of the Maass lift

The Maass lift `F(Z) = ∑ a(n, r, m) e^{2πi(nτ + rz + mω)}` of a Jacobi form `φ ∈ J_{k,1}`
(`SiegelUpperHalfSpace.maassLift`, LMFDB `mf.siegel.lift.maass`) is holomorphic on `ℋ₂` as soon as
its series converges absolutely at every point: the coefficients vanish unless
`T = (n, r/2; r/2, m)` is positive semidefinite, which makes it a series as in
`SiegelUpperHalfSpace.isHolomorphic_tsum_mul_liftExp`, for `N = 1`. With the reduction of the
theorem of Maass to convergence and holomorphy, the Maass lift of `φ ∈ J_{k,1}`, `k ≥ 3`, is a
Siegel modular form of weight `k` on `Sp(4, ℤ)` as soon as its series converges absolutely on `ℋ₂`.
The series converges absolutely if the Fourier coefficients of `φ` grow polynomially,
`‖c(n, r)‖ ≤ C (1 + |n|)^A`: the divisor sums then satisfy `|a(n, r, m)| ≤ C' (1 + n + m)^{k + 2A}`
(`SiegelUpperHalfSpace.summable_mul_liftExp_of_norm_le`). That bound on `c(n, r)` (a Hecke-type
estimate for Jacobi forms) is proved in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.CoefficientGrowth`.

## Main results

* `SiegelUpperHalfSpace.isHolomorphic_maassLift`: the Maass lift is holomorphic if its series
  converges absolutely on `ℋ₂`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_forall_summable`: for `φ ∈ J_{k,1}`
  with `k ≥ 3`, the Maass lift is a Siegel modular form of weight `k` on `Sp(4, ℤ)` if its series
  converges absolutely on `ℋ₂`.
* `SiegelUpperHalfSpace.summable_maassLift_of_norm_jacobiCoeff_le`: the series of the Maass lift
  converges absolutely if the Fourier coefficients of `φ` grow polynomially.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_norm_jacobiCoeff_le`: for
  `φ ∈ J_{k,1}` with `k ≥ 3` and polynomially bounded Fourier coefficients, the Maass lift is a
  Siegel modular form of weight `k` on `Sp(4, ℤ)`.
-/

open ModularForm SymplecticGroup

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} (p : ℤ × ℤ × ℤ) (Ω : SiegelUpperHalfSpace (Fin 2)) {C : ℝ} {A : ℕ}

private lemma maassCoeff_eq_zero_of_not_isLiftSupport (hφ : φ ∈ jacobiFormSpace k 1)
    (hp : ¬IsLiftSupport 1 p) : maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 = 0 :=
  maassCoeff_eq_zero_of_not_posSemidef _ _ _ hφ <| by
    simpa [IsLiftSupport] using hp

/-- **The Maass lift is holomorphic** as soon as its series converges absolutely on `ℋ₂`, for a
Jacobi form `φ ∈ J_{k,1}`: the coefficients `a(n, r, m)` vanish unless `T = (n, r/2; r/2, m)` is
positive semidefinite, so the series of the derivatives of the terms is dominated on a ball by the
series of the lift at a point `(iε/2) 1`. -/
lemma isHolomorphic_maassLift (hφ : φ ∈ jacobiFormSpace k 1)
    (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z) :
    IsHolomorphic (maassLift k φ) :=
  isHolomorphic_tsum_mul_liftExp (fun p ↦ maassCoeff_eq_zero_of_not_isLiftSupport p hφ) hs

private lemma norm_maassCoeff_le (hk : 1 ≤ k) (hC : 0 ≤ C)
    (hc : ∀ n r : ℤ, ‖jacobiCoeff φ (n, r)‖ ≤ C * (1 + |(n : ℝ)|) ^ A)
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ 4 * p.1 * p.2.2) :
    ‖maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2‖ ≤ (‖maassCoeff k (jacobiCoeff φ) 0 0 0‖ + C) *
      (1 + (p.1 + p.2.2 : ℝ)) ^ ((k - 1).toNat + 1 + 2 * A) := by
  have hn : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have hm : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hp.2.1
  have h1 : (1 : ℝ) ≤ (1 + (p.1 + p.2.2 : ℝ)) ^ ((k - 1).toNat + 1 + 2 * A) :=
    one_le_pow₀ (by linarith)
  by_cases h0 : p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2 = 0
  · rw [h0.1, h0.2.1, h0.2.2, Int.cast_zero, add_zero, add_zero, one_pow, mul_one]
    linarith
  rw [maassCoeff, ite_eq_right h0, ite_eq_left ⟨hp.1, hp.2.1⟩]
  have hnm : 0 < p.1 + p.2.2 := by
    by_contra h
    have hr : p.2.1 ^ 2 ≤ 0 := by nlinarith [hp.2.2]
    exact h0 ⟨by omega, pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm hr (sq_nonneg _)),
      by omega⟩
  have hg : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2 : ℕ) : ℤ) ≤ p.1 + p.2.2 :=
    Int.le_of_dvd hnm <| dvd_add ((Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _))
      (Int.gcd_dvd_right _ _)
  have hg' : (((p.1.gcd p.2.1 : ℤ).gcd p.2.2 : ℕ) : ℝ) ≤ p.1 + p.2.2 := by exact_mod_cast hg
  exact (norm_liftDivisorSum_le hk hC hc hp.1 hp.2.1 hg' le_rfl).trans <|
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) (by positivity)

/-- **The theorem of Maass, reduced to the convergence of the series** (LMFDB
`mf.siegel.lift.maass`): for a Jacobi form `φ ∈ J_{k,1}` of weight `k ≥ 3`, if the series of the
Maass lift converges absolutely at every point of `ℋ₂`, then the Maass lift is a Siegel modular
form of weight `k` on `Sp(4, ℤ)`: it is then holomorphic (`isHolomorphic_maassLift`). -/
lemma maassLift_mem_scalarModularForms_of_forall_summable (hφ : φ ∈ jacobiFormSpace k 1)
    (hk : 3 ≤ k) (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) :=
  maassLift_mem_scalarModularForms_of_summable_of_isHolomorphic hφ hk hs
    (isHolomorphic_maassLift hφ hs)

/-- **The series of the Maass lift converges absolutely** on `ℋ₂` if the Fourier coefficients of
the Jacobi form `φ ∈ J_{k,1}`, `k ≥ 1`, grow polynomially: `‖c(n, r)‖ ≤ C (1 + |n|)^A` (as follows
from a bound `C (1 + 4n - r²)^A` on the support `4n ≥ r²`). Then
`|a(n, r, m)| ≤ C' (1 + n + m)^{k + 2A}` on the positive semidefinite `(n, r/2; r/2, m)`, which
carry the coefficients, while `|e^{2πi(nτ + rz + mω)}| ≤ e^{-2πε(n + m)}` with
`ε = det(Im Z) / tr(Im Z)` and `|r| ≤ n + m`. -/
lemma summable_maassLift_of_norm_jacobiCoeff_le (hφ : φ ∈ jacobiFormSpace k 1) (hk : 1 ≤ k)
    (hc : ∀ n r : ℤ, ‖jacobiCoeff φ (n, r)‖ ≤ C * (1 + |(n : ℝ)|) ^ A) :
    Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Ω := by
  have hC : 0 ≤ C := by
    simpa using (norm_nonneg _).trans (hc 0 0)
  have hb (p : ℤ × ℤ × ℤ) (hp : IsLiftSupport 1 p) :
      ‖maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2‖ ≤ (‖maassCoeff k (jacobiCoeff φ) 0 0 0‖ + C) *
        (1 + (p.1 + (1 : ℕ) * p.2.2 : ℝ)) ^ ((k - 1).toNat + 1 + 2 * A) := by
    rw [Nat.cast_one, one_mul]
    exact norm_maassCoeff_le p hk hC hc <| by
      simpa [IsLiftSupport] using hp
  exact summable_mul_liftExp_of_norm_le Ω one_pos (by positivity)
    (fun p ↦ maassCoeff_eq_zero_of_not_isLiftSupport p hφ) hb

/-- **The theorem of Maass, reduced to a polynomial bound for the Fourier coefficients of `φ`**
(LMFDB `mf.siegel.lift.maass`): for a Jacobi form `φ ∈ J_{k,1}` of weight `k ≥ 3` whose Fourier
coefficients satisfy `‖c(n, r)‖ ≤ C (1 + |n|)^A`, the Maass lift is a Siegel modular form of weight
`k` on `Sp(4, ℤ)`. Every Jacobi form satisfies such a bound
(`ModularForm.norm_jacobiCoeff_le_of_mem_jacobiFormSpace`), so this gives the
`mem_modularForms` part of `MaassLiftTheorem` for `k ≥ 3`. -/
lemma maassLift_mem_scalarModularForms_of_norm_jacobiCoeff_le (hφ : φ ∈ jacobiFormSpace k 1)
    (hk : 3 ≤ k) (hc : ∀ n r : ℤ, ‖jacobiCoeff φ (n, r)‖ ≤ C * (1 + |(n : ℝ)|) ^ A) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) :=
  maassLift_mem_scalarModularForms_of_forall_summable hφ hk fun Z ↦
    summable_maassLift_of_norm_jacobiCoeff_le Z hφ (by omega) hc

end SiegelUpperHalfSpace
