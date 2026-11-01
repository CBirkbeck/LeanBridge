import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftFourierJacobi
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The Fourier–Jacobi coefficient of index `0` of the Maass lift

The Fourier–Jacobi coefficient `φ₀(τ, z) = ∑_n a(n, 0, 0) qⁿ` of index `0` of the Maass lift
(LMFDB `mf.siegel.lift.maass`) of a Jacobi form `φ ∈ J_{k,1}` of even weight `k ≥ 4` is
`-(B_k / 2k) c(0, 0) E_k(τ)`, where `E_k = 1 - (2k / B_k) ∑_{n ≥ 1} σ_{k-1}(n) qⁿ` is the normalised
Eisenstein series of level `1` (Mathlib's `ModularForm.E`): the coefficients of the lift are
`a(0, 0, 0) = -(B_k / 2k) c(0, 0)`, `a(n, 0, 0) = σ_{k-1}(n) c(0, 0)` for `n ≥ 1`, and
`a(n, r, 0) = 0` otherwise, the matrix `(n, r/2; r/2, 0)` being positive semidefinite only for
`r = 0` and `n ≥ 0`. So `φ₀` transforms under `(0, -1; 1, 0)` like a modular form of weight `k`,
which removes the index `0` from the hypotheses of the reduction of the theorem of Maass to the
index raising operators.

## Main results

* `SiegelUpperHalfSpace.maassFourierJacobi_zero`: `φ₀ = -(B_k / 2k) c(0, 0) E_k`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_summable_of_three_le`: for
  `φ ∈ J_{k,1}` with `k ≥ 3`, the Maass lift is a Siegel modular form of weight `k` on `Sp(4, ℤ)`
  if its series converges absolutely, it is holomorphic and every `φ_m`, `m ≥ 1`, transforms
  under `(0, -1; 1, 0)` like a Jacobi form of index `m`.
-/

open Complex ModularForm ModularGroup Real SymplecticGroup

open scoped ArithmeticFunction.sigma UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℕ} {φ : ℍ × ℂ → ℂ} (x : ℍ × ℂ)

private lemma maassCoeff_natCast_zero_zero (hk : 1 ≤ k) {n : ℕ} (hn : n ≠ 0) :
    maassCoeff k (jacobiCoeff φ) n 0 0 = jacobiCoeff φ (0, 0) * σ (k - 1) n := by
  rw [maassCoeff, ite_eq_right (by omega), ite_eq_left (by omega), liftDivisorSum]
  simp only [Int.gcd_zero_right, mul_zero, EuclideanDomain.zero_div, ArithmeticFunction.sigma_apply,
    Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [mul_comm, Nat.cast_pow, ← zpow_natCast, Nat.cast_sub hk, Nat.cast_one]

private lemma bernoulli_ne_zero (hk : Even k) (hk0 : k ≠ 0) : (bernoulli k : ℂ) ≠ 0 := fun hB ↦ by
  rcases hk with ⟨j, rfl⟩
  rw [← two_mul] at hB
  refine riemannZeta_ne_zero_of_one_lt_re (s := 2 * j) ?_ ?_
  · simp only [mul_re, natCast_im, mul_zero, sub_zero]
    norm_cast
    omega
  · rw [riemannZeta_two_mul_nat (by omega), hB, mul_zero, zero_div]

/-- **The Fourier–Jacobi coefficient of index `0` of the Maass lift is an Eisenstein series**: for
`φ ∈ J_{k,1}` with `k ≥ 3` even, `φ₀(τ, z) = -(B_k / 2k) c(0, 0) E_k(τ)`, where
`E_k = 1 - (2k / B_k) ∑_{n ≥ 1} σ_{k-1}(n) qⁿ` is the normalised Eisenstein series of weight `k`. -/
lemma maassFourierJacobi_zero (hφ : φ ∈ jacobiFormSpace k 1) (hk : 3 ≤ k) (hk2 : Even k) :
    maassFourierJacobi k φ 0 x = -(bernoulli k / (2 * k)) * jacobiCoeff φ (0, 0) * E hk x.1 := by
  have hinj : Function.Injective fun n : ℕ ↦ ((n : ℤ), (0 : ℤ)) := fun a b h ↦ by
    simpa using h
  have hsupp : Function.support (fun q : ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) q.1 q.2 0 * jacobiFourierExp q x) ⊆
        Set.range fun n : ℕ ↦ ((n : ℤ), (0 : ℤ)) := by
    rintro ⟨n, r⟩ hq
    by_contra hne
    refine hq ?_
    beta_reduce
    rw [maassCoeff_eq_zero_of_not_posSemidef _ _ _ hφ fun h ↦ hne ⟨n.toNat, ?_⟩, zero_mul]
    have hr : r = 0 := by
      nlinarith [sq_nonneg r]
    simp [hr, h.1]
  have hq (n : ℕ) : jacobiFourierExp ((n : ℤ), 0) x = cexp (2 * π * I * x.1) ^ n := by
    rw [jacobiFourierExp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring1
  have hterm (n : ℕ) : maassCoeff k (jacobiCoeff φ) ((n + 1 : ℕ) : ℤ) 0 0 *
      jacobiFourierExp (((n + 1 : ℕ) : ℤ), 0) x =
        jacobiCoeff φ (0, 0) * ((σ (k - 1) (n + 1) : ℂ) * cexp (2 * π * I * x.1) ^ (n + 1)) := by
    rw [maassCoeff_natCast_zero_zero (by omega) n.succ_ne_zero, hq, mul_assoc]
  have hs : Summable fun n : ℕ ↦ jacobiCoeff φ (0, 0) *
      ((σ (k - 1) (n + 1) : ℂ) * cexp (2 * π * I * x.1) ^ (n + 1)) :=
    ((summable_nat_add_iff 1).mpr
      (EisensteinSeries.summable_sigma_mul_cexp_pow (by omega) x.1)).mul_left _
  have hE : E hk x.1 = 1 - (2 * k / bernoulli k) *
      ∑' n : ℕ+, (σ (k - 1) n : ℂ) * cexp (2 * π * I * x.1) ^ (n : ℕ) := by
    simpa only [zpow_natCast] using EisensteinSeries.q_expansion_bernoulli hk hk2 x.1
  rw [maassFourierJacobi, ← hinj.tsum_eq hsupp, tsum_eq_zero_add' (hs.congr fun n ↦ (hterm n).symm)]
  dsimp only
  rw [tsum_congr hterm, tsum_mul_left, ← tsum_pnat_eq_tsum_succ
    (f := fun n ↦ (σ (k - 1) n : ℂ) * cexp (2 * π * I * x.1) ^ n), hE, hq 0, pow_zero, mul_one,
    Nat.cast_zero, maassCoeff, ite_eq_left ⟨rfl, rfl, rfl⟩, Int.toNat_natCast, Int.cast_natCast]
  have hB : (bernoulli k : ℂ) ≠ 0 := bernoulli_ne_zero hk2 (by omega)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring1

private lemma E_S_smul (hk : 3 ≤ k) (τ : ℍ) : E hk (S • τ) = (τ : ℂ) ^ k * E hk τ := by
  convert SlashInvariantForm.slash_action_eqn'' (E hk) (MonoidHom.mem_range.mpr ⟨S, rfl⟩) τ using 3
  · rfl
  · rw [zpow_natCast]
    exact congrArg (· ^ k) (ModularGroup.denom_S τ).symm

private lemma maassFourierJacobi_zero_S_smul (hφ : φ ∈ jacobiFormSpace k 1) (hk : 3 ≤ k)
    (hk2 : Even k) : maassFourierJacobi k φ 0 (S • x.1, x.2 / UpperHalfPlane.denom S x.1) =
      jacobiFactor k 0 x S * maassFourierJacobi k φ 0 x := by
  rw [maassFourierJacobi_zero _ hφ hk hk2, maassFourierJacobi_zero _ hφ hk hk2]
  dsimp only
  rw [E_S_smul hk, jacobiFactor, ModularGroup.denom_S]
  simp
  ring1

/-- **The theorem of Maass, reduced to the index raising operators and convergence** (LMFDB
`mf.siegel.lift.maass`), in weight `k ≥ 3`: for `φ ∈ J_{k,1}`, if the series of the Maass lift
converges absolutely on `ℋ₂`, the lift is holomorphic, and the Fourier–Jacobi coefficient `φ_m` of
the lift transforms under `(0, -1; 1, 0)` like a Jacobi form of weight `k` and index `m` for every
`m ≥ 1` (as `φ ∣ V_m` does, by the theorem of Eichler and Zagier, Theorem 4.2, that the index
raising operator `V_m` maps `J_{k,1}` to `J_{k,m}`), then the Maass lift is a Siegel modular form of
weight `k` on `Sp(4, ℤ)`. The coefficient `φ₀` is `c(0, 0)` times an Eisenstein series, and there
are no Jacobi forms of odd weight and index `1`. -/
lemma maassLift_mem_scalarModularForms_of_summable_of_three_le (hφ : φ ∈ jacobiFormSpace k 1)
    (hk : 3 ≤ k) (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hF : IsHolomorphic (maassLift k φ)) (hS : ∀ m : ℕ, 0 < m → ∀ x : ℍ × ℂ,
      maassFourierJacobi k φ m (S • x.1, x.2 / UpperHalfPlane.denom S x.1) =
        jacobiFactor k m x S * maassFourierJacobi k φ m x) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) := by
  rcases Nat.even_or_odd k with hk2 | hk2
  · refine maassLift_mem_scalarModularForms hφ hF fun Z ↦
      maassLift_partialInversion_smul Z hs fun m x ↦ ?_
    rcases m with _ | m
    · exact maassFourierJacobi_zero_S_smul x hφ hk hk2
    · exact hS (m + 1) m.succ_pos x
  · rw [maassLift_eq_zero_of_odd hφ (by exact_mod_cast hk2)]
    exact zero_mem _

end SiegelUpperHalfSpace
