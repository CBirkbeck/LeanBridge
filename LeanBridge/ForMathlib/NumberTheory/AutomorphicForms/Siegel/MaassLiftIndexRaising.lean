import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftEisenstein

/-!
# The theorem of Maass from the index raising operators

The Fourier–Jacobi coefficient `φ_m(τ, z) = ∑_{n, r} a(n, r, m) e^{2πi(nτ + rz)}` of index
`m ≥ 1` of the Maass lift of `φ ∈ J_{k,1}` (`SiegelUpperHalfSpace.maassFourierJacobi`, LMFDB
`mf.siegel.lift.maass`) is the image `φ ∣ V_m` of `φ` under the index raising operator of Eichler
and Zagier (`ModularForm.indexRaising`), `(φ ∣ V_m)(τ, z) = m⁻¹ ∑ a^k φ((aτ + b)/d, az)` over
`ad = m`, `0 ≤ b < d`: the Fourier coefficients of `φ ∣ V_m` are the divisor sums
`∑_{a ∣ (N, R, m)} a^{k-1} c(Nm/a², R/a)`
(`SiegelUpperHalfSpace.hasSum_liftDivisorSum_indexRaising`), which are the coefficients of the lift.
As `φ ∣ V_m` transforms like a Jacobi form of index `m` under `(0, -1; 1, 0)`
(`ModularForm.indexRaising_S`), the theorem of Maass reduces to the absolute convergence of the
series of the lift and its holomorphy, in weight `k ≥ 3`.

## Main results

* `SiegelUpperHalfSpace.maassCoeff_eq_liftDivisorSum`: for `m ≥ 1`, the coefficient `a(n, r, m)`
  is the divisor sum `∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` for all `n`.
* `SiegelUpperHalfSpace.maassFourierJacobi_eq_indexRaising`: `φ_m = φ ∣ V_m` for `m ≥ 1`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_summable_of_isHolomorphic`: for
  `φ ∈ J_{k,1}` with `k ≥ 3`, the Maass lift is a Siegel modular form of weight `k` on `Sp(4, ℤ)`
  if its series converges absolutely and it is holomorphic.
-/

open ModularForm SymplecticGroup

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} {m : ℕ}

/-- **The Fourier coefficients of the Fourier–Jacobi coefficients of index `m ≥ 1` of the Maass
lift**: for `φ ∈ J_{k,1}` and `m ≥ 1`, `a(n, r, m) = ∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` for
all `n, r`, also for `n < 0`, where both sides vanish. -/
lemma maassCoeff_eq_liftDivisorSum (hφ : φ ∈ jacobiFormSpace k 1) (hm : 0 < m) (n r : ℤ) :
    maassCoeff k (jacobiCoeff φ) n r m = liftDivisorSum k (jacobiCoeff φ) n r m := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  rw [maassCoeff, ite_eq_right fun h ↦ hm'.ne' h.2.2]
  split_ifs with h
  · rfl
  · have hn : n < 0 := by
      by_contra hn
      exact h ⟨not_lt.mp hn, hm'.le⟩
    exact (liftDivisorSum_eq_zero n r m hφ (by nlinarith [sq_nonneg r])).symm

/-- **The Fourier–Jacobi coefficients of the Maass lift are the images of `φ` under the index
raising operators**: for `φ ∈ J_{k,1}` and `m ≥ 1`, `φ_m = φ ∣ V_m`, where
`φ_m(τ, z) = ∑_{n, r} a(n, r, m) e^{2πi(nτ + rz)}` is defined by the Fourier coefficients of the
lift and `(φ ∣ V_m)(τ, z) = m⁻¹ ∑ a^k φ((aτ + b)/d, az)` by the cosets of the matrices of
determinant `m` (Eichler and Zagier, Theorem 4.2). In particular the series of `φ_m` converges. -/
lemma maassFourierJacobi_eq_indexRaising (hφ : φ ∈ jacobiFormSpace k 1) (hm : 0 < m) :
    maassFourierJacobi k φ m = indexRaising k φ m := by
  funext x
  refine ((hasSum_liftDivisorSum_indexRaising x
    (hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ) hm).congr_fun
      fun q ↦ ?_).tsum_eq
  rw [maassCoeff_eq_liftDivisorSum hφ hm]

/-- **The theorem of Maass, reduced to convergence and holomorphy** (LMFDB `mf.siegel.lift.maass`):
for a Jacobi form `φ ∈ J_{k,1}` of weight `k ≥ 3`, if the series of the Maass lift converges
absolutely on `ℋ₂` and the lift is holomorphic, then the Maass lift is a Siegel modular form of
weight `k` on `Sp(4, ℤ)`. Its Fourier–Jacobi coefficients `φ_m = φ ∣ V_m` transform like Jacobi
forms of index `m` under `(0, -1; 1, 0)`, which gives the law under the partial inversion `J₁`, and
the law under the Siegel parabolic subgroup holds without convergence. -/
lemma maassLift_mem_scalarModularForms_of_summable_of_isHolomorphic (hφ : φ ∈ jacobiFormSpace k 1)
    (hk : 3 ≤ k) (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hF : IsHolomorphic (maassLift k φ)) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) := by
  lift k to ℕ using by omega
  exact maassLift_mem_scalarModularForms_of_summable_of_three_le hφ (by exact_mod_cast hk) hs hF
    fun _ hm x ↦ by
      rw [maassFourierJacobi_eq_indexRaising hφ hm, indexRaising_S x hφ.2.1 hm]

end SiegelUpperHalfSpace
