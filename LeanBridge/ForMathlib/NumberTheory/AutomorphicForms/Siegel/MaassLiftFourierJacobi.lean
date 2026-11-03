import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GritsenkoLiftModularity
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftParabolic

/-!
# The Fourier–Jacobi expansion of the Maass lift

When its series converges absolutely, the Maass lift `F(Z) = ∑ a(n, r, m) e^{2πi(nτ + rz + mω)}`
of `φ` (`SiegelUpperHalfSpace.maassLift`, LMFDB `mf.siegel.lift.maass`) has the Fourier–Jacobi
expansion `F(Z) = ∑_m φ_m(τ, z) e^{2πimω}`, where `φ_m(τ, z) = ∑_{n, r} a(n, r, m) e^{2πi(nτ + rz)}`
is `φ ∣ V_m` for `m ≥ 1`, the image of `φ` under the index raising operator of Eichler and Zagier,
and `c(0, 0)` times the Eisenstein series of weight `k` for `m = 0`. The partial inversion
`J₁ : (τ, z, ω) ↦ (-1/τ, z/τ, ω - z²/τ)` acts on each term through the transformation law of
`φ_m` under `(0, -1; 1, 0)`, so that `F(J₁Z) = τ^k F(Z)` as soon as each `φ_m` is a Jacobi form of
weight `k` and index `m`. With the transformation law under the Siegel parabolic subgroup and the
generation of `Sp(4, ℤ)` by it and `J₁`, this reduces the theorem of Maass (`MaassLiftTheorem`,
Eichler and Zagier, Theorem 6.2) to the absolute convergence of the series, the holomorphy of the
lift, and the theorem of Eichler and Zagier (Theorem 4.2) that `V_m` maps `J_{k,1}` to `J_{k,m}`.

## Main definitions

* `SiegelUpperHalfSpace.maassFourierJacobi` (LMFDB `mf.siegel.lift.maass`): the Fourier–Jacobi
  coefficients `φ_m` of the Maass lift.

## Main results

* `SiegelUpperHalfSpace.maassLift_partialInversion_smul`: `F(J₁Z) = τ^k F(Z)`, if the series
  converges absolutely and every `φ_m` transforms under `(0, -1; 1, 0)` like a Jacobi form of
  weight `k` and index `m`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_summable`: the Maass lift of
  `φ ∈ J_{k,1}` is a Siegel modular form of weight `k` on `Sp(4, ℤ)` if its series converges
  absolutely, it is holomorphic and every `φ_m` is a Jacobi form of weight `k` and index `m`.
-/

open ModularForm ModularGroup SymplecticGroup

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} (m : ℤ) (x : ℍ × ℂ) (Z : SiegelUpperHalfSpace (Fin 2))

variable (k φ) in
/-- The `m`-th **Fourier–Jacobi coefficient** `φ_m(τ, z) = ∑_{n, r} a(n, r, m) e^{2πi(nτ + rz)}` of
the Maass lift `(Vφ)(τ, z, ω) = ∑_m φ_m(τ, z) e^{2πimω}` (LMFDB `mf.siegel.lift.maass`) of
`φ : ℍ × ℂ → ℂ`, where `a(n, r, m)` are the Fourier coefficients of the lift (`maassCoeff`). For
`m ≥ 1` it is the image `φ ∣ V_m` of `φ` under the index raising operator
`V_m : J_{k,1} → J_{k,m}` of Eichler and Zagier (§4), defined by its Fourier coefficients
`∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)`; for `m = 0` it is `c(0, 0)` times the Eisenstein series
`-B_k/2k + ∑_{n ≥ 1} σ_{k-1}(n) qⁿ`, and it vanishes for `m < 0`. The `tsum` is the junk value `0`
where the series does not converge absolutely. -/
noncomputable def maassFourierJacobi : ℂ :=
  ∑' q : ℤ × ℤ, maassCoeff k (jacobiCoeff φ) q.1 q.2 m * jacobiFourierExp q x

/-- **The transformation law of the Maass lift under the partial inversion**
`J₁ : (τ, z; z, ω) ↦ (-1/τ, z/τ; z/τ, ω - z²/τ)`, `F(J₁Z) = τ^k F(Z)`, from its Fourier–Jacobi
expansion `F(Z) = ∑_m φ_m(τ, z) e^{2πimω}`: if the series of the lift converges absolutely on
`ℋ₂`, so that it can be summed over `m` first, and every Fourier–Jacobi coefficient `φ_m`
transforms under `(0, -1; 1, 0)` like a Jacobi form of weight `k` and index `m`,
`φ_m(-1/τ, z/τ) = τ^k e^{2πimz²/τ} φ_m(τ, z)`, then the factor `e^{2πimz²/τ}` cancels against the
shift `ω ↦ ω - z²/τ`. This is `tsum_mul_liftExp_partialInversion_smul` for `N = 1`. -/
lemma maassLift_partialInversion_smul (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2),
    Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hS : ∀ (m : ℕ) (x : ℍ × ℂ),
      maassFourierJacobi k φ m (S • x.1, x.2 / UpperHalfPlane.denom S x.1) =
        jacobiFactor k m x S * maassFourierJacobi k φ m x) :
    maassLift k φ (map (Int.castRingHom ℝ) partialInversion • Z) =
      Z.val 0 0 ^ k * maassLift k φ Z :=
  tsum_mul_liftExp_partialInversion_smul Z hs
    (fun _ hl _ ↦ (ite_eq_right fun h ↦ hl.ne h.2.2).trans (ite_eq_right fun h ↦ hl.not_ge h.2))
    fun m x ↦ by
      rw [one_mul]
      exact hS m x

/-- **The theorem of Maass, reduced to the index raising operators and convergence** (LMFDB
`mf.siegel.lift.maass`): for `φ ∈ J_{k,1}`, if the series of the Maass lift converges absolutely on
`ℋ₂`, the lift is holomorphic, and every Fourier–Jacobi coefficient `φ_m` of the lift is a Jacobi
form of weight `k` and index `m`, then the Maass lift is a Siegel modular form of weight `k` on
`Sp(4, ℤ)`. For `m ≥ 1` the last condition is the theorem of Eichler and Zagier (Theorem 4.2) that
the index raising operator `V_m` maps `J_{k,1}` to `J_{k,m}`, and for `m = 0` it says that
`c(0, 0)` times the Eisenstein series `-B_k/2k + ∑ σ_{k-1}(n) qⁿ` is a modular form of weight
`k`. -/
lemma maassLift_mem_scalarModularForms_of_summable (hφ : φ ∈ jacobiFormSpace k 1)
    (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hF : IsHolomorphic (maassLift k φ))
    (hV : ∀ m : ℕ, maassFourierJacobi k φ m ∈ jacobiFormSpace k m) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) :=
  maassLift_mem_scalarModularForms hφ hF fun Z ↦
    maassLift_partialInversion_smul Z hs fun m ↦ (hV m).2.1 S

end SiegelUpperHalfSpace
