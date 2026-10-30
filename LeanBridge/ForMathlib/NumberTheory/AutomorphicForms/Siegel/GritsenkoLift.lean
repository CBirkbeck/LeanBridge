import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.FourierCoefficients
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwo
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.Level
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ScalarValued
import Mathlib.NumberTheory.Bernoulli

/-!
# The Gritsenko and Maass lifts

For a Jacobi cusp form `φ ∈ J_{k,N}^cusp` of weight `k` and index `N` with Fourier coefficients
`c(n, r)`, the Gritsenko lift is the function
`Grit(φ)(Z) = ∑_{n, r, m} a(n, r, m) e^{2πi(nτ + rz + Nmω)}` on the Siegel upper half-space `ℋ₂`,
`Z = (τ, z; z, ω)`, with `a(n, r, m) = ∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` for `m ≥ 1` and
`a(n, r, m) = 0` for `m ≤ 0`; its `m`-th Fourier–Jacobi coefficient is the image of `φ` under the
index raising operator `V_m : J_{k,N} → J_{k,Nm}` of Eichler and Zagier. Gritsenko proved that it
is a paramodular cusp form of weight `k` and level `N`: `Grit(φ) ∈ S_k(K(N))`. For `N = 1` and any
Jacobi form `φ ∈ J_{k,1}`, not only a cusp form, the Maass lift adds the terms with `m = 0`:
`a(n, 0, 0) = σ_{k-1}(n) c(0, 0)` for `n ≥ 1` and `a(0, 0, 0) = -(B_k / 2k) c(0, 0)`. It is a Siegel
modular form of weight `k` on `Sp(4, ℤ)` (Maass; Eichler and Zagier, Theorem 6.2), and on cusp forms
it is the Gritsenko lift of level `1` (`maassLift_eq_gritsenkoLift`).

The two lifts are defined here by these formulas, as sums of series (`tsum`). That the series
converge absolutely on `ℋ₂`, which needs the polynomial growth of the coefficients `c(n, r)`, and
the theorems of Gritsenko and of Maass are stated (`GritsenkoLiftTheorem`, `MaassLiftTheorem`) and
not proved. The coefficient formula of the knowl `mf.siegel.lift.gritsenko` was checked numerically
on `φ = φ_{10,1}^N ∈ J_{10N,N}^cusp`, `N = 1, 2, 3`, against elements of `K(N)` outside its Jacobi
subgroup, such as `(τ, z, ω) ↦ (τ - z²/ω, z/(Nω), -1/(N²ω))`: no condition `gcd(d, N) = 1` on the
divisors `d` is needed (with that condition the lift is not paramodular).

## Main definitions

* `SiegelUpperHalfSpace.liftDivisorSum`: the divisor sum `∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)`.
* `SiegelUpperHalfSpace.gritsenkoCoeff` (LMFDB `mf.siegel.lift.gritsenko`): the Fourier coefficients
  of the Gritsenko lift.
* `SiegelUpperHalfSpace.liftExp`: the exponential `e^{2πi(nτ + rz + Nmω)}`.
* `SiegelUpperHalfSpace.gritsenkoLift` (LMFDB `mf.siegel.lift.gritsenko`): the Gritsenko lift.
* `SiegelUpperHalfSpace.GritsenkoLiftTheorem` (LMFDB `mf.siegel.lift.gritsenko`): Gritsenko's
  theorem, as a statement.
* `SiegelUpperHalfSpace.maassCoeff` (LMFDB `mf.siegel.lift.maass`): the Fourier coefficients of the
  Maass lift.
* `SiegelUpperHalfSpace.maassLift` (LMFDB `mf.siegel.lift.maass`): the Maass lift.
* `SiegelUpperHalfSpace.MaassLiftTheorem` (LMFDB `mf.siegel.lift.maass`): the theorem of Maass, as a
  statement.

## Main results

* `SiegelUpperHalfSpace.gritsenkoCoeff_comm`: the coefficients `a(n, r, m)` are symmetric in `n` and
  `m`.
* `SiegelUpperHalfSpace.maassLift_eq_gritsenkoLift`: on Jacobi cusp forms of index `1`, the Maass
  lift is the Gritsenko lift of level `1`.
-/

open Complex ModularForm Real

open UpperHalfPlane hiding I

namespace SiegelUpperHalfSpace

variable (k : ℤ) (N : ℕ) (c : ℤ × ℤ → ℂ) (φ : ℍ × ℂ → ℂ) (n r m : ℤ)
    (Z : SiegelUpperHalfSpace (Fin 2))

/-- The divisor sum `∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` over the positive divisors `d` of the
greatest common divisor of `n, r, m`; it is `0` for `n = r = m = 0`. -/
noncomputable def liftDivisorSum : ℂ :=
  ∑ d ∈ ((n.gcd r : ℤ).gcd m).divisors, (d : ℂ) ^ (k - 1) * c (n * m / (d : ℤ) ^ 2, r / d)

/-- The **Fourier coefficient** `a(n, r, m)` of the Gritsenko lift (LMFDB
`mf.siegel.lift.gritsenko`) of weight `k` of a function with Fourier coefficients `c(n, r)`:
`a(n, r, m) = ∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` for `m ≥ 1` and `a(n, r, m) = 0` for
`m ≤ 0`. It is the coefficient of `e^{2πi(nτ + rz + Nmω)}`. The knowl states the formula without a
range; it can only hold for `m ≥ 1`: for `m = n = r = 0` the sum would run over all `d`, and for
negative `n` and `m` it would give nonzero coefficients at negative definite `(n, r/2; r/2, Nm)`,
which the Fourier expansion of a Siegel modular form does not have. -/
noncomputable def gritsenkoCoeff : ℂ :=
  if 0 < m then liftDivisorSum k c n r m else 0

/-- The exponential `e^{2πi(nτ + rz + Nmω)}` at `Z = (τ, z; z, ω)`. -/
noncomputable def liftExp : ℂ :=
  cexp (2 * π * I * (n * Z.val 0 0 + r * Z.val 0 1 + N * m * Z.val 1 1))

/-- The **Gritsenko lift** `Grit(φ)` (LMFDB `mf.siegel.lift.gritsenko`) of weight `k` and level `N`
of `φ : ℍ × ℂ → ℂ`, a function on the Siegel upper half-space `ℋ₂` defined by its Fourier
coefficients: `Grit(φ)(Z) = ∑_{n, r, m ∈ ℤ} a(n, r, m) e^{2πi(nτ + rz + Nmω)}` for
`Z = (τ, z; z, ω)`, where `a(n, r, m) = ∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` for `m ≥ 1` and
`a(n, r, m) = 0` otherwise (`gritsenkoCoeff`), and `c(n, r)` are the Fourier coefficients of `φ`
(`jacobiCoeff`). For a Jacobi cusp form `φ ∈ J_{k,N}^cusp` the series converges absolutely and
`Grit(φ)` is a paramodular cusp form in `S_k(K(N))`, the frequencies `Nm` of `ω` being those of the
Fourier expansions on `K(N)` (`GritsenkoLiftTheorem`, not proved here). The `tsum` is the sum of the
series wherever it converges absolutely, and the junk value `0` elsewhere. -/
noncomputable def gritsenkoLift : ℂ :=
  ∑' p : ℤ × ℤ × ℤ, gritsenkoCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp N p.1 p.2.1 p.2.2 Z

/-- **Gritsenko's theorem** (LMFDB `mf.siegel.lift.gritsenko`), as a statement: for `N ≥ 1` and a
Jacobi cusp form `φ ∈ J_{k,N}^cusp`, the series of the Gritsenko lift converges absolutely on `ℋ₂`,
and `Grit(φ)` is a paramodular cusp form of weight `k` and level `N`: `Grit(φ) ∈ S_k(K(N))`, where
`K(N) = Γ^para(1, N)`. It is a theorem of Gritsenko, which is not proved here. -/
structure GritsenkoLiftTheorem : Prop where
  summable : ∀ (k : ℤ) (N : ℕ+) (φ : ℍ × ℂ → ℂ), φ ∈ jacobiCuspFormSpace k N →
    ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      gritsenkoCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp N p.1 p.2.1 p.2.2 Z
  mem_cuspForms : ∀ (k : ℤ) (N : ℕ+) (φ : ℍ × ℂ → ℂ), φ ∈ jacobiCuspFormSpace k N →
    gritsenkoLift k N φ ∈ cuspForms (TauCeti.detPowerRep ℂ 2 k)
      (SymplecticGroup.paramodular ![1, N]) 1

/-- **The Fourier coefficients of the Gritsenko lift are symmetric** in `n` and `m`, which for a
Jacobi cusp form makes the lift invariant under `(τ, z, ω) ↦ (Nω, z, τ/N)`. -/
lemma gritsenkoCoeff_comm (hn : 0 < n) (hm : 0 < m) :
    gritsenkoCoeff k c n r m = gritsenkoCoeff k c m r n := by
  have h : (n.gcd r : ℤ).gcd m = (m.gcd r : ℤ).gcd n := by
    rw [Int.gcd_assoc, Int.gcd_comm, Int.gcd_comm r]
  rw [gritsenkoCoeff, gritsenkoCoeff, ite_eq_left hm, ite_eq_left hn, liftDivisorSum,
    liftDivisorSum, h, mul_comm n]

/-- The **Fourier coefficient** `a(n, r, m)` of the Maass lift (LMFDB `mf.siegel.lift.maass`) of
weight `k` of a function with Fourier coefficients `c(n, r)`: `a(0, 0, 0) = -(B_k / 2k) c(0, 0)`,
`a(n, r, m) = ∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` for the other `n, m ≥ 0`, and
`a(n, r, m) = 0` if `n < 0` or `m < 0`. It is the coefficient of `e^{2πi(nτ + rz + mω)}`. For a
Jacobi form of index `1`, `c(n, r)` only depends on `4n - r²`
(`ModularForm.jacobiCoeff_eq_of_mem_jacobiFormSpace_one`), and this is the formula
`a(n, r, m) = ∑_{d ∣ (n, r, m)} d^{k-1} c((4nm - r²)/d²)` of Eichler and Zagier; for `m = 0` it
gives `a(n, 0, 0) = σ_{k-1}(n) c(0, 0)`, the coefficients of `c(0, 0)` times the Eisenstein series
of weight `k`. -/
noncomputable def maassCoeff : ℂ :=
  if n = 0 ∧ r = 0 ∧ m = 0 then -((bernoulli k.toNat : ℂ) / (2 * k)) * c (0, 0)
  else if 0 ≤ n ∧ 0 ≤ m then liftDivisorSum k c n r m else 0

/-- The **Maass lift** (LMFDB `mf.siegel.lift.maass`) of weight `k` of `φ : ℍ × ℂ → ℂ`, a function
on the Siegel upper half-space `ℋ₂` defined by its Fourier coefficients:
`(Vφ)(Z) = ∑_{n, r, m ∈ ℤ} a(n, r, m) e^{2πi(nτ + rz + mω)}` for `Z = (τ, z; z, ω)`, where
`a(n, r, m)` is given by `maassCoeff` from the Fourier coefficients `c(n, r)` of `φ`
(`jacobiCoeff`). For a Jacobi form `φ ∈ J_{k,1}` of index `1` the series converges absolutely, and
`Vφ` is a Siegel modular form of weight `k` on `Sp(4, ℤ)`, a cusp form if `φ` is one
(`MaassLiftTheorem`, not proved here): this is the map `V : J_{k,1} → M_k(Sp(4, ℤ))` of Eichler and
Zagier, whose image is the Maass space, spanned by the Saito–Kurokawa lifts. The knowl gives no
formula; this is that of Eichler and Zagier. The `tsum` is the sum of the series wherever it
converges absolutely, and the junk value `0` elsewhere. -/
noncomputable def maassLift : ℂ :=
  ∑' p : ℤ × ℤ × ℤ, maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z

/-- **The theorem of Maass** (LMFDB `mf.siegel.lift.maass`), as a statement: for a Jacobi form
`φ ∈ J_{k,1}`, the series of the Maass lift converges absolutely on `ℋ₂`, the Maass lift `Vφ` is a
Siegel modular form of weight `k` on `Sp(4, ℤ)`, and it is a cusp form if `φ` is one (Eichler and
Zagier, Theorem 6.2). It is not proved here. -/
structure MaassLiftTheorem : Prop where
  summable : ∀ (k : ℤ) (φ : ℍ × ℂ → ℂ), φ ∈ jacobiFormSpace k 1 →
    ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z
  mem_modularForms : ∀ (k : ℤ) (φ : ℍ × ℂ → ℂ), φ ∈ jacobiFormSpace k 1 →
    maassLift k φ ∈ scalarModularForms k (SymplecticGroup.integral (Fin 2))
  mem_cuspForms : ∀ (k : ℤ) (φ : ℍ × ℂ → ℂ), φ ∈ jacobiCuspFormSpace k 1 →
    maassLift k φ ∈ cuspForms (TauCeti.detPowerRep ℂ 2 k) (SymplecticGroup.integral (Fin 2)) 1

variable {k φ} in
lemma maassCoeff_eq_gritsenkoCoeff (hφ : φ ∈ jacobiCuspFormSpace k 1) :
    maassCoeff k (jacobiCoeff φ) n r m = gritsenkoCoeff k (jacobiCoeff φ) n r m := by
  have hc (p : ℤ × ℤ) (hp : 4 * p.1 ≤ p.2 ^ 2) : jacobiCoeff φ p = 0 :=
    jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2 <| by
      simpa using hp
  have hs (hp : ∀ d ∈ ((n.gcd r : ℤ).gcd m).divisors, 4 * (n * m / (d : ℤ) ^ 2) ≤ (r / d) ^ 2) :
      liftDivisorSum k (jacobiCoeff φ) n r m = 0 :=
    Finset.sum_eq_zero fun d hd ↦ by
      rw [hc _ (hp d hd), mul_zero]
  rcases lt_or_ge 0 m with hm | hm
  · rcases lt_or_ge n 0 with hn | hn
    · rw [maassCoeff, ite_eq_right (by omega), ite_eq_right (by omega), gritsenkoCoeff,
        ite_eq_left hm, hs]
      intro d hd
      have hnm : n * m / (d : ℤ) ^ 2 ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg (by nlinarith) <|
        pow_pos (Int.natCast_pos.mpr (Nat.pos_of_mem_divisors hd)) 2
      nlinarith
    · rw [maassCoeff, ite_eq_right (by omega), ite_eq_left ⟨hn, hm.le⟩, gritsenkoCoeff,
        ite_eq_left hm]
  · rw [gritsenkoCoeff, ite_eq_right (by omega), maassCoeff]
    split_ifs with h₀ h₁
    · rw [hc (0, 0) (by simp), mul_zero]
    · refine hs fun d hd ↦ ?_
      rw [(by omega : m = 0), mul_zero, Int.zero_ediv, mul_zero]
      positivity
    · rfl

variable {k φ} in
/-- **On Jacobi cusp forms of index `1`, the Maass lift is the Gritsenko lift of level `1`**: their
Fourier coefficients agree, the terms with `m = 0` of the Maass lift vanishing for cusp forms. -/
lemma maassLift_eq_gritsenkoLift (hφ : φ ∈ jacobiCuspFormSpace k 1) :
    maassLift k φ = gritsenkoLift k 1 φ :=
  funext fun Z ↦ tsum_congr fun p ↦ by
    rw [maassCoeff_eq_gritsenkoCoeff _ _ _ hφ]

end SiegelUpperHalfSpace
