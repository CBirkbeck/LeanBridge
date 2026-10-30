import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.UpperHalfSpace
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Theta series of lattices with pluriharmonic coefficients

For the Gram matrix `Q` of a positive definite even lattice of rank `m` (a symmetric `m × m` matrix
with integral entries and even diagonal) and a polynomial `P` in the entries of an `m × g` matrix,
the theta series of degree `g` is `θ_{Q,P}(Ω) = ∑_{N ∈ ℤ^{m × g}} P(N) e^{πi tr(NᵀQNΩ)}` on the
Siegel upper half-space `ℋ_g`; for `P = 1` it is the theta series `θ_Q` of the lattice. The
polynomial `P` is pluriharmonic with respect to `Q` if `∑_{a, b} (Q⁻¹)_{ab} ∂²P/∂N_{ai}∂N_{bj} = 0`
for all columns `i, j`: in coordinates `Y = FN` with `Q = FᵀF`, this is the usual condition
`∑_r ∂²P/∂Y_{ri}∂Y_{rj} = 0`. If moreover `P(NA) = det(A)^ν P(N)` for `A ∈ GL(g, ℂ)`, then `θ_{Q,P}`
is a Siegel modular form of weight `m/2 + ν` on `Γ₀(ℓ)`, where `ℓQ⁻¹` is even, with the character
`γ ↦ ((-1)^{m/2} det Q / det D)` for even `m`, and a cusp form if `ν > 0` (Freitag, Andrianov); this
is not proved here.

## Main definitions

* `SiegelUpperHalfSpace.latticeTheta` (LMFDB `mf.siegel.theta_series`): the theta series
  `θ_{Q,P}`.
* `SiegelUpperHalfSpace.IsPluriharmonic` (LMFDB `mf.siegel.theta_series`): pluriharmonic
  polynomials.
-/

open Complex Matrix MvPolynomial Real

namespace SiegelUpperHalfSpace

variable {ι l : Type*} [Fintype ι] [Fintype l] (Q : Matrix ι ι ℚ) (P : MvPolynomial (ι × l) ℂ)

/-- The **theta series** `θ_{Q,P}(Ω) = ∑_{N ∈ ℤ^{m × g}} P(N) e^{πi tr(NᵀQNΩ)}` (LMFDB
`mf.siegel.theta_series`) of degree `g = |l|` of a rational symmetric `m × m` matrix `Q`, `m = |ι|`,
with coefficient the polynomial `P` in the entries `N_{ai}` of `N`. For `Q` the Gram matrix of a
positive definite even lattice the series converges absolutely, which is not proved here; the
`tsum` is the junk value `0` where it does not. The knowl writes `exp(πi N'QNΩ)` for the scalar
`exp(πi tr(N'QNΩ))`. -/
noncomputable def latticeTheta (Ω : SiegelUpperHalfSpace l) : ℂ :=
  ∑' N : Matrix ι l ℤ, eval (fun p ↦ (N p.1 p.2 : ℂ)) P *
    cexp (π * I * ((N.map ((↑) : ℤ → ℂ))ᵀ * Q.map ((↑) : ℚ → ℂ) * N.map ((↑) : ℤ → ℂ) *
      Ω.val).trace)

variable [DecidableEq ι] in
/-- A polynomial `P` in the entries of an `m × g` matrix `N` is **pluriharmonic** with respect to an
invertible symmetric matrix `Q` (LMFDB `mf.siegel.theta_series`) if
`∑_{a, b} (Q⁻¹)_{ab} ∂²P/∂N_{ai}∂N_{bj} = 0` for all columns `i, j`, the condition under which the
theta series `θ_{Q,P}` transforms like a modular form. For `Q = 1` it is the knowl's condition
`∑_r ∂²P/∂N_{ri}∂N_{rj} = 0`, which the knowl writes with the roles of rows and columns exchanged:
summing over the `g` columns for two rows instead of over the `m` rows for two columns. -/
def IsPluriharmonic : Prop :=
  ∀ i j : l, ∑ a, ∑ b, (Q⁻¹ a b : ℂ) • pderiv (a, i) (pderiv (b, j) P) = 0

end SiegelUpperHalfSpace
