import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Poincaré series

For a subgroup `G` of `SL(2, ℤ)`, a multiplier system `v` on `G`, a cusp `s = γ_s ∞` of `G` of
width `w` with stabiliser `G_s` in `G`, an integer `n` and a weight `k ≥ 3`, the `n`-th Poincaré
series at `s` is `P(z) = Σ_{g ∈ G_s \ G} conj(v(g)) e^{2πi (n/w) γ_s⁻¹ g z} j(γ_s⁻¹ g, z)^{-k}`.

## Main definitions

* `ModularForm.cuspStabilizer`: the stabiliser `G_s` of the cusp `γ_s ∞` in `G`.
* `ModularForm.poincareTerm`: the term of the series at `g ∈ G`.
* `ModularForm.poincareSeries` (LMFDB `specialfunction.poincare`).
-/

open UpperHalfPlane Matrix SpecialLinearGroup OnePoint

open scoped MatrixGroups ComplexConjugate

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ))

variable (G) in
/-- The stabiliser `G_s = G ∩ γ_s Γ_∞ γ_s⁻¹` in `G` of the cusp `s = γ_s ∞`. -/
noncomputable def cuspStabilizer : Subgroup G :=
  (MulAction.stabilizer (GL (Fin 2) ℝ) (mapGL ℝ γ • (OnePoint.infty : OnePoint ℝ))).comap
    ((mapGL ℝ).comp G.subtype)

/-- The term `conj(v(g)) e^{2πi (n/w) γ_s⁻¹ g z} j(γ_s⁻¹ g, z)^{-k}` at `g ∈ G` and `z ∈ ℍ` of the
`n`-th Poincaré series of weight `k` and multiplier `v` at the cusp `γ_s ∞` of width `w`. -/
noncomputable def poincareTerm (v : G →* Circle) (k n : ℤ) (w : ℕ) (z : ℍ) (g : G) : ℂ :=
  conj (v g : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (n / w) * ↑((γ⁻¹ * g) • z)) *
    denom (γ⁻¹ * g) z ^ (-k)

/-- The `n`-th **Poincaré series** (LMFDB `specialfunction.poincare`)
`P_k^n(G, v; z; s) = Σ_{g ∈ G_s \ G} conj(v(g)) e^{2πi (n/w) γ_s⁻¹ g z} j(γ_s⁻¹ g, z)^{-k}` of
weight `k` and multiplier `v` on `G ≤ SL(2, ℤ)`, at the cusp `s = γ_s ∞` of width `w`, as an
unconditional sum (`tsum`, `0` when not summable) over the right cosets `G_s g`, each represented
by a chosen element; the definition imposes no hypothesis. For `G` of finite index, `k ≥ 3`, `w` the
width of `s` and `v(h) = (±1)^k` for `h ∈ G_s` with `γ_s⁻¹ h γ_s = ±T^b` (the corrected form of the
LMFDB's "`v` trivial on `G_s`", which fails at `-I` for odd `k`), the terms do not depend on the
representatives (`PoincareConvergence.lean`), the series converges absolutely to a holomorphic
function (`PoincareHolomorphic.lean`), and for `n ≥ 1` it is a cusp form
(`PoincareCuspForm.lean`). -/
noncomputable def poincareSeries (v : G →* Circle) (k n : ℤ) (w : ℕ) (z : ℍ) : ℂ :=
  ∑' q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)), poincareTerm γ v k n w z q.out

end ModularForm
