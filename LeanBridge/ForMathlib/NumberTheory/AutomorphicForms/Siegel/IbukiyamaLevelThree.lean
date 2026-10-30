import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IbukiyamaRings
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LatticeThetaSeries
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Siegel modular forms of degree 2 on `Γ₀(3)`

Ibukiyama determined the graded ring `M_*(Γ₀(3))` of Siegel modular forms of degree 2 on `Γ₀(3)` and
the module `⊕_k M_k(Γ₀(3), ψ₃)` of forms with the character `ψ₃(γ) = (-3 / det D)`. The generators
are theta series of lattices: with the Gram matrices `A₂`, `E₆`, `E₆^* = 3E₆⁻¹` and `2S`,
`α₁ = θ_{A₂}`, `β₃ = θ_{E₆} - 10θ_{A₂}³ + 9θ_{E₆^*}`, `δ₃ = θ_{E₆} - 9θ_{E₆^*}` (weights 1, 3, 3 and
character `ψ₃`), the cusp form `γ₄ = θ_{2S,P}` of weight 4 with a pluriharmonic coefficient `P`, and
the cusp form `χ₁₄` of weight 14 and character `ψ₃`, a Jacobian of the other four. With
`B = ℂ[α₁, β₃, γ₄, δ₃]`, the four being algebraically independent, and
`C = ℂ[α₁², β₃², γ₄, δ₃²]`, over which `B` is free with basis the `α₁^a β₃^b δ₃^d`, `a, b, d ≤ 1`,
`M_*(Γ₀(3)) = B^even ⊕ B^odd χ₁₄` and `⊕_k M_k(Γ₀(3), ψ₃) = B^odd ⊕ B^even χ₁₄`, the exponents
`even` and `odd` referring to the weight. The structure theorems are stated here, not proved.

The knowls' formulas were checked exactly on Fourier coefficients `a(n, r, m)` of
`e^{2πi(nτ + rz + mω)}`, computed by counting lattice vectors. Corrections:
* the knowls' `P` is not homogeneous, and not pluriharmonic; with the first term squared,
  `P = (x₁y₃ - x₃y₁)² + (x₂y₄ - x₄y₂)² - (x₁y₄ - x₄y₁ + x₃y₂ - x₂y₃ + x₁y₂ - x₂y₁)²` is
  homogeneous of degree 2 in the `2 × 2` minors of `(x | y)`, as the weight `4 = 4/2 + 2` of `γ₄`
  needs, and pluriharmonic with respect to `2S` (`isPluriharmonic_P`);
* `S` has half-integral entries, and `θ_{S,P}` is `∑ P(N) e^{2πi tr(NᵀSNΩ)} = θ_{2S,P}`, where
  `2S ≅ A₂ ⊕ A₂` is even (with `θ_{2S} = θ_{A₂}²`, checked);
* `α₁`, `β₃`, `δ₃` are not cusp forms, as the knowls' `S₁(Γ₀(3), ψ₃)`, `S₃(Γ₀(3), ψ₃)` say: their
  coefficients `a(0, 0, 0)` are `1`, `0`, `-8` and `a(1, 0, 0)` are `6`, `-108`, `72`; they lie in
  `M₁(Γ₀(3), ψ₃)` and `M₃(Γ₀(3), ψ₃)`;
* in the determinant defining `χ₁₄`, the first row must be `(kᵢFᵢ) = (α₁, 3β₃, 4γ₄, 3δ₃)` for the
  Jacobian to be modular: the knowls' `4γ₄/2` and `3δ₄` are typos. With this row the knowls'
  normalisation `2⁻⁹ 3⁻¹⁰ (2πi)⁻³` gives `χ₁₄` the Fourier coefficient `1` at
  `e^{2πi(2τ + z + 3ω)}` and `-1` at `e^{2πi(3τ + z + 2ω)}`, its only nonzero coefficients
  `a(n, r, m)` with `n, m ≤ 3` and `r > 0` (the entry `4γ₄` does not contribute to them, so they
  do not distinguish it from the knowls' `4γ₄/2`; the row is forced by modularity).

## Main definitions

* `SymplecticGroup.psi3` (LMFDB `mf.siegel.family.gamma0_3_psi_3`): the character
  `ψ₃(γ) = (-3 / det D)` of `Γ₀(3)`, and `SymplecticGroup.psi3Rat` the same on `Γ₀(3) ⊆ Sp(4, ℚ)`.
* `SiegelUpperHalfSpace.gradedModularFormsChar`: the module `⊕_k M_k(Γ, ψ)`.
* `SiegelUpperHalfSpace.IbukiyamaThree.A2`, `E6`, `E6dual`, `S`, `P`: the lattices and the
  pluriharmonic polynomial of the knowls.
* `SiegelUpperHalfSpace.IbukiyamaThree.alpha1`, `beta3`, `delta3`, `gamma4`, `chi14` (LMFDB
  `mf.siegel.family.gamma0_3`, `mf.siegel.family.gamma0_3_psi_3`): the generators.
* `SiegelUpperHalfSpace.IbukiyamaThree.Gamma0ThreeGenerators`: the modularity and the algebraic
  independence of the generators, as a statement.
* `SiegelUpperHalfSpace.IbukiyamaThree.Gamma0ThreeStructure` (LMFDB `mf.siegel.family.gamma0_3`) and
  `SiegelUpperHalfSpace.IbukiyamaThree.Gamma0ThreePsi3Structure` (LMFDB
  `mf.siegel.family.gamma0_3_psi_3`): Ibukiyama's structure theorems, as statements.

## Main results

* `SiegelUpperHalfSpace.IbukiyamaThree.isPluriharmonic_P`: the corrected polynomial `P` is
  pluriharmonic with respect to `2S`.
-/

open Complex Matrix MvPolynomial Real

namespace SymplecticGroup

variable (l : Type*) [Fintype l] [DecidableEq l]

/-- The character `ψ₃(γ) = (-3 / det D)` of `Γ₀(3)` (LMFDB `mf.siegel.family.gamma0_3_psi_3`,
`mf.siegel.family.gamma0_3`), for `γ = (A, B; C, D) ∈ Γ₀(3)`, where `det D` is prime to `3` since
`C ≡ 0 (mod 3)`: the Kronecker symbol `(-3 / d)` is the Legendre symbol `(d / 3)`, the quadratic
character of `ℤ/3ℤ`, applied to `det D`. -/
noncomputable def psi3 : Gamma0 l 3 →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp <| (quadraticChar (ZMod 3)).toUnitHom.comp <|
    siegelParabolicDet.comp <|
      (map (Int.castRingHom (ZMod 3))).subgroupComap (siegelParabolic l (ZMod 3))

/-- The character `ψ₃` of `Γ₀(3)`, on its image in `Sp(2g, ℚ)`. -/
noncomputable def psi3Rat : (Gamma0 l 3).map (map (Int.castRingHom ℚ)) →* ℂˣ :=
  (psi3 l).comp ((Gamma0 l 3).equivMapOfInjective _ map_intCast_injective).symm.toMonoidHom

end SymplecticGroup

namespace SiegelUpperHalfSpace

/-- The module `⊕_{k ≥ 0} M_k(Γ, ψ)` of scalar-valued Siegel modular forms of degree `n` with
character `ψ` on `Γ` (LMFDB `mf.siegel.family.gamma0_3_psi_3`), as the sum of the spaces
`M_k(Γ, ψ)` in the functions on `ℋ_n`; for `ψ = 1` it is the graded ring `gradedModularForms Γ`. -/
noncomputable def gradedModularFormsChar {n : ℕ} (Γ : Subgroup (symplecticGroup (Fin n) ℚ))
    (ψ : Γ →* ℂˣ) : Submodule ℂ (SiegelUpperHalfSpace (Fin n) → ℂ) :=
  ⨆ k : ℕ, modularForms (TauCeti.detPowerRep ℂ n k) Γ ψ

namespace IbukiyamaThree

/-- The Gram matrix `A₂ = (2, 1; 1, 2)` of the root lattice `A₂` (LMFDB
`mf.siegel.family.gamma0_3`). -/
def A2 : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2, 1; 1, 2]

/-- The Gram matrix of the root lattice `E₆`, its Cartan matrix (LMFDB
`mf.siegel.family.gamma0_3`). -/
def E6 : Matrix (Fin 6) (Fin 6) ℚ :=
  !![2, -1, 0, 0, 0, 0; -1, 2, -1, 0, 0, 0; 0, -1, 2, -1, 0, -1; 0, 0, -1, 2, -1, 0;
    0, 0, 0, -1, 2, 0; 0, 0, -1, 0, 0, 2]

/-- The Gram matrix `E₆^* = 3E₆⁻¹` of the dual lattice of `E₆`, scaled by `3` (LMFDB
`mf.siegel.family.gamma0_3`), an even matrix of determinant `3⁵`. -/
noncomputable def E6dual : Matrix (Fin 6) (Fin 6) ℚ :=
  (3 : ℚ) • E6⁻¹

/-- The half-integral matrix `S = (1, 0, 3/2, 0; 0, 1, 0, 3/2; 3/2, 0, 3, 0; 0, 3/2, 0, 3)` (LMFDB
`mf.siegel.family.gamma0_3`); `2S` is the Gram matrix of a lattice isometric to `A₂ ⊕ A₂`. -/
def S : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 3 / 2, 0; 0, 1, 0, 3 / 2; 3 / 2, 0, 3, 0; 0, 3 / 2, 0, 3]

variable (i : Fin 4)

/-- The coordinate `xᵢ = N_{i1}` of the first column of `N ∈ ℂ^{4 × 2}`. -/
private noncomputable def xVar : MvPolynomial (Fin 4 × Fin 2) ℂ :=
  X (i, 0)

/-- The coordinate `yᵢ = N_{i2}` of the second column of `N ∈ ℂ^{4 × 2}`. -/
private noncomputable def yVar : MvPolynomial (Fin 4 × Fin 2) ℂ :=
  X (i, 1)

/-- The pluriharmonic polynomial
`P(x, y) = (x₁y₃ - x₃y₁)² + (x₂y₄ - x₄y₂)² - (x₁y₄ - x₄y₁ + x₃y₂ - x₂y₃ + x₁y₂ - x₂y₁)²` of the
columns `x, y` of `N ∈ ℂ^{4 × 2}` (LMFDB `mf.siegel.family.gamma0_3`). The knowls write the first
term `(x₁y₃ - x₃y₁)` without the square, which makes `P` neither homogeneous nor pluriharmonic; with
the square, `P` is a quadratic form in the `2 × 2` minors of `N`, so `P(NA) = det(A)² P(N)`. -/
noncomputable def P : MvPolynomial (Fin 4 × Fin 2) ℂ :=
  (xVar 0 * yVar 2 - xVar 2 * yVar 0) ^ 2 + (xVar 1 * yVar 3 - xVar 3 * yVar 1) ^ 2 -
    (xVar 0 * yVar 3 - xVar 3 * yVar 0 + xVar 2 * yVar 1 - xVar 1 * yVar 2 + xVar 0 * yVar 1 -
      xVar 1 * yVar 0) ^ 2

/-- **`P` is pluriharmonic with respect to `2S`**: `∑_{a, b} ((2S)⁻¹)_{ab} ∂²P/∂N_{ai}∂N_{bj} = 0`
for all columns `i, j`, so that `θ_{2S,P}` transforms like a modular form of weight `4/2 + 2`. -/
lemma isPluriharmonic_P : IsPluriharmonic ((2 : ℚ) • S) P := by
  have hinv : ((2 : ℚ) • S)⁻¹ = !![2, 0, -1, 0; 0, 2, 0, -1; -1, 0, 2 / 3, 0; 0, -1, 0, 2 / 3] := by
    refine inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [S]
  have h2 (a : Fin 4 × Fin 2) : pderiv a (2 : MvPolynomial (Fin 4 × Fin 2) ℂ) = 0 := by
    simpa using (pderiv a).map_natCast 2
  intro i j
  rw [hinv]
  refine MvPolynomial.funext fun x ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, P, xVar, yVar, h2] <;> ring1

/-- The form `α₁ = θ_{A₂}` of weight 1 and character `ψ₃` on `Γ₀(3)` (LMFDB
`mf.siegel.family.gamma0_3`, `mf.siegel.family.gamma0_3_psi_3`), not a cusp form. -/
noncomputable def alpha1 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  latticeTheta A2 1

/-- The form `β₃ = θ_{E₆} - 10θ_{A₂}³ + 9θ_{E₆^*}` of weight 3 and character `ψ₃` on `Γ₀(3)` (LMFDB
`mf.siegel.family.gamma0_3`, `mf.siegel.family.gamma0_3_psi_3`), not a cusp form. -/
noncomputable def beta3 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  latticeTheta E6 1 - (10 : ℂ) • latticeTheta A2 1 ^ 3 + (9 : ℂ) • latticeTheta E6dual 1

/-- The form `δ₃ = θ_{E₆} - 9θ_{E₆^*}` of weight 3 and character `ψ₃` on `Γ₀(3)` (LMFDB
`mf.siegel.family.gamma0_3`, `mf.siegel.family.gamma0_3_psi_3`), not a cusp form. -/
noncomputable def delta3 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  latticeTheta E6 1 - (9 : ℂ) • latticeTheta E6dual 1

/-- The cusp form `γ₄ = θ_{S,P} = ∑ P(N) e^{2πi tr(NᵀSNΩ)}` of weight 4 on `Γ₀(3)` (LMFDB
`mf.siegel.family.gamma0_3`, `mf.siegel.family.gamma0_3_psi_3`), the theta series of the even
matrix `2S` with the pluriharmonic coefficient `P`. -/
noncomputable def gamma4 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  latticeTheta ((2 : ℚ) • S) P

/-- The cusp form `χ₁₄` of weight 14 and character `ψ₃` on `Γ₀(3)` (LMFDB
`mf.siegel.family.gamma0_3`, `mf.siegel.family.gamma0_3_psi_3`):
`χ₁₄ = 2⁻⁹ 3⁻¹⁰ (2πi)⁻³ det(kᵢFᵢ, ∂Fᵢ/∂τ, ∂Fᵢ/∂z, ∂Fᵢ/∂ω)` for
`(F₁, F₂, F₃, F₄) = (α₁, β₃, γ₄, δ₃)`, of weights `kᵢ = 1, 3, 4, 3`. The knowls write the first row
as `(α₁, 3β₃, 4γ₄/2, 3δ₄)`, with two typos: the Jacobian of modular forms has the first row
`(kᵢFᵢ)`. With this normalisation the Fourier coefficient of `χ₁₄` at `e^{2πi(2τ + z + 3ω)}` is
`1`. -/
noncomputable def chi14 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  ((2 ^ 9 * 3 ^ 10 : ℂ) * (2 * π * I) ^ 3)⁻¹ •
    jacobianDet ![alpha1, beta3, gamma4, delta3] ![1, 3, 4, 3]

/-- The generators of the knowls `mf.siegel.family.gamma0_3` and `mf.siegel.family.gamma0_3_psi_3`,
as a statement: `α₁, β₃, δ₃` are Siegel modular forms on `Γ₀(3)` of weights 1, 3, 3 and character
`ψ₃`, `γ₄` is a cusp form of weight 4, `χ₁₄` is a cusp form of weight 14 and character `ψ₃`, and
`α₁, β₃, γ₄, δ₃` are algebraically independent. These are theorems of Ibukiyama, which are not
proved here. -/
structure Gamma0ThreeGenerators : Prop where
  alpha1_mem : alpha1 ∈ modularForms (TauCeti.detPowerRep ℂ 2 1) (Ibukiyama.gamma0 3)
    (SymplecticGroup.psi3Rat (Fin 2))
  beta3_mem : beta3 ∈ modularForms (TauCeti.detPowerRep ℂ 2 3) (Ibukiyama.gamma0 3)
    (SymplecticGroup.psi3Rat (Fin 2))
  delta3_mem : delta3 ∈ modularForms (TauCeti.detPowerRep ℂ 2 3) (Ibukiyama.gamma0 3)
    (SymplecticGroup.psi3Rat (Fin 2))
  gamma4_mem : gamma4 ∈ cuspForms (TauCeti.detPowerRep ℂ 2 4) (Ibukiyama.gamma0 3) 1
  chi14_mem : chi14 ∈ cuspForms (TauCeti.detPowerRep ℂ 2 14) (Ibukiyama.gamma0 3)
    (SymplecticGroup.psi3Rat (Fin 2))
  algebraicIndependent : AlgebraicIndependent ℂ ![alpha1, beta3, gamma4, delta3]

/-- **Ibukiyama's theorem on `Γ₀(3)`** (LMFDB `mf.siegel.family.gamma0_3`), as a statement: the
generators are as in `Gamma0ThreeGenerators`, and with `B = ℂ[α₁, β₃, γ₄, δ₃]` and
`C = ℂ[α₁², β₃², γ₄, δ₃²]`, the graded ring of Siegel modular forms on `Γ₀(3)` is
`M_*(Γ₀(3)) = B^even ⊕ Cα₁χ₁₄ ⊕ Cβ₃χ₁₄ ⊕ Cδ₃χ₁₄ ⊕ Cα₁β₃δ₃χ₁₄`, where
`B^even = C ⊕ Cα₁β₃ ⊕ Cα₁δ₃ ⊕ Cβ₃δ₃` is the part of `B` of even weight: `M_*(Γ₀(3))` is the free
`C`-module with basis `1, α₁β₃, α₁δ₃, β₃δ₃, α₁χ₁₄, β₃χ₁₄, δ₃χ₁₄, α₁β₃δ₃χ₁₄`. It is not proved
here. -/
structure Gamma0ThreeStructure : Prop extends Gamma0ThreeGenerators where
  isFreeOverAdjoin : IsFreeOverAdjoin (gradedModularForms (Ibukiyama.gamma0 3))
    ![alpha1 ^ 2, beta3 ^ 2, gamma4, delta3 ^ 2] ![1, alpha1 * beta3, alpha1 * delta3,
      beta3 * delta3, alpha1 * chi14, beta3 * chi14, delta3 * chi14,
      alpha1 * beta3 * delta3 * chi14]

/-- **Ibukiyama's theorem on `Γ₀(3)` with the character `ψ₃`** (LMFDB
`mf.siegel.family.gamma0_3_psi_3`), as a statement: the generators are as in
`Gamma0ThreeGenerators`, and with `B = ℂ[α₁, β₃, γ₄, δ₃]` and `C = ℂ[α₁², β₃², γ₄, δ₃²]`,
`⊕_k M_k(Γ₀(3), ψ₃) = B^odd ⊕ B^even χ₁₄`, where `B^odd = Cα₁ ⊕ Cβ₃ ⊕ Cδ₃ ⊕ Cα₁β₃δ₃` and
`B^even = C ⊕ Cα₁β₃ ⊕ Cα₁δ₃ ⊕ Cβ₃δ₃` are the parts of `B` of odd and even weight: it is the free
`C`-module with basis `α₁, β₃, δ₃, α₁β₃δ₃, χ₁₄, α₁β₃χ₁₄, α₁δ₃χ₁₄, β₃δ₃χ₁₄`. It is not proved
here. -/
structure Gamma0ThreePsi3Structure : Prop extends Gamma0ThreeGenerators where
  isFreeOverAdjoin : IsFreeOverAdjoin
    (gradedModularFormsChar (Ibukiyama.gamma0 3) (SymplecticGroup.psi3Rat (Fin 2)))
    ![alpha1 ^ 2, beta3 ^ 2, gamma4, delta3 ^ 2] ![alpha1, beta3, delta3, alpha1 * beta3 * delta3,
      chi14, alpha1 * beta3 * chi14, alpha1 * delta3 * chi14, beta3 * delta3 * chi14]

end IbukiyamaThree

end SiegelUpperHalfSpace
