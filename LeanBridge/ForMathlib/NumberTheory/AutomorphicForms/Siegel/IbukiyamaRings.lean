import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwo
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ScalarValued
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ThetaConstant
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Rings of Siegel modular forms of degree 2 on `Γ₀(2)` and `Γ₀(4)`

The graded rings of Siegel modular forms of degree 2 on the congruence subgroups `Γ₀(2)` and
`Γ₀(4)` of `Sp(4, ℤ)` were determined by Ibukiyama, Aoki and Hayashida. Their generators are
polynomials in the ten even theta constants `θ_{abcd}` of degree 2 (`thetaConstant`), evaluated at
`Ω` or at `2Ω`, and the rings are free modules over polynomial rings in four algebraically
independent generators. The structure theorems rest on dimension formulas; they are stated here,
not proved.

The formulas of the knowls were checked numerically: `X`, `Y`, `Z`, `K` transform as modular forms
of weights 2, 4, 4, 6 under generators of `Γ₀(2)`, and `X`, `X(2Ω)`, `f₂(2Ω)`, `K(2Ω)`, `Y(2Ω)`,
`f₁₁(2Ω)` as forms of weights 2, 2, 2, 6, 4, 11 under generators of `Γ₀(4)`, while `f₁(2Ω)` has
weight 1 and character `ψ₄`. Four statements of the knowls are wrong as written: the theta formula
for `χ₁₉` (replaced here by the Jacobian of `X`, `Y`, `Z`, `K`), the weight 4 of `f₂(2Ω)` (it is
2), the list of generators of `M_*(Γ₀(4))`, which omits `Y(2Ω)`, and the decomposition of
`⊕ M_{2k}(Γ₀(4), ψ₄)`, whose summand `Y(2Ω) B` has trivial character and whose
`f₃ = (θ₀₀₀₀ θ₀₀₀₁ θ₀₀₁₁)²` is not modular (the swap of the two coordinates, which lies in `Γ₀(4)`,
sends it to `(θ₀₀₀₀ θ₀₀₁₀ θ₀₀₁₁)²`); that decomposition is not formalised.

## Main definitions

* `SymplecticGroup.siegelParabolicDet`: the homomorphism `γ ↦ det D` on the Siegel parabolic
  subgroup.
* `SymplecticGroup.psi4` (LMFDB `mf.siegel.family.gamma0_4_psi_4`): the character
  `ψ₄(γ) = (-4 / det D)` of `Γ₀(4)`, and `SymplecticGroup.psi4Rat` the same on `Γ₀(4) ⊆ Sp(4, ℚ)`.
* `SiegelUpperHalfSpace.directionalDeriv`, `SiegelUpperHalfSpace.jacobianDet`: directional
  derivatives on `ℋ_g` and the Jacobian of four functions on `ℋ₂`.
* `SiegelUpperHalfSpace.gradedModularForms` (LMFDB `mf.siegel.family.gamma0_2`,
  `mf.siegel.family.gamma0_4`): the graded ring `M_*(Γ) = ⊕_k M_k(Γ)`.
* `SiegelUpperHalfSpace.evenWeightModularForms` (LMFDB `mf.siegel.family.gamma0_4_psi_4`): the
  module `⊕_k M_{2k}(Γ, ψ)`.
* `SiegelUpperHalfSpace.IsFreeOverAdjoin`: `M = ⊕ᵢ bᵢ ℂ[F]` with `F` algebraically independent.
* `SiegelUpperHalfSpace.Ibukiyama.X`, `Y`, `Z`, `K`, `chi19`, `chi5`, `f6`, `f11`, `f2`, `f1`: the
  generators of the knowls.
* `SiegelUpperHalfSpace.Ibukiyama.Gamma0TwoStructure` (LMFDB `mf.siegel.family.gamma0_2`) and
  `SiegelUpperHalfSpace.Ibukiyama.Gamma0FourStructure` (LMFDB `mf.siegel.family.gamma0_4`): the
  structure theorems, as statements.

## Main results

* `SymplecticGroup.isUnit_det_toBlocks₂₂`: the block `D` of an element of the Siegel parabolic
  subgroup is invertible.
-/

open Matrix

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R] (γ : siegelParabolic l R)

private lemma eq_fromBlocks_of_mem_siegelParabolic :
    ((γ : symplecticGroup l R) : Matrix (l ⊕ l) (l ⊕ l) R) = fromBlocks
      (γ : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ (γ : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₂ 0
        (γ : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ := by
  rw [← γ.2, fromBlocks_toBlocks]

/-- **The block `D` of `γ = (A, B; 0, D)` in the Siegel parabolic subgroup is invertible**: the
symplectic relation gives `AᵀD = 1`. -/
lemma isUnit_det_toBlocks₂₂ :
    IsUnit ((γ : symplecticGroup l R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂.det := by
  have h : (γ : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R * γ = J l R :=
    mem_iff'.mp (γ : symplecticGroup l R).2
  rw [eq_fromBlocks_of_mem_siegelParabolic, fromBlocks_transpose, J, fromBlocks_multiply,
    fromBlocks_multiply] at h
  exact isUnit_det_of_left_inverse <| by simpa using congrArg toBlocks₁₂ h

/-- The homomorphism `γ ↦ det D` on the Siegel parabolic subgroup `{C = 0}` of `Sp(2g, R)`, for
`γ = (A, B; 0, D)`, with values in the units of `R`: `AᵀD = 1`. -/
noncomputable def siegelParabolicDet : siegelParabolic l R →* Rˣ where
  toFun γ := (isUnit_det_toBlocks₂₂ γ).unit
  map_one' := Units.ext <| by
    rw [IsUnit.unit_spec, Units.val_one, OneMemClass.coe_one, OneMemClass.coe_one, ← fromBlocks_one,
      toBlocks_fromBlocks₂₂, det_one]
  map_mul' γ γ' := Units.ext <| by
    rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, Subgroup.coe_mul,
      Submonoid.coe_mul, eq_fromBlocks_of_mem_siegelParabolic γ,
      eq_fromBlocks_of_mem_siegelParabolic γ', fromBlocks_multiply]
    simp

lemma map_intCast_injective {S : Type*} [CommRing S] [CharZero S] :
    Function.Injective (map (Int.castRingHom S) : symplecticGroup l ℤ →* symplecticGroup l S) :=
  fun _ _ h ↦ Subtype.ext <| Matrix.map_injective Int.cast_injective <| congrArg Subtype.val h

variable (l) in
/-- The character `ψ₄(γ) = (-4 / det D)` of `Γ₀(4)` (LMFDB `mf.siegel.family.gamma0_4_psi_4`): the
nontrivial Dirichlet character `χ₋₄` modulo `4` applied to `det D`, for
`γ = (A, B; C, D) ∈ Γ₀(4)`, where `det D` is odd since `C ≡ 0 (mod 4)`. The knowl names `ψ₄`
without defining it; this is the definition of Hayashida and Ibukiyama, the analogue of the
character `ψ₃(γ) = (-3 / det D)` of `Γ₀(3)` (LMFDB `mf.siegel.family.gamma0_3_psi_3`). -/
noncomputable def psi4 : Gamma0 l 4 →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp <| ZMod.χ₄.toUnitHom.comp <|
    siegelParabolicDet.comp <|
      (map (Int.castRingHom (ZMod 4))).subgroupComap (siegelParabolic l (ZMod 4))

variable (l) in
/-- The character `ψ₄` of `Γ₀(4)`, on its image in `Sp(2g, ℚ)`. -/
noncomputable def psi4Rat : (Gamma0 l 4).map (map (Int.castRingHom ℚ)) →* ℂˣ :=
  (psi4 l).comp ((Gamma0 l 4).equivMapOfInjective _ map_intCast_injective).symm.toMonoidHom

end SymplecticGroup

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] {n : ℕ} (Γ : Subgroup (symplecticGroup (Fin n) ℚ))

/-- The derivative `∂F/∂E` of `F : ℋ_g → ℂ` in the direction of a symmetric matrix `E` at `Ω`: the
complex derivative at `t = 0` of `t ↦ F(Ω + tE)`, through the extension of `F` to the square
matrices whose symmetrisation lies in `ℋ_g`. -/
noncomputable def directionalDeriv (E : Matrix l l ℂ) (F : SiegelUpperHalfSpace l → ℂ)
    (Ω : SiegelUpperHalfSpace l) : ℂ :=
  deriv (fun t : ℂ ↦ extend F (Ω.val + t • E)) 0

/-- The **Jacobian** `det(kᵢFᵢ, ∂Fᵢ/∂τ, ∂Fᵢ/∂z, ∂Fᵢ/∂ω)` of four functions `Fᵢ` on `ℋ₂` of weights
`kᵢ`, where `Ω = (τ, z; z, ω)`. For Siegel modular forms `Fᵢ` of weights `kᵢ` on `Γ`, it is a
Siegel modular form of weight `k₁ + k₂ + k₃ + k₄ + 3` on `Γ`, which is not proved here. -/
noncomputable def jacobianDet (F : Fin 4 → SiegelUpperHalfSpace (Fin 2) → ℂ) (k : Fin 4 → ℕ)
    (Ω : SiegelUpperHalfSpace (Fin 2)) : ℂ :=
  (of fun i ↦ ![k i * F i Ω, directionalDeriv !![1, 0; 0, 0] (F i) Ω,
    directionalDeriv !![0, 1; 1, 0] (F i) Ω, directionalDeriv !![0, 0; 0, 1] (F i) Ω]).det

/-- The **graded ring** `M_*(Γ) = ⊕_{k ≥ 0} M_k(Γ)` of scalar-valued Siegel modular forms of
degree `n` on `Γ` (LMFDB `mf.siegel.family.gamma0_2`, `mf.siegel.family.gamma0_4`), as the sum of
the spaces `M_k(Γ)` in the algebra of functions on `ℋ_n`. The sum is direct, and a subalgebra,
which is not proved here. -/
noncomputable def gradedModularForms : Submodule ℂ (SiegelUpperHalfSpace (Fin n) → ℂ) :=
  ⨆ k : ℕ, scalarModularForms k Γ

/-- The module `⊕_{k ≥ 0} M_{2k}(Γ, ψ)` of scalar-valued Siegel modular forms of even weight and
character `ψ` on `Γ` (LMFDB `mf.siegel.family.gamma0_4_psi_4`), as the sum of the spaces
`M_{2k}(Γ, ψ)` in the functions on `ℋ_n`. -/
noncomputable def evenWeightModularForms (ψ : Γ →* ℂˣ) :
    Submodule ℂ (SiegelUpperHalfSpace (Fin n) → ℂ) :=
  ⨆ k : ℕ, modularForms (TauCeti.detPowerRep ℂ n (2 * k)) Γ ψ

/-- A submodule `M` of the functions on `ℋ_g` is the **free module `⊕ᵢ bᵢ ℂ[F]`** with basis `b`
over the algebra `ℂ[F]` generated by an algebraically independent family `F` of functions: `M` is
the direct sum of the `bᵢ ℂ[F]`. -/
structure IsFreeOverAdjoin {ι κ : Type*} (M : Submodule ℂ (SiegelUpperHalfSpace l → ℂ))
    (F : ι → SiegelUpperHalfSpace l → ℂ) (b : κ → SiegelUpperHalfSpace l → ℂ) : Prop where
  algebraicIndependent : AlgebraicIndependent ℂ F
  iSupIndep : iSupIndep fun i ↦
    (Algebra.adjoin ℂ (Set.range F)).toSubmodule.map (LinearMap.mulLeft ℂ (b i))
  iSup_eq : ⨆ i, (Algebra.adjoin ℂ (Set.range F)).toSubmodule.map (LinearMap.mulLeft ℂ (b i)) = M

namespace Ibukiyama

/-- The degree-2 theta constant `θ_{abcd}` of characteristic `((a, b), (c, d))`. -/
noncomputable abbrev theta (a b c d : ℤ) : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  thetaConstant ![a, b] ![c, d]

/-- The group `Γ₀(N)` of degree 2, as a subgroup of `Sp(4, ℚ)`. -/
abbrev gamma0 (N : ℕ) : Subgroup (symplecticGroup (Fin 2) ℚ) :=
  (SymplecticGroup.Gamma0 (Fin 2) N).map (SymplecticGroup.map (Int.castRingHom ℚ))

/-- The form `X = (θ₀₀₀₀⁴ + θ₀₀₀₁⁴ + θ₀₀₁₀⁴ + θ₀₀₁₁⁴) / 4` of weight 2 on `Γ₀(2)` (LMFDB
`mf.siegel.family.gamma0_2`, `mf.siegel.family.gamma0_4`). -/
noncomputable def X : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  (theta 0 0 0 0 ^ 4 + theta 0 0 0 1 ^ 4 + theta 0 0 1 0 ^ 4 + theta 0 0 1 1 ^ 4) / 4

/-- The form `Y = (θ₀₀₀₀ θ₀₀₀₁ θ₀₀₁₀ θ₀₀₁₁)²` of weight 4 on `Γ₀(2)` (LMFDB
`mf.siegel.family.gamma0_2`, `mf.siegel.family.gamma0_4`). -/
noncomputable def Y : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  (theta 0 0 0 0 * theta 0 0 0 1 * theta 0 0 1 0 * theta 0 0 1 1) ^ 2

/-- The form `Z = (θ₀₁₀₀⁴ - θ₀₁₁₀⁴)² / 16384` of weight 4 on `Γ₀(2)` (LMFDB
`mf.siegel.family.gamma0_2`). -/
noncomputable def Z : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  (theta 0 1 0 0 ^ 4 - theta 0 1 1 0 ^ 4) ^ 2 / 16384

/-- The form `K = (θ₀₁₀₀ θ₀₁₁₀ θ₁₀₀₀ θ₁₀₀₁ θ₁₁₀₀ θ₁₁₁₁)² / 4096` of weight 6 on `Γ₀(2)` (LMFDB
`mf.siegel.family.gamma0_2`, `mf.siegel.family.gamma0_4`). -/
noncomputable def K : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  (theta 0 1 0 0 * theta 0 1 1 0 * theta 1 0 0 0 * theta 1 0 0 1 * theta 1 1 0 0 *
    theta 1 1 1 1) ^ 2 / 4096

/-- The cusp form `χ₁₉` of weight 19 on `Γ₀(2)` (LMFDB `mf.siegel.family.gamma0_2`), taken as the
Jacobian of `X`, `Y`, `Z`, `K`. The knowl gives the formula
`χ₁₉ = θθ'(8YZ - X²T + YT + 1024ZT + 96T² - 8XK) / 32` in theta constants, which is not modular:
the factor `θ' = (θ₁₀₀₀¹² + θ₁₀₀₁¹² + θ₁₁₀₀¹² + θ₁₁₁₁¹²) / 1536` is not an eigenvector of the
translation `Ω ↦ Ω + diag(0, 1)` of `Γ₀(2)`, which exchanges `θ₁₀₀₀¹²` and `θ₁₀₀₁¹²` and negates
`θ₁₁₀₀¹²` and `θ₁₁₁₁¹²`. By the structure theorem, `M₁₉(Γ₀(2)) = ℂ χ₁₉`, and the Jacobian is a
nonzero form of weight `2 + 4 + 4 + 6 + 3 = 19`, so it is `χ₁₉` up to a constant, as in the work of
Aoki and Ibukiyama; the LMFDB's normalisation of `χ₁₉` is not determined here. -/
noncomputable def chi19 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  jacobianDet ![X, Y, Z, K] ![2, 4, 4, 6]

/-- The form `χ₅`, the product of the ten even theta constants of degree 2, of weight 5 (LMFDB
`mf.siegel.family.gamma0_4`). -/
noncomputable def chi5 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  theta 0 0 0 0 * theta 0 0 0 1 * theta 0 0 1 0 * theta 0 0 1 1 * theta 0 1 0 0 * theta 0 1 1 0 *
    theta 1 0 0 0 * theta 1 0 0 1 * theta 1 1 0 0 * theta 1 1 1 1

/-- The form `f₆ = (θ₀₀₀₁⁴ - θ₀₀₁₀⁴)(θ₀₀₀₁⁴ - θ₀₀₁₁⁴)(θ₀₀₁₀⁴ - θ₀₀₁₁⁴)` of weight 6 (LMFDB
`mf.siegel.family.gamma0_4`). -/
noncomputable def f6 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  (theta 0 0 0 1 ^ 4 - theta 0 0 1 0 ^ 4) * (theta 0 0 0 1 ^ 4 - theta 0 0 1 1 ^ 4) *
    (theta 0 0 1 0 ^ 4 - theta 0 0 1 1 ^ 4)

/-- The form `f₁₁ = f₆ χ₅` of weight 11 (LMFDB `mf.siegel.family.gamma0_4`); `f₁₁(2Ω)` is a cusp
form of weight 11 on `Γ₀(4)`. -/
noncomputable def f11 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  f6 * chi5

/-- The form `f₂ = θ₀₀₀₀⁴` (LMFDB `mf.siegel.family.gamma0_4`); `f₂(2Ω)` is a form of weight 2 on
`Γ₀(4)`, not of weight 4 as the knowl states. -/
noncomputable def f2 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  theta 0 0 0 0 ^ 4

/-- The form `f₁ = θ₀₀₀₀²` (LMFDB `mf.siegel.family.gamma0_4_psi_4`); `f₁(2Ω)` is a form of
weight 1 and character `ψ₄` on `Γ₀(4)`. -/
noncomputable def f1 : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  theta 0 0 0 0 ^ 2

/-- **Ibukiyama's theorem on `Γ₀(2)`** (LMFDB `mf.siegel.family.gamma0_2`), as a statement: `X`,
`Y`, `Z`, `K` are modular forms of weights 2, 4, 4, 6 on `Γ₀(2)` and `χ₁₉` is a cusp form of
weight 19, the forms `X`, `Y`, `Z`, `K` are algebraically independent, and the graded ring of
modular forms on `Γ₀(2)` is `M_*(Γ₀(2)) = ℂ[X, Y, Z, K] ⊕ χ₁₉ ℂ[X, Y, Z, K]`. It is a theorem of
Ibukiyama, whose proof rests on dimension formulas, and is not proved here. -/
structure Gamma0TwoStructure : Prop where
  X_mem : X ∈ scalarModularForms 2 (gamma0 2)
  Y_mem : Y ∈ scalarModularForms 4 (gamma0 2)
  Z_mem : Z ∈ scalarModularForms 4 (gamma0 2)
  K_mem : K ∈ scalarModularForms 6 (gamma0 2)
  chi19_mem : chi19 ∈ cuspForms (TauCeti.detPowerRep ℂ 2 19) (gamma0 2) 1
  isFreeOverAdjoin : IsFreeOverAdjoin (gradedModularForms (gamma0 2)) ![X, Y, Z, K] ![1, chi19]

/-- **The theorem of Aoki, Hayashida and Ibukiyama on `Γ₀(4)`** (LMFDB
`mf.siegel.family.gamma0_4`), as a statement: `X`, `X(2Ω)`, `f₂(2Ω)`, `K(2Ω)`, `Y(2Ω)` are modular
forms on `Γ₀(4)` of weights 2, 2, 2, 6, 4 and `f₁₁(2Ω)` is a cusp form of weight 11, the forms `X`,
`X(2Ω)`, `f₂(2Ω)`, `K(2Ω)` are algebraically independent, and with `B = ℂ[X, X(2Ω), f₂(2Ω), K(2Ω)]`,
`M_*(Γ₀(4)) = B ⊕ Y(2Ω) B ⊕ f₁₁(2Ω) B ⊕ f₁₁(2Ω) Y(2Ω) B`. The knowl gives `f₂(2Ω)` the weight 4,
but `f₂ = θ₀₀₀₀⁴` has weight 2, and it leaves `Y(2Ω)` out of its list of generators, although
`Y(2Ω)` is not a polynomial in the listed ones (as their Fourier expansions in weight 4 show). It
is not proved here. -/
structure Gamma0FourStructure : Prop where
  X_mem : X ∈ scalarModularForms 2 (gamma0 4)
  X_comp_double_mem : X ∘ double ∈ scalarModularForms 2 (gamma0 4)
  f2_comp_double_mem : f2 ∘ double ∈ scalarModularForms 2 (gamma0 4)
  K_comp_double_mem : K ∘ double ∈ scalarModularForms 6 (gamma0 4)
  Y_comp_double_mem : Y ∘ double ∈ scalarModularForms 4 (gamma0 4)
  f11_comp_double_mem : f11 ∘ double ∈ cuspForms (TauCeti.detPowerRep ℂ 2 11) (gamma0 4) 1
  isFreeOverAdjoin : IsFreeOverAdjoin (gradedModularForms (gamma0 4))
    ![X, X ∘ double, f2 ∘ double, K ∘ double] ![1, Y ∘ double, f11 ∘ double, (f11 * Y) ∘ double]

end Ibukiyama

end SiegelUpperHalfSpace
