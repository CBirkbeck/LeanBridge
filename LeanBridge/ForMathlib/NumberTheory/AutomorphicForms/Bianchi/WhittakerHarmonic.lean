import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKRecurrence
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HodgeCasimir
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.NewformOfWeight
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The Fourier–Bessel vector of weight `k` is harmonic

For `μ ∈ ℂ`, `μ ≠ 0`, the function `F(x, y) = y W_k(u, 4π|μ|y) ψ(μx)` on `ℋ₃`, where
`ψ(z) = e^{2πi(z + z̄)}`, `u = μ / |μ|` and `W_k(u, t) = ((iu)^{k/2-j} K_{j-k/2}(t))_j` is the
vector `bianchiWhittakerVector` of the weight `k` Fourier–Bessel expansion (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`), satisfies both Casimir equations of
`IsBianchiHarmonic k`: `Ψ` and `Ψ'` act on its lift `Φ_F` to `SL(2, ℂ)` by `(k² - 4) / 8`.

The proof is a computation with the holomorphic Lie derivatives `H₁, E₁, F₁` (`lieDerivOne`), which
are derivations: on the entries of `g ∈ SL(2, ℂ)` they act by right multiplication by `H, E, F`,
and they kill the conjugate entries. The Casimir operator satisfies the Leibniz rule
`Ψ(f₁f₂) = (Ψf₁)f₂ + f₁(Ψf₂) + [f₁, f₂]` (`casimirOneBracket`) and the chain rules for holomorphic
and real functions. Pairing `Φ_F(g)` with `(C(k, i) w₁^{k-i} w₂^i)_i`
(`sum_choose_mul_symPowMatrix`) gives `∑_j C(k, j) (iu)^{⌊k/2⌋-j} Q^j P^{k-j} ρ_j(y) e^θ`, where
`g = (a, b; c, d)`, `Q = c w₁ + d w₂` is holomorphic, `P = d̄ w₁ - c̄ w₂` antiholomorphic,
`y = 1 / (|c|² + |d|²)`, `θ = 2πi(μx + conj(μx))` at `g j = (x, y)` and
`ρ_j(y) = y^{k+1} K_{j-k/2}(4π|μ|y)`. Then `ΨQ^j = j(j + 2)/2 Q^j`, `Ψy = -y/2`, `[y, y] = y²`,
`Ψθ = 0`, `[θ, θ] = -16π²|μ|²y²`, `[Q, y] = -yQ`, `[Q, θ] = 4πiμyP` and `[y, θ] = 0`, so that the
Casimir equation is, coefficient by coefficient, the radial equation
`j(j + 2)/2 ρ_j - y ρ_j'/2 + y² ρ_j''/2 - 8π²|μ|²y² ρ_j - j y ρ_j' + 4π|μ|(k - j) y ρ_{j+1} =
(k² - 4)/8 ρ_j`, a consequence of the recurrences of the `K`-Bessel functions
(`Complex.hasDerivAt_besselK_eq_add`, `Complex.hasDerivAt_besselK_eq_sub`). Complex conjugation of
`SL(2, ℂ)` exchanges `Ψ` and `Ψ'` and turns the pairings into those of the frequency `μ̄`, which
gives the second equation.

That `y W_k ψ(μx)` is, up to a scalar, the only harmonic function `ψ(μx) φ(y)` with `φ` of class
`C²` and of moderate growth is proved for `k ≥ 1` in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerUnique`, from the radial
equations of `LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerRadial`, which
reuse the functions `Q`, `P`, `y`, `θ` on `SL(2, ℂ)` of this file with their Lie derivatives,
Casimir values and brackets (namespace `HyperbolicThreeSpace.WhittakerCasimir`). Every Bianchi cusp
form of weight `k ≥ 1` has a Fourier–Bessel expansion:
`IsBianchiCuspidal.hasBianchiWhittakerExpansion`.

## Main definitions

* `HyperbolicThreeSpace.bianchiWhittakerFunction` (LMFDB `mf.bianchi.spaces`): the function
  `y W_k(u, 4π|μ|y) ψ(μx)`.
* `HyperbolicThreeSpace.casimirOneBracket`: the bilinear form of the Leibniz rule of `Ψ`.
* `HyperbolicThreeSpace.sl2Basis`: the basis `H, E, F` of `𝔰𝔩₂(ℂ)`.
* `HyperbolicThreeSpace.WhittakerCasimir.ent`, `HyperbolicThreeSpace.WhittakerCasimir.cent`: the
  entries of `g ∈ SL(2, ℂ)` and their conjugates.
* `HyperbolicThreeSpace.WhittakerCasimir.fQ`, `HyperbolicThreeSpace.WhittakerCasimir.fP`,
  `HyperbolicThreeSpace.WhittakerCasimir.fN`, `HyperbolicThreeSpace.WhittakerCasimir.fU`,
  `HyperbolicThreeSpace.WhittakerCasimir.fUb`, `HyperbolicThreeSpace.WhittakerCasimir.fV`,
  `HyperbolicThreeSpace.WhittakerCasimir.fY`, `HyperbolicThreeSpace.WhittakerCasimir.fYr`,
  `HyperbolicThreeSpace.WhittakerCasimir.fΘ`: the functions `Q`, `P`, `N`, `U`, `Ū`, `V`, `y`
  (complex and real) and `θ` on `SL(2, ℂ)`.
* `HyperbolicThreeSpace.WhittakerCasimir.conjSL`: complex conjugation of `SL(2, ℂ)`.

## Main results

* `HyperbolicThreeSpace.sum_choose_mul_symPowMatrix`: the transpose of `Sym^k`.
* `HyperbolicThreeSpace.casimirOne_bianchiLift_bianchiWhittakerFunction`: the first Casimir
  equation.
* `HyperbolicThreeSpace.casimirTwo_bianchiLift_bianchiWhittakerFunction`: the second Casimir
  equation.
* `HyperbolicThreeSpace.isBianchiHarmonic_bianchiWhittakerFunction`: the Fourier–Bessel vector of
  weight `k` is harmonic.
* `HyperbolicThreeSpace.isBianchiHarmonic_bianchiWhittakerTerm`: the terms of the Fourier–Bessel
  expansion of weight `k` (`HasBianchiWhittakerExpansion`) are harmonic.
-/

open Complex Matrix NumberField

open scoped ComplexConjugate MatrixGroups Real

namespace HyperbolicThreeSpace

variable (b b' : Fin 3) (w : ℂ) {f f₁ f₂ : SL(2, ℂ) → ℂ}

/-- The basis `H, E, F` of `𝔰𝔩₂(ℂ)` of the one-parameter subgroups `sl2Exp`. -/
def sl2Basis : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, -1], !![0, 1; 0, 0], !![0, 0; 1, 0]]

lemma IsLieSmooth.mul (h₁ : IsLieSmooth f₁) (h₂ : IsLieSmooth f₂) : IsLieSmooth (f₁ * f₂) :=
  fun g b₁ w₁ b₂ w₂ ↦ (h₁ g b₁ w₁ b₂ w₂).mul (h₂ g b₁ w₁ b₂ w₂)

variable (f₁ f₂) in
/-- The bilinear form `(f₁, f₂) ↦ H₁f₁ H₁f₂ + 2 E₁f₁ F₁f₂ + 2 F₁f₁ E₁f₂` of the Leibniz rule
`Ψ(f₁ f₂) = (Ψ f₁) f₂ + f₁ (Ψ f₂) + [f₁, f₂]` of the Casimir operator `Ψ = casimirOne`. -/
noncomputable def casimirOneBracket : SL(2, ℂ) → ℂ :=
  lieDerivOne 0 f₁ * lieDerivOne 0 f₂ + 2 * (lieDerivOne 1 f₁ * lieDerivOne 2 f₂) +
    2 * (lieDerivOne 2 f₁ * lieDerivOne 1 f₂)

lemma casimirOne_mul (h₁ : IsLieSmooth f₁) (h₂ : IsLieSmooth f₂) : casimirOne (f₁ * f₂) =
    casimirOne f₁ * f₂ + f₁ * casimirOne f₂ + casimirOneBracket f₁ f₂ := by
  simp only [casimirOne, casimirOneBracket, lieDerivOne_lieDerivOne_mul _ _ h₁ h₂]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.ofNat_apply]
  ring1

variable {φ φ' φ'' : ℂ → ℂ}

lemma lieDerivOne_comp (hφ : ∀ g, HasDerivAt φ (φ' (f g)) (f g)) (hf : IsLieDifferentiable f) :
    lieDerivOne b (φ ∘ f) = (φ' ∘ f) * lieDerivOne b f := by
  funext g
  have h (v : ℂ) : HasDerivAt (fun t : ℝ ↦ φ (f (g * sl2Exp b (t * v))))
      (φ' (f g) * deriv (fun t : ℝ ↦ f (g * sl2Exp b (t * v))) 0) 0 := by
    have h₀ : f (g * sl2Exp b ((0 : ℝ) * v)) = f g := by
      rw [ofReal_zero, zero_mul, sl2Exp_zero, mul_one]
    have h₁ : HasDerivAt (φ ∘ fun t : ℝ ↦ f (g * sl2Exp b (t * v)))
        (φ' (f (g * sl2Exp b ((0 : ℝ) * v))) * deriv (fun t : ℝ ↦ f (g * sl2Exp b (t * v))) 0) 0 :=
      (hφ (g * sl2Exp b ((0 : ℝ) * v))).comp (0 : ℝ) (hf g b v).hasDerivAt
    rw [h₀] at h₁
    exact h₁
  simp only [lieDerivOne, lieDeriv, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul,
    Function.comp_apply, (h 1).deriv, (h I).deriv]
  ring1

lemma IsLieDifferentiable.comp (hφ : ∀ g, HasDerivAt φ (φ' (f g)) (f g))
    (hf : IsLieDifferentiable f) : IsLieDifferentiable (φ ∘ f) :=
  fun g b v ↦
    ((hφ (g * sl2Exp b ((0 : ℝ) * v))).comp (0 : ℝ) (hf g b v).hasDerivAt).differentiableAt

lemma casimirOne_comp (hφ : ∀ g, HasDerivAt φ (φ' (f g)) (f g))
    (hφ' : ∀ g, HasDerivAt φ' (φ'' (f g)) (f g)) (hf : IsLieSmooth f) :
    casimirOne (φ ∘ f) =
      (φ' ∘ f) * casimirOne f + (2⁻¹ : ℂ) • ((φ'' ∘ f) * casimirOneBracket f f) := by
  have hd : IsLieDifferentiable (φ' ∘ f) := hf.isLieDifferentiable.comp hφ'
  have h (b b' : Fin 3) : lieDerivOne b (lieDerivOne b' (φ ∘ f)) = (φ'' ∘ f) * lieDerivOne b f *
      lieDerivOne b' f + (φ' ∘ f) * lieDerivOne b (lieDerivOne b' f) := by
    rw [lieDerivOne_comp b' hφ hf.isLieDifferentiable,
      lieDerivOne_mul b hd (hf.isLieDifferentiable_lieDerivOne b'),
      lieDerivOne_comp b hφ' hf.isLieDifferentiable]
  simp only [casimirOne, casimirOneBracket, h]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.ofNat_apply]
  ring1

lemma casimirOneBracket_comp (hφ : ∀ g, HasDerivAt φ (φ' (f g)) (f g))
    (hf : IsLieDifferentiable f) (f' : SL(2, ℂ) → ℂ) :
    casimirOneBracket (φ ∘ f) f' = (φ' ∘ f) * casimirOneBracket f f' := by
  simp only [casimirOneBracket, lieDerivOne_comp _ hφ hf]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  ring1

variable {ρ ρ' ρ'' : ℝ → ℂ} {r : SL(2, ℂ) → ℝ}

lemma hasDerivAt_comp_real (hρ : ∀ g, HasDerivAt ρ (ρ' (r g)) (r g))
    (hr : IsLieDifferentiable fun g ↦ (r g : ℂ)) (g : SL(2, ℂ)) (v : ℂ) :
    HasDerivAt (fun t : ℝ ↦ ρ (r (g * sl2Exp b (t * v))))
      (ρ' (r g) * lieDeriv b v (fun g ↦ (r g : ℂ)) g) 0 := by
  have h₀ : r (g * sl2Exp b ((0 : ℝ) * v)) = r g := by
    rw [ofReal_zero, zero_mul, sl2Exp_zero, mul_one]
  have hc : HasDerivAt (fun t : ℝ ↦ ((r (g * sl2Exp b (t * v)) : ℝ) : ℂ))
      (lieDeriv b v (fun g ↦ (r g : ℂ)) g) 0 :=
    (hr g b v).hasDerivAt
  have hre : HasDerivAt (fun t : ℝ ↦ r (g * sl2Exp b (t * v)))
      (lieDeriv b v (fun g ↦ (r g : ℂ)) g).re 0 := by
    have h : HasDerivAt (reCLM ∘ fun t : ℝ ↦ ((r (g * sl2Exp b (t * v)) : ℝ) : ℂ))
        (lieDeriv b v (fun g ↦ (r g : ℂ)) g).re 0 :=
      reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    have e : (reCLM ∘ fun t : ℝ ↦ ((r (g * sl2Exp b (t * v)) : ℝ) : ℂ)) =
        fun t : ℝ ↦ r (g * sl2Exp b (t * v)) := by
      funext t
      simp
    rwa [e] at h
  have he : ((lieDeriv b v (fun g ↦ (r g : ℂ)) g).re : ℂ) = lieDeriv b v (fun g ↦ (r g : ℂ)) g :=
    hre.ofReal_comp.unique hc
  have h₁ : HasDerivAt (ρ ∘ fun t : ℝ ↦ r (g * sl2Exp b (t * v)))
      ((lieDeriv b v (fun g ↦ (r g : ℂ)) g).re • ρ' (r (g * sl2Exp b ((0 : ℝ) * v)))) 0 :=
    (hρ (g * sl2Exp b ((0 : ℝ) * v))).scomp (0 : ℝ) hre
  rw [h₀, real_smul, he, mul_comm] at h₁
  exact h₁

lemma lieDerivOne_comp_real (hρ : ∀ g, HasDerivAt ρ (ρ' (r g)) (r g))
    (hr : IsLieDifferentiable fun g ↦ (r g : ℂ)) :
    lieDerivOne b (ρ ∘ r) = (ρ' ∘ r) * lieDerivOne b fun g ↦ (r g : ℂ) := by
  funext g
  simp only [lieDerivOne, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  rw [lieDeriv, lieDeriv]
  simp only [Function.comp_apply, (hasDerivAt_comp_real b hρ hr g 1).deriv,
    (hasDerivAt_comp_real b hρ hr g I).deriv]
  ring1

lemma IsLieDifferentiable.comp_real (hρ : ∀ g, HasDerivAt ρ (ρ' (r g)) (r g))
    (hr : IsLieDifferentiable fun g ↦ (r g : ℂ)) : IsLieDifferentiable (ρ ∘ r) :=
  fun g b v ↦ (hasDerivAt_comp_real b hρ hr g v).differentiableAt

lemma casimirOne_comp_real (hρ : ∀ g, HasDerivAt ρ (ρ' (r g)) (r g))
    (hρ' : ∀ g, HasDerivAt ρ' (ρ'' (r g)) (r g)) (hr : IsLieSmooth fun g ↦ (r g : ℂ)) :
    casimirOne (ρ ∘ r) = (ρ' ∘ r) * casimirOne (fun g ↦ (r g : ℂ)) +
      (2⁻¹ : ℂ) • ((ρ'' ∘ r) * casimirOneBracket (fun g ↦ (r g : ℂ)) fun g ↦ (r g : ℂ)) := by
  have hd : IsLieDifferentiable (ρ' ∘ r) := hr.isLieDifferentiable.comp_real hρ'
  have h (b b' : Fin 3) : lieDerivOne b (lieDerivOne b' (ρ ∘ r)) =
      (ρ'' ∘ r) * lieDerivOne b (fun g ↦ (r g : ℂ)) * lieDerivOne b' (fun g ↦ (r g : ℂ)) +
        (ρ' ∘ r) * lieDerivOne b (lieDerivOne b' fun g ↦ (r g : ℂ)) := by
    rw [lieDerivOne_comp_real b' hρ hr.isLieDifferentiable,
      lieDerivOne_mul b hd (hr.isLieDifferentiable_lieDerivOne b'),
      lieDerivOne_comp_real b hρ' hr.isLieDifferentiable]
  simp only [casimirOne, casimirOneBracket, h]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.ofNat_apply]
  ring1

lemma casimirOneBracket_comp_real (hρ : ∀ g, HasDerivAt ρ (ρ' (r g)) (r g))
    (hr : IsLieDifferentiable fun g ↦ (r g : ℂ)) (f' : SL(2, ℂ) → ℂ) :
    casimirOneBracket (ρ ∘ r) f' = (ρ' ∘ r) * casimirOneBracket (fun g ↦ (r g : ℂ)) f' := by
  simp only [casimirOneBracket, lieDerivOne_comp_real _ hρ hr]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  ring1

variable (f₁ f₂) in
lemma casimirOneBracket_comm : casimirOneBracket f₁ f₂ = casimirOneBracket f₂ f₁ := by
  funext g
  simp only [casimirOneBracket, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  ring1

lemma lieDerivOne_zero : lieDerivOne b (0 : SL(2, ℂ) → ℂ) = 0 := by
  have h (w : ℂ) : lieDeriv b w (0 : SL(2, ℂ) → ℂ) = 0 :=
    funext fun _ ↦ deriv_const 0 0
  simp [lieDerivOne, h]

lemma casimirOne_of_lieDerivOne_eq_zero (h : ∀ b, lieDerivOne b f = 0) : casimirOne f = 0 := by
  simp [casimirOne, h, lieDerivOne_zero]

lemma casimirOneBracket_of_lieDerivOne_eq_zero (h : ∀ b, lieDerivOne b f₂ = 0) :
    casimirOneBracket f₁ f₂ = 0 := by
  simp [casimirOneBracket, h]

lemma casimirOne_mul_of_lieDerivOne_eq_zero (h₁ : IsLieSmooth f₁) (h₂ : IsLieSmooth f₂)
    (h : ∀ b, lieDerivOne b f₂ = 0) : casimirOne (f₁ * f₂) = casimirOne f₁ * f₂ := by
  rw [casimirOne_mul h₁ h₂, casimirOne_of_lieDerivOne_eq_zero h,
    casimirOneBracket_of_lieDerivOne_eq_zero h, mul_zero, add_zero, add_zero]

section

variable (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)

lemma hasDerivAt_sl2Exp_apply :
    HasDerivAt (fun t : ℝ ↦ (sl2Exp b (t * w) : Matrix (Fin 2) (Fin 2) ℂ) i j)
      (w * sl2Basis b i j) 0 := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;> simp [sl2Exp, sl2Basis] <;>
    first
    | exact hasDerivAt_const _ _
    | simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w
    | simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).cexp
    | simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).neg.cexp

lemma hasDerivAt_mul_apply (g : SL(2, ℂ)) : HasDerivAt
    (fun t : ℝ ↦ (((g * sl2Exp b (t * w) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * M) i j)
    (w * ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b * M) i j) 0 := by
  have h (l m : Fin 2) : HasDerivAt
      (fun t : ℝ ↦ g i l * (sl2Exp b (t * w) : Matrix (Fin 2) (Fin 2) ℂ) l m * M m j)
      (g i l * (w * sl2Basis b l m) * M m j) 0 :=
    ((hasDerivAt_sl2Exp_apply b w l m).const_mul (g i l)).mul_const (M m j)
  have e : (fun t : ℝ ↦ (((g * sl2Exp b (t * w) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * M) i j) =
      fun t : ℝ ↦ g i 0 * (sl2Exp b (t * w) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * M 0 j +
        g i 0 * (sl2Exp b (t * w) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * M 1 j +
        (g i 1 * (sl2Exp b (t * w) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * M 0 j +
          g i 1 * (sl2Exp b (t * w) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * M 1 j) := by
    funext t
    simp only [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
    ring1
  rw [e]
  refine (((h 0 0).add (h 0 1)).add ((h 1 0).add (h 1 1))).congr_deriv ?_
  simp only [mul_apply, Fin.sum_univ_two]
  ring1

lemma lieDerivOne_mul_apply :
    lieDerivOne b (fun g : SL(2, ℂ) ↦ ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) i j) =
      fun g : SL(2, ℂ) ↦ ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b * M) i j := by
  funext g
  simp only [lieDerivOne, lieDeriv, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    (hasDerivAt_mul_apply b 1 M i j g).deriv, (hasDerivAt_mul_apply b I M i j g).deriv]
  linear_combination (-(2⁻¹ * ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b * M) i j)) * I_sq

lemma lieDerivOne_conj_mul_apply :
    lieDerivOne b (fun g : SL(2, ℂ) ↦ conj (((g : Matrix (Fin 2) (Fin 2) ℂ) * M) i j)) = 0 := by
  funext g
  have h (v : ℂ) : HasDerivAt
      (fun t : ℝ ↦ conj ((((g * sl2Exp b (t * v) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * M) i j))
      (conj (v * ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b * M) i j)) 0 :=
    (hasDerivAt_mul_apply b v M i j g).star
  simp only [lieDerivOne, lieDeriv, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, (h 1).deriv,
    (h I).deriv, Pi.zero_apply, map_mul, conj_I, map_one]
  linear_combination (2⁻¹ * conj (((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b * M) i j)) * I_sq

namespace WhittakerCasimir

/-- The entry `g i j` of `g ∈ SL(2, ℂ)`. -/
def ent : SL(2, ℂ) → ℂ :=
  fun g ↦ (g : Matrix (Fin 2) (Fin 2) ℂ) i j

/-- The conjugate `conj (g i j)` of the entry `g i j` of `g ∈ SL(2, ℂ)`. -/
noncomputable def cent : SL(2, ℂ) → ℂ :=
  fun g ↦ conj ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)

lemma isLieSmooth_ent : IsLieSmooth (ent i j) :=
  isLieSmooth_of_contDiff fun _ hγ ↦ hγ i j

lemma isLieSmooth_cent : IsLieSmooth (cent i j) :=
  isLieSmooth_of_contDiff fun _ hγ ↦ contDiff_conj.comp (hγ i j)

lemma lieDerivOne_ent : lieDerivOne b (ent i j) =
    fun g : SL(2, ℂ) ↦ ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) i j := by
  have h : lieDerivOne b (fun g : SL(2, ℂ) ↦
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j) =
        fun g : SL(2, ℂ) ↦
          ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b * (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j :=
    lieDerivOne_mul_apply b 1 i j
  simp only [Matrix.mul_one] at h
  exact h

lemma lieDerivOne_cent : lieDerivOne b (cent i j) = 0 := by
  have h : lieDerivOne b (fun g : SL(2, ℂ) ↦
      conj (((g : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j)) = 0 :=
    lieDerivOne_conj_mul_apply b 1 i j
  simp only [Matrix.mul_one] at h
  exact h

lemma casimirOne_ent : casimirOne (ent i j) = (3 / 2 : ℂ) • ent i j := by
  have h (b b' : Fin 3) : lieDerivOne b (lieDerivOne b' (ent i j)) =
      fun g : SL(2, ℂ) ↦ ((g : Matrix (Fin 2) (Fin 2) ℂ) * (sl2Basis b * sl2Basis b')) i j := by
    rw [lieDerivOne_ent]
    simpa [Matrix.mul_assoc] using lieDerivOne_mul_apply b (sl2Basis b') i j
  simp only [casimirOne, h]
  funext g
  fin_cases i <;> fin_cases j <;>
    simp [ent, sl2Basis, Matrix.mul_apply] <;> ring1

lemma casimirOne_cent : casimirOne (cent i j) = 0 := by
  simp [casimirOne, lieDerivOne_cent, lieDerivOne_zero]

lemma lieDerivOne_ent_mul_cent (m n : Fin 2) : lieDerivOne b (ent i j * cent m n) =
    fun g : SL(2, ℂ) ↦ ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) i j * cent m n g := by
  rw [lieDerivOne_mul b (isLieSmooth_ent i j).isLieDifferentiable
    (isLieSmooth_cent m n).isLieDifferentiable, lieDerivOne_ent, lieDerivOne_cent, mul_zero,
    add_zero]
  rfl

lemma casimirOne_ent_mul_cent (m n : Fin 2) :
    casimirOne (ent i j * cent m n) = (3 / 2 : ℂ) • (ent i j * cent m n) := by
  rw [casimirOne_mul_of_lieDerivOne_eq_zero (isLieSmooth_ent i j) (isLieSmooth_cent m n)
    fun b ↦ lieDerivOne_cent b m n, casimirOne_ent, smul_mul_assoc]

end WhittakerCasimir

end

open WhittakerCasimir

variable (w₁ w₂ μ : ℂ) {f₃ : SL(2, ℂ) → ℂ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {Φ : SL(2, ℂ) → V}

lemma casimirOneBracket_add_right (h₂ : IsLieDifferentiable f₂) (h₃ : IsLieDifferentiable f₃) :
    casimirOneBracket f₁ (f₂ + f₃) = casimirOneBracket f₁ f₂ + casimirOneBracket f₁ f₃ := by
  simp only [casimirOneBracket, lieDerivOne_add _ h₂ h₃]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  ring1

lemma casimirOneBracket_smul_right (c : ℂ) (h₂ : IsLieDifferentiable f₂) :
    casimirOneBracket f₁ (c • f₂) = c • casimirOneBracket f₁ f₂ := by
  simp only [casimirOneBracket, lieDerivOne_smul _ c h₂]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.ofNat_apply]
  ring1

lemma casimirOneBracket_mul_right (h₂ : IsLieDifferentiable f₂) (h₃ : IsLieDifferentiable f₃) :
    casimirOneBracket f₁ (f₂ * f₃) =
      f₂ * casimirOneBracket f₁ f₃ + f₃ * casimirOneBracket f₁ f₂ := by
  simp only [casimirOneBracket, lieDerivOne_mul _ h₂ h₃]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  ring1

lemma casimirOneBracket_mul_left (h₁ : IsLieDifferentiable f₁) (h₂ : IsLieDifferentiable f₂) :
    casimirOneBracket (f₁ * f₂) f₃ =
      f₁ * casimirOneBracket f₂ f₃ + f₂ * casimirOneBracket f₁ f₃ := by
  rw [casimirOneBracket_comm, casimirOneBracket_mul_right h₁ h₂, casimirOneBracket_comm f₃,
    casimirOneBracket_comm f₃]

lemma casimirOneBracket_smul_left (c : ℂ) (h₁ : IsLieDifferentiable f₁) :
    casimirOneBracket (c • f₁) f₂ = c • casimirOneBracket f₁ f₂ := by
  rw [casimirOneBracket_comm, casimirOneBracket_smul_right c h₁, casimirOneBracket_comm]

lemma IsLieSmooth.comp_contDiff (hφ : ContDiff ℝ 2 φ) (hf : IsLieSmooth f) : IsLieSmooth (φ ∘ f) :=
  fun g b₁ w₁ b₂ w₂ ↦ hφ.comp (hf g b₁ w₁ b₂ w₂)

namespace WhittakerCasimir

/-- `Q(g) = c w₁ + d w₂` for `g = (a, b; c, d)`. -/
noncomputable def fQ : SL(2, ℂ) → ℂ :=
  w₁ • ent 1 0 + w₂ • ent 1 1

/-- `P(g) = d̄ w₁ - c̄ w₂` for `g = (a, b; c, d)`. -/
noncomputable def fP : SL(2, ℂ) → ℂ :=
  w₁ • cent 1 1 - w₂ • cent 1 0

/-- `N(g) = |c|² + |d|²` for `g = (a, b; c, d)`. -/
noncomputable def fN : SL(2, ℂ) → ℂ :=
  ent 1 0 * cent 1 0 + ent 1 1 * cent 1 1

/-- `U(g) = a c̄ + b d̄` for `g = (a, b; c, d)`. -/
noncomputable def fU : SL(2, ℂ) → ℂ :=
  ent 0 0 * cent 1 0 + ent 0 1 * cent 1 1

/-- `Ū(g) = ā c + b̄ d` for `g = (a, b; c, d)`. -/
noncomputable def fUb : SL(2, ℂ) → ℂ :=
  cent 0 0 * ent 1 0 + cent 0 1 * ent 1 1

lemma isLieSmooth_fQ : IsLieSmooth (fQ w₁ w₂) :=
  ((isLieSmooth_ent 1 0).const_smul w₁).add ((isLieSmooth_ent 1 1).const_smul w₂)

lemma isLieSmooth_fP : IsLieSmooth (fP w₁ w₂) := by
  rw [fP, sub_eq_add_neg, ← neg_smul]
  exact ((isLieSmooth_cent 1 1).const_smul w₁).add ((isLieSmooth_cent 1 0).const_smul (-w₂))

lemma isLieSmooth_fN : IsLieSmooth fN :=
  ((isLieSmooth_ent 1 0).mul (isLieSmooth_cent 1 0)).add
    ((isLieSmooth_ent 1 1).mul (isLieSmooth_cent 1 1))

lemma isLieSmooth_fU : IsLieSmooth fU :=
  ((isLieSmooth_ent 0 0).mul (isLieSmooth_cent 1 0)).add
    ((isLieSmooth_ent 0 1).mul (isLieSmooth_cent 1 1))

lemma isLieSmooth_fUb : IsLieSmooth fUb :=
  ((isLieSmooth_cent 0 0).mul (isLieSmooth_ent 1 0)).add
    ((isLieSmooth_cent 0 1).mul (isLieSmooth_ent 1 1))

lemma lieDerivOne_fQ : lieDerivOne b (fQ w₁ w₂) = fun g : SL(2, ℂ) ↦
    w₁ * ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) 1 0 +
      w₂ * ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) 1 1 := by
  rw [fQ, lieDerivOne_add b ((isLieSmooth_ent 1 0).const_smul w₁).isLieDifferentiable
    ((isLieSmooth_ent 1 1).const_smul w₂).isLieDifferentiable,
    lieDerivOne_smul b w₁ (isLieSmooth_ent 1 0).isLieDifferentiable,
    lieDerivOne_smul b w₂ (isLieSmooth_ent 1 1).isLieDifferentiable, lieDerivOne_ent,
    lieDerivOne_ent]
  rfl

lemma lieDerivOne_fP : lieDerivOne b (fP w₁ w₂) = 0 := by
  rw [fP, sub_eq_add_neg, ← neg_smul,
    lieDerivOne_add b ((isLieSmooth_cent 1 1).const_smul w₁).isLieDifferentiable
      ((isLieSmooth_cent 1 0).const_smul (-w₂)).isLieDifferentiable,
    lieDerivOne_smul b w₁ (isLieSmooth_cent 1 1).isLieDifferentiable,
    lieDerivOne_smul b (-w₂) (isLieSmooth_cent 1 0).isLieDifferentiable, lieDerivOne_cent,
    lieDerivOne_cent, smul_zero, smul_zero, add_zero]

lemma lieDerivOne_fN : lieDerivOne b fN = fun g : SL(2, ℂ) ↦
    ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) 1 0 * cent 1 0 g +
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) 1 1 * cent 1 1 g := by
  rw [fN, lieDerivOne_add b
    ((isLieSmooth_ent 1 0).mul (isLieSmooth_cent 1 0)).isLieDifferentiable
    ((isLieSmooth_ent 1 1).mul (isLieSmooth_cent 1 1)).isLieDifferentiable,
    lieDerivOne_ent_mul_cent, lieDerivOne_ent_mul_cent]
  rfl

lemma lieDerivOne_fU : lieDerivOne b fU = fun g : SL(2, ℂ) ↦
    ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) 0 0 * cent 1 0 g +
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) 0 1 * cent 1 1 g := by
  rw [fU, lieDerivOne_add b
    ((isLieSmooth_ent 0 0).mul (isLieSmooth_cent 1 0)).isLieDifferentiable
    ((isLieSmooth_ent 0 1).mul (isLieSmooth_cent 1 1)).isLieDifferentiable,
    lieDerivOne_ent_mul_cent, lieDerivOne_ent_mul_cent]
  rfl

lemma lieDerivOne_fUb : lieDerivOne b fUb = fun g : SL(2, ℂ) ↦
    cent 0 0 g * ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) 1 0 +
      cent 0 1 g * ((g : Matrix (Fin 2) (Fin 2) ℂ) * sl2Basis b) 1 1 := by
  rw [fUb, mul_comm (cent 0 0), mul_comm (cent 0 1), lieDerivOne_add b
    ((isLieSmooth_ent 1 0).mul (isLieSmooth_cent 0 0)).isLieDifferentiable
    ((isLieSmooth_ent 1 1).mul (isLieSmooth_cent 0 1)).isLieDifferentiable,
    lieDerivOne_ent_mul_cent, lieDerivOne_ent_mul_cent]
  funext g
  simp only [Pi.add_apply]
  ring1

lemma casimirOne_fQ : casimirOne (fQ w₁ w₂) = (3 / 2 : ℂ) • fQ w₁ w₂ := by
  rw [fQ, casimirOne_add ((isLieSmooth_ent 1 0).const_smul w₁)
    ((isLieSmooth_ent 1 1).const_smul w₂), casimirOne_smul w₁ (isLieSmooth_ent 1 0),
    casimirOne_smul w₂ (isLieSmooth_ent 1 1), casimirOne_ent, casimirOne_ent, smul_add,
    smul_comm w₁, smul_comm w₂]

lemma casimirOne_fN : casimirOne fN = (3 / 2 : ℂ) • fN := by
  rw [fN, casimirOne_add ((isLieSmooth_ent 1 0).mul (isLieSmooth_cent 1 0))
    ((isLieSmooth_ent 1 1).mul (isLieSmooth_cent 1 1)), casimirOne_ent_mul_cent,
    casimirOne_ent_mul_cent, smul_add]

lemma casimirOne_fU : casimirOne fU = (3 / 2 : ℂ) • fU := by
  rw [fU, casimirOne_add ((isLieSmooth_ent 0 0).mul (isLieSmooth_cent 1 0))
    ((isLieSmooth_ent 0 1).mul (isLieSmooth_cent 1 1)), casimirOne_ent_mul_cent,
    casimirOne_ent_mul_cent, smul_add]

lemma casimirOne_fUb : casimirOne fUb = (3 / 2 : ℂ) • fUb := by
  rw [fUb, mul_comm (cent 0 0), mul_comm (cent 0 1),
    casimirOne_add ((isLieSmooth_ent 1 0).mul (isLieSmooth_cent 0 0))
    ((isLieSmooth_ent 1 1).mul (isLieSmooth_cent 0 1)), casimirOne_ent_mul_cent,
    casimirOne_ent_mul_cent, smul_add]

lemma casimirOneBracket_fQ_fQ :
    casimirOneBracket (fQ w₁ w₂) (fQ w₁ w₂) = fQ w₁ w₂ * fQ w₁ w₂ := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fQ, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  simp [fQ, ent, sl2Basis, Matrix.mul_apply]
  ring1

lemma casimirOneBracket_fN_fN : casimirOneBracket fN fN = fN * fN := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fN, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  simp [fN, ent, sl2Basis, Matrix.mul_apply]
  ring1

lemma casimirOneBracket_fQ_fN : casimirOneBracket (fQ w₁ w₂) fN = fQ w₁ w₂ * fN := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fQ, lieDerivOne_fN, Pi.add_apply, Pi.mul_apply,
    Pi.ofNat_apply]
  simp [fQ, fN, ent, sl2Basis, Matrix.mul_apply]
  ring1

lemma casimirOneBracket_fN_fU : casimirOneBracket fN fU = fN * fU := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fN, lieDerivOne_fU, Pi.add_apply, Pi.mul_apply,
    Pi.ofNat_apply]
  simp [fN, fU, ent, sl2Basis, Matrix.mul_apply]
  ring1

lemma casimirOneBracket_fN_fUb : casimirOneBracket fN fUb = fN * fUb := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fN, lieDerivOne_fUb, Pi.add_apply, Pi.mul_apply,
    Pi.ofNat_apply]
  simp [fN, fUb, ent, sl2Basis, Matrix.mul_apply]
  ring1

lemma det_cent (g : SL(2, ℂ)) : cent 0 0 g * cent 1 1 g - cent 0 1 g * cent 1 0 g = 1 := by
  simp only [cent, ← map_mul, ← map_sub]
  rw [g.fin_two_mul_sub_mul_eq_one, map_one]

lemma casimirOneBracket_fQ_fU :
    casimirOneBracket (fQ w₁ w₂) fU = fQ w₁ w₂ * fU + 2 * fP w₁ w₂ := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fQ, lieDerivOne_fU, Pi.add_apply, Pi.mul_apply,
    Pi.ofNat_apply]
  simp [fQ, fU, fP, ent, sl2Basis, Matrix.mul_apply]
  linear_combination (2 * (w₁ * cent 1 1 g - w₂ * cent 1 0 g)) * g.fin_two_mul_sub_mul_eq_one

lemma casimirOneBracket_fQ_fUb : casimirOneBracket (fQ w₁ w₂) fUb = fQ w₁ w₂ * fUb := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fQ, lieDerivOne_fUb, Pi.add_apply, Pi.mul_apply,
    Pi.ofNat_apply]
  simp [fQ, fUb, ent, sl2Basis, Matrix.mul_apply]
  ring1

lemma casimirOneBracket_fU_fU : casimirOneBracket fU fU = fU * fU := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fU, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  simp [fU, ent, sl2Basis, Matrix.mul_apply]
  ring1

lemma casimirOneBracket_fUb_fUb : casimirOneBracket fUb fUb = fUb * fUb := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fUb, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  simp [fUb, ent, sl2Basis, Matrix.mul_apply]
  ring1

lemma casimirOneBracket_fU_fUb : casimirOneBracket fU fUb = fU * fUb + 2 := by
  funext g
  simp only [casimirOneBracket, lieDerivOne_fU, lieDerivOne_fUb, Pi.add_apply, Pi.mul_apply,
    Pi.ofNat_apply]
  simp [fU, fUb, ent, sl2Basis, Matrix.mul_apply]
  linear_combination (2 * (cent 0 0 g * cent 1 1 g - cent 0 1 g * cent 1 0 g)) *
    g.fin_two_mul_sub_mul_eq_one + 2 * det_cent g

/-- `V(g) = μ U(g) + μ̄ Ū(g)`, so that `2πi(μ x + conj(μ x)) = 2πi y V` at `g j = (x, y)`. -/
noncomputable def fV : SL(2, ℂ) → ℂ :=
  μ • fU + conj μ • fUb

lemma isLieSmooth_fV : IsLieSmooth (fV μ) :=
  (isLieSmooth_fU.const_smul μ).add (isLieSmooth_fUb.const_smul (conj μ))

lemma casimirOne_fV : casimirOne (fV μ) = (3 / 2 : ℂ) • fV μ := by
  rw [fV, casimirOne_add (isLieSmooth_fU.const_smul μ) (isLieSmooth_fUb.const_smul (conj μ)),
    casimirOne_smul μ isLieSmooth_fU, casimirOne_smul (conj μ) isLieSmooth_fUb, casimirOne_fU,
    casimirOne_fUb, smul_add, smul_comm μ, smul_comm (conj μ)]

lemma casimirOneBracket_fV (h₁ : casimirOneBracket f₁ fU = f₁ * fU + f₂)
    (h₂ : casimirOneBracket f₁ fUb = f₁ * fUb + f₃) :
    casimirOneBracket f₁ (fV μ) = f₁ * fV μ + (μ • f₂ + conj μ • f₃) := by
  rw [fV, casimirOneBracket_add_right (isLieSmooth_fU.const_smul μ).isLieDifferentiable
    (isLieSmooth_fUb.const_smul (conj μ)).isLieDifferentiable,
    casimirOneBracket_smul_right μ isLieSmooth_fU.isLieDifferentiable,
    casimirOneBracket_smul_right (conj μ) isLieSmooth_fUb.isLieDifferentiable, h₁, h₂]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring1

lemma casimirOneBracket_fN_fV : casimirOneBracket fN (fV μ) = fN * fV μ := by
  rw [casimirOneBracket_fV μ (f₂ := 0) (f₃ := 0) (by rw [add_zero, casimirOneBracket_fN_fU])
    (by rw [add_zero, casimirOneBracket_fN_fUb]), smul_zero, smul_zero, add_zero, add_zero]

lemma casimirOneBracket_fQ_fV :
    casimirOneBracket (fQ w₁ w₂) (fV μ) = fQ w₁ w₂ * fV μ + (2 * μ) • fP w₁ w₂ := by
  rw [casimirOneBracket_fV μ (f₂ := 2 * fP w₁ w₂) (f₃ := 0) (casimirOneBracket_fQ_fU w₁ w₂)
    (by rw [add_zero, casimirOneBracket_fQ_fUb]), smul_zero, add_zero, mul_smul]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.ofNat_apply]
  ring1

lemma casimirOneBracket_fV_fV :
    casimirOneBracket (fV μ) (fV μ) = fV μ * fV μ + (4 * normSq μ : ℂ) • 1 := by
  have h₁ : casimirOneBracket (fV μ) fU = fV μ * fU + conj μ • 2 := by
    rw [casimirOneBracket_comm, casimirOneBracket_fV μ (f₂ := 0) (f₃ := 2)
      (by rw [add_zero, casimirOneBracket_fU_fU]) (by rw [casimirOneBracket_fU_fUb])]
    funext g
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring1
  have h₂ : casimirOneBracket (fV μ) fUb = fV μ * fUb + μ • 2 := by
    rw [casimirOneBracket_comm, casimirOneBracket_fV μ (f₂ := 2) (f₃ := 0)
      (by rw [casimirOneBracket_comm, casimirOneBracket_fU_fUb, mul_comm])
      (by rw [add_zero, casimirOneBracket_fUb_fUb])]
    funext g
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring1
  rw [casimirOneBracket_fV μ h₁ h₂]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.ofNat_apply, ← mul_conj]
  ring1

lemma fN_apply (g : SL(2, ℂ)) :
    fN g = ((normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
      normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℝ) : ℂ) := by
  simp [fN, ent, cent, mul_conj]

lemma normSq_bottom_pos (g : SL(2, ℂ)) : 0 < normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
    normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  simpa [moebiusDenom, add_comm] using moebiusDenom_pos g (p := (0, 1)) one_pos

lemma fN_ne_zero (g : SL(2, ℂ)) : fN g ≠ 0 := by
  rw [fN_apply]
  exact ofReal_ne_zero.mpr (normSq_bottom_pos g).ne'

/-- `y(g) = 1 / (|c|² + |d|²)` for `g = (a, b; c, d)`, the height of `g j`. -/
noncomputable def fY : SL(2, ℂ) → ℂ :=
  fun g ↦ (fN g)⁻¹

lemma isLieSmooth_fY : IsLieSmooth fY :=
  isLieSmooth_of_contDiff fun γ hγ ↦ by
    have h₁₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := hγ 1 0
    have h₁₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := hγ 1 1
    have hN (st : ℝ × ℝ) : fN (γ st) ≠ 0 := fN_ne_zero (γ st)
    simp only [Function.comp_def, fY, fN, ent, cent, Pi.add_apply, Pi.mul_apply] at hN ⊢
    exact ContDiff.inv (by fun_prop) hN

lemma hasDerivAt_inv_fN (g : SL(2, ℂ)) :
    HasDerivAt Inv.inv ((fun z : ℂ ↦ -(z ^ 2)⁻¹) (fN g)) (fN g) :=
  hasDerivAt_inv (fN_ne_zero g)

lemma hasDerivAt_neg_inv_sq_fN (g : SL(2, ℂ)) :
    HasDerivAt (fun z : ℂ ↦ -(z ^ 2)⁻¹) ((fun z : ℂ ↦ 2 * (z ^ 3)⁻¹) (fN g)) (fN g) := by
  have h : fN g ≠ 0 := fN_ne_zero g
  refine (((hasDerivAt_pow 2 (fN g)).inv (pow_ne_zero 2 h)).neg).congr_deriv ?_
  field_simp
  ring1

lemma fY_eq : fY = Inv.inv ∘ fN :=
  rfl

variable (f₂) in
lemma casimirOneBracket_fY (g : SL(2, ℂ)) :
    casimirOneBracket fY f₂ g = -(fN g ^ 2)⁻¹ * casimirOneBracket fN f₂ g := by
  rw [fY_eq, casimirOneBracket_comp (φ' := fun z : ℂ ↦ -(z ^ 2)⁻¹) hasDerivAt_inv_fN
    isLieSmooth_fN.isLieDifferentiable]
  rfl

lemma casimirOne_fY : casimirOne fY = (-(1 / 2) : ℂ) • fY := by
  rw [fY_eq, casimirOne_comp (φ' := fun z : ℂ ↦ -(z ^ 2)⁻¹) (φ'' := fun z : ℂ ↦ 2 * (z ^ 3)⁻¹)
    hasDerivAt_inv_fN hasDerivAt_neg_inv_sq_fN isLieSmooth_fN, casimirOne_fN,
    casimirOneBracket_fN_fN]
  funext g
  have h : fN g ≠ 0 := fN_ne_zero g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  field_simp
  ring1

lemma casimirOneBracket_fY_fY (g : SL(2, ℂ)) : casimirOneBracket fY fY g = fY g ^ 2 := by
  have h : fN g ≠ 0 := fN_ne_zero g
  rw [casimirOneBracket_fY, casimirOneBracket_comm, casimirOneBracket_fY, casimirOneBracket_fN_fN]
  simp only [Pi.mul_apply, fY]
  field_simp

lemma casimirOneBracket_fY_fV (g : SL(2, ℂ)) :
    casimirOneBracket fY (fV μ) g = -(fY g * fV μ g) := by
  have h : fN g ≠ 0 := fN_ne_zero g
  rw [casimirOneBracket_fY, casimirOneBracket_fN_fV]
  simp only [Pi.mul_apply, fY]
  field_simp

lemma casimirOneBracket_fY_fQ (g : SL(2, ℂ)) :
    casimirOneBracket fY (fQ w₁ w₂) g = -(fY g * fQ w₁ w₂ g) := by
  have h : fN g ≠ 0 := fN_ne_zero g
  rw [casimirOneBracket_fY, casimirOneBracket_comm, casimirOneBracket_fQ_fN]
  simp only [Pi.mul_apply, fY]
  field_simp

/-- `θ(g) = 2πi y V`, the phase `2πi(μ x + conj(μ x))` of the character at `g j = (x, y)`. -/
noncomputable def fΘ : SL(2, ℂ) → ℂ :=
  (2 * π * I : ℂ) • (fY * fV μ)

lemma isLieSmooth_fΘ : IsLieSmooth (fΘ μ) :=
  (isLieSmooth_fY.mul (isLieSmooth_fV μ)).const_smul _

lemma casimirOne_fΘ : casimirOne (fΘ μ) = 0 := by
  rw [fΘ, casimirOne_smul _ (isLieSmooth_fY.mul (isLieSmooth_fV μ)),
    casimirOne_mul isLieSmooth_fY (isLieSmooth_fV μ), casimirOne_fY, casimirOne_fV]
  funext g
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, casimirOneBracket_fY_fV,
    Pi.zero_apply]
  ring1

variable (f₂) in
lemma casimirOneBracket_fY_mul_fV (g : SL(2, ℂ)) :
    casimirOneBracket (fY * fV μ) f₂ g =
      fY g * casimirOneBracket (fV μ) f₂ g + fV μ g * casimirOneBracket fY f₂ g := by
  rw [casimirOneBracket_mul_left isLieSmooth_fY.isLieDifferentiable
    (isLieSmooth_fV μ).isLieDifferentiable]
  rfl

lemma casimirOneBracket_fΘ_fΘ (g : SL(2, ℂ)) :
    casimirOneBracket (fΘ μ) (fΘ μ) g = -(16 * π ^ 2 * normSq μ) * fY g ^ 2 := by
  have hd : IsLieDifferentiable (fY * fV μ) :=
    (isLieSmooth_fY.mul (isLieSmooth_fV μ)).isLieDifferentiable
  rw [fΘ, casimirOneBracket_smul_left _ hd, casimirOneBracket_smul_right _ hd]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [casimirOneBracket_fY_mul_fV, casimirOneBracket_comm (fV μ) (fY * fV μ),
    casimirOneBracket_fY_mul_fV, casimirOneBracket_comm fY (fY * fV μ), casimirOneBracket_fY_mul_fV,
    casimirOneBracket_fV_fV, casimirOneBracket_comm (fV μ) fY, casimirOneBracket_fY_fV,
    casimirOneBracket_fY_fY]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
  linear_combination (16 * (π : ℂ) ^ 2 * normSq μ * fY g ^ 2) * I_sq

variable (f₂) in
lemma casimirOneBracket_fΘ (g : SL(2, ℂ)) :
    casimirOneBracket (fΘ μ) f₂ g = 2 * π * I * (fY g * casimirOneBracket (fV μ) f₂ g +
      fV μ g * casimirOneBracket fY f₂ g) := by
  rw [fΘ, casimirOneBracket_smul_left _ (isLieSmooth_fY.mul (isLieSmooth_fV μ)).isLieDifferentiable,
    Pi.smul_apply, casimirOneBracket_fY_mul_fV, smul_eq_mul]

lemma casimirOneBracket_fY_fΘ (g : SL(2, ℂ)) : casimirOneBracket fY (fΘ μ) g = 0 := by
  rw [casimirOneBracket_comm, casimirOneBracket_fΘ, casimirOneBracket_comm (fV μ),
    casimirOneBracket_fY_fV, casimirOneBracket_fY_fY]
  ring1

lemma casimirOneBracket_fQ_fΘ (g : SL(2, ℂ)) :
    casimirOneBracket (fQ w₁ w₂) (fΘ μ) g = 4 * π * I * μ * fY g * fP w₁ w₂ g := by
  rw [casimirOneBracket_comm, casimirOneBracket_fΘ, casimirOneBracket_comm (fV μ),
    casimirOneBracket_fQ_fV, casimirOneBracket_fY_fQ]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring1

/-- The height `y(g) = 1 / (|c|² + |d|²)` of `g j`, `g = (a, b; c, d)`, as a real number. -/
noncomputable def fYr (g : SL(2, ℂ)) : ℝ :=
  (normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) + normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1))⁻¹

lemma fYr_pos (g : SL(2, ℂ)) : 0 < fYr g :=
  inv_pos.mpr (normSq_bottom_pos g)

lemma ofReal_fYr : (fun g ↦ (fYr g : ℂ)) = fY := by
  funext g
  rw [fY, fN_apply, fYr, ofReal_inv]

lemma contDiff_fYr_comp {γ : ℝ × ℝ → SL(2, ℂ)}
    (hγ : ∀ i j, ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) i j) :
    ContDiff ℝ 2 fun st ↦ fYr (γ st) := by
  have h₁₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := hγ 1 0
  have h₁₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := hγ 1 1
  have hN (st : ℝ × ℝ) : normSq ((γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
      normSq ((γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ≠ 0 :=
    (inv_pos.mp (fYr_pos (γ st))).ne'
  simp only [fYr]
  exact ContDiff.inv (by fun_prop) hN

lemma isLieSmooth_comp_fYr (hρ : ContDiffOn ℝ 2 ρ (Set.Ioi 0)) : IsLieSmooth (ρ ∘ fYr) :=
  isLieSmooth_of_contDiff fun γ hγ ↦ hρ.comp_contDiff (contDiff_fYr_comp hγ) fun st ↦ fYr_pos (γ st)

lemma casimirOne_fQ_pow (j : ℕ) (g : SL(2, ℂ)) :
    casimirOne ((fun z ↦ z ^ j) ∘ fQ w₁ w₂) g = (j * (j + 2) / 2 : ℂ) * fQ w₁ w₂ g ^ j := by
  rw [casimirOne_comp (φ' := fun z ↦ (j : ℂ) * z ^ (j - 1))
    (φ'' := fun z ↦ (j : ℂ) * (((j - 1 : ℕ) : ℂ) * z ^ (j - 1 - 1)))
    (fun g ↦ hasDerivAt_pow j _) (fun g ↦ (hasDerivAt_pow (j - 1) _).const_mul _)
    (isLieSmooth_fQ w₁ w₂), casimirOne_fQ, casimirOneBracket_fQ_fQ]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  rcases j with _ | _ | m
  · simp
  · simp only [zero_add, Nat.sub_self, pow_zero, Nat.cast_zero, pow_one]
    ring1
  · simp only [Nat.add_sub_cancel, Nat.cast_add]
    ring1

variable (f₂) in
lemma casimirOneBracket_fQ_pow (j : ℕ) (g : SL(2, ℂ)) :
    casimirOneBracket ((fun z ↦ z ^ j) ∘ fQ w₁ w₂) f₂ g =
      j * fQ w₁ w₂ g ^ (j - 1) * casimirOneBracket (fQ w₁ w₂) f₂ g := by
  rw [casimirOneBracket_comp (φ' := fun z ↦ (j : ℂ) * z ^ (j - 1)) (fun g ↦ hasDerivAt_pow j _)
    (isLieSmooth_fQ w₁ w₂).isLieDifferentiable]
  rfl

lemma lieDerivOne_fP_pow (m : ℕ) : lieDerivOne b ((fun z ↦ z ^ m) ∘ fP w₁ w₂) = 0 := by
  rw [lieDerivOne_comp (φ' := fun z ↦ (m : ℂ) * z ^ (m - 1)) b (fun g ↦ hasDerivAt_pow m _)
    (isLieSmooth_fP w₁ w₂).isLieDifferentiable, lieDerivOne_fP, mul_zero]

lemma casimirOne_exp_fΘ (g : SL(2, ℂ)) : casimirOne (cexp ∘ fΘ μ) g =
    -(8 * π ^ 2 * normSq μ) * fY g ^ 2 * cexp (fΘ μ g) := by
  rw [casimirOne_comp (φ' := cexp) (φ'' := cexp) (fun g ↦ hasDerivAt_exp _)
    (fun g ↦ hasDerivAt_exp _) (isLieSmooth_fΘ μ), casimirOne_fΘ]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    Pi.zero_apply, casimirOneBracket_fΘ_fΘ]
  ring1

variable (f₂) in
lemma casimirOneBracket_exp_fΘ (g : SL(2, ℂ)) :
    casimirOneBracket (cexp ∘ fΘ μ) f₂ g = cexp (fΘ μ g) * casimirOneBracket (fΘ μ) f₂ g := by
  rw [casimirOneBracket_comp (φ' := cexp) (fun g ↦ hasDerivAt_exp _)
    (isLieSmooth_fΘ μ).isLieDifferentiable]
  rfl

lemma isLieSmooth_pow_comp (m : ℕ) (hf : IsLieSmooth f) : IsLieSmooth ((fun z : ℂ ↦ z ^ m) ∘ f) :=
  hf.comp_contDiff (contDiff_id.pow m)

lemma hasDerivAt_ofReal_pow {s : ℝ} (n : ℕ) :
    HasDerivAt (fun s : ℝ ↦ (s : ℂ) ^ (n + 1)) (((n + 1 : ℕ) : ℂ) * (s : ℂ) ^ n) s := by
  have h : HasDerivAt (fun s : ℝ ↦ (s : ℂ) ^ (n + 1))
      (((n + 1 : ℕ) : ℂ) * (s : ℂ) ^ (n + 1 - 1)) s :=
    (hasDerivAt_pow (n + 1) (s : ℂ)).comp_ofReal
  rwa [Nat.add_sub_cancel] at h

lemma sum_range_succ_eq_of_shift (k : ℕ) (X Y : ℕ → ℂ) (h : ∀ i < k, X i = Y (i + 1))
    (hk : X k = 0) (h₀ : Y 0 = 0) :
    ∑ j ∈ Finset.range (k + 1), X j = ∑ j ∈ Finset.range (k + 1), Y j := by
  rw [Finset.sum_range_succ, hk, add_zero, Finset.sum_range_succ', h₀, add_zero]
  exact Finset.sum_congr rfl fun i hi ↦ h i (Finset.mem_range.mp hi)

lemma moebius_fst (g : SL(2, ℂ)) : (moebius g (0, 1)).1 = fU g * fY g := by
  simp [moebius, moebiusDenom, fU, fY, fN, ent, cent, div_eq_mul_inv, add_comm]
  exact Or.inl (by rw [mul_conj, mul_conj])

lemma moebius_snd (g : SL(2, ℂ)) : (moebius g (0, 1)).2 = fYr g := by
  simp [moebius, moebiusDenom, fYr, add_comm]

lemma contDiff_fΘ_comp {γ : ℝ × ℝ → SL(2, ℂ)}
    (hγ : ∀ i j, ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) i j) :
    ContDiff ℝ 2 fun st ↦ fΘ μ (γ st) := by
  have h₀₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := hγ 0 0
  have h₀₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := hγ 0 1
  have h₁₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := hγ 1 0
  have h₁₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := hγ 1 1
  have hN (st : ℝ × ℝ) : fN (γ st) ≠ 0 := fN_ne_zero (γ st)
  simp only [fΘ, fY, fV, fN, fU, fUb, ent, cent, Pi.smul_apply, Pi.mul_apply, Pi.add_apply] at hN ⊢
  exact contDiff_const.mul ((ContDiff.inv (by fun_prop) hN).mul (by fun_prop))

/-- Complex conjugation `g ↦ ḡ` of `SL(2, ℂ)`, which exchanges the two Casimir operators. -/
noncomputable def conjSL : SL(2, ℂ) →* SL(2, ℂ) :=
  SpecialLinearGroup.map (starRingEnd ℂ)

lemma conjSL_apply (g : SL(2, ℂ)) (i j : Fin 2) :
    (conjSL g : Matrix (Fin 2) (Fin 2) ℂ) i j = conj ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  rfl

lemma conjSL_conjSL (g : SL(2, ℂ)) : conjSL (conjSL g) = g := by
  ext i j
  simp [conjSL_apply]

lemma conjSL_sl2Exp (x : ℂ) : conjSL (sl2Exp b x) = sl2Exp b (conj x) := by
  ext i j
  rw [conjSL_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;> simp [sl2Exp, ← exp_conj]

lemma lieDeriv_comp_conjSL (g : SL(2, ℂ)) :
    lieDeriv b w (Φ ∘ conjSL) g = lieDeriv b (conj w) Φ (conjSL g) := by
  simp only [lieDeriv, Function.comp_apply, map_mul, conjSL_sl2Exp, conj_ofReal]

lemma lieDeriv_neg (g : SL(2, ℂ)) : lieDeriv b (-w) Φ g = -lieDeriv b w Φ g := by
  have h : (fun t : ℝ ↦ Φ (g * sl2Exp b (t * -w))) =
      fun t : ℝ ↦ Φ (g * sl2Exp b ((-t : ℝ) * w)) := by
    funext t
    simp only [ofReal_neg, neg_mul, mul_neg]
  rw [lieDeriv, h, deriv_comp_neg (f := fun t : ℝ ↦ Φ (g * sl2Exp b (t * w))), neg_zero]
  rfl

lemma lieDerivOne_comp_conjSL : lieDerivOne b (Φ ∘ conjSL) = lieDerivTwo b Φ ∘ conjSL := by
  funext g
  simp only [lieDerivOne, lieDerivTwo, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
    Function.comp_apply, lieDeriv_comp_conjSL, map_one, conj_I, lieDeriv_neg, smul_neg,
    sub_neg_eq_add]

lemma casimirOne_comp_conjSL : casimirOne (Φ ∘ conjSL) = casimirTwo Φ ∘ conjSL := by
  simp only [casimirOne, casimirTwo, lieDerivOne_comp_conjSL]
  rfl

end WhittakerCasimir

lemma IsLieSmooth.comp_conjSL (hf : IsLieSmooth Φ) : IsLieSmooth (Φ ∘ conjSL) := by
  intro g b₁ w₁ b₂ w₂
  simpa only [Function.comp_def, map_mul, conjSL_sl2Exp, conj_ofReal] using
    hf (conjSL g) b₁ (conj w₁) b₂ (conj w₂)

variable (k : ℕ) (ν : ℂ) {α s : ℝ}

variable (α s) in
/-- The radial factor `s^{k+1} K_ν(α s)` of the Fourier–Bessel vector. -/
private noncomputable def radial : ℂ :=
  (s : ℂ) ^ (k + 1) * besselK ν (α * s)

variable (α s) in
/-- The derivative of `radial`. -/
private noncomputable def radial' : ℂ :=
  (s : ℂ)⁻¹ * ((k + 1 + ν) * (s : ℂ) ^ (k + 1) * besselK ν (α * s) -
    α * (s : ℂ) ^ (k + 2) * besselK (ν + 1) (α * s))

variable (α s) in
/-- The second derivative of `radial`. -/
private noncomputable def radial'' : ℂ :=
  -((s : ℂ) ^ 2)⁻¹ * ((k + 1 + ν) * (s : ℂ) ^ (k + 1) * besselK ν (α * s) -
    α * (s : ℂ) ^ (k + 2) * besselK (ν + 1) (α * s)) +
  (s : ℂ)⁻¹ * ((k + 1 + ν) * (((k + 1 : ℕ) : ℂ) * (s : ℂ) ^ k * besselK ν (α * s) +
    (s : ℂ) ^ (k + 1) * (α * (-besselK (ν + 1) (α * s) + ν / (α * s : ℝ) * besselK ν (α * s)))) -
    α * (((k + 2 : ℕ) : ℂ) * (s : ℂ) ^ (k + 1) * besselK (ν + 1) (α * s) +
      (s : ℂ) ^ (k + 2) * (α * (-besselK (ν + 1 - 1) (α * s) -
        (ν + 1) / (α * s : ℝ) * besselK (ν + 1) (α * s)))))

private lemma hasDerivAt_besselK_comp (μ' : ℂ) (hα : 0 < α) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ ↦ besselK μ' (α * s))
      (α * (-besselK (μ' + 1) (α * s) + μ' / (α * s : ℝ) * besselK μ' (α * s))) s := by
  have h : HasDerivAt ((fun x ↦ besselK μ' x) ∘ fun s ↦ α * s)
      ((α * 1) • (-besselK (μ' + 1) (α * s) + μ' / (α * s : ℝ) * besselK μ' (α * s))) s :=
    (hasDerivAt_besselK_eq_add μ' (mul_pos hα hs)).scomp s ((hasDerivAt_id s).const_mul α)
  rw [mul_one, real_smul] at h
  exact h

private lemma hasDerivAt_besselK_comp' (μ' : ℂ) (hα : 0 < α) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ ↦ besselK μ' (α * s))
      (α * (-besselK (μ' - 1) (α * s) - μ' / (α * s : ℝ) * besselK μ' (α * s))) s := by
  have h : HasDerivAt ((fun x ↦ besselK μ' x) ∘ fun s ↦ α * s)
      ((α * 1) • (-besselK (μ' - 1) (α * s) - μ' / (α * s : ℝ) * besselK μ' (α * s))) s :=
    (hasDerivAt_besselK_eq_sub μ' (mul_pos hα hs)).scomp s ((hasDerivAt_id s).const_mul α)
  rw [mul_one, real_smul] at h
  exact h

private lemma hasDerivAt_radial (hα : 0 < α) (hs : 0 < s) :
    HasDerivAt (radial k ν α) (radial' k ν α s) s := by
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
  refine ((hasDerivAt_ofReal_pow k).mul (hasDerivAt_besselK_comp ν hα hs)).congr_deriv ?_
  simp only [radial', ofReal_mul]
  push_cast
  field_simp
  ring1

private lemma hasDerivAt_radial' (hα : 0 < α) (hs : 0 < s) :
    HasDerivAt (radial' k ν α) (radial'' k ν α s) s := by
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  convert ((hasDerivAt_id s).ofReal_comp.inv hs').mul
    ((((hasDerivAt_ofReal_pow k).mul (hasDerivAt_besselK_comp ν hα hs)).const_mul
      (k + 1 + ν)).sub
      (((hasDerivAt_ofReal_pow (k + 1)).mul (hasDerivAt_besselK_comp' (ν + 1) hα hs)).const_mul
        (α : ℂ))) using 1
  · funext x
    simp only [radial', Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, id]
    ring1
  · simp only [radial'', Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, id]
    push_cast
    ring1

private lemma radial_equation (j : ℕ) (hα : 0 < α) (hs : 0 < s) :
    (j * (j + 2) / 2 : ℂ) * radial k ((j : ℂ) - k / 2) α s -
      (2⁻¹ : ℂ) * s * radial' k ((j : ℂ) - k / 2) α s +
      (2⁻¹ : ℂ) * (s : ℂ) ^ 2 * radial'' k ((j : ℂ) - k / 2) α s -
      (2⁻¹ : ℂ) * (α : ℂ) ^ 2 * (s : ℂ) ^ 2 * radial k ((j : ℂ) - k / 2) α s -
      j * s * radial' k ((j : ℂ) - k / 2) α s +
      ((k : ℂ) - j) * α * s * radial k ((j : ℂ) - k / 2 + 1) α s =
    ((k : ℂ) ^ 2 - 4) / 8 * radial k ((j : ℂ) - k / 2) α s := by
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
  simp only [radial, radial', radial'', add_sub_cancel_right]
  push_cast
  field_simp
  ring1

private lemma contDiffOn_radial (hα : 0 < α) : ContDiffOn ℝ 2 (radial k ν α) (Set.Ioi 0) := by
  have hK : ContDiffOn ℝ 2 (fun s : ℝ ↦ besselK ν (α * s)) (Set.Ioi 0) :=
    ((contDiffOn_besselK ν).of_le (by norm_cast)).comp (by fun_prop)
      fun s hs ↦ mul_pos hα hs
  exact (contDiff_ofReal.pow (k + 1)).contDiffOn.mul hK

private lemma casimirOne_radial (hα : 0 < α) (g : SL(2, ℂ)) :
    casimirOne (radial k ν α ∘ fYr) g = radial' k ν α (fYr g) * (-(1 / 2) * fY g) +
      2⁻¹ * (radial'' k ν α (fYr g) * fY g ^ 2) := by
  have h : IsLieSmooth fun g ↦ (fYr g : ℂ) := by
    rw [ofReal_fYr]
    exact isLieSmooth_fY
  rw [casimirOne_comp_real (fun g ↦ hasDerivAt_radial k ν hα (fYr_pos g))
    (fun g ↦ hasDerivAt_radial' k ν hα (fYr_pos g)) h, ofReal_fYr, casimirOne_fY]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    casimirOneBracket_fY_fY]

variable (f₂) in
private lemma casimirOneBracket_radial (hα : 0 < α) (g : SL(2, ℂ)) :
    casimirOneBracket (radial k ν α ∘ fYr) f₂ g =
      radial' k ν α (fYr g) * casimirOneBracket fY f₂ g := by
  have h : IsLieDifferentiable fun g ↦ (fYr g : ℂ) := by
    rw [ofReal_fYr]
    exact isLieSmooth_fY.isLieDifferentiable
  rw [casimirOneBracket_comp_real (fun g ↦ hasDerivAt_radial k ν hα (fYr_pos g)) h, ofReal_fYr]
  rfl

variable (α) in
/-- The `j`-th term `Q^j y^{k+1} K_{j - k/2}(α y) e^θ P^{k-j}` of the generating function. -/
private noncomputable def whittakerTerm (j : ℕ) : SL(2, ℂ) → ℂ :=
  (fun z ↦ z ^ j) ∘ fQ w₁ w₂ * ((radial k ((j : ℂ) - k / 2) α ∘ fYr) * (cexp ∘ fΘ μ)) *
    ((fun z ↦ z ^ (k - j)) ∘ fP w₁ w₂)

private lemma isLieSmooth_whittakerTerm (hα : 0 < α) (j : ℕ) :
    IsLieSmooth (whittakerTerm w₁ w₂ μ k α j) :=
  ((isLieSmooth_pow_comp j (isLieSmooth_fQ w₁ w₂)).mul
    ((isLieSmooth_comp_fYr (contDiffOn_radial k _ hα)).mul
      ((isLieSmooth_fΘ μ).comp_contDiff contDiff_exp))).mul
    (isLieSmooth_pow_comp (k - j) (isLieSmooth_fP w₁ w₂))

private lemma casimirOne_whittakerTerm (hα : 0 < α) (j : ℕ) (g : SL(2, ℂ)) :
    casimirOne (whittakerTerm w₁ w₂ μ k α j) g = fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) *
      (fQ w₁ w₂ g ^ j * ((j * (j + 2) / 2 : ℂ) * radial k ((j : ℂ) - k / 2) α (fYr g) -
        (2⁻¹ : ℂ) * fY g * radial' k ((j : ℂ) - k / 2) α (fYr g) +
        (2⁻¹ : ℂ) * fY g ^ 2 * radial'' k ((j : ℂ) - k / 2) α (fYr g) -
        8 * π ^ 2 * normSq μ * fY g ^ 2 * radial k ((j : ℂ) - k / 2) α (fYr g) -
        j * fY g * radial' k ((j : ℂ) - k / 2) α (fYr g)) +
      j * fQ w₁ w₂ g ^ (j - 1) * (4 * π * I * μ * fY g * fP w₁ w₂ g) *
        radial k ((j : ℂ) - k / 2) α (fYr g)) := by
  have hQ : IsLieSmooth ((fun z ↦ z ^ j) ∘ fQ w₁ w₂) :=
    isLieSmooth_pow_comp j (isLieSmooth_fQ w₁ w₂)
  have hR : IsLieSmooth (radial k ((j : ℂ) - k / 2) α ∘ fYr) :=
    isLieSmooth_comp_fYr (contDiffOn_radial k ((j : ℂ) - k / 2) hα)
  have hE : IsLieSmooth (cexp ∘ fΘ μ) :=
    (isLieSmooth_fΘ μ).comp_contDiff contDiff_exp
  rw [whittakerTerm, casimirOne_mul_of_lieDerivOne_eq_zero (hQ.mul (hR.mul hE))
    (isLieSmooth_pow_comp (k - j) (isLieSmooth_fP w₁ w₂)) fun b ↦ lieDerivOne_fP_pow b _ _ _,
    casimirOne_mul hQ (hR.mul hE), casimirOne_mul hR hE,
    casimirOneBracket_mul_right hR.isLieDifferentiable hE.isLieDifferentiable]
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  rw [casimirOne_fQ_pow, casimirOne_radial k _ hα, casimirOne_exp_fΘ,
    casimirOneBracket_radial _ k _ hα, casimirOneBracket_comm fY, casimirOneBracket_exp_fΘ,
    casimirOneBracket_comm (fΘ μ), casimirOneBracket_fY_fΘ, casimirOneBracket_fQ_pow,
    casimirOneBracket_fQ_pow, casimirOneBracket_comm (fQ w₁ w₂), casimirOneBracket_exp_fΘ,
    casimirOneBracket_comm (fΘ μ), casimirOneBracket_fQ_fΘ, casimirOneBracket_comm (fQ w₁ w₂),
    casimirOneBracket_radial _ k _ hα, casimirOneBracket_fY_fQ]
  rcases j with _ | j
  · simp
    ring1
  · simp only [Nat.add_sub_cancel, Nat.cast_add, pow_succ]
    ring1

lemma isLieSmooth_sum {ι : Type*} (t : Finset ι) {F : ι → SL(2, ℂ) → ℂ}
    (hF : ∀ i, IsLieSmooth (F i)) : IsLieSmooth (∑ i ∈ t, F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact fun _ _ _ _ _ ↦ by simpa using contDiff_const
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a).add ih

lemma casimirOne_sum {ι : Type*} (t : Finset ι) {F : ι → SL(2, ℂ) → ℂ}
    (hF : ∀ i, IsLieSmooth (F i)) : casimirOne (∑ i ∈ t, F i) = ∑ i ∈ t, casimirOne (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact casimirOne_of_lieDerivOne_eq_zero fun b ↦ by simpa using lieDerivOne_zero b
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, casimirOne_add (hF a) (isLieSmooth_sum t hF),
      ih]

/-- The coefficient `C(k, j) (iu)^{⌊k/2⌋ - j}`, `u = μ / |μ|`, of the `j`-th coordinate. -/
private noncomputable def whittakerCoeff (j : ℕ) : ℂ :=
  (k.choose j : ℂ) * (I * (μ / ‖μ‖)) ^ (((k / 2 : ℕ) : ℤ) - j)

private lemma whittakerCoeff_succ (hμ : μ ≠ 0) (i : ℕ) (hi : i < k) :
    whittakerCoeff μ k (i + 1) * (i + 1 : ℕ) * (4 * π * I * μ) =
      whittakerCoeff μ k i * ((k : ℂ) - i) * ((4 * π * ‖μ‖ : ℝ) : ℂ) := by
  have hμ' : (‖μ‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hμ)
  have hu : I * (μ / ‖μ‖) ≠ 0 := mul_ne_zero I_ne_zero (div_ne_zero hμ hμ')
  have hc :
      ((k.choose (i + 1) : ℕ) : ℂ) * ((i + 1 : ℕ) : ℂ) = (k.choose i : ℂ) * ((k : ℂ) - i) := by
    rw [← Nat.cast_mul, Nat.choose_succ_right_eq, Nat.cast_mul, Nat.cast_sub hi.le]
  have hz : (I * (μ / ‖μ‖)) ^ (((k / 2 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) =
      (I * (μ / ‖μ‖)) ^ (((k / 2 : ℕ) : ℤ) - (i : ℤ)) * (I * (μ / ‖μ‖))⁻¹ := by
    rw [← zpow_sub_one₀ hu]
    congr 1
    push_cast
    ring1
  have hU : (I * (μ / ‖μ‖))⁻¹ * (I * μ) = ‖μ‖ := by
    field_simp
  simp only [whittakerCoeff, hz, ofReal_mul, ofReal_ofNat]
  linear_combination ((I * (μ / ‖μ‖)) ^ (((k / 2 : ℕ) : ℤ) - (i : ℤ)) * (I * (μ / ‖μ‖))⁻¹ *
    (4 * π * I * μ)) * hc + ((k.choose i : ℂ) * ((k : ℂ) - i) *
      (I * (μ / ‖μ‖)) ^ (((k / 2 : ℕ) : ℤ) - (i : ℤ)) * 4 * π) * hU

/-- The generating function `∑_j c_j Q^j P^{k-j} y^{k+1} K_{j - k/2}(4π|μ|y) e^θ`; for
`c_j = C(k, j) (iu)^{⌊k/2⌋ - j}` it pairs the lift of the Fourier–Bessel vector with
`(C(k, i) w₁^{k-i} w₂^i)_i`. -/
private noncomputable def whittakerGen (c : ℕ → ℂ) : SL(2, ℂ) → ℂ :=
  ∑ j ∈ Finset.range (k + 1), c j • whittakerTerm w₁ w₂ μ k (4 * π * ‖μ‖) j

private lemma casimirOne_whittakerGen (c : ℕ → ℂ) (hμ : μ ≠ 0) (hc : ∀ i < k,
    c (i + 1) * (i + 1 : ℕ) * (4 * π * I * μ) = c i * ((k : ℂ) - i) * ((4 * π * ‖μ‖ : ℝ) : ℂ)) :
    casimirOne (whittakerGen w₁ w₂ μ k c) = harmonicEigenvalue k • whittakerGen w₁ w₂ μ k c := by
  have hα : 0 < 4 * π * ‖μ‖ := by
    have hμ' : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
    positivity
  rw [whittakerGen,
    casimirOne_sum _ fun j ↦ (isLieSmooth_whittakerTerm w₁ w₂ μ k hα j).const_smul _]
  funext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hy : fY g = (fYr g : ℂ) := by
    rw [← ofReal_fYr]
  have key (j : ℕ) : (casimirOne (c j • whittakerTerm w₁ w₂ μ k (4 * π * ‖μ‖) j)) g =
      harmonicEigenvalue k * (c j * whittakerTerm w₁ w₂ μ k (4 * π * ‖μ‖) j g) -
        c j * (((k : ℂ) - j) * ((4 * π * ‖μ‖ : ℝ) : ℂ) * fY g *
          radial k ((j : ℂ) - k / 2 + 1) (4 * π * ‖μ‖) (fYr g)) * fQ w₁ w₂ g ^ j *
            fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) +
        c j * (j * fQ w₁ w₂ g ^ (j - 1)) * (4 * π * I * μ * fY g * fP w₁ w₂ g) *
          radial k ((j : ℂ) - k / 2) (4 * π * ‖μ‖) (fYr g) * fP w₁ w₂ g ^ (k - j) *
            cexp (fΘ μ g) := by
    rw [casimirOne_smul _ (isLieSmooth_whittakerTerm w₁ w₂ μ k hα j), Pi.smul_apply, smul_eq_mul,
      casimirOne_whittakerTerm w₁ w₂ μ k hα j]
    have hr : (j * (j + 2) / 2 : ℂ) * radial k ((j : ℂ) - k / 2) (4 * π * ‖μ‖) (fYr g) -
        (2⁻¹ : ℂ) * (fYr g : ℂ) * radial' k ((j : ℂ) - k / 2) (4 * π * ‖μ‖) (fYr g) +
        (2⁻¹ : ℂ) * (fYr g : ℂ) ^ 2 * radial'' k ((j : ℂ) - k / 2) (4 * π * ‖μ‖) (fYr g) -
        (2⁻¹ : ℂ) * ((4 * π * ‖μ‖ : ℝ) : ℂ) ^ 2 * (fYr g : ℂ) ^ 2 *
          radial k ((j : ℂ) - k / 2) (4 * π * ‖μ‖) (fYr g) -
        j * (fYr g : ℂ) * radial' k ((j : ℂ) - k / 2) (4 * π * ‖μ‖) (fYr g) +
        ((k : ℂ) - j) * ((4 * π * ‖μ‖ : ℝ) : ℂ) * (fYr g : ℂ) *
          radial k ((j : ℂ) - k / 2 + 1) (4 * π * ‖μ‖) (fYr g) =
        ((k : ℂ) ^ 2 - 4) / 8 * radial k ((j : ℂ) - k / 2) (4 * π * ‖μ‖) (fYr g) :=
      radial_equation k j hα (fYr_pos g)
    have hn : (normSq μ : ℂ) = (‖μ‖ : ℂ) ^ 2 := by
      rw [normSq_eq_norm_sq, ofReal_pow]
    simp only [whittakerTerm, Pi.mul_apply, Function.comp_apply, harmonicEigenvalue, hy, hn]
    simp only [ofReal_mul, ofReal_ofNat] at hr ⊢
    linear_combination (c j * fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) * fQ w₁ w₂ g ^ j) * hr
  have hXY : ∑ j ∈ Finset.range (k + 1), c j *
      (((k : ℂ) - j) * ((4 * π * ‖μ‖ : ℝ) : ℂ) * fY g *
        radial k ((j : ℂ) - k / 2 + 1) (4 * π * ‖μ‖) (fYr g)) * fQ w₁ w₂ g ^ j *
          fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) =
      ∑ j ∈ Finset.range (k + 1), c j * (j * fQ w₁ w₂ g ^ (j - 1)) *
        (4 * π * I * μ * fY g * fP w₁ w₂ g) * radial k ((j : ℂ) - k / 2) (4 * π * ‖μ‖) (fYr g) *
          fP w₁ w₂ g ^ (k - j) * cexp (fΘ μ g) := by
    refine sum_range_succ_eq_of_shift k _ _ (fun i hi ↦ ?_) (by simp) (by simp)
    have e₁ : ((i + 1 : ℕ) : ℂ) - k / 2 = (i : ℂ) - k / 2 + 1 := by
      push_cast
      ring1
    have e₂ : k - i = k - (i + 1) + 1 := by
      omega
    rw [e₁, e₂, Nat.add_sub_cancel, pow_succ]
    linear_combination (-(fY g * radial k ((i : ℂ) - k / 2 + 1) (4 * π * ‖μ‖) (fYr g) *
      fQ w₁ w₂ g ^ i * fP w₁ w₂ g ^ (k - (i + 1)) * fP w₁ w₂ g * cexp (fΘ μ g))) * hc i hi
  rw [Finset.sum_congr rfl fun j _ ↦ key j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  linear_combination (-1 : ℂ) * hXY

/-- **The transpose of `Sym^k`**: pairing `Sym^k(A) v` with the vector `(C(k, i) w₁^{k-i} w₂^i)_i`
is pairing `v` with the same vector for `Aᵀ w`. -/
lemma sum_choose_mul_symPowMatrix (A : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin (k + 1)) :
    ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) * symPowMatrix k A i j =
      (k.choose j : ℂ) * (A 0 0 * w₁ + A 1 0 * w₂) ^ (k - j : ℕ) *
        (A 0 1 * w₁ + A 1 1 * w₂) ^ (j : ℕ) := by
  have hp : (∑ l : Fin (k + 1), Polynomial.C ((∑ i : Fin (k + 1), (k.choose i : ℂ) *
      w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) * symPowMatrix k A i l) - (k.choose l : ℂ) *
        (A 0 0 * w₁ + A 1 0 * w₂) ^ (k - l : ℕ) * (A 0 1 * w₁ + A 1 1 * w₂) ^ (l : ℕ)) *
          Polynomial.X ^ (k - l : ℕ)) = 0 := by
    refine Polynomial.funext fun x ↦ ?_
    have h₁ : ∑ l : Fin (k + 1), (∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) *
        w₂ ^ (i : ℕ) * symPowMatrix k A i l) * x ^ (k - l : ℕ) =
          (w₂ * (A 1 0 * x + A 1 1 * 1) + w₁ * (A 0 0 * x + A 0 1 * 1)) ^ k := by
      have hm (i : Fin (k + 1)) : ∑ l : Fin (k + 1), symPowMatrix k A i l * x ^ (k - l : ℕ) =
          (A 0 0 * x + A 0 1 * 1) ^ (k - i : ℕ) * (A 1 0 * x + A 1 1 * 1) ^ (i : ℕ) := by
        simpa [mulVec, dotProduct, monomialVector] using
          congrFun (symPowMatrix_mulVec_monomialVector k A x 1) i
      rw [add_pow, ← Fin.sum_univ_eq_sum_range (fun m ↦ (w₂ * (A 1 0 * x + A 1 1 * 1)) ^ m *
        (w₁ * (A 0 0 * x + A 0 1 * 1)) ^ (k - m) * (k.choose m : ℂ))]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have e : ∑ l : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) *
          symPowMatrix k A i l * x ^ (k - l : ℕ) = (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) *
            w₂ ^ (i : ℕ) * ∑ l : Fin (k + 1), symPowMatrix k A i l * x ^ (k - l : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ ↦ by ring1
      rw [e, hm i, mul_pow, mul_pow]
      ring1
    have h₂ : ∑ l : Fin (k + 1), (k.choose l : ℂ) * (A 0 0 * w₁ + A 1 0 * w₂) ^ (k - l : ℕ) *
        (A 0 1 * w₁ + A 1 1 * w₂) ^ (l : ℕ) * x ^ (k - l : ℕ) =
          ((A 0 1 * w₁ + A 1 1 * w₂) + (A 0 0 * w₁ + A 1 0 * w₂) * x) ^ k := by
      rw [add_pow, ← Fin.sum_univ_eq_sum_range (fun m ↦ (A 0 1 * w₁ + A 1 1 * w₂) ^ m *
        ((A 0 0 * w₁ + A 1 0 * w₂) * x) ^ (k - m) * (k.choose m : ℂ))]
      exact Finset.sum_congr rfl fun l _ ↦ by
        rw [mul_pow]
        ring1
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, sub_mul,
      Finset.sum_sub_distrib, h₁, h₂]
    ring1
  have hc : (∑ l : Fin (k + 1), if k - j = k - l then (∑ i : Fin (k + 1), (k.choose i : ℂ) *
      w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) * symPowMatrix k A i l) - (k.choose l : ℂ) *
        (A 0 0 * w₁ + A 1 0 * w₂) ^ (k - l : ℕ) * (A 0 1 * w₁ + A 1 1 * w₂) ^ (l : ℕ) else 0) =
          0 := by
    simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
      using congrArg (Polynomial.coeff · (k - j : ℕ)) hp
  rw [Finset.sum_eq_single j (fun l _ hl ↦ ite_eq_right fun e ↦ hl (Fin.ext (by omega)))
    (by simp), ite_eq_left rfl] at hc
  exact sub_eq_zero.mp hc

lemma eq_zero_of_sum_choose_mul {v : Fin (k + 1) → ℂ}
    (h : ∀ w₁ w₂ : ℂ,
      ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) * v i = 0) :
    v = 0 := by
  have hp :
      (∑ l : Fin (k + 1), Polynomial.C ((k.choose l : ℂ) * v l) * Polynomial.X ^ (l : ℕ)) = 0 :=
    Polynomial.funext fun x ↦ by
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [← h 1 x]
      exact Finset.sum_congr rfl fun l _ ↦ by ring1
  funext j
  have hc : (∑ l : Fin (k + 1), if (j : ℕ) = l then (k.choose l : ℂ) * v l else 0) = 0 := by
    simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
      using congrArg (Polynomial.coeff · (j : ℕ)) hp
  rw [Finset.sum_eq_single j (fun l _ hl ↦ ite_eq_right fun e ↦ hl (Fin.ext e.symm)) (by simp),
    ite_eq_left rfl] at hc
  have hj : (k.choose j : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.lt_succ_iff.mp j.2)).ne'
  exact (mul_eq_zero.mp hc).resolve_left hj

/-- The **Fourier–Bessel (Whittaker) function** `y W_k(u, 4π|μ|y) ψ(μx)` of weight `k` and
frequency `μ ∈ ℂ` on `ℋ₃`, where `ψ(z) = e^{2πi(z + z̄)}`, `u = μ / |μ|` and
`W_k(u, t) = ((iu)^{k/2-j} K_{j-k/2}(t))_j` (`bianchiWhittakerVector`): the function of the terms
of the Fourier–Bessel expansion of weight `k` (`bianchiWhittakerTerm`, with `μ = α / √Δ`). -/
noncomputable def bianchiWhittakerFunction : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  fun z ↦ ((z.coords.2 : ℂ) * cexp (2 * π * I * (μ * z.coords.1 + conj (μ * z.coords.1)))) •
    bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖ * z.coords.2)

private lemma extend_bianchiWhittakerFunction (g : SL(2, ℂ)) :
    extend (bianchiWhittakerFunction μ k) (moebius g (0, 1)) =
      ((fYr g : ℂ) * cexp (fΘ μ g)) • bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖ * fYr g) := by
  have hpos : 0 < (moebius g (0, 1)).2 := moebius_snd_pos g one_pos
  have hc : coords (.mk (WithLp.toLp 2 (moebius g (0, 1))) hpos) = moebius g (0, 1) :=
    rfl
  have hU : conj (fU g) = fUb g := by
    simp [fU, fUb, ent, cent]
  have hY : conj (fY g) = fY g := by
    rw [← ofReal_fYr, conj_ofReal]
  rw [extend, dite_eq_left hpos]
  simp only [bianchiWhittakerFunction, hc, moebius_snd, moebius_fst]
  congr 3
  simp only [fΘ, fV, Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul, map_mul, hU, hY]
  ring1

private lemma isLieSmooth_bianchiLift_bianchiWhittakerFunction :
    IsLieSmooth (bianchiLift k (bianchiWhittakerFunction μ k)) :=
  isLieSmooth_of_contDiff fun γ hγ ↦ by
    have h₀₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := hγ 0 0
    have h₀₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := hγ 0 1
    have h₁₀ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := hγ 1 0
    have h₁₁ : ContDiff ℝ 2 fun st ↦ (γ st : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := hγ 1 1
    have hN (st : ℝ × ℝ) : moebiusDenom (γ st) (0, 1) ≠ 0 :=
      (moebiusDenom_pos (γ st) (p := (0, 1)) one_pos).ne'
    have hD : ContDiff ℝ 2 fun st ↦ moebiusDenom (γ st) (0, 1) := by
      simp only [moebiusDenom]
      fun_prop
    have hY : ContDiff ℝ 2 fun st ↦ fYr (γ st) := contDiff_fYr_comp hγ
    have hK (ν' : ℂ) : ContDiff ℝ 2 fun st ↦ besselK ν' (4 * π * ‖μ‖ * fYr (γ st)) := by
      rcases eq_or_ne μ 0 with hμ | hμ
      · simp only [hμ, norm_zero, mul_zero, zero_mul]
        exact contDiff_const
      · have hα : 0 < 4 * π * ‖μ‖ := by
          have hμ' : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
          positivity
        exact ((contDiffOn_besselK ν').of_le (by norm_cast)).comp_contDiff
          (contDiff_const.mul hY) fun st ↦ mul_pos hα (fYr_pos (γ st))
    refine contDiff_pi.2 fun i ↦ ?_
    simp only [Function.comp_def, bianchiLift_apply, extend_bianchiWhittakerFunction, mulVec,
      dotProduct]
    refine ContDiff.sum fun j _ ↦ ContDiff.mul ?_ ?_
    · simp only [inv_automorphyFactor, symPowMatrix, of_apply, Matrix.smul_apply,
        cons_val_zero, cons_val_one, ← ofReal_inv]
      fun_prop (disch := exact hN _)
    · simp only [Pi.smul_apply, smul_eq_mul, bianchiWhittakerVector]
      exact ((contDiff_ofReal.comp hY).mul (contDiff_exp.comp (contDiff_fΘ_comp μ hγ))).mul
        (contDiff_const.mul (hK _))

private lemma sum_choose_mul_bianchiLift (g : SL(2, ℂ)) :
    ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) *
      bianchiLift k (bianchiWhittakerFunction μ k) g i =
        whittakerGen w₁ w₂ μ k (whittakerCoeff μ k) g := by
  have hE : extend (bianchiWhittakerFunction μ k) (moebius g (0, 1)) =
      ((fYr g : ℂ) * cexp (fΘ μ g)) • bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖ * fYr g) :=
    extend_bianchiWhittakerFunction μ k g
  have hS : ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) *
      bianchiLift k (bianchiWhittakerFunction μ k) g i = ∑ j : Fin (k + 1),
        (∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) *
          symPowMatrix k (automorphyFactor g (0, 1))⁻¹ i j) *
            extend (bianchiWhittakerFunction μ k) (moebius g (0, 1)) j := by
    simp only [bianchiLift_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring1
  have hN : (moebiusDenom g (0, 1) : ℂ) = fN g := by
    rw [fN_apply, moebiusDenom]
    simp only [mul_zero, zero_add, one_pow, mul_one]
    push_cast
    ring1
  have hY : (fN g)⁻¹ = (fYr g : ℂ) :=
    (congrFun ofReal_fYr g).symm
  rw [hS, hE, whittakerGen, Finset.sum_apply,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ (whittakerCoeff μ k j •
      whittakerTerm w₁ w₂ μ k (4 * π * ‖μ‖) j) g)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [sum_choose_mul_symPowMatrix, inv_automorphyFactor, hN]
  simp only [whittakerTerm, whittakerCoeff, bianchiWhittakerVector, radial, Pi.mul_apply,
    Function.comp_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, of_apply, cons_val',
    cons_val_zero, cons_val_one, cons_val_fin_one, fQ, fP, ent, cent, Pi.add_apply, Pi.sub_apply,
    hY, mul_zero, zero_add, ofReal_one, mul_one]
  have hb₁ : (fYr g : ℂ) * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * w₁ +
      (fYr g : ℂ) * -conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * w₂ = (fYr g : ℂ) *
        (w₁ * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) -
          w₂ * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
    ring1
  have hb₂ : (fYr g : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * w₁ +
      (fYr g : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * w₂ = (fYr g : ℂ) *
        (w₁ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 + w₂ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
    ring1
  have hp : (fYr g : ℂ) ^ (k - j : ℕ) * (fYr g : ℂ) ^ (j : ℕ) * fYr g = (fYr g : ℂ) ^ (k + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp j.2), pow_succ]
  rw [hb₁, hb₂, mul_pow, mul_pow]
  linear_combination ((k.choose j : ℂ) * (I * (μ / ‖μ‖)) ^ (((k / 2 : ℕ) : ℤ) - ((j : ℕ) : ℤ)) *
    (w₁ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 + w₂ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ^ (j : ℕ) *
      besselK (((j : ℕ) : ℂ) - k / 2) (4 * π * ‖μ‖ * fYr g) * cexp (fΘ μ g) *
        (w₁ * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) -
          w₂ * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) ^ (k - j : ℕ)) * hp

/-- **The first Casimir equation for the Fourier–Bessel vector**: for `μ ≠ 0`, the Casimir operator
`Ψ` acts on the lift of `y W_k(u, 4π|μ|y) ψ(μx)` (`bianchiWhittakerFunction`) by `(k² - 4) / 8`. -/
lemma casimirOne_bianchiLift_bianchiWhittakerFunction (hμ : μ ≠ 0) :
    casimirOne (bianchiLift k (bianchiWhittakerFunction μ k)) =
      harmonicEigenvalue k • bianchiLift k (bianchiWhittakerFunction μ k) := by
  funext g
  refine sub_eq_zero.mp (eq_zero_of_sum_choose_mul k fun w₁ w₂ ↦ ?_)
  let L : (Fin (k + 1) → ℂ) →L[ℂ] ℂ := ∑ i : Fin (k + 1),
    ((k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ)) • ContinuousLinearMap.proj i
  have hL (v : Fin (k + 1) → ℂ) :
      L v = ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) * v i := by
    simp [L]
  have h₁ : L ∘ bianchiLift k (bianchiWhittakerFunction μ k) =
      whittakerGen w₁ w₂ μ k (whittakerCoeff μ k) :=
    funext fun g ↦ by rw [Function.comp_apply, hL, sum_choose_mul_bianchiLift]
  have h₂ : casimirOne (L ∘ bianchiLift k (bianchiWhittakerFunction μ k)) g =
      (L ∘ casimirOne (bianchiLift k (bianchiWhittakerFunction μ k))) g :=
    congrFun (casimirOne_clm_comp L (isLieSmooth_bianchiLift_bianchiWhittakerFunction μ k)) g
  rw [h₁, casimirOne_whittakerGen w₁ w₂ μ k _ hμ (whittakerCoeff_succ μ k hμ), Function.comp_apply,
    hL, Pi.smul_apply, ← sum_choose_mul_bianchiLift w₁ w₂ μ k g] at h₂
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [← h₂, smul_eq_mul, Finset.mul_sum, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ ↦ by ring1

private lemma whittakerTerm_conjSL (j : ℕ) (g : SL(2, ℂ)) :
    whittakerTerm w₁ w₂ μ k (4 * π * ‖μ‖) j (conjSL g) = fP w₂ (-w₁) g ^ j *
      (radial k ((j : ℂ) - k / 2) (4 * π * ‖conj μ‖) (fYr g) * cexp (fΘ (conj μ) g)) *
        (-fQ w₂ (-w₁) g) ^ (k - j) := by
  have hY : fYr (conjSL g) = fYr g := by
    simp [fYr, conjSL_apply]
  have hΘ : fΘ μ (conjSL g) = fΘ (conj μ) g := by
    simp only [fΘ, fY, fV, fN, fU, fUb, ent, cent, Pi.smul_apply, Pi.mul_apply, Pi.add_apply,
      smul_eq_mul, conjSL_apply, conj_conj]
    ring1
  simp only [whittakerTerm, Pi.mul_apply, Function.comp_apply, hY, hΘ, norm_conj]
  congr 2
  · simp [fQ, fP, ent, cent, conjSL_apply]
    ring1
  · simp [fQ, fP, ent, cent, conjSL_apply]
    ring1

private lemma whittakerGen_conjSL (c : ℕ → ℂ) (g : SL(2, ℂ)) :
    whittakerGen w₁ w₂ μ k c (conjSL g) =
      whittakerGen w₂ (-w₁) (conj μ) k (fun j ↦ c (k - j) * (-1) ^ j) g := by
  simp only [whittakerGen, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, whittakerTerm_conjSL]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e : ((k - j : ℕ) : ℂ) - k / 2 = -((j : ℂ) - k / 2) := by
    rw [Nat.cast_sub hj']
    ring1
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hj', radial, e, besselK_neg]
  simp only [whittakerTerm, Pi.mul_apply, Function.comp_apply, radial]
  rw [neg_pow (fQ w₂ (-w₁) g)]
  ring1

private lemma whittakerCoeff_reflect (c : ℕ → ℂ) (hc : ∀ i < k,
    c (i + 1) * (i + 1 : ℕ) * (4 * π * I * μ) = c i * ((k : ℂ) - i) * ((4 * π * ‖μ‖ : ℝ) : ℂ)) :
    ∀ i < k, c (k - (i + 1)) * (-1) ^ (i + 1) * (i + 1 : ℕ) * (4 * π * I * conj μ) =
      c (k - i) * (-1) ^ i * ((k : ℂ) - i) * ((4 * π * ‖conj μ‖ : ℝ) : ℂ) := by
  intro i hi
  have h : c (k - (i + 1) + 1) * ((k - (i + 1) + 1 : ℕ) : ℂ) * (4 * π * I * μ) =
      c (k - (i + 1)) * ((k : ℂ) - ((k - (i + 1) : ℕ) : ℂ)) * ((4 * π * ‖μ‖ : ℝ) : ℂ) :=
    hc (k - (i + 1)) (by omega)
  have e₁ : k - (i + 1) + 1 = k - i := by
    omega
  have e₂ : ((k - (i + 1) + 1 : ℕ) : ℂ) = (k : ℂ) - i := by
    rw [e₁, Nat.cast_sub hi.le]
  have e₃ : (k : ℂ) - ((k - (i + 1) : ℕ) : ℂ) = (i + 1 : ℕ) := by
    rw [Nat.cast_sub hi]
    push_cast
    ring1
  rw [e₂, e₃, e₁] at h
  have hn : μ * conj μ = (‖μ‖ : ℂ) ^ 2 := by
    rw [mul_conj, normSq_eq_norm_sq, ofReal_pow]
  rw [norm_conj]
  simp only [ofReal_mul, ofReal_ofNat] at h ⊢
  rcases eq_or_ne μ 0 with hμ | hμ
  · simp [hμ]
  · have hα : (4 * (π : ℂ) * ‖μ‖) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
        (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hμ))
    refine mul_right_cancel₀ hα ?_
    linear_combination ((-1) ^ (i + 1) * (4 * π * I * conj μ)) * h.symm +
      (c (k - i) * ((k : ℂ) - i) * (-1) ^ i * 16 * π ^ 2) * hn -
        (16 * π ^ 2 * μ * conj μ * c (k - i) * (-1) ^ i * ((k : ℂ) - i)) * I_sq

/-- **The second Casimir equation for the Fourier–Bessel vector**: for `μ ≠ 0`, the Casimir
operator `Ψ'` acts on the lift of `y W_k(u, 4π|μ|y) ψ(μx)` (`bianchiWhittakerFunction`) by
`(k² - 4) / 8`. Complex conjugation `g ↦ ḡ` of `SL(2, ℂ)` turns `Ψ'` into `Ψ`, and the lift into
one whose pairings are again generating functions of the first Casimir equation, for `μ̄`. -/
lemma casimirTwo_bianchiLift_bianchiWhittakerFunction (hμ : μ ≠ 0) :
    casimirTwo (bianchiLift k (bianchiWhittakerFunction μ k)) =
      harmonicEigenvalue k • bianchiLift k (bianchiWhittakerFunction μ k) := by
  funext g
  refine sub_eq_zero.mp (eq_zero_of_sum_choose_mul k fun w₁ w₂ ↦ ?_)
  let L : (Fin (k + 1) → ℂ) →L[ℂ] ℂ := ∑ i : Fin (k + 1),
    ((k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ)) • ContinuousLinearMap.proj i
  have hL (v : Fin (k + 1) → ℂ) :
      L v = ∑ i : Fin (k + 1), (k.choose i : ℂ) * w₁ ^ (k - i : ℕ) * w₂ ^ (i : ℕ) * v i := by
    simp [L]
  have h₁ : L ∘ (bianchiLift k (bianchiWhittakerFunction μ k) ∘ conjSL) =
      whittakerGen w₂ (-w₁) (conj μ) k (fun j ↦ whittakerCoeff μ k (k - j) * (-1) ^ j) :=
    funext fun h ↦ by
      rw [Function.comp_apply, Function.comp_apply, hL, sum_choose_mul_bianchiLift,
        whittakerGen_conjSL]
  have h₂ : casimirOne (L ∘ (bianchiLift k (bianchiWhittakerFunction μ k) ∘ conjSL)) (conjSL g) =
      (L ∘ casimirOne (bianchiLift k (bianchiWhittakerFunction μ k) ∘ conjSL)) (conjSL g) :=
    congrFun (casimirOne_clm_comp L
      (isLieSmooth_bianchiLift_bianchiWhittakerFunction μ k).comp_conjSL) (conjSL g)
  rw [h₁, casimirOne_whittakerGen w₂ (-w₁) (conj μ) k _ ((map_ne_zero _).mpr hμ)
    (whittakerCoeff_reflect μ k _ (whittakerCoeff_succ μ k hμ)), Pi.smul_apply, ← h₁,
    casimirOne_comp_conjSL] at h₂
  simp only [Function.comp_apply, conjSL_conjSL, hL] at h₂
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [← h₂, smul_eq_mul, Finset.mul_sum, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ ↦ by ring1

/-- **The Fourier–Bessel vector of weight `k` is harmonic** (LMFDB `mf.bianchi.spaces`,
`mf.bianchi.newform`): for every frequency `μ ≠ 0`, the function `y W_k(u, 4π|μ|y) ψ(μx)` of the
weight `k` Fourier–Bessel expansion (`bianchiWhittakerVector`) satisfies both Casimir equations
`IsBianchiHarmonic k`. -/
lemma isBianchiHarmonic_bianchiWhittakerFunction (hμ : μ ≠ 0) :
    IsBianchiHarmonic k (bianchiWhittakerFunction μ k) :=
  ⟨casimirOne_bianchiLift_bianchiWhittakerFunction μ k hμ,
    casimirTwo_bianchiLift_bianchiWhittakerFunction μ k hμ⟩

lemma isBianchiHarmonic_smul_bianchiWhittakerFunction (hμ : μ ≠ 0) (a : ℂ) :
    IsBianchiHarmonic k (a • bianchiWhittakerFunction μ k) := by
  have h : IsLieSmooth (bianchiLift k (bianchiWhittakerFunction μ k)) :=
    isLieSmooth_bianchiLift_bianchiWhittakerFunction μ k
  rw [IsBianchiHarmonic, bianchiLift_smul, casimirOne_smul a h, casimirTwo_smul a h,
    casimirOne_bianchiLift_bianchiWhittakerFunction μ k hμ,
    casimirTwo_bianchiLift_bianchiWhittakerFunction μ k hμ, smul_comm a]
  exact ⟨rfl, rfl⟩

variable {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ) (δ : ℂ) (c : 𝓞 K → ℂ) (a : 𝓞 K)

lemma bianchiWhittakerTerm_coords (hδ : ‖δ‖ = √|(discr K : ℝ)|) (z : HyperbolicThreeSpace) :
    bianchiWhittakerTerm σ δ k c z.coords a = c a • bianchiWhittakerFunction (σ a / δ) k z := by
  have e₁ : (σ a : ℂ) * z.coords.1 / δ = (σ a : ℂ) / δ * z.coords.1 := by
    ring1
  have e₂ : 4 * π * ‖(σ a : ℂ)‖ * z.coords.2 / √|(discr K : ℝ)| =
      4 * π * ‖(σ a : ℂ) / δ‖ * z.coords.2 := by
    rw [norm_div, hδ]
    ring1
  simp only [bianchiWhittakerTerm, bianchiWhittakerFunction]
  rw [e₁, e₂, smul_smul]
  congr 1
  ring1

variable {a} in
/-- **The terms of the Fourier–Bessel expansion of weight `k` are harmonic** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): for `δ` with `|δ| = √|Δ|`, every term
`c(α) y W_k(u, 4π|α|y / √|Δ|) ψ(αx / δ)`, `α ≠ 0`, of the expansion `HasBianchiWhittakerExpansion`
satisfies the Casimir equations `IsBianchiHarmonic k`. -/
lemma isBianchiHarmonic_bianchiWhittakerTerm (hδ : ‖δ‖ = √|(discr K : ℝ)|) (ha : a ≠ 0) :
    IsBianchiHarmonic k fun z ↦ bianchiWhittakerTerm σ δ k c z.coords a := by
  have hδ₀ : δ ≠ 0 := norm_ne_zero_iff.mp <| hδ ▸ (Real.sqrt_pos.mpr <| abs_pos.mpr <|
    Int.cast_ne_zero.mpr <| discr_ne_zero K).ne'
  have hμ : (σ a : ℂ) / δ ≠ 0 :=
    div_ne_zero ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr ha)) hδ₀
  have e : (fun z ↦ bianchiWhittakerTerm σ δ k c z.coords a) =
      c a • bianchiWhittakerFunction ((σ a : ℂ) / δ) k :=
    funext fun z ↦ bianchiWhittakerTerm_coords k σ δ c a hδ z
  rw [e]
  exact isBianchiHarmonic_smul_bianchiWhittakerFunction _ k hμ (c a)

end HyperbolicThreeSpace
