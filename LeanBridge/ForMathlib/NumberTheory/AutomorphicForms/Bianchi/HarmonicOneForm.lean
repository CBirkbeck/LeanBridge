import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HeckeAlgebra
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Weight 2 Bianchi modular forms as harmonic differential 1-forms

Hyperbolic 3-space `ℋ₃ = {(x, y) ∈ ℂ × ℝ | y > 0}`, `x = x₁ + i x₂`, carries the metric
`(dx₁² + dx₂² + dy²) / y²`. A complex differential 1-form `ω = a₁ dx₁ + a₂ dx₂ + a₃ dy` on `ℋ₃` is
given here by its coefficient functions `a : ℂ × ℝ → ℂ³`. For this metric, `g_{ij} = y⁻² δ_{ij}`
and `√det g = y⁻³`, the codifferentials (the formal adjoints of the exterior derivative `d`) are
`δω = -y³ ∑ᵢ ∂ᵢ(y⁻¹ aᵢ)` on 1-forms and `(δη)_j = -y ∑ᵢ ∂ᵢ(y η_{ij})` on 2-forms, and `ω` is
**harmonic** if its Hodge Laplacian `Δω = dδω + δdω` vanishes.

LMFDB `mf.bianchi.weight2` describes a weight 2 Bianchi modular form for `Γ` alternatively as a real
analytic `F = (F₁, F₂, F₃) : ℋ₃ → ℂ³` such that the 1-form `F₁β₁ + F₂β₂ + F₃β₃` is harmonic and
`Γ`-invariant, and calls it **cuspidal** if moreover the constant term of `F ∣ γ` vanishes for every
`γ ∈ PSL₂(𝒪_K)` (`IsCuspidalWeightTwo`). The knowl takes `β = (-dx/y, dy/y, dx̄/y)`, with
`dx = dx₁ + i dx₂`, but with its slash operator `F ∣ γ` (`slashTwo`), which is `Sym²` of the
adjugate of `J(γ, z)` in the basis `X², XY, Y²`, the invariance of the 1-form is `F ∣ γ = F` for
`β = (-dx/y, 2 dy/y, dx̄/y)`, which is used here (the knowl's basis would give the invariance of
`(F₁, F₂ / 2, F₃)`). Invariance is the invariance of the 1-form under pullback by the
transformations `z ↦ g z` of `ℋ₃`, for the `SL(2, ℂ)`-representatives `g` of the elements of `Γ`.
The knowl also omits the polynomial growth at the cusps, which is added here.

The knowl's description of the action of `PSL(2, ℂ)` on 1-forms through `Sym²(J(γ, z))` is proved
(`oneFormPullback_weightTwoOneForm`), by computing the derivative of `z ↦ g z`: the pullback of the
1-form of `F` is the 1-form of `F ∣ g`. Hence the invariance of the 1-form is `F ∣ γ = F`, that is
the invariance of `y⁻¹ F` under the weight 2 slash operator `bianchiSlash 2` of LMFDB `mf.bianchi`,
and the description agrees with the Bianchi modular forms `IsBianchiModularForm` of weight `2`
(for `y⁻¹ F`) as soon as the harmonicity of the 1-form is equivalent to the Casimir equations
`IsBianchiHarmonic 2` (`isBianchiWeightTwoForm_iff_isBianchiModularForm`). That equivalence, between
the Hodge Laplacian of the 1-form and the Casimir operators of `SL(2, ℂ)` on the lift of `y⁻¹ F`,
is not proved here.

## Main definitions

* `HyperbolicThreeSpace.coordDeriv`: the partial derivatives `∂/∂x₁`, `∂/∂x₂`, `∂/∂y`.
* `HyperbolicThreeSpace.hodgeLaplacianOneForm` (LMFDB `mf.bianchi.weight2`): the Hodge Laplacian
  `Δ = dδ + δd` of a 1-form on `ℋ₃`.
* `HyperbolicThreeSpace.IsHarmonicOneForm` (LMFDB `mf.bianchi.weight2`): harmonic 1-forms.
* `HyperbolicThreeSpace.oneFormPullback`: the pullback of a 1-form by `z ↦ g z`, `g ∈ SL(2, ℂ)`.
* `HyperbolicThreeSpace.weightTwoOneForm` (LMFDB `mf.bianchi.weight2`): the 1-form
  `F₁β₁ + F₂β₂ + F₃β₃`.
* `HyperbolicThreeSpace.IsBianchiWeightTwoForm` (LMFDB `mf.bianchi.weight2`): weight 2 Bianchi
  modular forms as harmonic invariant 1-forms.
* `HyperbolicThreeSpace.IsCuspidalBianchiWeightTwoForm` (LMFDB `mf.bianchi.weight2`): cuspidal
  ones.

## Main results

* `HyperbolicThreeSpace.weightTwoOneForm_injective`: the 1-form determines `F` on `ℋ₃`.
* `HyperbolicThreeSpace.oneFormPullback_weightTwoOneForm`: `g^*(F₁β₁ + F₂β₂ + F₃β₃)` is the 1-form
  of `F ∣ g`.
* `HyperbolicThreeSpace.oneFormPullback_weightTwoOneForm_eq_iff`: the 1-form of `F` is invariant
  under `g` exactly when `F ∣ g = F`.
* `HyperbolicThreeSpace.bianchiSlash_two_inv_smul_eq_iff`: `F ∣ g = F` exactly when `y⁻¹ F` is
  fixed by `bianchiSlash 2 g`.
* `HyperbolicThreeSpace.isBianchiWeightTwoForm_iff`: the description in terms of `y⁻¹ F` and the
  conditions of `IsBianchiModularForm`.
* `HyperbolicThreeSpace.isBianchiWeightTwoForm_iff_isBianchiModularForm`: agreement with
  `IsBianchiModularForm` in weight `2`, given the equivalence of the two harmonicity conditions.
-/

open Complex Matrix NumberField

open scoped ComplexConjugate MatrixGroups

namespace HyperbolicThreeSpace

variable (ω : ℂ × ℝ → Fin 3 → ℂ) (p : ℂ × ℝ) (i j : Fin 3)

/-- The coordinate vectors `∂/∂x₁ = (1, 0)`, `∂/∂x₂ = (i, 0)` and `∂/∂y = (0, 1)` of
`ℂ × ℝ = ℝ³`. -/
def coordVector : Fin 3 → ℂ × ℝ :=
  ![(1, 0), (I, 0), (0, 1)]

/-- The coordinate functions `dx₁(v) = Re v₁`, `dx₂(v) = Im v₁` and `dy(v) = v₂` of `ℂ × ℝ = ℝ³`,
the dual basis of `coordVector`, with complex values. -/
noncomputable def coordFun : Fin 3 → ℂ × ℝ → ℂ :=
  ![fun v ↦ (v.1.re : ℂ), fun v ↦ (v.1.im : ℂ), fun v ↦ (v.2 : ℂ)]

/-- The partial derivative `∂f/∂xᵢ` at `p` of `f : ℂ × ℝ → ℂ` in the coordinates
`(x₁, x₂, y)`, `x = x₁ + i x₂`. -/
noncomputable def coordDeriv (f : ℂ × ℝ → ℂ) : ℂ :=
  fderiv ℝ f p (coordVector i)

/-- The codifferential `δω = -y³ ∑ᵢ ∂ᵢ(y⁻¹ aᵢ)` of the 1-form `ω = ∑ᵢ aᵢ dxᵢ` on `ℋ₃`, for the
hyperbolic metric `(dx₁² + dx₂² + dy²) / y²`: the formal adjoint of the exterior derivative. -/
noncomputable def oneFormCodiff : ℂ :=
  -((p.2 : ℂ) ^ 3) * ∑ i, coordDeriv p i fun q ↦ (q.2 : ℂ)⁻¹ * ω q i

/-- The exterior derivative `dω = ∑_{i,j} (∂ᵢ aⱼ - ∂ⱼ aᵢ) dxᵢ ⊗ dxⱼ / 2` of the 1-form
`ω = ∑ᵢ aᵢ dxᵢ`, by its antisymmetric coefficients `(dω)_{ij} = ∂ᵢ aⱼ - ∂ⱼ aᵢ`. -/
noncomputable def oneFormExtDeriv : ℂ :=
  coordDeriv p i (fun q ↦ ω q j) - coordDeriv p j fun q ↦ ω q i

/-- The codifferential `(δη)_j = -y ∑ᵢ ∂ᵢ(y η_{ij})` of the 2-form `η` with antisymmetric
coefficients `η_{ij}` on `ℋ₃`, for the hyperbolic metric: the formal adjoint of the exterior
derivative on 1-forms. -/
noncomputable def twoFormCodiff (η : ℂ × ℝ → Fin 3 → Fin 3 → ℂ) : ℂ :=
  -(p.2 : ℂ) * ∑ i, coordDeriv p i fun q ↦ (q.2 : ℂ) * η q i j

/-- The **Hodge Laplacian** `Δω = dδω + δdω` (LMFDB `mf.bianchi.weight2`) of the 1-form
`ω = ∑ᵢ aᵢ dxᵢ` on `ℋ₃`, `(x₁, x₂, y)` being the coordinates, for the hyperbolic metric
`(dx₁² + dx₂² + dy²) / y²`, by its coefficients. -/
noncomputable def hodgeLaplacianOneForm : ℂ :=
  coordDeriv p j (oneFormCodiff ω) + twoFormCodiff p j (oneFormExtDeriv ω)

/-- A 1-form `ω` on `ℋ₃` is **harmonic** (LMFDB `mf.bianchi.weight2`) if its Hodge Laplacian
`Δω = dδω + δdω` vanishes at every point of `ℋ₃`. -/
def IsHarmonicOneForm : Prop :=
  ∀ p : ℂ × ℝ, 0 < p.2 → hodgeLaplacianOneForm ω p = 0

/-- The **pullback** `g^*ω` of the 1-form `ω = ∑ᵢ aᵢ dxᵢ` by the transformation `z ↦ g z` of `ℋ₃`,
`g ∈ SL(2, ℂ)` (`moebius`): `(g^*ω)_p(v) = ω_{gp}(D(g·)_p v)`, by its coefficients. -/
noncomputable def oneFormPullback (g : SL(2, ℂ)) : Fin 3 → ℂ :=
  fun j ↦ ∑ i, ω (moebius g p) i * coordFun i (fderiv ℝ (moebius g) p (coordVector j))

/-- The 1-form `F₁β₁ + F₂β₂ + F₃β₃` (LMFDB `mf.bianchi.weight2`) of `F : ℋ₃ → ℂ³`, given on
`ℂ × ℝ`, with `β = (-dx/y, 2 dy/y, dx̄/y)`, `dx = dx₁ + i dx₂`, in the coordinates `(x₁, x₂, y)`:
`((F₃ - F₁) dx₁ - i (F₁ + F₃) dx₂ + 2 F₂ dy) / y`. The knowl writes `β₂ = dy/y`, which is not
compatible with its slash operator (`slashTwo`); see the module docstring. -/
noncomputable def weightTwoOneForm (F : ℂ × ℝ → Fin 3 → ℂ) : Fin 3 → ℂ :=
  (p.2 : ℂ)⁻¹ • ![F p 2 - F p 0, -I * (F p 0 + F p 2), 2 * F p 1]

variable {K : Type*} [Field K] (σ : K →+* ℂ) (Γ : Subgroup (GL (Fin 2) (𝓞 K)))
  (F : ℂ × ℝ → Fin 3 → ℂ)

/-- A **weight 2 Bianchi modular form** for `Γ ≤ GL₂(𝒪_K)`, `K` embedded in `ℂ` by `σ`, in the
alternative description of LMFDB `mf.bianchi.weight2`: a function `F : ℋ₃ → ℂ³`, given on
`ℂ × ℝ`, which is real analytic on `ℋ₃`, whose 1-form `F₁β₁ + F₂β₂ + F₃β₃` (`weightTwoOneForm`)
is harmonic and invariant under the pullback by `z ↦ g z` for every `SL(2, ℂ)`-representative `g`
of every element of `Γ`, and of polynomial growth at the cusps. The knowl omits the growth
condition, without which harmonic invariant 1-forms may grow exponentially at the cusps and are
not the weight 2 Bianchi modular forms of LMFDB `mf.bianchi`; it is imposed on the function
`y⁻¹ F` of the convention of `bianchiSlash`, as in `IsBianchiModularForm`. -/
structure IsBianchiWeightTwoForm : Prop where
  /-- `F` is real analytic on `ℋ₃`. -/
  analyticAt (p : ℂ × ℝ) : 0 < p.2 → AnalyticAt ℝ F p
  /-- The 1-form of `F` is harmonic. -/
  harmonic : IsHarmonicOneForm (weightTwoOneForm · F)
  /-- The 1-form of `F` is invariant under `Γ`. -/
  invariant : ∀ γ ∈ Γ, ∀ (g : SL(2, ℂ)) (s : ℂ),
    (g : Matrix (Fin 2) (Fin 2) ℂ) = s⁻¹ • (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map
      (σ.comp (algebraMap (𝓞 K) K)) →
    ∀ p : ℂ × ℝ, 0 < p.2 → oneFormPullback (weightTwoOneForm · F) p g = weightTwoOneForm p F
  /-- `F` has at worst polynomial growth at the cusps, which the knowl omits. -/
  growth : HasPolynomialGrowthAtCusps σ 2 fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords

/-- A weight 2 Bianchi modular form `F` for `Γ`, in the description of LMFDB `mf.bianchi.weight2`
(`IsBianchiWeightTwoForm`), is **cuspidal** (LMFDB `mf.bianchi.weight2`) if the constant term of
`F ∣ γ` vanishes for every `γ ∈ SL₂(𝒪_K)` (`IsCuspidalWeightTwo`, which integrates over the
period lattices of `F ∣ γ`, as the knowl's `∫_{ℂ / 𝒪_K}` is only meaningful for `𝒪_K`-periodic
`F ∣ γ`). -/
def IsCuspidalBianchiWeightTwoForm : Prop :=
  IsBianchiWeightTwoForm σ Γ F ∧ IsCuspidalWeightTwo σ F

variable {F} {G : ℂ × ℝ → Fin 3 → ℂ}

/-- **The 1-form `F₁β₁ + F₂β₂ + F₃β₃` determines `F` on `ℋ₃`.** -/
lemma weightTwoOneForm_injective (hp : 0 < p.2) (h : weightTwoOneForm p F = weightTwoOneForm p G) :
    F p = G p := by
  have hy : (p.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  have h₀ : weightTwoOneForm p F 0 = weightTwoOneForm p G 0 := congrFun h 0
  have h₁ : weightTwoOneForm p F 1 = weightTwoOneForm p G 1 := congrFun h 1
  have h₂ : weightTwoOneForm p F 2 = weightTwoOneForm p G 2 := congrFun h 2
  simp [weightTwoOneForm, hy] at h₀ h₁ h₂
  have e₀ : F p 0 = G p 0 := by linear_combination (h₁ - h₀) / 2
  have e₂ : F p 2 = G p 2 := by linear_combination (h₀ + h₁) / 2
  ext i
  fin_cases i
  exacts [e₀, h₂, e₂]

variable (g : SL(2, ℂ)) (v : ℂ × ℝ)

lemma ofReal_moebiusDenom (q : ℂ × ℝ) : (moebiusDenom g q : ℂ) =
    (g 1 0 * q.1 + g 1 1) * conj (g 1 0 * q.1 + g 1 1) + g 1 0 * conj (g 1 0) * (q.2 : ℂ) ^ 2 := by
  simp only [moebiusDenom, ofReal_add, ofReal_mul, ofReal_pow, ← mul_conj]

private lemma hasDerivAt_line_fst : HasDerivAt (fun t : ℝ ↦ p.1 + (t : ℂ) * v.1) v.1 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v.1).const_add p.1

private lemma hasDerivAt_line_snd :
    HasDerivAt (fun t : ℝ ↦ (p.2 : ℂ) + (t : ℂ) * v.2) (v.2 : ℂ) 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (v.2 : ℂ)).const_add (p.2 : ℂ)

private lemma hasDerivAt_affine_line (a b : ℂ) :
    HasDerivAt (fun t : ℝ ↦ a * (p.1 + t * v.1) + b) (a * v.1) 0 :=
  ((hasDerivAt_line_fst p v).const_mul a).add_const b

private lemma hasDerivAt_moebiusDenom_line : HasDerivAt (fun t : ℝ ↦
    (g 1 0 * (p.1 + t * v.1) + g 1 1) * conj (g 1 0 * (p.1 + t * v.1) + g 1 1) +
      g 1 0 * conj (g 1 0) * ((p.2 : ℂ) + t * v.2) ^ 2)
    (g 1 0 * v.1 * conj (g 1 0 * p.1 + g 1 1) + (g 1 0 * p.1 + g 1 1) * conj (g 1 0 * v.1) +
      2 * g 1 0 * conj (g 1 0) * p.2 * v.2) 0 := by
  have hr : HasDerivAt (fun t : ℝ ↦ g 1 0 * (p.1 + t * v.1) + g 1 1) (g 1 0 * v.1) 0 :=
    hasDerivAt_affine_line p v (g 1 0) (g 1 1)
  convert (hr.mul hr.star).add (((hasDerivAt_line_snd p v).pow 2).const_mul
    (g 1 0 * conj (g 1 0))) using 1
  · funext t
    simp
  · simp
    ring1

private lemma moebiusDenom_line_zero_ne_zero (hp : 0 < p.2) :
    (g 1 0 * (p.1 + (0 : ℝ) * v.1) + g 1 1) * conj (g 1 0 * (p.1 + (0 : ℝ) * v.1) + g 1 1) +
      g 1 0 * conj (g 1 0) * ((p.2 : ℂ) + (0 : ℝ) * v.2) ^ 2 ≠ 0 := by
  simpa [ofReal_moebiusDenom] using ofReal_ne_zero.mpr (moebiusDenom_pos g hp).ne'

private lemma hasDerivAt_moebius_fst_line (hp : 0 < p.2) :
    HasDerivAt (fun t : ℝ ↦ (moebius g (p + t • v)).1)
      ((conj (g 1 0 * p.1 + g 1 1) ^ 2 * v.1 - (conj (g 1 0) * p.2) ^ 2 * conj v.1 +
        2 * conj (g 1 0 * p.1 + g 1 1) * (conj (g 1 0) * p.2) * v.2) /
          (moebiusDenom g p : ℂ) ^ 2) 0 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := g.fin_two_mul_sub_mul_eq_one
  convert (((hasDerivAt_affine_line p v (g 0 0) (g 0 1)).mul
    (hasDerivAt_affine_line p v (g 1 0) (g 1 1)).star).add
      (((hasDerivAt_line_snd p v).pow 2).const_mul (g 0 0 * conj (g 1 0)))).div
        (hasDerivAt_moebiusDenom_line p g v) (moebiusDenom_line_zero_ne_zero p g v hp) using 1
  · funext t
    simp [moebius, ofReal_moebiusDenom]
  · rw [ofReal_moebiusDenom]
    simp
    congr 1
    linear_combination (-((conj (g 1 0) * conj p.1 + conj (g 1 1)) ^ 2 * v.1 -
      conj (g 1 0) ^ 2 * (p.2 : ℂ) ^ 2 * conj v.1 +
        2 * conj (g 1 0) * (conj (g 1 0) * conj p.1 + conj (g 1 1)) * p.2 * v.2)) * hdet

private lemma hasDerivAt_moebius_snd_line (hp : 0 < p.2) :
    HasDerivAt (fun t : ℝ ↦ ((moebius g (p + t • v)).2 : ℂ))
      ((-(g 1 0 * p.2 * conj (g 1 0 * p.1 + g 1 1) * v.1 +
        conj (g 1 0) * p.2 * (g 1 0 * p.1 + g 1 1) * conj v.1) +
          ((g 1 0 * p.1 + g 1 1) * conj (g 1 0 * p.1 + g 1 1) -
            g 1 0 * conj (g 1 0) * (p.2 : ℂ) ^ 2) * v.2) / (moebiusDenom g p : ℂ) ^ 2) 0 := by
  convert (hasDerivAt_line_snd p v).div (hasDerivAt_moebiusDenom_line p g v)
    (moebiusDenom_line_zero_ne_zero p g v hp) using 1
  · funext t
    simp [moebius, ofReal_moebiusDenom]
  · rw [ofReal_moebiusDenom]
    simp
    congr 1
    ring1

private lemma hasDerivAt_line : HasDerivAt (fun t : ℝ ↦ p + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p

lemma fderiv_moebius_apply_fst (hp : 0 < p.2) : (fderiv ℝ (moebius g) p v).1 =
    (conj (g 1 0 * p.1 + g 1 1) ^ 2 * v.1 - (conj (g 1 0) * p.2) ^ 2 * conj v.1 +
      2 * conj (g 1 0 * p.1 + g 1 1) * (conj (g 1 0) * p.2) * v.2) /
        (moebiusDenom g p : ℂ) ^ 2 := by
  have hf : HasFDerivAt (moebius g) (fderiv ℝ (moebius g) p) p :=
    (analyticAt_moebius g hp).differentiableAt.hasFDerivAt
  exact ((ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hf.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line p v) (by simp))).unique
      (hasDerivAt_moebius_fst_line p g v hp)

lemma ofReal_fderiv_moebius_apply_snd (hp : 0 < p.2) : ((fderiv ℝ (moebius g) p v).2 : ℂ) =
    (-(g 1 0 * p.2 * conj (g 1 0 * p.1 + g 1 1) * v.1 +
      conj (g 1 0) * p.2 * (g 1 0 * p.1 + g 1 1) * conj v.1) +
        ((g 1 0 * p.1 + g 1 1) * conj (g 1 0 * p.1 + g 1 1) -
          g 1 0 * conj (g 1 0) * (p.2 : ℂ) ^ 2) * v.2) / (moebiusDenom g p : ℂ) ^ 2 := by
  have hf : HasFDerivAt (moebius g) (fderiv ℝ (moebius g) p) p :=
    (analyticAt_moebius g hp).differentiableAt.hasFDerivAt
  exact ((ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℝ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hf.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line p v) (by simp))).unique
      (hasDerivAt_moebius_snd_line p g v hp)

/-- **`PSL(2, ℂ)` acts on the 1-forms through the slash operator** (LMFDB `mf.bianchi.weight2`): the
pullback of the 1-form `F₁β₁ + F₂β₂ + F₃β₃` by `z ↦ g z` is the 1-form of `F ∣ g` (`slashTwo`), that
is `g^*(β₁, β₂, β₃)ᵗ = (|r|² + |s|²)⁻¹ M ᵗ(β₁, β₂, β₃)` for the knowl's matrix `M`, with
`β = (-dx/y, 2 dy/y, dx̄/y)`. -/
lemma oneFormPullback_weightTwoOneForm (hp : 0 < p.2) :
    oneFormPullback (weightTwoOneForm · F) p g = weightTwoOneForm p (slashTwo F g) := by
  have hN : (moebiusDenom g p : ℂ) ≠ 0 := ofReal_ne_zero.mpr (moebiusDenom_pos g hp).ne'
  have hy : (p.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  have hY : ((moebius g p).2 : ℂ) = (p.2 : ℂ) / (moebiusDenom g p : ℂ) := by
    simp [moebius]
  have hS : ((normSq (g 1 0 * p.1 + g 1 1) + normSq (g 1 0 * (p.2 : ℂ)) : ℝ) : ℂ) =
      (moebiusDenom g p : ℂ) := by
    simp [moebiusDenom, sq]
  have hD : ((normSq (g 1 0 * p.1 + g 1 1) - normSq (g 1 0 * (p.2 : ℂ)) : ℝ) : ℂ) =
      (g 1 0 * p.1 + g 1 1) * conj (g 1 0 * p.1 + g 1 1) -
        g 1 0 * (p.2 : ℂ) * conj (g 1 0 * (p.2 : ℂ)) := by
    simp only [ofReal_sub, ← mul_conj]
  ext j
  simp only [oneFormPullback, weightTwoOneForm, slashTwo, Fin.sum_univ_three, coordFun, hY, hS, hD,
    re_eq_add_conj, im_eq_sub_conj]
  generalize F (moebius g p) = f
  fin_cases j <;>
  · simp [coordVector]
    rw [fderiv_moebius_apply_fst p g _ hp, ofReal_fderiv_moebius_apply_snd p g _ hp]
    simp [vecHead, vecTail, map_ofNat]
    field_simp
    ring1

/-- **The 1-form of `F` is invariant under `g` exactly when `F ∣ g = F`** (LMFDB
`mf.bianchi.weight2`): at a point `p` of `ℋ₃`, `g^*(F₁β₁ + F₂β₂ + F₃β₃) = F₁β₁ + F₂β₂ + F₃β₃`
exactly when `(F ∣ g)(p) = F(p)` for the slash operator `slashTwo` of the knowl. -/
lemma oneFormPullback_weightTwoOneForm_eq_iff (hp : 0 < p.2) :
    oneFormPullback (weightTwoOneForm · F) p g = weightTwoOneForm p F ↔ slashTwo F g p = F p := by
  rw [oneFormPullback_weightTwoOneForm p g hp]
  exact ⟨weightTwoOneForm_injective p hp, fun h ↦ by simp only [weightTwoOneForm, h]⟩

lemma extend_inv_smul (hp : 0 < p.2) : extend (fun z : HyperbolicThreeSpace ↦
    (z.coords.2 : ℂ)⁻¹ • F z.coords) p = (p.2 : ℂ)⁻¹ • F p := by
  rw [extend, dite_eq_left hp]
  rfl

lemma bianchiSlash_two_inv_smul (z : HyperbolicThreeSpace) :
    bianchiSlash 2 g (fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords) z =
      (z.coords.2 : ℂ)⁻¹ • slashTwo F g z.coords := by
  have hN : (moebiusDenom g z.coords : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (moebiusDenom_pos g (coords_snd_pos z)).ne'
  have hY : ((moebius g z.coords).2 : ℂ) = (z.coords.2 : ℂ) / (moebiusDenom g z.coords : ℂ) := by
    simp [moebius]
  rw [bianchiSlash_two, slashTwo, slashTwo,
    extend_inv_smul _ (moebius_snd_pos g (coords_snd_pos z)), hY]
  simp only [mulVec_smul, smul_smul]
  congr 1
  field_simp

/-- **The invariance of `F` under the slash operator of LMFDB `mf.bianchi.weight2` is the invariance
of `y⁻¹ F` under the weight 2 slash operator of LMFDB `mf.bianchi`**: `F ∣ g = F` on `ℋ₃`
(`slashTwo`) exactly when `y⁻¹ F` is fixed by `bianchiSlash 2 g`. -/
lemma bianchiSlash_two_inv_smul_eq_iff :
    bianchiSlash 2 g (fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords) =
      (fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords) ↔ ∀ p : ℂ × ℝ, 0 < p.2 → slashTwo F g p = F p := by
  refine ⟨fun h p hp ↦ ?_, fun h ↦ funext fun z ↦ ?_⟩
  · have h₁ : bianchiSlash 2 g (fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords)
        (.mk (WithLp.toLp 2 p) hp) = (p.2 : ℂ)⁻¹ • F p := congrFun h (.mk (WithLp.toLp 2 p) hp)
    rw [bianchiSlash_two_inv_smul] at h₁
    exact smul_right_injective _ (inv_ne_zero (ofReal_ne_zero.mpr hp.ne')) h₁
  · rw [bianchiSlash_two_inv_smul, h z.coords (coords_snd_pos z)]

/-- **Weight 2 Bianchi modular forms as 1-forms** (LMFDB `mf.bianchi.weight2`): `F` is a weight 2
Bianchi modular form for `Γ` in the description of the knowl exactly when it is real analytic on
`ℋ₃`, its 1-form is harmonic and `y⁻¹ F` is invariant under `Γ` for the weight 2 slash operator
`bianchiSlash 2` of LMFDB `mf.bianchi` (`IsBianchiSlashInvariant`), as for the Bianchi modular
forms `IsBianchiModularForm` of weight `2`. -/
lemma isBianchiWeightTwoForm_iff : IsBianchiWeightTwoForm σ Γ F ↔
    (∀ p : ℂ × ℝ, 0 < p.2 → AnalyticAt ℝ F p) ∧ IsHarmonicOneForm (weightTwoOneForm · F) ∧
      IsBianchiSlashInvariant σ Γ 2 (fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords) ∧
        HasPolynomialGrowthAtCusps σ 2 fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords := by
  refine ⟨fun hF ↦ ⟨hF.analyticAt, hF.harmonic, fun γ hγ g s hg ↦ ?_, hF.growth⟩,
    fun hF ↦ ⟨hF.1, hF.2.1, fun γ hγ g s hg p hp ↦ ?_, hF.2.2.2⟩⟩
  · exact (bianchiSlash_two_inv_smul_eq_iff g).mpr fun p hp ↦
      (oneFormPullback_weightTwoOneForm_eq_iff p g hp).mp (hF.invariant γ hγ g s hg p hp)
  · exact (oneFormPullback_weightTwoOneForm_eq_iff p g hp).mpr
      ((bianchiSlash_two_inv_smul_eq_iff g).mp (hF.2.2.1 γ hγ g s hg) p hp)

lemma analyticAt_iff_analyticAt_extend_inv_smul : (∀ p : ℂ × ℝ, 0 < p.2 → AnalyticAt ℝ F p) ↔
    ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ
      (extend fun z : HyperbolicThreeSpace ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords) z.coords := by
  have hU (p : ℂ × ℝ) (hp : 0 < p.2) : ∀ᶠ q in nhds p, 0 < q.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  refine ⟨fun hF z ↦ ?_, fun hF p hp ↦ ?_⟩
  · have h : AnalyticAt ℝ (fun q : ℂ × ℝ ↦ (q.2 : ℂ)⁻¹ • F q) z.coords := by
      have hy : (z.coords.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (coords_snd_pos z).ne'
      have hFz : AnalyticAt ℝ F z.coords := hF z.coords (coords_snd_pos z)
      fun_prop (disch := exact hy)
    refine h.congr ?_
    filter_upwards [hU _ (coords_snd_pos z)] with q hq
    exact (extend_inv_smul q hq).symm
  · have hE : AnalyticAt ℝ (extend fun z : HyperbolicThreeSpace ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords)
        p := hF (.mk (WithLp.toLp 2 p) hp)
    have h : AnalyticAt ℝ (fun q : ℂ × ℝ ↦ (q.2 : ℂ) •
        extend (fun z : HyperbolicThreeSpace ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords) q) p := by
      fun_prop
    refine h.congr ?_
    filter_upwards [hU p hp] with q hq
    rw [extend_inv_smul q hq, smul_inv_smul₀ (ofReal_ne_zero.mpr hq.ne')]

/-- **The alternative description of weight 2 forms agrees with the general one, up to
harmonicity**: if the harmonicity of the 1-form `F₁β₁ + F₂β₂ + F₃β₃` is equivalent to the
harmonicity `IsBianchiHarmonic 2` of `y⁻¹ F` (the Casimir equations of LMFDB `mf.bianchi`, a
hypothesis here, not proved), then `F` is a weight 2 Bianchi modular form for `Γ` in the
description of LMFDB `mf.bianchi.weight2` exactly when `y⁻¹ F` is a Bianchi modular form of weight
`2` for `Γ` (`IsBianchiModularForm`). -/
lemma isBianchiWeightTwoForm_iff_isBianchiModularForm
    (h : IsHarmonicOneForm (weightTwoOneForm · F) ↔
      IsBianchiHarmonic 2 fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords) :
    IsBianchiWeightTwoForm σ Γ F ↔
      IsBianchiModularForm σ Γ 2 fun z ↦ (z.coords.2 : ℂ)⁻¹ • F z.coords := by
  rw [isBianchiWeightTwoForm_iff, analyticAt_iff_analyticAt_extend_inv_smul, h]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₃, h₂, h₄⟩,
    fun hF ↦ ⟨hF.analyticAt, hF.harmonic, hF.invariant, hF.growth⟩⟩

end HyperbolicThreeSpace
