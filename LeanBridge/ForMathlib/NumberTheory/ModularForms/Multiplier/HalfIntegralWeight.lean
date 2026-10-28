import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.Weight
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Modular forms of half-integral weight

For an odd integer `k`, a positive integer `N` divisible by `4` and a Dirichlet character `χ`
modulo `N`, a modular form of weight `k/2`, level `N` and character `χ` is a holomorphic function
`f : ℍ → ℂ` with `f(γz) = χ(d) j(γ, z)^k f(z)` for every `γ = (a, b; c, d) ∈ Γ₀(N)`, where `j` is
the theta multiplier, which is holomorphic at the cusps. Holomorphy at the cusp `γ∞` of the
weight-`k/2` form `f` means that `|cz + d|^(-k/2) |f(γz)|` is bounded as `Im z → ∞`; for cusp forms
it tends to `0`.

## Main definitions

* `ModularForm.halfIntegralWeightSlash`: the function `z ↦ |cz + d|^(-k/2) f(γz)`.
* `ModularForm.halfIntegralWeightSpace` (LMFDB `mf.half_integral_weight`): `M_{k/2}(N, χ)`.
* `ModularForm.halfIntegralWeightCuspSpace` (LMFDB `mf.half_integral_weight`): `S_{k/2}(N, χ)`.

## Main results

* `ModularForm.hasWeight_of_mem_halfIntegralWeightSpace`: the forms in `M_{k/2}(N, χ)` have weight
  `k/2` in the sense of `ModularForm.HasWeight`.
-/

open UpperHalfPlane CongruenceSubgroup Matrix SpecialLinearGroup

open scoped MatrixGroups Manifold

namespace ModularForm

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ) (γ : SL(2, ℤ)) {f g : ℍ → ℂ}

variable (f) in
/-- The function `z ↦ |cz + d|^(-k/2) f(γz)` for `γ = (a, b; c, d) ∈ SL(2, ℤ)`: up to a factor of
absolute value `1`, the slash of `f` by `γ` in weight `k/2`, whatever branch of `(cz + d)^(k/2)`
is chosen. -/
noncomputable def halfIntegralWeightSlash (z : ℍ) : ℂ :=
  (‖denom γ z‖ ^ (-(k / 2 : ℝ)) : ℝ) * f (γ • z)

lemma halfIntegralWeightSlash_zero : halfIntegralWeightSlash k γ 0 = 0 := by
  ext z
  simp [halfIntegralWeightSlash]

lemma halfIntegralWeightSlash_add :
    halfIntegralWeightSlash k γ (f + g) =
      halfIntegralWeightSlash k γ f + halfIntegralWeightSlash k γ g := by
  ext z
  simp [halfIntegralWeightSlash, mul_add]

lemma halfIntegralWeightSlash_smul (a : ℂ) :
    halfIntegralWeightSlash k γ (a • f) = a • halfIntegralWeightSlash k γ f := by
  ext z
  simp [halfIntegralWeightSlash, mul_left_comm]

/-- The space `M_{k/2}(N, χ)` of **modular forms of half-integral weight** `k/2` (LMFDB
`mf.half_integral_weight`), level `N` and character `χ`: the holomorphic `f : ℍ → ℂ` with
`f(γz) = χ(d) j(γ, z)^k f(z)` for every `γ = (a, b; c, d) ∈ Γ₀(N)` and `z ∈ ℍ`, where `j` is
Shimura's theta multiplier `ModularForm.thetaFactor`, that are holomorphic at the cusps: for every
`γ ∈ SL(2, ℤ)`, `|cz + d|^(-k/2) f(γz)` is bounded as `Im z → ∞`. The LMFDB requires `k` odd and
`4 ∣ N` (`hasWeight_of_mem_halfIntegralWeightSpace`); the space is defined for all `k` and `N`.

The LMFDB defines `j(γ, z) = θ(γz) / θ(z)` with `θ(z) = Σ_n e^{2πin²z}`; Shimura's formula
`j(γ, z) = (c/d) ε_d⁻¹ (cz + d)^(1/2)` for `γ ∈ Γ₀(4)` is used instead, its equality with the
quotient of theta functions being a theorem that is not proved here. -/
def halfIntegralWeightSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | MDiff f ∧
    (∀ γ ∈ Gamma0 N, ∀ z, f (γ • z) = χ (γ 1 1) * weightFactor k γ z * f z) ∧
      ∀ γ, IsBoundedAtImInfty (halfIntegralWeightSlash k γ f)}
  add_mem' hf hg := ⟨hf.1.add hg.1, fun γ hγ z ↦ by
    rw [Pi.add_apply, Pi.add_apply, hf.2.1 γ hγ z, hg.2.1 γ hγ z, mul_add],
    fun γ ↦ by
      rw [halfIntegralWeightSlash_add]
      exact (hf.2.2 γ).add (hg.2.2 γ)⟩
  zero_mem' := ⟨mdifferentiable_const, fun γ _ z ↦ by simp, fun γ ↦ by
    rw [halfIntegralWeightSlash_zero]
    exact zero_form_isBoundedAtImInfty⟩
  smul_mem' a f hf := ⟨hf.1.const_smul a, fun γ hγ z ↦ by
    rw [Pi.smul_apply, Pi.smul_apply, hf.2.1 γ hγ z, smul_eq_mul, smul_eq_mul, mul_left_comm],
    fun γ ↦ by
      rw [halfIntegralWeightSlash_smul]
      exact (hf.2.2 γ).smul a⟩

/-- The space `S_{k/2}(N, χ)` of **cusp forms of half-integral weight** `k/2` (LMFDB
`mf.half_integral_weight`), level `N` and character `χ`: the `f ∈ M_{k/2}(N, χ)` that vanish at
the cusps, that is, `|cz + d|^(-k/2) f(γz) → 0` as `Im z → ∞` for every `γ ∈ SL(2, ℤ)`. -/
def halfIntegralWeightCuspSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | f ∈ halfIntegralWeightSpace χ k ∧
    ∀ γ, IsZeroAtImInfty (halfIntegralWeightSlash k γ f)}
  add_mem' hf hg := ⟨add_mem hf.1 hg.1, fun γ ↦ by
    rw [halfIntegralWeightSlash_add]
    exact (hf.2 γ).add (hg.2 γ)⟩
  zero_mem' := ⟨zero_mem _, fun γ ↦ by
    rw [halfIntegralWeightSlash_zero]
    exact Filter.zero_zeroAtFilter _⟩
  smul_mem' a f hf := ⟨Submodule.smul_mem _ a hf.1, fun γ ↦ by
    rw [halfIntegralWeightSlash_smul]
    exact (hf.2 γ).smul a⟩

/-- **The forms of `M_{k/2}(N, χ)` have weight `k/2`**: for odd `k` and `4 ∣ N` they satisfy the
transformation law of weight `k/2` of `ModularForm.HasWeight`. -/
lemma hasWeight_of_mem_halfIntegralWeightSpace (hf : f ∈ halfIntegralWeightSpace χ k)
    (hN : 4 ∣ N) : HasWeight f N χ (k / 2) :=
  ⟨k, by ring1, fun _ ↦ hN, hf.2.1⟩

end ModularForm
