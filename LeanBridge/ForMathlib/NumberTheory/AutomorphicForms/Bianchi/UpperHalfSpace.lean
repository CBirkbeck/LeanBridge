import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic

/-!
# The action of `SL(2, ℂ)` on hyperbolic 3-space

Hyperbolic 3-space `ℋ₃ = {(x, y) ∈ ℂ × ℝ | y > 0}`, with the metric `(dx₁² + dx₂² + dy²) / y²`
where `x = x₁ + i x₂`, is Tau Ceti's upper half-space model `TauCeti.UpperHalfSpace ℂ` (LMFDB
`mf.bianchi.hyperbolic3space`). This file adds the action of `SL(2, ℂ)` on it by the explicit
formula of the LMFDB, the induced action of the Picard group `PSL(2, ℤ[i])`, the hyperbolic volume
and the hyperbolic Laplacian in coordinates.

## Main definitions

* `HyperbolicThreeSpace`: a name for `TauCeti.UpperHalfSpace ℂ`.
* `HyperbolicThreeSpace.moebius`: the action `(x, y) ↦ γ · (x, y)` of `SL(2, ℂ)` in coordinates.
* The instances `SMul SL(2, ℂ) HyperbolicThreeSpace` and
  `SMul (Matrix.ProjectiveSpecialLinearGroup (Fin 2) GaussianInt) HyperbolicThreeSpace`.
* `HyperbolicThreeSpace.hyperbolicVolume`: the measure `dx₁ dx₂ dy / y³`.
* `HyperbolicThreeSpace.laplacian` (LMFDB `mf.maass.picard.laplacian`).
-/

open Complex Matrix MeasureTheory TauCeti WithLp
open scoped ComplexConjugate MatrixGroups

/-- Hyperbolic 3-space `ℋ₃`, the upper half-space `{(x, y) ∈ ℂ × ℝ | y > 0}` with the metric
`(dx₁² + dx₂² + dy²) / y²`, where `x = x₁ + i x₂`: Tau Ceti's upper half-space model
`TauCeti.UpperHalfSpace ℂ`. -/
abbrev HyperbolicThreeSpace : Type :=
  UpperHalfSpace ℂ

namespace HyperbolicThreeSpace

variable (γ : SL(2, ℂ)) (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) (z : HyperbolicThreeSpace)

instance : MeasurableSpace HyperbolicThreeSpace :=
  inferInstanceAs <| MeasurableSpace (upperHalfSpaceOpens ℂ)

/-- The coordinates `(x, y) ∈ ℂ × ℝ` of a point `z` of hyperbolic 3-space. -/
noncomputable def coords : ℂ × ℝ :=
  ofLp (z : WithLp 2 (ℂ × ℝ))

lemma coords_injective : Function.Injective coords :=
  fun _ _ h ↦ UpperHalfSpace.ext <| congrArg (toLp 2) h

lemma measurableEmbedding_coords : MeasurableEmbedding coords :=
  (MeasurableEquiv.toLp 2 (ℂ × ℝ)).symm.measurableEmbedding.comp <|
    .subtype_coe (upperHalfSpaceOpens ℂ).isOpen.measurableSet

/-- The denominator `|cx + d|² + |c|² y²` of the action of `γ = (a, b; c, d) ∈ SL(2, ℂ)` at
`p = (x, y)`. -/
noncomputable def moebiusDenom : ℝ :=
  normSq (γ 1 0 * p.1 + γ 1 1) + normSq (γ 1 0) * p.2 ^ 2

/-- The action `γ · (x, y) = (((ax + b) conj(cx + d) + a conj(c) y²) / N, y / N)`, where
`N = |cx + d|² + |c|² y²`, of `γ = (a, b; c, d) ∈ SL(2, ℂ)` on `ℂ × ℝ`, as in the LMFDB
(`mf.bianchi.hyperbolic3space`). On hyperbolic 3-space it is the action `z ↦ (az + b)(cz + d)⁻¹`
of `SL(2, ℂ)` in the quaternions, where `z = x + yj`. -/
noncomputable def moebius : ℂ × ℝ :=
  (((γ 0 0 * p.1 + γ 0 1) * conj (γ 1 0 * p.1 + γ 1 1) + γ 0 0 * conj (γ 1 0) * (p.2 ^ 2 : ℝ)) /
    (moebiusDenom γ p : ℂ), p.2 / moebiusDenom γ p)

variable {p} in
lemma moebiusDenom_pos (hp : 0 < p.2) : 0 < moebiusDenom γ p := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hd : γ 1 1 ≠ 0 := by
      intro hd
      have h : (γ : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := γ.det_coe
      rw [det_fin_two, hc, hd] at h
      simp at h
    simpa [moebiusDenom, hc] using normSq_pos.mpr hd
  · exact add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (normSq_pos.mpr hc) (by positivity))

noncomputable instance : SMul SL(2, ℂ) HyperbolicThreeSpace where
  smul γ z := .mk (toLp 2 (moebius γ z.coords)) <| div_pos z.height_pos <|
    moebiusDenom_pos γ z.height_pos

lemma coords_smul : (γ • z).coords = moebius γ z.coords :=
  rfl

variable {γ} in
lemma moebius_eq_of_coe_eq_smul {γ' : SL(2, ℂ)} {s : ℂ} (hs : normSq s = 1)
    (h : (γ' : Matrix (Fin 2) (Fin 2) ℂ) = s • (γ : Matrix (Fin 2) (Fin 2) ℂ)) :
    moebius γ' p = moebius γ p := by
  have h' : ∀ i j, γ' i j = s * γ i j := fun i j ↦ by rw [h]; rfl
  have hs' : s * conj s = 1 := by rw [mul_conj, hs, ofReal_one]
  have e : s * γ 1 0 * p.1 + s * γ 1 1 = s * (γ 1 0 * p.1 + γ 1 1) := by ring1
  have hD : moebiusDenom γ' p = moebiusDenom γ p := by
    simp only [moebiusDenom, h', e, normSq_mul, hs, one_mul]
  have hN : (γ' 0 0 * p.1 + γ' 0 1) * conj (γ' 1 0 * p.1 + γ' 1 1) +
      γ' 0 0 * conj (γ' 1 0) * (p.2 ^ 2 : ℝ) = (γ 0 0 * p.1 + γ 0 1) * conj (γ 1 0 * p.1 + γ 1 1) +
      γ 0 0 * conj (γ 1 0) * (p.2 ^ 2 : ℝ) := by
    simp only [h', e, map_mul]
    linear_combination ((γ 0 0 * p.1 + γ 0 1) * conj (γ 1 0 * p.1 + γ 1 1) +
      γ 0 0 * conj (γ 1 0) * (p.2 ^ 2 : ℝ)) * hs'
  rw [moebius, moebius, hN, hD]

/-- `SL(2, ℤ[i])` inside `SL(2, ℂ)`. -/
noncomputable abbrev gaussianIntToSL2C : SL(2, GaussianInt) →* SL(2, ℂ) :=
  SpecialLinearGroup.map GaussianInt.toComplex

variable (a b : SL(2, GaussianInt))

variable {a b} in
private lemma moebius_eq_of_inv_mul_mem_center
    (hab : a⁻¹ * b ∈ Subgroup.center SL(2, GaussianInt)) :
    moebius (gaussianIntToSL2C b) p = moebius (gaussianIntToSL2C a) p := by
  rw [SpecialLinearGroup.mem_center_iff] at hab
  rcases hab with ⟨r, hr, hrab⟩
  refine moebius_eq_of_coe_eq_smul p (s := GaussianInt.toComplex r) ?_ ?_
  · have h2 : normSq (GaussianInt.toComplex r) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, ← Fintype.card_fin 2, hr, map_one, map_one]
    exact (pow_eq_one_iff_of_nonneg (normSq_nonneg _) two_ne_zero).mp h2
  · have hb : (b : Matrix (Fin 2) (Fin 2) GaussianInt) = a * scalar (Fin 2) r := by
      rw [hrab, ← SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    ext i j
    fin_cases j <;> simp [hb, mul_comm]

noncomputable instance : SMul (ProjectiveSpecialLinearGroup (Fin 2) GaussianInt)
    HyperbolicThreeSpace where
  smul g z := Quotient.liftOn' g (gaussianIntToSL2C · • z) fun _ _ hab ↦
    coords_injective (moebius_eq_of_inv_mul_mem_center z.coords
      (QuotientGroup.leftRel_apply.mp hab)).symm

lemma mk_smul : (QuotientGroup.mk a : ProjectiveSpecialLinearGroup (Fin 2) GaussianInt) • z =
    gaussianIntToSL2C a • z :=
  rfl

/-- The hyperbolic volume `dx₁ dx₂ dy / y³` on hyperbolic 3-space, where `x = x₁ + i x₂`: the
Lebesgue measure of `ℂ × ℝ`, pulled back along the coordinates (`measurableEmbedding_coords`), with
density `y⁻³`. -/
noncomputable def hyperbolicVolume : Measure HyperbolicThreeSpace :=
  (volume.comap coords).withDensity fun z ↦ ENNReal.ofReal (z.height ^ 3)⁻¹

/-- The second derivative `∂²f/∂v²` of `f : ℂ × ℝ → ℂ` in the direction `v` at `p`. -/
noncomputable def secondDeriv (v : ℂ × ℝ) : ℂ :=
  fderiv ℝ (fun q ↦ fderiv ℝ f q v) p v

/-- The **hyperbolic Laplacian** (LMFDB `mf.maass.picard.laplacian`)
`Δ = y² (∂²/∂x₁² + ∂²/∂x₂² + ∂²/∂y²) - y ∂/∂y` of a function `f(x, y)` on hyperbolic 3-space, where
`x = x₁ + i x₂`: the Laplace–Beltrami operator of the metric `(dx₁² + dx₂² + dy²) / y²`, with the
sign making it negative semi-definite. The function is given on `ℂ × ℝ`; only its values near `p`
matter. -/
noncomputable def laplacian : ℂ :=
  (p.2 ^ 2 : ℝ) * (secondDeriv f p (1, 0) + secondDeriv f p (I, 0) + secondDeriv f p (0, 1)) -
    p.2 * fderiv ℝ f p (0, 1)

end HyperbolicThreeSpace
