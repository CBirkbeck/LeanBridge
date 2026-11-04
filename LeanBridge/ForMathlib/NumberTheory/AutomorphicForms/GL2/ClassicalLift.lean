import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.AutomorphicFormSpace
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.StrongApproximation
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.Bounds
import TauCeti.NumberTheory.ModularForms.Conjugate

/-!
# The adelic lift of a classical modular form

Let `N ≥ 1` and `k` be integers, and `f` a function on the upper half plane `ℍ` invariant under
`Γ₁(N)` in weight `k`, for instance a cusp form of level `Γ₁(N)`. Its **adelic lift** is the
function `φ_f` on `GL₂(𝔸_ℚ)` given by `φ_f(γ x u) = Φ_f(x)` for `γ ∈ GL₂(ℚ)`, `x ∈ GL₂(ℝ)` and
`u ∈ K₁(N)`, where `Φ_f(x) = det(x) ^ (1 - k / 2) (f ∣[k] x)(i)` when `det x > 0` and
`Φ_f(x) = Φ_f(J x)` when `det x < 0`, for `J = diag(-1, 1)`. Every element of `GL₂(𝔸_ℚ)` has such a
decomposition, since `GL₂(𝔸_ℚ^f) = GL₂(ℚ)⁺ K₁(N)` by strong approximation
(`AdelicGL2.rat_exists_eq_mul_levelOne`), and `φ_f` does not depend on it, since
`GL₂(ℚ)⁺ ∩ K₁(N) = Γ₁(N)` (`AdelicGL2.mem_gamma1_of_mem_levelOne`): this is the master formula
`AdelicGL2.adelicLift_apply`. With Mathlib's slash operator, which carries the factor
`|det x| ^ (k - 1)`, the normalisation makes `Φ_f` invariant under the positive scalars, and
`Φ_f(x) = det(x) ^ (k / 2) (c i + d) ^ (-k) f(x i)` for `x = (a, b; c, d)` of positive determinant.

This file proves that `φ_f` is left invariant under `GL₂(ℚ)` and right invariant under `K₁(N)`,
that it is `K_∞`-finite, that it is smooth in the archimedean variable when `f` is holomorphic, and
that it is bounded, so of moderate growth, when `f` is a cusp form. Its Casimir eigenvalue, its
central character, its cuspidality and its Hecke eigenvalues are in the files
`ClassicalLiftCasimir`, `ClassicalLiftCentral`, `ClassicalLiftCuspidal` and `ClassicalLiftHecke`.

## Main definitions

* `AdelicGL2.posDet`: the matrix `x` or `J x`, whichever has positive determinant.
* `AdelicGL2.normalizedSlash`: the value `|det x| ^ (1 - k / 2) (f ∣[k] x)(i)`.
* `AdelicGL2.classicalFun`: the function `Φ_f` on `GL₂(ℝ)`.
* `AdelicGL2.ratJ`: the matrix `J = diag(-1, 1)` of `GL₂(ℚ)`.
* `AdelicGL2.liftGlobal`: a choice of the rational part of the decomposition `γ x u`.
* `AdelicGL2.adelicLift`: the adelic lift `φ_f`.
* `AdelicGL2.explicitFun`: the explicit formula of `Φ_f` on the real matrices.

## Main results

* `AdelicGL2.classicalFun_map_mul`: `Φ_f(δ x) = Φ_f(x)` for `δ ∈ GL₂(ℚ)` with finite component in
  `K₁(N)`.
* `AdelicGL2.adelicLift_apply`: the master formula `φ_f(γ x u) = Φ_f(x)`.
* `AdelicGL2.exists_eq_ofGlobal_mul_ofInf_mul_ofFin_of_pos`: every element of `GL₂(𝔸_ℚ)` is `γ x u`
  with `det x > 0`.
* `AdelicGL2.isKFinite_adelicLift`: `φ_f` is `K_∞`-finite.
* `AdelicGL2.isSmoothOnGL_classicalFun`, `AdelicGL2.isSmoothAtInfinity_adelicLift`: smoothness, for
  a holomorphic `f`.
* `AdelicGL2.exists_norm_adelicLift_le`, `AdelicGL2.hasModerateGrowth_adelicLift`: the adelic lift
  of a cusp form is bounded, so of moderate growth.
-/

open IsDedekindDomain NumberField UpperHalfPlane

open Matrix hiding mul_inv_rev one_zpow zpow_mul zpow_neg

open mixedEmbedding (mixedSpace)

open scoped AdeleRing Classical Manifold MatrixGroups ModularForm

namespace AdelicGL2

section Real

variable (k : ℤ) (f : ℍ → ℂ) {h h' m γ : GL (Fin 2) ℝ}

variable (h) in
/-- The matrix `h` or `J h`, whichever has positive determinant, for `J = diag(-1, 1)`. -/
noncomputable def posDet : GL (Fin 2) ℝ :=
  if 0 < (h.det : ℝ) then h else J * h

variable (h) in
/-- The value `|det h| ^ (1 - k / 2) (f ∣[k] h)(i)` at the point `i` of the slash `f ∣[k] h`, for
Mathlib's slash operator, normalised so as to be invariant under the positive scalars. -/
noncomputable def normalizedSlash : ℂ :=
  ((Real.sqrt |(h.det : ℝ)| ^ (2 - k) : ℝ) : ℂ) * (f ∣[k] h) I

variable (h) in
/-- The **function `Φ_f` on `GL₂(ℝ)` attached to a function `f` on `ℍ`** in weight `k`:
`h ↦ det(h) ^ (1 - k / 2) (f ∣[k] h)(i)` when `det h > 0`, and its value at `J h` when `det h < 0`,
for `J = diag(-1, 1)`. -/
noncomputable def classicalFun : ℂ :=
  normalizedSlash k f (posDet h)

lemma posDet_of_pos (hh : 0 < (h.det : ℝ)) : posDet h = h :=
  ite_eq_left hh

lemma posDet_of_neg (hh : (h.det : ℝ) < 0) : posDet h = J * h :=
  ite_eq_right (not_lt.mpr hh.le)

lemma det_J_mul : ((J * h).det : ℝ) = -(h.det : ℝ) := by
  rw [map_mul, Units.val_mul, det_J]
  simp

lemma J_mul_J : J * J = 1 := by
  rw [← sq, J_sq]

variable (h) in
lemma posDet_J_mul : posDet (J * h) = posDet h := by
  rcases (h.det.ne_zero : (h.det : ℝ) ≠ 0).lt_or_gt with hh | hh
  · rw [posDet_of_neg hh, posDet_of_pos (by rw [det_J_mul]; linarith)]
  · rw [posDet_of_pos hh, posDet_of_neg (by rw [det_J_mul]; linarith), ← mul_assoc, J_mul_J,
      one_mul]

variable (h) in
lemma classicalFun_J_mul : classicalFun k f (J * h) = classicalFun k f h := by
  rw [classicalFun, classicalFun, posDet_J_mul]

variable (h) in
lemma det_posDet_pos : 0 < ((posDet h).det : ℝ) := by
  rcases (h.det.ne_zero : (h.det : ℝ) ≠ 0).lt_or_gt with hh | hh
  · rw [posDet_of_neg hh, det_J_mul]
    linarith
  · rw [posDet_of_pos hh]
    exact hh

lemma classicalFun_of_pos (hh : 0 < (h.det : ℝ)) : classicalFun k f h = normalizedSlash k f h := by
  rw [classicalFun, posDet_of_pos hh]

variable (h h') in
lemma normalizedSlash_mul : normalizedSlash k f (h * h') =
    ((Real.sqrt |(h.det : ℝ)| ^ (2 - k) : ℝ) : ℂ) * normalizedSlash k (f ∣[k] h) h' := by
  rw [normalizedSlash, normalizedSlash, SlashAction.slash_mul, map_mul, Units.val_mul, abs_mul,
    Real.sqrt_mul (abs_nonneg _), mul_zpow, Complex.ofReal_mul, mul_assoc]

variable {f}

lemma normalizedSlash_of_pos (hh : 0 < (h.det : ℝ)) : normalizedSlash k f h =
    ((Real.sqrt (h.det : ℝ) ^ k : ℝ) : ℂ) * denom h I ^ (-k) * f (h • I) := by
  have hs : Real.sqrt (h.det : ℝ) ^ (2 - k) * (h.det : ℝ) ^ (k - 1) =
      Real.sqrt (h.det : ℝ) ^ k := by
    have h₀ : Real.sqrt (h.det : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
    have h₁ : (h.det : ℝ) ^ (k - 1) = Real.sqrt (h.det : ℝ) ^ (2 * (k - 1)) := by
      rw [zpow_mul, zpow_two, Real.mul_self_sqrt hh.le]
    rw [h₁, ← zpow_add₀ h₀]
    congr 1
    ring1
  rw [normalizedSlash, ModularForm.slash_apply_of_det_pos k hh, abs_of_pos hh, ← hs]
  push_cast
  ring1

lemma norm_normalizedSlash (hh : 0 < (h.det : ℝ)) :
    ‖normalizedSlash k f h‖ = (h • I).im ^ (k / 2 : ℝ) * ‖f (h • I)‖ := by
  have him : (h • I).im = (h.det : ℝ) / ‖denom h I‖ ^ 2 := by
    rw [im_smul_eq_div_normSq, abs_of_pos hh, I_im, mul_one, Complex.normSq_eq_norm_sq]
  have h₁ : (h.det : ℝ) ^ (k / 2 : ℝ) = Real.sqrt (h.det : ℝ) ^ k := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hh.le]
    congr 1
    ring1
  have h₂ : (‖denom h I‖ ^ 2) ^ (k / 2 : ℝ) = ‖denom h I‖ ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]
    congr 1
    push_cast
    ring1
  have hr : (h • I).im ^ (k / 2 : ℝ) = Real.sqrt (h.det : ℝ) ^ k * ‖denom h I‖ ^ (-k) := by
    rw [him, Real.div_rpow hh.le (by positivity), h₁, h₂, div_eq_mul_inv, zpow_neg]
  rw [normalizedSlash_of_pos k hh, norm_mul, norm_mul, norm_zpow, Complex.norm_real,
    Real.norm_of_nonneg (zpow_nonneg (Real.sqrt_nonneg _) _), hr]

lemma normalizedSlash_mul_of_slash_eq (hγ : f ∣[k] γ = f) (hd : |(γ.det : ℝ)| = 1) :
    normalizedSlash k f (γ * h) = normalizedSlash k f h := by
  rw [normalizedSlash_mul, hγ, hd, Real.sqrt_one]
  simp

lemma classicalFun_mul_of_slash_eq (hd : (γ.det : ℝ) = 1) (h₁ : f ∣[k] γ = f)
    (h₂ : f ∣[k] (J * γ * J) = f) : classicalFun k f (γ * h) = classicalFun k f h := by
  have hd₁ : |(γ.det : ℝ)| = 1 := by
    rw [hd, abs_one]
  rcases (h.det.ne_zero : (h.det : ℝ) ≠ 0).lt_or_gt with hh | hh
  · have hh' : ((γ * h).det : ℝ) < 0 := by
      rw [map_mul, Units.val_mul, hd, one_mul]
      exact hh
    have hd₂ : |((J * γ * J).det : ℝ)| = 1 := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, det_J, hd]
      simp
    have hJ : J * (γ * h) = J * γ * J * (J * h) := by
      rw [mul_assoc (J * γ), ← mul_assoc J J, J_mul_J, one_mul, mul_assoc]
    rw [classicalFun, classicalFun, posDet_of_neg hh, posDet_of_neg hh', hJ,
      normalizedSlash_mul_of_slash_eq k h₂ hd₂]
  · have hh' : 0 < ((γ * h).det : ℝ) := by
      rw [map_mul, Units.val_mul, hd, one_mul]
      exact hh
    rw [classicalFun_of_pos k f hh, classicalFun_of_pos k f hh',
      normalizedSlash_mul_of_slash_eq k h₁ hd₁]

lemma posDet_mul_of_pos (hm : 0 < (m.det : ℝ)) : posDet (h * m) = posDet h * m := by
  rcases (h.det.ne_zero : (h.det : ℝ) ≠ 0).lt_or_gt with hh | hh
  · rw [posDet_of_neg hh, posDet_of_neg (by rw [map_mul, Units.val_mul]; nlinarith), mul_assoc]
  · rw [posDet_of_pos hh, posDet_of_pos (by rw [map_mul, Units.val_mul]; positivity)]

variable (f h) in
lemma classicalFun_mul_of_smul_I (hm : (m.det : ℝ) = 1) (hI : m • I = I) :
    classicalFun k f (h * m) = denom m I ^ (-k) * classicalFun k f h := by
  have hm₀ : 0 < (m.det : ℝ) := by
    rw [hm]
    exact one_pos
  rw [classicalFun, classicalFun, posDet_mul_of_pos hm₀, normalizedSlash_mul, normalizedSlash,
    normalizedSlash, ModularForm.slash_apply_of_det_pos k hm₀, hI, hm, abs_one, Real.sqrt_one]
  simp only [one_zpow, Complex.ofReal_one]
  ring1

lemma smul_I_of_transpose_mul_self (hm : (m : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * m = 1)
    (hd : (m.det : ℝ) = 1) : m • I = I := by
  have e (i j : Fin 2) : m 0 i * m 0 j + m 1 i * m 1 j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    rw [← hm, Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  have e₀₀ : m 0 0 * m 0 0 + m 1 0 * m 1 0 = 1 := e 0 0
  have e₀₁ : m 0 0 * m 0 1 + m 1 0 * m 1 1 = 0 := e 0 1
  have ed : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
    rw [← hd, GeneralLinearGroup.val_det_apply, det_fin_two]
  refine (gl_smul_I_eq_I_iff_of_pos (hd ▸ one_pos)).mpr ⟨?_, ?_⟩
  · linear_combination m 1 1 * e₀₀ - m 1 0 * e₀₁ - m 0 0 * ed
  · linear_combination (-m 0 1) * e₀₀ + m 0 0 * e₀₁ - m 1 0 * ed

end Real

section Rat

variable (k : ℤ) {f : ℍ → ℂ} {N : ℕ} [NeZero N] {δ : GL (Fin 2) ℚ} (h : GL (Fin 2) ℝ)

/-- The matrix `J = diag(-1, 1)` of `GL₂(ℚ)`. -/
noncomputable def ratJ : GL (Fin 2) ℚ :=
  diagHom (-1)

lemma map_ratJ_real : GeneralLinearGroup.map (algebraMap ℚ ℝ) ratJ = J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratJ, diagHom]

lemma map_ratJ_mem_levelOne {𝔑 : Ideal (𝓞 ℚ)} :
    GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) ratJ ∈ levelOne 𝔑 := by
  rw [ratJ, map_diagHom]
  refine diagFin_mem_levelOne fun v ↦ ?_
  have h₁ : (-1 : 𝔸ᶠ[ℚ]) v = -1 := rfl
  simp [h₁]

lemma det_ratJ : (ratJ.det : ℚ) = -1 := by
  simp [ratJ, det_diagHom]

lemma classicalFun_map_mul_of_pos
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    (hd : 0 < (δ.det : ℚ))
    (hδ : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) δ ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)})) :
    classicalFun k f (GeneralLinearGroup.map (algebraMap ℚ ℝ) δ * h) = classicalFun k f h := by
  rcases mem_gamma1_of_mem_levelOne N hd hδ with ⟨g, hg, rfl⟩
  rw [SpecialLinearGroup.map_mapGL]
  refine classicalFun_mul_of_slash_eq k ?_ (hf g hg) ?_
  · simp
  · rw [SpecialLinearGroup.J_mul_mapGL_mul_J]
    exact hf _ (TauCeti.conjJ_mem_Gamma1 hg)

/-- **`Φ_f` is invariant under the rational matrices of level `K₁(N)`**: `Φ_f(δ x) = Φ_f(x)` for
`δ ∈ GL₂(ℚ)` whose finite component lies in `K₁(N)`, when `f` is invariant under `Γ₁(N)` in
weight `k`. For `det δ > 0` such a `δ` lies in `Γ₁(N)`, and for `det δ < 0` so does `J δ`. -/
lemma classicalFun_map_mul
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    (hδ : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) δ ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)})) :
    classicalFun k f (GeneralLinearGroup.map (algebraMap ℚ ℝ) δ * h) = classicalFun k f h := by
  rcases (δ.det.ne_zero : (δ.det : ℚ) ≠ 0).lt_or_gt with hd | hd
  · have hd' : 0 < ((ratJ * δ).det : ℚ) := by
      rw [map_mul, Units.val_mul, det_ratJ]
      linarith
    have hδ' : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (ratJ * δ) ∈
        levelOne (Ideal.span {(N : 𝓞 ℚ)}) := by
      rw [map_mul]
      exact mul_mem map_ratJ_mem_levelOne hδ
    rw [← classicalFun_J_mul, ← mul_assoc, ← map_ratJ_real, ← map_mul,
      classicalFun_map_mul_of_pos k h hf hd' hδ']
  · exact classicalFun_map_mul_of_pos k h hf hd hδ

end Rat

section Adelic

variable (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)

/-- The rational part `γ` of a decomposition `g = γ x u` of `g ∈ GL₂(𝔸_ℚ)`, with `γ ∈ GL₂(ℚ)`,
`x ∈ GL₂(ℝ)` and `u ∈ K₁(N)`, chosen by `AdelicGL2.rat_exists_eq_mul_levelOne` from the finite
component of `g`. -/
noncomputable def liftGlobal (g : AdelicGL2 ℚ) : GL (Fin 2) ℚ :=
  (rat_exists_eq_mul_levelOne N (toFin ℚ g)).choose

/-- The **adelic lift** `φ_f` of a function `f` on `ℍ` invariant under `Γ₁(N)` in weight `k`: for
`g = γ x u` with `γ ∈ GL₂(ℚ)`, `x ∈ GL₂(ℝ)` and `u ∈ K₁(N)`, `φ_f(g) = Φ_f(x)` for the function
`Φ_f = AdelicGL2.classicalFun k f` on `GL₂(ℝ)`, which is `det(x) ^ (1 - k / 2) (f ∣[k] x)(i)` when
`det x > 0`. It does not depend on the decomposition (`AdelicGL2.adelicLift_apply`). -/
noncomputable def adelicLift (g : AdelicGL2 ℚ) : ℂ :=
  classicalFun k f (ratInfEquiv ((toInf ℚ (ofGlobal ℚ (liftGlobal N g)))⁻¹ * toInf ℚ g))

variable {N k f}

variable (N) in
lemma exists_mem_levelOne_liftGlobal (g : AdelicGL2 ℚ) : ∃ u ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)}),
    toFin ℚ g = GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (liftGlobal N g) * u :=
  (rat_exists_eq_mul_levelOne N (toFin ℚ g)).choose_spec.2

lemma toFin_ofGlobal_mul_ofInf_mul_ofFin (γ : GL (Fin 2) ℚ) (x : GL (Fin 2) (mixedSpace ℚ))
    (u : GL (Fin 2) 𝔸ᶠ[ℚ]) : toFin ℚ (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u) = GeneralLinearGroup.map
      (algebraMap ℚ 𝔸ᶠ[ℚ]) γ * u := by
  rw [map_mul, map_mul, toFin_ofGlobal, toFin_ofInf, toFin_ofFin, mul_one]

lemma toInf_ofGlobal_mul_ofInf_mul_ofFin (γ : GL (Fin 2) ℚ) (x : GL (Fin 2) (mixedSpace ℚ))
    (u : GL (Fin 2) 𝔸ᶠ[ℚ]) :
    toInf ℚ (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u) = toInf ℚ (ofGlobal ℚ γ) * x := by
  rw [map_mul, map_mul, toInf_ofInf, toInf_ofFin, mul_one]

/-- **The master formula of the adelic lift**: `φ_f(γ x u) = Φ_f(x)` for every `γ ∈ GL₂(ℚ)`,
`x ∈ GL₂(ℝ)` and `u ∈ K₁(N)`. Two such decompositions of an element differ by a matrix
`δ ∈ GL₂(ℚ)` whose finite component lies in `K₁(N)`, and `Φ_f(δ x) = Φ_f(x)` for such `δ`. -/
lemma adelicLift_apply
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    (γ : GL (Fin 2) ℚ) (x : GL (Fin 2) (mixedSpace ℚ)) {u : GL (Fin 2) 𝔸ᶠ[ℚ]}
    (hu : u ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)})) :
    adelicLift N k f (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u) = classicalFun k f (ratInfEquiv x) := by
  rcases exists_mem_levelOne_liftGlobal N (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u) with
    ⟨u₀, hu₀, he⟩
  rw [toFin_ofGlobal_mul_ofInf_mul_ofFin] at he
  have hδ : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ])
      ((liftGlobal N (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u))⁻¹ * γ) ∈
        levelOne (Ideal.span {(N : 𝓞 ℚ)}) := by
    have h₁ : (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ])
        (liftGlobal N (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u)))⁻¹ *
          GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) γ = u₀ * u⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← he, mul_inv_cancel_right]
    rw [map_mul, map_inv, h₁]
    exact mul_mem hu₀ (inv_mem hu)
  have hx : (toInf ℚ (ofGlobal ℚ (liftGlobal N (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u))))⁻¹ *
      (toInf ℚ (ofGlobal ℚ γ) * x) = toInf ℚ (ofGlobal ℚ
        ((liftGlobal N (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u))⁻¹ * γ)) * x := by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact (mul_assoc _ _ _).symm
  rw [adelicLift, toInf_ofGlobal_mul_ofInf_mul_ofFin, hx, toInf_ofGlobal, map_mul,
    ratInfEquiv_map_mixedEmbedding, classicalFun_map_mul k _ hf hδ]

variable (N) in
lemma exists_eq_ofGlobal_mul_ofInf_mul_ofFin (g : AdelicGL2 ℚ) : ∃ (γ : GL (Fin 2) ℚ)
    (x : GL (Fin 2) (mixedSpace ℚ)), ∃ u ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)}), g =
      ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u := by
  rcases exists_mem_levelOne_liftGlobal N g with ⟨u, hu, he⟩
  refine ⟨liftGlobal N g, (toInf ℚ (ofGlobal ℚ (liftGlobal N g)))⁻¹ * toInf ℚ g, u, hu,
    ext_toInf_toFin ?_ ?_⟩
  · rw [toInf_ofGlobal_mul_ofInf_mul_ofFin, mul_inv_cancel_left]
  · rw [toFin_ofGlobal_mul_ofInf_mul_ofFin, he]

lemma ratInfEquiv_toInf_ofGlobal_ratJ : ratInfEquiv (toInf ℚ (ofGlobal ℚ ratJ)) = J := by
  rw [toInf_ofGlobal, ratInfEquiv_map_mixedEmbedding, map_ratJ_real]

variable (N) in
/-- **Every element of `GL₂(𝔸_ℚ)` is `γ x u`** with `γ ∈ GL₂(ℚ)`, `x ∈ GL₂(ℝ)` of positive
determinant and `u ∈ K₁(N)`, `J = diag(-1, 1)` lying in `GL₂(ℚ)` and its finite component in
`K₁(N)`. -/
lemma exists_eq_ofGlobal_mul_ofInf_mul_ofFin_of_pos (g : AdelicGL2 ℚ) : ∃ (γ : GL (Fin 2) ℚ)
    (x : GL (Fin 2) (mixedSpace ℚ)), 0 < ((ratInfEquiv x).det : ℝ) ∧
      ∃ u ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)}), g = ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u := by
  rcases exists_eq_ofGlobal_mul_ofInf_mul_ofFin N g with ⟨γ, x, u, hu, rfl⟩
  rcases ((ratInfEquiv x).det.ne_zero : ((ratInfEquiv x).det : ℝ) ≠ 0).lt_or_gt with hx | hx
  · refine ⟨γ * ratJ, (toInf ℚ (ofGlobal ℚ ratJ))⁻¹ * x, ?_,
      (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) ratJ)⁻¹ * u,
      mul_mem (inv_mem map_ratJ_mem_levelOne) hu, ext_toInf_toFin ?_ ?_⟩
    · rw [map_mul, map_inv, ratInfEquiv_toInf_ofGlobal_ratJ, map_mul, Units.val_mul, map_inv,
        Units.val_inv_eq_inv_val, det_J]
      simpa using hx
    · simp
    · simp [toFin_ofGlobal]
  · exact ⟨γ, x, hx, u, hu, rfl⟩

lemma adelicLift_ofGlobal_mul
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    (γ : GL (Fin 2) ℚ) (g : AdelicGL2 ℚ) :
    adelicLift N k f (ofGlobal ℚ γ * g) = adelicLift N k f g := by
  rcases exists_eq_ofGlobal_mul_ofInf_mul_ofFin N g with ⟨γ', x, u, hu, rfl⟩
  rw [← mul_assoc, ← mul_assoc, ← map_mul, adelicLift_apply hf _ _ hu, adelicLift_apply hf _ _ hu]

lemma adelicLift_mul_ofFin
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    (g : AdelicGL2 ℚ) {u : GL (Fin 2) 𝔸ᶠ[ℚ]} (hu : u ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)})) :
    adelicLift N k f (g * ofFin ℚ u) = adelicLift N k f g := by
  rcases exists_eq_ofGlobal_mul_ofInf_mul_ofFin N g with ⟨γ, x, u', hu', rfl⟩
  rw [mul_assoc, ← map_mul, adelicLift_apply hf _ _ (mul_mem hu' hu), adelicLift_apply hf _ _ hu']

variable (N) in
lemma exists_adelicLift_mul_ofInf
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    (g : AdelicGL2 ℚ) : ∃ h₀ : GL (Fin 2) ℝ, 0 < (h₀.det : ℝ) ∧ ∀ y,
      adelicLift N k f (g * ofInf ℚ y) = classicalFun k f (h₀ * ratInfEquiv y) := by
  rcases exists_eq_ofGlobal_mul_ofInf_mul_ofFin_of_pos N g with ⟨γ, x, hx, u, hu, rfl⟩
  refine ⟨ratInfEquiv x, hx, fun y ↦ ?_⟩
  rw [mul_assoc, ofFin_mul_ofInf, ← mul_assoc, mul_assoc (ofGlobal ℚ γ), ← map_mul,
    adelicLift_apply hf _ _ hu, map_mul]

lemma ratMixedEquiv_star (w : mixedSpace ℚ) : ratMixedEquiv (star w) = ratMixedEquiv w :=
  star_trivial _

lemma transpose_ratInfEquiv_mul_self (u : unitaryGroup (Fin 2) (mixedSpace ℚ)) :
    (ratInfEquiv (Unitary.toUnits u)).valᵀ * (ratInfEquiv (Unitary.toUnits u)).val = 1 := by
  have h₁ : ratMixedEquiv.mapMatrix (star (u : Matrix (Fin 2) (Fin 2) (mixedSpace ℚ))) *
      ratMixedEquiv.mapMatrix (u : Matrix (Fin 2) (Fin 2) (mixedSpace ℚ)) = 1 := by
    rw [← map_mul, Unitary.star_mul_self_of_mem u.2, map_one]
  have h₂ : ratMixedEquiv.mapMatrix (star (u : Matrix (Fin 2) (Fin 2) (mixedSpace ℚ))) =
      (ratInfEquiv (Unitary.toUnits u) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by
    ext i j
    simp [ratMixedEquiv_star, ratInfEquiv_apply]
  rw [← h₂]
  exact h₁

lemma det_sq_eq_one_of_transpose_mul_self {m : GL (Fin 2) ℝ}
    (hm : (m : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * m = 1) : (m.det : ℝ) ^ 2 = 1 := by
  have h : ((m : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * m).det = 1 := by
    rw [hm, det_one]
  rw [det_mul, det_transpose] at h
  rw [sq, GeneralLinearGroup.val_det_apply]
  exact h

variable (N) in
lemma adelicLift_mul_ofInf_of_smul_I
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    (g : AdelicGL2 ℚ) {y : GL (Fin 2) (mixedSpace ℚ)} (z : GL (Fin 2) (mixedSpace ℚ))
    (hy : ((ratInfEquiv y).det : ℝ) = 1) (hI : ratInfEquiv y • I = I) :
    adelicLift N k f (g * ofInf ℚ (z * y)) =
      denom (ratInfEquiv y) I ^ (-k) * adelicLift N k f (g * ofInf ℚ z) := by
  rcases exists_adelicLift_mul_ofInf N hf g with ⟨h₀, -, hh₀⟩
  rw [hh₀, hh₀, map_mul, ← mul_assoc, classicalFun_mul_of_smul_I k f _ hy hI]

/-- **The adelic lift is `K_∞`-finite**: its right translates by `K_∞ = O(2)` lie in the span of
`φ_f` and `g ↦ φ_f(g J)`, since `φ_f(g r) = j(r, i) ^ (-k) φ_f(g)` for a rotation `r`. -/
lemma isKFinite_adelicLift
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f) :
    IsKFinite (adelicLift N k f) := by
  let ε : GL (Fin 2) (mixedSpace ℚ) := ratInfEquiv.symm J
  let W : Submodule ℂ (AdelicGL2 ℚ → ℂ) :=
    Submodule.span ℂ {adelicLift N k f, rightTranslate (ofInf ℚ ε) (adelicLift N k f)}
  have hW : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hε : ratInfEquiv ε = J := ratInfEquiv.apply_symm_apply J
  have hle : kInfSpan (adelicLift N k f) ≤ W := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun u ↦ ?_)
    have hT : (ratInfEquiv (Unitary.toUnits u)).valᵀ * (ratInfEquiv (Unitary.toUnits u)).val = 1 :=
      transpose_ratInfEquiv_mul_self u
    have hsq : ((ratInfEquiv (Unitary.toUnits u)).det : ℝ) *
        (ratInfEquiv (Unitary.toUnits u)).det = 1 := by
      rw [← sq]
      exact det_sq_eq_one_of_transpose_mul_self hT
    rcases mul_self_eq_one_iff.mp hsq with h₁ | h₁
    · have he : rightTranslate (ofInf ℚ (Unitary.toUnits u)) (adelicLift N k f) =
          denom (ratInfEquiv (Unitary.toUnits u)) I ^ (-k) • adelicLift N k f := funext fun g ↦ by
        have h₂ : adelicLift N k f (g * ofInf ℚ (1 * Unitary.toUnits u)) =
            denom (ratInfEquiv (Unitary.toUnits u)) I ^ (-k) * adelicLift N k f (g * ofInf ℚ 1) :=
          adelicLift_mul_ofInf_of_smul_I N hf g 1 h₁ (smul_I_of_transpose_mul_self hT h₁)
        rw [one_mul, map_one, mul_one] at h₂
        exact h₂
      rw [SetLike.mem_coe, he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · have hJt : (J : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = J := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hJT : (J : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * J = 1 := by
        rw [hJt, ← Units.val_mul, J_mul_J, Units.val_one]
      have hd : ((ratInfEquiv (ε * Unitary.toUnits u)).det : ℝ) = 1 := by
        rw [map_mul, hε, map_mul, Units.val_mul, det_J, h₁]
        norm_num
      have hT' : (ratInfEquiv (ε * Unitary.toUnits u) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
          ratInfEquiv (ε * Unitary.toUnits u) = 1 := by
        rw [map_mul, hε, Units.val_mul, transpose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc (J : Matrix (Fin 2) (Fin 2) ℝ)ᵀ, hJT, Matrix.one_mul, hT]
      have hεε : ε * ε = 1 := ratInfEquiv.injective <| by
        rw [map_mul, hε, J_mul_J, map_one]
      have he : rightTranslate (ofInf ℚ (Unitary.toUnits u)) (adelicLift N k f) =
          denom (ratInfEquiv (ε * Unitary.toUnits u)) I ^ (-k) •
            rightTranslate (ofInf ℚ ε) (adelicLift N k f) := funext fun g ↦ by
        have h₂ : adelicLift N k f (g * ofInf ℚ (ε * (ε * Unitary.toUnits u))) =
            denom (ratInfEquiv (ε * Unitary.toUnits u)) I ^ (-k) *
              adelicLift N k f (g * ofInf ℚ ε) :=
          adelicLift_mul_ofInf_of_smul_I N hf g ε hd (smul_I_of_transpose_mul_self hT' hd)
        rw [← mul_assoc, hεε, one_mul] at h₂
        exact h₂
      rw [SetLike.mem_coe, he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact Submodule.finiteDimensional_of_le hle

end Adelic

section Smooth

variable {k : ℤ} {f : ℍ → ℂ}

lemma contDiffAt_zpow_complex (m : ℤ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ ↦ w ^ m) z :=
  (((differentiableOn_zpow m {w | w ≠ 0} (Or.inl (by simp))).contDiffOn isOpen_ne).contDiffAt
    (isOpen_ne.mem_nhds hz)).restrict_scalars ℝ

variable (k f) in
/-- The explicit formula `√(det M) ^ k (c i + d) ^ (-k) f((a i + b) / (c i + d))` of
`AdelicGL2.classicalFun` at a real matrix `M = (a, b; c, d)` of positive determinant
(`AdelicGL2.classicalFun_eq_explicitFun`), defined on all real matrices. -/
noncomputable def explicitFun (M : Fin 2 → Fin 2 → ℝ) : ℂ :=
  ((Real.sqrt (M 0 0 * M 1 1 - M 0 1 * M 1 0) : ℂ)) ^ k *
    ((M 1 0 : ℂ) * Complex.I + M 1 1) ^ (-k) *
      (f ∘ ofComplex) (((M 0 0 : ℂ) * Complex.I + M 0 1) / ((M 1 0 : ℂ) * Complex.I + M 1 1))

lemma classicalFun_eq_explicitFun {h : GL (Fin 2) ℝ} (hh : 0 < (h.det : ℝ)) :
    classicalFun k f h = explicitFun k f fun i j ↦ h i j := by
  have hd : (h.det : ℝ) = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [GeneralLinearGroup.val_det_apply, det_fin_two]
  have hI : ((h • I : ℍ) : ℂ) =
      ((h 0 0 : ℂ) * Complex.I + h 0 1) / ((h 1 0 : ℂ) * Complex.I + h 1 1) :=
    coe_smul_of_det_pos hh I
  rw [classicalFun_of_pos k f hh, normalizedSlash_of_pos k hh, explicitFun, Function.comp_apply,
    ← hI, ofComplex_apply, hd, Complex.ofReal_zpow]
  rfl

lemma denom_ne_zero_of_pos {M : Fin 2 → Fin 2 → ℝ} (hM : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0) :
    (M 1 0 : ℂ) * Complex.I + M 1 1 ≠ 0 := by
  intro h
  have h₁ : M 1 1 = 0 := by simpa using congrArg Complex.re h
  have h₂ : M 1 0 = 0 := by simpa using congrArg Complex.im h
  rw [h₁, h₂] at hM
  simp at hM

lemma im_div_denom_pos {M : Fin 2 → Fin 2 → ℝ} (hM : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0) :
    0 < (((M 0 0 : ℂ) * Complex.I + M 0 1) / ((M 1 0 : ℂ) * Complex.I + M 1 1)).im := by
  have hn : 0 < Complex.normSq ((M 1 0 : ℂ) * Complex.I + M 1 1) :=
    Complex.normSq_pos.mpr (denom_ne_zero_of_pos hM)
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_im]
  rw [← sub_div]
  exact div_pos (by linarith) hn

lemma contDiffAt_explicitFun (hf : MDiff f) {M : Fin 2 → Fin 2 → ℝ}
    (hM : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (explicitFun k f) M := by
  have hc (i j : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun M : Fin 2 → Fin 2 → ℝ ↦ (M i j : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ i j)
  have hdet : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun M : Fin 2 → Fin 2 → ℝ ↦ M 0 0 * M 1 1 - M 0 1 * M 1 0 :=
    ((contDiff_apply_apply ℝ 0 0).mul (contDiff_apply_apply ℝ 1 1)).sub
      ((contDiff_apply_apply ℝ 0 1).mul (contDiff_apply_apply ℝ 1 0))
  have hs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun M : Fin 2 → Fin 2 → ℝ ↦ ((Real.sqrt (M 0 0 * M 1 1 - M 0 1 * M 1 0) : ℂ))) M :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp M
      ((Real.contDiffAt_sqrt hM.ne').comp M hdet.contDiffAt)
  have hs₀ : ((Real.sqrt (M 0 0 * M 1 1 - M 0 1 * M 1 0) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hM).ne'
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun M : Fin 2 → Fin 2 → ℝ ↦ (M 1 0 : ℂ) * Complex.I + M 1 1 :=
    ((hc 1 0).mul contDiff_const).add (hc 1 1)
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun M : Fin 2 → Fin 2 → ℝ ↦ (M 0 0 : ℂ) * Complex.I + M 0 1 :=
    ((hc 0 0).mul contDiff_const).add (hc 0 1)
  have hq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun M : Fin 2 → Fin 2 → ℝ ↦
      ((M 0 0 : ℂ) * Complex.I + M 0 1) / ((M 1 0 : ℂ) * Complex.I + M 1 1)) M :=
    hN.contDiffAt.mul (hD.contDiffAt.inv (denom_ne_zero_of_pos hM))
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ ofComplex)
      (((M 0 0 : ℂ) * Complex.I + M 0 1) / ((M 1 0 : ℂ) * Complex.I + M 1 1)) :=
    (((UpperHalfPlane.mdifferentiable_iff.mp hf).contDiffOn hopen).contDiffAt
      (hopen.mem_nhds (im_div_denom_pos hM))).restrict_scalars ℝ
  exact (((contDiffAt_zpow_complex k hs₀).comp M hs).mul
    ((contDiffAt_zpow_complex (-k) (denom_ne_zero_of_pos hM)).comp M hD.contDiffAt)).mul
      (hF.comp M hq)

lemma contDiffAt_extendGL_of_pos (hf : MDiff f) (h₀ : GL (Fin 2) ℝ)
    {m₀ : Fin 2 → Fin 2 → mixedSpace ℚ} (hm₀ : IsUnit (of m₀))
    (hpos : 0 < ((h₀ * ratInfEquiv hm₀.unit).det : ℝ)) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (extendGL fun x ↦ classicalFun k f (h₀ * ratInfEquiv x)) m₀ := by
  let L : (Fin 2 → Fin 2 → mixedSpace ℚ) → Fin 2 → Fin 2 → ℝ :=
    fun m i j ↦ ∑ l, h₀ i l * ratMixedEquiv (m l j)
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L :=
    contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦ ContDiff.sum fun l _ ↦
      contDiff_const.mul (ratMixedEquivL.contDiff.comp (contDiff_apply_apply ℝ l j))
  have hLm (m : Fin 2 → Fin 2 → mixedSpace ℚ) (hm : IsUnit (of m)) :
      (fun i j ↦ (h₀ * ratInfEquiv hm.unit : GL (Fin 2) ℝ) i j) = L m := by
    ext i j
    simp [Matrix.mul_apply, ratInfEquiv_apply, L]
  have hdet (m : Fin 2 → Fin 2 → mixedSpace ℚ) (hm : IsUnit (of m)) :
      ((h₀ * ratInfEquiv hm.unit).det : ℝ) = L m 0 0 * L m 1 1 - L m 0 1 * L m 1 0 := by
    rw [← hLm m hm, GeneralLinearGroup.val_det_apply, det_fin_two]
  let U : Set (Fin 2 → Fin 2 → mixedSpace ℚ) :=
    {m | IsUnit (of m)} ∩ {m | 0 < L m 0 0 * L m 1 1 - L m 0 1 * L m 1 0}
  have hU : IsOpen U := (isOpen_setOf_isUnit ℚ).inter (isOpen_lt continuous_const
    (((hL.continuous.matrix_elem 0 0).mul (hL.continuous.matrix_elem 1 1)).sub
      ((hL.continuous.matrix_elem 0 1).mul (hL.continuous.matrix_elem 1 0))))
  have hm₀U : m₀ ∈ U := ⟨hm₀, by rw [Set.mem_ofPred_eq, ← hdet m₀ hm₀]; exact hpos⟩
  have he : (extendGL fun x ↦ classicalFun k f (h₀ * ratInfEquiv x)) =ᶠ[nhds m₀]
      explicitFun k f ∘ L := Filter.eventually_of_mem (hU.mem_nhds hm₀U) fun m hm ↦ by
    rw [extendGL_of_isUnit _ hm.1, classicalFun_eq_explicitFun (hdet m hm.1 ▸ hm.2), hLm m hm.1]
    rfl
  exact ((contDiffAt_explicitFun hf hm₀U.2).comp m₀ hL.contDiffAt).congr_of_eventuallyEq he

/-- **The function `x ↦ Φ_f(h₀ x)` is smooth on `GL₂(E)`** for a holomorphic `f`, where `E = ℝ` is
the mixed space of `ℚ`. -/
lemma isSmoothOnGL_classicalFun (hf : MDiff f) (h₀ : GL (Fin 2) ℝ) :
    IsSmoothOnGL fun x ↦ classicalFun k f (h₀ * ratInfEquiv x) := fun m₀ hm₀ ↦ by
  refine ContDiffAt.contDiffWithinAt ?_
  rcases ((h₀ * ratInfEquiv hm₀.unit).det.ne_zero :
    ((h₀ * ratInfEquiv hm₀.unit).det : ℝ) ≠ 0).lt_or_gt with hneg | hpos
  · have he : (fun x ↦ classicalFun k f (h₀ * ratInfEquiv x)) =
        fun x ↦ classicalFun k f (J * h₀ * ratInfEquiv x) :=
      funext fun x ↦ by rw [mul_assoc, classicalFun_J_mul]
    rw [he]
    exact contDiffAt_extendGL_of_pos hf (J * h₀) hm₀ (by rw [mul_assoc, det_J_mul]; linarith)
  · exact contDiffAt_extendGL_of_pos hf h₀ hm₀ hpos

variable {N : ℕ} [NeZero N]

/-- **The adelic lift of a holomorphic function is smooth in the archimedean variable.** -/
lemma isSmoothAtInfinity_adelicLift (hh : MDiff f)
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f) :
    IsSmoothAtInfinity (adelicLift N k f) := fun g ↦ by
  rcases exists_adelicLift_mul_ofInf N hf g with ⟨h₀, -, he⟩
  simp only [he]
  exact isSmoothOnGL_classicalFun hh h₀

end Smooth

section CuspForm

variable {N : ℕ} {k : ℤ} (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map
  (SpecialLinearGroup.mapGL ℝ)) k)

lemma slash_mapGL_eq_of_mem_gamma1 :
    ∀ g ∈ CongruenceSubgroup.Gamma1 N, ⇑f ∣[k] SpecialLinearGroup.mapGL ℝ g = ⇑f :=
  fun g hg ↦ SlashInvariantForm.slash_action_eqn f _ ⟨g, hg, rfl⟩

variable [NeZero N]

/-- **The adelic lift of a cusp form is bounded**, as `|Φ_f(h)| = (im h i) ^ (k / 2) |f(h i)|`
for `det h > 0`. -/
lemma exists_norm_adelicLift_le : ∃ C, ∀ g, ‖adelicLift N k f g‖ ≤ C := by
  rcases CuspFormClass.exists_bound f with ⟨C, hC⟩
  refine ⟨C, fun g ↦ ?_⟩
  rcases exists_adelicLift_mul_ofInf N (slash_mapGL_eq_of_mem_gamma1 f) g with ⟨h₀, hh₀, he⟩
  have h₁ : adelicLift N k f (g * ofInf ℚ 1) = classicalFun k f (h₀ * ratInfEquiv 1) := he 1
  rw [map_one, mul_one, map_one, mul_one] at h₁
  have hpos : 0 < (h₀ • I).im ^ (k / 2 : ℝ) := Real.rpow_pos_of_pos (h₀ • I).im_pos _
  rw [h₁, classicalFun_of_pos k f hh₀, norm_normalizedSlash k hh₀, mul_comm]
  exact (le_div_iff₀ hpos).mp (hC (h₀ • I))

/-- **The adelic lift of a cusp form has moderate growth**: it is bounded. -/
lemma hasModerateGrowth_adelicLift : HasModerateGrowth (adelicLift N k f) := fun y ↦ by
  rcases exists_norm_adelicLift_le f with ⟨C, hC⟩
  exact ⟨C, 0, fun x ↦ by simpa using hC _⟩

lemma exists_openSubgroup_adelicLift : ∃ U : OpenSubgroup (GL (Fin 2) 𝔸ᶠ[ℚ]), ∀ u ∈ U, ∀ g,
    adelicLift N k f (g * ofFin ℚ u) = adelicLift N k f g :=
  ⟨⟨levelOne (Ideal.span {(N : 𝓞 ℚ)}), isOpen_levelOne (span_natCast_ne_bot N)⟩,
    fun _ hu g ↦ adelicLift_mul_ofFin (slash_mapGL_eq_of_mem_gamma1 f) g hu⟩

lemma isSmoothAtInfinity_adelicLift_cuspForm : IsSmoothAtInfinity (adelicLift N k f) :=
  isSmoothAtInfinity_adelicLift (CuspFormClass.holo f) (slash_mapGL_eq_of_mem_gamma1 f)

end CuspForm

end AdelicGL2
