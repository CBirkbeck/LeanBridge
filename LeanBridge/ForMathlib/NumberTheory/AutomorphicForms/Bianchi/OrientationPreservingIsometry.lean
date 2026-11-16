import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.MoebiusIsometry
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# The orientation-preserving isometries of hyperbolic 3-space are `PSL(2, ℂ)`

The isometries of hyperbolic 3-space `ℋ₃`, for the hyperbolic metric `ds = |dz| / y` (Tau Ceti's
Riemannian structure on the upper half-space `ℋ₃ ⊆ ℂ × ℝ`), that preserve the orientation of
`ℂ × ℝ = ℝ³` are exactly the transformations `z ↦ (az + b)(cz + d)⁻¹` of `PSL(2, ℂ)` (LMFDB
`mf.bianchi.hyperbolic3space`, `mf.bianchi.bianchigroup`, `mf.maass.picard`): the injective
homomorphism `pslToIsom : PSL(2, ℂ) → Isom(ℋ₃)` has for image the group of orientation-preserving
isometries.

An isometry `Φ` is orientation-preserving when its Jacobian determinant `jacobianDet Φ p`, the
determinant of its differential read in the chart `ℂ × ℝ`, is positive at every point `p`; its sign
is the same at every point (`isOrientationPreserving_iff_jacobianDet_pos`). The isometry
`(x, y) ↦ (-x̄, y)` does not preserve orientation (`not_isOrientationPreserving_negConjIsom`).

By Tau Ceti's classification, an isometry is a similarity `(x, y) ↦ (c A x + b, c y)`, with `A` a
linear isometry of `ℂ`, or such a similarity followed by an inversion in a sphere centred on the
boundary. Their Jacobian determinants are `c³ det A` and `-f³ c³ det A` with `f > 0`, and `A` is a
rotation (`det A = 1`) or a rotation after `x ↦ x̄` (`det A = -1`). A similarity with a rotation is
the action of an upper triangular matrix, and the inversion in the sphere of radius `|R|` about
`(a, 0)` is the action of `(a, |a|² - R²; 1, ā) / R` after `(x, y) ↦ (-x̄, y)`
(`inversion_eq_pslToIsom_mul_negConjIsom`).

## Main definitions

* `HyperbolicThreeSpace.jacobianDet`: the Jacobian determinant of an isometry of `ℋ₃`.
* `HyperbolicThreeSpace.IsOrientationPreserving`: orientation-preserving isometries.
* `HyperbolicThreeSpace.orientationPreservingIsom`: the group `Isom⁺(ℋ₃)` they form.

## Main results

* `HyperbolicThreeSpace.not_isOrientationPreserving_negConjIsom`: `(x, y) ↦ (-x̄, y)` does not
  preserve orientation.
* `HyperbolicThreeSpace.inversion_eq_pslToIsom_mul_negConjIsom`: an inversion in a sphere centred
  on the boundary is an element of `PSL(2, ℂ)` after `(x, y) ↦ (-x̄, y)`.
* `HyperbolicThreeSpace.isOrientationPreserving_pslToIsom`: `PSL(2, ℂ)` acts by
  orientation-preserving isometries.
* `HyperbolicThreeSpace.isOrientationPreserving_iff_mem_range`: the orientation-preserving
  isometries of `ℋ₃` are exactly those of `PSL(2, ℂ)`.
* `HyperbolicThreeSpace.isOrientationPreserving_iff_jacobianDet_pos`: the sign of the Jacobian
  determinant of an isometry is the same at every point.
* `HyperbolicThreeSpace.pslEquivOrientationPreservingIsom`: `PSL(2, ℂ) ≃* Isom⁺(ℋ₃)`.
-/

open Complex Matrix Module TauCeti UpperHalfSpace

open scoped ComplexConjugate Manifold MatrixGroups

namespace HyperbolicThreeSpace

variable (Φ Ψ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) HyperbolicThreeSpace) (p : HyperbolicThreeSpace) (a : ℂ)
  (R : ℝ) (hR : R ≠ 0) (c : ℝ) (hc : 0 < c) (u : Circle) (b : ℂ)

/-- The differential of an isometry `Φ` of `ℋ₃` at `p`, read in the chart `ℂ × ℝ`. -/
noncomputable def chartDeriv : WithLp 2 (ℂ × ℝ) →L[ℝ] WithLp 2 (ℂ × ℝ) :=
  (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (Φ p) :
      TangentSpace 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (Φ p) →L[ℝ] WithLp 2 (ℂ × ℝ)).comp
    ((mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) Φ p).comp
      (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) p).symm.toContinuousLinearMap)

/-- The **Jacobian determinant** of an isometry `Φ` of `ℋ₃` at `p`: the determinant of its
differential in the chart `ℂ × ℝ = ℝ³`. -/
noncomputable def jacobianDet : ℝ :=
  LinearMap.det (chartDeriv Φ p : WithLp 2 (ℂ × ℝ) →ₗ[ℝ] WithLp 2 (ℂ × ℝ))

/-- An isometry `Φ` of `ℋ₃` is **orientation-preserving** if its Jacobian determinant in the chart
`ℂ × ℝ = ℝ³` is positive at every point; the sign is the same at every point
(`isOrientationPreserving_iff_jacobianDet_pos`). -/
def IsOrientationPreserving : Prop :=
  ∀ p, 0 < jacobianDet Φ p

lemma chartDeriv_mul : chartDeriv (Φ * Ψ) p = (chartDeriv Φ (Ψ p)).comp (chartDeriv Ψ p) := by
  have h : mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (Φ * Ψ) p =
      (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) Φ (Ψ p)).comp
        (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) Ψ p) := by
    rw [RiemannianIsometry.coe_mul]
    exact mfderiv_comp p (Φ.mdifferentiableAt _) (Ψ.mdifferentiableAt _)
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [chartDeriv, h]
  rfl

lemma jacobianDet_mul : jacobianDet (Φ * Ψ) p = jacobianDet Φ (Ψ p) * jacobianDet Ψ p := by
  simp only [jacobianDet, chartDeriv_mul, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

variable {Φ Ψ} in
lemma IsOrientationPreserving.mul (h : IsOrientationPreserving Φ) (h' : IsOrientationPreserving Ψ) :
    IsOrientationPreserving (Φ * Ψ) :=
  fun p ↦ (mul_pos (h (Ψ p)) (h' p)).trans_eq (jacobianDet_mul Φ Ψ p).symm

lemma finrank_withLp_prod : finrank ℝ (WithLp 2 (ℂ × ℝ)) = 3 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).finrank_eq, finrank_prod, finrank_real_complex,
    finrank_self]

lemma jacobianDet_similarity (A : ℂ ≃ₗᵢ[ℝ] ℂ) :
    jacobianDet (similarity c hc A b) p = c ^ 3 * LinearMap.det (A.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) := by
  have h : (chartDeriv (similarity c hc A b) p : WithLp 2 (ℂ × ℝ) →ₗ[ℝ] WithLp 2 (ℂ × ℝ)) =
      c • (((WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).symm : ℂ × ℝ →ₗ[ℝ] WithLp 2 (ℂ × ℝ)) ∘ₗ
        ((A.toLinearEquiv : ℂ →ₗ[ℝ] ℂ).prodMap LinearMap.id) ∘ₗ
          ((WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).symm.symm : WithLp 2 (ℂ × ℝ) →ₗ[ℝ] ℂ × ℝ)) :=
    LinearMap.ext fun v ↦ tangentSpaceCastModel_mfderiv_similarity c hc A b p
      ((tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) p).symm v)
  rw [jacobianDet, h, LinearMap.det_smul, finrank_withLp_prod, LinearMap.det_conj,
    LinearMap.det_prodMap, LinearMap.det_id, mul_one]

lemma jacobianDet_inversion_neg : jacobianDet (inversion a R hR) p < 0 := by
  have hd : dist (p : WithLp 2 (ℂ × ℝ)) (WithLp.toLp 2 (a, 0)) ≠ 0 :=
    dist_ne_zero.mpr (coe_ne_toLp p a)
  have h : (chartDeriv (inversion a R hR) p : WithLp 2 (ℂ × ℝ) →ₗ[ℝ] WithLp 2 (ℂ × ℝ)) =
      (R / dist (p : WithLp 2 (ℂ × ℝ)) (WithLp.toLp 2 (a, 0))) ^ 2 •
        (ℝ ∙ ((p : WithLp 2 (ℂ × ℝ)) - WithLp.toLp 2 (a, 0)))ᗮ.reflection.toLinearMap :=
    LinearMap.ext fun v ↦ tangentSpaceCastModel_mfderiv_inversion a R hR p
      ((tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) p).symm v)
  rw [jacobianDet, h, LinearMap.det_smul, finrank_withLp_prod, Submodule.det_reflection,
    Submodule.orthogonal_orthogonal, finrank_span_singleton (sub_ne_zero.mpr (coe_ne_toLp p a)),
    pow_one, mul_neg_one, neg_lt_zero]
  positivity

lemma isOrientationPreserving_similarity_rotation :
    IsOrientationPreserving (similarity c hc (rotation u) b) := fun p ↦ by
  rw [jacobianDet_similarity, det_rotation, mul_one]
  positivity

lemma det_conjLIE_trans_rotation :
    LinearMap.det ((conjLIE.trans (rotation u)).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 := by
  have h : ((conjLIE.trans (rotation u)).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
      ((rotation u).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ (conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) :=
    rfl
  rw [h, LinearMap.det_comp, det_rotation, det_conjLIE, one_mul]

/-- The isometry `(x, y) ↦ (-x̄, y)` of `ℋ₃`. -/
noncomputable def negConjIsom : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) HyperbolicThreeSpace :=
  similarity 1 one_pos (conjLIE.trans (rotation (-1))) 0

lemma coords_negConjIsom : coords (negConjIsom p) = (-conj p.coords.1, p.coords.2) := by
  rw [negConjIsom, coords_similarity]
  simp

lemma jacobianDet_negConjIsom : jacobianDet negConjIsom p = -1 := by
  rw [negConjIsom, jacobianDet_similarity, det_conjLIE_trans_rotation]
  norm_num

/-- **Not every isometry of `ℋ₃` preserves orientation**: `(x, y) ↦ (-x̄, y)` reverses it. -/
lemma not_isOrientationPreserving_negConjIsom : ¬IsOrientationPreserving negConjIsom := fun h ↦ by
  have h₁ : 0 < jacobianDet negConjIsom basePoint := h basePoint
  rw [jacobianDet_negConjIsom] at h₁
  norm_num at h₁

lemma negConjIsom_mul_self : negConjIsom * negConjIsom = 1 :=
  RiemannianIsometry.ext fun z ↦ coords_injective <| by
    rw [RiemannianIsometry.mul_apply, coords_negConjIsom, coords_negConjIsom,
      RiemannianIsometry.one_apply]
    simp

lemma negConjIsom_mul_similarity : negConjIsom * similarity c hc (conjLIE.trans (rotation u)) b =
    similarity c hc (rotation (-u⁻¹)) (-conj b) :=
  RiemannianIsometry.ext fun z ↦ coords_injective <| by
    rw [RiemannianIsometry.mul_apply, coords_negConjIsom, coords_similarity, coords_similarity]
    refine Prod.ext ?_ rfl
    simp only [LinearIsometryEquiv.trans_apply, rotation_apply, conjLIE_apply, Circle.coe_neg,
      Circle.coe_inv_eq_conj, real_smul, map_add, map_mul, conj_ofReal, conj_conj]
    ring1

lemma coords_inversion : coords (inversion a R hR p) =
    ((R ^ 2 / (normSq (p.coords.1 - a) + p.coords.2 ^ 2)) • (p.coords.1 - a) + a,
      R ^ 2 / (normSq (p.coords.1 - a) + p.coords.2 ^ 2) * p.coords.2) := by
  have hd : dist (p : WithLp 2 (ℂ × ℝ)) (WithLp.toLp 2 (a, 0)) ^ 2 =
      normSq (p.coords.1 - a) + p.coords.2 ^ 2 := by
    rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2, normSq_eq_norm_sq]
    simp [coords]
  rw [coords, coe_inversion_apply, EuclideanGeometry.inversion, div_pow, hd]
  exact Prod.ext rfl (by simp [coords])

/-- The matrix `(a, |a|² - R²; 1, ā) / R` of `SL(2, ℂ)`: its action on `ℋ₃` after
`(x, y) ↦ (-x̄, y)` is the inversion in the sphere of radius `|R|` about `(a, 0)`
(`inversion_eq_pslToIsom_mul_negConjIsom`). -/
noncomputable def inversionMatrix : SL(2, ℂ) :=
  ⟨!![a / R, (normSq a - R ^ 2) / R; 1 / R, conj a / R], by
    have hR' : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR
    rw [det_fin_two_of]
    field_simp
    linear_combination mul_conj a⟩

/-- **An inversion in a sphere centred on the boundary is an element of `PSL(2, ℂ)` composed with
`(x, y) ↦ (-x̄, y)`**: the inversion of `ℋ₃` in the sphere of radius `|R|` about `(a, 0)` is the
action of `(a, |a|² - R²; 1, ā) / R` after `(x, y) ↦ (-x̄, y)`. -/
lemma inversion_eq_pslToIsom_mul_negConjIsom :
    inversion a R hR = pslToIsom (QuotientGroup.mk (inversionMatrix a R hR)) * negConjIsom := by
  refine RiemannianIsometry.ext fun (z : HyperbolicThreeSpace) ↦ coords_injective ?_
  have hy : 0 < z.coords.2 := coords_snd_pos z
  have hR' : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR
  have hD : normSq (z.coords.1 - a) + z.coords.2 ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (normSq_nonneg _) (pow_pos hy 2)).ne'
  have hD' : (normSq (z.coords.1 - a) : ℂ) + (z.coords.2 : ℂ) ^ 2 ≠ 0 :=
    mod_cast hD
  have e₀₀ : (inversionMatrix a R hR) 0 0 = a / R :=
    rfl
  have e₀₁ : (inversionMatrix a R hR) 0 1 = (normSq a - R ^ 2) / R :=
    rfl
  have e₁₀ : (inversionMatrix a R hR) 1 0 = 1 / R :=
    rfl
  have e₁₁ : (inversionMatrix a R hR) 1 1 = conj a / R :=
    rfl
  have hN : moebiusDenom (inversionMatrix a R hR) (-conj z.coords.1, z.coords.2) =
      (normSq (z.coords.1 - a) + z.coords.2 ^ 2) / R ^ 2 := by
    have h : 1 / (R : ℂ) * -conj z.coords.1 + conj a / R = -conj (z.coords.1 - a) / R := by
      rw [map_sub]
      ring1
    simp only [moebiusDenom, e₁₀, e₁₁]
    rw [h, normSq_div, normSq_neg, normSq_conj, normSq_div, normSq_one, normSq_ofReal]
    field_simp
  rw [RiemannianIsometry.mul_apply, pslToIsom_apply, mk_smul_eq, coords_smul, coords_negConjIsom,
    coords_inversion]
  refine Prod.ext ?_ ?_
  · simp only [moebius, e₀₀, e₀₁, e₁₀, e₁₁, hN, real_smul, ofReal_div, ofReal_add, ofReal_pow,
      map_add, map_mul, map_div₀, map_neg, map_one, conj_conj, conj_ofReal]
    field_simp
    simp only [← mul_conj, map_sub]
    ring1
  · simp only [moebius, hN]
    field_simp

lemma isOrientationPreserving_pslToIsom_mk_of_apply_one_zero {g : SL(2, ℂ)} (hg : g 1 0 = 0) :
    IsOrientationPreserving (pslToIsom (QuotientGroup.mk g)) := by
  have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one (mul_apply_one_one_eq_one_of_apply_one_zero hg)
  have ha' : conj (g 0 0) ≠ 0 := (map_ne_zero _).mpr ha
  have hn : 0 < ‖g 0 0‖ ^ 2 := by
    positivity
  have h : pslToIsom (QuotientGroup.mk g) = similarity (‖g 0 0‖ ^ 2) hn
      (rotation (Circle.ofConjDivSelf (conj (g 0 0)) ha')) (g 0 0 * g 0 1) :=
    RiemannianIsometry.ext fun z ↦
      (pslToIsom_apply _ z).trans (congrFun (coe_similarity_eq_smul hg hn ha') z).symm
  rw [h]
  exact isOrientationPreserving_similarity_rotation _ _ _ _

/-- **`PSL(2, ℂ)` acts on `ℋ₃` by orientation-preserving isometries**: every `γ ∈ PSL(2, ℂ)` is a
product of upper triangular matrices, which act by similarities `(x, y) ↦ (|a|² u x + b, |a|² y)`
with `|u| = 1`, and of `(0, -1; 1, 0)`, which acts by an inversion after `(x, y) ↦ (-x̄, y)`, two
isometries of negative Jacobian determinant. -/
lemma isOrientationPreserving_pslToIsom (γ : PSL(2, ℂ)) :
    IsOrientationPreserving (pslToIsom γ) := by
  induction γ using QuotientGroup.induction_on with
  | H g =>
    by_cases h₀ : g 1 0 = 0
    · exact isOrientationPreserving_pslToIsom_mk_of_apply_one_zero h₀
    let P : SL(2, ℂ) := ⟨!![(g 1 0)⁻¹, g 0 0; 0, g 1 0], by simp [h₀]⟩
    let Q : SL(2, ℂ) := ⟨!![1, g 1 1 / g 1 0; 0, 1], by simp⟩
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := g.fin_two_mul_sub_mul_eq_one
    have hg : g = P * inversionMatrix 0 1 one_ne_zero * Q := by
      refine Subtype.ext ?_
      rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [P, inversionMatrix, Q]
      · field_simp
        linear_combination -hdet
      · field_simp
    have hS : IsOrientationPreserving (inversion (0 : ℂ) 1 one_ne_zero * negConjIsom) := fun z ↦ by
      rw [jacobianDet_mul, jacobianDet_negConjIsom]
      exact mul_pos_of_neg_of_neg (jacobianDet_inversion_neg _ 0 1 one_ne_zero) neg_one_lt_zero
    rw [inversion_eq_pslToIsom_mul_negConjIsom, mul_assoc, negConjIsom_mul_self, mul_one] at hS
    rw [hg, QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul]
    exact ((isOrientationPreserving_pslToIsom_mk_of_apply_one_zero rfl).mul hS).mul
      (isOrientationPreserving_pslToIsom_mk_of_apply_one_zero rfl)

lemma similarity_rotation_mem_range : similarity c hc (rotation u) b ∈ pslToIsom.range := by
  let α : ℂ := ((c : ℂ) * u) ^ ((2 : ℕ)⁻¹ : ℂ)
  have hα : α ^ 2 = c * u :=
    cpow_nat_inv_pow _ two_ne_zero
  have hα₀ : α ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hα
    exact mul_ne_zero (ofReal_ne_zero.mpr hc.ne') (Circle.coe_ne_zero u) hα.symm
  have hnα : ‖α‖ ^ 2 = c := by
    rw [← norm_pow, hα, norm_mul, norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg hc.le]
  let g : SL(2, ℂ) := ⟨!![α, b / α; 0, α⁻¹], by simp [hα₀]⟩
  refine ⟨QuotientGroup.mk g, RiemannianIsometry.ext fun (z : HyperbolicThreeSpace) ↦
    coords_injective ?_⟩
  rw [pslToIsom_apply, mk_smul_eq, coords_smul, moebius_eq_of_apply_one_zero (g := g) rfl,
    coords_similarity]
  have e₀₀ : g 0 0 = α :=
    rfl
  have e₀₁ : g 0 1 = b / α :=
    rfl
  rw [e₀₀, e₀₁, hα, hnα, rotation_apply, real_smul, mul_div_cancel₀ _ hα₀, mul_assoc]

lemma mem_range_of_isOrientationPreserving (h : IsOrientationPreserving Φ) :
    Φ ∈ pslToIsom.range := by
  rcases exists_eq_similarity_or_exists_eq_inversion_mul_similarity Φ with
    ⟨c, hc, A, b, rfl⟩ | ⟨a, R, hR, c, hc, A, b, rfl⟩
  · rcases linear_isometry_complex A with ⟨u, rfl | rfl⟩
    · exact similarity_rotation_mem_range c hc u b
    · have h₁ : 0 < jacobianDet (similarity c hc (conjLIE.trans (rotation u)) b) basePoint :=
        h basePoint
      rw [jacobianDet_similarity, det_conjLIE_trans_rotation] at h₁
      linarith [pow_pos hc 3]
  · rcases linear_isometry_complex A with ⟨u, rfl | rfl⟩
    · have h₁ : 0 < jacobianDet (inversion a R hR * similarity c hc (rotation u) b) basePoint :=
        h basePoint
      rw [jacobianDet_mul, jacobianDet_similarity, det_rotation, mul_one] at h₁
      nlinarith [pow_pos hc 3, jacobianDet_inversion_neg (similarity c hc (rotation u) b basePoint)
        a R hR]
    · rw [inversion_eq_pslToIsom_mul_negConjIsom, mul_assoc, negConjIsom_mul_similarity]
      exact mul_mem ⟨_, rfl⟩ (similarity_rotation_mem_range c hc _ _)

/-- **The orientation-preserving isometries of `ℋ₃` are exactly `PSL(2, ℂ)`** (LMFDB
`mf.bianchi.hyperbolic3space`, `mf.bianchi.bianchigroup`, `mf.maass.picard`): an isometry of the
hyperbolic metric `ds = |dz| / y` preserves orientation if and only if it is the action
`z ↦ (az + b)(cz + d)⁻¹` of an element of `PSL(2, ℂ)`. -/
lemma isOrientationPreserving_iff_mem_range : IsOrientationPreserving Φ ↔ Φ ∈ pslToIsom.range :=
  ⟨mem_range_of_isOrientationPreserving Φ, fun ⟨γ, hγ⟩ ↦ hγ ▸ isOrientationPreserving_pslToIsom γ⟩

/-- **The orientation of an isometry of `ℋ₃` can be read at any point**: the sign of its Jacobian
determinant is the same everywhere, `c³ det A` for a similarity and `-f³ c³ det A` with `f > 0` for
an inversion after a similarity. -/
lemma isOrientationPreserving_iff_jacobianDet_pos :
    IsOrientationPreserving Φ ↔ 0 < jacobianDet Φ p := by
  refine ⟨fun h ↦ h p, fun h q ↦ ?_⟩
  rcases exists_eq_similarity_or_exists_eq_inversion_mul_similarity Φ with
    ⟨c, hc, A, b, rfl⟩ | ⟨a, R, hR, c, hc, A, b, rfl⟩
  · rw [jacobianDet_similarity] at h ⊢
    exact h
  · rw [jacobianDet_mul, jacobianDet_similarity] at h ⊢
    exact mul_pos_of_neg_of_neg (jacobianDet_inversion_neg _ a R hR)
      (neg_of_mul_pos_right h (jacobianDet_inversion_neg _ a R hR).le)

/-- The group `Isom⁺(ℋ₃)` of the orientation-preserving isometries of `ℋ₃` (LMFDB
`mf.bianchi.hyperbolic3space`, `mf.bianchi.bianchigroup`), the image of `PSL(2, ℂ)`
(`isOrientationPreserving_iff_mem_range`). -/
noncomputable def orientationPreservingIsom :
    Subgroup (Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) HyperbolicThreeSpace) :=
  pslToIsom.range.copy {Φ | IsOrientationPreserving Φ}
    (Set.ext isOrientationPreserving_iff_mem_range)

lemma range_pslToIsom : pslToIsom.range = orientationPreservingIsom :=
  (Subgroup.copy_eq _ _ _).symm

/-- **`PSL(2, ℂ)` is the group of orientation-preserving isometries of `ℋ₃`** (LMFDB
`mf.bianchi.hyperbolic3space`, `mf.bianchi.bianchigroup`, `mf.maass.picard`): `pslToIsom` is an
isomorphism onto `Isom⁺(ℋ₃)`. -/
noncomputable def pslEquivOrientationPreservingIsom : PSL(2, ℂ) ≃* orientationPreservingIsom :=
  (MonoidHom.ofInjective pslToIsom_injective).trans (MulEquiv.subgroupCongr range_pslToIsom)

end HyperbolicThreeSpace
