import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.GammaZeroFundamentalDomain
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Quaternion
import TauCeti.Geometry.Manifold.Riemannian.Isometry.UpperHalfSpace

/-!
# `PSL(2, ℂ)` acts on hyperbolic 3-space by isometries

The action `γ z = (az + b)(cz + d)⁻¹` of `PSL(2, ℂ)` on hyperbolic 3-space `ℋ₃` (LMFDB
`mf.maass.picard`, `mf.bianchi.hyperbolic3space`), given in coordinates by the explicit formula of
`HyperbolicThreeSpace.moebius`, is an action by isometries of the hyperbolic metric
`ds² = (dx₁² + dx₂² + dy²) / y²`, the metric `ds = |dz| / y` of the LMFDB, and it is faithful. So
`PSL(2, ℂ)` is a group of isometries of `ℋ₃`: it embeds in Tau Ceti's isometry group `Isom(ℋ₃)` of
the Riemannian manifold `ℋ₃`, whose elements are the diffeomorphisms whose differential preserves
the metric.

An upper triangular matrix `(a, b; 0, a⁻¹)` acts by `(x, y) ↦ (a²x + ab, |a|²y)`, a similarity of
`ℂ × ℝ` scaling the height by `|a|²`, which is an isometry (`TauCeti.UpperHalfSpace.similarity`).
The matrix `(0, -1; 1, 0)` acts by `(x, y) ↦ (-x̄, y) / (|x|² + y²)`: the inversion in the unit
sphere (`TauCeti.UpperHalfSpace.inversion`), followed by the isometry `(x, y) ↦ (-x̄, y)`. A matrix
`(a, b; c, d)` with `c ≠ 0` is the product `(c⁻¹, a; 0, c) (0, -1; 1, 0) (1, d / c; 0, 1)`. Only
`±1` fixes every point, as the fixed points of any other element of `SL(2, ℂ)` form a null set.

In the quaternions, with `z = x + yj`, the action is the linear fractional transformation
`z ↦ (az + b)(cz + d)⁻¹` of the LMFDB, for a representative `(a, b; c, d)` of determinant `1`.

## Main definitions

* `HyperbolicThreeSpace.pslToIsom` (LMFDB `mf.maass.picard`): the homomorphism
  `PSL(2, ℂ) → Isom(ℋ₃)`.
* `HyperbolicThreeSpace.toQuaternion`: the quaternion `x + yj` of a point `(x, y)` of `ℋ₃`.

## Main results

* `HyperbolicThreeSpace.pslToIsom_apply` (LMFDB `mf.maass.picard`): `pslToIsom γ` is the map
  `z ↦ γ z`.
* `HyperbolicThreeSpace.pslToIsom_injective` (LMFDB `mf.maass.picard`): the action of `PSL(2, ℂ)`
  is faithful.
* `HyperbolicThreeSpace.toQuaternion_smul` (LMFDB `mf.maass.picard`,
  `mf.bianchi.hyperbolic3space`): `γ z = (az + b)(cz + d)⁻¹` in the quaternions.
-/

open Complex Matrix MeasureTheory Quaternion TauCeti UpperHalfSpace

open scoped ComplexConjugate Manifold MatrixGroups

namespace HyperbolicThreeSpace

variable (g : SL(2, ℂ)) (γ : PSL(2, ℂ)) (z : HyperbolicThreeSpace) (w v w' v' : ℂ)

lemma coords_similarity (c : ℝ) (hc : 0 < c) (A : ℂ ≃ₗᵢ[ℝ] ℂ) (b : ℂ) :
    coords (similarity c hc A b z) = (c • A z.coords.1 + b, c * z.coords.2) := by
  rw [coords, coe_similarity_apply]
  rfl

variable {g} in
lemma coe_similarity_eq_smul (hg : g 1 0 = 0) (hc : 0 < ‖g 0 0‖ ^ 2) (ha : conj (g 0 0) ≠ 0) :
    ⇑(similarity (‖g 0 0‖ ^ 2) hc (rotation (Circle.ofConjDivSelf (conj (g 0 0)) ha))
      (g 0 0 * g 0 1)) = (g • ·) := by
  have hu : ((Circle.ofConjDivSelf (conj (g 0 0)) ha : Circle) : ℂ) = g 0 0 / conj (g 0 0) :=
    congrArg (· / conj (g 0 0)) (conj_conj (g 0 0))
  refine funext fun z ↦ coords_injective ?_
  rw [coords_similarity, coords_smul, moebius_eq_of_apply_one_zero hg, rotation_apply, hu,
    real_smul, ofReal_pow, ← mul_conj']
  refine Prod.ext ?_ rfl
  field_simp

variable {g} in
lemma exists_coe_eq_smul_of_apply_one_zero (hg : g 1 0 = 0) :
    ∃ Φ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) HyperbolicThreeSpace, ⇑Φ = (g • ·) := by
  have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one (mul_apply_one_one_eq_one_of_apply_one_zero hg)
  exact ⟨_, coe_similarity_eq_smul hg (by positivity) ((map_ne_zero _).mpr ha)⟩

/-- The matrix `(0, -1; 1, 0)` of `SL(2, ℂ)`. -/
private def slS : SL(2, ℂ) :=
  ⟨!![0, -1; 1, 0], by simp⟩

/-- The linear isometry `x ↦ -x̄` of `ℂ` over `ℝ`. -/
private noncomputable def negConjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  conjLIE.trans (LinearIsometryEquiv.neg ℝ)

/-- The isometry `(x, y) ↦ (-x̄, y) / (|x|² + y²)` of `ℋ₃`: the inversion in the unit sphere,
followed by `(x, y) ↦ (-x̄, y)`. -/
private noncomputable def isomS : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) HyperbolicThreeSpace :=
  similarity 1 one_pos negConjLIE 0 * inversion (0 : ℂ) 1 one_ne_zero

private lemma coe_isomS : ⇑isomS = (slS • ·) := by
  funext z
  refine coords_injective ?_
  have hN : ‖(z : WithLp 2 (ℂ × ℝ))‖ ^ 2 = moebiusDenom slS z.coords := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [moebiusDenom, slS, normSq_eq_norm_sq]
    rfl
  have hi :
      coords (inversion (0 : ℂ) 1 one_ne_zero z) = (‖(z : WithLp 2 (ℂ × ℝ))‖ ^ 2)⁻¹ • z.coords := by
    simp only [coords, coe_inversion_apply, EuclideanGeometry.inversion, Prod.mk_zero_zero,
      WithLp.toLp_zero, dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero, one_div,
      inv_pow, WithLp.ofLp_smul]
  rw [isomS, RiemannianIsometry.mul_apply, coords_similarity, coords_smul, hi, hN]
  refine Prod.ext ?_ ?_
  · simp [negConjLIE, moebius, slS, div_eq_inv_mul]
  · simp [moebius, div_eq_inv_mul]

lemma exists_coe_eq_smul :
    ∃ Φ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) HyperbolicThreeSpace, ⇑Φ = (g • ·) := by
  by_cases hc : g 1 0 = 0
  · exact exists_coe_eq_smul_of_apply_one_zero hc
  let p : SL(2, ℂ) := ⟨!![(g 1 0)⁻¹, g 0 0; 0, g 1 0], by simp [hc]⟩
  let q : SL(2, ℂ) := ⟨!![1, g 1 1 / g 1 0; 0, 1], by simp⟩
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := g.fin_two_mul_sub_mul_eq_one
  have hg : g = p * slS * q := by
    refine Subtype.ext ?_
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [p, slS, q]
    · field_simp
      linear_combination -hdet
    · field_simp
  rcases exists_coe_eq_smul_of_apply_one_zero (g := p) rfl with ⟨Φ, hΦ⟩
  rcases exists_coe_eq_smul_of_apply_one_zero (g := q) rfl with ⟨Ψ, hΨ⟩
  refine ⟨Φ * isomS * Ψ, ?_⟩
  rw [RiemannianIsometry.coe_mul, RiemannianIsometry.coe_mul, hΦ, hΨ, coe_isomS, hg]
  funext z
  simp [mul_smul]

lemma exists_coe_eq_smul_psl :
    ∃ Φ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) HyperbolicThreeSpace, ⇑Φ = (γ • ·) :=
  QuotientGroup.induction_on γ exists_coe_eq_smul

/-- The homomorphism `PSL(2, ℂ) → Isom(ℋ₃)` (LMFDB `mf.maass.picard`): `γ ∈ PSL(2, ℂ)` acts on
hyperbolic 3-space `ℋ₃` by the isometry `z ↦ γ z` of the hyperbolic metric
`ds² = (dx₁² + dx₂² + dy²) / y²` (`pslToIsom_apply`), and the action is faithful
(`pslToIsom_injective`). -/
noncomputable def pslToIsom : PSL(2, ℂ) →* Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) HyperbolicThreeSpace where
  toFun γ := (exists_coe_eq_smul_psl γ).choose
  map_one' := RiemannianIsometry.ext fun z ↦ by
    rw [congrFun (exists_coe_eq_smul_psl 1).choose_spec z, one_smul, RiemannianIsometry.one_apply]
  map_mul' γ δ := RiemannianIsometry.ext fun z ↦ by
    rw [RiemannianIsometry.mul_apply, congrFun (exists_coe_eq_smul_psl (γ * δ)).choose_spec z,
      congrFun (exists_coe_eq_smul_psl δ).choose_spec z,
      congrFun (exists_coe_eq_smul_psl γ).choose_spec, mul_smul]

/-- **`PSL(2, ℂ)` acts on `ℋ₃` by isometries** (LMFDB `mf.maass.picard`): the isometry
`pslToIsom γ` of the hyperbolic metric is the map `z ↦ γ z`. -/
lemma pslToIsom_apply : pslToIsom γ z = γ • z :=
  congrFun (exists_coe_eq_smul_psl γ).choose_spec z

/-- **`PSL(2, ℂ)` is a group of isometries of `ℋ₃`** (LMFDB `mf.maass.picard`): the action is
faithful, as the fixed points of `g ∈ SL(2, ℂ)`, `g ≠ ±1`, form a null set. -/
lemma pslToIsom_injective : Function.Injective pslToIsom := by
  refine (injective_iff_map_eq_one _).mpr fun γ hγ ↦ ?_
  induction γ using QuotientGroup.induction_on with
  | H g =>
    have hfix : {z : HyperbolicThreeSpace | g • z = z} = Set.univ :=
      Set.eq_univ_of_forall fun z ↦ (pslToIsom_apply (QuotientGroup.mk g) z).symm.trans <| by
        rw [hγ, RiemannianIsometry.one_apply]
    by_contra h
    have h₁ : g ≠ 1 := by
      rintro rfl
      exact h rfl
    have h₂ : g ≠ -1 := by
      rintro rfl
      exact h <| (QuotientGroup.eq_one_iff _).mpr <|
        SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)
    have h₀ : hyperbolicVolume {z : HyperbolicThreeSpace | g • z = z} = 0 :=
      hyperbolicVolume_setOf_smul_eq_self g h₁ h₂
    rw [hfix] at h₀
    exact isOpen_univ.measure_ne_zero hyperbolicVolume ⟨basePoint, trivial⟩ h₀

/-- The quaternion `x + yj` of a point `z = (x, y)` of hyperbolic 3-space, where `x = x₁ + x₂ i`:
the embedding of `ℋ₃` in the quaternions `ℍ` of the LMFDB (`mf.bianchi.hyperbolic3space`). -/
noncomputable def toQuaternion : ℍ[ℝ] :=
  ⟨z.coords.1.re, z.coords.1.im, z.coords.2, 0⟩

/-- The quaternion `w + vj`, for `w, v ∈ ℂ`. -/
private def qpair : ℍ[ℝ] :=
  ⟨w.re, w.im, v.re, v.im⟩

private lemma qpair_mul :
    qpair w v * qpair w' v' = qpair (w * w' - v * conj v') (w * v' + v * conj w') := by
  ext <;> simp [qpair] <;> ring1

private lemma qpair_add : qpair w v + qpair w' v' = qpair (w + w') (v + v') := by
  ext <;> simp [qpair]

private lemma coeComplex_eq_qpair : (w : ℍ[ℝ]) = qpair w 0 := by
  ext <;> simp [qpair]

variable {v} in
private lemma qpair_ne_zero_of_snd_ne_zero (h : v ≠ 0) : qpair w v ≠ 0 :=
  fun h₀ ↦ h <| Complex.ext (congrArg QuaternionAlgebra.imJ h₀) (congrArg QuaternionAlgebra.imK h₀)

variable {w} in
private lemma qpair_ne_zero_of_fst_ne_zero (h : w ≠ 0) : qpair w v ≠ 0 :=
  fun h₀ ↦ h <| Complex.ext (congrArg QuaternionAlgebra.re h₀) (congrArg QuaternionAlgebra.imI h₀)

/-- **The action of `SL(2, ℂ)` on `ℋ₃` is the linear fractional transformation
`z ↦ (az + b)(cz + d)⁻¹`** (LMFDB `mf.maass.picard`, `mf.bianchi.hyperbolic3space`): for
`g = (a, b; c, d)` of determinant `1` and `z = x + yj` in the quaternions, `g z` is the quaternion
`(az + b)(cz + d)⁻¹`. -/
lemma toQuaternion_smul : toQuaternion (g • z) = (g 0 0 * toQuaternion z + g 0 1) *
    (g 1 0 * toQuaternion z + g 1 1)⁻¹ := by
  have hz : toQuaternion z = qpair z.coords.1 z.coords.2 := by
    ext <;> simp [toQuaternion, qpair]
  have hgz : toQuaternion (g • z) = qpair (g • z).coords.1 (g • z).coords.2 := by
    ext <;> simp [toQuaternion, qpair]
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := g.fin_two_mul_sub_mul_eq_one
  have hy : 0 < z.coords.2 := coords_snd_pos z
  have hN : (moebiusDenom g z.coords : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (moebiusDenom_pos g hy).ne'
  have hN' : (moebiusDenom g z.coords : ℂ) =
      (g 1 0 * z.coords.1 + g 1 1) * conj (g 1 0 * z.coords.1 + g 1 1) +
        g 1 0 * conj (g 1 0) * (z.coords.2 : ℂ) ^ 2 := by
    rw [moebiusDenom, ofReal_add, ofReal_mul, ← mul_conj, ← mul_conj, ofReal_pow]
  have hx : (g • z).coords.1 = ((g 0 0 * z.coords.1 + g 0 1) * conj (g 1 0 * z.coords.1 + g 1 1) +
      g 0 0 * conj (g 1 0) * (z.coords.2 : ℂ) ^ 2) / (moebiusDenom g z.coords : ℂ) := by
    simp only [coords_smul, moebius, ofReal_pow]
  have hy' : ((g • z).coords.2 : ℂ) = (z.coords.2 : ℂ) / (moebiusDenom g z.coords : ℂ) := by
    simp only [coords_smul, moebius, ofReal_div]
  have hc : qpair (g 1 0 * z.coords.1 + g 1 1) (g 1 0 * z.coords.2) ≠ 0 := by
    by_cases hc : g 1 0 = 0
    · refine qpair_ne_zero_of_fst_ne_zero _ ?_
      rw [hc, zero_mul, zero_add]
      intro hd
      rw [hc, hd] at hdet
      simp at hdet
    · exact qpair_ne_zero_of_snd_ne_zero _ (mul_ne_zero hc (ofReal_ne_zero.mpr hy.ne'))
  rw [hz, hgz, coeComplex_eq_qpair, coeComplex_eq_qpair, coeComplex_eq_qpair, coeComplex_eq_qpair,
    qpair_mul, qpair_mul, qpair_add, qpair_add]
  simp only [zero_mul, sub_zero, add_zero]
  refine (eq_mul_inv_iff_mul_eq₀ hc).mpr ?_
  rw [qpair_mul, hx, hy', map_mul, conj_ofReal]
  congr 1
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div, div_eq_iff hN, hN']
    linear_combination (conj (g 1 0) * (z.coords.2 : ℂ) ^ 2) * hdet
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hN, hN']
    linear_combination (-(z.coords.2 : ℂ) * conj (g 1 0 * z.coords.1 + g 1 1)) * hdet

end HyperbolicThreeSpace
