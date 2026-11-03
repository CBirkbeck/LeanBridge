import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.Level
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonProduct
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Instances.Matrix

/-!
# The Siegel upper half-space as a topological space, and proper discontinuity

The Siegel upper half-space `ℋ_g` carries the topology induced by its coordinates
`SiegelUpperHalfSpace.toCoords`, which identify it with an open subset of `ℂ^{g(g + 1) / 2}`; this
topology is second countable, locally compact and Hausdorff, it induces the measurable structure of
`ℋ_g`, and `Sp(2g, ℝ)` acts on it continuously.

The action of an arithmetic subgroup `Γ` of `Sp(2g, ℚ)` on `ℋ_g` is properly discontinuous. Let `K`,
`L` be compact and `γ = (a, b; c, d) ∈ Sp(2g, ℝ)` with `τ ∈ K` and `γτ ∈ L`. From
`Im τ = Jᴴ Im(γτ) J` for `J = cτ + d`, the matrix `J` is bounded in terms of `K` and `L`, hence so
is `aτ + b = (γτ) J`. A row `(u, v)` of `γ` is recovered from `uτ + v`, the imaginary part giving
`u` and then the real part `v`, so `γ` is bounded. So only finitely many integral `γ` occur, and an
arithmetic subgroup is a finite union of translates of a subgroup of `Sp(2g, ℤ)`.

## Main results

* The instances `T2Space`, `SecondCountableTopology`, `LocallyCompactSpace` and `BorelSpace` of
  `SiegelUpperHalfSpace l`.
* `SiegelUpperHalfSpace.isOpenEmbedding_toCoords`: the coordinates are an open embedding.
* `SiegelUpperHalfSpace.continuous_val`: the matrix of a point depends continuously on the point.
* The instance `ContinuousConstSMul (symplecticGroup l ℝ) (SiegelUpperHalfSpace l)`.
* `SiegelUpperHalfSpace.exists_abs_apply_le_of_isCompact`: the elements of `Sp(2g, ℝ)` moving a
  compact set `K` into a compact set `L` are bounded.
* `SiegelUpperHalfSpace.finite_setOf_smul_mem_of_isArithmetic`: an arithmetic subgroup has finitely
  many elements moving a point of `K` into `L`.
* `SiegelUpperHalfSpace.properlyDiscontinuousSMul_transformationGroup`: an arithmetic subgroup acts
  properly discontinuously on `ℋ_g`.
-/

open Complex Matrix Set Topology

open scoped ComplexOrder

namespace SiegelUpperHalfSpace

variable {l : Type*}

lemma continuous_toCoords : Continuous (toCoords (l := l)) :=
  continuous_induced_dom

lemma isEmbedding_toCoords : IsEmbedding (toCoords (l := l)) :=
  ⟨⟨rfl⟩, toCoords_injective⟩

instance : T2Space (SiegelUpperHalfSpace l) :=
  isEmbedding_toCoords.t2Space

/-- **The matrix of a point of `ℋ_g` depends continuously on the point.** -/
lemma continuous_val : Continuous fun τ : SiegelUpperHalfSpace l ↦ τ.val :=
  continuous_matrix fun i j ↦ by
    have e : (fun τ : SiegelUpperHalfSpace l ↦ τ.val i j) = fun τ ↦ τ.toCoords s(i, j) :=
      funext fun τ ↦ congrFun (congrFun (ofSymCoords_toCoords τ).symm i) j
    rw [e]
    exact (continuous_apply _).comp continuous_toCoords

lemma continuous_im_apply (i j : l) : Continuous fun τ : SiegelUpperHalfSpace l ↦ (τ.val i j).im :=
  Complex.continuous_im.comp <| (continuous_apply_apply i j).comp continuous_val

lemma continuous_re_apply (i j : l) : Continuous fun τ : SiegelUpperHalfSpace l ↦ (τ.val i j).re :=
  Complex.continuous_re.comp <| (continuous_apply_apply i j).comp continuous_val

variable [Fintype l]

/-- **The coordinates of the Siegel upper half-space are an open embedding** into
`ℂ^{g(g + 1) / 2}`. -/
lemma isOpenEmbedding_toCoords : IsOpenEmbedding (toCoords (l := l)) :=
  ⟨isEmbedding_toCoords, by
    rw [range_toCoords]
    exact isOpen_coordSet⟩

instance : SecondCountableTopology (SiegelUpperHalfSpace l) :=
  isEmbedding_toCoords.secondCountableTopology

instance : LocallyCompactSpace (SiegelUpperHalfSpace l) :=
  isOpenEmbedding_toCoords.locallyCompactSpace

instance : BorelSpace (SiegelUpperHalfSpace l) :=
  measurableEmbedding_toCoords.borelSpace isEmbedding_toCoords.isInducing

variable {K L : Set (SiegelUpperHalfSpace l)}

/-! ### Uniform bounds on compact sets -/

private lemma exists_pos_mul_pow_le {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {K : Set α} (hK : IsCompact K) {g : α → E → ℝ}
    (hg : Continuous fun p : α × E ↦ g p.1 p.2) {n : ℕ} (hn : n ≠ 0)
    (hpos : ∀ x ∈ K, ∀ v, v ≠ 0 → 0 < g x v)
    (hhom : ∀ x (r : ℝ) v, 0 < r → g x (r • v) = r ^ n * g x v) (h₀ : ∀ x, g x 0 = 0) :
    ∃ c > 0, ∀ x ∈ K, ∀ v, c * ‖v‖ ^ n ≤ g x v := by
  have hc : IsCompact (K ×ˢ Metric.sphere (0 : E) 1) := hK.prod (isCompact_sphere 0 1)
  have key (c : ℝ) (hc₀ : ∀ x ∈ K, ∀ u ∈ Metric.sphere (0 : E) 1, c ≤ g x u) (x : α) (hx : x ∈ K)
      (v : E) : c * ‖v‖ ^ n ≤ g x v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp [h₀, hn]
    have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv'.ne']
    have e : v = ‖v‖ • ‖v‖⁻¹ • v := by
      rw [smul_smul, mul_inv_cancel₀ hv'.ne', one_smul]
    rw [e, hhom x ‖v‖ _ hv', ← e, mul_comm]
    exact mul_le_mul_of_nonneg_left (hc₀ x hx _ hu) (by positivity)
  rcases (K ×ˢ Metric.sphere (0 : E) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, key 1 fun x hx u hu ↦ ?_⟩
    have hm : (x, u) ∈ K ×ˢ Metric.sphere (0 : E) 1 := ⟨hx, hu⟩
    rw [he] at hm
    exact hm.elim
  rcases hc.exists_isMinOn hne hg.continuousOn with ⟨⟨x₀, u₀⟩, ⟨hx₀, hu₀⟩, hmin⟩
  have hu₀' : u₀ ≠ 0 := fun h ↦ by
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu₀
    exact zero_ne_one hu₀
  exact ⟨g x₀ u₀, hpos x₀ hx₀ u₀ hu₀', key _ fun x hx u hu ↦ hmin (mk_mem_prod hx hu)⟩

private lemma exists_norm_val_le (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ τ ∈ K, ∀ i j, ‖τ.val i j‖ ≤ C := by
  have hc : Continuous fun τ : SiegelUpperHalfSpace l ↦ fun p : l × l ↦ τ.val p.1 p.2 :=
    continuous_pi fun p ↦ (continuous_apply_apply p.1 p.2).comp continuous_val
  rcases hK.exists_bound_of_continuousOn hc.continuousOn with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, fun τ hτ i j ↦ ?_⟩
  exact ((norm_le_pi_norm (fun p : l × l ↦ τ.val p.1 p.2) (i, j)).trans (hC τ hτ)).trans
    (le_max_left _ _)

private lemma exists_pos_mul_normSq_le (hL : IsCompact L) : ∃ ε > 0, ∀ τ ∈ L, ∀ v : l → ℂ,
    ε * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (((τ.val.map im).map ofReal) *ᵥ v)).re := by
  refine exists_pos_mul_pow_le hL (g := fun τ v ↦ (star v ⬝ᵥ (((τ.val.map im).map ofReal) *ᵥ v)).re)
    ?_ two_ne_zero (fun τ _ v hv ↦ ?_) (fun τ r v hr ↦ ?_) fun τ ↦ by simp
  · refine Complex.continuous_re.comp ?_
    have hm : Continuous fun p : SiegelUpperHalfSpace l × (l → ℂ) ↦ (p.1.val.map im).map ofReal :=
      continuous_matrix fun i j ↦ Complex.continuous_ofReal.comp
        ((continuous_im_apply i j).comp continuous_fst)
    exact (continuous_snd.star).dotProduct (hm.matrix_mulVec continuous_snd)
  · have h : 0 < star v ⬝ᵥ (((τ.val.map im).map ofReal) *ᵥ v) :=
      (posDef_map_ofReal_iff.mpr τ.posDef_im).dotProduct_mulVec_pos hv
    exact (Complex.lt_def.mp h).1
  · have e : star (r • v) ⬝ᵥ (((τ.val.map im).map ofReal) *ᵥ (r • v)) =
        ((r ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ (((τ.val.map im).map ofReal) *ᵥ v)) := by
      have e₁ : r • v = (r : ℂ) • v := by
        ext i
        simp
      rw [e₁, mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
      simp [pow_two, mul_assoc]
    rw [e, Complex.re_ofReal_mul]

variable [DecidableEq l] (γ : symplecticGroup l ℝ)

instance : ContinuousConstSMul (symplecticGroup l ℝ) (SiegelUpperHalfSpace l) where
  continuous_const_smul γ := by
    refine continuous_induced_rng.mpr ?_
    have e : (toCoords ∘ fun τ : SiegelUpperHalfSpace l ↦ γ • τ) = moebiusCoords γ ∘ toCoords :=
      funext fun τ ↦ toCoords_smul τ γ
    rw [e]
    refine ContinuousOn.comp_continuous (s := coordSet l) (fun h hh ↦ ?_) continuous_toCoords
      toCoords_mem_coordSet
    exact (hasFDerivAt_moebiusCoords h γ
      (isUnit_denom γ (ofCoords h hh))).continuousAt.continuousWithinAt

/-- The vector `(u τ + v)` for a real row `w = (u, v)` and a point `τ` of `ℋ_g`. -/
private noncomputable def rowTerm (τ : SiegelUpperHalfSpace l) (w : l ⊕ l → ℝ) : l → ℂ :=
  fun m ↦ ∑ k, (w (.inl k) : ℂ) * τ.val k m + (w (.inr m) : ℂ)

private lemma rowTerm_eq_zero {τ : SiegelUpperHalfSpace l} {w : l ⊕ l → ℝ} (h : rowTerm τ w = 0) :
    w = 0 := by
  have hu : (fun k ↦ w (.inl k)) ᵥ* τ.val.map im = 0 := by
    ext m
    have h₁ : (∑ k, (w (.inl k) : ℂ) * τ.val k m + (w (.inr m) : ℂ)).im = 0 := by
      have h₂ : rowTerm τ w m = 0 := congrFun h m
      rw [rowTerm] at h₂
      rw [h₂, zero_im]
    simpa [vecMul, dotProduct] using h₁
  have hT : (τ.val.map im)ᵀ = τ.val.map im := by
    rw [← transpose_map, τ.transpose_val]
  have hu₀ : (fun k ↦ w (.inl k)) = 0 := by
    have hu₁ : τ.val.map im *ᵥ (fun k ↦ w (.inl k)) = 0 := by
      have h₁ : (τ.val.map im)ᵀ *ᵥ (fun k ↦ w (.inl k)) = (fun k ↦ w (.inl k)) ᵥ* τ.val.map im :=
        mulVec_transpose _ _
      rw [hT] at h₁
      rw [h₁, hu]
    have hdet : IsUnit (τ.val.map im) := τ.posDef_im.isUnit
    exact (mulVec_injective_of_isUnit hdet) (hu₁.trans (mulVec_zero _).symm)
  have hul (k : l) : w (.inl k) = 0 := congrFun hu₀ k
  ext (k | k)
  · exact hul k
  · have h₂ : rowTerm τ w k = 0 := congrFun h k
    simpa [rowTerm, hul] using h₂

private lemma exists_pos_mul_norm_le_rowTerm (hK : IsCompact K) :
    ∃ c > 0, ∀ τ ∈ K, ∀ w : l ⊕ l → ℝ, c * ‖w‖ ≤ ‖rowTerm τ w‖ := by
  have hcont : Continuous fun p : SiegelUpperHalfSpace l × (l ⊕ l → ℝ) ↦ ‖rowTerm p.1 p.2‖ := by
    refine (continuous_pi fun m ↦ ?_).norm
    refine (continuous_finsetSum _ fun k _ ↦ ?_).add ?_
    · exact (Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_snd)).mul
        ((continuous_apply_apply k m).comp (continuous_val.comp continuous_fst))
    · exact Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_snd)
  have hhom (τ : SiegelUpperHalfSpace l) (r : ℝ) (w : l ⊕ l → ℝ) (hr : 0 < r) :
      ‖rowTerm τ (r • w)‖ = r ^ 1 * ‖rowTerm τ w‖ := by
    have e : rowTerm τ (r • w) = (r : ℂ) • rowTerm τ w := by
      ext m
      simp [rowTerm, Finset.mul_sum, mul_add, mul_assoc]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, pow_one]
  have h₀ (τ : SiegelUpperHalfSpace l) : ‖rowTerm τ 0‖ = 0 := by
    have e : rowTerm τ 0 = 0 := by
      ext m
      simp [rowTerm]
    rw [e, norm_zero]
  rcases exists_pos_mul_pow_le hK hcont one_ne_zero
    (fun τ _ w hw ↦ norm_pos_iff.mpr fun h ↦ hw (rowTerm_eq_zero h)) hhom h₀ with ⟨c, hc, h⟩
  exact ⟨c, hc, fun τ hτ w ↦ by simpa using h τ hτ w⟩

private lemma rowTerm_inl (τ : SiegelUpperHalfSpace l) (i : l) :
    rowTerm τ ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) (.inl i)) = num γ τ.val i := by
  ext m
  simp [rowTerm, num, toBlocks₁₁, toBlocks₁₂, Matrix.mul_apply]

private lemma rowTerm_inr (τ : SiegelUpperHalfSpace l) (i : l) :
    rowTerm τ ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) (.inr i)) = denom γ τ.val i := by
  ext m
  simp [rowTerm, denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]

private lemma star_mulVec_dotProduct_eq (τ : SiegelUpperHalfSpace l) (m : l) :
    star (denom γ τ.val *ᵥ Pi.single m 1) ⬝ᵥ
      ((((γ • τ).val.map im).map ofReal) *ᵥ (denom γ τ.val *ᵥ Pi.single m 1)) = (τ.val m m).im := by
  have hJ : IsUnit (denom γ τ.val).det := isUnit_det_denom γ τ
  have e : (denom γ τ.val)ᴴ * (((γ • τ).val.map im).map ofReal) * denom γ τ.val =
      (τ.val.map im).map ofReal := by
    rw [map_im_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
      nonsing_inv_mul _ hJ, conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc,
      nonsing_inv_mul _ hJ, Matrix.mul_one]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, e]
  simp [dotProduct, Pi.single_apply]

/-- **The elements of `Sp(2g, ℝ)` moving a compact set into a compact set are bounded**: if
`τ ∈ K` and `γτ ∈ L` for `γ = (a, b; c, d)`, then `Im τ = Jᴴ Im(γτ) J` for `J = cτ + d` bounds `J`,
then `aτ + b = (γτ) J` is bounded, and a row of `γ` is recovered from these. -/
lemma exists_abs_apply_le_of_isCompact (hK : IsCompact K) (hL : IsCompact L) : ∃ M : ℝ,
    ∀ γ : symplecticGroup l ℝ, ∀ τ ∈ K, γ • τ ∈ L → ∀ x y, |(γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x y| ≤
      M := by
  rcases exists_pos_mul_normSq_le hL with ⟨ε, hε, hεL⟩
  rcases exists_norm_val_le hK with ⟨CK, hCK₀, hCK⟩
  rcases exists_norm_val_le hL with ⟨CL, hCL₀, hCL⟩
  rcases exists_pos_mul_norm_le_rowTerm hK with ⟨c, hc, hcK⟩
  let A : ℝ := √(CK / ε)
  let B : ℝ := A + Fintype.card l * (CL * A)
  have hA₀ : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨B / c, fun γ τ hτ hγτ x y ↦ ?_⟩
  have hJ (i m : l) : ‖denom γ τ.val i m‖ ≤ A := by
    have h₁ : ε * ‖denom γ τ.val *ᵥ Pi.single m 1‖ ^ 2 ≤ (star (denom γ τ.val *ᵥ Pi.single m 1) ⬝ᵥ
        (((γ • τ).val.map im).map ofReal *ᵥ denom γ τ.val *ᵥ Pi.single m 1)).re :=
      hεL (γ • τ) hγτ (denom γ τ.val *ᵥ Pi.single m 1)
    rw [star_mulVec_dotProduct_eq, ofReal_re] at h₁
    have h₂ : (τ.val m m).im ≤ CK := (abs_le.mp (Complex.abs_im_le_norm _)).2.trans (hCK τ hτ m m)
    have h₃ : ‖denom γ τ.val *ᵥ Pi.single m 1‖ ^ 2 ≤ CK / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      exact h₁.trans h₂
    have h₄ : ‖denom γ τ.val *ᵥ Pi.single m 1‖ ≤ A := Real.le_sqrt_of_sq_le h₃
    have h₅ : ‖(denom γ τ.val *ᵥ Pi.single m 1) i‖ ≤ ‖denom γ τ.val *ᵥ Pi.single m 1‖ :=
      norm_le_pi_norm _ i
    have h₆ : (denom γ τ.val *ᵥ Pi.single m 1) i = denom γ τ.val i m := by
      simp
    rw [h₆] at h₅
    exact h₅.trans h₄
  have hN (i m : l) : ‖num γ τ.val i m‖ ≤ Fintype.card l * (CL * A) := by
    have e : num γ τ.val = (γ • τ).val * denom γ τ.val := by
      rw [val_smul, nonsing_inv_mul_cancel_right _ _ (isUnit_det_denom γ τ)]
    rw [e, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    have h₁ (k : l) : ‖(γ • τ).val i k * denom γ τ.val k m‖ ≤ CL * A := by
      rw [norm_mul]
      exact mul_le_mul (hCL _ hγτ i k) (hJ k m) (norm_nonneg _) hCL₀
    refine (Finset.sum_le_sum fun k _ ↦ h₁ k).trans_eq ?_
    simp
  have hrow : ‖rowTerm τ ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x)‖ ≤ B := by
    have hB : 0 ≤ B := by
      positivity
    refine (pi_norm_le_iff_of_nonneg hB).mpr fun m ↦ ?_
    rcases x with i | i
    · rw [rowTerm_inl]
      refine (hN i m).trans ?_
      simp only [B]
      linarith
    · rw [rowTerm_inr]
      refine (hJ i m).trans ?_
      simp only [B]
      have h₀ : 0 ≤ (Fintype.card l : ℝ) * (CL * A) := by
        positivity
      linarith
  have h₁ : c * ‖(γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x‖ ≤ B :=
    (hcK τ hτ _).trans hrow
  rw [le_div_iff₀ hc, mul_comm]
  have h₂ : |(γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x y| ≤ ‖(γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm ((γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x) y
  exact (mul_le_mul_of_nonneg_left h₂ hc.le).trans h₁

/-! ### Proper discontinuity -/

private lemma finite_setOf_smul_mem_integral (hK : IsCompact K) (hL : IsCompact L) :
    {γ : symplecticGroup l ℤ | ∃ τ ∈ K, SymplecticGroup.map (Int.castRingHom ℝ) γ • τ ∈
      L}.Finite := by
  rcases exists_abs_apply_le_of_isCompact hK hL with ⟨M, hM⟩
  let n : ℤ := ⌈M⌉
  have hfin : {A : l ⊕ l → l ⊕ l → ℤ | ∀ x, A x ∈ {a : l ⊕ l → ℤ | ∀ y, a y ∈ Icc (-n) n}}.Finite :=
    Finite.pi' fun _ ↦ Finite.pi' fun _ ↦ finite_Icc _ _
  refine Finite.of_finite_image (f := fun γ : symplecticGroup l ℤ ↦
    ((γ : Matrix (l ⊕ l) (l ⊕ l) ℤ) : l ⊕ l → l ⊕ l → ℤ)) (hfin.subset ?_)
      (fun _ _ _ _ h ↦ Subtype.ext h)
  rintro _ ⟨γ, ⟨τ, hτ, hγτ⟩, rfl⟩ x y
  have h : |(SymplecticGroup.map (Int.castRingHom ℝ) γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x y| ≤ M :=
    hM _ τ hτ hγτ x y
  simp only [SymplecticGroup.coe_map_apply, map_apply, eq_intCast, abs_le] at h
  refine ⟨?_, ?_⟩
  · have h₁ : ((-n : ℤ) : ℝ) ≤ ((γ : Matrix (l ⊕ l) (l ⊕ l) ℤ) x y : ℝ) := by
      push_cast
      linarith [Int.le_ceil M, h.1]
    exact_mod_cast h₁
  · have h₁ : ((γ : Matrix (l ⊕ l) (l ⊕ l) ℤ) x y : ℝ) ≤ (n : ℝ) :=
      h.2.trans (Int.le_ceil M)
    exact_mod_cast h₁

variable {Γ : Subgroup (symplecticGroup l ℚ)}

/-- **An arithmetic subgroup has finitely many elements moving a compact set `K` to meet a compact
set `L`**: it is a finite union of translates of a subgroup of `Sp(2g, ℤ)`. -/
lemma finite_setOf_smul_mem_of_isArithmetic (hΓ : SymplecticGroup.IsArithmetic Γ) (hK : IsCompact K)
    (hL : IsCompact L) : {γ : Γ | ∃ τ ∈ K,
      SymplecticGroup.map (algebraMap ℚ ℝ) (γ : symplecticGroup l ℚ) • τ ∈ L}.Finite := by
  have hi : ((SymplecticGroup.integral l).subgroupOf Γ).FiniteIndex := ⟨hΓ.2.relIndex_ne_zero⟩
  have hfinq : Finite (Γ ⧸ (SymplecticGroup.integral l).subgroupOf Γ) :=
    Subgroup.finite_quotient_of_finiteIndex
  let r : (Γ ⧸ (SymplecticGroup.integral l).subgroupOf Γ) → Γ := Quotient.out
  have hr (q) : IsCompact
      ((fun τ ↦ (SymplecticGroup.map (algebraMap ℚ ℝ) (r q : symplecticGroup l ℚ))⁻¹ • τ) '' L) :=
    hL.image (continuous_const_smul _)
  let A (q : Γ ⧸ (SymplecticGroup.integral l).subgroupOf Γ) : Set (symplecticGroup l ℤ) :=
    {γ | ∃ τ ∈ K, SymplecticGroup.map (Int.castRingHom ℝ) γ • τ ∈
      (fun τ ↦ (SymplecticGroup.map (algebraMap ℚ ℝ) (r q : symplecticGroup l ℚ))⁻¹ • τ) '' L}
  have hA (q) : (A q).Finite := finite_setOf_smul_mem_integral hK (hr q)
  have hinj : Function.Injective fun γ : Γ ↦ (γ : symplecticGroup l ℚ) := Subtype.val_injective
  refine Finite.of_finite_image (f := fun γ : Γ ↦ (γ : symplecticGroup l ℚ))
    ((finite_iUnion fun q ↦ (hA q).image fun γ ↦
      (r q : symplecticGroup l ℚ) * SymplecticGroup.map (Int.castRingHom ℚ) γ).subset ?_) hinj.injOn
  rintro _ ⟨γ, ⟨τ, hτ, hγτ⟩, rfl⟩
  let q : Γ ⧸ (SymplecticGroup.integral l).subgroupOf Γ := QuotientGroup.mk γ
  have hq : (r q)⁻¹ * γ ∈ (SymplecticGroup.integral l).subgroupOf Γ :=
    QuotientGroup.eq.mp (Quotient.out_eq q)
  rcases hq with ⟨δ, -, hδ⟩
  have hδ' : (γ : symplecticGroup l ℚ) =
      (r q : symplecticGroup l ℚ) * SymplecticGroup.map (Int.castRingHom ℚ) δ := by
    rw [hδ]
    simp
  have hmap (x : symplecticGroup l ℤ) : SymplecticGroup.map (algebraMap ℚ ℝ)
      (SymplecticGroup.map (Int.castRingHom ℚ) x) = SymplecticGroup.map (Int.castRingHom ℝ) x :=
    Subtype.ext <| by
      ext a b
      simp
  refine mem_iUnion.mpr ⟨q, δ, ⟨τ, hτ, ?_⟩, hδ'.symm⟩
  refine ⟨_, hγτ, ?_⟩
  simp only
  rw [hδ', map_mul, hmap, mul_smul, inv_smul_smul]

/-- **An arithmetic subgroup of `Sp(2g, ℚ)` acts properly discontinuously on `ℋ_g`.** -/
lemma properlyDiscontinuousSMul_transformationGroup (hΓ : SymplecticGroup.IsArithmetic Γ) :
    ProperlyDiscontinuousSMul (transformationGroup Γ) (SiegelUpperHalfSpace l) where
  finite_disjoint_inter_image {K L} hK hL := by
    refine ((finite_setOf_smul_mem_of_isArithmetic hΓ hK hL).image fun γ : Γ ↦
      (⟨_, (γ : symplecticGroup l ℚ), γ.2, rfl⟩ : transformationGroup Γ)).subset ?_
    rintro ⟨_, γ, hγ, rfl⟩ hg
    rcases hg with ⟨_, ⟨τ, hτ, rfl⟩, hτL⟩
    exact ⟨⟨γ, hγ⟩, ⟨τ, hτ, hτL⟩, rfl⟩

instance : ContinuousConstSMul (transformationGroup Γ) (SiegelUpperHalfSpace l) where
  continuous_const_smul g := by
    rcases g with ⟨_, γ, -, rfl⟩
    exact continuous_const_smul (SymplecticGroup.map (algebraMap ℚ ℝ) γ)

end SiegelUpperHalfSpace
