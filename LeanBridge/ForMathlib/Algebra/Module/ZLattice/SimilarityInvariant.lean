import LeanBridge.ForMathlib.Algebra.Module.ZLattice.Extreme
import LeanBridge.ForMathlib.Algebra.Module.ZLattice.Perfect
import LeanBridge.ForMathlib.LinearAlgebra.Lattice.RealLattice
import TauCeti.LinearAlgebra.BilinearForm.Ideals

/-!
# Similarity invariants of lattices

Lattices `L` and `M` are similar (LMFDB `lattice.similarity`) if `L` is isometric to `αM` for a
real constant `α ≠ 0` (`LinearMap.BilinForm.IsSimilarLattice`). Similarity is an equivalence
relation. Well-roundedness, eutaxy, perfection and the packing density are similarity invariants
of lattices of full rank in real inner product spaces, and a similarity class containing an
integral lattice whose form is not zero contains a primitive integral lattice (scale ideal `ℤ`, so
the entries of a Gram matrix have gcd `1`, LMFDB `lattice.primitive`), unique up to isometry.

An isometry `L ≅ αM` of lattices of full rank extends, through a `ℤ`-basis of `L`, which is a basis
of the space, to a similitude `ψ` of the ambient spaces, `⟪ψ v, ψ w⟫ = α⁻² ⟪v, w⟫`, with `ψ L = M`.
It multiplies the norms by `|α|⁻¹`, so it carries the minimal vectors of `L` onto those of `M`; it
multiplies the covolume by `|det ψ| = |α|⁻ⁿ` and the radius of the packing balls by `|α|⁻¹`; and,
`P` being its matrix, it carries `x xᵀ` to `P x xᵀ Pᵀ`, which preserves perfection.

Eutaxy and perfection depend on the ambient space, so they are invariants of lattices of full rank
only: `ℤ ⊆ ℝ` is eutactic and perfect, while the isometric `ℤ e₁ ⊆ ℝ²` is neither. The existence
of a primitive lattice in a similarity class needs a form that does not vanish on the lattice:
every lattice similar to the zero lattice, or to `ℤ v` with `v` isotropic, has the zero form.

## Main results

* `LinearMap.BilinForm.isSimilarLattice_refl`, `LinearMap.BilinForm.IsSimilarLattice.symm` and
  `LinearMap.BilinForm.IsSimilarLattice.trans`: similarity is an equivalence relation.
* `LinearMap.BilinForm.IsSimilarLattice.exists_linearEquiv`: similar lattices of full rank are
  related by a similitude of the ambient spaces.
* `LinearMap.BilinForm.IsSimilarLattice.relIndex_span_minimalVectors_eq`: the index of the
  sublattice spanned by the minimal vectors is a similarity invariant, so well-roundedness and
  generation by minimal vectors are.
* `LinearMap.BilinForm.IsSimilarLattice.isEutactic_iff`: eutaxy is a similarity invariant.
* `LinearMap.BilinForm.IsSimilarLattice.isPerfect_iff`: perfection is a similarity invariant.
* `LinearMap.BilinForm.IsSimilarLattice.packingDensity_eq`: the packing density is a similarity
  invariant.
* `LinearMap.BilinForm.scaleIdeal_integralForm_inv_sqrt_smul` and
  `LinearMap.BilinForm.exists_isSimilarLattice_scaleIdeal_eq_top`: an integral lattice whose form is
  not zero is similar to a primitive integral lattice.
* `LinearMap.BilinForm.IsSimilarLattice.exists_isometry`: similar primitive integral lattices are
  isometric.
-/

open Module MeasureTheory Matrix Submodule

open scoped InnerProductSpace Pointwise

open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {V W U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U] {B : BilinForm ℝ V} {B' : BilinForm ℝ W} {B'' : BilinForm ℝ U}
  {L : Submodule ℤ V} {M : Submodule ℤ W} {N : Submodule ℤ U}

variable (B L) in
/-- **Similarity is reflexive.** -/
lemma isSimilarLattice_refl : B.IsSimilarLattice L B L :=
  ⟨1, one_ne_zero, LinearEquiv.ofEq _ _ (one_smul ℝ L).symm, fun _ _ ↦ rfl⟩

/-- **Similarity is symmetric.** -/
lemma IsSimilarLattice.symm (h : B.IsSimilarLattice L B' M) : B'.IsSimilarLattice M B L := by
  rcases h with ⟨α, hα, e, he⟩
  let s : M ≃ₗ[ℤ] ↥(α • M) := equivMapOfInjective (DistribSMul.toLinearMap ℤ W α)
    (smul_right_injective W hα) M
  let t : L ≃ₗ[ℤ] ↥(α⁻¹ • L) := equivMapOfInjective (DistribSMul.toLinearMap ℤ V α⁻¹)
    (smul_right_injective V (inv_ne_zero hα)) L
  refine ⟨α⁻¹, inv_ne_zero hα, s.trans (e.symm.trans t), fun x y ↦ ?_⟩
  have hxy : B' (α • (x : W)) (α • (y : W)) = B (e.symm (s x)) (e.symm (s y)) := by
    rw [← he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl
  have ht (z : L) : (t z : V) = α⁻¹ • (z : V) :=
    rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, ht, ht, smul_left, smul_right, ← hxy, smul_left, smul_right]
  field_simp

/-- **Similarity is transitive.** -/
lemma IsSimilarLattice.trans (h : B.IsSimilarLattice L B' M) (h' : B'.IsSimilarLattice M B'' N) :
    B.IsSimilarLattice L B'' N := by
  rcases h with ⟨α, hα, e, he⟩
  rcases h' with ⟨β, hβ, e', he'⟩
  let s : M ≃ₗ[ℤ] ↥(α • M) := equivMapOfInjective (DistribSMul.toLinearMap ℤ W α)
    (smul_right_injective W hα) M
  let t : ↥(β • N) ≃ₗ[ℤ] ↥(α • β • N) := equivMapOfInjective
    (DistribSMul.toLinearMap ℤ U α) (smul_right_injective U hα) (β • N)
  refine ⟨α * β, mul_ne_zero hα hβ, e.trans (s.symm.trans (e'.trans (t.trans
    (LinearEquiv.ofEq _ _ (smul_smul α β N))))), fun x y ↦ ?_⟩
  have hs (z : ↥(α • M)) : α • (s.symm z : W) = z :=
    map_equivMapOfInjective_symm_apply _ _ _ z
  have h1 : B'' (e' (s.symm (e x))) (e' (s.symm (e y))) = B' (s.symm (e x)) (s.symm (e y)) :=
    he' _ _
  have ht (z : ↥(β • N)) : (t z : U) = α • (z : U) :=
    rfl
  rw [← he, ← hs (e x), ← hs (e y), smul_left, smul_right, ← h1, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, LinearEquiv.coe_ofEq_apply, ht, ht,
    smul_left, smul_right]

end LinearMap.BilinForm

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {L : Submodule ℤ E} {M : Submodule ℤ F} {ψ : E ≃ₗ[ℝ] F} {k : ℝ}

lemma norm_eq_sqrt_mul_norm (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ) (v : E) :
    ‖ψ v‖ = √k * ‖v‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (ψ v)), ← real_inner_self_eq_norm_sq, hψ,
    real_inner_self_eq_norm_sq, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)]

lemma minimum_eq_sqrt_mul_minimum (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ)
    (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M) : minimum M = √k * minimum L := by
  subst hLM
  have hset : norm '' ((L.map (ψ.restrictScalars ℤ).toLinearMap : Set F) \ {0}) =
      √k • norm '' ((L : Set E) \ {0}) := by
    ext r
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, ⟨⟨x, hx, rfl⟩, hx0⟩, rfl⟩
      exact ⟨‖x‖, ⟨x, ⟨hx, fun h ↦ hx0 (by rw [h, map_zero])⟩, rfl⟩,
        (norm_eq_sqrt_mul_norm hψ x).symm⟩
    · rintro ⟨-, ⟨x, ⟨hx, hx0⟩, rfl⟩, rfl⟩
      exact ⟨ψ x, ⟨⟨x, hx, rfl⟩, ψ.map_ne_zero_iff.mpr hx0⟩, norm_eq_sqrt_mul_norm hψ x⟩
  rw [minimum, minimum, hset, Real.sInf_smul_of_nonneg (Real.sqrt_nonneg k), smul_eq_mul]

lemma minimalVectors_eq_image (hk : 0 < k) (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ)
    (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M) :
    minimalVectors M = ψ '' minimalVectors L := by
  have hmin : minimum M = √k * minimum L := minimum_eq_sqrt_mul_minimum hψ hLM
  subst hLM
  ext y
  simp only [minimalVectors, mem_map, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy0, hy⟩
    refine ⟨x, ⟨hx, fun h ↦ hy0 (by rw [h, map_zero]), ?_⟩, rfl⟩
    rw [hmin, norm_eq_sqrt_mul_norm hψ] at hy
    exact mul_left_cancel₀ (Real.sqrt_ne_zero'.mpr hk) hy
  · rintro ⟨x, ⟨hx, hx0, hxn⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ψ.map_ne_zero_iff.mpr hx0, by rw [hmin, norm_eq_sqrt_mul_norm hψ, hxn]⟩

lemma relIndex_span_minimalVectors_eq (hk : 0 < k) (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ)
    (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M) :
    (span ℤ (minimalVectors M)).toAddSubgroup.relIndex M.toAddSubgroup =
      (span ℤ (minimalVectors L)).toAddSubgroup.relIndex L.toAddSubgroup := by
  have himg : ψ '' minimalVectors L = (ψ.restrictScalars ℤ).toLinearMap '' minimalVectors L :=
    rfl
  rw [minimalVectors_eq_image hk hψ hLM, himg, span_image, ← hLM, map_toAddSubgroup,
    map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ ψ.injective]

lemma IsEutactic.of_map_eq (h : IsEutactic L) (hk : 0 < k) (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ)
    (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M) : IsEutactic M := by
  rcases h with ⟨c, hc, h⟩
  refine ⟨fun y ↦ c (ψ.symm y) / k, ?_, fun w ↦ ?_⟩
  · rw [minimalVectors_eq_image hk hψ hLM]
    rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [LinearEquiv.symm_apply_apply]
    exact div_pos (hc x hx) hk
  · have hw : ⟪w, w⟫_ℝ = k * ⟪ψ.symm w, ψ.symm w⟫_ℝ := by
      rw [← hψ, LinearEquiv.apply_symm_apply]
    have hwx (x : E) : ⟪w, ψ x⟫_ℝ = k * ⟪ψ.symm w, x⟫_ℝ := by
      rw [← hψ, LinearEquiv.apply_symm_apply]
    rw [minimalVectors_eq_image hk hψ hLM, finsum_mem_image ψ.injective.injOn, hw, h (ψ.symm w),
      mul_finsum_mem]
    refine finsum_mem_congr rfl fun x _ ↦ ?_
    dsimp only
    rw [LinearEquiv.symm_apply_apply, hwx]
    field_simp

end ZLattice

namespace LinearMap.BilinForm

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {L : Submodule ℤ E}
  {M : Submodule ℤ F} [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology M] [IsZLattice ℝ M]

/-- **Similar lattices of full rank are related by a similitude of the ambient spaces**: if `L` is
isometric to `αM`, a real linear equivalence `ψ` with `⟪ψ v, ψ w⟫ = k ⟪v, w⟫`, `k = α⁻² > 0`,
carries `L` onto `M`. -/
lemma IsSimilarLattice.exists_linearEquiv (h : IsSimilarLattice (innerₗ E) L (innerₗ F) M) :
    ∃ ψ : E ≃ₗ[ℝ] F, ∃ k : ℝ, 0 < k ∧ (∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ) ∧
      L.map (ψ.restrictScalars ℤ).toLinearMap = M := by
  rcases h with ⟨α, hα, e, he⟩
  let g : L ≃ₗ[ℤ] M := e.trans
    (equivMapOfInjective (DistribSMul.toLinearMap ℤ F α) (smul_right_injective F hα) M).symm
  have hg (x : L) : α • (g x : F) = e x :=
    map_equivMapOfInjective_symm_apply _ (smul_right_injective F hα) M (e x)
  have hgg (x y : L) : ⟪(g x : F), g y⟫_ℝ = (α ^ 2)⁻¹ * ⟪(x : E), y⟫_ℝ := by
    have h1 : ⟪α • (g x : F), α • (g y : F)⟫_ℝ = ⟪(x : E), y⟫_ℝ := by
      rw [hg, hg]
      exact he x y
    rw [real_inner_smul_left, real_inner_smul_right] at h1
    rw [← h1]
    field_simp
  let b : Basis (Free.ChooseBasisIndex ℤ L) ℤ L := Free.chooseBasis ℤ L
  let ψ : E ≃ₗ[ℝ] F := (b.ofZLatticeBasis ℝ L).equiv ((b.map g).ofZLatticeBasis ℝ M) (.refl _)
  have hψb (i : Free.ChooseBasisIndex ℤ L) : ψ (b i) = g (b i) := by
    rw [← b.ofZLatticeBasis_apply ℝ L, Basis.equiv_apply, Equiv.refl_apply,
      Basis.ofZLatticeBasis_apply, Basis.map_apply]
  have hψg (x : L) : ψ x = g x := by
    have hext : (ψ.restrictScalars ℤ).toLinearMap ∘ₗ L.subtype = M.subtype ∘ₗ g.toLinearMap :=
      b.ext hψb
    exact LinearMap.congr_fun hext x
  refine ⟨ψ, (α ^ 2)⁻¹, by positivity, fun v w ↦ ?_, ?_⟩
  · have hB : (innerₗ F).compl₁₂ ψ.toLinearMap ψ.toLinearMap = (α ^ 2)⁻¹ • innerₗ E :=
      LinearMap.ext_basis (b.ofZLatticeBasis ℝ L) (b.ofZLatticeBasis ℝ L) fun i j ↦ by
        simp [hψb, hgg]
    exact LinearMap.congr_fun₂ hB v w
  · ext y
    refine ⟨?_, fun hy ↦ ⟨g.symm ⟨y, hy⟩, (g.symm ⟨y, hy⟩).2, ?_⟩⟩
    · rintro ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, hψg ⟨x, hx⟩]
      exact (g ⟨x, hx⟩).2
    · rw [LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, hψg, LinearEquiv.apply_symm_apply]

/-- **The index of the sublattice spanned by the minimal vectors is a similarity invariant**
(LMFDB `lattice.similarity`): similar lattices `L` and `M` of full rank in real inner product
spaces have `[L : ⟨S(L)⟩] = [M : ⟨S(M)⟩]`, `S` the set of minimal vectors. So similarity preserves
well-roundedness (LMFDB `lattice.well_rounded`: finite index) and generation by minimal vectors
(index `1`). -/
lemma IsSimilarLattice.relIndex_span_minimalVectors_eq
    (h : IsSimilarLattice (innerₗ E) L (innerₗ F) M) :
    (span ℤ (ZLattice.minimalVectors M)).toAddSubgroup.relIndex M.toAddSubgroup =
      (span ℤ (ZLattice.minimalVectors L)).toAddSubgroup.relIndex L.toAddSubgroup := by
  rcases h.exists_linearEquiv with ⟨ψ, k, hk, hψ, hLM⟩
  exact ZLattice.relIndex_span_minimalVectors_eq hk hψ hLM

/-- **Eutaxy is a similarity invariant** (LMFDB `lattice.similarity`, `lattice.eutactic`): of two
similar lattices of full rank in real inner product spaces, one is eutactic exactly when the other
is. -/
lemma IsSimilarLattice.isEutactic_iff (h : IsSimilarLattice (innerₗ E) L (innerₗ F) M) :
    ZLattice.IsEutactic L ↔ ZLattice.IsEutactic M := by
  rcases h.exists_linearEquiv with ⟨ψ, k, hk, hψ, hLM⟩
  rcases h.symm.exists_linearEquiv with ⟨ψ', k', hk', hψ', hML⟩
  exact ⟨fun hL ↦ hL.of_map_eq hk hψ hLM, fun hM ↦ hM.of_map_eq hk' hψ' hML⟩

end LinearMap.BilinForm

namespace ZLattice

variable {ι : Type*} [Fintype ι] {L M : Submodule ℤ (EuclideanSpace ℝ ι)}
  {ψ : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι} {k : ℝ}

lemma IsPerfect.of_map_eq (h : IsPerfect L) (hk : 0 < k) (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ)
    (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M) : IsPerfect M := by
  classical
  intro A hA
  let P : Matrix ι ι ℝ := (toLpLin 2 2).symm ψ.toLinearMap
  let Q : Matrix ι ι ℝ := (toLpLin 2 2).symm ψ.symm.toLinearMap
  have hP : toLpLin 2 2 P = ψ.toLinearMap := LinearEquiv.apply_symm_apply _ _
  have hPQ : P * Q = 1 := by
    rw [← toLpLin_symm_comp (q := 2), LinearEquiv.comp_symm, toLpLin_symm_id]
  let T : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ := (LinearMap.mulLeft ℝ P) ∘ₗ LinearMap.mulRight ℝ Pᵀ
  have hT (x : EuclideanSpace ℝ ι) :
      T (vecMulVec x.ofLp x.ofLp) = vecMulVec (ψ x).ofLp (ψ x).ofLp := by
    rw [← LinearEquiv.coe_coe ψ, ← hP, toLpLin_apply, WithLp.ofLp_toLp, LinearMap.comp_apply,
      LinearMap.mulRight_apply, LinearMap.mulLeft_apply, vecMulVec_mul, mul_vecMulVec,
      vecMul_transpose]
  have hQA : (Q * A * Qᵀ).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, hA.eq, mul_assoc]
  have hTQA : T (Q * A * Qᵀ) = A := by
    rw [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, ← mul_assoc,
      ← mul_assoc, ← mul_assoc, hPQ, one_mul, mul_assoc, ← transpose_mul, hPQ, transpose_one,
      mul_one]
  have himg : (fun y : EuclideanSpace ℝ ι ↦ vecMulVec y.ofLp y.ofLp) '' minimalVectors M =
      T '' ((fun x : EuclideanSpace ℝ ι ↦ vecMulVec x.ofLp x.ofLp) '' minimalVectors L) := by
    rw [minimalVectors_eq_image hk hψ hLM, Set.image_image, Set.image_image]
    exact Set.image_congr fun x _ ↦ (hT x).symm
  rw [← hTQA, himg, span_image]
  exact mem_map_of_mem (h _ hQA)

lemma covolume_eq_abs_det_mul [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology M]
    [IsZLattice ℝ M] (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M) :
    covolume M = |LinearMap.det ψ.toLinearMap| * covolume L := by
  classical
  let b : Basis (Free.ChooseBasisIndex ℤ L) ℤ L := Free.chooseBasis ℤ L
  let g : L ≃ₗ[ℤ] M := ((ψ.restrictScalars ℤ).submoduleMap L).trans (LinearEquiv.ofEq _ _ hLM)
  have hb : ((↑) ∘ b : _ → EuclideanSpace ℝ ι) = b.ofZLatticeBasis ℝ L :=
    funext fun i ↦ (b.ofZLatticeBasis_apply ℝ L i).symm
  have hgb :
      ((↑) ∘ b.map g : _ → EuclideanSpace ℝ ι) = ψ.toLinearMap ∘ b.ofZLatticeBasis ℝ L := by
    rw [← hb]
    rfl
  rw [covolume_eq_det_mul_measureReal M volume (b.map g) (b.ofZLatticeBasis ℝ L),
    covolume_eq_det_mul_measureReal L volume b (b.ofZLatticeBasis ℝ L), hgb, hb, Basis.det_comp,
    Basis.det_self, mul_one, abs_one, one_mul]

lemma abs_det_eq_sqrt_pow (hk : 0 < k) (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ) :
    |LinearMap.det ψ.toLinearMap| = √k ^ Fintype.card ι := by
  classical
  let P : Matrix ι ι ℝ := (toLpLin 2 2).symm ψ.toLinearMap
  have hP : toLpLin 2 2 P = ψ.toLinearMap := LinearEquiv.apply_symm_apply _ _
  have hdet : LinearMap.det ψ.toLinearMap = P.det := by
    rw [← hP, LinearMap.det_toLpLin]
  have hPP : Pᵀ * P = k • 1 := by
    ext i j
    have h : ⟪ψ (EuclideanSpace.single j 1), ψ (EuclideanSpace.single i 1)⟫_ℝ =
        k * ⟪EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single i (1 : ℝ)⟫_ℝ :=
      hψ _ _
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      ← LinearEquiv.coe_coe ψ, ← hP, toLpLin_apply, toLpLin_apply, WithLp.ofLp_toLp,
      WithLp.ofLp_toLp, PiLp.ofLp_single, PiLp.ofLp_single, star_trivial, star_trivial,
      mulVec_single_one, mulVec_single_one] at h
    simpa [mul_apply, dotProduct, one_apply, Pi.single_apply, eq_comm] using h
  have hdet2 : (Pᵀ * P).det = P.det ^ 2 := by
    rw [det_mul, det_transpose, sq]
  have hsq : P.det ^ 2 = (√k ^ Fintype.card ι) ^ 2 := by
    rw [pow_right_comm, Real.sq_sqrt hk.le, ← hdet2, hPP, det_smul, det_one, mul_one]
  rw [hdet, ← abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg k) (Fintype.card ι))]
  exact (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq

lemma packingDensity_eq_of_map_eq [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology M]
    [IsZLattice ℝ M] (hk : 0 < k) (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ)
    (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M) : packingDensity M = packingDensity L := by
  rw [packingDensity, packingDensity, minimum_eq_sqrt_mul_minimum hψ hLM,
    covolume_eq_abs_det_mul hLM, abs_det_eq_sqrt_pow hk hψ, mul_div_assoc, measureReal_def,
    measureReal_def, Measure.addHaar_ball_mul_of_pos _ _ (Real.sqrt_pos.mpr hk), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (Real.sqrt_nonneg k) _), finrank_euclideanSpace,
    mul_div_mul_left _ _ (pow_ne_zero _ (Real.sqrt_ne_zero'.mpr hk))]

end ZLattice

namespace LinearMap.BilinForm

variable {ι : Type*} [Fintype ι] {L M : Submodule ℤ (EuclideanSpace ℝ ι)} [DiscreteTopology L]
  [IsZLattice ℝ L] [DiscreteTopology M] [IsZLattice ℝ M]

/-- **Perfection is a similarity invariant** (LMFDB `lattice.similarity`, `lattice.perfect`): of
two similar lattices of full rank in `ℝⁿ`, one is perfect exactly when the other is. -/
lemma IsSimilarLattice.isPerfect_iff
    (h : IsSimilarLattice (innerₗ (EuclideanSpace ℝ ι)) L (innerₗ (EuclideanSpace ℝ ι)) M) :
    ZLattice.IsPerfect L ↔ ZLattice.IsPerfect M := by
  rcases h.exists_linearEquiv with ⟨ψ, k, hk, hψ, hLM⟩
  rcases h.symm.exists_linearEquiv with ⟨ψ', k', hk', hψ', hML⟩
  exact ⟨fun hL ↦ hL.of_map_eq hk hψ hLM, fun hM ↦ hM.of_map_eq hk' hψ' hML⟩

/-- **The packing density is a similarity invariant** (LMFDB `lattice.similarity`,
`lattice.density`): similar lattices of full rank in `ℝⁿ` have the same packing density. -/
lemma IsSimilarLattice.packingDensity_eq
    (h : IsSimilarLattice (innerₗ (EuclideanSpace ℝ ι)) L (innerₗ (EuclideanSpace ℝ ι)) M) :
    ZLattice.packingDensity L = ZLattice.packingDensity M := by
  rcases h.exists_linearEquiv with ⟨ψ, k, hk, hψ, hLM⟩
  exact (ZLattice.packingDensity_eq_of_map_eq hk hψ hLM).symm

end LinearMap.BilinForm

namespace LinearMap.BilinForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {B : BilinForm ℝ V} {B' : BilinForm ℝ W} {L : Submodule ℤ V} {M : Submodule ℤ W}

lemma isIntegralLattice_inv_sqrt_smul (hL : B.IsIntegralLattice L) {d : ℕ} (hd0 : d ≠ 0)
    (hd : (B.integralForm L hL).scaleIdeal = Ideal.span {(d : ℤ)}) :
    B.IsIntegralLattice ((√d)⁻¹ • L) := by
  rw [← Real.sqrt_inv]
  refine isIntegralLattice_sqrt_smul (inv_nonneg.mpr d.cast_nonneg) fun x hx y hy ↦ ?_
  have hxy : B.integralForm L hL ⟨x, hx⟩ ⟨y, hy⟩ ∈ Ideal.span {(d : ℤ)} :=
    hd ▸ apply_mem_scaleIdeal _ _ _
  rcases Ideal.mem_span_singleton.mp hxy with ⟨q, hq⟩
  have hB : (B.integralForm L hL ⟨x, hx⟩ ⟨y, hy⟩ : ℝ) = B x y :=
    intCast_integralForm hL _ _
  refine ⟨q, ?_⟩
  rw [← hB, hq, Int.cast_mul, Int.cast_natCast, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hd0)]

/-- **An integral lattice is similar to a primitive integral lattice**, if its form is not zero
(LMFDB `lattice.similarity`, `lattice.primitive`): if the scale ideal of `L` (generated by the
entries of a Gram matrix) is `dℤ`, `d ≠ 0`, the gcd of those entries, then the integral lattice
`d^(-1/2) L`, similar to `L`, has scale ideal `ℤ`: it is primitive. -/
lemma scaleIdeal_integralForm_inv_sqrt_smul (hL : B.IsIntegralLattice L) {d : ℕ} (hd0 : d ≠ 0)
    (hd : (B.integralForm L hL).scaleIdeal = Ideal.span {(d : ℤ)}) :
    (B.integralForm ((√d)⁻¹ • L) (isIntegralLattice_inv_sqrt_smul hL hd0 hd)).scaleIdeal = ⊤ := by
  have hle : (B.integralForm L hL).scaleIdeal ≤ Ideal.span {(d : ℤ)} *
      (B.integralForm ((√d)⁻¹ • L) (isIntegralLattice_inv_sqrt_smul hL hd0 hd)).scaleIdeal := by
    refine (scaleIdeal_le_iff _ _).mpr fun x y ↦ ?_
    have hx : (√d)⁻¹ • (x : V) ∈ (√d)⁻¹ • L :=
      smul_mem_pointwise_smul _ _ _ x.2
    have hy : (√d)⁻¹ • (y : V) ∈ (√d)⁻¹ • L :=
      smul_mem_pointwise_smul _ _ _ y.2
    have hxy : B.integralForm L hL x y = d * B.integralForm _
        (isIntegralLattice_inv_sqrt_smul hL hd0 hd) ⟨_, hx⟩ ⟨_, hy⟩ := by
      refine Int.cast_injective (α := ℝ) ?_
      simp only [Int.cast_mul, Int.cast_natCast, intCast_integralForm, smul_left, smul_right]
      rw [← mul_assoc (√(d : ℝ))⁻¹, ← mul_inv, Real.mul_self_sqrt d.cast_nonneg,
        mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr hd0)]
    rw [hxy]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (apply_mem_scaleIdeal _ _ _)
  rw [hd] at hle
  rcases Ideal.mem_span_singleton_mul.mp (hle (Ideal.mem_span_singleton_self _)) with ⟨z, hz, hdz⟩
  have hz1 : z = 1 :=
    mul_left_cancel₀ (Int.natCast_ne_zero.mpr hd0) (hdz.trans (mul_one _).symm)
  exact Ideal.eq_top_of_isUnit_mem _ hz (hz1 ▸ isUnit_one)

/-- **A similarity class containing an integral lattice with a nonzero form contains a primitive
integral lattice** (LMFDB `lattice.similarity`, `lattice.primitive`): if `B(L, L) ⊆ ℤ` and
`B(x, y) ≠ 0` for some `x, y ∈ L`, then `L` is similar to an integral lattice `K` of the same space
whose scale ideal is `ℤ`, namely `d^(-1/2) L` for `dℤ` the scale ideal of `L`
(`LinearMap.BilinForm.scaleIdeal_integralForm_inv_sqrt_smul`); `K` is finitely generated and
discrete when `L` is (`Submodule.FG.pointwise_smul`, `Submodule.discreteTopology_pointwise_smul`).
-/
lemma exists_isSimilarLattice_scaleIdeal_eq_top (hL : B.IsIntegralLattice L)
    (h0 : ∃ x ∈ L, ∃ y ∈ L, B x y ≠ 0) : ∃ K : Submodule ℤ V, ∃ hK : B.IsIntegralLattice K,
      (B.integralForm K hK).scaleIdeal = ⊤ ∧ B.IsSimilarLattice L B K := by
  let d : ℕ := (IsPrincipal.generator (B.integralForm L hL).scaleIdeal).natAbs
  have hd : (B.integralForm L hL).scaleIdeal = Ideal.span {(d : ℤ)} := by
    rw [Int.span_natAbs, Ideal.span_singleton_generator]
  have hd0 : d ≠ 0 := by
    rcases h0 with ⟨x, hx, y, hy, hxy⟩
    intro hd0
    have hmem : B.integralForm L hL ⟨x, hx⟩ ⟨y, hy⟩ ∈ Ideal.span {(d : ℤ)} :=
      hd ▸ apply_mem_scaleIdeal _ _ _
    rw [hd0, Nat.cast_zero, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hmem
    have hB : (B.integralForm L hL ⟨x, hx⟩ ⟨y, hy⟩ : ℝ) = B x y :=
      intCast_integralForm hL _ _
    rw [hmem, Int.cast_zero] at hB
    exact hxy hB.symm
  exact ⟨_, isIntegralLattice_inv_sqrt_smul hL hd0 hd,
    scaleIdeal_integralForm_inv_sqrt_smul hL hd0 hd,
    isSimilarLattice_smul B L (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)))⟩

lemma exists_intCast_eq (hL : B.IsIntegralLattice L) (hM : B'.IsIntegralLattice M)
    (hMp : (B'.integralForm M hM).scaleIdeal = ⊤) {a : ℝ} (g : L ≃ₗ[ℤ] M)
    (hg : ∀ x y : L, B x y = a * B' (g x) (g y)) : ∃ n : ℤ, (n : ℝ) = a := by
  have hle : (B'.integralForm M hM).scaleIdeal ≤
      (LinearMap.range (Algebra.linearMap ℤ ℝ)).comap (LinearMap.toSpanSingleton ℤ ℝ a) := by
    refine (scaleIdeal_le_iff _ _).mpr fun u v ↦ mem_comap.mpr (LinearMap.mem_range.mpr
      ⟨B.integralForm L hL (g.symm u) (g.symm v), ?_⟩)
    rw [Algebra.linearMap_apply, eq_intCast, intCast_integralForm, hg,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearMap.toSpanSingleton_apply,
      zsmul_eq_mul, intCast_integralForm, mul_comm]
  rcases LinearMap.mem_range.mp (mem_comap.mp (hle (hMp ▸ Submodule.mem_top))) with ⟨n, hn⟩
  rw [Algebra.linearMap_apply, eq_intCast, LinearMap.toSpanSingleton_apply, one_zsmul] at hn
  exact ⟨n, hn⟩

/-- **A similarity class contains at most one primitive integral lattice, up to isometry** (LMFDB
`lattice.similarity`, `lattice.primitive`): similar integral lattices whose scale ideals are `ℤ`
are isometric. If `L ≅ αM`, then `B(L, L) = α² B'(M, M)`, so `α²` and `α⁻²` are integers, hence
`α² = 1`. -/
lemma IsSimilarLattice.exists_isometry (h : B.IsSimilarLattice L B' M) (hL : B.IsIntegralLattice L)
    (hM : B'.IsIntegralLattice M) (hLp : (B.integralForm L hL).scaleIdeal = ⊤)
    (hMp : (B'.integralForm M hM).scaleIdeal = ⊤) :
    ∃ e : L ≃ₗ[ℤ] M, ∀ x y, B' (e x) (e y) = B x y := by
  rcases h with ⟨α, hα, e, he⟩
  let g : L ≃ₗ[ℤ] M := e.trans
    (equivMapOfInjective (DistribSMul.toLinearMap ℤ W α) (smul_right_injective W hα) M).symm
  have hg (x : L) : α • (g x : W) = e x :=
    map_equivMapOfInjective_symm_apply _ (smul_right_injective W hα) M (e x)
  have hform (x y : L) : B x y = α ^ 2 * B' (g x) (g y) := by
    rw [← he, ← hg, ← hg, smul_left, smul_right, sq, mul_assoc]
  have hform' (u v : M) : B' u v = (α ^ 2)⁻¹ * B (g.symm u) (g.symm v) := by
    rw [hform, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      inv_mul_cancel_left₀ (pow_ne_zero 2 hα)]
  rcases exists_intCast_eq hL hM hMp g hform with ⟨n, hn⟩
  rcases exists_intCast_eq hM hL hLp g.symm hform' with ⟨m, hm⟩
  have hnm : n * m = 1 := Int.cast_injective (α := ℝ) <| by
    rw [Int.cast_mul, hn, hm, Int.cast_one, mul_inv_cancel₀ (pow_ne_zero 2 hα)]
  have hn0 : (0 : ℝ) ≤ n := by
    rw [hn]
    exact sq_nonneg α
  have hn1 : n = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h1 | h1
    · exact h1
    · rw [h1] at hn0
      norm_num at hn0
  refine ⟨g, fun x y ↦ ?_⟩
  rw [hform, ← hn, hn1, Int.cast_one, one_mul]

end LinearMap.BilinForm
