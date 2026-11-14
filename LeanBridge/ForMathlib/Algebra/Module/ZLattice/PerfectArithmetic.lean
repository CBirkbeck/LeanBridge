import LeanBridge.ForMathlib.Algebra.Module.ZLattice.ArithmeticBilinear
import LeanBridge.ForMathlib.Algebra.Module.ZLattice.Perfect
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Perfect lattices are arithmetic and determined by their minimal vectors

A lattice `L` in `ℝⁿ` is perfect (LMFDB `lattice.perfect`) if the matrices `x xᵀ`, for the minimal
vectors `x` of `L`, span the symmetric `n × n` real matrices. Pairing a symmetric matrix `A` with
`x xᵀ` by the trace form gives `xᵀ A x`, and the trace form is nondegenerate on symmetric
matrices, so perfection says exactly that a symmetric bilinear form `B` on `ℝⁿ` with `B(x, x) = 0`
for every minimal vector `x` is zero. Hence the Gram matrix of a perfect lattice in a basis is the
unique solution of the linear equations `aᵀ A a = m`, where `a` runs over the coordinate vectors of
the minimal vectors and `m` is the minimal norm. This has three consequences, proved here.

* A perfect `ℤ`-submodule of `ℝⁿ` is a lattice: discrete and of full rank.
* A perfect lattice is determined by its minimal vectors (Voronoi): a symmetric bilinear form is
  determined by its values `B(x, x)` on them, so a linear map scaling the norms of the minimal
  vectors by `c` is a similitude of ratio `c`, and a lattice `M` whose minimal vectors contain the
  image of those of `L` under a linear bijection `L → M` is similar to `L`, isometric if the
  minima agree. The knowl's "uniquely determined by its minimal vectors" has to be read in this
  way: as subsets of `ℝⁿ`, the lattices `D₁₂` and `D₁₂⁺` are distinct perfect lattices with the
  same minimal vectors.
* A perfect lattice is arithmetic (LMFDB `lattice.arithmetic`). The linear equations have integer
  coefficients, so for every `ℚ`-linear `f : ℝ → ℚ` with `f(m) = 0` the form with Gram matrix
  `f(⟪bᵢ, bⱼ⟫)` vanishes at the minimal vectors, hence is zero; so the inner products of `L` are
  rational multiples of `m`, with bounded denominators since `L` is finitely generated.

## Main results

* `ZLattice.IsPerfect.eq_of_apply_self_eq` (LMFDB `lattice.perfect`): a symmetric bilinear form on
  `ℝⁿ` is determined by its values `B(x, x)` at the minimal vectors `x` of a perfect lattice.
* `ZLattice.IsPerfect.discreteTopology` and `ZLattice.IsPerfect.isZLattice`: a perfect
  `ℤ`-submodule of `ℝⁿ` is discrete and spans `ℝⁿ`.
* `ZLattice.relIndex_span_minimalVectors_ne_zero`: a lattice whose minimal vectors span the space
  is well-rounded (LMFDB `lattice.well_rounded`): they span a sublattice of finite index.
* `ZLattice.IsPerfect.relIndex_span_minimalVectors_ne_zero` (LMFDB `lattice.perfect`): a perfect
  lattice is well-rounded.
* `ZLattice.IsPerfect.inner_map_eq`: a linear map that multiplies the norms of the minimal vectors
  of a perfect lattice by `c` multiplies all inner products by `c²`.
* `ZLattice.IsPerfect.inner_map_eq_of_mapsTo`: a linear map carrying the minimal vectors of a
  perfect lattice to minimal vectors of a lattice with the same minimum is an isometry.
* `ZLattice.IsPerfect.isSimilarLattice_of_mapsTo` (LMFDB `lattice.perfect`): a perfect lattice is
  determined up to similarity by its minimal vectors.
* `ZLattice.IsPerfect.inner_mem_span_minimum_sq`: the inner products of the vectors of a perfect
  lattice are rational multiples of its minimal norm.
* `ZLattice.IsPerfect.isArithmetic` (LMFDB `lattice.perfect`): a perfect lattice is arithmetic.
* `ZLattice.IsPerfect.exists_isIntegralLattice_isSimilarLattice` (LMFDB `lattice.perfect`): a
  perfect lattice is similar to an integral lattice.

## References

* G. Voronoi, *Nouvelles applications des paramètres continus à la théorie des formes
  quadratiques. Premier mémoire*, J. Reine Angew. Math. 133 (1908), 97–178.
* J. Martinet, *Perfect Lattices in Euclidean Spaces*, Springer, 2003, Chapter 3.
-/

open Matrix Module

open scoped InnerProductSpace Pointwise

open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {L : Submodule ℤ E} {M : Submodule ℤ F}

lemma isSimilarLattice_of_map_eq (ψ : E ≃ₗ[ℝ] F) {k : ℝ} (hk : 0 < k)
    (hψ : ∀ v w, ⟪ψ v, ψ w⟫_ℝ = k * ⟪v, w⟫_ℝ) (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M) :
    IsSimilarLattice (innerₗ E) L (innerₗ F) M := by
  have hα : (√k)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.mpr hk)
  let s : M ≃ₗ[ℤ] ↥((√k)⁻¹ • M) := Submodule.equivMapOfInjective
    (DistribSMul.toLinearMap ℤ F (√k)⁻¹) (smul_right_injective F hα) M
  let e : L ≃ₗ[ℤ] ↥((√k)⁻¹ • M) :=
    (((ψ.restrictScalars ℤ).submoduleMap L).trans (.ofEq _ _ hLM)).trans s
  refine ⟨(√k)⁻¹, hα, e, fun x y ↦ ?_⟩
  have hs (z : L) : (e z : F) = (√k)⁻¹ • ψ z :=
    rfl
  rw [hs, hs, smul_left, smul_right, innerₗ_apply_apply, hψ, innerₗ_apply_apply, ← mul_assoc,
    ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hk.le, inv_mul_cancel₀ hk.ne', one_mul]

end LinearMap.BilinForm

namespace ZLattice

section Minimum

variable {E : Type*} [NormedAddCommGroup E] {L : Submodule ℤ E} {x : E}

lemma minimum_le_norm (hx : x ∈ L) (hx₀ : x ≠ 0) : minimum L ≤ ‖x‖ :=
  csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg y⟩ ⟨x, ⟨hx, hx₀⟩, rfl⟩

lemma minimum_pos_of_mem_minimalVectors (hx : x ∈ minimalVectors L) : 0 < minimum L :=
  hx.2.2 ▸ norm_pos_iff.mpr hx.2.1

lemma discreteTopology_of_minimum_pos (h : 0 < minimum L) : DiscreteTopology L :=
  .of_forall_le_norm h fun x hx ↦ minimum_le_norm x.2 fun h0 ↦ hx (Subtype.ext h0)

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- **A lattice whose minimal vectors span the space is well-rounded** (LMFDB
`lattice.well_rounded`): if the minimal vectors of a lattice `L` of full rank span the ambient
real space, the sublattice they span has finite index in `L`, both having the rank of the space. -/
lemma relIndex_span_minimalVectors_ne_zero (h : Submodule.span ℝ (minimalVectors L) = ⊤) :
    (Submodule.span ℤ (minimalVectors L)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  have hle : Submodule.span ℤ (minimalVectors L) ≤ L := Submodule.span_le.mpr fun x hx ↦ hx.1
  have hd : DiscreteTopology (Submodule.span ℤ (minimalVectors L)) :=
    .of_continuous_injective (continuous_inclusion hle) (Set.inclusion_injective hle)
  have hrank : finrank ℤ (Submodule.span ℤ (minimalVectors L)) = finrank ℤ L := by
    rw [ZLattice.rank ℝ L, ← Set.finrank, ← Real.finrank_eq_int_finrank_of_discrete hd,
      Set.finrank, h, finrank_top]
  have hfin : Finite (L ⧸ (Submodule.span ℤ (minimalVectors L)).comap L.subtype) :=
    (Submodule.finiteQuotient_iff _).mpr
      ((Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans hrank)
  exact AddSubgroup.index_ne_zero_of_finite (hH := hfin)

end Minimum

variable {ι : Type*} [Fintype ι] {L : Submodule ℤ (EuclideanSpace ℝ ι)} {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {M : Submodule ℤ F} {x y : EuclideanSpace ℝ ι}

lemma IsPerfect.eq_zero_of_apply_self_eq_zero (h : IsPerfect L)
    {B : BilinForm ℝ (EuclideanSpace ℝ ι)} (hB : B.IsSymm)
    (hS : ∀ x ∈ minimalVectors L, B x x = 0) : B = 0 := by
  classical
  let b : Basis ι ℝ (EuclideanSpace ℝ ι) := PiLp.basisFun 2 ℝ ι
  have hA : (BilinForm.toMatrix b B).IsSymm := (BilinForm.isSymm_toMatrix_iff_isSymm b).mpr hB
  have htr : (BilinForm.toMatrix b B * BilinForm.toMatrix b B).trace = 0 := by
    refine Submodule.span_induction (p := fun Y _ ↦ (BilinForm.toMatrix b B * Y).trace = 0) ?_
      (by simp) (fun X Y _ _ hX hY ↦ ?_) (fun c X _ hX ↦ ?_) (h _ hA)
    · rintro _ ⟨x, hx, rfl⟩
      rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
      exact (B.apply_eq_dotProduct_toMatrix_mulVec b x x).symm.trans (hS x hx)
    · rw [mul_add, trace_add, hX, hY, add_zero]
    · rw [mul_smul_comm, trace_smul, hX, smul_zero]
  refine (BilinForm.toMatrix b).injective (.trans ?_ (map_zero _).symm)
  rwa [← trace_conjTranspose_mul_self_eq_zero_iff, conjTranspose_eq_transpose_of_trivial, hA.eq]

/-- **A symmetric bilinear form is determined by its values at the minimal vectors of a perfect
lattice** (LMFDB `lattice.perfect`): if `L` is a perfect lattice of `ℝⁿ` and the symmetric bilinear
forms `B` and `B'` on `ℝⁿ` satisfy `B(x, x) = B'(x, x)` for every minimal vector `x` of `L`, then
`B = B'`. In a basis of `L`, the Gram matrix of `L` is the only symmetric matrix `A` with
`aᵀ A a = m` for the coordinate vectors `a` of the minimal vectors, `m` being the minimal norm. -/
lemma IsPerfect.eq_of_apply_self_eq (h : IsPerfect L) {B B' : BilinForm ℝ (EuclideanSpace ℝ ι)}
    (hB : B.IsSymm) (hB' : B'.IsSymm) (hS : ∀ x ∈ minimalVectors L, B x x = B' x x) : B = B' :=
  sub_eq_zero.mp <| h.eq_zero_of_apply_self_eq_zero (hB.sub hB') fun x hx ↦
    sub_eq_zero.mpr (hS x hx)

lemma IsPerfect.nonempty_minimalVectors [Nonempty ι] (h : IsPerfect L) :
    (minimalVectors L).Nonempty := by
  classical
  by_contra hS
  have h1 : (1 : Matrix ι ι ℝ) ∈ Submodule.span ℝ
      ((fun x : EuclideanSpace ℝ ι ↦ vecMulVec x.ofLp x.ofLp) '' minimalVectors L) :=
    h 1 isSymm_one
  rw [Set.not_nonempty_iff_eq_empty.mp hS, Set.image_empty, Submodule.span_empty,
    Submodule.mem_bot] at h1
  exact one_ne_zero h1

lemma IsPerfect.minimum_pos [Nonempty ι] (h : IsPerfect L) : 0 < minimum L :=
  h.nonempty_minimalVectors.elim fun _ hx ↦ minimum_pos_of_mem_minimalVectors hx

/-- **A perfect `ℤ`-submodule of `ℝⁿ` is discrete**: its nonzero vectors have norm at least that
of a minimal vector, which exists because the matrices `x xᵀ` span. -/
lemma IsPerfect.discreteTopology (h : IsPerfect L) : DiscreteTopology L := by
  rcases isEmpty_or_nonempty ι with _ | _
  · infer_instance
  · exact discreteTopology_of_minimum_pos h.minimum_pos

/-- **A perfect `ℤ`-submodule of `ℝⁿ` has full rank**: its minimal vectors span `ℝⁿ`. -/
lemma IsPerfect.isZLattice [DiscreteTopology L] (h : IsPerfect L) : IsZLattice ℝ L := by
  classical
  exact ⟨eq_top_iff.mpr <| h.span_minimalVectors ▸ Submodule.span_mono fun x hx ↦ hx.1⟩

/-- **A perfect lattice is well-rounded** (LMFDB `lattice.perfect`, `lattice.well_rounded`): the
sublattice spanned by the minimal vectors of a perfect lattice `L` has finite index in `L`. -/
lemma IsPerfect.relIndex_span_minimalVectors_ne_zero (h : IsPerfect L) :
    (Submodule.span ℤ (minimalVectors L)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  classical
  have hd : DiscreteTopology L := h.discreteTopology
  have hz : IsZLattice ℝ L := h.isZLattice
  exact ZLattice.relIndex_span_minimalVectors_ne_zero h.span_minimalVectors

/-- **A linear map that multiplies the norms of the minimal vectors of a perfect lattice by `c`
multiplies all inner products by `c²`**: it is a similitude of ratio `c`. -/
lemma IsPerfect.inner_map_eq (h : IsPerfect L) (ψ : EuclideanSpace ℝ ι →ₗ[ℝ] F) {c : ℝ}
    (hψ : ∀ x ∈ minimalVectors L, ‖ψ x‖ = c * ‖x‖) (v w : EuclideanSpace ℝ ι) :
    ⟪ψ v, ψ w⟫_ℝ = c ^ 2 * ⟪v, w⟫_ℝ := by
  have hi : BilinForm.IsSymm (innerₗ (EuclideanSpace ℝ ι)) := ⟨fun x y ↦ real_inner_comm y x⟩
  have hB : (innerₗ F).compl₁₂ ψ ψ = c ^ 2 • innerₗ (EuclideanSpace ℝ ι) :=
    h.eq_of_apply_self_eq ⟨fun x y ↦ real_inner_comm (ψ y) (ψ x)⟩ (hi.smul (c ^ 2)) fun x hx ↦ by
      rw [LinearMap.compl₁₂_apply, innerₗ_apply_apply, real_inner_self_eq_norm_sq, hψ x hx,
        LinearMap.smul_apply, LinearMap.smul_apply, innerₗ_apply_apply,
        real_inner_self_eq_norm_sq, smul_eq_mul, mul_pow]
  exact LinearMap.congr_fun₂ hB v w

/-- **A linear map carrying the minimal vectors of a perfect lattice `L` to minimal vectors of a
lattice `M` with the same minimum is an isometry.** -/
lemma IsPerfect.inner_map_eq_of_mapsTo (h : IsPerfect L) (ψ : EuclideanSpace ℝ ι →ₗ[ℝ] F)
    (hS : Set.MapsTo ψ (minimalVectors L) (minimalVectors M)) (hLM : minimum M = minimum L)
    (v w : EuclideanSpace ℝ ι) : ⟪ψ v, ψ w⟫_ℝ = ⟪v, w⟫_ℝ := by
  rw [h.inner_map_eq ψ (c := 1) fun x hx ↦ by rw [(hS hx).2.2, hLM, hx.2.2, one_mul], one_pow,
    one_mul]

/-- **A perfect lattice is determined up to similarity by its minimal vectors** (LMFDB
`lattice.perfect`): if `L` is a perfect lattice of `ℝⁿ`, and a linear bijection `ψ` carries `L`
onto a lattice `M` and the minimal vectors of `L` to minimal vectors of `M`, then `M` is similar to
`L`; `ψ` is a similitude of ratio `m(M) / m(L)`, an isometry if the minima agree
(`ZLattice.IsPerfect.inner_map_eq_of_mapsTo`). So the Gram matrix of `M` in the basis `ψ(bᵢ)` is
the multiple by `(m(M) / m(L))²` of that of `L` in a basis `bᵢ`: the quadratic form of a perfect
lattice is determined, up to scaling, by the coordinates of its minimal vectors. -/
lemma IsPerfect.isSimilarLattice_of_mapsTo (h : IsPerfect L) (ψ : EuclideanSpace ℝ ι ≃ₗ[ℝ] F)
    (hLM : L.map (ψ.restrictScalars ℤ).toLinearMap = M)
    (hS : Set.MapsTo ψ (minimalVectors L) (minimalVectors M)) :
    BilinForm.IsSimilarLattice (innerₗ (EuclideanSpace ℝ ι)) L (innerₗ F) M := by
  rcases isEmpty_or_nonempty ι with _ | _
  · refine BilinForm.isSimilarLattice_of_map_eq ψ one_pos (fun v w ↦ ?_) hLM
    rw [Subsingleton.elim v 0, map_zero, inner_zero_left, inner_zero_left, mul_zero]
  · rcases h.nonempty_minimalVectors with ⟨x, hx⟩
    refine BilinForm.isSimilarLattice_of_map_eq ψ
      (pow_pos (div_pos (minimum_pos_of_mem_minimalVectors (hS hx)) h.minimum_pos) 2)
      (h.inner_map_eq ψ.toLinearMap fun y hy ↦ ?_) hLM
    rw [LinearEquiv.coe_coe, (hS hy).2.2, hy.2.2, div_mul_cancel₀ _ h.minimum_pos.ne']

variable [DiscreteTopology L] [IsZLattice ℝ L] {κ : Type*} [Fintype κ] (b : Basis κ ℤ L) in
lemma inner_eq_sum_repr_mul (hx : x ∈ L) (hy : y ∈ L) : ⟪x, y⟫_ℝ =
    ∑ i, ∑ j, (b.repr ⟨x, hx⟩ i : ℝ) * ⟪(b i : EuclideanSpace ℝ ι), b j⟫_ℝ * b.repr ⟨y, hy⟩ j := by
  classical
  have h : ⟪x, y⟫_ℝ = Matrix.toBilin (b.ofZLatticeBasis ℝ L)
      (BilinForm.toMatrix (b.ofZLatticeBasis ℝ L) (innerₗ _)) x y := by
    rw [Matrix.toBilin_toMatrix]
    rfl
  rw [h, Matrix.toBilin_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [BilinForm.toMatrix_apply, b.ofZLatticeBasis_apply ℝ L i, b.ofZLatticeBasis_apply ℝ L j,
    ← b.ofZLatticeBasis_repr_apply ℝ L ⟨x, hx⟩ i, ← b.ofZLatticeBasis_repr_apply ℝ L ⟨y, hy⟩ j]
  rfl

/-- **The inner products of the vectors of a perfect lattice are rational multiples of its minimal
norm** `m(L)`, the square of `ZLattice.minimum L`. -/
lemma IsPerfect.inner_mem_span_minimum_sq (h : IsPerfect L) (hx : x ∈ L) (hy : y ∈ L) :
    ⟪x, y⟫_ℝ ∈ Submodule.span ℚ {minimum L ^ 2} := by
  classical
  have hd : DiscreteTopology L := h.discreteTopology
  have hz : IsZLattice ℝ L := h.isZLattice
  by_contra hxy
  rcases Submodule.exists_le_ker_of_notMem hxy with ⟨f, hf, hker⟩
  have hm : f (minimum L ^ 2) = 0 := hker (Submodule.mem_span_singleton_self _)
  let b : Basis (Free.ChooseBasisIndex ℤ L) ℤ L := Free.chooseBasis ℤ L
  let B : BilinForm ℝ (EuclideanSpace ℝ ι) := Matrix.toBilin (b.ofZLatticeBasis ℝ L)
    (.of fun i j ↦ (f ⟪(b i : EuclideanSpace ℝ ι), b j⟫_ℝ : ℝ))
  have key {u v : EuclideanSpace ℝ ι} (hu : u ∈ L) (hv : v ∈ L) : B u v = f ⟪u, v⟫_ℝ := by
    rw [Matrix.toBilin_apply, inner_eq_sum_repr_mul b hu hv, map_sum, Rat.cast_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_sum, Rat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [b.ofZLatticeBasis_repr_apply ℝ L ⟨u, hu⟩ i, b.ofZLatticeBasis_repr_apply ℝ L ⟨v, hv⟩ j,
      of_apply]
    have h1 : (b.repr ⟨u, hu⟩ i : ℝ) * ⟪(b i : EuclideanSpace ℝ ι), b j⟫_ℝ * b.repr ⟨v, hv⟩ j =
        ((b.repr ⟨u, hu⟩ i * b.repr ⟨v, hv⟩ j : ℤ) : ℚ) • ⟪(b i : EuclideanSpace ℝ ι), b j⟫_ℝ := by
      rw [Rat.smul_def]
      push_cast
      ring1
    rw [h1, map_smul, smul_eq_mul]
    push_cast
    ring1
  have hB : B = 0 := by
    refine h.eq_zero_of_apply_self_eq_zero ((isSymm_toBilin_iff_isSymm _).mpr <| .ext fun i j ↦ ?_)
      fun z hz ↦ ?_
    · rw [of_apply, of_apply, real_inner_comm]
    · rw [key hz.1 hz.1, real_inner_self_eq_norm_sq, hz.2.2, hm, Rat.cast_zero]
  refine hf (Rat.cast_injective (α := ℝ) ?_)
  rw [← key hx hy, hB, Rat.cast_zero]
  rfl

/-- **A perfect lattice is arithmetic** (LMFDB `lattice.perfect`, `lattice.arithmetic`): for some
real `c > 0`, the inner products of the vectors of `L`, multiplied by `c`, are integers. Indeed
they are rational multiples of the minimal norm `m(L)`
(`ZLattice.IsPerfect.inner_mem_span_minimum_sq`), and `L` is finitely generated. -/
lemma IsPerfect.isArithmetic (h : IsPerfect L) : IsArithmetic L := by
  classical
  have hd : DiscreteTopology L := h.discreteTopology
  have hz : IsZLattice ℝ L := h.isZLattice
  rcases isEmpty_or_nonempty ι with _ | _
  · refine ⟨1, one_pos, fun x _ y _ ↦ ⟨0, ?_⟩⟩
    rw [Subsingleton.elim x 0, inner_zero_left, mul_zero, Int.cast_zero]
  let b : Basis (Free.ChooseBasisIndex ℤ L) ℤ L := Free.chooseBasis ℤ L
  have hq (i j) : ∃ q : ℚ, q • minimum L ^ 2 = ⟪(b i : EuclideanSpace ℝ ι), b j⟫_ℝ :=
    Submodule.mem_span_singleton.mp (h.inner_mem_span_minimum_sq (b i).2 (b j).2)
  choose q hq using hq
  let D : ℕ := ∏ p : Free.ChooseBasisIndex ℤ L × Free.ChooseBasisIndex ℤ L, (q p.1 p.2).den
  have hD : 0 < D := Finset.prod_pos fun p _ ↦ (q p.1 p.2).den_pos
  have hm : minimum L ≠ 0 := h.minimum_pos.ne'
  have hn (i j) : ∃ n : ℤ, D / minimum L ^ 2 * ⟪(b i : EuclideanSpace ℝ ι), b j⟫_ℝ = n := by
    rcases Finset.dvd_prod_of_mem
      (fun p : Free.ChooseBasisIndex ℤ L × Free.ChooseBasisIndex ℤ L ↦ (q p.1 p.2).den)
      (Finset.mem_univ (i, j)) with ⟨k, hk⟩
    have hDk : (D : ℝ) = (q i j).den * k := by
      exact_mod_cast hk
    have hden : ((q i j).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q i j).den_nz
    refine ⟨k * (q i j).num, ?_⟩
    rw [← hq, Rat.smul_def, Rat.cast_def, hDk]
    push_cast
    field_simp
  choose n hn using hn
  refine ⟨D / minimum L ^ 2, div_pos (Nat.cast_pos.mpr hD) (pow_pos h.minimum_pos 2),
    fun x hx y hy ↦ ⟨∑ i, ∑ j, b.repr ⟨x, hx⟩ i * n i j * b.repr ⟨y, hy⟩ j, ?_⟩⟩
  rw [inner_eq_sum_repr_mul b hx hy, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hn i j]
  ring1

/-- **A perfect lattice is similar to an integral lattice** (LMFDB `lattice.perfect`,
`lattice.arithmetic`, `lattice.similarity`): a perfect lattice `L` of `ℝⁿ` is similar to a lattice
`K` of `ℝⁿ`, finitely generated and discrete, whose inner products are integers. -/
lemma IsPerfect.exists_isIntegralLattice_isSimilarLattice (h : IsPerfect L) :
    ∃ K : Submodule ℤ (EuclideanSpace ℝ ι), K.FG ∧ DiscreteTopology K ∧
      BilinForm.IsIntegralLattice (innerₗ (EuclideanSpace ℝ ι)) K ∧ BilinForm.IsSimilarLattice
        (innerₗ (EuclideanSpace ℝ ι)) L (innerₗ (EuclideanSpace ℝ ι)) K := by
  have hd : DiscreteTopology L := h.discreteTopology
  have hz : IsZLattice ℝ L := h.isZLattice
  exact (BilinForm.isArithmeticLattice_iff (ZLattice.FG ℝ L)).mp h.isArithmetic

end ZLattice
