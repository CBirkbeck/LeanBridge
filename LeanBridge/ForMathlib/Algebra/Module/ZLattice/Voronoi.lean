import LeanBridge.ForMathlib.Algebra.Module.ZLattice.PerfectArithmetic
import LeanBridge.ForMathlib.Analysis.CStarAlgebra.Matrix
import LeanBridge.ForMathlib.Analysis.InnerProductSpace.SelfAdjointDetBounds
import Mathlib.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Convex.Cone.Alternative

/-!
# Voronoi's theorem: extreme lattices are the perfect eutactic lattices

A lattice `L` of `ℝⁿ` is extreme (LMFDB `lattice.extreme`, `ZLattice.IsExtreme`) if its packing
density is a local maximum among the lattices `g L`, `g ∈ GL_n(ℝ)` near the identity. Voronoi's
theorem: `L` is extreme if and only if it is perfect (`ZLattice.IsPerfect`) and eutactic
(`ZLattice.IsEutactic`).

The packing density of `g L` is a fixed multiple of `min(g L)ⁿ / |det g|`, with `min(g L)` the
length of a shortest nonzero vector of `g L` (`ZLattice.minimum`), and `‖g x‖² = ⟪P x, x⟫` for
`P = gᵀ g`. Near the identity, only the minimal vectors `S` of `L` can be the shortest vectors of
`g L`. Write `H[x] = ⟪H x, x⟫` for a self-adjoint map `H`. The analysis is done in a
finite-dimensional real inner product space `E`.

* **Extreme lattices.** If `H ≠ 0` is self-adjoint with `H[x] ≥ 0` on `S` and `tr H ≤ 0`, then
  `g = 1 + t H`, `t > 0` small, does not shorten the minimal vectors, so `min(g L) ≥ min L`, while
  `det (1 + t H) < exp (t tr H) ≤ 1`: `g L` is denser than `L`. So an extreme lattice has no such
  `H`. If `L` is not perfect, some `H ≠ 0` has `H[x] = 0` on `S` (the matrices `x xᵀ` do not span
  the symmetric matrices), and `H` or `-H` is such a direction. If `L` is not eutactic, Tucker's
  theorem of the alternative, applied to the matrices `x xᵀ`, `x ∈ S`, and `-1`, gives a nonzero
  linear form on the matrices, nonnegative at the `x xᵀ` and nonpositive at `1`, whose symmetric
  part is such a direction.
* **Perfect eutactic lattices.** Eutaxy, `⟪v, v⟫ = ∑ₓ cₓ ⟪v, x⟫²` with `cₓ > 0`, gives
  `tr H = ∑ₓ cₓ H[x]`. With perfection and the compactness of the unit sphere, `tr H ≥ κ ‖H‖` for
  some `κ > 0` and every self-adjoint `H` with `H[x] ≥ 0` on `S`. For `g` near the identity,
  normalise `P = gᵀ g` by the least value `q` of `P[x] / ‖x‖²` on the minimal vectors:
  `H = P / q - 1` satisfies `H[x] ≥ 0` on `S` and is small, and
  `det (1 + H) ≥ 1 + tr H - 2 n ‖H‖² ≥ 1`. So `det(g)² = det P ≥ qⁿ`, while
  `min(g L)² ≤ q min(L)²`: the density of `g L` is at most that of `L`.

Extremality is the local maximality of the packing density, not a strict one, and both directions
hold in that sense: a lattice that is not perfect or not eutactic has strictly denser lattices
`g L` arbitrarily close to it. The eutaxy of `ZLattice.IsEutactic`, a positive combination of the
`x xᵀ` over all the minimal vectors, is Voronoi's eutaxy, which sums over the minimal vectors up
to sign: the coefficients of `x` and `-x` can be merged or split.

## Main results

* `ZLattice.exists_abs_det_mul_minimum_pow_lt`: a nonzero self-adjoint `H` with `H[x] ≥ 0` at the
  minimal vectors and `tr H ≤ 0` gives lattices `g L`, `g` arbitrarily near the identity, with
  `|det g| min(L)ⁿ < min(g L)ⁿ`.
* `ZLattice.exists_forall_minimum_map_pow_le`: for a eutactic lattice whose minimal vectors detect
  self-adjoint maps, `min(g L)ⁿ ≤ |det g| min(L)ⁿ` for `g` near the identity.
* `ZLattice.IsExtreme.trace_pos`: a nonzero self-adjoint `H` with `H[x] ≥ 0` at the minimal
  vectors of an extreme lattice has positive trace.
* `ZLattice.IsExtreme.isPerfect` (LMFDB `lattice.extreme`): an extreme lattice is perfect.
* `ZLattice.IsExtreme.isEutactic` (LMFDB `lattice.extreme`): an extreme lattice is eutactic.
* `ZLattice.IsPerfect.isExtreme` (LMFDB `lattice.extreme`): a perfect eutactic lattice is extreme.
* `ZLattice.isExtreme_iff_isPerfect_and_isEutactic` (LMFDB `lattice.extreme`): Voronoi's theorem.
* `LinearMap.BilinForm.IsSimilarLattice.isExtreme_iff` (LMFDB `lattice.extreme`): extremality is a
  similarity invariant.

## References

* G. Voronoi, *Nouvelles applications des paramètres continus à la théorie des formes
  quadratiques. Premier mémoire*, J. Reine Angew. Math. 133 (1908), 97–178.
* J. Martinet, *Perfect Lattices in Euclidean Spaces*, Springer, 2003, Theorem 3.4.6.
* A. Schürmann, *Computational Geometry of Positive Definite Quadratic Forms*, University Lecture
  Series 48, AMS, 2009.
-/

open Module MeasureTheory Set

open scoped InnerProductSpace

namespace ZLattice

section General

variable {E : Type*} [NormedAddCommGroup E] {L : Submodule ℤ E} [InnerProductSpace ℝ E]
  {H : E →L[ℝ] E} [DiscreteTopology L]

variable [Nontrivial E] [IsZLattice ℝ L] in
lemma ne_bot_of_isZLattice : L ≠ ⊥ := by
  intro hL
  have h : Submodule.span ℝ (L : Set E) = ⊤ := IsZLattice.span_top
  rw [hL, Submodule.bot_coe, Submodule.span_zero_singleton] at h
  exact bot_ne_top h

variable [FiniteDimensional ℝ E]

/-- **A direction that does not shrink the minimal vectors and does not increase the trace gives
denser lattices** (LMFDB `lattice.extreme`): if `H ≠ 0` is a self-adjoint map with
`⟪H x, x⟫ ≥ 0` at the minimal vectors `x` of `L` and `tr H ≤ 0`, then for every `ε > 0` some
`g = 1 + t H`, `t > 0`, with `‖g - 1‖ < ε` has `|det g| min(L)ⁿ < min(g L)ⁿ`: the minimal vectors
do not shrink, the other vectors of `L` stay longer than them, and `det g < exp (t tr H) ≤ 1`. -/
lemma exists_abs_det_mul_minimum_pow_lt (hL : L ≠ ⊥) (hH : IsSelfAdjoint H) (hH0 : H ≠ 0)
    (hS : ∀ x ∈ minimalVectors L, 0 ≤ ⟪H x, x⟫_ℝ) (htr : LinearMap.trace ℝ E H ≤ 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ g : E ≃L[ℝ] E, ‖(g : E →L[ℝ] E) - .id ℝ E‖ < ε ∧
      |(g : E →L[ℝ] E).det| * minimum L ^ finrank ℝ E <
        minimum (L.map (g.toLinearMap.restrictScalars ℤ)) ^ finrank ℝ E := by
  have hSne : (minimalVectors L).Nonempty := nonempty_minimalVectors hL
  have hm : 0 < minimum L := minimum_pos hL
  rcases exists_lt_forall_le_norm hSne with ⟨m₂, hm₂, hgap⟩
  set η : ℝ := min (min ε (1 - minimum L / m₂)) 1
  have hη : 0 < η :=
    lt_min (lt_min hε (sub_pos.mpr ((div_lt_one (hm.trans hm₂)).mpr hm₂))) one_pos
  have hηε : η ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηm : minimum L ≤ (1 - η) * m₂ := by
    have h1 : η ≤ 1 - minimum L / m₂ := (min_le_left _ _).trans (min_le_right _ _)
    exact (div_le_iff₀ (hm.trans hm₂)).mp (by linarith)
  have hHn : 0 < ‖H‖ := norm_pos_iff.mpr hH0
  have ht : 0 < η / (2 * ‖H‖) := by
    positivity
  generalize hT_def : (η / (2 * ‖H‖)) • H = T
  have hTn : ‖T‖ = η / 2 := by
    rw [← hT_def, norm_smul, Real.norm_of_nonneg ht.le, div_mul_eq_mul_div,
      mul_div_mul_right _ _ hHn.ne']
  have hT : IsSelfAdjoint T := hT_def ▸ (IsSelfAdjoint.all _).smul hH
  have hT1 : ‖T‖ < 1 := by
    rw [hTn]
    linarith
  have hTS (x : E) (hx : x ∈ minimalVectors L) : 0 ≤ ⟪T x, x⟫_ℝ := by
    rw [← hT_def, smul_apply, real_inner_smul_left]
    exact mul_nonneg ht.le (hS x hx)
  have hdet0 : 0 < (1 + T).det := ContinuousLinearMap.det_one_add_pos hT hT1
  have hdet1 : (1 + T).det < 1 := by
    refine (ContinuousLinearMap.det_one_add_lt_exp_trace hT hT1
      (hT_def ▸ smul_ne_zero ht.ne' hH0)).trans_le (Real.exp_le_one_iff.mpr ?_)
    rw [← hT_def, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ht.le htr
  let g : E ≃L[ℝ] E := (LinearMap.equivOfDetNeZero _ hdet0.ne').toContinuousLinearEquiv
  have hg (x : E) : g x = x + T x :=
    rfl
  have hgT : (g : E →L[ℝ] E) = 1 + T :=
    ContinuousLinearMap.ext hg
  have hmin : minimum L ≤ minimum (L.map (g.toLinearMap.restrictScalars ℤ)) := by
    refine le_minimum_map g hL fun x hx hx0 ↦ ?_
    by_cases hxS : x ∈ minimalVectors L
    · rw [← hxS.2.2]
      refine (sq_le_sq₀ (norm_nonneg x) (norm_nonneg (g x))).mp ?_
      rw [hg, norm_add_sq_real, real_inner_comm]
      linarith [hTS x hxS, sq_nonneg ‖T x‖]
    · have h1 : ‖T x‖ ≤ η / 2 * ‖x‖ := hTn ▸ T.le_opNorm x
      have h2 : ‖x‖ ≤ ‖g x‖ + ‖T x‖ := by
        have h3 : ‖g x - T x‖ ≤ ‖g x‖ + ‖T x‖ := norm_sub_le (g x) (T x)
        rwa [hg, add_sub_cancel_right] at h3
      linarith [mul_nonneg hη.le (norm_nonneg x),
        mul_nonneg (sub_nonneg.mpr hη1) (sub_nonneg.mpr (hgap x hx hx0 hxS))]
  refine ⟨g, ?_, ?_⟩
  · rw [hgT, ← ContinuousLinearMap.one_def, add_sub_cancel_left, hTn]
    linarith
  · rw [hgT, abs_of_pos hdet0]
    exact (mul_lt_of_lt_one_left (pow_pos hm _) hdet1).trans_le (pow_le_pow_left₀ hm.le hmin _)

/-- **The minimum of a eutactic lattice whose minimal vectors detect self-adjoint maps is locally
maximal against the determinant** (LMFDB `lattice.extreme`): if `L` is eutactic and the only
self-adjoint map `H` with `⟪H x, x⟫ = 0` at the minimal vectors `x` of `L` is `0` (perfection),
then `min(g L)ⁿ ≤ |det g| min(L)ⁿ` for every invertible `g` near the identity. -/
lemma exists_forall_minimum_map_pow_le (hL : L ≠ ⊥) (hE : IsEutactic L)
    (hperf : ∀ H : E →L[ℝ] E, IsSelfAdjoint H → (∀ x ∈ minimalVectors L, ⟪H x, x⟫_ℝ = 0) → H = 0) :
    ∃ ε > 0, ∀ g : E ≃L[ℝ] E, ‖(g : E →L[ℝ] E) - .id ℝ E‖ < ε →
      minimum (L.map (g.toLinearMap.restrictScalars ℤ)) ^ finrank ℝ E ≤
        |(g : E →L[ℝ] E).det| * minimum L ^ finrank ℝ E := by
  rcases hE with ⟨c, hc, hcE⟩
  have hfin : (minimalVectors L).Finite := finite_minimalVectors
  have hSne : (minimalVectors L).Nonempty := nonempty_minimalVectors hL
  have hm : 0 < minimum L := minimum_pos hL
  have hE' (v : E) : ⟪v, v⟫_ℝ = ∑ x ∈ hfin.toFinset, c x * ⟪v, x⟫_ℝ ^ 2 :=
    (hcE v).trans (finsum_mem_eq_finite_toFinset_sum _ hfin)
  rcases ContinuousLinearMap.exists_pos_forall_mul_norm_le
    (fun x hx ↦ hc x (hfin.mem_toFinset.mp hx))
    fun H hH h0 ↦ hperf H hH fun x hx ↦ h0 x (hfin.mem_toFinset.mpr hx) with ⟨κ, hκ, hκH⟩
  have hnt : Nontrivial E := hSne.elim fun x hx ↦ nontrivial_of_ne x 0 hx.2.1
  have hn : 0 < (finrank ℝ E : ℝ) := Nat.cast_pos.mpr finrank_pos
  set δ : ℝ := min (1 / 2) (κ / (2 * finrank ℝ E))
  have hδ : 0 < δ := lt_min one_half_pos (by positivity)
  refine ⟨min (1 / 6) (δ / 12), lt_min (by norm_num) (by positivity), fun g hg ↦ ?_⟩
  generalize hD_def : (g : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E = D at hg
  have hD1 : ‖D‖ < 1 / 6 := hg.trans_le (min_le_left _ _)
  have hDδ : 12 * ‖D‖ < δ := by
    linarith [hg.trans_le (min_le_right _ _)]
  have hgD : (g : E →L[ℝ] E) = 1 + D := by
    rw [← hD_def, ← ContinuousLinearMap.one_def, add_sub_cancel]
  have hDs : ‖star D‖ = ‖D‖ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint.norm_map D
  generalize hP_def : star (g : E →L[ℝ] E) * (g : E →L[ℝ] E) = P
  have hPv (v : E) : ⟪P v, v⟫_ℝ = ‖g v‖ ^ 2 := by
    rw [← hP_def, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
      ContinuousLinearEquiv.coe_coe]
  have hP1 : ‖P - 1‖ ≤ 3 * ‖D‖ := by
    have hPD : P - 1 = D + star D + star D * D := by
      rw [← hP_def, hgD, star_add, star_one]
      simp only [add_mul, mul_add, one_mul, mul_one]
      abel
    have h1 : ‖star D * D‖ ≤ ‖D‖ := (norm_mul_le _ _).trans (by
      rw [hDs]
      nlinarith [norm_nonneg D])
    rw [hPD]
    linarith [norm_add_le (D + star D) (star D * D), norm_add_le D (star D)]
  rcases hfin.toFinset.exists_min_image (fun x ↦ ‖g x‖) (hfin.toFinset_nonempty.mpr hSne) with
    ⟨x₀, hx₀, hmin⟩
  have hx₀S : x₀ ∈ minimalVectors L := hfin.mem_toFinset.mp hx₀
  have hgx₀ : 0 < ‖g x₀‖ := norm_pos_iff.mpr (g.toLinearEquiv.map_ne_zero_iff.mpr hx₀S.2.1)
  have hx₀2 : 0 < ‖x₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx₀S.2.1) 2
  set q : ℝ := ‖g x₀‖ ^ 2 / minimum L ^ 2 with hq_def
  have hq1 : |q - 1| ≤ ‖P - 1‖ := by
    have h1 : q - 1 = ⟪(P - 1) x₀, x₀⟫_ℝ / ‖x₀‖ ^ 2 := by
      rw [hq_def, sub_apply, inner_sub_left, hPv, one_apply_eq_self, real_inner_self_eq_norm_sq,
        hx₀S.2.2, div_sub_one (pow_pos hm 2).ne']
    have h2 : |⟪(P - 1) x₀, x₀⟫_ℝ| ≤ ‖P - 1‖ * ‖x₀‖ ^ 2 := by
      rw [sq, ← mul_assoc]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right ((P - 1).le_opNorm x₀) (norm_nonneg _))
    rwa [h1, abs_div, abs_of_pos hx₀2, div_le_iff₀ hx₀2]
  have hq : 1 / 2 ≤ q := by
    linarith [neg_abs_le (q - 1)]
  have hq0 : 0 < q := by
    linarith
  have hH : IsSelfAdjoint (q⁻¹ • P - 1) :=
    ((IsSelfAdjoint.all _).smul (hP_def ▸ IsSelfAdjoint.star_mul_self _)).sub (IsSelfAdjoint.one _)
  generalize hH_def : q⁻¹ • P - 1 = H at hH
  have hHS (x : E) (hx : x ∈ hfin.toFinset) : 0 ≤ ⟪H x, x⟫_ℝ := by
    have hxS : x ∈ minimalVectors L := hfin.mem_toFinset.mp hx
    rw [← hH_def, sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, real_inner_smul_left,
      hPv, real_inner_self_eq_norm_sq, hxS.2.2]
    have h1 : q⁻¹ * ‖g x₀‖ ^ 2 = minimum L ^ 2 := by
      rw [hq_def, inv_div, div_mul_cancel₀ _ (pow_pos hgx₀ 2).ne']
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (hmin x hx) 2, inv_pos.mpr hq0]
  have hHn : ‖H‖ ≤ δ := by
    have hH' : H = q⁻¹ • (P - 1) + (q⁻¹ - 1) • (1 : E →L[ℝ] E) := by
      rw [← hH_def, smul_sub, sub_smul, one_smul]
      abel
    have h1 : q⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hq0 two_pos]
      linarith
    have h2 : |q⁻¹ - 1| ≤ 2 * ‖P - 1‖ := by
      have h3 : q⁻¹ - 1 = q⁻¹ * (1 - q) := by
        rw [mul_sub, mul_one, inv_mul_cancel₀ hq0.ne']
      rw [h3, abs_mul, abs_of_pos (inv_pos.mpr hq0), abs_sub_comm]
      exact mul_le_mul h1 hq1 (abs_nonneg _) two_pos.le
    have h4 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    rw [hH']
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hq0.le), Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg (P - 1)),
      mul_le_mul_of_nonneg_left h4 (abs_nonneg (q⁻¹ - 1))]
  have hdet : 1 ≤ (1 + H).det := by
    have h1 : 1 + LinearMap.trace ℝ E H - 2 * finrank ℝ E * ‖H‖ ^ 2 ≤ (1 + H).det :=
      ContinuousLinearMap.one_add_trace_sub_le_det_one_add hH (hHn.trans (min_le_left _ _))
    have h2 : κ * ‖H‖ ≤ LinearMap.trace ℝ E H :=
      (hκH H hH hHS).trans_eq (ContinuousLinearMap.trace_eq_sum_of_forall_inner_self_eq hE' hH).symm
    have h3 : ‖H‖ * (2 * finrank ℝ E) ≤ κ :=
      (le_div_iff₀ (by positivity)).mp (hHn.trans (min_le_right _ _))
    nlinarith [mul_le_mul_of_nonneg_right h3 (norm_nonneg H)]
  have hdetP : (1 + H).det = q⁻¹ ^ finrank ℝ E * |(g : E →L[ℝ] E).det| ^ 2 := by
    have h1 : LinearMap.det (P : E →ₗ[ℝ] E) = |(g : E →L[ℝ] E).det| ^ 2 := by
      rw [← hP_def, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
        ← LinearMap.normDet_eq_abs_det]
      exact (ContinuousLinearMap.normDet_sq (g : E →L[ℝ] E)).symm
    rw [← hH_def, add_sub_cancel, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.det_smul, h1]
  have hqn : q ^ finrank ℝ E ≤ |(g : E →L[ℝ] E).det| ^ 2 := by
    rwa [hdetP, inv_pow, le_inv_mul_iff₀ (pow_pos hq0 _), mul_one] at hdet
  have hming : minimum (L.map (g.toLinearMap.restrictScalars ℤ)) ^ 2 ≤ q * minimum L ^ 2 := by
    rw [hq_def, div_mul_cancel₀ _ (pow_pos hm 2).ne']
    exact pow_le_pow_left₀ minimum_nonneg (minimum_map_le_norm g hx₀S.1 hx₀S.2.1) 2
  refine (pow_le_pow_iff_left₀ (pow_nonneg minimum_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [pow_right_comm, mul_pow, pow_right_comm (minimum L)]
  refine (pow_le_pow_left₀ (sq_nonneg _) hming _).trans ?_
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hqn (pow_nonneg (sq_nonneg _) _)

end General

open Matrix

section Euclidean

variable {ι : Type*} [Fintype ι] {L : Submodule ℤ (EuclideanSpace ℝ ι)}
  {H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι} [DiscreteTopology L] [IsZLattice ℝ L]

variable [Nonempty ι] in
/-- **A nonzero self-adjoint map that does not shrink the minimal vectors of an extreme lattice to
first order has positive trace**: if `L` is extreme and `H ≠ 0` is a self-adjoint map of `ℝⁿ` with
`⟪H x, x⟫ ≥ 0` for every minimal vector `x` of `L`, then `tr H > 0`
(`ZLattice.exists_abs_det_mul_minimum_pow_lt`). -/
lemma IsExtreme.trace_pos (h : IsExtreme L) (hH : IsSelfAdjoint H) (hH0 : H ≠ 0)
    (hS : ∀ x ∈ minimalVectors L, 0 ≤ ⟪H x, x⟫_ℝ) :
    0 < LinearMap.trace ℝ (EuclideanSpace ℝ ι) H := by
  by_contra! htr
  rcases h with ⟨ε, hε, h⟩
  rcases exists_abs_det_mul_minimum_pow_lt ne_bot_of_isZLattice hH hH0 hS htr hε with
    ⟨g, hg, hlt⟩
  rw [finrank_euclideanSpace] at hlt
  exact hlt.not_ge ((packingDensity_map_le_packingDensity_iff g).mp (h g hg))

/-- **An extreme lattice is perfect** (LMFDB `lattice.extreme`, Voronoi): otherwise a nonzero
linear form `f` on the matrices vanishes at the matrices `x xᵀ` of the minimal vectors `x` but not
at some symmetric matrix, and the symmetric matrices of `f` and `-f` are nonzero self-adjoint maps
`H` with `⟪H x, x⟫ = 0` at the minimal vectors, of traces `f 1` and `-f 1`, one of which is not
positive, against `ZLattice.IsExtreme.trace_pos`. -/
lemma IsExtreme.isPerfect (h : IsExtreme L) : IsPerfect L := by
  classical
  rcases isEmpty_or_nonempty ι with _ | _
  · rintro A -
    have hA0 : A = 0 := Matrix.ext fun i ↦ isEmptyElim i
    rw [hA0]
    exact zero_mem _
  intro A hA
  by_contra hAS
  rcases Submodule.exists_le_ker_of_notMem hAS with ⟨f, hfA, hf⟩
  have hfS (x : EuclideanSpace ℝ ι) (hx : x ∈ minimalVectors L) : f (vecMulVec x.ofLp x.ofLp) = 0 :=
    LinearMap.mem_ker.mp (hf (Submodule.subset_span ⟨x, hx, rfl⟩))
  have hfA' : (-f) A ≠ 0 := by
    rw [LinearMap.neg_apply]
    exact neg_ne_zero.mpr hfA
  have h1 : 0 < f 1 := trace_toEuclideanCLM_dualSymmMatrix f ▸ h.trace_pos
    (isSelfAdjoint_toEuclideanCLM_dualSymmMatrix f) (toEuclideanCLM_dualSymmMatrix_ne_zero hA hfA)
    fun x hx ↦ by rw [inner_toEuclideanCLM_dualSymmMatrix, hfS x hx]
  have h2 : 0 < (-f) 1 := trace_toEuclideanCLM_dualSymmMatrix (-f) ▸ h.trace_pos
    (isSelfAdjoint_toEuclideanCLM_dualSymmMatrix (-f))
    (toEuclideanCLM_dualSymmMatrix_ne_zero hA hfA') fun x hx ↦ by
      rw [inner_toEuclideanCLM_dualSymmMatrix, LinearMap.neg_apply, hfS x hx, neg_zero]
  rw [LinearMap.neg_apply] at h2
  linarith

/-- **An extreme lattice is eutactic** (LMFDB `lattice.extreme`, Voronoi). Tucker's theorem of the
alternative (`TauCeti.exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos`), for the
matrices `x xᵀ` of the minimal vectors `x` and the matrix `-1`, gives `μ ≥ 0` with
`μ₀ 1 = ∑ₓ μₓ x xᵀ` and a linear form `y` with `y(x xᵀ) ≥ 0`, `y(1) ≤ 0`, and `μ + y > 0` at each of
them. The symmetric matrix of `y` is a self-adjoint `H` with `⟪H x, x⟫ ≥ 0` and `tr H ≤ 0`, so
`H = 0` (`ZLattice.IsExtreme.trace_pos`), `y` vanishes there and all the `μ` are positive:
`⟪v, v⟫ = ∑ₓ (μₓ / μ₀) ⟪v, x⟫²`. -/
lemma IsExtreme.isEutactic (h : IsExtreme L) : IsEutactic L := by
  classical
  rcases isEmpty_or_nonempty ι with _ | _
  · have h0 (v : EuclideanSpace ℝ ι) : v = 0 := by
      ext i
      exact isEmptyElim i
    refine ⟨0, fun x hx ↦ (hx.2.1 (h0 x)).elim, fun v ↦ ?_⟩
    simp [h0 v]
  have hfin : (minimalVectors L).Finite := finite_minimalVectors
  rcases TauCeti.exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos (K := ℝ)
    fun j : Option hfin.toFinset ↦ j.elim (-1) fun x ↦
      vecMulVec (x : EuclideanSpace ℝ ι).ofLp (x : EuclideanSpace ℝ ι).ofLp with
    ⟨μ, y, -, hsum, hy, hpos⟩
  have hyS (x : EuclideanSpace ℝ ι) (hx : x ∈ hfin.toFinset) : 0 ≤ y (vecMulVec x.ofLp x.ofLp) :=
    hy (some ⟨x, hx⟩)
  have hy1 : y 1 ≤ 0 := by
    have h1 : 0 ≤ y (-1) := hy none
    rw [map_neg] at h1
    linarith
  have hK0 : toEuclideanCLM (𝕜 := ℝ) (dualSymmMatrix y) = 0 := by
    by_contra hK0
    refine (h.trace_pos (isSelfAdjoint_toEuclideanCLM_dualSymmMatrix y) hK0 fun x hx ↦ ?_).not_ge ?_
    · rw [inner_toEuclideanCLM_dualSymmMatrix]
      exact hyS x (hfin.mem_toFinset.mpr hx)
    · rwa [trace_toEuclideanCLM_dualSymmMatrix]
  have hY : dualSymmMatrix y = 0 := EmbeddingLike.map_eq_zero_iff.mp hK0
  have hy0 (x : EuclideanSpace ℝ ι) : y (vecMulVec x.ofLp x.ofLp) = 0 := by
    rw [← inner_toEuclideanCLM_dualSymmMatrix y, hY, map_zero]
    exact inner_zero_left _
  have hy10 : y 1 = 0 := by
    rw [← trace_toEuclideanCLM_dualSymmMatrix y, hY, map_zero,
      ContinuousLinearMap.toLinearMap_zero, map_zero]
  have hμ (j : Option hfin.toFinset) : 0 < μ j := by
    rcases j with _ | x
    · have h1 : 0 < μ none + y (-1) := hpos none
      rwa [map_neg, hy10, neg_zero, add_zero] at h1
    · have h1 : 0 < μ (some x) +
          y (vecMulVec (x : EuclideanSpace ℝ ι).ofLp (x : EuclideanSpace ℝ ι).ofLp) :=
        hpos (some x)
      rwa [hy0, add_zero] at h1
  let c : EuclideanSpace ℝ ι → ℝ :=
    fun x ↦ if hx : x ∈ hfin.toFinset then μ (some ⟨x, hx⟩) / μ none else 0
  have hc (x : hfin.toFinset) : c x = μ (some x) / μ none := dite_eq_left x.2
  refine ⟨c, fun x hx ↦ ?_, fun v ↦ ?_⟩
  · exact (div_pos (hμ _) (hμ none)).trans_eq (hc ⟨x, hfin.mem_toFinset.mpr hx⟩).symm
  have hv : μ none * -(v.ofLp ⬝ᵥ v.ofLp) + ∑ x : hfin.toFinset, μ (some x) *
      ((x : EuclideanSpace ℝ ι).ofLp ⬝ᵥ v.ofLp * v.ofLp ⬝ᵥ (x : EuclideanSpace ℝ ι).ofLp) = 0 := by
    simpa only [Fintype.sum_option, Option.elim, add_mulVec, sum_mulVec, smul_mulVec, neg_mulVec,
      one_mulVec, vecMulVec_mulVec, dotProduct_add, dotProduct_sum, dotProduct_smul,
      dotProduct_neg, op_smul_eq_smul, smul_eq_mul, zero_mulVec, dotProduct_zero] using
      congrArg (fun A : Matrix ι ι ℝ ↦ v.ofLp ⬝ᵥ A *ᵥ v.ofLp) hsum
  have hsum' : ∑ᶠ x ∈ minimalVectors L, c x * ⟪v, x⟫_ℝ ^ 2 = (μ none)⁻¹ *
      ∑ x : hfin.toFinset, μ (some x) *
        ((x : EuclideanSpace ℝ ι).ofLp ⬝ᵥ v.ofLp * v.ofLp ⬝ᵥ (x : EuclideanSpace ℝ ι).ofLp) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_coe_sort, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [hc x, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm v.ofLp]
    ring1
  have hvv : ⟪v, v⟫_ℝ = v.ofLp ⬝ᵥ v.ofLp := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [hvv, hsum', eq_inv_mul_iff_mul_eq₀ (hμ none).ne']
  linear_combination -hv

/-- **A perfect eutactic lattice is extreme** (LMFDB `lattice.extreme`, Voronoi): by
`ZLattice.exists_forall_minimum_map_pow_le`, whose hypothesis on self-adjoint maps is perfection
(`ZLattice.IsPerfect.eq_zero_of_isSelfAdjoint`), `min(g L)ⁿ ≤ |det g| min(L)ⁿ` for `g` near the
identity, and the packing density of `g L` is a fixed multiple of `min(g L)ⁿ / |det g|`. -/
lemma IsPerfect.isExtreme (hP : IsPerfect L) (hE : IsEutactic L) : IsExtreme L := by
  rcases isEmpty_or_nonempty ι with _ | _
  · refine ⟨1, one_pos, fun g _ ↦ (congrArg packingDensity (Submodule.ext fun x ↦ ?_)).le⟩
    have hx : x = 0 := by
      ext i
      exact isEmptyElim i
    simp [hx]
  rcases exists_forall_minimum_map_pow_le ne_bot_of_isZLattice hE
    fun H hH h0 ↦ hP.eq_zero_of_isSelfAdjoint hH h0 with ⟨ε, hε, h⟩
  refine ⟨ε, hε, fun g hg ↦ (packingDensity_map_le_packingDensity_iff g).mpr ?_⟩
  simpa only [finrank_euclideanSpace] using h g hg

/-- **Voronoi's theorem** (LMFDB `lattice.extreme`): a lattice of `ℝⁿ` is extreme, a local
maximum of the packing density, if and only if it is perfect and eutactic. -/
lemma isExtreme_iff_isPerfect_and_isEutactic : IsExtreme L ↔ IsPerfect L ∧ IsEutactic L :=
  ⟨fun h ↦ ⟨h.isPerfect, h.isEutactic⟩, fun h ↦ h.1.isExtreme h.2⟩

end Euclidean

end ZLattice

namespace LinearMap.BilinForm

/-- **Extremality is a similarity invariant** (LMFDB `lattice.extreme`, `lattice.similarity`): of
two similar lattices of full rank in `ℝⁿ`, one is extreme exactly when the other is, since
perfection and eutaxy are similarity invariants. So extremality is a property of a lattice up to
similarity, such as a lattice given by a Gram matrix. -/
lemma IsSimilarLattice.isExtreme_iff {ι : Type*} [Fintype ι]
    {L M : Submodule ℤ (EuclideanSpace ℝ ι)} [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology M] [IsZLattice ℝ M]
    (h : IsSimilarLattice (innerₗ (EuclideanSpace ℝ ι)) L (innerₗ (EuclideanSpace ℝ ι)) M) :
    ZLattice.IsExtreme L ↔ ZLattice.IsExtreme M := by
  rw [ZLattice.isExtreme_iff_isPerfect_and_isEutactic,
    ZLattice.isExtreme_iff_isPerfect_and_isEutactic, h.isPerfect_iff, h.isEutactic_iff]

end LinearMap.BilinForm
