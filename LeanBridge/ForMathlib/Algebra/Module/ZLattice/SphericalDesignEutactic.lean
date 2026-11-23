import LeanBridge.ForMathlib.Algebra.Module.ZLattice.Perfect
import LeanBridge.ForMathlib.Algebra.Module.ZLattice.SphericalDesign
import LeanBridge.ForMathlib.Analysis.CStarAlgebra.Matrix
import LeanBridge.ForMathlib.MeasureTheory.Constructions.HaarToSphereIsometry
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Spherical 2-design lattices are the strongly eutactic ones; strongly perfect lattices are perfect

Let `σ` be the normalised rotation-invariant measure on the unit sphere of `ℝⁿ`. Averaging over `σ`
is invariant under the linear isometries of `ℝⁿ` (`LinearIsometryEquiv.average_toSphere_comp`), so
changing the sign of a coordinate, swapping two coordinates and `x ↦ -x` give the moments of order
at most two: `⨍ xᵢ dσ = 0` and `⨍ xᵢ xⱼ dσ = δᵢⱼ / n`, hence `⨍ ⟪v, x⟫² dσ = ‖v‖² / n`.

A polynomial of degree at most `2` is a combination of the monomials `1`, `xᵢ` and `xᵢ xⱼ`. For the
set `S` of the `m` minimal vectors of a lattice `L` of minimum `r`, symmetric under `x ↦ -x`, this
gives (LMFDB `lattice.spherical_design`): `S` is a spherical `2`-design exactly when
`∑_{s ∈ S} ⟪v, s⟫² = (m r² / n) ‖v‖²` for every `v`, that is when `L` is strongly eutactic
(LMFDB `lattice.eutactic`); the constant is forced by taking traces.

Venkov's theorem: a strongly perfect lattice, one whose minimal vectors form a spherical `4`-design,
is perfect (LMFDB `lattice.perfect`). Otherwise a nonzero linear form on the symmetric matrices
vanishes at the `s sᵀ`, `s ∈ S`, and its symmetric matrix `Y ≠ 0` has `sᵀ Y s = 0` on `S`. The
polynomial `(xᵀ Y x)²` has degree `4`, so its average over the sphere is its average over `S`,
`0`; as it is continuous and nonnegative and `σ` charges every open set, `xᵀ Y x = 0` on the sphere,
hence everywhere, and `Y = 0`.

The lattice `ℤ` of `ℝ¹` is strongly perfect, and even a spherical `t`-design lattice for every `t`:
its minimal vectors `±1` form the whole unit sphere, on which every average is the mean of the
values at `±1`.

Tau Ceti's main branch, past the pin, has the uniform law `TauCeti.Probability.uniformSphereMeasure`
on the unit sphere (the normalised `volume.toSphere`) and its second moments
`TauCeti.Probability.integral_inner_mul_inner_uniformSphereMeasure`: `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫ / n`.
At the bump the moments below follow from them.

## Main definitions

* `EuclideanSpace.coordNegIsometry`: the linear isometry of `ℝⁿ` changing the sign of one
  coordinate.
* `ZLattice.integerLattice`: the lattice `ℤ` of `ℝ¹`.

## Main results

* `EuclideanSpace.average_toSphere_inner_sq`: the second moments of the sphere measure.
* `ZLattice.isSphericalDesign_two_iff_isStronglyEutactic` (LMFDB `lattice.spherical_design`): a
  lattice of `ℝⁿ`, `n ≥ 1`, is a spherical `2`-design lattice exactly when it is strongly eutactic.
* `ZLattice.IsStronglyPerfect.isPerfect` (LMFDB `lattice.spherical_design`, Venkov): a strongly
  perfect lattice is perfect.
* `ZLattice.isSphericalDesign_integerLattice` (LMFDB `lattice.spherical_design`): `ℤ` is a spherical
  `t`-design lattice for every `t`, in particular strongly perfect.

## References

* B. Venkov, *Réseaux et designs sphériques*, Réseaux euclidiens, designs sphériques et formes
  modulaires, Monogr. Enseign. Math. 37 (2001), 10–86.
* J. Martinet, *Perfect Lattices in Euclidean Spaces*, Springer, 2003, §16.
-/

open MeasureTheory Metric Module Matrix MvPolynomial

open scoped InnerProductSpace

namespace Finsupp

variable {ι R : Type*} [CommMonoid R] (y : ι → R) (i j : ι)

lemma eq_zero_or_exists_eq_single_or_exists_eq_add_single {d : ι →₀ ℕ} (hd : d.degree ≤ 2) :
    d = 0 ∨ (∃ i, d = single i 1) ∨ ∃ i j, d = single i 1 + single j 1 := by
  classical
  rcases eq_or_ne d 0 with h0 | h0
  · exact Or.inl h0
  rcases support_nonempty_iff.mpr h0 with ⟨i, hi⟩
  have hd' : d = (d - single i 1) + single i 1 :=
    (tsub_add_cancel_of_le (single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr
      (mem_support_iff.mp hi)))).symm
  have hdeg : (d - single i 1).degree ≤ 1 := by
    have h : degree d = degree (d - single i 1 + single i 1) := congrArg degree hd'
    rw [map_add, degree_single] at h
    omega
  rcases eq_or_ne (d - single i 1) 0 with h1 | h1
  · exact Or.inr (Or.inl ⟨i, by rw [hd', h1, zero_add]⟩)
  rcases support_nonempty_iff.mpr h1 with ⟨j, hj⟩
  have hd'' : d - single i 1 = (d - single i 1 - single j 1) + single j 1 :=
    (tsub_add_cancel_of_le (single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr
      (mem_support_iff.mp hj)))).symm
  have h2 : d - single i 1 - single j 1 = 0 := by
    rw [← degree_eq_zero_iff]
    have h : degree (d - single i 1) = degree (d - single i 1 - single j 1 + single j 1) :=
      congrArg degree hd''
    rw [map_add, degree_single] at h
    omega
  exact Or.inr (Or.inr ⟨j, i, by rw [hd', hd'', h2, zero_add]⟩)

lemma prod_single_one_pow : ((single i 1).prod fun k e ↦ y k ^ e) = y i := by
  rw [prod_single_index (h := fun k e ↦ y k ^ e) (pow_zero (y i)), pow_one]

lemma prod_single_one_add_single_one_pow :
    ((single i 1 + single j 1).prod fun k e ↦ y k ^ e) = y i * y j := by
  rw [prod_add_index' (h := fun k e ↦ y k ^ e) (fun k ↦ pow_zero (y k))
    (fun k _ _ ↦ pow_add (y k) _ _), prod_single_one_pow, prod_single_one_pow]

end Finsupp

namespace MvPolynomial

lemma totalDegree_C_mul_X_mul_X_le {ι : Type*} (a : ℝ) (i j : ι) :
    (C a * X i * X j : MvPolynomial ι ℝ).totalDegree ≤ 2 := by
  have h1 : (C a * X i : MvPolynomial ι ℝ).totalDegree ≤ 1 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X]
  omega

end MvPolynomial

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι] (i j : ι)

variable [DecidableEq ι] in
/-- The linear isometry of `ℝⁿ = EuclideanSpace ℝ ι` changing the sign of the `i`-th coordinate. -/
noncomputable def coordNegIsometry : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j ↦ if j = i then .neg ℝ else .refl ℝ ℝ

variable [DecidableEq ι] in
lemma coordNegIsometry_apply (x : EuclideanSpace ℝ ι) :
    coordNegIsometry i x j = if j = i then -x j else x j := by
  simp only [coordNegIsometry, LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> rfl

lemma integrable_toSphere {f : sphere (0 : EuclideanSpace ℝ ι) 1 → ℝ} (hf : Continuous f) :
    Integrable f (volume : Measure (EuclideanSpace ℝ ι)).toSphere :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma continuous_apply_toSphere :
    Continuous fun x : sphere (0 : EuclideanSpace ℝ ι) 1 ↦ (x : EuclideanSpace ℝ ι) i :=
  (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val

lemma average_toSphere_apply :
    ⨍ x, (x : EuclideanSpace ℝ ι) i ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = 0 := by
  have h : ⨍ x, -(x : EuclideanSpace ℝ ι) i ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere =
      ⨍ x, (x : EuclideanSpace ℝ ι) i ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
    simpa only [LinearIsometryEquiv.coe_sphereHomeomorph_apply, LinearIsometryEquiv.coe_neg,
      PiLp.neg_apply] using
        (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ ι)).average_toSphere_comp
          (LinearIsometryEquiv.measurePreserving _) fun x ↦ (x : EuclideanSpace ℝ ι) i
  rw [average_fun_neg] at h
  linarith

variable {i j} in
lemma average_toSphere_apply_mul_apply (hij : i ≠ j) : ⨍ x, (x : EuclideanSpace ℝ ι) i *
    (x : EuclideanSpace ℝ ι) j ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = 0 := by
  classical
  have h : ⨍ x, -((x : EuclideanSpace ℝ ι) i * (x : EuclideanSpace ℝ ι) j)
      ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere =
        ⨍ x, (x : EuclideanSpace ℝ ι) i * (x : EuclideanSpace ℝ ι) j
          ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
    simpa only [LinearIsometryEquiv.coe_sphereHomeomorph_apply, coordNegIsometry_apply, hij.symm,
      ↓reduceIte, neg_mul] using
        (coordNegIsometry i).average_toSphere_comp (LinearIsometryEquiv.measurePreserving _)
          fun x ↦ (x : EuclideanSpace ℝ ι) i * (x : EuclideanSpace ℝ ι) j
  rw [average_fun_neg] at h
  linarith

lemma average_toSphere_apply_sq_eq : ⨍ x, (x : EuclideanSpace ℝ ι) i ^ 2
    ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = ⨍ x, (x : EuclideanSpace ℝ ι) j ^ 2
    ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
  classical
  simpa only [LinearIsometryEquiv.coe_sphereHomeomorph_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, Equiv.symm_swap,
    Equiv.swap_apply_right] using
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)).average_toSphere_comp
        (LinearIsometryEquiv.measurePreserving _) fun x ↦ (x : EuclideanSpace ℝ ι) j ^ 2

lemma continuous_prod_toSphere (r : ℝ) (d : ι →₀ ℕ) : Continuous fun x : sphere
    (0 : EuclideanSpace ℝ ι) 1 ↦ d.prod fun i e ↦ (r * (x : EuclideanSpace ℝ ι) i) ^ e :=
  continuous_finsetProd _ fun i _ ↦ (continuous_const.mul (continuous_apply_toSphere i)).pow _

variable [Nonempty ι]

lemma average_toSphere_one :
    ⨍ _x, (1 : ℝ) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = 1 := by
  have : NeZero (volume : Measure (EuclideanSpace ℝ ι)).toSphere := ⟨Measure.toSphere_ne_zero _⟩
  exact average_const _ 1

lemma average_toSphere_apply_sq : ⨍ x, (x : EuclideanSpace ℝ ι) i ^ 2
    ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = (Fintype.card ι : ℝ)⁻¹ := by
  have hsum : ∑ j : ι, ⨍ x, (x : EuclideanSpace ℝ ι) j ^ 2
      ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = 1 := by
    rw [← average_fun_finsetSum (f := fun j (x : sphere (0 : EuclideanSpace ℝ ι) 1) ↦
      (x : EuclideanSpace ℝ ι) j ^ 2) fun j _ ↦
        integrable_toSphere ((continuous_apply_toSphere j).pow 2)]
    refine (average_congr (ae_of_all _ fun x ↦ ?_)).trans average_toSphere_one
    have hx : ‖(x : EuclideanSpace ℝ ι)‖ ^ 2 = 1 := by
      rw [mem_sphere_zero_iff_norm.mp x.2, one_pow]
    rw [EuclideanSpace.norm_sq_eq] at hx
    simpa only [Real.norm_eq_abs, sq_abs] using hx
  rw [Finset.sum_congr rfl fun j _ ↦ average_toSphere_apply_sq_eq j i, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  exact eq_inv_of_mul_eq_one_right hsum

variable [DecidableEq ι] in
lemma average_toSphere_apply_mul_apply_eq : ⨍ x, (x : EuclideanSpace ℝ ι) i *
    (x : EuclideanSpace ℝ ι) j ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere =
    if i = j then (Fintype.card ι : ℝ)⁻¹ else 0 := by
  split_ifs with hij
  · rw [← average_toSphere_apply_sq i, hij]
    simp only [sq]
  · exact average_toSphere_apply_mul_apply hij

/-- **The second moments of the sphere measure**: `⨍ ⟪v, x⟫² dσ(x) = ‖v‖² / n` on the unit sphere of
`ℝⁿ`, `n ≥ 1`, for the normalised rotation-invariant measure `σ`. -/
lemma average_toSphere_inner_sq (v : EuclideanSpace ℝ ι) : ⨍ x, ⟪v, (x : EuclideanSpace ℝ ι)⟫_ℝ ^ 2
    ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = ‖v‖ ^ 2 / Fintype.card ι := by
  classical
  have hint (i j : ι) : Integrable (fun x : sphere (0 : EuclideanSpace ℝ ι) 1 ↦
      v i * v j * ((x : EuclideanSpace ℝ ι) i * (x : EuclideanSpace ℝ ι) j))
      (volume : Measure (EuclideanSpace ℝ ι)).toSphere :=
    integrable_toSphere (continuous_const.mul
      ((continuous_apply_toSphere i).mul (continuous_apply_toSphere j)))
  have hexp (x : EuclideanSpace ℝ ι) : ⟪v, x⟫_ℝ ^ 2 = ∑ i, ∑ j, v i * v j * (x i * x j) := by
    rw [PiLp.inner_apply, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring1
  have hfn (i j : ι) : ⨍ x, v i * v j * ((x : EuclideanSpace ℝ ι) i * (x : EuclideanSpace ℝ ι) j)
      ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = v i * v j *
        (if i = j then (Fintype.card ι : ℝ)⁻¹ else 0) := by
    rw [← average_toSphere_apply_mul_apply_eq]
    exact average_const_mul _ (v i * v j) _
  have hrow (i : ι) : ⨍ x, ∑ j, v i * v j * ((x : EuclideanSpace ℝ ι) i *
      (x : EuclideanSpace ℝ ι) j) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere =
        v i * v i * (Fintype.card ι : ℝ)⁻¹ := by
    rw [average_fun_finsetSum fun j _ ↦ hint i j]
    simp only [hfn, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [hexp]
  rw [average_fun_finsetSum fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  simp only [hrow]
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.norm_eq_abs, sq_abs, div_eq_mul_inv, sq]

lemma average_eval_eq_of_totalDegree_le_two {r c : ℝ} {T : Finset (EuclideanSpace ℝ ι)}
    (h0 : c * T.card = 1)
    (h1 : ∀ i, c * ∑ v ∈ T, v i = ⨍ x, r * (x : EuclideanSpace ℝ ι) i
      ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere)
    (h2 : ∀ i j, c * ∑ v ∈ T, v i * v j = ⨍ x, r * (x : EuclideanSpace ℝ ι) i *
      (r * (x : EuclideanSpace ℝ ι) j) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere)
    {f : MvPolynomial ι ℝ} (hf : f.totalDegree ≤ 2) : ⨍ x, f.eval
    (fun i ↦ r * (x : EuclideanSpace ℝ ι) i) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere =
    c * ∑ v ∈ T, f.eval fun i ↦ v i := by
  classical
  have key (d : ι →₀ ℕ) (hd : d ∈ f.support) : ⨍ x, (d.prod fun i e ↦
      (r * (x : EuclideanSpace ℝ ι) i) ^ e) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere =
        c * ∑ v ∈ T, d.prod fun i e ↦ v i ^ e := by
    rcases Finsupp.eq_zero_or_exists_eq_single_or_exists_eq_add_single
      ((le_totalDegree hd).trans hf) with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · simp only [Finsupp.prod_zero_index, Finset.sum_const, nsmul_eq_mul, mul_one, h0]
      exact average_toSphere_one
    · simp only [Finsupp.prod_single_one_pow]
      exact (h1 i).symm
    · simp only [Finsupp.prod_single_one_add_single_one_pow]
      exact (h2 i j).symm
  have hexp (y : ι → ℝ) : f.eval y = ∑ d ∈ f.support, f.coeff d * d.prod fun i e ↦ y i ^ e :=
    eval_eq y f
  have hR : c * ∑ v ∈ T, ∑ d ∈ f.support, f.coeff d * (d.prod fun i e ↦ v i ^ e) =
      ∑ d ∈ f.support, f.coeff d * (c * ∑ v ∈ T, d.prod fun i e ↦ v i ^ e) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← Finset.mul_sum, mul_left_comm]
  simp only [hexp]
  rw [average_fun_finsetSum (f := fun d (x : sphere (0 : EuclideanSpace ℝ ι) 1) ↦
    f.coeff d * d.prod fun i e ↦ (r * (x : EuclideanSpace ℝ ι) i) ^ e) fun d _ ↦
      integrable_toSphere (continuous_const.mul (continuous_prod_toSphere r d)), hR]
  exact Finset.sum_congr rfl fun d hd ↦ by rw [average_const_mul, key d hd]

end EuclideanSpace

namespace ZLattice

variable {ι : Type*} [Fintype ι] {L : Submodule ℤ (EuclideanSpace ℝ ι)} {x : EuclideanSpace ℝ ι}

lemma minimalVectors_finite : (minimalVectors L).Finite := by
  rcases (minimum_nonneg (L := L)).lt_or_eq with h | h
  · have : DiscreteTopology L := discreteTopology_of_minimum_pos h
    exact finite_minimalVectors
  · exact Set.finite_empty.subset fun x hx ↦ hx.2.1 (norm_eq_zero.mp (hx.2.2.trans h.symm))

lemma neg_mem_minimalVectors (hx : x ∈ minimalVectors L) : -x ∈ minimalVectors L :=
  ⟨neg_mem hx.1, neg_ne_zero.mpr hx.2.1, (norm_neg x).trans hx.2.2⟩

lemma sum_toFinset_minimalVectors_apply (hS : (minimalVectors L).Finite) (i : ι) :
    ∑ v ∈ hS.toFinset, v i = 0 := by
  have h : ∑ v ∈ hS.toFinset, v i = ∑ v ∈ hS.toFinset, (-v) i :=
    Finset.sum_nbij' Neg.neg Neg.neg (fun v hv ↦ by
      simpa using neg_mem_minimalVectors (hS.mem_toFinset.mp hv))
      (fun v hv ↦ by simpa using neg_mem_minimalVectors (hS.mem_toFinset.mp hv))
      (fun v _ ↦ neg_neg v) (fun v _ ↦ neg_neg v) fun v _ ↦ by rw [neg_neg]
  simp only [PiLp.neg_apply, Finset.sum_neg_distrib] at h
  linarith

/-- **Spherical `2`-design lattices are the strongly eutactic lattices** (LMFDB
`lattice.spherical_design`): the minimal vectors `S` of a lattice `L` of `ℝⁿ`, `n ≥ 1`, form a
spherical `2`-design if and only if `⟪v, v⟫ = c ∑_{s ∈ S} ⟪v, s⟫²` for some `c > 0` and every `v`;
then `c = n / (|S| min(L)²)`. -/
lemma isSphericalDesign_two_iff_isStronglyEutactic [Nonempty ι] :
    IsSphericalDesign 2 L ↔ IsStronglyEutactic L := by
  classical
  have hS : (minimalVectors L).Finite := minimalVectors_finite
  have hsum (g : EuclideanSpace ℝ ι → ℝ) : ∑ᶠ v ∈ minimalVectors L, g v = ∑ v ∈ hS.toFinset, g v :=
    finsum_mem_eq_finite_toFinset_sum g hS
  have hcard : (Nat.card (minimalVectors L) : ℝ) = hS.toFinset.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hS]
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · rintro ⟨hr, -, hne, -, hpoly⟩
    have hT : (0 : ℝ) < hS.toFinset.card := Nat.cast_pos.mpr (hS.toFinset_nonempty.mpr hne).card_pos
    refine ⟨Fintype.card ι / (hS.toFinset.card * minimum L ^ 2), by positivity, fun v ↦ ?_⟩
    have hdeg1 : (∑ i, C (v i) * X i : MvPolynomial ι ℝ).totalDegree ≤ 1 :=
      (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦
        (totalDegree_mul _ _).trans (by simp))
    have hdeg : ((∑ i, C (v i) * X i) ^ 2 : MvPolynomial ι ℝ).totalDegree ≤ 2 :=
      (totalDegree_pow _ 2).trans (by omega)
    have he (y : ι → ℝ) :
        ((∑ i, C (v i) * X i) ^ 2 : MvPolynomial ι ℝ).eval y = (∑ i, v i * y i) ^ 2 := by
      simp
    have hin (y : EuclideanSpace ℝ ι) : ∑ i, v i * y i = ⟪v, y⟫_ℝ := by
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_comm]
    have hin' (y : EuclideanSpace ℝ ι) : ∑ i, v i * (minimum L * y i) = minimum L * ⟪v, y⟫_ℝ := by
      rw [← hin, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring1
    have hlhs : ⨍ x, (∑ i, v i * (minimum L * (x : EuclideanSpace ℝ ι) i)) ^ 2
        ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = minimum L ^ 2 *
          (‖v‖ ^ 2 / Fintype.card ι) := by
      rw [← EuclideanSpace.average_toSphere_inner_sq, ← average_const_mul]
      exact average_congr (ae_of_all _ fun x ↦ by simp only [hin', mul_pow])
    have h : minimum L ^ 2 * (‖v‖ ^ 2 / Fintype.card ι) =
        (hS.toFinset.card : ℝ)⁻¹ * ∑ s ∈ hS.toFinset, ⟪v, s⟫_ℝ ^ 2 := by
      simpa only [he, hlhs, hcard, hsum, hin] using hpoly _ hdeg
    rw [real_inner_self_eq_norm_sq, hsum]
    field_simp at h ⊢
    linarith
  · rintro ⟨c, hc, h⟩
    simp only [hsum] at h
    have hpol (u w : EuclideanSpace ℝ ι) :
        ⟪u, w⟫_ℝ = c * ∑ s ∈ hS.toFinset, ⟪u, s⟫_ℝ * ⟪w, s⟫_ℝ := by
      have h1 : ⟪u + w, u + w⟫_ℝ = c * ∑ s ∈ hS.toFinset, ⟪u + w, s⟫_ℝ ^ 2 := h (u + w)
      have h2 : ⟪u - w, u - w⟫_ℝ = c * ∑ s ∈ hS.toFinset, ⟪u - w, s⟫_ℝ ^ 2 := h (u - w)
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right] at h1 h2
      have h3 : ∑ s ∈ hS.toFinset, (⟪u, s⟫_ℝ + ⟪w, s⟫_ℝ) ^ 2 -
          ∑ s ∈ hS.toFinset, (⟪u, s⟫_ℝ - ⟪w, s⟫_ℝ) ^ 2 =
            4 * ∑ s ∈ hS.toFinset, ⟪u, s⟫_ℝ * ⟪w, s⟫_ℝ := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ ↦ by ring1
      have h4 : c * ∑ s ∈ hS.toFinset, (⟪u, s⟫_ℝ + ⟪w, s⟫_ℝ) ^ 2 -
          c * ∑ s ∈ hS.toFinset, (⟪u, s⟫_ℝ - ⟪w, s⟫_ℝ) ^ 2 =
            4 * (c * ∑ s ∈ hS.toFinset, ⟪u, s⟫_ℝ * ⟪w, s⟫_ℝ) := by
        rw [← mul_sub, h3]
        ring1
      linarith [real_inner_comm u w]
    have hne : (minimalVectors L).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      simpa [hne] using hpol (EuclideanSpace.single (Classical.arbitrary ι) 1)
        (EuclideanSpace.single (Classical.arbitrary ι) 1)
    have hr : 0 < minimum L := minimum_pos_of_mem_minimalVectors hne.some_mem
    have hT : (0 : ℝ) < hS.toFinset.card :=
      Nat.cast_pos.mpr (hS.toFinset_nonempty.mpr hne).card_pos
    have hij (i j : ι) : ∑ s ∈ hS.toFinset, s i * s j = if i = j then c⁻¹ else 0 := by
      have h' : (if i = j then (1 : ℝ) else 0) = c * ∑ s ∈ hS.toFinset, s i * s j := by
        simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply] using
          hpol (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
      split_ifs at h' ⊢ with hij
      · exact eq_inv_of_mul_eq_one_right h'.symm
      · rcases mul_eq_zero.mp h'.symm with h0 | h0
        · exact absurd h0 hc.ne'
        · exact h0
    have htrace : (hS.toFinset.card : ℝ) * minimum L ^ 2 = Fintype.card ι * c⁻¹ := by
      have h' : ∑ s ∈ hS.toFinset, ‖s‖ ^ 2 = ∑ i, ∑ s ∈ hS.toFinset, s i * s i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [Real.norm_eq_abs, sq_abs, sq]
      rw [Finset.sum_congr rfl fun s hs ↦ by rw [(hS.mem_toFinset.mp hs).2.2], Finset.sum_const,
        nsmul_eq_mul] at h'
      simp only [hij, Finset.sum_const, nsmul_eq_mul] at h'
      exact h'
    refine ⟨hr, hS, hne, fun v hv ↦ hv.2.2, fun f hf ↦ ?_⟩
    rw [hcard, hsum]
    refine EuclideanSpace.average_eval_eq_of_totalDegree_le_two
      (inv_mul_cancel₀ hT.ne') (fun i ↦ ?_) (fun i j ↦ ?_) hf
    · rw [sum_toFinset_minimalVectors_apply hS, mul_zero, average_const_mul,
        EuclideanSpace.average_toSphere_apply, mul_zero]
    · rw [hij, show (fun x : sphere (0 : EuclideanSpace ℝ ι) 1 ↦ minimum L *
          (x : EuclideanSpace ℝ ι) i * (minimum L * (x : EuclideanSpace ℝ ι) j)) =
            fun x : sphere (0 : EuclideanSpace ℝ ι) 1 ↦
              minimum L ^ 2 * ((x : EuclideanSpace ℝ ι) i * (x : EuclideanSpace ℝ ι) j) from
          funext fun x ↦ by ring1, average_const_mul,
        EuclideanSpace.average_toSphere_apply_mul_apply_eq]
      split_ifs
      · have hc' : c⁻¹ = hS.toFinset.card * minimum L ^ 2 / Fintype.card ι := by
          rw [eq_div_iff hn.ne', htrace, mul_comm]
        rw [hc', mul_div_assoc', inv_mul_cancel_left₀ hT.ne', div_eq_mul_inv]
      · rw [mul_zero, mul_zero]

lemma eq_zero_of_forall_sum_mul_eq_zero {Y : Matrix ι ι ℝ} (hY : Y.IsSymm)
    (h : ∀ y : ι → ℝ, ∑ i, ∑ j, y i * y j * Y i j = 0) : Y = 0 := by
  classical
  have hB (y z : ι → ℝ) : ∑ i, ∑ j, y i * z j * Y i j = 0 := by
    have h1 : ∑ i, ∑ j, (y + z) i * (y + z) j * Y i j = 0 := h (y + z)
    have hsymm : ∑ i, ∑ j, z i * y j * Y i j = ∑ i, ∑ j, y i * z j * Y i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
        rw [hY.apply i j]
        ring1
    simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib, h y, h z] at h1
    linarith
  ext i j
  simpa [Pi.single_apply] using hB (Pi.single i 1) (Pi.single j 1)

/-- **Venkov's theorem: a strongly perfect lattice is perfect** (LMFDB
`lattice.spherical_design`): if the minimal vectors `S` of a lattice of `ℝⁿ` form a spherical
`4`-design, the matrices `s sᵀ`, `s ∈ S`, span the symmetric matrices. -/
lemma IsStronglyPerfect.isPerfect (h : IsStronglyPerfect L) : IsPerfect L := by
  classical
  rcases h with ⟨hr, -, hne, -, hpoly⟩
  intro A hA
  by_contra hAS
  rcases Submodule.exists_le_ker_of_notMem hAS with ⟨f, hfA, hf⟩
  have hq (y : ι → ℝ) : f (vecMulVec y y) = ∑ i, ∑ j, y i * y j * dualSymmMatrix f i j := by
    rw [apply_eq_sum_dualSymmMatrix f (transpose_vecMulVec y y)]
    simp only [vecMulVec_apply]
  have hS0 (s : EuclideanSpace ℝ ι) (hs : s ∈ minimalVectors L) :
      ∑ i, ∑ j, s i * s j * dualSymmMatrix f i j = 0 := by
    rw [← hq]
    exact LinearMap.mem_ker.mp (hf (Submodule.subset_span ⟨s, hs, rfl⟩))
  have hhom (t : ℝ) (y : ι → ℝ) : ∑ i, ∑ j, t * y i * (t * y j) * dualSymmMatrix f i j =
      t ^ 2 * ∑ i, ∑ j, y i * y j * dualSymmMatrix f i j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring1
  -- the degree `4` polynomial `(xᵀ Y x)²`
  let P : MvPolynomial ι ℝ := (∑ i, ∑ j, C (dualSymmMatrix f i j) * X i * X j) ^ 2
  have hP : P.totalDegree ≤ 4 := by
    have h2 : (∑ i, ∑ j, C (dualSymmMatrix f i j) * X i * X j : MvPolynomial ι ℝ).totalDegree ≤ 2 :=
      (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦
        (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ ↦
          totalDegree_C_mul_X_mul_X_le _ i j))
    exact (totalDegree_pow _ 2).trans (by omega)
  have hPe (y : ι → ℝ) : P.eval y = (∑ i, ∑ j, y i * y j * dualSymmMatrix f i j) ^ 2 := by
    simp only [P, map_pow, map_sum, map_mul, eval_C, eval_X]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring1
  have hzero : ⨍ x, P.eval (fun i ↦ minimum L * (x : EuclideanSpace ℝ ι) i)
      ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere =
        (Nat.card (minimalVectors L) : ℝ)⁻¹ * ∑ᶠ v ∈ minimalVectors L, P.eval fun i ↦ v i :=
    hpoly P hP
  simp only [hPe] at hzero
  rw [finsum_mem_congr rfl fun s hs ↦ by rw [hS0 s hs, sq, mul_zero], finsum_mem_zero,
    mul_zero] at hzero
  -- the nonnegative continuous integrand vanishes, so `xᵀ Y x = 0` on the unit sphere
  set g : sphere (0 : EuclideanSpace ℝ ι) 1 → ℝ := fun x ↦
    (∑ i, ∑ j, minimum L * (x : EuclideanSpace ℝ ι) i * (minimum L * (x : EuclideanSpace ℝ ι) j) *
      dualSymmMatrix f i j) ^ 2
  have hgc : Continuous g := (continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    ((continuous_const.mul (EuclideanSpace.continuous_apply_toSphere i)).mul
      (continuous_const.mul (EuclideanSpace.continuous_apply_toSphere j))).mul
        continuous_const).pow 2
  have hint : ∫ x, g x ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere = 0 := by
    rcases hne with ⟨s, hs⟩
    have : Nonempty ι := by
      by_contra hι
      rw [not_nonempty_iff] at hι
      exact hs.2.1 (Subsingleton.elim _ _)
    have : NeZero (volume : Measure (EuclideanSpace ℝ ι)).toSphere :=
      ⟨Measure.toSphere_ne_zero _⟩
    rw [average_eq, smul_eq_mul, mul_eq_zero] at hzero
    exact hzero.resolve_left (inv_ne_zero measureReal_univ_ne_zero)
  have hg0 : g = 0 := (hgc.ae_eq_iff_eq _ continuous_const).mp
    ((integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg _)
      (EuclideanSpace.integrable_toSphere hgc)).mp hint)
  have hq0 (y : ι → ℝ) : ∑ i, ∑ j, y i * y j * dualSymmMatrix f i j = 0 := by
    rcases eq_or_ne (WithLp.toLp 2 y : EuclideanSpace ℝ ι) 0 with hy | hy
    · have hy' : y = 0 := by
        simpa using hy
      simp [hy']
    have hx : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ ι)‖⁻¹ • (WithLp.toLp 2 y : EuclideanSpace ℝ ι) ∈
        sphere (0 : EuclideanSpace ℝ ι) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
    have h0 : g ⟨_, hx⟩ = 0 := congrFun hg0 ⟨_, hx⟩
    simp only [g, PiLp.smul_apply, smul_eq_mul, sq_eq_zero_iff] at h0
    have h1 : ∑ i, ∑ j, minimum L * (‖(WithLp.toLp 2 y : EuclideanSpace ℝ ι)‖⁻¹ * y i) *
        (minimum L * (‖(WithLp.toLp 2 y : EuclideanSpace ℝ ι)‖⁻¹ * y j)) * dualSymmMatrix f i j =
          (minimum L * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ ι)‖⁻¹) ^ 2 *
            ∑ i, ∑ j, y i * y j * dualSymmMatrix f i j := by
      rw [← hhom]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring1
    rw [h1, mul_eq_zero] at h0
    exact h0.resolve_left (pow_ne_zero 2 (mul_ne_zero hr.ne'
      (inv_ne_zero (norm_ne_zero_iff.mpr hy))))
  have hY : dualSymmMatrix f = 0 := eq_zero_of_forall_sum_mul_eq_zero (isSymm_dualSymmMatrix f) hq0
  rw [apply_eq_sum_dualSymmMatrix f hA, hY] at hfA
  simp at hfA

/-- The lattice `ℤ` of `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, spanned by the unit vector `e₀`. -/
noncomputable def integerLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 1)) :=
  Submodule.span ℤ {EuclideanSpace.single 0 1}

lemma norm_zsmul_single_zero (z : ℤ) :
    ‖z • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))‖ = |(z : ℝ)| := by
  rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs]

lemma eq_or_eq_neg_of_mem_sphere {y : EuclideanSpace ℝ (Fin 1)} (hy : ‖y‖ = 1) :
    y = EuclideanSpace.single 0 1 ∨ y = -EuclideanSpace.single 0 1 := by
  have h0 : |y 0| = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
      at hy
    exact hy
  rcases abs_eq (zero_le_one' ℝ) |>.mp h0 with h | h
  · exact Or.inl (by ext i; fin_cases i; simpa using h)
  · exact Or.inr (by ext i; fin_cases i; simpa using h)

lemma minimum_integerLattice : minimum integerLattice = 1 := by
  refine IsLeast.csInf_eq ⟨⟨EuclideanSpace.single 0 1, ⟨Submodule.subset_span rfl, ?_⟩, ?_⟩, ?_⟩
  · exact (PiLp.single_eq_zero_iff 2 0).not.mpr one_ne_zero
  · rw [PiLp.norm_single, norm_one]
  · rintro _ ⟨y, ⟨hy, hy0⟩, rfl⟩
    rcases Submodule.mem_span_singleton.mp hy with ⟨z, rfl⟩
    have hz : z ≠ 0 := by
      rintro rfl
      exact hy0 (zero_smul _ _)
    rw [norm_zsmul_single_zero]
    exact_mod_cast Int.one_le_abs hz

lemma minimalVectors_integerLattice :
    minimalVectors integerLattice = {EuclideanSpace.single 0 1, -EuclideanSpace.single 0 1} := by
  ext y
  refine ⟨fun hy ↦ eq_or_eq_neg_of_mem_sphere (hy.2.2.trans minimum_integerLattice), ?_⟩
  have he : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) ∈ integerLattice :=
    Submodule.subset_span rfl
  have he0 : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) ≠ 0 :=
    (PiLp.single_eq_zero_iff 2 0).not.mpr one_ne_zero
  rintro (rfl | rfl)
  · exact ⟨he, he0, by rw [minimum_integerLattice, PiLp.norm_single, norm_one]⟩
  · exact ⟨neg_mem he, neg_ne_zero.mpr he0, by
      rw [minimum_integerLattice, norm_neg, PiLp.norm_single, norm_one]⟩

/-- **The lattice `ℤ` is a spherical `t`-design lattice for every `t`** (LMFDB
`lattice.spherical_design`), in particular strongly perfect: its minimal vectors `±1` form the
whole unit sphere of `ℝ¹`, over which every average is the mean of the values at `±1`. -/
lemma isSphericalDesign_integerLattice (t : ℕ) : IsSphericalDesign t integerLattice := by
  classical
  set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have he : e ≠ -e := fun h ↦ by
    have h0 : e 0 = (-e) 0 := congrArg (· 0) h
    norm_num [e] at h0
  refine ⟨by rw [minimum_integerLattice]; exact one_pos, ?_, ?_, fun v hv ↦ hv.2.2, fun f _ ↦ ?_⟩
  · rw [minimalVectors_integerLattice]
    exact Set.toFinite _
  · rw [minimalVectors_integerLattice]
    exact Set.insert_nonempty _ _
  rw [minimalVectors_integerLattice, minimum_integerLattice, finsum_mem_pair he,
    Nat.card_coe_set_eq, Set.ncard_pair he]
  set F : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 → ℝ := fun x ↦
    f.eval fun i ↦ 1 * (x : EuclideanSpace ℝ (Fin 1)) i
  have hF : Continuous F :=
    (MvPolynomial.continuous_eval f).comp (continuous_pi fun i ↦
      continuous_const.mul (EuclideanSpace.continuous_apply_toSphere i))
  have hneg : ⨍ x, F ((LinearIsometryEquiv.neg ℝ).sphereHomeomorph x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere =
        ⨍ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere :=
    (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin 1))).average_toSphere_comp
      (LinearIsometryEquiv.measurePreserving _) F
  have hpt (x : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) : F x +
      F ((LinearIsometryEquiv.neg ℝ).sphereHomeomorph x) = (f.eval fun i ↦ e i) +
      f.eval fun i ↦ (-e) i := by
    simp only [F, LinearIsometryEquiv.coe_sphereHomeomorph_apply, LinearIsometryEquiv.coe_neg,
      one_mul]
    rcases eq_or_eq_neg_of_mem_sphere (mem_sphere_zero_iff_norm.mp x.2) with hx | hx
    · rw [hx]
    · rw [hx, neg_neg, add_comm]
  have h2 : 2 * ⨍ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere =
      (f.eval fun i ↦ e i) + f.eval fun i ↦ (-e) i := by
    have : NeZero (volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere :=
      ⟨Measure.toSphere_ne_zero _⟩
    rw [two_mul]
    nth_rewrite 2 [← hneg]
    rw [← average_fun_add (f := F)
      (g := fun x ↦ F ((LinearIsometryEquiv.neg ℝ).sphereHomeomorph x))
      (EuclideanSpace.integrable_toSphere hF)
      (EuclideanSpace.integrable_toSphere (hF.comp (Homeomorph.continuous _))),
      average_congr (ae_of_all _ hpt), average_const]
  rw [← h2, Nat.cast_ofNat, inv_mul_cancel_left₀ two_ne_zero]

end ZLattice
