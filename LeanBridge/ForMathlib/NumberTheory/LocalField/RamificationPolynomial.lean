import LeanBridge.ForMathlib.Analysis.Convex.LowerConvexHull
import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeInseparability
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolygonHull

/-!
# The ramification polynomial and the ramification polygon

Let `L` be a nonarchimedean local field, `φ` a monic polynomial of degree `n` over a subfield `F`
of `L`, and `α ≠ 0` an element of `L`. The ramification polynomial of `φ` at `α` (LMFDB
`lf.ramification_polygon`) is `ρ(x) = α ^ (-n) φ(α x + α) = x ^ n + ∑_{i < n} ρ_i x ^ i ∈ L[x]`,
and the ramification polygon is the lower convex hull of the points `(-i, v_L(ρ_i))` with
`ρ_i ≠ 0`, the point `(-n, 0)` of the leading coefficient included: the reflection through the
vertical axis of the Newton polygon of `ρ`, the lower convex hull of the points `(i, v_L(ρ_i))`
(LMFDB `lf.newton_polygon`). For a finite extension `L / K` of `p`-adic fields, `F` is the maximal
unramified subextension, `α` a uniformiser of `L` and `φ` its minimal polynomial over `F`.

This file defines the ramification polynomial and the ramification polygon as a subset of the
plane, through Mathlib's convex hull (`lowerConvexHull`), and the ramification polygon of a Herbrand
invariant `I = (r_1, …, r_w)_ε^f` as the LMFDB draws it: the polygonal line through `(-e, 0)`,
`(-p ^ w, 0)` and the points `(-p ^ (w - k), e m_k)`, the reflection of
`IsNonarchimedeanLocalField.HerbrandInvariant.ramificationPolygon`. The slopes of its segments are
`r_1, …, r_w` and, when `ε > 1`, the slope `0` of the segment from `(-e, 0)` to `(-p ^ w, 0)`. When
the ramification polygon of a monic polynomial `g` over `𝒪[F]` at a uniformiser `π` of `L` is the
polygon of `I` in the sense of
`IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon` (Monge's Proposition 1 and
Lemma 1), the ramification polygon of `g` at `π` is that polygonal line.

## Main definitions

* `IsNonarchimedeanLocalField.ramificationPolynomial` (LMFDB `lf.ramification_polygon`): the
  ramification polynomial `ρ(x) = α ^ (-n) φ(α x + α)`.
* `IsNonarchimedeanLocalField.coeffHeight`: the heights `v_L(ρ_i)` of the coefficients of a
  polynomial over `L`.
* `IsNonarchimedeanLocalField.ramificationPolygonOf` (LMFDB `lf.ramification_polygon`): the
  ramification polygon, the lower convex hull of the points `(-i, v_L(ρ_i))`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.reflectedPolygon` (LMFDB
  `lf.ramification_polygon`): the ramification polygon of a Herbrand invariant, as a subset of the
  plane.

## Main results

* `IsNonarchimedeanLocalField.monic_ramificationPolynomial` and
  `IsNonarchimedeanLocalField.ramificationPolynomial_eq_X_pow_add_sum` (LMFDB
  `lf.ramification_polygon`): `ρ(x) = x ^ n + ∑_{i < n} ρ_i x ^ i`.
* `IsNonarchimedeanLocalField.coeff_zero_ramificationPolynomial`: `ρ_0 = 0` when `φ(α) = 0`.
* `IsNonarchimedeanLocalField.addValuation_mul`: the normalised valuation is additive.
* `IsNonarchimedeanLocalField.mem_image_reflectVertical_heightPoints_coeffHeight`: the points of
  the ramification polygon are the `(-i, v_L(ρ_i))` with `ρ_i ≠ 0`.
* `IsNonarchimedeanLocalField.ramificationPolygonOf_eq_image_reflectVertical` (LMFDB
  `lf.ramification_polygon`): the ramification polygon is the reflection of the Newton polygon of
  `ρ` through the vertical axis.
* `IsNonarchimedeanLocalField.coeffHeight_ramificationPolynomial`: the heights
  `IsNonarchimedeanLocalField.HerbrandInvariant.ramificationHeight` are the valuations of the
  coefficients of the ramification polynomial.
* `IsNonarchimedeanLocalField.HerbrandInvariant.segmentSlopes_reflectedPolygon` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.setOf_mem_segmentSlopes_reflectedPolygon_ne_zero`
  (LMFDB `lf.ramification_polygon`): the nonzero slopes of the segments of the ramification polygon
  of `I` are its rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mk_neg_pow_mem_reflectedPolygon` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.mk_neg_ramificationIndex_mem_reflectedPolygon`:
  the points `(-p ^ (w - k), e m_k)` and `(-e, 0)` of the ramification polygon of `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon.ramificationPolygonOf_eq`
  and
  `IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon.ramificationPolygonOf_minpoly`
  (LMFDB `lf.ramification_polygon`): the ramification polygon of a polynomial with the polygon of
  `I`, and of the minimal polynomial of a uniformiser over the field `F`, is the ramification
  polygon of `I`.

## References

* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, p. 3.
-/

open IsDiscreteValuationRing Polynomial TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {φ : F[X]} {α : L} {ρ : L[X]} {n : ℕ}
  {q : ℝ × ℝ}

variable (φ α) in
/-- The **ramification polynomial** `ρ(x) = α ^ (-n) φ(α x + α) ∈ L[x]` (LMFDB
`lf.ramification_polygon`) of a polynomial `φ` of degree `n` over a subfield `F` of `L` at an
element `α` of `L`. For a finite extension `L / K` of `p`-adic fields, `F` is the maximal unramified
subextension of `L / K`, `α` is a uniformiser of `L` and `φ` is its minimal polynomial over `F`. -/
noncomputable def ramificationPolynomial : L[X] :=
  C (α⁻¹ ^ φ.natDegree) * (φ.map (algebraMap F L)).comp (C α * X + C α)

lemma natDegree_ramificationPolynomial (hα : α ≠ 0) :
    (ramificationPolynomial φ α).natDegree = φ.natDegree := by
  rw [ramificationPolynomial, natDegree_C_mul (pow_ne_zero _ <| inv_ne_zero hα), natDegree_comp,
    natDegree_linear hα, mul_one, natDegree_map]

/-- **The ramification polynomial is monic**: for `φ` monic and `α ≠ 0`. -/
lemma monic_ramificationPolynomial (hφ : φ.Monic) (hα : α ≠ 0) :
    (ramificationPolynomial φ α).Monic := by
  rw [Monic, ramificationPolynomial, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_comp (natDegree_linear hα ▸ one_ne_zero), leadingCoeff_linear hα,
    (hφ.map _).leadingCoeff, natDegree_map, one_mul, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hα)]

/-- **The shape of the ramification polynomial** (LMFDB `lf.ramification_polygon`): for `φ` monic
of degree `n` and `α ≠ 0`, `ρ(x) = x ^ n + ∑_{i < n} ρ_i x ^ i`. -/
lemma ramificationPolynomial_eq_X_pow_add_sum (hφ : φ.Monic) (hα : α ≠ 0) :
    ramificationPolynomial φ α = X ^ φ.natDegree +
      ∑ i ∈ Finset.range φ.natDegree, C ((ramificationPolynomial φ α).coeff i) * X ^ i := by
  simpa only [natDegree_ramificationPolynomial hα] using
    (monic_ramificationPolynomial hφ hα).as_sum

/-- **The ramification polynomial has no constant term**: `ρ_0 = 0` when `α` is a root of `φ`. -/
lemma coeff_zero_ramificationPolynomial (h : aeval α φ = 0) :
    (ramificationPolynomial φ α).coeff 0 = 0 := by
  rw [ramificationPolynomial, coeff_zero_eq_eval_zero, eval_mul, eval_comp, eval_add, eval_mul,
    eval_C, eval_X, mul_zero, zero_add, eval_C, eval_map_algebraMap, h, mul_zero]

variable [ValuativeRel L]

variable [ValuativeRel F] [ValuativeExtension F L] {g : 𝒪[F][X]} {π : 𝒪[L]} in
lemma map_mongeShift_zero (hg : g.Monic) (hπ : π ≠ 0) :
    (HerbrandInvariant.mongeShift g π 0).map (algebraMap 𝒪[L] L) =
      C ((π : L) ^ g.natDegree) * ramificationPolynomial (g.map (algebraMap 𝒪[F] F)) (π : L) := by
  have hα : (π : L) ≠ 0 := fun h ↦ hπ <| Subtype.ext h
  have hmap :
      (algebraMap 𝒪[L] L).comp (algebraMap 𝒪[F] 𝒪[L]) = (algebraMap F L).comp (algebraMap 𝒪[F] F) :=
    RingHom.ext coe_algebraMap_integerRing
  rw [ramificationPolynomial, hg.natDegree_map, ← mul_assoc, ← C_mul, ← mul_pow,
    mul_inv_cancel₀ hα, one_pow, C_1, one_mul, HerbrandInvariant.mongeShift, map_comp, map_map,
    map_map, hmap, Polynomial.map_add, Polynomial.map_mul, map_C, map_C, map_X, zero_add, pow_one,
    add_comm]
  rfl

variable [TopologicalSpace L] [IsNonarchimedeanLocalField L] {x y : L} {v : ℝ}

variable (L) in
lemma addValuation_zero : addValuation L 0 = ⊤ :=
  dite_eq_left rfl

lemma addValuation_eq_top_iff : addValuation L x = ⊤ ↔ x = 0 := by
  refine ⟨fun h ↦ by_contra fun hx ↦ ?_, fun h ↦ h ▸ addValuation_zero L⟩
  rw [addValuation, dite_eq_right hx] at h
  exact WithTop.coe_ne_top h

/-- **The normalised valuation is additive**: `v_L(x y) = v_L(x) + v_L(y)` for `x, y ≠ 0`. -/
lemma addValuation_mul (hx : x ≠ 0) (hy : y ≠ 0) :
    addValuation L (x * y) = addValuation L x + addValuation L y := by
  rw [addValuation, addValuation, addValuation, dite_eq_right hx, dite_eq_right hy,
    dite_eq_right (mul_ne_zero hx hy), ← WithTop.coe_add, Units.mk0_mul, map_mul, toAdd_mul]

variable (ρ) in
/-- The **heights of the coefficients** of a polynomial `ρ` over a nonarchimedean local field `L`:
the normalised valuation `v_L(ρ_n)` of the `n`-th coefficient, as a real number, and `⊤` if
`ρ_n = 0`. The points `(n, v_L(ρ_n))` with `ρ_n ≠ 0` are `TauCeti.heightPoints (coeffHeight ρ)`,
and their lower convex hull is the Newton polygon of `ρ` (LMFDB `lf.newton_polygon`). -/
noncomputable def coeffHeight : ℕ → WithTop ℝ :=
  fun n ↦ (addValuation L (ρ.coeff n)).map (↑)

variable (ρ n) in
lemma coeffHeight_apply : coeffHeight ρ n = (addValuation L (ρ.coeff n)).map (↑) :=
  rfl

lemma coeffHeight_eq_top_iff : coeffHeight ρ n = ⊤ ↔ ρ.coeff n = 0 := by
  rw [coeffHeight_apply, WithTop.map_eq_top_iff, addValuation_eq_top_iff]

lemma coeffHeight_eq_coe_iff :
    coeffHeight ρ n = v ↔ ∃ z : ℤ, addValuation L (ρ.coeff n) = z ∧ (z : ℝ) = v :=
  WithTop.map_eq_some_iff

/-- **The points of the ramification polygon**: the reflections through the vertical axis of the
points of a polynomial `ρ` over `L` are the points `(-i, v_L(ρ_i))` for the `i` with `ρ_i ≠ 0`. -/
lemma mem_image_reflectVertical_heightPoints_coeffHeight :
    q ∈ reflectVertical '' heightPoints (coeffHeight ρ) ↔
      ∃ (i : ℕ) (z : ℤ), addValuation L (ρ.coeff i) = z ∧ q = (-(i : ℝ), (z : ℝ)) := by
  rw [mem_image_reflectVertical_heightPoints]
  refine exists_congr fun i ↦ ⟨?_, ?_⟩
  · rintro ⟨hi, hq⟩
    rcases coeffHeight_eq_coe_iff.mp hq with ⟨z, hz, hz'⟩
    exact ⟨z, hz, Prod.ext hi hz'.symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨rfl, coeffHeight_eq_coe_iff.mpr ⟨z, hz, rfl⟩⟩

variable (φ α) in
/-- The **ramification polygon** (LMFDB `lf.ramification_polygon`) of a polynomial `φ` over a
subfield `F` of a nonarchimedean local field `L` at an element `α` of `L`, as a subset of the
plane: the lower convex hull of the points `(-i, v_L(ρ_i))`, for the coefficients `ρ_i ≠ 0` of the
ramification polynomial `ρ(x) = α ^ (-n) φ(α x + α)`, the leading coefficient `ρ_n = 1` included.
The ramification polygon of a finite extension `L / K` of `p`-adic fields is that of the minimal
polynomial over the maximal unramified subextension of a uniformiser `α` of `L`. -/
noncomputable def ramificationPolygonOf : Set (ℝ × ℝ) :=
  lowerConvexHull (reflectVertical '' heightPoints (coeffHeight (ramificationPolynomial φ α)))

variable (φ α) in
/-- **The ramification polygon is the reflection of the Newton polygon of the ramification
polynomial through the vertical axis** (LMFDB `lf.ramification_polygon`), the Newton polygon of `ρ`
being the lower convex hull of the points `(i, v_L(ρ_i))` with `ρ_i ≠ 0` (LMFDB
`lf.newton_polygon`). -/
lemma ramificationPolygonOf_eq_image_reflectVertical : ramificationPolygonOf φ α =
    reflectVertical '' lowerConvexHull (heightPoints (coeffHeight (ramificationPolynomial φ α))) :=
  lowerConvexHull_image_reflectVertical _

variable [ValuativeRel F] [ValuativeExtension F L] {g : 𝒪[F][X]} {π : 𝒪[L]}

/-- **The heights of the ramification polygon are the valuations of the coefficients of the
ramification polynomial**: for a monic polynomial `g` over `𝒪[F]` and a uniformiser `π` of `L`,
`IsNonarchimedeanLocalField.HerbrandInvariant.ramificationHeight g π n` is the valuation
`v_L(ρ_n)` of the `n`-th coefficient of the ramification polynomial `ρ` of `g` at `π`, and `⊤` if
`ρ_n = 0`. -/
lemma coeffHeight_ramificationPolynomial (hg : g.Monic) (hπ : Irreducible π) :
    coeffHeight (ramificationPolynomial (g.map (algebraMap 𝒪[F] F)) (π : L)) =
      HerbrandInvariant.ramificationHeight g π := by
  funext n
  have hα : (π : L) ^ g.natDegree ≠ 0 := pow_ne_zero _ fun h ↦ hπ.ne_zero <| Subtype.ext h
  have hc : (((HerbrandInvariant.mongeShift g π 0).coeff n : 𝒪[L]) : L) = (π : L) ^ g.natDegree *
      (ramificationPolynomial (g.map (algebraMap 𝒪[F] F)) (π : L)).coeff n := by
    rw [← coeff_C_mul, ← map_mongeShift_zero hg hπ.ne_zero, coeff_map]
    rfl
  rw [coeffHeight_apply, HerbrandInvariant.ramificationHeight]
  rcases eq_or_ne ((HerbrandInvariant.mongeShift g π 0).coeff n) 0 with h₀ | h₀
  · rw [h₀, (mul_eq_zero.mp <| hc.symm.trans <| congrArg _ h₀).resolve_left hα,
      addValuation_zero, AddValuation.map_zero, WithTop.map_top, ENat.map_top]
  · have hρ : (ramificationPolynomial (g.map (algebraMap 𝒪[F] F)) (π : L)).coeff n ≠ 0 :=
      fun h ↦ h₀ <| Subtype.ext <| hc.trans <| h ▸ mul_zero _
    rcases ENat.ne_top_iff_exists.mp <| mt addVal_eq_top_iff.mp h₀ with ⟨a, ha⟩
    have h₁ : addValuation L (((HerbrandInvariant.mongeShift g π 0).coeff n : 𝒪[L]) : L) =
        ((a : ℤ) : WithTop ℤ) :=
      addValuation_coe ha.symm
    have h₂ : addValuation L ((π ^ g.natDegree : 𝒪[L]) : L) = ((g.natDegree : ℤ) : WithTop ℤ) :=
      addValuation_coe <| by rw [addVal_pow, addVal_uniformizer hπ, nsmul_one]
    rw [hc, addValuation_mul hα hρ, ← Subring.coe_pow, h₂, addValuation, dite_eq_right hρ,
      ← WithTop.coe_add, WithTop.coe_eq_coe] at h₁
    rw [addValuation, dite_eq_right hρ, ← ha, WithTop.map_coe, ENat.map_natCast,
      WithTop.coe_eq_coe, eq_sub_iff_add_eq']
    exact_mod_cast h₁

namespace HerbrandInvariant

variable {p k : ℕ} (I : HerbrandInvariant p)

/-- The **ramification polygon of a Herbrand invariant** `I = (r_1, …, r_w)_ε^f` (LMFDB
`lf.ramification_polygon`, for a family `I / K`), as a subset of the plane, as the LMFDB draws it:
the reflection through the vertical axis of the polygon with the heights
`IsNonarchimedeanLocalField.HerbrandInvariant.ramificationPolygon`. It is the polygonal line over
`[-e, -1]`, `e = ε p ^ w`, through the points `(-e, 0)`, `(-p ^ w, 0)` and `(-p ^ (w - k), e m_k)`
for `1 ≤ k ≤ w`; its segment between the abscissas `-p ^ (w - k + 1)` and `-p ^ (w - k)` has the
slope `r_k`. -/
noncomputable def reflectedPolygon : Set (ℝ × ℝ) :=
  reflectVertical '' polygonGraph I.ramificationPolygon

lemma mk_neg_natCast_mem_reflectedPolygon :
    (-(n : ℝ), v) ∈ I.reflectedPolygon ↔ I.ramificationPolygon n = v := by
  rw [reflectedPolygon, mem_image_reflectVertical, reflectVertical_apply, neg_neg,
    natCast_mem_polygonGraph]

lemma finiteEdges_ramificationPolygon :
    finiteEdges I.ramificationPolygon = Set.Ico 1 I.ramificationIndex := by
  ext n
  rw [mem_finiteEdges, ramificationPolygon_ne_top_iff, ramificationPolygon_ne_top_iff,
    Set.mem_Icc, Set.mem_Icc, Set.mem_Ico]
  omega

/-- **The slopes of the segments of the ramification polygon of a Herbrand invariant**: they are
the negatives of the unit slopes of
`IsNonarchimedeanLocalField.HerbrandInvariant.ramificationPolygon` on its edges from `n` to `n + 1`
for `1 ≤ n < e`. -/
lemma segmentSlopes_reflectedPolygon : segmentSlopes I.reflectedPolygon =
    {s | ∃ n ∈ Set.Ico 1 I.ramificationIndex, -unitSlope I.ramificationPolygon n = s} := by
  rw [reflectedPolygon, segmentSlopes_image_reflectVertical,
    segmentSlopes_polygonGraph, finiteEdges_ramificationPolygon, Set.image_image]
  rfl

variable [Fact p.Prime]

/-- **The vertices of the ramification polygon of a Herbrand invariant**: it passes through the
points `(-p ^ (w - k), e m_k)` for `0 ≤ k ≤ w` and the means `m_k`. -/
lemma mk_neg_pow_mem_reflectedPolygon (hk : k ≤ I.w) :
    (-((p ^ (I.w - k) : ℕ) : ℝ), ((I.ramificationIndex * I.mean k : ℚ) : ℝ)) ∈ I.reflectedPolygon :=
  I.mk_neg_natCast_mem_reflectedPolygon.mpr <| I.ramificationPolygon_pow hk

/-- **The left end of the ramification polygon of a Herbrand invariant** is the point `(-e, 0)`
of the leading coefficient of the ramification polynomial. -/
lemma mk_neg_ramificationIndex_mem_reflectedPolygon :
    (-(I.ramificationIndex : ℝ), 0) ∈ I.reflectedPolygon :=
  I.mk_neg_natCast_mem_reflectedPolygon.mpr <|
    I.ramificationPolygon_of_pow_le (Nat.le_mul_of_pos_left _ I.ε_pos) le_rfl

/-- **The nonzero slopes of the segments of the ramification polygon of a Herbrand invariant are
its rams** (LMFDB `lf.ramification_polygon`, with "nonzero slopes" for "slopes"): the nonzero
slopes of the segments of the ramification polygon of `I = (r_1, …, r_w)_ε^f` are `r_1, …, r_w`.
The slope `0`, which occurs when `ε > 1`, is not a ram. -/
lemma setOf_mem_segmentSlopes_reflectedPolygon_ne_zero :
    {s | s ≠ 0 ∧ s ∈ segmentSlopes I.reflectedPolygon} =
      {s | ∃ j < I.w, (I.ram (j + 1) : ℝ) = s} := by
  rw [segmentSlopes_reflectedPolygon]
  exact I.setOf_neg_unitSlope_ramificationPolygon_ne_zero

variable {I}

/-- **The ramification polygon of a polynomial with the polygon of a Herbrand invariant** (LMFDB
`lf.ramification_polygon`): let `g` be a monic polynomial over `𝒪[F]` with a root `π`, a
uniformiser of `L`, whose ramification polygon is the polygon of the Herbrand invariant `I` in the
sense of `IsRamificationPolygon` (Monge's Proposition 1 and Lemma 1). Then the ramification polygon
of `g` at `π`, the lower convex hull of the points `(-i, v_L(ρ_i))` of its ramification polynomial
`ρ`, is the ramification polygon of `I`. -/
lemma IsRamificationPolygon.ramificationPolygonOf_eq (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hg : g.Monic) (hroot : aeval π g = 0) :
    ramificationPolygonOf (g.map (algebraMap 𝒪[F] F)) (π : L) = I.reflectedPolygon := by
  have hfin : {n | ramificationHeight g π n ≠ ⊤}.Finite :=
    (Set.finite_Iic g.natDegree).subset fun n hn ↦
      not_lt.mp fun h ↦ hn <| ramificationHeight_of_natDegree_lt h
  rw [ramificationPolygonOf, coeffHeight_ramificationPolynomial hg hπ,
    lowerConvexHull_image_reflectVertical, lowerConvexHull_heightPoints hfin,
    hP.lowerConvexEnvelope_eq hπ hg hroot, reflectedPolygon]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- **The ramification polygon of a uniformiser with the polygon of a Herbrand invariant** (LMFDB
`lf.ramification_polygon`): for a finite extension `L / F` of nonarchimedean local fields and a
uniformiser `π` of `L`, if the ramification polygon of the minimal polynomial of `π` over `𝒪[F]`
is the polygon of the Herbrand invariant `I` in the sense of `IsRamificationPolygon`, then the
ramification polygon of the minimal polynomial `φ` of `π` over the field `F`, the lower convex
hull of the points `(-i, v_L(ρ_i))` of `ρ(x) = π ^ (-n) φ(π x + π)`, is the ramification polygon of
`I`. -/
lemma IsRamificationPolygon.ramificationPolygonOf_minpoly
    (hP : I.IsRamificationPolygon (minpoly 𝒪[F] π) π) (hπ : Irreducible π) :
    ramificationPolygonOf (minpoly F (π : L)) (π : L) = I.reflectedPolygon := by
  have hint : IsIntegral 𝒪[F] π := IsIntegral.of_finite 𝒪[F] π
  have hmin : minpoly F (π : L) = (minpoly 𝒪[F] π).map (algebraMap 𝒪[F] F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F L hint
  rw [hmin]
  exact hP.ramificationPolygonOf_eq hπ (minpoly.monic hint) (minpoly.aeval _ π)

end HerbrandInvariant

end IsNonarchimedeanLocalField
