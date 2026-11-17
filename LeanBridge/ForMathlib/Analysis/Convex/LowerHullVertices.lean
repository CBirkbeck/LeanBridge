import LeanBridge.ForMathlib.Analysis.Convex.PolygonEdges
import Mathlib.Data.Nat.Log

/-!
# The lower convex hull of a set of points from its vertices

Let `S` be a set of points of the plane, and let `(n_0, y_0), …, (n_{k + 1}, y_{k + 1})` be points
of `S` with natural abscissas `n_0 ≤ ⋯ ≤ n_{k + 1}` such that `(n_{t + 1}, y_{t + 1})` lies on the
line of slope `τ_t` through `(n_t, y_t)`, and such that every point of `S` lies in the strip
`n_0 ≤ x ≤ n_{k + 1}`, on or above each of these lines (`IsLowerHullVertices`). Then the lower
convex hull of `S` is the polygon through these points: the graph over `[n_0, n_{k + 1}]` of the
maximum of the lines (`vertexPolygon`), which is the line of slope `τ_t` on `[n_t, n_{t + 1}]`. It
is the polygon `TauCeti.polygonGraph` of the convex height sequence of its values at the integers
(`vertexHeights`), whose unit slope is `τ_t` on `[n_t, n_{t + 1}]`. When the slopes increase, the
segments of the hull are the segments from `(n_t, y_t)` to `(n_{t + 1}, y_{t + 1})` with
`n_t < n_{t + 1}`, of slope `τ_t`.

The LMFDB reads the slopes of an extension of `p`-adic fields off such a polygon (LMFDB
`lf.slopes`): the slopes `s > 1` of its segments, each repeated `m` times for the segment running
from `n₁` to `n₂ = p ^ m n₁` (`wildSegmentSlopes`). For the polygon through the vertices, these are
the `τ_t > 1` with `n_t < n_{t + 1}`, repeated `log_p (n_{t + 1} / n_t)` times.

## Main definitions

* `vertexPolygon`: the maximum of the lines of slope `τ_t` through `(n_t, y_t)`, `t ≤ k`.
* `IsLowerHullVertices`: the points `(n_t, y_t)` are the vertices of the lower convex hull of `S`,
  with slopes `τ_t`.
* `vertexHeights`: the values of `vertexPolygon` at the integers of `[n_0, n_{k + 1}]`.
* `slopeMultiplicity` (LMFDB `lf.slopes`): the `m` with `n₂ / n₁ = p ^ m` for the segment of slope
  `s` of a polygon, running from `n₁` to `n₂`.
* `wildSegmentSlopes` (LMFDB `lf.slopes`): the slopes `s > 1` of the segments of a polygon, each
  repeated `slopeMultiplicity p B s` times.

## Main results

* `IsLowerHullVertices.lowerConvexHull_eq`: the lower convex hull of `S` is the graph of
  `vertexPolygon` over `[n_0, n_{k + 1}]`.
* `IsLowerHullVertices.vertexPolygon_eq`: on `[n_t, n_{t + 1}]` the polygon is the line of slope
  `τ_t` through `(n_t, y_t)`.
* `IsLowerHullVertices.lowerConvexHull_eq_polygonGraph`: the lower convex hull of `S` is the polygon
  of the convex height sequence `vertexHeights`.
* `IsLowerHullVertices.isConvexSeq_vertexHeights`: this height sequence is convex.
* `IsLowerHullVertices.unitSlope_vertexHeights`: its unit slope is `τ_t` on `[n_t, n_{t + 1}]`.
* `IsLowerHullVertices.segmentSlopes_lowerConvexHull`: the slopes of the segments of the hull are
  the `τ_t` with `n_t < n_{t + 1}`.
* `IsLowerHullVertices.sUnion_polygonEdgesWithSlope_lowerConvexHull` and
  `IsLowerHullVertices.mem_polygonEdges_lowerConvexHull`: for increasing slopes, the segments of the
  hull are the segments from `(n_t, y_t)` to `(n_{t + 1}, y_{t + 1})` with `n_t < n_{t + 1}`.
* `IsLowerHullVertices.slope_eq_of_segment_subset` and
  `IsLowerHullVertices.exists_eq_of_mem_polygonEdges`: a segment of the hull runs from `n_t` to
  `n_{t + 1}`, with slope `τ_t`.
* `IsLowerHullVertices.slopeMultiplicity_lowerConvexHull` and
  `IsLowerHullVertices.wildSegmentSlopes_lowerConvexHull`: for increasing slopes, the wild slopes
  of the hull are the `τ_t > 1` with `n_t < n_{t + 1}`, repeated `log_p (n_{t + 1} / n_t)` times.
-/

open Set

variable {S : Set (ℝ × ℝ)} {k : ℕ} {n : ℕ → ℕ} {y τ : ℕ → ℝ} {p : ℕ} {B : Set (ℝ × ℝ)}
  {q q' : ℝ × ℝ} {σ : Set (ℝ × ℝ)} {t m : ℕ} {x : ℝ}

variable (k n y τ x) in
/-- The **polygon through the vertices** `(n_t, y_t)`, `t ≤ k + 1`, with slopes `τ_t`, `t ≤ k`: the
maximum of the lines `x ↦ y_t + τ_t (x - n_t)` for `t ≤ k`. When the vertices and the slopes satisfy
`IsLowerHullVertices`, it is the line of slope `τ_t` through `(n_t, y_t)` on `[n_t, n_{t + 1}]`
(`IsLowerHullVertices.vertexPolygon_eq`). -/
noncomputable def vertexPolygon : ℝ :=
  (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one fun t ↦ y t + τ t * (x - n t)

variable (S k n y τ) in
/-- The points `(n_t, y_t)`, `t ≤ k + 1`, are the **vertices of the lower convex hull** of a set `S`
of points of the plane, with slopes `τ_t`, `t ≤ k`: they lie in `S`, their abscissas increase,
`(n_{t + 1}, y_{t + 1})` lies on the line of slope `τ_t` through `(n_t, y_t)`, and every point of
`S` lies in the strip `n_0 ≤ x ≤ n_{k + 1}`, on or above each of these lines. -/
structure IsLowerHullVertices : Prop where
  /-- The vertices lie in `S`. -/
  mem : ∀ t ≤ k + 1, ((n t : ℝ), y t) ∈ S
  /-- The abscissas of the vertices increase. -/
  le_succ : ∀ t ≤ k, n t ≤ n (t + 1)
  /-- The vertex `(n_{t + 1}, y_{t + 1})` lies on the line of slope `τ_t` through `(n_t, y_t)`. -/
  eq_add_mul : ∀ t ≤ k, y (t + 1) = y t + τ t * (n (t + 1) - n t)
  /-- The points of `S` lie on or above the line of slope `τ_t` through `(n_t, y_t)`. -/
  add_mul_le : ∀ q ∈ S, ∀ t ≤ k, y t + τ t * (q.1 - n t) ≤ q.2
  /-- The points of `S` lie in the strip `n_0 ≤ x ≤ n_{k + 1}`. -/
  mem_Icc : ∀ q ∈ S, q.1 ∈ Icc (n 0 : ℝ) (n (k + 1))

variable (k n y τ m) in
/-- The **heights of the polygon through the vertices** at the integers: the value of
`vertexPolygon` at the integers `m` with `n_0 ≤ m ≤ n_{k + 1}`, and `⊤` elsewhere. -/
noncomputable def vertexHeights : WithTop ℝ :=
  if n 0 ≤ m ∧ m ≤ n (k + 1) then (vertexPolygon k n y τ m : WithTop ℝ) else ⊤

variable (p B) in
/-- The **multiplicity at `p` of a slope** `s` of a polygon `B` (LMFDB `lf.slopes`): the `m` with
`n₂ / n₁ = p ^ m`, for the segment of `B` of slope `s` running from the abscissa `n₁` to `n₂`. It is
`⌊log_p (n₂ / n₁)⌋`, read off the projection to the first coordinate of the segments of slope
`s`. -/
noncomputable def slopeMultiplicity (s : ℝ) : ℕ :=
  Nat.log p ⌊sSup (Prod.fst '' ⋃₀ polygonEdgesWithSlope B {s}) /
    sInf (Prod.fst '' ⋃₀ polygonEdgesWithSlope B {s})⌋₊

variable (p B) in
/-- The **wild slopes** at `p` of a polygon `B` (LMFDB `lf.slopes`): the slopes `s > 1` of the
segments of `B`, each repeated `m` times, where the segment of slope `s` runs from the abscissa `n₁`
to `n₂ = p ^ m n₁` (`slopeMultiplicity`). It is a finite sum when `B` has finitely many slopes. -/
noncomputable def wildSegmentSlopes : Multiset ℝ :=
  ∑ᶠ s ∈ segmentSlopes B ∩ Ioi 1, Multiset.replicate (slopeMultiplicity p B s) s

lemma image_fst_segment (h : q.1 ≤ q'.1) : Prod.fst '' segment ℝ q q' = Icc q.1 q'.1 :=
  (image_segment ℝ (LinearMap.fst ℝ ℝ ℝ).toAffineMap q q').trans (segment_eq_Icc h)

namespace IsLowerHullVertices

lemma exists_mem_Icc (hx₀ : (n 0 : ℝ) ≤ x) :
    ∀ j, x ≤ n (j + 1) → ∃ t ≤ j, x ∈ Icc (n t : ℝ) (n (t + 1))
  | 0, h => ⟨0, le_rfl, hx₀, h⟩
  | j + 1, h => (le_or_gt x (n (j + 1))).elim
    (fun h' ↦ (exists_mem_Icc hx₀ j h').imp fun _ ht ↦ ⟨ht.1.trans j.le_succ, ht.2⟩)
    fun h' ↦ ⟨j + 1, le_rfl, h'.le, h⟩

lemma exists_le_lt (hm₀ : n 0 ≤ m) : ∀ j, m < n (j + 1) → ∃ t ≤ j, n t ≤ m ∧ m < n (t + 1)
  | 0, h => ⟨0, le_rfl, hm₀, h⟩
  | j + 1, h => (lt_or_ge m (n (j + 1))).elim
    (fun h' ↦ (exists_le_lt hm₀ j h').imp fun _ ht ↦ ⟨ht.1.trans j.le_succ, ht.2⟩)
    fun h' ↦ ⟨j + 1, le_rfl, h', h⟩

lemma le_of_le (hS : IsLowerHullVertices S k n y τ) {s : ℕ} (hst : s ≤ t) (ht : t ≤ k + 1) :
    n s ≤ n t := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih => exact (ih (by omega)).trans (hS.le_succ t (by omega))

lemma add_mul_le_of_mem_convexHull (hS : IsLowerHullVertices S k n y τ) (hq : q ∈ convexHull ℝ S)
    (ht : t ≤ k) : y t + τ t * (q.1 - n t) ≤ q.2 := by
  have hconv : Convex ℝ {q : ℝ × ℝ | y t + τ t * (q.1 - n t) ≤ q.2} := by
    intro u hu v hv a b ha hb hab
    rw [mem_ofPred_eq] at hu hv ⊢
    rw [eq_sub_of_add_eq hab] at ha ⊢
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linarith [mul_le_mul_of_nonneg_left hu ha, mul_le_mul_of_nonneg_left hv hb]
  exact convexHull_min (fun q hq ↦ hS.add_mul_le q hq t ht) hconv hq

lemma mem_Icc_of_mem_convexHull (hS : IsLowerHullVertices S k n y τ) (hq : q ∈ convexHull ℝ S) :
    q.1 ∈ Icc (n 0 : ℝ) (n (k + 1)) :=
  convexHull_min (fun q hq ↦ hS.mem_Icc q hq)
    ((convex_Icc _ _).is_linear_preimage (LinearMap.fst ℝ ℝ ℝ).isLinear) hq

lemma vertexPolygon_le_of_mem_convexHull (hS : IsLowerHullVertices S k n y τ)
    (hq : q ∈ convexHull ℝ S) : vertexPolygon k n y τ q.1 ≤ q.2 :=
  Finset.sup'_le _ _ fun _ ht ↦
    hS.add_mul_le_of_mem_convexHull hq (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))

lemma mk_mem_convexHull (hS : IsLowerHullVertices S k n y τ) (ht : t ≤ k)
    (hx : x ∈ Icc (n t : ℝ) (n (t + 1))) : (x, y t + τ t * (x - n t)) ∈ convexHull ℝ S := by
  rcases (Nat.cast_le.mpr (hS.le_succ t ht) : (n t : ℝ) ≤ n (t + 1)).lt_or_eq with hlt | heq
  · have hy : y t + (x - n t) / (n (t + 1) - n t) * (y (t + 1) - y t) = y t + τ t * (x - n t) := by
      rw [hS.eq_add_mul t ht]
      field_simp
      ring1
    exact segment_subset_convexHull (hS.mem t (by omega)) (hS.mem (t + 1) (by omega))
      (hy ▸ mk_mem_segment hlt hx)
  · rw [le_antisymm (hx.2.trans heq.ge) hx.1, sub_self, mul_zero, add_zero]
    exact subset_convexHull ℝ S (hS.mem t (by omega))

/-- **The polygon through the vertices is the line of slope `τ_t` on `[n_t, n_{t + 1}]`.** -/
lemma vertexPolygon_eq (hS : IsLowerHullVertices S k n y τ) (ht : t ≤ k)
    (hx : x ∈ Icc (n t : ℝ) (n (t + 1))) : vertexPolygon k n y τ x = y t + τ t * (x - n t) :=
  (hS.vertexPolygon_le_of_mem_convexHull (hS.mk_mem_convexHull ht hx)).antisymm <|
    Finset.le_sup' (fun t ↦ y t + τ t * (x - n t)) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))

lemma mk_vertexPolygon_mem_convexHull (hS : IsLowerHullVertices S k n y τ)
    (hx : x ∈ Icc (n 0 : ℝ) (n (k + 1))) : (x, vertexPolygon k n y τ x) ∈ convexHull ℝ S := by
  rcases exists_mem_Icc hx.1 k hx.2 with ⟨t, ht, hxt⟩
  rw [hS.vertexPolygon_eq ht hxt]
  exact hS.mk_mem_convexHull ht hxt

/-- **The lower convex hull from its vertices**: if the points `(n_t, y_t)` are the vertices of the
lower convex hull of `S` with slopes `τ_t`, in the sense of `IsLowerHullVertices`, then the lower
convex hull of `S` is the graph of the polygon `vertexPolygon` through them over
`[n_0, n_{k + 1}]`. -/
lemma lowerConvexHull_eq (hS : IsLowerHullVertices S k n y τ) : lowerConvexHull S =
    {q | q.1 ∈ Icc (n 0 : ℝ) (n (k + 1)) ∧ q.2 = vertexPolygon k n y τ q.1} := by
  ext q
  refine ⟨fun hq ↦ ⟨hS.mem_Icc_of_mem_convexHull hq.1, ?_⟩, fun hq ↦ ?_⟩
  · exact (hq.2 (hS.mk_vertexPolygon_mem_convexHull (hS.mem_Icc_of_mem_convexHull hq.1))).antisymm
      (hS.vertexPolygon_le_of_mem_convexHull hq.1)
  · refine ⟨?_, fun y hy ↦ ?_⟩
    · rw [mem_ofPred_eq, hq.2]
      exact hS.mk_vertexPolygon_mem_convexHull hq.1
    · rw [hq.2]
      exact hS.vertexPolygon_le_of_mem_convexHull hy

lemma vertexHeights_ne_top_iff : vertexHeights k n y τ m ≠ ⊤ ↔ n 0 ≤ m ∧ m ≤ n (k + 1) := by
  rw [vertexHeights]
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ WithTop.coe_ne_top⟩
  · exact ⟨fun h' ↦ absurd rfl h', fun h' ↦ absurd h' h⟩

lemma untop₀_vertexHeights (hm : n 0 ≤ m ∧ m ≤ n (k + 1)) :
    (vertexHeights k n y τ m).untop₀ = vertexPolygon k n y τ m := by
  rw [vertexHeights, ite_eq_left hm, WithTop.untop₀_coe]

lemma interpolationDomain_vertexHeights :
    TauCeti.interpolationDomain (vertexHeights k n y τ) = Icc (n 0 : ℝ) (n (k + 1)) :=
  TauCeti.interpolationDomain_eq_Icc fun _ ↦ vertexHeights_ne_top_iff

lemma finite_vertexHeights_ne_top : {m | vertexHeights k n y τ m ≠ ⊤}.Finite :=
  (finite_Iic (n (k + 1))).subset fun _ hm ↦ (vertexHeights_ne_top_iff.mp hm).2

lemma mem_finiteEdges_vertexHeights :
    m ∈ TauCeti.finiteEdges (vertexHeights k n y τ) ↔ n 0 ≤ m ∧ m < n (k + 1) := by
  rw [TauCeti.mem_finiteEdges, vertexHeights_ne_top_iff, vertexHeights_ne_top_iff]
  omega

lemma linearInterpolate_vertexHeights (hS : IsLowerHullVertices S k n y τ)
    (hx : x ∈ Icc (n 0 : ℝ) (n (k + 1))) :
    TauCeti.linearInterpolate (fun m ↦ (vertexHeights k n y τ m).untop₀) x =
      vertexPolygon k n y τ x := by
  have hx₀ : 0 ≤ x := (Nat.cast_nonneg _).trans hx.1
  rcases hx.2.lt_or_eq with hlt | heq
  · have hm₀ : n 0 ≤ ⌊x⌋₊ := Nat.le_floor hx.1
    have hm₁ : ⌊x⌋₊ < n (k + 1) := (Nat.floor_lt hx₀).mpr hlt
    rcases exists_le_lt hm₀ k hm₁ with ⟨t, ht, htm, hmt⟩
    have hxm : x ∈ Icc (⌊x⌋₊ : ℝ) (⌊x⌋₊ + 1) := ⟨Nat.floor_le hx₀, (Nat.lt_floor_add_one x).le⟩
    have hle : n (t + 1) ≤ n (k + 1) := hS.le_of_le (by omega) le_rfl
    rw [TauCeti.linearInterpolate_of_mem_Icc _ hxm, untop₀_vertexHeights ⟨hm₀, hm₁.le⟩,
      untop₀_vertexHeights ⟨by omega, by omega⟩,
      hS.vertexPolygon_eq ht ⟨Nat.cast_le.mpr htm, Nat.cast_le.mpr hmt.le⟩,
      hS.vertexPolygon_eq ht ⟨Nat.cast_le.mpr (htm.trans (Nat.le_succ _)), Nat.cast_le.mpr hmt⟩,
      hS.vertexPolygon_eq ht ⟨(Nat.cast_le.mpr htm).trans hxm.1,
        hxm.2.trans (by exact_mod_cast hmt)⟩]
    push_cast
    ring1
  · rw [heq, TauCeti.linearInterpolate_natCast, untop₀_vertexHeights ⟨hS.le_of_le (by omega) le_rfl,
      le_rfl⟩]

/-- **The lower convex hull is the polygon of the heights at the integers**: if the points
`(n_t, y_t)` are the vertices of the lower convex hull of `S` with slopes `τ_t`, then the lower
convex hull of `S` is the polygon `TauCeti.polygonGraph` of the height sequence `vertexHeights`,
whose finite heights are the values of `vertexPolygon` at the integers of `[n_0, n_{k + 1}]`. -/
lemma lowerConvexHull_eq_polygonGraph (hS : IsLowerHullVertices S k n y τ) :
    lowerConvexHull S = TauCeti.polygonGraph (vertexHeights k n y τ) := by
  rw [hS.lowerConvexHull_eq]
  ext q
  rw [TauCeti.polygonGraph, mem_ofPred_eq, mem_ofPred_eq, interpolationDomain_vertexHeights]
  exact and_congr_right fun hq ↦ by rw [hS.linearInterpolate_vertexHeights hq]

/-- **The heights of the polygon through the vertices form a convex sequence.** -/
lemma isConvexSeq_vertexHeights : TauCeti.IsConvexSeq (vertexHeights k n y τ) := by
  refine TauCeti.isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun a ha b hb c hc ↦ ?_⟩, fun m hm hm₂ ↦ ?_⟩
  · rw [mem_ofPred_eq, vertexHeights_ne_top_iff] at ha hb ⊢
    exact ⟨ha.1.trans hc.1, hc.2.trans hb.2⟩
  · rw [vertexHeights_ne_top_iff] at hm hm₂
    rw [untop₀_vertexHeights ⟨by omega, by omega⟩, untop₀_vertexHeights hm,
      untop₀_vertexHeights hm₂]
    have h : vertexPolygon k n y τ ((m + 1 : ℕ) : ℝ) ≤
        (vertexPolygon k n y τ m + vertexPolygon k n y τ ((m + 2 : ℕ) : ℝ)) / 2 :=
      Finset.sup'_le _ _ fun t ht ↦ by
        have h₁ : y t + τ t * ((m : ℝ) - n t) ≤ vertexPolygon k n y τ m :=
          Finset.le_sup' (fun t ↦ y t + τ t * ((m : ℝ) - n t)) ht
        have h₂ : y t + τ t * (((m + 2 : ℕ) : ℝ) - n t) ≤ vertexPolygon k n y τ ((m + 2 : ℕ) : ℝ) :=
          Finset.le_sup' (fun t ↦ y t + τ t * (((m + 2 : ℕ) : ℝ) - n t)) ht
        push_cast at h₂ ⊢
        linarith
    linarith

/-- **The unit slope of the polygon through the vertices is `τ_t` on `[n_t, n_{t + 1}]`.** -/
lemma unitSlope_vertexHeights (hS : IsLowerHullVertices S k n y τ) (ht : t ≤ k) (hm : n t ≤ m)
    (hm' : m < n (t + 1)) : TauCeti.unitSlope (vertexHeights k n y τ) m = τ t := by
  have h₀ : n 0 ≤ n t := hS.le_of_le (Nat.zero_le t) (by omega)
  have h₁ : n (t + 1) ≤ n (k + 1) := hS.le_of_le (by omega) le_rfl
  rw [TauCeti.unitSlope_def, untop₀_vertexHeights ⟨by omega, by omega⟩,
    untop₀_vertexHeights ⟨by omega, by omega⟩,
    hS.vertexPolygon_eq ht ⟨Nat.cast_le.mpr (hm.trans (Nat.le_succ _)), Nat.cast_le.mpr hm'⟩,
    hS.vertexPolygon_eq ht ⟨Nat.cast_le.mpr hm, Nat.cast_le.mpr hm'.le⟩]
  push_cast
  ring1

lemma mem_image_unitSlope_vertexHeights (hS : IsLowerHullVertices S k n y τ) (ht : t ≤ k)
    (hlt : n t < n (t + 1)) : τ t ∈ TauCeti.unitSlope (vertexHeights k n y τ) ''
      TauCeti.finiteEdges (vertexHeights k n y τ) :=
  ⟨n t, mem_finiteEdges_vertexHeights.mpr ⟨hS.le_of_le (Nat.zero_le t) (by omega),
    hlt.trans_le (hS.le_of_le (by omega) le_rfl)⟩, hS.unitSlope_vertexHeights ht le_rfl hlt⟩

/-- **The slopes of the segments of the hull** are the slopes `τ_t` with `n_t < n_{t + 1}`. -/
lemma segmentSlopes_lowerConvexHull (hS : IsLowerHullVertices S k n y τ) :
    segmentSlopes (lowerConvexHull S) = τ '' {t | t ≤ k ∧ n t < n (t + 1)} := by
  rw [hS.lowerConvexHull_eq_polygonGraph, TauCeti.segmentSlopes_polygonGraph]
  ext s
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [mem_finiteEdges_vertexHeights] at hm
    rcases exists_le_lt hm.1 k hm.2 with ⟨t, ht, htm, hmt⟩
    exact ⟨t, ⟨ht, htm.trans_lt hmt⟩, (hS.unitSlope_vertexHeights ht htm hmt).symm⟩
  · rintro ⟨t, ⟨ht, hlt⟩, rfl⟩
    exact hS.mem_image_unitSlope_vertexHeights ht hlt

lemma slopeIndices_vertexHeights (hS : IsLowerHullVertices S k n y τ) (hτ : StrictMonoOn τ (Iic k))
    (ht : t ≤ k) :
    TauCeti.slopeIndices (vertexHeights k n y τ) (τ t) = {m | n t ≤ m ∧ m < n (t + 1)} := by
  ext m
  refine ⟨fun ⟨hm, hslope⟩ ↦ ?_, fun hm ↦ ⟨?_, hS.unitSlope_vertexHeights ht hm.1 hm.2⟩⟩
  · rw [mem_finiteEdges_vertexHeights] at hm
    rcases exists_le_lt hm.1 k hm.2 with ⟨s, hs, hsm, hms⟩
    rw [hS.unitSlope_vertexHeights hs hsm hms] at hslope
    rw [← hτ.injOn (mem_Iic.mpr hs) (mem_Iic.mpr ht) hslope]
    exact ⟨hsm, hms⟩
  · exact mem_finiteEdges_vertexHeights.mpr ⟨(hS.le_of_le (Nat.zero_le t) (by omega)).trans hm.1,
      hm.2.trans_le (hS.le_of_le (by omega) le_rfl)⟩

lemma edgeOfSlope_vertexHeights (hS : IsLowerHullVertices S k n y τ) (hτ : StrictMonoOn τ (Iic k))
    (ht : t ≤ k) (hlt : n t < n (t + 1)) : TauCeti.edgeOfSlope (vertexHeights k n y τ) (τ t) =
      segment ℝ ((n t : ℝ), y t) ((n (t + 1) : ℝ), y (t + 1)) := by
  have hl : sInf (TauCeti.slopeIndices (vertexHeights k n y τ) (τ t)) = n t := by
    rw [hS.slopeIndices_vertexHeights hτ ht]
    exact le_antisymm (Nat.sInf_le ⟨le_rfl, hlt⟩) (le_csInf ⟨n t, le_rfl, hlt⟩ fun _ hm ↦ hm.1)
  have hu : sSup (TauCeti.slopeIndices (vertexHeights k n y τ) (τ t)) + 1 = n (t + 1) := by
    rw [hS.slopeIndices_vertexHeights hτ ht]
    have h : sSup {m | n t ≤ m ∧ m < n (t + 1)} = n (t + 1) - 1 :=
      le_antisymm (csSup_le ⟨n t, le_rfl, hlt⟩ fun _ hm ↦ Nat.le_sub_one_of_lt hm.2)
        (le_csSup ⟨n (t + 1), fun _ hm ↦ hm.2.le⟩ ⟨by omega, by omega⟩)
    omega
  have hy : (vertexHeights k n y τ (n t)).untop₀ = y t := by
    rw [untop₀_vertexHeights ⟨hS.le_of_le (Nat.zero_le t) (by omega),
      hS.le_of_le (by omega) le_rfl⟩, hS.vertexPolygon_eq ht ⟨le_rfl, Nat.cast_le.mpr hlt.le⟩,
      sub_self, mul_zero, add_zero]
  rw [TauCeti.edgeOfSlope, hl, hu, hy, hS.eq_add_mul t ht, mul_comm (τ t)]

/-- **The segment of slope `τ_t` of the hull**: for increasing slopes and `n_t < n_{t + 1}`, the
union of the segments of the lower convex hull of `S` of slope `τ_t` is the segment from
`(n_t, y_t)` to `(n_{t + 1}, y_{t + 1})`. -/
lemma sUnion_polygonEdgesWithSlope_lowerConvexHull (hS : IsLowerHullVertices S k n y τ)
    (hτ : StrictMonoOn τ (Iic k)) (ht : t ≤ k) (hlt : n t < n (t + 1)) :
    ⋃₀ polygonEdgesWithSlope (lowerConvexHull S) {τ t} =
      segment ℝ ((n t : ℝ), y t) ((n (t + 1) : ℝ), y (t + 1)) := by
  rw [hS.lowerConvexHull_eq_polygonGraph, TauCeti.polygonEdgesWithSlope_polygonGraph _
    isConvexSeq_vertexHeights finite_vertexHeights_ne_top,
    inter_singleton_of_mem (hS.mem_image_unitSlope_vertexHeights ht hlt), image_singleton,
    sUnion_singleton, hS.edgeOfSlope_vertexHeights hτ ht hlt]

/-- **The segments of the hull**: for increasing slopes, the segments of the lower convex hull of
`S` are the segments from `(n_t, y_t)` to `(n_{t + 1}, y_{t + 1})` with `n_t < n_{t + 1}`. -/
lemma mem_polygonEdges_lowerConvexHull (hS : IsLowerHullVertices S k n y τ)
    (hτ : StrictMonoOn τ (Iic k)) : σ ∈ polygonEdges (lowerConvexHull S) ↔
      ∃ t ≤ k, n t < n (t + 1) ∧ segment ℝ ((n t : ℝ), y t) ((n (t + 1) : ℝ), y (t + 1)) = σ := by
  rw [hS.lowerConvexHull_eq_polygonGraph, TauCeti.mem_polygonEdges_polygonGraph_iff
    isConvexSeq_vertexHeights finite_vertexHeights_ne_top]
  constructor
  · rintro ⟨s, ⟨m, hm, rfl⟩, rfl⟩
    rw [mem_finiteEdges_vertexHeights] at hm
    rcases exists_le_lt hm.1 k hm.2 with ⟨t, ht, htm, hmt⟩
    rw [hS.unitSlope_vertexHeights ht htm hmt]
    exact ⟨t, ht, htm.trans_lt hmt, (hS.edgeOfSlope_vertexHeights hτ ht (htm.trans_lt hmt)).symm⟩
  · rintro ⟨t, ht, hlt, rfl⟩
    exact ⟨τ t, hS.mem_image_unitSlope_vertexHeights ht hlt, hS.edgeOfSlope_vertexHeights hτ ht hlt⟩

/-- **The slope of a segment of the hull**: a segment `[q, q']`, `q.1 < q'.1`, contained in the
lower convex hull of `S`, with `n_t ≤ q.1 < n_{t + 1}`, has slope `τ_t`. -/
lemma slope_eq_of_segment_subset (hS : IsLowerHullVertices S k n y τ) (ht : t ≤ k) (hq : q.1 < q'.1)
    (hsub : segment ℝ q q' ⊆ lowerConvexHull S) (h₁ : (n t : ℝ) ≤ q.1) (h₂ : q.1 < n (t + 1)) :
    (q'.2 - q.2) / (q'.1 - q.1) = τ t := by
  rw [hS.lowerConvexHull_eq_polygonGraph] at hsub
  have hq₀ : q.1 ∈ TauCeti.interpolationDomain (vertexHeights k n y τ) :=
    (hsub (left_mem_segment ℝ q q')).1
  rw [interpolationDomain_vertexHeights] at hq₀
  have hfl : n t ≤ ⌊q.1⌋₊ := Nat.le_floor h₁
  have hfl' : ⌊q.1⌋₊ < n (t + 1) := (Nat.floor_lt ((Nat.cast_nonneg _).trans h₁)).mpr h₂
  rw [← TauCeti.unitSlope_floor_eq hq hsub, hS.unitSlope_vertexHeights ht hfl hfl']

/-- **The multiplicity of a slope of the hull**: for increasing slopes and `n_t < n_{t + 1}`, the
multiplicity at `p` of the slope `τ_t` of the lower convex hull of `S` is
`⌊log_p (n_{t + 1} / n_t)⌋`, read off its segment from `(n_t, y_t)` to `(n_{t + 1}, y_{t + 1})`. -/
lemma slopeMultiplicity_lowerConvexHull (hS : IsLowerHullVertices S k n y τ)
    (hτ : StrictMonoOn τ (Iic k)) (ht : t ≤ k) (hlt : n t < n (t + 1)) :
    slopeMultiplicity p (lowerConvexHull S) (τ t) = Nat.log p ⌊(n (t + 1) : ℝ) / n t⌋₊ := by
  have hle : ((n t : ℝ), y t).1 ≤ ((n (t + 1) : ℝ), y (t + 1)).1 := Nat.cast_le.mpr hlt.le
  rw [slopeMultiplicity, hS.sUnion_polygonEdgesWithSlope_lowerConvexHull hτ ht hlt,
    image_fst_segment hle, csSup_Icc hle, csInf_Icc hle]

/-- **The wild slopes of the hull**: for increasing slopes, the wild slopes at `p` of the lower
convex hull of `S` (`wildSegmentSlopes`) are the slopes `τ_t > 1` with `n_t < n_{t + 1}`, each
repeated `⌊log_p (n_{t + 1} / n_t)⌋` times. -/
lemma wildSegmentSlopes_lowerConvexHull (hS : IsLowerHullVertices S k n y τ)
    (hτ : StrictMonoOn τ (Iic k)) : wildSegmentSlopes p (lowerConvexHull S) =
      ∑ t ∈ (Finset.range (k + 1)).filter (fun t ↦ n t < n (t + 1) ∧ 1 < τ t),
        Multiset.replicate (Nat.log p ⌊(n (t + 1) : ℝ) / n t⌋₊) (τ t) := by
  have hset : segmentSlopes (lowerConvexHull S) ∩ Ioi 1 =
      τ '' ↑((Finset.range (k + 1)).filter (fun t ↦ n t < n (t + 1) ∧ 1 < τ t)) := by
    rw [hS.segmentSlopes_lowerConvexHull]
    ext s
    simp only [Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨t, ⟨ht, hlt⟩, rfl⟩, hs⟩
      exact ⟨t, ⟨by omega, hlt, hs⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hlt, hs⟩, rfl⟩
      exact ⟨⟨t, ⟨by omega, hlt⟩, rfl⟩, hs⟩
  have hinj : InjOn τ ↑((Finset.range (k + 1)).filter (fun t ↦ n t < n (t + 1) ∧ 1 < τ t)) :=
    hτ.injOn.mono fun t ht ↦ mem_Iic.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp
      (Finset.mem_filter.mp ht).1))
  rw [wildSegmentSlopes, hset, finsum_mem_image hinj, finsum_mem_coe_finset]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [Finset.mem_filter, Finset.mem_range] at ht
  rw [hS.slopeMultiplicity_lowerConvexHull hτ (by omega) ht.2.1]

/-- **The abscissas of a segment of the hull**: for increasing slopes, a segment `[q, q']`,
`q.1 < q'.1`, of the lower convex hull of `S` runs from the abscissa `n_t` to `n_{t + 1}`, for some
`t ≤ k` with `n_t < n_{t + 1}`, and its slope is `τ_t`. -/
lemma exists_eq_of_mem_polygonEdges (hS : IsLowerHullVertices S k n y τ)
    (hτ : StrictMonoOn τ (Iic k)) (hq : q.1 < q'.1)
    (hσ : segment ℝ q q' ∈ polygonEdges (lowerConvexHull S)) : ∃ t ≤ k, n t < n (t + 1) ∧
      q.1 = n t ∧ q'.1 = n (t + 1) ∧ (q'.2 - q.2) / (q'.1 - q.1) = τ t := by
  rcases (hS.mem_polygonEdges_lowerConvexHull hτ).mp hσ with ⟨t, ht, hlt, heq⟩
  have hle : ((n t : ℝ), y t).1 ≤ ((n (t + 1) : ℝ), y (t + 1)).1 := Nat.cast_le.mpr hlt.le
  have hI : Icc (n t : ℝ) (n (t + 1)) = Icc q.1 q'.1 := by
    simpa only [image_fst_segment hle, image_fst_segment hq.le] using congrArg (Prod.fst '' ·) heq
  rcases (Icc_eq_Icc_iff hle).mp hI with ⟨h₁, h₂⟩
  exact ⟨t, ht, hlt, h₁.symm, h₂.symm, hS.slope_eq_of_segment_subset ht hq hσ.2.1 h₁.le <|
    h₁.symm.trans_lt (Nat.cast_lt.mpr hlt)⟩

end IsLowerHullVertices
