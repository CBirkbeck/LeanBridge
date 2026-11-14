import Mathlib.Analysis.Convex.Topology
import TauCeti.Analysis.Convex.Sequence.Envelope
import TauCeti.Analysis.Convex.Sequence.Interpolation

/-!
# The lower convex hull of a set of points of the plane

The lower convex hull of a set `S` of points of the plane is the lower boundary of its convex hull.
Newton polygons are lower convex hulls of points `(n, h_n)` with natural abscissas, which Tau Ceti
treats through the height sequence `h : ℕ → WithTop ℝ` and its lower convex envelope
`TauCeti.lowerConvexEnvelope h`, the greatest convex sequence below `h`. This file defines the lower
convex hull with Mathlib's `convexHull` and proves that the two notions agree: for a height sequence
with finitely many finite heights, the lower convex hull of its points is the graph of the
piecewise-affine interpolation of its lower convex envelope. So the envelope gives the heights of
the polygon at the integers, its vertices among them, and its unit slopes are the slopes of the
segments of the polygon.

The lower convex hull and the slopes of segments are compatible with the reflection of the plane
through the vertical axis, which negates the slopes; this is how the LMFDB draws the ramification
polygon of an extension of `p`-adic fields (LMFDB `lf.ramification_polygon`).

## Main definitions

* `lowerConvexHull`: the lower convex hull of a set of points of the plane.
* `segmentSlopes`: the slopes of the segments of a subset of the plane.
* `reflectVertical`: the reflection of the plane through the vertical axis.
* `TauCeti.heightPoints`: the points `(n, h_n)` of a height sequence.
* `TauCeti.polygonGraph`: the polygon of a height sequence, as a subset of the plane.

## Main results

* `lowerConvexHull_image_reflectVertical`: the lower convex hull of the reflected points is the
  reflection of the lower convex hull.
* `segmentSlopes_image_reflectVertical`: the reflection negates the slopes of the segments.
* `TauCeti.linearInterpolate_le_of_mem_convexHull_heightPoints`: the convex hull of the points of a
  height sequence lies above the polygon of its lower convex envelope.
* `TauCeti.lowerConvexHull_heightPoints`: the lower convex hull of the points of a height sequence
  is the polygon of its lower convex envelope.
* `TauCeti.segmentSlopes_polygonGraph`: the slopes of the segments of the polygon of a height
  sequence are its unit slopes.
-/

open Set

/-- The **lower convex hull** of a set `S` of points of the plane: the lower boundary of the convex
hull of `S`, that is the points `(x, y)` of the convex hull such that the convex hull has no point
`(x, y')` with `y' < y`. -/
def lowerConvexHull (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {q | IsLeast {y | (q.1, y) ∈ convexHull ℝ S} q.2}

/-- The **slopes of the segments** of a subset `P` of the plane: the slopes of the segments, not
vertical and not reduced to a point, that `P` contains. When `P` is a polygonal line that is the
graph of a function, these are the slopes of its maximal segments. -/
def segmentSlopes (P : Set (ℝ × ℝ)) : Set ℝ :=
  {s | ∃ q ∈ P, ∃ q' ∈ P, q.1 < q'.1 ∧ segment ℝ q q' ⊆ P ∧ (q'.2 - q.2) / (q'.1 - q.1) = s}

/-- The **reflection of the plane through the vertical axis**, `(x, y) ↦ (-x, y)`. -/
def reflectVertical : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ :=
  (-LinearMap.id).prodMap LinearMap.id

variable {S P : Set (ℝ × ℝ)} {q : ℝ × ℝ} {x x₁ x₂ y₁ y₂ : ℝ}

variable (q) in
lemma reflectVertical_apply : reflectVertical q = (-q.1, q.2) :=
  rfl

variable (q) in
lemma reflectVertical_reflectVertical : reflectVertical (reflectVertical q) = q := by
  rw [reflectVertical_apply, reflectVertical_apply, neg_neg]

lemma mem_image_reflectVertical : q ∈ reflectVertical '' P ↔ reflectVertical q ∈ P :=
  ⟨fun ⟨_, h, hq⟩ ↦ hq ▸ (reflectVertical_reflectVertical _).symm ▸ h,
    fun h ↦ ⟨_, h, reflectVertical_reflectVertical q⟩⟩

variable (P) in
lemma image_reflectVertical_image_reflectVertical : reflectVertical '' (reflectVertical '' P) = P :=
  ext fun _ ↦ by rw [mem_image_reflectVertical, mem_image_reflectVertical,
    reflectVertical_reflectVertical]

variable (S) in
/-- **The lower convex hull of the reflected points is the reflection of the lower convex hull**,
for the reflection through the vertical axis. -/
lemma lowerConvexHull_image_reflectVertical :
    lowerConvexHull (reflectVertical '' S) = reflectVertical '' lowerConvexHull S :=
  ext fun q ↦ by
    simp only [lowerConvexHull, mem_ofPred_eq, ← reflectVertical.image_convexHull,
      mem_image_reflectVertical, reflectVertical_apply]

lemma segmentSlopes_image_reflectVertical_subset :
    segmentSlopes (reflectVertical '' P) ⊆ Neg.neg '' segmentSlopes P := by
  rintro s ⟨q, hq, q', hq', hlt, hseg, rfl⟩
  have himage :
      reflectVertical '' segment ℝ q' q = segment ℝ (reflectVertical q') (reflectVertical q) :=
    image_segment ℝ reflectVertical.toAffineMap q' q
  refine ⟨_, ⟨reflectVertical q', mem_image_reflectVertical.mp hq', reflectVertical q,
    mem_image_reflectVertical.mp hq, neg_lt_neg hlt, ?_, rfl⟩, ?_⟩
  · rw [← himage, segment_symm]
    exact (image_mono hseg).trans (image_reflectVertical_image_reflectVertical P).subset
  · rw [reflectVertical_apply, reflectVertical_apply, ← neg_div, neg_sub, neg_sub_neg,
      ← neg_div_neg_eq, neg_sub, neg_sub]

variable (P) in
/-- **The reflection through the vertical axis negates the slopes of the segments.** -/
lemma segmentSlopes_image_reflectVertical :
    segmentSlopes (reflectVertical '' P) = Neg.neg '' segmentSlopes P := by
  refine segmentSlopes_image_reflectVertical_subset.antisymm ?_
  rintro _ ⟨s, hs, rfl⟩
  rw [← image_reflectVertical_image_reflectVertical P] at hs
  rcases segmentSlopes_image_reflectVertical_subset hs with ⟨t, ht, rfl⟩
  rwa [neg_neg]

lemma mk_mem_segment (h : x₁ < x₂) (hx : x ∈ Icc x₁ x₂) :
    (x, y₁ + (x - x₁) / (x₂ - x₁) * (y₂ - y₁)) ∈ segment ℝ (x₁, y₁) (x₂, y₂) := by
  have hd : 0 < x₂ - x₁ := sub_pos.mpr h
  refine ⟨1 - (x - x₁) / (x₂ - x₁), (x - x₁) / (x₂ - x₁),
    sub_nonneg.mpr <| (div_le_one hd).mpr <| sub_le_sub_right hx.2 _,
    div_nonneg (sub_nonneg.mpr hx.1) hd.le, sub_add_cancel 1 _, Prod.ext ?_ ?_⟩
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    field_simp
    ring1
  · simp only [Prod.smul_mk, Prod.mk_add_mk]
    ring1

namespace TauCeti

variable {a h : ℕ → WithTop ℝ} {c m y : ℝ} {n : ℕ}

variable (h) in
/-- The **points of a height sequence** `h`: the points `(n, h_n)` of the plane, for the natural
numbers `n` with `h_n` finite. -/
def heightPoints : Set (ℝ × ℝ) :=
  {q | ∃ n : ℕ, q.1 = n ∧ h n = q.2}

variable (h) in
/-- The **polygon of a height sequence** `h`, as a subset of the plane: the graph of the
piecewise-affine interpolation of the heights over the real domain of `h`, that is the union of
the segments joining `(n, h_n)` to `(n + 1, h_{n + 1})`, together with the isolated points
`(n, h_n)`, for the finite heights. -/
def polygonGraph : Set (ℝ × ℝ) :=
  {q | q.1 ∈ interpolationDomain h ∧ q.2 = linearInterpolate (fun n ↦ (h n).untop₀) q.1}

lemma natCast_mem_heightPoints : ((n : ℝ), y) ∈ heightPoints h ↔ h n = y := by
  refine ⟨?_, fun hy ↦ ⟨n, rfl, hy⟩⟩
  rintro ⟨k, hk, hy⟩
  rwa [Nat.cast_injective hk]

lemma mem_image_reflectVertical_heightPoints :
    q ∈ reflectVertical '' heightPoints h ↔ ∃ n : ℕ, q.1 = -n ∧ h n = q.2 := by
  rw [mem_image_reflectVertical, reflectVertical_apply]
  exact exists_congr fun n ↦ and_congr_left fun _ ↦ neg_eq_iff_eq_neg

lemma natCast_mem_polygonGraph : ((n : ℝ), y) ∈ polygonGraph h ↔ h n = y := by
  rw [polygonGraph, mem_ofPred_eq, natCast_mem_interpolationDomain, linearInterpolate_natCast]
  refine ⟨fun ⟨hn, hy⟩ ↦ ?_, fun hy ↦ ?_⟩
  · have hy' : y = (h n).untop₀ := hy
    rw [hy', WithTop.coe_untop₀_of_ne_top hn]
  · rw [hy]
    exact ⟨WithTop.coe_ne_top, rfl⟩

lemma mem_interpolationDomain_of_mem_Icc (hn : h n ≠ ⊤) (hn' : h (n + 1) ≠ ⊤)
    (hx : x ∈ Icc (n : ℝ) (n + 1)) : x ∈ interpolationDomain h := by
  have hx₀ : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
  rcases hx.2.lt_or_eq with hlt | rfl
  · have hfl : ⌊x⌋₊ = n := (Nat.floor_eq_iff hx₀).mpr ⟨hx.1, hlt⟩
    have hce : ⌈x⌉₊ = n ∨ ⌈x⌉₊ = n + 1 := by
      have h₁ : ⌈x⌉₊ ≤ ⌊x⌋₊ + 1 := Nat.ceil_le_floor_add_one x
      have h₂ : ⌊x⌋₊ ≤ ⌈x⌉₊ := Nat.floor_le_ceil x
      omega
    refine ⟨hx₀, hfl ▸ hn, ?_⟩
    rcases hce with h | h
    · exact h ▸ hn
    · exact h ▸ hn'
  · rw [← Nat.cast_add_one]
    exact natCast_mem_interpolationDomain.mpr hn'

lemma isAdmissible_of_finite (ha : {n | a n ≠ ⊤}.Finite) : IsAdmissible a := by
  rcases (ha.image fun n ↦ (a n).untop₀).bddBelow with ⟨c, hc⟩
  refine ⟨c, 0, fun n ↦ ?_⟩
  rcases eq_or_ne (a n) ⊤ with hn | hn
  · exact hn ▸ le_top
  · rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe, zero_mul, add_zero]
    exact hc ⟨n, hn, rfl⟩

lemma finite_heightPoints (ha : {n | a n ≠ ⊤}.Finite) : (heightPoints a).Finite := by
  refine (ha.image fun n : ℕ ↦ ((n : ℝ), (a n).untop₀)).subset ?_
  rintro q ⟨n, hn, hy⟩
  exact ⟨n, by rw [mem_ofPred_eq, hy]; exact WithTop.coe_ne_top,
    Prod.ext hn.symm <| congrArg WithTop.untop₀ hy⟩

lemma add_mul_le_of_mem_convexHull_heightPoints (hcm : ∀ n : ℕ, ((c + m * n : ℝ) : WithTop ℝ) ≤ a n)
    (hq : q ∈ convexHull ℝ (heightPoints a)) : c + m * q.1 ≤ q.2 := by
  have hconv : Convex ℝ {q : ℝ × ℝ | c + m * q.1 ≤ q.2} := by
    intro u hu v hv s t hs ht hst
    rw [mem_ofPred_eq] at hu hv ⊢
    rw [eq_sub_of_add_eq hst] at hs ⊢
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linarith [mul_le_mul_of_nonneg_left hu hs, mul_le_mul_of_nonneg_left hv ht]
  refine convexHull_min ?_ hconv hq
  rintro u ⟨n, hn, hy⟩
  have h : ((c + m * n : ℝ) : WithTop ℝ) ≤ a n := hcm n
  rw [hy, WithTop.coe_le_coe] at h
  rwa [mem_ofPred_eq, hn]

/-- **The convex hull of the points lies above the polygon of the lower convex envelope**: a point
`(x, y)` of the convex hull of the points of an admissible height sequence `a`, with `x` in the
real domain of the lower convex envelope of `a`, lies on or above the piecewise-affine
interpolation of the envelope. -/
lemma linearInterpolate_le_of_mem_convexHull_heightPoints (ha : IsAdmissible a)
    (hq : q ∈ convexHull ℝ (heightPoints a))
    (hx : q.1 ∈ interpolationDomain (lowerConvexEnvelope a)) :
    linearInterpolate (fun n ↦ (lowerConvexEnvelope a n).untop₀) q.1 ≤ q.2 := by
  rcases (isConvexSeq_lowerConvexEnvelope a).exists_affine_minorant_eq_linearInterpolate hx with
    ⟨c, m, hcm, hc⟩
  exact hc ▸ add_mul_le_of_mem_convexHull_heightPoints
    (fun n ↦ (hcm n).trans <| lowerConvexEnvelope_le ha n) hq

lemma natCast_untop₀_mem_convexHull_heightPoints (ha : {n | a n ≠ ⊤}.Finite)
    (hn : lowerConvexEnvelope a n ≠ ⊤) :
    ((n : ℝ), (lowerConvexEnvelope a n).untop₀) ∈ convexHull ℝ (heightPoints a) := by
  classical
  have hadm : IsAdmissible a := isAdmissible_of_finite ha
  have hconv : Convex ℝ (convexHull ℝ (heightPoints a)) := convex_convexHull ℝ _
  have hcomp : IsCompact (convexHull ℝ (heightPoints a)) :=
    (finite_heightPoints ha).isCompact_convexHull ℝ
  have hfib (j : ℕ) : IsCompact {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)} := by
    have h : {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)} =
        Prod.snd '' (convexHull ℝ (heightPoints a) ∩ {q | q.1 = j}) := by
      ext y
      refine ⟨fun hy ↦ ⟨((j : ℝ), y), ⟨hy, rfl⟩, rfl⟩, ?_⟩
      rintro ⟨q, ⟨hq, hq'⟩, rfl⟩
      rwa [mem_ofPred_eq, ← hq', Prod.mk.eta]
    rw [h]
    exact (hcomp.inter_right <| isClosed_eq continuous_fst continuous_const).image continuous_snd
  have hmem (j : ℕ) (hj : {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)}.Nonempty) :
      ((j : ℝ), sInf {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)}) ∈
        convexHull ℝ (heightPoints a) :=
    (hfib j).sInf_mem hj
  let G : ℕ → WithTop ℝ := fun j ↦
    if {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)}.Nonempty then
      ((sInf {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)} : ℝ) : WithTop ℝ) else ⊤
  have hG (j : ℕ) (hj : {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)}.Nonempty) :
      G j = ((sInf {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)} : ℝ) : WithTop ℝ) :=
    ite_eq_left hj
  have hGne (j : ℕ) (hj : G j ≠ ⊤) : {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)}.Nonempty :=
    by_contra fun h ↦ hj <| ite_eq_right h
  have hGa : G ≤ a := fun j ↦ by
    rcases eq_or_ne (a j) ⊤ with hj | hj
    · exact hj ▸ le_top
    · have hy : (a j).untop₀ ∈ {y | ((j : ℝ), y) ∈ convexHull ℝ (heightPoints a)} :=
        subset_convexHull ℝ _ <| natCast_mem_heightPoints.mpr
          (WithTop.coe_untop₀_of_ne_top hj).symm
      rw [hG j ⟨_, hy⟩, ← WithTop.coe_untop₀_of_ne_top hj, WithTop.coe_le_coe]
      exact csInf_le (hfib j).bddBelow hy
  have hGconv : IsConvexSeq G := by
    refine isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun i hi k hk j hj ↦ ?_⟩, fun j hj hj₂ ↦ ?_⟩
    · rcases hj.1.eq_or_lt with rfl | hij
      · exact hi
      · have hik : (i : ℝ) < k := Nat.cast_lt.mpr <| hij.trans_le hj.2
        have hmem' : ((j : ℝ), _) ∈ convexHull ℝ (heightPoints a) :=
          hconv.segment_subset (hmem i <| hGne i hi) (hmem k <| hGne k hk) <|
            mk_mem_segment hik ⟨Nat.cast_le.mpr hj.1, Nat.cast_le.mpr hj.2⟩
        rw [mem_ofPred_eq, hG j ⟨_, hmem'⟩]
        exact WithTop.coe_ne_top
    · have hlt : (j : ℝ) < (j + 2 : ℕ) := Nat.cast_lt.mpr <| by omega
      have h₁ : ((j + 1 : ℕ) : ℝ) - j = 1 := by
        push_cast
        ring1
      have h₂ : ((j + 2 : ℕ) : ℝ) - j = 2 := by
        push_cast
        ring1
      have hmem' : (((j + 1 : ℕ) : ℝ), _) ∈ convexHull ℝ (heightPoints a) :=
        hconv.segment_subset (hmem j <| hGne j hj) (hmem (j + 2) <| hGne (j + 2) hj₂) <|
          mk_mem_segment hlt ⟨Nat.cast_le.mpr <| by omega, Nat.cast_le.mpr <| by omega⟩
      have hle : sInf {y | (((j + 1 : ℕ) : ℝ), y) ∈ convexHull ℝ (heightPoints a)} ≤ _ :=
        csInf_le (hfib (j + 1)).bddBelow hmem'
      rw [hG j <| hGne j hj, hG (j + 1) ⟨_, hmem'⟩, hG (j + 2) <| hGne (j + 2) hj₂,
        WithTop.untop₀_coe, WithTop.untop₀_coe, WithTop.untop₀_coe]
      rw [h₁, h₂] at hle
      linarith
  have hne : {y | ((n : ℝ), y) ∈ convexHull ℝ (heightPoints a)}.Nonempty :=
    hGne n <| ne_top_of_le_ne_top hn <| le_lowerConvexEnvelope hGconv hGa n
  have hle : G n ≤ lowerConvexEnvelope a n := le_lowerConvexEnvelope hGconv hGa n
  have hge :
      (lowerConvexEnvelope a n).untop₀ ≤ sInf {y | ((n : ℝ), y) ∈ convexHull ℝ (heightPoints a)} :=
    (linearInterpolate_natCast _ n).symm.trans_le <|
      linearInterpolate_le_of_mem_convexHull_heightPoints hadm (hmem n hne) <|
        natCast_mem_interpolationDomain.mpr hn
  rw [hG n hne, ← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe] at hle
  exact hle.antisymm hge ▸ hmem n hne

lemma mk_linearInterpolate_mem_convexHull_heightPoints (ha : {n | a n ≠ ⊤}.Finite)
    (hx : x ∈ interpolationDomain (lowerConvexEnvelope a)) :
    (x, linearInterpolate (fun n ↦ (lowerConvexEnvelope a n).untop₀) x) ∈
      convexHull ℝ (heightPoints a) := by
  rcases hx with ⟨hx₀, hfl, hce⟩
  by_cases hedge : lowerConvexEnvelope a (⌊x⌋₊ + 1) = ⊤
  · have hc : ⌈x⌉₊ = ⌊x⌋₊ := (Nat.floor_le_ceil x).antisymm' <| Nat.lt_succ_iff.mp <|
      (Nat.ceil_le_floor_add_one x).lt_of_ne fun hc ↦ hce <| hc ▸ hedge
    have hxn : x = ⌊x⌋₊ := (hc ▸ Nat.le_ceil x).antisymm <| Nat.floor_le hx₀
    rw [hxn, linearInterpolate_natCast]
    exact natCast_untop₀_mem_convexHull_heightPoints ha <| hxn ▸ hfl
  · have hmem : (x, _) ∈ convexHull ℝ (heightPoints a) :=
      (convex_convexHull ℝ _).segment_subset
        (natCast_untop₀_mem_convexHull_heightPoints ha hfl)
        (natCast_untop₀_mem_convexHull_heightPoints ha hedge) <|
        mk_mem_segment (Nat.cast_lt.mpr ⌊x⌋₊.lt_succ_self)
          ⟨Nat.floor_le hx₀, (Nat.lt_floor_add_one x).le.trans_eq (Nat.cast_add_one _).symm⟩
    rwa [Nat.cast_add_one, add_sub_cancel_left, div_one] at hmem

/-- **The lower convex hull of the points of a height sequence is the polygon of its lower convex
envelope**: for a height sequence `a` with finitely many finite heights, the lower boundary of the
convex hull of the points `(n, a_n)` is the graph of the piecewise-affine interpolation of the
lower convex envelope of `a`. So Tau Ceti's `TauCeti.lowerConvexEnvelope` is the lower convex hull
of a finite set of points with natural abscissas, read at the integers. -/
lemma lowerConvexHull_heightPoints (ha : {n | a n ≠ ⊤}.Finite) :
    lowerConvexHull (heightPoints a) = polygonGraph (lowerConvexEnvelope a) := by
  have hadm : IsAdmissible a := isAdmissible_of_finite ha
  have hdom :
      convexHull ℝ (heightPoints a) ⊆ Prod.fst ⁻¹' interpolationDomain (lowerConvexEnvelope a) := by
    refine convexHull_min ?_ <| (convex_interpolationDomain_iff.mpr
      (isConvexSeq_lowerConvexEnvelope a).ordConnected).is_linear_preimage
        (LinearMap.fst ℝ ℝ ℝ).isLinear
    rintro q ⟨n, hn, hy⟩
    rw [mem_preimage, hn, natCast_mem_interpolationDomain]
    exact ne_top_of_le_ne_top (hy ▸ WithTop.coe_ne_top) <| lowerConvexEnvelope_le hadm n
  ext q
  refine ⟨fun hq ↦ ⟨hdom hq.1, ?_⟩, fun hq ↦ ?_⟩
  · exact (hq.2 <| mk_linearInterpolate_mem_convexHull_heightPoints ha <| hdom hq.1).antisymm <|
      linearInterpolate_le_of_mem_convexHull_heightPoints hadm hq.1 <| hdom hq.1
  · rw [lowerConvexHull, mem_ofPred_eq, hq.2]
    exact ⟨mk_linearInterpolate_mem_convexHull_heightPoints ha hq.1, fun y hy ↦
      linearInterpolate_le_of_mem_convexHull_heightPoints hadm hy hq.1⟩

variable (h) in
/-- **The slopes of the segments of the polygon of a height sequence are its unit slopes**: the
slopes of the segments contained in the polygon of `h` are the increments `h_{n + 1} - h_n`
between consecutive finite heights. -/
lemma segmentSlopes_polygonGraph :
    segmentSlopes (polygonGraph h) = unitSlope h '' finiteEdges h := by
  refine Subset.antisymm ?_ ?_
  · rintro s ⟨q, hq, q', hq', hlt, hseg, rfl⟩
    have hq₀ : 0 ≤ q.1 := hq.1.1
    have hx : q.1 < min q'.1 (⌊q.1⌋₊ + 1) := lt_min hlt <| Nat.lt_floor_add_one q.1
    have hx' : min q'.1 (⌊q.1⌋₊ + 1) ∈ Icc (⌊q.1⌋₊ : ℝ) (⌊q.1⌋₊ + 1) :=
      ⟨(Nat.floor_le hq₀).trans hx.le, min_le_right _ _⟩
    have hz : (min q'.1 (⌊q.1⌋₊ + 1), _) ∈ polygonGraph h :=
      hseg <| mk_mem_segment hlt ⟨hx.le, min_le_left _ _⟩
    have hce : ⌈min q'.1 (⌊q.1⌋₊ + 1)⌉₊ = ⌊q.1⌋₊ + 1 :=
      (Nat.ceil_eq_iff ⌊q.1⌋₊.succ_ne_zero).mpr
        ⟨(Nat.floor_le hq₀).trans_lt hx, hx'.2.trans_eq (Nat.cast_add_one _).symm⟩
    have hd : 0 < q'.1 - q.1 := sub_pos.mpr hlt
    have h₁ : q.2 = _ := hq.2.trans <|
      linearInterpolate_of_mem_Icc _ ⟨Nat.floor_le hq₀, (Nat.lt_floor_add_one q.1).le⟩
    have h₂ : q.2 + _ = _ := hz.2.trans <| linearInterpolate_of_mem_Icc _ hx'
    refine ⟨⌊q.1⌋₊, ⟨hq.1.2.1, hce ▸ hz.1.2.2⟩, ?_⟩
    rw [unitSlope_def, eq_div_iff hd.ne']
    refine mul_right_cancel₀ (sub_pos.mpr hx).ne' ?_
    field_simp at h₂
    linear_combination (q'.1 - q.1) * h₁ - h₂
  · rintro _ ⟨n, ⟨hn, hn'⟩, rfl⟩
    have hlt : (n : ℝ) < (n + 1 : ℕ) := Nat.cast_lt.mpr n.lt_succ_self
    refine ⟨_, natCast_mem_polygonGraph.mpr (WithTop.coe_untop₀_of_ne_top hn).symm, _,
      natCast_mem_polygonGraph.mpr (WithTop.coe_untop₀_of_ne_top hn').symm, hlt, ?_, ?_⟩
    · rintro z ⟨s, t, hs, ht, hst, rfl⟩
      have hz : s • ((n : ℝ), (h n).untop₀) + t • (((n + 1 : ℕ) : ℝ), (h (n + 1)).untop₀) =
          ((n : ℝ) + t, (h n).untop₀ + t * ((h (n + 1)).untop₀ - (h n).untop₀)) := by
        rw [eq_sub_of_add_eq hst]
        simp only [Prod.smul_mk, Prod.mk_add_mk, Nat.cast_add_one]
        exact Prod.ext (by ring1) (by ring1)
      have hmem : (n : ℝ) + t ∈ Icc (n : ℝ) (n + 1) := by
        constructor <;> linarith
      rw [hz]
      refine ⟨mem_interpolationDomain_of_mem_Icc hn hn' hmem, ?_⟩
      rw [linearInterpolate_of_mem_Icc _ hmem, add_sub_cancel_left]
    · rw [unitSlope_def, Nat.cast_add_one, add_sub_cancel_left, div_one]

end TauCeti
