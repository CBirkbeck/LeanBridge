import LeanBridge.ForMathlib.Analysis.Convex.LowerConvexHull

/-!
# The segments of a convex polygon

The segments of a polygonal line `P` of the plane are its maximal straight pieces: the segments
`[q, q']` with `q.1 < q'.1` contained in `P` and in no larger such segment contained in `P`
(`polygonEdges`). For the polygon of a convex height sequence `h` with finitely many finite heights
(`TauCeti.polygonGraph h`), each slope `s` of a unit edge gives one segment, from the first index
`l` of the unit edges of slope `s` to the last one plus one, `u` (`TauCeti.edgeOfSlope`), and these
are all the segments. So the segments of the polygon correspond to its distinct slopes, and the
number of its segments with slope in a set `T` is the number of slopes of its unit edges in `T`.
The reflection of the plane through the vertical axis maps the segments of a set to the segments
of its reflection, and negates their slopes.

## Main definitions

* `polygonEdges`: the segments of a subset of the plane.
* `polygonEdgesWithSlope`: its segments whose slope lies in a given set.
* `TauCeti.edgeOfSlope`: the segment of slope `s` of the polygon of a height sequence.

## Main results

* `mem_polygonEdges_image_reflectVertical`: the segments of the reflection of a set are the
  reflections of its segments.
* `polygonEdgesWithSlope_image_reflectVertical`: the reflection negates their slopes.
* `TauCeti.mem_polygonEdges_polygonGraph_iff`: the segments of the polygon of a convex height
  sequence are the segments of the slopes of its unit edges.
* `TauCeti.polygonEdgesWithSlope_polygonGraph`: its segments with slope in `T` are the segments of
  the slopes in `T` of its unit edges.
* `TauCeti.ncard_polygonEdgesWithSlope_polygonGraph`: the number of segments of the polygon of a
  convex height sequence with slope in `T` is the number of slopes of its unit edges in `T`.
-/

open Set

/-- The **segments** of a subset `P` of the plane, its maximal straight pieces: the segments
`[q, q']` with `q.1 < q'.1` that are contained in `P` and in no other such segment contained in
`P`. For a polygonal line, the graph of a piecewise affine function, these are its segments. -/
def polygonEdges (P : Set (ℝ × ℝ)) : Set (Set (ℝ × ℝ)) :=
  {σ | (∃ q q' : ℝ × ℝ, q.1 < q'.1 ∧ segment ℝ q q' = σ) ∧ σ ⊆ P ∧
    ∀ q q' : ℝ × ℝ, q.1 < q'.1 → segment ℝ q q' ⊆ P → σ ⊆ segment ℝ q q' → segment ℝ q q' = σ}

/-- The **segments of `P` with slope in `T`**: the segments `[q, q']`, `q.1 < q'.1`, of `P` whose
slope `(q'.2 - q.2) / (q'.1 - q.1)` lies in `T`. -/
def polygonEdgesWithSlope (P : Set (ℝ × ℝ)) (T : Set ℝ) : Set (Set (ℝ × ℝ)) :=
  {σ ∈ polygonEdges P | ∃ q q' : ℝ × ℝ, q.1 < q'.1 ∧ segment ℝ q q' = σ ∧
    (q'.2 - q.2) / (q'.1 - q.1) ∈ T}

variable {P σ : Set (ℝ × ℝ)} {T : Set ℝ} {q q' : ℝ × ℝ} {x x₁ x₂ a m : ℝ}

lemma mem_segment_mk_iff (h : x₁ < x₂) {z : ℝ × ℝ} :
    z ∈ segment ℝ (x₁, a) (x₂, a + (x₂ - x₁) * m) ↔ z.1 ∈ Icc x₁ x₂ ∧ z.2 = a + (z.1 - x₁) * m := by
  refine ⟨?_, fun ⟨hz, hz'⟩ ↦ ?_⟩
  · rintro ⟨θ, η, hθ, hη, hθη, rfl⟩
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [eq_sub_of_add_eq hθη]
    refine ⟨⟨by nlinarith, by nlinarith⟩, by ring1⟩
  · have hmem : (z.1, a + (z.1 - x₁) / (x₂ - x₁) * (a + (x₂ - x₁) * m - a)) ∈
        segment ℝ (x₁, a) (x₂, a + (x₂ - x₁) * m) :=
      mk_mem_segment h hz
    have hy : a + (z.1 - x₁) / (x₂ - x₁) * (a + (x₂ - x₁) * m - a) = z.2 := by
      rw [hz']
      field_simp
      ring1
    rwa [hy, Prod.mk.eta] at hmem

lemma reflectVertical_involutive : Function.Involutive reflectVertical :=
  reflectVertical_reflectVertical

variable (q q') in
lemma image_reflectVertical_segment :
    reflectVertical '' segment ℝ q q' = segment ℝ (reflectVertical q') (reflectVertical q) := by
  rw [segment_symm ℝ (reflectVertical q')]
  exact image_segment ℝ reflectVertical.toAffineMap q q'

lemma image_reflectVertical_subset_iff {A B : Set (ℝ × ℝ)} :
    reflectVertical '' A ⊆ B ↔ A ⊆ reflectVertical '' B := by
  refine ⟨fun h x hx ↦ mem_image_reflectVertical.mpr (h ⟨x, hx, rfl⟩), ?_⟩
  rintro h _ ⟨y, hy, rfl⟩
  exact mem_image_reflectVertical.mp (h hy)

lemma image_reflectVertical_mem_polygonEdges (hσ : σ ∈ polygonEdges (reflectVertical '' P)) :
    reflectVertical '' σ ∈ polygonEdges P := by
  rcases hσ with ⟨⟨q, q', hq, rfl⟩, hsub, hmax⟩
  refine ⟨⟨reflectVertical q', reflectVertical q, neg_lt_neg hq,
    (image_reflectVertical_segment q q').symm⟩, image_reflectVertical_subset_iff.mpr hsub,
    fun r r' hr hrP hle ↦ ?_⟩
  have himage : reflectVertical '' segment ℝ r r' ⊆ reflectVertical '' P := image_mono hrP
  rw [image_reflectVertical_segment] at himage
  have h : segment ℝ (reflectVertical r') (reflectVertical r) = segment ℝ q q' :=
    hmax (reflectVertical r') (reflectVertical r) (neg_lt_neg hr) himage <| by
    rw [← image_reflectVertical_segment]
    exact image_reflectVertical_subset_iff.mp hle
  rw [← h, ← image_reflectVertical_segment, image_reflectVertical_image_reflectVertical]

/-- **The segments of the reflection of a set are the reflections of its segments**, for the
reflection through the vertical axis. -/
lemma mem_polygonEdges_image_reflectVertical :
    σ ∈ polygonEdges (reflectVertical '' P) ↔ reflectVertical '' σ ∈ polygonEdges P := by
  refine ⟨image_reflectVertical_mem_polygonEdges, fun h ↦ ?_⟩
  rw [← image_reflectVertical_image_reflectVertical P] at h
  simpa only [image_reflectVertical_image_reflectVertical] using
    image_reflectVertical_mem_polygonEdges h

lemma image_reflectVertical_mem_polygonEdgesWithSlope
    (hσ : σ ∈ polygonEdgesWithSlope (reflectVertical '' P) T) :
    reflectVertical '' σ ∈ polygonEdgesWithSlope P (Neg.neg '' T) := by
  rcases hσ with ⟨hσ, q, q', hq, rfl, hT⟩
  refine ⟨image_reflectVertical_mem_polygonEdges hσ, reflectVertical q', reflectVertical q,
    neg_lt_neg hq, (image_reflectVertical_segment q q').symm, _, hT, ?_⟩
  rw [reflectVertical_apply, reflectVertical_apply]
  ring1

variable (P T) in
/-- **The reflection through the vertical axis negates the slopes of the segments**: the
segments of slope in `T` of the reflection of `P` are the reflections of the segments of `P` of
slope in `-T`. -/
lemma polygonEdgesWithSlope_image_reflectVertical : polygonEdgesWithSlope (reflectVertical '' P) T =
    image reflectVertical '' polygonEdgesWithSlope P (Neg.neg '' T) := by
  ext σ
  refine ⟨fun h ↦ ⟨_, image_reflectVertical_mem_polygonEdgesWithSlope h,
    image_reflectVertical_image_reflectVertical σ⟩, ?_⟩
  rintro ⟨τ, hτ, rfl⟩
  rw [← image_reflectVertical_image_reflectVertical P] at hτ
  have h : reflectVertical '' τ ∈
      polygonEdgesWithSlope (reflectVertical '' P) (Neg.neg '' (Neg.neg '' T)) :=
    image_reflectVertical_mem_polygonEdgesWithSlope hτ
  rwa [image_image, image_congr fun x _ ↦ neg_neg x, image_id'] at h

variable (P T) in
lemma ncard_polygonEdgesWithSlope_image_reflectVertical :
    (polygonEdgesWithSlope (reflectVertical '' P) T).ncard =
      (polygonEdgesWithSlope P (Neg.neg '' T)).ncard := by
  rw [polygonEdgesWithSlope_image_reflectVertical]
  exact ncard_image_of_injective _ (image_injective.mpr reflectVertical_involutive.injective)

namespace TauCeti

variable {h : ℕ → WithTop ℝ} {s t : ℝ} {n : ℕ}

variable (h s) in
/-- The indices `n` of the unit edges `[n, n + 1]` of slope `s` of a height sequence `h`. -/
def slopeIndices : Set ℕ :=
  {n | n ∈ finiteEdges h ∧ unitSlope h n = s}

variable (h s) in
/-- The **segment of slope `s`** of the polygon of a height sequence `h`: the segment of slope `s`
from `(l, h_l)` over `[l, u]`, where `l` is the first index of the unit edges of slope `s` and
`u - 1` the last one. -/
noncomputable def edgeOfSlope : Set (ℝ × ℝ) :=
  segment ℝ ((sInf (slopeIndices h s) : ℕ), (h (sInf (slopeIndices h s))).untop₀)
    ((sSup (slopeIndices h s) + 1 : ℕ), (h (sInf (slopeIndices h s))).untop₀ +
      (((sSup (slopeIndices h s) + 1 : ℕ) : ℝ) - (sInf (slopeIndices h s) : ℕ)) * s)

variable (s) in
lemma bddAbove_slopeIndices (hfin : {n | h n ≠ ⊤}.Finite) : BddAbove (slopeIndices h s) :=
  (hfin.subset fun _ (hn : _ ∈ slopeIndices h s) ↦ hn.1.1).bddAbove

lemma slopeIndices_nonempty (hs : s ∈ unitSlope h '' finiteEdges h) :
    (slopeIndices h s).Nonempty := by
  rcases hs with ⟨n, hn, rfl⟩
  exact ⟨n, hn, rfl⟩

lemma sInf_mem_slopeIndices (hs : s ∈ unitSlope h '' finiteEdges h) :
    sInf (slopeIndices h s) ∈ slopeIndices h s :=
  Nat.sInf_mem <| slopeIndices_nonempty hs

lemma sSup_mem_slopeIndices (hfin : {n | h n ≠ ⊤}.Finite) (hs : s ∈ unitSlope h '' finiteEdges h) :
    sSup (slopeIndices h s) ∈ slopeIndices h s :=
  Nat.sSup_mem (slopeIndices_nonempty hs) (bddAbove_slopeIndices s hfin)

lemma sInf_le_sSup_slopeIndices (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h) : sInf (slopeIndices h s) ≤ sSup (slopeIndices h s) :=
  Nat.sInf_le <| sSup_mem_slopeIndices hfin hs

lemma mem_slopeIndices_of_le_of_le (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h) (h₁ : sInf (slopeIndices h s) ≤ n)
    (h₂ : n ≤ sSup (slopeIndices h s)) : n ∈ slopeIndices h s := by
  have hl : sInf (slopeIndices h s) ∈ slopeIndices h s := sInf_mem_slopeIndices hs
  have hu : sSup (slopeIndices h s) ∈ slopeIndices h s := sSup_mem_slopeIndices hfin hs
  have hn : n ∈ finiteEdges h := (ordConnected_finiteEdges hh.ordConnected).out hl.1 hu.1 ⟨h₁, h₂⟩
  refine ⟨hn, le_antisymm ?_ ?_⟩
  · exact (hh.monotoneOn hn hu.1 h₂).trans_eq hu.2
  · exact hl.2.symm.trans_le (hh.monotoneOn hl.1 hn h₁)

lemma untop₀_eq_add_mul (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h) (h₁ : sInf (slopeIndices h s) ≤ n)
    (h₂ : n ≤ sSup (slopeIndices h s) + 1) : (h n).untop₀ =
      (h (sInf (slopeIndices h s))).untop₀ + ((n : ℝ) - (sInf (slopeIndices h s) : ℕ)) * s := by
  have hl : sInf (slopeIndices h s) ∈ slopeIndices h s := sInf_mem_slopeIndices hs
  have hu : sSup (slopeIndices h s) ∈ slopeIndices h s := sSup_mem_slopeIndices hfin hs
  have hn : h n ≠ ⊤ := hh.ordConnected.out hl.1.1 hu.1.2 ⟨h₁, h₂⟩
  have hsum : ∑ i ∈ Finset.Ico (sInf (slopeIndices h s)) n, unitSlope h i =
      ∑ _i ∈ Finset.Ico (sInf (slopeIndices h s)) n, s :=
    Finset.sum_congr rfl fun i hi ↦ (mem_slopeIndices_of_le_of_le hh hfin hs
      (Finset.mem_Ico.mp hi).1 (Nat.lt_succ_iff.mp <| (Finset.mem_Ico.mp hi).2.trans_le h₂)).2
  rw [eq_coe_add_sum_unitSlope hn h₁, WithTop.untop₀_coe, hsum, Finset.sum_const, Nat.card_Ico,
    nsmul_eq_mul, Nat.cast_sub h₁]

lemma natCast_sInf_lt_natCast_sSup_add_one (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h) :
    ((sInf (slopeIndices h s) : ℕ) : ℝ) < ((sSup (slopeIndices h s) + 1 : ℕ) : ℝ) :=
  Nat.cast_lt.mpr <| Nat.lt_succ_of_le <| sInf_le_sSup_slopeIndices hfin hs

lemma mk_mem_polygonGraph (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h)
    (hx : x ∈ Icc ((sInf (slopeIndices h s) : ℕ) : ℝ) ((sSup (slopeIndices h s) + 1 : ℕ) : ℝ)) :
    (x, (h (sInf (slopeIndices h s))).untop₀ + (x - (sInf (slopeIndices h s) : ℕ)) * s) ∈
      polygonGraph h := by
  have hx₀ : 0 ≤ x := (Nat.cast_nonneg _).trans hx.1
  have hl : sInf (slopeIndices h s) ≤ min ⌊x⌋₊ (sSup (slopeIndices h s)) :=
    le_min (Nat.le_floor hx.1) (sInf_le_sSup_slopeIndices hfin hs)
  have hm : min ⌊x⌋₊ (sSup (slopeIndices h s)) ∈ slopeIndices h s :=
    mem_slopeIndices_of_le_of_le hh hfin hs hl (min_le_right _ _)
  have hxm : x ∈ Icc ((min ⌊x⌋₊ (sSup (slopeIndices h s)) : ℕ) : ℝ)
      ((min ⌊x⌋₊ (sSup (slopeIndices h s)) : ℕ) + 1) := by
    refine ⟨(Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le hx₀), ?_⟩
    rw [Nat.cast_min, ← min_add_add_right]
    refine le_min (Nat.lt_floor_add_one x).le ?_
    exact_mod_cast hx.2
  have hu : (h (min ⌊x⌋₊ (sSup (slopeIndices h s)))).untop₀ = (h (sInf (slopeIndices h s))).untop₀ +
      (((min ⌊x⌋₊ (sSup (slopeIndices h s)) : ℕ) : ℝ) - (sInf (slopeIndices h s) : ℕ)) * s :=
    untop₀_eq_add_mul hh hfin hs hl ((min_le_right _ _).trans (Nat.le_succ _))
  refine ⟨mem_interpolationDomain_of_mem_Icc hm.1.1 hm.1.2 hxm, ?_⟩
  rw [linearInterpolate_of_mem_Icc _ hxm, ← unitSlope_def, hm.2, hu]
  ring1

lemma edgeOfSlope_subset_polygonGraph (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h) : edgeOfSlope h s ⊆ polygonGraph h := by
  intro z hz
  rw [edgeOfSlope, mem_segment_mk_iff (natCast_sInf_lt_natCast_sSup_add_one hfin hs)] at hz
  simpa only [← hz.2] using mk_mem_polygonGraph hh hfin hs hz.1

lemma mk_mem_polygonGraph_of_segment_subset (hq : q.1 < q'.1)
    (hsub : segment ℝ q q' ⊆ polygonGraph h) (hx : x ∈ Icc q.1 q'.1) :
    (x, q.2 + (x - q.1) * ((q'.2 - q.2) / (q'.1 - q.1))) ∈ polygonGraph h := by
  have hmem : (x, q.2 + (x - q.1) / (q'.1 - q.1) * (q'.2 - q.2)) ∈ segment ℝ q q' :=
    mk_mem_segment hq hx
  have hy : q.2 + (x - q.1) / (q'.1 - q.1) * (q'.2 - q.2) =
      q.2 + (x - q.1) * ((q'.2 - q.2) / (q'.1 - q.1)) := by
    ring1
  rw [hy] at hmem
  exact hsub hmem

lemma unitSlope_eq_of_segment_subset (hq : q.1 < q'.1) (hsub : segment ℝ q q' ⊆ polygonGraph h)
    (hn₁ : (n : ℝ) < q'.1) (hn₂ : q.1 < n + 1) : unitSlope h n = (q'.2 - q.2) / (q'.1 - q.1) := by
  have hlt : max (n : ℝ) q.1 < min ((n : ℝ) + 1) q'.1 :=
    max_lt (lt_min (lt_add_one _) hn₁) (lt_min hn₂ hq)
  have h₁ : q.2 + (max (n : ℝ) q.1 - q.1) * ((q'.2 - q.2) / (q'.1 - q.1)) =
      linearInterpolate (fun i ↦ (h i).untop₀) (max (n : ℝ) q.1) :=
    (mk_mem_polygonGraph_of_segment_subset hq hsub
      ⟨le_max_right (n : ℝ) q.1, max_le hn₁.le hq.le⟩).2
  have h₂ : q.2 + (min ((n : ℝ) + 1) q'.1 - q.1) * ((q'.2 - q.2) / (q'.1 - q.1)) =
      linearInterpolate (fun i ↦ (h i).untop₀) (min ((n : ℝ) + 1) q'.1) :=
    (mk_mem_polygonGraph_of_segment_subset hq hsub
      ⟨le_min hn₂.le hq.le, min_le_right ((n : ℝ) + 1) q'.1⟩).2
  rw [linearInterpolate_of_mem_Icc _ ⟨le_max_left _ _, max_le (le_add_of_nonneg_right zero_le_one)
    hn₂.le⟩, ← unitSlope_def] at h₁
  rw [linearInterpolate_of_mem_Icc _ ⟨le_min (le_add_of_nonneg_right zero_le_one) hn₁.le,
    min_le_left _ _⟩, ← unitSlope_def] at h₂
  exact (mul_left_cancel₀ (sub_ne_zero.mpr hlt.ne') (by linear_combination h₂ - h₁)).symm

lemma floor_mem_finiteEdges (hh : IsConvexSeq h) (hq : q.1 < q'.1)
    (hsub : segment ℝ q q' ⊆ polygonGraph h) : ⌊q.1⌋₊ ∈ finiteEdges h := by
  have hq₁ : q.1 ∈ interpolationDomain h := (hsub (left_mem_segment ℝ q q')).1
  have hq₂ : q'.1 ∈ interpolationDomain h := (hsub (right_mem_segment ℝ q q')).1
  exact ⟨hq₁.2.1, hh.ordConnected.out hq₁.2.1 hq₂.2.2
    ⟨Nat.le_succ _, Nat.lt_ceil.mpr <| (Nat.floor_le hq₁.1).trans_lt hq⟩⟩

lemma unitSlope_floor_eq (hq : q.1 < q'.1) (hsub : segment ℝ q q' ⊆ polygonGraph h) :
    unitSlope h ⌊q.1⌋₊ = (q'.2 - q.2) / (q'.1 - q.1) := by
  have hq₁ : q.1 ∈ interpolationDomain h := (hsub (left_mem_segment ℝ q q')).1
  exact unitSlope_eq_of_segment_subset hq hsub ((Nat.floor_le hq₁.1).trans_lt hq)
    (Nat.lt_floor_add_one q.1)

lemma slope_mem_image_unitSlope (hh : IsConvexSeq h) (hq : q.1 < q'.1)
    (hsub : segment ℝ q q' ⊆ polygonGraph h) :
    (q'.2 - q.2) / (q'.1 - q.1) ∈ unitSlope h '' finiteEdges h :=
  ⟨⌊q.1⌋₊, floor_mem_finiteEdges hh hq hsub, unitSlope_floor_eq hq hsub⟩

lemma segment_subset_edgeOfSlope (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite)
    (hq : q.1 < q'.1) (hsub : segment ℝ q q' ⊆ polygonGraph h) :
    segment ℝ q q' ⊆ edgeOfSlope h ((q'.2 - q.2) / (q'.1 - q.1)) := by
  have hs : (q'.2 - q.2) / (q'.1 - q.1) ∈ unitSlope h '' finiteEdges h :=
    slope_mem_image_unitSlope hh hq hsub
  have hq₁ : q.1 ∈ interpolationDomain h := (hsub (left_mem_segment ℝ q q')).1
  have hq₂ : q'.1 ∈ interpolationDomain h := (hsub (right_mem_segment ℝ q q')).1
  have hfl : ⌊q.1⌋₊ ∈ slopeIndices h ((q'.2 - q.2) / (q'.1 - q.1)) :=
    ⟨floor_mem_finiteEdges hh hq hsub, unitSlope_floor_eq hq hsub⟩
  have hc : 1 ≤ ⌈q'.1⌉₊ := Nat.one_le_ceil_iff.mpr (hq₁.1.trans_lt hq)
  have hlt : ⌊q.1⌋₊ < ⌈q'.1⌉₊ := Nat.lt_ceil.mpr ((Nat.floor_le hq₁.1).trans_lt hq)
  have hn' : ⌈q'.1⌉₊ - 1 ∈ finiteEdges h :=
    ⟨hh.ordConnected.out hfl.1.1 hq₂.2.2 ⟨by omega, by omega⟩, by
      rw [Nat.sub_add_cancel hc]
      exact hq₂.2.2⟩
  have hce : ⌈q'.1⌉₊ - 1 ∈ slopeIndices h ((q'.2 - q.2) / (q'.1 - q.1)) := by
    refine ⟨hn', unitSlope_eq_of_segment_subset hq hsub ?_ ?_⟩
    · rw [Nat.cast_sub hc, Nat.cast_one, sub_lt_iff_lt_add]
      exact Nat.ceil_lt_add_one (hq₁.1.trans hq.le)
    · rw [Nat.cast_sub hc, Nat.cast_one, sub_add_cancel]
      exact hq.trans_le (Nat.le_ceil _)
  have hl : ((sInf (slopeIndices h ((q'.2 - q.2) / (q'.1 - q.1))) : ℕ) : ℝ) ≤ q.1 :=
    (Nat.cast_le.mpr (Nat.sInf_le hfl)).trans (Nat.floor_le hq₁.1)
  have hu : q'.1 ≤ ((sSup (slopeIndices h ((q'.2 - q.2) / (q'.1 - q.1))) + 1 : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans <| Nat.cast_le.mpr <| (Nat.sub_add_cancel hc).symm.le.trans <|
      Nat.succ_le_succ <| le_csSup (bddAbove_slopeIndices _ hfin) hce
  have hmem (z : ℝ × ℝ) (hz : z ∈ segment ℝ q q') (hz₁ : z.1 ∈ Icc q.1 q'.1) :
      z ∈ edgeOfSlope h ((q'.2 - q.2) / (q'.1 - q.1)) := by
    rw [edgeOfSlope, mem_segment_mk_iff (natCast_sInf_lt_natCast_sSup_add_one hfin hs)]
    have hzI : z.1 ∈ Icc ((sInf (slopeIndices h ((q'.2 - q.2) / (q'.1 - q.1))) : ℕ) : ℝ)
        ((sSup (slopeIndices h ((q'.2 - q.2) / (q'.1 - q.1))) + 1 : ℕ) : ℝ) :=
      ⟨hl.trans hz₁.1, hz₁.2.trans hu⟩
    exact ⟨hzI, (hsub hz).2.trans (mk_mem_polygonGraph hh hfin hs hzI).2.symm⟩
  exact (convex_segment _ _).segment_subset (hmem q (left_mem_segment ℝ q q') ⟨le_rfl, hq.le⟩)
    (hmem q' (right_mem_segment ℝ q q') ⟨hq.le, le_rfl⟩)

lemma eq_of_edgeOfSlope_subset (hfin : {n | h n ≠ ⊤}.Finite) (hs : s ∈ unitSlope h '' finiteEdges h)
    (ht : t ∈ unitSlope h '' finiteEdges h) (hst : edgeOfSlope h s ⊆ edgeOfSlope h t) : s = t := by
  have hA : (((sInf (slopeIndices h s) : ℕ) : ℝ), (h (sInf (slopeIndices h s))).untop₀) ∈
      edgeOfSlope h t :=
    hst (left_mem_segment ℝ _ _)
  have hB : (((sSup (slopeIndices h s) + 1 : ℕ) : ℝ), (h (sInf (slopeIndices h s))).untop₀ +
      (((sSup (slopeIndices h s) + 1 : ℕ) : ℝ) - (sInf (slopeIndices h s) : ℕ)) * s) ∈
        edgeOfSlope h t :=
    hst (right_mem_segment ℝ _ _)
  rw [edgeOfSlope, mem_segment_mk_iff (natCast_sInf_lt_natCast_sSup_add_one hfin ht)] at hA hB
  exact mul_left_cancel₀ (sub_ne_zero.mpr (natCast_sInf_lt_natCast_sSup_add_one hfin hs).ne')
    (by linear_combination hB.2 - hA.2)

lemma slope_eq_of_segment_eq_edgeOfSlope (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h) (hq : q.1 < q'.1)
    (heq : segment ℝ q q' = edgeOfSlope h s) : (q'.2 - q.2) / (q'.1 - q.1) = s := by
  have hA : q ∈ edgeOfSlope h s := heq ▸ left_mem_segment ℝ q q'
  have hB : q' ∈ edgeOfSlope h s := heq ▸ right_mem_segment ℝ q q'
  rw [edgeOfSlope, mem_segment_mk_iff (natCast_sInf_lt_natCast_sSup_add_one hfin hs)] at hA hB
  rw [div_eq_iff (sub_ne_zero.mpr hq.ne')]
  linear_combination hB.2 - hA.2

/-- **The segments of the polygon of a convex height sequence**: for a convex height sequence `h`
with finitely many finite heights, the segments of its polygon are the segments `edgeOfSlope h s`
for the slopes `s` of its unit edges. -/
lemma mem_polygonEdges_polygonGraph_iff (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite) :
    σ ∈ polygonEdges (polygonGraph h) ↔ ∃ s ∈ unitSlope h '' finiteEdges h,
      edgeOfSlope h s = σ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨q, q', hq, rfl⟩, hsub, hmax⟩
    have hs : (q'.2 - q.2) / (q'.1 - q.1) ∈ unitSlope h '' finiteEdges h :=
      slope_mem_image_unitSlope hh hq hsub
    exact ⟨_, hs, hmax _ _ (natCast_sInf_lt_natCast_sSup_add_one hfin hs)
      (edgeOfSlope_subset_polygonGraph hh hfin hs) (segment_subset_edgeOfSlope hh hfin hq hsub)⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨_, _, ?_, rfl⟩, edgeOfSlope_subset_polygonGraph hh hfin hs, fun r r' hr hrP hle ↦ ?_⟩
    · exact natCast_sInf_lt_natCast_sSup_add_one hfin hs
    have hsub : segment ℝ r r' ⊆ edgeOfSlope h ((r'.2 - r.2) / (r'.1 - r.1)) :=
      segment_subset_edgeOfSlope hh hfin hr hrP
    rw [← eq_of_edgeOfSlope_subset hfin hs (slope_mem_image_unitSlope hh hr hrP)
      (hle.trans hsub)] at hsub
    exact hsub.antisymm hle

variable (T) in
/-- **The segments of the polygon of a convex height sequence with slope in `T`**: they are the
segments `edgeOfSlope h s` for the slopes `s ∈ T` of its unit edges. -/
lemma polygonEdgesWithSlope_polygonGraph (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite) :
    polygonEdgesWithSlope (polygonGraph h) T =
      edgeOfSlope h '' (unitSlope h '' finiteEdges h ∩ T) := by
  ext τ
  refine ⟨?_, ?_⟩
  · rintro ⟨hτ, q, q', hq, rfl, hT⟩
    rcases (mem_polygonEdges_polygonGraph_iff hh hfin).mp hτ with ⟨s, hs, heq⟩
    exact ⟨s, ⟨hs, slope_eq_of_segment_eq_edgeOfSlope hfin hs hq heq.symm ▸ hT⟩, heq⟩
  · rintro ⟨s, ⟨hs, hT⟩, rfl⟩
    refine ⟨(mem_polygonEdges_polygonGraph_iff hh hfin).mpr ⟨s, hs, rfl⟩, _, _, ?_, rfl, ?_⟩
    · exact natCast_sInf_lt_natCast_sSup_add_one hfin hs
    · exact (slope_eq_of_segment_eq_edgeOfSlope hfin hs
        (natCast_sInf_lt_natCast_sSup_add_one hfin hs) rfl).symm ▸ hT

variable (T) in
/-- **The number of segments of the polygon of a convex height sequence with slope in `T`**: for a
convex height sequence `h` with finitely many finite heights, it is the number of slopes in `T` of
the unit edges of `h`, the segments of distinct slopes being distinct. -/
lemma ncard_polygonEdgesWithSlope_polygonGraph (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite) :
    (polygonEdgesWithSlope (polygonGraph h) T).ncard =
      (unitSlope h '' finiteEdges h ∩ T).ncard := by
  rw [polygonEdgesWithSlope_polygonGraph T hh hfin]
  exact InjOn.ncard_image fun s hs t ht hst ↦ eq_of_edgeOfSlope_subset hfin hs.1 ht.1 hst.subset

end TauCeti
