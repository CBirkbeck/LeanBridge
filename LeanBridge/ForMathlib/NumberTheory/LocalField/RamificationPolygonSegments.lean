import LeanBridge.ForMathlib.Analysis.Convex.PolygonEdges
import LeanBridge.ForMathlib.NumberTheory.LocalField.CompatibleAdmissible
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolynomial

/-!
# The segments of the ramification polygon of a Herbrand invariant

Let `I = (r_1, …, r_w)_ε^f` be a Herbrand invariant at a prime `p`, with `e = ε p ^ w` and means
`m_k`. Its ramification polygon (LMFDB `lf.ramification_polygon`,
`IsNonarchimedeanLocalField.HerbrandInvariant.reflectedPolygon`) is the polygonal line through the
points `(-e, 0)`, `(-p ^ w, 0)` and `(-p ^ (w - k), e m_k)`. This file lists its segments, the
maximal straight pieces `polygonEdges`: for `ε > 1` the horizontal segment from `(-e, 0)` to
`(-p ^ w, 0)`, and for each distinct ram `b`, of multiplicity `d` and with `c` rams smaller than
it, the segment of slope `b` from `(-p ^ (w - c), e m_c)` to `(-p ^ (w - c - d), e m_{c + d})`. So
the segments correspond to their slopes, which are `0`, when `ε > 1`, and the distinct rams, and
the segment of slope `u` ends at the point `(-p ^ (w - k), e m_k)` for the number `k` of rams at
most `u`.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.edgeStart` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.edgeEnd`: the two ends of the segment of slope `u`
  of the ramification polygon.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.slopeIndices_ramificationPolygon_neg_ram` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.slopeIndices_ramificationPolygon_zero`: the unit
  edges of the polygon of a given slope.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mem_image_unitSlope_ramificationPolygon_iff`: the
  slopes of the polygon are `0`, for `ε > 1`, and the negatives of the rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mem_segmentSlopes_reflectedPolygon_iff` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.ratCast_mem_segmentSlopes_reflectedPolygon_iff`
  (LMFDB `lf.ramification_polygon`): the slopes of the segments of the ramification polygon are
  `0`, for `ε > 1`, and the rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mem_polygonEdges_reflectedPolygon_iff` (LMFDB
  `lf.ramification_polygon`): the segments of the ramification polygon.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mem_polygonEdges_reflectedPolygon_iff_exists`: the
  segments of the ramification polygon are the segments from `edgeStart u` to `edgeEnd u`, for its
  slopes `u`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.edgeEnd_snd_sub_div`: the segment from
  `edgeStart u` to `edgeEnd u` has the slope `u`.
-/

open TauCeti

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p) {b u : ℚ} {s : ℝ} {σ : Set (ℝ × ℝ)}

variable (u) in
/-- The **left end of the segment of slope `u`** of the ramification polygon of a Herbrand
invariant `I = (r_1, …, r_w)_ε^f` (LMFDB `lf.ramification_polygon`): the point `(-e, 0)` for
`u = 0`, and otherwise `(-p ^ (w - c), e m_c)` for the number `c` of rams smaller than `u`. -/
noncomputable def edgeStart : ℝ × ℝ :=
  (-((if u = 0 then I.ramificationIndex else p ^ (I.w - I.ramCountLT u) : ℕ) : ℝ),
    ((I.ramificationIndex * I.mean (I.ramCountLT u) : ℚ) : ℝ))

variable (u) in
/-- The **right end of the segment of slope `u`** of the ramification polygon of a Herbrand
invariant `I = (r_1, …, r_w)_ε^f` (LMFDB `lf.ramification_polygon`): the point
`(-p ^ (w - k), e m_k)` for the number `k` of rams at most `u`, the sum of the number of rams
smaller than `u` and of the multiplicity of `u`. -/
noncomputable def edgeEnd : ℝ × ℝ :=
  (-((p ^ (I.w - (I.ramCountLT u + I.ramMultiplicity u)) : ℕ) : ℝ),
    ((I.ramificationIndex * I.mean (I.ramCountLT u + I.ramMultiplicity u) : ℚ) : ℝ))

lemma edgeStart_zero : I.edgeStart 0 = (-(I.ramificationIndex : ℝ), 0) := by
  rw [edgeStart, ite_eq_left rfl, I.ramCountLT_zero, I.mean_zero, mul_zero, Rat.cast_zero]

lemma edgeEnd_zero : I.edgeEnd 0 = (-((p ^ I.w : ℕ) : ℝ), 0) := by
  rw [edgeEnd, I.ramCountLT_zero, I.ramMultiplicity_zero, Nat.sub_zero, I.mean_zero, mul_zero,
    Rat.cast_zero]

lemma edgeStart_of_mem (hb : b ∈ (Finset.Icc 1 I.w).image I.ram) : I.edgeStart b =
    (-((p ^ (I.w - I.ramCountLT b) : ℕ) : ℝ),
      ((I.ramificationIndex * I.mean (I.ramCountLT b) : ℚ) : ℝ)) := by
  have hb₀ : b ≠ 0 := (I.pos_of_mem_image_ram hb).ne'
  rw [edgeStart, ite_eq_right hb₀]

lemma finite_setOf_ramificationPolygon_ne_top : {n | I.ramificationPolygon n ≠ ⊤}.Finite :=
  (Set.finite_Icc 1 I.ramificationIndex).subset fun _ hn ↦ I.ramificationPolygon_ne_top_iff.mp hn

private lemma sSup_Ico_add_one {a c : ℕ} (h : a < c) : sSup (Set.Ico a c) + 1 = c := by
  have h₁ : IsGreatest (Set.Ico a c) (c - 1) :=
    ⟨⟨by omega, by omega⟩, fun n hn ↦ Nat.le_sub_one_of_lt hn.2⟩
  rw [h₁.csSup_eq]
  omega

variable [Fact p.Prime]

/-- **The unit edges of the slope of a ram**: for a ram `b` of `I`, of multiplicity `d` and with `c`
rams smaller than it, the unit edges `[n, n + 1]` of slope `-b` of the ramification polygon of `I`
are those with `p ^ (w - c - d) ≤ n < p ^ (w - c)`. -/
lemma slopeIndices_ramificationPolygon_neg_ram (hb : b ∈ (Finset.Icc 1 I.w).image I.ram) :
    slopeIndices I.ramificationPolygon (-(b : ℝ)) = Set.Ico
      (p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b))) (p ^ (I.w - I.ramCountLT b)) := by
  have hp : p.Prime := Fact.out
  have hb₀ : 0 < b := I.pos_of_mem_image_ram hb
  have hcd : I.ramCountLT b + I.ramMultiplicity b ≤ I.w := I.ramCountLT_add_ramMultiplicity_le b
  have hd : 0 < I.ramMultiplicity b := I.ramMultiplicity_pos hb
  ext n
  rw [slopeIndices, Set.mem_ofPred_eq, finiteEdges_ramificationPolygon, Set.mem_Ico, Set.mem_Ico]
  constructor
  · rintro ⟨⟨hn₁, hn₂⟩, hs⟩
    have hn₀ : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn₁
    rw [I.unitSlope_ramificationPolygon_eq_neg_ram hn₀ hn₂, neg_inj, Rat.cast_inj] at hs
    have hj₀ : I.w - Nat.log p n ≠ 0 := fun h ↦ hb₀.ne' <| by rw [← hs, h, I.ram_zero]
    have h₁ : ¬I.w - Nat.log p n ≤ I.ramCountLT b :=
      (I.ram_lt_iff_le_ramCountLT (Nat.one_le_iff_ne_zero.mpr hj₀) (Nat.sub_le _ _)).not.mp
        hs.not_lt
    have h₂ : I.w - Nat.log p n ≤ I.ramCountLT b + I.ramMultiplicity b :=
      (I.ram_le_iff_le_ramCountLT_add_ramMultiplicity (Nat.one_le_iff_ne_zero.mpr hj₀)
        (Nat.sub_le _ _)).mp hs.le
    exact ⟨(Nat.pow_le_pow_right hp.pos (by omega)).trans (Nat.pow_log_le_self p hn₀),
      (Nat.lt_pow_succ_log_self hp.one_lt n).trans_le (Nat.pow_le_pow_right hp.pos (by omega))⟩
  · rintro ⟨hn₁, hn₂⟩
    have hn₀ : n ≠ 0 := (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero) |>.trans_le hn₁).ne'
    have hne : n < I.ramificationIndex := hn₂.trans_le <|
      (Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)).trans (Nat.le_mul_of_pos_left _ I.ε_pos)
    have hl₁ : I.w - (I.ramCountLT b + I.ramMultiplicity b) ≤ Nat.log p n :=
      Nat.le_log_of_pow_le hp.one_lt hn₁
    have hl₂ : Nat.log p n < I.w - I.ramCountLT b := Nat.log_lt_of_lt_pow hn₀ hn₂
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hn₀, hne⟩, ?_⟩
    rw [I.unitSlope_ramificationPolygon_eq_neg_ram hn₀ hne,
      I.ram_eq_of_ramCountLT_lt (b := b) (by omega) (by omega)]

/-- **The unit edges of slope `0`**: the unit edges `[n, n + 1]` of slope `0` of the ramification
polygon of `I` are those with `p ^ w ≤ n < e`. -/
lemma slopeIndices_ramificationPolygon_zero :
    slopeIndices I.ramificationPolygon 0 = Set.Ico (p ^ I.w) I.ramificationIndex := by
  have hp : p.Prime := Fact.out
  ext n
  rw [slopeIndices, Set.mem_ofPred_eq, finiteEdges_ramificationPolygon, Set.mem_Ico, Set.mem_Ico]
  constructor
  · rintro ⟨⟨hn₁, hn₂⟩, hs⟩
    exact ⟨(I.unitSlope_ramificationPolygon_eq_zero_iff (Nat.one_le_iff_ne_zero.mp hn₁) hn₂).mp hs,
      hn₂⟩
  · rintro ⟨hn₁, hn₂⟩
    exact ⟨⟨(Nat.one_le_pow _ _ hp.pos).trans hn₁, hn₂⟩,
      I.unitSlope_ramificationPolygon_of_pow_le hn₁ hn₂⟩

lemma edgeOfSlope_ramificationPolygon_neg_ram (hb : b ∈ (Finset.Icc 1 I.w).image I.ram) :
    edgeOfSlope I.ramificationPolygon (-(b : ℝ)) = segment ℝ
      (((p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b)) : ℕ) : ℝ),
        ((I.ramificationIndex * I.mean (I.ramCountLT b + I.ramMultiplicity b) : ℚ) : ℝ))
      (((p ^ (I.w - I.ramCountLT b) : ℕ) : ℝ),
        ((I.ramificationIndex * I.mean (I.ramCountLT b) : ℚ) : ℝ)) := by
  have hp : p.Prime := Fact.out
  have hcd : I.ramCountLT b + I.ramMultiplicity b ≤ I.w := I.ramCountLT_add_ramMultiplicity_le b
  have hd : 0 < I.ramMultiplicity b := I.ramMultiplicity_pos hb
  have hlt : p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b)) < p ^ (I.w - I.ramCountLT b) :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hblock : (I.ramificationIndex : ℚ) * I.mean (I.ramCountLT b + I.ramMultiplicity b) -
      I.ramificationIndex * I.mean (I.ramCountLT b) =
        p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b)) * ((p ^ I.ramMultiplicity b - 1) * b) :=
    I.mul_mean_add_sub_mul_mean hcd fun _ ↦ I.ram_eq_of_ramCountLT_lt
  have hpow : (p : ℚ) ^ (I.w - I.ramCountLT b) =
      p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b)) * p ^ I.ramMultiplicity b := by
    rw [← pow_add, (by omega : I.w - (I.ramCountLT b + I.ramMultiplicity b) +
      I.ramMultiplicity b = I.w - I.ramCountLT b)]
  have hy : (I.ramificationIndex : ℚ) * I.mean (I.ramCountLT b + I.ramMultiplicity b) +
      ((p : ℚ) ^ (I.w - I.ramCountLT b) - p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b))) * -b =
        I.ramificationIndex * I.mean (I.ramCountLT b) := by
    linear_combination hblock - b * hpow
  rw [edgeOfSlope, I.slopeIndices_ramificationPolygon_neg_ram hb, csInf_Ico hlt,
    sSup_Ico_add_one hlt, I.ramificationPolygon_pow hcd, WithTop.untop₀_coe]
  congr 2
  exact_mod_cast hy

lemma edgeOfSlope_ramificationPolygon_zero (hε : 1 < I.ε) : edgeOfSlope I.ramificationPolygon 0 =
    segment ℝ (((p ^ I.w : ℕ) : ℝ), 0) ((I.ramificationIndex : ℝ), 0) := by
  have hp : p.Prime := Fact.out
  have hlt : p ^ I.w < I.ramificationIndex := lt_mul_of_one_lt_left (pow_pos hp.pos _) hε
  rw [edgeOfSlope, I.slopeIndices_ramificationPolygon_zero, csInf_Ico hlt, sSup_Ico_add_one hlt,
    I.ramificationPolygon_of_pow_le le_rfl hlt.le, mul_zero, add_zero]
  rfl

/-- **The slopes of the ramification polygon of a Herbrand invariant**: the slopes of its unit
edges are `0`, when `ε > 1`, and the negatives of the rams. -/
lemma mem_image_unitSlope_ramificationPolygon_iff : s ∈ unitSlope I.ramificationPolygon ''
    finiteEdges I.ramificationPolygon ↔
      s = 0 ∧ 1 < I.ε ∨ ∃ b ∈ (Finset.Icc 1 I.w).image I.ram, s = -(b : ℝ) := by
  have hp : p.Prime := Fact.out
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [finiteEdges_ramificationPolygon] at hn
    have hn₀ : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn.1
    rcases lt_or_ge n (p ^ I.w) with hlt | hge
    · have hlog : Nat.log p n < I.w := Nat.log_lt_of_lt_pow hn₀ hlt
      exact .inr ⟨_, ram_mem_image (by omega) (Nat.sub_le _ _),
        I.unitSlope_ramificationPolygon_eq_neg_ram hn₀ hn.2⟩
    · exact .inl ⟨I.unitSlope_ramificationPolygon_of_pow_le hge hn.2,
        lt_of_mul_lt_mul_right ((one_mul _).trans_le hge |>.trans_lt hn.2) (Nat.zero_le _)⟩
  · rintro (⟨rfl, hε⟩ | ⟨b, hb, rfl⟩)
    · have hlt : p ^ I.w < I.ramificationIndex := lt_mul_of_one_lt_left (pow_pos hp.pos _) hε
      have hmem : p ^ I.w ∈ slopeIndices I.ramificationPolygon 0 :=
        I.slopeIndices_ramificationPolygon_zero ▸ ⟨le_rfl, hlt⟩
      exact ⟨_, hmem.1, hmem.2⟩
    · have hlt : p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b)) < p ^ (I.w - I.ramCountLT b) :=
        Nat.pow_lt_pow_right hp.one_lt <| by
          have h₁ : I.ramCountLT b + I.ramMultiplicity b ≤ I.w :=
            I.ramCountLT_add_ramMultiplicity_le b
          have h₂ : 0 < I.ramMultiplicity b := I.ramMultiplicity_pos hb
          omega
      have hmem : p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b)) ∈
          slopeIndices I.ramificationPolygon (-(b : ℝ)) :=
        I.slopeIndices_ramificationPolygon_neg_ram hb ▸ ⟨le_rfl, hlt⟩
      exact ⟨_, hmem.1, hmem.2⟩

/-- **The slopes of the segments of the ramification polygon** (LMFDB `lf.ramification_polygon`):
the slopes of the segments of the ramification polygon of `I = (r_1, …, r_w)_ε^f` are `0`, when
`ε > 1`, and the rams `r_1, …, r_w`. -/
lemma mem_segmentSlopes_reflectedPolygon_iff : s ∈ segmentSlopes I.reflectedPolygon ↔
    s = 0 ∧ 1 < I.ε ∨ ∃ b ∈ (Finset.Icc 1 I.w).image I.ram, s = b := by
  have h : s ∈ segmentSlopes I.reflectedPolygon ↔
      -s ∈ unitSlope I.ramificationPolygon '' finiteEdges I.ramificationPolygon := by
    rw [segmentSlopes_reflectedPolygon, finiteEdges_ramificationPolygon]
    exact ⟨fun ⟨n, hn, hs⟩ ↦ ⟨n, hn, by rw [← hs, neg_neg]⟩,
      fun ⟨n, hn, hs⟩ ↦ ⟨n, hn, by rw [hs, neg_neg]⟩⟩
  rw [h, I.mem_image_unitSlope_ramificationPolygon_iff, neg_eq_zero]
  exact or_congr_right <| exists_congr fun _ ↦ and_congr_right fun _ ↦ neg_inj

/-- **The segments of the ramification polygon of a Herbrand invariant** (LMFDB
`lf.ramification_polygon`): the segments of the ramification polygon of `I = (r_1, …, r_w)_ε^f`,
with `e = ε p ^ w`, are the horizontal segment from `(-e, 0)` to `(-p ^ w, 0)`, when `ε > 1`, and
for each distinct ram `b`, of multiplicity `d` and with `c` rams smaller than it, the segment from
`(-p ^ (w - c), e m_c)` to `(-p ^ (w - c - d), e m_{c + d})`, whose slope is `b`. -/
lemma mem_polygonEdges_reflectedPolygon_iff : σ ∈ polygonEdges I.reflectedPolygon ↔
    1 < I.ε ∧ σ = segment ℝ (-(I.ramificationIndex : ℝ), 0) (-((p ^ I.w : ℕ) : ℝ), 0) ∨
      ∃ b ∈ (Finset.Icc 1 I.w).image I.ram, σ = segment ℝ (-((p ^ (I.w - I.ramCountLT b) : ℕ) : ℝ),
          ((I.ramificationIndex * I.mean (I.ramCountLT b) : ℚ) : ℝ))
        (-((p ^ (I.w - (I.ramCountLT b + I.ramMultiplicity b)) : ℕ) : ℝ),
          ((I.ramificationIndex * I.mean (I.ramCountLT b + I.ramMultiplicity b) : ℚ) : ℝ)) := by
  have hσ (τ : Set (ℝ × ℝ)) : reflectVertical '' σ = τ ↔ σ = reflectVertical '' τ :=
    ⟨fun h ↦ by rw [← h, image_reflectVertical_image_reflectVertical],
      fun h ↦ by rw [h, image_reflectVertical_image_reflectVertical]⟩
  rw [reflectedPolygon, mem_polygonEdges_image_reflectVertical,
    mem_polygonEdges_polygonGraph_iff I.isConvexSeq_ramificationPolygon
      I.finite_setOf_ramificationPolygon_ne_top]
  constructor
  · rintro ⟨s, hs, hσs⟩
    rw [eq_comm, hσ] at hσs
    rcases (I.mem_image_unitSlope_ramificationPolygon_iff).mp hs with ⟨rfl, hε⟩ | ⟨b, hb, rfl⟩
    · refine .inl ⟨hε, ?_⟩
      rw [hσs, I.edgeOfSlope_ramificationPolygon_zero hε, image_reflectVertical_segment]
      rfl
    · refine .inr ⟨b, hb, ?_⟩
      rw [hσs, I.edgeOfSlope_ramificationPolygon_neg_ram hb, image_reflectVertical_segment]
      rfl
  · rintro (⟨hε, rfl⟩ | ⟨b, hb, rfl⟩)
    · refine ⟨0, (I.mem_image_unitSlope_ramificationPolygon_iff).mpr (.inl ⟨rfl, hε⟩), ?_⟩
      rw [eq_comm, hσ, I.edgeOfSlope_ramificationPolygon_zero hε, image_reflectVertical_segment]
      rfl
    · refine ⟨-(b : ℝ), (I.mem_image_unitSlope_ramificationPolygon_iff).mpr (.inr ⟨b, hb, rfl⟩),
        ?_⟩
      rw [eq_comm, hσ, I.edgeOfSlope_ramificationPolygon_neg_ram hb, image_reflectVertical_segment]
      rfl

/-- **The rational slopes of the segments of the ramification polygon** (LMFDB
`lf.ramification_polygon`): a rational number `u` is the slope of a segment of the ramification
polygon of `I = (r_1, …, r_w)_ε^f` if and only if `u = 0` and `ε > 1`, or `u` is a ram. -/
lemma ratCast_mem_segmentSlopes_reflectedPolygon_iff : (u : ℝ) ∈ segmentSlopes I.reflectedPolygon ↔
    u = 0 ∧ 1 < I.ε ∨ u ∈ (Finset.Icc 1 I.w).image I.ram := by
  rw [I.mem_segmentSlopes_reflectedPolygon_iff, Rat.cast_eq_zero]
  exact or_congr_right ⟨fun ⟨b, hb, h⟩ ↦ by rwa [Rat.cast_injective h], fun h ↦ ⟨u, h, rfl⟩⟩

lemma nonneg_of_ratCast_mem_segmentSlopes (hu : (u : ℝ) ∈ segmentSlopes I.reflectedPolygon) :
    0 ≤ u := by
  rcases I.ratCast_mem_segmentSlopes_reflectedPolygon_iff.mp hu with ⟨rfl, -⟩ | hb
  · exact le_rfl
  · rcases Finset.mem_image.mp hb with ⟨j, -, rfl⟩
    exact I.ram_nonneg j

lemma one_lt_ε_mul_pow_of_ratCast_mem_segmentSlopes
    (hu : (u : ℝ) ∈ segmentSlopes I.reflectedPolygon) :
    1 < I.ε * p ^ (I.ramCountLT u + I.ramMultiplicity u) := by
  have hp : p.Prime := Fact.out
  rcases I.ratCast_mem_segmentSlopes_reflectedPolygon_iff.mp hu with ⟨rfl, hε⟩ | hb
  · rwa [I.ramCountLT_zero, I.ramMultiplicity_zero, pow_zero, mul_one]
  · exact (Nat.one_lt_pow (Nat.add_pos_right _ (I.ramMultiplicity_pos hb)).ne' hp.one_lt).trans_le
      (Nat.le_mul_of_pos_left _ I.ε_pos)

/-- **The segments of the ramification polygon correspond to its slopes** (LMFDB
`lf.ramification_polygon`): the segments of the ramification polygon of `I = (r_1, …, r_w)_ε^f` are
the segments from `edgeStart u` to `edgeEnd u`, for the slopes `u` of its segments: `0`, when
`ε > 1`, and the distinct rams. The segment of slope `u` ends at `(-p ^ (w - k), e m_k)`, for the
number `k` of rams at most `u`. -/
lemma mem_polygonEdges_reflectedPolygon_iff_exists : σ ∈ polygonEdges I.reflectedPolygon ↔
    ∃ u : ℚ, (u : ℝ) ∈ segmentSlopes I.reflectedPolygon ∧
      σ = segment ℝ (I.edgeStart u) (I.edgeEnd u) := by
  rw [I.mem_polygonEdges_reflectedPolygon_iff]
  constructor
  · rintro (⟨hε, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact ⟨0, I.ratCast_mem_segmentSlopes_reflectedPolygon_iff.mpr (.inl ⟨rfl, hε⟩),
        by rw [I.edgeStart_zero, I.edgeEnd_zero]⟩
    · exact ⟨b, I.ratCast_mem_segmentSlopes_reflectedPolygon_iff.mpr (.inr hb),
        by rw [I.edgeStart_of_mem hb, edgeEnd]⟩
  · rintro ⟨u, hu, rfl⟩
    rcases I.ratCast_mem_segmentSlopes_reflectedPolygon_iff.mp hu with ⟨rfl, hε⟩ | hb
    · exact .inl ⟨hε, by rw [I.edgeStart_zero, I.edgeEnd_zero]⟩
    · exact .inr ⟨u, hb, by rw [I.edgeStart_of_mem hb, edgeEnd]⟩

lemma edgeStart_fst_lt_edgeEnd_fst (hu : (u : ℝ) ∈ segmentSlopes I.reflectedPolygon) :
    (I.edgeStart u).1 < (I.edgeEnd u).1 := by
  have hp : p.Prime := Fact.out
  rcases I.ratCast_mem_segmentSlopes_reflectedPolygon_iff.mp hu with ⟨rfl, hε⟩ | hb
  · rw [I.edgeStart_zero, I.edgeEnd_zero]
    exact neg_lt_neg <| Nat.cast_lt.mpr <| lt_mul_of_one_lt_left (pow_pos hp.pos _) hε
  · have hd : 0 < I.ramMultiplicity u := I.ramMultiplicity_pos hb
    have hcd : I.ramCountLT u + I.ramMultiplicity u ≤ I.w := I.ramCountLT_add_ramMultiplicity_le u
    rw [I.edgeStart_of_mem hb, edgeEnd]
    exact neg_lt_neg <| Nat.cast_lt.mpr <| Nat.pow_lt_pow_right hp.one_lt (by omega)

/-- **The slope of the segment of slope `u`**: for a slope `u` of a segment of the ramification
polygon of `I`, the segment from `edgeStart u` to `edgeEnd u` has the slope `u`: the ram, or `0`
for the horizontal segment. -/
lemma edgeEnd_snd_sub_div (hu : (u : ℝ) ∈ segmentSlopes I.reflectedPolygon) :
    ((I.edgeEnd u).2 - (I.edgeStart u).2) / ((I.edgeEnd u).1 - (I.edgeStart u).1) = u := by
  have hlt : (I.edgeStart u).1 < (I.edgeEnd u).1 := I.edgeStart_fst_lt_edgeEnd_fst hu
  rcases I.ratCast_mem_segmentSlopes_reflectedPolygon_iff.mp hu with ⟨rfl, hε⟩ | hb
  · rw [I.edgeStart_zero, I.edgeEnd_zero, sub_self, zero_div, Rat.cast_zero]
  · have hcd : I.ramCountLT u + I.ramMultiplicity u ≤ I.w := I.ramCountLT_add_ramMultiplicity_le u
    have hblock : (I.ramificationIndex : ℚ) * I.mean (I.ramCountLT u + I.ramMultiplicity u) -
        I.ramificationIndex * I.mean (I.ramCountLT u) =
          p ^ (I.w - (I.ramCountLT u + I.ramMultiplicity u)) *
            ((p ^ I.ramMultiplicity u - 1) * u) :=
      I.mul_mean_add_sub_mul_mean hcd fun _ ↦ I.ram_eq_of_ramCountLT_lt
    have hpow : (p : ℚ) ^ (I.w - I.ramCountLT u) =
        p ^ (I.w - (I.ramCountLT u + I.ramMultiplicity u)) * p ^ I.ramMultiplicity u := by
      rw [← pow_add, (by omega : I.w - (I.ramCountLT u + I.ramMultiplicity u) +
        I.ramMultiplicity u = I.w - I.ramCountLT u)]
    have h : (I.ramificationIndex : ℚ) * I.mean (I.ramCountLT u + I.ramMultiplicity u) -
        I.ramificationIndex * I.mean (I.ramCountLT u) = u * ((p : ℚ) ^ (I.w - I.ramCountLT u) -
          p ^ (I.w - (I.ramCountLT u + I.ramMultiplicity u))) := by
      linear_combination hblock - u * hpow
    rw [div_eq_iff (sub_pos.mpr hlt).ne']
    rw [I.edgeStart_of_mem hb, edgeEnd] at hlt ⊢
    have h' : ((I.ramificationIndex * I.mean (I.ramCountLT u + I.ramMultiplicity u) : ℚ) : ℝ) -
        ((I.ramificationIndex * I.mean (I.ramCountLT u) : ℚ) : ℝ) =
          u * (((p ^ (I.w - I.ramCountLT u) : ℕ) : ℝ) -
            ((p ^ (I.w - (I.ramCountLT u + I.ramMultiplicity u)) : ℕ) : ℝ)) := by
      exact_mod_cast h
    linear_combination h'

end IsNonarchimedeanLocalField.HerbrandInvariant
