import LeanBridge.ForMathlib.Analysis.Convex.PolygonEdges
import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionRamificationPolygon

/-!
# The number of wild segments of a family of extensions

Let `I = (r_1, …, r_w)_ε^f` be a Herbrand invariant. The number of wild segments of a family `I / K`
(LMFDB `lf.wild_segments`) is the number of segments of positive slope of the ramification polygon
of an extension `L / K` in `I / K` (LMFDB `lf.ramification_polygon`), its maximal straight pieces
(`polygonEdges`). This polygon is the ramification polygon of `I`, the same for all the extensions
in `I / K` and all their uniformisers, so the number does not depend on `L / K`. Its segments are
those of the distinct slopes of its unit edges: `0` on `[-e, -p ^ w]`, and `r_k` on
`[-p ^ (w - k + 1), -p ^ (w - k)]`; so the number of wild segments is the number of distinct rams,
which is the number of distinct Swan slopes, as `s_j = s_k` exactly when `r_j = r_k`.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.wildSegmentCount` (LMFDB `lf.wild_segments`): the
  number of wild segments of a family `I / K`.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.wildSegmentCount_eq_ncard_image_ram`: it is the
  number of distinct rams of `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ncard_image_swanSlope_eq_wildSegmentCount`: it is
  the number of distinct Swan slopes of `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.ncard_polygonEdgesWithSlope_eq`
  (LMFDB `lf.wild_segments`): for every extension in `I / K` and every uniformiser, the number of
  segments of positive slope of its ramification polygon is the number of wild segments of `I / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.ncard_setOf_mem_visibleSwanSlopes`
  (LMFDB `lf.wild_segments`): the number of distinct positive Swan slopes of every extension in
  `I / K` is the number of wild segments of `I / K`.
* `IsNonarchimedeanLocalField.ncard_polygonEdgesWithSlope_ramificationPolygonOf_minpoly` (LMFDB
  `lf.wild_segments`): for every finite extension `L / K` inside `K̄`, the number of segments of
  positive slope of its ramification polygon is the number of distinct positive Swan slopes of
  `L / K`.
-/

open Set TauCeti ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace Set

lemma ncard_image_eq_ncard_image_of_iff {ι α β : Type*} {s : Set ι} {f : ι → α} {g : ι → β}
    (h : ∀ j ∈ s, ∀ k ∈ s, f j = f k ↔ g j = g k) : (f '' s).ncard = (g '' s).ncard := by
  have hfst : InjOn Prod.fst ((fun k ↦ (f k, g k)) '' s) := by
    rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩ hjk
    exact Prod.ext hjk ((h j hj k hk).mp hjk)
  have hsnd : InjOn Prod.snd ((fun k ↦ (f k, g k)) '' s) := by
    rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩ hjk
    exact Prod.ext ((h j hj k hk).mpr hjk) hjk
  have hf : f '' s = Prod.fst '' ((fun k ↦ (f k, g k)) '' s) := by
    rw [image_image]
  have hg : g '' s = Prod.snd '' ((fun k ↦ (f k, g k)) '' s) := by
    rw [image_image]
  rw [hf, hg, hfst.ncard_image, hsnd.ncard_image]

end Set

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K] {E : IntermediateField K (AlgebraicClosure K)}
  [FiniteDimensional K E] {π : 𝒪[E]}

namespace HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p) {j k : ℕ}

/-- The **number of wild segments** (LMFDB `lf.wild_segments`) of a family `I / K`: the number of
segments of positive slope of the ramification polygon of `I`, which is the ramification polygon of
every extension in `I / K`, at every uniformiser
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.ramificationPolygonOf_minpoly`). -/
noncomputable def wildSegmentCount : ℕ :=
  (polygonEdgesWithSlope I.reflectedPolygon (Ioi 0)).ncard

variable {I} in
/-- **The number of wild segments of the extensions in a family** (LMFDB `lf.wild_segments`): for
every extension `E` inside `K̄` in the family `I / K`, `I` at the residue characteristic of `K`,
with maximal unramified subextension `K'`, and every uniformiser `π` of `E`, the number of segments
of positive slope of the ramification polygon of `E / K` at `π` is the number of wild segments of
`I / K`. So it does not depend on the extension in `I / K`, nor on the uniformiser. -/
lemma IsInvariantOf.ncard_polygonEdgesWithSlope_eq (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) (hπ : Irreducible π) : (polygonEdgesWithSlope (ramificationPolygonOf
      (minpoly (unramifiedExtension K E (inertiaDegree K E)) (π : E)) (π : E)) (Ioi 0)).ncard =
        I.wildSegmentCount := by
  rw [hE.ramificationPolygonOf_minpoly hp hπ, wildSegmentCount]

variable [Fact p.Prime]

lemma isConvexSeq_ramificationPolygon : IsConvexSeq I.ramificationPolygon := by
  have hset : {n | I.ramificationPolygon n ≠ ⊤} = Icc 1 I.ramificationIndex :=
    ext fun _ ↦ I.ramificationPolygon_ne_top_iff
  refine ⟨hset ▸ ordConnected_Icc, ?_⟩
  rw [finiteEdges_ramificationPolygon]
  intro m hm n hn hmn
  rw [I.unitSlope_ramificationPolygon_eq_neg_ram (Nat.one_le_iff_ne_zero.mp hm.1) hm.2,
    I.unitSlope_ramificationPolygon_eq_neg_ram (Nat.one_le_iff_ne_zero.mp hn.1) hn.2,
    neg_le_neg_iff, Rat.cast_le]
  exact I.monotone_ram (Nat.sub_le_sub_left (Nat.log_mono_right hmn) _)

lemma unitSlope_ramificationPolygon_nonpos {n : ℕ} (hn : n ∈ Ico 1 I.ramificationIndex) :
    unitSlope I.ramificationPolygon n ≤ 0 := by
  rw [I.unitSlope_ramificationPolygon_eq_neg_ram (Nat.one_le_iff_ne_zero.mp hn.1) hn.2, neg_nonpos,
    Rat.cast_nonneg]
  exact I.ram_nonneg _

/-- **The number of wild segments is the number of distinct rams**: the segments of positive slope
of the ramification polygon of `I = (r_1, …, r_w)_ε^f` correspond to the distinct rams. -/
lemma wildSegmentCount_eq_ncard_image_ram : I.wildSegmentCount = (I.ram '' Icc 1 I.w).ncard := by
  have hset : {n | I.ramificationPolygon n ≠ ⊤} = Icc 1 I.ramificationIndex :=
    ext fun _ ↦ I.ramificationPolygon_ne_top_iff
  have hS : unitSlope I.ramificationPolygon '' finiteEdges I.ramificationPolygon ∩
      Neg.neg '' Ioi 0 = Neg.neg '' {s | s ≠ 0 ∧
        ∃ n ∈ Ico 1 I.ramificationIndex, -unitSlope I.ramificationPolygon n = s} := by
    rw [finiteEdges_ramificationPolygon]
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨n, hn, rfl⟩, y, hy, hyx⟩
      refine ⟨-unitSlope I.ramificationPolygon n, ⟨?_, n, hn, rfl⟩, neg_neg _⟩
      rw [← hyx, neg_neg]
      exact (mem_Ioi.mp hy).ne'
    · rintro ⟨_, ⟨hs, n, hn, rfl⟩, rfl⟩
      rw [neg_neg]
      exact ⟨⟨n, hn, rfl⟩, -unitSlope I.ramificationPolygon n,
        (neg_nonneg.mpr (I.unitSlope_ramificationPolygon_nonpos hn)).lt_of_ne hs.symm, neg_neg _⟩
  have hR : {s | ∃ j < I.w, (I.ram (j + 1) : ℝ) = s} = ((↑) : ℚ → ℝ) '' (I.ram '' Icc 1 I.w) := by
    ext s
    refine ⟨?_, ?_⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, ⟨j + 1, ⟨by omega, by omega⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, ⟨hk₁, hk₂⟩, rfl⟩, rfl⟩
      exact ⟨k - 1, by omega, by rw [Nat.sub_add_cancel hk₁]⟩
  rw [wildSegmentCount, reflectedPolygon,
    ncard_polygonEdgesWithSlope_image_reflectVertical,
    ncard_polygonEdgesWithSlope_polygonGraph _ I.isConvexSeq_ramificationPolygon
      (hset ▸ finite_Icc _ _), hS, ncard_image_of_injective _ neg_injective,
    I.setOf_neg_unitSlope_ramificationPolygon_ne_zero, hR,
    ncard_image_of_injective _ Rat.cast_injective]

lemma swanSlope_eq_swanSlope_iff (hjk : j ≤ k) :
    I.swanSlope k = I.swanSlope j ↔ I.ram k = I.ram j := by
  have hnn (i : ℕ) : 0 ≤ I.ram (i + 1) - I.ram i := sub_nonneg.mpr <| I.monotone_ram i.le_succ
  have hden (i : ℕ) : (0 : ℚ) < I.ε * p ^ i := mul_pos I.natCast_ε_pos (pow_pos natCast_prime_pos i)
  have hs : I.swanSlope k - I.swanSlope j =
      ∑ i ∈ Finset.Ico j k, (I.ram (i + 1) - I.ram i) / (I.ε * p ^ i) :=
    (Finset.sum_Ico_eq_sub _ hjk).symm
  have hr : I.ram k - I.ram j = ∑ i ∈ Finset.Ico j k, (I.ram (i + 1) - I.ram i) :=
    (Finset.sum_Ico_sub I.ram hjk).symm
  rw [← sub_eq_zero, hs, Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ div_nonneg (hnn i) (hden i).le,
    ← sub_eq_zero (a := I.ram k), hr, Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnn i]
  exact forall₂_congr fun i _ ↦ div_eq_zero_iff.trans (or_iff_left (hden i).ne')

/-- **The number of wild segments is the number of distinct Swan slopes**: the Swan slopes
`s_j` and `s_k` of `I` agree exactly when the rams `r_j` and `r_k` do. -/
lemma ncard_image_swanSlope_eq_wildSegmentCount :
    (I.swanSlope '' Icc 1 I.w).ncard = I.wildSegmentCount := by
  rw [I.wildSegmentCount_eq_ncard_image_ram]
  refine ncard_image_eq_ncard_image_of_iff fun j _ k _ ↦ ?_
  rcases le_total j k with hjk | hjk
  · exact (eq_comm.trans (I.swanSlope_eq_swanSlope_iff hjk)).trans eq_comm
  · exact I.swanSlope_eq_swanSlope_iff hjk

lemma swanSlope_pos (hk₀ : 1 ≤ k) (hk : k ≤ I.w) : 0 < I.swanSlope k := by
  have h₁ : 0 < I.swanSlope 1 := by
    rw [swanSlope, Finset.sum_range_one, I.ram_zero, sub_zero, pow_zero, mul_one]
    exact div_pos (I.zero_lt_ram_one (by omega)) I.natCast_ε_pos
  exact h₁.trans_le (swanSlope_mono hk₀)

variable {I} in
/-- **The number of wild segments is the number of distinct positive Swan slopes** (LMFDB
`lf.wild_segments`): for every extension `E` inside `K̄` in the family `I / K`, `I` at the residue
characteristic of `K`, the number of distinct positive Swan slopes of `E / K` (Deligne's positive
upper ramification breaks `IsNonarchimedeanLocalField.visibleSwanSlopes`) is the number of wild
segments of `I / K`. -/
lemma IsInvariantOf.ncard_setOf_mem_visibleSwanSlopes (hE : I.IsInvariantOf K E) :
    {s : ℝ | 0 < s ∧ s ∈ visibleSwanSlopes E}.ncard = I.wildSegmentCount := by
  have h :
      {s : ℝ | 0 < s ∧ s ∈ visibleSwanSlopes E} = ((↑) : ℚ → ℝ) '' (I.swanSlope '' Icc 1 I.w) := by
    rw [hE.2.2]
    ext s
    refine ⟨?_, ?_⟩
    · rintro ⟨-, hs⟩
      rcases Multiset.mem_map.mp hs with ⟨k, hk, rfl⟩
      have hk' : k < I.w := Multiset.mem_range.mp hk
      exact ⟨_, ⟨k + 1, ⟨by omega, by omega⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, ⟨hk₁, hk₂⟩, rfl⟩, rfl⟩
      refine ⟨Rat.cast_pos.mpr (I.swanSlope_pos hk₁ hk₂), Multiset.mem_map.mpr
        ⟨k - 1, Multiset.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel hk₁]⟩⟩
  rw [h, ncard_image_of_injective _ Rat.cast_injective, I.ncard_image_swanSlope_eq_wildSegmentCount]

end HerbrandInvariant

/-- **The segments of positive slope of the ramification polygon and the Swan slopes** (LMFDB
`lf.wild_segments`): for a finite extension `E` of a `p`-adic field `K` inside `K̄`, with maximal
unramified subextension `K'`, and a uniformiser `π` of `E`, the number of segments of positive
slope of the ramification polygon of `E / K` at `π` is the number of distinct positive Swan slopes
of `E / K`. -/
lemma ncard_polygonEdgesWithSlope_ramificationPolygonOf_minpoly (hπ : Irreducible π) :
    (polygonEdgesWithSlope (ramificationPolygonOf
      (minpoly (unramifiedExtension K E (inertiaDegree K E)) (π : E)) (π : E)) (Ioi 0)).ncard =
        {s : ℝ | 0 < s ∧ s ∈ visibleSwanSlopes E}.ncard := by
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  rw [(isInvariantOf_visibleHerbrandInvariant E).ncard_polygonEdgesWithSlope_eq
    rfl hπ, (isInvariantOf_visibleHerbrandInvariant E).ncard_setOf_mem_visibleSwanSlopes]

end IsNonarchimedeanLocalField
