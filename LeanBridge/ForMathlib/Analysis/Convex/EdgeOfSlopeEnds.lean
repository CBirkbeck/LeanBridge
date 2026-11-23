import LeanBridge.ForMathlib.Analysis.Convex.PolygonEdges

/-!
# The ends of the segments of the lower convex envelope of a height sequence

Let `a : ℕ → WithTop ℝ` be a height sequence with finitely many finite heights and `h` its lower
convex envelope `TauCeti.lowerConvexEnvelope a`, the greatest convex sequence below `a`, whose
polygon is the lower convex hull of the points `(n, a_n)` with `a_n` finite
(`TauCeti.lowerConvexHull_heightPoints`). For the slope `s` of a unit edge of `h`, the segment
`TauCeti.edgeOfSlope h s` of the polygon runs from the first index `k` of the unit edges of slope
`s` to the last one plus one, `u`. This file proves that both ends of the segment are points of
`a`, `a_k = h_k` and `a_u = h_u`, that the points of `a` lie on or above the line of the segment,
and that the segments of two consecutive slopes share an end. So the segments of the lower convex
hull of finitely many points with natural abscissas join two of the points, as the segments of a
Newton polygon do.

The ends are points of `a` because a line through `(k, h_k)` lies strictly below `h` at all the
other finite heights of `h` when its slope lies strictly between the slopes of the unit edges of
`h` on either side of `k`: if `a_k > h_k`, a slightly higher parallel line would be a convex
minorant of `a` above `h` at `k`.

## Main results

* `TauCeti.lowerConvexEnvelope_sInf_slopeIndices` and
  `TauCeti.lowerConvexEnvelope_sSup_slopeIndices_add_one`: the ends of the segment of slope `s` of
  the polygon are points of `a`.
* `TauCeti.add_mul_le_of_mem_image_unitSlope`: the points of `a` lie on or above the line of the
  segment of slope `s`.
* `TauCeti.sSup_slopeIndices_add_one_eq_sInf`: the segments of two consecutive slopes share an
  end.
-/

open Set

namespace TauCeti

variable {a h : ℕ → WithTop ℝ} {s t σ : ℝ} {k n : ℕ}

lemma finite_lowerConvexEnvelope_ne_top (hfin : {n | a n ≠ ⊤}.Finite) :
    {n | lowerConvexEnvelope a n ≠ ⊤}.Finite := by
  rcases hfin.bddAbove with ⟨b, hb⟩
  refine (finite_Iic b).subset fun n hn ↦ ?_
  rcases (lowerConvexEnvelope_ne_top_iff (isAdmissible_of_finite hfin)).mp hn with
    ⟨-, -, j, hnj, -, hj⟩
  exact hnj.trans (hb hj)

lemma lowerConvexEnvelope_eq_of_lt (hfin : {n | a n ≠ ⊤}.Finite) (hk : lowerConvexEnvelope a k ≠ ⊤)
    (hlt : ∀ n, n ≠ k → lowerConvexEnvelope a n ≠ ⊤ → (lowerConvexEnvelope a k).untop₀ +
      σ * ((n : ℝ) - k) < (lowerConvexEnvelope a n).untop₀) : lowerConvexEnvelope a k = a k := by
  have hle : lowerConvexEnvelope a ≤ a :=
    lowerConvexEnvelope_le (isAdmissible_of_finite hfin)
  refine le_antisymm (hle k) (not_lt.mp fun hka ↦ ?_)
  have hne : hfin.toFinset.Nonempty := by
    rcases (lowerConvexEnvelope_ne_top_iff (isAdmissible_of_finite hfin)).mp hk with
      ⟨i, -, -, -, hi, -⟩
    exact ⟨i, hfin.mem_toFinset.mpr hi⟩
  have hgap (m : ℕ) (hm : m ∈ hfin.toFinset) :
      0 < (a m).untop₀ - ((lowerConvexEnvelope a k).untop₀ + σ * ((m : ℝ) - k)) := by
    have ham : a m ≠ ⊤ :=
      hfin.mem_toFinset.mp hm
    have hm' : lowerConvexEnvelope a m ≠ ⊤ :=
      ne_top_of_le_ne_top ham (hle m)
    have hle' : (lowerConvexEnvelope a m).untop₀ ≤ (a m).untop₀ :=
      WithTop.coe_le_coe.mp <| by
        rw [WithTop.coe_untop₀_of_ne_top hm', WithTop.coe_untop₀_of_ne_top ham]
        exact hle m
    rcases eq_or_ne m k with rfl | hmk
    · have hlt' : (lowerConvexEnvelope a m).untop₀ < (a m).untop₀ :=
        WithTop.coe_lt_coe.mp <| by
          rwa [WithTop.coe_untop₀_of_ne_top hm', WithTop.coe_untop₀_of_ne_top ham]
      linarith
    · linarith [hlt m hmk hm']
  set ε : ℝ := hfin.toFinset.inf' hne fun m ↦
    (a m).untop₀ - ((lowerConvexEnvelope a k).untop₀ + σ * ((m : ℝ) - k))
  have hε : 0 < ε :=
    (Finset.lt_inf'_iff hne).mpr hgap
  have hline : (fun m : ℕ ↦ (((lowerConvexEnvelope a k).untop₀ + ε - σ * k + σ * m : ℝ) :
      WithTop ℝ)) ≤ a := by
    intro m
    rcases eq_or_ne (a m) ⊤ with ham | ham
    · rw [ham]
      exact le_top
    have hinf : ε ≤ (a m).untop₀ - ((lowerConvexEnvelope a k).untop₀ + σ * ((m : ℝ) - k)) :=
      Finset.inf'_le _ (hfin.mem_toFinset.mpr ham)
    rw [← WithTop.coe_untop₀_of_ne_top ham, WithTop.coe_le_coe]
    linarith
  have hk' :
      (lowerConvexEnvelope a k).untop₀ + ε - σ * k + σ * k ≤ (lowerConvexEnvelope a k).untop₀ :=
    WithTop.coe_le_coe.mp ((le_lowerConvexEnvelope (isConvexSeq_affine _ σ) hline k).trans_eq
      (WithTop.coe_untop₀_of_ne_top hk).symm)
  linarith

lemma exists_lt_of_sInf_slopeIndices (hh : IsConvexSeq h) (hs : s ∈ unitSlope h '' finiteEdges h) :
    ∃ σ : ℝ, ∀ n, n ≠ sInf (slopeIndices h s) → h n ≠ ⊤ → (h (sInf (slopeIndices h s))).untop₀ +
      σ * ((n : ℝ) - sInf (slopeIndices h s)) < (h n).untop₀ := by
  set K : ℕ := sInf (slopeIndices h s)
  have hK : K ∈ slopeIndices h s :=
    sInf_mem_slopeIndices hs
  have hright (σ : ℝ) (hσ : σ < s) (n : ℕ) (hKn : K < n) (hn : h n ≠ ⊤) :
      (h K).untop₀ + σ * ((n : ℝ) - K) < (h n).untop₀ := by
    have h₁ : ((n - K : ℕ) : ℝ) * unitSlope h K ≤ (h n).untop₀ - (h K).untop₀ :=
      hh.mul_slope_le_sub hK.1.1 hn hK.1.1 hK.1.2 hKn.le le_rfl
    rw [hK.2, Nat.cast_sub hKn.le] at h₁
    have h₂ : (0 : ℝ) < n - K :=
      sub_pos.mpr (Nat.cast_lt.mpr hKn)
    nlinarith
  by_cases hL : ∃ j, j + 1 = K ∧ j ∈ finiteEdges h
  · rcases hL with ⟨j, hj, hjE⟩
    have hjs : unitSlope h j < s := by
      refine lt_of_le_of_ne ?_ fun heq ↦ Nat.notMem_of_lt_sInf (by omega : j < K) ⟨hjE, heq⟩
      have h₁ : unitSlope h j ≤ unitSlope h K :=
        hh.monotoneOn hjE hK.1 (by omega)
      rwa [hK.2] at h₁
    refine ⟨(unitSlope h j + s) / 2, fun n hnK hn ↦ ?_⟩
    rcases lt_or_gt_of_ne hnK with hnK | hnK
    · have h₁ : (h K).untop₀ - (h n).untop₀ ≤ ((K - n : ℕ) : ℝ) * unitSlope h j :=
        hh.sub_le_mul_slope hn hK.1.1 hjE.1 hjE.2 hnK.le (by omega)
      rw [Nat.cast_sub hnK.le] at h₁
      have h₂ : (0 : ℝ) < K - n :=
        sub_pos.mpr (Nat.cast_lt.mpr hnK)
      nlinarith
    · exact hright _ (by linarith) n hnK hn
  · refine ⟨s - 1, fun n hnK hn ↦ ?_⟩
    rcases lt_or_gt_of_ne hnK with hnK | hnK
    · refine absurd ⟨K - 1, by omega, ?_, by rw [Nat.sub_add_cancel (by omega)]; exact hK.1.1⟩ hL
      exact hh.ne_top_of_le_of_le hn hK.1.1 (by omega) (by omega)
    · exact hright _ (by linarith) n hnK hn

lemma exists_lt_of_sSup_slopeIndices_add_one (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h) : ∃ σ : ℝ, ∀ n, n ≠ sSup (slopeIndices h s) + 1 →
      h n ≠ ⊤ → (h (sSup (slopeIndices h s) + 1)).untop₀ +
        σ * ((n : ℝ) - (sSup (slopeIndices h s) + 1 : ℕ)) < (h n).untop₀ := by
  set U : ℕ := sSup (slopeIndices h s)
  have hU : U ∈ slopeIndices h s :=
    sSup_mem_slopeIndices hfin hs
  have hleft (σ : ℝ) (hσ : s < σ) (n : ℕ) (hnU : n < U + 1) (hn : h n ≠ ⊤) :
      (h (U + 1)).untop₀ + σ * ((n : ℝ) - (U + 1 : ℕ)) < (h n).untop₀ := by
    have h₁ : (h (U + 1)).untop₀ - (h n).untop₀ ≤ ((U + 1 - n : ℕ) : ℝ) * unitSlope h U :=
      hh.sub_le_mul_slope hn hU.1.2 hU.1.1 hU.1.2 hnU.le le_rfl
    rw [hU.2, Nat.cast_sub hnU.le] at h₁
    have h₂ : (0 : ℝ) < (U + 1 : ℕ) - n :=
      sub_pos.mpr (Nat.cast_lt.mpr hnU)
    nlinarith
  by_cases hR : U + 1 ∈ finiteEdges h
  · have hRs : s < unitSlope h (U + 1) := by
      refine lt_of_le_of_ne ?_ fun heq ↦ ?_
      · have h₁ : unitSlope h U ≤ unitSlope h (U + 1) :=
          hh.monotoneOn hU.1 hR (by omega)
        rwa [hU.2] at h₁
      · have hmem : U + 1 ∈ slopeIndices h s :=
          ⟨hR, heq.symm⟩
        have hle : U + 1 ≤ U :=
          le_csSup (bddAbove_slopeIndices s hfin) hmem
        omega
    refine ⟨(s + unitSlope h (U + 1)) / 2, fun n hnU hn ↦ ?_⟩
    rcases lt_or_gt_of_ne hnU with hnU | hnU
    · exact hleft _ (by linarith) n hnU hn
    · have h₁ : ((n - (U + 1) : ℕ) : ℝ) * unitSlope h (U + 1) ≤
          (h n).untop₀ - (h (U + 1)).untop₀ :=
        hh.mul_slope_le_sub hR.1 hn hR.1 hR.2 hnU.le le_rfl
      rw [Nat.cast_sub hnU.le] at h₁
      have h₂ : (0 : ℝ) < n - (U + 1 : ℕ) :=
        sub_pos.mpr (Nat.cast_lt.mpr hnU)
      nlinarith
  · refine ⟨s + 1, fun n hnU hn ↦ ?_⟩
    rcases lt_or_gt_of_ne hnU with hnU | hnU
    · exact hleft _ (by linarith) n hnU hn
    · exact absurd ⟨hU.1.2, hh.ne_top_of_le_of_le hU.1.2 hn (by omega) hnU⟩ hR

/-- **The first end of a segment of the polygon is a point**: for a height sequence `a` with
finitely many finite heights and the slope `s` of a unit edge of its lower convex envelope `h`, the
envelope agrees with `a` at the first index `k` of the unit edges of slope `s`, the first end of
the segment `TauCeti.edgeOfSlope h s` of the polygon. -/
lemma lowerConvexEnvelope_sInf_slopeIndices (hfin : {n | a n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope (lowerConvexEnvelope a) '' finiteEdges (lowerConvexEnvelope a)) :
    lowerConvexEnvelope a (sInf (slopeIndices (lowerConvexEnvelope a) s)) =
      a (sInf (slopeIndices (lowerConvexEnvelope a) s)) := by
  rcases exists_lt_of_sInf_slopeIndices (isConvexSeq_lowerConvexEnvelope a) hs with ⟨σ, hσ⟩
  exact lowerConvexEnvelope_eq_of_lt hfin (sInf_mem_slopeIndices hs).1.1 hσ

/-- **The last end of a segment of the polygon is a point**: for a height sequence `a` with
finitely many finite heights and the slope `s` of a unit edge of its lower convex envelope `h`, the
envelope agrees with `a` at the last index `u - 1` of the unit edges of slope `s` plus one, the
last end of the segment `TauCeti.edgeOfSlope h s` of the polygon. -/
lemma lowerConvexEnvelope_sSup_slopeIndices_add_one (hfin : {n | a n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope (lowerConvexEnvelope a) '' finiteEdges (lowerConvexEnvelope a)) :
    lowerConvexEnvelope a (sSup (slopeIndices (lowerConvexEnvelope a) s) + 1) =
      a (sSup (slopeIndices (lowerConvexEnvelope a) s) + 1) := by
  rcases exists_lt_of_sSup_slopeIndices_add_one (isConvexSeq_lowerConvexEnvelope a)
    (finite_lowerConvexEnvelope_ne_top hfin) hs with ⟨σ, hσ⟩
  exact lowerConvexEnvelope_eq_of_lt hfin
    (sSup_mem_slopeIndices (finite_lowerConvexEnvelope_ne_top hfin) hs).1.2 hσ

variable (n) in
/-- **The points lie above the line of a segment**: for a height sequence `a` with finitely many
finite heights and the slope `s` of a unit edge of its lower convex envelope, the points `(n, a_n)`
lie on or above the line of slope `s` through the first end `(k, a_k)` of the segment of slope
`s` of the polygon. -/
lemma add_mul_le_of_mem_image_unitSlope (hfin : {n | a n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope (lowerConvexEnvelope a) '' finiteEdges (lowerConvexEnvelope a)) :
    (((a (sInf (slopeIndices (lowerConvexEnvelope a) s))).untop₀ +
      ((n : ℝ) - sInf (slopeIndices (lowerConvexEnvelope a) s)) * s : ℝ) : WithTop ℝ) ≤ a n := by
  have hK :
      sInf (slopeIndices (lowerConvexEnvelope a) s) ∈ slopeIndices (lowerConvexEnvelope a) s :=
    sInf_mem_slopeIndices hs
  have h₁ : (((lowerConvexEnvelope a (sInf (slopeIndices (lowerConvexEnvelope a) s))).untop₀ +
      ((n : ℝ) - sInf (slopeIndices (lowerConvexEnvelope a) s)) *
        unitSlope (lowerConvexEnvelope a) (sInf (slopeIndices (lowerConvexEnvelope a) s)) : ℝ) :
          WithTop ℝ) ≤ lowerConvexEnvelope a n :=
    (isConvexSeq_lowerConvexEnvelope a).supportingLine_le hK.1.1 hK.1.2 n
  rw [hK.2, lowerConvexEnvelope_sInf_slopeIndices hfin hs] at h₁
  exact h₁.trans (lowerConvexEnvelope_le (isAdmissible_of_finite hfin) n)

/-- **Consecutive segments share an end**: for a convex height sequence `h` with finitely many
finite heights and two slopes `s < t` of unit edges of `h` with no slope of a unit edge strictly
between them, the segment of slope `s` ends where the segment of slope `t` starts. -/
lemma sSup_slopeIndices_add_one_eq_sInf (hh : IsConvexSeq h) (hfin : {n | h n ≠ ⊤}.Finite)
    (hs : s ∈ unitSlope h '' finiteEdges h) (ht : t ∈ unitSlope h '' finiteEdges h) (hst : s < t)
    (hbetween : ∀ r ∈ unitSlope h '' finiteEdges h, s < r → t ≤ r) :
    sSup (slopeIndices h s) + 1 = sInf (slopeIndices h t) := by
  have hU : sSup (slopeIndices h s) ∈ slopeIndices h s :=
    sSup_mem_slopeIndices hfin hs
  have hK : sInf (slopeIndices h t) ∈ slopeIndices h t :=
    sInf_mem_slopeIndices ht
  have hle : sSup (slopeIndices h s) < sInf (slopeIndices h t) := by
    by_contra hcon
    have h₁ : unitSlope h (sInf (slopeIndices h t)) ≤ unitSlope h (sSup (slopeIndices h s)) :=
      hh.monotoneOn hK.1 hU.1 (not_lt.mp hcon)
    rw [hK.2, hU.2] at h₁
    linarith
  have hR : sSup (slopeIndices h s) + 1 ∈ finiteEdges h :=
    (ordConnected_finiteEdges hh.ordConnected).out hU.1 hK.1 ⟨by omega, by omega⟩
  have hRs : s < unitSlope h (sSup (slopeIndices h s) + 1) := by
    have h₁ : unitSlope h (sSup (slopeIndices h s)) ≤ unitSlope h (sSup (slopeIndices h s) + 1) :=
      hh.monotoneOn hU.1 hR (by omega)
    rw [hU.2] at h₁
    refine h₁.lt_of_ne fun heq ↦ ?_
    have hle' : sSup (slopeIndices h s) + 1 ≤ sSup (slopeIndices h s) :=
      le_csSup (bddAbove_slopeIndices s hfin) ⟨hR, heq.symm⟩
    omega
  have hRt : unitSlope h (sSup (slopeIndices h s) + 1) ≤ t := by
    have h₁ : unitSlope h (sSup (slopeIndices h s) + 1) ≤ unitSlope h (sInf (slopeIndices h t)) :=
      hh.monotoneOn hR hK.1 (by omega)
    rwa [hK.2] at h₁
  have hRt' : unitSlope h (sSup (slopeIndices h s) + 1) = t :=
    le_antisymm hRt (hbetween _ ⟨_, hR, rfl⟩ hRs)
  exact le_antisymm (by omega) (Nat.sInf_le ⟨hR, hRt'⟩)

end TauCeti
