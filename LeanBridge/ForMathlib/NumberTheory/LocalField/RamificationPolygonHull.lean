import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeLevels
import TauCeti.Analysis.Convex.Sequence.Face

/-!
# The ramification polygon as a lower convex hull

Let `g` be a monic polynomial of degree `e` over a ring `R` and `π` a root of `g` that is a
uniformiser of a discrete valuation ring `S` over `R`. The ramification polynomial of `g` at `π` is
`ρ(x) = π ^ (-e) g(π x + π) = x ^ e + ∑_{i < e} ρ_i x ^ i`, and the ramification polygon (LMFDB
`lf.ramification_polygon`) is the lower convex hull of the points `(i, v_S(ρ_i))` with `ρ_i ≠ 0`,
the point `(e, 0)` of the leading coefficient included: the Newton polygon of `ρ`. The LMFDB draws
its reflection through the vertical axis, the hull of the points `(-i, v_S(ρ_i))`, whose slopes are
the negatives of the slopes here. This file defines the heights `v_S(ρ_i)`
(`IsNonarchimedeanLocalField.HerbrandInvariant.ramificationHeight`) and takes their lower convex
hull with Tau Ceti's `TauCeti.lowerConvexEnvelope`.

For a Herbrand invariant `I = (r_1, …, r_w)_ε^f` with `e = ε p ^ w`, means `m_k` and Swan slopes
`s_k`, the ramification polygon of `I`
(`IsNonarchimedeanLocalField.HerbrandInvariant.ramificationPolygon`) is the polygon over `[1, e]`
with the vertices `(p ^ (w - k), e m_k)` for `0 ≤ k ≤ w` and `(e, 0)`: on
`[p ^ (w - k), p ^ (w - k + 1)]` it is the line `x ↦ e s_k - r_k x` of slope `-r_k`, and on
`[p ^ w, e]` it is `0`. So its slopes are the negatives of the rams, together with the slope `0`
on `[p ^ w, e]` when `ε > 1`, which is not a ram: the nonzero slopes of the LMFDB's reflected
polygon are the rams, and LMFDB `lf.family_diagrams` and `lf.ramification_polygon` need the word
"nonzero".

The main theorem says that when the ramification polygon of `g` at `π` is the polygon of `I` in
the sense of `IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon` (the points lie
above the lines, and the vertices are attained: Monge's Proposition 1 and Lemma 1), the lower
convex hull of the points `(i, v_S(ρ_i))` is the ramification polygon of `I`.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.ramificationHeight` (LMFDB
  `lf.ramification_polygon`): the heights `v_S(ρ_i)` of the ramification polynomial.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ramificationLine`: the lines `x ↦ e s_k - r_k x`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ramificationPolygon` (LMFDB
  `lf.ramification_polygon`): the ramification polygon of a Herbrand invariant.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.ramificationHeight_eq_map_addVal_coeff`: the heights
  are the valuations of the coefficients of the ramification polynomial.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon.C_pow_dvd_mongeShift`:
  the ramification polynomial has coefficients in `S`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ramificationPolygon_pow`: the vertices
  `(p ^ (w - k), e m_k)` of the ramification polygon of `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.unitSlope_ramificationPolygon`: its slope on
  `[p ^ (w - k), p ^ (w - k + 1)]` is `-r_k`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.unitSlope_ramificationPolygon_of_pow_le`: its slope
  on `[p ^ w, e]` is `0`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.unitSlope_ramificationPolygon_pow_of_one_lt`: for
  `ε > 1` it has the slope `0` at `p ^ w`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.map_neg_unitSlope_ramificationPolygon`: the rams
  are the negatives of its slopes between the consecutive powers of `p`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.unitSlope_ramificationPolygon_eq_neg_ram`: each of
  its slopes is the negative of a ram, or `0`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.unitSlope_ramificationPolygon_eq_zero_iff`: its
  slope is `0` exactly on `[p ^ w, e]`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.setOf_neg_unitSlope_ramificationPolygon_ne_zero`
  (LMFDB `lf.ramification_polygon`): the nonzero slopes of its reflection are the rams.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon.lowerConvexEnvelope_eq`
  (LMFDB `lf.ramification_polygon`): the lower convex hull of the points `(i, v_S(ρ_i))` is the
  ramification polygon of `I`.

## References

* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, Proposition 1 and Lemma 1.
-/

open IsDiscreteValuationRing Polynomial TauCeti

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p) {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Algebra R S] {g : R[X]} {π : S} {j k n : ℕ} {x : ℚ}

variable (k x) in
/-- The `k`-th **line of the ramification polygon** of a Herbrand invariant
`I = (r_1, …, r_w)_ε^f`: the line `x ↦ e s_k - r_k x` of slope `-r_k`, for `e = ε p ^ w` and the
Swan slope `s_k`. It passes through `(p ^ (w - k), e m_k)` and, for `k ≥ 1`, through
`(p ^ (w - k + 1), e m_{k - 1})`, and it is `0` for `k = 0`. -/
def ramificationLine : ℚ :=
  I.ramificationIndex * I.swanSlope k - I.ram k * x

variable (x) in
lemma ramificationLine_zero : I.ramificationLine 0 x = 0 := by
  simp [ramificationLine, swanSlope, I.ram_zero]

variable (k x) in
lemma cast_ramificationLine : ((I.ramificationLine k x : ℚ) : ℝ) =
    ((I.ramificationIndex * I.swanSlope k : ℚ) : ℝ) + -(I.ram k : ℝ) * x := by
  rw [ramificationLine]
  push_cast
  ring1

lemma isVertex_zero : I.IsVertex 0 := by
  rcases Nat.eq_zero_or_pos I.w with h | h
  · exact .inl h.symm
  · exact .inr <| I.ram_zero.le.trans_lt <| I.zero_lt_ram_one h

private lemma ram_pos (hk : k ≠ 0) (hk' : k ≤ I.w) : 0 < I.ram k :=
  (I.zero_lt_ram_one <| (Nat.pos_of_ne_zero hk).trans_le hk').trans_le <|
    I.monotone_ram <| Nat.one_le_iff_ne_zero.mpr hk

variable (n) in
/-- The **ramification polygon of a Herbrand invariant** `I = (r_1, …, r_w)_ε^f` (LMFDB
`lf.ramification_polygon`, for a family `I / K`), as a height sequence: for `1 ≤ n ≤ e = ε p ^ w`
its height at `n` is `e s_k - r_k n`, where `k = w - ⌊log_p n⌋` (and `k = 0` for `n ≥ p ^ w`) is
the index with `p ^ (w - k) ≤ n < p ^ (w - k + 1)`, and it is `⊤` outside `[1, e]`. It is the
polygon with the vertices `(p ^ (w - k), e m_k)`, `0 ≤ k ≤ w`, and `(e, 0)`, which the LMFDB draws
reflected through the vertical axis. -/
noncomputable def ramificationPolygon : WithTop ℝ :=
  if n ∈ Set.Icc 1 I.ramificationIndex then
    (((I.ramificationLine (I.w - Nat.log p n) n : ℚ) : ℝ) : WithTop ℝ)
  else ⊤

lemma ramificationPolygon_ne_top_iff :
    I.ramificationPolygon n ≠ ⊤ ↔ n ∈ Set.Icc 1 I.ramificationIndex := by
  rw [ramificationPolygon]
  split_ifs with h
  · exact iff_of_true WithTop.coe_ne_top h
  · exact iff_of_false (fun h' ↦ h' rfl) h

variable (g π n) in
/-- The **heights of the ramification polynomial** (LMFDB `lf.ramification_polygon`) of a polynomial
`g` of degree `e` over `R` at an element `π` of a discrete valuation ring `S` over `R`: the
valuation `v_S(ρ_n)` of the coefficient of `x ^ n` in the ramification polynomial
`ρ(x) = π ^ (-e) g(π x + π)`, that is the valuation of the coefficient of `x ^ n` in `g(π x + π)`
minus `e`, and `⊤` if this coefficient is `0`. The ramification polygon of `g` at `π` is the lower
convex hull `TauCeti.lowerConvexEnvelope` of the points `(n, v_S(ρ_n))`. -/
noncomputable def ramificationHeight : WithTop ℝ :=
  (addVal S ((mongeShift g π 0).coeff n)).map fun v ↦ (v : ℝ) - g.natDegree

lemma ramificationHeight_zero (hroot : aeval π g = 0) : ramificationHeight g π 0 = ⊤ := by
  rw [ramificationHeight, coeff_zero_eq_eval_zero, eval_mongeShift, mul_zero, add_zero, hroot,
    AddValuation.map_zero, ENat.map_top]

lemma ramificationHeight_of_natDegree_lt (hn : g.natDegree < n) : ramificationHeight g π n = ⊤ := by
  rw [ramificationHeight, coeff_mongeShift_eq_mul, coeff_eq_zero_of_natDegree_lt <|
    (natDegree_taylor _ _).trans_lt <| natDegree_map_le.trans_lt hn, zero_mul,
    AddValuation.map_zero, ENat.map_top]

lemma isAdmissible_ramificationHeight : TauCeti.IsAdmissible (ramificationHeight g π) := by
  refine ⟨-g.natDegree, 0, fun n ↦ ?_⟩
  rw [ramificationHeight]
  rcases eq_or_ne (addVal S ((mongeShift g π 0).coeff n)) ⊤ with h | h
  · rw [h, ENat.map_top]
    exact le_top
  · rcases ENat.ne_top_iff_exists.mp h with ⟨v, hv⟩
    rw [← hv, ENat.map_natCast]
    exact WithTop.coe_le_coe.mpr (by simp)

lemma ramificationHeight_eq (hπ : Irreducible π) {v : ℕ}
    (hv : addVal S ((taylor π (g.map (algebraMap R S))).coeff n) = v) :
    ramificationHeight g π n = ((v + n - g.natDegree : ℝ) : WithTop ℝ) := by
  rw [ramificationHeight, addVal_coeff_mongeShift n hπ, hv, ← Nat.cast_add, ENat.map_natCast,
    WithTop.coe_eq_coe]
  push_cast
  ring1

lemma ramificationHeight_natDegree (hπ : Irreducible π) (hg : g.Monic) :
    ramificationHeight g π g.natDegree = 0 := by
  have h : addVal S ((taylor π (g.map (algebraMap R S))).coeff g.natDegree) = (0 : ℕ) := by
    rw [← hg.natDegree_map (algebraMap R S), coeff_taylor_natDegree, (hg.map _).leadingCoeff,
      AddValuation.map_one, Nat.cast_zero]
  rw [ramificationHeight_eq hπ h, Nat.cast_zero, zero_add, sub_self, WithTop.coe_zero]

variable (n) in
/-- **The heights are the valuations of the coefficients of the ramification polynomial**: if
`ρ ∈ S[X]` is the ramification polynomial of `g` at a uniformiser `π`, that is
`g(π x + π) = π ^ e ρ(x)`, then the height at `n` is `v_S(ρ_n)`, and `⊤` if `ρ_n = 0`. -/
lemma ramificationHeight_eq_map_addVal_coeff (hπ : Irreducible π) {ρ : S[X]}
    (hρ : mongeShift g π 0 = C (π ^ g.natDegree) * ρ) :
    ramificationHeight g π n = (addVal S (ρ.coeff n)).map (↑) := by
  rw [ramificationHeight, hρ, coeff_C_mul, addVal_mul, addVal_pow, addVal_uniformizer hπ,
    nsmul_one]
  rcases eq_or_ne (addVal S (ρ.coeff n)) ⊤ with h | h
  · rw [h, add_top, ENat.map_top, ENat.map_top]
  · rcases ENat.ne_top_iff_exists.mp h with ⟨v, hv⟩
    rw [← hv, ← Nat.cast_add, ENat.map_natCast, ENat.map_natCast, WithTop.coe_eq_coe]
    push_cast
    ring1

variable {I} in
lemma IsRamificationPolygon.ramificationLine_le (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hk : k ≤ I.w) (hn : n ≠ 0) :
    (((I.ramificationLine k n : ℚ) : ℝ) : WithTop ℝ) ≤ ramificationHeight g π n := by
  rcases eq_or_ne (addVal S ((taylor π (g.map (algebraMap R S))).coeff n)) ⊤ with h | h
  · rw [ramificationHeight, addVal_coeff_mongeShift n hπ, h, top_add, ENat.map_top]
    exact le_top
  · rcases ENat.ne_top_iff_exists.mp h with ⟨v, hv⟩
    have hle : (I.ramificationIndex : ℚ) * (I.swanSlope k + 1) ≤ v + n + n * I.ram k :=
      hP.le_addVal hk hn hv.symm
    have hle' : I.ramificationLine k n ≤ (v : ℚ) + n - g.natDegree := by
      rw [ramificationLine, hP.natDegree_eq]
      linarith
    rw [ramificationHeight_eq hπ hv.symm, WithTop.coe_le_coe]
    exact_mod_cast hle'

variable {I} in
lemma IsRamificationPolygon.ramificationHeight_pow (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hk : k ≤ I.w) (hv : I.IsVertex k) :
    ramificationHeight g π (p ^ (I.w - k)) =
      (((I.ramificationIndex * I.mean k : ℚ) : ℝ) : WithTop ℝ) := by
  rcases hP.exists_addVal_eq hk hv with ⟨v, hv₁, hv₂⟩
  have h : (v : ℚ) + (p ^ (I.w - k) : ℕ) - g.natDegree = I.ramificationIndex * I.mean k := by
    rw [hP.natDegree_eq]
    push_cast
    linarith
  rw [ramificationHeight_eq hπ hv₁, WithTop.coe_eq_coe]
  exact_mod_cast h

variable {I} in
lemma IsRamificationPolygon.lowerConvexEnvelope_pow_le (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hk : k ≤ I.w) (hv : I.IsVertex k) :
    lowerConvexEnvelope (ramificationHeight g π) (p ^ (I.w - k)) ≤
      (((I.ramificationIndex * I.mean k : ℚ) : ℝ) : WithTop ℝ) :=
  (lowerConvexEnvelope_le isAdmissible_ramificationHeight _).trans_eq <|
    hP.ramificationHeight_pow hπ hk hv

variable {I} in
/-- **The ramification polynomial has integral coefficients**: if the ramification polygon of `g`
at a uniformiser `π`, a root of `g`, is the polygon of a Herbrand invariant, then `π ^ e` divides
`g(π x + π)` in `S[X]`, so that the ramification polynomial `ρ(x) = π ^ (-e) g(π x + π)` lies in
`S[X]`. -/
lemma IsRamificationPolygon.C_pow_dvd_mongeShift (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hroot : aeval π g = 0) : C (π ^ g.natDegree) ∣ mongeShift g π 0 := by
  refine (C_dvd_iff_dvd_coeff _ _).mpr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [coeff_zero_eq_eval_zero, eval_mongeShift, mul_zero, add_zero, hroot]
    exact dvd_zero _
  · rw [pow_dvd_iff_le_addVal hπ, addVal_coeff_mongeShift n hπ, zero_add, one_mul]
    rcases eq_or_ne (addVal S ((taylor π (g.map (algebraMap R S))).coeff n)) ⊤ with h | h
    · rw [h, top_add]
      exact le_top
    · rcases ENat.ne_top_iff_exists.mp h with ⟨v, hv⟩
      have hle : (I.ramificationIndex : ℚ) * (I.swanSlope 0 + 1) ≤ v + n + n * I.ram 0 :=
        hP.le_addVal I.w.zero_le hn hv.symm
      have hle' : I.ramificationIndex ≤ v + n := by
        rw [swanSlope, Finset.range_zero, Finset.sum_empty, I.ram_zero] at hle
        exact_mod_cast (by linarith : (I.ramificationIndex : ℚ) ≤ v + n)
      rw [← hv, hP.natDegree_eq]
      exact_mod_cast hle'

variable {I} in
lemma IsRamificationPolygon.isSupportingLine_lowerConvexEnvelope (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hroot : aeval π g = 0) (hk : k ≤ I.w) : IsSupportingLine
      (lowerConvexEnvelope (ramificationHeight g π)) (-(I.ram k : ℝ))
      ((I.ramificationIndex * I.swanSlope k : ℚ) : ℝ) := by
  have hle : (fun m : ℕ ↦ if m ∈ Set.Icc 1 I.ramificationIndex then
      ((((I.ramificationIndex * I.swanSlope k : ℚ) : ℝ) + -(I.ram k : ℝ) * m : ℝ) : WithTop ℝ)
      else ⊤) ≤ ramificationHeight g π := by
    intro m
    beta_reduce
    split_ifs with hm
    · rw [← Rat.cast_natCast m, ← I.cast_ramificationLine]
      exact hP.ramificationLine_le hπ hk (Nat.one_le_iff_ne_zero.mp hm.1)
    · rcases Nat.eq_zero_or_pos m with rfl | hm₀
      · exact (ramificationHeight_zero hroot).ge
      · exact (ramificationHeight_of_natDegree_lt <| hP.natDegree_eq.trans_lt <|
          not_le.mp fun h ↦ hm ⟨hm₀, h⟩).ge
  intro n
  refine (le_lowerConvexEnvelope (isConvexSeq_affine_ite Set.ordConnected_Icc _ _) hle n).trans' ?_
  split_ifs
  · exact le_rfl
  · exact le_top

variable {I} in
lemma IsRamificationPolygon.lowerConvexEnvelope_eq_ramificationLine
    (hP : I.IsRamificationPolygon g π) (hπ : Irreducible π) (hroot : aeval π g = 0) {i l : ℕ}
    (hk : k ≤ I.w) (hin : i ≤ n) (hnl : n ≤ l)
    (hi : lowerConvexEnvelope (ramificationHeight g π) i ≤
      (((I.ramificationLine k i : ℚ) : ℝ) : WithTop ℝ))
    (hl : lowerConvexEnvelope (ramificationHeight g π) l ≤
      (((I.ramificationLine k l : ℚ) : ℝ) : WithTop ℝ)) :
    lowerConvexEnvelope (ramificationHeight g π) n =
      (((I.ramificationLine k n : ℚ) : ℝ) : WithTop ℝ) := by
  have hs : IsSupportingLine (lowerConvexEnvelope (ramificationHeight g π)) (-(I.ram k : ℝ))
      ((I.ramificationIndex * I.swanSlope k : ℚ) : ℝ) :=
    hP.isSupportingLine_lowerConvexEnvelope hπ hroot hk
  rw [I.cast_ramificationLine, Rat.cast_natCast] at hi hl ⊢
  exact ((isConvexSeq_lowerConvexEnvelope _).ordConnected_supportingFace hs).out
    (hi.antisymm (hs i)) (hl.antisymm (hs l)) ⟨hin, hnl⟩

variable {I} in
lemma IsRamificationPolygon.lowerConvexEnvelope_eq_zero_of_pow_le (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hg : g.Monic) (hroot : aeval π g = 0) (hn : p ^ I.w ≤ n)
    (hn' : n ≤ I.ramificationIndex) : lowerConvexEnvelope (ramificationHeight g π) n = 0 := by
  have hi : lowerConvexEnvelope (ramificationHeight g π) (p ^ I.w) ≤
      (((I.ramificationLine 0 (p ^ I.w : ℕ) : ℚ) : ℝ) : WithTop ℝ) :=
    (hP.lowerConvexEnvelope_pow_le hπ I.w.zero_le I.isVertex_zero).trans_eq <| by
      rw [I.mean_zero, mul_zero, I.ramificationLine_zero]
  have hl : lowerConvexEnvelope (ramificationHeight g π) I.ramificationIndex ≤
      (((I.ramificationLine 0 I.ramificationIndex : ℚ) : ℝ) : WithTop ℝ) :=
    (lowerConvexEnvelope_le isAdmissible_ramificationHeight _).trans_eq <| by
      rw [← hP.natDegree_eq, ramificationHeight_natDegree hπ hg, I.ramificationLine_zero,
        Rat.cast_zero, WithTop.coe_zero]
  rw [hP.lowerConvexEnvelope_eq_ramificationLine hπ hroot I.w.zero_le hn hn' hi hl,
    I.ramificationLine_zero, Rat.cast_zero, WithTop.coe_zero]

variable [Fact p.Prime]

lemma ramificationLine_succ_sub (hk : k < I.w) : I.ramificationLine (k + 1) x -
    I.ramificationLine k x = (I.ram (k + 1) - I.ram k) * (p ^ (I.w - k) - x) := by
  have hs : I.swanSlope (k + 1) = I.swanSlope k + (I.ram (k + 1) - I.ram k) / (I.ε * p ^ k) :=
    Finset.sum_range_succ _ _
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hε : (I.ε : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr I.ε_pos.ne'
  have hpow : (p : ℚ) ^ I.w = p ^ k * p ^ (I.w - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk.le]
  rw [ramificationLine, ramificationLine, hs, HerbrandInvariant.ramificationIndex]
  push_cast
  rw [hpow]
  field_simp
  ring1

lemma ramificationLine_pow (hk : k ≤ I.w) :
    I.ramificationLine k (p ^ (I.w - k)) = I.ramificationIndex * I.mean k := by
  rw [ramificationLine, I.mul_swanSlope_eq hk, polygonLine]
  ring1

lemma ramificationLine_succ_pow (hk : k < I.w) :
    I.ramificationLine (k + 1) (p ^ (I.w - k)) = I.ramificationIndex * I.mean k := by
  rw [← I.ramificationLine_pow hk.le, ← sub_eq_zero, I.ramificationLine_succ_sub hk, sub_self,
    mul_zero]

lemma ramificationLine_succ_of_not_isVertex (hk : k < I.w) (hv : ¬I.IsVertex k) :
    I.ramificationLine (k + 1) x = I.ramificationLine k x := by
  have hr : I.ram (k + 1) = I.ram k :=
    (not_lt.mp fun h ↦ hv <| .inr h).antisymm <| I.monotone_ram k.le_succ
  rw [← sub_eq_zero, I.ramificationLine_succ_sub hk, hr, sub_self, zero_mul]

lemma exists_isVertex_ge (hk : k ≤ I.w) : ∃ k₁, k ≤ k₁ ∧ k₁ ≤ I.w ∧ I.IsVertex k₁ ∧
    ∀ y, I.ramificationLine k₁ y = I.ramificationLine k y := by
  refine Nat.decreasingInduction (fun j hj ih ↦ ?_) ⟨I.w, le_rfl, le_rfl, .inl rfl, fun _ ↦ rfl⟩ hk
  by_cases hv : I.IsVertex j
  · exact ⟨j, le_rfl, hj.le, hv, fun _ ↦ rfl⟩
  · rcases ih with ⟨k₁, h₁, h₂, h₃, h₄⟩
    exact ⟨k₁, j.le_succ.trans h₁, h₂, h₃, fun y ↦
      (h₄ y).trans <| I.ramificationLine_succ_of_not_isVertex hj hv⟩

lemma exists_isVertex_lt (hk₀ : k ≠ 0) (hk : k ≤ I.w) :
    ∃ k₀ < k, I.IsVertex k₀ ∧ ∀ y, I.ramificationLine (k₀ + 1) y = I.ramificationLine k y := by
  induction k with
  | zero => exact absurd rfl hk₀
  | succ j ih =>
    by_cases hv : I.IsVertex j
    · exact ⟨j, j.lt_succ_self, hv, fun _ ↦ rfl⟩
    · rcases ih (fun h ↦ hv <| h ▸ I.isVertex_zero) (j.le_succ.trans hk) with ⟨k₀, h₀, h₁, h₂⟩
      exact ⟨k₀, h₀.trans j.lt_succ_self, h₁, fun y ↦
        (h₂ y).trans (I.ramificationLine_succ_of_not_isVertex hk hv).symm⟩

private lemma mem_Icc_ramificationIndex_of_le_of_le (hn : p ^ (I.w - (j + 1)) ≤ n)
    (hn' : n ≤ p ^ (I.w - j)) : n ∈ Set.Icc 1 I.ramificationIndex :=
  ⟨(Nat.one_le_pow _ _ (Fact.out : p.Prime).pos).trans hn, hn'.trans <|
    (Nat.pow_le_pow_right (Fact.out : p.Prime).pos <| I.w.sub_le j).trans <|
      Nat.le_mul_of_pos_left _ I.ε_pos⟩

lemma ramificationPolygon_of_pow_le (hn : p ^ I.w ≤ n) (hn' : n ≤ I.ramificationIndex) :
    I.ramificationPolygon n = 0 := by
  have hp : p.Prime := Fact.out
  rw [ramificationPolygon, ite_eq_left ⟨(Nat.one_le_pow _ _ hp.pos).trans hn, hn'⟩,
    Nat.sub_eq_zero_of_le (Nat.le_log_of_pow_le hp.one_lt hn), ramificationLine_zero,
    Rat.cast_zero, WithTop.coe_zero]

lemma ramificationPolygon_of_le_of_le (hj : j < I.w) (hn : p ^ (I.w - (j + 1)) ≤ n)
    (hn' : n ≤ p ^ (I.w - j)) :
    I.ramificationPolygon n = (((I.ramificationLine (j + 1) n : ℚ) : ℝ) : WithTop ℝ) := by
  have hp : p.Prime := Fact.out
  rw [ramificationPolygon, ite_eq_left (I.mem_Icc_ramificationIndex_of_le_of_le hn hn')]
  rcases hn'.lt_or_eq with hlt | rfl
  · rw [Nat.log_eq_of_pow_le_of_lt_pow hn (by rwa [(by omega : I.w - (j + 1) + 1 = I.w - j)]),
      (by omega : I.w - (I.w - (j + 1)) = j + 1)]
  · rw [Nat.log_pow hp.one_lt, (by omega : I.w - (I.w - j) = j), Nat.cast_pow,
      I.ramificationLine_pow hj.le, I.ramificationLine_succ_pow hj]

/-- **The vertices of the ramification polygon of a Herbrand invariant**: its height at
`p ^ (w - k)` is `e m_k`, for `0 ≤ k ≤ w` and the mean `m_k`. -/
lemma ramificationPolygon_pow (hk : k ≤ I.w) : I.ramificationPolygon (p ^ (I.w - k)) =
    (((I.ramificationIndex * I.mean k : ℚ) : ℝ) : WithTop ℝ) := by
  have hp : p.Prime := Fact.out
  rcases k with _ | j
  · rw [Nat.sub_zero, I.ramificationPolygon_of_pow_le le_rfl (Nat.le_mul_of_pos_left _ I.ε_pos),
      I.mean_zero, mul_zero, Rat.cast_zero, WithTop.coe_zero]
  · rw [I.ramificationPolygon_of_le_of_le hk le_rfl (Nat.pow_le_pow_right hp.pos <| by omega),
      Nat.cast_pow, I.ramificationLine_pow hk]

/-- **The slopes of the ramification polygon of a Herbrand invariant are the negatives of its
rams**: on `[p ^ (w - k), p ^ (w - k + 1)]`, for `1 ≤ k ≤ w`, the slope is `-r_k`. The LMFDB's
polygon is the reflection through the vertical axis, where this slope is `r_k`. -/
lemma unitSlope_ramificationPolygon (hj : j < I.w) (hn : p ^ (I.w - (j + 1)) ≤ n)
    (hn' : n < p ^ (I.w - j)) : unitSlope I.ramificationPolygon n = -I.ram (j + 1) := by
  rw [unitSlope_def, I.ramificationPolygon_of_le_of_le hj (hn.trans <| Nat.le_add_right n 1)
    (Nat.add_one_le_iff.mpr hn'), I.ramificationPolygon_of_le_of_le hj hn hn'.le,
    WithTop.untop₀_coe, WithTop.untop₀_coe, ramificationLine, ramificationLine]
  push_cast
  ring1

/-- **The tame part of the ramification polygon of a Herbrand invariant is horizontal**: on
`[p ^ w, e]`, which is not a point when `ε > 1`, the slope is `0`, which is not a ram. -/
lemma unitSlope_ramificationPolygon_of_pow_le (hn : p ^ I.w ≤ n) (hn' : n < I.ramificationIndex) :
    unitSlope I.ramificationPolygon n = 0 := by
  rw [unitSlope_def, I.ramificationPolygon_of_pow_le (hn.trans <| Nat.le_add_right n 1)
    (Nat.add_one_le_iff.mpr hn'), I.ramificationPolygon_of_pow_le hn hn'.le, sub_self]

/-- **For `ε > 1` the ramification polygon of a Herbrand invariant has the slope `0`**, at
`p ^ w`: so its slopes are not all negatives of rams, which are positive, and LMFDB
`lf.family_diagrams` and `lf.ramification_polygon` need "nonzero slopes" for "slopes". -/
lemma unitSlope_ramificationPolygon_pow_of_one_lt (hε : 1 < I.ε) :
    unitSlope I.ramificationPolygon (p ^ I.w) = 0 :=
  I.unitSlope_ramificationPolygon_of_pow_le le_rfl <|
    lt_mul_of_one_lt_left (pow_pos (Fact.out : p.Prime).pos _) hε

/-- **The rams are the negatives of the slopes of the ramification polygon**: the slopes of the
ramification polygon of `I = (r_1, …, r_w)_ε^f` from `p ^ (w - k)` to `p ^ (w - k + 1)`, for
`k = 1, …, w`, are `-r_1, …, -r_w`. -/
lemma map_neg_unitSlope_ramificationPolygon :
    (Multiset.range I.w).map (fun j ↦ -unitSlope I.ramificationPolygon (p ^ (I.w - (j + 1)))) =
      (Multiset.range I.w).map fun j ↦ (I.ram (j + 1) : ℝ) := by
  refine Multiset.map_congr rfl fun j hj ↦ ?_
  have hj' : j < I.w := Multiset.mem_range.mp hj
  rw [I.unitSlope_ramificationPolygon hj' le_rfl <|
    Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt <| by omega, neg_neg]

private lemma exists_pow_le_and_lt_pow (hn : n ≠ 0) (hn' : n < p ^ I.w) :
    ∃ j < I.w, p ^ (I.w - (j + 1)) ≤ n ∧ n < p ^ (I.w - j) ∧ j + 1 = I.w - Nat.log p n := by
  have hlog : Nat.log p n < I.w := Nat.log_lt_of_lt_pow hn hn'
  refine ⟨I.w - (Nat.log p n + 1), by omega, ?_, ?_, by omega⟩
  · rw [(by omega : I.w - (I.w - (Nat.log p n + 1) + 1) = Nat.log p n)]
    exact Nat.pow_log_le_self p hn
  · rw [(by omega : I.w - (I.w - (Nat.log p n + 1)) = Nat.log p n + 1)]
    exact Nat.lt_pow_succ_log_self (Fact.out : p.Prime).one_lt n

/-- **Every slope of the ramification polygon of a Herbrand invariant is the negative of a ram, or
`0`**: for `1 ≤ n < e`, the slope at `n` is `-r_k` for the index `k = w - ⌊log_p n⌋` with
`p ^ (w - k) ≤ n < p ^ (w - k + 1)`, where `k = 0` and `r_0 = 0` for `n ≥ p ^ w`. -/
lemma unitSlope_ramificationPolygon_eq_neg_ram (hn : n ≠ 0) (hn' : n < I.ramificationIndex) :
    unitSlope I.ramificationPolygon n = -I.ram (I.w - Nat.log p n) := by
  rcases lt_or_ge n (p ^ I.w) with hlt | hge
  · rcases I.exists_pow_le_and_lt_pow hn hlt with ⟨j, hj, h₁, h₂, hjl⟩
    rw [I.unitSlope_ramificationPolygon hj h₁ h₂, hjl]
  · rw [I.unitSlope_ramificationPolygon_of_pow_le hge hn',
      Nat.sub_eq_zero_of_le (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hge), I.ram_zero,
      Rat.cast_zero, neg_zero]

/-- **The slope `0` of the ramification polygon of a Herbrand invariant is its tame part**: for
`1 ≤ n < e`, the slope at `n` is `0` exactly when `p ^ w ≤ n`. So the polygon has a segment of
slope `0`, from `p ^ w` to `e`, exactly when `ε > 1`. -/
lemma unitSlope_ramificationPolygon_eq_zero_iff (hn : n ≠ 0) (hn' : n < I.ramificationIndex) :
    unitSlope I.ramificationPolygon n = 0 ↔ p ^ I.w ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ I.unitSlope_ramificationPolygon_of_pow_le h hn'⟩
  by_contra hlt
  have hlog : Nat.log p n < I.w := Nat.log_lt_of_lt_pow hn (not_le.mp hlt)
  rw [I.unitSlope_ramificationPolygon_eq_neg_ram hn hn', neg_eq_zero, Rat.cast_eq_zero] at h
  exact (I.ram_pos (by omega) (I.w.sub_le _)).ne' h

/-- **The nonzero slopes of the ramification polygon of a Herbrand invariant are its rams**: the
nonzero slopes of the reflection through the vertical axis of the ramification polygon of
`I = (r_1, …, r_w)_ε^f`, on its edges from `n` to `n + 1` for `1 ≤ n < e`, are `r_1, …, r_w`. The
slope `0`, which occurs when `ε > 1`, is not a ram. -/
lemma setOf_neg_unitSlope_ramificationPolygon_ne_zero :
    {s : ℝ | s ≠ 0 ∧ ∃ n ∈ Set.Ico 1 I.ramificationIndex, -unitSlope I.ramificationPolygon n = s} =
      {s | ∃ j < I.w, (I.ram (j + 1) : ℝ) = s} := by
  have hp : p.Prime := Fact.out
  refine Set.ext fun s ↦ ⟨?_, ?_⟩
  · rintro ⟨hs, n, hn, rfl⟩
    rw [I.unitSlope_ramificationPolygon_eq_neg_ram (Nat.one_le_iff_ne_zero.mp hn.1) hn.2,
      neg_neg] at hs ⊢
    have hk : I.w - Nat.log p n ≠ 0 := fun h ↦ hs <| by rw [h, I.ram_zero, Rat.cast_zero]
    exact ⟨I.w - Nat.log p n - 1, by omega,
      by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]⟩
  · rintro ⟨j, hj, rfl⟩
    have hlt : p ^ (I.w - (j + 1)) < p ^ (I.w - j) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact ⟨(Rat.cast_pos.mpr <| I.ram_pos j.succ_ne_zero hj).ne', p ^ (I.w - (j + 1)),
      ⟨Nat.one_le_pow _ _ hp.pos,
        hlt.trans_le (I.mem_Icc_ramificationIndex_of_le_of_le hlt.le le_rfl).2⟩,
      by rw [I.unitSlope_ramificationPolygon hj le_rfl hlt, neg_neg]⟩

variable {I}

lemma IsRamificationPolygon.lowerConvexEnvelope_eq_of_le_of_le (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hroot : aeval π g = 0) (hj : j < I.w) (hn : p ^ (I.w - (j + 1)) ≤ n)
    (hn' : n ≤ p ^ (I.w - j)) : lowerConvexEnvelope (ramificationHeight g π) n =
    (((I.ramificationLine (j + 1) n : ℚ) : ℝ) : WithTop ℝ) := by
  have hp : p.Prime := Fact.out
  rcases I.exists_isVertex_ge hj with ⟨k₁, h₁, h₁w, hv₁, hL₁⟩
  rcases I.exists_isVertex_lt j.succ_ne_zero hj with ⟨k₀, h₀, hv₀, hL₀⟩
  have hk₀ : k₀ < I.w := h₀.trans_le hj
  refine hP.lowerConvexEnvelope_eq_ramificationLine hπ hroot hj
    ((Nat.pow_le_pow_right hp.pos (by omega : I.w - k₁ ≤ I.w - (j + 1))).trans hn)
    (hn'.trans <| Nat.pow_le_pow_right hp.pos (by omega : I.w - j ≤ I.w - k₀)) ?_ ?_
  · rw [← hL₁, Nat.cast_pow, I.ramificationLine_pow h₁w]
    exact hP.lowerConvexEnvelope_pow_le hπ h₁w hv₁
  · rw [← hL₀, Nat.cast_pow, I.ramificationLine_succ_pow hk₀]
    exact hP.lowerConvexEnvelope_pow_le hπ hk₀.le hv₀

/-- **The ramification polygon is the polygon of the Herbrand invariant** (LMFDB
`lf.ramification_polygon`): let `g` be a monic polynomial over `R` with a root `π`, a uniformiser
of the discrete valuation ring `S`, whose ramification polygon is the polygon of the Herbrand
invariant `I` in the sense of `IsRamificationPolygon` (Monge's Proposition 1 and Lemma 1). Then
the lower convex hull of the points `(n, v_S(ρ_n))`, for the coefficients `ρ_n ≠ 0` of the
ramification polynomial `ρ(x) = π ^ (-e) g(π x + π)`, is the ramification polygon of `I`: it has
the vertices `(p ^ (w - k), e m_k)` and `(e, 0)`, and its slopes are the `-r_k` and, on
`[p ^ w, e]`, `0`. -/
lemma IsRamificationPolygon.lowerConvexEnvelope_eq (hP : I.IsRamificationPolygon g π)
    (hπ : Irreducible π) (hg : g.Monic) (hroot : aeval π g = 0) :
    lowerConvexEnvelope (ramificationHeight g π) = I.ramificationPolygon := by
  funext n
  by_cases hn : n ∈ Set.Icc 1 I.ramificationIndex
  · rcases lt_or_ge n (p ^ I.w) with hlt | hge
    · rcases I.exists_pow_le_and_lt_pow (Nat.one_le_iff_ne_zero.mp hn.1) hlt with
        ⟨j, hj, h₁, h₂, -⟩
      rw [hP.lowerConvexEnvelope_eq_of_le_of_le hπ hroot hj h₁ h₂.le,
        I.ramificationPolygon_of_le_of_le hj h₁ h₂.le]
    · rw [hP.lowerConvexEnvelope_eq_zero_of_pow_le hπ hg hroot hge hn.2,
        I.ramificationPolygon_of_pow_le hge hn.2]
  · rw [ramificationPolygon, ite_eq_right hn]
    rcases Nat.eq_zero_or_pos n with rfl | hn₀
    · exact lowerConvexEnvelope_eq_top_of_forall_le fun i hi ↦
        Nat.le_zero.mp hi ▸ ramificationHeight_zero hroot
    · exact lowerConvexEnvelope_eq_top_of_forall_ge fun m hm ↦
        ramificationHeight_of_natDegree_lt <| hP.natDegree_eq.trans_lt <|
          (not_le.mp fun h ↦ hn ⟨hn₀, h⟩).trans_le hm

end IsNonarchimedeanLocalField.HerbrandInvariant
