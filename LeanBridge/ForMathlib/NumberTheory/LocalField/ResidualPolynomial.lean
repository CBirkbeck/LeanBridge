import LeanBridge.ForMathlib.Analysis.Convex.EdgeOfSlopeEnds
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolynomial

/-!
# Residual polynomials of the segments of the ramification polygon

Let `L` be a nonarchimedean local field, `α` a uniformiser of `L` and `ρ(x) = ∑_i ρ_i x ^ i` a
polynomial over `L`, such as the ramification polynomial `α ^ (-n) φ(α x + α)` of the minimal
polynomial `φ` of `α` over a subfield (LMFDB `lf.ramification_polygon`). Let `S` be a segment of
the ramification polygon, the lower convex hull of the points `(-i, v_L(ρ_i))`, with endpoints
`(-k - l, v_L(ρ_{k + l}))` and `(-k, v_L(ρ_k))` and slope
`h / m = (v_L(ρ_k) - v_L(ρ_{k + l})) / l` in lowest terms. Its **residual polynomial** (LMFDB
`lf.residual_polynomials`) is `A(x) = ∑_{j = 0}^{l / m} (ρ_{j m + k} α ^ (j h - v_L(ρ_k)))‾ x ^ j`
over the residue field `L̲`, where `δ‾` is the image of `δ ∈ 𝒪_L` in `L̲`.

This file defines the residual polynomial of a segment, exactly as the knowl writes it, the
segments `S_1, …, S_ℓ` of the ramification polygon, numbered from the right as in Pauli and Sinclair
(*Enumerating extensions of (π)-adic fields with given invariants*, Theorem 4.8), the list of their
residual polynomials, and the knowl's equivalence class
`𝒜 = {(γ_{δ,1} A_1(δ^{h_1} x), …, γ_{δ,ℓ} A_ℓ(δ^{h_ℓ} x)) : δ ∈ K̲ ^ ×}` of the list, with
`γ_{δ,ℓ} = δ ^ (-h_ℓ deg A_ℓ)` and `γ_{δ,i} = γ_{δ,i+1} δ ^ (-h_i deg A_i)`. The segments are read
off Tau Ceti's lower convex envelope of the heights `v_L(ρ_i)`: they are the segments of the
ramification polygon (`IsNonarchimedeanLocalField.mem_polygonEdges_ramificationPolygonOf_iff`),
their ends are points `(-i, v_L(ρ_i))`, and each one starts where the previous one ends. The
residual polynomial of a segment then has its coefficients in `𝒪_L` before reduction, degree `l / m`
and nonzero constant term, and the constant term of each residual polynomial is the leading
coefficient of the one of the segment to its left, the next one in the left-to-right order of the
LMFDB's diagram (LMFDB `lf.ramification_polygon_display`).

## Main definitions

* `IsNonarchimedeanLocalField.residueOf`: the reduction `𝒪_L → L̲`, extended by `0` to `L`.
* `IsNonarchimedeanLocalField.residualPolynomial` (LMFDB `lf.residual_polynomials`): the residual
  polynomial of a segment.
* `IsNonarchimedeanLocalField.residualSegments` (LMFDB `lf.residual_polynomials`): the segments
  `S_1, …, S_ℓ` of the ramification polygon, from the right.
* `IsNonarchimedeanLocalField.residualPolynomials` (LMFDB `lf.residual_polynomials`): the list of
  the residual polynomials of the segments.
* `IsNonarchimedeanLocalField.residualPolynomialClass` (LMFDB `lf.residual_polynomials`): the
  equivalence class `𝒜` of the list of residual polynomials.

## Main results

* `IsNonarchimedeanLocalField.mem_polygonEdges_ramificationPolygonOf_iff` (LMFDB
  `lf.residual_polynomials`): the segments `S_1, …, S_ℓ` are the segments of the ramification
  polygon, with the endpoints `(-k - l, v_L(ρ_{k + l}))` and `(-k, v_L(ρ_k))`.
* `IsNonarchimedeanLocalField.residualSegments_succ_fst` and
  `IsNonarchimedeanLocalField.residualSlope_lt_residualSlope`: each segment starts where the
  previous one ends, and the slopes decrease from the right to the left.
* `IsNonarchimedeanLocalField.mem_integer_residualPolynomial` (LMFDB `lf.residual_polynomials`):
  the elements reduced in the residual polynomial of a segment lie in `𝒪_L`.
* `IsNonarchimedeanLocalField.natDegree_residualPolynomial` and
  `IsNonarchimedeanLocalField.coeff_zero_residualPolynomial_ne_zero`: the residual polynomial of a
  segment of length `l` and slope `h / m` has degree `l / m` and a nonzero constant term.
* `IsNonarchimedeanLocalField.coeff_zero_residualPolynomials_succ` (LMFDB
  `lf.ramification_polygon_display`): the constant term of each residual polynomial is the leading
  coefficient of the next one, from the left.

## References

* O. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. 99 (1928).
* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017); arXiv:1504.06671, Definition 4.1 and Theorem 4.8.
-/

open Polynomial TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] {F : Type*} [Field F] {ρ : L[X]} {α x y : L}
  {i k l n : ℕ} {ϖ : 𝒪[L]} {kl : ℕ × ℕ} {s : ℝ}

lemma addValuation_of_ne_zero (hx : x ≠ 0) :
    addValuation L x = (normalizedValuation L (Units.mk0 x hx)).toAdd :=
  dite_eq_right hx

lemma mem_integer_iff_zero_le_addValuation (hx : x ≠ 0) : x ∈ 𝒪[L] ↔ 0 ≤ addValuation L x := by
  rw [addValuation_of_ne_zero hx, WithTop.coe_nonneg]
  exact mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 x hx)

variable (x y) in
lemma min_addValuation_le_addValuation_add :
    min (addValuation L x) (addValuation L y) ≤ addValuation L (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [addValuation_zero, zero_add, min_eq_right le_top]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [addValuation_zero, add_zero, min_eq_left le_top]
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · rw [hxy, addValuation_zero]
    exact le_top
  rw [addValuation_of_ne_zero hx, addValuation_of_ne_zero hy, addValuation_of_ne_zero hxy,
    ← WithTop.coe_min, WithTop.coe_le_coe]
  rcases le_total (valuation L x) (valuation L y) with h | h
  · refine min_le_of_right_le ((toAdd_normalizedValuation_le_iff_valuation_le _ _).mpr ?_)
    exact (Valuation.map_add _ _ _).trans (max_le h le_rfl)
  · refine min_le_of_left_le ((toAdd_normalizedValuation_le_iff_valuation_le _ _).mpr ?_)
    exact (Valuation.map_add _ _ _).trans (max_le le_rfl h)

lemma addValuation_zpow (hϖ : Irreducible ϖ) (z : ℤ) : addValuation L ((ϖ : L) ^ z) = z := by
  have hϖ₀ : (ϖ : L) ≠ 0 :=
    fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hmk : Units.mk0 ((ϖ : L) ^ z) (zpow_ne_zero z hϖ₀) = Units.mk0 (ϖ : L) hϖ₀ ^ z :=
    Units.ext (by rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0])
  rw [addValuation_of_ne_zero (zpow_ne_zero z hϖ₀), hmk, map_zpow,
    normalizedValuation_irreducible hϖ]
  simp

lemma addValuation_mul_zpow (hϖ : Irreducible ϖ) (hx : x ≠ 0) (z : ℤ) :
    addValuation L (x * (ϖ : L) ^ z) = addValuation L x + z := by
  rw [addValuation_mul hx (zpow_ne_zero z fun h ↦ hϖ.ne_zero (Subtype.ext h)), addValuation_zpow hϖ]

lemma addValuation_coe_unit (u : 𝒪[L]ˣ) : addValuation L ((u : 𝒪[L]) : L) = 0 := by
  rw [addValuation_coe (IsDiscreteValuationRing.addVal_eq_zero_of_unit u)]
  rfl

lemma residue_eq_zero_of_pos {z : 𝒪[L]} (hz : 0 < addValuation L (z : L)) :
    IsLocalRing.residue 𝒪[L] z = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  rw [← hu.unit_spec, addValuation_coe_unit] at hz
  exact lt_irrefl _ hz

open Classical in
variable (L) in
/-- The **reduction** `δ ↦ δ‾` of the ring of integers `𝒪_L` of a nonarchimedean local field onto
its residue field `L̲`, extended by `0` to the elements of `L` outside `𝒪_L` (a junk value: the
residual polynomials only reduce elements of `𝒪_L`). -/
noncomputable def residueOf (x : L) : 𝓀[L] :=
  if h : x ∈ 𝒪[L] then IsLocalRing.residue 𝒪[L] ⟨x, h⟩ else 0

lemma residueOf_coe (z : 𝒪[L]) : residueOf L (z : L) = IsLocalRing.residue 𝒪[L] z :=
  dite_eq_left z.2

lemma residueOf_mul (hx : x ∈ 𝒪[L]) (hy : y ∈ 𝒪[L]) :
    residueOf L (x * y) = residueOf L x * residueOf L y := by
  rw [residueOf, dite_eq_left (mul_mem hx hy), residueOf, dite_eq_left hx, residueOf,
    dite_eq_left hy, ← map_mul]
  rfl

lemma residueOf_eq_of_pos (hx : x ∈ 𝒪[L]) (hy : y ∈ 𝒪[L]) (hxy : 0 < addValuation L (x - y)) :
    residueOf L x = residueOf L y := by
  rw [residueOf, dite_eq_left hx, residueOf, dite_eq_left hy, ← sub_eq_zero, ← map_sub]
  exact residue_eq_zero_of_pos hxy

lemma coe_units_zpow {M : Type*} [Field M] (S : Subring M) (u : Sˣ) (z : ℤ) :
    ((u : S) : M) ^ z = (((u ^ z : Sˣ) : S) : M) :=
  ((congrArg Units.val (map_zpow (Units.map S.subtype.toMonoidHom) u z)).trans
    (Units.val_zpow_eq_zpow_val _ z)).symm

lemma residueOf_unit_zpow (u : 𝒪[L]ˣ) (z : ℤ) :
    residueOf L (((u : 𝒪[L]) : L) ^ z) = IsLocalRing.residue 𝒪[L] u ^ z := by
  rw [coe_units_zpow, residueOf_coe]
  exact (congrArg Units.val (map_zpow (Units.map (IsLocalRing.residue 𝒪[L]).toMonoidHom) u z)).trans
    (Units.val_zpow_eq_zpow_val _ z)

variable (ρ i) in
/-- The valuation `v_L(ρ_i)` of the coefficient of `x ^ i` of a polynomial `ρ` over `L`, as an
integer, and `0` when `ρ_i = 0`. -/
noncomputable def coeffVal : ℤ :=
  (addValuation L (ρ.coeff i)).untop₀

lemma addValuation_coeff (hρ : ρ.coeff i ≠ 0) : addValuation L (ρ.coeff i) = coeffVal ρ i :=
  (WithTop.coe_untop₀_of_ne_top (mt addValuation_eq_top_iff.mp hρ)).symm

lemma coeffHeight_of_coeff_ne_zero (hρ : ρ.coeff i ≠ 0) : coeffHeight ρ i = (coeffVal ρ i : ℝ) := by
  rw [coeffHeight_apply, addValuation_coeff hρ, WithTop.map_coe]

lemma untop₀_coeffHeight : (coeffHeight ρ i).untop₀ = coeffVal ρ i := by
  rcases eq_or_ne (ρ.coeff i) 0 with hρ | hρ
  · rw [(coeffHeight_eq_top_iff.mpr hρ), coeffVal, hρ, addValuation_zero, WithTop.untop₀_top,
      WithTop.untop₀_top, Int.cast_zero]
  · rw [coeffHeight_of_coeff_ne_zero hρ, WithTop.untop₀_coe]

variable (ρ k l) in
/-- The slope `h / m = (v_L(ρ_k) - v_L(ρ_{k + l})) / l` of the segment of the ramification polygon
with endpoints `(-k - l, v_L(ρ_{k + l}))` and `(-k, v_L(ρ_k))`, as a rational number: its numerator
`h` and denominator `m` are the knowl's. -/
noncomputable def residualSlope : ℚ :=
  ((coeffVal ρ k - coeffVal ρ (k + l) : ℤ) : ℚ) / l

variable (ρ α k l) in
/-- The **residual polynomial** (LMFDB `lf.residual_polynomials`, after Ore) of the segment of the
ramification polygon with endpoints `(-k - l, v_L(ρ_{k + l}))` and `(-k, v_L(ρ_k))`, of slope
`h / m = (v_L(ρ_k) - v_L(ρ_{k + l})) / l` in lowest terms:
`A(x) = ∑_{j = 0}^{l / m} (ρ_{j m + k} α ^ (j h - v_L(ρ_k)))‾ x ^ j` over the residue field,
where `‾` is the reduction `IsNonarchimedeanLocalField.residueOf`. -/
noncomputable def residualPolynomial : 𝓀[L][X] :=
  ∑ j ∈ Finset.range (l / (residualSlope ρ k l).den + 1),
    C (residueOf L (ρ.coeff (j * (residualSlope ρ k l).den + k) *
      α ^ ((j : ℤ) * (residualSlope ρ k l).num - coeffVal ρ k))) * X ^ j

variable (ρ) in
/-- The heights of the Newton polygon of `ρ` at the integers: Tau Ceti's lower convex envelope of
the heights `v_L(ρ_i)`. The reflection of its polygon through the vertical axis is the ramification
polygon, when `ρ` is a ramification polynomial. -/
noncomputable abbrev coeffEnvelope : ℕ → WithTop ℝ :=
  lowerConvexEnvelope (coeffHeight ρ)

open Classical in
variable (ρ) in
/-- The slopes of the unit edges of the Newton polygon of `ρ`, the negatives of the slopes of the
segments of the ramification polygon, as a finite set. -/
noncomputable def residualUnitSlopes : Finset ℝ :=
  ((Finset.range (ρ.natDegree + 1)).filter (· ∈ finiteEdges (coeffEnvelope ρ))).image
    (unitSlope (coeffEnvelope ρ))

variable (ρ) in
/-- The slopes of the unit edges of the Newton polygon of `ρ`, in increasing order: the negatives of
the slopes of the segments of the ramification polygon, from the right to the left. -/
noncomputable def residualSlopeList : List ℝ :=
  (residualUnitSlopes ρ).sort

variable (ρ s) in
/-- The segment of the ramification polygon of `ρ` of slope `-s`, as the pair `(k, l)` of the
abscissa `-k` of its right end and its length `l`: the first index `k` of the unit edges of slope
`s` of the Newton polygon, and the number `l` of these edges. -/
noncomputable def residualSegmentOf : ℕ × ℕ :=
  (sInf (slopeIndices (coeffEnvelope ρ) s),
    sSup (slopeIndices (coeffEnvelope ρ) s) + 1 - sInf (slopeIndices (coeffEnvelope ρ) s))

variable (ρ) in
/-- The **segments** `S_1, …, S_ℓ` of the ramification polygon of `ρ` (LMFDB
`lf.residual_polynomials`), numbered from the right as in Pauli and Sinclair, each given by the pair
`(k, l)` of the abscissa `-k` of its right end and its length `l`: the segment `S_i` runs from
`(-k - l, v_L(ρ_{k + l}))` to `(-k, v_L(ρ_k))`, and its slope decreases with `i`. -/
noncomputable def residualSegments : List (ℕ × ℕ) :=
  (residualSlopeList ρ).map (residualSegmentOf ρ)

variable (ρ α) in
/-- The **list of residual polynomials** (LMFDB `lf.residual_polynomials`) `A_1, …, A_ℓ` of the
segments `S_1, …, S_ℓ` of the ramification polygon of `ρ`, numbered from the right. -/
noncomputable def residualPolynomials : List 𝓀[L][X] :=
  (residualSegments ρ).map fun kl ↦ residualPolynomial ρ α kl.1 kl.2

lemma finite_coeffHeight_ne_top : {n | coeffHeight ρ n ≠ ⊤}.Finite :=
  ρ.support.finite_toSet.subset fun _ hn ↦
    Finset.mem_coe.mpr (mem_support_iff.mpr fun h ↦ hn (coeffHeight_eq_top_iff.mpr h))

lemma finite_coeffEnvelope_ne_top : {n | coeffEnvelope ρ n ≠ ⊤}.Finite :=
  finite_lowerConvexEnvelope_ne_top finite_coeffHeight_ne_top

lemma isConvexSeq_coeffEnvelope : IsConvexSeq (coeffEnvelope ρ) :=
  isConvexSeq_lowerConvexEnvelope _

lemma mem_residualUnitSlopes : s ∈ residualUnitSlopes ρ ↔
    s ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ) := by
  classical
  rw [residualUnitSlopes, Finset.mem_image]
  refine ⟨fun ⟨n, hn, hs⟩ ↦ ⟨n, (Finset.mem_filter.mp hn).2, hs⟩, fun ⟨n, hn, hs⟩ ↦
    ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hn⟩, hs⟩⟩
  rcases (lowerConvexEnvelope_ne_top_iff (isAdmissible_of_finite finite_coeffHeight_ne_top)).mp
    hn.1 with ⟨-, -, j, hnj, -, hj⟩
  exact Nat.lt_succ_of_le <| hnj.trans <|
    le_natDegree_of_ne_zero fun h ↦ hj (coeffHeight_eq_top_iff.mpr h)

lemma mem_residualSlopeList :
    s ∈ residualSlopeList ρ ↔ s ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ) :=
  (Finset.mem_sort _).trans mem_residualUnitSlopes

lemma residualSegmentOf_fst : (residualSegmentOf ρ s).1 = sInf (slopeIndices (coeffEnvelope ρ) s) :=
  rfl

lemma residualSegmentOf_fst_add_snd
    (hs : s ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ)) :
    (residualSegmentOf ρ s).1 + (residualSegmentOf ρ s).2 =
      sSup (slopeIndices (coeffEnvelope ρ) s) + 1 := by
  have hle : sInf (slopeIndices (coeffEnvelope ρ) s) ≤ sSup (slopeIndices (coeffEnvelope ρ) s) :=
    sInf_le_sSup_slopeIndices finite_coeffEnvelope_ne_top hs
  rw [residualSegmentOf]
  omega

lemma exists_of_mem_residualSegments (hkl : kl ∈ residualSegments ρ) :
    ∃ s ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ),
      sInf (slopeIndices (coeffEnvelope ρ) s) = kl.1 ∧
        sSup (slopeIndices (coeffEnvelope ρ) s) + 1 = kl.1 + kl.2 := by
  rcases List.mem_map.mp hkl with ⟨s, hs, rfl⟩
  have hs' : s ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ) :=
    mem_residualSlopeList.mp hs
  exact ⟨s, hs', rfl, (residualSegmentOf_fst_add_snd hs').symm⟩

lemma coeffEnvelope_fst_of_mem_residualSegments (hkl : kl ∈ residualSegments ρ) :
    coeffEnvelope ρ kl.1 = coeffHeight ρ kl.1 := by
  rcases exists_of_mem_residualSegments hkl with ⟨s, hs, hK, -⟩
  rw [← hK]
  exact lowerConvexEnvelope_sInf_slopeIndices finite_coeffHeight_ne_top hs

lemma coeffEnvelope_add_of_mem_residualSegments (hkl : kl ∈ residualSegments ρ) :
    coeffEnvelope ρ (kl.1 + kl.2) = coeffHeight ρ (kl.1 + kl.2) := by
  rcases exists_of_mem_residualSegments hkl with ⟨s, hs, -, hU⟩
  rw [← hU]
  exact lowerConvexEnvelope_sSup_slopeIndices_add_one finite_coeffHeight_ne_top hs

lemma coeff_fst_ne_zero_of_mem_residualSegments (hkl : kl ∈ residualSegments ρ) :
    ρ.coeff kl.1 ≠ 0 := by
  rcases exists_of_mem_residualSegments hkl with ⟨s, hs, hK, -⟩
  have h₁ : coeffEnvelope ρ kl.1 ≠ ⊤ := hK ▸ (sInf_mem_slopeIndices hs).1.1
  rw [coeffEnvelope_fst_of_mem_residualSegments hkl] at h₁
  exact fun h ↦ h₁ (coeffHeight_eq_top_iff.mpr h)

lemma coeff_add_ne_zero_of_mem_residualSegments (hkl : kl ∈ residualSegments ρ) :
    ρ.coeff (kl.1 + kl.2) ≠ 0 := by
  rcases exists_of_mem_residualSegments hkl with ⟨s, hs, -, hU⟩
  have h₁ : coeffEnvelope ρ (kl.1 + kl.2) ≠ ⊤ :=
    hU ▸ (sSup_mem_slopeIndices finite_coeffEnvelope_ne_top hs).1.2
  rw [coeffEnvelope_add_of_mem_residualSegments hkl] at h₁
  exact fun h ↦ h₁ (coeffHeight_eq_top_iff.mpr h)

lemma pos_of_mem_residualSegments (hkl : kl ∈ residualSegments ρ) : 0 < kl.2 := by
  rcases exists_of_mem_residualSegments hkl with ⟨s, hs, hK, hU⟩
  have hle : sInf (slopeIndices (coeffEnvelope ρ) s) ≤ sSup (slopeIndices (coeffEnvelope ρ) s) :=
    sInf_le_sSup_slopeIndices finite_coeffEnvelope_ne_top hs
  omega

lemma unitSlope_eq_neg_residualSlope (hkl : kl ∈ residualSegments ρ)
    (hs : s ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ))
    (hK : sInf (slopeIndices (coeffEnvelope ρ) s) = kl.1)
    (hU : sSup (slopeIndices (coeffEnvelope ρ) s) + 1 = kl.1 + kl.2) :
    s = -(residualSlope ρ kl.1 kl.2 : ℝ) := by
  have hle : sInf (slopeIndices (coeffEnvelope ρ) s) ≤ sSup (slopeIndices (coeffEnvelope ρ) s) :=
    sInf_le_sSup_slopeIndices finite_coeffEnvelope_ne_top hs
  have h₁ : (coeffEnvelope ρ (kl.1 + kl.2)).untop₀ =
      (coeffEnvelope ρ kl.1).untop₀ + (((kl.1 + kl.2 : ℕ) : ℝ) - (kl.1 : ℕ)) * s := by
    rw [← hU, ← hK]
    exact untop₀_eq_add_mul isConvexSeq_coeffEnvelope finite_coeffEnvelope_ne_top hs (by omega)
      le_rfl
  rw [coeffEnvelope_add_of_mem_residualSegments hkl, coeffEnvelope_fst_of_mem_residualSegments hkl,
    untop₀_coeffHeight, untop₀_coeffHeight] at h₁
  have hl : (kl.2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pos_of_mem_residualSegments hkl).ne'
  rw [residualSlope]
  push_cast at h₁ ⊢
  field_simp
  linarith

lemma coeffVal_sub_mul_le (hkl : kl ∈ residualSegments ρ) (hn : ρ.coeff n ≠ 0) :
    (coeffVal ρ kl.1 : ℚ) - residualSlope ρ kl.1 kl.2 * ((n : ℚ) - kl.1) ≤ coeffVal ρ n := by
  rcases exists_of_mem_residualSegments hkl with ⟨s, hs, hK, hU⟩
  have h₁ : (((coeffHeight ρ kl.1).untop₀ + ((n : ℝ) - (kl.1 : ℕ)) * s : ℝ) : WithTop ℝ) ≤
      coeffHeight ρ n := by
    rw [← hK]
    exact add_mul_le_of_mem_image_unitSlope n finite_coeffHeight_ne_top hs
  rw [unitSlope_eq_neg_residualSlope hkl hs hK hU, untop₀_coeffHeight,
    coeffHeight_of_coeff_ne_zero hn, WithTop.coe_le_coe] at h₁
  have h₂ : (coeffVal ρ kl.1 : ℝ) - (residualSlope ρ kl.1 kl.2 : ℝ) * ((n : ℝ) - kl.1) ≤
      (coeffVal ρ n : ℝ) := by
    linarith
  exact_mod_cast h₂

/-- **The segments of the ramification polygon** (LMFDB `lf.residual_polynomials`): the segments
of the ramification polygon of `φ` at `α`, the lower convex hull of the points `(-i, v_L(ρ_i))` of
the ramification polynomial `ρ`, are the segments `S_i` from `(-k - l, v_L(ρ_{k + l}))` to
`(-k, v_L(ρ_k))`, for the pairs `(k, l)` of `IsNonarchimedeanLocalField.residualSegments ρ`. So
their ends are points `(-i, v_L(ρ_i))`, as the knowl's notation for a segment says. -/
lemma mem_polygonEdges_ramificationPolygonOf_iff [Algebra F L] {φ : F[X]} {σ : Set (ℝ × ℝ)} :
    σ ∈ polygonEdges (ramificationPolygonOf φ α) ↔
      ∃ kl ∈ residualSegments (ramificationPolynomial φ α),
        segment ℝ (-((kl.1 + kl.2 : ℕ) : ℝ),
          (coeffVal (ramificationPolynomial φ α) (kl.1 + kl.2) : ℝ))
            (-(kl.1 : ℝ), (coeffVal (ramificationPolynomial φ α) kl.1 : ℝ)) = σ := by
  rw [ramificationPolygonOf_eq_image_reflectVertical,
    lowerConvexHull_heightPoints finite_coeffHeight_ne_top, mem_polygonEdges_image_reflectVertical,
    mem_polygonEdges_polygonGraph_iff isConvexSeq_coeffEnvelope finite_coeffEnvelope_ne_top]
  have hedge (s : ℝ) (hs : s ∈ unitSlope (coeffEnvelope (ramificationPolynomial φ α)) ''
      finiteEdges (coeffEnvelope (ramificationPolynomial φ α))) :
      reflectVertical '' edgeOfSlope (coeffEnvelope (ramificationPolynomial φ α)) s =
        segment ℝ
          (-((sSup (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) + 1 : ℕ) : ℝ),
            (coeffVal (ramificationPolynomial φ α)
              (sSup (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) + 1) : ℝ))
          (-((sInf (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) : ℕ) : ℝ),
            (coeffVal (ramificationPolynomial φ α)
              (sInf (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s)) : ℝ)) := by
    have hle : sInf (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) ≤
        sSup (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) :=
      sInf_le_sSup_slopeIndices finite_coeffEnvelope_ne_top hs
    rw [edgeOfSlope, image_reflectVertical_segment, ← untop₀_eq_add_mul isConvexSeq_coeffEnvelope
      finite_coeffEnvelope_ne_top hs
        (n := sSup (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) + 1) (by omega)
          le_rfl, coeffEnvelope, lowerConvexEnvelope_sInf_slopeIndices finite_coeffHeight_ne_top hs,
      lowerConvexEnvelope_sSup_slopeIndices_add_one finite_coeffHeight_ne_top hs,
      untop₀_coeffHeight, untop₀_coeffHeight, reflectVertical_apply, reflectVertical_apply]
  refine ⟨fun ⟨s, hs, heq⟩ ↦ ?_, fun ⟨kl, hkl, heq⟩ ↦ ?_⟩
  · have hle : sInf (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) ≤
        sSup (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) :=
      sInf_le_sSup_slopeIndices finite_coeffEnvelope_ne_top hs
    refine ⟨(sInf (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s),
      sSup (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s) + 1 -
        sInf (slopeIndices (coeffEnvelope (ramificationPolynomial φ α)) s)),
      List.mem_map.mpr ⟨s, mem_residualSlopeList.mpr hs, rfl⟩, ?_⟩
    dsimp only
    rw [Nat.add_sub_cancel' (by omega), ← hedge s hs, heq,
      image_reflectVertical_image_reflectVertical]
  · rcases exists_of_mem_residualSegments hkl with ⟨s, hs, hK, hU⟩
    refine ⟨s, hs, ?_⟩
    rw [← hU, ← hK] at heq
    rw [← heq, ← hedge s hs, image_reflectVertical_image_reflectVertical]

variable (k l) in
lemma residualSlope_den_dvd : (residualSlope ρ k l).den ∣ l := by
  have h₁ : ((Rat.divInt (coeffVal ρ k - coeffVal ρ (k + l)) l).den : ℤ) ∣ (l : ℤ) :=
    Rat.den_dvd _ _
  rw [Rat.divInt_eq_div] at h₁
  exact Int.natCast_dvd_natCast.mp h₁

variable (k) in
lemma num_mul_div_den (hl : l ≠ 0) : (residualSlope ρ k l).num *
    ((l / (residualSlope ρ k l).den : ℕ) : ℤ) = coeffVal ρ k - coeffVal ρ (k + l) := by
  have hden : ((residualSlope ρ k l).den : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (residualSlope ρ k l).den_nz
  have h₁ :
      (((l / (residualSlope ρ k l).den : ℕ) : ℤ) : ℚ) = (l : ℚ) / (residualSlope ρ k l).den := by
    rw [Int.cast_natCast, Nat.cast_div (residualSlope_den_dvd k l) hden]
  have h₂ : ((residualSlope ρ k l).num : ℚ) = residualSlope ρ k l * (residualSlope ρ k l).den :=
    (Rat.mul_den_eq_num _).symm
  have h₃ : residualSlope ρ k l * l = (coeffVal ρ k - coeffVal ρ (k + l) : ℤ) := by
    rw [residualSlope, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hl)]
  exact_mod_cast (by rw [Int.cast_mul, h₁, h₂]; field_simp; exact h₃ :
    (((residualSlope ρ k l).num * ((l / (residualSlope ρ k l).den : ℕ) : ℤ) : ℤ) : ℚ) =
      (coeffVal ρ k - coeffVal ρ (k + l) : ℤ))

lemma coeff_residualPolynomial (j : ℕ) : (residualPolynomial ρ α k l).coeff j =
    if j ≤ l / (residualSlope ρ k l).den then
      residueOf L (ρ.coeff (j * (residualSlope ρ k l).den + k) *
        α ^ ((j : ℤ) * (residualSlope ρ k l).num - coeffVal ρ k)) else 0 := by
  rw [residualPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_add_one_iff]

open Valuation in
lemma residueOf_ne_zero (hx : x ≠ 0) (h : addValuation L x = 0) : residueOf L x ≠ 0 := by
  have hmem : x ∈ 𝒪[L] :=
    (mem_integer_iff_zero_le_addValuation hx).mpr h.ge
  have hv : valuation L x = 1 := by
    rw [addValuation_of_ne_zero hx, WithTop.coe_eq_zero, toAdd_eq_zero] at h
    exact (normalizedValuation_eq_one_iff (Units.mk0 x hx)).mp h
  have hu : IsUnit (⟨x, hmem⟩ : 𝒪[L]) :=
    (integer.integers (valuation L)).isUnit_iff_valuation_eq_one.mpr hv
  rw [residueOf, dite_eq_left hmem]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu

lemma mem_integer_of_le (hϖ : Irreducible ϖ) {z : ℤ}
    (h : ((-z : ℤ) : WithTop ℤ) ≤ addValuation L x) : x * (ϖ : L) ^ z ∈ 𝒪[L] := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_mul]
    exact zero_mem _
  rw [mem_integer_iff_zero_le_addValuation (mul_ne_zero hx (zpow_ne_zero z fun h ↦
    hϖ.ne_zero (Subtype.ext h))), addValuation_mul_zpow hϖ hx]
  rw [addValuation_of_ne_zero hx] at h ⊢
  rw [← WithTop.coe_add, WithTop.coe_nonneg]
  linarith [WithTop.coe_le_coe.mp h]

/-- **The elements reduced in the residual polynomial of a segment lie in `𝒪_L`** (LMFDB
`lf.residual_polynomials`): for a segment `(k, l)` of the ramification polygon of `ρ`, of slope
`h / m`, a uniformiser `α` of `L` and `0 ≤ j ≤ l / m`, the element
`ρ_{j m + k} α ^ (j h - v_L(ρ_k))` lies in the ring of integers, as the point
`(-j m - k, v_L(ρ_{j m + k}))` lies on or above the segment. -/
lemma mem_integer_residualPolynomial (hϖ : Irreducible ϖ) (hkl : kl ∈ residualSegments ρ) (j : ℕ) :
    ρ.coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) *
      (ϖ : L) ^ ((j : ℤ) * (residualSlope ρ kl.1 kl.2).num - coeffVal ρ kl.1) ∈ 𝒪[L] := by
  rcases eq_or_ne (ρ.coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1)) 0 with h₀ | h₀
  · rw [h₀, zero_mul]
    exact zero_mem _
  refine mem_integer_of_le hϖ ?_
  rw [addValuation_coeff h₀, WithTop.coe_le_coe]
  have h₁ : (coeffVal ρ kl.1 : ℚ) -
      residualSlope ρ kl.1 kl.2 * (((j * (residualSlope ρ kl.1 kl.2).den + kl.1 : ℕ) : ℚ) - kl.1) ≤
        coeffVal ρ (j * (residualSlope ρ kl.1 kl.2).den + kl.1) :=
    coeffVal_sub_mul_le hkl h₀
  have h₂ : (residualSlope ρ kl.1 kl.2) *
      (((j * (residualSlope ρ kl.1 kl.2).den + kl.1 : ℕ) : ℚ) - kl.1) =
        j * (residualSlope ρ kl.1 kl.2).num := by
    push_cast
    rw [add_sub_cancel_right, mul_comm (j : ℚ), ← mul_assoc, Rat.mul_den_eq_num, mul_comm]
  rw [h₂] at h₁
  have h₃ : ((-((j : ℤ) * (residualSlope ρ kl.1 kl.2).num - coeffVal ρ kl.1) : ℤ) : ℚ) ≤
      (coeffVal ρ (j * (residualSlope ρ kl.1 kl.2).den + kl.1) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h₃

lemma residueOf_mul_zpow_ne_zero (hϖ : Irreducible ϖ) (hρ : ρ.coeff i ≠ 0) :
    residueOf L (ρ.coeff i * (ϖ : L) ^ (-coeffVal ρ i)) ≠ 0 := by
  refine residueOf_ne_zero (mul_ne_zero hρ (zpow_ne_zero _ fun h ↦ hϖ.ne_zero (Subtype.ext h))) ?_
  rw [addValuation_mul_zpow hϖ hρ, addValuation_coeff hρ, ← WithTop.coe_add, add_neg_cancel]
  rfl

lemma coeff_zero_residualPolynomial :
    (residualPolynomial ρ α k l).coeff 0 = residueOf L (ρ.coeff k * α ^ (-coeffVal ρ k)) := by
  rw [coeff_residualPolynomial, ite_eq_left (Nat.zero_le _), zero_mul, zero_add, Nat.cast_zero,
    zero_mul, zero_sub]

lemma coeff_div_den_residualPolynomial (hkl : kl ∈ residualSegments ρ) :
    (residualPolynomial ρ α kl.1 kl.2).coeff (kl.2 / (residualSlope ρ kl.1 kl.2).den) =
      residueOf L (ρ.coeff (kl.1 + kl.2) * α ^ (-coeffVal ρ (kl.1 + kl.2))) := by
  rw [coeff_residualPolynomial, ite_eq_left le_rfl, Nat.div_mul_cancel (residualSlope_den_dvd _ _),
    add_comm kl.2, mul_comm _ (residualSlope ρ kl.1 kl.2).num,
    num_mul_div_den kl.1 (pos_of_mem_residualSegments hkl).ne', sub_sub_cancel_left]

/-- **The constant term of the residual polynomial of a segment is nonzero** (LMFDB
`lf.residual_polynomials`): for a segment `(k, l)` of the ramification polygon of `ρ` and a
uniformiser `α`, the constant term `(ρ_k α ^ (-v_L(ρ_k)))‾` of its residual polynomial is
nonzero. -/
lemma coeff_zero_residualPolynomial_ne_zero (hϖ : Irreducible ϖ) (hkl : kl ∈ residualSegments ρ) :
    (residualPolynomial ρ ϖ kl.1 kl.2).coeff 0 ≠ 0 := by
  rw [coeff_zero_residualPolynomial]
  exact residueOf_mul_zpow_ne_zero hϖ (coeff_fst_ne_zero_of_mem_residualSegments hkl)

/-- **The degree of the residual polynomial of a segment** (LMFDB `lf.residual_polynomials`): for a
segment `(k, l)` of the ramification polygon of `ρ`, of slope `h / m` in lowest terms, and a
uniformiser `α`, the residual polynomial has degree `l / m`, its leading coefficient being
`(ρ_{k + l} α ^ (-v_L(ρ_{k + l})))‾`; `m` divides `l`. -/
lemma natDegree_residualPolynomial (hϖ : Irreducible ϖ) (hkl : kl ∈ residualSegments ρ) :
    (residualPolynomial ρ ϖ kl.1 kl.2).natDegree = kl.2 / (residualSlope ρ kl.1 kl.2).den := by
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ ?_)
    (le_natDegree_of_ne_zero ?_)
  · rw [coeff_residualPolynomial, ite_eq_right (not_le.mpr (by exact_mod_cast hj))]
  · rw [coeff_div_den_residualPolynomial hkl]
    exact residueOf_mul_zpow_ne_zero hϖ (coeff_add_ne_zero_of_mem_residualSegments hkl)

lemma leadingCoeff_residualPolynomial (hϖ : Irreducible ϖ) (hkl : kl ∈ residualSegments ρ) :
    (residualPolynomial ρ ϖ kl.1 kl.2).leadingCoeff =
      residueOf L (ρ.coeff (kl.1 + kl.2) * (ϖ : L) ^ (-coeffVal ρ (kl.1 + kl.2))) := by
  rw [leadingCoeff, natDegree_residualPolynomial hϖ hkl, coeff_div_den_residualPolynomial hkl]

lemma length_residualSegments : (residualSegments ρ).length = (residualSlopeList ρ).length :=
  List.length_map _

lemma sortedLT_residualSlopeList : (residualSlopeList ρ).SortedLT :=
  Finset.sortedLT_sort _

lemma residualSlope_residualSegmentOf (hs : s ∈ residualSlopeList ρ) :
    (residualSlope ρ (residualSegmentOf ρ s).1 (residualSegmentOf ρ s).2 : ℝ) = -s := by
  have hs' : s ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ) :=
    mem_residualSlopeList.mp hs
  linarith [unitSlope_eq_neg_residualSlope (List.mem_map_of_mem hs) hs' rfl
    (residualSegmentOf_fst_add_snd hs').symm]

/-- **Each segment starts where the previous one ends** (LMFDB `lf.residual_polynomials`): the
segment `S_{i + 1}` of the ramification polygon of `ρ` has the left end `(-k - l, v_L(ρ_{k + l}))`
of `S_i` as its right end, the segments being numbered from the right. -/
lemma residualSegments_succ_fst (h : i + 1 < (residualSegments ρ).length) :
    (residualSegments ρ)[i + 1].1 = (residualSegments ρ)[i].1 + (residualSegments ρ)[i].2 := by
  have hlen : i + 1 < (residualSlopeList ρ).length := by
    rwa [← length_residualSegments]
  have hsort : (residualSlopeList ρ).SortedLT :=
    sortedLT_residualSlopeList
  have hs :
      (residualSlopeList ρ)[i] ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ) :=
    mem_residualSlopeList.mp (List.getElem_mem (Nat.lt_of_succ_lt hlen))
  have ht :
      (residualSlopeList ρ)[i + 1] ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ) :=
    mem_residualSlopeList.mp (List.getElem_mem hlen)
  have hst : (residualSlopeList ρ)[i] < (residualSlopeList ρ)[i + 1] :=
    hsort.getElem_lt_getElem_iff.mpr (Nat.lt_succ_self i)
  have hbetween (r : ℝ) (hr : r ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ))
      (hsr : (residualSlopeList ρ)[i] < r) : (residualSlopeList ρ)[i + 1] ≤ r := by
    rcases List.mem_iff_getElem.mp (mem_residualSlopeList.mpr hr) with ⟨j, hj, rfl⟩
    exact hsort.getElem_le_getElem_iff.mpr (hsort.getElem_lt_getElem_iff.mp hsr)
  simp only [residualSegments, List.getElem_map]
  rw [residualSegmentOf_fst_add_snd hs, residualSegmentOf_fst]
  exact (sSup_slopeIndices_add_one_eq_sInf isConvexSeq_coeffEnvelope finite_coeffEnvelope_ne_top
    hs ht hst hbetween).symm

/-- **The slopes of the segments decrease from the right to the left** (LMFDB
`lf.residual_polynomials`): the slope `h_{i + 1} / m_{i + 1}` of the segment `S_{i + 1}` of the
ramification polygon of `ρ` is smaller than the slope `h_i / m_i` of `S_i`. -/
lemma residualSlope_lt_residualSlope (h : i + 1 < (residualSegments ρ).length) :
    residualSlope ρ (residualSegments ρ)[i + 1].1 (residualSegments ρ)[i + 1].2 <
      residualSlope ρ (residualSegments ρ)[i].1 (residualSegments ρ)[i].2 := by
  have hlen : i + 1 < (residualSlopeList ρ).length := by
    rwa [← length_residualSegments]
  have hst : (residualSlopeList ρ)[i] < (residualSlopeList ρ)[i + 1] :=
    sortedLT_residualSlopeList.getElem_lt_getElem_iff.mpr (Nat.lt_succ_self i)
  simp only [residualSegments, List.getElem_map]
  have h₃ : (residualSlope ρ (residualSegmentOf ρ (residualSlopeList ρ)[i + 1]).1
      (residualSegmentOf ρ (residualSlopeList ρ)[i + 1]).2 : ℝ) <
        residualSlope ρ (residualSegmentOf ρ (residualSlopeList ρ)[i]).1
          (residualSegmentOf ρ (residualSlopeList ρ)[i]).2 := by
    rw [residualSlope_residualSegmentOf (List.getElem_mem (Nat.lt_of_succ_lt hlen)),
      residualSlope_residualSegmentOf (List.getElem_mem hlen)]
    linarith
  exact_mod_cast h₃

/-- **The constant term of each residual polynomial is the leading coefficient of the next**
(LMFDB `lf.ramification_polygon_display`): the segments `S_{i + 1}` and `S_i` of the ramification
polygon of `ρ` share the vertex `(-k, v_L(ρ_k))`, the left end of `S_i`, so the constant term of the
residual polynomial `A_{i + 1}` is the leading coefficient of `A_i`, both being
`(ρ_k α ^ (-v_L(ρ_k)))‾`, for a uniformiser `α`. The LMFDB lists the residual polynomials from the
left, `A_ℓ, …, A_1`, so `A_i` is the next one after `A_{i + 1}`. -/
lemma coeff_zero_residualPolynomials_succ (hϖ : Irreducible ϖ)
    (h : i + 1 < (residualPolynomials ρ ϖ).length) : (residualPolynomials ρ ϖ)[i + 1].coeff 0 =
      ((residualPolynomials ρ ϖ)[i]'(Nat.lt_of_succ_lt h)).leadingCoeff := by
  have h' : i + 1 < (residualSegments ρ).length := by
    rwa [residualPolynomials, List.length_map] at h
  simp only [residualPolynomials, List.getElem_map]
  rw [coeff_zero_residualPolynomial, leadingCoeff_residualPolynomial hϖ
    (List.getElem_mem (Nat.lt_of_succ_lt h')), residualSegments_succ_fst h']

/-- The constants `γ_{δ,i}` of the equivalence of lists of residual polynomials (LMFDB
`lf.residual_polynomials`), for a list of pairs `(h_i, A_i)`: `γ_{δ,ℓ} = δ ^ (-h_ℓ deg A_ℓ)` and
`γ_{δ,i} = γ_{δ,i+1} δ ^ (-h_i deg A_i)`. -/
noncomputable def residualGammas (δ : F) : List (ℤ × F[X]) → List F
  | [] => []
  | hA :: t => ((residualGammas δ t).headD 1 * δ ^ (-(hA.1 * hA.2.natDegree))) :: residualGammas δ t

/-- The action of `δ` on a list of pairs `(h_i, A_i)` (LMFDB `lf.residual_polynomials`): the list
`(γ_{δ,1} A_1(δ ^ h_1 x), …, γ_{δ,ℓ} A_ℓ(δ ^ h_ℓ x))`. -/
noncomputable def residualAct (δ : F) (P : List (ℤ × F[X])) : List F[X] :=
  List.zipWith (fun γ hA ↦ C γ * hA.2.comp (C (δ ^ hA.1) * X)) (residualGammas δ P) P

variable (ρ α) in
/-- The pairs `(h_i, A_i)` of the numerators of the slopes of the segments `S_1, …, S_ℓ` of the
ramification polygon of `ρ` and of their residual polynomials. -/
noncomputable def residualPairs : List (ℤ × 𝓀[L][X]) :=
  (residualSegments ρ).map fun kl ↦
    ((residualSlope ρ kl.1 kl.2).num, residualPolynomial ρ α kl.1 kl.2)

variable (ρ α) in
/-- The **equivalence class of residual polynomials** (LMFDB `lf.residual_polynomials`, Pauli and
Sinclair's Theorem 4.8): for the residual polynomials `A_1, …, A_ℓ` of the segments of the
ramification polygon of `ρ` at `α`, numbered from the right, of slopes `h_i / m_i`, the set
`𝒜 = {(γ_{δ,1} A_1(δ ^ h_1 x), …, γ_{δ,ℓ} A_ℓ(δ ^ h_ℓ x)) : δ ∈ K̲ ^ ×}`, where
`γ_{δ,ℓ} = δ ^ (-h_ℓ deg A_ℓ)` and `γ_{δ,i} = γ_{δ,i+1} δ ^ (-h_i deg A_i)`. -/
noncomputable def residualPolynomialClass : Set (List 𝓀[L][X]) :=
  Set.range fun δ : 𝓀[K]ˣ ↦ residualAct (algebraMap 𝓀[K] 𝓀[L] δ) (residualPairs ρ α)

end IsNonarchimedeanLocalField
