import LeanBridge.ForMathlib.NumberTheory.LocalField.PadicRadical
import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialInvariance

/-!
# The residual polynomials of `ℚ₃(∛3)`

The knowl LMFDB `lf.residual_polynomials` says that the list of residual polynomials of the
minimal polynomial `φ` of a uniformiser is not an invariant of the extension, only its equivalence
class is. This file checks it on the totally ramified cubic extension `L = ℚ₃(∛3)`, the field
`LeanBridge.PadicRadical 3 3` obtained by adjoining a root `α` of the Eisenstein polynomial `X³ - 3`
to `ℚ₃`. The ramification polynomial of `X³ - 3` at `α` is `ρ(x) = (x + 1)³ - 1 = x³ + 3 x² + 3 x`,
with the points `(-1, 3)`, `(-2, 3)` and `(-3, 0)`, so the ramification polygon has the single
segment from `(-3, 0)` to `(-1, 3)`, of slope `3 / 2`, and its residual polynomial at `α` is
`1 + x`. At the uniformiser `-α` it is `(-1) ^ (-3) (1 + (-1) ^ 3 x) = -1 + x = 2 + x` over
`L̲ = 𝔽₃`, by the change of residual polynomials under a change of uniformiser. So the two lists
`[1 + x]` and `[2 + x]` differ, while they lie in the same class `{[1 + x], [2 + x]}`.

## Main results

* `IsNonarchimedeanLocalField.PadicCbrtThree.residualSegments_eq` (LMFDB
  `lf.residual_polynomials`): the ramification polygon has the single segment `(k, l) = (1, 2)`.
* `IsNonarchimedeanLocalField.PadicCbrtThree.residualPolynomials_cbrtThree` and
  `IsNonarchimedeanLocalField.PadicCbrtThree.residualPolynomials_neg_cbrtThree` (LMFDB
  `lf.residual_polynomials`): the lists of residual polynomials at `α` and `-α` are `[1 + x]` and
  `[2 + x]`.
* `IsNonarchimedeanLocalField.PadicCbrtThree.residualPolynomials_neg_cbrtThree_ne` (LMFDB
  `lf.residual_polynomials`): the list of residual polynomials depends on the uniformiser.
-/

open LeanBridge PadicRadical Polynomial ValuativeRel TauCeti

namespace IsNonarchimedeanLocalField.PadicCbrtThree

local instance : Nontrivial ℚ_[3] :=
  ⟨⟨0, 1, zero_ne_one⟩⟩

lemma cbrtThree_pow_three : root 3 3 ^ 3 = 3 :=
  (root_pow 3 3).trans Nat.cast_ofNat

lemma coe_ofNat_three : ((3 : 𝒪[PadicRadical 3 3]) : PadicRadical 3 3) = 3 :=
  map_ofNat (Subring.subtype 𝒪[PadicRadical 3 3]) 3

lemma ramificationPolynomial_cbrtThree :
    ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3) = X ^ 3 + C 3 * X ^ 2 +
      C 3 * X := by
  have h₁ : (C (root 3 3) * X + C (root 3 3)) ^ 3 - C 3 = C (root 3 3 ^ 3) * ((X + 1) ^ 3 - 1) := by
    rw [← cbrtThree_pow_three, C_pow]
    ring1
  have h₂ : C ((root 3 3)⁻¹ ^ 3) * C (root 3 3 ^ 3) = (1 : (PadicRadical 3 3)[X]) := by
    rw [← C_mul, ← mul_pow, inv_mul_cancel₀ (root_ne_zero 3 3), one_pow, C_1]
  rw [ramificationPolynomial, minpoly_root, natDegree_X_pow_sub_C, Polynomial.map_sub,
    Polynomial.map_pow, map_X, map_C, map_natCast, Nat.cast_ofNat, sub_comp, pow_comp, X_comp,
    C_comp, h₁, ← mul_assoc, h₂, one_mul, map_ofNat C 3]
  ring1

lemma addValuation_three : addValuation (PadicRadical 3 3) 3 = 3 := by
  have h : addValuation (PadicRadical 3 3) ((integerRoot 3 3 : PadicRadical 3 3) ^ (3 : ℤ)) =
      ((3 : ℤ) : WithTop ℤ) :=
    addValuation_zpow (irreducible_integerRoot 3 3) 3
  rw [coe_integerRoot, zpow_ofNat, cbrtThree_pow_three] at h
  exact h

lemma addValuation_one : addValuation (PadicRadical 3 3) 1 = 0 := by
  have h : addValuation (PadicRadical 3 3) ((integerRoot 3 3 : PadicRadical 3 3) ^ (0 : ℤ)) =
      ((0 : ℤ) : WithTop ℤ) :=
    addValuation_zpow (irreducible_integerRoot 3 3) 0
  rwa [zpow_zero] at h

lemma coeff_ramificationPolynomial_cbrtThree (n : ℕ) :
    (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)).coeff n =
      if n = 3 then 1 else if n = 1 ∨ n = 2 then 3 else 0 := by
  rw [ramificationPolynomial_cbrtThree]
  simp only [coeff_add, coeff_C_mul, coeff_X]
  rcases n with _ | _ | _ | _ | n <;> simp

lemma coeffHeight_cbrtThree (n : ℕ) :
    coeffHeight (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) n =
      if n = 3 then 0 else if n = 1 ∨ n = 2 then 3 else ⊤ := by
  rw [coeffHeight_apply, coeff_ramificationPolynomial_cbrtThree]
  split_ifs
  · rw [addValuation_one]
    simp
  · rw [addValuation_three]
    rfl
  · rw [addValuation_zero]
    rfl

lemma coeffEnvelope_cbrtThree (n : ℕ) :
    coeffEnvelope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) n =
      if n ∈ Set.Icc 1 3 then (((9 / 2 : ℝ) + -(3 / 2) * n : ℝ) : WithTop ℝ) else ⊤ := by
  have hg : (fun n : ℕ ↦ if n ∈ Set.Icc 1 3 then (((9 / 2 : ℝ) + -(3 / 2) * n : ℝ) : WithTop ℝ)
      else ⊤) ≤ coeffHeight (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) := by
    intro n
    rw [coeffHeight_cbrtThree]
    simp only [Set.mem_Icc]
    rcases n with _ | _ | _ | _ | n
    · norm_num
    · norm_num
    · norm_num
      rw [← WithTop.coe_ofNat, WithTop.coe_le_coe]
      norm_num
    · norm_num
    · rw [ite_eq_right (by omega)]
      exact le_top
  have hle : (fun n : ℕ ↦ if n ∈ Set.Icc 1 3 then (((9 / 2 : ℝ) + -(3 / 2) * n : ℝ) : WithTop ℝ)
      else ⊤) ≤ coeffEnvelope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) :=
    le_lowerConvexEnvelope (isConvexSeq_affine_ite Set.ordConnected_Icc _ _) hg
  have hge : coeffEnvelope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) ≤
      coeffHeight (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) :=
    lowerConvexEnvelope_le (isAdmissible_of_finite finite_coeffHeight_ne_top)
  have h₁ : coeffEnvelope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) 1 = 3 := by
    refine le_antisymm ((hge 1).trans_eq ?_) ((hle 1).trans_eq' ?_)
    · rw [coeffHeight_cbrtThree]
      norm_num
    · norm_num
  have h₃ : coeffEnvelope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) 3 = 0 := by
    refine le_antisymm ((hge 3).trans_eq ?_) ((hle 3).trans_eq' ?_)
    · rw [coeffHeight_cbrtThree]
      norm_num
    · norm_num
  refine le_antisymm ?_ (hle n)
  rcases n with _ | _ | _ | _ | n
  · norm_num
  · rw [h₁]
    norm_num
  · set ρ : (PadicRadical 3 3)[X] := ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)
    have hconv :
        2 * (coeffEnvelope ρ 2).untop₀ ≤ (coeffEnvelope ρ 1).untop₀ + (coeffEnvelope ρ 3).untop₀ :=
      (isConvexSeq_iff_two_mul_le.mp isConvexSeq_coeffEnvelope).2 1
        (by rw [h₁]; exact WithTop.coe_ne_top) (by rw [h₃]; exact WithTop.coe_ne_top)
    have h₂ : coeffEnvelope ρ 2 ≠ ⊤ :=
      isConvexSeq_coeffEnvelope.ne_top_of_le_of_le (by rw [h₁]; exact WithTop.coe_ne_top)
        (by rw [h₃]; exact WithTop.coe_ne_top) (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 3)
    rw [h₁, h₃] at hconv
    rw [← WithTop.coe_untop₀_of_ne_top h₂]
    norm_num at hconv ⊢
    exact_mod_cast (by linarith : (coeffEnvelope ρ 2).untop₀ ≤ 3 / 2)
  · rw [h₃]
    norm_num
  · rw [ite_eq_right (by simp only [Set.mem_Icc]; omega)]
    exact le_top

lemma mem_finiteEdges_cbrtThree (n : ℕ) :
    n ∈ finiteEdges (coeffEnvelope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3))) ↔
      n = 1 ∨ n = 2 := by
  rw [mem_finiteEdges, coeffEnvelope_cbrtThree, coeffEnvelope_cbrtThree]
  rcases n with _ | _ | _ | _ | n
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [ite_eq_right (by simp only [Set.mem_Icc]; omega)]
    simp only [ne_eq, not_true_eq_false, false_and, false_iff]
    omega

lemma unitSlope_cbrtThree {n : ℕ} (hn : n = 1 ∨ n = 2) :
    unitSlope (coeffEnvelope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3))) n =
      -(3 / 2) := by
  rcases hn with rfl | rfl <;> rw [unitSlope_def, coeffEnvelope_cbrtThree,
    coeffEnvelope_cbrtThree] <;> norm_num

lemma slopeIndices_cbrtThree : slopeIndices (coeffEnvelope
    (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3))) (-(3 / 2)) = {1, 2} := by
  ext n
  refine ⟨fun hn ↦ (mem_finiteEdges_cbrtThree n).mp hn.1, fun hn ↦ ?_⟩
  exact ⟨(mem_finiteEdges_cbrtThree n).mpr hn, unitSlope_cbrtThree hn⟩

lemma residualUnitSlopes_cbrtThree : residualUnitSlopes
    (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) = {-(3 / 2)} := by
  ext s
  rw [mem_residualUnitSlopes, Finset.mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, hn, rfl⟩
    exact unitSlope_cbrtThree ((mem_finiteEdges_cbrtThree n).mp hn)
  · rintro rfl
    exact ⟨1, (mem_finiteEdges_cbrtThree 1).mpr (.inl rfl), unitSlope_cbrtThree (.inl rfl)⟩

/-- **The ramification polygon of `ℚ₃(∛3)` has a single segment** (LMFDB
`lf.residual_polynomials`): the segment `(k, l) = (1, 2)` from `(-3, 0)` to `(-1, 3)`. -/
lemma residualSegments_eq :
    residualSegments (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) = [(1, 2)] := by
  rw [residualSegments, residualSlopeList, residualUnitSlopes_cbrtThree, Finset.sort_singleton,
    List.map_singleton, residualSegmentOf, slopeIndices_cbrtThree, csInf_pair, csSup_pair]
  rfl

lemma coeffVal_one_cbrtThree :
    coeffVal (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) 1 = 3 := by
  rw [coeffVal, coeff_ramificationPolynomial_cbrtThree]
  norm_num
  rw [addValuation_three]
  rfl

lemma coeffVal_three_cbrtThree :
    coeffVal (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) 3 = 0 := by
  rw [coeffVal, coeff_ramificationPolynomial_cbrtThree, ite_eq_left rfl, addValuation_one]
  rfl

lemma residualSlope_cbrtThree :
    residualSlope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) 1 2 = 3 / 2 := by
  rw [residualSlope, coeffVal_one_cbrtThree, coeffVal_three_cbrtThree]
  norm_num

lemma residueOf_one_cbrtThree : residueOf (PadicRadical 3 3) 1 = 1 := by
  rw [← OneMemClass.coe_one 𝒪[PadicRadical 3 3], residueOf_coe, map_one]

lemma residualPolynomial_cbrtThree : residualPolynomial
    (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) (root 3 3) 1 2 = 1 + X := by
  have hnum : (residualSlope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) 1
      2).num = 3 := by
    rw [residualSlope_cbrtThree]
    norm_num
  have hden : (residualSlope (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) 1
      2).den = 2 := by
    rw [residualSlope_cbrtThree]
    norm_num
  have h₁ : (3 : PadicRadical 3 3) * (root 3 3 ^ 3)⁻¹ = 1 := by
    rw [cbrtThree_pow_three, mul_inv_cancel₀ three_ne_zero]
  rw [residualPolynomial, hnum, hden, coeffVal_one_cbrtThree]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    coeff_ramificationPolynomial_cbrtThree]
  norm_num
  rw [h₁, residueOf_one_cbrtThree, C_1, one_mul]

/-- **The list of residual polynomials of `ℚ₃(∛3)` at `α = ∛3` is `[1 + x]`** (LMFDB
`lf.residual_polynomials`). -/
lemma residualPolynomials_cbrtThree :
    residualPolynomials (ramificationPolynomial (minpoly ℚ_[3] (root 3 3)) (root 3 3)) (root 3 3) =
      [1 + X] := by
  rw [residualPolynomials, residualSegments_eq, List.map_singleton, residualPolynomial_cbrtThree]

lemma three_eq_zero_residueField : (3 : 𝓀[PadicRadical 3 3]) = 0 := by
  rw [← map_ofNat (IsLocalRing.residue 𝒪[PadicRadical 3 3]) 3]
  refine residue_eq_zero_of_pos ?_
  rw [coe_ofNat_three, addValuation_three]
  exact WithTop.coe_lt_coe.mpr (by norm_num)

/-- **The list of residual polynomials of `ℚ₃(∛3)` at `-α = -∛3` is `[2 + x]`** (LMFDB
`lf.residual_polynomials`): by the change of the residual polynomials under the change of
uniformiser `α ↦ -α`, it is `[(-1) ^ (-3) (1 + (-1) ^ 3 x)] = [-1 + x]`, and `-1 = 2` in
`L̲ = 𝔽₃`. -/
lemma residualPolynomials_neg_cbrtThree :
    residualPolynomials (ramificationPolynomial (minpoly ℚ_[3] (-root 3 3)) (-root 3 3))
      (-root 3 3) = [C 2 + X] := by
  have hα' : Irreducible (-integerRoot 3 3) :=
    Associated.irreducible ⟨-1, by rw [Units.val_neg, Units.val_one, mul_neg_one]⟩
      (irreducible_integerRoot 3 3)
  have hu :
      -integerRoot 3 3 = ((-1 : 𝒪[PadicRadical 3 3]ˣ) : 𝒪[PadicRadical 3 3]) * integerRoot 3 3 := by
    rw [Units.val_neg, Units.val_one, neg_one_mul]
  have hkl : ((1, 2) : ℕ × ℕ) ∈ residualSegments (ramificationPolynomial
      (minpoly ℚ_[3] ((integerRoot 3 3 : 𝒪[PadicRadical 3 3]) : PadicRadical 3 3))
        ((integerRoot 3 3 : 𝒪[PadicRadical 3 3]) : PadicRadical 3 3)) := by
    rw [coe_integerRoot, residualSegments_eq]
    exact List.mem_singleton_self _
  have hcoe : (-root 3 3 : PadicRadical 3 3) =
      ((-integerRoot 3 3 : 𝒪[PadicRadical 3 3]) : PadicRadical 3 3) :=
    rfl
  rw [hcoe, residualPolynomials, residualSegments_eq_of_irreducible (isTotallyRamified 3 3)
    (irreducible_integerRoot 3 3) hα', coe_integerRoot, residualSegments_eq, List.map_singleton]
  dsimp only
  rw [residualPolynomial_eq_of_irreducible (isTotallyRamified 3 3) (irreducible_integerRoot 3 3) hα'
    (-1) hu hkl, coe_integerRoot]
  dsimp only
  rw [residualPolynomial_cbrtThree, coeffVal_one_cbrtThree, residualSlope_cbrtThree]
  have h₁ : ((3 / 2 : ℚ)).num = 3 := by
    norm_num
  have h₂ : (-1 : 𝓀[PadicRadical 3 3]) = 2 := by
    linear_combination -three_eq_zero_residueField
  rw [h₁, Units.val_neg, Units.val_one, map_neg, map_one, add_comp, one_comp, X_comp, zpow_neg,
    zpow_ofNat, Odd.neg_one_pow (by decide), inv_neg, inv_one, mul_add, mul_one, ← mul_assoc,
    ← C_mul, neg_one_mul, neg_neg, C_1, one_mul, h₂]

/-- **The list of residual polynomials is not an invariant** (LMFDB `lf.residual_polynomials`):
the lists of residual polynomials of `ℚ₃(∛3) / ℚ₃` at the uniformisers `∛3` and `-∛3`, `[1 + x]` and
`[2 + x]`, differ. They lie in the same class `𝒜`, by the invariance theorem. -/
lemma residualPolynomials_neg_cbrtThree_ne :
    residualPolynomials (ramificationPolynomial (minpoly ℚ_[3] (-root 3 3)) (-root 3 3))
      (-root 3 3) ≠ residualPolynomials (ramificationPolynomial (minpoly ℚ_[3] (root 3 3))
        (root 3 3)) (root 3 3) := by
  rw [residualPolynomials_neg_cbrtThree, residualPolynomials_cbrtThree]
  intro h
  have h₁ : (C 2 + X : 𝓀[PadicRadical 3 3][X]).coeff 0 = (1 + X : 𝓀[PadicRadical 3 3][X]).coeff 0 :=
    congrArg (fun A ↦ A.coeff 0) (List.singleton_injective h)
  simp only [coeff_add, coeff_C_zero, coeff_X_zero, coeff_one_zero] at h₁
  have h₂ : (1 : 𝓀[PadicRadical 3 3]) = 0 := by
    linear_combination h₁
  exact one_ne_zero h₂

end IsNonarchimedeanLocalField.PadicCbrtThree
