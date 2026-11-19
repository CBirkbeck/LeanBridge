import LeanBridge.ForMathlib.Analysis.Convex.LowerHullVertices
import LeanBridge.ForMathlib.FieldTheory.Galois.SubextensionCorrespondence
import LeanBridge.ForMathlib.GroupTheory.Index
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamsDiscriminantExponent

/-!
# The slope polygon of the subextensions of a Galois extension of local fields

Let `M / K` be a finite Galois extension of nonarchimedean local fields, with group `G`, lower
ramification groups `G_i`, largest lower jump `T` and Herbrand function `φ`. For a subgroup `J` of
`G` set `c(J) = [G : J] ∑_{i = 0}^{T} (#G_i - #(J ∩ G_i)) / #G_0`. If `J = Gal(M / E)` for an
intermediate field `E`, then `c(J)` is the discriminant exponent of `E / K`: Hilbert's formula for
`M / K` and `M / E` and the tower formula for differents give
`#(J ∩ G_0) d(E / K) = ∑_i (#G_i - #(J ∩ G_i))`, and `c = f d` with `e f = [E : K] = [G : J]` and
`e = [G_0 : J ∩ G_0]`.

Fix a subgroup `H` of `G`, the group of an intermediate field `L`, and let
`τ_t = (#G_0 + ⋯ + #G_{t - 1}) / #G_0`, so that `τ_0 = 0`, `τ_1 = 1` and `τ_{t + 1} = 1 + φ(t)`. The
subextensions of `L / K` correspond to the subgroups `J ⊇ H`. With `I_X = [G : X]`,
`c(J) - τ_t I_J = (∑_{i ≥ t} I_J (#G_i - #(J ∩ G_i)) - ∑_{i < t} I_J #(J ∩ G_i)) / #G_0`, and
`I_J #(J ∩ G_i) ≤ I_H #(H ∩ G_i)` for `J ⊇ H`, with equality for `J = H G_s` and `i ≤ s`. So every
point `(I_J, c(J))` lies on or above the line of slope `τ_t` through the points of `H G_{t - 1}` and
`H G_t` (of `G` and `H G_0` for `t = 0`), and the points of the subgroups
`G ⊇ H G_0 ⊇ H G_1 ⊇ ⋯ ⊇ H G_{T + 1} = H` are the vertices of the lower convex hull of the points of
all the `J ⊇ H` (`IsNonarchimedeanLocalField.isLowerHullVertices_subgroupSlopePoints`). The slopes
`τ_t > 1` of this polygon, each repeated `log_p` of the ratio of the abscissas of its segment, are
the `1 + φ(i)`, `i ≥ 1`, each repeated `log_p ([G_i : H ∩ G_i] / [G_{i + 1} : H ∩ G_{i + 1}])`
times: the Swan slopes of `M^H / K` plus `1`, Deligne's positive upper ramification breaks
(`IsNonarchimedeanLocalField.sum_filter_replicate_eq_map_swanSlopesOfSubgroup`). This is how the
LMFDB's slope polygon of `L / K` (LMFDB `lf.slopes`) is computed.

For the subgroups `H ⊆ J ⊆ H G_0`, of the subextensions of `L` over its maximal unramified
subextension `K_f = M^{H G_0}`, the points `([H G_0 : J], c(J) / f - [H G_0 : J] + 1)`, with
`f = [G : H G_0]`, have the vertices `H ⊇ H G_t`, `t ≤ T + 1`, and slopes `τ_{t + 1} - 1 = φ(t)`
(`IsNonarchimedeanLocalField.isLowerHullVertices_subgroupMeanPoints`): this is the slope polygon of
LMFDB `lf.means`.

## Main definitions

* `IsNonarchimedeanLocalField.subgroupDiscriminantExponent`: `c(J)`.
* `IsNonarchimedeanLocalField.subgroupSlope`: `τ_t`.
* `IsNonarchimedeanLocalField.subgroupIntercept`: the intercept of the line of slope `τ_t` through
  the vertices.
* `IsNonarchimedeanLocalField.subgroupMeanAbscissa` and
  `IsNonarchimedeanLocalField.subgroupMeanOrdinate`: the coordinates `[H G_0 : J]` and
  `c(J) / f - [H G_0 : J] + 1` of the points of LMFDB `lf.means`.
* `IsNonarchimedeanLocalField.slopeVertexSubgroup`: the subgroups `G, H G_0, H G_1, …` at the
  vertices.
* `IsNonarchimedeanLocalField.subgroupSlopePoints`: the points `(I_J, c(J))`, `J ⊇ H`.
* `IsNonarchimedeanLocalField.subgroupMeanPoints`: the points
  `([H G_0 : J], c(J) / f - [H G_0 : J] + 1)`, `H ⊆ J ⊆ H G_0`.

## Main results

* `IsNonarchimedeanLocalField.natCast_discriminantExponent_eq_subgroupDiscriminantExponent`: `c(J)`
  is the discriminant exponent of the fixed field of `J`.
* `IsNonarchimedeanLocalField.subgroupIntercept_le` and
  `IsNonarchimedeanLocalField.subgroupDiscriminantExponent_sup_sub`: the points `(I_J, c(J))`,
  `J ⊇ H`, lie on or above the line of slope `τ_t` through the points of `H G_{t - 1}` and `H G_t`.
* `IsNonarchimedeanLocalField.natCast_subgroupSlope_succ`: `τ_{t + 1} = 1 + φ(t)`.
* `IsNonarchimedeanLocalField.index_sup_lowerRamificationGroup_add_two`: the indices of
  `H G_{i + 1}` and `H G_{i + 2}` differ by the factor
  `[G_{i + 1} : H ∩ G_{i + 1}] / [G_{i + 2} : H ∩ G_{i + 2}]`, a power of `p`.
* `IsNonarchimedeanLocalField.isLowerHullVertices_subgroupSlopePoints`: the vertices of the lower
  convex hull of the points `(I_J, c(J))` are the points of `G` and of the `H G_t`.
* `IsNonarchimedeanLocalField.sum_filter_replicate_eq_map_swanSlopesOfSubgroup`: its slopes `> 1`,
  with their multiplicities, are the Swan slopes of `M^H / K` plus `1`.
* `IsNonarchimedeanLocalField.isLowerHullVertices_subgroupMeanPoints`: the vertices of the lower
  convex hull of the points of the subgroups between `H` and `H G_0`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §4, and Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  appendix.
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

namespace IsNonarchimedeanLocalField

variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  (H J : Subgroup (M ≃ₐ[K] M)) (t : ℕ)

/-- The **discriminant exponent of a subgroup** `J` of the Galois group `G` of a finite Galois
extension `M / K` of nonarchimedean local fields: `c(J) = [G : J] ∑_{i = 0}^{T} (#G_i - #(J ∩ G_i))
/ #G_0`, for the lower ramification groups `G_i` and the largest lower jump `T`. It is the
discriminant exponent of the fixed field of `J`
(`IsNonarchimedeanLocalField.natCast_discriminantExponent_eq_subgroupDiscriminantExponent`). -/
noncomputable def subgroupDiscriminantExponent : ℚ :=
  (J.index * ∑ i ∈ range ((largestLowerJump K M).toNat + 1),
    ((Nat.card (lowerRamificationGroup K M i) : ℚ) -
      Nat.card ↥(J ⊓ lowerRamificationGroup K M i))) / Nat.card (lowerRamificationGroup K M 0)

/-- The `t`-th **slope** `τ_t = (#G_0 + ⋯ + #G_{t - 1}) / #G_0` of a finite Galois extension `M / K`
of nonarchimedean local fields, with lower ramification groups `G_i`: `τ_0 = 0`, `τ_1 = 1` and
`τ_{t + 1} = 1 + φ(t)` for the Herbrand function `φ`
(`IsNonarchimedeanLocalField.natCast_subgroupSlope_succ`). -/
noncomputable def subgroupSlope : ℚ :=
  (∑ i ∈ range t, (Nat.card (lowerRamificationGroup K M i) : ℚ)) /
    Nat.card (lowerRamificationGroup K M 0)

/-- The `t`-th **intercept** `-(∑_{i < t} [G : H] #(H ∩ G_i)) / #G_0` of a subgroup `H` of the
Galois group `G` of `M / K`: the line of slope `τ_t` through the points `([G : J], c(J))` of the
vertices `H G_{t - 1}` and `H G_t` meets the vertical axis there. -/
noncomputable def subgroupIntercept : ℚ :=
  -(∑ i ∈ range t, (H.index : ℚ) * Nat.card ↥(H ⊓ lowerRamificationGroup K M i)) /
    Nat.card (lowerRamificationGroup K M 0)

/-- The **subgroups at the vertices** of the slope polygon of a subgroup `H` of the Galois group `G`
of `M / K`: `G`, then `H G_t` for `t = 0, 1, …`, with `G_t` the lower ramification groups. -/
noncomputable def slopeVertexSubgroup : ℕ → Subgroup (M ≃ₐ[K] M)
  | 0 => ⊤
  | s + 1 => H ⊔ lowerRamificationGroup K M s

/-- The **points of the subgroups containing** `H`: the points `([G : J], c(J))` of the plane, for
the subgroups `J ⊇ H` of the Galois group `G` of `M / K`, those of the subextensions of
`M^H / K`. -/
noncomputable def subgroupSlopePoints : Set (ℝ × ℝ) :=
  (fun J : Subgroup (M ≃ₐ[K] M) ↦ ((J.index : ℝ), (subgroupDiscriminantExponent K M J : ℝ))) ''
    {J | H ≤ J}

/-- The **abscissa** `[H G_0 : J]` of a subgroup `J` of the Galois group `G` of `M / K` in the slope
polygon of LMFDB `lf.means` attached to a subgroup `H`, with `G_0` the inertia group: the degree of
the fixed field of `J` over `M^{H G_0}`. -/
noncomputable def subgroupMeanAbscissa : ℕ :=
  J.relIndex (H ⊔ lowerRamificationGroup K M 0)

/-- The **ordinate** `c(J) / f - [H G_0 : J] + 1`, with `f = [G : H G_0]`, of a subgroup `J` of the
Galois group `G` of `M / K` in the slope polygon of LMFDB `lf.means` attached to a subgroup `H`: the
number `e' m'` for the degree `e'` and the mean `m'` of the fixed field of `J` over `M^{H G_0}`. -/
noncomputable def subgroupMeanOrdinate : ℚ :=
  subgroupDiscriminantExponent K M J / (H ⊔ lowerRamificationGroup K M 0).index -
    subgroupMeanAbscissa K M H J + 1

/-- The **points of the subgroups between** `H` and `H G_0`: the points
`([H G_0 : J], c(J) / f - [H G_0 : J] + 1)` of the plane, with `f = [G : H G_0]`, for the subgroups
`H ⊆ J ⊆ H G_0` of the Galois group `G` of `M / K`, those of the subextensions of `M^H` over its
maximal unramified subextension `M^{H G_0}`. -/
noncomputable def subgroupMeanPoints : Set (ℝ × ℝ) :=
  (fun J : Subgroup (M ≃ₐ[K] M) ↦ ((subgroupMeanAbscissa K M H J : ℝ),
    (subgroupMeanOrdinate K M H J : ℝ))) '' {J | H ≤ J ∧ J ≤ H ⊔ lowerRamificationGroup K M 0}

variable {K M H J t} {i s : ℕ}

variable (H) in
lemma index_sup_mul_card_inf_lowerRamificationGroup (hi : i ≤ s) :
    ((H ⊔ lowerRamificationGroup K M s).index : ℚ) *
      Nat.card ↥((H ⊔ lowerRamificationGroup K M s) ⊓ lowerRamificationGroup K M i) =
        H.index * Nat.card ↥(H ⊓ lowerRamificationGroup K M i) := by
  have hsi : lowerRamificationGroup K M s ≤ lowerRamificationGroup K M i :=
    lowerRamificationGroup_antitone K M (Nat.cast_le.mpr hi)
  have h₁ : Nat.card ↥(H ⊔ lowerRamificationGroup K M s ⊔ lowerRamificationGroup K M i) *
      Nat.card ↥((H ⊔ lowerRamificationGroup K M s) ⊓ lowerRamificationGroup K M i) =
        Nat.card ↥(H ⊔ lowerRamificationGroup K M s) * Nat.card (lowerRamificationGroup K M i) :=
    Subgroup.card_sup_mul_card_inf _ _
  rw [sup_assoc, sup_of_le_right hsi] at h₁
  have hX : (Nat.card ↥(H ⊔ lowerRamificationGroup K M i) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hH : (Nat.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine mul_right_cancel₀ (mul_ne_zero hX hH) ?_
  have e₁ : (Nat.card ↥(H ⊔ lowerRamificationGroup K M i) : ℚ) *
      Nat.card ↥((H ⊔ lowerRamificationGroup K M s) ⊓ lowerRamificationGroup K M i) =
        Nat.card ↥(H ⊔ lowerRamificationGroup K M s) * Nat.card (lowerRamificationGroup K M i) := by
    exact_mod_cast h₁
  have e₂ : (Nat.card ↥(H ⊔ lowerRamificationGroup K M i) : ℚ) *
      Nat.card ↥(H ⊓ lowerRamificationGroup K M i) =
        Nat.card H * Nat.card (lowerRamificationGroup K M i) := by
    exact_mod_cast H.card_sup_mul_card_inf (lowerRamificationGroup K M i)
  have e₃ : ((H ⊔ lowerRamificationGroup K M s).index : ℚ) *
      Nat.card ↥(H ⊔ lowerRamificationGroup K M s) = Nat.card (M ≃ₐ[K] M) := by
    exact_mod_cast (H ⊔ lowerRamificationGroup K M s).index_mul_card
  have e₄ : (H.index : ℚ) * Nat.card H = Nat.card (M ≃ₐ[K] M) := by
    exact_mod_cast H.index_mul_card
  linear_combination ((H ⊔ lowerRamificationGroup K M s).index * Nat.card H : ℚ) * e₁ +
    (Nat.card H * Nat.card (lowerRamificationGroup K M i) : ℚ) * e₃ -
    (Nat.card H * Nat.card (lowerRamificationGroup K M i) : ℚ) * e₄ -
    (H.index * Nat.card H : ℚ) * e₂

variable (H) in
lemma sup_inf_lowerRamificationGroup_of_le (hsi : s ≤ i) : (H ⊔ lowerRamificationGroup K M s) ⊓
    lowerRamificationGroup K M i = lowerRamificationGroup K M i :=
  inf_of_le_right <| (lowerRamificationGroup_antitone K M (Nat.cast_le.mpr hsi)).trans le_sup_right

lemma index_mul_card_inf_le (hHJ : H ≤ J) (j : ℤ) : (J.index : ℚ) *
    Nat.card ↥(J ⊓ lowerRamificationGroup K M j) ≤
      H.index * Nat.card ↥(H ⊓ lowerRamificationGroup K M j) := by
  have h₁ : H.relIndex (J ⊓ lowerRamificationGroup K M j) *
      Nat.card ↥(H ⊓ (J ⊓ lowerRamificationGroup K M j)) =
        Nat.card ↥(J ⊓ lowerRamificationGroup K M j) :=
    H.relIndex_mul_card _
  rw [← inf_assoc, inf_of_le_left hHJ] at h₁
  have h₂ : H.relIndex J * J.index = H.index := H.relIndex_mul_index hHJ
  have h₃ : (H.relIndex (J ⊓ lowerRamificationGroup K M j) : ℚ) ≤ H.relIndex J := by
    exact_mod_cast Subgroup.relIndex_le_of_le_right inf_le_left Subgroup.index_ne_zero_of_finite
  have h₀ : (0 : ℚ) ≤ J.index * Nat.card ↥(H ⊓ lowerRamificationGroup K M j) := by positivity
  rw [← h₁, ← h₂]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h₃ h₀]

variable (J) in
lemma subgroupDiscriminantExponent_sub_subgroupSlope_mul
    (ht : t ≤ (largestLowerJump K M).toNat + 1) : subgroupDiscriminantExponent K M J -
      subgroupSlope K M t * J.index =
        (∑ i ∈ Ico t ((largestLowerJump K M).toNat + 1), (J.index : ℚ) *
            ((Nat.card (lowerRamificationGroup K M i) : ℚ) -
              Nat.card ↥(J ⊓ lowerRamificationGroup K M i)) -
          ∑ i ∈ range t, (J.index : ℚ) * Nat.card ↥(J ⊓ lowerRamificationGroup K M i)) /
            Nat.card (lowerRamificationGroup K M 0) := by
  rw [subgroupDiscriminantExponent, subgroupSlope, ← sum_range_add_sum_Ico _ ht]
  simp only [sum_sub_distrib, ← mul_sum]
  ring1

/-- **The points of the subgroups containing `H` lie above the lines of slope `τ_t`**: for
`J ⊇ H` and `t ≤ T + 1`, `c(J) - τ_t [G : J]` is at least the `t`-th intercept of `H`. -/
lemma subgroupIntercept_le (hHJ : H ≤ J) (ht : t ≤ (largestLowerJump K M).toNat + 1) :
    subgroupIntercept K M H t ≤ subgroupDiscriminantExponent K M J -
      subgroupSlope K M t * J.index := by
  rw [subgroupDiscriminantExponent_sub_subgroupSlope_mul J ht, subgroupIntercept]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have h₁ : 0 ≤ ∑ i ∈ Ico t ((largestLowerJump K M).toNat + 1), (J.index : ℚ) *
      ((Nat.card (lowerRamificationGroup K M i) : ℚ) -
        Nat.card ↥(J ⊓ lowerRamificationGroup K M i)) :=
    sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (Nat.cast_le.mpr (Subgroup.card_le_of_le inf_le_right)))
  have h₂ : ∑ i ∈ range t, (J.index : ℚ) * Nat.card ↥(J ⊓ lowerRamificationGroup K M i) ≤
      ∑ i ∈ range t, (H.index : ℚ) * Nat.card ↥(H ⊓ lowerRamificationGroup K M i) :=
    sum_le_sum fun i _ ↦ index_mul_card_inf_le hHJ i
  linarith

variable (H) in
/-- **The vertices lie on the lines of slope `τ_t`**: for `s ≤ t ≤ s + 1` and `t ≤ T + 1`,
`c(H G_s) - τ_t [G : H G_s]` is the `t`-th intercept of `H`. -/
lemma subgroupDiscriminantExponent_sup_sub (hst : s ≤ t) (hts : t ≤ s + 1)
    (ht : t ≤ (largestLowerJump K M).toNat + 1) :
    subgroupDiscriminantExponent K M (H ⊔ lowerRamificationGroup K M s) -
      subgroupSlope K M t * (H ⊔ lowerRamificationGroup K M s).index =
        subgroupIntercept K M H t := by
  have h₁ : ∑ i ∈ Ico t ((largestLowerJump K M).toNat + 1),
      ((H ⊔ lowerRamificationGroup K M s).index : ℚ) *
        ((Nat.card (lowerRamificationGroup K M i) : ℚ) -
          Nat.card ↥((H ⊔ lowerRamificationGroup K M s) ⊓ lowerRamificationGroup K M i)) = 0 :=
    sum_eq_zero fun i hi ↦ by
      rw [sup_inf_lowerRamificationGroup_of_le H (hst.trans (mem_Ico.mp hi).1), sub_self, mul_zero]
  have h₂ : ∑ i ∈ range t, ((H ⊔ lowerRamificationGroup K M s).index : ℚ) *
      Nat.card ↥((H ⊔ lowerRamificationGroup K M s) ⊓ lowerRamificationGroup K M i) =
        ∑ i ∈ range t, (H.index : ℚ) * Nat.card ↥(H ⊓ lowerRamificationGroup K M i) :=
    sum_congr rfl fun i hi ↦
      index_sup_mul_card_inf_lowerRamificationGroup H (by have := mem_range.mp hi; omega)
  rw [subgroupDiscriminantExponent_sub_subgroupSlope_mul _ ht, h₁, h₂, zero_sub, subgroupIntercept]

lemma subgroupDiscriminantExponent_top : subgroupDiscriminantExponent K M ⊤ = 0 := by
  simp [subgroupDiscriminantExponent]

lemma subgroupSlope_zero : subgroupSlope K M 0 = 0 := by
  simp [subgroupSlope]

lemma subgroupIntercept_zero : subgroupIntercept K M H 0 = 0 := by
  simp [subgroupIntercept]

lemma subgroupSlope_one : subgroupSlope K M 1 = 1 := by
  rw [subgroupSlope, sum_range_one]
  exact div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

lemma subgroupSlope_succ : subgroupSlope K M (t + 1) =
    subgroupSlope K M t + Nat.card (lowerRamificationGroup K M t) /
      Nat.card (lowerRamificationGroup K M 0) := by
  rw [subgroupSlope, subgroupSlope, sum_range_succ, add_div]

lemma subgroupSlope_strictMono : StrictMono (subgroupSlope K M) :=
  strictMono_nat_of_lt_succ fun t ↦ by
    rw [subgroupSlope_succ]
    exact lt_add_of_pos_right _ (div_pos (Nat.cast_pos.mpr Nat.card_pos)
      (Nat.cast_pos.mpr Nat.card_pos))

lemma one_lt_subgroupSlope_iff : 1 < subgroupSlope K M t ↔ 2 ≤ t := by
  have h : subgroupSlope K M 1 = 1 := subgroupSlope_one
  rw [← h, subgroupSlope_strictMono.lt_iff_lt]
  omega

lemma slopeVertexSubgroup_succ_le :
    slopeVertexSubgroup K M H (t + 1) ≤ slopeVertexSubgroup K M H t := by
  rcases t with _ | t
  · exact le_top
  · exact sup_le_sup_left (lowerRamificationGroup_antitone K M (by omega)) H

variable (t) in
lemma le_slopeVertexSubgroup : H ≤ slopeVertexSubgroup K M H t := by
  rcases t with _ | t
  · exact le_top
  · exact le_sup_left

lemma index_slopeVertexSubgroup_zero : (slopeVertexSubgroup K M H 0).index = 1 :=
  Subgroup.index_top

lemma sup_lowerRamificationGroup_largestLowerJump :
    H ⊔ lowerRamificationGroup K M ((largestLowerJump K M).toNat + 1 : ℕ) = H := by
  rw [lowerRamificationGroup_largestLowerJump_toNat_add_one K M, sup_bot_eq]

lemma slopeVertexSubgroup_largestLowerJump :
    slopeVertexSubgroup K M H ((largestLowerJump K M).toNat + 1 + 1) = H :=
  sup_lowerRamificationGroup_largestLowerJump

lemma subgroupDiscriminantExponent_slopeVertexSubgroup_sub
    (ht : t ≤ (largestLowerJump K M).toNat + 1) :
    subgroupDiscriminantExponent K M (slopeVertexSubgroup K M H t) -
      subgroupSlope K M t * (slopeVertexSubgroup K M H t).index = subgroupIntercept K M H t := by
  rcases t with _ | t
  · rw [slopeVertexSubgroup, subgroupDiscriminantExponent_top, subgroupSlope_zero,
      subgroupIntercept_zero, zero_mul, sub_zero]
  · exact subgroupDiscriminantExponent_sup_sub H (Nat.le_succ t) le_rfl ht

lemma subgroupDiscriminantExponent_slopeVertexSubgroup_succ_sub
    (ht : t ≤ (largestLowerJump K M).toNat + 1) :
    subgroupDiscriminantExponent K M (slopeVertexSubgroup K M H (t + 1)) -
      subgroupSlope K M t * (slopeVertexSubgroup K M H (t + 1)).index =
        subgroupIntercept K M H t :=
  subgroupDiscriminantExponent_sup_sub H le_rfl (Nat.le_succ t) ht

variable (H) in
/-- **The vertices of the slope polygon of a subgroup**: for a subgroup `H` of the Galois group `G`
of `M / K`, the points `([G : X], c(X))` of the subgroups `X = G, H G_0, H G_1, …, H G_{T + 1} = H`
are the vertices of the lower convex hull of the points `([G : J], c(J))` of the subgroups
`J ⊇ H`, with slopes `τ_0 = 0, τ_1 = 1, τ_2, …, τ_{T + 1}`. -/
lemma isLowerHullVertices_subgroupSlopePoints :
    IsLowerHullVertices (subgroupSlopePoints K M H) ((largestLowerJump K M).toNat + 1)
      (fun t ↦ (slopeVertexSubgroup K M H t).index)
      (fun t ↦ (subgroupDiscriminantExponent K M (slopeVertexSubgroup K M H t) : ℝ))
      (fun t ↦ (subgroupSlope K M t : ℝ)) where
  mem t _ := ⟨slopeVertexSubgroup K M H t, le_slopeVertexSubgroup t, rfl⟩
  le_succ _ _ := Subgroup.index_antitone slopeVertexSubgroup_succ_le
  eq_add_mul t ht := by
    have h₁ : (subgroupDiscriminantExponent K M (slopeVertexSubgroup K M H t) : ℝ) -
        subgroupSlope K M t * (slopeVertexSubgroup K M H t).index = subgroupIntercept K M H t := by
      exact_mod_cast subgroupDiscriminantExponent_slopeVertexSubgroup_sub ht
    have h₂ : (subgroupDiscriminantExponent K M (slopeVertexSubgroup K M H (t + 1)) : ℝ) -
        subgroupSlope K M t * (slopeVertexSubgroup K M H (t + 1)).index =
          subgroupIntercept K M H t := by
      exact_mod_cast subgroupDiscriminantExponent_slopeVertexSubgroup_succ_sub ht
    linear_combination h₂ - h₁
  add_mul_le q hq t ht := by
    rcases hq with ⟨J, hJ, rfl⟩
    have h₁ : (subgroupDiscriminantExponent K M (slopeVertexSubgroup K M H t) : ℝ) -
        subgroupSlope K M t * (slopeVertexSubgroup K M H t).index = subgroupIntercept K M H t := by
      exact_mod_cast subgroupDiscriminantExponent_slopeVertexSubgroup_sub ht
    have h₂ : (subgroupIntercept K M H t : ℝ) ≤
        subgroupDiscriminantExponent K M J - subgroupSlope K M t * J.index := by
      exact_mod_cast subgroupIntercept_le hJ ht
    dsimp only
    linarith
  mem_Icc q hq := by
    rcases hq with ⟨J, hJ, rfl⟩
    dsimp only
    rw [index_slopeVertexSubgroup_zero, slopeVertexSubgroup_largestLowerJump, Nat.cast_one]
    exact ⟨Nat.one_le_cast.mpr (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite),
      Nat.cast_le.mpr (Subgroup.index_antitone hJ)⟩

variable (H i) in
lemma sup_lowerRamificationGroup_le_sup_zero :
    H ⊔ lowerRamificationGroup K M i ≤ H ⊔ lowerRamificationGroup K M 0 :=
  sup_le_sup_left (lowerRamificationGroup_antitone K M (by omega)) H

lemma subgroupDiscriminantExponent_sub_eq_mul (hJ : J ≤ H ⊔ lowerRamificationGroup K M 0) :
    subgroupDiscriminantExponent K M J - subgroupSlope K M t * J.index =
      (H ⊔ lowerRamificationGroup K M 0).index * (subgroupMeanOrdinate K M H J -
        (subgroupSlope K M t - 1) * subgroupMeanAbscissa K M H J - 1) := by
  have hf : ((H ⊔ lowerRamificationGroup K M 0).index : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have e :
      (J.index : ℚ) = subgroupMeanAbscissa K M H J * (H ⊔ lowerRamificationGroup K M 0).index := by
    exact_mod_cast (Subgroup.relIndex_mul_index hJ).symm
  rw [subgroupMeanOrdinate, e]
  field_simp
  ring1

variable (H) in
/-- **The vertices of the slope polygon of the subgroups between `H` and `H G_0`**: for a subgroup
`H` of the Galois group `G` of `M / K`, the points `([H G_0 : X], c(X) / f - [H G_0 : X] + 1)`, with
`f = [G : H G_0]`, of the subgroups `X = H G_0, H G_1, …, H G_{T + 1} = H` are the vertices of the
lower convex hull of the points of the subgroups `H ⊆ J ⊆ H G_0`, with slopes `τ_{t + 1} - 1`. -/
lemma isLowerHullVertices_subgroupMeanPoints :
    IsLowerHullVertices (subgroupMeanPoints K M H) (largestLowerJump K M).toNat
      (fun t ↦ subgroupMeanAbscissa K M H (H ⊔ lowerRamificationGroup K M t))
      (fun t ↦ (subgroupMeanOrdinate K M H (H ⊔ lowerRamificationGroup K M t) : ℝ))
      (fun t ↦ (subgroupSlope K M (t + 1) - 1 : ℚ)) where
  mem t _ := ⟨H ⊔ lowerRamificationGroup K M t,
    ⟨le_sup_left, sup_lowerRamificationGroup_le_sup_zero H t⟩, rfl⟩
  le_succ t _ := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.relIndex_dvd_of_le_left _ (sup_le_sup_left (lowerRamificationGroup_antitone K M
      (by omega)) H))
  eq_add_mul t ht := by
    have hf : ((H ⊔ lowerRamificationGroup K M 0).index : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
    have h₁ : subgroupDiscriminantExponent K M (H ⊔ lowerRamificationGroup K M t) -
        subgroupSlope K M (t + 1) * (H ⊔ lowerRamificationGroup K M t).index =
          subgroupIntercept K M H (t + 1) :=
      subgroupDiscriminantExponent_sup_sub H (Nat.le_succ t) le_rfl (by omega)
    have h₂ : subgroupDiscriminantExponent K M (H ⊔ lowerRamificationGroup K M (t + 1 : ℕ)) -
        subgroupSlope K M (t + 1) * (H ⊔ lowerRamificationGroup K M (t + 1 : ℕ)).index =
          subgroupIntercept K M H (t + 1) :=
      subgroupDiscriminantExponent_sup_sub H le_rfl (Nat.le_succ _) (by omega)
    rw [subgroupDiscriminantExponent_sub_eq_mul (sup_lowerRamificationGroup_le_sup_zero H t)] at h₁
    rw [subgroupDiscriminantExponent_sub_eq_mul
      (sup_lowerRamificationGroup_le_sup_zero H (t + 1))] at h₂
    have h : subgroupMeanOrdinate K M H (H ⊔ lowerRamificationGroup K M (t + 1 : ℕ)) =
        subgroupMeanOrdinate K M H (H ⊔ lowerRamificationGroup K M t) +
          (subgroupSlope K M (t + 1) - 1) *
            ((subgroupMeanAbscissa K M H (H ⊔ lowerRamificationGroup K M (t + 1 : ℕ)) : ℚ) -
              subgroupMeanAbscissa K M H (H ⊔ lowerRamificationGroup K M t)) := by
      linear_combination mul_left_cancel₀ hf (h₂.trans h₁.symm)
    exact_mod_cast h
  add_mul_le q hq t ht := by
    rcases hq with ⟨J, ⟨hHJ, hJ⟩, rfl⟩
    have hf : (0 : ℚ) < (H ⊔ lowerRamificationGroup K M 0).index :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    have h₁ : subgroupDiscriminantExponent K M (H ⊔ lowerRamificationGroup K M t) -
        subgroupSlope K M (t + 1) * (H ⊔ lowerRamificationGroup K M t).index =
          subgroupIntercept K M H (t + 1) :=
      subgroupDiscriminantExponent_sup_sub H (Nat.le_succ t) le_rfl (by omega)
    have h₂ : subgroupIntercept K M H (t + 1) ≤
        subgroupDiscriminantExponent K M J - subgroupSlope K M (t + 1) * J.index :=
      subgroupIntercept_le hHJ (by omega)
    rw [subgroupDiscriminantExponent_sub_eq_mul (sup_lowerRamificationGroup_le_sup_zero H t)] at h₁
    rw [subgroupDiscriminantExponent_sub_eq_mul hJ, ← h₁] at h₂
    have h : subgroupMeanOrdinate K M H (H ⊔ lowerRamificationGroup K M t) +
        (subgroupSlope K M (t + 1) - 1) * ((subgroupMeanAbscissa K M H J : ℚ) -
          subgroupMeanAbscissa K M H (H ⊔ lowerRamificationGroup K M t)) ≤
            subgroupMeanOrdinate K M H J := by
      linarith [le_of_mul_le_mul_left h₂ hf]
    dsimp only
    exact_mod_cast h
  mem_Icc q hq := by
    rcases hq with ⟨J, ⟨hHJ, hJ⟩, rfl⟩
    dsimp only
    rw [Nat.cast_zero, sup_lowerRamificationGroup_largestLowerJump]
    simp only [subgroupMeanAbscissa]
    rw [Subgroup.relIndex_self, Nat.cast_one]
    exact ⟨Nat.one_le_cast.mpr (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite),
      Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.relIndex_dvd_of_le_left _ hHJ))⟩

variable (H) in
lemma index_sup_mul_relIndex (j : ℤ) : (H ⊔ lowerRamificationGroup K M j).index *
    H.relIndex (lowerRamificationGroup K M j) = H.index := by
  rw [← Subgroup.relIndex_sup_of_normal, mul_comm]
  exact H.relIndex_mul_index le_sup_left

variable [IsGalois K M]

variable (t) in
/-- **The slopes are `1 + φ`**: `τ_{t + 1} = 1 + φ(t)` for the Herbrand function `φ` of `M / K`. -/
lemma natCast_subgroupSlope_succ : (subgroupSlope K M (t + 1) : ℝ) =
    1 + herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := by
  rw [coe_herbrand_of_coe_eq_natCast K M t (u := ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) rfl,
    sum_Icc_one_eq_sum_range, subgroupSlope, sum_range_succ']
  have h₀ : (Nat.card (lowerRamificationGroup K M 0) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  field_simp
  ring1

variable (H i) in
/-- **Consecutive vertices differ by a power of `p`**: for `i ≥ 0`, the index of `H G_{i + 2}` is
`p ^ m` times that of `H G_{i + 1}`, where `p ^ m = [G_{i + 1} : H ∩ G_{i + 1}] /
[G_{i + 2} : H ∩ G_{i + 2}]` and `p` is the residue characteristic. -/
lemma index_sup_lowerRamificationGroup_add_two :
    (H ⊔ lowerRamificationGroup K M (i + 2 : ℕ)).index =
      (H ⊔ lowerRamificationGroup K M (i + 1 : ℕ)).index * ringChar 𝓀[K] ^
        padicValNat (ringChar 𝓀[K]) (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
          H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨hp⟩
  rcases exists_relIndex_lowerRamificationGroup_eq_pow K M H (by omega : 1 ≤ i + 1) with ⟨a, ha⟩
  rcases exists_relIndex_lowerRamificationGroup_eq_pow K M H (by omega : 1 ≤ i + 2) with ⟨b, hb⟩
  have hba : b ≤ a := by
    have h : H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ)) ≤
        H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) :=
      Subgroup.relIndex_le_of_le_right (lowerRamificationGroup_antitone K M (by omega))
        Subgroup.index_ne_zero_of_finite
    rw [ha, hb] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  have h₁ : (H ⊔ lowerRamificationGroup K M (i + 1 : ℕ)).index * ringChar 𝓀[K] ^ a = H.index := by
    rw [← ha]
    exact index_sup_mul_relIndex H (i + 1 : ℕ)
  have h₂ : (H ⊔ lowerRamificationGroup K M (i + 2 : ℕ)).index * ringChar 𝓀[K] ^ b = H.index := by
    rw [← hb]
    exact index_sup_mul_relIndex H (i + 2 : ℕ)
  rw [ha, hb, Nat.pow_div hba hp.pos, padicValNat.prime_pow]
  refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos b) ?_
  rw [h₂, ← h₁, mul_assoc, ← pow_add, Nat.sub_add_cancel hba]

variable (H i) in
lemma natCast_index_div_index_sup_lowerRamificationGroup :
    ((H ⊔ lowerRamificationGroup K M (i + 2 : ℕ)).index : ℝ) /
      (H ⊔ lowerRamificationGroup K M (i + 1 : ℕ)).index = (ringChar 𝓀[K] ^
        padicValNat (ringChar 𝓀[K]) (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
          H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) : ℕ) := by
  rw [index_sup_lowerRamificationGroup_add_two H i, Nat.cast_mul,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite)]

variable (H i) in
lemma ite_replicate_eq_replicate_padicValNat :
    (if (H ⊔ lowerRamificationGroup K M (i + 1 : ℕ)).index <
        (H ⊔ lowerRamificationGroup K M (i + 2 : ℕ)).index ∧ 1 < (subgroupSlope K M (i + 2) : ℝ)
      then Multiset.replicate (Nat.log (ringChar 𝓀[K])
        ⌊((H ⊔ lowerRamificationGroup K M (i + 2 : ℕ)).index : ℝ) /
          (H ⊔ lowerRamificationGroup K M (i + 1 : ℕ)).index⌋₊) (subgroupSlope K M (i + 2) : ℝ)
      else 0) =
      Multiset.replicate (padicValNat (ringChar 𝓀[K])
        (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
          H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))))
        ((herbrand K M ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ : ℝ) + 1) := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  rw [natCast_index_div_index_sup_lowerRamificationGroup H i, Nat.floor_natCast,
    Nat.log_pow hp.one_lt]
  set m : ℕ := padicValNat (ringChar 𝓀[K]) (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
    H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ)))
  have hn : (H ⊔ lowerRamificationGroup K M (i + 2 : ℕ)).index =
      (H ⊔ lowerRamificationGroup K M (i + 1 : ℕ)).index * ringChar 𝓀[K] ^ m :=
    index_sup_lowerRamificationGroup_add_two H i
  have hτ : (subgroupSlope K M (i + 2) : ℝ) =
      (herbrand K M ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ : ℝ) + 1 := by
    rw [natCast_subgroupSlope_succ (i + 1), add_comm]
  rw [hτ]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm, Multiset.replicate_zero]
    exact ite_eq_right fun h ↦ h.1.ne (by rw [hn, hm, pow_zero, mul_one])
  · have hlt : (H ⊔ lowerRamificationGroup K M (i + 1 : ℕ)).index <
        (H ⊔ lowerRamificationGroup K M (i + 2 : ℕ)).index := by
      rw [hn]
      exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Nat.one_lt_pow hm.ne' hp.one_lt)
    rw [ite_eq_left ⟨hlt, by rw [← hτ]; exact_mod_cast one_lt_subgroupSlope_iff.mpr (by omega)⟩]

variable (H) in
/-- **The wild slopes of the slope polygon of a subgroup are the Swan slopes plus `1`**: for a
subgroup `H` of the Galois group of `M / K`, the slopes `τ_t > 1` of the polygon through the points
of `G, H G_0, H G_1, …, H G_{T + 1}` whose abscissas `n_t < n_{t + 1}` differ, each repeated
`log_p (n_{t + 1} / n_t)` times, are the Swan slopes of `M^H / K` plus `1`: the `1 + φ(i)`, `i ≥ 1`,
each repeated `log_p ([G_i : H ∩ G_i] / [G_{i + 1} : H ∩ G_{i + 1}])` times. -/
lemma sum_filter_replicate_eq_map_swanSlopesOfSubgroup :
    ∑ t ∈ (range ((largestLowerJump K M).toNat + 1 + 1)).filter (fun t ↦
        (slopeVertexSubgroup K M H t).index < (slopeVertexSubgroup K M H (t + 1)).index ∧
          1 < (subgroupSlope K M t : ℝ)),
      Multiset.replicate (Nat.log (ringChar 𝓀[K]) ⌊((slopeVertexSubgroup K M H (t + 1)).index : ℝ) /
        (slopeVertexSubgroup K M H t).index⌋₊) (subgroupSlope K M t : ℝ) =
      (swanSlopesOfSubgroup K M H).map (· + 1) := by
  have hP (t : ℕ) (ht : t ≤ 1) : ¬((slopeVertexSubgroup K M H t).index <
      (slopeVertexSubgroup K M H (t + 1)).index ∧ 1 < (subgroupSlope K M t : ℝ)) :=
    fun h ↦ absurd (one_lt_subgroupSlope_iff.mp (by exact_mod_cast h.2)) (by omega)
  rw [sum_filter, sum_range_succ', sum_range_succ', ite_eq_right (hP (0 + 1) (by omega)),
    ite_eq_right (hP 0 (by omega)), add_zero, add_zero, swanSlopesOfSubgroup,
    ← Multiset.coe_mapAddMonoidHom, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate]
  exact ite_replicate_eq_replicate_padicValNat H i

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [Algebra L M] [IsScalarTower K L M] [ValuativeExtension L M] [Module.Finite L M]
  [ValuativeExtension K L]

lemma natCast_differentExponent_mul_card : (differentExponent K L : ℚ) *
    Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K).range ⊓ lowerRamificationGroup K M 0) =
      ∑ i ∈ range ((largestLowerJump K M).toNat + 1),
        ((Nat.card (lowerRamificationGroup K M i) : ℚ) -
          Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K).range ⊓
            lowerRamificationGroup K M i)) := by
  have hL : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  set H : Subgroup (M ≃ₐ[K] M) := (AlgEquiv.restrictScalarsHom (S := L) K).range
  set T : ℕ := (largestLowerJump K M).toNat
  have hbot (i : ℕ) (hi : T + 1 ≤ i) : lowerRamificationGroup K M i = ⊥ :=
    lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (by omega)
  have hcard (i : ℤ) :
      Nat.card (lowerRamificationGroup L M i) = Nat.card ↥(H ⊓ lowerRamificationGroup K M i) := by
    rw [← map_restrictScalarsHom_lowerRamificationGroup K M L,
      Subgroup.card_map_of_injective (AlgEquiv.restrictScalars_injective K)]
  have hKM : (differentExponent K M : ℝ) =
      ∑ i ∈ range (T + 1), ((Nat.card (lowerRamificationGroup K M i) : ℝ) - 1) :=
    natCast_differentExponent_eq_sum_range fun i hi ↦ by rw [hbot i hi, Subgroup.card_bot]
  have hLM : (differentExponent L M : ℝ) =
      ∑ i ∈ range (T + 1), ((Nat.card ↥(H ⊓ lowerRamificationGroup K M i) : ℝ) - 1) := by
    rw [natCast_differentExponent_eq_sum_range fun i hi ↦ by
      rw [hcard, hbot i hi, inf_bot_eq, Subgroup.card_bot]]
    exact sum_congr rfl fun i _ ↦ by rw [hcard]
  have htower : (differentExponent K M : ℝ) =
      differentExponent L M + ramificationIndex L M * differentExponent K L := by
    exact_mod_cast differentExponent_tower K L M
  have hB : (ramificationIndex L M : ℝ) = Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) := by
    rw [← natCard_lowerRamificationGroup_zero L M, hcard]
  have h : (differentExponent K L : ℝ) * Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) =
      ∑ i ∈ range (T + 1), ((Nat.card (lowerRamificationGroup K M i) : ℝ) -
        Nat.card ↥(H ⊓ lowerRamificationGroup K M i)) := by
    have hs : ∑ i ∈ range (T + 1), ((Nat.card (lowerRamificationGroup K M i) : ℝ) -
        Nat.card ↥(H ⊓ lowerRamificationGroup K M i)) =
          differentExponent K M - differentExponent L M := by
      rw [hKM, hLM, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ by ring1
    rw [hs, htower, hB]
    ring1
  exact_mod_cast h

variable [Algebra.IsSeparable K L] in
/-- **The discriminant exponent of an intermediate field from its Galois group**: in a tower
`M / L / K` of nonarchimedean local fields with `M / K` finite Galois, the discriminant exponent of
`L / K` is `c(Gal(M / L)) = [G : Gal(M / L)] ∑_{i ≥ 0} (#G_i - #(Gal(M / L) ∩ G_i)) / #G_0`. -/
lemma natCast_discriminantExponent_eq_subgroupDiscriminantExponent :
    (discriminantExponent K L : ℚ) =
      subgroupDiscriminantExponent K M (AlgEquiv.restrictScalarsHom (S := L) K).range := by
  have hcard' : (ramificationIndex K L : ℚ) *
      Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K).range ⊓ lowerRamificationGroup K M 0) =
        Nat.card (lowerRamificationGroup K M 0) := by
    rw [← relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom K M L]
    exact_mod_cast Subgroup.relIndex_mul_card _ _
  have hef : (ramificationIndex K L : ℚ) * inertiaDegree K L = Module.finrank K L := by
    exact_mod_cast ramificationIndex_mul_inertiaDegree K L
  have he : (ramificationIndex K L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ramificationIndex_pos.ne'
  have hh : (Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K).range ⊓
      lowerRamificationGroup K M 0) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent, subgroupDiscriminantExponent,
    AlgEquiv.index_range_restrictScalarsHom K L M, ← natCast_differentExponent_mul_card, ← hcard',
    ← hef]
  push_cast
  field_simp

end IsNonarchimedeanLocalField
