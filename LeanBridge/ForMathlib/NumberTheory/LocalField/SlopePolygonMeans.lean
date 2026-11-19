import LeanBridge.ForMathlib.NumberTheory.LocalField.HerbrandInvariantCompatibility
import LeanBridge.ForMathlib.NumberTheory.LocalField.VisibleSlopes
import TauCeti.NumberTheory.LocalField.Discriminant.Tower

/-!
# The means of an extension of `p`-adic fields from its slope polygon

Let `L / K` be a finite separable extension of nonarchimedean local fields of residue
characteristic `p`, inside `K̄`, with residue degree `f`, ramification index `e = ε p ^ w` and
discriminant exponent `c`. LMFDB `lf.means` defines the mean `m` of `L / K` by `c = f (e - 1 + e m)`
(`IsNonarchimedeanLocalField.extensionMean`), so that the height `H(L / K)` of LMFDB `lf.heights`,
defined by `c = f (e - 1 + H(L / K))` (`IsNonarchimedeanLocalField.extensionHeight`), is `e m`. Let
`K_f` be the maximal unramified subextension of `L / K`. The slope polygon `S` of `L / K`
(`IsNonarchimedeanLocalField.meanPolygon`) is the lower boundary of the convex hull of the points
`(e', e' m')` of the subextensions `L' / K_f` of `L / K_f`, with `e' = [L' : K_f]` and `m'` the mean
of `L' / K_f`. It is the graph of a function `h` on `[1, e]`, `e = [L : K_f]`, and the means of
`L / K` are `m_k = h(ε p ^ k) / (ε p ^ k)` for `1 ≤ k ≤ w`
(`IsNonarchimedeanLocalField.polygonMean`).

We prove that these are the means `m_k = ∑_{j ≤ k} (p - 1) r_j / (ε p ^ j)` of the Herbrand
invariant `(r_1, …, r_w)_ε^f` of `L / K` (LMFDB `lf.herbrand_invariant`), which gives the knowl's
relations `(p - 1) s_k = p m_k - m_{k - 1}`, `m_0 = 0`, with the Swan slopes `s_k` of LMFDB
`lf.slopes`, read off the convex hull of the points of the subextensions of `L / K`. Let `M` be the
Galois closure of `L` in `K̄`, with group `G`, lower ramification groups `G_i`, Herbrand function
`φ_{M/K}` and `H = Gal(M / L)`. Then `K_f` is the fixed field of `H G_0`, and the subextension `L'`
fixed by `H ⊆ J ⊆ H G_0` is totally ramified over `K_f`, of degree `e' = [H G_0 : J]` and
discriminant exponent `c(J) / f`, so that `e' m' = c(J) / f - e' + 1`. The vertices of `S` are the
points of the subgroups `H G_t`, with slopes `φ_{M/K}(t)`
(`IsNonarchimedeanLocalField.isLowerHullVertices_subgroupMeanPoints`), and the line of slope
`φ_{M/K}(t)` through them is `x ↦ x φ_{M/K}(t) - φ_{M/L}(t)`, for the Herbrand function
`φ_{M/L}(t) = (#H_1 + ⋯ + #H_t) / #H_0` of `M / L`. The abscissa `ε p ^ k` lies on the segment of
slope `φ_{M/K}(t)` exactly when `r_k ≤ φ_{M/L}(t) ≤ r_{k + 1}`, where the Herbrand function of the
invariant gives `φ_{M/K}(t) = s_k + (φ_{M/L}(t) - r_k) / (ε p ^ k)`, so that
`h(ε p ^ k) = ε p ^ k s_k - r_k = ε p ^ k m_k`.

## Main definitions

* `IsNonarchimedeanLocalField.extensionMean` (LMFDB `lf.means`): the mean `m` of `L / K`.
* `IsNonarchimedeanLocalField.extensionHeight` (LMFDB `lf.heights`): the height `H(L / K)`.
* `IsNonarchimedeanLocalField.intermediateDegree` and `IsNonarchimedeanLocalField.intermediateMean`:
  the degree and the mean of a subextension `E / F` of `K̄ / K`.
* `IsNonarchimedeanLocalField.meanPoints` (LMFDB `lf.means`): the points `(e', e' m')`.
* `IsNonarchimedeanLocalField.meanPolygon` (LMFDB `lf.means`): the slope polygon `S`.
* `IsNonarchimedeanLocalField.meanPolygonFunction` (LMFDB `lf.means`): the function `h`.
* `IsNonarchimedeanLocalField.polygonMean` (LMFDB `lf.means`): the means `m_k`.

## Main results

* `IsNonarchimedeanLocalField.natCast_discriminantExponent_eq_extensionMean` and
  `IsNonarchimedeanLocalField.eq_extensionMean_iff` (LMFDB `lf.means`): the mean is the number
  determined by `c = f (e - 1 + e m)`.
* `IsNonarchimedeanLocalField.extensionHeight_eq_mul_extensionMean` (LMFDB `lf.means`,
  `lf.heights`): `H(L / K) = e m`.
* `IsNonarchimedeanLocalField.le_unramifiedExtension_of_isUnramified` (LMFDB `lf.means`): the
  unramified extension `K_f ⊆ L` of degree `f` is the maximal unramified subextension of `L / K`.
* `IsNonarchimedeanLocalField.meanPolygon_eq` (LMFDB `lf.means`): the slope polygon is the graph of
  `h` on `[1, e]`, with `e = [L : K_f]`
  (`IsNonarchimedeanLocalField.intermediateDegree_unramifiedExtension_le`).
* `IsNonarchimedeanLocalField.polygonMean_zero` (LMFDB `lf.means`): `m_0 = 0`.
* `IsNonarchimedeanLocalField.polygonMean_eq_mean` (LMFDB `lf.means`, `lf.herbrand_invariant`): the
  means read off the slope polygon are the means of the Herbrand invariant of `L / K`, so that the
  points `(ε p ^ k, ε p ^ k m_k)` lie on the polygon.
* `IsNonarchimedeanLocalField.sort_hullWildSwanSlopes_eq` (LMFDB `lf.means`): the Swan slopes
  `s_1 ≤ ⋯ ≤ s_w` of LMFDB `lf.slopes` satisfy `(p - 1) s_k = p m_k - m_{k - 1}`.
* `IsNonarchimedeanLocalField.extensionMean_eq_polygonMean` (LMFDB `lf.means`): the mean of `L / K`
  is its last mean `m_w`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §4, and Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  appendix.
-/

open ValuativeRel TauCeti LocalFieldsRamification Set

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

section Mean

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

/-- The **mean** `m` (LMFDB `lf.means`) of a finite separable extension `L / K` of nonarchimedean
local fields: the number determined by `c = f (e - 1 + e m)`, for the discriminant exponent `c`, the
residue degree `f` and the ramification index `e` of `L / K`. -/
noncomputable def extensionMean : ℚ :=
  ((discriminantExponent K L : ℚ) / inertiaDegree K L - ramificationIndex K L + 1) /
    ramificationIndex K L

/-- The **height** `H(L / K)` (LMFDB `lf.heights`) of a finite separable extension `L / K` of
nonarchimedean local fields: the number determined by `c = f (e - 1 + H(L / K))`, for the
discriminant exponent `c`, the residue degree `f` and the ramification index `e` of `L / K`. -/
noncomputable def extensionHeight : ℚ :=
  (discriminantExponent K L : ℚ) / inertiaDegree K L - ramificationIndex K L + 1

/-- **The defining formula of the mean** (LMFDB `lf.means`): `c = f (e - 1 + e m)`. -/
lemma natCast_discriminantExponent_eq_extensionMean : (discriminantExponent K L : ℚ) =
    inertiaDegree K L *
        (ramificationIndex K L - 1 + ramificationIndex K L * extensionMean K L) := by
  have he : (ramificationIndex K L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ramificationIndex_pos.ne'
  have hf : (inertiaDegree K L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr inertiaDegree_pos.ne'
  rw [extensionMean]
  field_simp
  ring1

/-- **The mean is determined by its formula** (LMFDB `lf.means`): a rational number `m` satisfies
`c = f (e - 1 + e m)` exactly when it is the mean of `L / K`. -/
lemma eq_extensionMean_iff (m : ℚ) : (discriminantExponent K L : ℚ) =
    inertiaDegree K L * (ramificationIndex K L - 1 + ramificationIndex K L * m) ↔
      m = extensionMean K L := by
  have he : (ramificationIndex K L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ramificationIndex_pos.ne'
  have hf : (inertiaDegree K L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr inertiaDegree_pos.ne'
  have h₀ : (discriminantExponent K L : ℚ) = inertiaDegree K L *
      (ramificationIndex K L - 1 + ramificationIndex K L * extensionMean K L) :=
    natCast_discriminantExponent_eq_extensionMean K L
  refine ⟨fun h ↦ mul_left_cancel₀ (mul_ne_zero hf he) ?_, fun h ↦ h ▸ h₀⟩
  linear_combination h₀ - h

lemma natCast_discriminantExponent_eq_extensionHeight : (discriminantExponent K L : ℚ) =
    inertiaDegree K L * (ramificationIndex K L - 1 + extensionHeight K L) := by
  have hf : (inertiaDegree K L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr inertiaDegree_pos.ne'
  rw [extensionHeight]
  field_simp
  ring1

/-- **The height is `e` times the mean** (LMFDB `lf.means`, `lf.heights`): `H(L / K) = e m`. -/
lemma extensionHeight_eq_mul_extensionMean :
    extensionHeight K L = ramificationIndex K L * extensionMean K L := by
  have he : (ramificationIndex K L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ramificationIndex_pos.ne'
  rw [extensionHeight, extensionMean, mul_div_cancel₀ _ he]

end Mean

section Subgroup

variable {K M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  (H : Subgroup (M ≃ₐ[K] M)) (t : ℕ)

lemma subgroupMeanAbscissa_mul_relIndex :
    subgroupMeanAbscissa K M H (H ⊔ lowerRamificationGroup K M t) *
      H.relIndex (lowerRamificationGroup K M t) = H.relIndex (lowerRamificationGroup K M 0) := by
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite :
    (H ⊔ lowerRamificationGroup K M 0).index ≠ 0)) ?_
  rw [index_sup_mul_relIndex H 0, ← index_sup_mul_relIndex H t,
    ← Subgroup.relIndex_mul_index (sup_lowerRamificationGroup_le_sup_zero H t),
    subgroupMeanAbscissa]
  ring1

lemma subgroupMeanAbscissa_sup_zero :
    subgroupMeanAbscissa K M H (H ⊔ lowerRamificationGroup K M 0) = 1 := by
  rw [subgroupMeanAbscissa, Subgroup.relIndex_self]

lemma subgroupIntercept_succ_div_add_one : subgroupIntercept K M H (t + 1) /
    (H ⊔ lowerRamificationGroup K M 0).index + 1 = -herbrandOfSubgroup K M H t := by
  have hf : ((H ⊔ lowerRamificationGroup K M 0).index : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hg : (Nat.card (lowerRamificationGroup K M 0) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hh : (Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key : (H.index : ℚ) * Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) =
      (H ⊔ lowerRamificationGroup K M 0).index * Nat.card (lowerRamificationGroup K M 0) := by
    rw [← index_sup_mul_relIndex H 0, ← H.relIndex_mul_card (lowerRamificationGroup K M 0)]
    push_cast
    ring1
  induction t with
  | zero =>
    simp only [subgroupIntercept, zero_add, Finset.sum_range_one, Nat.cast_zero,
      herbrandOfSubgroup_zero]
    rw [key]
    field_simp
    ring1
  | succ t ih =>
    have hD : subgroupIntercept K M H (t + 1 + 1) = subgroupIntercept K M H (t + 1) -
        H.index * Nat.card ↥(H ⊓ lowerRamificationGroup K M (t + 1 : ℕ)) /
          Nat.card (lowerRamificationGroup K M 0) := by
      rw [subgroupIntercept, subgroupIntercept, Finset.sum_range_succ]
      ring1
    have e : (H.index : ℚ) * Nat.card ↥(H ⊓ lowerRamificationGroup K M (t + 1 : ℕ)) /
        Nat.card (lowerRamificationGroup K M 0) / (H ⊔ lowerRamificationGroup K M 0).index =
          Nat.card ↥(H ⊓ lowerRamificationGroup K M (t + 1 : ℕ)) /
            Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) := by
      rw [div_div, div_eq_div_iff (mul_ne_zero hg hf) hh]
      linear_combination (Nat.card ↥(H ⊓ lowerRamificationGroup K M (t + 1 : ℕ)) : ℚ) * key
    rw [hD, sub_div, e, herbrandOfSubgroup_succ]
    linear_combination ih

lemma subgroupMeanOrdinate_sub_mul (ht : t ≤ (largestLowerJump K M).toNat) :
    subgroupMeanOrdinate K M H (H ⊔ lowerRamificationGroup K M t) -
      (subgroupSlope K M (t + 1) - 1) *
        subgroupMeanAbscissa K M H (H ⊔ lowerRamificationGroup K M t) =
          -herbrandOfSubgroup K M H t := by
  have hf : ((H ⊔ lowerRamificationGroup K M 0).index : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have h₁ : subgroupDiscriminantExponent K M (H ⊔ lowerRamificationGroup K M t) -
      subgroupSlope K M (t + 1) * (H ⊔ lowerRamificationGroup K M t).index =
        subgroupIntercept K M H (t + 1) :=
    subgroupDiscriminantExponent_sup_sub H (Nat.le_succ t) le_rfl (by omega)
  rw [subgroupDiscriminantExponent_sub_eq_mul (sup_lowerRamificationGroup_le_sup_zero H t)] at h₁
  have h₂ : subgroupIntercept K M H (t + 1) / (H ⊔ lowerRamificationGroup K M 0).index + 1 =
      -herbrandOfSubgroup K M H t :=
    subgroupIntercept_succ_div_add_one H t
  rw [← h₁, mul_div_cancel_left₀ _ hf] at h₂
  linear_combination h₂

variable [IsGalois K M]

lemma relIndex_mul_pow_countP : H.relIndex (lowerRamificationGroup K M (t + 1 : ℕ)) *
    ringChar 𝓀[K] ^ (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) =
      ringChar 𝓀[K] ^ Multiset.card (ramsOfSubgroup K M H) := by
  have hs : (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) +
      ∑ i ∈ Finset.range (largestLowerJump K M).toNat, (if t + 1 ≤ i + 1 then
        padicValNat (ringChar 𝓀[K]) (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
          H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) else 0) =
        Multiset.card (ramsOfSubgroup K M H) := by
    rw [countP_le_herbrandOfSubgroup, ← Finset.sum_add_distrib, ramsOfSubgroup, Multiset.card_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Multiset.card_replicate]
    push_cast
    split_ifs <;> omega
  rw [relIndex_lowerRamificationGroup_eq_pow_sum K M H (by omega : 1 ≤ t + 1), ← pow_add, ← hs,
    add_comm]

lemma subgroupMeanAbscissa_sup_succ :
    subgroupMeanAbscissa K M H (H ⊔ lowerRamificationGroup K M (t + 1 : ℕ)) =
      ordCompl[ringChar 𝓀[K]] (H.relIndex (lowerRamificationGroup K M 0)) *
        ringChar 𝓀[K] ^ (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) := by
  have h₃ : ordCompl[ringChar 𝓀[K]] (H.relIndex (lowerRamificationGroup K M 0)) *
      ringChar 𝓀[K] ^ Multiset.card (ramsOfSubgroup K M H) =
        H.relIndex (lowerRamificationGroup K M 0) := by
    rw [card_ramsOfSubgroup, card_swanSlopesOfSubgroup, mul_comm]
    exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have h₄ : ordCompl[ringChar 𝓀[K]] (H.relIndex (lowerRamificationGroup K M 0)) *
      ringChar 𝓀[K] ^ (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) *
        H.relIndex (lowerRamificationGroup K M (t + 1 : ℕ)) =
          H.relIndex (lowerRamificationGroup K M 0) := by
    rw [mul_assoc, mul_comm (ringChar 𝓀[K] ^ _), relIndex_mul_pow_countP H t, h₃]
  refine Nat.eq_of_mul_eq_mul_right (m := H.relIndex (lowerRamificationGroup K M (t + 1 : ℕ)))
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) ?_
  rw [subgroupMeanAbscissa_mul_relIndex H (t + 1), h₄]

end Subgroup

section Correspondence

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {D E N : IntermediateField F Ω}

/-- The **degree** `[E : D]` of intermediate fields `D ≤ E` of an extension `Ω / F`, for the
inclusion of `D` in `E`. -/
noncomputable def intermediateDegree (h : D ≤ E) : ℕ :=
  letI : Algebra D E := (IntermediateField.inclusion h).toAlgebra
  Module.finrank D E

lemma finrank_mul_intermediateDegree (h : D ≤ E) :
    Module.finrank F D * intermediateDegree h = Module.finrank F E := by
  let a : Algebra D E := (IntermediateField.inclusion h).toAlgebra
  have hs : IsScalarTower F D E := .of_algebraMap_eq fun _ ↦ rfl
  exact Module.finrank_mul_finrank F D E

variable [FiniteDimensional F N] [IsGalois F N] in
lemma intermediateDegree_eq_relIndex (hDE : D ≤ E) (hEN : E ≤ N) : intermediateDegree hDE =
    (fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' E)).relIndex
      (fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' D)) := by
  let a : Algebra D E := (IntermediateField.inclusion hDE).toAlgebra
  have hs : IsScalarTower F D E := .of_algebraMap_eq fun _ ↦ rfl
  have hD : FiniteDimensional F D := IntermediateField.finiteDimensional_of_le (hDE.trans hEN)
  have h : (fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' E)).relIndex
      (fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' D)) * Module.finrank F D =
        Module.finrank F D * Module.finrank D E := by
    rw [Module.finrank_mul_finrank F D E, finrank_eq_index_fixingSubgroup hEN,
      finrank_eq_index_fixingSubgroup (hDE.trans hEN)]
    exact Subgroup.relIndex_mul_index (fixingSubgroup_antitone (N ≃ₐ[F] N) N
      (preimage_mono (f := ((↑) : N → Ω)) hDE))
  exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos (h.trans (mul_comm _ _))).symm

end Correspondence

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {E : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E]

/-- The **mean** `m(E / F)` (LMFDB `lf.means`) of intermediate fields `F ≤ E` of `K̄ / K`, finite
over `K` and with `E / K` separable, for Tau Ceti's spectral-norm local-field structures on `F` and
`E` and the inclusion of `F` in `E`. -/
noncomputable def intermediateMean {F : IntermediateField K (AlgebraicClosure K)}
    [FiniteDimensional K F] [Algebra.IsSeparable K E] (h : F ≤ E) : ℚ :=
  letI : Algebra F E := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower K F E := .of_algebraMap_eq fun _ ↦ rfl
  haveI : ValuativeExtension F E := (IntermediateField.inclusion h).valuativeExtension
  haveI : Algebra.IsSeparable F E := Algebra.isSeparable_tower_top_of_isSeparable K F E
  extensionMean F E

lemma relIndex_lowerRamificationGroup_zero_fixingSubgroup
    {N : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K N] [IsGalois K N]
    (h : E ≤ N) : (fixingSubgroup (N ≃ₐ[K] N) (((↑) : N → AlgebraicClosure K) ⁻¹' E)).relIndex
      (lowerRamificationGroup K N 0) = ramificationIndex K E := by
  let a : Algebra E N := (IntermediateField.inclusion h).toAlgebra
  have hs : IsScalarTower K E N := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension E N := (IntermediateField.inclusion h).valuativeExtension
  have hf : Module.Finite E N := .of_restrictScalars_finite K E N
  rw [fixingSubgroup_preimage_eq_range_restrictScalarsHom h]
  exact relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom K N E

variable (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]

/-- The **points `(e', e' m')`** (LMFDB `lf.means`) of a finite extension `L / K` inside `K̄`: for
each subextension `L' / K_f` of `L / K_f`, finite and separable over `K`, where `K_f` is the maximal
unramified subextension of `L / K` (the unramified extension of `K` of degree `f(L / K)` in `K̄`,
which lies in `L`), the degree `e' = [L' : K_f]` and `e' m'` for the mean `m'` of `L' / K_f`. -/
noncomputable def meanPoints : Set (ℝ × ℝ) :=
  {q | ∃ (L' : IntermediateField K (AlgebraicClosure K))
    (h : unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) ≤ L') (_ : L' ≤ L)
      (_ : FiniteDimensional K L') (_ : Algebra.IsSeparable K L'),
        q = ((intermediateDegree h : ℝ), (intermediateDegree h * intermediateMean h : ℝ))}

/-- The **slope polygon** `S` (LMFDB `lf.means`) of a finite extension `L / K` inside `K̄`: the
lower boundary of the convex hull of the points `(e', e' m')` of the subextensions `L' / K_f` of
`L / K_f`. -/
noncomputable def meanPolygon : Set (ℝ × ℝ) :=
  lowerConvexHull (meanPoints L)

/-- The **function** `h` (LMFDB `lf.means`) whose graph is the slope polygon `S` of a finite
extension `L / K` inside `K̄`, on `[1, e]` (`IsNonarchimedeanLocalField.meanPolygon_eq`): `h(x)` is
the least `y` with `(x, y)` on `S`. -/
noncomputable def meanPolygonFunction (x : ℝ) : ℝ :=
  sInf {y | (x, y) ∈ meanPolygon L}

/-- The `k`-th **mean** `m_k = h(ε p ^ k) / (ε p ^ k)` (LMFDB `lf.means`) of a finite extension
`L / K` inside `K̄`, for the tame degree `ε` of `L / K` and the residue characteristic `p`: the
means of `L / K` are `⟨m_1, …, m_w⟩`, and `m_0 = 0`. -/
noncomputable def polygonMean (k : ℕ) : ℝ :=
  meanPolygonFunction L (tameDegree K L * ringChar 𝓀[K] ^ k : ℕ) /
    (tameDegree K L * ringChar 𝓀[K] ^ k : ℕ)

lemma unramifiedExtension_inertiaDegree_le :
    unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) ≤ L := by
  rcases exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K L with ⟨ζ, hζ⟩
  rw [unramifiedExtension_eq_adjoin_simple inertiaDegree_pos.ne'
    (hζ.map_of_injective (algebraMap L (AlgebraicClosure K)).injective)]
  exact IntermediateField.adjoin_simple_le_iff.mpr ζ.2

variable [Algebra.IsSeparable K L] {L' : IntermediateField K (AlgebraicClosure K)}
  (h : unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) ≤ L')

lemma fixingSubgroup_unramifiedExtension :
    fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹'
        unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) =
      fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
        (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
          lowerRamificationGroup K (Algebra.galoisClosure K L) 0 := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  have hKfL : unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) ≤ L :=
    unramifiedExtension_inertiaDegree_le L
  have hur : IsUnramified K (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) :=
    isUnramified_unramifiedExtension inertiaDegree_pos.ne'
  have hG : lowerRamificationGroup K (Algebra.galoisClosure K L) 0 ≤
      fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
        (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹'
          unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) :=
    Subgroup.relIndex_eq_one.mp <| (relIndex_lowerRamificationGroup_zero_fixingSubgroup
      (hKfL.trans hLM)).trans <| (isUnramified_iff_ramificationIndex_eq_one _ _).mp hur
  have hle : fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
        lowerRamificationGroup K (Algebra.galoisClosure K L) 0 ≤
      fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
        (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹'
          unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) :=
    sup_le (fixingSubgroup_antitone _ _ (preimage_mono hKfL)) hG
  have hidx : (fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹'
        unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L))).index =
      (fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
        (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
          lowerRamificationGroup K (Algebra.galoisClosure K L) 0).index := by
    rw [← finrank_eq_index_fixingSubgroup (hKfL.trans hLM),
      finrank_unramifiedExtension inertiaDegree_pos.ne']
    refine Nat.eq_of_mul_eq_mul_right (m := ramificationIndex K L) ramificationIndex_pos ?_
    rw [← relIndex_lowerRamificationGroup_zero_fixingSubgroup hLM, index_sup_mul_relIndex,
      relIndex_lowerRamificationGroup_zero_fixingSubgroup hLM, mul_comm,
      ramificationIndex_mul_inertiaDegree K L, finrank_eq_index_fixingSubgroup hLM]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp (Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (((Subgroup.relIndex_mul_index hle).trans hidx.symm).trans (one_mul _).symm))) hle

lemma index_fixingSubgroup_sup_lowerRamificationGroup_zero :
    (fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
        lowerRamificationGroup K (Algebra.galoisClosure K L) 0).index = inertiaDegree K L := by
  rw [← fixingSubgroup_unramifiedExtension L, ← finrank_eq_index_fixingSubgroup
    ((unramifiedExtension_inertiaDegree_le L).trans (Algebra.le_galoisClosure L)),
    finrank_unramifiedExtension inertiaDegree_pos.ne']

lemma index_fixingSubgroup_sup_lowerRamificationGroup_one :
    (fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
        lowerRamificationGroup K (Algebra.galoisClosure K L) 1).index =
      inertiaDegree K L * tameDegree K L := by
  set H : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)
  have h₁ : subgroupMeanAbscissa K (Algebra.galoisClosure K L) H
      (H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) ((0 + 1 : ℕ) : ℤ)) =
        tameDegree K L := by
    rw [subgroupMeanAbscissa_sup_succ H 0, herbrandOfSubgroup_zero,
      Multiset.countP_eq_zero.mpr fun r hr ↦ (pos_of_mem_ramsOfSubgroup K _ H hr).not_ge, pow_zero,
      mul_one, relIndex_lowerRamificationGroup_zero_fixingSubgroup (Algebra.le_galoisClosure L),
      tameDegree]
  rw [← index_fixingSubgroup_sup_lowerRamificationGroup_zero L, ← h₁, mul_comm]
  exact (Subgroup.relIndex_mul_index (sup_lowerRamificationGroup_le_sup_zero H 1)).symm

lemma intermediateDegree_eq_subgroupMeanAbscissa (hL' : L' ≤ L) : intermediateDegree h =
    subgroupMeanAbscissa K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L')) := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  rw [intermediateDegree_eq_relIndex h (hL'.trans hLM), fixingSubgroup_unramifiedExtension L,
    subgroupMeanAbscissa]

variable [FiniteDimensional K L'] [Algebra.IsSeparable K L'] in
lemma intermediateDegree_mul_intermediateMean (hL' : L' ≤ L) : (intermediateDegree h : ℚ) *
    intermediateMean h = subgroupMeanOrdinate K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L')) := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  set H : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)
  set J : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L')
  have hx : intermediateDegree h = subgroupMeanAbscissa K (Algebra.galoisClosure K L) H J :=
    intermediateDegree_eq_subgroupMeanAbscissa L h hL'
  have hHJ : H ≤ J := fixingSubgroup_antitone _ _ (preimage_mono hL')
  have hJ : J ≤ H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0 := by
    rw [← fixingSubgroup_unramifiedExtension L]
    exact fixingSubgroup_antitone _ _ (preimage_mono h)
  have hcJ : (discriminantExponent K L' : ℚ) =
      subgroupDiscriminantExponent K (Algebra.galoisClosure K L) J :=
    natCast_discriminantExponent_eq_subgroupDiscriminantExponent_fixingSubgroup (hL'.trans hLM)
  have heJ : J.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0) =
      ramificationIndex K L' :=
    relIndex_lowerRamificationGroup_zero_fixingSubgroup (hL'.trans hLM)
  have hfK : (H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0).index =
      Module.finrank K (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) := by
    rw [← fixingSubgroup_unramifiedExtension L, finrank_eq_index_fixingSubgroup
      ((unramifiedExtension_inertiaDegree_le L).trans hLM)]
  let a : Algebra (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' :=
    (IntermediateField.inclusion h).toAlgebra
  have hs : IsScalarTower K (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hv :
      ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' :=
    (IntermediateField.inclusion h).valuativeExtension
  have hsep :
      Algebra.IsSeparable (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' :=
    Algebra.isSeparable_tower_top_of_isSeparable K _ L'
  have hur : IsUnramified K (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) :=
    isUnramified_unramifiedExtension inertiaDegree_pos.ne'
  have hm : intermediateMean h =
      extensionMean (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' :=
    rfl
  have hd : intermediateDegree h =
      Module.finrank (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' :=
    rfl
  have hc : (discriminantExponent K L' : ℚ) =
      Module.finrank K (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) *
        discriminantExponent (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L))
          L' := by
    rw [discriminantExponent_tower K
      (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L',
      (discriminantExponent_eq_zero_iff (K := K)
        (L := unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L))).mpr hur, mul_zero,
      zero_add, IsUnramified.inertiaDegree_eq_finrank (K := K)
        (L := unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)), Nat.cast_mul]
  have he : ramificationIndex (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' =
      intermediateDegree h := by
    have hJ' : J ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0 =
        H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0 :=
      le_antisymm (sup_le hJ le_sup_right) (sup_le_sup_right hHJ _)
    rw [IsUnramified.ramificationIndex_tower_eq (K := K), ← heJ, hx, subgroupMeanAbscissa, ← hJ',
      Subgroup.relIndex_sup_of_normal]
  have hf :
      inertiaDegree (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' = 1 := by
    have h₁ : intermediateDegree h *
        inertiaDegree (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L' =
          intermediateDegree h := by
      rw [← he, ramificationIndex_mul_inertiaDegree
        (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) L', he, hd]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by rw [hx]; exact
      Subgroup.index_ne_zero_of_finite)) (h₁.trans (mul_one _).symm)
  have hx₀ : (intermediateDegree h : ℚ) ≠ 0 := by
    rw [hx]
    exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hf₀ : ((H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0).index : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  rw [hm, extensionMean, hf, he, subgroupMeanOrdinate, ← hx, ← hcJ, hc, hfK]
  rw [hfK] at hf₀
  field_simp
  ring1

lemma meanPoints_eq : meanPoints L = subgroupMeanPoints K (Algebra.galoisClosure K L)
    (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  ext q
  constructor
  · rintro ⟨L', h, hL', hfin, hsep, rfl⟩
    refine ⟨fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L'),
      ⟨fixingSubgroup_antitone _ _ (preimage_mono hL'), ?_⟩, ?_⟩
    · rw [← fixingSubgroup_unramifiedExtension L]
      exact fixingSubgroup_antitone _ _ (preimage_mono h)
    · dsimp only
      rw [← intermediateDegree_eq_subgroupMeanAbscissa L h hL',
        ← intermediateDegree_mul_intermediateMean L h hL']
      push_cast
      rfl
  · rintro ⟨J, ⟨hHJ, hJ⟩, rfl⟩
    have hle :
        IntermediateField.lift (IntermediateField.fixedField J) ≤ Algebra.galoisClosure K L :=
      IntermediateField.lift_le _
    have hfin : FiniteDimensional K (IntermediateField.lift (IntermediateField.fixedField J)) :=
      IntermediateField.finiteDimensional_of_le hle
    have hsep : Algebra.IsSeparable K (IntermediateField.lift (IntermediateField.fixedField J)) :=
      IntermediateField.isSeparable_of_le hle
    have hKf : unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) ≤
        IntermediateField.lift (IntermediateField.fixedField J) :=
      le_lift_fixedField ((unramifiedExtension_inertiaDegree_le L).trans hLM)
        (hJ.trans (fixingSubgroup_unramifiedExtension L).ge)
    have hL' : IntermediateField.lift (IntermediateField.fixedField J) ≤ L :=
      lift_fixedField_le hLM hHJ
    refine ⟨_, hKf, hL', hfin, hsep, ?_⟩
    dsimp only
    have h₁ : intermediateDegree hKf = subgroupMeanAbscissa K (Algebra.galoisClosure K L)
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) J := by
      rw [intermediateDegree_eq_subgroupMeanAbscissa L hKf hL',
        fixingSubgroup_preimage_lift_fixedField]
    have h₂ : (intermediateDegree hKf : ℚ) * intermediateMean hKf =
        subgroupMeanOrdinate K (Algebra.galoisClosure K L)
          (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) J := by
      rw [intermediateDegree_mul_intermediateMean L hKf hL',
        fixingSubgroup_preimage_lift_fixedField]
    rw [h₁] at h₂ ⊢
    rw [← h₂]
    push_cast
    rfl

/-- **`K_f` is the maximal unramified subextension** (LMFDB `lf.means`): the unramified extension
`K_f` of `K` of degree `f(L / K)` in `K̄`, which lies in `L`, contains every subextension of `L / K`
unramified over `K`. -/
lemma le_unramifiedExtension_of_isUnramified (hEL : E ≤ L) (hE : IsUnramified K E) :
    E ≤ unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  have hG : lowerRamificationGroup K (Algebra.galoisClosure K L) 0 ≤
      fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
        (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' E) :=
    Subgroup.relIndex_eq_one.mp <| (relIndex_lowerRamificationGroup_zero_fixingSubgroup
      (hEL.trans hLM)).trans <| (isUnramified_iff_ramificationIndex_eq_one _ _).mp hE
  have hJ : fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹'
        unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) ≤
      fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
        (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' E) := by
    rw [fixingSubgroup_unramifiedExtension L]
    exact sup_le (fixingSubgroup_antitone _ _ (preimage_mono hEL)) hG
  exact (le_lift_fixedField (hEL.trans hLM) le_rfl).trans
    (lift_fixedField_le ((unramifiedExtension_inertiaDegree_le L).trans hLM) hJ)

/-- **The degree of `L` over `K_f` is the ramification index** (LMFDB `lf.means`): for the maximal
unramified subextension `K_f` of a finite separable extension `L / K` inside `K̄`,
`[L : K_f] = e(L / K)`. -/
lemma intermediateDegree_unramifiedExtension_le :
    intermediateDegree (unramifiedExtension_inertiaDegree_le L) = ramificationIndex K L := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  rw [intermediateDegree_eq_subgroupMeanAbscissa L _ le_rfl, subgroupMeanAbscissa,
    Subgroup.relIndex_sup_of_normal, relIndex_lowerRamificationGroup_zero_fixingSubgroup hLM]

lemma meanPolygon_eq_lowerConvexHull : meanPolygon L =
    lowerConvexHull (subgroupMeanPoints K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))) := by
  rw [meanPolygon, meanPoints_eq]

lemma subgroupMeanAbscissa_largestLowerJump :
    (subgroupMeanAbscissa K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
          lowerRamificationGroup K (Algebra.galoisClosure K L)
            ((largestLowerJump K (Algebra.galoisClosure K L)).toNat + 1 : ℕ))) =
      ramificationIndex K L := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  rw [sup_lowerRamificationGroup_largestLowerJump, subgroupMeanAbscissa,
    Subgroup.relIndex_sup_of_normal, relIndex_lowerRamificationGroup_zero_fixingSubgroup hLM]

lemma lowerConvexHull_subgroupMeanPoints : lowerConvexHull (subgroupMeanPoints K
    (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))) =
    {q | q.1 ∈ Icc (1 : ℝ) (ramificationIndex K L) ∧ q.2 =
      vertexPolygon (largestLowerJump K (Algebra.galoisClosure K L)).toNat
        (fun t ↦ subgroupMeanAbscissa K (Algebra.galoisClosure K L)
          (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
          (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
            lowerRamificationGroup K (Algebra.galoisClosure K L) t))
        (fun t ↦ (subgroupMeanOrdinate K (Algebra.galoisClosure K L)
          (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
          (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
            lowerRamificationGroup K (Algebra.galoisClosure K L) t) : ℝ))
        (fun t ↦ (subgroupSlope K (Algebra.galoisClosure K L) (t + 1) - 1 : ℚ)) q.1} := by
  rw [(isLowerHullVertices_subgroupMeanPoints _).lowerConvexHull_eq, Nat.cast_zero,
    subgroupMeanAbscissa_sup_zero, subgroupMeanAbscissa_largestLowerJump, Nat.cast_one]

private lemma sInf_setOf_mem_graph {g : ℝ → ℝ} {A : Set ℝ} {x : ℝ} (hx : x ∈ A) :
    sInf {y | (x, y) ∈ {q : ℝ × ℝ | q.1 ∈ A ∧ q.2 = g q.1}} = g x := by
  have h : {y | (x, y) ∈ {q : ℝ × ℝ | q.1 ∈ A ∧ q.2 = g q.1}} = {g x} :=
    Set.ext fun _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩
  rw [h, csInf_singleton]

lemma meanPolygonFunction_eq {x : ℝ} (hx : x ∈ Icc (1 : ℝ) (ramificationIndex K L)) :
    meanPolygonFunction L x = vertexPolygon (largestLowerJump K (Algebra.galoisClosure K L)).toNat
      (fun t ↦ subgroupMeanAbscissa K (Algebra.galoisClosure K L)
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
          lowerRamificationGroup K (Algebra.galoisClosure K L) t))
      (fun t ↦ (subgroupMeanOrdinate K (Algebra.galoisClosure K L)
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
          lowerRamificationGroup K (Algebra.galoisClosure K L) t) : ℝ))
      (fun t ↦ (subgroupSlope K (Algebra.galoisClosure K L) (t + 1) - 1 : ℚ)) x := by
  rw [meanPolygonFunction, meanPolygon_eq_lowerConvexHull, lowerConvexHull_subgroupMeanPoints]
  exact sInf_setOf_mem_graph hx

/-- **The slope polygon is the graph of `h` on `[1, e]`** (LMFDB `lf.means`): the slope polygon `S`
of a finite separable extension `L / K` inside `K̄` is the graph of the function
`IsNonarchimedeanLocalField.meanPolygonFunction` on `[1, e]`, for `e = e(L / K) = [L : K_f]`. -/
lemma meanPolygon_eq : meanPolygon L =
    {q | q.1 ∈ Icc (1 : ℝ) (ramificationIndex K L) ∧ q.2 = meanPolygonFunction L q.1} := by
  ext q
  rw [meanPolygon_eq_lowerConvexHull, lowerConvexHull_subgroupMeanPoints]
  exact and_congr_right fun hq ↦ by rw [meanPolygonFunction_eq L hq]

/-- **The means of the slope polygon are the means of the Herbrand invariant** (LMFDB `lf.means`,
`lf.herbrand_invariant`): for `k ≤ w`, the mean `m_k = h(ε p ^ k) / (ε p ^ k)` read off the slope
polygon of a finite separable extension `L / K` inside `K̄` is the mean
`∑_{j ≤ k} (p - 1) r_j / (ε p ^ j)` of its Herbrand invariant `(r_1, …, r_w)_ε^f`; for `k = 0` it is
`m_0 = 0`. So the points `(ε p ^ k, ε p ^ k m_k)` lie on the slope polygon. -/
lemma polygonMean_eq_mean {k : ℕ} (hk : k ≤ (visibleHerbrandInvariant L).w) :
    polygonMean L k = (visibleHerbrandInvariant L).mean k := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  set H : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) with hH
  have he :
      H.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0) = ramificationIndex K L :=
    relIndex_lowerRamificationGroup_zero_fixingSubgroup hLM
  rcases (⟨_, rfl⟩ : ∃ I : HerbrandInvariant (ringChar 𝓀[K]), I = HerbrandInvariant.ofRams
    (ringChar 𝓀[K]) hp (ramsOfSubgroup K (Algebra.galoisClosure K L) H)
    (fun _ ↦ pos_of_mem_ramsOfSubgroup K _ H)
    (H.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0)) (inertiaDegree K L)
    Subgroup.index_ne_zero_of_finite inertiaDegree_pos) with ⟨I, hI⟩
  have hVI : visibleHerbrandInvariant L = I := by
    rw [hI, visibleHerbrandInvariant]
    congr 1
    exact he.symm
  have hε : I.ε = ordCompl[ringChar 𝓀[K]]
      (H.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0)) := by
    rw [hI]
    rfl
  have hw : I.w = Multiset.card (ramsOfSubgroup K (Algebra.galoisClosure K L) H) := by
    rw [hI]
    rfl
  have hεw : I.ε * ringChar 𝓀[K] ^ I.w = ramificationIndex K L := by
    rw [← hVI]
    exact ε_mul_pow_w_visibleHerbrandInvariant L
  rw [hVI] at hk ⊢
  have hτ₀ : tameDegree K L = I.ε := by
    rw [hε, he]
    rfl
  have hx₁ : (1 : ℝ) ≤ (I.ε * ringChar 𝓀[K] ^ k : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mul_ne_zero I.ε_pos.ne' (pow_ne_zero _ hp.ne_zero))
  have hx₂ : ((I.ε * ringChar 𝓀[K] ^ k : ℕ) : ℝ) ≤ ramificationIndex K L := by
    rw [← hεw]
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.pos hk)
  have h₀ : ((subgroupMeanAbscissa K _ H (H ⊔ lowerRamificationGroup K
      (Algebra.galoisClosure K L) ((0 : ℕ) : ℤ)) : ℕ) : ℝ) ≤ (I.ε * ringChar 𝓀[K] ^ k : ℕ) := by
    rw [Nat.cast_zero, subgroupMeanAbscissa_sup_zero, Nat.cast_one]
    exact hx₁
  have hT : ((I.ε * ringChar 𝓀[K] ^ k : ℕ) : ℝ) ≤ (subgroupMeanAbscissa K _ H
      (H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L)
        ((largestLowerJump K (Algebra.galoisClosure K L)).toNat + 1 : ℕ)) : ℕ) := by
    rw [subgroupMeanAbscissa_largestLowerJump]
    exact hx₂
  rcases IsLowerHullVertices.exists_mem_Icc
    (n := fun t ↦ subgroupMeanAbscissa K _ H (H ⊔ lowerRamificationGroup K _ t)) h₀ _ hT with
    ⟨t, ht, hxt⟩
  rw [polygonMean, hτ₀, meanPolygonFunction_eq L ⟨hx₁, hx₂⟩,
    (isLowerHullVertices_subgroupMeanPoints H).vertexPolygon_eq ht hxt]
  have hφ₀ : 0 ≤ herbrandOfSubgroup K _ H t :=
    herbrandOfSubgroup_zero K _ H ▸ (herbrandOfSubgroup_strictMono K _ H).monotone t.zero_le
  have hk₁ : k ≤ (ramsOfSubgroup K _ H).countP (· ≤ herbrandOfSubgroup K _ H t) := by
    have h : ((I.ε * ringChar 𝓀[K] ^ k : ℕ) : ℝ) ≤
        (subgroupMeanAbscissa K _ H (H ⊔ lowerRamificationGroup K _ (t + 1 : ℕ)) : ℕ) :=
      hxt.2
    rw [subgroupMeanAbscissa_sup_succ H t, ← hε] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (Nat.le_of_mul_le_mul_left (Nat.cast_le.mp h)
      I.ε_pos)
  have hr₁ : (I.ram k : ℝ) ≤ herbrandOfSubgroup K _ H t := by
    have h : I.ram ((ramsOfSubgroup K _ H).countP (· ≤ herbrandOfSubgroup K _ H t)) ≤
        herbrandOfSubgroup K _ H t := by
      rw [hI]
      exact HerbrandInvariant.ram_countP_le _ hp _ (fun _ ↦ pos_of_mem_ramsOfSubgroup K _ H)
        (H.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0)) (inertiaDegree K L)
        Subgroup.index_ne_zero_of_finite inertiaDegree_pos hφ₀
    exact_mod_cast (I.monotone_ram hk₁).trans h
  have hr₂ (hkw : k < I.w) : (herbrandOfSubgroup K _ H t : ℝ) ≤ I.ram (k + 1) := by
    rcases t with _ | s
    · rw [herbrandOfSubgroup_zero, Rat.cast_zero]
      exact_mod_cast I.ram_nonneg (k + 1)
    · have hk₀ : (ramsOfSubgroup K _ H).countP (· ≤ herbrandOfSubgroup K _ H s) ≤ k := by
        have h : (subgroupMeanAbscissa K _ H (H ⊔ lowerRamificationGroup K _ (s + 1 : ℕ)) : ℝ) ≤
            (I.ε * ringChar 𝓀[K] ^ k : ℕ) :=
          hxt.1
        rw [subgroupMeanAbscissa_sup_succ H s, ← hε] at h
        exact (Nat.pow_le_pow_iff_right hp.one_lt).mp
          (Nat.le_of_mul_le_mul_left (Nat.cast_le.mp h) I.ε_pos)
      have hlt : herbrandOfSubgroup K _ H s <
          I.ram ((ramsOfSubgroup K _ H).countP (· ≤ herbrandOfSubgroup K _ H s) + 1) := by
        rw [hI]
        exact HerbrandInvariant.lt_ram_countP_le_add_one _ hp _
          (fun _ ↦ pos_of_mem_ramsOfSubgroup K _ H)
          (H.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0)) (inertiaDegree K L)
          Subgroup.index_ne_zero_of_finite inertiaDegree_pos (a := herbrandOfSubgroup K _ H s)
          (by omega)
      have hmem : I.ram (k + 1) ∈ ramsOfSubgroup K _ H := by
        rw [hI]
        exact HerbrandInvariant.ram_ofRams_mem _ hp _ (fun _ ↦ pos_of_mem_ramsOfSubgroup K _ H)
          (H.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0)) (inertiaDegree K L)
          Subgroup.index_ne_zero_of_finite inertiaDegree_pos (k := k + 1) (by omega) (by omega)
      rcases Multiset.mem_sum.mp hmem with ⟨i, -, hi⟩
      have hri : I.ram (k + 1) = herbrandOfSubgroup K _ H (i + 1) :=
        Multiset.eq_of_mem_replicate hi
      have h₁ : herbrandOfSubgroup K _ H s < herbrandOfSubgroup K _ H (i + 1) :=
        hri ▸ hlt.trans_le (I.monotone_ram (by omega))
      have h₂ : s + 1 ≤ i + 1 := (herbrandOfSubgroup_strictMono K _ H).lt_iff_lt.mp h₁
      rw [hri]
      exact_mod_cast (herbrandOfSubgroup_strictMono K _ H).monotone h₂
  have hherb :
      (herbrand K (Algebra.galoisClosure K L) ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) =
        I.swanSlope k +
          ((herbrandOfSubgroup K _ H t : ℝ) - I.ram k) / (I.ε * ringChar 𝓀[K] ^ k) := by
    rw [← herbrandFunction_ofRams_herbrandOfSubgroup K (Algebra.galoisClosure K L) H
      (inertiaDegree K L) inertiaDegree_pos (t := t), ← hI]
    rcases hk.lt_or_eq with hkw | rfl
    · exact I.herbrandFunction_of_mem_Icc hkw ⟨hr₁, hr₂ hkw⟩
    · exact I.herbrandFunction_of_le hr₁
  have hline : (subgroupMeanOrdinate K _ H (H ⊔ lowerRamificationGroup K _ t) : ℝ) -
      ((subgroupSlope K (Algebra.galoisClosure K L) (t + 1) : ℝ) - 1) *
        (subgroupMeanAbscissa K _ H (H ⊔ lowerRamificationGroup K _ t) : ℕ) =
          -(herbrandOfSubgroup K _ H t : ℝ) := by
    exact_mod_cast subgroupMeanOrdinate_sub_mul H t ht
  have hx₀ : (I.ε : ℝ) * ringChar 𝓀[K] ^ k ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr I.ε_pos.ne') (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))
  have hherb' :
      (herbrand K (Algebra.galoisClosure K L) ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) *
        (I.ε * ringChar 𝓀[K] ^ k) = I.swanSlope k * (I.ε * ringChar 𝓀[K] ^ k) +
          ((herbrandOfSubgroup K _ H t : ℝ) - I.ram k) := by
    rw [hherb, add_mul, div_mul_cancel₀ _ hx₀]
  have htiny : (I.ram k : ℝ) = (I.swanSlope k - I.mean k) * (I.ε * ringChar 𝓀[K] ^ k) := by
    have h : I.ram k / (I.ε * ringChar 𝓀[K] ^ k) = I.swanSlope k - I.mean k :=
      I.tinyRam_eq_swanSlope_sub_mean hp.ne_zero k
    have h' : (I.ram k : ℝ) / (I.ε * ringChar 𝓀[K] ^ k) = I.swanSlope k - I.mean k := by
      exact_mod_cast h
    rw [← h', div_mul_cancel₀ _ hx₀]
  push_cast
  rw [div_eq_iff hx₀]
  linear_combination hline + (I.ε * ringChar 𝓀[K] ^ k : ℝ) *
    natCast_subgroupSlope_succ (K := K) (M := Algebra.galoisClosure K L) t + hherb' - htiny

/-- **The convention `m_0 = 0`** (LMFDB `lf.means`): the mean `m_0 = h(ε) / ε` read off the slope
polygon of a finite separable extension `L / K` inside `K̄` is `0`. -/
lemma polygonMean_zero : polygonMean L 0 = 0 := by
  rw [polygonMean_eq_mean L (Nat.zero_le _), HerbrandInvariant.mean_zero, Rat.cast_zero]

/-- **The mean of `L / K` is its last mean** (LMFDB `lf.means`): the mean `m` of a finite separable
extension `L / K` inside `K̄`, determined by `c = f (e - 1 + e m)`, is the last mean `m_w` read off
its slope polygon. -/
lemma extensionMean_eq_polygonMean :
    (extensionMean K L : ℝ) = polygonMean L (visibleHerbrandInvariant L).w := by
  rw [polygonMean_eq_mean L le_rfl]
  exact_mod_cast ((eq_extensionMean_iff K L _).mp
    (natCast_discriminantExponent_visibleHerbrandInvariant L)).symm

lemma visibleSwanSlopes_eq_map_swanSlope : visibleSwanSlopes L =
    (Multiset.range (visibleHerbrandInvariant L).w).map
      fun k ↦ ((visibleHerbrandInvariant L).swanSlope (k + 1) : ℝ) := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  let a : Algebra L (Algebra.galoisClosure K L) := (IntermediateField.inclusion hLM).toAlgebra
  have hs : IsScalarTower K L (Algebra.galoisClosure K L) := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension L (Algebra.galoisClosure K L) :=
    (IntermediateField.inclusion hLM).valuativeExtension
  have hf : Module.Finite L (Algebra.galoisClosure K L) := .of_restrictScalars_finite K L _
  rw [visibleSwanSlopes_eq_swanSlopesOfSubgroup,
    fixingSubgroup_preimage_eq_range_restrictScalarsHom hLM,
    HerbrandInvariant.visibleHerbrandInvariant_eq_herbrandInvariantOfTower L]
  exact (map_swanSlope_herbrandInvariantOfTower K _ L).symm

/-- **The Swan slopes in terms of the means** (LMFDB `lf.means`): the Swan slopes `s_1 ≤ ⋯ ≤ s_w`
of a finite separable extension `L / K` inside `K̄` (LMFDB `lf.slopes`, read off the lower convex
hull of the points of its subextensions) satisfy `(p - 1) s_k = p m_k - m_{k - 1}` for the means
`m_k` read off its slope polygon, with `m_0 = 0`: the sorted list of its Swan slopes is
`[(p m_k - m_{k - 1}) / (p - 1)]_{1 ≤ k ≤ w}`. -/
lemma sort_hullWildSwanSlopes_eq : (hullWildSwanSlopes L).sort (· ≤ ·) =
    (List.range (visibleHerbrandInvariant L).w).map fun k ↦
      ((ringChar 𝓀[K] : ℝ) * polygonMean L (k + 1) - polygonMean L k) / (ringChar 𝓀[K] - 1) := by
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  have hl : (List.range (visibleHerbrandInvariant L).w).map
      (fun k ↦ ((visibleHerbrandInvariant L).swanSlope (k + 1) : ℝ)) =
        (List.range (visibleHerbrandInvariant L).w).map fun k ↦
          ((ringChar 𝓀[K] : ℝ) * polygonMean L (k + 1) - polygonMean L k) /
            (ringChar 𝓀[K] - 1) := by
    refine List.map_congr_left fun k hk ↦ ?_
    rw [List.mem_range] at hk
    rw [polygonMean_eq_mean L (by omega), polygonMean_eq_mean L (by omega),
      HerbrandInvariant.swanSlope_succ_eq]
    push_cast
    rfl
  have hmono : Monotone fun k ↦ ((visibleHerbrandInvariant L).swanSlope (k + 1) : ℝ) :=
    fun _ _ hab ↦ Rat.cast_le.mpr (HerbrandInvariant.swanSlope_mono (Nat.add_le_add_right hab 1))
  rw [← hl, hullWildSwanSlopes_eq_visibleSwanSlopes, visibleSwanSlopes_eq_map_swanSlope,
    ← Multiset.coe_range, Multiset.map_coe, Multiset.coe_sort]
  exact List.mergeSort_eq_self _
    (List.pairwise_map.mpr ((List.sortedLT_range _).sortedLE.pairwise.imp fun hab ↦ hmono hab))

end IsNonarchimedeanLocalField
