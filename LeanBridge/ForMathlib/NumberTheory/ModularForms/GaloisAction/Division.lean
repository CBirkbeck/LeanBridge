import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Forms
import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Holomorphic
import TauCeti.NumberTheory.ModularForms.Norm.Cusps

/-!
# Integrally dependent quotients of modular forms are modular forms

Let `𝒢` be a group of finite index in `SL₂(ℤ)`, `A` a modular form of level `𝒢` and weight `w + k`,
and `D ≠ 0` a modular form of level one and weight `w`. If the quotient `A / D` is a root of a monic
polynomial whose coefficients of degree `d - j` are modular forms of level one and weight `j * k`,
then it is holomorphic on the upper half-plane and at the cusps, so it is a modular form of level
`𝒢` and weight `k`: a root of a monic polynomial is bounded in terms of the coefficients. If
moreover the coefficients other than the leading one vanish at the cusp `∞`, the quotient is a cusp
form.

## Main definitions

* `TauCeti.GaloisAction.IsIntegralQuotient`: the hypotheses above.

## Main results

* `TauCeti.GaloisAction.norm_le_of_sum_mul_pow_eq_zero`: the bound of a root of a monic polynomial.
* `TauCeti.GaloisAction.IsIntegralQuotient.exists_modularForm`: the quotient `A / D` is a modular
  form.
* `TauCeti.GaloisAction.IsIntegralQuotient.isCuspForm`: the quotient `A / D` is a cusp form if the
  coefficients other than the leading one vanish at the cusp `∞`.
-/

open UpperHalfPlane ModularForm SlashInvariantForm Matrix Filter Asymptotics Subgroup

open scoped MatrixGroups Manifold Topology

namespace TauCeti.GaloisAction

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} {w k : ℤ} {d : ℕ} {c : ℕ → ℍ → ℂ} {A D F a : ℍ → ℂ}

/-- **The bound of a root of a monic polynomial** in terms of the coefficients. -/
lemma norm_le_of_sum_mul_pow_eq_zero {b : ℕ → ℂ} {x : ℂ} (hb : b 0 = 1)
    (h : ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (b j * x ^ (d - j)) = 0) :
    ‖x‖ ≤ 1 + ∑ j ∈ Finset.range d, ‖b (j + 1)‖ := by
  rw [Finset.sum_range_succ'] at h
  simp only [pow_zero, one_mul, hb, Nat.sub_zero] at h
  by_contra hx
  push Not at hx
  have hS : 0 ≤ ∑ j ∈ Finset.range d, ‖b (j + 1)‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hx1 : 1 < ‖x‖ := by linarith
  rcases d with _ | d
  · simp at h
  · have hbound : ‖x‖ ^ (d + 1) ≤ (∑ j ∈ Finset.range (d + 1), ‖b (j + 1)‖) * ‖x‖ ^ d := by
      rw [← norm_pow, eq_neg_of_add_eq_zero_right h, norm_neg, Finset.sum_mul]
      refine (norm_sum_le _ _).trans <| Finset.sum_le_sum fun j hj ↦ ?_
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow]
      gcongr
      · exact hx1.le
      · have hj' : j < d + 1 := Finset.mem_range.mp hj
        omega
    have hle : ‖x‖ ≤ ∑ j ∈ Finset.range (d + 1), ‖b (j + 1)‖ := by
      rw [pow_succ, mul_comm] at hbound
      exact le_of_mul_le_mul_right hbound (by positivity)
    linarith

variable (𝒢 w k d c A D) in
/-- The hypotheses under which the quotient `A / D` is a modular form of level `𝒢` and weight `k`:
`A` is a modular form of level `𝒢` and weight `w + k`, `D ≠ 0` is a modular form of level one and
weight `w`, and `A / D` is a root of the monic polynomial `∑ⱼ (-1)ʲ c j Xᵈ⁻ʲ`, where `c j` is a
modular form of level one and weight `j * k`. The last condition is stated without dividing by `D`:
`∑ⱼ (-1)ʲ c j A^(d - j) D^j = 0`. -/
structure IsIntegralQuotient : Prop where
  isForm_num : IsForm 𝒢 (w + k) A
  isForm_den : IsForm 𝒮ℒ w D
  den_ne_zero : D ≠ 0
  isForm_coeff (j : ℕ) : IsForm 𝒮ℒ (j * k) (c j)
  coeff_zero : c 0 = 1
  sum_eq_zero (τ : ℍ) : ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (c j τ * A τ ^ (d - j) * D τ ^ j) = 0

lemma IsForm.mdifferentiable (ha : IsForm 𝒢 w a) : MDiff a := by
  rcases ha with ⟨g, rfl⟩
  exact ModularFormClass.holo g

lemma IsForm.slash_eq (ha : IsForm 𝒮ℒ w a) (γ : SL(2, ℤ)) : a ∣[w] γ = a := by
  rcases ha with ⟨g, rfl⟩
  exact slash_action_eqn g _ ⟨γ, rfl⟩

lemma IsIntegralQuotient.sum_mul_pow_eq_zero (h : IsIntegralQuotient 𝒢 w k d c A D) {τ : ℍ}
    (hτ : D τ ≠ 0) :
    ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (c j τ * (A τ / D τ) ^ (d - j)) = 0 := by
  have h₁ : ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (c j τ * A τ ^ (d - j) * D τ ^ j) = 0 :=
    h.sum_eq_zero τ
  have h₂ : ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (c j τ * A τ ^ (d - j) * D τ ^ j) =
      D τ ^ d * ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (c j τ * (A τ / D τ) ^ (d - j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j + (d - j) = d := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    have hd : D τ ^ d = D τ ^ j * D τ ^ (d - j) := by
      rw [← pow_add, hj']
    rw [hd, div_pow]
    field_simp
  rw [h₂] at h₁
  exact (mul_eq_zero.mp h₁).resolve_left (pow_ne_zero _ hτ)

lemma IsIntegralQuotient.exists_mdifferentiable_mul_eq (h : IsIntegralQuotient 𝒢 w k d c A D) :
    ∃ F : ℍ → ℂ, MDiff F ∧ ∀ τ, D τ * F τ = A τ := by
  refine GaloisAction.exists_mdifferentiable_mul_eq h.isForm_num.mdifferentiable
    h.isForm_den.mdifferentiable h.den_ne_zero
    (B := fun τ ↦ 1 + ∑ j ∈ Finset.range d, ‖c (j + 1) τ‖) ?_
    fun τ hτ ↦ norm_le_of_sum_mul_pow_eq_zero (b := fun j ↦ c j τ)
      (congrFun h.coeff_zero τ) (h.sum_mul_pow_eq_zero hτ)
  exact continuous_const.add <| continuous_finsetSum _ fun j _ ↦
    (h.isForm_coeff (j + 1)).mdifferentiable.continuous.norm

lemma IsIntegralQuotient.sum_mul_pow_eq_zero_of_mul_eq (h : IsIntegralQuotient 𝒢 w k d c A D)
    (hF : MDiff F) (hDF : ∀ τ, D τ * F τ = A τ) :
    ∑ j ∈ Finset.range (d + 1), ((-1) ^ j : ℂ) • (c j * F ^ (d - j)) = 0 := by
  have hG : MDiff (∑ j ∈ Finset.range (d + 1), ((-1) ^ j : ℂ) • (c j * F ^ (d - j))) :=
    .sum fun j _ ↦ ((h.isForm_coeff j).mdifferentiable.mul (hF.pow _)).const_smul _
  refine eq_of_mul_eq_mul h.isForm_den.mdifferentiable h.den_ne_zero hG
    mdifferentiable_const fun τ ↦ ?_
  rcases eq_or_ne (D τ) 0 with hτ | hτ
  · simp [hτ]
  · have hFτ : F τ = A τ / D τ := eq_div_of_mul_eq hτ (by rw [mul_comm, hDF])
    have hs : ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (c j τ * (A τ / D τ) ^ (d - j)) = 0 :=
      h.sum_mul_pow_eq_zero hτ
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul, hFτ, hs,
      Pi.zero_apply]

lemma IsIntegralQuotient.sum_mul_slash_pow_eq_zero (h : IsIntegralQuotient 𝒢 w k d c A D)
    (hF : MDiff F) (hDF : ∀ τ, D τ * F τ = A τ) (γ : SL(2, ℤ)) :
    ∑ j ∈ Finset.range (d + 1), ((-1) ^ j : ℂ) • (c j * (F ∣[k] γ) ^ (d - j)) = 0 := by
  have h₀ : (∑ j ∈ Finset.range (d + 1), ((-1) ^ j : ℂ) • (c j * F ^ (d - j))) ∣[(d : ℤ) * k] γ =
      (0 : ℍ → ℂ) ∣[(d : ℤ) * k] γ := by
    rw [h.sum_mul_pow_eq_zero_of_mul_eq hF hDF]
  simp only [SlashAction.sum_slash, SL_smul_slash, SlashAction.zero_slash] at h₀
  rw [← h₀]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : (d : ℤ) * k = j * k + ((d - j : ℕ) : ℤ) * k := by
    rw [← add_mul, ← Nat.cast_add,
      Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  rw [hj', mul_slash_SL2, (h.isForm_coeff j).slash_eq, pow_slash]

lemma IsIntegralQuotient.slash_eq (h : IsIntegralQuotient 𝒢 w k d c A D) (hF : MDiff F)
    (hDF : ∀ τ, D τ * F τ = A τ) {γ : SL(2, ℤ)} (hγ : SpecialLinearGroup.mapGL ℝ γ ∈ 𝒢) :
    F ∣[k] γ = F := by
  have hfun : D * F = A := funext hDF
  have hA : A ∣[w + k] γ = A := by
    rcases h.isForm_num with ⟨g, hg⟩
    rw [← hg]
    exact slash_action_eqn g _ hγ
  refine eq_of_mul_eq_mul h.isForm_den.mdifferentiable h.den_ne_zero
    (hF.slash k (SpecialLinearGroup.mapGL ℝ γ)) hF fun τ ↦ ?_
  have h₁ : (D * F) ∣[w + k] γ = D ∣[w] γ * F ∣[k] γ := mul_slash_SL2 w k γ D F
  rw [hfun, hA, h.isForm_den.slash_eq] at h₁
  rw [hDF τ, h₁]
  rfl

lemma IsForm.isBoundedAtImInfty (ha : IsForm 𝒮ℒ w a) : IsBoundedAtImInfty a := by
  rcases ha with ⟨g, rfl⟩
  exact ModularFormClass.bdd_at_infty g

lemma IsIntegralQuotient.isBoundedAtImInfty_slash (h : IsIntegralQuotient 𝒢 w k d c A D)
    (hF : MDiff F) (hDF : ∀ τ, D τ * F τ = A τ) (γ : SL(2, ℤ)) : IsBoundedAtImInfty (F ∣[k] γ) := by
  have hc : IsBoundedAtImInfty fun τ ↦ 1 + ∑ j ∈ Finset.range d, ‖c (j + 1) τ‖ :=
    (const_boundedAtFilter _ _).add <| .fun_sum fun j _ ↦
      (h.isForm_coeff (j + 1)).isBoundedAtImInfty.norm_left
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun τ ↦ ?_)).trans hc
  have h₀ : (∑ j ∈ Finset.range (d + 1), ((-1) ^ j : ℂ) • (c j * (F ∣[k] γ) ^ (d - j))) τ =
      (0 : ℍ → ℂ) τ :=
    congrFun (h.sum_mul_slash_pow_eq_zero hF hDF γ) τ
  simp only [Finset.sum_apply, Pi.smul_apply] at h₀
  have hle : ‖(F ∣[k] γ) τ‖ ≤ 1 + ∑ j ∈ Finset.range d, ‖c (j + 1) τ‖ :=
    norm_le_of_sum_mul_pow_eq_zero (b := fun j ↦ c j τ) (congrFun h.coeff_zero τ) h₀
  rwa [one_mul, Real.norm_of_nonneg (add_nonneg zero_le_one
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))]

variable [𝒢.IsArithmetic]

/-- **An integrally dependent quotient of modular forms is a modular form**: under the hypotheses
`IsIntegralQuotient`, the quotient `A / D` is a modular form of level `𝒢` and weight `k`. -/
lemma IsIntegralQuotient.exists_modularForm (h : IsIntegralQuotient 𝒢 w k d c A D) (h𝒢 : 𝒢 ≤ 𝒮ℒ) :
    ∃ G : ModularForm 𝒢 k, ∀ τ, D τ * G τ = A τ := by
  rcases h.exists_mdifferentiable_mul_eq with ⟨F, hF, hDF⟩
  refine ⟨{ toFun := F, slash_action_eq' := fun g hg ↦ ?_, holo' := hF, bdd_at_cusps' := ?_ }, hDF⟩
  · rcases h𝒢 hg with ⟨γ, rfl⟩
    exact h.slash_eq hF hDF hg
  · intro c hc
    rw [IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ ↦ h.isBoundedAtImInfty_slash hF hDF γ

/-- **The quotient is a cusp form if the coefficients vanish at the cusp `∞`**: under the hypotheses
`IsIntegralQuotient`, if the coefficients other than the leading one tend to zero at `∞`, then the
quotient `A / D` is a cusp form, its translates being roots of the same monic polynomial. -/
lemma IsIntegralQuotient.isCuspForm (h : IsIntegralQuotient 𝒢 w k d c A D) {G : ModularForm 𝒢 k}
    (hG : ∀ τ, D τ * G τ = A τ) (hc : ∀ j, j ≠ 0 → Tendsto (c j) atImInfty (𝓝 0)) :
    IsCuspForm 𝒢 k G := by
  refine ⟨{ toSlashInvariantForm := G.toSlashInvariantForm
            holo' := G.holo'
            zero_at_cusps' := ?_ }, rfl⟩
  intro c' hc'
  rw [IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc'
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
  intro γ _
  have hlim : Tendsto (⇑G ∣[k] γ) atImInfty (𝓝 (valueAtInfty (⇑G ∣[k] γ))) :=
    quotientFunc_cosetOf G γ ▸ ModularForm.tendsto_quotientFunc_valueAtInfty G (cosetOf 𝒢 γ)
  have hrel : ∑ j ∈ Finset.range (d + 1), ((-1) ^ j : ℂ) • (c j * (⇑G ∣[k] γ) ^ (d - j)) = 0 :=
    h.sum_mul_slash_pow_eq_zero G.holo' hG γ
  have hterm (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :
      Tendsto (fun τ ↦ ((-1) ^ j : ℂ) • (c j τ * ((⇑G ∣[k] γ) τ) ^ (d - j))) atImInfty
        (𝓝 (if j = 0 then valueAtInfty (⇑G ∣[k] γ) ^ d else 0)) := by
    split_ifs with h₀
    · subst h₀
      simpa [h.coeff_zero] using hlim.pow d
    · simpa using ((hc j h₀).mul (hlim.pow (d - j))).const_smul ((-1) ^ j : ℂ)
  have hsum : Tendsto (fun τ ↦ ∑ j ∈ Finset.range (d + 1),
      ((-1) ^ j : ℂ) • (c j τ * ((⇑G ∣[k] γ) τ) ^ (d - j))) atImInfty
        (𝓝 (∑ j ∈ Finset.range (d + 1), if j = 0 then valueAtInfty (⇑G ∣[k] γ) ^ d else 0)) :=
    tendsto_finsetSum _ hterm
  rw [Finset.sum_ite_eq' (Finset.range (d + 1)) 0, ite_eq_left (Finset.mem_range.mpr d.succ_pos)]
    at hsum
  have hzero : (fun τ ↦ ∑ j ∈ Finset.range (d + 1),
      ((-1) ^ j : ℂ) • (c j τ * ((⇑G ∣[k] γ) τ) ^ (d - j))) = 0 := by
    ext τ
    simpa using congrFun hrel τ
  rw [hzero] at hsum
  have hv : valueAtInfty (⇑G ∣[k] γ) = 0 := by
    by_contra hv
    exact pow_ne_zero d hv (tendsto_nhds_unique hsum tendsto_const_nhds)
  rw [hv] at hlim
  exact hlim

end TauCeti.GaloisAction
