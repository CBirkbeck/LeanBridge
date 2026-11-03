import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeLevels

/-!
# The ramification polygon of a semicanonical polynomial and the recovery of the rams

This file proves the two steps of the converse of Monge's reduction (arXiv:1109.4617, §2.2): the
ramification polygon of a specialisation `q` of the generic polynomial of a Herbrand invariant `I`
which is admissible for `e₀ = v_R(p)`, at coefficients `f_σ` that are units at the `A`-points, is
the polygon of `I`, and two Herbrand invariants with the same polygon, the same `w` and the same `ε`
have the same rams. So the polynomials of the family all have Herbrand invariant `I`, once their
degree, tame degree and residue degree have been checked.

For the first step, the digits of `q` lie above the bottom edges of the bands by construction, and
the arithmetic of the binomial coefficients gives the lower bound for the polygon. At a vertex `k`
of the polygon, the term comes from an `A`-point of index `k` at a geometric band, from the term of
index `k - 1` at an arithmetic band, as `r_k^* = e₀`, and from the leading term for `k = 0`.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.ram_eq_ram_of_isRamificationPolygon`: the recovery
  of the rams from the ramification polygon.
* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_vertex_term_specialisation`: the terms of a
  semicanonical polynomial at the vertices.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isRamificationPolygon_specialisation`: the
  ramification polygon of a semicanonical polynomial.
-/

open Finset IsDiscreteValuationRing IsLocalRing Polynomial

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} {I J : HerbrandInvariant p} {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Algebra R S] {g : R[X]} {π : S} {ϖ : R} {f : ℕ → R}
  {b e₀ i j k r v σ : ℕ}

variable [IsDomain R] [IsDiscreteValuationRing R] in
lemma exists_mem_genericIndices_of_addVal_coeff (hϖ : Irreducible ϖ) (hi : i < I.ramificationIndex)
    (hj : addVal R ((I.specialisation ϖ f).coeff i) = j) :
    ∃ σ ∈ I.genericIndices, σ % I.ramificationIndex = i ∧ σ / I.ramificationIndex + 1 ≤ j := by
  by_contra hne
  push Not at hne
  have hdvd : ϖ ^ (j + 1) ∣ (I.specialisation ϖ f).coeff i := by
    rw [coeff_specialisation_of_lt ϖ f hi, pow_succ']
    refine mul_dvd_mul_left ϖ (dvd_sum fun σ hσ ↦ ?_)
    split_ifs with h
    · exact (pow_dvd_pow ϖ (Nat.lt_succ_iff.mp (hne σ hσ h.symm))).mul_left _
    · exact dvd_zero _
  rw [pow_dvd_iff_le_addVal hϖ, hj] at hdvd
  have h₁ : j + 1 ≤ j := by
    exact_mod_cast hdvd
  omega

lemma mean_le_of_mem_genericIndices (hσ : σ ∈ I.genericIndices) (hσ₀ : σ ≠ 0) :
    I.mean (I.pointIndex (σ % I.ramificationIndex)) ≤ (σ : ℚ) / I.ramificationIndex := by
  by_contra hlt
  have hZ : I.pointType σ = .Z := by
    rw [pointType, ite_eq_right hσ₀]
    exact ite_eq_left (not_le.mp hlt)
  rcases (mem_filter.mp hσ).2 with h | h | h | ⟨h, -⟩ <;> rw [hZ] at h <;> cases h

lemma ne_zero_of_pointType_eq_A (hA : I.pointType σ = .A) : σ ≠ 0 := by
  rintro rfl
  rw [pointType_zero] at hA
  cases hA

lemma div_eq_mean_of_pointType_eq_A (hA : I.pointType σ = .A) :
    (σ : ℚ) / I.ramificationIndex = I.mean (I.pointIndex (σ % I.ramificationIndex)) := by
  rw [pointType] at hA
  split_ifs at hA with h₁ h₂ h₃ h₄
  exact h₄.1

lemma isGeometricBand_of_pointType_eq_A (hA : I.pointType σ = .A) :
    I.IsGeometricBand (I.pointIndex (σ % I.ramificationIndex)) := by
  rw [pointType] at hA
  split_ifs at hA with h₁ h₂ h₃ h₄
  exact h₄.2.1

lemma isFinal_of_pointType_eq_A (hA : I.pointType σ = .A) :
    I.IsFinal (I.pointIndex (σ % I.ramificationIndex)) := by
  rw [pointType] at hA
  split_ifs at hA with h₁ h₂ h₃ h₄
  exact h₄.2.2

lemma lt_swanSlope_of_pointType (hT : I.pointType σ = .A ∨ I.pointType σ = .B) :
    (σ : ℚ) / I.ramificationIndex < I.swanSlope (I.pointIndex (σ % I.ramificationIndex)) := by
  rcases hT with hT | hT <;>
  · rw [pointType] at hT
    split_ifs at hT with h₁ h₂ h₃ h₄
    all_goals exact h₃

variable [Fact p.Prime]

lemma polygonLine_lt_of_ram_lt {x : ℚ} (hkb : k + 1 ≤ b) (hb : b ≤ I.w) (hx : I.ram b < x) :
    I.polygonLine b x < I.polygonLine k x := by
  have hp₁ : (1 : ℚ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hstep {j : ℕ} (hj : j + 1 ≤ I.w) (hxj : I.ram (j + 1) < x) :
      I.polygonLine (j + 1) x < I.polygonLine j x := by
    rw [← sub_neg, I.polygonLine_succ_sub hj]
    exact mul_neg_of_pos_of_neg (mul_pos (by linarith) (by positivity)) (by linarith)
  induction b, hkb using Nat.le_induction with
  | base => exact hstep hb hx
  | succ b hkb ih =>
    exact (hstep hb hx).trans (ih (by omega) ((I.monotone_ram b.le_succ).trans_lt hx))

lemma mul_swanSlope_le_polygonLine (hI : I.IsRamificationPolygon g π)
    (hJ : J.IsRamificationPolygon g π) (hw : I.w = J.w) (hε : I.ε = J.ε) (hb : b ≤ I.w)
    (hv : I.IsVertex b) (hk : k ≤ J.w) :
    (J.ramificationIndex : ℚ) * J.swanSlope k ≤ I.polygonLine b (J.ram k) := by
  have hp : p.Prime :=
    Fact.out
  have he : I.ramificationIndex = J.ramificationIndex := by
    rw [ramificationIndex, ramificationIndex, hw, hε]
  rcases hI.exists_addVal_eq hb hv with ⟨v, hv₁, hform⟩
  have hLB : (J.ramificationIndex : ℚ) * (J.swanSlope k + 1) ≤
      v + (p ^ (I.w - b) : ℕ) + (p ^ (I.w - b) : ℕ) * J.ram k :=
    hJ.le_addVal hk (pow_ne_zero (I.w - b) hp.ne_zero) hv₁
  rw [polygonLine, he]
  rw [he] at hform
  push_cast at hLB
  rw [mul_add] at hLB hform
  linarith

lemma not_ram_lt_ram_of_isRamificationPolygon (hI : I.IsRamificationPolygon g π)
    (hJ : J.IsRamificationPolygon g π) (hw : I.w = J.w) (hε : I.ε = J.ε) (hk : k + 1 ≤ I.w)
    (hlow : ∀ j ≤ k, I.ram j = J.ram j) : ¬I.ram (k + 1) < J.ram (k + 1) := by
  intro hlt
  have he : I.ramificationIndex = J.ramificationIndex := by
    rw [ramificationIndex, ramificationIndex, hw, hε]
  have hmean : I.mean k = J.mean k := by
    rw [mean, mean]
    refine sum_congr rfl fun j hj ↦ ?_
    rw [hlow j (mem_Icc.mp hj).2, hε]
  have hline : I.polygonLine k (J.ram (k + 1)) = J.polygonLine k (J.ram (k + 1)) := by
    rw [polygonLine, polygonLine, he, hmean, hw]
  let P : ℕ → Prop := fun b ↦ I.ram b < J.ram (k + 1)
  have hPb : P (Nat.findGreatest P I.w) :=
    Nat.findGreatest_spec hk hlt
  have hle : k + 1 ≤ Nat.findGreatest P I.w :=
    Nat.le_findGreatest hk hlt
  have hbw : Nat.findGreatest P I.w ≤ I.w :=
    Nat.findGreatest_le I.w
  have hnext : Nat.findGreatest P I.w < I.w → J.ram (k + 1) ≤ I.ram (Nat.findGreatest P I.w + 1) :=
    fun hb ↦ not_lt.mp (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hb)
  generalize Nat.findGreatest P I.w = b at hPb hle hbw hnext
  have hv : I.IsVertex b := by
    rcases hbw.lt_or_eq with hb | hb
    · exact .inr (hPb.trans_le (hnext hb))
    · exact .inl hb
  have hE : (J.ramificationIndex : ℚ) * J.swanSlope (k + 1) ≤ I.polygonLine b (J.ram (k + 1)) :=
    mul_swanSlope_le_polygonLine hI hJ hw hε hbw hv (hw ▸ hk)
  rw [J.mul_swanSlope_eq (hw ▸ hk), J.polygonLine_succ_ram (hw ▸ hk), ← hline] at hE
  exact absurd hE (not_le.mpr (polygonLine_lt_of_ram_lt hle hbw hPb))

/-- **The recovery of the rams from the ramification polygon**: if the ramification polygon of `g`
at `π` is that of the Herbrand invariants `I` and `J`, with the same `w` and `ε`, then they have the
same rams. -/
lemma ram_eq_ram_of_isRamificationPolygon (hI : I.IsRamificationPolygon g π)
    (hJ : J.IsRamificationPolygon g π) (hw : I.w = J.w) (hε : I.ε = J.ε) : I.ram = J.ram := by
  have hle (k : ℕ) (hk : k ≤ I.w) : I.ram k = J.ram k := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases k with _ | k
      · rw [I.ram_zero, J.ram_zero]
      · have hlow : ∀ j ≤ k, I.ram j = J.ram j :=
          fun j hj ↦ ih j (by omega) (by omega)
        exact le_antisymm
          (not_lt.mp (not_ram_lt_ram_of_isRamificationPolygon hJ hI hw.symm hε.symm (hw ▸ hk)
            fun j hj ↦ (hlow j hj).symm))
          (not_lt.mp (not_ram_lt_ram_of_isRamificationPolygon hI hJ hw hε hk hlow))
  funext k
  rcases le_total k I.w with hk | hk
  · exact hle k hk
  · rw [I.ram_of_le k hk, J.ram_of_le k (hw ▸ hk), ← hw]
    exact hle _ le_rfl

variable [IsDomain R] [IsDiscreteValuationRing R]

lemma isUnit_add_mul (hϖ : Irreducible ϖ) {u : R} (hu : IsUnit u) (t : R) : IsUnit (u + ϖ * t) := by
  refine (residue_ne_zero_iff_isUnit _).mp ?_
  rw [map_add, map_mul, (hϖ.residue_eq_zero_iff_dvd ϖ).mpr dvd_rfl, zero_mul, add_zero]
  exact (residue_ne_zero_iff_isUnit _).mpr hu

lemma mul_mean_add_le_of_addVal_coeff (hϖ : Irreducible ϖ) (hi : i ∈ Icc 1 I.ramificationIndex)
    (hj : addVal R ((I.specialisation ϖ f).coeff i) = j) :
    (I.ramificationIndex : ℚ) * (I.mean (I.w - min (padicValNat p i) I.w) + 1) ≤
      (I.ramificationIndex * j + i : ℕ) := by
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hi₀ : i ≠ 0 :=
    (Nat.lt_of_lt_of_le one_pos (mem_Icc.mp hi).1).ne'
  rcases (mem_Icc.mp hi).2.lt_or_eq with hlt | rfl
  · rcases exists_mem_genericIndices_of_addVal_coeff hϖ hlt hj with ⟨σ, hσ, hmod, hle⟩
    have hσ₀ : σ ≠ 0 := by
      rintro rfl
      exact hi₀ (hmod.symm.trans (Nat.zero_mod _))
    have hmean : I.mean (I.pointIndex (σ % I.ramificationIndex)) ≤ (σ : ℚ) / I.ramificationIndex :=
      mean_le_of_mem_genericIndices hσ hσ₀
    rw [hmod, pointIndex, padicValNat_gcd_pow hi₀, le_div_iff₀ he] at hmean
    have hσeq : (σ : ℚ) = I.ramificationIndex * (σ / I.ramificationIndex : ℕ) + i := by
      have h₁ : I.ramificationIndex * (σ / I.ramificationIndex) + σ % I.ramificationIndex = σ :=
        Nat.div_add_mod σ I.ramificationIndex
      rw [hmod] at h₁
      exact_mod_cast h₁.symm
    have hle' : ((σ / I.ramificationIndex + 1 : ℕ) : ℚ) ≤ j := by
      exact_mod_cast hle
    push_cast at hle' ⊢
    nlinarith
  · rw [padicValNat_ramificationIndex, min_self, Nat.sub_self, I.mean_zero, zero_add]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℚ) j]

lemma polygon_le_of_isAdmissible (hadm : I.IsAdmissible e₀) (he₀ : addVal R (p : R) = e₀)
    (hϖ : Irreducible ϖ) (h : IsMongeRoot (I.specialisation ϖ f) π p) (hk : k ≤ I.w) (hr : r ≠ 0)
    (hv : addVal S ((taylor π ((I.specialisation ϖ f).map (algebraMap R S))).coeff r) = v) :
    (I.ramificationIndex : ℚ) * (I.swanSlope k + 1) ≤ v + r + r * I.ram k := by
  have hp : p.Prime :=
    Fact.out
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hn : (I.specialisation ϖ f).natDegree = I.ramificationIndex :=
    natDegree_specialisation ϖ f
  rcases exists_mem_Icc_addVal_coeff_taylor_add_eq h hr with ⟨i, hi, hti⟩
  rw [hv, addVal_algebraMap_mul_pow h, addVal_mul, ← Nat.cast_add] at hti
  rcases exists_natCast_of_natCast_eq_nsmul_add h.natDegree_pos.ne' hti with ⟨b, j, hb, hj, hvj⟩
  rw [hn] at hi hvj
  have hC1 : (I.ramificationIndex : ℚ) * (I.mean (I.w - min (padicValNat p i) I.w) + 1) ≤
      (I.ramificationIndex * j + i : ℕ) :=
    mul_mean_add_le_of_addVal_coeff hϖ hi hj
  have hchoose : i.choose r ≠ 0 := fun h₀ ↦ by
    rw [h₀, Nat.cast_zero, addVal_zero] at hb
    exact ENat.natCast_ne_top b hb.symm
  have hri : r ≤ i := by
    by_contra hlt
    exact hchoose (Nat.choose_eq_zero_of_lt (not_le.mp hlt))
  rw [addVal_natCast_eq h he₀ hchoose] at hb
  have hb' : padicValNat p (i.choose r) * e₀ = b := by
    exact_mod_cast hb
  have hrk : (0 : ℚ) ≤ I.ram k :=
    I.ram_nonneg k
  have hvj' : (v : ℚ) + r = (I.ramificationIndex * (b + j) + i : ℕ) := by
    exact_mod_cast hvj
  have hra : min (padicValNat p i) I.w ≤ I.w :=
    min_le_right _ _
  have hab : min (padicValNat p i) I.w ≤ padicValNat p i :=
    min_le_left _ _
  generalize min (padicValNat p i) I.w = a at hC1 hra hab
  have hline : (I.ramificationIndex : ℚ) * I.swanSlope k ≤
      I.ramificationIndex * I.mean (I.w - a) + p ^ a * I.ram k := by
    have h₁ : (I.ramificationIndex : ℚ) * I.swanSlope k ≤ I.polygonLine (I.w - a) (I.ram k) :=
      I.polygonLine_le hk (Nat.sub_le _ _)
    rwa [polygonLine, Nat.sub_sub_self hra] at h₁
  have hb₀ : (0 : ℚ) ≤ b :=
    Nat.cast_nonneg b
  have hmul₀ : (0 : ℚ) ≤ I.ramificationIndex * b :=
    mul_nonneg he.le hb₀
  have hdvd : p ^ padicValNat p r ≤ r :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hr) pow_padicValNat_dvd
  rcases le_or_gt a (padicValNat p r) with hcase | hcase
  · have hpr : ((p ^ a : ℕ) : ℚ) ≤ r := by
      exact_mod_cast (Nat.pow_le_pow_right hp.pos hcase).trans hdvd
    have hmul : ((p ^ a : ℕ) : ℚ) * I.ram k ≤ r * I.ram k :=
      mul_le_mul_of_nonneg_right hpr hrk
    push_cast at hC1 hvj' hmul ⊢
    rw [mul_add] at hC1 ⊢
    rw [mul_add] at hvj'
    linarith
  · have hlow : padicValNat p i ≤ padicValNat p (i.choose r) + padicValNat p r :=
      padicValNat_le_padicValNat_choose_add hri hr
    have hline₂ : (I.ramificationIndex : ℚ) * I.swanSlope k ≤
        I.ramificationIndex * I.mean (I.w - padicValNat p r) + p ^ padicValNat p r * I.ram k := by
      have h₁ : (I.ramificationIndex : ℚ) * I.swanSlope k ≤
          I.polygonLine (I.w - padicValNat p r) (I.ram k) :=
        I.polygonLine_le hk (Nat.sub_le _ _)
      rwa [polygonLine, Nat.sub_sub_self (by omega)] at h₁
    have hmean : I.mean (I.w - a + (a - padicValNat p r)) - I.mean (I.w - a) ≤
        ((a - padicValNat p r : ℕ) : ℚ) * e₀ :=
      I.mean_add_sub_le hadm.smallRam_le (by omega)
    rw [(by omega : I.w - a + (a - padicValNat p r) = I.w - padicValNat p r)] at hmean
    have hge : ((a - padicValNat p r : ℕ) : ℚ) * e₀ ≤ b := by
      rw [← hb']
      exact_mod_cast Nat.mul_le_mul_right e₀ (by omega)
    have hpr : ((p ^ padicValNat p r : ℕ) : ℚ) ≤ r := by
      exact_mod_cast hdvd
    have hmul : ((p ^ padicValNat p r : ℕ) : ℚ) * I.ram k ≤ r * I.ram k :=
      mul_le_mul_of_nonneg_right hpr hrk
    have hmul₂ : (I.ramificationIndex : ℚ) * (I.mean (I.w - padicValNat p r) - I.mean (I.w - a)) ≤
        I.ramificationIndex * (((a - padicValNat p r : ℕ) : ℚ) * e₀) :=
      mul_le_mul_of_nonneg_left hmean he.le
    have hmul₃ : (I.ramificationIndex : ℚ) * (((a - padicValNat p r : ℕ) : ℚ) * e₀) ≤
        I.ramificationIndex * b :=
      mul_le_mul_of_nonneg_left hge he.le
    push_cast at hC1 hvj' hmul ⊢
    rw [mul_add] at hC1 ⊢
    rw [mul_add] at hvj'
    rw [mul_sub] at hmul₂
    nlinarith

lemma addVal_coeff_of_pointType_eq_A (hϖ : Irreducible ϖ)
    (hA : ∀ σ ∈ I.genericIndices, I.pointType σ = .A → IsUnit (f σ)) (hσ : σ ∈ I.genericIndices)
    (hT : I.pointType σ = .A) : addVal R ((I.specialisation ϖ f).coeff (σ % I.ramificationIndex)) =
      ((σ / I.ramificationIndex + 1 : ℕ) : ℕ∞) := by
  classical
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hpos : 0 < I.ramificationIndex :=
    ramificationIndex_pos
  have hσ₀ : σ ≠ 0 :=
    ne_zero_of_pointType_eq_A hT
  have hm : (σ : ℚ) / I.ramificationIndex = I.mean (I.pointIndex (σ % I.ramificationIndex)) :=
    div_eq_mean_of_pointType_eq_A hT
  have hother {τ : ℕ} (hτ : τ ∈ I.genericIndices.erase σ)
      (hmod : σ % I.ramificationIndex = τ % I.ramificationIndex) :
      σ / I.ramificationIndex + 1 ≤ τ / I.ramificationIndex := by
    have hτ₀ : τ ≠ 0 := by
      rintro rfl
      have h₁ : I.pointIndex (σ % I.ramificationIndex) = 0 := by
        rw [hmod, Nat.zero_mod, I.pointIndex_zero]
      rw [h₁, I.mean_zero] at hm
      exact hσ₀ (by simpa [he.ne'] using hm)
    have hτ₁ : I.mean (I.pointIndex (τ % I.ramificationIndex)) ≤ (τ : ℚ) / I.ramificationIndex :=
      mean_le_of_mem_genericIndices (mem_of_mem_erase hτ) hτ₀
    rw [← hmod, ← hm, div_le_div_iff_of_pos_right he] at hτ₁
    have hle : σ ≤ τ := by
      exact_mod_cast hτ₁
    have hlt : σ < τ :=
      lt_of_le_of_ne hle fun heq ↦ (ne_of_mem_erase hτ) heq.symm
    have h₁ : I.ramificationIndex * (σ / I.ramificationIndex) + σ % I.ramificationIndex = σ :=
      Nat.div_add_mod σ I.ramificationIndex
    have h₂ : I.ramificationIndex * (τ / I.ramificationIndex) + τ % I.ramificationIndex = τ :=
      Nat.div_add_mod τ I.ramificationIndex
    rw [hmod] at h₁
    by_contra hc
    have h₃ : τ / I.ramificationIndex ≤ σ / I.ramificationIndex := by
      omega
    have h₄ : I.ramificationIndex * (τ / I.ramificationIndex) ≤
        I.ramificationIndex * (σ / I.ramificationIndex) :=
      Nat.mul_le_mul_left I.ramificationIndex h₃
    omega
  have hsum : ϖ ^ (σ / I.ramificationIndex + 1) ∣ ∑ τ ∈ I.genericIndices.erase σ,
      if σ % I.ramificationIndex = τ % I.ramificationIndex then
        f τ * ϖ ^ (τ / I.ramificationIndex) else 0 := by
    refine dvd_sum fun τ hτ ↦ ?_
    split_ifs with hmod
    · exact (pow_dvd_pow ϖ (hother hτ hmod)).mul_left _
    · exact dvd_zero _
  rcases hsum with ⟨t, ht⟩
  rw [coeff_specialisation_of_lt ϖ f (Nat.mod_lt σ hpos), ← add_sum_erase _ _ hσ, ite_eq_left rfl,
    ht, (by ring1 : ϖ * (f σ * ϖ ^ (σ / I.ramificationIndex) +
      ϖ ^ (σ / I.ramificationIndex + 1) * t) = ϖ ^ (σ / I.ramificationIndex + 1) * (f σ + ϖ * t)),
    addVal_mul, addVal_pow, addVal_uniformizer hϖ,
    addVal_eq_zero_iff.mpr (isUnit_add_mul hϖ (hA σ hσ hT) t), add_zero, nsmul_one]

lemma smallRam_pos (hk : k < I.w) : 0 < I.smallRam (k + 1) := by
  have hp₁ : (1 : ℚ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hε : (0 : ℚ) < I.ε :=
    I.natCast_ε_pos
  have hr : 0 < I.ram (k + 1) :=
    (I.zero_lt_ram_one (by omega)).trans_le (I.monotone_ram (by omega))
  exact div_pos (mul_pos (by linarith) hr) (by positivity)

lemma isVertex_of_smallRam_eq (hadm : I.IsAdmissible e₀) (hk : k < I.w)
    (hs : I.smallRam (k + 1) = e₀) : I.IsVertex k := by
  have hp₁ : (1 : ℚ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  by_contra hnv
  rw [IsVertex, not_or, not_lt] at hnv
  have hr : I.ram (k + 1) = I.ram k :=
    le_antisymm hnv.2 (I.monotone_ram k.le_succ)
  rcases k with _ | k
  · have h₀ : 0 < I.ram 1 :=
      I.zero_lt_ram_one (by omega)
    rw [zero_add] at hr
    rw [hr, I.ram_zero] at h₀
    exact lt_irrefl 0 h₀
  · have h₁ : I.smallRam (k + 1) ≤ e₀ :=
      hadm.smallRam_le (by omega)
    rw [I.smallRam_eq_mul_of_ram_eq hr, hs] at h₁
    have h₂ : 0 < I.smallRam (k + 1 + 1) :=
      smallRam_pos hk
    rw [hs] at h₂
    nlinarith

lemma pointType_eq_A_of_pointIndex (hk : k < I.w) (hv : I.IsVertex (k + 1))
    (hd : (I.smallRam (k + 1)).den ≠ 1) (hσ : (σ : ℚ) = I.ramificationIndex * I.mean (k + 1))
    (hidx : I.pointIndex (σ % I.ramificationIndex) = k + 1) : I.pointType σ = .A := by
  have hp : p.Prime :=
    Fact.out
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hp₀ : (0 : ℚ) < p :=
    natCast_prime_pos
  have hε : (0 : ℚ) < I.ε :=
    I.natCast_ε_pos
  have hm : (σ : ℚ) / I.ramificationIndex = I.mean (k + 1) := by
    rw [hσ, mul_div_cancel_left₀ _ he.ne']
  have hmpos : 0 < I.mean (k + 1) := by
    rw [I.mean_succ]
    exact add_pos_of_nonneg_of_pos (I.mean_nonneg k) (smallRam_pos hk)
  have hσ₀ : σ ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, zero_div] at hm
    exact hmpos.ne hm
  have hslope : I.mean (k + 1) < I.swanSlope (k + 1) := by
    have ht : I.tinyRam (k + 1) = I.swanSlope (k + 1) - I.mean (k + 1) :=
      I.tinyRam_eq_swanSlope_sub_mean hp.ne_zero (k + 1)
    have hr : 0 < I.ram (k + 1) :=
      (I.zero_lt_ram_one (by omega)).trans_le (I.monotone_ram (by omega))
    have h₂ : 0 < I.tinyRam (k + 1) :=
      div_pos hr (by positivity)
    linarith
  have hfinal : I.IsFinal (k + 1) := by
    rcases hv with h₁ | h₁
    · exact .inl h₁
    · refine .inr ?_
      rw [swanSlope, swanSlope, sum_range_succ _ (k + 1)]
      exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr h₁) (by positivity))
  rw [pointType, ite_eq_right hσ₀, hidx]
  have h₃ : (I.point σ).2 = I.mean (k + 1) :=
    hm
  rw [h₃, ite_eq_right (lt_irrefl _), ite_eq_left hslope, ite_eq_left ⟨rfl, hd, hfinal⟩]

lemma swanSlope_mono : Monotone I.swanSlope := by
  refine monotone_nat_of_le_succ fun k ↦ ?_
  have hp₀ : (0 : ℚ) < p :=
    natCast_prime_pos
  have hε : (0 : ℚ) < I.ε :=
    I.natCast_ε_pos
  rw [swanSlope, swanSlope, sum_range_succ]
  exact le_add_of_nonneg_right
    (div_nonneg (sub_nonneg.mpr (I.monotone_ram k.le_succ)) (by positivity))

lemma mem_range_floor_of_div_le (hle : (σ : ℚ) / I.ramificationIndex ≤ I.swanSlope I.w) :
    σ ∈ range (⌊(I.ramificationIndex : ℚ) * I.swanSlope I.w⌋₊ + 1) := by
  refine mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ?_))
  rw [mul_comm]
  exact (div_le_iff₀ I.natCast_ramificationIndex_pos).mp hle

lemma mem_genericIndices_of_pointType (hT : I.pointType σ = .A ∨ I.pointType σ = .B) :
    σ ∈ I.genericIndices :=
  mem_filter.mpr ⟨mem_range_floor_of_div_le
    ((lt_swanSlope_of_pointType hT).le.trans (swanSlope_mono (Nat.sub_le _ _))),
    .inr (hT.imp id .inl)⟩

/-- **The terms of a semicanonical polynomial at the vertices** (Monge, arXiv:1109.4617, §2.2): if
`I` is admissible for `e₀ = v_R(p)`, and `f_σ` is a unit at the `A`-points, then for a vertex `k` of
`I` there is an `i` with `p ^ (w - k) ∣ i` and
`e v_R(q_i) + e (v_p(i) - (w - k)) e₀ + i = e (m_k + 1)` for the specialisation `q` of the generic
polynomial at `f`: it comes from an `A`-point, of the index `k` when the band `B_k` is geometric,
and of a smaller index when it is arithmetic, and from the leading term `x ^ e` when there is no
such `A`-point. -/
lemma exists_vertex_term_specialisation (hadm : I.IsAdmissible e₀) (hϖ : Irreducible ϖ)
    (hA : ∀ σ ∈ I.genericIndices, I.pointType σ = .A → IsUnit (f σ)) (hk : k ≤ I.w)
    (hv : I.IsVertex k) : ∃ i ∈ Icc 1 I.ramificationIndex, ∃ j : ℕ,
      addVal R ((I.specialisation ϖ f).coeff i) = j ∧ I.w - k ≤ padicValNat p i ∧
        ((I.ramificationIndex * ((padicValNat p i - (I.w - k)) * e₀ + j) + i : ℕ) : ℚ) =
          I.ramificationIndex * (I.mean k + 1) := by
  have hp : p.Prime :=
    Fact.out
  have hpos : 0 < I.ramificationIndex :=
    ramificationIndex_pos
  induction k with
  | zero =>
    refine ⟨I.ramificationIndex, mem_Icc.mpr ⟨hpos, le_rfl⟩, 0, ?_, ?_, ?_⟩
    · have hm : (I.specialisation ϖ f).coeff I.ramificationIndex = 1 := by
        have h₁ : (I.specialisation ϖ f).coeff (I.specialisation ϖ f).natDegree = 1 :=
          (monic_specialisation ϖ f).coeff_natDegree
        rwa [natDegree_specialisation] at h₁
      rw [hm]
      simp
    · rw [padicValNat_ramificationIndex]
      omega
    · rw [padicValNat_ramificationIndex, Nat.sub_zero, Nat.sub_self, I.mean_zero]
      simp
  | succ k ih =>
    have hk' : k < I.w :=
      hk
    by_cases hd : (I.smallRam (k + 1)).den = 1
    · have hs : I.smallRam (k + 1) = e₀ :=
        hadm.smallRam_eq hk' hv hd
      rcases ih hk'.le (isVertex_of_smallRam_eq hadm hk' hs) with ⟨i, hi, j, hj, hle, hform⟩
      refine ⟨i, hi, j, hj, by omega, ?_⟩
      have hsub : padicValNat p i - (I.w - (k + 1)) = padicValNat p i - (I.w - k) + 1 := by
        omega
      rw [hsub, I.mean_succ, hs]
      rw [mul_add] at hform
      push_cast at hform ⊢
      linear_combination hform
    · rcases hadm.exists_pointIndex_eq hk' hv hd with ⟨σ, hσ, hidx⟩
      have hT : I.pointType σ = .A :=
        pointType_eq_A_of_pointIndex hk' hv hd hσ hidx
      have hmodlt : σ % I.ramificationIndex < I.ramificationIndex :=
        Nat.mod_lt σ hpos
      have hi₀ : σ % I.ramificationIndex ≠ 0 := by
        intro h₀
        rw [h₀, I.pointIndex_zero] at hidx
        omega
      have hvp : padicValNat p (σ % I.ramificationIndex) = I.w - (k + 1) := by
        rw [pointIndex, padicValNat_gcd_pow hi₀] at hidx
        rcases le_total (padicValNat p (σ % I.ramificationIndex)) I.w with h₁ | h₁
        · rw [min_eq_left h₁] at hidx
          omega
        · rw [min_eq_right h₁] at hidx
          omega
      refine ⟨σ % I.ramificationIndex, mem_Icc.mpr ⟨Nat.pos_of_ne_zero hi₀, hmodlt.le⟩,
        σ / I.ramificationIndex + 1,
        addVal_coeff_of_pointType_eq_A hϖ hA (mem_genericIndices_of_pointType (.inl hT)) hT,
        hvp.ge, ?_⟩
      rw [hvp, Nat.sub_self, zero_mul, zero_add, mul_add, mul_add]
      have h₂ : (σ : ℚ) = I.ramificationIndex * (σ / I.ramificationIndex : ℕ) +
          (σ % I.ramificationIndex : ℕ) := by
        exact_mod_cast (Nat.div_add_mod σ I.ramificationIndex).symm
      push_cast at h₂ ⊢
      linear_combination hσ - h₂

/-- **The ramification polygon of a semicanonical polynomial** (Monge, arXiv:1109.4617, §2.2): let
`I` be admissible for `e₀ = v_R(p)`, and `q` the specialisation of the generic polynomial of `I` at
coefficients `f_σ` that are units at the `A`-points, and let `π` be a root of `q` in a discrete
valuation ring `S` over `R`, satisfying the hypotheses of Monge's reduction. Then the ramification
polygon of `q` at `π` is the polygon of `I`. -/
lemma isRamificationPolygon_specialisation (hadm : I.IsAdmissible e₀) (he₀ : addVal R (p : R) = e₀)
    (hϖ : Irreducible ϖ) (hA : ∀ σ ∈ I.genericIndices, I.pointType σ = .A → IsUnit (f σ))
    (h : IsMongeRoot (I.specialisation ϖ f) π p) :
    I.IsRamificationPolygon (I.specialisation ϖ f) π := by
  have hp : p.Prime :=
    Fact.out
  have hn : (I.specialisation ϖ f).natDegree = I.ramificationIndex :=
    natDegree_specialisation ϖ f
  refine ⟨hn, polygon_le_of_isAdmissible hadm he₀ hϖ h, fun {k} hk hv ↦ ?_⟩
  rcases exists_vertex_term_specialisation hadm hϖ hA hk hv with ⟨i, hi, j, hj, hle, hform⟩
  rcases exists_addVal_natCast_choose_pow h he₀ (hn.symm ▸ hi) hj hle with ⟨v, hv', hvle⟩
  refine ⟨v, hv', le_antisymm ?_ ?_⟩
  · rw [hn] at hvle
    rw [← hform]
    exact_mod_cast hvle
  · have hLB : (I.ramificationIndex : ℚ) * (I.swanSlope k + 1) ≤
        v + (p ^ (I.w - k) : ℕ) + (p ^ (I.w - k) : ℕ) * I.ram k :=
      polygon_le_of_isAdmissible hadm he₀ hϖ h hk (pow_ne_zero (I.w - k) hp.ne_zero) hv'
    have hline : (I.ramificationIndex : ℚ) * I.swanSlope k =
        I.ramificationIndex * I.mean k + p ^ (I.w - k) * I.ram k :=
      I.mul_swanSlope_eq hk
    rw [mul_add, hline] at hLB
    rw [mul_add]
    push_cast at hLB ⊢
    linarith

end IsNonarchimedeanLocalField.HerbrandInvariant
