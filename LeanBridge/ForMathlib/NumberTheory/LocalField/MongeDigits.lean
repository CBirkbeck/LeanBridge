import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeConverse

/-!
# The digits of a polynomial and the reduction step of Monge

Monge's reduction algorithm (arXiv:1109.4617, Algorithms 1 and 2, p. 7) determines the coefficients
of a polynomial `g` over a discrete valuation ring with uniformiser `ϖ`, of degree `e`, one digit at
a time: the digit `f_r` at `r = j e + i`, `0 ≤ i < e`, is the coefficient of `ϖ ^ (j + 1) x ^ i`.
This file sets up the corresponding notion
(`IsNonarchimedeanLocalField.HerbrandInvariant.HasDigits`) and determines the digits at the
`A`-points and the `Z`-points from the ramification polygon, which proves the first part of Monge's
Proposition 3 (p. 9).

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.digitSum`: the sum of the terms of the digits below
  `r`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.HasDigits`: a polynomial has given digits below `r`.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.specialisation_eq_add_digitSum`: the semicanonical
  polynomials from the digits.
* `IsNonarchimedeanLocalField.HerbrandInvariant.HasDigits.pow_dvd_coeff`: the digit at `r`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.HasDigits.succ`: the passage to the next digit.
* `IsNonarchimedeanLocalField.HerbrandInvariant.addVal_coeff_eq_of_pointType_eq_A`: the digits at
  the `A`-points do not vanish.
* `IsNonarchimedeanLocalField.HerbrandInvariant.lt_addVal_coeff_of_pointType_eq_Z`: the digits at
  the `Z`-points vanish.
-/

open Finset IsDiscreteValuationRing IsLocalRing Polynomial

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (ϖ : R) (f : ℕ → R) (r : ℕ) {π : S}

variable [IsLocalRing R] in
lemma mem_maximalIdeal_of_dvd_algebraMap (hπ : Irreducible π) {x : R} (hx : π ∣ algebraMap R S x) :
    x ∈ maximalIdeal R := by
  by_contra hne
  exact hπ.not_isUnit (isUnit_of_dvd_unit hx ((notMem_maximalIdeal.mp hne).map _))

lemma C_pow_dvd_comp_of_forall_pow_dvd {D : R[X]} {M m : ℕ}
    (hD : ∀ i, π ^ M ∣ algebraMap R S (D.coeff i) * π ^ i) :
    C (π ^ M) ∣ (D.map (algebraMap R S)).comp (C π + C (π ^ (m + 1)) * X) := by
  rw [comp, eval₂_map, eval₂_eq_sum_range]
  refine dvd_sum fun i _ ↦ ?_
  have hA : C π + C (π ^ (m + 1)) * X = C π * (1 + C (π ^ m) * X) := by
    rw [pow_succ', C_mul]
    ring1
  rw [hA, mul_pow, ← C_pow, RingHom.comp_apply, ← mul_assoc, ← C_mul]
  exact (map_dvd C (hD i)).mul_right _

/-- The polynomial `∑_{σ < r} f_σ ϖ ^ (j + 1) x ^ i`, the sum over the indices `σ = j e + i`,
`0 ≤ i < e`, below `r`: the **sum of the terms of the digits** `f_σ` below `r`, for `e` the
ramification index of the Herbrand invariant `I` (Monge, arXiv:1109.4617, p. 7). -/
noncomputable def digitSum : R[X] :=
  ∑ σ ∈ range r, C (f σ * ϖ ^ (σ / I.ramificationIndex + 1)) * X ^ (σ % I.ramificationIndex)

lemma digitSum_succ : I.digitSum ϖ f (r + 1) = I.digitSum ϖ f r +
    C (f r * ϖ ^ (r / I.ramificationIndex + 1)) * X ^ (r % I.ramificationIndex) :=
  sum_range_succ _ _

variable {f r}

lemma digitSum_congr {f' : ℕ → R} (h : ∀ σ < r, f σ = f' σ) :
    I.digitSum ϖ f r = I.digitSum ϖ f' r :=
  sum_congr rfl fun σ hσ ↦ by rw [h σ (mem_range.mp hσ)]

lemma coeff_digitSum (i : ℕ) : (I.digitSum ϖ f r).coeff i = ∑ σ ∈ range r,
    if i = σ % I.ramificationIndex then f σ * ϖ ^ (σ / I.ramificationIndex + 1) else 0 := by
  rw [digitSum, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]

lemma coeff_digitSum_eq_zero {i : ℕ} (h : ∀ σ < r, σ % I.ramificationIndex = i → f σ = 0) :
    (I.digitSum ϖ f r).coeff i = 0 := by
  rw [coeff_digitSum]
  refine sum_eq_zero fun σ hσ ↦ ?_
  split_ifs with hi
  · rw [h σ (mem_range.mp hσ) hi.symm, zero_mul]
  · rfl

variable [IsDomain R] [IsDiscreteValuationRing R] (f r) in
/-- The polynomial `g` over a discrete valuation ring **has the digits `f` below `r`**: for every
`0 ≤ i < e`, the coefficient of `x ^ i` of `g - ∑_{σ < r} f_σ ϖ ^ (j + 1) x ^ i` has valuation at
least `j + 1` as soon as `j e + i ≥ r`. In other words, `r + e ≤ e v(c_i) + i` for its coefficient
`c_i` (Monge, arXiv:1109.4617, p. 7). -/
def HasDigits (g : R[X]) : Prop :=
  ∀ i < I.ramificationIndex, ((r + I.ramificationIndex : ℕ) : ℕ∞) ≤
    I.ramificationIndex • addVal R ((g - I.digitSum ϖ f r).coeff i) + i

variable {I ϖ}

/-- **The semicanonical polynomials from the digits**: the specialisation of the generic polynomial
at digits `f` which vanish off the generic indices is `x ^ e` plus the sum of the terms of the
digits. -/
lemma specialisation_eq_add_digitSum (hgen : I.genericIndices ⊆ range r)
    (hf : ∀ σ < r, σ ∉ I.genericIndices → f σ = 0) :
    I.specialisation ϖ f = X ^ I.ramificationIndex + I.digitSum ϖ f r := by
  rw [specialisation, digitSum, ← sum_subset hgen fun σ hσ hn ↦ by
    rw [hf σ (mem_range.mp hσ) hn, zero_mul, C_0, zero_mul], mul_sum]
  congr 1
  refine sum_congr rfl fun σ _ ↦ ?_
  rw [← mul_assoc, ← C_mul, pow_succ]
  congr 2
  ring1

lemma notMem_genericIndices_of_pointType_eq_Z {σ : ℕ} (hZ : I.pointType σ = .Z) :
    σ ∉ I.genericIndices := fun hσ ↦ by
  rcases (mem_filter.mp hσ).2 with h | h | h | ⟨h, -⟩ <;> rw [hZ] at h <;> cases h

variable [Fact p.Prime] in
lemma pointType_eq_Z_of_lt {σ : ℕ} (hσ : σ < r)
    (hmod : σ % I.ramificationIndex = r % I.ramificationIndex) (hr₀ : r ≠ 0)
    (hr : (r : ℚ) / I.ramificationIndex ≤ I.mean (I.pointIndex (r % I.ramificationIndex))) :
    I.pointType σ = .Z := by
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hσ₀ : σ ≠ 0 := by
    rintro rfl
    rw [← hmod, Nat.zero_mod, I.pointIndex_zero, I.mean_zero] at hr
    exact absurd hr (not_le.mpr (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hr₀) he))
  have hlt : (σ : ℚ) / I.ramificationIndex < (r : ℚ) / I.ramificationIndex :=
    div_lt_div_of_pos_right (by exact_mod_cast hσ) he
  rw [pointType, ite_eq_right hσ₀]
  exact ite_eq_left (by rw [hmod]; exact hlt.trans_le hr)

variable [Fact p.Prime] in
lemma coeff_digitSum_eq_zero_of_le_mean (hf : ∀ σ < r, σ ∉ I.genericIndices → f σ = 0) (hr₀ : r ≠ 0)
    (hr : (r : ℚ) / I.ramificationIndex ≤ I.mean (I.pointIndex (r % I.ramificationIndex))) :
    (I.digitSum ϖ f r).coeff (r % I.ramificationIndex) = 0 :=
  coeff_digitSum_eq_zero I ϖ fun σ hσ hmod ↦ hf σ hσ
    (notMem_genericIndices_of_pointType_eq_Z (pointType_eq_Z_of_lt hσ hmod hr₀ hr))

variable [IsDomain R] [IsDiscreteValuationRing R] {e i j N : ℕ} {x y : R}

lemma le_nsmul_addVal_sub_add (hx : (N : ℕ∞) ≤ e • addVal R x + i)
    (hy : (N : ℕ∞) ≤ e • addVal R y + i) : (N : ℕ∞) ≤ e • addVal R (x - y) + i := by
  have hmin : min (addVal R x) (addVal R y) ≤ addVal R (x - y) :=
    AddValuation.map_sub (addVal R) x y
  have hmono : e • min (addVal R x) (addVal R y) + i ≤ e • addVal R (x - y) + i :=
    add_le_add_left (nsmul_le_nsmul_right hmin e) _
  refine le_trans ?_ hmono
  rcases le_total (addVal R x) (addVal R y) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

lemma succ_le_nsmul_addVal_add (he : e ≠ 0) (hx : (N : ℕ∞) ≤ e • addVal R x + i) (hi : i < e)
    (hN : N % e ≠ i) : ((N + 1 : ℕ) : ℕ∞) ≤ e • addVal R x + i := by
  rcases eq_or_ne (addVal R x) ⊤ with htop | htop
  · rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast he), top_add]
    exact le_top
  rcases ENat.ne_top_iff_exists.mp htop with ⟨v, hv⟩
  rw [← hv, nsmul_eq_mul] at hx ⊢
  have hx' : N ≤ e * v + i := by
    exact_mod_cast hx
  have h₂ : N + 1 ≤ e * v + i :=
    lt_of_le_of_ne hx' fun heq ↦ hN (by rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hi])
  exact_mod_cast h₂

lemma pow_dvd_of_le_nsmul_addVal_add (hϖ : Irreducible ϖ) (he : e ≠ 0)
    (hx : ((e * j + i : ℕ) : ℕ∞) ≤ e • addVal R x + i) : ϖ ^ j ∣ x := by
  rw [pow_dvd_iff_le_addVal hϖ]
  rcases eq_or_ne (addVal R x) ⊤ with htop | htop
  · rw [htop]
    exact le_top
  rcases ENat.ne_top_iff_exists.mp htop with ⟨v, hv⟩
  rw [← hv, nsmul_eq_mul] at hx
  rw [← hv]
  have hx' : e * j ≤ e * v := by
    have h₁ : e * j + i ≤ e * v + i := by
      exact_mod_cast hx
    omega
  exact_mod_cast Nat.le_of_mul_le_mul_left hx' (Nat.pos_of_ne_zero he)

lemma le_nsmul_addVal_add_of_pow_dvd (hϖ : Irreducible ϖ) (hx : ϖ ^ j ∣ x) :
    ((e * j + i : ℕ) : ℕ∞) ≤ e • addVal R x + i := by
  rw [Nat.cast_add]
  refine add_le_add_left ?_ _
  rw [Nat.cast_mul, ← nsmul_eq_mul]
  exact nsmul_le_nsmul_right ((pow_dvd_iff_le_addVal hϖ).mp hx) e

variable [Fact p.Prime] {g : R[X]}

/-- **The digit at `r`**: a polynomial with the digits `f` below `r` has, at `i = r mod e` and for
`j = r / e`, a coefficient `c_i` of `g - ∑_{σ < r} f_σ ϖ ^ (j + 1) x ^ i` divisible by
`ϖ ^ (j + 1)`. -/
lemma HasDigits.pow_dvd_coeff (hϖ : Irreducible ϖ) (h : I.HasDigits ϖ f r g) :
    ϖ ^ (r / I.ramificationIndex + 1) ∣ (g - I.digitSum ϖ f r).coeff (r % I.ramificationIndex) := by
  have hpos : 0 < I.ramificationIndex :=
    ramificationIndex_pos
  refine pow_dvd_of_le_nsmul_addVal_add hϖ hpos.ne' (i := r % I.ramificationIndex) ?_
  have h₁ : ((r + I.ramificationIndex : ℕ) : ℕ∞) ≤ I.ramificationIndex •
      addVal R ((g - I.digitSum ϖ f r).coeff (r % I.ramificationIndex)) +
        (r % I.ramificationIndex : ℕ) :=
    h _ (Nat.mod_lt r hpos)
  have h₂ : I.ramificationIndex * (r / I.ramificationIndex) + r % I.ramificationIndex = r :=
    Nat.div_add_mod r I.ramificationIndex
  have hnum : r + I.ramificationIndex = I.ramificationIndex * (r / I.ramificationIndex + 1) +
      r % I.ramificationIndex := by
    rw [mul_add, mul_one]
    omega
  rwa [hnum] at h₁

/-- **The passage to the next digit**: if `g` has the digits `f` below `r`, the coefficients of `g'`
agree with those of `g` below the level `r + e`, and the digit of `g'` at `r` is `t`, then `g'` has
the digits `f`, updated with `f_r = t`, below `r + 1`. -/
lemma HasDigits.succ {g' : R[X]} {t : R} (hϖ : Irreducible ϖ) (h : I.HasDigits ϖ f r g)
    (hd : ∀ i < I.ramificationIndex, ((r + I.ramificationIndex : ℕ) : ℕ∞) ≤
      I.ramificationIndex • addVal R ((g - g').coeff i) + i)
    (ht : ϖ ^ (r / I.ramificationIndex + 2) ∣ (g' - I.digitSum ϖ f r).coeff
      (r % I.ramificationIndex) - t * ϖ ^ (r / I.ramificationIndex + 1)) :
    I.HasDigits ϖ (Function.update f r t) (r + 1) g' := by
  have hpos : 0 < I.ramificationIndex :=
    ramificationIndex_pos
  have hsum : I.digitSum ϖ (Function.update f r t) (r + 1) = I.digitSum ϖ f r +
      C (t * ϖ ^ (r / I.ramificationIndex + 1)) * X ^ (r % I.ramificationIndex) := by
    rw [digitSum_succ, Function.update_self, digitSum_congr I ϖ
      fun σ hσ ↦ Function.update_of_ne hσ.ne _ _]
  intro i hi
  rw [hsum, ← sub_sub, coeff_sub, coeff_C_mul_X_pow]
  split_ifs with hir
  · subst hir
    refine le_trans ?_ (le_nsmul_addVal_add_of_pow_dvd hϖ ht)
    have h₂ : I.ramificationIndex * (r / I.ramificationIndex) + r % I.ramificationIndex = r :=
      Nat.div_add_mod r I.ramificationIndex
    have h₃ : r + 1 + I.ramificationIndex ≤ I.ramificationIndex *
        (r / I.ramificationIndex + 2) + r % I.ramificationIndex := by
      rw [mul_add]
      omega
    exact_mod_cast h₃
  · rw [sub_zero]
    have heq :
        (g' - I.digitSum ϖ f r).coeff i = (g - I.digitSum ϖ f r).coeff i - (g - g').coeff i := by
      simp only [coeff_sub]
      ring1
    rw [heq, Nat.add_right_comm r 1]
    refine succ_le_nsmul_addVal_add hpos.ne' (le_nsmul_addVal_sub_add (h i hi) (hd i hi)) hi ?_
    rw [Nat.add_mod_right]
    exact fun hne ↦ hir hne.symm

variable [IsDomain S] [IsDiscreteValuationRing S] {e₀ : ℕ}

/-- **The digits at the `A`-points do not vanish** (Monge, arXiv:1109.4617, p. 8): if the
ramification polygon of `g` at `π` is that of `I`, and `P_r` is an `A`-point of the Eisenstein
diagram, then the coefficient of `x ^ i` in `g`, `r = j e + i`, `0 ≤ i < e`, has valuation exactly
`j + 1`. -/
lemma addVal_coeff_eq_of_pointType_eq_A (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hT : I.pointType r = .A) :
    addVal R (g.coeff (r % I.ramificationIndex)) = ((r / I.ramificationIndex + 1 : ℕ) : ℕ∞) := by
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hn : g.natDegree = I.ramificationIndex :=
    hP.natDegree_eq
  have hpos : 0 < I.ramificationIndex :=
    hn ▸ h.natDegree_pos
  have hm : (r : ℚ) / I.ramificationIndex = I.mean (I.pointIndex (r % I.ramificationIndex)) :=
    div_eq_mean_of_pointType_eq_A hT
  have hgeo : I.IsGeometricBand (I.pointIndex (r % I.ramificationIndex)) :=
    isGeometricBand_of_pointType_eq_A hT
  have hfin : I.IsFinal (I.pointIndex (r % I.ramificationIndex)) :=
    isFinal_of_pointType_eq_A hT
  have hkw : I.pointIndex (r % I.ramificationIndex) ≤ I.w :=
    Nat.sub_le _ _
  have hr' : (0 : ℚ) < (r : ℚ) / I.ramificationIndex :=
    div_pos (by exact_mod_cast Nat.pos_of_ne_zero (ne_zero_of_pointType_eq_A hT)) he
  rcases hk : I.pointIndex (r % I.ramificationIndex) with _ | k
  · rw [hk, I.mean_zero] at hm
    exact absurd hm hr'.ne'
  rw [hk] at hm hgeo hfin hkw
  have hv : I.IsVertex (k + 1) :=
    hfin.imp id ram_lt_ram_of_swanSlope_lt
  rcases exists_term_of_den_ne_one he₀ h hP hkw hv hgeo with ⟨i, hi, j, hj, hval, hform⟩
  have hσ : (r : ℚ) = I.ramificationIndex * I.mean (k + 1) := by
    rw [← hm]
    field_simp
  have hnat : I.ramificationIndex * j + i = r + I.ramificationIndex := by
    have h₁ : ((I.ramificationIndex * j + i : ℕ) : ℚ) = ((r + I.ramificationIndex : ℕ) : ℚ) := by
      rw [hn] at hform
      rw [hform, mul_add, mul_one, ← hσ]
      push_cast
      rfl
    exact_mod_cast h₁
  have hlt : i < I.ramificationIndex := by
    refine lt_of_le_of_ne (hn ▸ (mem_Icc.mp hi).2) fun hin ↦ ?_
    rw [hin, padicValNat_ramificationIndex] at hval
    omega
  have hmod : i = r % I.ramificationIndex := by
    have h₁ : (I.ramificationIndex * j + i) % I.ramificationIndex =
        (r + I.ramificationIndex) % I.ramificationIndex :=
      congrArg (· % I.ramificationIndex) hnat
    rwa [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, Nat.add_mod_right] at h₁
  have hdiv : j = r / I.ramificationIndex + 1 := by
    have h₁ : I.ramificationIndex * (r / I.ramificationIndex) + r % I.ramificationIndex = r :=
      Nat.div_add_mod r I.ramificationIndex
    rw [← hmod] at h₁
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [mul_add, mul_one]
    omega
  rw [← hmod, hj, hdiv]

/-- **The digits at the `Z`-points vanish** (Monge, arXiv:1109.4617, first part of Proposition 3):
if the ramification polygon of `g` at `π` is that of `I`, and `P_r` is a `Z`-point of the Eisenstein
diagram, then the coefficient of `x ^ i` in `g`, `r = j e + i`, `0 ≤ i < e`, has valuation larger
than `j + 1`. -/
lemma lt_addVal_coeff_of_pointType_eq_Z (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hT : I.pointType r = .Z) :
    ((r / I.ramificationIndex + 1 : ℕ) : ℕ∞) < addVal R (g.coeff (r % I.ramificationIndex)) := by
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hn : g.natDegree = I.ramificationIndex :=
    hP.natDegree_eq
  have hpos : 0 < I.ramificationIndex :=
    hn ▸ h.natDegree_pos
  have hlt : (r : ℚ) / I.ramificationIndex < I.mean (I.pointIndex (r % I.ramificationIndex)) := by
    rw [pointType] at hT
    split_ifs at hT with h₁ h₂
    exact h₂
  have hr₀' : (0 : ℚ) ≤ (r : ℚ) / I.ramificationIndex :=
    div_nonneg (Nat.cast_nonneg r) he.le
  have hk₀ : I.pointIndex (r % I.ramificationIndex) ≠ 0 := by
    intro hk
    rw [hk, I.mean_zero] at hlt
    exact absurd hlt (not_lt.mpr hr₀')
  have hi₀ : r % I.ramificationIndex ≠ 0 := by
    intro hi
    refine hk₀ ?_
    rw [hi, I.pointIndex_zero]
  have hidx : I.pointIndex (r % I.ramificationIndex) =
      I.w - min (padicValNat p (r % I.ramificationIndex)) I.w := by
    rw [pointIndex, padicValNat_gcd_pow hi₀]
  have hw : padicValNat p (r % I.ramificationIndex) ≤ I.w := by
    rcases le_total (padicValNat p (r % I.ramificationIndex)) I.w with h₁ | h₁
    · exact h₁
    · rw [min_eq_right h₁] at hidx
      omega
  rw [min_eq_left hw] at hidx
  by_contra hcon
  rw [not_lt] at hcon
  rcases ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hcon) with ⟨v, hv⟩
  rw [← hv] at hcon
  have hv' : v ≤ r / I.ramificationIndex + 1 := by
    exact_mod_cast hcon
  have hmem : r % I.ramificationIndex ∈ Icc 1 g.natDegree :=
    mem_Icc.mpr ⟨Nat.pos_of_ne_zero hi₀, hn ▸ (Nat.mod_lt r hpos).le⟩
  have hL1 : (I.ramificationIndex : ℚ) *
      (I.mean (I.w - padicValNat p (r % I.ramificationIndex)) + 1) ≤
        (g.natDegree * v + r % I.ramificationIndex : ℕ) :=
    mean_le_of_addVal_coeff he₀ h hP hmem hv.symm hw
  rw [← hidx, hn, mul_add, mul_one] at hL1
  rw [div_lt_iff₀ he] at hlt
  have h₁ : I.ramificationIndex * (r / I.ramificationIndex) + r % I.ramificationIndex = r :=
    Nat.div_add_mod r I.ramificationIndex
  have h₂ : I.ramificationIndex * v + r % I.ramificationIndex ≤ r + I.ramificationIndex := by
    have h₃ : I.ramificationIndex * v ≤ I.ramificationIndex * (r / I.ramificationIndex + 1) :=
      Nat.mul_le_mul_left I.ramificationIndex hv'
    rw [mul_add, mul_one] at h₃
    omega
  have h₃ : ((I.ramificationIndex * v + r % I.ramificationIndex : ℕ) : ℚ) ≤
      ((r + I.ramificationIndex : ℕ) : ℚ) := by
    exact_mod_cast h₂
  push_cast at h₃ hL1
  nlinarith

end IsNonarchimedeanLocalField.HerbrandInvariant
