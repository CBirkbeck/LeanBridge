import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeAdmissible

/-!
# Which indices are levels, and the surjectivity of Monge's additive polynomials

Let `g` be an Eisenstein polynomial with root `π` whose ramification polygon is that of a Herbrand
invariant `I`. This file determines Monge's level of `g` at a natural number `m`, the valuation
of the additive part of the shifted polynomial `g(π + π ^ (m + 1) T)`, and proves what the reduction
algorithm of Monge (arXiv:1109.4617, Algorithms 1 and 2, p. 7) needs to know about it: the level at
`r_k ≤ m ≤ r_{k + 1}` is `e m_k + p ^ (w - k) m + e`, which is attained by the term of degree
`p ^ (w - k)`, and this is the only term when `r_k < m < r_{k + 1}` (the second statement of Monge's
Proposition 2, p. 5). Then `S_m` is surjective on the residue field. A `C`-point `P_σ` with `σ / e`
not a Swan slope is the level of such an `m` (Monge, p. 8), which Monge states without proof.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.mongeLevel_eq_of_mem_segment` (Monge's
  Proposition 1): the level at `m`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.pow_succ_dvd_coeff_mongeShift_of_ne` (Monge's
  Proposition 2): the shifted polynomial has only one monomial away from the breaks.
* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_coeff_mongeShift_eq`: the coefficient at the
  vertex.
* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_segment_of_pointType_eq_C`: the non critical
  `C`-points are levels.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mem_mongeImage_of_forall_pow_succ_dvd`: the
  surjectivity of `S_m` away from the breaks.
-/

open Finset Ideal IsDiscreteValuationRing Polynomial

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} {I : HerbrandInvariant p} {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {g : R[X]} {π : S} {k m N r v σ : ℕ}

variable (r) in
lemma coeff_mongeShift_eq_mul : (mongeShift g π m).coeff r =
    (taylor π (g.map (algebraMap R S))).coeff r * (π ^ (m + 1)) ^ r := by
  have hcomp :
      mongeShift g π m = (taylor π (g.map (algebraMap R S))).comp (C (π ^ (m + 1)) * X) := by
    rw [mongeShift, taylor_apply, comp_assoc]
    simp [add_comm]
  rw [hcomp, comp_C_mul_X_coeff]

/-- **Surjectivity of `S_m` away from the breaks** (Monge, arXiv:1109.4617, p. 6): if the shifted
polynomial `g(π + π ^ (m + 1) T)` has level `N = σ + n`, and modulo `π ^ (N + 1)` only one monomial,
at `T ^ (p ^ a)`, and if `R` surjects onto the residue field of `S`, which is perfect, then Monge's
image at `σ` is the whole residue field of `R`. -/
lemma mem_mongeImage_of_forall_pow_succ_dvd (𝔪 : Ideal R) {ϖ d : R} (hd : g.coeff 0 = ϖ * d)
    (hdu : IsUnit (algebraMap R S d)) {a : ℕ} (hm : 1 ≤ m)
    (hlevel : mongeLevel g π m = (σ + g.natDegree : ℕ)) {c : S} (hc : IsUnit c)
    (hcoeff : (mongeShift g π m).coeff (p ^ a) = π ^ (σ + g.natDegree) * c)
    (hne : ∀ r, r ≠ p ^ a → π ^ (σ + g.natDegree + 1) ∣ (mongeShift g π m).coeff r)
    (hsurj : ∀ z : S, ∃ θ : R, π ∣ algebraMap R S θ - z)
    (hperf : ∀ z : S, ∃ w : S, π ∣ w ^ p ^ a - z) (x : R ⧸ 𝔪) : x ∈ mongeImage ϖ 𝔪 g π σ := by
  rcases Quotient.mk_surjective x with ⟨r, rfl⟩
  have hU : IsUnit (algebraMap R S ((-d) ^ (σ / g.natDegree + 1)) * c) := by
    rw [map_pow, map_neg]
    exact (hdu.neg.pow _).mul hc
  rcases hU with ⟨U, hU⟩
  have hz : algebraMap R S ((-d) ^ (σ / g.natDegree + 1)) * c * (↑U⁻¹ * algebraMap R S r) =
      algebraMap R S r := by
    rw [← hU, ← mul_assoc, Units.mul_inv, one_mul]
  rcases hperf (↑U⁻¹ * algebraMap R S r) with ⟨w, hw⟩
  rcases hsurj w with ⟨θ, hθ⟩
  have hC : C (π ^ (σ + g.natDegree + 1)) ∣ mongeShift g π m -
      C (π ^ (σ + g.natDegree) * c) * X ^ p ^ a := by
    refine (C_dvd_iff_dvd_coeff _ _).mpr fun r ↦ ?_
    rw [coeff_sub, coeff_C_mul_X_pow]
    split_ifs with hr
    · rw [hr, hcoeff, sub_self]
      exact dvd_zero _
    · rw [sub_zero]
      exact hne r hr
  rcases hC with ⟨Q, hQ⟩
  have heval : (mongeShift g π m).eval (algebraMap R S θ) = π ^ (σ + g.natDegree) *
      (c * algebraMap R S θ ^ p ^ a + π * Q.eval (algebraMap R S θ)) := by
    rw [sub_eq_iff_eq_add.mp hQ]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    ring1
  refine ⟨m, hm, hlevel, d, r, θ, _, hd, rfl, heval, mem_span_singleton.mpr ?_⟩
  have heq : algebraMap R S r - algebraMap R S ((-d) ^ (σ / g.natDegree + 1)) *
      (c * algebraMap R S θ ^ p ^ a + π * Q.eval (algebraMap R S θ)) =
      algebraMap R S ((-d) ^ (σ / g.natDegree + 1)) * c *
        (-(w ^ p ^ a - ↑U⁻¹ * algebraMap R S r) -
          (algebraMap R S θ ^ p ^ a - w ^ p ^ a)) -
        π * (algebraMap R S ((-d) ^ (σ / g.natDegree + 1)) * Q.eval (algebraMap R S θ)) := by
    linear_combination -hz
  rw [heq]
  refine dvd_sub (Dvd.dvd.mul_left (dvd_sub (dvd_neg.mpr hw) ?_) _) (dvd_mul_right _ _)
  exact hθ.trans (sub_dvd_pow_sub_pow _ _ _)

lemma ram_lt_ram_of_swanSlope_lt (h : I.swanSlope k < I.swanSlope (k + 1)) :
    I.ram k < I.ram (k + 1) := by
  by_contra hr
  have hr' : I.ram (k + 1) = I.ram k :=
    le_antisymm (not_lt.mp hr) (I.monotone_ram k.le_succ)
  have hs : I.swanSlope (k + 1) = I.swanSlope k := by
    rw [swanSlope, sum_range_succ, hr', sub_self, zero_div, add_zero]
    rfl
  exact h.ne hs.symm

lemma swanSlope_le_of_pointType_eq_C (hC : I.pointType σ = .C) :
    I.swanSlope (I.pointIndex (σ % I.ramificationIndex)) ≤ (σ : ℚ) / I.ramificationIndex := by
  rw [pointType] at hC
  split_ifs at hC with h₁ h₂ h₃ h₄
  exact not_lt.mp h₃

variable [IsDomain S] [IsDiscreteValuationRing S]

variable (r) in
lemma addVal_coeff_mongeShift (hπ : Irreducible π) : addVal S ((mongeShift g π m).coeff r) =
    addVal S ((taylor π (g.map (algebraMap R S))).coeff r) + ((m + 1) * r : ℕ) := by
  rw [coeff_mongeShift_eq_mul, addVal_mul, addVal_pow, addVal_pow, addVal_uniformizer hπ, nsmul_one,
    nsmul_eq_mul]
  push_cast
  ring1

variable [IsDomain R] [IsDiscreteValuationRing R] in
/-- **The coefficient at the vertex**: if the ramification polygon of `g` at `π` is that of `I` and
`r_k ≤ m ≤ r_{k + 1}` for a vertex `k`, then the coefficient of `T ^ (p ^ (w - k))` in
`g(π + π ^ (m + 1) T)` has valuation exactly the level `N` of `g` at `m`. -/
lemma exists_coeff_mongeShift_eq (h : IsMongeRoot g π p) (hP : I.IsRamificationPolygon g π)
    (hk : k ≤ I.w) (hv : I.IsVertex k) (hN : (N : ℚ) = I.polygonLine k m + I.ramificationIndex) :
    ∃ c : S, IsUnit c ∧ (mongeShift g π m).coeff (p ^ (I.w - k)) = π ^ N * c := by
  rcases hP.exists_addVal_eq hk hv with ⟨v₀, hv₀, hform⟩
  have heq : v₀ + (m + 1) * p ^ (I.w - k) = N := by
    have h₃ : ((v₀ + (m + 1) * p ^ (I.w - k) : ℕ) : ℚ) = (N : ℚ) := by
      rw [hN, polygonLine]
      push_cast
      linear_combination hform
    exact_mod_cast h₃
  have hval : addVal S ((mongeShift g π m).coeff (p ^ (I.w - k))) = N := by
    rw [addVal_coeff_mongeShift _ h.irreducible, hv₀, ← heq]
    push_cast
    rfl
  rcases (pow_dvd_iff_le_addVal h.irreducible).mpr hval.ge with ⟨c, hc⟩
  refine ⟨c, ?_, hc⟩
  refine addVal_eq_zero_iff.mp ?_
  rw [hc, addVal_mul, addVal_pow, addVal_uniformizer h.irreducible, nsmul_one] at hval
  simpa using hval

variable [Fact p.Prime]

lemma polygonLine_add_le (hP : I.IsRamificationPolygon g π) (hk : k ≤ I.w) (hr : r ≠ 0)
    (hv : addVal S ((taylor π (g.map (algebraMap R S))).coeff r) = v) (h₁ : I.ram k ≤ m)
    (h₂ : k < I.w → (m : ℚ) ≤ I.ram (k + 1)) :
    I.polygonLine k m + I.ramificationIndex ≤ v + (m + 1) * r := by
  have hLB : (I.ramificationIndex : ℚ) * (I.swanSlope k + 1) ≤ v + r + r * I.ram k :=
    hP.le_addVal hk hr hv
  rw [mul_add, I.mul_swanSlope_eq hk, polygonLine] at hLB
  rw [polygonLine]
  by_cases hR : ((p ^ (I.w - k) : ℕ) : ℚ) ≤ r
  · push_cast at hR
    nlinarith
  · have hk' : k < I.w := by
      refine lt_of_le_of_ne hk fun hkw ↦ hR ?_
      rw [hkw, Nat.sub_self, pow_zero]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have hLB' : (I.ramificationIndex : ℚ) * (I.swanSlope (k + 1) + 1) ≤ v + r + r * I.ram (k + 1) :=
      hP.le_addVal hk' hr hv
    rw [mul_add, I.mul_swanSlope_eq hk', I.polygonLine_succ_ram hk', polygonLine] at hLB'
    push_cast at hR
    nlinarith [h₂ hk']

lemma polygonLine_add_lt (hP : I.IsRamificationPolygon g π) (hk : k ≤ I.w) (hr : r ≠ 0)
    (hrR : r ≠ p ^ (I.w - k)) (hv : addVal S ((taylor π (g.map (algebraMap R S))).coeff r) = v)
    (h₁ : I.ram k < m) (h₂ : k < I.w → (m : ℚ) < I.ram (k + 1)) :
    I.polygonLine k m + I.ramificationIndex < v + (m + 1) * r := by
  have hLB : (I.ramificationIndex : ℚ) * (I.swanSlope k + 1) ≤ v + r + r * I.ram k :=
    hP.le_addVal hk hr hv
  rw [mul_add, I.mul_swanSlope_eq hk, polygonLine] at hLB
  rw [polygonLine]
  rcases lt_or_gt_of_ne hrR with hR | hR
  · have hk' : k < I.w := by
      refine lt_of_le_of_ne hk fun hkw ↦ ?_
      rw [hkw, Nat.sub_self, pow_zero] at hR
      omega
    have hLB' : (I.ramificationIndex : ℚ) * (I.swanSlope (k + 1) + 1) ≤ v + r + r * I.ram (k + 1) :=
      hP.le_addVal hk' hr hv
    rw [mul_add, I.mul_swanSlope_eq hk', I.polygonLine_succ_ram hk', polygonLine] at hLB'
    have hR' : (r : ℚ) < p ^ (I.w - k) := by
      exact_mod_cast hR
    nlinarith [h₂ hk']
  · have hR' : (p : ℚ) ^ (I.w - k) < r := by
      exact_mod_cast hR
    nlinarith

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **Monge's level at a natural number** (Monge, arXiv:1109.4617, Proposition 1, p. 4): if the
ramification polygon of `g` at `π` is that of `I` and `r_k ≤ m ≤ r_{k + 1}`, for a vertex `k`, then
Monge's level at `m` is `N = e m_k + p ^ (w - k) m + e`. -/
lemma mongeLevel_eq_of_mem_segment (h : IsMongeRoot g π p) (hP : I.IsRamificationPolygon g π)
    (hk : k ≤ I.w) (hv : I.IsVertex k) (h₁ : I.ram k ≤ m) (h₂ : k < I.w → (m : ℚ) ≤ I.ram (k + 1))
    (hN : (N : ℚ) = I.polygonLine k m + I.ramificationIndex) : mongeLevel g π m = N := by
  rcases hP.exists_addVal_eq hk hv with ⟨v₀, hv₀, hform⟩
  refine le_antisymm (iInf_le_of_le (p ^ (I.w - k)) ?_) (le_iInf fun r ↦ ?_)
  · rw [emultiplicity_eq_addVal h.irreducible, addVal_coeff_mongeShift _ h.irreducible, hv₀]
    have heq : v₀ + (m + 1) * p ^ (I.w - k) = N := by
      have h₃ : ((v₀ + (m + 1) * p ^ (I.w - k) : ℕ) : ℚ) = (N : ℚ) := by
        rw [hN, polygonLine]
        push_cast
        linear_combination hform
      exact_mod_cast h₃
    rw [← heq]
    push_cast
    exact le_rfl
  · rw [emultiplicity_eq_addVal h.irreducible]
    rcases eq_or_ne r 0 with rfl | hr
    · rw [coeff_mongeShift_zero h, addVal_zero]
      exact le_top
    rw [addVal_coeff_mongeShift _ h.irreducible]
    rcases eq_or_ne (addVal S ((taylor π (g.map (algebraMap R S))).coeff r)) ⊤ with htop | htop
    · rw [htop, top_add]
      exact le_top
    rcases ENat.ne_top_iff_exists.mp htop with ⟨v, hv'⟩
    rw [← hv']
    have hle : N ≤ v + (m + 1) * r := by
      exact_mod_cast hN.le.trans (polygonLine_add_le hP hk hr hv'.symm h₁ h₂)
    exact_mod_cast hle

/-- **Monge's Proposition 2, away from the breaks** (Monge, arXiv:1109.4617, Proposition 2, p. 5,
second statement): if the ramification polygon of `g` at `π` is that of `I` and
`r_k < m < r_{k + 1}` for a vertex `k`, then the coefficients of `g(π + π ^ (m + 1) T)` at the
`r ≠ p ^ (w - k)` are divisible by `π ^ (N + 1)`, for the level `N` of `g` at `m`. So `S_m` has only
one monomial. -/
lemma pow_succ_dvd_coeff_mongeShift_of_ne (h : IsMongeRoot g π p) (hP : I.IsRamificationPolygon g π)
    (hk : k ≤ I.w) (h₁ : I.ram k < m) (h₂ : k < I.w → (m : ℚ) < I.ram (k + 1))
    (hN : (N : ℚ) = I.polygonLine k m + I.ramificationIndex) (hrR : r ≠ p ^ (I.w - k)) :
    π ^ (N + 1) ∣ (mongeShift g π m).coeff r := by
  rw [pow_dvd_iff_le_addVal h.irreducible]
  rcases eq_or_ne r 0 with rfl | hr
  · rw [coeff_mongeShift_zero h, addVal_zero]
    exact le_top
  rw [addVal_coeff_mongeShift _ h.irreducible]
  rcases eq_or_ne (addVal S ((taylor π (g.map (algebraMap R S))).coeff r)) ⊤ with htop | htop
  · rw [htop, top_add]
    exact le_top
  rcases ENat.ne_top_iff_exists.mp htop with ⟨v, hv'⟩
  rw [← hv']
  have hlt : N + 1 ≤ v + (m + 1) * r := by
    exact_mod_cast hN.trans_lt (polygonLine_add_lt hP hk hr hrR hv'.symm h₁ h₂)
  exact_mod_cast hlt

variable (I) in
lemma pow_dvd_of_pointIndex : p ^ (I.w - I.pointIndex (σ % I.ramificationIndex)) ∣ σ := by
  have hp : p.Prime :=
    Fact.out
  have hne : (σ % I.ramificationIndex).gcd (p ^ I.w) ≠ 0 :=
    (Nat.gcd_pos_of_pos_right _ (pow_pos hp.pos _)).ne'
  have hd : p ^ padicValNat p ((σ % I.ramificationIndex).gcd (p ^ I.w)) ∣
      (σ % I.ramificationIndex).gcd (p ^ I.w) :=
    pow_padicValNat_dvd
  have hw : padicValNat p ((σ % I.ramificationIndex).gcd (p ^ I.w)) ≤ I.w :=
    (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hd.trans (Nat.gcd_dvd_right _ _))
  rw [pointIndex, Nat.sub_sub_self hw]
  have h₂ : p ^ padicValNat p ((σ % I.ramificationIndex).gcd (p ^ I.w)) ∣ I.ramificationIndex :=
    ((pow_dvd_pow p hw).mul_left I.ε)
  have h₃ : p ^ padicValNat p ((σ % I.ramificationIndex).gcd (p ^ I.w)) ∣
      I.ramificationIndex * (σ / I.ramificationIndex) + σ % I.ramificationIndex :=
    dvd_add (h₂.mul_right _) (hd.trans (Nat.gcd_dvd_left _ _))
  rwa [Nat.div_add_mod] at h₃

/-- **The `C`-points are levels** (Monge, arXiv:1109.4617, p. 8): if the ramification polygon of `g`
at `π` is that of `I`, then a `C`-point `P_σ`, `σ > 0`, with `σ / e` not a Swan slope is a level of
an integer `m ≥ 1` which is not a ramification break: `r_k < m < r_{k + 1}` and
`σ = e m_k + p ^ (w - k) m`, for a vertex `k`. This uses that the index `k₀` of `σ` gives
`p ^ (w - k₀) ∣ σ`, and `p ^ (w - k) ∣ e m_k` at the vertices. -/
lemma exists_segment_of_pointType_eq_C {e₀ : ℕ} (he₀ : addVal R (p : R) = e₀)
    (h : IsMongeRoot g π p) (hP : I.IsRamificationPolygon g π) (hσ : σ ≠ 0)
    (hC : I.pointType σ = .C)
    (hnc : ∀ j ∈ Icc 1 I.w, (σ : ℚ) / I.ramificationIndex ≠ I.swanSlope j) : ∃ k m : ℕ, k ≤ I.w ∧
      I.IsVertex k ∧ 1 ≤ m ∧ I.ram k < m ∧ (k < I.w → (m : ℚ) < I.ram (k + 1)) ∧
        (σ : ℚ) = I.polygonLine k m := by
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hσ' : (0 : ℚ) < σ := by
    exact_mod_cast Nat.pos_of_ne_zero hσ
  have hk₀ : I.pointIndex (σ % I.ramificationIndex) ≤ I.w :=
    Nat.sub_le _ _
  have hPk₀ :
      I.swanSlope (I.pointIndex (σ % I.ramificationIndex)) < (σ : ℚ) / I.ramificationIndex := by
    refine lt_of_le_of_ne (swanSlope_le_of_pointType_eq_C hC) fun heq ↦ ?_
    rcases Nat.eq_zero_or_pos (I.pointIndex (σ % I.ramificationIndex)) with h₀ | h₀
    · rw [h₀] at heq
      simp only [swanSlope] at heq
      exact (div_pos hσ' he).ne heq
    · exact hnc _ (mem_Icc.mpr ⟨h₀, hk₀⟩) heq.symm
  let P : ℕ → Prop := fun k ↦ I.swanSlope k < (σ : ℚ) / I.ramificationIndex
  have hPk : P (Nat.findGreatest P I.w) :=
    Nat.findGreatest_spec hk₀ hPk₀
  have hle₀ : I.pointIndex (σ % I.ramificationIndex) ≤ Nat.findGreatest P I.w :=
    Nat.le_findGreatest hk₀ hPk₀
  have hkw : Nat.findGreatest P I.w ≤ I.w :=
    Nat.findGreatest_le I.w
  have hnext : Nat.findGreatest P I.w < I.w →
      (σ : ℚ) / I.ramificationIndex < I.swanSlope (Nat.findGreatest P I.w + 1) := fun hlt ↦
    lt_of_le_of_ne (not_lt.mp (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hlt))
      (hnc _ (mem_Icc.mpr ⟨by omega, hlt⟩))
  generalize Nat.findGreatest P I.w = k at hPk hle₀ hkw hnext
  have hPk' : (I.ramificationIndex : ℚ) * I.swanSlope k < σ := by
    rw [mul_comm]
    exact (lt_div_iff₀ he).mp hPk
  have hv : I.IsVertex k := by
    rcases hkw.lt_or_eq with hlt | heq
    · exact .inr (ram_lt_ram_of_swanSlope_lt (hPk.trans (hnext hlt)))
    · exact .inl heq
  rcases exists_natCast_eq_mul_mean he₀ h hP hkw hv with ⟨σ', hσ₁, hdvd'⟩
  have hdvd : p ^ (I.w - k) ∣ σ :=
    (pow_dvd_pow p (by omega)).trans (pow_dvd_of_pointIndex I)
  have hline : (I.ramificationIndex : ℚ) * I.swanSlope k =
      I.ramificationIndex * I.mean k + p ^ (I.w - k) * I.ram k :=
    I.mul_swanSlope_eq hkw
  have hpow : (0 : ℚ) < p ^ (I.w - k) :=
    pow_pos natCast_prime_pos _
  have hrk : (0 : ℚ) ≤ I.ram k :=
    I.ram_nonneg k
  have hle : σ' ≤ σ := by
    have h₁ : (σ' : ℚ) ≤ σ := by
      rw [hσ₁]
      nlinarith
    exact_mod_cast h₁
  rcases Nat.dvd_sub hdvd hdvd' with ⟨m, hm⟩
  have hσeq : (σ : ℚ) = I.polygonLine k m := by
    have h₁ : σ = σ' + p ^ (I.w - k) * m := by
      omega
    rw [h₁, polygonLine]
    push_cast
    rw [hσ₁]
  have hrm : I.ram k < m := by
    rw [hline, hσeq, polygonLine] at hPk'
    exact lt_of_mul_lt_mul_left (lt_of_add_lt_add_left hPk') hpow.le
  refine ⟨k, m, hkw, hv, ?_, hrm, fun hlt ↦ ?_, hσeq⟩
  · have h₀ : (0 : ℚ) < m :=
      lt_of_le_of_lt hrk hrm
    exact Nat.one_le_iff_ne_zero.mpr fun hm₀ ↦ by simp [hm₀] at h₀
  · have h₁ : (σ : ℚ) / I.ramificationIndex < I.swanSlope (k + 1) :=
      hnext hlt
    rw [div_lt_iff₀ he, mul_comm, I.mul_swanSlope_eq hlt, I.polygonLine_succ_ram hlt, hσeq,
      polygonLine, polygonLine] at h₁
    exact lt_of_mul_lt_mul_left (lt_of_add_lt_add_left h₁) hpow.le

end IsNonarchimedeanLocalField.HerbrandInvariant
