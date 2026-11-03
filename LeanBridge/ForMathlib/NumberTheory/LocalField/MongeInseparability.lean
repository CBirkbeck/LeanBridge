import LeanBridge.ForMathlib.NumberTheory.LocalField.IndexOfInseparability
import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeRepresentationProof

/-!
# The `A`-points of the generic polynomial and the indices of inseparability

The knowl LMFDB `lf.family_polynomial` says that the elements of the set `𝒜` of a Herbrand invariant
`I` correspond to certain indices of inseparability (LMFDB `lf.indices_of_inseparability`). This
file proves it: for a finite extension `L / K` of `p`-adic fields with the rams of `I`, and a vertex
`k` of the ramification polygon, the index of inseparability `i_{w - k}` of Heiermann is `e m_k`. So
an element `σ` of `𝒜`, of index `k`, is `i_{w - k}`.

The minimum defining `i_{w - k}` is bounded from below by the position of the digits of a minimal
polynomial of a uniformiser above the bottom edges of the bands, and by Monge's Lemma 2. It is
attained at the term of the polynomial at the vertex, or at its constant term when this term is the
leading one.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.mul_mean_add_le`: the lower bound for the index of
  inseparability at `k`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_add_le_mul_mean`: the minimum defining the
  index of inseparability at a vertex is attained.
* `IsNonarchimedeanLocalField.HerbrandInvariant.inseparabilityIndex_eq_of_isVertex`: the indices of
  inseparability at the vertices.
* `IsNonarchimedeanLocalField.HerbrandInvariant.inseparabilityIndex_eq_of_mem_aIndices`: the
  elements of `𝒜` are indices of inseparability.
* `IsNonarchimedeanLocalField.HerbrandInvariant.inseparabilityIndex_eq_of_isInvariantOf` (LMFDB
  `lf.family_polynomial`): the same for the extensions in the family `I / K`.
-/

open Algebra Finset IntermediateField IsDiscreteValuationRing IsLocalRing Polynomial TauCeti
  ValuativeRel LocalFieldsRamification

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

lemma addValuation_coe {y : 𝒪[K]} {a : ℕ} (h : addVal 𝒪[K] y = a) :
    addValuation K (y : K) = ((a : ℤ) : WithTop ℤ) := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  rcases (HerbrandInvariant.pow_dvd_iff_le_addVal hϖ).mpr h.ge with ⟨u, rfl⟩
  rw [addVal_mul, addVal_pow, addVal_uniformizer hϖ, nsmul_one] at h
  have hu : IsUnit u :=
    addVal_eq_zero_iff.mp (by simpa using h)
  have hϖ₀ : (ϖ : K) ≠ 0 :=
    fun h₀ ↦ hϖ.ne_zero (Subtype.ext h₀)
  have hu₀ : (u : K) ≠ 0 :=
    fun h₀ ↦ hu.ne_zero (Subtype.ext h₀)
  have hy : ((ϖ ^ a * u : 𝒪[K]) : K) ≠ 0 := by
    push_cast
    exact mul_ne_zero (pow_ne_zero a hϖ₀) hu₀
  have hprod :
      Units.mk0 ((ϖ ^ a * u : 𝒪[K]) : K) hy = Units.mk0 (ϖ : K) hϖ₀ ^ a * Units.mk0 (u : K) hu₀ :=
    Units.ext (by push_cast; rfl)
  have hval : normalizedValuation K (Units.mk0 (u : K) hu₀) = 1 := by
    have h₁ : normalizedValuationWithZero K (u : K) = 1 :=
      isUnit_iff_normalizedValuationWithZero_eq_one.mp hu
    rw [← Units.val_mk0 hu₀, normalizedValuationWithZero_coe] at h₁
    exact_mod_cast h₁
  rw [addValuation, dite_eq_right hy, hprod, map_mul, map_pow, normalizedValuation_irreducible hϖ,
    hval, mul_one]
  simp

namespace HerbrandInvariant

variable {p : ℕ} {I : HerbrandInvariant p} {k σ : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  {g : R[X]} {π : S} {e₀ i j' a : ℕ}

variable [Fact p.Prime] in
lemma mean_mono : Monotone I.mean :=
  monotone_nat_of_le_succ fun k ↦ by
    rw [I.mean_succ]
    exact le_add_of_nonneg_right (I.smallRam_nonneg _)

variable [Fact p.Prime] in
lemma mul_mean_add_le_of_lt_natDegree (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hi : i < g.natDegree) (ha : addVal R (g.coeff i) = a) :
    (I.ramificationIndex : ℚ) *
      (I.mean (I.w - if i = 0 then I.w else min (padicValNat p i) I.w) + 1) ≤
        (g.natDegree * a + i : ℕ) := by
  by_cases hc : i ≠ 0 ∧ padicValNat p i ≤ I.w
  · rw [ite_eq_right hc.1, min_eq_left hc.2]
    exact mean_le_of_addVal_coeff he₀ h hP (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hc.1, hi.le⟩) ha hc.2
  · have hb : (if i = 0 then I.w else min (padicValNat p i) I.w) = I.w := by
      split_ifs with hi₀
      · rfl
      · exact min_eq_right (not_le.mp fun hv ↦ hc ⟨hi₀, hv⟩).le
    have hle : (g.natDegree : ℕ∞) ≤ g.natDegree • addVal R (g.coeff i) + i :=
      natDegree_le_nsmul_addVal_add h hi
    rw [ha, nsmul_eq_mul] at hle
    have hle' : g.natDegree ≤ g.natDegree * a + i := by
      exact_mod_cast hle
    rw [hb, Nat.sub_self, ← hP.natDegree_eq, I.mean_zero, zero_add, mul_one]
    exact_mod_cast hle'

variable [Fact p.Prime] in
/-- **The lower bound for the index of inseparability at `k`**: if the ramification polygon of `g`
at `π` is that of `I`, `k ≤ w`, `0 ≤ i < e` and `v̄_p(i) ≤ j'`, then
`e (m_k + 1) ≤ e v_R(g_i) + i + (j' - (w - k)) e e₀`, for `e₀ = v_R(p)`. -/
lemma mul_mean_add_le (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k ≤ I.w) (hi : i < g.natDegree)
    (hb : (if i = 0 then I.w else min (padicValNat p i) I.w) ≤ j') (ha : addVal R (g.coeff i) = a) :
    (I.ramificationIndex : ℚ) * (I.mean k + 1) ≤ (g.natDegree * a + i : ℕ) +
      ((j' - (I.w - k) : ℕ) : ℚ) * (I.ramificationIndex * e₀) := by
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hB : (I.ramificationIndex : ℚ) *
      (I.mean (I.w - if i = 0 then I.w else min (padicValNat p i) I.w) + 1) ≤
        (g.natDegree * a + i : ℕ) :=
    mul_mean_add_le_of_lt_natDegree he₀ h hP hi ha
  have hbw : (if i = 0 then I.w else min (padicValNat p i) I.w) ≤ I.w := by
    split_ifs
    · exact le_rfl
    · exact min_le_right _ _
  generalize (if i = 0 then I.w else min (padicValNat p i) I.w) = b at hB hb hbw
  have hm : I.mean k ≤ I.mean (I.w - b) + ((j' - (I.w - k) : ℕ) : ℚ) * e₀ := by
    have hx : (0 : ℚ) ≤ ((j' - (I.w - k) : ℕ) : ℚ) * e₀ :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rcases le_total k (I.w - b) with hkb | hkb
    · linarith [mean_mono (I := I) hkb]
    · have h₁ : I.mean (I.w - b + (k - (I.w - b))) - I.mean (I.w - b) ≤
          ((k - (I.w - b) : ℕ) : ℚ) * e₀ :=
        I.mean_add_sub_le (fun hk ↦ smallRam_le he₀ h hP hk) (by omega)
      rw [Nat.add_sub_cancel' hkb] at h₁
      have h₂ : ((k - (I.w - b) : ℕ) : ℚ) ≤ ((j' - (I.w - k) : ℕ) : ℚ) := by
        exact_mod_cast (by omega : k - (I.w - b) ≤ j' - (I.w - k))
      nlinarith [(Nat.cast_nonneg e₀ : (0 : ℚ) ≤ e₀)]
  have hmul : (I.ramificationIndex : ℚ) * I.mean k ≤ I.ramificationIndex *
      (I.mean (I.w - b) + ((j' - (I.w - k) : ℕ) : ℚ) * e₀) :=
    mul_le_mul_of_nonneg_left hm he.le
  rw [mul_add] at hB hmul
  rw [mul_add]
  nlinarith

variable [Fact p.Prime] in
/-- **The minimum defining the index of inseparability at a vertex is attained**: if the
ramification polygon of `g` at `π` is that of `I`, and `k` is a vertex, there are `w - k ≤ j' ≤ w`
and `0 ≤ i < e` with `v̄_p(i) ≤ j'` and `e v_R(g_i) + i + (j' - (w - k)) e e₀ ≤ e (m_k + 1)`, for
`e₀ = v_R(p)`: the term at the vertex, or the constant term when this term is the leading one. -/
lemma exists_add_le_mul_mean (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (h₀ : addVal R (g.coeff 0) = 1) (hk : k ≤ I.w)
    (hv : I.IsVertex k) : ∃ j' ∈ Icc (I.w - k) I.w, ∃ i < g.natDegree,
      (if i = 0 then I.w else min (padicValNat p i) I.w) ≤ j' ∧ ∃ a : ℕ,
        addVal R (g.coeff i) = a ∧ ((g.natDegree * a + i : ℕ) : ℚ) +
          ((j' - (I.w - k) : ℕ) : ℚ) * (I.ramificationIndex * e₀) ≤
            I.ramificationIndex * (I.mean k + 1) := by
  rcases exists_vertex_term he₀ h hP hk hv with ⟨i, hi, j, hj, hple, hform⟩
  have hn : g.natDegree = I.ramificationIndex :=
    hP.natDegree_eq
  rcases (mem_Icc.mp hi).2.lt_or_eq with hlt | rfl
  · have hi₀ : i ≠ 0 :=
      (Nat.lt_of_lt_of_le one_pos (mem_Icc.mp hi).1).ne'
    refine ⟨min (padicValNat p i) I.w, mem_Icc.mpr ⟨le_min hple (Nat.sub_le _ _),
      min_le_right _ _⟩, i, hlt, (ite_eq_right hi₀).le, j, hj, ?_⟩
    have h₁ : ((min (padicValNat p i) I.w - (I.w - k) : ℕ) : ℚ) ≤
        ((padicValNat p i - (I.w - k) : ℕ) : ℚ) := by
      exact_mod_cast
        (by omega : min (padicValNat p i) I.w - (I.w - k) ≤ padicValNat p i - (I.w - k))
    have h₂ : ((min (padicValNat p i) I.w - (I.w - k) : ℕ) : ℚ) * (I.ramificationIndex * e₀) ≤
        ((padicValNat p i - (I.w - k) : ℕ) : ℚ) * (I.ramificationIndex * e₀) :=
      mul_le_mul_of_nonneg_right h₁ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    rw [← hform, hn]
    push_cast at h₂ ⊢
    linarith
  · have hj₀ : j = 0 := by
      simpa [h.monic.coeff_natDegree, eq_comm] using hj
    subst hj₀
    refine ⟨I.w, mem_Icc.mpr ⟨Nat.sub_le _ _, le_rfl⟩, 0, h.natDegree_pos, (ite_eq_left rfl).le, 1,
      h₀, ?_⟩
    rw [← hform, hn, padicValNat_ramificationIndex]
    push_cast
    linarith

variable {F L M : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Algebra K F] [ValuativeExtension K F] [Module.Finite K F]
  [IsGalois K F] [IsUnramified K F] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsGalois K M] [Algebra F M] [ValuativeExtension F M] [Module.Finite F M] [IsScalarTower K F M]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Algebra F L] [ValuativeExtension F L]
  [IsScalarTower K F L] [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [IsScalarTower K L M] [IsScalarTower F L M]

variable (K M) in
lemma inf_inf_eq_of_isVertex [CharZero K] (hI : I.HasSameRams (herbrandInvariantOfTower K M L))
    (htr : IsTotallyRamified F L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (hk : k ≤ I.w) (hv : I.IsVertex k)
    (hσ : (σ : ℚ) = I.ramificationIndex * I.mean k) :
    letI n : ℕ := Module.finrank F L
    letI ν : ℕ := padicValNat p n
    (Icc (I.w - k) ν).inf (fun j' ↦ ((range n).filter fun h ↦
      (if h = 0 then ν else min (padicValNat p h) ν) ≤ j').inf (fun h ↦
        n • addValuation F ((minpoly F (ϖ : L)).coeff h) + ((h - n : ℤ) : WithTop ℤ)) +
      (j' - (I.w - k)) • addValuation L (p : L)) = ((σ : ℤ) : WithTop ℤ) := by
  rcases hI.prime_eq with rfl
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hcL : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  have hst : IsMongeStage (minpoly 𝒪[F] ϖ) ϖ :=
    isMongeStage_minpoly htr hϖ
  have h : IsMongeRoot (minpoly 𝒪[F] ϖ) ϖ (ringChar 𝓀[K]) :=
    hst.isMongeRoot
  have hP : I.IsRamificationPolygon (minpoly 𝒪[F] ϖ) ϖ :=
    IsMongeStage.isRamificationPolygon_of_hasSameRams K M hI hst
  rcases exists_addVal_natCast_eq K F (Fact.out : (ringChar 𝓀[K]).Prime).ne_zero with ⟨e₀, he₀⟩
  have hdeg : (minpoly 𝒪[F] ϖ).natDegree = I.ramificationIndex :=
    hP.natDegree_eq
  have hn : Module.finrank F L = I.ramificationIndex := by
    rw [← hdeg, hst.natDegree_eq, (isTotallyRamified_iff_ramificationIndex_eq_finrank F L).mp htr]
  have h₀ : addVal 𝒪[F] ((minpoly 𝒪[F] ϖ).coeff 0) = 1 := by
    have h₁ : Irreducible ((minpoly 𝒪[F] ϖ).coeff 0) :=
      hst.isEisensteinAt.irreducible_coeff_zero h.natDegree_pos
    exact addVal_uniformizer h₁
  have hint : IsIntegral 𝒪[F] ϖ :=
    IsIntegral.of_finite 𝒪[F] ϖ
  have hmin : minpoly F (ϖ : L) = (minpoly 𝒪[F] ϖ).map (algebraMap 𝒪[F] F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F L hint
  have hL : addValuation L ((ringChar 𝓀[K] : ℕ) : L) =
      (((I.ramificationIndex * e₀ : ℕ) : ℤ) : WithTop ℤ) := by
    have h₁ : addVal 𝒪[L] ((ringChar 𝓀[K] : ℕ) : 𝒪[L]) = ((I.ramificationIndex * e₀ : ℕ) : ℕ∞) := by
      rw [← map_natCast (algebraMap 𝒪[F] 𝒪[L]), h.addVal_algebraMap, he₀, hdeg, nsmul_eq_mul]
      push_cast
      rfl
    have h₂ : addValuation L (((ringChar 𝓀[K] : ℕ) : 𝒪[L]) : L) =
        (((I.ramificationIndex * e₀ : ℕ) : ℤ) : WithTop ℤ) :=
      addValuation_coe h₁
    rwa [Subring.coe_natCast] at h₂
  have hmul : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  have hσ' : (σ : ℚ) + I.ramificationIndex = I.ramificationIndex * (I.mean k + 1) := by
    rw [hσ]
    ring1
  rw [hn, padicValNat_ramificationIndex, hmin]
  simp only [hL, coeff_map]
  refine le_antisymm ?_ (Finset.le_inf fun j' hj' ↦ ?_)
  · rcases exists_add_le_mul_mean he₀ h hP h₀ hk hv with ⟨j', hj', i, hi, hb, a, ha, hle⟩
    rw [hdeg] at hi hle
    refine (Finset.inf_le hj').trans ((add_le_add_left (Finset.inf_le (mem_filter.mpr
      ⟨mem_range.mpr hi, hb⟩)) _).trans ?_)
    have hc :
        addValuation F (algebraMap 𝒪[F] F ((minpoly 𝒪[F] ϖ).coeff i)) = ((a : ℤ) : WithTop ℤ) :=
      addValuation_coe ha
    rw [hc, ← WithTop.coe_nsmul, ← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_add,
      WithTop.coe_le_coe, nsmul_eq_mul, nsmul_eq_mul]
    rw [← hσ'] at hle
    have hle' : (I.ramificationIndex * a + i) + (j' - (I.w - k)) * (I.ramificationIndex * e₀) ≤
        σ + I.ramificationIndex := by
      exact_mod_cast hle
    zify at hle'
    push_cast at hle' ⊢
    linarith
  · have hsplit : ((σ : ℤ) : WithTop ℤ) =
        (((σ : ℤ) - (j' - (I.w - k)) • ((I.ramificationIndex * e₀ : ℕ) : ℤ) : ℤ) : WithTop ℤ) +
          (j' - (I.w - k)) • (((I.ramificationIndex * e₀ : ℕ) : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_nsmul, ← WithTop.coe_add, sub_add_cancel]
    rw [hsplit]
    refine add_le_add_left (Finset.le_inf fun i hi ↦ ?_) _
    rcases mem_filter.mp hi with ⟨hi₁, hb⟩
    rcases eq_or_ne (addVal 𝒪[F] ((minpoly 𝒪[F] ϖ).coeff i)) ⊤ with htop | htop
    · have hzero : (minpoly 𝒪[F] ϖ).coeff i = 0 :=
        addVal_eq_top_iff.mp htop
      have htop' : I.ramificationIndex • (⊤ : WithTop ℤ) = ⊤ := by
        rcases Nat.exists_eq_succ_of_ne_zero (hdeg ▸ h.natDegree_pos.ne') with ⟨m, hm⟩
        rw [hm, succ_nsmul, WithTop.add_top]
      rw [hzero, map_zero, addValuation, dite_eq_left rfl, htop', top_add]
      exact le_top
    · rcases ENat.ne_top_iff_exists.mp htop with ⟨a, ha⟩
      have hc :
          addValuation F (algebraMap 𝒪[F] F ((minpoly 𝒪[F] ϖ).coeff i)) = ((a : ℤ) : WithTop ℤ) :=
        addValuation_coe ha.symm
      have hle : (I.ramificationIndex : ℚ) * (I.mean k + 1) ≤
          ((minpoly 𝒪[F] ϖ).natDegree * a + i : ℕ) +
            ((j' - (I.w - k) : ℕ) : ℚ) * (I.ramificationIndex * e₀) :=
        mul_mean_add_le he₀ h hP hk (hdeg ▸ mem_range.mp hi₁) hb ha.symm
      rw [← hσ', hdeg] at hle
      have hle' : σ + I.ramificationIndex ≤
          (I.ramificationIndex * a + i) + (j' - (I.w - k)) * (I.ramificationIndex * e₀) := by
        exact_mod_cast hle
      zify at hle'
      rw [hc, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
        nsmul_eq_mul]
      push_cast at hle' ⊢
      linarith

variable [FiniteDimensional K L]

variable (M) in
/-- **The indices of inseparability at the vertices** (LMFDB `lf.indices_of_inseparability`): for a
finite extension `L / K` of `p`-adic fields with the rams of a Herbrand invariant `I`, inside a
finite Galois extension `M / K`, and a vertex `k` of the ramification polygon, the index of
inseparability `i_{w - k}` of `L / K` is `e m_k`. -/
lemma inseparabilityIndex_eq_of_isVertex [CharZero K]
    (hI : I.HasSameRams (herbrandInvariantOfTower K M L)) (hk : k ≤ I.w) (hv : I.IsVertex k)
    (hσ : (σ : ℚ) = I.ramificationIndex * I.mean k) :
    inseparabilityIndex K L (I.w - k) = ((σ : ℤ) : WithTop ℤ) := by
  rcases hI.prime_eq with rfl
  let vF : ValuativeRel (unramifiedExtension K L (inertiaDegree K L)) :=
    finiteIntermediateFieldValuativeRel K L _
  let tF : TopologicalSpace (unramifiedExtension K L (inertiaDegree K L)) :=
    finiteIntermediateFieldTopology K L _
  have hF : IsNonarchimedeanLocalField (unramifiedExtension K L (inertiaDegree K L)) :=
    finiteIntermediateField_isNonarchimedeanLocalField K L _
  have hKF : ValuativeExtension K (unramifiedExtension K L (inertiaDegree K L)) :=
    finiteIntermediateField_valuativeExtension K L _
  have hur : IsUnramified K (unramifiedExtension K L (inertiaDegree K L)) :=
    isUnramified_unramifiedExtension_inertiaDegree K L
  have htr : IsTotallyRamified (unramifiedExtension K L (inertiaDegree K L)) L :=
    isTotallyRamified_unramifiedExtension_inertiaDegree K L
  have hFL : ValuativeExtension (unramifiedExtension K L (inertiaDegree K L)) L :=
    IntermediateField.valuativeExtension _
  have hFM : ValuativeExtension (unramifiedExtension K L (inertiaDegree K L)) M :=
    .trans _ L M
  have fFM : Module.Finite (unramifiedExtension K L (inertiaDegree K L)) M :=
    .of_restrictScalars_finite K _ M
  rcases (isUniformizer_iff_exists_irreducible L _).mp
    (exists_isUniformizer (K := L)).choose_spec with ⟨ϖ, hϖ, hϖπ⟩
  unfold inseparabilityIndex inseparabilityIndexOf
  rw [← hϖπ]
  exact inf_inf_eq_of_isVertex K M hI htr hϖ hk hv hσ

variable (M) in
/-- **The elements of `𝒜` are indices of inseparability** (LMFDB `lf.family_polynomial`): for a
finite extension `L / K` of `p`-adic fields with the rams of a Herbrand invariant `I`, inside a
finite Galois extension `M / K`, an element `σ` of the set `𝒜` of `I`, of index `k`, is the index of
inseparability `i_{w - k}` of `L / K`. -/
lemma inseparabilityIndex_eq_of_mem_aIndices [CharZero K]
    (hI : I.HasSameRams (herbrandInvariantOfTower K M L)) (hσ : σ ∈ I.aIndices) :
    inseparabilityIndex K L (I.w - I.pointIndex (σ % I.ramificationIndex)) =
      ((σ : ℤ) : WithTop ℤ) := by
  rcases hI.prime_eq with rfl
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hT : I.pointType σ = .A :=
    (mem_filter.mp hσ).2
  have hm : (σ : ℚ) / I.ramificationIndex = I.mean (I.pointIndex (σ % I.ramificationIndex)) :=
    div_eq_mean_of_pointType_eq_A hT
  have hk : I.pointIndex (σ % I.ramificationIndex) ≤ I.w :=
    Nat.sub_le _ _
  refine inseparabilityIndex_eq_of_isVertex M hI hk
    ((isFinal_of_pointType_eq_A hT).imp id ram_lt_ram_of_swanSlope_lt) ?_
  rw [← hm, mul_div_cancel₀ _ I.natCast_ramificationIndex_pos.ne']

/-- **The elements of `𝒜` are indices of inseparability, in the family** (LMFDB
`lf.family_polynomial`): if `E` is an extension in the family `I / K`, for a Herbrand invariant `I`
at the residue characteristic of `K`, then an element `σ` of the set `𝒜` of `I`, of index `k`, is
the index of inseparability `i_{w - k}` of `E / K`. -/
lemma inseparabilityIndex_eq_of_isInvariantOf [CharZero K] (hp : ringChar 𝓀[K] = p)
    {E : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E]
    (hI : I.IsInvariantOf K E) (hσ : σ ∈ I.aIndices) :
    letI : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
    letI : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
    haveI : IsNonarchimedeanLocalField E :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ E
    haveI : ValuativeExtension K E :=
      finiteIntermediateField_valuativeExtension K _ E
    inseparabilityIndex K E (I.w - I.pointIndex (σ % I.ramificationIndex)) =
      ((σ : ℤ) : WithTop ℤ) := by
  subst hp
  let vE : ValuativeRel E :=
    finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E :=
    finiteIntermediateFieldTopology K _ E
  have hE : IsNonarchimedeanLocalField E :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E :=
    finiteIntermediateField_valuativeExtension K _ E
  let vM : ValuativeRel (galoisClosure K E) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (galoisClosure K E) :=
    finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hEM : E ≤ galoisClosure K E :=
    galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
  let aEM : Algebra E (galoisClosure K E) :=
    (inclusion hEM).toAlgebra
  have sEM : IsScalarTower K E (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have vEM : ValuativeExtension E (galoisClosure K E) :=
    (inclusion hEM).valuativeExtension
  have fEM : Module.Finite E (galoisClosure K E) :=
    .of_restrictScalars_finite K E _
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hs : I.HasSameRams (herbrandInvariantOfTower K (galoisClosure K E) E) := by
    rw [← visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
    exact hasSameRams_of_isInvariantOf hI (isInvariantOf_visibleHerbrandInvariant E)
  exact inseparabilityIndex_eq_of_mem_aIndices (galoisClosure K E) hs hσ

end HerbrandInvariant

end IsNonarchimedeanLocalField
