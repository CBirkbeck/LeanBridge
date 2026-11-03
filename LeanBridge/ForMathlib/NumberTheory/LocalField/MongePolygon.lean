import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolygon

/-!
# The ramification polygon of an Eisenstein polynomial and the rams

Let `g` be a monic polynomial of degree `e = ε p ^ w` over a discrete valuation ring `R`, `π` a root
of `g` in a discrete valuation ring `S` over `R`, and `c_r` the coefficient of `T ^ r` in
`g(π + T)`. This file introduces what it means for the Newton polygon of the ramification
polynomial of Monge (arXiv:1109.4617, Int. J. Number Theory 10 (2014), p. 3) to be the polygon given
by the rams of a Herbrand invariant `I`
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon`): the points
`(r, v_S(c_r) + r - e)` lie above the lines through `(p ^ (w - k), e m_k)` of slope `-r_k`,
and the points `(p ^ (w - k), e m_k)` belong to the polygon when `p ^ (w - k)` is the abscissa of a
vertex. This is proved for an Eisenstein polynomial with a root generating an extension `L / K` and
for the Herbrand invariant of `L / K`, which need not be normal, computed in a finite Galois
extension `M / K` containing `L`.

The lower bound is Monge's Proposition 1, already proved in
`LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolygon`. The vertices need more: over
`𝒪[M]`, the polynomial `∏_i (d_i + ϖ ^ ρ X)` is `ϖ ^ (∑_i min(v(d_i), ρ))` times a polynomial whose
reduction has degree exactly the number of `i` with `v(d_i) ≥ ρ`. So the coefficient of `f(y + T)`
at this number has the valuation that the Newton polygon predicts, and this number is
`n_t = [G_t : G_t ∩ H]` for `ρ = ∑_{k ≤ t} #H_k`, as the values `v_M(σ y - y)` are of this form.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.IsVertex`: the indices `k` such that `p ^ (w - k)`
  is the abscissa of a vertex of the polygon of `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon`: the ramification polygon of
  `g` at `π` is the polygon of `I`.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.addVal_coeff_prod_C_add_C_mul_X`: the top
  coefficient of a product of linear polynomials.
* `IsNonarchimedeanLocalField.HerbrandInvariant.sum_card_mul_relIndex_add_addVal_coeff_taylor`: the
  vertices of the ramification polygon, in terms of the ramification groups.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isRamificationPolygon_herbrandInvariantOfTower`
  (Monge's Proposition 1 and Lemma 1): the ramification polygon of an extension is the polygon of
  its Herbrand invariant.
-/

open Algebra Finset IntermediateField IsDiscreteValuationRing Polynomial TauCeti IsLocalRing
  LocalFieldsRamification ValuativeRel

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {T ι : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] {ϖ : T}

lemma exists_C_add_C_mul_X_eq (hϖ : Irreducible ϖ) (d : T) {ρ l : ℕ}
    (hl : (l : ℕ∞) = min (addVal T d) ρ) : ∃ F : T[X], C d + C (ϖ ^ ρ) * X = C (ϖ ^ l) * F ∧
      F.map (residue T) ≠ 0 ∧
        (F.map (residue T)).natDegree = if (ρ : ℕ∞) ≤ addVal T d then 1 else 0 := by
  by_cases h : (ρ : ℕ∞) ≤ addVal T d
  · rcases (pow_dvd_iff_le_addVal hϖ).mpr h with ⟨u, hu⟩
    have hlρ : l = ρ := by
      rw [min_eq_right h] at hl
      exact_mod_cast hl
    subst hlρ
    refine ⟨C u + X, ?_, ?_, ?_⟩
    · rw [hu, C_mul]
      ring1
    · rw [Polynomial.map_add, map_C, map_X, add_comm]
      exact X_add_C_ne_zero _
    · rw [Polynomial.map_add, map_C, map_X, add_comm, natDegree_X_add_C, ite_eq_left h]
  · have hlt : addVal T d < ρ :=
      not_le.mp h
    rw [min_eq_left hlt.le] at hl
    rcases (pow_dvd_iff_le_addVal hϖ).mpr hl.le with ⟨u, hu⟩
    have hρ : l < ρ := by
      rw [← hl] at hlt
      exact_mod_cast hlt
    rcases Nat.exists_eq_add_of_lt hρ with ⟨b, rfl⟩
    have hu₀ : residue T u ≠ 0 := by
      refine (residue_ne_zero_iff_isUnit u).mpr (addVal_eq_zero_iff.mp ?_)
      have hd : addVal T d = l :=
        hl.symm
      rw [hu, addVal_mul, addVal_pow, addVal_uniformizer hϖ, nsmul_one] at hd
      simpa using hd
    have hb : residue T (ϖ ^ (b + 1)) = 0 :=
      (hϖ.residue_eq_zero_iff_dvd _).mpr (dvd_pow_self ϖ b.succ_ne_zero)
    refine ⟨C u + C (ϖ ^ (b + 1)) * X, ?_, ?_, ?_⟩
    · rw [hu, C_mul, add_assoc, pow_add, C_mul]
      ring1
    · rw [Polynomial.map_add, Polynomial.map_mul, map_C, map_C, map_X, hb, C_0, zero_mul, add_zero]
      exact C_ne_zero.mpr hu₀
    · rw [Polynomial.map_add, Polynomial.map_mul, map_C, map_C, map_X, hb, C_0, zero_mul, add_zero,
        natDegree_C, ite_eq_right h]

/-- **The top coefficient of a product of linear polynomials**: over a discrete valuation ring with
uniformiser `ϖ`, the coefficient of `X ^ R` in `∏_i (d_i + ϖ ^ ρ X)`, where `R` is the number of
`i` with `v(d_i) ≥ ρ`, has valuation `∑_i min(v(d_i), ρ)`, the Gauss level of the product. -/
lemma addVal_coeff_prod_C_add_C_mul_X (hϖ : Irreducible ϖ) (A : Finset ι) (d : ι → T) (l : ι → ℕ)
    {ρ : ℕ} (hl : ∀ i ∈ A, (l i : ℕ∞) = min (addVal T (d i)) ρ) :
    addVal T ((∏ i ∈ A, (C (d i) + C (ϖ ^ ρ) * X)).coeff #{i ∈ A | (ρ : ℕ∞) ≤ addVal T (d i)}) =
      (∑ i ∈ A, l i : ℕ) := by
  choose! F hF hF₀ hF₁ using fun i (hi : i ∈ A) ↦ exists_C_add_C_mul_X_eq hϖ (d i) (hl i hi)
  have hprod : ∏ i ∈ A, (C (d i) + C (ϖ ^ ρ) * X) = C (ϖ ^ ∑ i ∈ A, l i) * ∏ i ∈ A, F i := by
    rw [prod_congr rfl hF, prod_mul_distrib, ← prod_pow_eq_pow_sum, map_prod]
  have hdeg :
      ((∏ i ∈ A, F i).map (residue T)).natDegree = #{i ∈ A | (ρ : ℕ∞) ≤ addVal T (d i)} := by
    rw [Polynomial.map_prod, natDegree_prod _ _ hF₀, sum_congr rfl hF₁, card_filter]
  have hne : (∏ i ∈ A, F i).map (residue T) ≠ 0 := by
    rw [Polynomial.map_prod]
    exact prod_ne_zero_iff.mpr hF₀
  have hu : IsUnit ((∏ i ∈ A, F i).coeff #{i ∈ A | (ρ : ℕ∞) ≤ addVal T (d i)}) := by
    refine (residue_ne_zero_iff_isUnit _).mp ?_
    rw [← coeff_map, ← hdeg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne
  rw [hprod, coeff_C_mul, addVal_mul, addVal_pow, addVal_uniformizer hϖ, nsmul_one,
    addVal_eq_zero_iff.mpr hu, add_zero]

section Tower

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Field M] [ValuativeRel M]
  [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra L M] [ValuativeExtension L M]
  [Module.Finite L M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsScalarTower K L M] [IsGalois K M] {y : 𝒪[L]} (t : ℕ) {f : 𝒪[K][X]}

variable (L M) in
lemma natCast_sum_card_lowerRamificationGroup_eq :
    ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) =
      ∑ τ : M ≃ₐ[L] M, min (lowerIndex 𝒪[M] τ) (t : ℕ∞) := by
  rw [sum_min_lowerIndex_natCast]
  simp only [lowerRamificationGroup_def]
  push_cast
  rfl

lemma le_addVal_or_addVal_le (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) (σ : M ≃ₐ[K] M) :
    ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) ≤
        addVal 𝒪[M] (σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y) ∨
      addVal 𝒪[M] (σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y) ≤
        ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) := by
  rcases exists_forall_lowerIndex_mul_restrictScalars_le (L := L) σ with ⟨τ₀, hτ₀⟩
  have hsum : ∑ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) =
      ∑ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ₀.restrictScalars K * τ.restrictScalars K) := by
    refine (Fintype.sum_equiv (Equiv.mulLeft τ₀) _ _ fun τ ↦ ?_).symm
    rw [mul_assoc]
    rfl
  rw [addVal_smul_algebraMap_sub_eq_sum σ hy, hsum, natCast_sum_card_lowerRamificationGroup_eq,
    natCast_sum_card_lowerRamificationGroup_eq]
  simp_rw [lowerIndex_mul_restrictScalars_of_forall_le _ hτ₀]
  rcases le_or_gt ((t + 1 : ℕ) : ℕ∞) (lowerIndex 𝒪[M]
    (σ * τ₀.restrictScalars K)) with h | h
  · exact .inl <| sum_le_sum fun τ _ ↦ min_le_min_left _ h
  · refine .inr <| sum_le_sum fun τ _ ↦ min_le_min_left _ ?_
    rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt h) with ⟨j, hj⟩
    rw [← hj] at h ⊢
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h)

open scoped Classical in
variable [Fintype ((M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range)] in
lemma card_filter_mul_natCard_lowerRamificationGroup (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) :
    #{c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range |
      ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) ≤
        addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y)} *
      Nat.card (lowerRamificationGroup L M (t : ℤ)) =
        Nat.card (lowerRamificationGroup K M (t : ℤ)) := by
  rcases exists_natCast_eq_min (M := M) K t hy with ⟨l₀, hl₀, hs₀⟩
  rcases exists_natCast_eq_min (M := M) K (t + 1) hy with ⟨l, hl, hs⟩
  have hc (c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range) :
      l c = l₀ c + if ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) :
        ℕ∞) ≤ addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y) then
          Nat.card (lowerRamificationGroup L M (t : ℤ)) else 0 := by
    have hle : ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) ≤
        ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) := by
      exact_mod_cast sum_le_sum_of_subset (range_mono t.le_succ)
    rcases le_addVal_or_addVal_le t hy c.out with h | h
    · rw [AddValuation.map_sub_swap, ite_eq_left h]
      have h₁' : l c = ∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) := by
        have h₁ : (l c : ℕ∞) = _ :=
          (hl c).trans (by rw [AddValuation.map_sub_swap, min_eq_right h])
        exact_mod_cast h₁
      have h₀' : l₀ c = ∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) := by
        have h₀ : (l₀ c : ℕ∞) = _ :=
          (hl₀ c).trans (by rw [AddValuation.map_sub_swap, min_eq_right (hle.trans h)])
        exact_mod_cast h₀
      rw [h₁', h₀', sum_range_succ]
    · have hnot : ¬((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) :
          ℕ∞) ≤ addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y) := by
        rw [AddValuation.map_sub_swap]
        refine not_le.mpr (h.trans_lt ?_)
        rw [sum_range_succ]
        exact_mod_cast Nat.lt_add_of_pos_right Nat.card_pos
      rw [ite_eq_right hnot, add_zero]
      have h₁ : (l c : ℕ∞) = (l₀ c : ℕ∞) := by
        rw [hl c, hl₀ c, AddValuation.map_sub_swap, min_eq_left (h.trans hle), min_eq_left h]
      exact_mod_cast h₁
  have hsum : ∑ c, l c = ∑ c, l₀ c +
      #{c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range |
        ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) ≤
          addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y)} *
        Nat.card (lowerRamificationGroup L M (t : ℤ)) := by
    rw [sum_congr rfl fun c _ ↦ hc c, sum_add_distrib, sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul]
  rw [hs, hs₀, sum_range_succ] at hsum
  omega

/-- **The vertices of the ramification polygon**: in a tower `M / L / K` with `M / K` finite Galois,
`G = Gal(M / K)` and `H = Gal(M / L)`, let `y` generate `𝒪[L]` over `𝒪[K]`, `f` be a monic
polynomial of degree `[L : K]` with root `y`, and `c_r` the coefficient of `T ^ r` in `f(y + T)`.
For `t ∈ ℕ` and `n_t = [G_t : G_t ∩ H]`, the minimum of `(∑_{k ≤ t} #H_k) r + e(M / L) v_L(c_r)`,
which is `∑_{k ≤ t} #G_k`, is attained at `r = n_t`. -/
lemma sum_card_mul_relIndex_add_addVal_coeff_taylor (hy : Algebra.adjoin 𝒪[K] {y} = ⊤)
    (hf : f.Monic) (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0) :
    ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ))) *
      (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex (lowerRamificationGroup K M t) : ℕ) +
        TauCeti.ramificationIndex L M •
          addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff
            ((AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex
              (lowerRamificationGroup K M t))) =
      (∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) := by
  classical
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[M] with ⟨ϖ', hϖ'⟩
  rcases exists_natCast_eq_min (M := M) K (t + 1) hy with ⟨l, hl, hs⟩
  have hcard : #{c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range |
      ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) ≤
        addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y)} =
      (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex (lowerRamificationGroup K M t) := by
    have h₂ : (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex
        (lowerRamificationGroup K M t) * Nat.card (lowerRamificationGroup L M (t : ℤ)) =
          Nat.card (lowerRamificationGroup K M (t : ℤ)) := by
      have h : (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex
          (lowerRamificationGroup K M t) *
            Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K).range ⊓
              lowerRamificationGroup K M t) = Nat.card (lowerRamificationGroup K M (t : ℤ)) :=
        Subgroup.relIndex_mul_card _ _
      rwa [← map_restrictScalarsHom_lowerRamificationGroup K M L,
        Subgroup.card_map_of_injective (AlgEquiv.restrictScalars_injective K)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
      ((card_filter_mul_natCard_lowerRamificationGroup t hy).trans h₂.symm)
  have hprod : ∏ c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range,
      (C (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y) +
        C (ϖ' ^ ∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ))) * X) =
      (taylor (algebraMap 𝒪[L] 𝒪[M] y) (f.map (algebraMap 𝒪[K] 𝒪[M]))).comp
        (C (ϖ' ^ ∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ))) * X) := by
    rw [taylor_apply, comp_assoc, map_eq_prod_quotient hy hf hdeg hroot, Polynomial.prod_comp]
    refine prod_congr rfl fun c _ ↦ ?_
    simp only [sub_comp, X_comp, C_comp, add_comp, C_sub]
    ring1
  have hmap : taylor (algebraMap 𝒪[L] 𝒪[M] y) (f.map (algebraMap 𝒪[K] 𝒪[M])) =
      (taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).map (algebraMap 𝒪[L] 𝒪[M]) := by
    rw [map_taylor, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  rw [← hs, ← addVal_coeff_prod_C_add_C_mul_X hϖ' univ _ l fun c _ ↦ hl c, hcard, hprod,
    comp_C_mul_X_coeff, hmap, coeff_map, addVal_mul, TauCeti.addVal_algebraMap, addVal_pow,
    addVal_pow, addVal_uniformizer hϖ', nsmul_one, add_comm]
  push_cast
  rw [mul_comm]
  simp

end Tower

variable {p : ℕ} (I : HerbrandInvariant p) {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Algebra R S]

/-- The index `k` is a **vertex** of a Herbrand invariant if `k = w` or `r_k < r_{k + 1}`, so that
`p ^ (w - k)` is the abscissa of a vertex of the ramification polygon. For `1 ≤ k ≤ w` this means
that `k` is final in its segment (`IsFinal`), and `0` is a vertex. -/
def IsVertex (k : ℕ) : Prop :=
  k = I.w ∨ I.ram k < I.ram (k + 1)

/-- The **ramification polygon** of a polynomial `g` over a discrete valuation ring `R` at a root
`π` in a discrete valuation ring `S` over `R` is the polygon of the Herbrand invariant `I`, for the
coefficients `c_r` of `T ^ r` in `g(π + T)`: `g` has degree `e = ε p ^ w`, for all `0 ≤ k ≤ w` and
`r ≥ 1`, `e (s_k + 1) ≤ v_S(c_r) + r + r r_k`, and at the vertices `k`,
`v_S(c_{p ^ (w - k)}) + p ^ (w - k) = e (m_k + 1)`. Dividing the polynomial `g(π + π T)` by
`π ^ e`, the ramification polynomial `Φ` of Monge (arXiv:1109.4617, p. 3), these say that the points
of the Newton polygon of `Φ` lie above the lines of slope `-r_k` through `(p ^ (w - k), e m_k)`, and
the points `(p ^ (w - k), e m_k)` at the vertices belong to it. -/
structure IsRamificationPolygon (g : R[X]) (π : S) : Prop where
  natDegree_eq : g.natDegree = I.ramificationIndex
  le_addVal {k r v : ℕ} (hk : k ≤ I.w) (hr : r ≠ 0)
    (hv : addVal S ((taylor π (g.map (algebraMap R S))).coeff r) = v) :
    (I.ramificationIndex : ℚ) * (I.swanSlope k + 1) ≤ v + r + r * I.ram k
  exists_addVal_eq {k : ℕ} (hk : k ≤ I.w) (hfin : I.IsVertex k) :
    ∃ v : ℕ, addVal S ((taylor π (g.map (algebraMap R S))).coeff (p ^ (I.w - k))) = v ∧
      (v : ℚ) + p ^ (I.w - k) = I.ramificationIndex * (I.mean k + 1)

variable (K M L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
  [ValuativeExtension K L] [Algebra L M] [IsScalarTower K L M]

lemma ramsOfSubgroup_countP_le_ram {k : ℕ} (hk : k ≤ (herbrandInvariantOfTower K M L).w)
    (hfin : (herbrandInvariantOfTower K M L).IsVertex k) :
    (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).countP
      (· ≤ (herbrandInvariantOfTower K M L).ram k) = k := by
  have hw : (herbrandInvariantOfTower K M L).w =
      Multiset.card (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range) :=
    rfl
  have h₀ : 0 ≤ (herbrandInvariantOfTower K M L).ram k :=
    (herbrandInvariantOfTower K M L).ram_zero ▸
      (herbrandInvariantOfTower K M L).monotone_ram k.zero_le
  have h₁ : (herbrandInvariantOfTower K M L).ram
      ((ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).countP
        (· ≤ (herbrandInvariantOfTower K M L).ram k)) ≤ (herbrandInvariantOfTower K M L).ram k :=
    HerbrandInvariant.ram_countP_le _ _ _ _ _ _ _ _ h₀
  have hle : (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).countP
      (· ≤ (herbrandInvariantOfTower K M L).ram k) ≤
        Multiset.card (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range) :=
    Multiset.countP_le_card _ _
  generalize hc : (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).countP
    (· ≤ (herbrandInvariantOfTower K M L).ram k) = c at h₁ hle
  rcases lt_trichotomy c k with h | h | h
  · have h₂ : (herbrandInvariantOfTower K M L).ram k <
        (herbrandInvariantOfTower K M L).ram (c + 1) := by
      rw [← hc]
      exact HerbrandInvariant.lt_ram_countP_le_add_one _ _ _ _ _ _ _ _ (by omega)
    exact absurd ((herbrandInvariantOfTower K M L).monotone_ram (Nat.succ_le_of_lt h)) h₂.not_ge
  · exact h
  · rcases hfin with rfl | hfin
    · omega
    · exact absurd (hfin.trans_le ((herbrandInvariantOfTower K M L).monotone_ram
        (Nat.succ_le_of_lt h))) h₁.not_gt

variable [IsGalois K M]

lemma relIndex_lowerRamificationGroup_succ (t : ℕ) :
    (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex
      (lowerRamificationGroup K M (t + 1 : ℕ)) = ringChar 𝓀[K] ^
        ((herbrandInvariantOfTower K M L).w -
          (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).countP
            (· ≤ herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range t)) := by
  rw [relIndex_lowerRamificationGroup_eq_pow_sum K M _ (by omega)]
  congr 1
  have hs : (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).countP
      (· ≤ herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range t) +
      ∑ i ∈ range (largestLowerJump K M).toNat, (if t + 1 ≤ i + 1 then padicValNat (ringChar 𝓀[K])
        ((AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex
            (lowerRamificationGroup K M (i + 1 : ℕ)) /
          (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex
            (lowerRamificationGroup K M (i + 2 : ℕ))) else 0) =
        Multiset.card (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range) := by
    rw [countP_le_herbrandOfSubgroup, ← sum_add_distrib, ramsOfSubgroup, Multiset.card_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Multiset.card_replicate]
    push_cast
    split_ifs <;> omega
  have hw : (herbrandInvariantOfTower K M L).w =
      Multiset.card (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range) :=
    rfl
  omega

variable [ValuativeExtension L M] [Module.Finite L M]

lemma exists_ram_eq_herbrandOfSubgroup_of_le {k : ℕ} (hk : k ≤ (herbrandInvariantOfTower K M L).w) :
    ∃ t, (herbrandInvariantOfTower K M L).ram k =
      herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range t ∧
      ((herbrandInvariantOfTower K M L).swanSlope k : ℝ) =
        herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk₀
  · refine ⟨0, by rw [herbrandOfSubgroup_zero, HerbrandInvariant.ram_zero], ?_⟩
    rw [herbrand_of_coe_le_zero K M (by simp)]
    simp [swanSlope]
  · exact exists_ram_eq_herbrandOfSubgroup hk₀ hk

variable {K M L} {y : 𝒪[L]} {f : 𝒪[K][X]}

variable (M) in
lemma rat_le_of_addVal_coeff_taylor (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) (hf : f.Monic)
    (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0) {k r v : ℕ}
    (hk : k ≤ (herbrandInvariantOfTower K M L).w)
    (hv : addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff r) = v) :
    ((herbrandInvariantOfTower K M L).ramificationIndex : ℚ) *
      ((herbrandInvariantOfTower K M L).swanSlope k + 1) ≤
        v + r + r * (herbrandInvariantOfTower K M L).ram k := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  rcases exists_ram_eq_herbrandOfSubgroup_of_le K M L hk with ⟨t, hr, hs⟩
  have h₁ : ∑ j ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (j : ℤ)) ≤
      (∑ j ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (j : ℤ))) * r +
        TauCeti.ramificationIndex L M * v := by
    have h : ((∑ j ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (j : ℤ)) : ℕ) : ℕ∞) ≤
        ((∑ j ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (j : ℤ))) * r : ℕ) +
          TauCeti.ramificationIndex L M •
            addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff r) := by
      rw [← iInf_sum_card_mul_add_addVal_coeff_taylor (t + 1) hy hf hdeg hroot]
      exact iInf_le (fun r ↦ ((∑ j ∈ range (t + 1),
        Nat.card (lowerRamificationGroup L M (j : ℤ))) * r : ℕ) + TauCeti.ramificationIndex L M •
          addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff r)) r
    rw [hv, nsmul_eq_mul] at h
    exact_mod_cast h
  have he : (0 : ℝ) < TauCeti.ramificationIndex L M := by
    exact_mod_cast TauCeti.ramificationIndex_pos
  have h₂ : ((∑ j ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (j : ℤ)) : ℕ) : ℝ) ≤
      ((∑ j ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (j : ℤ)) : ℕ) : ℝ) * r +
        TauCeti.ramificationIndex L M * v := by
    exact_mod_cast h₁
  rw [natCast_sum_card_lowerRamificationGroup K M t, natCast_sum_card_lowerRamificationGroup L M t,
    ← herbrandOfSubgroup_range_restrictScalarsHom K M t L, ← hr, ← hs,
    ramificationIndex_tower (L := L) M] at h₂
  have h₃ : ((TauCeti.ramificationIndex K L : ℝ)) *
      (((herbrandInvariantOfTower K M L).swanSlope k : ℝ) + 1) ≤
        v + r + r * ((herbrandInvariantOfTower K M L).ram k : ℝ) := by
    refine le_of_mul_le_mul_left ?_ he
    push_cast at h₂
    linarith
  rw [← ε_mul_pow_w_herbrandInvariantOfTower K M L] at h₃
  refine (Rat.cast_le (K := ℝ)).mp ?_
  rw [HerbrandInvariant.ramificationIndex]
  push_cast at h₃ ⊢
  exact h₃

variable (M) in
lemma exists_addVal_coeff_taylor_eq (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) (hf : f.Monic)
    (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0) {k : ℕ}
    (hk : k ≤ (herbrandInvariantOfTower K M L).w)
    (hfin : (herbrandInvariantOfTower K M L).IsVertex k) : ∃ v : ℕ,
      addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff
        (ringChar 𝓀[K] ^ ((herbrandInvariantOfTower K M L).w - k))) = v ∧
      (v : ℚ) + ringChar 𝓀[K] ^ ((herbrandInvariantOfTower K M L).w - k) =
        (herbrandInvariantOfTower K M L).ramificationIndex *
          ((herbrandInvariantOfTower K M L).mean k + 1) := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  have hpp : (ringChar 𝓀[K]).Prime :=
    CharP.prime_ringChar _
  rcases exists_ram_eq_herbrandOfSubgroup_of_le K M L hk with ⟨t, hr, hs⟩
  have hindex : (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex
      (lowerRamificationGroup K M (t + 1 : ℕ)) =
        ringChar 𝓀[K] ^ ((herbrandInvariantOfTower K M L).w - k) := by
    rw [relIndex_lowerRamificationGroup_succ, ← hr, ramsOfSubgroup_countP_le_ram K M L hk hfin]
  have key : ((∑ j ∈ range (t + 1 + 1), Nat.card (lowerRamificationGroup L M (j : ℤ))) *
      ringChar 𝓀[K] ^ ((herbrandInvariantOfTower K M L).w - k) : ℕ) +
        TauCeti.ramificationIndex L M •
          addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff
            (ringChar 𝓀[K] ^ ((herbrandInvariantOfTower K M L).w - k))) =
      (∑ j ∈ range (t + 1 + 1), Nat.card (lowerRamificationGroup K M (j : ℤ)) : ℕ) := by
    rw [← hindex]
    exact sum_card_mul_relIndex_add_addVal_coeff_taylor (t + 1) hy hf hdeg hroot
  rcases ENat.ne_top_iff_exists.mp (fun htop ↦ by
    rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast TauCeti.ramificationIndex_pos.ne'),
      add_top] at key
    exact ENat.natCast_ne_top _ key.symm : addVal 𝒪[L] ((taylor y
      (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff
        (ringChar 𝓀[K] ^ ((herbrandInvariantOfTower K M L).w - k))) ≠ ⊤) with ⟨v, hv⟩
  refine ⟨v, hv.symm, ?_⟩
  rw [← hv, nsmul_eq_mul] at key
  have hreal : ((∑ j ∈ range (t + 1 + 1), Nat.card (lowerRamificationGroup L M (j : ℤ)) : ℕ) : ℝ) *
      ((ringChar 𝓀[K] ^ ((herbrandInvariantOfTower K M L).w - k) : ℕ) : ℝ) +
        TauCeti.ramificationIndex L M * v =
      ((∑ j ∈ range (t + 1 + 1), Nat.card (lowerRamificationGroup K M (j : ℤ)) : ℕ) : ℝ) := by
    exact_mod_cast key
  rw [natCast_sum_card_lowerRamificationGroup K M (t + 1),
    natCast_sum_card_lowerRamificationGroup L M (t + 1),
    ← herbrandOfSubgroup_range_restrictScalarsHom K M (t + 1) L,
    ← herbrandFunction_herbrandInvariantOfTower_herbrandOfSubgroup (L := L) (t + 1),
    ramificationIndex_tower (K := K) (L := L) M] at hreal
  have hstrict :
      StrictMono (herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range) :=
    herbrandOfSubgroup_strictMono K M _
  generalize hx : herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range (t + 1) =
    x at hreal
  have hle : (herbrandInvariantOfTower K M L).ram k ≤ x := by
    rw [hr, ← hx]
    exact hstrict.monotone t.le_succ
  have hφ : (herbrandInvariantOfTower K M L).herbrandFunction x =
      (herbrandInvariantOfTower K M L).swanSlope k + ((x : ℝ) -
        (herbrandInvariantOfTower K M L).ram k) /
          ((herbrandInvariantOfTower K M L).ε * (ringChar 𝓀[K] : ℝ) ^ k) := by
    rcases hk.lt_or_eq with hlt | rfl
    · refine (herbrandInvariantOfTower K M L).herbrandFunction_of_mem_Icc hlt
        ⟨Rat.cast_le.mpr hle, Rat.cast_le.mpr ?_⟩
      rcases exists_ram_eq_herbrandOfSubgroup_of_le K M L hlt with ⟨t', hr', -⟩
      rcases hfin with rfl | hfin
      · exact absurd hlt (lt_irrefl _)
      rw [hr', ← hx]
      refine hstrict.monotone (Nat.succ_le_of_lt (hstrict.lt_iff_lt.mp ?_))
      rw [← hr, ← hr']
      exact hfin
    · exact (herbrandInvariantOfTower K M L).herbrandFunction_of_le (Rat.cast_le.mpr hle)
  rw [hφ] at hreal
  have hp₀ : (ringChar 𝓀[K] : ℝ) ≠ 0 := by
    exact_mod_cast hpp.ne_zero
  have hε : ((herbrandInvariantOfTower K M L).ε : ℝ) ≠ 0 := by
    exact_mod_cast (herbrandInvariantOfTower K M L).ε_pos.ne'
  have he : (TauCeti.ramificationIndex L M : ℝ) ≠ 0 := by
    exact_mod_cast TauCeti.ramificationIndex_pos.ne'
  have htiny : (((herbrandInvariantOfTower K M L).ram k : ℝ)) /
      ((herbrandInvariantOfTower K M L).ε * (ringChar 𝓀[K] : ℝ) ^ k) =
        ((herbrandInvariantOfTower K M L).swanSlope k : ℝ) -
          (herbrandInvariantOfTower K M L).mean k := by
    have h : (herbrandInvariantOfTower K M L).tinyRam k =
        (herbrandInvariantOfTower K M L).swanSlope k - (herbrandInvariantOfTower K M L).mean k :=
      (herbrandInvariantOfTower K M L).tinyRam_eq_swanSlope_sub_mean hpp.ne_zero k
    rw [tinyRam] at h
    exact_mod_cast h
  have hpow : ((ringChar 𝓀[K] : ℝ)) ^ (herbrandInvariantOfTower K M L).w =
      (ringChar 𝓀[K] : ℝ) ^ k * (ringChar 𝓀[K] : ℝ) ^ ((herbrandInvariantOfTower K M L).w - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  have hRI : (TauCeti.ramificationIndex K L : ℝ) = (herbrandInvariantOfTower K M L).ε *
      (ringChar 𝓀[K] : ℝ) ^ (herbrandInvariantOfTower K M L).w := by
    exact_mod_cast (ε_mul_pow_w_herbrandInvariantOfTower K M L).symm
  have hdiv : (TauCeti.ramificationIndex K L : ℝ) * ((x : ℝ) /
      ((herbrandInvariantOfTower K M L).ε * (ringChar 𝓀[K] : ℝ) ^ k)) =
        (ringChar 𝓀[K] : ℝ) ^ ((herbrandInvariantOfTower K M L).w - k) * x := by
    rw [hRI, hpow]
    field_simp
  have hmain : (v : ℝ) + (ringChar 𝓀[K] : ℝ) ^ ((herbrandInvariantOfTower K M L).w - k) =
      (TauCeti.ramificationIndex K L : ℝ) *
        (((herbrandInvariantOfTower K M L).mean k : ℝ) + 1) := by
    refine mul_left_cancel₀ he ?_
    rw [sub_div, htiny] at hreal
    push_cast at hreal
    linear_combination hreal + (TauCeti.ramificationIndex L M : ℝ) * hdiv
  rw [HerbrandInvariant.ramificationIndex]
  rw [hRI] at hmain
  exact_mod_cast hmain

variable (M) in
/-- **The ramification polygon of an extension is the polygon of its Herbrand invariant** (Monge,
arXiv:1109.4617, Proposition 1 and Lemma 1, p. 4, for an extension `L / K` that need not be normal):
in a tower `M / L / K` with `M / K` finite Galois, let `f` be a monic Eisenstein polynomial over
`𝒪[K]` with a root `y ∈ 𝒪[L]` generating `L` over `K`. Then the ramification polygon of `f` at `y`
is the polygon of the Herbrand invariant of `L / K`. -/
lemma isRamificationPolygon_herbrandInvariantOfTower (hm : f.Monic) (hf : f.IsEisensteinAt 𝓂[K])
    (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot y) (hgen : K⟮(y : L)⟯ = ⊤) :
    (herbrandInvariantOfTower K M L).IsRamificationPolygon f y := by
  have hy : Algebra.adjoin 𝒪[K] {y} = ⊤ :=
    algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top hf hroot hgen
  have hdeg : f.natDegree = Module.finrank K L :=
    natDegree_eq_finrank_of_isEisensteinAt hf hroot hgen
  have hroot' : aeval y f = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact hroot
  refine ⟨?_, fun hk _ hv ↦ rat_le_of_addVal_coeff_taylor M hy hm hdeg hroot' hk hv,
    fun hk hfin ↦ exists_addVal_coeff_taylor_eq M hy hm hdeg hroot' hk hfin⟩
  rw [HerbrandInvariant.ramificationIndex, ε_mul_pow_w_herbrandInvariantOfTower,
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf y hroot hgen]

end IsNonarchimedeanLocalField.HerbrandInvariant
