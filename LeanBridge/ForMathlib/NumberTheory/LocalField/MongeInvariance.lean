import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolygon

/-!
# Monge's subgroups depend only on the uniformiser modulo its square

Let `L / K` be a totally ramified extension of nonarchimedean local fields, contained in a finite
Galois extension `M` of `K`, and `y`, `y'` two uniformisers of `L` generating `𝒪[L]` over `𝒪[K]`
with `y' ≡ y` modulo `y ^ 2`, roots of the monic polynomials `f`, `f'` of degree `[L : K]` over
`𝒪[K]`. Monge (arXiv:1109.4617, Int. J. Number Theory 10 (2014), p. 6) states that the additive
polynomials `S_m` of `f` at `y` and of `f'` at `y'` agree, for all `m`, as a consequence of his
Theorem 2 (p. 15), a finer congruence between `f` and `f'` which is not formalised. This file proves
it directly by comparing the factorisations of `f(y + y ^ (m + 1) T)` and `f'(y' + y' ^ (m + 1) T)`
over `𝒪[M]`: for `σ ∈ Gal(M / K)`, `y' - σ y' ≡ y - σ y` modulo `(y - σ y) 𝔪_M`, so that the two
polynomials are congruent modulo `y ^ (N + 1)` for their common level `N`. So Monge's subgroups
`W_σ` of `f` at `y` and of `f'` at `y'` are the same, which is what Monge's reduction needs in order
to keep the sets of representatives of `λ / W_σ` along the changes of uniformiser.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.mongeLevel_eq_mongeLevel`: the level does not depend
  on the uniformiser generating `𝒪[L]`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.C_pow_succ_dvd_mongeShift_sub`: the shifted
  polynomials of `f` at `y` and of `f'` at `y'` are congruent above their level.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mongeSubgroup_eq_of_pow_two_dvd_sub` (LMFDB
  `lf.family_polynomial`): Monge's subgroups depend only on `L` and the class of the uniformiser
  modulo its square.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mongeSubgroup_eq_of_pow_two_dvd_sub_visible`: the
  same for an extension of `K` inside `K̄`, where `M` is its Galois closure and no tower remains in
  the statement.
-/

open Algebra Finset Ideal IntermediateField IsDiscreteValuationRing Polynomial TauCeti IsLocalRing
  LocalFieldsRamification ValuativeRel

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {T ι : Type*} [CommRing T] {ρ : T} (A : Finset ι) (F F' : ι → T[X]) (l : ι → ℕ)

lemma C_pow_dvd_prod (hF : ∀ i ∈ A, C (ρ ^ l i) ∣ F i) : C (ρ ^ ∑ i ∈ A, l i) ∣ ∏ i ∈ A, F i := by
  rw [← prod_pow_eq_pow_sum, map_prod]
  exact prod_dvd_prod_of_dvd _ _ hF

lemma C_pow_succ_dvd_prod_sub_prod (hF : ∀ i ∈ A, C (ρ ^ l i) ∣ F i)
    (hF' : ∀ i ∈ A, C (ρ ^ (l i + 1)) ∣ F' i - F i) :
    C (ρ ^ (∑ i ∈ A, l i + 1)) ∣ ∏ i ∈ A, F' i - ∏ i ∈ A, F i := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert i A hi ih =>
    have ih' : C (ρ ^ (∑ i ∈ A, l i + 1)) ∣ ∏ i ∈ A, F' i - ∏ i ∈ A, F i :=
      ih (fun j hj ↦ hF j (mem_insert_of_mem hj)) fun j hj ↦ hF' j (mem_insert_of_mem hj)
    have hP : C (ρ ^ ∑ i ∈ A, l i) ∣ ∏ i ∈ A, F i :=
      C_pow_dvd_prod A F l fun j hj ↦ hF j (mem_insert_of_mem hj)
    have hQ : C (ρ ^ ∑ i ∈ A, l i) ∣ ∏ i ∈ A, F' i := by
      rw [← sub_add_cancel (∏ i ∈ A, F' i) (∏ i ∈ A, F i)]
      refine dvd_add (dvd_trans ?_ ih') hP
      exact map_dvd C (pow_dvd_pow ρ (Nat.le_succ _))
    have heq : F' i * ∏ i ∈ A, F' i - F i * ∏ i ∈ A, F i =
        (F' i - F i) * ∏ i ∈ A, F' i + F i * (∏ i ∈ A, F' i - ∏ i ∈ A, F i) := by
      ring1
    have h₁ : C (ρ ^ (l i + ∑ i ∈ A, l i + 1)) = C (ρ ^ (l i + 1)) * C (ρ ^ ∑ i ∈ A, l i) := by
      rw [← C_mul, ← pow_add]
      congr 2
      omega
    have h₂ : C (ρ ^ (l i + ∑ i ∈ A, l i + 1)) = C (ρ ^ l i) * C (ρ ^ (∑ i ∈ A, l i + 1)) := by
      rw [← C_mul, ← pow_add]
      congr 2
    rw [prod_insert hi, prod_insert hi, sum_insert hi, heq]
    refine dvd_add ?_ ?_
    · rw [h₁]
      exact mul_dvd_mul (hF' i (mem_insert_self i A)) hQ
    · rw [h₂]
      exact mul_dvd_mul (hF i (mem_insert_self i A)) ih'

variable [IsDomain T] [IsDiscreteValuationRing T] in
lemma dvd_of_not_isUnit (hρ : Irreducible ρ) {x : T} (hx : ¬IsUnit x) : ρ ∣ x := by
  rw [← mem_span_singleton, ← hρ.maximalIdeal_eq, mem_maximalIdeal, mem_nonunits_iff]
  exact hx

lemma eq_of_natCast_mul_eq {e B : ℕ} (he : e ≠ 0) {x z : ℕ∞} (hx : (e : ℕ∞) * x = B)
    (hz : (e : ℕ∞) * z = B) : x = z := by
  have hne {w : ℕ∞} (hw : (e : ℕ∞) * w = B) : w ≠ ⊤ := fun h ↦ by
    rw [h, ENat.mul_top (by exact_mod_cast he)] at hw
    exact ENat.natCast_ne_top B hw.symm
  rcases ENat.ne_top_iff_exists.mp (hne hx) with ⟨a, rfl⟩
  rcases ENat.ne_top_iff_exists.mp (hne hz) with ⟨c, rfl⟩
  have h₁ : e * a = e * c := by
    exact_mod_cast hx.trans hz.symm
  rw [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) h₁]

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] {y y' : 𝒪[L]}
  {f f' : 𝒪[K][X]} {m N t p : ℕ}

section Tower

variable {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra L M] [ValuativeExtension L M] [Algebra K M] [ValuativeExtension K M]
  [Module.Finite K M] [IsScalarTower K L M] {ϖ : 𝒪[M]}

lemma not_isUnit_algebraMap (hyπ : Irreducible y) : ¬IsUnit (algebraMap 𝒪[L] 𝒪[M] y) := fun hu ↦ by
  rcases hu with ⟨u, hu⟩
  have h₀ : addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y) = 0 := by
    rw [← hu]
    exact addVal_eq_zero_of_unit u
  rw [TauCeti.addVal_algebraMap, addVal_uniformizer hyπ, nsmul_one] at h₀
  exact TauCeti.ramificationIndex_pos.ne' (by exact_mod_cast h₀)

variable [Module.Finite L M]

lemma dvd_sub_smul_sub_sub (hyπ : Irreducible y) (hy : adjoin 𝒪[K] {y} = ⊤) (hdvd : y ^ 2 ∣ y' - y)
    (σ : M ≃ₐ[K] M) (hϖ : Irreducible ϖ) :
    (algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y) * ϖ ∣ algebraMap 𝒪[L] 𝒪[M] y' -
      σ • algebraMap 𝒪[L] 𝒪[M] y' - (algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y) := by
  rcases hdvd with ⟨w, hw⟩
  have hy' : y' = y + y * (y * w) := by
    linear_combination hw
  have hnu : ¬IsUnit (algebraMap 𝒪[L] 𝒪[M] y) :=
    not_isUnit_algebraMap hyπ
  have hnuσ : ¬IsUnit (σ • algebraMap 𝒪[L] 𝒪[M] y) := fun hu ↦ hnu <| by
    simpa using hu.map (MulSemiringAction.toRingHom (M ≃ₐ[K] M) 𝒪[M] σ⁻¹)
  have h₁ : algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y ∣
      algebraMap 𝒪[L] 𝒪[M] (y * w) - σ • algebraMap 𝒪[L] 𝒪[M] (y * w) := by
    rw [← neg_sub, ← neg_sub (σ • algebraMap 𝒪[L] 𝒪[M] (y * w)), neg_dvd, dvd_neg]
    exact smul_sub_dvd_smul_algebraMap_sub σ hy (y * w)
  have heq : algebraMap 𝒪[L] 𝒪[M] y' - σ • algebraMap 𝒪[L] 𝒪[M] y' -
      (algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y) =
      (algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y) * algebraMap 𝒪[L] 𝒪[M] (y * w) +
        σ • algebraMap 𝒪[L] 𝒪[M] y *
          (algebraMap 𝒪[L] 𝒪[M] (y * w) - σ • algebraMap 𝒪[L] 𝒪[M] (y * w)) := by
    rw [hy', map_add, map_mul, smul_add, smul_mul']
    ring1
  rw [heq]
  refine dvd_add (mul_dvd_mul_left _ ?_) ?_
  · rw [map_mul]
    exact (dvd_of_not_isUnit hϖ hnu).mul_right _
  · rw [mul_comm (σ • algebraMap 𝒪[L] 𝒪[M] y)]
    exact mul_dvd_mul h₁ (dvd_of_not_isUnit hϖ hnuσ)

lemma C_pow_succ_dvd_factor_sub (hyπ : Irreducible y) (hy : adjoin 𝒪[K] {y} = ⊤)
    (hdvd : y ^ 2 ∣ y' - y) (σ : M ≃ₐ[K] M) (hϖ : Irreducible ϖ) {a : ℕ}
    (ha : (a : ℕ∞) = min (addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y))
      (addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1)))) : C (ϖ ^ (a + 1)) ∣
    (X - C (σ • algebraMap 𝒪[L] 𝒪[M] y')).comp
        (C (algebraMap 𝒪[L] 𝒪[M] y') + C (algebraMap 𝒪[L] 𝒪[M] y' ^ (m + 1)) * X) -
      (X - C (σ • algebraMap 𝒪[L] 𝒪[M] y)).comp
        (C (algebraMap 𝒪[L] 𝒪[M] y) + C (algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1)) * X) := by
  have h₀ : ϖ ^ a ∣ algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y :=
    (pow_dvd_iff_le_addVal hϖ).mpr (ha.trans_le (min_le_left _ _))
  have h₁ : ϖ ^ a ∣ algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1) :=
    (pow_dvd_iff_le_addVal hϖ).mpr (ha.trans_le (min_le_right _ _))
  have hcoeff₀ : ϖ ^ (a + 1) ∣ algebraMap 𝒪[L] 𝒪[M] y' - σ • algebraMap 𝒪[L] 𝒪[M] y' -
      (algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y) := by
    rw [pow_succ]
    exact (mul_dvd_mul_right h₀ ϖ).trans (dvd_sub_smul_sub_sub hyπ hy hdvd σ hϖ)
  have hcoeff₁ :
      ϖ ^ (a + 1) ∣ algebraMap 𝒪[L] 𝒪[M] y' ^ (m + 1) - algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1) := by
    rcases hdvd with ⟨w, hw⟩
    have hy' :
        algebraMap 𝒪[L] 𝒪[M] y' = algebraMap 𝒪[L] 𝒪[M] y * (1 + algebraMap 𝒪[L] 𝒪[M] (y * w)) := by
      rw [← map_one (algebraMap 𝒪[L] 𝒪[M]), ← map_add, ← map_mul]
      exact congrArg _ (by linear_combination hw)
    have h₂ : ϖ ∣ (1 + algebraMap 𝒪[L] 𝒪[M] (y * w)) ^ (m + 1) - 1 ^ (m + 1) := by
      refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ (m + 1))
      rw [add_sub_cancel_left, map_mul]
      exact (dvd_of_not_isUnit hϖ (not_isUnit_algebraMap hyπ)).mul_right _
    have heq : algebraMap 𝒪[L] 𝒪[M] y' ^ (m + 1) - algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1) =
        algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1) *
          ((1 + algebraMap 𝒪[L] 𝒪[M] (y * w)) ^ (m + 1) - 1 ^ (m + 1)) := by
      rw [hy', mul_pow, one_pow]
      ring1
    rw [heq, pow_succ]
    exact mul_dvd_mul h₁ h₂
  have heq : (X - C (σ • algebraMap 𝒪[L] 𝒪[M] y')).comp
        (C (algebraMap 𝒪[L] 𝒪[M] y') + C (algebraMap 𝒪[L] 𝒪[M] y' ^ (m + 1)) * X) -
      (X - C (σ • algebraMap 𝒪[L] 𝒪[M] y)).comp
        (C (algebraMap 𝒪[L] 𝒪[M] y) + C (algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1)) * X) =
      C (algebraMap 𝒪[L] 𝒪[M] y' - σ • algebraMap 𝒪[L] 𝒪[M] y' -
        (algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y)) +
        C (algebraMap 𝒪[L] 𝒪[M] y' ^ (m + 1) - algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1)) * X := by
    simp only [sub_comp, X_comp, C_comp, C_sub]
    ring1
  rw [heq]
  exact dvd_add (map_dvd C hcoeff₀) ((map_dvd C hcoeff₁).mul_right X)

variable [IsGalois K M]

lemma C_pow_succ_dvd_map_mongeShift_sub (hyπ : Irreducible y) (hy : adjoin 𝒪[K] {y} = ⊤)
    (hf : f.Monic) (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0)
    (hy' : adjoin 𝒪[K] {y'} = ⊤) (hf' : f'.Monic) (hdeg' : f'.natDegree = Module.finrank K L)
    (hroot' : aeval y' f' = 0) (hdvd : y ^ 2 ∣ y' - y) (hϖ : Irreducible ϖ)
    (ht : ∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) =
      (m + 1) * TauCeti.ramificationIndex L M) :
    C (ϖ ^ (∑ k ∈ range t, Nat.card (lowerRamificationGroup K M (k : ℤ)) + 1)) ∣
      (mongeShift f' y' m - mongeShift f y m).map (algebraMap 𝒪[L] 𝒪[M]) := by
  classical
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  rcases exists_natCast_eq_min (M := M) K t hy with ⟨l, hl, hsum⟩
  have hv : addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1)) =
      ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) := by
    rw [addVal_pow, TauCeti.addVal_algebraMap, addVal_uniformizer hyπ, ht, nsmul_one, nsmul_eq_mul]
    push_cast
    rfl
  have hl' (c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range) :
      (l c : ℕ∞) = min (addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y))
        (addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1))) := by
    rw [hv]
    exact hl c
  rw [Polynomial.map_sub, map_mongeShift_eq_prod univ _ (map_eq_prod_quotient hy' hf' hdeg' hroot'),
    map_mongeShift_eq_prod univ _ (map_eq_prod_quotient hy hf hdeg hroot), Polynomial.prod_comp,
    Polynomial.prod_comp, ← hsum]
  refine C_pow_succ_dvd_prod_sub_prod univ _ _ l (fun c _ ↦ ?_) fun c _ ↦
    C_pow_succ_dvd_factor_sub hyπ hy hdvd _ hϖ (hl' c)
  have h₁ : (X - C (c.out • algebraMap 𝒪[L] 𝒪[M] y)).comp
      (C (algebraMap 𝒪[L] 𝒪[M] y) + C (algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1)) * X) =
      C (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y) +
        C (algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1)) * X := by
    simp only [sub_comp, X_comp, C_comp, C_sub]
    ring1
  rw [h₁]
  exact (isGaussLevel_C_add_C_mul_X hϖ (hl' c)).1

end Tower

/-- **The level does not depend on the uniformiser generating `𝒪[L]`**: in a tower `M / L / K` with
`M / K` finite Galois, Monge's level at `m` of a monic polynomial of degree `[L : K]` with a
uniformiser `y` of `L` as a root, generating `𝒪[L]` over `𝒪[K]`, depends only on `L / K` and `m`. -/
lemma mongeLevel_eq_mongeLevel (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
    [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M] [IsScalarTower K L M]
    (hyπ : Irreducible y) (hy : adjoin 𝒪[K] {y} = ⊤) (hf : f.Monic)
    (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0) (hyπ' : Irreducible y')
    (hy' : adjoin 𝒪[K] {y'} = ⊤) (hf' : f'.Monic) (hdeg' : f'.natDegree = Module.finrank K L)
    (hroot' : aeval y' f' = 0) : mongeLevel f' y' m = mongeLevel f y m := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  exact eq_of_natCast_mul_eq (TauCeti.ramificationIndex_pos (K := L) (L := M)).ne'
    (natCast_mul_mongeLevel_eq (M := M) hyπ' hy' hf' hdeg' hroot'
      (sum_card_lowerRamificationGroup_psiNat m L M))
    (natCast_mul_mongeLevel_eq (M := M) hyπ hy hf hdeg hroot
      (sum_card_lowerRamificationGroup_psiNat m L M))

/-- **The invariance of Monge's additive polynomials** (Monge, arXiv:1109.4617, p. 6), in terms of
the shifted polynomials: in a tower `M / L / K` with `M / K` finite Galois, let `y`, `y'` be
uniformisers of `L` generating `𝒪[L]` over `𝒪[K]`, roots of monic polynomials `f`, `f'` of degree
`[L : K]` over `𝒪[K]`, with `y' ≡ y` modulo `y ^ 2`. If `N` is the level of `f` at `y` and `m`, then
`f'(y' + y' ^ (m + 1) T) ≡ f(y + y ^ (m + 1) T)` modulo `y ^ (N + 1)`. -/
lemma C_pow_succ_dvd_mongeShift_sub (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
    [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M] [IsScalarTower K L M]
    (hyπ : Irreducible y) (hy : adjoin 𝒪[K] {y} = ⊤) (hf : f.Monic)
    (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0) (hy' : adjoin 𝒪[K] {y'} = ⊤)
    (hf' : f'.Monic) (hdeg' : f'.natDegree = Module.finrank K L) (hroot' : aeval y' f' = 0)
    (hdvd : y ^ 2 ∣ y' - y) (hN : mongeLevel f y m = N) :
    C (y ^ (N + 1)) ∣ mongeShift f' y' m - mongeShift f y m := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  have ht : ∑ k ∈ range (psiNat L M m + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) =
      (m + 1) * TauCeti.ramificationIndex L M :=
    sum_card_lowerRamificationGroup_psiNat m L M
  generalize psiNat L M m = t at ht
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[M] with ⟨ϖ, hϖ⟩
  have hlevel : TauCeti.ramificationIndex L M * N =
      ∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (k : ℤ)) := by
    have h₁ : (TauCeti.ramificationIndex L M : ℕ∞) * mongeLevel f y m =
        (∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) :=
      natCast_mul_mongeLevel_eq hyπ hy hf hdeg hroot ht
    rw [hN] at h₁
    exact_mod_cast h₁
  have hcore : C (ϖ ^ (∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (k : ℤ)) + 1)) ∣
      (mongeShift f' y' m - mongeShift f y m).map (algebraMap 𝒪[L] 𝒪[M]) :=
    C_pow_succ_dvd_map_mongeShift_sub hyπ hy hf hdeg hroot hy' hf' hdeg' hroot' hdvd hϖ ht
  rw [← hlevel, C_dvd_iff_dvd_coeff] at hcore
  refine (C_dvd_iff_dvd_coeff _ _).mpr fun k ↦ ?_
  have h₂ : ϖ ^ (TauCeti.ramificationIndex L M * N + 1) ∣
      ((mongeShift f' y' m - mongeShift f y m).map (algebraMap 𝒪[L] 𝒪[M])).coeff k :=
    hcore k
  rw [coeff_map, pow_dvd_iff_le_addVal hϖ, TauCeti.addVal_algebraMap] at h₂
  rw [pow_dvd_iff_le_addVal hyπ]
  rcases eq_or_ne (addVal 𝒪[L] ((mongeShift f' y' m - mongeShift f y m).coeff k)) ⊤ with htop | htop
  · rw [htop]
    exact le_top
  rcases ENat.ne_top_iff_exists.mp htop with ⟨v, hv⟩
  rw [← hv, nsmul_eq_mul] at h₂
  rw [← hv]
  have h₃ : TauCeti.ramificationIndex L M * N + 1 ≤ TauCeti.ramificationIndex L M * v := by
    exact_mod_cast h₂
  have h₄ : N < v :=
    Nat.lt_of_mul_lt_mul_left (a := TauCeti.ramificationIndex L M) (by omega)
  exact_mod_cast h₄

variable {ϖ : 𝒪[K]} {a a' : ℕ → 𝒪[K]}

lemma dvd_algebraMap_sub_of_pow_two_dvd (h : IsMongeRoot f y p) (h' : IsMongeRoot f' y' p)
    (hdeg : f'.natDegree = f.natDegree) (hϖ : Irreducible ϖ)
    (ha : ∀ i < f.natDegree, f.coeff i = ϖ * a i) (ha' : ∀ i < f'.natDegree, f'.coeff i = ϖ * a' i)
    (hdvd : y ^ 2 ∣ y' - y) : y ∣ algebraMap 𝒪[K] 𝒪[L] (a' 0) - algebraMap 𝒪[K] 𝒪[L] (a 0) := by
  have h₁ : y ^ f.natDegree = algebraMap 𝒪[K] 𝒪[L] ϖ *
      -∑ i ∈ range f.natDegree, algebraMap 𝒪[K] 𝒪[L] (a i) * y ^ i :=
    pow_natDegree_eq_mul_neg_sum h.monic ha h.aeval_eq_zero
  have h₂ : y' ^ f'.natDegree = algebraMap 𝒪[K] 𝒪[L] ϖ *
      -∑ i ∈ range f'.natDegree, algebraMap 𝒪[K] 𝒪[L] (a' i) * y' ^ i :=
    pow_natDegree_eq_mul_neg_sum h'.monic ha' h'.aeval_eq_zero
  have h₃ : y ∣ -∑ i ∈ range f.natDegree, algebraMap 𝒪[K] 𝒪[L] (a i) * y ^ i +
      algebraMap 𝒪[K] 𝒪[L] (a 0) :=
    mem_span_singleton.mp (neg_sum_add_mem_span_singleton h.natDegree_pos)
  have h₄ : y' ∣ -∑ i ∈ range f'.natDegree, algebraMap 𝒪[K] 𝒪[L] (a' i) * y' ^ i +
      algebraMap 𝒪[K] 𝒪[L] (a' 0) :=
    mem_span_singleton.mp (neg_sum_add_mem_span_singleton h'.natDegree_pos)
  generalize -∑ i ∈ range f.natDegree, algebraMap 𝒪[K] 𝒪[L] (a i) * y ^ i = v at h₁ h₃
  generalize -∑ i ∈ range f'.natDegree, algebraMap 𝒪[K] 𝒪[L] (a' i) * y' ^ i = v' at h₂ h₄
  rcases hdvd with ⟨w, hw⟩
  have hy' : y' = y * (1 + y * w) := by
    linear_combination hw
  have hyy' : y ∣ y' :=
    ⟨_, hy'⟩
  rw [hdeg] at h₂
  have hpow : y ^ (f.natDegree + 1) ∣ y' ^ f.natDegree - y ^ f.natDegree := by
    have h₅ : y ∣ (1 + y * w) ^ f.natDegree - 1 ^ f.natDegree := by
      refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ f.natDegree)
      rw [add_sub_cancel_left]
      exact dvd_mul_right y w
    have h₆ : y' ^ f.natDegree - y ^ f.natDegree =
        y ^ f.natDegree * ((1 + y * w) ^ f.natDegree - 1 ^ f.natDegree) := by
      rw [hy', mul_pow, one_pow]
      ring1
    rw [h₆, pow_succ]
    exact mul_dvd_mul_left _ h₅
  have hv : y ∣ v' - v := by
    have h₅ : y' ^ f.natDegree - y ^ f.natDegree = algebraMap 𝒪[K] 𝒪[L] ϖ * (v' - v) := by
      rw [h₁, h₂]
      ring1
    rw [h₅, pow_dvd_iff_le_addVal h.irreducible, addVal_mul, h.addVal_algebraMap,
      addVal_uniformizer hϖ, nsmul_one] at hpow
    rcases eq_or_ne (addVal 𝒪[L] (v' - v)) ⊤ with htop | htop
    · exact (addVal_eq_top_iff.mp htop) ▸ dvd_zero y
    rcases ENat.ne_top_iff_exists.mp htop with ⟨b, hb⟩
    rw [← hb] at hpow
    have h₆ : f.natDegree + 1 ≤ f.natDegree + b := by
      exact_mod_cast hpow
    refine (pow_one y ▸ (pow_dvd_iff_le_addVal h.irreducible).mpr ?_ : y ∣ v' - v)
    rw [← hb]
    exact_mod_cast (by omega : 1 ≤ b)
  have heq : algebraMap 𝒪[K] 𝒪[L] (a' 0) - algebraMap 𝒪[K] 𝒪[L] (a 0) =
      (v' + algebraMap 𝒪[K] 𝒪[L] (a' 0)) - (v + algebraMap 𝒪[K] 𝒪[L] (a 0)) - (v' - v) := by
    ring1
  rw [heq]
  exact dvd_sub (dvd_sub (hyy'.trans h₄) h₃) hv

lemma mongeImage_subset_of_pow_two_dvd_sub (M : Type*) [Field M] [ValuativeRel M]
    [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra L M] [ValuativeExtension L M]
    [Module.Finite L M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]
    [IsScalarTower K L M] (𝔪 : Ideal 𝒪[K]) (σ : ℕ) (h : IsMongeRoot f y p)
    (h' : IsMongeRoot f' y' p) (hy : adjoin 𝒪[K] {y} = ⊤) (hy' : adjoin 𝒪[K] {y'} = ⊤)
    (hdeg : f.natDegree = Module.finrank K L) (hdeg' : f'.natDegree = Module.finrank K L)
    (hϖ : Irreducible ϖ) (ha : ∀ i < f.natDegree, f.coeff i = ϖ * a i)
    (ha' : ∀ i < f'.natDegree, f'.coeff i = ϖ * a' i) (hdvd : y ^ 2 ∣ y' - y) :
    mongeImage ϖ 𝔪 f y σ ⊆ mongeImage ϖ 𝔪 f' y' σ := by
  rintro x ⟨k, hk, hl, d, r, θ, u, hd, hr, hu, hmem⟩
  have hdd : f'.natDegree = f.natDegree :=
    hdeg'.trans hdeg.symm
  have hda : d = a 0 :=
    mul_left_cancel₀ hϖ.ne_zero (hd.symm.trans (ha 0 h.natDegree_pos))
  have hl' : mongeLevel f' y' k = (σ + f'.natDegree : ℕ) := by
    rw [hdd, mongeLevel_eq_mongeLevel M h.irreducible hy h.monic hdeg h.aeval_eq_zero h'.irreducible
      hy' h'.monic hdeg' h'.aeval_eq_zero, hl]
  have hC : C (y' ^ (σ + f'.natDegree)) ∣ mongeShift f' y' k :=
    (C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ pow_dvd_of_le_emultiplicity (hl' ▸ iInf_le _ i)
  have hdvd' : y' ^ (σ + f'.natDegree) ∣ (mongeShift f' y' k).eval (algebraMap 𝒪[K] 𝒪[L] θ) := by
    simpa using eval_dvd (x := algebraMap 𝒪[K] 𝒪[L] θ) hC
  rcases hdvd' with ⟨u', hu'⟩
  refine ⟨k, hk, hl', a' 0, r, θ, u', ha' 0 h'.natDegree_pos, hr, hu', ?_⟩
  have hdig : y ∣ algebraMap 𝒪[K] 𝒪[L] (a' 0) - algebraMap 𝒪[K] 𝒪[L] (a 0) :=
    dvd_algebraMap_sub_of_pow_two_dvd h h' hdd hϖ ha ha' hdvd
  have he : y ^ (σ + f.natDegree + 1) ∣ (mongeShift f' y' k).eval (algebraMap 𝒪[K] 𝒪[L] θ) -
      (mongeShift f y k).eval (algebraMap 𝒪[K] 𝒪[L] θ) := by
    simpa using eval_dvd (x := algebraMap 𝒪[K] 𝒪[L] θ)
      (C_pow_succ_dvd_mongeShift_sub M h.irreducible hy h.monic hdeg h.aeval_eq_zero hy' h'.monic
        hdeg' h'.aeval_eq_zero hdvd hl)
  rcases hdvd with ⟨w, hw⟩
  have hyv : y' = y * (1 + y * w) := by
    linear_combination hw
  have hyy' : y ∣ y' :=
    ⟨_, hyv⟩
  have hy'y : y' ∣ y :=
    h.irreducible.dvd_symm h'.irreducible hyy'
  have hv : y ∣ (1 + y * w) ^ (σ + f.natDegree) - 1 ^ (σ + f.natDegree) := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ (σ + f.natDegree))
    rw [add_sub_cancel_left]
    exact dvd_mul_right y w
  have huu : y ∣ u' - u := by
    rw [hu, hu', hdd, hyv, mul_pow, mul_assoc, ← mul_sub, pow_succ,
      mul_dvd_mul_iff_left (pow_ne_zero _ h.irreducible.ne_zero)] at he
    have heq : u' - u = (1 + y * w) ^ (σ + f.natDegree) * u' - u -
        ((1 + y * w) ^ (σ + f.natDegree) - 1 ^ (σ + f.natDegree)) * u' := by
      rw [one_pow]
      ring1
    rw [heq]
    exact dvd_sub he (hv.mul_right u')
  refine mem_span_singleton.mpr (hy'y.trans ?_)
  have hA : y ∣ (-algebraMap 𝒪[K] 𝒪[L] (a 0)) ^ (σ / f.natDegree + 1) -
      (-algebraMap 𝒪[K] 𝒪[L] (a' 0)) ^ (σ / f.natDegree + 1) := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ _)
    rw [neg_sub_neg]
    exact hdig
  rw [hda] at hmem
  have heq : algebraMap 𝒪[K] 𝒪[L] r - algebraMap 𝒪[K] 𝒪[L] ((-a' 0) ^ (σ / f'.natDegree + 1)) * u' =
      algebraMap 𝒪[K] 𝒪[L] r - algebraMap 𝒪[K] 𝒪[L] ((-a 0) ^ (σ / f.natDegree + 1)) * u +
        ((-algebraMap 𝒪[K] 𝒪[L] (a 0)) ^ (σ / f.natDegree + 1) -
          (-algebraMap 𝒪[K] 𝒪[L] (a' 0)) ^ (σ / f.natDegree + 1)) * u -
        (-algebraMap 𝒪[K] 𝒪[L] (a' 0)) ^ (σ / f.natDegree + 1) * (u' - u) := by
    rw [hdd, map_pow, map_pow, map_neg, map_neg]
    ring1
  rw [heq]
  exact dvd_sub (dvd_add (mem_span_singleton.mp hmem) (hA.mul_right u)) (huu.mul_left _)

/-- **Monge's subgroups depend only on `L` and the uniformiser modulo its square** (Monge,
arXiv:1109.4617, p. 6; LMFDB `lf.family_polynomial`): in a tower `M / L / K` with
`M / K` finite Galois, let `f`, `f'` be monic Eisenstein polynomials over `𝒪[K]` with roots `y`,
`y' ∈ 𝒪[L]` generating `L` over `K`, and `y' ≡ y` modulo `y ^ 2`. Then for a uniformiser `ϖ` of `K`,
Monge's subgroups `W_σ` of `f` at `y` and of `f'` at `y'` are the same. -/
lemma mongeSubgroup_eq_of_pow_two_dvd_sub (M : Type*) [Field M] [ValuativeRel M]
    [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra L M] [ValuativeExtension L M]
    [Module.Finite L M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]
    [IsScalarTower K L M] (𝔪 : Ideal 𝒪[K]) (σ : ℕ) (hm : f.Monic) (hf : f.IsEisensteinAt 𝓂[K])
    (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot y) (hgen : K⟮(y : L)⟯ = ⊤) (hm' : f'.Monic)
    (hf' : f'.IsEisensteinAt 𝓂[K]) (hroot' : (f'.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot y')
    (hgen' : K⟮(y' : L)⟯ = ⊤) (hϖ : Irreducible ϖ) (hdvd : y ^ 2 ∣ y' - y) :
    mongeSubgroup ϖ 𝔪 f' y' σ = mongeSubgroup ϖ 𝔪 f y σ := by
  have hp : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hc : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  have h : IsMongeRoot f y (ringChar 𝓀[K]) :=
    isMongeRoot_of_isEisensteinAt hm hf hroot hgen
  have h' : IsMongeRoot f' y' (ringChar 𝓀[K]) :=
    isMongeRoot_of_isEisensteinAt hm' hf' hroot' hgen'
  have hdigits {g : 𝒪[K][X]} (hg : g.IsEisensteinAt 𝓂[K]) :
      ∃ b : ℕ → 𝒪[K], ∀ i < g.natDegree, g.coeff i = ϖ * b i := by
    have hb (i : ℕ) : ∃ b : 𝒪[K], i < g.natDegree → g.coeff i = ϖ * b := by
      by_cases hi : i < g.natDegree
      · have hmem : g.coeff i ∈ 𝓂[K] :=
          hg.mem hi
        rw [hϖ.maximalIdeal_eq, mem_span_singleton] at hmem
        rcases hmem with ⟨b, hb⟩
        exact ⟨b, fun _ ↦ hb⟩
      · exact ⟨0, fun h ↦ absurd h hi⟩
    choose b hb using hb
    exact ⟨b, fun i hi ↦ hb i hi⟩
  rcases hdigits hf with ⟨b, hb⟩
  rcases hdigits hf' with ⟨b', hb'⟩
  have hy : adjoin 𝒪[K] {y} = ⊤ :=
    algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top hf hroot hgen
  have hy' : adjoin 𝒪[K] {y'} = ⊤ :=
    algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top hf' hroot' hgen'
  have hdeg : f.natDegree = Module.finrank K L :=
    natDegree_eq_finrank_of_isEisensteinAt hf hroot hgen
  have hdeg' : f'.natDegree = Module.finrank K L :=
    natDegree_eq_finrank_of_isEisensteinAt hf' hroot' hgen'
  have hyy' : y ∣ y' := by
    rcases hdvd with ⟨w, hw⟩
    exact ⟨1 + y * w, by linear_combination hw⟩
  have hy'y : y' ∣ y :=
    h.irreducible.dvd_symm h'.irreducible hyy'
  have hdvd' : y' ^ 2 ∣ y - y' :=
    (pow_dvd_pow_of_dvd hy'y 2).trans (dvd_sub_comm.mp hdvd)
  exact congrArg AddSubgroup.closure <| subset_antisymm
    (mongeImage_subset_of_pow_two_dvd_sub M 𝔪 σ h' h hy' hy hdeg' hdeg hϖ hb' hb hdvd')
    (mongeImage_subset_of_pow_two_dvd_sub M 𝔪 σ h h' hy hy' hdeg hdeg' hϖ hb hb' hdvd)

/-- **Monge's subgroups inside `K̄`** (Monge, arXiv:1109.4617, p. 6; LMFDB `lf.family_polynomial`):
let `f`, `f'` be monic Eisenstein polynomials over `𝒪[K]` with roots `y`, `y'` in the ring of
integers of a finite separable extension `E` of `K` inside `K̄`, generating `E` over `K`, and
`y' ≡ y` modulo `y ^ 2`. Then Monge's subgroups `W_σ` of `f` at `y` and of `f'` at `y'` are the
same. The tower of `mongeSubgroup_eq_of_pow_two_dvd_sub` is the Galois closure of `E` in `K̄`, with
Tau Ceti's spectral-norm local-field structures. -/
lemma mongeSubgroup_eq_of_pow_two_dvd_sub_visible (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (𝔪 : Ideal 𝒪[K]) (σ : ℕ) (hm : f.Monic)
    (hf : f.IsEisensteinAt 𝓂[K]) (hm' : f'.Monic) (hf' : f'.IsEisensteinAt 𝓂[K])
    (hϖ : Irreducible ϖ) :
    letI : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
    letI : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
    haveI : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
    haveI : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
    ∀ y y' : 𝒪[E], (f.map (algebraMap 𝒪[K] 𝒪[E])).IsRoot y → K⟮(y : E)⟯ = ⊤ →
      (f'.map (algebraMap 𝒪[K] 𝒪[E])).IsRoot y' → K⟮(y' : E)⟯ = ⊤ → y ^ 2 ∣ y' - y →
        mongeSubgroup ϖ 𝔪 f' y' σ = mongeSubgroup ϖ 𝔪 f y σ := by
  let vE : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
  have hE : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
  intro y y' hroot hgen hroot' hgen' hdvd
  let vM : ValuativeRel (galoisClosure K E) := finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (galoisClosure K E) := finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hEM : E ≤ galoisClosure K E :=
    galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
  let a : Algebra E (galoisClosure K E) := (inclusion hEM).toAlgebra
  have hs : IsScalarTower K E (galoisClosure K E) := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension E (galoisClosure K E) := (inclusion hEM).valuativeExtension
  have hfin : Module.Finite E (galoisClosure K E) := .of_restrictScalars_finite K E _
  exact mongeSubgroup_eq_of_pow_two_dvd_sub (galoisClosure K E) 𝔪 σ hm hf hroot hgen hm' hf' hroot'
    hgen' hϖ hdvd

end IsNonarchimedeanLocalField.HerbrandInvariant
