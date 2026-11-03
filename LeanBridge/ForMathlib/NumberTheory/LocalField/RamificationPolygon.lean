import LeanBridge.ForMathlib.NumberTheory.LocalField.DeligneRamificationBreaks
import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeAdditive
import Mathlib.Data.ENat.BigOperators
import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified

/-!
# The ramification polygon of an extension of local fields and the Herbrand function

Let `M / L / K` be a tower of nonarchimedean local fields with `M / K` finite Galois, where `L / K`
need not be normal, `G = Gal(M / K)` and `H = Gal(M / L)`. Let `y` be a generator of `𝒪[L]` over
`𝒪[K]`, `f` a monic polynomial of degree `[L : K]` over `𝒪[K]` with root `y`, and `c_r` the
coefficient of `T ^ r` in `f(y + T)`, so that the ramification polynomial of Monge (arXiv:1109.4617,
Int. J. Number Theory 10 (2014), p. 3) is `Φ(T) = y ^ (-n) f(y T + y) = ∑_r c_r y ^ (r - n) T ^ r`
for a uniformiser `y`, whose Newton polygon is the **ramification polygon** of `L / K`.

The polynomial `f(y + T)` splits over `𝒪[M]` with the roots `σ y - y`, one for each coset `σ H`, and
the Gauss norm is multiplicative, so that the valuations of the `c_r` determine the
`v_M(σ y - y)`. Serre's computation (*Local Fields*, IV, Proposition 3) gives
`v_M(σ y - y) = ∑_{τ ∈ H} i_G(σ τ)`, without using that `L / K` is normal, whence the formula
`min_r ((x + 1) r + v_L(c_r)) = e(L / K) (φ_{L / K}(x) + 1)` for the values `x = φ_{M / L}(t)`,
`t ∈ ℕ`, which include all the natural numbers and all the rams of `L / K`. This is Monge's
Proposition 1 (p. 4). Together with the results of
`LeanBridge.ForMathlib.NumberTheory.LocalField.MongeAdditive`, it bounds the digits of an Eisenstein
polynomial from below (Monge, p. 8): they vanish at the `Z`-points of the Eisenstein diagram (LMFDB
`lf.eisenstein_diagram`) of the Herbrand invariant of `L / K`.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.IsGaussLevel`: the valuation of the Gauss norm of a
  polynomial over a discrete valuation ring.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.addVal_smul_algebraMap_sub_eq_sum` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.min_addVal_smul_algebraMap_sub`: the distance
  between the conjugates of a generator, for an extension `L / K` that need not be normal.
* `IsNonarchimedeanLocalField.HerbrandInvariant.iInf_sum_card_mul_add_addVal_coeff_taylor`: the
  ramification polygon in terms of the ramification groups.
* `IsNonarchimedeanLocalField.HerbrandInvariant.natCast_toNat_mongeLevel` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.natCast_toNat_mongeLevel_of_isEisensteinAt` (LMFDB
  `lf.herbrand_function`, Monge's Proposition 1): Monge's level `N` of an Eisenstein polynomial at
  `m` is `n (φ(m) + 1)`, for Deligne's Herbrand function `φ` of the extension.
* `IsNonarchimedeanLocalField.HerbrandInvariant.sum_card_add_le` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.mean_pointIndex_le`: the lower bound of the
  coefficients of an Eisenstein polynomial given by the ramification polygon.
* `IsNonarchimedeanLocalField.HerbrandInvariant.pointType_ne_Z` (LMFDB `lf.eisenstein_diagram`): the
  digits of an Eisenstein polynomial vanish at the `Z`-points.
* `IsNonarchimedeanLocalField.HerbrandInvariant.natCast_toNat_mongeLevel_visibleHerbrandInvariant`
  and `IsNonarchimedeanLocalField.HerbrandInvariant.pointType_visibleHerbrandInvariant_ne_Z`: the
  same statements for an extension `E` of `K` inside `K̄`, where `M` is the Galois closure of `E`
  and no tower remains in the statement.
-/

open Algebra Finset IntermediateField IsDiscreteValuationRing Polynomial TauCeti IsLocalRing
  LocalFieldsRamification ValuativeRel

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {T R S ι : Type*} [CommRing T] [CommRing R] [CommRing S] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T] {g : R[X]} {π : S} {ϖ : T} {P Q : T[X]} {m a b : ℕ}
  (A : Finset ι) (r : ι → T) (l : ι → ℕ)

lemma map_mongeShift_eq_prod (hfac : g.map (algebraMap R T) = ∏ i ∈ A, (X - C (r i))) :
    (mongeShift g π m).map (algebraMap S T) = (∏ i ∈ A, (X - C (r i))).comp
      (C (algebraMap S T π) + C (algebraMap S T π ^ (m + 1)) * X) := by
  rw [mongeShift, Polynomial.map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, hfac]
  simp only [Polynomial.map_add, Polynomial.map_mul, map_pow, Polynomial.map_pow, map_C, map_X]

variable (ϖ P a) in
/-- `P` has **Gauss level** `a` at `ϖ`: `ϖ ^ a` divides all the coefficients of `P`, and
`ϖ ^ (a + 1)` does not. -/
def IsGaussLevel : Prop :=
  C (ϖ ^ a) ∣ P ∧ ¬C (ϖ ^ (a + 1)) ∣ P

variable [IsDomain T] [IsDiscreteValuationRing T]

lemma IsGaussLevel.mul (hϖ : Irreducible ϖ) (hP : IsGaussLevel ϖ P a) (hQ : IsGaussLevel ϖ Q b) :
    IsGaussLevel ϖ (P * Q) (a + b) := by
  rcases hP.1 with ⟨P₁, rfl⟩
  rcases hQ.1 with ⟨Q₁, rfl⟩
  have hprime : Prime (C ϖ) :=
    prime_C_iff.mpr hϖ.prime
  have hP₁ : ¬C ϖ ∣ P₁ := fun h ↦ hP.2 <| by
    rw [pow_succ, C_mul]
    exact mul_dvd_mul_left _ h
  have hQ₁ : ¬C ϖ ∣ Q₁ := fun h ↦ hQ.2 <| by
    rw [pow_succ, C_mul]
    exact mul_dvd_mul_left _ h
  have heq : C (ϖ ^ a) * P₁ * (C (ϖ ^ b) * Q₁) = C (ϖ ^ (a + b)) * (P₁ * Q₁) := by
    rw [pow_add, C_mul]
    ring1
  rw [IsGaussLevel, heq]
  refine ⟨dvd_mul_right _ _, fun h ↦ ?_⟩
  rw [pow_succ, C_mul, mul_dvd_mul_iff_left (C_ne_zero.mpr (pow_ne_zero _ hϖ.ne_zero))] at h
  exact (hprime.dvd_or_dvd h).elim hP₁ hQ₁

lemma isGaussLevel_prod (hϖ : Irreducible ϖ) (F : ι → T[X])
    (hF : ∀ i ∈ A, IsGaussLevel ϖ (F i) (l i)) : IsGaussLevel ϖ (∏ i ∈ A, F i) (∑ i ∈ A, l i) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨by simp, fun h ↦ hϖ.not_isUnit ?_⟩
    have h₁ : C (ϖ ^ 1) ∣ (1 : T[X]) := by
      simpa using h
    rw [pow_one, C_dvd_iff_dvd_coeff] at h₁
    exact isUnit_of_dvd_one (by simpa using h₁ 0)
  | insert i A hi ih =>
    rw [prod_insert hi, sum_insert hi]
    exact (hF i (mem_insert_self i A)).mul hϖ (ih fun j hj ↦ hF j (mem_insert_of_mem hj))

lemma isGaussLevel_C_add_C_mul_X (hϖ : Irreducible ϖ) {c d : T}
    (ha : (a : ℕ∞) = min (addVal T c) (addVal T d)) : IsGaussLevel ϖ (C c + C d * X) a := by
  have hcoeff (n : ℕ) : C (ϖ ^ n) ∣ C c + C d * X ↔ ϖ ^ n ∣ c ∧ ϖ ^ n ∣ d := by
    rw [C_dvd_iff_dvd_coeff]
    refine ⟨fun h ↦ ⟨by simpa using h 0, by simpa using h 1⟩, fun ⟨h₁, h₂⟩ k ↦ ?_⟩
    rcases k with _ | _ | k
    · simpa using h₁
    · simpa using h₂
    · simp
  refine ⟨(hcoeff a).mpr ⟨(pow_dvd_iff_le_addVal hϖ).mpr (ha.trans_le (min_le_left _ _)),
    (pow_dvd_iff_le_addVal hϖ).mpr (ha.trans_le (min_le_right _ _))⟩, fun h ↦ ?_⟩
  rcases (hcoeff (a + 1)).mp h with ⟨h₁, h₂⟩
  have hle : ((a + 1 : ℕ) : ℕ∞) ≤ a := by
    rw [ha]
    exact le_min ((pow_dvd_iff_le_addVal hϖ).mp h₁) ((pow_dvd_iff_le_addVal hϖ).mp h₂)
  have hle' : a + 1 ≤ a := by
    exact_mod_cast hle
  omega

lemma isGaussLevel_comp (hϖ : Irreducible ϖ) (y d : T)
    (hl : ∀ i ∈ A, (l i : ℕ∞) = min (addVal T (y - r i)) (addVal T d)) :
    IsGaussLevel ϖ ((∏ i ∈ A, (X - C (r i))).comp (C y + C d * X)) (∑ i ∈ A, l i) := by
  rw [Polynomial.prod_comp]
  refine isGaussLevel_prod A l hϖ _ fun i hi ↦ ?_
  have h₁ : (X - C (r i)).comp (C y + C d * X) = C (y - r i) + C d * X := by
    simp only [sub_comp, X_comp, C_comp, C_sub]
    ring1
  rw [h₁]
  exact isGaussLevel_C_add_C_mul_X hϖ (hl i hi)

lemma iInf_addVal_coeff_eq (hϖ : Irreducible ϖ) (hG : IsGaussLevel ϖ P a) :
    ⨅ k, addVal T (P.coeff k) = a := by
  refine le_antisymm ?_ (le_iInf fun k ↦
    (pow_dvd_iff_le_addVal hϖ).mp ((C_dvd_iff_dvd_coeff _ _).mp hG.1 k))
  have h₂ : ¬C (ϖ ^ (a + 1)) ∣ P :=
    hG.2
  rw [C_dvd_iff_dvd_coeff] at h₂
  push Not at h₂
  rcases h₂ with ⟨k₀, hk₀⟩
  rw [pow_dvd_iff_le_addVal hϖ, not_le, Nat.cast_add, Nat.cast_one,
    ENat.lt_add_one_iff (ENat.natCast_ne_top a)] at hk₀
  exact iInf_le_of_le k₀ hk₀

lemma iInf_natCast_mul_add_addVal_coeff_taylor (hϖ : Irreducible ϖ) (y : T) (c : ℕ)
    (hl : ∀ i ∈ A, (l i : ℕ∞) = min (addVal T (y - r i)) c) : ⨅ k, ((c * k : ℕ) : ℕ∞) +
      addVal T ((taylor y (∏ i ∈ A, (X - C (r i)))).coeff k) = (∑ i ∈ A, l i : ℕ) := by
  rw [← iInf_addVal_coeff_eq hϖ (isGaussLevel_comp A r l hϖ y (ϖ ^ c) fun i hi ↦ by
    rw [hl i hi, addVal_pow, addVal_uniformizer hϖ, nsmul_one])]
  refine iInf_congr fun k ↦ ?_
  have hcomp : (∏ i ∈ A, (X - C (r i))).comp (C y + C (ϖ ^ c) * X) =
      (taylor y (∏ i ∈ A, (X - C (r i)))).comp (C (ϖ ^ c) * X) := by
    rw [taylor_apply, comp_assoc]
    simp [add_comm]
  rw [hcomp, comp_C_mul_X_coeff, addVal_mul, addVal_pow, addVal_pow, addVal_uniformizer hϖ,
    add_comm, Nat.cast_mul, mul_comm]
  simp

variable [IsDomain S] [IsDiscreteValuationRing S] in
lemma natCast_mul_mongeLevel_eq_sum (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (hval : ∀ s : S, addVal T (algebraMap S T s) = e • addVal S s)
    (hfac : g.map (algebraMap R T) = ∏ i ∈ A, (X - C (r i)))
    (hl : ∀ i ∈ A, (l i : ℕ∞) = min (addVal T (algebraMap S T π - r i))
      (addVal T (algebraMap S T π ^ (m + 1)))) :
    (e : ℕ∞) * mongeLevel g π m = (∑ i ∈ A, l i : ℕ) := by
  have hG : IsGaussLevel ϖ ((mongeShift g π m).map (algebraMap S T)) (∑ i ∈ A, l i) := by
    rw [map_mongeShift_eq_prod A r hfac]
    exact isGaussLevel_comp A r l hϖ _ _ hl
  rw [mongeLevel, ENat.mul_iInf, ← iInf_addVal_coeff_eq hϖ hG]
  refine iInf_congr fun k ↦ ?_
  rw [emultiplicity_eq_addVal hπ, coeff_map, hval, nsmul_eq_mul]

lemma sum_range_succ_eq_add_sum_Icc (f : ℕ → ℕ) (t : ℕ) :
    ∑ k ∈ range (t + 1), f k = f 0 + ∑ j ∈ Icc 1 t, f j := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, ih, sum_Icc_succ_top t.succ_pos, add_assoc]

variable {K L M : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Field M]
  [ValuativeRel M] [Algebra K L] [Algebra L M] [ValuativeExtension L M] [Algebra K M]
  [ValuativeExtension K M] [IsScalarTower K L M] {y : 𝒪[L]} (t : ℕ) {f : 𝒪[K][X]} {p : ℕ}

variable (K L M) [ValuativeExtension K L] in
lemma isScalarTower_integerRing : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
  IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <| by
    simp only [coe_algebraMap_integerRing]
    exact IsScalarTower.algebraMap_apply K L M (x : K)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Module.Finite K M] (σ : M ≃ₐ[K] M)

variable [ValuativeExtension K L] in
lemma smul_sub_dvd_smul_algebraMap_sub (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) (w : 𝒪[L]) :
    σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y ∣ σ • algebraMap 𝒪[L] 𝒪[M] w -
      algebraMap 𝒪[L] 𝒪[M] w := by
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  rcases (by rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hy]
             exact Algebra.mem_top : ∃ q : 𝒪[K][X], aeval y q = w) with ⟨q, rfl⟩
  rw [← aeval_algebraMap_apply, ← aeval_smul, ← eval_map_algebraMap, ← eval_map_algebraMap]
  exact sub_dvd_eval_sub _ _ _

variable {σ} [ValuativeExtension K L] in
lemma mem_range_of_smul_algebraMap_eq (hy : Algebra.adjoin 𝒪[K] {y} = ⊤)
    (h : σ • algebraMap 𝒪[L] 𝒪[M] y = algebraMap 𝒪[L] 𝒪[M] y) :
    σ ∈ (AlgEquiv.restrictScalarsHom (S := L) K).range := by
  have hw (w : 𝒪[L]) : σ (algebraMap L M (w : L)) = algebraMap L M (w : L) := by
    have h₁ : σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y ∣
        σ • algebraMap 𝒪[L] 𝒪[M] w - algebraMap 𝒪[L] 𝒪[M] w :=
      smul_sub_dvd_smul_algebraMap_sub σ hy w
    rw [h, sub_self, zero_dvd_iff, sub_eq_zero] at h₁
    simpa using congrArg Subtype.val h₁
  have ha (a : L) : σ (algebraMap L M a) = algebraMap L M a := by
    rcases IsFractionRing.div_surjective (A := 𝒪[L]) a with ⟨w₁, w₂, -, rfl⟩
    rw [map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hw w₁) (hw w₂)
  exact ⟨{ σ with commutes' := ha }, AlgEquiv.ext fun x ↦ rfl⟩

variable [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Module.Finite L M] [IsGalois K M]

variable [ValuativeExtension K L]
  [Fintype ((M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range)] in
lemma map_eq_prod_quotient (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) (hf : f.Monic)
    (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0) :
    f.map (algebraMap 𝒪[K] 𝒪[M]) =
      ∏ c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range,
        (X - C (c.out • algebraMap 𝒪[L] 𝒪[M] y)) := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  have hcard : Fintype.card ((M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range) =
      Module.finrank K L := by
    have h₁ : (AlgEquiv.restrictScalarsHom K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range.index *
        Nat.card (M ≃ₐ[L] M) = Nat.card (M ≃ₐ[K] M) := by
      rw [Nat.card_congr (MonoidHom.ofInjective (f := AlgEquiv.restrictScalarsHom (S := L) K)
        (AlgEquiv.restrictScalars_injective K)).toEquiv, Subgroup.index_mul_card]
    rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
      ← Module.finrank_mul_finrank K L M] at h₁
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h₁
  have hinj : Function.Injective fun c : (M ≃ₐ[K] M) ⧸
      (AlgEquiv.restrictScalarsHom (S := L) K).range ↦ c.out • algebraMap 𝒪[L] 𝒪[M] y := by
    intro c c' h
    have h' : c.out • algebraMap 𝒪[L] 𝒪[M] y = c'.out • algebraMap 𝒪[L] 𝒪[M] y :=
      h
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
    refine mem_range_of_smul_algebraMap_eq hy ?_
    rw [mul_smul, ← h', inv_smul_smul]
  have hzero (σ : M ≃ₐ[K] M) :
      (f.map (algebraMap 𝒪[K] 𝒪[M])).eval (σ • algebraMap 𝒪[L] 𝒪[M] y) = 0 := by
    rw [eval_map_algebraMap, aeval_smul, aeval_algebraMap_apply, hroot, map_zero, smul_zero]
  have hne : f.map (algebraMap 𝒪[K] 𝒪[M]) ≠ 0 :=
    (hf.map _).ne_zero
  have hdvd : ∏ c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range,
      (X - C (c.out • algebraMap 𝒪[L] 𝒪[M] y)) ∣ f.map (algebraMap 𝒪[K] 𝒪[M]) := by
    convert (Multiset.prod_X_sub_C_dvd_iff_le_roots hne _).2
      ((Multiset.le_iff_subset (Finset.univ.nodup.map hinj)).2 fun a ha ↦ ?_)
    · simp
    · rcases Multiset.mem_map.1 ha with ⟨c, -, rfl⟩
      exact (mem_roots hne).2 (hzero c.out)
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ fun c _ ↦ monic_X_sub_C _)
    (hf.map _) hdvd ?_
  rw [natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _), hdeg,
    natDegree_prod_of_monic _ _ fun c _ ↦ monic_X_sub_C _, ← hcard]
  simp

variable [TopologicalSpace L] [IsNonarchimedeanLocalField L]

variable (L M m) [IsGalois L M] in
lemma sum_card_lowerRamificationGroup_psiNat : ∑ k ∈ range (psiNat L M m + 1),
    Nat.card (lowerRamificationGroup L M (k : ℤ)) = (m + 1) * TauCeti.ramificationIndex L M := by
  rw [sum_range_succ_eq_add_sum_Icc, (psiNat_eq_iff L M).mp rfl, Nat.cast_zero,
    natCard_lowerRamificationGroup_zero]
  ring1

variable (K M) in
lemma natCast_sum_card_lowerRamificationGroup :
    ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) : ℝ) =
      TauCeti.ramificationIndex K M *
          ((herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) + 1) := by
  have hne : (TauCeti.ramificationIndex K M : ℝ) ≠ 0 := by
    exact_mod_cast TauCeti.ramificationIndex_pos.ne'
  rw [sum_range_succ_eq_add_sum_Icc, coe_herbrand_of_coe_eq_natCast K M t rfl,
    natCard_lowerRamificationGroup_zero, Nat.cast_zero, natCard_lowerRamificationGroup_zero,
    mul_add, mul_div_cancel₀ _ hne, mul_one, add_comm]
  push_cast
  rfl

variable {t} [IsGalois L M] in
lemma coe_herbrand_natCast_of_sum
    (ht : ∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) =
      (m + 1) * TauCeti.ramificationIndex L M) :
    (herbrand L M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) = m := by
  have hne : (TauCeti.ramificationIndex L M : ℝ) ≠ 0 := by
    exact_mod_cast TauCeti.ramificationIndex_pos.ne'
  have h₁ : ((m : ℝ) + 1) * TauCeti.ramificationIndex L M = TauCeti.ramificationIndex L M *
      ((herbrand L M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) + 1) := by
    rw [← natCast_sum_card_lowerRamificationGroup L M t, ht]
    push_cast
    rfl
  rw [mul_comm] at h₁
  linarith [mul_left_cancel₀ hne h₁]

variable {t} in
lemma herbrandOfTower_natCast_of_sum
    (ht : ∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) =
      (m + 1) * TauCeti.ramificationIndex L M) :
    herbrandOfTower K M L m = (herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  have hmax : (⟨max (m : ℝ) (-1), le_max_right (m : ℝ) (-1)⟩ : RamificationIndexDomain) =
      herbrand L M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := by
    refine Subtype.ext ?_
    rw [coe_herbrand_natCast_of_sum ht]
    exact max_eq_left ((by norm_num : (-1 : ℝ) ≤ 0).trans m.cast_nonneg)
  rw [herbrandOfTower, hmax, inverseHerbrand_herbrand]

variable [ValuativeExtension K L]

lemma natDegree_eq_finrank_of_isEisensteinAt (hf : f.IsEisensteinAt 𝓂[K])
    (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot y) (hgen : K⟮(y : L)⟯ = ⊤) :
    f.natDegree = Module.finrank K L := by
  rw [← ramificationIndex_mul_inertiaDegree K L,
    inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top f hf y hroot hgen, mul_one,
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf y hroot hgen]

/-- **The distance between the conjugates of a generator**: in a tower `M / L / K` with `M / K`
finite Galois and `H = Gal(M / L)`, where `L / K` need not be normal, a generator `y` of `𝒪[L]` over
`𝒪[K]` satisfies `v_M(σ y - y) = ∑_{τ ∈ H} i_G(σ τ)` for all `σ ∈ G = Gal(M / K)`. This is the
argument of Serre, *Local Fields*, IV, Proposition 3, which does not need `L / K` to be normal. -/
lemma addVal_smul_algebraMap_sub_eq_sum (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) :
    addVal 𝒪[M] (σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y) = ∑ τ : M ≃ₐ[L] M,
      lowerIndex 𝒪[M] (σ * τ.restrictScalars K) := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  rcases exists_integerRing_adjoin_eq_top K M with ⟨x, hx⟩
  have h₁ : σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y ∣
      (σ • MulSemiringAction.charpoly (M ≃ₐ[L] M) x).eval x := by
    rw [← sub_zero ((σ • MulSemiringAction.charpoly (M ≃ₐ[L] M) x).eval x),
      ← MulSemiringAction.eval_charpoly (M ≃ₐ[L] M) x, ← eval_sub, eval_eq_sum_range]
    refine Finset.dvd_sum fun n _ ↦ Dvd.dvd.mul_right ?_ _
    rcases IsInvariant.isInvariant (A := 𝒪[L]) (G := M ≃ₐ[L] M)
      ((MulSemiringAction.charpoly (M ≃ₐ[L] M) x).coeff n)
      (MulSemiringAction.smul_coeff_charpoly x n) with ⟨w, hw⟩
    rw [coeff_sub, coeff_smul, ← hw]
    exact smul_sub_dvd_smul_algebraMap_sub σ hy w
  have h₂ : (σ • MulSemiringAction.charpoly (M ≃ₐ[L] M) x).eval x ∣
      algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y := by
    rcases (by rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hx]
               exact Algebra.mem_top : ∃ q : 𝒪[K][X], aeval x q = algebraMap 𝒪[L] 𝒪[M] y) with
      ⟨q, hq⟩
    have hg (τ : M ≃ₐ[L] M) :
        (q.map (algebraMap 𝒪[K] 𝒪[M]) - C (algebraMap 𝒪[L] 𝒪[M] y)).eval (τ • x) = 0 := by
      rw [eval_sub, eval_C, eval_map_algebraMap,
        ← AlgEquiv.restrictScalars_smul_integerRing (K := K) τ x, aeval_smul, hq,
        AlgEquiv.restrictScalars_smul_integerRing, smul_algebraMap, sub_self]
    have hinj : Function.Injective fun τ : M ≃ₐ[L] M ↦ τ • x := by
      simpa [Function.comp_def] using
        (smul_left_injective_of_adjoin_singleton_eq_top (G := M ≃ₐ[K] M) hx).comp
          (AlgEquiv.restrictScalars_injective (R := K) (S := L) (A := M))
    rcases MulSemiringAction.charpoly_dvd hinj hg with ⟨h, hh⟩
    have hσg : σ • (q.map (algebraMap 𝒪[K] 𝒪[M]) - C (algebraMap 𝒪[L] 𝒪[M] y)) =
        q.map (algebraMap 𝒪[K] 𝒪[M]) - C (σ • algebraMap 𝒪[L] 𝒪[M] y) := by
      have hmap : (MulSemiringAction.toRingHom (M ≃ₐ[K] M) 𝒪[M] σ).comp (algebraMap 𝒪[K] 𝒪[M]) =
          algebraMap 𝒪[K] 𝒪[M] :=
        RingHom.ext fun r ↦ smul_algebraMap σ r
      rw [smul_sub, smul_C, smul_eq_map, Polynomial.map_map, hmap]
    refine ⟨(σ • h).eval x, ?_⟩
    rw [← eval_mul, ← smul_mul', ← hh, hσg, eval_sub, eval_C, eval_map_algebraMap, hq]
  have key : addVal 𝒪[M] (σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y) =
      addVal 𝒪[M] ((σ • MulSemiringAction.charpoly (M ≃ₐ[L] M) x).eval x) :=
    (addVal_eq_iff_associated _ _).2 <| associated_of_dvd_dvd h₁ (dvd_sub_comm.1 h₂)
  simp_rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, AddValuation.map_sub_swap _ _ x,
    ← AddValuation.map_prod, mul_smul, AlgEquiv.restrictScalars_smul_integerRing,
    ← MulSemiringAction.eval_smul_charpoly]
  exact key

/-- **The truncated distance between the conjugates of a generator**: in a tower `M / L / K` with
`M / K` finite Galois and `H = Gal(M / L)`, for a generator `y` of `𝒪[L]` over `𝒪[K]`, `σ ∈ G` and
`t ∈ ℕ`, `min(v_M(σ y - y), ∑_{τ ∈ H} min(i_H(τ), t)) = ∑_{τ ∈ H} min(i_G(σ τ), t)`. -/
lemma min_addVal_smul_algebraMap_sub (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) : min
    (addVal 𝒪[M] (σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y))
    (∑ τ : M ≃ₐ[L] M, min (lowerIndex 𝒪[M] τ) (t : ℕ∞)) = ∑ τ : M ≃ₐ[L] M,
      min (lowerIndex 𝒪[M] (σ * τ.restrictScalars K)) (t : ℕ∞) := by
  rcases exists_forall_lowerIndex_mul_restrictScalars_le (L := L) σ with ⟨τ₀, hτ₀⟩
  have hsum (g : (M ≃ₐ[K] M) → ℕ∞) : ∑ τ : M ≃ₐ[L] M, g (σ * τ.restrictScalars K) =
      ∑ τ : M ≃ₐ[L] M, g (σ * τ₀.restrictScalars K * τ.restrictScalars K) := by
    refine (Fintype.sum_equiv (Equiv.mulLeft τ₀) _ _ fun τ ↦ ?_).symm
    rw [mul_assoc]
    rfl
  rw [addVal_smul_algebraMap_sub_eq_sum σ hy, hsum (lowerIndex 𝒪[M]),
    hsum fun σ ↦ min (lowerIndex 𝒪[M] σ) (t : ℕ∞)]
  simp_rw [lowerIndex_mul_restrictScalars_of_forall_le _ hτ₀]
  rcases le_total (lowerIndex 𝒪[M] (σ * τ₀.restrictScalars K)) (t : ℕ∞) with h | h
  · rw [min_eq_left (sum_le_sum fun τ _ ↦ min_le_min_left _ h)]
    exact sum_congr rfl fun τ _ ↦ (min_eq_left ((min_le_right _ _).trans h)).symm
  · rw [min_eq_right (sum_le_sum fun τ _ ↦ min_le_min_left _ h)]
    exact sum_congr rfl fun τ _ ↦ by rw [min_assoc, min_eq_right h]

variable (K) [Fintype ((M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range)] in
lemma exists_natCast_eq_min (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) :
    ∃ l : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range → ℕ,
      (∀ c, (l c : ℕ∞) =
        min (addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y - c.out • algebraMap 𝒪[L] 𝒪[M] y))
          ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞)) ∧
      ∑ c, l c = ∑ k ∈ range t, Nat.card (lowerRamificationGroup K M (k : ℤ)) := by
  classical
  have hA : ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) =
      ∑ τ : M ≃ₐ[L] M, min (lowerIndex 𝒪[M] τ) (t : ℕ∞) := by
    rw [sum_min_lowerIndex_natCast]
    simp only [lowerRamificationGroup_def]
    push_cast
    rfl
  have hne (c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range) :
      ∑ τ : M ≃ₐ[L] M, min (lowerIndex 𝒪[M] (c.out * τ.restrictScalars K)) (t : ℕ∞) ≠ ⊤ :=
    ENat.sum_ne_top.mpr fun τ _ ↦ ne_top_of_le_ne_top (ENat.natCast_ne_top t) (min_le_right _ _)
  have hout (g : (M ≃ₐ[K] M) → ℕ∞) :
      ∑ c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range,
        ∑ τ : M ≃ₐ[L] M, g (c.out * τ.restrictScalars K) = ∑ σ, g σ := by
    rw [← Finset.sum_fiberwise univ (QuotientGroup.mk
      (s := (AlgEquiv.restrictScalarsHom (S := L) K).range)) g]
    refine Fintype.sum_congr _ _ fun c ↦ ?_
    refine Finset.sum_nbij (fun τ ↦ c.out * τ.restrictScalars K) (fun τ _ ↦ ?_)
      (fun τ₁ _ τ₂ _ h ↦ ?_) (fun σ hσ ↦ ?_) fun _ _ ↦ rfl
    · have hτ : τ.restrictScalars K ∈ (AlgEquiv.restrictScalarsHom (S := L) K).range :=
        ⟨τ, rfl⟩
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [QuotientGroup.mk_mul_of_mem _ hτ, QuotientGroup.out_eq']
    · exact AlgEquiv.restrictScalars_injective K (mul_left_cancel h)
    · have hσ' : (QuotientGroup.mk σ : (M ≃ₐ[K] M) ⧸
          (AlgEquiv.restrictScalarsHom (S := L) K).range) = c :=
        (mem_filter.1 hσ).2
      have hmem : c.out⁻¹ * σ ∈ (AlgEquiv.restrictScalarsHom (S := L) K).range :=
        QuotientGroup.eq.1 (by rw [QuotientGroup.out_eq', hσ'])
      rcases hmem with ⟨τ, hτ⟩
      refine ⟨τ, mem_coe.2 (mem_univ τ), ?_⟩
      beta_reduce
      rw [← AlgEquiv.restrictScalarsHom_apply K τ, hτ, mul_inv_cancel_left]
  choose l hl using fun c ↦ ENat.ne_top_iff_exists.mp (hne c)
  refine ⟨l, fun c ↦ ?_, ?_⟩
  · rw [hl c, AddValuation.map_sub_swap, hA, min_addVal_smul_algebraMap_sub t _ hy]
  · have h₁ : ((∑ c, l c : ℕ) : ℕ∞) =
        ((∑ k ∈ range t, Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) : ℕ∞) := by
      push_cast
      simp only [hl]
      rw [hout fun σ ↦ min (lowerIndex 𝒪[M] σ) (t : ℕ∞), sum_min_lowerIndex_natCast]
      simp only [lowerRamificationGroup_def]
    exact_mod_cast h₁

/-- **The ramification polygon and the Herbrand function** (Monge, arXiv:1109.4617, Proposition 1,
p. 4, for an extension `L / K` that need not be normal): in a tower `M / L / K` with `M / K` finite
Galois, `G = Gal(M / K)` and `H = Gal(M / L)`, let `y` generate `𝒪[L]` over `𝒪[K]` and `f` be a
monic polynomial of degree `[L : K]` over `𝒪[K]` with root `y`, and let `c_r` be the coefficient of
`T ^ r` in `f(y + T)`. Then for all `t ∈ ℕ`,
`min_r ((∑_{k < t} #H_k) r + e(M / L) v_L(c_r)) = ∑_{k < t} #G_k`. Since
`∑_{k ≤ t} #H_k = e(M / L) (φ_{M / L}(t) + 1)` and `∑_{k ≤ t} #G_k = e(M / K) (φ_{M / K}(t) + 1)`,
this is the formula `min_r ((x + 1) r + v_L(c_r)) = e(L / K) (φ_{L / K}(x) + 1)` for the values
`x = φ_{M / L}(t)`, which include all the rams of `L / K`. -/
lemma iInf_sum_card_mul_add_addVal_coeff_taylor (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) (hf : f.Monic)
    (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0) : ⨅ r,
    ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ))) * r : ℕ) +
      TauCeti.ramificationIndex L M •
          addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff r) =
            (∑ k ∈ range t, Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) := by
  classical
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[M] with ⟨ϖ', hϖ'⟩
  rcases exists_natCast_eq_min (M := M) K t hy with ⟨l, hl, hsum⟩
  rw [← hsum, ← iInf_natCast_mul_add_addVal_coeff_taylor univ _ l hϖ' (algebraMap 𝒪[L] 𝒪[M] y) _
    fun c _ ↦ hl c, ← map_eq_prod_quotient hy hf hdeg hroot]
  refine iInf_congr fun r ↦ ?_
  have hmap : taylor (algebraMap 𝒪[L] 𝒪[M] y) (f.map (algebraMap 𝒪[K] 𝒪[M])) =
      (taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).map (algebraMap 𝒪[L] 𝒪[M]) := by
    rw [map_taylor, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  rw [hmap, coeff_map, TauCeti.addVal_algebraMap]

variable {t} in
lemma natCast_mul_mongeLevel_eq (hyπ : Irreducible y) (hy : Algebra.adjoin 𝒪[K] {y} = ⊤)
    (hf : f.Monic) (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0)
    (ht : ∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) =
      (m + 1) * TauCeti.ramificationIndex L M) :
    (TauCeti.ramificationIndex L M : ℕ∞) * mongeLevel f y m =
      (∑ k ∈ range t, Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) := by
  classical
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[M] with ⟨ϖ', hϖ'⟩
  rcases exists_natCast_eq_min (M := M) K t hy with ⟨l, hl, hsum⟩
  have hv : addVal 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] y ^ (m + 1)) =
      ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ)) : ℕ) : ℕ∞) := by
    rw [addVal_pow, TauCeti.addVal_algebraMap, addVal_uniformizer hyπ, ht, nsmul_one, nsmul_eq_mul]
    push_cast
    rfl
  rw [natCast_mul_mongeLevel_eq_sum univ _ l hyπ hϖ' TauCeti.addVal_algebraMap
    (map_eq_prod_quotient hy hf hdeg hroot) fun c _ ↦ by rw [hv]; exact hl c, hsum]

variable (m) in
/-- **Monge's Proposition 1 for a tower** (Monge, arXiv:1109.4617, Proposition 1, p. 4, for an
extension `L / K` that need not be normal): in a tower `M / L / K` with `M / K` finite Galois, let
`y` be a uniformiser of `L` generating `𝒪[L]` over `𝒪[K]`, and `f` a monic polynomial of degree
`[L : K]` over `𝒪[K]` with root `y`. For all `m ∈ ℕ`, Monge's level `N` of `f` at `y` and `m` is
`e(L / K) (φ_{L / K}(m) + 1)`, for Deligne's Herbrand function `φ_{L / K} = φ_{M / K} ∘ ψ_{M / L}`.
-/
lemma natCast_toNat_mongeLevel (hyπ : Irreducible y) (hy : Algebra.adjoin 𝒪[K] {y} = ⊤)
    (hf : f.Monic) (hdeg : f.natDegree = Module.finrank K L) (hroot : aeval y f = 0) :
    ((mongeLevel f y m).toNat : ℝ) =
      TauCeti.ramificationIndex K L * (herbrandOfTower K M L m + 1) := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  have ht : ∑ k ∈ range (psiNat L M m + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) =
      (m + 1) * TauCeti.ramificationIndex L M :=
    sum_card_lowerRamificationGroup_psiNat m L M
  generalize psiNat L M m = t at ht
  have hb : (TauCeti.ramificationIndex L M : ℝ) ≠ 0 := by
    exact_mod_cast TauCeti.ramificationIndex_pos.ne'
  have hlevel : (TauCeti.ramificationIndex L M : ℕ∞) * mongeLevel f y m =
      (∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) :=
    natCast_mul_mongeLevel_eq hyπ hy hf hdeg hroot ht
  rcases ENat.ne_top_iff_exists.mp (fun htop ↦ by
    rw [htop, ENat.mul_top (by exact_mod_cast TauCeti.ramificationIndex_pos.ne')] at hlevel
    exact ENat.natCast_ne_top _ hlevel.symm : mongeLevel f y m ≠ ⊤) with ⟨N, hN⟩
  rw [← hN] at hlevel ⊢
  have hreal : (TauCeti.ramificationIndex L M : ℝ) * N =
      (TauCeti.ramificationIndex K L : ℝ) * TauCeti.ramificationIndex L M *
        ((herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) + 1) := by
    have h₁ : ((∑ k ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) : ℝ) =
        (TauCeti.ramificationIndex K L : ℝ) * TauCeti.ramificationIndex L M *
          ((herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) + 1) := by
      rw [natCast_sum_card_lowerRamificationGroup, ramificationIndex_tower (K := K) (L := L) M,
        Nat.cast_mul]
    rw [← h₁]
    exact_mod_cast hlevel
  rw [herbrandOfTower_natCast_of_sum ht, ENat.toNat_natCast]
  refine mul_left_cancel₀ hb (hreal.trans ?_)
  ring1

lemma herbrandFunction_herbrandInvariantOfTower_herbrandOfSubgroup :
    (herbrandInvariantOfTower K M L).herbrandFunction
      (herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range t) =
        herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := by
  rw [← herbrandFunction_ofRams_herbrandOfSubgroup K M
    (AlgEquiv.restrictScalarsHom K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range (inertiaDegree K L)
    inertiaDegree_pos (t := t)]
  simp only [herbrandInvariantOfTower,
    relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom]

variable (m) in
lemma herbrandFunction_herbrandInvariantOfTower :
    (herbrandInvariantOfTower K M L).herbrandFunction m = herbrandOfTower K M L m := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  have ht : ∑ k ∈ range (psiNat L M m + 1), Nat.card (lowerRamificationGroup L M (k : ℤ)) =
      (m + 1) * TauCeti.ramificationIndex L M :=
    sum_card_lowerRamificationGroup_psiNat m L M
  generalize psiNat L M m = t at ht
  have hsub : ((herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range t : ℚ) : ℝ) =
      m := by
    rw [herbrandOfSubgroup_range_restrictScalarsHom, coe_herbrand_natCast_of_sum ht]
  rw [herbrandOfTower_natCast_of_sum ht, ← hsub,
    herbrandFunction_herbrandInvariantOfTower_herbrandOfSubgroup]

variable (m) in
/-- **Monge's Proposition 1** (Monge, arXiv:1109.4617, Proposition 1, p. 4, for an extension `L / K`
that need not be normal): let `f` be a monic Eisenstein polynomial over `𝒪[K]` with a root
`y ∈ 𝒪[L]` generating `L` over `K`, in a tower `M / L / K` with `M / K` finite Galois. For all
`m ∈ ℕ`, Monge's level of `f` at `y` and `m` is `n (φ(m) + 1)`, for the degree `n` of `f` and the
Herbrand function `φ` (LMFDB `lf.herbrand_function`) of the Herbrand invariant of `L / K`. -/
lemma natCast_toNat_mongeLevel_of_isEisensteinAt (hm : f.Monic) (hf : f.IsEisensteinAt 𝓂[K])
    (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot y) (hgen : K⟮(y : L)⟯ = ⊤) :
    ((mongeLevel f y m).toNat : ℝ) =
      f.natDegree * ((herbrandInvariantOfTower K M L).herbrandFunction m + 1) := by
  rw [herbrandFunction_herbrandInvariantOfTower,
    natCast_toNat_mongeLevel (M := M) m (irreducible_of_eisenstein_adjoin_eq_top f hf y hroot hgen)
      (algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top hf hroot hgen) hm
      (natDegree_eq_finrank_of_isEisensteinAt hf hroot hgen) (by
        rw [aeval_def, eval₂_eq_eval_map]
        exact hroot),
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf y hroot hgen]

/-- **The ramification polygon bounds the coefficients of `f` from below** (Monge, arXiv:1109.4617,
p. 8): in a tower `M / L / K` with `M / K` finite Galois, `G = Gal(M / K)` and `H = Gal(M / L)`, let
`y` be a uniformiser of `L` generating `𝒪[L]` over `𝒪[K]` and a root of `f`. If `1 ≤ i ≤ n` and
`binom(i, p ^ q)` is prime to `p`, then for all `t ∈ ℕ`,
`∑_{k < t} #G_k + e(M / L) p ^ q ≤ (∑_{k < t} #H_k) p ^ q + e(M / L) (n v_K(f_i) + i)`. -/
lemma sum_card_add_le (h : IsMongeRoot f y p) (hy : Algebra.adjoin 𝒪[K] {y} = ⊤)
    (hdeg : f.natDegree = Module.finrank K L) {i q : ℕ} (hi : i ∈ Icc 1 f.natDegree)
    (hcop : p.Coprime (i.choose (p ^ q))) (hp : p ≠ 0) :
    ((∑ k ∈ range t, Nat.card (lowerRamificationGroup K M (k : ℤ)) +
        TauCeti.ramificationIndex L M * p ^ q : ℕ) : ℕ∞) ≤
      ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ))) * p ^ q : ℕ) +
        TauCeti.ramificationIndex L M • (f.natDegree • addVal 𝒪[K] (f.coeff i) + i) := by
  have h₁ : ((∑ k ∈ range t, Nat.card (lowerRamificationGroup K M (k : ℤ)) : ℕ) : ℕ∞) ≤
      ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ))) * p ^ q : ℕ) +
        TauCeti.ramificationIndex L M •
          addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff (p ^ q)) := by
    rw [← iInf_sum_card_mul_add_addVal_coeff_taylor t hy h.monic hdeg h.aeval_eq_zero]
    exact iInf_le (fun r ↦
      ((∑ k ∈ range t, Nat.card (lowerRamificationGroup L M (k : ℤ))) * r : ℕ) +
        TauCeti.ramificationIndex L M •
          addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff r)) (p ^ q)
  have h₂ : addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff (p ^ q)) + (p ^ q : ℕ) ≤
      f.natDegree • addVal 𝒪[K] (f.coeff i) + i := by
    refine (addVal_coeff_taylor_add_le h (pow_ne_zero q hp) hi).trans_eq ?_
    rcases h.isUnit_natCast hcop with ⟨w, hw⟩
    have h₄ : algebraMap 𝒪[K] 𝒪[L] ((i.choose (p ^ q) : 𝒪[K]) * f.coeff i) * y ^ i =
        (w : 𝒪[L]) * (algebraMap 𝒪[K] 𝒪[L] (f.coeff i) * y ^ i) := by
      rw [hw, RingHom.map_mul, map_natCast, mul_assoc]
    rw [h₄, addVal_mul, addVal_eq_zero_of_unit, zero_add, addVal_mul, addVal_pow,
      addVal_uniformizer h.irreducible, nsmul_one, h.addVal_algebraMap]
  have h₃ : TauCeti.ramificationIndex L M •
      (addVal 𝒪[L] ((taylor y (f.map (algebraMap 𝒪[K] 𝒪[L]))).coeff (p ^ q)) + (p ^ q : ℕ)) ≤
      TauCeti.ramificationIndex L M • (f.natDegree • addVal 𝒪[K] (f.coeff i) + i) :=
    nsmul_le_nsmul_right h₂ _
  rw [nsmul_add] at h₃
  refine le_trans ?_ (add_le_add_right h₃ _)
  rw [← add_assoc, Nat.cast_add]
  refine add_le_add h₁ ?_
  simp

lemma exists_ram_eq_herbrandOfSubgroup {k : ℕ} (hk₀ : 1 ≤ k)
    (hk : k ≤ (herbrandInvariantOfTower K M L).w) : ∃ t, (herbrandInvariantOfTower K M L).ram k =
      herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range t ∧
      ((herbrandInvariantOfTower K M L).swanSlope k : ℝ) =
        herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := by
  have hmem : (herbrandInvariantOfTower K M L).ram k ∈
      ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range :=
    ram_ofRams_mem _ _ _ _ _ _ _ _ hk₀ hk
  rcases Multiset.mem_sum.mp hmem with ⟨i, -, hi⟩
  have hr : (herbrandInvariantOfTower K M L).ram k =
      herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range (i + 1) :=
    Multiset.eq_of_mem_replicate hi
  refine ⟨i + 1, hr, ?_⟩
  rw [← herbrandFunction_herbrandInvariantOfTower_herbrandOfSubgroup (L := L) _, ← hr]
  rcases hk.lt_or_eq with h | h
  · rw [herbrandFunction_of_mem_Icc _ h ⟨le_rfl, ram_le_ram _ (Nat.le_succ _)⟩, sub_self, zero_div,
      add_zero]
  · rw [herbrandFunction_of_le _ (h ▸ le_rfl), ← h, sub_self, zero_div, add_zero]

/-- **The digits of an Eisenstein polynomial vanish below its bands** (Monge, arXiv:1109.4617, p. 8
and the first part of Proposition 3): let `f` be a monic Eisenstein polynomial of degree `n` over
`𝒪[K]` with a root `y ∈ 𝒪[L]` generating `L` over `K`, in a tower `M / L / K` with `M / K` finite
Galois. If `i < n` and `v_K(f_i) ≤ j + 1`, then `m_k ≤ (j n + i) / n` for the index `k` of `i` and
the means `m_k` (LMFDB `lf.rams`) of the Herbrand invariant of `L / K`. -/
lemma mean_pointIndex_le (hm : f.Monic) (hf : f.IsEisensteinAt 𝓂[K])
    (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot y) (hgen : K⟮(y : L)⟯ = ⊤) {i j : ℕ}
    (hi : i < f.natDegree) (hj : addVal 𝒪[K] (f.coeff i) ≤ (j + 1 : ℕ)) :
    (herbrandInvariantOfTower K M L).mean ((herbrandInvariantOfTower K M L).pointIndex i) ≤
      ((j * f.natDegree + i : ℕ) : ℚ) / f.natDegree := by
  have hL : IsGalois L M :=
    IsGalois.tower_top_of_isGalois K L M
  have hp : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hc : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  have h : IsMongeRoot f y (ringChar 𝓀[K]) :=
    isMongeRoot_of_isEisensteinAt hm hf hroot hgen
  have he : TauCeti.ramificationIndex K L = f.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf y hroot hgen
  have hn : (herbrandInvariantOfTower K M L).ε *
      ringChar 𝓀[K] ^ (herbrandInvariantOfTower K M L).w = f.natDegree :=
    (ε_mul_pow_w_herbrandInvariantOfTower K M L).trans he
  have hnpos : (0 : ℝ) < f.natDegree := by
    exact_mod_cast h.natDegree_pos
  rcases (Nat.dvd_prime_pow hp.out).mp (Nat.gcd_dvd_right i
    (ringChar 𝓀[K] ^ (herbrandInvariantOfTower K M L).w)) with ⟨q, hq, hgcd⟩
  have hk :
      (herbrandInvariantOfTower K M L).pointIndex i = (herbrandInvariantOfTower K M L).w - q := by
    rw [pointIndex, hgcd, padicValNat.prime_pow]
  rw [hk]
  rcases eq_or_ne q (herbrandInvariantOfTower K M L).w with hqw | hqw
  · rw [hqw, Nat.sub_self, mean, Icc_eq_empty (by omega), sum_empty]
    positivity
  have hlt : q < (herbrandInvariantOfTower K M L).w :=
    lt_of_le_of_ne hq hqw
  rcases (hgcd ▸ Nat.gcd_dvd_left i (ringChar 𝓀[K] ^ (herbrandInvariantOfTower K M L).w) :
    ringChar 𝓀[K] ^ q ∣ i) with ⟨u, hu⟩
  have hcop : (ringChar 𝓀[K]).Coprime u := by
    refine hp.out.coprime_iff_not_dvd.mpr fun hd ↦ ?_
    have h₁ :
        ringChar 𝓀[K] ^ (q + 1) ∣ i.gcd (ringChar 𝓀[K] ^ (herbrandInvariantOfTower K M L).w) :=
      Nat.dvd_gcd (by
        rw [hu, pow_succ]
        exact mul_dvd_mul_left _ hd) (pow_dvd_pow _ hlt)
    rw [hgcd] at h₁
    have h₂ : q + 1 ≤ q :=
      (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h₁
    omega
  have hchoose : (ringChar 𝓀[K]).Coprime (i.choose (ringChar 𝓀[K] ^ q)) :=
    hu ▸ coprime_choose_pow_mul q hcop
  have hi₀ : i ≠ 0 := by
    rintro rfl
    rcases Nat.mul_eq_zero.mp hu.symm with h₁ | h₁
    · exact pow_ne_zero q hp.out.ne_zero h₁
    · rw [h₁, Nat.coprime_zero_right] at hcop
      exact hp.out.one_lt.ne' hcop
  have hi' : i ∈ Icc 1 f.natDegree :=
    mem_Icc.mpr ⟨Nat.pos_of_ne_zero hi₀, hi.le⟩
  rcases exists_ram_eq_herbrandOfSubgroup (K := K) (M := M) (L := L)
    (k := (herbrandInvariantOfTower K M L).w - q) (by omega) (by omega) with ⟨t, hr, hs⟩
  have hw : ringChar 𝓀[K] ^ (herbrandInvariantOfTower K M L).w =
      ringChar 𝓀[K] ^ ((herbrandInvariantOfTower K M L).w - q) * ringChar 𝓀[K] ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hq]
  generalize hk' : (herbrandInvariantOfTower K M L).w - q = k at hr hs hw ⊢
  have hle :
      f.natDegree • addVal 𝒪[K] (f.coeff i) + i ≤ ((f.natDegree * (j + 1) + i : ℕ) : ℕ∞) := by
    rw [Nat.cast_add]
    refine add_le_add ((nsmul_le_nsmul_right hj _).trans_eq ?_) le_rfl
    rw [nsmul_eq_mul, Nat.cast_mul]
  have hnat : ∑ a ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (a : ℤ)) +
      TauCeti.ramificationIndex L M * ringChar 𝓀[K] ^ q ≤
      (∑ a ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (a : ℤ))) * ringChar 𝓀[K] ^ q +
        TauCeti.ramificationIndex L M * (f.natDegree * (j + 1) + i) := by
    exact_mod_cast (sum_card_add_le (M := M) (t + 1) h
      (algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top hf hroot hgen)
      (natDegree_eq_finrank_of_isEisensteinAt hf hroot hgen) hi' hchoose hp.out.ne_zero).trans
      (add_le_add le_rfl ((nsmul_le_nsmul_right hle _).trans_eq
        (by rw [nsmul_eq_mul, ← Nat.cast_mul] :
          _ = ((TauCeti.ramificationIndex L M * (f.natDegree * (j + 1) + i) : ℕ) : ℕ∞))))
  have hreal : ((∑ a ∈ range (t + 1), Nat.card (lowerRamificationGroup K M (a : ℤ)) : ℕ) : ℝ) +
      TauCeti.ramificationIndex L M * (ringChar 𝓀[K] ^ q : ℕ) ≤
      ((∑ a ∈ range (t + 1), Nat.card (lowerRamificationGroup L M (a : ℤ)) : ℕ) : ℝ) *
        (ringChar 𝓀[K] ^ q : ℕ) + TauCeti.ramificationIndex L M * (f.natDegree * (j + 1) + i) := by
    exact_mod_cast hnat
  have hr' : (herbrand L M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ : ℝ) =
      ((herbrandInvariantOfTower K M L).ram k : ℝ) := by
    rw [hr]
    exact (herbrandOfSubgroup_range_restrictScalarsHom K M t L).symm
  rw [natCast_sum_card_lowerRamificationGroup K M t, natCast_sum_card_lowerRamificationGroup L M t,
    ramificationIndex_tower (K := K) (L := L) M, he, ← hs, hr'] at hreal
  have he' : (0 : ℝ) < TauCeti.ramificationIndex L M := by
    exact_mod_cast TauCeti.ramificationIndex_pos
  push_cast at hreal
  have hfinal : (f.natDegree : ℝ) * ((herbrandInvariantOfTower K M L).swanSlope k : ℝ) ≤
      ((herbrandInvariantOfTower K M L).ram k : ℝ) * ((ringChar 𝓀[K] : ℕ) : ℝ) ^ q +
        f.natDegree * j + i := by
    refine le_of_mul_le_mul_left ?_ he'
    linarith
  have hε : ((herbrandInvariantOfTower K M L).ε : ℝ) ≠ 0 := by
    exact_mod_cast (herbrandInvariantOfTower K M L).ε_pos.ne'
  have hpk : ((ringChar 𝓀[K] : ℕ) : ℝ) ^ k ≠ 0 := by
    exact_mod_cast pow_ne_zero k hp.out.ne_zero
  have htiny : ((herbrandInvariantOfTower K M L).tinyRam k : ℝ) * f.natDegree =
      ((herbrandInvariantOfTower K M L).ram k : ℝ) * ((ringChar 𝓀[K] : ℕ) : ℝ) ^ q := by
    rw [tinyRam, ← hn, hw]
    push_cast
    field_simp
  have hmean : ((herbrandInvariantOfTower K M L).mean k : ℝ) =
      ((herbrandInvariantOfTower K M L).swanSlope k : ℝ) -
        ((herbrandInvariantOfTower K M L).tinyRam k : ℝ) := by
    rw [tinyRam_eq_swanSlope_sub_mean _ hp.out.ne_zero]
    push_cast
    ring1
  refine (Rat.cast_le (K := ℝ)).mp ?_
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, le_div_iff₀ hnpos, hmean, sub_mul, htiny]
  push_cast
  linarith

/-- **The `Z`-points of an Eisenstein polynomial have zero digits** (Monge, arXiv:1109.4617, p. 8):
let `f` be a monic Eisenstein polynomial of degree `n` over `𝒪[K]` with a root `y ∈ 𝒪[L]` generating
`L` over `K`, in a tower `M / L / K` with `M / K` finite Galois. If `σ = j n + i`, `0 ≤ i < n`, and
`v_K(f_i) ≤ j + 1`, that is the digit of `f_i` at `π_K ^ (j + 1)` or a lower one does not vanish,
then `P_σ` is not a `Z`-point of the Eisenstein diagram (LMFDB `lf.eisenstein_diagram`) of the
Herbrand invariant of `L / K`. -/
lemma pointType_ne_Z (hm : f.Monic) (hf : f.IsEisensteinAt 𝓂[K])
    (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot y) (hgen : K⟮(y : L)⟯ = ⊤) {σ : ℕ}
    (hσ : addVal 𝒪[K] (f.coeff (σ % f.natDegree)) ≤ (σ / f.natDegree + 1 : ℕ)) :
    (herbrandInvariantOfTower K M L).pointType σ ≠ .Z := by
  have he : (herbrandInvariantOfTower K M L).ramificationIndex = f.natDegree :=
    (ε_mul_pow_w_herbrandInvariantOfTower K M L).trans
      (ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf y hroot hgen)
  have hpos : 0 < f.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf y hroot hgen ▸
      TauCeti.ramificationIndex_pos
  have hmean : (herbrandInvariantOfTower K M L).mean
      ((herbrandInvariantOfTower K M L).pointIndex (σ % f.natDegree)) ≤
      ((σ / f.natDegree * f.natDegree + σ % f.natDegree : ℕ) : ℚ) / f.natDegree :=
    mean_pointIndex_le hm hf hroot hgen (Nat.mod_lt σ hpos) hσ
  rw [Nat.div_add_mod' σ f.natDegree] at hmean
  rcases eq_or_ne σ 0 with rfl | h₀
  · rw [pointType_zero]
    exact nofun
  rw [pointType, ite_eq_right h₀, point, he, ite_eq_right (not_lt.mpr hmean)]
  split_ifs <;> exact nofun

variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]

lemma visibleHerbrandInvariant_eq_herbrandInvariantOfTower :
    letI : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
    letI : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
    haveI : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
    haveI : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
    letI : ValuativeRel (galoisClosure K E) := finiteIntermediateFieldValuativeRel K _ _
    letI : TopologicalSpace (galoisClosure K E) := finiteIntermediateFieldTopology K _ _
    haveI : IsNonarchimedeanLocalField (galoisClosure K E) :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ _
    haveI : ValuativeExtension K (galoisClosure K E) :=
      finiteIntermediateField_valuativeExtension K _ _
    haveI hEM : E ≤ galoisClosure K E :=
      galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
    letI : Algebra E (galoisClosure K E) := (inclusion hEM).toAlgebra
    haveI : IsScalarTower K E (galoisClosure K E) := .of_algebraMap_eq fun _ ↦ rfl
    haveI : ValuativeExtension E (galoisClosure K E) := (inclusion hEM).valuativeExtension
    haveI : Module.Finite E (galoisClosure K E) := .of_restrictScalars_finite K E _
    visibleHerbrandInvariant E = herbrandInvariantOfTower K (galoisClosure K E) E := by
  rw [visibleHerbrandInvariant, herbrandInvariantOfTower]
  congr 1
  rw [visibleRams, fixingSubgroup_preimage_eq_range_restrictScalarsHom]

variable (m) [Algebra.IsSeparable K E] in
/-- **Monge's Proposition 1 inside `K̄`** (Monge, arXiv:1109.4617, Proposition 1, p. 4): let `f` be
a monic Eisenstein polynomial over `𝒪[K]` with a root `y` in the ring of integers of a finite
separable extension `E` of `K` inside `K̄`, generating `E` over `K`. Then Monge's level of `f` at
`y` and `m` is `n (φ(m) + 1)`, for the Herbrand function `φ` of the Herbrand invariant of `E / K`.
The tower of `natCast_toNat_mongeLevel_of_isEisensteinAt` is the Galois closure of `E` in `K̄`, with
Tau Ceti's spectral-norm local-field structures. -/
lemma natCast_toNat_mongeLevel_visibleHerbrandInvariant (hm : f.Monic)
    (hf : f.IsEisensteinAt 𝓂[K]) :
    letI : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
    letI : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
    haveI : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
    haveI : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
    ∀ y : 𝒪[E], (f.map (algebraMap 𝒪[K] 𝒪[E])).IsRoot y → K⟮(y : E)⟯ = ⊤ →
      ((mongeLevel f y m).toNat : ℝ) =
        f.natDegree * ((visibleHerbrandInvariant E).herbrandFunction m + 1) := by
  let vE : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
  have hE : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
  intro y hroot hgen
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
  rw [visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
  exact natCast_toNat_mongeLevel_of_isEisensteinAt m hm hf hroot hgen

variable [Algebra.IsSeparable K E] in
/-- **The `Z`-points inside `K̄`** (Monge, arXiv:1109.4617, p. 8): let `f` be a monic Eisenstein
polynomial of degree `n` over `𝒪[K]` with a root `y` in the ring of integers of a finite separable
extension `E` of `K` inside `K̄`, generating `E` over `K`. If `σ = j n + i`, `0 ≤ i < n`, and
`v_K(f_i) ≤ j + 1`, then `P_σ` is not a `Z`-point of the Eisenstein diagram (LMFDB
`lf.eisenstein_diagram`) of the Herbrand invariant of `E / K`. -/
lemma pointType_visibleHerbrandInvariant_ne_Z (hm : f.Monic) (hf : f.IsEisensteinAt 𝓂[K]) {σ : ℕ}
    (hσ : addVal 𝒪[K] (f.coeff (σ % f.natDegree)) ≤ (σ / f.natDegree + 1 : ℕ)) :
    letI : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
    letI : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
    haveI : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
    haveI : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
    ∀ y : 𝒪[E], (f.map (algebraMap 𝒪[K] 𝒪[E])).IsRoot y → K⟮(y : E)⟯ = ⊤ →
      (visibleHerbrandInvariant E).pointType σ ≠ .Z := by
  let vE : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
  have hE : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
  intro y hroot hgen
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
  rw [visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
  exact pointType_ne_Z hm hf hroot hgen hσ

end IsNonarchimedeanLocalField.HerbrandInvariant
