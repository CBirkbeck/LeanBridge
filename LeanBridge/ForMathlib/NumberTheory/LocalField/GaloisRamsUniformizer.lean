import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeUnramifiedBase

/-!
# The rams of a Galois extension through a uniformiser

Let `L / K` be a finite Galois extension of nonarchimedean local fields with group `G`, lower
ramification groups `G_i` and a uniformiser `π_L`. LMFDB `lf.rams` states that a ram of `L / K` is
any number of the form `v_L(σ(π_L) - π_L) - 1` for some `σ ≠ 1` in the wild inertia group of `G`,
so that the rams of a Galois extension are positive integers. This file proves it, for the rams
`IsNonarchimedeanLocalField.ramsOfIsGalois`, the positive lower ramification jumps `i`, repeated
`log_p [G_i : G_{i + 1}]` times, and the wild inertia group `G_1`.

For `σ` in the inertia group `G_0`, Serre's lower index `i_G(σ) = min_x v_L(σ x - x)` is
`v_L(σ π_L - π_L)`: `σ` fixes the maximal unramified subextension `K'`, over which `L` is totally
ramified, so that `π_L` generates the ring of integers of `L` over that of `K'`. A positive integer
`n` is a ram exactly when `G_n ≠ G_{n + 1}`, that is when `i_G(σ) = n + 1` for some `σ`.

## Main results

* `IsNonarchimedeanLocalField.lowerIndex_eq_addVal_smul_sub`: for `σ` in the inertia group,
  `i_G(σ) = v_L(σ π_L - π_L)`.
* `IsNonarchimedeanLocalField.mem_ramsOfIsGalois_iff`: the rams of `L / K` are the integers `n ≥ 1`
  with `G_n ≠ G_{n + 1}`; in particular they are positive.
* `IsNonarchimedeanLocalField.mem_ramsOfIsGalois_iff_exists_addVal` (LMFDB `lf.rams`): a ram of
  `L / K` is any number of the form `v_L(σ π_L - π_L) - 1` for `σ ≠ 1` in the wild inertia group.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §1.
-/

open IsDiscreteValuationRing TauCeti ValuativeRel LocalFieldsRamification

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L] {π : 𝒪[L]} {n : ℕ} {σ : L ≃ₐ[K] L}

/-- **The lower index of an element of the inertia group at a uniformiser**: for a finite Galois
extension `L / K` of nonarchimedean local fields, a uniformiser `π_L` of `L` and `σ` in the inertia
group `G_0`, Serre's lower index `i_G(σ)` is `v_L(σ π_L - π_L)`. -/
lemma lowerIndex_eq_addVal_smul_sub (hπ : Irreducible π) (hσ : σ ∈ lowerRamificationGroup K L 0) :
    IsLocalRing.lowerIndex 𝒪[L] σ = addVal 𝒪[L] (σ • π - π) := by
  have hur : IsUnramified K (unramifiedExtension K L (inertiaDegree K L)) :=
    isUnramified_unramifiedExtension_inertiaDegree K L
  have htr : IsTotallyRamified (unramifiedExtension K L (inertiaDegree K L)) L :=
    isTotallyRamified_unramifiedExtension_inertiaDegree K L
  have hFL : ValuativeExtension (unramifiedExtension K L (inertiaDegree K L)) L :=
    IntermediateField.valuativeExtension _
  rcases lowerRamificationGroup_le_range K (unramifiedExtension K L (inertiaDegree K L)) L le_rfl
    hσ with ⟨τ, rfl⟩
  rw [AlgEquiv.restrictScalarsHom_apply, lowerIndex_restrictScalars,
    IsLocalRing.lowerIndex_eq_addVal_of_adjoin_singleton_eq_top
      (htr.adjoin_eq_top_of_irreducible hπ) τ, AlgEquiv.restrictScalars_smul_integerRing]

/-- **The rams of a Galois extension are its positive lower jumps**: for a finite Galois extension
`L / K` of nonarchimedean local fields, a natural number `n` is a ram of `L / K` if and only if
`n ≥ 1` and `G_{n + 1} ≠ G_n`. So the rams of a Galois extension are positive integers (LMFDB
`lf.rams`). -/
lemma mem_ramsOfIsGalois_iff : n ∈ ramsOfIsGalois K L ↔
    n ≠ 0 ∧ lowerRamificationGroup K L (n + 1 : ℕ) ≠ lowerRamificationGroup K L n := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨hp⟩
  have hval (i : ℕ) : padicValNat (ringChar 𝓀[K]) ((lowerRamificationGroup K L (i + 2)).relIndex
      (lowerRamificationGroup K L (i + 1))) ≠ 0 ↔
        lowerRamificationGroup K L (i + 2) ≠ lowerRamificationGroup K L (i + 1) := by
    have hle : lowerRamificationGroup K L (i + 2) ≤ lowerRamificationGroup K L (i + 1) :=
      lowerRamificationGroup_antitone K L (by omega)
    have hdvd : (lowerRamificationGroup K L (i + 2)).relIndex (lowerRamificationGroup K L (i + 1)) ∣
        Nat.card (lowerRamificationGroup K L (i + 1)) :=
      Subgroup.relIndex_dvd_card _ _
    rcases exists_relIndex_lowerRamificationGroup_eq_pow K L ⊥ (Nat.le_add_left 1 i) with ⟨a, ha⟩
    rw [Subgroup.relIndex_bot_left, Nat.cast_add, Nat.cast_one] at ha
    rw [ha] at hdvd
    rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨m, -, hm⟩
    rw [hm, padicValNat.prime_pow]
    refine not_congr ⟨fun h₀ ↦ hle.antisymm <| Subgroup.relIndex_eq_one.mp <| by
      rw [hm, h₀, pow_zero], fun heq ↦ ?_⟩
    have h₁ : ringChar 𝓀[K] ^ m = 1 := hm ▸ Subgroup.relIndex_eq_one.mpr heq.ge
    exact (Nat.pow_eq_one.mp h₁).resolve_left hp.one_lt.ne'
  rw [ramsOfIsGalois, Multiset.mem_sum]
  constructor
  · rintro ⟨i, -, hi⟩
    rcases Multiset.mem_replicate.mp hi with ⟨hm, rfl⟩
    exact ⟨i.succ_ne_zero, (hval i).mp hm⟩
  · rintro ⟨hn, hne⟩
    rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨i, rfl⟩
    refine ⟨i, Finset.mem_range.mpr <| not_le.mp fun hT ↦ hne ?_,
      Multiset.mem_replicate.mpr ⟨(hval i).mpr hne, rfl⟩⟩
    have h₁ : largestLowerJump K L < ((i + 1 : ℕ) : ℤ) := by omega
    have h₂ : largestLowerJump K L < ((i + 1 + 1 : ℕ) : ℤ) := by omega
    rw [lowerRamificationGroup_eq_bot_of_largestLowerJump_lt h₂,
      lowerRamificationGroup_eq_bot_of_largestLowerJump_lt h₁]

/-- **The rams of a Galois extension through a uniformiser** (LMFDB `lf.rams`): for a finite Galois
extension `L / K` of nonarchimedean local fields and a uniformiser `π_L` of `L`, a ram of `L / K`
is any number of the form `v_L(σ π_L - π_L) - 1` for some `σ ≠ 1` in the wild inertia group `G_1`
of `Gal(L / K)`: a natural number `n` is a ram if and only if `v_L(σ π_L - π_L) = n + 1` for such a
`σ`. -/
lemma mem_ramsOfIsGalois_iff_exists_addVal (hπ : Irreducible π) : n ∈ ramsOfIsGalois K L ↔
    ∃ σ ∈ lowerRamificationGroup K L 1, σ ≠ 1 ∧ addVal 𝒪[L] (σ • π - π) = (n + 1 : ℕ) := by
  have hmem (i : ℤ) {τ : L ≃ₐ[K] L} {N : ℕ} (hN : IsLocalRing.lowerIndex 𝒪[L] τ = N) :
      τ ∈ lowerRamificationGroup K L i ↔ i + 1 ≤ N :=
    IsLocalRing.mem_ramificationGroup_iff_of_lowerIndex_eq hN
  rw [mem_ramsOfIsGalois_iff]
  constructor
  · rintro ⟨hn, hne⟩
    have hlt : lowerRamificationGroup K L (n + 1 : ℕ) < lowerRamificationGroup K L n :=
      (lowerRamificationGroup_antitone K L (by omega)).lt_of_ne hne
    rcases IsConcreteLE.exists_of_lt hlt with ⟨σ, hσ, hσ'⟩
    have hσ₁ : σ ≠ 1 := fun h ↦ hσ' (h ▸ one_mem _)
    rcases ENat.ne_top_iff_exists.mp
      (mt (IsLocalRing.lowerIndex_eq_top_iff (S := 𝒪[L])).mp hσ₁) with ⟨N, hN⟩
    rw [hmem _ hN.symm] at hσ hσ'
    refine ⟨σ, (hmem 1 hN.symm).mpr (by omega), hσ₁, ?_⟩
    rw [← lowerIndex_eq_addVal_smul_sub hπ ((hmem 0 hN.symm).mpr (by omega)), ← hN]
    exact congrArg _ (by omega)
  · rintro ⟨σ, hσ, -, hval⟩
    have hN : IsLocalRing.lowerIndex 𝒪[L] σ = (n + 1 : ℕ) :=
      (lowerIndex_eq_addVal_smul_sub hπ (lowerRamificationGroup_antitone K L zero_le_one hσ)).trans
        hval
    rw [hmem 1 hN] at hσ
    refine ⟨by omega, fun heq ↦ ?_⟩
    have h : σ ∈ lowerRamificationGroup K L (n + 1 : ℕ) := heq ▸ (hmem n hN).mpr (by omega)
    rw [hmem _ hN] at h
    omega

end IsNonarchimedeanLocalField
