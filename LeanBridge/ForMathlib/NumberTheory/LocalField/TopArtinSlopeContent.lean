import LeanBridge.ForMathlib.NumberTheory.LocalField.TopArtinSlope
import LeanBridge.ForMathlib.NumberTheory.LocalField.WildArtinSlopes
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic

/-!
# The top Artin slope in terms of the slope content

Let `E / K` be a finite separable extension of nonarchimedean local fields, with Artin slope content
`[s_1, …, s_k]_t^u` (LMFDB `lf.slopes`, `IsNonarchimedeanLocalField.artinSlopeContent`): the wild
Artin slopes `s_i` and the tame degree `t` of the Galois closure. The LMFDB (`lf.top_slope`) reads
the top Artin slope off it: it is `s_k`, which is greater than `1`, if `k > 0`; otherwise it is `1`
if `t > 1` and `0` if `t = 1`, so that the trivial extension `K / K` has top slope `0`.

For a Galois extension `L / K` with lower ramification groups `G_i` and largest lower jump `T`, the
top Artin slope is `1 + φ(T)` and the wild Artin slopes are the `1 + φ(i)` for the lower jumps
`1 ≤ i ≤ T`, counted with multiplicity `log_p [G_i : G_{i + 1}]`. Since `G_1` is a `p`-group
(`#G_1 = p ^ v_p(e)`), the jump `T` has positive multiplicity when `T ≥ 1`, so there are wild
slopes exactly when `G_1 ≠ 1`, and then the largest is `1 + φ(T) > 1`. When `G_1 = 1`, the tame
degree is `e = #G_0`, so `t > 1` exactly when `G_0 ≠ 1`, that is `T = 0` and the top slope is
`1 + φ(0) = 1`, and otherwise `T = -1` and the top slope is `1 + φ(-1) = 0`.

## Main results

* `IsNonarchimedeanLocalField.wildArtinSlopesOfIsGalois_eq_zero_iff`: a Galois extension has no
  wild Artin slopes exactly when its first lower ramification group `G_1` is trivial.
* `IsNonarchimedeanLocalField.isGreatest_topArtinSlope` (LMFDB `lf.top_slope`): if `k > 0`, the
  top Artin slope is the largest wild Artin slope `s_k`.
* `IsNonarchimedeanLocalField.one_lt_topArtinSlope` (LMFDB `lf.top_slope`): if `k > 0`, the top
  Artin slope is greater than `1`.
* `IsNonarchimedeanLocalField.topArtinSlope_eq_one` (LMFDB `lf.top_slope`): if `k = 0` and `t > 1`,
  the top Artin slope is `1`.
* `IsNonarchimedeanLocalField.topArtinSlope_eq_zero` (LMFDB `lf.top_slope`): if `k = 0` and
  `t ≤ 1`, the top Artin slope is `0`.
* `IsNonarchimedeanLocalField.topArtinSlope_self` (LMFDB `lf.top_slope`): the trivial extension
  `K / K` has top Artin slope `0`; its Galois closure has trivial Galois group (the instance
  `Subsingleton (Algebra.galoisClosure K K ≃ₐ[K] Algebra.galoisClosure K K)`).
-/

open ValuativeRel TauCeti LocalFieldsRamification

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] (E : Type*) [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

lemma lowerRamificationGroup_natCast_eq_bot_iff {n : ℕ} :
    lowerRamificationGroup K L n = ⊥ ↔ largestLowerJump K L < n := by
  refine ⟨fun h ↦ ?_, lowerRamificationGroup_eq_bot_of_largestLowerJump_lt⟩
  have hn : sInf {n : ℕ | lowerRamificationGroup K L n = ⊥} ≤ n := Nat.sInf_le h
  rw [largestLowerJump]
  omega

lemma one_le_largestLowerJump (h : lowerRamificationGroup K L 1 ≠ ⊥) :
    1 ≤ largestLowerJump K L := by
  by_contra! hlt
  exact h <| (lowerRamificationGroup_natCast_eq_bot_iff K L (n := 1)).mpr (by exact_mod_cast hlt)

variable [IsGalois K L]

lemma mem_wildArtinSlopesOfIsGalois_iff {s : ℝ} : s ∈ wildArtinSlopesOfIsGalois K L ↔
    ∃ i < (largestLowerJump K L).toNat, padicValNat (ringChar 𝓀[K])
      ((lowerRamificationGroup K L (i + 2)).relIndex (lowerRamificationGroup K L (i + 1))) ≠ 0 ∧
      s = 1 + herbrand K L ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ := by
  simp [wildArtinSlopesOfIsGalois, Multiset.mem_replicate]

lemma padicValNat_relIndex_ne_zero (h : lowerRamificationGroup K L 1 ≠ ⊥) :
    padicValNat (ringChar 𝓀[K])
      ((lowerRamificationGroup K L (((largestLowerJump K L).toNat - 1 : ℕ) + 2)).relIndex
        (lowerRamificationGroup K L (((largestLowerJump K L).toNat - 1 : ℕ) + 1))) ≠ 0 := by
  have hT : 1 ≤ largestLowerJump K L := one_le_largestLowerJump K L h
  have hp : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩
  have h1 : (((largestLowerJump K L).toNat - 1 : ℕ) : ℤ) + 1 = largestLowerJump K L := by omega
  have h2 : (((largestLowerJump K L).toNat - 1 : ℕ) : ℤ) + 2 = largestLowerJump K L + 1 := by omega
  have : Nontrivial (L ≃ₐ[K] L) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h (Subsingleton.elim _ _)
  rw [h1, h2, lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (lt_add_one _),
    Subgroup.relIndex_bot_left]
  have hdvd : Nat.card (lowerRamificationGroup K L (largestLowerJump K L)) ∣
      ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K]) := by
    rw [← natCard_lowerRamificationGroup_one K L]
    exact Subgroup.card_dvd_of_le (lowerRamificationGroup_antitone K L hT)
  rcases (Nat.dvd_prime_pow hp.out).mp hdvd with ⟨m, -, hm⟩
  rw [hm, padicValNat.prime_pow]
  rintro rfl
  rw [pow_zero, Subgroup.card_eq_one] at hm
  exact lowerRamificationGroup_largestLowerJump_ne_bot K L hm

lemma topArtinSlopeOfIsGalois_mem (h : lowerRamificationGroup K L 1 ≠ ⊥) :
    topArtinSlopeOfIsGalois K L ∈ wildArtinSlopesOfIsGalois K L := by
  have hT : 1 ≤ largestLowerJump K L := one_le_largestLowerJump K L h
  have hcast : (((largestLowerJump K L).toNat - 1 + 1 : ℕ) : ℝ) = (largestLowerJump K L : ℝ) := by
    have h' : (((largestLowerJump K L).toNat - 1 + 1 : ℕ) : ℤ) = largestLowerJump K L := by omega
    exact_mod_cast h'
  refine (mem_wildArtinSlopesOfIsGalois_iff K L).mpr
    ⟨(largestLowerJump K L).toNat - 1, by omega, padicValNat_relIndex_ne_zero K L h, ?_⟩
  rw [topArtinSlopeOfIsGalois]
  congr 3
  exact Subtype.ext hcast.symm

lemma le_topArtinSlopeOfIsGalois {s : ℝ} (hs : s ∈ wildArtinSlopesOfIsGalois K L) :
    s ≤ topArtinSlopeOfIsGalois K L := by
  rcases (mem_wildArtinSlopesOfIsGalois_iff K L).mp hs with ⟨i, hi, -, rfl⟩
  rw [topArtinSlopeOfIsGalois, add_le_add_iff_left, Subtype.coe_le_coe]
  refine (herbrand_strictMono K L).monotone (Subtype.mk_le_mk.mpr ?_)
  have h' : ((i + 1 : ℕ) : ℤ) ≤ largestLowerJump K L := by omega
  exact_mod_cast h'

lemma one_lt_topArtinSlopeOfIsGalois (h : lowerRamificationGroup K L 1 ≠ ⊥) :
    1 < topArtinSlopeOfIsGalois K L := by
  have hT : 1 ≤ largestLowerJump K L := one_le_largestLowerJump K L h
  have hlt : herbrand K L ⟨0, by norm_num⟩ <
      herbrand K L ⟨largestLowerJump K L, Set.mem_Ici.mpr <| by
        exact_mod_cast neg_one_le_largestLowerJump K L⟩ :=
    herbrand_strictMono K L <| Subtype.mk_lt_mk.mpr <| by exact_mod_cast hT
  rw [herbrand_of_coe_le_zero K L le_rfl, ← Subtype.coe_lt_coe] at hlt
  rw [topArtinSlopeOfIsGalois, lt_add_iff_pos_right]
  exact hlt

/-- **A Galois extension has wild Artin slopes exactly when it is wildly ramified**: there are no
wild Artin slopes exactly when the first lower ramification group `G_1` is trivial. -/
lemma wildArtinSlopesOfIsGalois_eq_zero_iff :
    wildArtinSlopesOfIsGalois K L = 0 ↔ lowerRamificationGroup K L 1 = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra h1
    have hmem : topArtinSlopeOfIsGalois K L ∈ wildArtinSlopesOfIsGalois K L :=
      topArtinSlopeOfIsGalois_mem K L h1
    rw [h] at hmem
    exact Multiset.notMem_zero _ hmem
  · have hT : largestLowerJump K L < (1 : ℕ) :=
      (lowerRamificationGroup_natCast_eq_bot_iff K L (n := 1)).mp h
    have hT0 : (largestLowerJump K L).toNat = 0 := by omega
    simp [wildArtinSlopesOfIsGalois, hT0]

lemma tameDegree_eq_natCard (h : lowerRamificationGroup K L 1 = ⊥) :
    tameDegree K L = Nat.card (lowerRamificationGroup K L 0) := by
  rw [tameDegree, ← natCard_lowerRamificationGroup_one, h, Subgroup.card_bot, Nat.div_one,
    natCard_lowerRamificationGroup_zero]

lemma topArtinSlopeOfIsGalois_eq_one (h : wildArtinSlopesOfIsGalois K L = 0)
    (ht : 1 < tameDegree K L) : topArtinSlopeOfIsGalois K L = 1 := by
  rw [wildArtinSlopesOfIsGalois_eq_zero_iff] at h
  rw [tameDegree_eq_natCard K L h, Subgroup.one_lt_card_iff_ne_bot] at ht
  have h1 : largestLowerJump K L < (1 : ℕ) :=
    (lowerRamificationGroup_natCast_eq_bot_iff K L (n := 1)).mp h
  have h0 : ¬largestLowerJump K L < (0 : ℕ) :=
    fun h0 ↦ ht ((lowerRamificationGroup_natCast_eq_bot_iff K L (n := 0)).mpr h0)
  have hT : largestLowerJump K L = 0 := by
    omega
  simp [topArtinSlopeOfIsGalois, hT]

lemma topArtinSlopeOfIsGalois_eq_zero (h : wildArtinSlopesOfIsGalois K L = 0)
    (ht : tameDegree K L ≤ 1) : topArtinSlopeOfIsGalois K L = 0 := by
  rw [wildArtinSlopesOfIsGalois_eq_zero_iff] at h
  rw [tameDegree_eq_natCard K L h, ← not_lt, Subgroup.one_lt_card_iff_ne_bot, not_not] at ht
  have h0 : largestLowerJump K L < (0 : ℕ) :=
    (lowerRamificationGroup_natCast_eq_bot_iff K L (n := 0)).mp ht
  have hT : largestLowerJump K L = -1 := by
    have h1 : -1 ≤ largestLowerJump K L := neg_one_le_largestLowerJump K L
    omega
  simp [topArtinSlopeOfIsGalois, hT]

/-- **If `k > 0`, the top Artin slope is the largest wild Artin slope `s_k`**
(LMFDB `lf.top_slope`): for a finite separable extension `E / K` with Artin slope content
`[s_1, …, s_k]_t^u`, if there are wild Artin slopes, then the top Artin slope is the greatest of
them. -/
lemma isGreatest_topArtinSlope (hk : 0 < Multiset.card (wildArtinSlopes K E)) :
    IsGreatest {s | s ∈ wildArtinSlopes K E} (topArtinSlope K E) :=
  have h : lowerRamificationGroup K (Algebra.galoisClosure K E) 1 ≠ ⊥ :=
    (wildArtinSlopesOfIsGalois_eq_zero_iff K _).not.mp (Multiset.card_pos.mp hk)
  ⟨topArtinSlopeOfIsGalois_mem K _ h, fun _ hs ↦ le_topArtinSlopeOfIsGalois K _ hs⟩

/-- **If `k > 0`, the top Artin slope is greater than `1`** (LMFDB `lf.top_slope`). -/
lemma one_lt_topArtinSlope (hk : 0 < Multiset.card (wildArtinSlopes K E)) : 1 < topArtinSlope K E :=
  one_lt_topArtinSlopeOfIsGalois K _ <|
    (wildArtinSlopesOfIsGalois_eq_zero_iff K _).not.mp (Multiset.card_pos.mp hk)

/-- **If `k = 0` and `t > 1`, the top Artin slope is `1`** (LMFDB `lf.top_slope`): for a finite
separable extension `E / K` with Artin slope content `[s_1, …, s_k]_t^u`, if there are no wild Artin
slopes and the tame degree is greater than `1`, then the top Artin slope is `1`. -/
lemma topArtinSlope_eq_one (hk : Multiset.card (wildArtinSlopes K E) = 0)
    (ht : 1 < galoisTameDegree K E) : topArtinSlope K E = 1 :=
  topArtinSlopeOfIsGalois_eq_one K _ (Multiset.card_eq_zero.mp hk) ht

/-- **If `k = 0` and `t = 1`, the top Artin slope is `0`** (LMFDB `lf.top_slope`): for a finite
separable extension `E / K` with Artin slope content `[s_1, …, s_k]_t^u`, if there are no wild Artin
slopes and the tame degree is at most `1`, then the top Artin slope is `0`. -/
lemma topArtinSlope_eq_zero (hk : Multiset.card (wildArtinSlopes K E) = 0)
    (ht : galoisTameDegree K E ≤ 1) : topArtinSlope K E = 0 :=
  topArtinSlopeOfIsGalois_eq_zero K _ (Multiset.card_eq_zero.mp hk) ht

instance : Subsingleton (Algebra.galoisClosure K K ≃ₐ[K] Algebra.galoisClosure K K) := by
  refine ⟨fun σ τ ↦ AlgEquiv.ext fun x ↦ ?_⟩
  have hle : Algebra.galoisClosure K K ≤ ⊥ := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro - ⟨-, ⟨f, rfl⟩, y, rfl⟩
    exact IntermediateField.mem_bot.mpr ⟨y, (f.commutes y).symm⟩
  rcases IntermediateField.mem_bot.mp (hle x.2) with ⟨c, hc⟩
  have hx : x = algebraMap K (Algebra.galoisClosure K K) c := Subtype.ext hc.symm
  rw [hx, σ.commutes, τ.commutes]

/-- **The trivial extension `K / K` has top Artin slope `0`** (LMFDB `lf.top_slope`). -/
lemma topArtinSlope_self : topArtinSlope K K = 0 :=
  topArtinSlopeOfIsGalois_of_subsingleton K _

end IsNonarchimedeanLocalField
