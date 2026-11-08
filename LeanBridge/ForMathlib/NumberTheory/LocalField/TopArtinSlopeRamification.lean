import LeanBridge.ForMathlib.NumberTheory.LocalField.TopArtinSlopeContent
import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic
import TauCeti.NumberTheory.LocalField.Unramified.Basic

/-!
# Top Artin slopes `0` and `1`: unramified and tamely ramified extensions

The top Artin slope (LMFDB `lf.top_slope`) of a finite Galois extension `L / K` of nonarchimedean
local fields is `1 + φ_{L/K}(t)` for the largest lower ramification jump `t`. The jump `t` is `-1`
exactly when the inertia group `G_0` is trivial, that is when `L / K` is unramified (`#G_0` is the
ramification index), and it is at most `0` exactly when the wild inertia group `G_1` is trivial,
that is when `L / K` is tamely ramified (Tau Ceti). Since `φ_{L/K}(-1) = -1` and `φ_{L/K}(0) = 0`,
the top Artin slope is `0` exactly for unramified extensions and `1` exactly for tamely ramified
extensions that are not unramified (LMFDB `modlgal.top_slope`: "a top slope of `0` signifies that
the field is unramified at `ℓ`, and a top slope of `1` indicates that it is ramified, but only
tamely"). For a finite separable extension `E / K` the same holds for the Galois closure of `E`,
with its canonical structure of nonarchimedean local field.

## Main results

* `IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois_eq_zero_iff`: the top Artin slope of a
  finite Galois extension is `0` exactly when it is unramified.
* `IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois_le_one_iff`: it is at most `1` exactly when
  the extension is tamely ramified.
* `IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois_eq_one_iff`: it is `1` exactly when the
  extension is tamely ramified but not unramified.
* `IsNonarchimedeanLocalField.topArtinSlope_eq_zero_iff`,
  `IsNonarchimedeanLocalField.topArtinSlope_le_one_iff`,
  `IsNonarchimedeanLocalField.topArtinSlope_eq_one_iff`: the same for a finite separable extension
  and its Galois closure.
-/

open ValuativeRel TauCeti LocalFieldsRamification

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L] (E : Type*) [Field E]
  [Algebra K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]

lemma lowerRamificationGroup_zero_eq_bot_iff :
    lowerRamificationGroup K L 0 = ⊥ ↔ IsUnramified K L := by
  rw [← Subgroup.card_eq_one, natCard_lowerRamificationGroup_zero,
    isUnramified_iff_ramificationIndex_eq_one]

lemma one_le_topArtinSlopeOfIsGalois (h : 0 ≤ largestLowerJump K L) :
    1 ≤ topArtinSlopeOfIsGalois K L := by
  have h1 : ((herbrand K L ⟨0, by norm_num⟩ : RamificationIndexDomain) : ℝ) ≤
      herbrand K L ⟨largestLowerJump K L, Set.mem_Ici.mpr <| by
        exact_mod_cast neg_one_le_largestLowerJump K L⟩ :=
    Subtype.coe_le_coe.mpr <| (herbrand_strictMono K L).monotone <|
      Subtype.mk_le_mk.mpr <| by exact_mod_cast h
  rw [herbrand_of_coe_le_zero K L (u := ⟨0, by norm_num⟩) le_rfl] at h1
  rw [topArtinSlopeOfIsGalois]
  linarith

/-- **Top Artin slope `0` means unramified** (LMFDB `modlgal.top_slope`): the top Artin slope of a
finite Galois extension of nonarchimedean local fields is `0` exactly when it is unramified. -/
lemma topArtinSlopeOfIsGalois_eq_zero_iff :
    topArtinSlopeOfIsGalois K L = 0 ↔ IsUnramified K L := by
  rw [← lowerRamificationGroup_zero_eq_bot_iff]
  constructor
  · intro h
    refine (lowerRamificationGroup_natCast_eq_bot_iff K L (n := 0)).mpr ?_
    by_contra hT
    push Not at hT
    have h1 : 1 ≤ topArtinSlopeOfIsGalois K L := one_le_topArtinSlopeOfIsGalois K L (mod_cast hT)
    linarith
  · intro h0
    have hT : largestLowerJump K L < (0 : ℕ) :=
      (lowerRamificationGroup_natCast_eq_bot_iff K L (n := 0)).mp h0
    have h1 : -1 ≤ largestLowerJump K L := neg_one_le_largestLowerJump K L
    have hT' : largestLowerJump K L = -1 := by
      push_cast at hT
      omega
    simp [topArtinSlopeOfIsGalois, hT']

/-- **Top Artin slope at most `1` means tamely ramified** (LMFDB `modlgal.top_slope`): the top Artin
slope of a finite Galois extension of nonarchimedean local fields is at most `1` exactly when it is
tamely ramified. -/
lemma topArtinSlopeOfIsGalois_le_one_iff :
    topArtinSlopeOfIsGalois K L ≤ 1 ↔ IsTamelyRamified K L := by
  rw [← lowerRamificationGroup_one_eq_bot_iff_isTamelyRamified]
  refine ⟨fun h ↦ ?_, fun h1 ↦ ?_⟩
  · by_contra h1
    exact (one_lt_topArtinSlopeOfIsGalois K L h1).not_ge h
  have hT : largestLowerJump K L < (1 : ℕ) :=
    (lowerRamificationGroup_natCast_eq_bot_iff K L (n := 1)).mp h1
  have hT0 : (largestLowerJump K L : ℝ) ≤ 0 := by
    push_cast at hT
    exact_mod_cast Int.lt_add_one_iff.mp hT
  rw [topArtinSlopeOfIsGalois, herbrand_of_coe_le_zero K L (u := ⟨largestLowerJump K L,
    Set.mem_Ici.mpr <| by exact_mod_cast neg_one_le_largestLowerJump K L⟩) hT0]
  simpa using hT0

/-- **Top Artin slope `1` means tamely ramified but not unramified** (LMFDB `modlgal.top_slope`):
the top Artin slope of a finite Galois extension of nonarchimedean local fields is `1` exactly when
it is tamely ramified and ramified. -/
lemma topArtinSlopeOfIsGalois_eq_one_iff :
    topArtinSlopeOfIsGalois K L = 1 ↔ IsTamelyRamified K L ∧ ¬IsUnramified K L := by
  rw [← topArtinSlopeOfIsGalois_le_one_iff, ← topArtinSlopeOfIsGalois_eq_zero_iff]
  refine ⟨fun h ↦ ⟨h.le, by rw [h]; norm_num⟩, fun ⟨h1, h0⟩ ↦ h1.antisymm ?_⟩
  refine one_le_topArtinSlopeOfIsGalois K L (not_lt.mp fun hT ↦ h0 ?_)
  rw [topArtinSlopeOfIsGalois_eq_zero_iff, ← lowerRamificationGroup_zero_eq_bot_iff]
  exact (lowerRamificationGroup_natCast_eq_bot_iff K L (n := 0)).mpr (by exact_mod_cast hT)

/-- **Top Artin slope `0` means an unramified Galois closure** (LMFDB `modlgal.top_slope`): the top
Artin slope of a finite separable extension `E / K` of a nonarchimedean local field is `0` exactly
when the Galois closure of `E` is unramified over `K`. -/
lemma topArtinSlope_eq_zero_iff :
    topArtinSlope K E = 0 ↔ IsUnramified K (Algebra.galoisClosure K E) :=
  topArtinSlopeOfIsGalois_eq_zero_iff K _

/-- **Top Artin slope at most `1` means a tamely ramified Galois closure** (LMFDB
`modlgal.top_slope`): the top Artin slope of a finite separable extension `E / K` of a
nonarchimedean local field is at most `1` exactly when the Galois closure of `E` is tamely
ramified over `K`. -/
lemma topArtinSlope_le_one_iff :
    topArtinSlope K E ≤ 1 ↔ IsTamelyRamified K (Algebra.galoisClosure K E) :=
  topArtinSlopeOfIsGalois_le_one_iff K _

/-- **Top Artin slope `1` means a tamely ramified, ramified Galois closure** (LMFDB
`modlgal.top_slope`): the top Artin slope of a finite separable extension `E / K` of a
nonarchimedean local field is `1` exactly when the Galois closure of `E` is tamely ramified but not
unramified over `K`. -/
lemma topArtinSlope_eq_one_iff : topArtinSlope K E = 1 ↔
    IsTamelyRamified K (Algebra.galoisClosure K E) ∧ ¬IsUnramified K (Algebra.galoisClosure K E) :=
  topArtinSlopeOfIsGalois_eq_one_iff K _

end IsNonarchimedeanLocalField
