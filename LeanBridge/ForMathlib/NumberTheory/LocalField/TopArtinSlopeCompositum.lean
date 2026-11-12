import LeanBridge.ForMathlib.NumberTheory.LocalField.GaloisClosureRamification
import Mathlib.FieldTheory.SeparableClosure
import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient

/-!
# The top Artin slope of a compositum of Galois extensions

Let `M₁, …, Mₙ` be finite Galois extensions of a nonarchimedean local field `K` inside a field `Ω`,
and `N = M₁ ⋯ Mₙ` their compositum, a finite Galois extension of `K`. The top Artin slope (LMFDB
`lf.top_slope`) of `N / K` is the largest top Artin slope of the `Mᵢ / K`. Restriction maps the
upper ramification group `G^v` of `N / K` onto that of `Mᵢ / K` (Herbrand's theorem, Tau Ceti), so
the top Artin slope does not decrease in a tower of Galois extensions; and an element of `G^v`
trivial on every `Mᵢ` is trivial on their compositum `N`, so `G^v` is trivial as soon as every
`Gᵢ^v` is. The fields carry Tau Ceti's spectral-norm structures of nonarchimedean local fields.

## Main results

* `IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois_le_of_isScalarTower`: in a tower `M / L / K`
  of finite Galois extensions, the top Artin slope of `L / K` is at most that of `M / K`.
* `IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois_iSup` (LMFDB `modlgal.top_slope`): the top
  Artin slope of a compositum of finitely many finite Galois extensions is the largest of their
  top Artin slopes.
-/

open ValuativeRel TauCeti IntermediateField LocalFieldsRamification

namespace IntermediateField

variable {F E ι : Type*} [Field F] [Field E] [Algebra F E] (M : ι → IntermediateField F E)

lemma iSup_fieldRange_inclusion_eq_top :
    ⨆ i, (inclusion (le_iSup M i)).fieldRange = (⊤ : IntermediateField F ↥(⨆ i, M i)) := by
  apply map_injective (⨆ i, M i).val
  rw [map_iSup, ← AlgHom.fieldRange_eq_map, fieldRange_val]
  simp_rw [AlgHom.map_fieldRange]
  have h (i : ι) : ((⨆ i, M i).val.comp (inclusion (le_iSup M i))).fieldRange = M i := by
    have hv : (⨆ i, M i).val.comp (inclusion (le_iSup M i)) = (M i).val := rfl
    rw [hv, fieldRange_val]
  simp_rw [h]

instance [∀ i, IsGalois F (M i)] : IsGalois F ↥(⨆ i, M i) where

end IntermediateField

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Tower

variable (L M : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

lemma upperRamificationGroup_eq_bot_of_lt {v : RamificationIndexDomain}
    (h : topArtinSlopeOfIsGalois K L < v + 1) : upperRamificationGroup K L v = ⊥ := by
  rcases subsingleton_or_nontrivial (L ≃ₐ[K] L) with hL | hL
  · exact Subsingleton.elim _ _
  exact (upperRamificationGroup_eq_bot_iff K L).mpr h

variable [Algebra L M] [ValuativeExtension L M] [Module.Finite L M] [Algebra K M]
  [ValuativeExtension K M] [Module.Finite K M] [IsScalarTower K L M] [IsGalois K M]

/-- **The top Artin slope does not decrease in a tower of Galois extensions**: for finite Galois
extensions `M / L / K` of nonarchimedean local fields, the top Artin slope of `L / K` is at most
that of `M / K`, since restriction maps the upper ramification groups of `M / K` onto those of
`L / K` (Herbrand's theorem). -/
lemma topArtinSlopeOfIsGalois_le_of_isScalarTower :
    topArtinSlopeOfIsGalois K L ≤ topArtinSlopeOfIsGalois K M := by
  rcases subsingleton_or_nontrivial (L ≃ₐ[K] L) with hL | hL
  · rw [topArtinSlopeOfIsGalois_of_subsingleton]
    exact topArtinSlopeOfIsGalois_nonneg M
  refine le_of_not_gt fun hlt ↦ ?_
  have h0 : 0 ≤ topArtinSlopeOfIsGalois K M := topArtinSlopeOfIsGalois_nonneg M
  let v : RamificationIndexDomain :=
    ⟨(topArtinSlopeOfIsGalois K M + topArtinSlopeOfIsGalois K L) / 2 - 1, by
      rw [Set.mem_Ici]
      linarith⟩
  have hv : (v : ℝ) + 1 = (topArtinSlopeOfIsGalois K M + topArtinSlopeOfIsGalois K L) / 2 := by
    rw [Subtype.coe_mk, sub_add_cancel]
  have hM : upperRamificationGroup K M v = ⊥ := upperRamificationGroup_eq_bot_of_lt M (by linarith)
  have hL' : upperRamificationGroup K L v = ⊥ := by
    rw [← map_restrictNormalHom_upperRamificationGroup K L M v, hM, Subgroup.map_bot]
  have h : topArtinSlopeOfIsGalois K L < v + 1 := (upperRamificationGroup_eq_bot_iff K L).mp hL'
  linarith

end Tower

section Compositum

variable {Ω : Type*} [Field Ω] [Algebra K Ω] {ι : Type*} [Finite ι] (M : ι → IntermediateField K Ω)
  [∀ i, FiniteDimensional K (M i)] [∀ i, IsGalois K (M i)]

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

lemma topArtinSlopeOfIsGalois_le_iSup (i : ι) :
    topArtinSlopeOfIsGalois K (M i) ≤ topArtinSlopeOfIsGalois K ↥(⨆ i, M i) := by
  let _ : Algebra (M i) ↥(⨆ i, M i) := (inclusion (le_iSup M i)).toAlgebra
  have : IsScalarTower K (M i) ↥(⨆ i, M i) := .of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension (M i) ↥(⨆ i, M i) := (inclusion (le_iSup M i)).valuativeExtension
  have : Module.Finite (M i) ↥(⨆ i, M i) := .of_restrictScalars_finite K _ _
  exact topArtinSlopeOfIsGalois_le_of_isScalarTower (M i) ↥(⨆ i, M i)

/-- **The top Artin slope of a compositum of Galois extensions is the largest of theirs** (LMFDB
`modlgal.top_slope`): for finitely many finite Galois extensions `Mᵢ` of a nonarchimedean local
field `K` inside a field `Ω`, the top Artin slope of their compositum `⨆ i, Mᵢ` is the largest top
Artin slope of the `Mᵢ`. All fields carry Tau Ceti's spectral-norm local-field structure. -/
lemma topArtinSlopeOfIsGalois_iSup [Nonempty ι] :
    topArtinSlopeOfIsGalois K ↥(⨆ i, M i) = ⨆ i, topArtinSlopeOfIsGalois K (M i) := by
  have hbdd : BddAbove (Set.range fun i ↦ topArtinSlopeOfIsGalois K (M i)) :=
    (Set.finite_range _).bddAbove
  refine le_antisymm (le_of_not_gt fun hlt ↦ ?_) (ciSup_le (topArtinSlopeOfIsGalois_le_iSup M))
  have h0 : 0 ≤ ⨆ i, topArtinSlopeOfIsGalois K (M i) :=
    (topArtinSlopeOfIsGalois_nonneg _).trans (le_ciSup hbdd (Classical.arbitrary ι))
  let v : RamificationIndexDomain :=
    ⟨((⨆ i, topArtinSlopeOfIsGalois K (M i)) + topArtinSlopeOfIsGalois K ↥(⨆ i, M i)) / 2 - 1, by
      rw [Set.mem_Ici]
      linarith⟩
  have hv : (v : ℝ) + 1 =
      ((⨆ i, topArtinSlopeOfIsGalois K (M i)) + topArtinSlopeOfIsGalois K ↥(⨆ i, M i)) / 2 := by
    rw [Subtype.coe_mk, sub_add_cancel]
  let _ (i : ι) : Algebra (M i) ↥(⨆ i, M i) := (inclusion (le_iSup M i)).toAlgebra
  have (i : ι) : IsScalarTower K (M i) ↥(⨆ i, M i) := .of_algebraMap_eq fun _ ↦ rfl
  have (i : ι) : ValuativeExtension (M i) ↥(⨆ i, M i) :=
    (inclusion (le_iSup M i)).valuativeExtension
  have (i : ι) : Module.Finite (M i) ↥(⨆ i, M i) := .of_restrictScalars_finite K _ _
  have hker (i : ι) : upperRamificationGroup K ↥(⨆ i, M i) v ≤
      (AlgEquiv.restrictNormalHom (M i) (K₁ := ↥(⨆ i, M i))).ker := by
    rw [← Subgroup.map_eq_bot_iff, map_restrictNormalHom_upperRamificationGroup K (M i) _ v]
    exact upperRamificationGroup_eq_bot_of_lt (M i) <| by
      linarith [le_ciSup hbdd i]
  have hfix : upperRamificationGroup K ↥(⨆ i, M i) v ≤ fixingSubgroup ⊤ := by
    rw [← le_iff_le, ← iSup_fieldRange_inclusion_eq_top M]
    refine iSup_le fun i ↦ (le_iff_le _ _).mpr ?_
    have hi : IsScalarTower.toAlgHom K (M i) ↥(⨆ i, M i) = inclusion (le_iSup M i) := rfl
    rw [← hi, ← AlgEquiv.ker_restrictNormalHom]
    exact hker i
  rw [fixingSubgroup_top, le_bot_iff] at hfix
  rcases subsingleton_or_nontrivial (↥(⨆ i, M i) ≃ₐ[K] ↥(⨆ i, M i)) with hN | hN
  · rw [topArtinSlopeOfIsGalois_of_subsingleton] at hlt
    linarith
  have h : topArtinSlopeOfIsGalois K ↥(⨆ i, M i) < v + 1 :=
    (upperRamificationGroup_eq_bot_iff K _).mp hfix
  linarith

end Compositum

end IsNonarchimedeanLocalField
