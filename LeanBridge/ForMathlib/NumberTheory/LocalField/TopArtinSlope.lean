import LeanBridge.ForMathlib.FieldTheory.AlgebraGaloisClosure
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.Herbrand.Basic

/-!
# The top Artin slope of an extension of local fields

The LMFDB indexes the upper ramification filtration of a Galois extension `L / K` by Artin slopes:
`G^{(s)}` is Serre's upper-numbering group `G^{s - 1}`. The top Artin slope is the largest `s` with
`G^{(s)}` nontrivial, which is `1 + φ_{L/K}(t)` for the largest lower jump `t`.

## Main definitions

* `IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois` (LMFDB `lf.top_slope`): the top Artin slope
  of a finite Galois extension of nonarchimedean local fields.
* `IsNonarchimedeanLocalField.topArtinSlope` (LMFDB `lf.top_slope`): the top Artin slope of a finite
  separable extension, that of its Galois closure.

## Main theorems

* `IsNonarchimedeanLocalField.upperRamificationGroup_eq_bot_iff`: for a nontrivial Galois group,
  `G^{(s)} = G^{s - 1}` is trivial exactly for `s` above the top Artin slope, which is therefore
  the largest `s` with `G^{(s)}` nontrivial.
* `IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois_of_subsingleton`: the top Artin slope of an
  extension with trivial Galois group, such as `K / K`, is `0`.
-/

open ValuativeRel TauCeti LocalFieldsRamification

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L]

/-- The **top Artin slope** (LMFDB `lf.top_slope`) of a finite Galois extension `L / K` of
nonarchimedean local fields: `1 + φ_{L/K}(t)`, where `t` is the largest lower ramification jump
(`-1` when the Galois group is trivial) and `φ_{L/K}` the Herbrand function. The LMFDB's
`G^{(s)}` is Serre's `G^{s - 1}`, so this is the largest `s` with `G^{(s)}` nontrivial
(`upperRamificationGroup_eq_bot_iff`): `0` when `L / K` is unramified, `1` when it is tamely
ramified but not unramified, and the largest wild Artin slope otherwise. -/
noncomputable def topArtinSlopeOfIsGalois : ℝ :=
  1 + herbrand K L
    ⟨largestLowerJump K L, Set.mem_Ici.mpr <| by exact_mod_cast neg_one_le_largestLowerJump K L⟩

/-- For a nontrivial Galois group, the upper ramification group `G^v = G^{(v + 1)}` is trivial
exactly when `v + 1` exceeds the top Artin slope. -/
lemma upperRamificationGroup_eq_bot_iff [Nontrivial (L ≃ₐ[K] L)] {v : RamificationIndexDomain} :
    upperRamificationGroup K L v = ⊥ ↔ topArtinSlopeOfIsGalois K L < v + 1 := by
  rw [upperRamificationGroup_def, lowerRamificationGroupReal_eq_bot_iff, topArtinSlopeOfIsGalois,
    add_comm, add_lt_add_iff_right, ← herbrand_inverseHerbrand K L v, Subtype.coe_lt_coe,
    (herbrand_strictMono K L).lt_iff_lt, inverseHerbrand_herbrand]
  rfl

/-- The top Artin slope of an extension with trivial Galois group is `0`. -/
lemma topArtinSlopeOfIsGalois_of_subsingleton [Subsingleton (L ≃ₐ[K] L)] :
    topArtinSlopeOfIsGalois K L = 0 := by
  have h : largestLowerJump K L = -1 := by
    rw [largestLowerJump, Nat.sInf_eq_zero.mpr (Or.inl (Subsingleton.elim _ _))]
    rfl
  simp [topArtinSlopeOfIsGalois, h]

variable (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]

/-- The **top Artin slope** (LMFDB `lf.top_slope`) of a finite separable extension `E / K` of a
nonarchimedean local field: the largest `s` with `G^{(s)}` nontrivial, where `G` is the Galois group
of the Galois closure `Algebra.galoisClosure K E`, that is the top Artin slope of the Galois
closure, equipped with Tau Ceti's spectral-norm local-field structure. -/
noncomputable def topArtinSlope : ℝ :=
  letI : ValuativeRel (Algebra.galoisClosure K E) := finiteIntermediateFieldValuativeRel K _ _
  letI : TopologicalSpace (Algebra.galoisClosure K E) := finiteIntermediateFieldTopology K _ _
  haveI : IsNonarchimedeanLocalField (Algebra.galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  haveI : ValuativeExtension K (Algebra.galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  topArtinSlopeOfIsGalois K (Algebra.galoisClosure K E)

end IsNonarchimedeanLocalField
