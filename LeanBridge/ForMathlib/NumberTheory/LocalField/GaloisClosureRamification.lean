import LeanBridge.ForMathlib.NumberTheory.LocalField.TopArtinSlopeRamification
import TauCeti.NumberTheory.LocalField.TamelyRamified.NormalClosure
import TauCeti.NumberTheory.LocalField.Unramified.BaseChange

/-!
# Ramification of the Galois closure of an extension of local fields

Let `E / K` be a finite separable extension of nonarchimedean local fields. Its Galois closure
`Algebra.galoisClosure K E`, the compositum in `K̄` of the images of the `K`-embeddings of `E`, is
unramified (tamely ramified) over `K` exactly when `E` is: one way because `E` embeds in it, the
other because a compositum of unramified (tamely ramified) extensions is unramified (tamely
ramified), by Tau Ceti. So the top Artin slope of `E / K` (LMFDB `lf.top_slope`), that of its
Galois closure, is `0` exactly when `E / K` is unramified, at most `1` exactly when `E / K` is
tamely ramified, and `1` exactly when `E / K` is tamely ramified but not unramified (LMFDB
`modlgal.top_slope`).

The Galois closure carries Tau Ceti's spectral-norm structure of nonarchimedean local field, as in
`IsNonarchimedeanLocalField.topArtinSlope`; `E` may carry any structure of nonarchimedean local
field extending that of `K` (mathematically there is only one, which is not used here).

## Main results

* `IsNonarchimedeanLocalField.isUnramified_galoisClosure_iff`: the Galois closure of `E / K` is
  unramified exactly when `E / K` is.
* `IsNonarchimedeanLocalField.isTamelyRamified_galoisClosure_iff`: the Galois closure of `E / K`
  is tamely ramified exactly when `E / K` is.
* `IsNonarchimedeanLocalField.topArtinSlope_eq_zero_iff_isUnramified`,
  `IsNonarchimedeanLocalField.topArtinSlope_le_one_iff_isTamelyRamified`,
  `IsNonarchimedeanLocalField.topArtinSlope_eq_one_iff_isTamelyRamified` (LMFDB
  `modlgal.top_slope`): the top Artin slope of `E / K` is `0` exactly when `E / K` is unramified,
  at most `1` exactly when it is tamely ramified, and `1` exactly when it is tamely ramified but
  not unramified.
-/

open ValuativeRel TauCeti IntermediateField LocalFieldsRamification

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

lemma isUnramified_sup {Ω : Type*} [Field Ω] [Algebra K Ω] {L M : IntermediateField K Ω}
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [ValuativeExtension K M]
    [ValuativeRel ↥(L ⊔ M)] [TopologicalSpace ↥(L ⊔ M)] [IsNonarchimedeanLocalField ↥(L ⊔ M)]
    [ValuativeExtension K ↥(L ⊔ M)] (hL : IsUnramified K L) (hM : IsUnramified K M) :
    IsUnramified K ↥(L ⊔ M) := by
  refine IsUnramified.of_fieldRange_sup_fieldRange_eq_top (inclusion le_sup_left)
    (inclusion le_sup_right) (lift_injective _ ?_)
  have hL' : lift (inclusion (le_sup_left : L ≤ L ⊔ M)).fieldRange = L := lift_restrict _
  have hM' : lift (inclusion (le_sup_right : M ≤ L ⊔ M)).fieldRange = M := lift_restrict _
  simp only [lift_sup, hL', hM', lift_top]

lemma ramificationIndex_eq_of_algEquiv {E M : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra K E] [ValuativeExtension K E] [Field M] [ValuativeRel M]
    [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M]
    (σ : E ≃ₐ[K] M) : ramificationIndex K E = ramificationIndex K M := by
  have : Module.Finite K E := finite_of_valuativeExtension K E
  let _ : Algebra E M := σ.toRingHom.toAlgebra
  have : IsScalarTower K E M := .of_algebraMap_eq fun x ↦ (σ.commutes x).symm
  have : ValuativeExtension E M := σ.toAlgHom.valuativeExtension
  have h1 : Module.finrank E M = 1 := Module.finrank_of_bijective_algebraMap σ.bijective
  rw [ramificationIndex_tower (K := K) (L := E) M,
    (mul_eq_one.mp ((ramificationIndex_mul_inertiaDegree E M).trans h1)).1, mul_one]

lemma topArtinSlopeOfIsGalois_nonneg (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
    [IsGalois K L] : 0 ≤ topArtinSlopeOfIsGalois K L := by
  have h : (-1 : ℝ) ≤ herbrand K L ⟨largestLowerJump K L, Set.mem_Ici.mpr <| by
      exact_mod_cast neg_one_le_largestLowerJump K L⟩ :=
    (herbrand K L _).2
  rw [topArtinSlopeOfIsGalois]
  linarith

lemma topArtinSlope_nonneg (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E] : 0 ≤ topArtinSlope K E :=
  topArtinSlopeOfIsGalois_nonneg _

lemma topArtinSlope_eq_one_of_le_one {E : Type*} [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E] (h1 : topArtinSlope K E ≤ 1) (h0 : topArtinSlope K E ≠ 0) :
    topArtinSlope K E = 1 :=
  (topArtinSlope_eq_one_iff K E).mpr
    ⟨(topArtinSlope_le_one_iff K E).mp h1, fun h ↦ h0 ((topArtinSlope_eq_zero_iff K E).mpr h)⟩

variable (K) (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra K E] [ValuativeExtension K E] [FiniteDimensional K E]

lemma isUnramified_normalClosure [IsUnramified K E] :
    IsUnramified K (normalClosure K E (AlgebraicClosure K)) := by
  let N : IntermediateField K (AlgebraicClosure K) := normalClosure K E (AlgebraicClosure K)
  have hbot : IsUnramified K (⊥ : IntermediateField K N) := by
    have h1 : Module.finrank K (⊥ : IntermediateField K N) = 1 := IntermediateField.finrank_bot
    rw [isUnramified_iff_ramificationIndex_eq_one]
    exact (mul_eq_one.mp ((ramificationIndex_mul_inertiaDegree K _).trans h1)).1
  have hrange (f : E →ₐ[K] N) : IsUnramified K f.fieldRange :=
    IsUnramified.of_algEquiv f.equivFieldRange
  let _ : Fintype (E →ₐ[K] N) := Fintype.ofFinite _
  have htop : (Finset.univ.sup fun f : E →ₐ[K] N ↦ f.fieldRange) = ⊤ := by
    simpa only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_true] using
      normalClosure_iSup_fieldRange_eq_top K E (AlgebraicClosure K)
  have hPt : IsUnramified K (⊤ : IntermediateField K N) :=
    htop ▸ Finset.sup_induction (p := fun F : IntermediateField K N ↦ IsUnramified K F) hbot
      (fun _ hF _ hG ↦ isUnramified_sup hF hG)
      fun f _ ↦ hrange f
  exact hPt.of_algEquiv topEquiv

/-- **The Galois closure of an extension of local fields is unramified exactly when the extension
is**: `E` embeds in its Galois closure, and the Galois closure is a compositum of conjugates of
`E`. -/
lemma isUnramified_galoisClosure_iff :
    IsUnramified K (Algebra.galoisClosure K E) ↔ IsUnramified K E := by
  refine ⟨fun h ↦ ?_, fun h ↦ (isUnramified_normalClosure K E).of_algEquiv
    (equivOfEq (Algebra.galoisClosure_eq_normalClosure (F := K) E).symm)⟩
  let _ : Algebra E (Algebra.galoisClosure K E) := (Algebra.toGaloisClosure K E).toAlgebra
  have : IsScalarTower K E (Algebra.galoisClosure K E) :=
    .of_algebraMap_eq fun x ↦ ((Algebra.toGaloisClosure K E).commutes x).symm
  have : ValuativeExtension E (Algebra.galoisClosure K E) :=
    (Algebra.toGaloisClosure K E).valuativeExtension
  exact IsUnramified.tower_bot K E (Algebra.galoisClosure K E)

/-- **The Galois closure of an extension of local fields is tamely ramified exactly when the
extension is**: `E` embeds in its Galois closure, and the normal closure of a tamely ramified
extension is tamely ramified (Tau Ceti). -/
lemma isTamelyRamified_galoisClosure_iff :
    IsTamelyRamified K (Algebra.galoisClosure K E) ↔ IsTamelyRamified K E := by
  refine ⟨fun h ↦ ?_, fun h ↦ (h.normalClosure (Ω := AlgebraicClosure K)).of_algEquiv
    (equivOfEq (Algebra.galoisClosure_eq_normalClosure (F := K) E).symm)⟩
  let _ : Algebra E (Algebra.galoisClosure K E) := (Algebra.toGaloisClosure K E).toAlgebra
  have : IsScalarTower K E (Algebra.galoisClosure K E) :=
    .of_algebraMap_eq fun x ↦ ((Algebra.toGaloisClosure K E).commutes x).symm
  have : ValuativeExtension E (Algebra.galoisClosure K E) :=
    (Algebra.toGaloisClosure K E).valuativeExtension
  exact h.tower_bot

variable [Algebra.IsSeparable K E]

/-- **Top Artin slope `0` means unramified** (LMFDB `modlgal.top_slope`): the top Artin slope of a
finite separable extension `E / K` of nonarchimedean local fields is `0` exactly when `E / K` is
unramified. -/
lemma topArtinSlope_eq_zero_iff_isUnramified : topArtinSlope K E = 0 ↔ IsUnramified K E :=
  (topArtinSlope_eq_zero_iff K E).trans (isUnramified_galoisClosure_iff K E)

/-- **Top Artin slope at most `1` means tamely ramified** (LMFDB `modlgal.top_slope`): the top Artin
slope of a finite separable extension `E / K` of nonarchimedean local fields is at most `1` exactly
when `E / K` is tamely ramified. -/
lemma topArtinSlope_le_one_iff_isTamelyRamified : topArtinSlope K E ≤ 1 ↔ IsTamelyRamified K E :=
  (topArtinSlope_le_one_iff K E).trans (isTamelyRamified_galoisClosure_iff K E)

/-- **Top Artin slope `1` means tamely ramified but not unramified** (LMFDB `modlgal.top_slope`):
the top Artin slope of a finite separable extension `E / K` of nonarchimedean local fields is `1`
exactly when `E / K` is tamely ramified and ramified. -/
lemma topArtinSlope_eq_one_iff_isTamelyRamified :
    topArtinSlope K E = 1 ↔ IsTamelyRamified K E ∧ ¬IsUnramified K E := by
  rw [topArtinSlope_eq_one_iff, isTamelyRamified_galoisClosure_iff, isUnramified_galoisClosure_iff]

end IsNonarchimedeanLocalField
