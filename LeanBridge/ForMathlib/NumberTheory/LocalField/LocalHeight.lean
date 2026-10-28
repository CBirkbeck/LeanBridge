import LeanBridge.ForMathlib.GroupTheory.RationalClassWeight
import Mathlib.Data.ZMod.Units
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic

/-!
# Local height functions

Let `G` be a finite group with a weight function `w`, and `φ : Γ_K → G` a continuous homomorphism
from the absolute Galois group of a nonarchimedean local field `K` of residue characteristic
`p ∤ #G`. The extension cut out by `ker φ` is tamely ramified, so the image `φ(I_K)` of the inertia
subgroup is cyclic, and the local height of `φ` is `w(φ(τ))` for a generator `φ(τ)` of `φ(I_K)`.
It does not depend on the generator, since a weight function takes the same value at any two
generators of a cyclic subgroup.

## Main definitions

* `IsNonarchimedeanLocalField.localHeight` (LMFDB `lf.local_height_function`): the local height
  `H_w(φ)`.

## Main theorems

* `Group.IsWeightFunction.apply_eq_of_zpowers_eq`: a weight function takes the same value at two
  generators of the same cyclic subgroup.
* `IsNonarchimedeanLocalField.localHeight_eq`: `H_w(φ) = w(g)` for any generator `g` of `φ(I_K)`.
-/

open scoped NNReal

namespace Group

variable {G : Type*} [Group G] [Finite G] {w : G → ℝ≥0}

/-- **A weight function is constant on the generators of a cyclic subgroup**: if `g` and `g'`
generate the same subgroup, then `w g = w g'`. A power `g ^ k` generating `⟨g⟩` has `k` prime to the
order of `g`, and `k` lifts modulo the order of `g` to an exponent prime to `#G`. -/
lemma IsWeightFunction.apply_eq_of_zpowers_eq (hw : IsWeightFunction w) {g g' : G}
    (h : Subgroup.zpowers g = Subgroup.zpowers g') : w g = w g' := by
  rcases mem_powers_iff_mem_zpowers.mpr (h ▸ Subgroup.mem_zpowers g') with ⟨k, rfl⟩
  have hord : orderOf (g ^ k) = orderOf g := by
    rw [← Nat.card_zpowers, ← Nat.card_zpowers, h]
  have hk : k.Coprime (orderOf g) := by
    rw [(isOfFinOrder_of_finite g).orderOf_pow, Nat.div_eq_self] at hord
    exact (Nat.gcd_comm _ _).trans <| hord.resolve_left (orderOf_pos g).ne'
  rcases ZMod.unitsMap_surjective (orderOf_dvd_natCard g) (ZMod.unitOfCoprime k hk) with ⟨v, hv⟩
  have hkv : (v : ZMod (Nat.card G)).val ≡ k [MOD orderOf g] := by
    rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.coe_unitOfCoprime k hk, ← hv, ZMod.unitsMap_def,
      Units.coe_map, MonoidHom.coe_ofClass, ZMod.castHom_apply, ZMod.natCast_val]
  dsimp only
  rw [← pow_eq_pow_iff_modEq.mpr hkv, hw.apply_pow g (ZMod.val_coe_unit_coprime v)]

end Group

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {G : Type*} [Group G] [TopologicalSpace G] (w : G → ℝ≥0)
  (φ : ContinuousMonoidHom (Field.absoluteGaloisGroup K) G)

/-- The **local height** `H_w(φ)` (LMFDB `lf.local_height_function`) of a continuous homomorphism
`φ : Γ_K → G` to a finite group with respect to a weight function `w` on `G`: `w(φ(τ))`, where
`φ(τ)` generates the image `φ(I_K)` of the inertia subgroup, i.e. `τ` generates the inertia group
of the extension cut out by `ker φ`. It is the supremum of `w` over the generators of `φ(I_K)`,
which all have the same `w` (`localHeight_eq`). When `p ∤ #G` the image of inertia is cyclic (the
cut out extension is tame), so a generator exists; this is not formalised. The LMFDB takes
`K = ℚ_p`. -/
noncomputable def localHeight : ℝ≥0 :=
  ⨆ g : {g : G // Subgroup.zpowers g = (TauCeti.inertiaSubgroup K).map φ.toMonoidHom}, w g

variable [Finite G]

/-- **The local height is the weight of any generator of the image of inertia**. -/
lemma localHeight_eq (hw : Group.IsWeightFunction w) {g : G}
    (hg : Subgroup.zpowers g = (TauCeti.inertiaSubgroup K).map φ.toMonoidHom) :
    localHeight K w φ = w g :=
  le_antisymm (ciSup_le' fun g' ↦ (hw.apply_eq_of_zpowers_eq <| g'.2.trans hg.symm).le) <|
    le_ciSup_of_le (Set.finite_range _).bddAbove ⟨g, hg⟩ le_rfl

end IsNonarchimedeanLocalField
