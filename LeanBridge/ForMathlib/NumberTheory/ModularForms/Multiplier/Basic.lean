import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.ZMod.Units
import TauCeti.NumberTheory.ModularForms.Parity

/-!
# Multiplier systems of integral weight

A multiplier system of weight `k ∈ ℤ` for a subgroup `Γ` of `GL(2, ℝ)` is a homomorphism
`v : Γ → S¹` with `v(-I) = (-1) ^ k` when `-I ∈ Γ`: it is the factor in the transformation law
`f ∣[k] γ = v(γ) f` of modular forms with multiplier. The condition at `-I` is forced by every
nonzero function satisfying that law, since `-I` fixes every point of `ℍ` and slashes by
`(-1) ^ k`. The nebentypus law `f ∣[k] γ = χ(d) f` on `Γ₀(N)` is the law of such a multiplier.

## Main definitions

* `MonoidHom.IsMultiplierSystem` (LMFDB `mf.multipliersystem`).
* `MonoidHom.toCircle`: a homomorphism from a finite group to `ℂˣ`, as a homomorphism to the unit
  circle.
* `CongruenceSubgroup.nebentypusMultiplier`: the homomorphism `γ ↦ χ(d)` on `Γ₀(N)` of a character
  `χ` of `(ℤ/Nℤ)ˣ`.

## Main results

* `MonoidHom.isMultiplierSystem_of_slash_eq_smul`: if a nonzero function satisfies
  `f ∣[k] γ = v(γ) f` for every `γ ∈ Γ`, then `v` is a multiplier system of weight `k`.
* `CongruenceSubgroup.mem_modFormCharSpace_iff_slash_eq_smul`: a modular form for `Γ₁(N)` lies in
  `M_k(Γ₁(N), χ)` exactly when it transforms under `Γ₀(N)` with the nebentypus multiplier of `χ`.
* `CongruenceSubgroup.isMultiplierSystem_nebentypusMultiplier_iff`: the nebentypus multiplier of
  `χ` is a multiplier system of weight `k` exactly when `χ(-1) = (-1) ^ k`.
-/

open Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm UpperHalfPlane

namespace MonoidHom

variable {Γ : Subgroup (GL (Fin 2) ℝ)} (v w : Γ →* Circle) {k l : ℤ} {G : Type*} [Group G]
    [Finite G] (χ : G →* ℂˣ)

variable (k) in
/-- A homomorphism `v : Γ → S¹` from a subgroup `Γ` of `GL(2, ℝ)` to the unit circle is a
**multiplier system** (LMFDB `mf.multipliersystem`) of weight `k ∈ ℤ` if `v(-I) = (-1) ^ k`
whenever `-I ∈ Γ`. This is the LMFDB's notion, for integral weight, where multiplier systems are
homomorphisms; the multipliers of non-integral weight, such as that of the Dedekind eta function,
are not homomorphisms and are not covered. -/
def IsMultiplierSystem : Prop :=
  ∀ h : (-1 : GL (Fin 2) ℝ) ∈ Γ, v ⟨-1, h⟩ = (-1) ^ k

/-- **The condition at `-I` is forced by the transformation law**: if a nonzero function
`f : ℍ → ℂ` satisfies `f ∣[k] γ = v(γ) f` for every `γ ∈ Γ`, then `v` is a multiplier system of
weight `k`, since `-I` slashes by `(-1) ^ k`. -/
lemma isMultiplierSystem_of_slash_eq_smul {f : ℍ → ℂ} (hf : f ≠ 0)
    (h : ∀ γ : Γ, f ∣[k] (γ : GL (Fin 2) ℝ) = (v γ : ℂ) • f) : v.IsMultiplierSystem k :=
  fun h1 ↦ Circle.ext <| by
    rw [Circle.coe_zpow, Circle.coe_neg, Circle.coe_one]
    exact smul_left_injective ℂ hf <| (h ⟨-1, h1⟩).symm.trans <| ModularForm.slash_neg_one k f

lemma IsMultiplierSystem.mul (hv : v.IsMultiplierSystem k) (hw : w.IsMultiplierSystem l) :
    (v * w).IsMultiplierSystem (k + l) :=
  fun h ↦ by rw [mul_apply, hv h, hw h, zpow_add]

lemma isMultiplierSystem_one_iff :
    (1 : Γ →* Circle).IsMultiplierSystem k ↔ ((-1 : GL (Fin 2) ℝ) ∈ Γ → Even k) := by
  rw [IsMultiplierSystem, neg_one_zpow_eq_ite]
  split_ifs with hk
  · simp [hk]
  · simp [hk, (Circle.neg_ne_self 1).symm]

/-- A homomorphism `χ : G → ℂˣ` from a finite group, as a homomorphism to the unit circle: its
values are roots of unity. -/
noncomputable def toCircle : G →* Circle :=
  mk' (fun g ↦ ⟨χ g, mem_sphere_zero_iff_norm.mpr <| Complex.norm_eq_one_of_pow_eq_one
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one])
    (isOfFinOrder_of_finite g).orderOf_pos.ne'⟩)
    fun g h ↦ Circle.ext <| (congrArg Units.val <| map_mul χ g h).trans <| Units.val_mul _ _

@[simp]
lemma coe_toCircle_apply (g : G) : (χ.toCircle g : ℂ) = χ g :=
  rfl

end MonoidHom

namespace CongruenceSubgroup

variable {N : ℕ} (χ : (ZMod N)ˣ →* ℂˣ) {k : ℤ} {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}

/-- The **nebentypus multiplier** of a character `χ` of `(ℤ/Nℤ)ˣ`: the homomorphism `γ ↦ χ(d)` on
`Γ₀(N)`, as a subgroup of `GL(2, ℝ)`, where `d` is the lower-right entry of `γ`. -/
noncomputable def nebentypusMultiplier : (Gamma0 N).map (mapGL ℝ) →* Circle :=
  χ.toCircle.comp <| (Gamma0Map N).toHomUnits.comp
    ((Gamma0 N).equivMapOfInjective (mapGL ℝ) mapGL_injective).symm.toMonoidHom

lemma coe_nebentypusMultiplier_apply_mapGL (γ : Gamma0 N) :
    (nebentypusMultiplier χ ⟨mapGL ℝ γ, Subgroup.mem_map_of_mem _ γ.2⟩ : ℂ) =
      χ ((Gamma0Map N).toHomUnits γ) := by
  rw [nebentypusMultiplier, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MonoidHom.coe_toCircle_apply]
  exact congrArg (fun g ↦ (χ ((Gamma0Map N).toHomUnits g) : ℂ)) <|
    ((Gamma0 N).equivMapOfInjective (mapGL ℝ) mapGL_injective).symm_apply_apply γ

/-- **The nebentypus law is the law of the nebentypus multiplier**: a modular form for `Γ₁(N)`
lies in Tau Ceti's `M_k(Γ₁(N), χ)` exactly when `f ∣[k] γ = v(γ) f` for every `γ ∈ Γ₀(N)`, where
`v` is the nebentypus multiplier of `χ`. -/
lemma mem_modFormCharSpace_iff_slash_eq_smul : f ∈ modFormCharSpace k χ ↔
    ∀ γ : (Gamma0 N).map (mapGL ℝ), ⇑f ∣[k] (γ : GL (Fin 2) ℝ) =
      (nebentypusMultiplier χ γ : ℂ) • ⇑f := by
  rw [mem_modFormCharSpace_iff_nebentypus]
  refine ⟨fun h γ ↦ ?_, fun h γ ↦ ?_⟩
  · rcases γ with ⟨_, γ, hγ, rfl⟩
    rw [coe_nebentypusMultiplier_apply_mapGL χ ⟨γ, hγ⟩]
    exact h ⟨γ, hγ⟩
  · rw [← coe_nebentypusMultiplier_apply_mapGL χ γ]
    exact h ⟨mapGL ℝ (γ : SL(2, ℤ)), Subgroup.mem_map_of_mem _ γ.2⟩

/-- The nebentypus multiplier of `χ` is a **multiplier system of weight `k`** exactly when `χ` has
the parity of `k`: `χ(-1) = (-1) ^ k`. -/
lemma isMultiplierSystem_nebentypusMultiplier_iff :
    (nebentypusMultiplier χ).IsMultiplierSystem k ↔ (χ (-1) : ℂ) = (-1) ^ k := by
  have h1 : (-1 : GL (Fin 2) ℝ) ∈ (Gamma0 N).map (mapGL ℝ) :=
    ⟨-1, neg_one_mem_Gamma0, mapGL_neg_one⟩
  have h2 : (⟨-1, h1⟩ : (Gamma0 N).map (mapGL ℝ)) =
      ⟨mapGL ℝ (Gamma0.negOne N : SL(2, ℤ)), Subgroup.mem_map_of_mem _ (Gamma0.negOne N).2⟩ :=
    Subtype.ext mapGL_neg_one.symm
  rw [MonoidHom.IsMultiplierSystem, forall_prop_of_true h1, ← Circle.coe_inj, Circle.coe_zpow,
    Circle.coe_neg, Circle.coe_one, h2, coe_nebentypusMultiplier_apply_mapGL,
    Gamma0Map_toHomUnits_negOne]

end CongruenceSubgroup
