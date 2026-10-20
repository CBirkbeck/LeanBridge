import Mathlib.NumberTheory.ModularForms.NormTrace
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# Levels of modular forms

A level of a modular form `f` (LMFDB `cmf.level`) is a positive integer `N` such that `f` is a
modular form on a subgroup `Γ` of `SL₂(ℤ)` containing the principal congruence subgroup `Γ(N)`, i.e.
such that `f` is a modular form on `Γ(N)`. The level of a newform is the least such `N`.

Tau Ceti's newforms of level `N` are newforms on `Γ₁(N) ⊇ Γ(N)`, so `N` is a level of each of them
and their least level is at most `N`. It is exactly `N`, as a newform on `Γ₁(N)` is not a modular
form on `Γ(M)` for any `M < N`, but that is not proved here.

## Main definitions

* `ModularForm.IsLevel`: `N` is a level of a modular form (LMFDB `cmf.level`).
* `HeckeRing.GL2.Newform.level`: the level of a newform, the least level of its underlying form
  (LMFDB `cmf.level`).

## Main results

* `ModularForm.isLevel_iff`: `N` is a level of `f` exactly when `f` is a modular form on `Γ(N)`.
* `HeckeRing.GL2.Newform.isLevel`: Tau Ceti's level `N` of a newform is a level of it.
* `HeckeRing.GL2.Newform.level_le`: the level of a newform of Tau Ceti's level `N` is at most `N`.
-/

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace ModularForm

variable {k : ℤ} {N : ℕ} {F : ℍ → ℂ}

variable (k N F) in
/-- A positive integer `N` is **a level** of a function `F : ℍ → ℂ` that is a modular form of
weight `k` (LMFDB `cmf.level`) if `F` is a modular form of weight `k` on a subgroup `Γ` of `SL₂(ℤ)`
containing the principal congruence subgroup `Γ(N)`; equivalently, on `Γ(N)` itself
(`isLevel_iff`). -/
def IsLevel : Prop :=
  0 < N ∧ ∃ Γ : Subgroup SL(2, ℤ), Gamma N ≤ Γ ∧ ∃ G : ModularForm (Γ.map (mapGL ℝ)) k, ⇑G = F

/-- **`N` is a level of `F` exactly when `F` is a modular form on `Γ(N)`**: a modular form on a
group `Γ ⊇ Γ(N)` is one on `Γ(N)`. -/
lemma isLevel_iff : IsLevel k N F ↔ 0 < N ∧ ∃ G : ModularForm ((Gamma N).map (mapGL ℝ)) k, ⇑G = F :=
  ⟨fun ⟨hN, _, hΓ, G, hG⟩ ↦ ⟨hN, G.restrict (Subgroup.map_mono hΓ), hG⟩,
    fun ⟨hN, G, hG⟩ ↦ ⟨hN, Gamma N, le_rfl, G, hG⟩⟩

end ModularForm

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)

/-- **The level `N` of a newform of level `N` is a level of it**: it is a modular form on
`Γ₁(N) ⊇ Γ(N)`. -/
lemma isLevel : ModularForm.IsLevel k N f.toCuspForm :=
  ⟨NeZero.pos N, Gamma1 N, Gamma_le_Gamma1 N, f.toCuspForm, rfl⟩

/-- The **level** of a newform `f` (LMFDB `cmf.level`): the least level of its underlying modular
form, i.e. the least `M` such that `f` is a modular form on `Γ(M)`. For a newform of Tau Ceti's
level `N` this is `N`, but only `level_le` is proved here. -/
noncomputable def level : ℕ :=
  sInf {M | ModularForm.IsLevel k M f.toCuspForm}

lemma isLevel_level : ModularForm.IsLevel k f.level f.toCuspForm :=
  Nat.sInf_mem (s := {M | ModularForm.IsLevel k M f.toCuspForm}) ⟨N, f.isLevel⟩

lemma level_pos : 0 < f.level :=
  f.isLevel_level.1

/-- **The level of a newform of level `N` is at most `N`.** -/
lemma level_le : f.level ≤ N :=
  Nat.sInf_le f.isLevel

end HeckeRing.GL2.Newform
