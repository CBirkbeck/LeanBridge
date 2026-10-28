import Mathlib.RingTheory.FractionalIdeal.Basic
import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Congruence subgroups of Hilbert modular groups

Let `F` be a number field, real quadratic for the LMFDB, with ring of integers `𝒪_F`, and let `𝔟` be
a nonzero fractional ideal of `F`, the component ideal of a Hilbert modular surface. The
`𝒪_F`-module `𝒪_F ⊕ 𝔟` is the lattice of the column vectors `(x, y)` of `F²` with `x ∈ 𝒪_F` and
`y ∈ 𝔟`, and its automorphism group `GL(𝒪_F ⊕ 𝔟)` is the stabilizer of this lattice in `GL₂(F)`.
The Hilbert modular groups `GL⁺(𝒪_F ⊕ 𝔟)` and `SL(𝒪_F ⊕ 𝔟)` are its elements with totally positive
determinant, respectively with determinant `1`. For a nonzero ideal `𝔑` of `𝒪_F`, an element of
`GL(𝒪_F ⊕ 𝔟)` acts on `(𝒪_F ⊕ 𝔟)/𝔑(𝒪_F ⊕ 𝔟) = 𝒪_F/𝔑 ⊕ 𝔟/𝔑𝔟`, and the elements acting trivially
form the kernel of reduction modulo `𝔑`. Its intersection with `GL⁺(𝒪_F ⊕ 𝔟)` or `SL(𝒪_F ⊕ 𝔟)` is
a **principal congruence subgroup** `Γ_𝔟(𝔑)`; a **congruence subgroup** is a subgroup of
`GL⁺(𝒪_F ⊕ 𝔟)` or `SL(𝒪_F ⊕ 𝔟)` containing a principal congruence subgroup of the same group, and
its **level** is the least such `𝔑` for divisibility, that is, the largest such ideal.

Such a least ideal is unique when it exists, and `HilbertModularGroup.level` is the sum of all the
nonzero ideals `𝔑` with `Γ_𝔟(𝔑) ≤ Γ`, which is the level when there is one. In `SL(𝒪_F ⊕ 𝔟)` it
always exists, as `Γ_𝔟(𝔐) Γ_𝔟(𝔑) = Γ_𝔟(𝔐 + 𝔑)` there, which is not formalised here. In
`GL⁺(𝒪_F ⊕ 𝔟)` it need not: for `F = ℚ(√2)` and `𝔟 = 𝒪_F`, the totally positive units are the
powers of `ε = 3 + 2√2`, which has order `4` modulo `3` and `6` modulo `5`, so the elements of
`GL⁺(𝒪_F ⊕ 𝒪_F)` with determinant in `⟨ε²⟩` form a subgroup containing `Γ_𝔟(3)` and `Γ_𝔟(5)` but
not `Γ_𝔟(1)`. Reading "minimal" as "of least norm" does not help: `ε` has order `3` modulo both
prime ideals above `7`, and `1` modulo `√2` and `2`, so the elements with determinant in `⟨ε³⟩`
form a subgroup containing the principal congruence subgroups of these two ideals of norm `7`, but
that of no ideal of smaller norm.

The definitions make sense for any field `F`, `𝒪_F` being the integral closure of `ℤ` in `F`.

## Main definitions

* `HilbertModularGroup.lattice`: the lattice `𝒪_F ⊕ 𝔟` of `F²`.
* `HilbertModularGroup.gl`, `HilbertModularGroup.glPlus` and `HilbertModularGroup.sl`: the groups
  `GL(𝒪_F ⊕ 𝔟)`, `GL⁺(𝒪_F ⊕ 𝔟)` and `SL(𝒪_F ⊕ 𝔟)`.
* `HilbertModularGroup.reductionKernel`: the kernel of reduction modulo `𝔑` on `GL(𝒪_F ⊕ 𝔟)`.
* `HilbertModularGroup.principalCongruenceSubgroup` (LMFDB `hmsurface.congruence_subgroup`).
* `HilbertModularGroup.IsCongruenceSubgroup` (LMFDB `hmsurface.congruence_subgroup`).
* `HilbertModularGroup.IsLevel` and `HilbertModularGroup.level` (LMFDB
  `hmsurface.congruence_subgroup`).

## Main results

* `HilbertModularGroup.principalCongruenceSubgroup_mono`: `Γ_𝔟(𝔐) ≤ Γ_𝔟(𝔑)` when `𝔑 ∣ 𝔐`.
* `HilbertModularGroup.level_eq_of_isLevel`: a level, when it exists, is `level`.
-/

open Matrix NumberField
open scoped nonZeroDivisors

namespace HilbertModularGroup

variable {F : Type*} [Field F] (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (G Γ : Subgroup (GL (Fin 2) F))
  {g : GL (Fin 2) F} {𝔐 𝔑 : Ideal (𝓞 F)} {v x : Fin 2 → F}

/-- The lattice `𝒪_F ⊕ 𝔟` of `F²`: the column vectors `(x, y)` with `x ∈ 𝒪_F` and `y ∈ 𝔟`. -/
noncomputable def lattice : Submodule (𝓞 F) (Fin 2 → F) :=
  Submodule.pi Set.univ ![1, (𝔟 : Submodule (𝓞 F) F)]

lemma mem_lattice : v ∈ lattice 𝔟 ↔ v 0 ∈ (1 : Submodule (𝓞 F) F) ∧ v 1 ∈ 𝔟 := by
  simp [lattice]

/-- The group `GL(𝒪_F ⊕ 𝔟)` of automorphisms of the `𝒪_F`-module `𝒪_F ⊕ 𝔟`: the stabilizer of the
lattice `𝒪_F ⊕ 𝔟` in `GL₂(F)`, acting on column vectors. -/
noncomputable def gl : Subgroup (GL (Fin 2) F) where
  carrier := {g | ∀ v, v ∈ lattice 𝔟 ↔ g.val *ᵥ v ∈ lattice 𝔟}
  one_mem' v := by
    rw [Units.val_one, one_mulVec]
  mul_mem' {g h} hg hh v := by
    rw [Units.val_mul, ← mulVec_mulVec, hh, hg]
  inv_mem' {g} hg v := by
    rw [hg ((g⁻¹).val *ᵥ v), mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec]

/-- The Hilbert modular group `GL⁺(𝒪_F ⊕ 𝔟)`: the elements of `GL(𝒪_F ⊕ 𝔟)` with totally positive
determinant. -/
noncomputable def glPlus : Subgroup (GL (Fin 2) F) :=
  gl 𝔟 ⊓ totallyPositiveUnits.comap GeneralLinearGroup.det

/-- The Hilbert modular group `SL(𝒪_F ⊕ 𝔟)`: the elements of `GL(𝒪_F ⊕ 𝔟)` with determinant `1`. -/
noncomputable def sl : Subgroup (GL (Fin 2) F) :=
  gl 𝔟 ⊓ GeneralLinearGroup.det.ker

lemma sl_le_glPlus : sl 𝔟 ≤ glPlus 𝔟 :=
  inf_le_inf_left _ fun g hg ↦ by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
    exact one_mem _

lemma mulVec_mem_smul_lattice (hg : g ∈ gl 𝔟) (hx : x ∈ 𝔑 • lattice 𝔟) :
    g.val *ᵥ x ∈ 𝔑 • lattice 𝔟 := by
  have h : (𝔑 • lattice 𝔟).map ((mulVecLin g.val).restrictScalars (𝓞 F)) ≤ 𝔑 • lattice 𝔟 := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ (Submodule.map_le_iff_le_comap.mpr fun v hv ↦ (hg v).mp hv)
  exact h ⟨x, hx, rfl⟩

variable (𝔑) in
/-- The **kernel of reduction modulo `𝔑`** on `GL(𝒪_F ⊕ 𝔟)`: the elements acting trivially on
`(𝒪_F ⊕ 𝔟)/𝔑(𝒪_F ⊕ 𝔟) = 𝒪_F/𝔑 ⊕ 𝔟/𝔑𝔟`, that is, moving every vector of `𝒪_F ⊕ 𝔟` by a vector
of `𝔑(𝒪_F ⊕ 𝔟)`. -/
noncomputable def reductionKernel : Subgroup (GL (Fin 2) F) where
  carrier := {g | g ∈ gl 𝔟 ∧ ∀ v ∈ lattice 𝔟, g.val *ᵥ v - v ∈ 𝔑 • lattice 𝔟}
  one_mem' := ⟨one_mem _, fun v _ ↦ by simp⟩
  mul_mem' {g h} hg hh := by
    refine ⟨mul_mem hg.1 hh.1, fun v hv ↦ ?_⟩
    have h₁ : g.val *ᵥ (h.val *ᵥ v - v) + (g.val *ᵥ v - v) ∈ 𝔑 • lattice 𝔟 :=
      add_mem (mulVec_mem_smul_lattice 𝔟 hg.1 (hh.2 v hv)) (hg.2 v hv)
    rwa [mulVec_sub, sub_add_sub_cancel, mulVec_mulVec, ← Units.val_mul] at h₁
  inv_mem' {g} hg := by
    refine ⟨inv_mem hg.1, fun v hv ↦ ?_⟩
    have h₁ : -((g⁻¹).val *ᵥ (g.val *ᵥ v - v)) ∈ 𝔑 • lattice 𝔟 :=
      neg_mem (mulVec_mem_smul_lattice 𝔟 (inv_mem hg.1) (hg.2 v hv))
    rwa [mulVec_sub, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      neg_sub] at h₁

variable (𝔑) in
/-- The **principal congruence subgroup** `Γ_𝔟(𝔑)` (LMFDB `hmsurface.congruence_subgroup`) of a
Hilbert modular group `G`, which the LMFDB takes to be `GL⁺(𝒪_F ⊕ 𝔟)` or `SL(𝒪_F ⊕ 𝔟)`: the kernel
of reduction modulo `𝔑` on `G`. -/
noncomputable def principalCongruenceSubgroup : Subgroup (GL (Fin 2) F) :=
  G ⊓ reductionKernel 𝔟 𝔑

/-- **Principal congruence subgroups shrink as the level grows for divisibility**:
`Γ_𝔟(𝔐) ≤ Γ_𝔟(𝔑)` when `𝔑` divides `𝔐`, that is, when `𝔐 ≤ 𝔑`. -/
lemma principalCongruenceSubgroup_mono (h : 𝔐 ≤ 𝔑) :
    principalCongruenceSubgroup 𝔟 G 𝔐 ≤ principalCongruenceSubgroup 𝔟 G 𝔑 :=
  inf_le_inf_left _ fun _ hg ↦ ⟨hg.1, fun v hv ↦ Submodule.smul_mono_left h (hg.2 v hv)⟩

/-- A subgroup `Γ` of `GL₂(F)` is a **congruence subgroup** (LMFDB `hmsurface.congruence_subgroup`)
if it is a subgroup of one of the Hilbert modular groups `GL⁺(𝒪_F ⊕ 𝔟)` and `SL(𝒪_F ⊕ 𝔟)`
containing a principal congruence subgroup `Γ_𝔟(𝔑)` of that group, for a nonzero ideal `𝔑`. -/
def IsCongruenceSubgroup : Prop :=
  ∃ H ∈ ({glPlus 𝔟, sl 𝔟} : Set (Subgroup (GL (Fin 2) F))), Γ ≤ H ∧
    ∃ 𝔑 ≠ ⊥, principalCongruenceSubgroup 𝔟 H 𝔑 ≤ Γ

variable (𝔑) in
/-- A nonzero ideal `𝔑` is the **level** (LMFDB `hmsurface.congruence_subgroup`) of a subgroup `Γ`
of a Hilbert modular group `G` if `Γ` contains `Γ_𝔟(𝔑)` and `𝔑` is minimal for divisibility among
the nonzero ideals with this property: it divides, that is contains, every nonzero ideal `𝔐` with
`Γ_𝔟(𝔐) ≤ Γ`. Such an ideal need not exist in `GL⁺(𝒪_F ⊕ 𝔟)`; see the module docstring. -/
def IsLevel : Prop :=
  𝔑 ≠ ⊥ ∧ principalCongruenceSubgroup 𝔟 G 𝔑 ≤ Γ ∧
    ∀ 𝔐 ≠ ⊥, principalCongruenceSubgroup 𝔟 G 𝔐 ≤ Γ → 𝔐 ≤ 𝔑

/-- The **level** (LMFDB `hmsurface.congruence_subgroup`) of a subgroup `Γ` of a Hilbert modular
group `G`: the sum of the nonzero ideals `𝔑` with `Γ_𝔟(𝔑) ≤ Γ`, which is the largest of them, that
is, the least for divisibility, when there is one (`level_eq_of_isLevel`). This is the case for
the congruence subgroups of `SL(𝒪_F ⊕ 𝔟)`, but not always for those of `GL⁺(𝒪_F ⊕ 𝔟)`; see the
module docstring. -/
noncomputable def level : Ideal (𝓞 F) :=
  sSup {𝔑 | 𝔑 ≠ ⊥ ∧ principalCongruenceSubgroup 𝔟 G 𝔑 ≤ Γ}

/-- **A level of `Γ`, when it exists, is `level 𝔟 G Γ`.** -/
lemma level_eq_of_isLevel (h : IsLevel 𝔟 G Γ 𝔑) : level 𝔟 G Γ = 𝔑 :=
  IsGreatest.csSup_eq ⟨⟨h.1, h.2.1⟩, fun 𝔐 h𝔐 ↦ h.2.2 𝔐 h𝔐.1 h𝔐.2⟩

end HilbertModularGroup
