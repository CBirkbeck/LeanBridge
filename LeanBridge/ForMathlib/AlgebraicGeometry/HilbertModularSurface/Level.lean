import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.CongruenceSubgroup

/-!
# The congruence subgroups `Γ₀(𝔑)_𝔟` and their level

Let `F` be a number field, real quadratic for the LMFDB, with ring of integers `𝒪_F`, let `𝔟` be a
nonzero fractional ideal of `F` and `𝔑` a nonzero ideal of `𝒪_F`. The congruence subgroup
`Γ₀(𝔑)_𝔟` of a Hilbert modular group `G`, which the LMFDB takes to be `GL⁺(𝒪_F ⊕ 𝔟)`, is the
stabiliser in `G` of the lattice `𝒪_F ⊕ 𝔑𝔟` of `F²`: for `g = (a, b; c, d)` in `GL(𝒪_F ⊕ 𝔟)`,
so that `a, d ∈ 𝒪_F`, `b ∈ 𝔟⁻¹` and `c ∈ 𝔟`, this is the condition `c ∈ 𝔑𝔟`. It contains the
principal congruence subgroup `Γ_𝔟(𝔑)`, so it is a congruence subgroup. The level (LMFDB
`hmsurface.level`) of a Hilbert modular surface is the nonzero ideal `𝔑` that determines
`Γ₀(𝔑)_𝔟`; the LMFDB identifies it by its label (LMFDB `nf.ideal.label.hmf`), a database
convention not formalised here. That `𝔑` is the level of `Γ₀(𝔑)_𝔟` in the sense of
`HilbertModularGroup.IsLevel`, that is, that `Γ_𝔟(𝔐) ≤ Γ₀(𝔑)_𝔟` forces `𝔑 ∣ 𝔐`, is not formalised.

## Main definitions

* `HilbertModularGroup.gammaZeroLattice`: the lattice `𝒪_F ⊕ 𝔑𝔟` of `F²`.
* `HilbertModularGroup.gammaZero` (LMFDB `hmsurface.level`): the congruence subgroup `Γ₀(𝔑)_𝔟`.

## Main results

* `HilbertModularGroup.principalCongruenceSubgroup_le_gammaZero`: `Γ_𝔟(𝔑) ≤ Γ₀(𝔑)_𝔟`.
* `HilbertModularGroup.isCongruenceSubgroup_gammaZero`: `Γ₀(𝔑)_𝔟` is a congruence subgroup of
  `GL⁺(𝒪_F ⊕ 𝔟)` and of `SL(𝒪_F ⊕ 𝔟)`.
-/

open Matrix NumberField
open scoped nonZeroDivisors

namespace HilbertModularGroup

variable {F : Type*} [Field F] (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (G : Subgroup (GL (Fin 2) F))
  (𝔑 : Ideal (𝓞 F)) {g : GL (Fin 2) F} {v : Fin 2 → F}

/-- The lattice `𝒪_F ⊕ 𝔑𝔟` of `F²`: the column vectors `(x, y)` with `x ∈ 𝒪_F` and `y ∈ 𝔑𝔟`. -/
noncomputable def gammaZeroLattice : Submodule (𝓞 F) (Fin 2 → F) :=
  Submodule.pi Set.univ ![1, 𝔑 • (𝔟 : Submodule (𝓞 F) F)]

lemma mem_gammaZeroLattice : v ∈ gammaZeroLattice 𝔟 𝔑 ↔
    v 0 ∈ (1 : Submodule (𝓞 F) F) ∧ v 1 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := by
  simp [gammaZeroLattice]

/-- The congruence subgroup **`Γ₀(𝔑)_𝔟`** (LMFDB `hmsurface.level`, of level `𝔑`) of a Hilbert
modular group `G`, which the LMFDB takes to be `GL⁺(𝒪_F ⊕ 𝔟)`: the stabiliser in `G` of the lattice
`𝒪_F ⊕ 𝔑𝔟`, that is, for `G ≤ GL(𝒪_F ⊕ 𝔟)`, the matrices `(a, b; c, d)` of `G` with `c ∈ 𝔑𝔟`. -/
noncomputable def gammaZero : Subgroup (GL (Fin 2) F) where
  carrier := {g | g ∈ G ∧ ∀ v, v ∈ gammaZeroLattice 𝔟 𝔑 ↔ g.val *ᵥ v ∈ gammaZeroLattice 𝔟 𝔑}
  one_mem' := ⟨one_mem G, fun v ↦ by rw [Units.val_one, one_mulVec]⟩
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, fun v ↦ by
    rw [Units.val_mul, ← mulVec_mulVec, hh.2, hg.2]⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, fun v ↦ by
    rw [hg.2 ((g⁻¹).val *ᵥ v), mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec]⟩

lemma apply_one_mem_of_mem_smul_lattice (hv : v ∈ 𝔑 • lattice 𝔟) :
    v 1 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := by
  let π : (Fin 2 → F) →ₗ[𝓞 F] F := (LinearMap.proj (R := F) 1).restrictScalars (𝓞 F)
  have h : (𝔑 • lattice 𝔟).map π ≤ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ (Submodule.map_le_iff_le_comap.mpr fun w hw ↦
      ((mem_lattice 𝔟).mp hw).2)
  exact h ⟨v, hv, rfl⟩

lemma mulVec_mem_gammaZeroLattice (hg : g ∈ principalCongruenceSubgroup 𝔟 G 𝔑)
    (hv : v ∈ gammaZeroLattice 𝔟 𝔑) : g.val *ᵥ v ∈ gammaZeroLattice 𝔟 𝔑 := by
  have hv' : v ∈ lattice 𝔟 := (mem_lattice 𝔟).mpr ⟨((mem_gammaZeroLattice 𝔟 𝔑).mp hv).1,
    Submodule.smul_le_right ((mem_gammaZeroLattice 𝔟 𝔑).mp hv).2⟩
  have hgv : g.val *ᵥ v ∈ lattice 𝔟 := (hg.2.1 v).mp hv'
  have h₁ : (g.val *ᵥ v - v) 1 + v 1 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) :=
    add_mem (apply_one_mem_of_mem_smul_lattice 𝔟 𝔑 (hg.2.2 v hv'))
      ((mem_gammaZeroLattice 𝔟 𝔑).mp hv).2
  rw [Pi.sub_apply, sub_add_cancel] at h₁
  exact (mem_gammaZeroLattice 𝔟 𝔑).mpr ⟨((mem_lattice 𝔟).mp hgv).1, h₁⟩

/-- **`Γ₀(𝔑)_𝔟` contains the principal congruence subgroup `Γ_𝔟(𝔑)`.** -/
lemma principalCongruenceSubgroup_le_gammaZero :
    principalCongruenceSubgroup 𝔟 G 𝔑 ≤ gammaZero 𝔟 G 𝔑 := fun g hg ↦ by
  refine ⟨hg.1, fun v ↦ ⟨mulVec_mem_gammaZeroLattice 𝔟 G 𝔑 hg, fun hv ↦ ?_⟩⟩
  have h : (g⁻¹).val *ᵥ (g.val *ᵥ v) ∈ gammaZeroLattice 𝔟 𝔑 :=
    mulVec_mem_gammaZeroLattice 𝔟 G 𝔑 (inv_mem hg) hv
  rwa [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h

/-- **`Γ₀(𝔑)_𝔟` is a congruence subgroup** of `G = GL⁺(𝒪_F ⊕ 𝔟)` and of `G = SL(𝒪_F ⊕ 𝔟)` for a
nonzero ideal `𝔑`. -/
lemma isCongruenceSubgroup_gammaZero (hG : G ∈ ({glPlus 𝔟, sl 𝔟} : Set (Subgroup (GL (Fin 2) F))))
    (h𝔑 : 𝔑 ≠ ⊥) : IsCongruenceSubgroup 𝔟 (gammaZero 𝔟 G 𝔑) :=
  ⟨G, hG, fun _ hg ↦ hg.1, 𝔑, h𝔑, principalCongruenceSubgroup_le_gammaZero 𝔟 G 𝔑⟩

end HilbertModularGroup
