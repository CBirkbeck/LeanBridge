import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.Level
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# The level of `Γ₀(𝔑)_𝔟` is `𝔑`

Let `F` be a number field with ring of integers `𝒪_F`, `𝔟` a nonzero fractional ideal and `𝔑` a
nonzero ideal of `𝒪_F`. The congruence subgroup `Γ₀(𝔑)_𝔟` (LMFDB `hmsurface.level`,
`HilbertModularGroup.gammaZero`) of `G = GL⁺(𝒪_F ⊕ 𝔟)` or `G = SL(𝒪_F ⊕ 𝔟)` contains the principal
congruence subgroup `Γ_𝔟(𝔑)`, and `𝔑` is its level in the sense of LMFDB
`hmsurface.congruence_subgroup` (`HilbertModularGroup.IsLevel`): if `Γ_𝔟(𝔐) ≤ Γ₀(𝔑)_𝔟`, then
`𝔑 ∣ 𝔐`. Indeed, for `c ∈ 𝔐𝔟` the lower unipotent matrix `(1, 0; c, 1)` lies in `Γ_𝔟(𝔐)`, and
if it lies in `Γ₀(𝔑)_𝔟` it maps `(1, 0)` into `𝒪_F ⊕ 𝔑𝔟`, so that `c ∈ 𝔑𝔟`; then `𝔐𝔟 ≤ 𝔑𝔟`,
and `𝔐 ≤ 𝔑` as `𝔟` is invertible. So `𝔑` is the least ideal for divisibility whose principal
congruence subgroup lies in `Γ₀(𝔑)_𝔟`: the level `𝔑` determines `Γ₀(𝔑)_𝔟`, and is determined by
it.

## Main definitions

* `HilbertModularGroup.lowerUnipotent`: the lower unipotent matrix `(1, 0; c, 1)` of `GL₂(F)`.

## Main results

* `HilbertModularGroup.isLevel_gammaZero` (LMFDB `hmsurface.level`): `𝔑` is the level of
  `Γ₀(𝔑)_𝔟`.
* `HilbertModularGroup.level_gammaZero` (LMFDB `hmsurface.level`): the level of `Γ₀(𝔑)_𝔟` is
  `𝔑`.
-/

open Matrix NumberField

open scoped nonZeroDivisors

namespace HilbertModularGroup

variable {F : Type*} [Field F] (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (G : Subgroup (GL (Fin 2) F))
  {𝔐 𝔑 : Ideal (𝓞 F)} {N : Submodule (𝓞 F) F} {c x : F}

/-- The **lower unipotent matrix** `(1, 0; c, 1)` of `GL₂(F)`, with inverse `(1, 0; -c, 1)`. -/
def lowerUnipotent (c : F) : GL (Fin 2) F :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1], by simp [one_fin_two], by simp [one_fin_two]⟩

lemma lowerUnipotent_mulVec (c : F) (v : Fin 2 → F) :
    (lowerUnipotent c).val *ᵥ v = ![v 0, c * v 0 + v 1] := by
  ext i
  fin_cases i <;> simp [lowerUnipotent, dotProduct]

lemma mul_mem_of_mem_of_mem_one (hc : c ∈ N) (hx : x ∈ (1 : Submodule (𝓞 F) F)) : c * x ∈ N :=
  (mul_one N).le (Submodule.mul_mem_mul hc hx)

lemma lowerUnipotent_mem_gl (hc : c ∈ (𝔟 : Submodule (𝓞 F) F)) : lowerUnipotent c ∈ gl 𝔟 := by
  intro v
  rw [lowerUnipotent_mulVec, mem_lattice, mem_lattice, ← FractionalIdeal.mem_coe,
    ← FractionalIdeal.mem_coe]
  refine ⟨fun h ↦ ⟨h.1, add_mem (mul_mem_of_mem_of_mem_one hc h.1) h.2⟩, fun h ↦ ⟨h.1, ?_⟩⟩
  simpa using sub_mem h.2 (mul_mem_of_mem_of_mem_one hc h.1)

lemma lowerUnipotent_mem_sl (hc : c ∈ (𝔟 : Submodule (𝓞 F) F)) : lowerUnipotent c ∈ sl 𝔟 :=
  ⟨lowerUnipotent_mem_gl 𝔟 hc, MonoidHom.mem_ker.mpr (Units.ext (by simp [lowerUnipotent]))⟩

lemma single_mem_smul_lattice (hc : c ∈ 𝔐 • (𝔟 : Submodule (𝓞 F) F)) :
    Pi.single 1 c ∈ 𝔐 • lattice 𝔟 := by
  have h : (𝔐 • (𝔟 : Submodule (𝓞 F) F)).map (LinearMap.single (𝓞 F) (fun _ ↦ F) 1) ≤
      𝔐 • lattice 𝔟 := by
    rw [Submodule.map_smul'']
    refine smul_mono_right _ (Submodule.map_le_iff_le_comap.mpr fun b hb ↦ ?_)
    exact (mem_lattice 𝔟).mpr ⟨by simp, by simpa using hb⟩
  exact h ⟨c, hc, rfl⟩

lemma lowerUnipotent_mem_reductionKernel (hc : c ∈ 𝔐 • (𝔟 : Submodule (𝓞 F) F)) :
    lowerUnipotent c ∈ reductionKernel 𝔟 𝔐 := by
  refine ⟨lowerUnipotent_mem_gl 𝔟 (Submodule.smul_le_right hc), fun v hv ↦ ?_⟩
  have h : (lowerUnipotent c).val *ᵥ v - v = Pi.single 1 (c * v 0) := by
    rw [lowerUnipotent_mulVec]
    ext i
    fin_cases i <;> simp
  rw [h]
  exact single_mem_smul_lattice 𝔟 (mul_mem_of_mem_of_mem_one hc ((mem_lattice 𝔟).mp hv).1)

lemma lowerUnipotent_mem_principalCongruenceSubgroup
    (hG : G ∈ ({glPlus 𝔟, sl 𝔟} : Set (Subgroup (GL (Fin 2) F))))
    (hc : c ∈ 𝔐 • (𝔟 : Submodule (𝓞 F) F)) :
    lowerUnipotent c ∈ principalCongruenceSubgroup 𝔟 G 𝔐 := by
  have hsl : lowerUnipotent c ∈ sl 𝔟 := lowerUnipotent_mem_sl 𝔟 (Submodule.smul_le_right hc)
  refine ⟨?_, lowerUnipotent_mem_reductionKernel 𝔟 hc⟩
  rcases hG with rfl | rfl
  · exact sl_le_glPlus 𝔟 hsl
  · exact hsl

lemma mem_smul_of_lowerUnipotent_mem_gammaZero (h : lowerUnipotent c ∈ gammaZero 𝔟 G 𝔑) :
    c ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := by
  have h₁ : Pi.single 0 1 ∈ gammaZeroLattice 𝔟 𝔑 :=
    (mem_gammaZeroLattice 𝔟 𝔑).mpr ⟨by simp, by simp⟩
  simpa [lowerUnipotent] using ((mem_gammaZeroLattice 𝔟 𝔑).mp ((h.2 _).mp h₁)).2

lemma smul_le_smul_of_le_gammaZero (hG : G ∈ ({glPlus 𝔟, sl 𝔟} : Set (Subgroup (GL (Fin 2) F))))
    (hle : principalCongruenceSubgroup 𝔟 G 𝔐 ≤ gammaZero 𝔟 G 𝔑) :
    𝔐 • (𝔟 : Submodule (𝓞 F) F) ≤ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := fun _ hc ↦
  mem_smul_of_lowerUnipotent_mem_gammaZero 𝔟 G
    (hle (lowerUnipotent_mem_principalCongruenceSubgroup 𝔟 G hG hc))

variable [NumberField F]

lemma le_of_smul_le_smul (h𝔟 : 𝔟 ≠ 0)
    (h : 𝔐 • (𝔟 : Submodule (𝓞 F) F) ≤ 𝔑 • (𝔟 : Submodule (𝓞 F) F)) : 𝔐 ≤ 𝔑 := by
  have h₀ : 𝔑 • (𝔟 : Submodule (𝓞 F) F) ≤
      ((𝔑 * 𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) :=
    Submodule.smul_le.mpr fun r hr n hn ↦ by
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hn
  have h₁ : (𝔐 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟 ≤ 𝔑 * 𝔟 := by
    refine FractionalIdeal.mul_le.mpr fun i hi j hj ↦ ?_
    rcases (FractionalIdeal.mem_coeIdeal _).mp hi with ⟨y, hy, rfl⟩
    have h₂ : y • j ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := h (Submodule.smul_mem_smul hy hj)
    rw [Algebra.smul_def y j] at h₂
    exact h₀ h₂
  have h₃ : (𝔐 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟 * 𝔟⁻¹ ≤ 𝔑 * 𝔟 * 𝔟⁻¹ := mul_le_mul_left h₁ 𝔟⁻¹
  rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ h𝔟, mul_one, mul_one,
    FractionalIdeal.coeIdeal_le_coeIdeal] at h₃

/-- **`𝔑` is the level of `Γ₀(𝔑)_𝔟`** (LMFDB `hmsurface.level`), for `G = GL⁺(𝒪_F ⊕ 𝔟)` or
`G = SL(𝒪_F ⊕ 𝔟)`: `Γ₀(𝔑)_𝔟` contains `Γ_𝔟(𝔑)`, and if it contains `Γ_𝔟(𝔐)` then `𝔑 ∣ 𝔐`, as
`(1, 0; c, 1) ∈ Γ_𝔟(𝔐)` for `c ∈ 𝔐𝔟`. -/
lemma isLevel_gammaZero (h𝔟 : 𝔟 ≠ 0)
    (hG : G ∈ ({glPlus 𝔟, sl 𝔟} : Set (Subgroup (GL (Fin 2) F)))) (h𝔑 : 𝔑 ≠ ⊥) :
    IsLevel 𝔟 G (gammaZero 𝔟 G 𝔑) 𝔑 :=
  ⟨h𝔑, principalCongruenceSubgroup_le_gammaZero 𝔟 G 𝔑, fun _ _ hle ↦
    le_of_smul_le_smul 𝔟 h𝔟 (smul_le_smul_of_le_gammaZero 𝔟 G hG hle)⟩

/-- **The level of `Γ₀(𝔑)_𝔟` is `𝔑`** (LMFDB `hmsurface.level`), for `G = GL⁺(𝒪_F ⊕ 𝔟)` or
`G = SL(𝒪_F ⊕ 𝔟)`. -/
lemma level_gammaZero (h𝔟 : 𝔟 ≠ 0)
    (hG : G ∈ ({glPlus 𝔟, sl 𝔟} : Set (Subgroup (GL (Fin 2) F)))) (h𝔑 : 𝔑 ≠ ⊥) :
    level 𝔟 G (gammaZero 𝔟 G 𝔑) = 𝔑 :=
  level_eq_of_isLevel 𝔟 G _ (isLevel_gammaZero 𝔟 G h𝔟 hG h𝔑)

end HilbertModularGroup
