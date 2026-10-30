import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.Label

/-!
# The congruence subgroups of the surfaces `X_0(𝔑)_𝔟` and `X_0^1(𝔑)_𝔟`

Let `F` be a number field, real quadratic for the LMFDB, `𝔟` a fractional ideal of `F` (the
component ideal) and `𝔑` an ideal of `𝒪_F` (the level). The Hilbert modular surface `X_0(𝔑)_𝔟`
(LMFDB `hmsurface.x0`) is the surface `X(Γ)` of the subgroup `Γ = Γ₀(𝔑)_𝔟` of `GL⁺(𝒪_F ⊕ 𝔟)`, and
`X_0^1(𝔑)_𝔟` (LMFDB `hmsurface.x01`) that of the subgroup `Γ₀¹(𝔑)_𝔟` of `SL(𝒪_F ⊕ 𝔟)`: in both
cases the inverse image of the upper triangular matrices `(∗ ∗; 0 ∗)` under reduction modulo `𝔑`,
from `GL(𝒪_F ⊕ 𝔟)` to `GL(𝒪_F/𝔑 ⊕ 𝔟/𝔑𝔟)`. A matrix `g = (a, b; c, d)` of `GL(𝒪_F ⊕ 𝔟)`, acting on
column vectors, has `a ∈ 𝒪_F`, `b𝔟 ⊆ 𝒪_F`, `c ∈ 𝔟` and `d𝔟 ⊆ 𝔟`, and the lower left entry of its
reduction is the map `𝒪_F/𝔑 → 𝔟/𝔑𝔟`, `x ↦ c x`, so that the reduction is upper triangular exactly
when `c ∈ 𝔑𝔟`.

LeanBridge defines these groups as the stabilisers `HilbertModularGroup.gammaZero` of the lattice
`𝒪_F ⊕ 𝔑𝔟` in `GL⁺(𝒪_F ⊕ 𝔟)` and in `SL(𝒪_F ⊕ 𝔟)`
(`HilbertModularGroup.SurfaceType.congruenceSubgroup`). The main result
`HilbertModularGroup.mem_gammaZero_iff` shows that they are the knowls' groups: an element of
`GL(𝒪_F ⊕ 𝔟)` stabilises `𝒪_F ⊕ 𝔑𝔟` if and only if `c ∈ 𝔑𝔟`. For the converse, the lower left
entry `c'` of `g⁻¹ = (a', b'; c', d')` is `-a' (d' c) + (b' c') c`, since `g⁻¹ g = 1`, and so lies
in `𝔑𝔟` with `c`.

The surfaces themselves and their moduli interpretations are not available: `X_0(𝔑)_𝔟`
parametrizes the triples `(A, ι, φ)` of an abelian surface `A` whose polarization module is
isomorphic to `(𝔡_F 𝔟)⁻¹`, an embedding `ι : 𝒪_F → End(A_{ℚ̄})` and an isogeny `φ : A → A'` with
kernel isomorphic to `𝒪_F/𝔑` compatible with `ι`, and `X_0^1(𝔑)_𝔟` the quadruples `(A, ι, λ, φ)`
with a polarization `λ` whose polarization module is isomorphic to `(𝔡_F 𝔟)⁻¹`; this needs dual
abelian varieties and polarizations.

## Main results

* `HilbertModularGroup.mem_gammaZero_iff` (LMFDB `hmsurface.x0`, `hmsurface.x01`): `Γ₀(𝔑)_𝔟` is
  the inverse image of the upper triangular matrices modulo `𝔑`.
* `HilbertModularGroup.SurfaceType.mem_congruenceSubgroup_iff` (LMFDB `hmsurface.x0`,
  `hmsurface.x01`): the congruence subgroups of `X_0(𝔑)_𝔟` and `X_0^1(𝔑)_𝔟` are the matrices
  `(a, b; c, d)` of `GL⁺(𝒪_F ⊕ 𝔟)` and of `SL(𝒪_F ⊕ 𝔟)` with `c ∈ 𝔑𝔟`.
-/

open Matrix NumberField

open scoped nonZeroDivisors

namespace HilbertModularGroup

variable {F : Type*} [Field F] (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (G : Subgroup (GL (Fin 2) F))
  (𝔑 : Ideal (𝓞 F)) {g : GL (Fin 2) F} {v : Fin 2 → F} {y : F}

lemma single_one_mem_smul_lattice (hy : y ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F)) :
    Pi.single 1 y ∈ 𝔑 • lattice 𝔟 := by
  let ι : F →ₗ[𝓞 F] Fin 2 → F := (LinearMap.single F (fun _ ↦ F) 1).restrictScalars (𝓞 F)
  have h : (𝔑 • (𝔟 : Submodule (𝓞 F) F)).map ι ≤ 𝔑 • lattice 𝔟 := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ <| Submodule.map_le_iff_le_comap.mpr fun z hz ↦
      (mem_lattice 𝔟).mpr ⟨by simp [ι], by simpa [ι] using hz⟩
  exact h ⟨y, hy, rfl⟩

lemma mulVec_mem_gammaZeroLattice_of_mem_gl (hg : g ∈ gl 𝔟)
    (hc : g.val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F)) (hv : v ∈ gammaZeroLattice 𝔟 𝔑) :
    g.val *ᵥ v ∈ gammaZeroLattice 𝔟 𝔑 := by
  rcases (mem_gammaZeroLattice 𝔟 𝔑).mp hv with ⟨hv₀, hv₁⟩
  have hgv : g.val *ᵥ v ∈ lattice 𝔟 :=
    (hg v).mp <| (mem_lattice 𝔟).mpr ⟨hv₀, Submodule.smul_le_right hv₁⟩
  rcases Submodule.mem_one.mp hv₀ with ⟨r, hr⟩
  have h₁ : (g.val *ᵥ Pi.single 1 (v 1)) 1 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) :=
    apply_one_mem_of_mem_smul_lattice 𝔟 𝔑 <| mulVec_mem_smul_lattice 𝔟 hg <|
      single_one_mem_smul_lattice 𝔟 𝔑 hv₁
  have h : (g.val *ᵥ v) 1 = r • g.val 1 0 + (g.val *ᵥ Pi.single 1 (v 1)) 1 := by
    simp [mulVec, ← hr, Algebra.smul_def, mul_comm]
  refine (mem_gammaZeroLattice 𝔟 𝔑).mpr ⟨((mem_lattice 𝔟).mp hgv).1, ?_⟩
  rw [h]
  exact add_mem (Submodule.smul_mem _ r hc) h₁

lemma inv_apply_one_zero_mem (hg : g ∈ gl 𝔟) (hc : g.val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F)) :
    (g⁻¹).val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := by
  have hg' : g⁻¹ ∈ gl 𝔟 := inv_mem hg
  have h₀ : (g⁻¹).val *ᵥ Pi.single 0 1 ∈ lattice 𝔟 :=
    (hg' _).mp <| (mem_lattice 𝔟).mpr ⟨by simp, by simpa using 𝔟.zero_mem⟩
  rw [mulVec_single_one, mem_lattice, col_apply, col_apply] at h₀
  have h₁ : (g⁻¹).val *ᵥ Pi.single 1 ((g⁻¹).val 1 0) ∈ lattice 𝔟 :=
    (hg' _).mp <| (mem_lattice 𝔟).mpr ⟨by simp, by simpa using h₀.2⟩
  have h₂ : ((g⁻¹).val *ᵥ Pi.single 1 (g.val 1 0)) 1 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) :=
    apply_one_mem_of_mem_smul_lattice 𝔟 𝔑 <| mulVec_mem_smul_lattice 𝔟 hg' <|
      single_one_mem_smul_lattice 𝔟 𝔑 hc
  rw [mulVec_single, mem_lattice, Pi.smul_apply, Pi.smul_apply, col_apply, col_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at h₁
  rw [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op] at h₂
  have h : (g⁻¹).val * g.val = 1 := g.inv_mul
  have e₀ : (g⁻¹).val 0 0 * g.val 0 0 + (g⁻¹).val 0 1 * g.val 1 0 = 1 := by
    simpa [mul_apply] using congrFun (congrFun h 0) 0
  have e₁ : (g⁻¹).val 1 0 * g.val 0 0 + (g⁻¹).val 1 1 * g.val 1 0 = 0 := by
    simpa [mul_apply] using congrFun (congrFun h 1) 0
  have e : (g⁻¹).val 1 0 = -((g⁻¹).val 0 0 * ((g⁻¹).val 1 1 * g.val 1 0)) +
      (g⁻¹).val 0 1 * (g⁻¹).val 1 0 * g.val 1 0 := by
    linear_combination (-(g⁻¹).val 1 0) * e₀ + (g⁻¹).val 0 0 * e₁
  rcases Submodule.mem_one.mp h₀.1 with ⟨r, hr⟩
  rcases Submodule.mem_one.mp h₁.1 with ⟨s, hs⟩
  rw [e, ← hr, ← hs, ← Algebra.smul_def, ← Algebra.smul_def]
  exact add_mem (neg_mem <| Submodule.smul_mem _ r h₂) (Submodule.smul_mem _ s hc)

/-- **`Γ₀(𝔑)_𝔟` is the inverse image of the upper triangular matrices modulo `𝔑`**: for a subgroup
`G` of `GL(𝒪_F ⊕ 𝔟)`, such as `GL⁺(𝒪_F ⊕ 𝔟)` or `SL(𝒪_F ⊕ 𝔟)`, the stabiliser in `G` of the
lattice `𝒪_F ⊕ 𝔑𝔟` consists of the matrices `(a, b; c, d)` of `G` with `c ∈ 𝔑𝔟`, those whose
reduction modulo `𝔑`, acting on `𝒪_F/𝔑 ⊕ 𝔟/𝔑𝔟`, is upper triangular. -/
lemma mem_gammaZero_iff (hG : G ≤ gl 𝔟) :
    g ∈ gammaZero 𝔟 G 𝔑 ↔ g ∈ G ∧ g.val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := by
  refine ⟨fun hg ↦ ⟨hg.1, ?_⟩, fun hg ↦ ⟨hg.1, fun v ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩⟩⟩
  · have h : g.val *ᵥ Pi.single 0 1 ∈ gammaZeroLattice 𝔟 𝔑 :=
      (hg.2 _).mp <| (mem_gammaZeroLattice 𝔟 𝔑).mpr ⟨by simp, by simp⟩
    simpa using ((mem_gammaZeroLattice 𝔟 𝔑).mp h).2
  · exact mulVec_mem_gammaZeroLattice_of_mem_gl 𝔟 𝔑 (hG hg.1) hg.2 hv
  · have h : (g⁻¹).val *ᵥ (g.val *ᵥ v) ∈ gammaZeroLattice 𝔟 𝔑 :=
      mulVec_mem_gammaZeroLattice_of_mem_gl 𝔟 𝔑 (inv_mem (hG hg.1))
        (inv_apply_one_zero_mem 𝔟 𝔑 (hG hg.1) hg.2) hv
    rwa [mulVec_mulVec, g.inv_mul, one_mulVec] at h

namespace SurfaceType

variable (s : SurfaceType)

lemma group_le_gl : s.group 𝔟 ≤ HilbertModularGroup.gl 𝔟 := by
  cases s <;> exact inf_le_left

/-- **The congruence subgroups `Γ₀¹(𝔑)_𝔟` of `X_0^1(𝔑)_𝔟` and `Γ₀(𝔑)_𝔟` of `X_0(𝔑)_𝔟` are the
inverse images of the upper triangular matrices modulo `𝔑`**: the matrices `(a, b; c, d)` of
`SL(𝒪_F ⊕ 𝔟)`, respectively `GL⁺(𝒪_F ⊕ 𝔟)`, with `c ∈ 𝔑𝔟`. -/
lemma mem_congruenceSubgroup_iff :
    g ∈ s.congruenceSubgroup 𝔟 𝔑 ↔ g ∈ s.group 𝔟 ∧ g.val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) :=
  mem_gammaZero_iff 𝔟 _ 𝔑 (s.group_le_gl 𝔟)

end SurfaceType

end HilbertModularGroup
