import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.GammaZeroFundamentalDomain
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Quotient
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The levels of Bianchi modular forms

Let `K` be an imaginary quadratic field, embedded in `ℂ` by `σ`. The level of a Bianchi modular
form is a subgroup of the Bianchi group `GL₂(𝒪_K)`, such as `Γ₀(𝔑)`, acting on `ℋ₃` through its
image in `PSL(2, ℂ)`, and that image is discrete. Indeed a matrix of `SL(2, ℂ)` representing a
matrix of `GL₂(𝒪_K)` has entries of the same absolute values, since the units of `𝒪_K` have
absolute value `1`, and there are finitely many integers of `K` of bounded absolute value. So only
finitely many elements of the image in `PSL(2, ℂ)` of a subgroup of `GL₂(𝒪_K)` lie in the open
neighbourhood of `1` given by the matrices with entries of absolute value less than `2`; as
`PSL(2, ℂ)` is a `T1` space (the centre of `SL(2, ℂ)` is closed: Tau Ceti's instance
`Subgroup.isClosed_center`), removing them leaves an open neighbourhood of `1` meeting the image
only in `1`, which is therefore discrete.

A smaller level has a larger space of Bianchi modular forms. In particular the space of the
`SL₂`-level `Γ₀(𝔑) ∩ SL₂(𝒪_K)` contains the space of the level `Γ₀(𝔑)`.

## Main results

* `HyperbolicThreeSpace.discreteTopology_bianchiPSLGroup` (LMFDB `mf.bianchi.level`): the image in
  `PSL(2, ℂ)` of a subgroup of `GL₂(𝒪_K)` is discrete.
* `HyperbolicThreeSpace.discreteTopology_bianchiPSLGroup_bianchiGammaZero` (LMFDB
  `mf.bianchi.level`): the image of the level `Γ₀(𝔑)` in `PSL(2, ℂ)` is discrete.
* `HyperbolicThreeSpace.bianchiModularForms_le_of_le` (LMFDB `mf.bianchi.level`): a smaller level
  has a larger space of Bianchi modular forms.
* `HyperbolicThreeSpace.bianchiModularForms_gamma0GL_le` (LMFDB `mf.bianchi.level`): the forms of
  level `Γ₀(𝔑)` are forms of the `SL₂`-level `Γ₀(𝔑) ∩ SL₂(𝒪_K)`.
-/

open Matrix Module NumberField Set Topology

open scoped MatrixGroups

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] (σ : K →+* ℂ) (k : ℕ)

/-- **A smaller level has a larger space of Bianchi modular forms** (LMFDB `mf.bianchi.level`): a
form of level `Γ'` is a form of every level `Γ ≤ Γ'`. -/
lemma bianchiModularForms_le_of_le {Γ Γ' : Subgroup (GL (Fin 2) (𝓞 K))} (h : Γ ≤ Γ') :
    bianchiModularForms σ Γ' k ≤ bianchiModularForms σ Γ k :=
  fun _ hF ↦ ⟨hF.analyticAt, fun γ hγ ↦ hF.invariant γ (h hγ), hF.harmonic, hF.growth⟩

/-- **The forms of level `Γ₀(𝔑)` are forms of the `SL₂`-level `Γ₀(𝔑) ∩ SL₂(𝒪_K)`** (LMFDB
`mf.bianchi.level`), a subgroup of `Γ₀(𝔑)` through `SL₂(𝒪_K) ≤ GL₂(𝒪_K)`. -/
lemma bianchiModularForms_gamma0GL_le (𝔑 : Ideal (𝓞 K)) : bianchiModularForms σ 𝔑.gamma0GL k ≤
    bianchiModularForms σ (𝔑.gamma0SL.map SpecialLinearGroup.toGL) k :=
  bianchiModularForms_le_of_le σ k <| Subgroup.map_comap_le _ _

variable [NumberField K] [IsTotallyComplex K] {σ}

lemma norm_apply_eq_of_mk_eq {a g : SL(2, ℂ)}
    (h : (QuotientGroup.mk a : PSL(2, ℂ)) = QuotientGroup.mk g) (i j : Fin 2) :
    ‖g i j‖ = ‖a i j‖ := by
  rcases SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp (QuotientGroup.eq.mp h) with
    hc | hc
  · rw [inv_mul_eq_one.mp hc]
  · rw [← mul_inv_cancel_left a g, hc]
    simp

/-- **The image in `PSL(2, ℂ)` of a subgroup of the Bianchi group `GL₂(𝒪_K)` is discrete**, for an
imaginary quadratic field `K` (LMFDB `mf.bianchi.level`): this holds for every subgroup `Γ` of
`GL₂(K)` whose elements come from `GL₂(𝒪_K)`, such as the levels of Bianchi modular forms. -/
lemma discreteTopology_bianchiPSLGroup (hK : finrank ℚ K = 2) {Γ : Subgroup (GL (Fin 2) K)}
    (hΓ : Γ ≤ (GeneralLinearGroup.map (algebraMap (𝓞 K) K)).range) :
    DiscreteTopology (bianchiPSLGroup σ Γ) := by
  let A : Set SL(2, ℂ) := ⋂ i, ⋂ j, {g | ‖g i j‖ < 2}
  have hA : IsOpen A :=
    isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      isOpen_lt (by fun_prop) continuous_const
  let F : Set (GL (Fin 2) (𝓞 K)) :=
    {γ | ∀ i j, ‖σ ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j : K)‖ ≤ 2}
  have hF : F.Finite := by
    refine Finite.of_finite_image (f := fun γ : GL (Fin 2) (𝓞 K) ↦
      ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) : Fin 2 → Fin 2 → 𝓞 K)) ?_ Units.val_injective.injOn
    refine ((Finite.pi fun _ : Fin 2 ↦ Finite.pi fun _ : Fin 2 ↦
      finite_setOf_norm_apply_le (σ := σ) hK 2)).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩ i - j -
    exact hγ i j
  refine discreteTopology_of_isOpen_singleton_one <| isOpen_induced_iff.mpr
    ⟨QuotientGroup.mk '' A \ (glToPSL σ '' F \ {1}),
      (QuotientGroup.isOpenMap_coe _ hA).sdiff (hF.image _ |>.sdiff).isClosed, ?_⟩
  ext ⟨γ', hγ'⟩
  simp only [mem_singleton_iff, Subgroup.mk_eq_one]
  refine ⟨fun ⟨⟨a, ha, hag⟩, hγ'F⟩ ↦ not_not.mp fun h₁ ↦ hγ'F ⟨?_, h₁⟩, ?_⟩
  · rcases hγ' with ⟨g, ⟨x, hx, hg⟩, rfl⟩
    rcases hΓ hx with ⟨γ, rfl⟩
    refine ⟨γ, fun i j ↦ ?_, (mk_eq_glToPSL g hg).symm⟩
    rw [norm_apply_eq_of_isSLRepresentative g hK hg, norm_apply_eq_of_mk_eq hag]
    exact (mem_iInter₂.mp ha i j).le
  · rintro rfl
    refine ⟨⟨1, mem_iInter₂.mpr fun i j ↦ ?_, rfl⟩, fun h ↦ h.2 rfl⟩
    by_cases h : i = j <;> simp [h]

/-- **The level `Γ₀(𝔑)` is a discrete subgroup of `PSL(2, ℂ)`** (LMFDB `mf.bianchi.level`): its
image there is discrete, for an imaginary quadratic field `K`. -/
lemma discreteTopology_bianchiPSLGroup_bianchiGammaZero (hK : finrank ℚ K = 2) (𝔑 : Ideal (𝓞 K)) :
    DiscreteTopology (bianchiPSLGroup σ (bianchiGammaZero 𝔑)) :=
  discreteTopology_bianchiPSLGroup hK fun x hx ↦ by
    rcases (mem_bianchiGammaZero_iff x).mp hx with ⟨γ, -, rfl⟩
    exact ⟨γ, rfl⟩

end HyperbolicThreeSpace
