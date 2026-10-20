import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.Petersson
import TauCeti.NumberTheory.ModularForms.DiamondOperators
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# The Eisenstein subspace of a space of modular forms

The LMFDB defines the Eisenstein subspace `E_k(Γ)` of `M_k(Γ)`, for a finite-index subgroup `Γ` of
`SL₂(ℤ)`, as the orthogonal complement of the cusp forms `S_k(Γ)` under the Petersson scalar
product, and its elements as the Eisenstein forms; the Eisenstein forms of level `N` and character
`χ` are those in `M_k(N, χ)`. This file makes these definitions in every weight, and proves that
`M_k(Γ) = E_k(Γ) ⊕ S_k(Γ)` and `M_k(N, χ) = E_k(N, χ) ⊕ S_k(N, χ)`.

Tau Ceti defines, in weight at least `3`, Eisenstein subspaces as spans of Eisenstein series
(`TauCeti.eisensteinSubspace`, `TauCeti.EisensteinSeries.congruenceEisensteinSubspace`). These are
also complements of the cusp forms, but their equality with the orthogonal complement, which
amounts to the Petersson orthogonality of Eisenstein series and cusp forms, is not proved here.

## Main definitions

* `ModularForm.eisensteinFormSubmodule` (LMFDB `cmf.eisenstein_form`): the space `E_k(Γ)`.
* `ModularForm.eisensteinFormCharSpace` (LMFDB `cmf.eisenstein_form`): the space `E_k(N, χ)`.

## Main results

* `ModularForm.isCompl_eisensteinFormSubmodule_cuspFormSubmodule`: `M_k(Γ) = E_k(Γ) ⊕ S_k(Γ)`.
* `ModularForm.peterssonScalarProduct_slash_slash`: slashing by an element of `SL₂(ℤ)` normalising
  `Γ` preserves the Petersson scalar product.
* `ModularForm.diamondOp_mem_eisensteinFormSubmodule`: the diamond operators preserve `E_k(Γ₁(N))`.
* `ModularForm.isCompl_eisensteinFormCharSpace_range_cuspToModFormCharSpace`:
  `M_k(N, χ) = E_k(N, χ) ⊕ S_k(N, χ)`.
-/

open MeasureTheory Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm Pointwise

namespace ModularForm

section Subgroup

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)

/-- The **Eisenstein subspace** `E_k(Γ)` (LMFDB `cmf.eisenstein_form`) of the space `M_k(Γ)` of
modular forms of weight `k` for a finite-index subgroup `Γ` of `SL₂(ℤ)`: the orthogonal complement
of the cusp forms under the Petersson scalar product `peterssonScalarProduct`. Its elements are the
**Eisenstein forms** of weight `k` on `Γ`. It is a complement of the cusp forms
(`isCompl_eisensteinFormSubmodule_cuspFormSubmodule`). -/
noncomputable def eisensteinFormSubmodule : Submodule ℂ (ModularForm (Γ.map (mapGL ℝ)) k) :=
  LinearMap.ker peterssonScalarProductₛₗ

variable {Γ k} {f g f' g' : ModularForm (Γ.map (mapGL ℝ)) k}

lemma mem_eisensteinFormSubmodule_iff : f ∈ eisensteinFormSubmodule Γ k ↔
    ∀ g : CuspForm (Γ.map (mapGL ℝ)) k, peterssonScalarProduct f g = 0 := by
  rw [eisensteinFormSubmodule, LinearMap.mem_ker, LinearMap.ext_iff]
  rfl

variable (Γ k)

/-- **Every modular form is uniquely the sum of an Eisenstein form and a cusp form**:
`M_k(Γ) = E_k(Γ) ⊕ S_k(Γ)`. The cusp forms meet their orthogonal complement only in `0` because
the Petersson scalar product is positive definite on them, and they have a complement because they
form a finite-dimensional space. -/
lemma isCompl_eisensteinFormSubmodule_cuspFormSubmodule :
    IsCompl (eisensteinFormSubmodule Γ k) (cuspFormSubmodule (Γ.map (mapGL ℝ)) k) := by
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun f _ ↦ ?_)⟩
  · rintro _ hf ⟨c, rfl⟩
    rw [(peterssonScalarProduct_coe_self_eq_zero c).mp (mem_eisensteinFormSubmodule_iff.mp hf c),
      map_zero]
  let Φ : ModularForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ]
      (Fin (Module.finrank ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) → ℂ) :=
    LinearMap.pi fun i ↦ peterssonScalarProductₛₗ.flip (Module.finBasis ℂ _ i)
  have hΦ (f f' : ModularForm (Γ.map (mapGL ℝ)) k) (h : Φ f = Φ f') :
      peterssonScalarProductₛₗ f = peterssonScalarProductₛₗ f' :=
    (Module.finBasis ℂ (CuspForm (Γ.map (mapGL ℝ)) k)).ext fun i ↦ congrFun h i
  have hinj : Function.Injective (Φ ∘ₗ CuspForm.toModularFormₗ) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_
    have h0 : peterssonScalarProductₛₗ (c : ModularForm (Γ.map (mapGL ℝ)) k) = 0 :=
      (hΦ _ 0 (hc.trans (map_zero Φ).symm)).trans (map_zero _)
    exact (peterssonScalarProduct_coe_self_eq_zero c).mp (LinearMap.congr_fun h0 c)
  rcases (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Module.finrank_fin_fun ℂ).symm).mp hinj (Φ f) with ⟨c, hc⟩
  rw [← sub_add_cancel f (c : ModularForm (Γ.map (mapGL ℝ)) k)]
  refine Submodule.add_mem_sup ?_ ⟨c, rfl⟩
  rw [eisensteinFormSubmodule, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact hΦ _ _ hc.symm

variable {Γ k}

omit [Γ.FiniteIndex] in
/-- **The Petersson scalar product is invariant under a normalising slash**: if `γ ∈ SL₂(ℤ)`
normalises `Γ`, then `⟨f ∣ γ, g ∣ γ⟩_Γ = ⟨f, g⟩_Γ`. -/
lemma peterssonScalarProduct_slash_slash {γ : SL(2, ℤ)}
    (hγ : ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • Γ.map (mapGL ℝ) = Γ.map (mapGL ℝ))
    (hf : ⇑f' = ⇑f ∣[k] mapGL ℝ γ) (hg : ⇑g' = ⇑g ∣[k] mapGL ℝ γ) :
    peterssonScalarProduct f' g' = peterssonScalarProduct f g := by
  have h𝔉 : IsFundamentalDomain (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
      (γ • ⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, q.out⁻¹ • fdo) :=
    isFundamentalDomain_smul_of_inv_conjAct_eq hγ
      (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ)
  rw [peterssonScalarProduct, peterssonScalarProduct, hf, hg]
  exact congrArg _ ((peterssonInner_slash_slash_SL k γ _ g f).trans
    (peterssonInner_eq_of_isFundamentalDomain k g f h𝔉
      (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ)))

end Subgroup

section Character

variable {N : ℕ} {k : ℤ} (d : (ZMod N)ˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}

variable (f) in
lemma peterssonScalarProduct_diamondOp (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonScalarProduct (diamondOp k d f) (diamondOp k d g) = peterssonScalarProduct f g := by
  rcases Gamma0Map_toHomUnits_surjective d with ⟨γ, hγ⟩
  exact peterssonScalarProduct_slash_slash (Gamma1_map_inv_conjAct_eq γ) (coe_diamondOp k d γ hγ f)
    (coe_diamondOp k d γ hγ g)

lemma diamondOp_mem_cuspFormSubmodule (hf : f ∈ cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp k d f ∈ cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k := by
  rcases hf with ⟨c, rfl⟩
  exact ⟨diamondOpCusp k d c, (diamondOp_coe_cuspForm k d c).symm⟩

variable [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)

variable (k) in
/-- The **Eisenstein subspace** `E_k(N, χ)` (LMFDB `cmf.eisenstein_form`) of the space `M_k(N, χ)`
of modular forms of weight `k`, level `N` and character `χ`: the Eisenstein forms of
`E_k(Γ₁(N))` (`eisensteinFormSubmodule`) that lie in `M_k(N, χ)`, as a subspace of `M_k(N, χ)`
(Tau Ceti's `modFormCharSpace k χ`). It is a complement of the cusp forms of character `χ`
(`isCompl_eisensteinFormCharSpace_range_cuspToModFormCharSpace`). -/
noncomputable def eisensteinFormCharSpace : Submodule ℂ (modFormCharSpace k χ) :=
  (eisensteinFormSubmodule (Gamma1 N) k).comap (modFormCharSpace k χ).subtype

/-- **The diamond operators preserve the Eisenstein forms**, being unitary for the Petersson
scalar product and preserving the cusp forms. -/
lemma diamondOp_mem_eisensteinFormSubmodule (hf : f ∈ eisensteinFormSubmodule (Gamma1 N) k) :
    diamondOp k d f ∈ eisensteinFormSubmodule (Gamma1 N) k := by
  rw [mem_eisensteinFormSubmodule_iff] at hf ⊢
  intro c
  have hc : (c : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = diamondOp k d
      (diamondOpCusp k d⁻¹ c : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    rw [← diamondOp_coe_cuspForm, ← LinearMap.comp_apply, ← diamondOp_mul, mul_inv_cancel,
      diamondOp_one, LinearMap.id_apply]
  rw [hc, peterssonScalarProduct_diamondOp, hf]

/-- **Every modular form with character is uniquely the sum of an Eisenstein form and a cusp form
with the same character**: `M_k(N, χ) = E_k(N, χ) ⊕ S_k(N, χ)`, with `S_k(N, χ)` embedded in
`M_k(N, χ)` by Tau Ceti's `cuspToModFormCharSpace`. -/
lemma isCompl_eisensteinFormCharSpace_range_cuspToModFormCharSpace :
    IsCompl (eisensteinFormCharSpace k χ) (LinearMap.range (cuspToModFormCharSpace k χ)) := by
  have hES : IsCompl (eisensteinFormSubmodule (Gamma1 N) k)
      (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k) :=
    isCompl_eisensteinFormSubmodule_cuspFormSubmodule (Gamma1 N) k
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun x _ ↦ ?_)⟩
  · rintro _ hxE ⟨c, rfl⟩
    exact Subtype.ext (Submodule.disjoint_def.mp hES.disjoint _ hxE
      ⟨c, (coe_cuspToModFormCharSpace k χ c).symm⟩)
  have hx : (x : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ eisensteinFormSubmodule (Gamma1 N) k ⊔
      cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k :=
    hES.codisjoint.eq_top ▸ Submodule.mem_top
  rcases Submodule.mem_sup.mp hx with ⟨e, he, s, hs, hes⟩
  have heq (d : (ZMod N)ˣ) :
      diamondOp k d e - (χ d : ℂ) • e = (χ d : ℂ) • s - diamondOp k d s := by
    have hxd : diamondOp k d x = (χ d : ℂ) • (x : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
      diamondOp_apply_of_mem_modFormCharSpace k χ d x.2
    rw [← hes, map_add, smul_add] at hxd
    linear_combination (norm := module) hxd
  have h0 (d : (ZMod N)ˣ) : diamondOp k d e - (χ d : ℂ) • e = 0 :=
    Submodule.disjoint_def.mp hES.disjoint _
      (sub_mem (diamondOp_mem_eisensteinFormSubmodule d he) (Submodule.smul_mem _ _ he))
      (heq d ▸ sub_mem (Submodule.smul_mem _ _ hs) (diamondOp_mem_cuspFormSubmodule d hs))
  have heχ : e ∈ modFormCharSpace k χ :=
    (mem_modFormCharSpace_iff k χ e).mpr fun d ↦ sub_eq_zero.mp (h0 d)
  have hsχ : s ∈ modFormCharSpace k χ :=
    (mem_modFormCharSpace_iff k χ s).mpr fun d ↦ (sub_eq_zero.mp (heq d ▸ h0 d)).symm
  rw [show x = ⟨e, heχ⟩ + ⟨s, hsχ⟩ from Subtype.ext hes.symm]
  refine Submodule.add_mem_sup he ?_
  rcases hs with ⟨c, rfl⟩
  exact ⟨⟨c, (coe_mem_modFormCharSpace_iff k χ c).mp hsχ⟩, rfl⟩

end Character

end ModularForm
