import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeFourier

/-!
# The coset decomposition of the Hecke operators `T_𝔭` on Hilbert modular forms

Let `F` be a number field, `𝔑` a nonzero ideal of `𝒪_F`, `𝔟` a fractional ideal and `𝔭 = (π)` a
prime ideal with `π` totally positive and `𝔭 + 𝔑 = 𝒪_F`. The right cosets `Γ₀(𝔑)_𝔟 α` of the
matrices `α = (a, b; c, d)` of `HilbertModularGroup.heckeSet 𝔑 𝔭 𝔟 𝔟` (`a, d ∈ 𝒪_F`, `b ∈ 𝔟⁻¹`,
`c ∈ 𝔑𝔟`, `(det α) = 𝔭`, `det α ≫ 0`) are the cosets of `(π, 0; 0, 1)` and of the `(1, β; 0, π)`,
`β ∈ 𝔟⁻¹ / π 𝔟⁻¹`, each exactly once. This is the hypothesis
`HilbertModularForm.IsHeckeCosetDecomposition` of `Hilbert/HeckeFourier.lean`, which is therefore
discharged for every such prime. For a prime `𝔭 ⊇ 𝔑`, the same argument gives the cosets of the
operator `U_𝔭` in `Hilbert/HeckeU.lean`.

The proof is elementwise and avoids counting lattices. A matrix `γ` with `γ₀₀, γ₁₁ ∈ 𝒪_F`,
`γ₀₁ ∈ 𝔟⁻¹`, `γ₁₀ ∈ 𝔑𝔟` and `(det γ)⁻¹ ∈ 𝒪_F` totally positive lies in `Γ₀(𝔑)_𝔟`, since its
inverse has entries of the same kind. For `α` in the Hecke set, `α (1, β; 0, π)⁻¹` has entries
`a, π⁻¹(b - aβ), c, π⁻¹(d - cβ)` and `α (π, 0; 0, 1)⁻¹` has entries `π⁻¹a, b, π⁻¹c, d`, so:

* if `c ∈ π𝔟` and `a ∈ 𝔭`, then `π⁻¹c ∈ π⁻¹c (𝔭 + 𝔑) ⊆ 𝔑𝔟` and `α` lies in the coset of
  `(π, 0; 0, 1)`;
* if `a ∉ 𝔭`, choose `a'` with `a'a ≡ 1 mod 𝔭` and `β = a'b`; then `a(d - cβ) ≡ det α ≡ 0`, so
  `d - cβ ∈ 𝔭`;
* if `c ∉ π𝔟`, there is `β₁ ∈ 𝔟⁻¹` with `e = cβ₁ ∉ 𝔭`; with `e'e ≡ 1` and `β = d e' β₁`,
  `d - cβ ∈ 𝔭`, and `e (b - aβ) y ∈ 𝔭` for `y ∈ 𝔟` gives `b - aβ ∈ π𝔟⁻¹`.

Distinct representatives give distinct cosets, by the entries `π⁻¹(β' - β)` and `π⁻¹` of
`(1, β'; 0, π)(1, β; 0, π)⁻¹` and `(1, β; 0, π)(π, 0; 0, 1)⁻¹`.

## Main results

* `HilbertModularForm.isHeckeCosetDecomposition`: the coset decomposition of `T_𝔭`.
* `HilbertModularForm.heckeIdealEigenvalueNormalised_eq_idealCoeff_of_isPrime` (LMFDB
  `mf.hilbert.eigenvalue`): for a normalised eigenform whose components have Fourier expansions, the
  normalised eigenvalue of `T_𝔭` at a prime `𝔭 = (π)`, `π ≫ 0`, `𝔭 ∤ 𝔑`, is `a_𝔭`, with no
  hypothesis on cosets.
-/

open Matrix NumberField HilbertModularGroup

open scoped nonZeroDivisors

namespace HilbertModularGroup

variable {F : Type*} [Field F] {M : Submodule (𝓞 F) F} {A : Matrix (Fin 2) (Fin 2) F} {x y : F}
  {v : Fin 2 → F} {𝔑 : Ideal (𝓞 F)} {𝔟 : FractionalIdeal (𝓞 F)⁰ F} {g : GL (Fin 2) F}

lemma mul_mem_of_mem_one (hx : x ∈ (1 : Submodule (𝓞 F) F)) (hy : y ∈ M) : x * y ∈ M := by
  simpa using Submodule.mul_mem_mul hx hy

lemma mulVec_mem_pi (h₀₀ : A 0 0 ∈ (1 : Submodule (𝓞 F) F))
    (h₀₁ : ∀ y ∈ M, A 0 1 * y ∈ (1 : Submodule (𝓞 F) F)) (h₁₀ : A 1 0 ∈ M)
    (h₁₁ : A 1 1 ∈ (1 : Submodule (𝓞 F) F)) (hv : v ∈ Submodule.pi Set.univ ![1, M]) :
    A *ᵥ v ∈ Submodule.pi Set.univ ![1, M] := by
  have h₀ : v 0 ∈ (1 : Submodule (𝓞 F) F) := hv 0 (Set.mem_univ 0)
  have h₁ : v 1 ∈ M := hv 1 (Set.mem_univ 1)
  rintro i -
  fin_cases i
  · simpa [mulVec] using add_mem (mul_mem_one h₀₀ h₀) (h₀₁ _ h₁)
  · simpa [mulVec] using
      add_mem (mul_comm (v 0) _ ▸ mul_mem_of_mem_one h₀ h₁₀) (mul_mem_of_mem_one h₁₁ h₁)

lemma val_inv_eq : (g⁻¹).val = g.det.val⁻¹ • !![g.val 1 1, -g.val 0 1; -g.val 1 0, g.val 0 0] := by
  rw [coe_units_inv, inv_def, adjugate_fin_two, Ring.inverse_eq_inv',
    GeneralLinearGroup.val_det_apply]

lemma mem_pi_iff_mulVec_mem (h₀₀ : g.val 0 0 ∈ (1 : Submodule (𝓞 F) F))
    (h₀₁ : ∀ y ∈ M, g.val 0 1 * y ∈ (1 : Submodule (𝓞 F) F)) (h₁₀ : g.val 1 0 ∈ M)
    (h₁₁ : g.val 1 1 ∈ (1 : Submodule (𝓞 F) F)) (hdet : g.det.val⁻¹ ∈ (1 : Submodule (𝓞 F) F)) :
    v ∈ Submodule.pi Set.univ ![1, M] ↔ g.val *ᵥ v ∈ Submodule.pi Set.univ ![1, M] := by
  refine ⟨mulVec_mem_pi h₀₀ h₀₁ h₁₀ h₁₁, fun h ↦ ?_⟩
  have hv : (g⁻¹).val *ᵥ (g.val *ᵥ v) = v := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [← hv, val_inv_eq]
  refine mulVec_mem_pi ?_ (fun y hy ↦ ?_) ?_ ?_ h
  · simpa using mul_mem_one hdet h₁₁
  · simpa [mul_assoc] using neg_mem (mul_mem_one hdet (h₀₁ y hy))
  · simpa using neg_mem (mul_mem_of_mem_one hdet h₁₀)
  · simpa using mul_mem_one hdet h₀₀

lemma mem_gammaZero_of_apply_mem (h₀₀ : g.val 0 0 ∈ (1 : Submodule (𝓞 F) F))
    (h₀₁ : ∀ y ∈ 𝔟, g.val 0 1 * y ∈ (1 : Submodule (𝓞 F) F))
    (h₁₀ : g.val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F)) (h₁₁ : g.val 1 1 ∈ (1 : Submodule (𝓞 F) F))
    (hdet : g.det.val⁻¹ ∈ (1 : Submodule (𝓞 F) F)) (hpos : IsTotallyPositive g.det.val) :
    g ∈ gammaZero 𝔟 (glPlus 𝔟) 𝔑 :=
  ⟨⟨fun _ ↦ mem_pi_iff_mulVec_mem h₀₀ h₀₁ (Submodule.smul_le_right h₁₀) h₁₁ hdet,
    Subgroup.mem_comap.mpr (mem_totallyPositiveUnits.mpr hpos)⟩,
    fun _ ↦ mem_pi_iff_mulVec_mem h₀₀ (fun y hy ↦ h₀₁ y (Submodule.smul_le_right hy)) h₁₀ h₁₁ hdet⟩

variable (π : Fˣ) (β : F) (α : GL (Fin 2) F)

lemma val_mul_inv_heckeUpper : (α * (heckeUpper π β)⁻¹).val =
    !![α.val 0 0, (π : F)⁻¹ * (α.val 0 1 - α.val 0 0 * β);
      α.val 1 0, (π : F)⁻¹ * (α.val 1 1 - α.val 1 0 * β)] := by
  rw [Units.val_mul, val_inv_eq, det_heckeUpper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeUpper, mul_apply] <;> ring1

lemma val_mul_inv_heckeLower : (α * (heckeLower π)⁻¹).val =
    !![(π : F)⁻¹ * α.val 0 0, α.val 0 1; (π : F)⁻¹ * α.val 1 0, α.val 1 1] := by
  rw [Units.val_mul, val_inv_eq, det_heckeLower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeLower, mul_apply] <;> ring1

lemma det_mul_inv_heckeUpper : (α * (heckeUpper π β)⁻¹).det.val = α.det.val * (π : F)⁻¹ := by
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, det_heckeUpper]

lemma det_mul_inv_heckeLower : (α * (heckeLower π)⁻¹).det.val = α.det.val * (π : F)⁻¹ := by
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, det_heckeLower]

variable {π β α} in
lemma mk_heckeUpper_eq_mk (hpos : IsTotallyPositive α.det.val) (hπ : IsTotallyPositive (π : F))
    (hdet : (α.det.val * (π : F)⁻¹)⁻¹ ∈ (1 : Submodule (𝓞 F) F))
    (h₀₀ : α.val 0 0 ∈ (1 : Submodule (𝓞 F) F))
    (h₀₁ : ∀ y ∈ 𝔟, (π : F)⁻¹ * (α.val 0 1 - α.val 0 0 * β) * y ∈ (1 : Submodule (𝓞 F) F))
    (h₁₀ : α.val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F))
    (h₁₁ : (π : F)⁻¹ * (α.val 1 1 - α.val 1 0 * β) ∈ (1 : Submodule (𝓞 F) F)) :
    (⟦heckeUpper π β⟧ : gammaZeroRightCosets 𝔑 𝔟) = ⟦α⟧ := by
  refine Quotient.sound <| QuotientGroup.rightRel_apply.mpr <| mem_gammaZero_of_apply_mem ?_
    (fun y hy ↦ ?_) ?_ ?_ ?_ ?_
  all_goals try rw [val_mul_inv_heckeUpper]
  · simpa using h₀₀
  · simpa using h₀₁ y hy
  · simpa using h₁₀
  · simpa using h₁₁
  · rwa [det_mul_inv_heckeUpper]
  · rw [det_mul_inv_heckeUpper]
    exact hpos.mul hπ.inv

variable {π α} in
lemma mk_heckeLower_eq_mk (hpos : IsTotallyPositive α.det.val) (hπ : IsTotallyPositive (π : F))
    (hdet : (α.det.val * (π : F)⁻¹)⁻¹ ∈ (1 : Submodule (𝓞 F) F))
    (h₀₀ : (π : F)⁻¹ * α.val 0 0 ∈ (1 : Submodule (𝓞 F) F))
    (h₀₁ : ∀ y ∈ 𝔟, α.val 0 1 * y ∈ (1 : Submodule (𝓞 F) F))
    (h₁₀ : (π : F)⁻¹ * α.val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F))
    (h₁₁ : α.val 1 1 ∈ (1 : Submodule (𝓞 F) F)) :
    (⟦heckeLower π⟧ : gammaZeroRightCosets 𝔑 𝔟) = ⟦α⟧ := by
  refine Quotient.sound <| QuotientGroup.rightRel_apply.mpr <| mem_gammaZero_of_apply_mem ?_
    (fun y hy ↦ ?_) ?_ ?_ ?_ ?_
  all_goals try rw [val_mul_inv_heckeLower]
  · simpa using h₀₀
  · simpa using h₀₁ y hy
  · simpa using h₁₀
  · simpa using h₁₁
  · rwa [det_mul_inv_heckeLower]
  · rw [det_mul_inv_heckeLower]
    exact hpos.mul hπ.inv

end HilbertModularGroup

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {π : Fˣ} {𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {𝔭 𝔑 : Ideal (𝓞 F)} {α : GL (Fin 2) F} {x y β : F}

lemma mul_mem_one_of_mem_translationLattice (hx : x ∈ translationLattice 𝔟)
    (hy : y ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : x * y ∈ (1 : Submodule (𝓞 F) F) := by
  have h : x * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.mem_inv_iff (Units.ne_zero 𝔟)).mp (by rwa [← Units.val_inv_eq_inv_val]) y hy
  rwa [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at h

lemma mem_translationLattice_of_forall
    (h : ∀ y ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F), x * y ∈ (1 : Submodule (𝓞 F) F)) :
    x ∈ translationLattice 𝔟 := by
  rw [translationLattice, FractionalIdeal.mem_coe, Units.val_inv_eq_inv_val,
    FractionalIdeal.mem_inv_iff (Units.ne_zero 𝔟)]
  intro y hy
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
  exact h y hy

lemma inv_mul_algebraMap_mem_one_iff
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (r : 𝓞 F) : (π : F)⁻¹ * algebraMap (𝓞 F) F r ∈ (1 : Submodule (𝓞 F) F) ↔ r ∈ 𝔭 := by
  have h : algebraMap (𝓞 F) F r ∈ (𝔭 : FractionalIdeal (𝓞 F)⁰ F) ↔ r ∈ 𝔭 :=
    (FractionalIdeal.mem_coeIdeal _).trans
      ⟨fun ⟨s, hs, h⟩ ↦ IsFractionRing.injective (𝓞 F) F h ▸ hs, fun h ↦ ⟨r, h, rfl⟩⟩
  rw [← h, ← hπ𝔭, FractionalIdeal.mem_spanSingleton, Submodule.mem_one]
  refine exists_congr fun z ↦ ?_
  rw [Algebra.smul_def, eq_inv_mul_iff_mul_eq₀ π.ne_zero, mul_comm]

lemma inv_mul_mem_one_of_mul_mem
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭.IsPrime) (hx : x ∈ (1 : Submodule (𝓞 F) F)) (hy : y ∈ (1 : Submodule (𝓞 F) F))
    (hxy : (π : F)⁻¹ * (x * y) ∈ (1 : Submodule (𝓞 F) F))
    (hx' : (π : F)⁻¹ * x ∉ (1 : Submodule (𝓞 F) F)) : (π : F)⁻¹ * y ∈ (1 : Submodule (𝓞 F) F) := by
  rcases Submodule.mem_one.mp hx with ⟨x, rfl⟩
  rcases Submodule.mem_one.mp hy with ⟨y, rfl⟩
  rw [← map_mul, inv_mul_algebraMap_mem_one_iff hπ𝔭] at hxy
  rw [inv_mul_algebraMap_mem_one_iff hπ𝔭] at hx' ⊢
  exact (h𝔭.mem_or_mem hxy).resolve_left hx'

lemma exists_inv_mul_one_sub_mul_mem
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭.IsMaximal) (hx : x ∈ (1 : Submodule (𝓞 F) F))
    (hx' : (π : F)⁻¹ * x ∉ (1 : Submodule (𝓞 F) F)) :
    ∃ x' ∈ (1 : Submodule (𝓞 F) F), (π : F)⁻¹ * (1 - x' * x) ∈ (1 : Submodule (𝓞 F) F) := by
  rcases Submodule.mem_one.mp hx with ⟨x, rfl⟩
  rw [inv_mul_algebraMap_mem_one_iff hπ𝔭] at hx'
  rcases h𝔭.exists_inv hx' with ⟨y, i, hi, h⟩
  refine ⟨algebraMap (𝓞 F) F y, Submodule.mem_one.mpr ⟨y, rfl⟩, ?_⟩
  rwa [← map_mul, ← map_one (algebraMap (𝓞 F) F), ← map_sub, inv_mul_algebraMap_mem_one_iff hπ𝔭,
    ← h, add_sub_cancel_left]

lemma exists_algebraMap_eq_det_mul_inv
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (hα : α ∈ heckeSet 𝔑 𝔭 𝔟 𝔟) :
    ∃ z : (𝓞 F)ˣ, algebraMap (𝓞 F) F z = α.det.val * (π : F)⁻¹ := by
  have h : FractionalIdeal.spanSingleton (𝓞 F)⁰ α.det.val =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) :=
    mul_right_cancel₀ (Units.ne_zero 𝔟) (hα.2.2.2.trans (by rw [hπ𝔭]))
  rcases FractionalIdeal.spanSingleton_eq_spanSingleton.mp h with ⟨z, hz⟩
  refine ⟨z⁻¹, ?_⟩
  rw [← hz, Units.smul_def, Algebra.smul_def, map_units_inv]
  field_simp
  exact (div_self α.det.ne_zero).symm

lemma mk_heckeUpper_out (hπ : IsTotallyPositive (π : F)) (b : translationLattice 𝔟) :
    (⟦heckeUpper π (QuotientAddGroup.mk b : HeckeTranslations π 𝔟).out⟧ :
      gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) = ⟦heckeUpper π b⟧ := by
  have h : -(QuotientAddGroup.mk b : HeckeTranslations π 𝔟).out + b ∈
      heckeTranslationSubgroup π 𝔟 :=
    QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _)
  refine mk_heckeUpper_eq_mk ?_ hπ ?_ ?_ (fun y hy ↦ ?_) ?_ ?_
  · rwa [det_heckeUpper]
  · rw [det_heckeUpper, mul_inv_cancel₀ π.ne_zero, inv_one]
    exact Submodule.one_le.mp le_rfl
  · simp [heckeUpper]
  · simpa [heckeUpper, neg_add_eq_sub] using
      mul_mem_one_of_mem_translationLattice ((mem_heckeTranslationSubgroup π).mp h) hy
  · simp [heckeUpper]
  · simp [heckeUpper]

lemma exists_mk_heckeCosetRep_eq
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭.IsMaximal) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤) (hπ : IsTotallyPositive (π : F))
    (hα : α ∈ heckeSet 𝔑 𝔭 𝔟 𝔟) :
    ∃ r, (⟦heckeCosetRep π 𝔟 r⟧ : gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) = ⟦α⟧ := by
  rcases exists_algebraMap_eq_det_mul_inv hπ𝔭 hα with ⟨z, hz⟩
  rcases hα with ⟨hpos, hL, hL', -⟩
  have hdet : (α.det.val * (π : F)⁻¹)⁻¹ ∈ (1 : Submodule (𝓞 F) F) :=
    Submodule.mem_one.mpr ⟨(z⁻¹ : (𝓞 F)ˣ), by rw [map_units_inv, hz]⟩
  have hδ : (π : F)⁻¹ * (α.val 0 0 * α.val 1 1 - α.val 0 1 * α.val 1 0) ∈
      (1 : Submodule (𝓞 F) F) :=
    Submodule.mem_one.mpr ⟨z, by rw [hz, GeneralLinearGroup.val_det_apply, det_fin_two, mul_comm]⟩
  have ha : α.val 0 0 ∈ (1 : Submodule (𝓞 F) F) := apply_zero_zero_mem hL
  have hb (y : F) (hy : y ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
      α.val 0 1 * y ∈ (1 : Submodule (𝓞 F) F) :=
    apply_zero_one_mul_mem hL hy
  have hc : α.val 1 0 ∈ 𝔑 • ((𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    simpa [mulVec, dotProduct] using ((mem_gammaZeroLattice _ _).mp (hL' ![1, 0]
      ((mem_gammaZeroLattice _ _).mpr ⟨Submodule.mem_one.mpr ⟨1, map_one _⟩, zero_mem _⟩))).2
  have hcb : α.val 1 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := Submodule.smul_le_right hc
  have hd : α.val 1 1 ∈ (1 : Submodule (𝓞 F) F) :=
    mem_one_of_forall_mul_mem (Units.ne_zero 𝔟) fun _ ↦ apply_one_one_mul_mem hL
  have hupper (β : F) (hβ : β ∈ translationLattice 𝔟)
      (h₀₁ : ∀ y ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F),
        (π : F)⁻¹ * (α.val 0 1 - α.val 0 0 * β) * y ∈ (1 : Submodule (𝓞 F) F))
      (h₁₁ : (π : F)⁻¹ * (α.val 1 1 - α.val 1 0 * β) ∈ (1 : Submodule (𝓞 F) F)) :
      ∃ r, (⟦heckeCosetRep π 𝔟 r⟧ : gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =
        ⟦α⟧ :=
    ⟨some (QuotientAddGroup.mk ⟨β, hβ⟩), (mk_heckeUpper_out hπ ⟨β, hβ⟩).trans
      (mk_heckeUpper_eq_mk hpos hπ hdet ha h₀₁ hc h₁₁)⟩
  by_cases hc' : (π : F)⁻¹ * α.val 1 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  · by_cases ha' : (π : F)⁻¹ * α.val 0 0 ∈ (1 : Submodule (𝓞 F) F)
    · refine ⟨none, mk_heckeLower_eq_mk hpos hπ hdet ha' hb ?_ hd⟩
      rcases Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h𝔭𝔑) with ⟨p, hp, n, hn, hpn⟩
      have hpn' : algebraMap (𝓞 F) F p + algebraMap (𝓞 F) F n = 1 := by
        rw [← map_add, hpn, map_one]
      have h : (π : F)⁻¹ * α.val 1 0 = (π : F)⁻¹ * algebraMap (𝓞 F) F p * α.val 1 0 +
          n • ((π : F)⁻¹ * α.val 1 0) := by
        rw [Algebra.smul_def]
        linear_combination (-((π : F)⁻¹ * α.val 1 0)) * hpn'
      rw [h]
      exact add_mem (mul_mem_of_mem_one ((inv_mul_algebraMap_mem_one_iff hπ𝔭 p).mpr hp) hc)
        (Submodule.smul_mem_smul hn hc')
    · rcases exists_inv_mul_one_sub_mul_mem hπ𝔭 h𝔭 ha ha' with ⟨a', ha'1, hP⟩
      refine hupper (a' * α.val 0 1) (mem_translationLattice_of_forall fun y hy ↦
        mul_assoc a' _ y ▸ mul_mem_one ha'1 (hb y hy)) (fun y hy ↦ ?_) ?_
      · convert mul_mem_one hP (hb y hy) using 1
        ring1
      · refine inv_mul_mem_one_of_mul_mem hπ𝔭 h𝔭.isPrime ha (sub_mem hd ?_) ?_ ha'
        · convert mul_mem_one ha'1 (hb _ hcb) using 1
          ring1
        · convert add_mem hδ (mul_mem_one (hb _ hcb) hP) using 1
          ring1
  · have h : ∃ β₁ ∈ translationLattice 𝔟,
        (π : F)⁻¹ * (α.val 1 0 * β₁) ∉ (1 : Submodule (𝓞 F) F) := by
      by_contra h
      push Not at h
      refine hc' ?_
      have h𝔟 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
        rw [Units.val_inv_eq_inv_val, inv_inv]
      rw [h𝔟, FractionalIdeal.mem_inv_iff (Units.ne_zero 𝔟⁻¹)]
      intro y hy
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one, mul_assoc]
      exact h y hy
    rcases h with ⟨β₁, hβ₁, he⟩
    have he1 : α.val 1 0 * β₁ ∈ (1 : Submodule (𝓞 F) F) :=
      mul_comm β₁ _ ▸ mul_mem_one_of_mem_translationLattice hβ₁ hcb
    rcases exists_inv_mul_one_sub_mul_mem hπ𝔭 h𝔭 he1 he with ⟨e', he'1, hP⟩
    refine hupper (α.val 1 1 * e' * β₁) (mem_translationLattice_of_forall fun y hy ↦ ?_)
      (fun y hy ↦ ?_) ?_
    · convert mul_mem_one (mul_mem_one hd he'1) (mul_mem_one_of_mem_translationLattice hβ₁ hy)
        using 1
      ring1
    · rw [mul_assoc]
      refine inv_mul_mem_one_of_mul_mem hπ𝔭 h𝔭.isPrime he1 ?_ ?_ he
      · convert sub_mem (hb y hy) (mul_mem_one (mul_mem_one (mul_mem_one ha hd) he'1)
          (mul_mem_one_of_mem_translationLattice hβ₁ hy)) using 1
        ring1
      · convert mul_mem_one (mul_mem_one_of_mem_translationLattice hβ₁ hy)
          (sub_mem (mul_mem_one ha (mul_mem_one hd hP)) hδ) using 1
        ring1
    · convert mul_mem_one hd hP using 1
      ring1

lemma heckeCosetRep_mem_heckeSet
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (hπ : IsTotallyPositive (π : F)) (r : Option (HeckeTranslations π 𝔟)) :
    heckeCosetRep π 𝔟 r ∈ heckeSet 𝔑 𝔭 𝔟 𝔟 := by
  have hπ1 : (π : F) ∈ (1 : Submodule (𝓞 F) F) := by
    rcases (FractionalIdeal.mem_coeIdeal _).mp
      (hπ𝔭 ▸ FractionalIdeal.mem_spanSingleton_self _ _) with ⟨p, -, hp⟩
    exact Submodule.mem_one.mpr ⟨p, hp⟩
  have h (M : Submodule (𝓞 F) F) (hM : M ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) (v : Fin 2 → F)
      (hv : v ∈ Submodule.pi Set.univ ![1, M]) :
      (heckeCosetRep π 𝔟 r).val *ᵥ v ∈ Submodule.pi Set.univ ![1, M] := by
    rcases r with _ | q
    · exact mulVec_mem_pi (by simpa [heckeCosetRep, heckeLower] using hπ1)
        (by simp [heckeCosetRep, heckeLower]) (by simp [heckeCosetRep, heckeLower])
        (by simp [heckeCosetRep, heckeLower]) hv
    · exact mulVec_mem_pi (by simp [heckeCosetRep, heckeUpper]) (fun y hy ↦ by
        simpa [heckeCosetRep, heckeUpper] using
          mul_mem_one_of_mem_translationLattice q.out.2 (hM hy))
        (by simp [heckeCosetRep, heckeUpper]) (by simpa [heckeCosetRep, heckeUpper] using hπ1) hv
  refine ⟨by rwa [det_heckeCosetRep], h _ le_rfl, h _ Submodule.smul_le_right, ?_⟩
  rw [det_heckeCosetRep, hπ𝔭]

lemma mk_heckeLower_ne_mk_heckeUpper
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭 ≠ ⊤) :
    (⟦heckeLower π⟧ : gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ≠
      ⟦heckeUpper π β⟧ := by
  intro h
  have hg : heckeUpper π β * (heckeLower π)⁻¹ ∈ gl (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :=
    (QuotientGroup.rightRel_apply.mp (Quotient.exact h)).1.1
  have h₀₀ : (heckeUpper π β * (heckeLower π)⁻¹).val 0 0 ∈ (1 : Submodule (𝓞 F) F) :=
    apply_zero_zero_mem fun v hv ↦ (hg v).mp hv
  rw [val_mul_inv_heckeLower] at h₀₀
  exact h𝔭 <| (Ideal.eq_top_iff_one _).mpr <|
    (inv_mul_algebraMap_mem_one_iff hπ𝔭 1).mp (by simpa [heckeUpper] using h₀₀)

lemma injOn_mk_heckeCosetRep
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭 ≠ ⊤) :
    Set.InjOn (fun r ↦ (⟦heckeCosetRep π 𝔟 r⟧ :
      gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) Set.univ := by
  rintro (_ | q) - (_ | q') - h
  · rfl
  · exact (mk_heckeLower_ne_mk_heckeUpper hπ𝔭 h𝔭 h).elim
  · exact (mk_heckeLower_ne_mk_heckeUpper hπ𝔭 h𝔭 h.symm).elim
  · have hg : heckeUpper π q'.out * (heckeUpper π q.out)⁻¹ ∈
        gl (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :=
      (QuotientGroup.rightRel_apply.mp (Quotient.exact h)).1.1
    have h₀₁ (y : F) (hy : y ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
        (π : F)⁻¹ * (-q.out + q'.out : translationLattice 𝔟) * y ∈ (1 : Submodule (𝓞 F) F) := by
      have h' : (heckeUpper π q'.out * (heckeUpper π q.out)⁻¹).val 0 1 * y ∈
          (1 : Submodule (𝓞 F) F) :=
        apply_zero_one_mul_mem (fun v hv ↦ (hg v).mp hv) hy
      rw [val_mul_inv_heckeUpper] at h'
      simpa [heckeUpper, neg_add_eq_sub] using h'
    refine congrArg some ?_
    rw [← q.out_eq', ← q'.out_eq']
    exact QuotientAddGroup.eq.mpr
      ((mem_heckeTranslationSubgroup π).mpr (mem_translationLattice_of_forall h₀₁))

/-- **The coset decomposition of `T_𝔭`**: for a prime `𝔭 = (π)` with `π` totally positive and
`𝔭 + 𝔑 = 𝒪_F`, the right cosets `Γ₀(𝔑)_𝔟 α`, `α ∈ heckeSet 𝔑 𝔭 𝔟 𝔟`, are the cosets of
`(π, 0; 0, 1)` and of the `(1, b; 0, π)`, `b ∈ 𝔟⁻¹ / π 𝔟⁻¹`, each exactly once. -/
lemma isHeckeCosetDecomposition
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤) (hπ : IsTotallyPositive (π : F)) :
    IsHeckeCosetDecomposition π 𝔟 𝔭 𝔑 := by
  have h𝔭' : 𝔭.IsMaximal := h𝔭.isMaximal fun h ↦ π.ne_zero <| by
    rwa [h, FractionalIdeal.coeIdeal_bot, FractionalIdeal.spanSingleton_eq_zero_iff] at hπ𝔭
  exact ⟨fun r _ ↦ ⟨_, heckeCosetRep_mem_heckeSet hπ𝔭 hπ r, rfl⟩,
    injOn_mk_heckeCosetRep hπ𝔭 h𝔭.ne_top, fun _ ⟨_, hα, hq⟩ ↦ hq ▸
      (exists_mk_heckeCosetRep_eq hπ𝔭 h𝔭' h𝔭𝔑 hπ hα).imp fun r hr ↦ ⟨Set.mem_univ r, hr⟩⟩

end HilbertModularForm

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
  {k : {w : InfinitePlace F // w.IsReal} → ℤ} {m : ℤ} {𝔑 : Ideal (𝓞 F)} [NeZero 𝔑]
  {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ} {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c}
  {f : HilbertModularForm 𝔑 k 𝔟 h𝔟} {𝔭 : (Ideal (𝓞 F))⁰} {π : Fˣ}

/-- **The Hecke eigenvalues of a normalised eigenform at primes are its Fourier coefficients**: for
`F` totally real, a normalised Hecke eigenform `f` of parallel weight `m` whose components have
Fourier expansions, and a prime `𝔭 = (π)` with `π` totally positive and `𝔭 + 𝔑 = 𝒪_F`, the
normalised eigenvalue of `T_𝔭` is `a_𝔭`. -/
lemma heckeIdealEigenvalueNormalised_eq_idealCoeff_of_isPrime (hk : ∀ w, k w = m)
    (hf : f.IsHeckeIdealEigenform) (hn : f.IsNormalised)
    (hexp : ∀ c, ∃ a, HasHilbertFourierExpansion (𝔟 c) (f.toFun c) a)
    (h𝔭 : (𝔭 : Ideal (𝓞 F)).IsPrime) (h𝔭𝔑 : (𝔭 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤)
    (hπ : IsTotallyPositive (π : F)) (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) =
      ((𝔭 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) :
    heckeIdealEigenvalueNormalised m 𝔭 hf h𝔭𝔑 = f.idealCoeff 𝔭 :=
  heckeIdealEigenvalueNormalised_eq_idealCoeff 𝔭 hk hf hn hexp h𝔭𝔑 h𝔭.ne_top hπ hπ𝔭 fun _ ↦
    isHeckeCosetDecomposition hπ𝔭 h𝔭 h𝔭𝔑 hπ

end HilbertModularForm
