import LeanBridge.ForMathlib.NumberTheory.ModularForms.Eisenstein.Subspace
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Subspace
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import TauCeti.NumberTheory.ModularForms.Newforms.Nebentypus
import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# Old and new subspaces of spaces of modular forms with character

Let `M_k(N, χ)` be the space of modular forms of weight `k`, level `N` and character `χ`. Its old
subspace `M_k^old(N, χ)` is the span of the images of the maps `M_k(M, χ_M) → M_k(N, χ)`,
`f(z) ↦ f(dz)`, for the proper divisors `M` of `N`, the characters `χ_M` modulo `M` inducing `χ`
and the divisors `d` of `N / M`. The old Eisenstein subspace `E_k^old(N, χ)` is the span of the
images of the Eisenstein subspaces `E_k(M, χ_M)` under the same maps, and the new Eisenstein
subspace `E_k^new(N, χ)` is the span of the Eisenstein series `E_k^{χ₁, χ₂}` with `χ₁ χ₂ = χ`
whose levels `N₁ N₂` are exactly `N`. In weight `2` and trivial character the series `E_2^{1, 1}`
is not holomorphic, and the LMFDB says that `E_2^new(N, 1)` is spanned by `E₂(z) - p E₂(pz)` when
`N = p` is prime and is zero otherwise. That is only its part coming from `E_2^{1, 1}`: it also
contains the `E_2^{ψ, ψ⁻¹}` for the nontrivial primitive characters `ψ` of conductor `m` with
`m² = N`, so that for example `E_2^new(9, 1)` is spanned by `E_2^{ψ, ψ}` for the quadratic
character `ψ` modulo `3`. The Eisenstein newforms are the normalised Hecke eigenforms in
`E_k^new(N, χ)`.

The cuspidal old and new subspaces, and the decomposition `S_k(N, χ) = S_k^old ⊕ S_k^new`, are
Tau Ceti's `TauCeti.cuspFormsOld`, `TauCeti.cuspFormsNew` and
`TauCeti.sup_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace`, at a fixed character by
intersection with `cuspFormCharSpace k χ`.

Tau Ceti constructs the Eisenstein series `E_k^{χ₁, χ₂}` only in weight at least `3`
(`TauCeti.EisensteinSeries.CharIndex.form`), and the corrected series `E₂(z) - t E₂(tz)` in weight
`2` (`TauCeti.EisensteinSeries.correctedE2`), so the new Eisenstein subspace is defined here in
these cases only. The decomposition `E_k(N, χ) = E_k^old ⊕ E_k^new`, which needs the Petersson
orthogonality of Eisenstein series and cusp forms and the linear independence of the Eisenstein
series, is not proved.

## Main definitions

* `ModularForm.modFormsOld` (LMFDB `cmf.subspaces`): the old subspace `M_k^old(N, χ)`.
* `ModularForm.eisensteinFormsOld` (LMFDB `cmf.eisenstein_newspace`): the old Eisenstein
  subspace `E_k^old(N, χ)`.
* `ModularForm.eisensteinFormsNew` (LMFDB `cmf.eisenstein_newspace`): the new Eisenstein subspace
  `E_k^new(N, χ)`, in weight `k ≥ 3`.
* `ModularForm.eisensteinFormsNewWeightTwo` (LMFDB `cmf.eisenstein_newspace`): the part of the new
  Eisenstein subspace `E_2^new(N, 1)` of weight `2` and trivial character coming from `E₂`.
* `ModularForm.IsEisensteinNewform` (LMFDB `cmf.eisenstein_newform`): Eisenstein newforms, in
  weight `k ≥ 3`.

## Main results

* `ModularForm.modFormsOld_le_modFormCharSpace`: `M_k^old(N, χ) ⊆ M_k(N, χ)`.
* `ModularForm.map_cuspFormsOld_inf_le_modFormsOld`: the cuspidal old forms of character `χ` are
  old forms.
* `ModularForm.eisensteinFormsOld_le_modFormsOld`: `E_k^old(N, χ) ⊆ M_k^old(N, χ)`.
* `ModularForm.eisensteinFormsNew_le_modFormCharSpace`: `E_k^new(N, χ) ⊆ M_k(N, χ)`.
* `ModularForm.eisensteinFormsNewWeightTwo_le_modFormCharSpace`: `E_2^new(N, 1) ⊆ M_2(N, 1)`.
-/

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing TauCeti
    TauCeti.EisensteinSeries
open scoped MatrixGroups ModularForm

namespace ModularForm

variable {N : ℕ} [NeZero N]

section Old

variable (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

/-- The **old subspace** `M_k^old(N, χ)` (LMFDB `cmf.subspaces`) of the space `M_k(N, χ)` of modular
forms of weight `k`, level `N` and character `χ`: the span of the images of the level-raising maps
`V_d : M_k(M, ψ) → M_k(N, χ)`, `f(z) ↦ f(dz)` (Tau Ceti's `TauCeti.ModularForm.levelRaise`), over
the proper divisors `M` of `N`, the divisors `d` of `N / M` and the characters `ψ` modulo `M` that
induce `χ`, i.e. with `χ = ψ ∘ ((ℤ/Nℤ)ˣ → (ℤ/Mℤ)ˣ)`. It lies in `M_k(N, χ)`
(`modFormsOld_le_modFormCharSpace`). -/
noncomputable def modFormsOld : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨆ (M : ℕ) (d : ℕ) (h : d * M ∣ N ∧ M ≠ N) (ψ : (ZMod M)ˣ →* ℂˣ)
    (_ : χ = ψ.comp (ZMod.unitsMap ((Dvd.intro_left d rfl).trans h.1))),
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
    (modFormCharSpace k ψ).map (ModularForm.levelRaiseₗ d
      (Gamma1_map_le_conjAct_scaleGL_of_dvd h.1))

lemma levelRaise_mem_modFormsOld {M d : ℕ} [NeZero d] (h : d * M ∣ N) (hM : M ≠ N)
    {ψ : (ZMod M)ˣ →* ℂˣ} {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k ψ) : ModularForm.levelRaise d
    (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f ∈ modFormsOld k
    (ψ.comp (ZMod.unitsMap ((Dvd.intro_left d rfl).trans h))) := by
  rw [← ModularForm.levelRaiseₗ_apply]
  exact Submodule.mem_iSup_of_mem M <| Submodule.mem_iSup_of_mem d <|
    Submodule.mem_iSup_of_mem ⟨h, hM⟩ <| Submodule.mem_iSup_of_mem ψ <|
      Submodule.mem_iSup_of_mem rfl <| Submodule.mem_map_of_mem hf

/-- **The old forms of character `χ` have character `χ`**: `M_k^old(N, χ) ⊆ M_k(N, χ)`. -/
lemma modFormsOld_le_modFormCharSpace : modFormsOld k χ ≤ modFormCharSpace k χ := by
  refine iSup_le fun M ↦ iSup_le fun d ↦ iSup_le fun h ↦ iSup_le fun ψ ↦ iSup_le fun hχ ↦ ?_
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
  rintro _ ⟨f, hf, rfl⟩
  rw [ModularForm.levelRaiseₗ_apply, hχ]
  exact ModularForm.levelRaise_mem_modFormCharSpace_of_dvd h.1 ψ hf

/-- **The cuspidal old forms are old forms**: the old cusp forms of character `χ` (Tau Ceti's
`TauCeti.cuspFormsOld`, intersected with `S_k(N, χ)`) lie in `M_k^old(N, χ)`. -/
lemma map_cuspFormsOld_inf_le_modFormsOld :
    (cuspFormsOld N k ⊓ cuspFormCharSpace k χ).map CuspForm.toModularFormₗ ≤ modFormsOld k χ := by
  refine Submodule.map_le_iff_le_comap.mpr <| cuspFormsOld_inf_cuspFormCharSpace_le
    fun M d _ h hM ψ hψ g hg ↦ ?_
  have hcoe : CuspForm.toModularFormₗ
      (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g) = ModularForm.levelRaise d
      (Gamma1_map_le_conjAct_scaleGL_of_dvd h) (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :=
    ModularForm.ext fun z ↦ by simp
  rw [Submodule.mem_comap, hcoe, hψ]
  exact levelRaise_mem_modFormsOld k h hM ((coe_mem_modFormCharSpace_iff k ψ g).mpr hg)

/-- The **old Eisenstein subspace** `E_k^old(N, χ)` (LMFDB `cmf.eisenstein_newspace`): the span of
the images of the Eisenstein subspaces `E_k(M, ψ)` (`eisensteinFormSubmodule` and
`modFormCharSpace`) under the level-raising maps `V_d : M_k(M, ψ) → M_k(N, χ)`, `f(z) ↦ f(dz)`, over
the proper divisors `M` of `N`, the divisors `d` of `N / M` and the characters `ψ` modulo `M` that
induce `χ`. The LMFDB regards it as a subspace of `E_k(N, χ)`; that the maps `V_d` preserve
Eisenstein forms is not proved here. -/
noncomputable def eisensteinFormsOld : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨆ (M : ℕ) (d : ℕ) (h : d * M ∣ N ∧ M ≠ N) (ψ : (ZMod M)ˣ →* ℂˣ)
    (_ : χ = ψ.comp (ZMod.unitsMap ((Dvd.intro_left d rfl).trans h.1))),
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
    haveI : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd h.1)
    (eisensteinFormSubmodule (Gamma1 M) k ⊓ modFormCharSpace k ψ).map (ModularForm.levelRaiseₗ d
      (Gamma1_map_le_conjAct_scaleGL_of_dvd h.1))

/-- **The old Eisenstein forms are old forms**: `E_k^old(N, χ) ⊆ M_k^old(N, χ)`. -/
lemma eisensteinFormsOld_le_modFormsOld : eisensteinFormsOld k χ ≤ modFormsOld k χ :=
  iSup_mono fun _ ↦ iSup_mono fun _ ↦ iSup_mono fun _ ↦ iSup_mono fun _ ↦ iSup_mono fun _ ↦
    Submodule.map_mono inf_le_right

end Old

section New

variable (k : ℕ) (χ : (ZMod N)ˣ →* ℂˣ) (hk : 3 ≤ (k : ℤ))

/-- The **new Eisenstein subspace** `E_k^new(N, χ)` (LMFDB `cmf.eisenstein_newspace`) in weight
`k ≥ 3`: the span of the Eisenstein series `E_k^{χ₁, χ₂}` (Tau Ceti's
`TauCeti.EisensteinSeries.CharIndex.form`, normalised to have first Fourier coefficient `1`) for
the pairs of primitive characters `χ₁` modulo `N₁` and `χ₂` modulo `N₂` with `N₁ N₂ = N`,
`χ₁ χ₂ = χ` and the parity of weight `k`, not raised to a higher level. It lies in `M_k(N, χ)`
(`eisensteinFormsNew_le_modFormCharSpace`); that it lies in `E_k(N, χ)` is the Petersson
orthogonality of Eisenstein series and cusp forms, not proved here. In weights `1` and `2` the
Eisenstein series are not available. -/
noncomputable def eisensteinFormsNew : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ
    {f | ∃ a : CharIndex N k, a.nebentypus = χ ∧ a.t = 1 ∧ a.u * a.v = N ∧ a.form hk = f}

/-- **The new Eisenstein forms have character `χ`**: `E_k^new(N, χ) ⊆ M_k(N, χ)`. -/
lemma eisensteinFormsNew_le_modFormCharSpace :
    eisensteinFormsNew k χ hk ≤ modFormCharSpace k χ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, ha, -, -, rfl⟩
  exact ha ▸ a.form_mem_modFormCharSpace hk

/-- An **Eisenstein newform** (LMFDB `cmf.eisenstein_newform`) of weight `k ≥ 3`, level `N` and
character `χ`: a form of the new Eisenstein subspace `E_k^new(N, χ)` that is an eigenform of all
the Hecke operators `T_n`, `n ≥ 1` (Tau Ceti's `HeckeRing.GL2.heckeTNat`, which is `U_p` at the
primes `p ∣ N`), normalised so that its first Fourier coefficient is `1`. -/
def IsEisensteinNewform (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  f ∈ eisensteinFormsNew k χ hk ∧ (∀ (n : ℕ) [NeZero n], ∃ c : ℂ, GL2.heckeTNat k n f = c • f) ∧
    (qExpansion 1 f).coeff 1 = 1

variable (N) in
/-- The **new Eisenstein subspace** `E_2^new(N, 1)` (LMFDB `cmf.eisenstein_newspace`) of weight `2`
and trivial character, as the LMFDB describes it: when `N = p` is prime it is spanned by
`E₂(z) - p E₂(pz)` (Tau Ceti's `TauCeti.EisensteinSeries.correctedE2`, a form for `Γ₀(p)`, here
restricted to `Γ₁(p)`), and otherwise it is zero.

This is the part of `E_2^new(N, 1)` coming from `E₂ = E_2^{1, 1}`, and all of it only when `N` is
not the square of the conductor `m` of a nontrivial primitive character, that is of an integer
`m > 1` with `m ≢ 2 mod 4`: the series `E_2^{ψ, ψ⁻¹}` for the primitive characters `ψ ≠ 1` modulo
such an `m` also lie in `E_2^new(m², 1)`, a case that the LMFDB's description omits. -/
noncomputable def eisensteinFormsNewWeightTwo :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) :=
  ⨆ _ : N.Prime, ℂ ∙ (correctedE2 N).restrict (Gamma1_map_le_Gamma0_map N)

/-- **The new Eisenstein forms of weight `2` have trivial character**:
`E_2^new(N, 1) ⊆ M_2(N, 1)`. -/
lemma eisensteinFormsNewWeightTwo_le_modFormCharSpace :
    eisensteinFormsNewWeightTwo N ≤ modFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) :=
  iSup_le fun _ ↦ (Submodule.span_singleton_le_iff_mem _ _).mpr
    (restrict_mem_modFormCharSpace_one (correctedE2 N))

end New

end ModularForm
