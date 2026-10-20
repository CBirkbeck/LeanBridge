import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbit
import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# Newform subspaces

The newform subspace `V_f` of a newform `f` (LMFDB `cmf.newform_subspace`) is the subspace spanned
by the Galois conjugates of `f`, here the complex span in `S_k(Γ₁(N))` of the Galois orbit of `f`.
The Galois orbit is a basis of it, since distinct newforms are linearly independent, and it is
stable under the Hecke operators `T_p` at every prime `p`, each conjugate being an eigenform.

The LMFDB's rationality statements refer to the rational structure of `V_f`, its subspace of forms
with rational coefficients, whose complexification is `V_f`; it is not formalised here. Over `ℚ`
the newform subspaces are the irreducible pieces of the newspace under the Hecke algebra; over
`ℂ`, as here, they still give its canonical decomposition, the decomposition of
`S_k(Γ₁(N))ⁿᵉʷ = ⨁ S_k^{new}(N, χ)` along the Galois orbits of newforms (LMFDB
`cmf.decomposition.new.gamma0chi`).

## Main definitions

* `HeckeRing.GL2.Newform.newformSubspace`: the newform subspace `V_f` of a newform
  (LMFDB `cmf.newform_subspace`).
* `HeckeRing.GL2.Newform.galoisOrbitBasis`: the Galois orbit of `f`, as a basis of `V_f`.
* `HeckeRing.GL2.NewformOrbit.newformSubspace`: the newform subspace of a newform orbit.

## Main results

* `HeckeRing.GL2.Newform.toCuspForm_mem_newformSubspace_iff`: the newforms in `V_f` are the Galois
  conjugates of `f`.
* `HeckeRing.GL2.Newform.finrank_newformSubspace`: `V_f` has dimension the size of the Galois orbit
  of `f`.
* `HeckeRing.GL2.Newform.span_image_toCuspForm_inf_cuspFormCharSpace`: the `χ`-part of a span of
  newforms is spanned by those of nebentypus `χ`.
* `HeckeRing.GL2.Newform.heckeTCuspNat_mem_newformSubspace`: `V_f` is stable under `T_p` for every
  prime `p`.
* `HeckeRing.GL2.NewformOrbit.iSupIndep_newformSubspace`,
  `HeckeRing.GL2.NewformOrbit.iSup_newformSubspace`: the new subspace `S_k(Γ₁(N))ⁿᵉʷ` is the
  direct sum of the newform subspaces of the newform orbits (LMFDB
  `cmf.decomposition.new.gamma0chi`).
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Matrix.SpecialLinearGroup Module

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

namespace Newform

variable {f g : Newform N k} {s t : Set (Newform N k)}

variable (s) in
lemma finrank_span_image_toCuspForm :
    Module.finrank ℂ (Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' s)) = s.ncard := by
  rw [finrank_span_set_eq_ncard (linearIndependent_toCuspForm.linearIndepOn s).id_image,
    Set.ncard_image_of_injective _ linearIndependent_toCuspForm.injective]

lemma toCuspForm_mem_span_image_iff :
    g.toCuspForm ∈ Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' s) ↔ g ∈ s :=
  ⟨fun h ↦ by_contra fun hg ↦ linearIndependent_toCuspForm.notMem_span_image hg h,
    fun hg ↦ Submodule.subset_span ⟨g, hg, rfl⟩⟩

lemma span_image_toCuspForm_inj : Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' s) =
    Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' t) ↔ s = t :=
  ⟨fun h ↦ Set.ext fun _ ↦ by
    rw [← toCuspForm_mem_span_image_iff, h, toCuspForm_mem_span_image_iff], fun h ↦ h ▸ rfl⟩

variable (s) in
/-- **The `χ`-part of a span of newforms is spanned by those of nebentypus `χ`**: the character
spaces `S_k(N, χ)` are independent. -/
lemma span_image_toCuspForm_inf_cuspFormCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' s) ⊓ cuspFormCharSpace k χ =
    Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' {g ∈ s | g.χ = χ}) := by
  refine le_antisymm (fun F hF ↦ ?_) <| le_inf
    (Submodule.span_mono (Set.image_mono (Set.sep_subset _ _)))
    (Submodule.span_le.mpr <| Set.image_subset_iff.mpr fun g hg ↦ hg.2 ▸ g.mem_charSpace)
  rcases Submodule.mem_inf.mp hF with ⟨hF, hFχ⟩
  rw [← Set.inter_union_sdiff s {g | g.χ = χ}, Set.image_union, Submodule.span_union,
    Submodule.mem_sup] at hF
  rcases hF with ⟨a, ha, b, hb, rfl⟩
  have hb₀ : b ∈ ⨆ (χ' : (ZMod N)ˣ →* ℂˣ) (_ : χ' ≠ χ), cuspFormCharSpace k χ' :=
    Submodule.span_le.mpr (Set.image_subset_iff.mpr fun g (hg : g ∈ s \ {g | g.χ = χ}) ↦
      Submodule.mem_iSup_of_mem g.χ (Submodule.mem_iSup_of_mem hg.2 g.mem_charSpace)) hb
  have ha₀ : a ∈ cuspFormCharSpace k χ :=
    Submodule.span_le.mpr (Set.image_subset_iff.mpr fun g hg ↦ hg.2 ▸ g.mem_charSpace) ha
  have hbχ : b ∈ cuspFormCharSpace k χ := by
    simpa using sub_mem hFχ ha₀
  have hb' : b = 0 := Submodule.disjoint_def.mp (iSupIndep_cuspFormCharSpace k χ) b hbχ hb₀
  rwa [hb', add_zero]

variable (f) in
/-- The **newform subspace** `V_f` of a newform `f` (LMFDB `cmf.newform_subspace`): the subspace of
`S_k(Γ₁(N))` spanned by the Galois conjugates of `f`, i.e. by its Galois orbit, over `ℂ`. -/
def newformSubspace : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' f.galoisOrbit)

/-- **The newforms in the newform subspace `V_f` are the Galois conjugates of `f`.** -/
lemma toCuspForm_mem_newformSubspace_iff : g.toCuspForm ∈ f.newformSubspace ↔ g ∈ f.galoisOrbit :=
  toCuspForm_mem_span_image_iff

lemma toCuspForm_mem_newformSubspace (hg : g ∈ f.galoisOrbit) : g.toCuspForm ∈ f.newformSubspace :=
  toCuspForm_mem_newformSubspace_iff.mpr hg

variable (f) in
lemma newformSubspace_le_cuspFormsNew : f.newformSubspace ≤ cuspFormsNew N k :=
  Submodule.span_le.mpr <| Set.image_subset_iff.mpr fun g _ ↦ g.isNew

lemma IsGaloisConjugate.newformSubspace_eq (hfg : f.IsGaloisConjugate g) :
    f.newformSubspace = g.newformSubspace := by
  rw [newformSubspace, newformSubspace, galoisOrbit_eq_iff.mpr hfg]

variable (f) in
/-- The **Galois orbit of `f` is a basis of its newform subspace** `V_f`, over `ℂ`: newforms are
linearly independent. -/
noncomputable def galoisOrbitBasis : Basis f.galoisOrbit ℂ f.newformSubspace :=
  (Basis.span (linearIndependent_toCuspForm.comp _ Subtype.val_injective)).map <|
    LinearEquiv.ofEq _ _ <| by rw [Set.range_comp, Subtype.range_coe, newformSubspace]

@[simp]
lemma coe_galoisOrbitBasis_apply (x : f.galoisOrbit) :
    (f.galoisOrbitBasis x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = x.1.toCuspForm := by
  simp [galoisOrbitBasis]

variable (f) in
/-- **The dimension of the newform subspace `V_f` is the size of the Galois orbit of `f`.** -/
lemma finrank_newformSubspace : Module.finrank ℂ f.newformSubspace = f.galoisOrbit.ncard :=
  finrank_span_image_toCuspForm _

/-- **The newform subspace is stable under the Hecke operators** `T_p` at every prime `p`, those
dividing the level included: every Galois conjugate of `f` is an eigenform of `T_p`. -/
lemma heckeTCuspNat_mem_newformSubspace {p : ℕ} [NeZero p] (hp : p.Prime)
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hF : F ∈ f.newformSubspace) :
    heckeTCuspNat k p F ∈ f.newformSubspace := by
  have h : f.newformSubspace ≤ f.newformSubspace.comap (heckeTCuspNat k p) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, g.heckeTCuspNat_eq_qExpansion_coeff_smul hp]
    exact Submodule.smul_mem _ _ (toCuspForm_mem_newformSubspace hg)
  exact h hF

end Newform

namespace NewformOrbit

variable (O : NewformOrbit N k)

/-- The **newform subspace** of a newform orbit `O` (LMFDB `cmf.newform_subspace`): the span of the
newforms in `O`, which is the newform subspace of each of them. -/
def newformSubspace : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' {g | g.newformOrbit = O})

@[simp]
lemma newformSubspace_newformOrbit (f : Newform N k) :
    f.newformOrbit.newformSubspace = f.newformSubspace :=
  congrArg (Submodule.span ℂ <| (fun g : Newform N k ↦ g.toCuspForm) '' ·) <| Set.ext fun _ ↦
    Newform.newformOrbit_eq_iff.trans ⟨.symm, .symm⟩

/-- **The newform subspaces of distinct newform orbits are independent**, newforms being linearly
independent. -/
lemma iSupIndep_newformSubspace : iSupIndep fun O : NewformOrbit N k ↦ O.newformSubspace := by
  intro O
  have h : ⨆ (O' : NewformOrbit N k) (_ : O' ≠ O), O'.newformSubspace =
      Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' {g | g.newformOrbit ≠ O}) := by
    simp only [newformSubspace, ← Submodule.span_iUnion]
    congr 2
    ext g
    simp
  rw [h]
  exact Newform.linearIndependent_toCuspForm.disjoint_span_image <|
    Set.disjoint_left.mpr fun _ h₁ h₂ ↦ h₂ h₁

/-- **The newform subspaces of the newform orbits span the new subspace** `S_k(Γ₁(N))ⁿᵉʷ`. -/
lemma iSup_newformSubspace : ⨆ O : NewformOrbit N k, O.newformSubspace = cuspFormsNew N k := by
  rw [← Newform.span_range_toCuspForm_eq_cuspFormsNew]
  simp only [newformSubspace, ← Submodule.span_iUnion]
  congr 2
  ext g
  simp

end NewformOrbit

end HeckeRing.GL2
