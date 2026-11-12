import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbitLabel
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NewformSubspace

/-!
# The decomposition of a newspace into newform subspaces

The newspaces of the LMFDB are the spaces `S_k^{new}(N, [χ])` of the Galois orbits `[χ]` of
Dirichlet characters modulo `N` (Tau Ceti's `MulChar.galoisOrbit`): the sum of the new subspaces
`S_k^{new}(N, ψ)` of `S_k(Γ₁(N))` over the characters `ψ` of `[χ]`. The newform subspace of a
newform `f` of nebentypus `χ` (LMFDB `cmf.newform_subspace`) is spanned by its Galois conjugates
`σ(f)`, of nebentypus `σ ∘ χ` (`HeckeRing.GL2.Newform.IsGaloisConjugateBy.χ_eq`), so it lies in
`S_k^{new}(N, [χ])`, but not in `S_k^{new}(N, χ)` when `χ` takes non-rational values. The newspace
that the knowl decomposes into newform subspaces is therefore `S_k^{new}(N, [χ])`.

This file proves that decomposition. The newforms of nebentypus `ψ` span `S_k^{new}(N, ψ)` (Tau
Ceti's `HeckeRing.GL2.Newform.span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace`), so
the newforms with nebentypus in `[χ]` span `S_k^{new}(N, [χ])`. They are the newforms of the newform
orbits whose nebentypus orbit (`HeckeRing.GL2.NewformOrbit.characterOrbit`) is `[χ]`, so the
newform subspaces of these orbits span `S_k^{new}(N, [χ])`; and they are independent, as the
newform subspaces of all the newform orbits are
(`HeckeRing.GL2.NewformOrbit.iSupIndep_newformSubspace`).

## Main definitions

* `HeckeRing.GL2.cuspFormsNewGaloisOrbit` (LMFDB `cmf.newspace`): the newspace
  `S_k^{new}(N, [χ])`.

## Main results

* `HeckeRing.GL2.span_image_toCuspForm_eq_cuspFormsNewGaloisOrbit`: the newforms with nebentypus
  in `[χ]` span `S_k^{new}(N, [χ])`.
* `HeckeRing.GL2.Newform.newformSubspace_le_cuspFormsNewGaloisOrbit`: the newform subspace of a
  newform of nebentypus `χ` lies in `S_k^{new}(N, [χ])`.
* `HeckeRing.GL2.NewformOrbit.iSupIndep_newformSubspace_characterOrbit`,
  `HeckeRing.GL2.NewformOrbit.iSup_newformSubspace_characterOrbit` (LMFDB `cmf.newform_subspace`):
  `S_k^{new}(N, [χ])` is the direct sum of the newform subspaces of the newform orbits whose
  nebentypus lies in `[χ]`.
-/

open TauCeti CongruenceSubgroup Matrix SpecialLinearGroup

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N)

variable (k) in
/-- The **newspace** `S_k^{new}(N, [χ])` (LMFDB `cmf.newspace`) of the Galois orbit `[χ]` of a
Dirichlet character `χ` modulo `N`: the sum of the new subspaces `S_k^{new}(N, ψ)` of `S_k(Γ₁(N))`
over the characters `ψ` of `[χ]` (Tau Ceti's `MulChar.galoisOrbit`). -/
noncomputable def cuspFormsNewGaloisOrbit : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨆ ψ ∈ χ.galoisOrbit, cuspFormsNew N k ⊓ cuspFormCharSpace k ψ.toUnitHom

lemma Newform.dirichletLift_eq_iff {f : Newform N k} {ψ : DirichletCharacter ℂ N} :
    f.dirichletLift = ψ ↔ f.χ = ψ.toUnitHom := by
  rw [dirichletLift_def, MulChar.ofUnitHom_eq, MulChar.toUnitHom_eq, Equiv.symm_apply_eq, eq_comm]

/-- **The newforms with nebentypus in `[χ]` span the newspace `S_k^{new}(N, [χ])`**, those of
nebentypus `ψ` spanning `S_k^{new}(N, ψ)`. -/
lemma span_image_toCuspForm_eq_cuspFormsNewGaloisOrbit : Submodule.span ℂ
    ((fun f : Newform N k ↦ f.toCuspForm) '' {f | f.dirichletLift ∈ χ.galoisOrbit}) =
      cuspFormsNewGaloisOrbit k χ := by
  simp only [cuspFormsNewGaloisOrbit,
    ← Newform.span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace, ← Submodule.span_iUnion₂,
    ← Set.image_iUnion₂]
  congr 2
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, ← Newform.dirichletLift_eq_iff,
    exists_eq_right']

/-- **The newform subspace of a newform of nebentypus `χ` lies in the newspace
`S_k^{new}(N, [χ])`**: its Galois conjugates have nebentypus in `[χ]`. -/
lemma Newform.newformSubspace_le_cuspFormsNewGaloisOrbit (f : Newform N k) :
    f.newformSubspace ≤ cuspFormsNewGaloisOrbit k f.dirichletLift := by
  refine (Submodule.span_mono <| Set.image_mono fun g hg ↦ ?_).trans_eq
    (span_image_toCuspForm_eq_cuspFormsNewGaloisOrbit _)
  rcases hg with ⟨_, hσ⟩
  exact hσ.dirichletLift_mem_galoisOrbit

namespace NewformOrbit

/-- **The newform subspaces of the newform orbits whose nebentypus lies in `[χ]` are
independent.** -/
lemma iSupIndep_newformSubspace_characterOrbit :
    iSupIndep fun O : {O : NewformOrbit N k // O.characterOrbit = χ.galoisOrbit} ↦
      O.1.newformSubspace :=
  iSupIndep_newformSubspace.comp Subtype.val_injective

/-- **The newform subspaces of the newform orbits whose nebentypus lies in `[χ]` span the newspace
`S_k^{new}(N, [χ])`** (LMFDB `cmf.newform_subspace`): with
`HeckeRing.GL2.NewformOrbit.iSupIndep_newformSubspace_characterOrbit`, the newspace is their direct
sum. -/
lemma iSup_newformSubspace_characterOrbit :
    ⨆ O : {O : NewformOrbit N k // O.characterOrbit = χ.galoisOrbit}, O.1.newformSubspace =
      cuspFormsNewGaloisOrbit k χ := by
  rw [← span_image_toCuspForm_eq_cuspFormsNewGaloisOrbit]
  simp only [newformSubspace, ← Submodule.span_iUnion]
  congr 2
  ext g
  simp [characterOrbit_newformOrbit, MulChar.galoisOrbit_eq_galoisOrbit_iff]

end NewformOrbit

end HeckeRing.GL2
