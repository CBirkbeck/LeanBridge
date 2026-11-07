import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.FourierExpansion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.Level

/-!
# The translation lattice of an arithmetic group is commensurable with `V_g(ℤ)`

The translation lattice `L_Γ` of a subgroup `Γ` of `Sp(2g, ℚ)` is the group of the rational
symmetric matrices `s` with `(1, s; 0, 1) ∈ Γ`: the preimage of `Γ` under the homomorphism
`s ↦ (1, s; 0, 1)` from the additive group of the vector space `V_g(ℚ)` of rational symmetric
matrices to `Sp(2g, ℚ)`. Preimages of commensurable subgroups are commensurable, and the
translation lattice of `Sp(2g, ℤ)` is the group `V_g(ℤ)` of integral symmetric matrices. So the
translation lattice of a subgroup commensurable with `Sp(2g, ℤ)` is commensurable with `V_g(ℤ)`.

## Main definitions

* `SiegelUpperHalfSpace.symmetricMatrices` (LMFDB `mf.siegel.q-expansion`): the vector space
  `V_g(ℚ)` of rational symmetric matrices.
* `SiegelUpperHalfSpace.integralSymmetricMatrices` (LMFDB `mf.siegel.q-expansion`): the group
  `V_g(ℤ)` of integral symmetric matrices.
* `SiegelUpperHalfSpace.translationHom`: the homomorphism `s ↦ (1, s; 0, 1)` from `V_g(ℚ)` to
  `Sp(2g, ℚ)`.

## Main results

* `SiegelUpperHalfSpace.translationLattice_integral`: the translation lattice of `Sp(2g, ℤ)` is
  `V_g(ℤ)`.
* `SiegelUpperHalfSpace.commensurable_translationLattice`: commensurable subgroups have
  commensurable translation lattices.
* `SiegelUpperHalfSpace.commensurable_translationLattice_integralSymmetricMatrices` (LMFDB
  `mf.siegel.q-expansion`): the translation lattice of an arithmetic subgroup is commensurable with
  `V_g(ℤ)`.
-/

open Matrix

namespace SiegelUpperHalfSpace

variable (l : Type*)

/-- The vector space `V_g(ℚ)` (LMFDB `mf.siegel.q-expansion`) of the rational symmetric `g × g`
matrices, the matrices fixed by the transpose. -/
def symmetricMatrices : Submodule ℚ (Matrix l l ℚ) :=
  (transposeLinearEquiv l l ℚ ℚ).toLinearMap.eqLocus LinearMap.id

/-- The group `V_g(ℤ)` (LMFDB `mf.siegel.q-expansion`) of the integral symmetric `g × g` matrices,
as rational matrices. It is the translation lattice of `Sp(2g, ℤ)`
(`translationLattice_integral`). -/
def integralSymmetricMatrices : AddSubgroup (Matrix l l ℚ) where
  carrier := {s | sᵀ = s ∧ ∀ i j, ∃ z : ℤ, s i j = z}
  add_mem' {s t} hs ht := ⟨by rw [transpose_add, hs.1, ht.1], fun i j ↦ by
    rcases hs.2 i j with ⟨y, hy⟩
    rcases ht.2 i j with ⟨z, hz⟩
    exact ⟨y + z, by rw [Matrix.add_apply, hy, hz, Int.cast_add]⟩⟩
  zero_mem' := ⟨transpose_zero, fun _ _ ↦ ⟨0, by simp⟩⟩
  neg_mem' {s} hs := ⟨by rw [transpose_neg, hs.1], fun i j ↦ by
    rcases hs.2 i j with ⟨z, hz⟩
    exact ⟨-z, by rw [Matrix.neg_apply, hz, Int.cast_neg]⟩⟩

variable {l} in
lemma mem_symmetricMatrices {s : Matrix l l ℚ} : s ∈ symmetricMatrices l ↔ sᵀ = s :=
  Iff.rfl

variable [Fintype l] [DecidableEq l] {Γ Γ' : Subgroup (symplecticGroup l ℚ)}

/-- The homomorphism `s ↦ (1, s; 0, 1)` from the additive group of the vector space `V_g(ℚ)` of
rational symmetric matrices to `Sp(2g, ℚ)`. -/
def translationHom : Multiplicative (symmetricMatrices l) →* symplecticGroup l ℚ where
  toFun s := SymplecticGroup.symTranslation (s.toAdd : Matrix l l ℚ)
    (mem_symmetricMatrices.mp s.toAdd.2)
  map_one' := Subtype.ext <| by
    simp [SymplecticGroup.coe_symTranslation]
  map_mul' s t := Subtype.ext <| by
    rw [Submonoid.coe_mul, SymplecticGroup.coe_symTranslation, SymplecticGroup.coe_symTranslation,
      SymplecticGroup.coe_symTranslation, fromBlocks_multiply]
    simp [add_comm]

variable {l}

variable (Γ) in
lemma translationLattice_eq :
    translationLattice Γ = ((Γ.comap (translationHom l)).toAddSubgroup').map
      (symmetricMatrices l).subtype.toAddMonoidHom := by
  ext s
  refine ⟨fun ⟨hs, γ, hγ, hγs⟩ ↦ ⟨⟨s, mem_symmetricMatrices.mpr hs⟩, ?_, rfl⟩, ?_⟩
  · rwa [SetLike.mem_coe, Subgroup.mem_toAddSubgroup', Subgroup.mem_comap, show translationHom l
      (Multiplicative.ofAdd ⟨s, mem_symmetricMatrices.mpr hs⟩) = γ from Subtype.ext hγs.symm]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, _, hx, rfl⟩

variable (l) in
/-- **The translation lattice of `Sp(2g, ℤ)` is `V_g(ℤ)`**, the group of integral symmetric
matrices. -/
lemma translationLattice_integral :
    translationLattice (SymplecticGroup.integral l) = integralSymmetricMatrices l := by
  ext s
  refine ⟨fun ⟨hs, γ, hγ, hγs⟩ ↦ ⟨hs, fun i j ↦ ?_⟩, fun ⟨hs, hz⟩ ↦ ⟨hs, ?_⟩⟩
  · rcases hγ with ⟨δ, -, rfl⟩
    exact ⟨(δ : Matrix (l ⊕ l) (l ⊕ l) ℤ) (.inl i) (.inr j), by
      simpa using (congrFun₂ hγs (.inl i) (.inr j)).symm⟩
  · choose z hz using hz
    have hzs : (of z)ᵀ = of z := by
      ext i j
      have h : s j i = s i j := by
        simpa using congrFun₂ hs i j
      exact_mod_cast (hz j i).symm.trans (h.trans (hz i j))
    have hs' : (of z).map (Int.castRingHom ℚ) = s := by
      ext i j
      exact (hz i j).symm
    refine ⟨_, ⟨SymplecticGroup.symTranslation (of z) hzs, trivial, rfl⟩, ?_⟩
    rw [SymplecticGroup.coe_map_apply, SymplecticGroup.coe_symTranslation, fromBlocks_map, hs']
    simp

/-- **Commensurable subgroups of `Sp(2g, ℚ)` have commensurable translation lattices**: these are
their preimages under `s ↦ (1, s; 0, 1)`. -/
lemma commensurable_translationLattice (h : Γ.Commensurable Γ') :
    (translationLattice Γ).Commensurable (translationLattice Γ') := by
  rw [translationLattice_eq, translationLattice_eq]
  exact ⟨.map _ ⟨(h.1.comap (translationHom l)).relIndex_ne_zero⟩,
    .map _ ⟨(h.2.comap (translationHom l)).relIndex_ne_zero⟩⟩

/-- **The translation lattice `L_Γ` of an arithmetic subgroup `Γ` of `Sp(2g, ℚ)` is commensurable
with `V_g(ℤ)`** (LMFDB `mf.siegel.q-expansion`): `L_Γ ∩ V_g(ℤ)` has finite index in both. -/
lemma commensurable_translationLattice_integralSymmetricMatrices
    (hΓ : SymplecticGroup.IsArithmetic Γ) :
    (translationLattice Γ).Commensurable (integralSymmetricMatrices l) :=
  translationLattice_integral l ▸ commensurable_translationLattice hΓ

end SiegelUpperHalfSpace
