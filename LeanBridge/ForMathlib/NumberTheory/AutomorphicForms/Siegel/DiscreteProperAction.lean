import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.FourierLevi
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ProperDiscontinuity

/-!
# Discrete subgroups of `Sp(2g, ℝ)` act properly discontinuously on `ℋ_g`

The symplectic group `Sp(2g, R)` over a topological commutative ring `R` is a topological group for
the topology of its matrix entries, its inverse `-J Aᵀ J` being continuous. Over `ℝ`, a discrete
subgroup `Γ` of `Sp(2g, ℝ)` is therefore closed, so its elements with bounded entries form a
compact discrete set, which is finite. The elements of `Sp(2g, ℝ)` moving a compact set `K` of the
Siegel upper half-space `ℋ_g` to meet a compact set `L` have bounded entries
(`SiegelUpperHalfSpace.exists_abs_apply_le_of_isCompact`), so only finitely many of them lie in
`Γ`: the action of every discrete subgroup of `Sp(2g, ℝ)` on `ℋ_g` is properly discontinuous
(LMFDB `mf.siegel.halfspace`). The action of the integral symplectic group `Γ_g = Sp(2g, ℤ)` is not
free for `g ≥ 1`: its element `-1 ≠ 1` fixes every point of `ℋ_g`.

## Main definitions

* `SymplecticGroup.negOne`: the element `-1` of `Sp(2g, R)`.

## Main results

* The instance `IsTopologicalGroup (symplecticGroup l R)`, for a topological commutative ring `R`.
* `SiegelUpperHalfSpace.properlyDiscontinuousSMul_of_discreteTopology` (LMFDB
  `mf.siegel.halfspace`): a discrete subgroup of `Sp(2g, ℝ)` acts properly discontinuously on
  `ℋ_g`.
* `SiegelUpperHalfSpace.negOne_smul`: `-1` fixes every point of `ℋ_g`.
* `SiegelUpperHalfSpace.not_free_integral` (LMFDB `mf.siegel.halfspace`): the integral symplectic
  group `Γ_g` does not act freely on `ℋ_g` for `g ≥ 1`.
-/

open Matrix Set

variable {l R : Type*} [DecidableEq l] [Fintype l]

namespace SymplecticGroup

variable (l R) [CommRing R]

/-- The element **`-1`** of the symplectic group `Sp(2g, R)`. -/
def negOne : symplecticGroup l R :=
  ⟨-1, neg_mem (one_mem _)⟩

@[simp]
lemma coe_negOne : (negOne l R : Matrix (l ⊕ l) (l ⊕ l) R) = -1 :=
  rfl

variable [TopologicalSpace R] [IsTopologicalRing R]

instance : ContinuousInv (symplecticGroup l R) where
  continuous_inv := continuous_induced_rng.mpr (by fun_prop)

instance : IsTopologicalGroup (symplecticGroup l R) where

end SymplecticGroup

namespace SiegelUpperHalfSpace

lemma isCompact_setOf_abs_apply_le (M : ℝ) :
    IsCompact {γ : symplecticGroup l ℝ | ∀ x y, |(γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x y| ≤ M} := by
  have h₁ : IsClosed (symplecticGroup l ℝ : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ)) :=
    isClosed_eq (by fun_prop) continuous_const
  have h₂ : IsCompact (Icc (fun _ _ ↦ -M) fun _ _ ↦ M : Set ((l ⊕ l) → (l ⊕ l) → ℝ)) :=
    isCompact_Icc
  have h₃ : {γ : symplecticGroup l ℝ | ∀ x y, |(γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) x y| ≤ M} =
      Subtype.val ⁻¹' Icc (fun _ _ ↦ -M) fun _ _ ↦ M := by
    ext γ
    simp only [abs_le]
    exact ⟨fun h ↦ ⟨fun x y ↦ (h x y).1, fun x y ↦ (h x y).2⟩, fun h x y ↦ ⟨h.1 x y, h.2 x y⟩⟩
  rw [h₃]
  exact h₁.isClosedEmbedding_subtypeVal.isCompact_preimage h₂

/-- **A discrete subgroup `Γ` of `Sp(2g, ℝ)` acts properly discontinuously on `ℋ_g`** (LMFDB
`mf.siegel.halfspace`): `Γ` is closed, and the elements of `Sp(2g, ℝ)` moving a compact set to meet
a compact set have bounded entries, so finitely many of them lie in `Γ`. -/
lemma properlyDiscontinuousSMul_of_discreteTopology (Γ : Subgroup (symplecticGroup l ℝ))
    [DiscreteTopology Γ] : ProperlyDiscontinuousSMul Γ (SiegelUpperHalfSpace l) where
  finite_disjoint_inter_image {K L} hK hL := by
    rcases exists_abs_apply_le_of_isCompact hK hL with ⟨M, hM⟩
    have hΓ : IsClosed (Γ : Set (symplecticGroup l ℝ)) := Subgroup.isClosed_of_discreteTopology
    have hc : IsCompact {γ : Γ | ∀ x y,
        |((γ : symplecticGroup l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ) x y| ≤ M} :=
      hΓ.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_setOf_abs_apply_le M)
    refine hc.finite_of_discrete.subset fun γ hγ x y ↦ ?_
    rcases hγ with ⟨_, ⟨τ, hτ, rfl⟩, hτL⟩
    exact hM γ τ hτ hτL x y

instance (Γ : Subgroup (symplecticGroup l ℝ)) [DiscreteTopology Γ] :
    ProperlyDiscontinuousSMul Γ (SiegelUpperHalfSpace l) :=
  properlyDiscontinuousSMul_of_discreteTopology Γ

/-- **The element `-1` of `Sp(2g, ℝ)` fixes every point of `ℋ_g`**: `(-τ)(-1)⁻¹ = τ`. -/
lemma negOne_smul (τ : SiegelUpperHalfSpace l) : SymplecticGroup.negOne l ℝ • τ = τ := by
  ext1
  rw [val_smul, num, denom, SymplecticGroup.coe_negOne, ← fromBlocks_one, fromBlocks_neg,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp [Matrix.map_neg _ Complex.ofReal_neg,
    Matrix.inv_eq_left_inv (by simp : (-1 : Matrix l l ℂ) * -1 = 1)]

/-- **The integral symplectic group `Γ_g = Sp(2g, ℤ)` does not act freely on `ℋ_g`** for `g ≥ 1`
(LMFDB `mf.siegel.halfspace`): its element `-1 ≠ 1` fixes every point. -/
lemma not_free_integral [Nonempty l] : ¬∀ γ ∈ SymplecticGroup.integral l,
    ∀ τ : SiegelUpperHalfSpace l, SymplecticGroup.map (algebraMap ℚ ℝ) γ • τ = τ → γ = 1 := by
  intro h
  have h₁ : SymplecticGroup.negOne l ℚ ∈ SymplecticGroup.integral l :=
    ⟨SymplecticGroup.negOne l ℤ, trivial, Subtype.ext <| by
      simp [Matrix.map_neg (fun x : ℤ ↦ (x : ℚ)) fun a ↦ Int.cast_neg a]⟩
  have h₂ : SymplecticGroup.map (algebraMap ℚ ℝ) (SymplecticGroup.negOne l ℚ) =
      SymplecticGroup.negOne l ℝ :=
    Subtype.ext (by simp [Matrix.map_neg _ (map_neg (algebraMap ℚ ℝ))])
  have h₃ : SymplecticGroup.negOne l ℚ = 1 := h _ h₁ basePoint (h₂ ▸ negOne_smul basePoint)
  rcases ‹Nonempty l› with ⟨i⟩
  have h₄ : (-1 : ℚ) = 1 := by
    simpa using congrFun (congrFun (congrArg Subtype.val h₃) (.inl i)) (.inl i)
  norm_num at h₄

end SiegelUpperHalfSpace
