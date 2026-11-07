import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level

/-!
# The index of an open subgroup is the index of its reduction modulo its level

Let `H` be a subgroup of a group `G` and `π` a homomorphism such that `H = G ∩ π⁻¹(π(H))`. Then
`[G : H] = [π(G) : π(H)]`: the index of `π⁻¹(π(H))` in `G` is that of `π(H)` in `π(G)`. An open
subgroup `H` of a matrix group `G` over `ℤ_ℓ` or `ℤ̂` is the inverse image in `G` of its reduction
modulo its level `N`, so its index in `G` is the index of its reduction modulo `N` in the reduction
of `G` modulo `N`.

## Main results

* `Subgroup.relIndex_map_of_inf_comap_map_eq`: `[π(G) : π(H)] = [G : H]` when
  `H = G ∩ π⁻¹(π(H))`.
* `Matrix.GeneralLinearGroup.relIndex_map_padicReduction_padicLevel` (LMFDB `gl2.index`): for an
  open subgroup of a matrix group over `ℤ_ℓ`, the index is that of the reductions modulo its level.
* `Matrix.GeneralLinearGroup.relIndex_map_adelicReduction_adelicLevel` (LMFDB `gl2.index`): the
  same over `ℤ̂`.
-/

/-- **The index of a subgroup is the index of its image when it is the preimage of its image**:
`[π(G) : π(H)] = [G : H]` when `H = G ∩ π⁻¹(π(H))`. -/
lemma Subgroup.relIndex_map_of_inf_comap_map_eq {Γ Q : Type*} [Group Γ] [Group Q] (f : Γ →* Q)
    {G H : Subgroup Γ} (h : G ⊓ (H.map f).comap f = H) :
    (H.map f).relIndex (G.map f) = H.relIndex G := by
  rw [← relIndex_comap, ← inf_relIndex_left, h]

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The index of an open subgroup of a matrix group over `ℤ_ℓ` is the index of its reduction
modulo its level** (LMFDB `gl2.index`): for `H` open in `G ≤ GL_n(ℤ_ℓ)` of level `N`,
`[G : H] = [G mod N : H mod N]`. -/
lemma relIndex_map_padicReduction_padicLevel (ℓ : ℕ) [Fact ℓ.Prime] {G H : Subgroup (GL n ℤ_[ℓ])}
    (hHG : H ≤ G) (hH : IsOpen (H.subgroupOf G : Set G)) :
    (H.map (padicReduction ℓ (padicLevel ℓ G H))).relIndex
      (G.map (padicReduction ℓ (padicLevel ℓ G H))) = H.relIndex G :=
  Subgroup.relIndex_map_of_inf_comap_map_eq _ (inf_comap_map_padicReduction_padicLevel ℓ G hHG hH)

/-- **The index of an open subgroup of a matrix group over `ℤ̂` is the index of its reduction
modulo its level** (LMFDB `gl2.index`): for `H` open in `G ≤ GL_n(ℤ̂) = ∏_ℓ GL_n(ℤ_ℓ)` of level `N`,
`[G : H] = [G mod N : H mod N]`. -/
lemma relIndex_map_adelicReduction_adelicLevel {G H : Subgroup (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ])}
    (hHG : H ≤ G) (hH : IsOpen (H.subgroupOf G : Set G)) :
    (H.map (adelicReduction (adelicLevel G H))).relIndex
      (G.map (adelicReduction (adelicLevel G H))) = H.relIndex G :=
  Subgroup.relIndex_map_of_inf_comap_map_eq _ (inf_comap_map_adelicReduction_adelicLevel G hHG hH)

end Matrix.GeneralLinearGroup
