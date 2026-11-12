import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.CartanNormalizerIndex

/-!
# The normalizers of split Cartan subgroups are the conjugates of `Ns`

Every split Cartan subgroup of `GL₂(F)` is conjugate to the group `Cs` of invertible diagonal
matrices (`Matrix.GeneralLinearGroup.IsSplitCartanSubgroup.exists_map_conj_eq`), and conjugation
carries normalizers to normalizers, so for `p > 2` the normalizer of a split Cartan subgroup of
`GL₂(𝔽_p)` is conjugate to the normalizer `Ns` of `Cs`. For `p = 2`, where the LMFDB calls a
subgroup containing a split Cartan subgroup with index `2` its normalizer, such a group and `Ns`
both have order `2`: they are Sylow `2`-subgroups of `GL₂(𝔽₂)`, hence conjugate. Conversely, the
conjugates of split Cartan subgroups and of their normalizers are again such groups. So the
normalizers of split Cartan subgroups of `GL₂(𝔽_p)` (LMFDB `gl2.normalizer_split_cartan`) are
exactly the conjugates of `Ns`, for every prime `p`.

## Main results

* `Matrix.GeneralLinearGroup.IsSplitCartanSubgroup.map_conj`: a conjugate of a split Cartan
  subgroup is a split Cartan subgroup.
* `Matrix.GeneralLinearGroup.IsSplitCartanNormalizer.map_conj`: a conjugate of the normalizer of a
  split Cartan subgroup is the normalizer of a split Cartan subgroup.
* `Matrix.GeneralLinearGroup.IsSplitCartanNormalizer.exists_map_conj_eq` (LMFDB
  `gl2.normalizer_split_cartan`): every normalizer of a split Cartan subgroup is conjugate to `Ns`.
* `Matrix.GeneralLinearGroup.isSplitCartanNormalizer_iff` (LMFDB `gl2.normalizer_split_cartan`):
  the normalizers of split Cartan subgroups of `GL₂(𝔽_p)` are exactly the conjugates of `Ns`.
-/

open TauCeti

namespace Matrix.GeneralLinearGroup

/-- **A conjugate of a split Cartan subgroup is a split Cartan subgroup**: it is conjugate to the
group of invertible diagonal matrices. -/
lemma IsSplitCartanSubgroup.map_conj {F : Type*} [Field F] {C : Subgroup (GL (Fin 2) F)}
    (hC : IsSplitCartanSubgroup C) (g : GL (Fin 2) F) :
    IsSplitCartanSubgroup (C.map (MulAut.conj g).toMonoidHom) := by
  rcases hC.exists_map_conj_eq with ⟨k, hk⟩
  refine isSplitCartanSubgroup_iff.mpr ⟨k * g⁻¹, ?_⟩
  rw [Subgroup.map_map, ← hk]
  congr 1
  exact MonoidHom.ext fun x ↦ by simp [mul_assoc]

variable {p : ℕ} [Fact p.Prime] {H : Subgroup (GL (Fin 2) (ZMod p))}

lemma natCard_labelNs_two : Nat.card (labelNs 2) = 2 := by
  have h : (diagonalTorus (ZMod 2) 2).relIndex (labelNs 2) = 2 := relIndex_diagonalTorus_labelNs 2
  rwa [diagonalTorus_eq_bot, Subgroup.relIndex_bot_left] at h

/-- **A conjugate of the normalizer of a split Cartan subgroup of `GL₂(𝔽_p)` is the normalizer of
a split Cartan subgroup**, in the LMFDB's convention: the normalizer of the conjugate split Cartan
subgroup for `p > 2`, and a subgroup containing it with index `2` for `p = 2`. -/
lemma IsSplitCartanNormalizer.map_conj (hH : IsSplitCartanNormalizer H) (g : GL (Fin 2) (ZMod p)) :
    IsSplitCartanNormalizer (H.map (MulAut.conj g).toMonoidHom) := by
  rcases hH with ⟨C, hC, h⟩
  refine ⟨C.map (MulAut.conj g).toMonoidHom, hC.map_conj g, ?_⟩
  split_ifs at h ⊢
  · exact ⟨Subgroup.map_mono h.1,
      (Subgroup.relIndex_map_map_of_injective C H (MulAut.conj g).injective).trans h.2⟩
  · rw [h, Subgroup.map_equiv_normalizer_eq]

/-- **Every normalizer of a split Cartan subgroup of `GL₂(𝔽_p)` is conjugate to `Ns`** (LMFDB
`gl2.normalizer_split_cartan`), for every prime `p`: for `p > 2` the split Cartan subgroup is
conjugate to `Cs`, so its normalizer to the normalizer `Ns` of `Cs`, and for `p = 2` both groups
have order `2`, so are Sylow `2`-subgroups of `GL₂(𝔽₂)`. -/
lemma IsSplitCartanNormalizer.exists_map_conj_eq (hH : IsSplitCartanNormalizer H) :
    ∃ g : GL (Fin 2) (ZMod p), H.map (MulAut.conj g).toMonoidHom = labelNs p := by
  by_cases hp : p = 2
  · subst hp
    exact exists_map_conj_eq_of_natCard_eq_two (hH.natCard_eq_two rfl) natCard_labelNs_two
  · rcases hH with ⟨C, hC, h⟩
    rw [ite_eq_right hp] at h
    rcases hC.exists_map_conj_eq with ⟨g, hg⟩
    exact ⟨g, by rw [h, Subgroup.map_equiv_normalizer_eq, hg, labelNs_eq_normalizer p hp]⟩

/-- **The normalizers of split Cartan subgroups of `GL₂(𝔽_p)` are exactly the conjugates of `Ns`**
(LMFDB `gl2.normalizer_split_cartan`), for every prime `p`. -/
lemma isSplitCartanNormalizer_iff : IsSplitCartanNormalizer H ↔
    ∃ g : GL (Fin 2) (ZMod p), H.map (MulAut.conj g).toMonoidHom = labelNs p := by
  refine ⟨fun hH ↦ hH.exists_map_conj_eq, fun ⟨g, hg⟩ ↦ ?_⟩
  have hH : (labelNs p).map (MulAut.conj g⁻¹).toMonoidHom = H := by
    rw [← hg, Subgroup.map_map]
    convert Subgroup.map_id H
    exact MonoidHom.ext fun x ↦ by simp [mul_assoc]
  exact hH ▸ (isSplitCartanNormalizer_labelNs p).map_conj g⁻¹

end Matrix.GeneralLinearGroup
