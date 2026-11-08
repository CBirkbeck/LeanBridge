import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2CanonicalLabel
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.CartanConjugate

/-!
# The projective image of an exceptional subgroup of `GL₂(𝔽_p)`

A subgroup `H` of `GL₂(𝔽_p)` is exceptional (LMFDB `gl2.exceptional`) if it does not contain
`SL₂(𝔽_p)` and lies neither in a Borel subgroup nor in the normalizer of a Cartan subgroup. By
Dickson's classification (`Matrix.GeneralLinearGroup.exists_holds`), some conjugate of `H` contains
`SL₂(𝔽_p)`, lies in the Borel group `B` of upper triangular matrices, in `Cs ≤ Ns`, `Cn ≤ Nn`, `Ns`
or `Nn`, or has projective image `A₄`, `S₄` or `A₅`. Conjugating back, `H` would contain
`SL₂(𝔽_p)`, which is normal, or lie in a conjugate of `B`, a Borel subgroup, or in a conjugate of
`Ns` or `Nn`, which are normalizers of Cartan subgroups in the LMFDB's sense, conjugates of these
being again such normalizers (`Matrix.GeneralLinearGroup.IsCartanNormalizer.map_conj`). So an
exceptional subgroup has projective image `A₄`, `S₄` or `A₅`, the projective images of conjugate
subgroups being isomorphic; the three types are distinct, of orders `12`, `24` and `60`. For the
same reason Sutherland's label of an exceptional subgroup has class `A4`, `S4` or `A5`, the type of
its projective image.

## Main definitions

* `Matrix.GeneralLinearGroup.ExceptionalType.card`: the order `12`, `24` or `60` of the group of an
  exceptional type.
* `Matrix.GeneralLinearGroup.ExceptionalType.toSutherlandClass`: the class `A4`, `S4` or `A5` of
  Sutherland's labels with the name of an exceptional type.

## Main results

* `Matrix.GeneralLinearGroup.isCartanNormalizer_labelNs`,
  `Matrix.GeneralLinearGroup.isCartanNormalizer_labelNn`: `Ns` and `Nn` are normalizers of Cartan
  subgroups in the LMFDB's sense.
* `Matrix.GeneralLinearGroup.HasExceptionalType.of_mem_subgroupConjClass`: the exceptional type is
  a conjugacy invariant.
* `Matrix.GeneralLinearGroup.HasExceptionalType.eq`: a subgroup has at most one exceptional type.
* `Matrix.GeneralLinearGroup.IsExceptionalSubgroup.not_holds` (LMFDB `gl2.exceptional`): an
  exceptional subgroup satisfies none of Sutherland's conditions for the classes `G`, `B`, `Cs`,
  `Cn`, `Ns`, `Nn`.
* `Matrix.GeneralLinearGroup.IsExceptionalSubgroup.exists_hasExceptionalType` (LMFDB
  `gl2.exceptional`): the projective image of an exceptional subgroup is isomorphic to `A₄`, `S₄`
  or `A₅`.
* `Matrix.GeneralLinearGroup.IsExceptionalSubgroup.exists_cls_eq` (LMFDB `gl2.exceptional`):
  Sutherland's label of an exceptional subgroup has class `A4`, `S4` or `A5`, the type of its
  projective image.
-/

open Matrix

open scoped Pointwise

namespace Matrix.GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] {H K X : Subgroup (GL (Fin 2) (ZMod p))} {t t' : ExceptionalType}

variable (p) in
/-- **`Ns` is the normalizer of a Cartan subgroup** of `GL₂(𝔽_p)` in the LMFDB's sense, for every
prime `p`. -/
lemma isCartanNormalizer_labelNs : IsCartanNormalizer (labelNs p) := by
  rcases isSplitCartanNormalizer_labelNs p with ⟨C, hC, h⟩
  exact ⟨C, hC.1, h⟩

variable (p) in
/-- **`Nn` is the normalizer of a Cartan subgroup** of `GL₂(𝔽_p)` in the LMFDB's sense, for every
prime `p`. -/
lemma isCartanNormalizer_labelNn : IsCartanNormalizer (labelNn p) := by
  rcases isNonsplitCartanNormalizer_labelNn p with ⟨C, hC, h⟩
  exact ⟨C, hC.1, h⟩

lemma exists_le_map_conj_of_mem_subgroupConjClass (hK : K ∈ subgroupConjClass p H) (hKX : K ≤ X) :
    ∃ P : GL (Fin 2) (ZMod p), H ≤ X.map (MulAut.conj P).toMonoidHom := by
  rcases hK with ⟨c, rfl⟩
  refine ⟨ConjAct.ofConjAct c⁻¹, ?_⟩
  rw [map_conj_eq_smul, ConjAct.toConjAct_ofConjAct,
    ← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := c), smul_inv_smul]
  exact hKX

lemma det_ker_le_of_mem_subgroupConjClass (hK : K ∈ subgroupConjClass p H)
    (hk : GeneralLinearGroup.det.ker ≤ K) : GeneralLinearGroup.det.ker ≤ H := by
  rcases hK with ⟨c, rfl⟩
  rwa [← GeneralLinearGroup.det.normal_ker.conjAct c,
    Subgroup.pointwise_smul_le_pointwise_smul_iff] at hk

/-- **The exceptional type is a conjugacy invariant**: a subgroup of `GL₂(𝔽_p)` has the exceptional
type of each of its conjugates, their projective images being isomorphic. -/
lemma HasExceptionalType.of_mem_subgroupConjClass (hK : K ∈ subgroupConjClass p H)
    (ht : HasExceptionalType K t) : HasExceptionalType H t := by
  rcases hK with ⟨c, rfl⟩
  have hc : c • H = H.map (MulAut.conj (ConjAct.ofConjAct c)).toMonoidHom := by
    rw [map_conj_eq_smul, ConjAct.toConjAct_ofConjAct]
  let e : projectiveImage (c • H) ≃* projectiveImage H :=
    (MulEquiv.subgroupCongr (congrArg projectiveImage hc)).trans (projectiveImageMapConjEquiv H _)
  cases t <;> exact Nonempty.map e.symm.trans ht

/-- The order of the group `A₄`, `S₄` or `A₅` of an exceptional type: `12`, `24` or `60`. -/
def ExceptionalType.card : ExceptionalType → ℕ
  | .A4 => 12
  | .S4 => 24
  | .A5 => 60

lemma natCard_projectiveImage_of_hasExceptionalType (ht : HasExceptionalType H t) :
    Nat.card (projectiveImage H) = t.card := by
  cases t <;> rcases ht with ⟨e⟩ <;> simp +decide [Nat.card_congr e.toEquiv]

/-- **A subgroup of `GL₂(𝔽_p)` has at most one exceptional type**: the groups `A₄`, `S₄` and `A₅`
have orders `12`, `24` and `60`. -/
lemma HasExceptionalType.eq (ht : HasExceptionalType H t) (ht' : HasExceptionalType H t') :
    t = t' := by
  have h : t.card = t'.card := (natCard_projectiveImage_of_hasExceptionalType ht).symm.trans
    (natCard_projectiveImage_of_hasExceptionalType ht')
  cases t <;> cases t' <;> first
    | rfl
    | exact absurd h (by decide)

lemma IsExceptionalSubgroup.not_le_of_mem_subgroupConjClass (hH : IsExceptionalSubgroup H)
    (hK : K ∈ subgroupConjClass p H) (hX : IsCartanNormalizer X) : ¬K ≤ X := fun hKX ↦ by
  rcases exists_le_map_conj_of_mem_subgroupConjClass hK hKX with ⟨P, hP⟩
  exact hH.2.2 _ (hX.map_conj P) hP

/-- **An exceptional subgroup of `GL₂(𝔽_p)` satisfies none of Sutherland's conditions for the
classes `G`, `B`, `Cs`, `Cn`, `Ns`, `Nn`** (LMFDB `gl2.exceptional`): a conjugate containing
`SL₂(𝔽_p)` or lying in `B`, `Cs`, `Cn`, `Ns` or `Nn` would make it contain `SL₂(𝔽_p)` or lie in a
Borel subgroup or in the normalizer of a Cartan subgroup. -/
lemma IsExceptionalSubgroup.not_holds (hH : IsExceptionalSubgroup H) {S : SutherlandClass}
    (hS : S.toNat < 6) : ¬S.Holds p H := by
  cases S
  · rintro ⟨K, hK, hk⟩
    exact hH.1 (det_ker_le_of_mem_subgroupConjClass hK hk)
  · rintro ⟨K, hK, hKB, -⟩
    rcases exists_le_map_conj_of_mem_subgroupConjClass hK hKB with ⟨P, hP⟩
    exact hH.2.1 _ (isBorelSubgroup_upperTriangularGroup.map_conj P) hP
  · rintro ⟨K, hK, hKT⟩
    exact hH.not_le_of_mem_subgroupConjClass hK (isCartanNormalizer_labelNs p)
      (hKT.trans (diagonalTorus_le_labelNs p))
  · rintro ⟨⟨K, hK, hKC⟩, -⟩
    exact hH.not_le_of_mem_subgroupConjClass hK (isCartanNormalizer_labelNn p)
      (hKC.trans (labelCn_le_labelNn p))
  · rintro ⟨K, hK, hKN, -⟩
    exact hH.not_le_of_mem_subgroupConjClass hK (isCartanNormalizer_labelNs p) hKN
  · rintro ⟨⟨K, hK, hKN, -⟩, -⟩
    exact hH.not_le_of_mem_subgroupConjClass hK (isCartanNormalizer_labelNn p) hKN
  all_goals exact absurd hS (by decide)

/-- The class `A4`, `S4` or `A5` of Sutherland's labels (LMFDB `gl2.exceptional`) bearing the name
of an exceptional type, that of the subgroups of `GL₂(𝔽_p)` with this projective image that do not
contain `SL₂(𝔽_p)`. -/
def ExceptionalType.toSutherlandClass : ExceptionalType → SutherlandClass
  | .A4 => .A4
  | .S4 => .S4
  | .A5 => .A5

lemma IsExceptionalSubgroup.exists_eq_toSutherlandClass (hH : IsExceptionalSubgroup H)
    {S : SutherlandClass} (hS : S.Holds p H) :
    ∃ t : ExceptionalType, S = t.toSutherlandClass ∧ HasExceptionalType H t := by
  cases S
  iterate 6 exact absurd hS (hH.not_holds (by decide))
  all_goals
    rcases hS with ⟨K, hK, ht, -⟩
    refine ⟨_, ?_, ht.of_mem_subgroupConjClass hK⟩
    rfl

/-- **The projective image of an exceptional subgroup of `GL₂(𝔽_p)` is isomorphic to `A₄`, `S₄` or
`A₅`** (LMFDB `gl2.exceptional`), by Dickson's classification. -/
lemma IsExceptionalSubgroup.exists_hasExceptionalType (hH : IsExceptionalSubgroup H) :
    ∃ t : ExceptionalType, HasExceptionalType H t :=
  (exists_holds H).elim fun _ hS ↦ (hH.exists_eq_toSutherlandClass hS).imp fun _ ↦ And.right

/-- **Sutherland's label of an exceptional subgroup of `GL₂(𝔽_p)` has class `A4`, `S4` or `A5`, the
type of its projective image** (LMFDB `gl2.exceptional`): exceptional subgroups are labelled by
identifiers containing one of the strings `A4`, `S4`, `A5`. -/
lemma IsExceptionalSubgroup.exists_cls_eq (hH : IsExceptionalSubgroup H) {L : SutherlandGroupLabel}
    (hL : IsCanonicalSutherlandLabel p H L) :
    ∃ t : ExceptionalType, L.cls = t.toSutherlandClass ∧ HasExceptionalType H t :=
  hH.exists_eq_toSutherlandClass hL.1.1

end Matrix.GeneralLinearGroup
