import Mathlib.GroupTheory.SpecificGroups.Dihedral
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.ExceptionalDeterminant
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SutherlandLabel

/-!
# Sutherland's labels `ℓS.a.b.c[d]` of subgroups of `GL₂(𝔽_ℓ)`

Sutherland (*Computing images of Galois representations attached to elliptic curves*, Forum Math.
Sigma 4 (2016), arXiv:1504.07618v7, §6.4 "Group labels", pp. 35–36) identifies conjugacy classes of
subgroups `G` of `GL₂(𝔽_ℓ)` by labels `ℓS.a.b.c[d]`, which the LMFDB uses for mod-`ℓ` Galois images
(LMFDB `ec.galois_rep_modell_image`):

* `S` is one of `G`, `B`, `Cs`, `Cn`, `Ns`, `Nn`, `A4`, `S4`, `A5`, given by a condition on the
  conjugacy class of `G` (`SutherlandClass.Holds`);
* `d` is the index of `det G` in `𝔽_ℓˣ`; the suffix `[d]` is omitted when `d = 1`;
* `a`, `b`, `c` are optional nonnegative integers. For `G`, `B`, `Cs`, `Cn`, `Ns`, `Nn` the label
  names a subgroup of `GL₂(𝔽_ℓ)` by generators built from `r`, the least positive integer
  generating the subgroup of index `d` of `𝔽_ℓˣ`, and `ε`, the least primitive root modulo `ℓ`;
  the label of `G` is the one naming a group conjugate to `G`, with `a`, `b`, `c` minimal and, for
  `Ns` and `Nn`, with the number of integers that Sutherland's script chooses. For `A4`, `S4`,
  `A5` they record the index `[det G : det Z(G)]`, `Z(G) = G ∩ Z(ℓ)` the scalars.

The groups of the labels with `d = 1` are the LMFDB's groups of `SutherlandLabel.subgroup`. Where
the paper's text is ambiguous or slips, the definitions follow its tables and its Magma script
(reference [68] of the paper), as the docstrings say.

## Main definitions

* `ZMod.leastGenOfIndex`: the least positive integer `r` generating the subgroup of index `d`.
* `Matrix.GeneralLinearGroup.SutherlandClass` (LMFDB `ec.galois_rep_modell_image`): the nine
  classes `S`; `SutherlandClass.Holds` is Sutherland's condition for each, and
  `Matrix.GeneralLinearGroup.HasSutherlandClass` the class of a subgroup.
* `Matrix.GeneralLinearGroup.labelGD` (LMFDB `ec.galois_rep_modell_image`): the group `ℓG[d]`;
  `labelBD`, `labelCsD`, `labelCnD`, `labelNsD`, `labelNnD`, `labelBABD`, `labelCsABD`,
  `labelNsABD`, `labelNsABCD` and `labelNnABC` are the other groups the labels name.
* `Matrix.GeneralLinearGroup.SutherlandGroupLabel` (LMFDB `ec.galois_rep_modell_image`): a label
  `ℓS.a.b.c[d]`, and `SutherlandGroupLabel.namedSubgroup`, the subgroup it names.
* `Matrix.GeneralLinearGroup.IsSutherlandLabel` (LMFDB `ec.galois_rep_modell_image`): a label is
  Sutherland's label of a subgroup.

## Main results

* `ZMod.leastGenOfIndex_five_one`, `ZMod.leastGenOfIndex_eleven_two`: tests of `r` against
  Sutherland's tables, with `d = 1` and `d = 2`, and
  `Matrix.GeneralLinearGroup.isSutherlandLabel_labelCn_two`,
  `Matrix.GeneralLinearGroup.isSutherlandLabel_three_Cs_one_one`: `C_ns(2)` and
  `⟨diag(1, -1)⟩ ≤ GL₂(𝔽₃)` have the labels `2Cn` and `3Cs.1.1`, as in his Table 3;
  `Matrix.GeneralLinearGroup.labelBABD_seven_two_six_three`: his tables do not take `(a, b)`
  lexicographically least among all pairs naming a conjugate group.
* `Matrix.GeneralLinearGroup.isSutherlandLabel_smul_iff`: the label is a conjugacy invariant.
* `Matrix.GeneralLinearGroup.IsSutherlandLabel.mem_subgroupConjClass`: two subgroups with the same
  label naming a subgroup are conjugate, and
  `Matrix.GeneralLinearGroup.IsSutherlandLabel.exists_mem_namedSubgroup`: every label of class `G`,
  `B`, `Cs`, `Cn`, `Ns`, `Nn` names a subgroup.
* `Matrix.GeneralLinearGroup.IsSutherlandLabel.cls_eq`: the class of the label is unique;
  `Matrix.GeneralLinearGroup.IsSutherlandLabel.eq`: so is the label, for classes other than `Ns`
  and `Nn`, and `Matrix.GeneralLinearGroup.IsSutherlandLabel.eq_of_length_eq`: for all classes,
  given its number of integers.
* `Matrix.GeneralLinearGroup.IsSutherlandLabel.cls_eq_G_iff`: the class is `G` exactly for the
  subgroups containing `SL₂(𝔽_p)`, and `Matrix.GeneralLinearGroup.isSutherlandLabel_G`: these have
  the label `ℓG[d]`.
* `Matrix.GeneralLinearGroup.exists_isSutherlandLabel_of_hasSutherlandClass_Cn`: every subgroup of
  class `Cn` has a label, for odd `p`.
* `Matrix.GeneralLinearGroup.IsSutherlandLabel.cls_eq_S4`: with surjective determinant, the classes
  `A4` and `A5` do not occur, and `Matrix.GeneralLinearGroup.IsSutherlandLabel.one_lt_d`: their
  labels have `d > 1`.
* `Matrix.GeneralLinearGroup.labelBABD_one`: with `d = 1`, `B.a.b[d]` is the LMFDB's `B.a.b`; the
  same holds for `Cs.a.b`, `Ns.a.b` and `Ns.a.b.c`.
-/

open Matrix MulAction Prod TauCeti

open scoped Pointwise

namespace ZMod

variable (p d : ℕ) [Fact p.Prime]

/-- The least positive integer `r` that generates the subgroup of index `d` of `(ℤ/pℤ)ˣ`, that is,
whose order modulo `p` is `(p - 1) / d` (Sutherland, arXiv:1504.07618, §6.4; LMFDB
`ec.galois_rep_modell_image`). It is the least primitive root for `d = 1`
(`leastGenOfIndex_one`); its value when `d` does not divide `p - 1` is junk. -/
noncomputable def leastGenOfIndex : ℕ :=
  sInf {r : ℕ | 0 < r ∧ orderOf (r : ZMod p) = (p - 1) / d}

lemma orderOf_leastPrimitiveRoot_pow (hd : d ∣ p - 1) :
    orderOf ((leastPrimitiveRoot p ^ d : ℕ) : ZMod p) = (p - 1) / d := by
  have hp : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt
  rw [Nat.cast_pow, orderOf_pow_of_dvd (ne_zero_of_dvd_ne_zero hp hd), orderOf_leastPrimitiveRoot]
  rwa [orderOf_leastPrimitiveRoot]

lemma leastGenOfIndex_mem (hd : d ∣ p - 1) :
    leastGenOfIndex p d ∈ {r : ℕ | 0 < r ∧ orderOf (r : ZMod p) = (p - 1) / d} :=
  Nat.sInf_mem ⟨_, pow_pos (leastPrimitiveRoot_pos p) d, orderOf_leastPrimitiveRoot_pow p d hd⟩

lemma leastGenOfIndex_pos (hd : d ∣ p - 1) : 0 < leastGenOfIndex p d :=
  (leastGenOfIndex_mem p d hd).1

lemma orderOf_leastGenOfIndex (hd : d ∣ p - 1) :
    orderOf (leastGenOfIndex p d : ZMod p) = (p - 1) / d :=
  (leastGenOfIndex_mem p d hd).2

lemma leastGenOfIndex_le {r : ℕ} (hr : 0 < r) (h : orderOf (r : ZMod p) = (p - 1) / d) :
    leastGenOfIndex p d ≤ r :=
  Nat.sInf_le ⟨hr, h⟩

lemma leastGenOfIndex_one : leastGenOfIndex p 1 = leastPrimitiveRoot p :=
  le_antisymm (leastGenOfIndex_le p 1 (leastPrimitiveRoot_pos p) <| by
    rw [orderOf_leastPrimitiveRoot, Nat.div_one]) <|
    leastPrimitiveRoot_le (leastGenOfIndex_pos p 1 (one_dvd _)) <| by
      rw [orderOf_leastGenOfIndex p 1 (one_dvd _), Nat.div_one]

lemma leastGenOfIndex_eq {r : ℕ} (hr : 0 < r) (h : orderOf (r : ZMod p) = (p - 1) / d)
    (hlt : ∀ s : ℕ, 0 < s → s < r → orderOf (s : ZMod p) ≠ (p - 1) / d) :
    leastGenOfIndex p d = r := by
  have hm : leastGenOfIndex p d ∈ {r : ℕ | 0 < r ∧ orderOf (r : ZMod p) = (p - 1) / d} :=
    Nat.sInf_mem ⟨r, hr, h⟩
  exact le_antisymm (leastGenOfIndex_le p d hr h) (not_lt.mp fun hc ↦ hlt _ hm.1 hc hm.2)

/-- **Test against Sutherland's Table 3**: `r = 2` for `ℓ = 5`, `d = 1`, so the generator
`!![4, 0; 0, r/4]` of `5B.1.4` is `!![4, 0; 0, 3]` (`2 = 3 * 4` in `𝔽₅`), as listed there. -/
lemma leastGenOfIndex_five_one :
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    leastGenOfIndex 5 1 = 2 :=
  @leastGenOfIndex_eq 5 1 ⟨Nat.prime_five⟩ 2 two_pos
    ((orderOf_eq_iff four_pos).mpr ⟨by decide, by decide⟩) fun s hs hs2 ↦ by interval_cases s; simp

/-- **Test against Sutherland's tables over quadratic fields** (§6.5): `r = 3` for `ℓ = 11`, `d = 2`
(the least generator of the squares, not the least primitive root `2`), so the generator
`!![4, 0; 0, r/4]` of `11B.1.4[2]` is `!![4, 0; 0, 9]` (`3 = 9 * 4` in `𝔽₁₁`), as listed there. -/
lemma leastGenOfIndex_eleven_two :
    haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    leastGenOfIndex 11 2 = 3 := by
  have h₂ : orderOf (2 : ZMod 11) = 10 :=
    (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
  exact @leastGenOfIndex_eq 11 2 ⟨Nat.prime_eleven⟩ 3 three_pos
    ((orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩) fun s hs hs3 ↦ by
      interval_cases s <;> simp [h₂]

end ZMod

namespace Matrix.GeneralLinearGroup

variable (p : ℕ) [Fact p.Prime] (d a b c : ℕ) (H : Subgroup (GL (Fin 2) (ZMod p)))

/-- The **classes** `S` of Sutherland's labels `ℓS.a.b.c[d]` of subgroups of `GL₂(𝔽_ℓ)`
(arXiv:1504.07618, §6.4; LMFDB `ec.galois_rep_modell_image`), in the order of his list. -/
inductive SutherlandClass
  /-- `G`: the subgroup contains `SL₂(𝔽_ℓ)`. -/
  | G
  /-- `B`: a subgroup of a Borel subgroup containing an element of order `ℓ`. -/
  | B
  /-- `Cs`: a subgroup of a split Cartan subgroup. -/
  | Cs
  /-- `Cn`: a subgroup of a non-split Cartan subgroup, not of a split one. -/
  | Cn
  /-- `Ns`: a subgroup of the normalizer of a split Cartan subgroup, with dihedral projective
  image. -/
  | Ns
  /-- `Nn`: a subgroup of the normalizer of a non-split Cartan subgroup, with dihedral projective
  image, and not of the normalizer of a split one. -/
  | Nn
  /-- `A4`: projective image `A₄`. -/
  | A4
  /-- `S4`: projective image `S₄`. -/
  | S4
  /-- `A5`: projective image `A₅`. -/
  | A5

/-- The position of a class in Sutherland's list `G, B, Cs, Cn, Ns, Nn, A4, S4, A5` (the integer `n`
of the identifiers `[ℓ, d, n, a, b, c]` of his Magma script). -/
def SutherlandClass.toNat : SutherlandClass → ℕ
  | .G => 0
  | .B => 1
  | .Cs => 2
  | .Cn => 3
  | .Ns => 4
  | .Nn => 5
  | .A4 => 6
  | .S4 => 7
  | .A5 => 8

lemma SutherlandClass.toNat_injective : Function.Injective SutherlandClass.toNat := by
  intro S T h
  cases S <;> cases T <;> first | rfl | exact absurd h (by decide)

/-- The conjugacy class of a subgroup `H` of `GL₂(𝔽_p)`. -/
abbrev subgroupConjClass : Set (Subgroup (GL (Fin 2) (ZMod p))) :=
  orbit (ConjAct (GL (Fin 2) (ZMod p))) H

/-- A subgroup of `GL₂(𝔽_p)` **has dihedral projective image** if its image in `PGL₂(𝔽_p)` is
isomorphic to a dihedral group `D_n`, `n ≥ 2`, of order `2n`: Sutherland (arXiv:1504.07618, §2)
counts the Klein group `D₂` as dihedral. -/
def HasDihedralImage : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ Nonempty (projectiveImage H ≃* DihedralGroup n)

/-- **Sutherland's condition** for a subgroup `H` of `GL₂(𝔽_p)` to have a label of class `S`
(arXiv:1504.07618, §6.4; LMFDB `ec.galois_rep_modell_image`), a condition on the conjugacy class of
`H`: `G` if `H` contains `SL₂(𝔽_p)`; `B` if `H` is conjugate to a subgroup of the Borel group of
upper triangular matrices containing an element of order `p`; `Cs` if it is conjugate to a subgroup
of `C_s` (diagonal matrices); `Cn` if it is conjugate to a subgroup of `C_ns` (`labelCn`) but not of
`C_s`; `Ns` if it is conjugate to a subgroup of `C_s⁺` (`labelNs`) with dihedral projective image;
`Nn` if it is conjugate to a subgroup of `C_ns⁺` (`labelNn`) with dihedral projective image but not
to a subgroup of `C_s⁺`; `A4`, `S4`, `A5` if its projective image is `A₄`, `S₄`, `A₅` and it does
not contain `SL₂(𝔽_p)` (for `A5` the paper omits this clause, needed at `p = 5`, where `5G[2]` has
projective image `PSL₂(𝔽₅) ≅ A₅`). -/
def SutherlandClass.Holds : SutherlandClass → Prop
  | .G => ∃ K ∈ subgroupConjClass p H, GeneralLinearGroup.det.ker ≤ K
  | .B => ∃ K ∈ subgroupConjClass p H, K ≤ GL2Borel (ZMod p) ∧ ∃ g ∈ K, orderOf g = p
  | .Cs => ∃ K ∈ subgroupConjClass p H, K ≤ diagonalTorus (ZMod p) 2
  | .Cn => (∃ K ∈ subgroupConjClass p H, K ≤ labelCn p) ∧
      ¬∃ K ∈ subgroupConjClass p H, K ≤ diagonalTorus (ZMod p) 2
  | .Ns => ∃ K ∈ subgroupConjClass p H, K ≤ labelNs p ∧ HasDihedralImage p K
  | .Nn => (∃ K ∈ subgroupConjClass p H, K ≤ labelNn p ∧ HasDihedralImage p K) ∧
      ¬∃ K ∈ subgroupConjClass p H, K ≤ labelNs p
  | .A4 => ∃ K ∈ subgroupConjClass p H, HasExceptionalType K .A4 ∧ ¬GeneralLinearGroup.det.ker ≤ K
  | .S4 => ∃ K ∈ subgroupConjClass p H, HasExceptionalType K .S4 ∧ ¬GeneralLinearGroup.det.ker ≤ K
  | .A5 => ∃ K ∈ subgroupConjClass p H, HasExceptionalType K .A5 ∧ ¬GeneralLinearGroup.det.ker ≤ K

/-- A subgroup `H` of `GL₂(𝔽_p)` **has Sutherland class** `S` (LMFDB `ec.galois_rep_modell_image`)
if it satisfies Sutherland's condition for `S` and none of the conditions of the classes before `S`
in his list. His conditions are meant to be mutually exclusive (Proposition 3.1 of the paper); the
order only resolves the case `p = 2`, where the LMFDB's `Nn = GL₂(𝔽₂)` (`labelNn_two`) has
dihedral projective image `S₃` and Sutherland's class of `GL₂(𝔽₂)` is `G`. -/
def HasSutherlandClass (S : SutherlandClass) : Prop :=
  S.Holds p H ∧ ∀ T : SutherlandClass, T.toNat < S.toNat → ¬T.Holds p H

/-- The group `ℓG[d]` (arXiv:1504.07618, §6.4; LMFDB `ec.galois_rep_modell_image`): the matrices
whose determinant lies in the subgroup of index `d` of `𝔽_pˣ`, that of the `d`-th powers. For
`d ∣ p - 1` it is the subgroup of index `d` of `GL₂(𝔽_p)` containing `SL₂(𝔽_p)`; `ℓG[1]` is
`GL₂(𝔽_p)`. -/
noncomputable def labelGD : Subgroup (GL (Fin 2) (ZMod p)) :=
  (powMonoidHom d : (ZMod p)ˣ →* (ZMod p)ˣ).range.comap GeneralLinearGroup.det

/-- The group `ℓB[d] = ℓB ∩ ℓG[d]` (arXiv:1504.07618, §6.4). -/
noncomputable def labelBD : Subgroup (GL (Fin 2) (ZMod p)) :=
  GL2Borel (ZMod p) ⊓ labelGD p d

/-- The group `ℓCs[d] = ℓCs ∩ ℓG[d]` (arXiv:1504.07618, §6.4). -/
noncomputable def labelCsD : Subgroup (GL (Fin 2) (ZMod p)) :=
  diagonalTorus (ZMod p) 2 ⊓ labelGD p d

/-- The group `ℓCn[d] = ℓCn ∩ ℓG[d]` (arXiv:1504.07618, §6.4). -/
noncomputable def labelCnD : Subgroup (GL (Fin 2) (ZMod p)) :=
  labelCn p ⊓ labelGD p d

/-- The group `ℓNs[d] = ℓNs ∩ ℓG[d]` (arXiv:1504.07618, §6.4). -/
noncomputable def labelNsD : Subgroup (GL (Fin 2) (ZMod p)) :=
  labelNs p ⊓ labelGD p d

/-- The group `ℓNn[d] = ℓNn ∩ ℓG[d]` (arXiv:1504.07618, §6.4). -/
noncomputable def labelNnD : Subgroup (GL (Fin 2) (ZMod p)) :=
  labelNn p ⊓ labelGD p d

/-- The group `ℓB.a.b[d]` (arXiv:1504.07618, §6.4): the subgroup of `GL₂(𝔽_p)` generated by
`!![a, 0; 0, 1/a]`, `!![b, 0; 0, r/b]` and `!![1, 1; 0, 1]`, where `r = ZMod.leastGenOfIndex p d`
is the least positive integer generating the subgroup of index `d` of `𝔽_pˣ`. -/
noncomputable def labelBABD : Subgroup (GL (Fin 2) (ZMod p)) :=
  Subgroup.closure (Units.val ⁻¹' {!![(a : ZMod p), 0; 0, (a : ZMod p)⁻¹],
    !![(b : ZMod p), 0; 0, (ZMod.leastGenOfIndex p d : ZMod p) / b], !![1, 1; 0, 1]})

/-- The group `ℓCs.a.b[d]` (arXiv:1504.07618, §6.4): the subgroup of `GL₂(𝔽_p)` generated by
`!![a, 0; 0, 1/a]` and `!![b, 0; 0, r/b]`, `r = ZMod.leastGenOfIndex p d`. -/
noncomputable def labelCsABD : Subgroup (GL (Fin 2) (ZMod p)) :=
  Subgroup.closure (Units.val ⁻¹' {!![(a : ZMod p), 0; 0, (a : ZMod p)⁻¹],
    !![(b : ZMod p), 0; 0, (ZMod.leastGenOfIndex p d : ZMod p) / b]})

/-- The group `ℓNs.a.b[d]` (arXiv:1504.07618, §6.4): the subgroup of `GL₂(𝔽_p)` generated by
`!![a, 0; 0, 1/a]` and `!![0, b; -r/b, 0]`, `r = ZMod.leastGenOfIndex p d`. -/
noncomputable def labelNsABD : Subgroup (GL (Fin 2) (ZMod p)) :=
  Subgroup.closure (Units.val ⁻¹' {!![(a : ZMod p), 0; 0, (a : ZMod p)⁻¹],
    !![0, (b : ZMod p); -((ZMod.leastGenOfIndex p d : ZMod p) / b), 0]})

/-- The group `ℓNs.a.b.c[d]` (arXiv:1504.07618, §6.4): the subgroup of `GL₂(𝔽_p)` generated by
`!![a, 0; 0, 1/a]`, `!![0, b; -1/b, 0]` and `!![0, c; -r/c, 0]`, `r = ZMod.leastGenOfIndex p d`. -/
noncomputable def labelNsABCD : Subgroup (GL (Fin 2) (ZMod p)) :=
  Subgroup.closure (Units.val ⁻¹' {!![(a : ZMod p), 0; 0, (a : ZMod p)⁻¹],
    !![0, (b : ZMod p); -(b : ZMod p)⁻¹, 0],
    !![0, (c : ZMod p); -((ZMod.leastGenOfIndex p d : ZMod p) / c), 0]})

/-- The group `ℓNn.a.b.c[d]` (arXiv:1504.07618, §6.4), for a generator `δ` of `C_ns = labelCn p`:
the subgroup of `GL₂(𝔽_p)` generated by `!![a, ε * b; b, a]` and `!![1, 0; 0, -1] * δ ^ c`, where
`ε` is the least primitive root modulo `p`. -/
noncomputable def labelNnABC (δ : GL (Fin 2) (ZMod p)) : Subgroup (GL (Fin 2) (ZMod p)) :=
  Subgroup.closure (Units.val ⁻¹'
    {!![(a : ZMod p), (ZMod.leastPrimitiveRoot p : ZMod p) * b; (b : ZMod p), a]}) ⊔
    Subgroup.zpowers (diagGL ![1, -1] * δ ^ c)

/-- A generator of the cyclic group `C_ns = labelCn p ≅ 𝔽_{p²}ˣ` (`zpowers_nonsplitCartanGen`),
chosen by `Classical.epsilon`; Sutherland's `ℓNn.a.b.c[d]` may use any generator. -/
noncomputable def nonsplitCartanGen : GL (Fin 2) (ZMod p) :=
  Classical.epsilon fun δ : GL (Fin 2) (ZMod p) ↦ Subgroup.zpowers δ = labelCn p

lemma isCyclic_labelCn : IsCyclic (labelCn p) := by
  have : Finite (NonsplitCartanAlgebra p) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm
  exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

lemma zpowers_nonsplitCartanGen : Subgroup.zpowers (nonsplitCartanGen p) = labelCn p := by
  rcases (isCyclic_labelCn p).exists_generator with ⟨g, hg⟩
  refine Classical.epsilon_spec (p := fun δ : GL (Fin 2) (ZMod p) ↦ Subgroup.zpowers δ = labelCn p)
    ⟨(g : GL (Fin 2) (ZMod p)), ?_⟩
  have h :
      (Subgroup.zpowers g).map (labelCn p).subtype = Subgroup.zpowers (g : GL (Fin 2) (ZMod p)) :=
    MonoidHom.map_zpowers _ _
  rw [← h, (Subgroup.eq_top_iff' _).mpr hg, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- The index `[det G : det Z(G)]` of the determinant of the scalar subgroup `Z(G) = G ∩ Z(ℓ)` in
that of `G` (arXiv:1504.07618, §6.4), recorded by the labels of classes `A4`, `S4`, `A5`. -/
noncomputable def detCenterIndex : ℕ :=
  ((H ⊓ Subgroup.center _).map GeneralLinearGroup.det).relIndex (H.map GeneralLinearGroup.det)

/-- `diag(a, 1/a)` generates the determinant-one part of the diagonal subgroup of `K`: the order of
`a` modulo `p` is the order of `K ∩ C_s ∩ SL₂(𝔽_p)`. This is how Sutherland's tables and script
choose the integer `a` of `B.a.b[d]`, `Cs.a.b[d]`, `Ns.a.b[d]`, `Ns.a.b.c[d]`
(arXiv:1504.07618, §6.4 and [68]). -/
def IsDetOneDiagGen (K : Subgroup (GL (Fin 2) (ZMod p))) : Prop :=
  orderOf (a : ZMod p) = Nat.card ↥(K ⊓ diagonalTorus (ZMod p) 2 ⊓ GeneralLinearGroup.det.ker)

/-- The determinants of the elements of `K` in `C_ns = labelCn p` and the negatives of the
determinants of the elements of `K` outside `C_ns` form disjoint sets: the case of Sutherland's
Corollary 3.17 (arXiv:1504.07618) in which his labels take the form `ℓNn.a.b.c[d]`, as his script
[68] decides; otherwise they take the form `ℓNn.a.b[d]`. -/
def IsNnDetDisjoint (K : Subgroup (GL (Fin 2) (ZMod p))) : Prop :=
  ∀ x ∈ K, x ∉ labelCn p → -GeneralLinearGroup.det x ∉ (K ⊓ labelCn p).map GeneralLinearGroup.det

/-- `(a, b)` is the lexicographically least pair of natural numbers satisfying `P`. -/
def IsLexLeastPair (P : ℕ → ℕ → Prop) : Prop :=
  P a b ∧ ∀ a' b' : ℕ, P a' b' → toLex (a, b) ≤ toLex (a', b')

/-- `(a, b, c)` is the lexicographically least triple of natural numbers satisfying `P`. -/
def IsLexLeastTriple (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  P a b c ∧ ∀ a' b' c' : ℕ, P a' b' c' → toLex (a, toLex (b, c)) ≤ toLex (a', toLex (b', c'))

/-- **Sutherland's label** `ℓS.a.b.c[d]` of a subgroup of `GL₂(𝔽_ℓ)` (arXiv:1504.07618, §6.4; LMFDB
`ec.galois_rep_modell_image`), without the prime `ℓ`: the class `S`, the list of the integers `a`,
`b`, `c` it has (none, one, two or three) and the index `d`. -/
@[ext]
structure SutherlandGroupLabel where
  /-- The class `S`. -/
  cls : SutherlandClass
  /-- The integers `a`, `b`, `c` of the label, as many as it has. -/
  params : List ℕ
  /-- The index `d` of the determinant of the group in `𝔽_ℓˣ` (the suffix `[d]`, omitted when
  `d = 1`). -/
  d : ℕ

variable (L : SutherlandGroupLabel)

/-- The subgroup of `GL₂(𝔽_p)` that a label of class `G`, `B`, `Cs`, `Cn`, `Ns` or `Nn` names by
Sutherland's generators (arXiv:1504.07618, §6.4): `ℓS[d]` is `ℓS ∩ ℓG[d]`, and `ℓS.a.b[d]`,
`ℓS.a.b.c[d]` are the groups `labelBABD`, `labelCsABD`, `labelCnAB`, `labelNsABD`, `labelNsABCD`,
`labelNnAB`, `labelNnABC` (the last with the generator `nonsplitCartanGen`). It is `none` for the
classes `A4`, `S4`, `A5`, whose labels record invariants (Sutherland's Algorithm 1 constructs a
group from them), and for lists of integers of a length the class does not use. -/
noncomputable def SutherlandGroupLabel.namedSubgroup : Option (Subgroup (GL (Fin 2) (ZMod p))) :=
  match L.cls, L.params with
  | .G, [] => some (labelGD p L.d)
  | .B, [] => some (labelBD p L.d)
  | .B, [a, b] => some (labelBABD p L.d a b)
  | .Cs, [] => some (labelCsD p L.d)
  | .Cs, [a, b] => some (labelCsABD p L.d a b)
  | .Cn, [] => some (labelCnD p L.d)
  | .Cn, [a, b] => some (labelCnAB p a b)
  | .Ns, [] => some (labelNsD p L.d)
  | .Ns, [a, b] => some (labelNsABD p L.d a b)
  | .Ns, [a, b, c] => some (labelNsABCD p L.d a b c)
  | .Nn, [] => some (labelNnD p L.d)
  | .Nn, [a, b] => some (labelNnAB p a b)
  | .Nn, [a, b, c] => some (labelNnABC p a b c (nonsplitCartanGen p))
  | _, _ => none

/-- Sutherland's conditions on the integers `a`, `b`, `c` of the label `L` of a subgroup `H` of
`GL₂(𝔽_p)` (arXiv:1504.07618, §6.4), besides `H` being conjugate to the group `L` names. A label
`ℓS.a.b[d]` or `ℓS.a.b.c[d]` is used when `H` is not conjugate to `ℓS[d]`, with `a, b, c > 0`
minimal for `B`, `Cs`, `Ns` (lexicographically, `a` making `diag(a, 1/a)` generate the
determinant-one diagonal part, as in Sutherland's tables), with `b > 0`, `a ≥ 0` and `(a, b)`
lexicographically minimal for `Cn` and `Nn`, and with `c = [Z(ℓ) : H ∩ Z(ℓ)]`, `δ` any generator
of `C_ns` and `!![a, ε * b; b, a]` generating the part in `C_ns`, which contains `H ∩ Z(ℓ)`, for
`Nn.a.b.c` (as in Corollary 3.17 and Sutherland's script). The text leaves implicit which of the
two forms of `Ns` and `Nn` labels applies when both name a conjugate of `H`; as in Sutherland's
script, `ℓNs.a.b[d]` is used when the determinant-one part of the group lies in `C_s` and
`ℓNs.a.b.c[d]` otherwise (which also excludes `b ≡ 0 mod ℓ`, where the second generator is not
invertible), and `ℓNn.a.b.c[d]` exactly in the case `IsNnDetDisjoint` of Corollary 3.17. For `A4`,
`ℓA4.a[d]` records `a = [det H : det Z(H)]`; `ℓS4` is used when `Z(H) = Z(ℓ)` and `d = 1`,
`ℓS4[d]` when `d > 1` and `[det H : det Z(H)] = 2`, and `ℓS4.1[d]` when this index is `1`; and
`ℓA5.1[d]` when it is `1` (the paper's text writes `ℓA5.[d]`, its tables, e.g. `11A5.1[2]`, and
Sutherland's script `ℓA5.1[d]`). -/
def SutherlandGroupLabel.ParamsOf : Prop :=
  match L.cls, L.params with
  | .G, [] => True
  | .B, [] => True
  | .B, [a, b] => labelBD p L.d ∉ subgroupConjClass p H ∧ IsLexLeastPair a b fun a b ↦ 0 < a ∧
      0 < b ∧ IsDetOneDiagGen p a (labelBABD p L.d a b) ∧
        labelBABD p L.d a b ∈ subgroupConjClass p H
  | .Cs, [] => True
  | .Cs, [a, b] => labelCsD p L.d ∉ subgroupConjClass p H ∧ IsLexLeastPair a b fun a b ↦ 0 < a ∧
      0 < b ∧ IsDetOneDiagGen p a (labelCsABD p L.d a b) ∧
        labelCsABD p L.d a b ∈ subgroupConjClass p H
  | .Cn, [] => True
  | .Cn, [a, b] => labelCnD p L.d ∉ subgroupConjClass p H ∧
      IsLexLeastPair a b fun a b ↦ 0 < b ∧ labelCnAB p a b ∈ subgroupConjClass p H
  | .Ns, [] => True
  | .Ns, [a, b] => labelNsD p L.d ∉ subgroupConjClass p H ∧ IsLexLeastPair a b fun a b ↦ 0 < a ∧
      0 < b ∧ IsDetOneDiagGen p a (labelNsABD p L.d a b) ∧
        labelNsABD p L.d a b ⊓ GeneralLinearGroup.det.ker ≤ diagonalTorus (ZMod p) 2 ∧
          labelNsABD p L.d a b ∈ subgroupConjClass p H
  | .Ns, [a, b, c] => labelNsD p L.d ∉ subgroupConjClass p H ∧ IsLexLeastTriple a b c
      fun a b c ↦ 0 < a ∧ 0 < b ∧ 0 < c ∧ IsDetOneDiagGen p a (labelNsABCD p L.d a b c) ∧
        ¬labelNsABCD p L.d a b c ⊓ GeneralLinearGroup.det.ker ≤ diagonalTorus (ZMod p) 2 ∧
          labelNsABCD p L.d a b c ∈ subgroupConjClass p H
  | .Nn, [] => True
  | .Nn, [a, b] => labelNnD p L.d ∉ subgroupConjClass p H ∧
      IsLexLeastPair a b fun a b ↦ 0 < b ∧ labelNnAB p a b ∈ subgroupConjClass p H
  | .Nn, [a, b, c] => labelNnD p L.d ∉ subgroupConjClass p H ∧
      c = (H ⊓ Subgroup.center _).relIndex (Subgroup.center _) ∧
      IsLexLeastPair a b fun a b ↦ 0 < b ∧ H ⊓ Subgroup.center _ ≤ labelCnAB p a b ∧
        ∀ δ : GL (Fin 2) (ZMod p), Subgroup.zpowers δ = labelCn p →
          IsNnDetDisjoint p (labelNnABC p a b c δ) ∧ labelNnABC p a b c δ ∈ subgroupConjClass p H
  | .A4, [a] => a = detCenterIndex p H
  | .S4, [] => L.d = 1 ∧ H ⊓ Subgroup.center _ = Subgroup.center _ ∨
      1 < L.d ∧ detCenterIndex p H = 2
  | .S4, [a] => a = 1 ∧ detCenterIndex p H = 1
  | .A5, [a] => a = 1 ∧ detCenterIndex p H = 1
  | _, _ => False

/-- `L` is **Sutherland's label** `ℓS.a.b.c[d]` of the subgroup `H` of `GL₂(𝔽_p)`
(arXiv:1504.07618, §6.4; LMFDB `ec.galois_rep_modell_image`): `H` has class `S`, `d` is the index
of `det H` in `𝔽_pˣ`, `H` is conjugate to the group the label names (classes `G`, `B`, `Cs`, `Cn`,
`Ns`, `Nn`), and the integers `a`, `b`, `c` satisfy Sutherland's conditions
(`SutherlandGroupLabel.ParamsOf`). -/
def IsSutherlandLabel : Prop :=
  HasSutherlandClass p H L.cls ∧ L.d = (H.map GeneralLinearGroup.det).index ∧
    (∀ K ∈ L.namedSubgroup p, K ∈ subgroupConjClass p H) ∧ L.ParamsOf p H

variable {p H} (g : ConjAct (GL (Fin 2) (ZMod p)))

lemma map_det_smul : (g • H).map GeneralLinearGroup.det = H.map GeneralLinearGroup.det := by
  ext u
  simp only [Subgroup.mem_map]
  refine ⟨fun ⟨x, hx, hxu⟩ ↦ ⟨g⁻¹ • x, Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx, ?_⟩,
    fun ⟨x, hx, hxu⟩ ↦ ⟨g • x, Subgroup.smul_mem_pointwise_smul x g H hx, ?_⟩⟩ <;>
    simp [ConjAct.smul_def, hxu]

lemma smul_inf_center : g • H ⊓ Subgroup.center _ = H ⊓ Subgroup.center _ := by
  ext x
  simp only [Subgroup.mem_inf, and_congr_left_iff]
  intro hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, Subgroup.mem_center_iff.mp hx,
    mul_inv_cancel_right]

lemma SutherlandClass.holds_smul_iff (S : SutherlandClass) : S.Holds p (g • H) ↔ S.Holds p H := by
  cases S <;> simp only [SutherlandClass.Holds, orbit_smul]

lemma hasSutherlandClass_smul_iff (S : SutherlandClass) :
    HasSutherlandClass p (g • H) S ↔ HasSutherlandClass p H S := by
  simp only [HasSutherlandClass, SutherlandClass.holds_smul_iff]

lemma SutherlandGroupLabel.paramsOf_smul_iff : L.ParamsOf p (g • H) ↔ L.ParamsOf p H := by
  simp only [SutherlandGroupLabel.ParamsOf, detCenterIndex, orbit_smul, smul_inf_center,
    map_det_smul]

/-- **Sutherland's label is a conjugacy invariant**: a subgroup of `GL₂(𝔽_p)` and its conjugates
have the same labels. -/
lemma isSutherlandLabel_smul_iff : IsSutherlandLabel p (g • H) L ↔ IsSutherlandLabel p H L := by
  rw [IsSutherlandLabel, IsSutherlandLabel, hasSutherlandClass_smul_iff, map_det_smul,
    L.paramsOf_smul_iff, subgroupConjClass, orbit_smul]

lemma map_conj_eq_smul (P : GL (Fin 2) (ZMod p)) :
    H.map (MulAut.conj P).toMonoidHom = ConjAct.toConjAct P • H := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    MulAut.conj_symm_apply, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]

lemma isSutherlandLabel_map_conj_iff (P : GL (Fin 2) (ZMod p)) :
    IsSutherlandLabel p (H.map (MulAut.conj P).toMonoidHom) L ↔ IsSutherlandLabel p H L := by
  rw [map_conj_eq_smul, isSutherlandLabel_smul_iff]

variable {L} {L' : SutherlandGroupLabel}

/-- **Two subgroups of `GL₂(𝔽_p)` with the same Sutherland label are conjugate** whenever the label
names a subgroup, as every label of class `G`, `B`, `Cs`, `Cn`, `Ns` or `Nn` does
(`IsSutherlandLabel.exists_mem_namedSubgroup`). -/
lemma IsSutherlandLabel.mem_subgroupConjClass {K N : Subgroup (GL (Fin 2) (ZMod p))}
    (hH : IsSutherlandLabel p H L) (hK : IsSutherlandLabel p K L) (hN : N ∈ L.namedSubgroup p) :
    K ∈ subgroupConjClass p H :=
  orbit_eq_iff.mp <|
    (orbit_eq_iff.mpr (hK.2.2.1 N hN)).symm.trans (orbit_eq_iff.mpr (hH.2.2.1 N hN))

/-- **A Sutherland label of class `G`, `B`, `Cs`, `Cn`, `Ns` or `Nn` names a subgroup.** -/
lemma IsSutherlandLabel.exists_mem_namedSubgroup (hH : IsSutherlandLabel p H L)
    (hS : L.cls.toNat < 6) : ∃ N, N ∈ L.namedSubgroup p := by
  rcases L with ⟨S, ps, d⟩
  rcases hH with ⟨-, -, -, h⟩
  cases S <;> rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, ps⟩⟩⟩⟩ <;>
    simp_all [SutherlandGroupLabel.ParamsOf, SutherlandGroupLabel.namedSubgroup,
      SutherlandClass.toNat]

/-- **The class of Sutherland's label of a subgroup of `GL₂(𝔽_p)` is unique.** -/
lemma IsSutherlandLabel.cls_eq (hL : IsSutherlandLabel p H L) (hL' : IsSutherlandLabel p H L') :
    L.cls = L'.cls := by
  rcases lt_trichotomy L.cls.toNat L'.cls.toNat with h | h | h
  · exact absurd hL.1.1 (hL'.1.2 _ h)
  · exact SutherlandClass.toNat_injective h
  · exact absurd hL'.1.1 (hL.1.2 _ h)

variable {a b} in
lemma IsLexLeastPair.eq {P : ℕ → ℕ → Prop} {a' b' : ℕ} (h : IsLexLeastPair a b P)
    (h' : IsLexLeastPair a' b' P) : (a, b) = (a', b') :=
  toLex.injective <| le_antisymm (h.2 a' b' h'.1) (h'.2 a b h.1)

variable {a b c} in
lemma IsLexLeastTriple.eq {P : ℕ → ℕ → ℕ → Prop} {a' b' c' : ℕ} (h : IsLexLeastTriple a b c P)
    (h' : IsLexLeastTriple a' b' c' P) : (a, b, c) = (a', b', c') := by
  simpa using le_antisymm (h.2 a' b' c' h'.1) (h'.2 a b c h.1)

lemma exists_isLexLeastPair {P : ℕ → ℕ → Prop} (h : ∃ a b, P a b) :
    ∃ a b, IsLexLeastPair a b P := by
  rcases h with ⟨a₀, b₀, h₀⟩
  let s : Set (ℕ ×ₗ ℕ) := {x | P (ofLex x).1 (ofLex x).2}
  have hs : s.Nonempty := ⟨toLex (a₀, b₀), h₀⟩
  exact ⟨(ofLex (wellFounded_lt.min s hs)).1, (ofLex (wellFounded_lt.min s hs)).2,
    wellFounded_lt.min_mem s hs, fun a' b' h' ↦
      not_lt.mp (wellFounded_lt.not_lt_min s (x := toLex (a', b')) h')⟩

/-- **Sutherland's label of a subgroup of `GL₂(𝔽_p)` is unique given its number of integers** `a`,
`b`, `c`. Labels of a subgroup with different numbers of integers could only be its `Ns.a.b[d]` and
`Ns.a.b.c[d]`, or its `Nn.a.b[d]` and `Nn.a.b.c[d]` (`IsSutherlandLabel.eq`). The conditions taken
from Sutherland's script (`SutherlandGroupLabel.ParamsOf`) are meant to separate these forms, by his
Lemma 3.16 and Corollaries 3.17 and 3.18; this is not proved here. -/
lemma IsSutherlandLabel.eq_of_length_eq (hL : IsSutherlandLabel p H L)
    (hL' : IsSutherlandLabel p H L') (hlen : L.params.length = L'.params.length) : L = L' := by
  have hcls : L.cls = L'.cls := hL.cls_eq hL'
  have hd : L.d = L'.d := hL.2.1.trans hL'.2.1.symm
  have h : L.ParamsOf p H := hL.2.2.2
  have h' : L'.ParamsOf p H := hL'.2.2.2
  rcases L with ⟨S, ps, d⟩
  rcases L' with ⟨S', ps', d'⟩
  dsimp only at hcls hd hlen
  subst hcls hd
  refine SutherlandGroupLabel.ext rfl ?_ rfl
  clear hL hL'
  cases S <;> rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, ps⟩⟩⟩⟩ <;>
    rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', ps'⟩⟩⟩⟩ <;> try simp at hlen
  all_goals simp only [SutherlandGroupLabel.ParamsOf] at h h'
  all_goals first
    | rfl
    | rcases h.trans h'.symm with rfl; rfl
    | rcases h.1.trans h'.1.symm with rfl; rfl
    | rcases h.2.eq h'.2 with ⟨⟩; rfl
    | rcases h.2.1.trans h'.2.1.symm with rfl
      rcases h.2.2.eq h'.2.2 with ⟨⟩
      rfl

variable {d a} in
lemma IsSutherlandLabel.false_of_S4 (hL : IsSutherlandLabel p H ⟨.S4, [], d⟩)
    (hL' : IsSutherlandLabel p H ⟨.S4, [a], d⟩) : False := by
  have h : SutherlandGroupLabel.ParamsOf p H ⟨.S4, [], d⟩ := hL.2.2.2
  have h' : SutherlandGroupLabel.ParamsOf p H ⟨.S4, [a], d⟩ := hL'.2.2.2
  simp only [SutherlandGroupLabel.ParamsOf] at h h'
  rcases h with ⟨hd, hZ⟩ | ⟨-, h₂⟩
  · have htop : H.map GeneralLinearGroup.det = ⊤ := Subgroup.index_eq_one.mp (hL.2.1.symm.trans hd)
    rw [detCenterIndex, hZ, htop, Subgroup.relIndex_top_right, Subgroup.index_eq_one] at h'
    rcases hL.1.1 with ⟨K, -, ⟨e⟩, -⟩
    rcases eq_or_ne p 2 with rfl | hp
    · have h₆ : Nat.card (projectiveImage K) ≤ 6 :=
        (Nat.le_of_dvd Nat.card_pos (K.card_map_dvd ProjGenLinGroup.mk)).trans <|
          K.card_le_card_group.trans_eq <| by
            rw [card_GL_field, Fin.prod_univ_two, ZMod.card]
            rfl
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin] at h₆
      exact absurd h₆ (by decide)
    rcases quadraticChar_exists_neg_one' (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) with ⟨u, hu⟩
    rcases (h'.2 ▸ Subgroup.mem_top u : u ∈ (Subgroup.center _).map GeneralLinearGroup.det) with
      ⟨z, hz, rfl⟩
    rw [center_eq_range_scalar] at hz
    rcases hz with ⟨v, rfl⟩
    rw [det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val, quadraticChar_sq_one' v.ne_zero]
      at hu
    exact absurd hu (by decide)
  · exact absurd (h₂.symm.trans h'.2) (by decide)

/-- **Sutherland's label of a subgroup of `GL₂(𝔽_p)` of class other than `Ns` and `Nn` is
unique**; for these two classes it is unique given its number of integers
(`IsSutherlandLabel.eq_of_length_eq`). -/
lemma IsSutherlandLabel.eq (hL : IsSutherlandLabel p H L) (hL' : IsSutherlandLabel p H L')
    (hNs : L.cls ≠ .Ns) (hNn : L.cls ≠ .Nn) : L = L' := by
  by_cases hlen : L.params.length = L'.params.length
  · exact hL.eq_of_length_eq hL' hlen
  have hcls : L.cls = L'.cls := hL.cls_eq hL'
  have hd : L.d = L'.d := hL.2.1.trans hL'.2.1.symm
  rcases L with ⟨S, ps, d⟩
  rcases L' with ⟨S', ps', d'⟩
  dsimp only at hcls hd hlen hNs hNn
  subst hcls hd
  have h : SutherlandGroupLabel.ParamsOf p H ⟨S, ps, d⟩ := hL.2.2.2
  have h' : SutherlandGroupLabel.ParamsOf p H ⟨S, ps', d⟩ := hL'.2.2.2
  cases S <;> rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, ps⟩⟩⟩⟩ <;>
    rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', ps'⟩⟩⟩⟩ <;> try simp at hlen
  all_goals simp only [SutherlandGroupLabel.ParamsOf] at h h'
  all_goals first
    | exact absurd rfl hNs
    | exact absurd rfl hNn
    | exact absurd (hL.2.2.1 _ rfl) h'.1
    | exact absurd (hL'.2.2.1 _ rfl) h.1
    | exact (hL.false_of_S4 hL').elim
    | exact (hL'.false_of_S4 hL).elim

/-- **A subgroup of `GL₂(𝔽_p)` has a label of class `G` exactly when it contains `SL₂(𝔽_p)`**
(arXiv:1504.07618, §6.4): the classes of the subgroups not containing `SL₂(𝔽_p)` are `B`, `Cs`,
`Cn`, `Ns`, `Nn`, `A4`, `S4`, `A5`, as LMFDB `ec.galois_rep_modell_image` says. -/
lemma IsSutherlandLabel.cls_eq_G_iff (hL : IsSutherlandLabel p H L) :
    L.cls = .G ↔ GeneralLinearGroup.det.ker ≤ H := by
  refine ⟨fun h ↦ ?_, fun h ↦ by_contra fun hne ↦ hL.1.2 .G
    (Nat.pos_of_ne_zero fun h₀ ↦ hne (SutherlandClass.toNat_injective h₀))
    ⟨H, mem_orbit_self H, h⟩⟩
  have hH : SutherlandClass.Holds p H .G := h ▸ hL.1.1
  rcases hH with ⟨K, ⟨g, rfl⟩, hK⟩
  rwa [← (GeneralLinearGroup.det.normal_ker).conjAct g,
    Subgroup.pointwise_smul_le_pointwise_smul_iff] at hK

/-- **A subgroup of `GL₂(𝔽_p)` with surjective determinant has no label of class `A4` or `A5`**
(LMFDB `ec.galois_rep_modell_image`: "the cases A4 and A5 cannot occur when K = ℚ"): an exceptional
class is then `S4`. -/
lemma IsSutherlandLabel.cls_eq_S4 (hL : IsSutherlandLabel p H L)
    (hdet : H.map GeneralLinearGroup.det = ⊤) (h : 6 ≤ L.cls.toNat) : L.cls = .S4 := by
  have hH : L.cls.Holds p H := hL.1.1
  rcases hc : L.cls <;> rw [hc] at hH h <;> try exact absurd h (by decide)
  all_goals
    rcases hH with ⟨K, ⟨g, rfl⟩, hK, -⟩
    exact nomatch eq_S4_of_hasExceptionalType (by rw [map_det_smul, hdet]) hK

/-- **A label of class `A4` or `A5` has `d > 1`**, as Sutherland states (arXiv:1504.07618, §6.4:
"This requires d > 1"). -/
lemma IsSutherlandLabel.one_lt_d (hL : IsSutherlandLabel p H L) (h : 6 ≤ L.cls.toNat)
    (hS : L.cls ≠ .S4) : 1 < L.d := by
  rw [hL.2.1]
  exact lt_of_le_of_ne (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) fun h₁ ↦
    hS (hL.cls_eq_S4 (Subgroup.index_eq_one.mp h₁.symm) h)

lemma labelGD_index_map_det (hH : GeneralLinearGroup.det.ker ≤ H) :
    labelGD p (H.map GeneralLinearGroup.det).index = H := by
  refine (congrArg (Subgroup.comap _) ?_).trans (Subgroup.comap_map_eq_self hH)
  rw [IsCyclic.subgroup_eq_iff_index_eq, IsCyclic.index_powMonoidHom_range,
    Nat.gcd_eq_right (Subgroup.index_dvd_card _)]

/-- **A subgroup of `GL₂(𝔽_p)` containing `SL₂(𝔽_p)` has Sutherland's label `ℓG[d]`**, `d` the index
of its determinant in `𝔽_pˣ` (arXiv:1504.07618, §6.4). -/
lemma isSutherlandLabel_G (hH : GeneralLinearGroup.det.ker ≤ H) :
    IsSutherlandLabel p H ⟨.G, [], (H.map GeneralLinearGroup.det).index⟩ := by
  refine ⟨⟨⟨H, mem_orbit_self H, hH⟩, fun T hT ↦ absurd hT (Nat.not_lt_zero _)⟩, rfl,
    fun K hK ↦ ?_, trivial⟩
  rw [Option.mem_def, SutherlandGroupLabel.namedSubgroup, Option.some_inj,
    labelGD_index_map_det hH] at hK
  exact hK ▸ mem_orbit_self H

lemma exists_isSutherlandLabel_of_le_labelCn (hp : p ≠ 2) (hK : H ≤ labelCn p)
    (hS : HasSutherlandClass p H .Cn) : ∃ L : SutherlandGroupLabel, IsSutherlandLabel p H L := by
  by_cases hfull : labelCnD p (H.map GeneralLinearGroup.det).index ∈ subgroupConjClass p H
  · refine ⟨⟨.Cn, [], _⟩, hS, rfl, fun N hN ↦ ?_, trivial⟩
    rw [Option.mem_def, SutherlandGroupLabel.namedSubgroup, Option.some_inj] at hN
    exact hN ▸ hfull
  have : IsCyclic (labelCn p) := isCyclic_labelCn p
  have : IsCyclic H := Subgroup.isCyclic_of_le hK
  rcases IsCyclic.exists_generator (α := H) with ⟨g, hg⟩
  have hgH : Subgroup.zpowers (g : GL (Fin 2) (ZMod p)) = H := by
    have h : (Subgroup.zpowers g).map H.subtype = Subgroup.zpowers (g : GL (Fin 2) (ZMod p)) :=
      MonoidHom.map_zpowers _ _
    rw [← h, (Subgroup.eq_top_iff' _).mpr hg, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hgCn : (g : GL (Fin 2) (ZMod p)) 1 1 = (g : GL (Fin 2) (ZMod p)) 0 0 ∧
      (g : GL (Fin 2) (ZMod p)) 0 1 =
        (ZMod.leastPrimitiveRoot p : ZMod p) * (g : GL (Fin 2) (ZMod p)) 1 0 :=
    (mem_labelCn_iff p hp).mp (hK g.2)
  have hy : (g : GL (Fin 2) (ZMod p)) 1 0 ≠ 0 := by
    intro hy
    refine hS.1.2 ⟨H, mem_orbit_self H, ?_⟩
    rw [← hgH, Subgroup.zpowers_le]
    exact mem_diagonalTorus_of_fin_two (ZMod p) (by rw [hgCn.2, hy, mul_zero]) hy
  have hw : labelCnAB p ((g : GL (Fin 2) (ZMod p)) 0 0).val ((g : GL (Fin 2) (ZMod p)) 1 0).val ∈
      subgroupConjClass p H := by
    rw [labelCnAB, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hmat : !![(g : GL (Fin 2) (ZMod p)) 0 0,
        (ZMod.leastPrimitiveRoot p : ZMod p) * (g : GL (Fin 2) (ZMod p)) 1 0;
        (g : GL (Fin 2) (ZMod p)) 1 0, (g : GL (Fin 2) (ZMod p)) 0 0] =
        ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hgCn.1, hgCn.2]
    rw [hmat, ← Set.image_singleton, Set.preimage_image_eq _ Units.val_injective,
      ← Subgroup.zpowers_eq_closure, hgH]
    exact mem_orbit_self H
  rcases exists_isLexLeastPair (P := fun a b ↦ 0 < b ∧ labelCnAB p a b ∈ subgroupConjClass p H)
    ⟨_, _, ZMod.val_pos.mpr hy, hw⟩ with ⟨a, b, hab⟩
  refine ⟨⟨.Cn, [a, b], _⟩, hS, rfl, fun N hN ↦ ?_, hfull, hab⟩
  rw [Option.mem_def, SutherlandGroupLabel.namedSubgroup, Option.some_inj] at hN
  exact hN ▸ hab.1.2

/-- **Every subgroup of `GL₂(𝔽_p)` of class `Cn` has a Sutherland label**, for odd `p`
(arXiv:1504.07618, §6.4): `ℓCn[d]` or `ℓCn.a.b[d]`, a generator `!![a, ε * b; b, a]` of a conjugate
in `C_ns` giving a pair `(a, b)` and hence a lexicographically least one. -/
lemma exists_isSutherlandLabel_of_hasSutherlandClass_Cn (hp : p ≠ 2)
    (hH : HasSutherlandClass p H .Cn) : ∃ L : SutherlandGroupLabel, IsSutherlandLabel p H L := by
  rcases hH.1.1 with ⟨K, hK, hKCn⟩
  rcases MulAction.mem_orbit_iff.mp hK with ⟨g, rfl⟩
  rcases exists_isSutherlandLabel_of_le_labelCn hp hKCn
    ((hasSutherlandClass_smul_iff g .Cn).mpr hH) with ⟨L, hL⟩
  exact ⟨L, (isSutherlandLabel_smul_iff L g).mp hL⟩

variable (p)

lemma labelGD_one : labelGD p 1 = ⊤ := by
  ext x
  simp [labelGD]

/-- **With `d = 1`, Sutherland's group `ℓB.a.b[d]` is the LMFDB's `B.a.b`** (`labelBAB`, LMFDB
`gl2.borel`), as are `ℓCs.a.b[1]`, `ℓNs.a.b[1]` and `ℓNs.a.b.c[1]` the LMFDB's `Cs.a.b`, `Ns.a.b`
and `Ns.a.b.c`. -/
lemma labelBABD_one : labelBABD p 1 a b = labelBAB p a b := by
  rw [labelBABD, ZMod.leastGenOfIndex_one, labelBAB]

lemma labelCsABD_one : labelCsABD p 1 a b = labelCsAB p a b := by
  rw [labelCsABD, ZMod.leastGenOfIndex_one, labelCsAB]

lemma labelNsABD_one : labelNsABD p 1 a b = labelNsAB p a b := by
  rw [labelNsABD, ZMod.leastGenOfIndex_one, labelNsAB]

lemma labelNsABCD_one : labelNsABCD p 1 a b c = labelNsABC p a b c := by
  rw [labelNsABCD, ZMod.leastGenOfIndex_one, labelNsABC]

/-- **Test against Sutherland's Table 3**: the subgroup `C_ns(2)` of index `2` of `GL₂(𝔽₂)`, listed
there as the mod-`2` image `2Cn` of the curve `[0, -1, 0, -2, 1]`, has the label `2Cn`. -/
lemma isSutherlandLabel_labelCn_two : IsSutherlandLabel 2 (labelCn 2) ⟨.Cn, [], 1⟩ := by
  have hunit : ∀ u : (ZMod 2)ˣ, u = 1 := by
    decide
  have hcard (g : ConjAct (GL (Fin 2) (ZMod 2))) : Nat.card ↥(g • labelCn 2) = 3 := by
    rw [← Nat.card_congr (Subgroup.equivSMul g (labelCn 2)).toEquiv]
    exact natCard_labelCn 2
  have hCs (g : ConjAct (GL (Fin 2) (ZMod 2))) : ¬g • labelCn 2 ≤ diagonalTorus (ZMod 2) 2 := by
    intro h
    have h₁ : Nat.card ↥(g • labelCn 2) ≤ Nat.card ↥(diagonalTorus (ZMod 2) 2) :=
      Subgroup.card_le_of_le h
    rw [hcard, ← Nat.card_congr (diagonalTorusEquiv (ZMod 2) 2).toEquiv] at h₁
    simp at h₁
  refine ⟨⟨⟨⟨labelCn 2, mem_orbit_self _, le_rfl⟩, by
    rintro ⟨K, ⟨g, rfl⟩, hK⟩
    exact hCs g hK⟩, fun T hT ↦ ?_⟩, ?_, fun K hK ↦ ?_, trivial⟩
  · cases T
    · rintro ⟨K, ⟨g, rfl⟩, hK⟩
      have hker : GeneralLinearGroup.det.ker = (⊤ : Subgroup (GL (Fin 2) (ZMod 2))) :=
        eq_top_iff.mpr fun x _ ↦ MonoidHom.mem_ker.mpr (hunit _)
      have h₁ : Nat.card ↥(GeneralLinearGroup.det.ker) ≤ Nat.card ↥(g • labelCn 2) :=
        Subgroup.card_le_of_le hK
      rw [hker, Subgroup.card_top, card_GL_field, Fin.prod_univ_two, ZMod.card, hcard] at h₁
      exact absurd h₁ (by decide)
    · rintro ⟨K, ⟨g, rfl⟩, -, x, hx, hxo⟩
      have h₁ : orderOf x ∣ Nat.card ↥(g • labelCn 2) := Subgroup.orderOf_dvd_natCard _ hx
      rw [hxo, hcard] at h₁
      exact absurd h₁ (by decide)
    · rintro ⟨K, ⟨g, rfl⟩, hK⟩
      exact hCs g hK
    all_goals exact absurd hT (by decide)
  · exact (Subgroup.index_eq_one.mpr (eq_top_iff.mpr fun u _ ↦ hunit u ▸ one_mem _)).symm
  · rw [Option.mem_def, SutherlandGroupLabel.namedSubgroup, Option.some_inj, labelCnD, labelGD_one,
      inf_top_eq] at hK
    exact hK ▸ mem_orbit_self _

/-- **Test against Sutherland's Table 3**: the subgroup of `GL₂(𝔽₃)` generated by
`!![1, 0; 0, 2] = diag(1, -1)`, listed there as the mod-`3` image `3Cs.1.1` of the curve
`[1, 0, 1, 4, -6]`, has the label `3Cs.1.1`: the conditions on the integers `a`, `b` are met. -/
lemma isSutherlandLabel_three_Cs_one_one :
    IsSutherlandLabel 3 (Subgroup.zpowers (diagGL ![1, -1])) ⟨.Cs, [1, 1], 1⟩ := by
  have hunit : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by
    decide
  have hs : orderOf (diagGL ![1, -1] : GL (Fin 2) (ZMod 3)) = 2 := by
    refine orderOf_eq_prime ?_ fun h ↦ ?_
    · rw [← map_pow]
      convert map_one (diagGL (k := ZMod 3) (ι := Fin 2))
      funext i
      fin_cases i <;> decide
    · have h₁ : (-1 : ZMod 3) = 1 := by
        simpa using
          congr_arg (fun g : GL (Fin 2) (ZMod 3) ↦ (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1) h
      exact absurd h₁ (by decide)
  have hdet : GeneralLinearGroup.det (diagGL ![1, -1] : GL (Fin 2) (ZMod 3)) = -1 := by
    ext
    simp
  have hcard (g : ConjAct (GL (Fin 2) (ZMod 3))) :
      Nat.card ↥(g • Subgroup.zpowers (diagGL ![1, -1] : GL (Fin 2) (ZMod 3))) = 2 := by
    rw [← Nat.card_congr (Subgroup.equivSMul g _).toEquiv, Nat.card_zpowers, hs]
  have hr : ZMod.leastGenOfIndex 3 1 = 2 :=
    ZMod.leastGenOfIndex_eq 3 1 two_pos ((orderOf_eq_iff two_pos).mpr ⟨by decide, by decide⟩)
      fun s hs₀ hs₂ ↦ by interval_cases s; simp
  have hnamed : labelCsABD 3 1 1 1 = Subgroup.zpowers (diagGL ![1, -1]) := by
    rw [labelCsABD, hr, Subgroup.zpowers_eq_closure]
    simp only [Nat.cast_one, Nat.cast_ofNat, inv_one, div_one]
    have hB : (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        ((diagGL ![1, -1] : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [← Matrix.one_fin_two, hB, ← Units.val_one, ← Set.image_pair,
      Set.preimage_image_eq _ Units.val_injective, Subgroup.closure_insert_one]
  have htor :
      diagonalTorus (ZMod 3) 2 ∉ subgroupConjClass 3 (Subgroup.zpowers (diagGL ![1, -1])) := by
    intro h
    rcases MulAction.mem_orbit_iff.mp h with ⟨g, hg⟩
    have h₁ : Nat.card ↥(diagonalTorus (ZMod 3) 2) = 2 := hg ▸ hcard g
    rw [← Nat.card_congr (diagonalTorusEquiv (ZMod 3) 2).toEquiv, Nat.card_fun,
      Nat.card_eq_fintype_card (α := (ZMod 3)ˣ), ZMod.card_units, Nat.card_fin] at h₁
    exact absurd h₁ (by decide)
  have hbot : Subgroup.zpowers (diagGL ![1, -1] : GL (Fin 2) (ZMod 3)) ⊓ diagonalTorus (ZMod 3) 2 ⊓
      GeneralLinearGroup.det.ker = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hx
    rcases hx with ⟨⟨hx, -⟩, hx₁⟩
    rw [mem_zpowers_iff_mem_range_orderOf, hs] at hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    rcases hx with ⟨i, hi, rfl⟩
    interval_cases i
    · exact Subgroup.mem_bot.mpr (pow_zero _)
    · rw [pow_one, MonoidHom.mem_ker, hdet] at hx₁
      exact absurd hx₁ (by decide)
  have ht : orderOf (mkOfDetNeZero (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3))
      (by simp)) = 3 :=
    orderOf_eq_prime (by decide) (by decide)
  refine ⟨⟨⟨_, mem_orbit_self _, Subgroup.zpowers_le.mpr ⟨_, rfl⟩⟩, fun T hT ↦ ?_⟩, ?_,
    fun K hK ↦ ?_, ?_⟩
  · cases T
    · rintro ⟨K, ⟨g, rfl⟩, hK⟩
      have h₁ : orderOf (mkOfDetNeZero (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3))
          (by simp)) ∣ Nat.card ↥(g • Subgroup.zpowers (diagGL ![1, -1] : GL (Fin 2) (ZMod 3))) :=
        Subgroup.orderOf_dvd_natCard _ (hK (MonoidHom.mem_ker.mpr (Units.ext (by simp))))
      rw [ht, hcard] at h₁
      exact absurd h₁ (by decide)
    · rintro ⟨K, ⟨g, rfl⟩, -, x, hx, hxo⟩
      have h₁ :
          orderOf x ∣ Nat.card ↥(g • Subgroup.zpowers (diagGL ![1, -1] : GL (Fin 2) (ZMod 3))) :=
        Subgroup.orderOf_dvd_natCard _ hx
      rw [hxo, hcard] at h₁
      exact absurd h₁ (by decide)
    all_goals exact absurd hT (by decide)
  · refine (Subgroup.index_eq_one.mpr (eq_top_iff.mpr fun u _ ↦ ?_)).symm
    rcases hunit u with rfl | rfl
    · exact one_mem _
    · exact ⟨_, Subgroup.mem_zpowers _, hdet⟩
  · rw [Option.mem_def, SutherlandGroupLabel.namedSubgroup, Option.some_inj, hnamed] at hK
    exact hK ▸ mem_orbit_self _
  · refine ⟨by rwa [labelCsD, labelGD_one, inf_top_eq], ⟨one_pos, one_pos, ?_,
      hnamed ▸ mem_orbit_self _⟩, fun a' b' ⟨ha', hb', _⟩ ↦ ?_⟩
    · rw [IsDetOneDiagGen, hnamed, hbot, Subgroup.card_bot, Nat.cast_one, orderOf_one]
    · rw [Lex.toLex_le_toLex]
      omega

/-- **Sutherland's tables do not take `(a, b)` lexicographically least among all pairs naming a
conjugate group**: the group `7B.6.3[2]` of his tables over quadratic fields (§6.5) is the group
`7B.1.3[2]`, as `diag(6, 6) = diag(3, 3) ^ 3`. The text's "a, b > 0 both as small as possible"
would label it `7B.1.3[2]`; his tables and script fix `a` by the determinant-one diagonal part
`{±1}` (`IsDetOneDiagGen`), which `diag(6, 1/6)` generates and `diag(1, 1)` does not. -/
lemma labelBABD_seven_two_six_three :
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    labelBABD 7 2 6 3 = labelBABD 7 2 1 3 := by
  have h₂₃ : (2 : ZMod 7) = 3 * 3 := by
    decide
  have h₆₆ : (6 : ZMod 7) * 6 = 1 := by
    decide
  have h₃ : (3 : ZMod 7) ≠ 0 := by
    decide
  have hr : orderOf (2 : ZMod 7) = 3 :=
    (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
  have h₃₃ : (!![3, 0; 0, 3] : Matrix (Fin 2) (Fin 2) (ZMod 7)) ^ 3 = !![6, 0; 0, 6] := by
    decide
  have h₃₅ : (!![3, 0; 0, 3] : Matrix (Fin 2) (Fin 2) (ZMod 7)) * !![5, 0; 0, 5] = 1 := by
    decide
  have h₅₃ : (!![5, 0; 0, 5] : Matrix (Fin 2) (Fin 2) (ZMod 7)) * !![3, 0; 0, 3] = 1 := by
    decide
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  rw [labelBABD, labelBABD, ZMod.leastGenOfIndex_eq 7 2 two_pos hr fun s hs₀ hs₂ ↦ by
    interval_cases s; simp]
  simp only [Nat.cast_ofNat, Nat.cast_one, inv_one, inv_eq_of_mul_eq_one_right h₆₆,
    div_eq_of_eq_mul h₃ h₂₃]
  refine le_antisymm ((Subgroup.closure_le _).mpr fun g hg ↦ ?_)
    ((Subgroup.closure_le _).mpr fun g hg ↦ ?_)
  · rcases hg with hg | hg | hg
    · have hg' : g = (⟨_, _, h₃₅, h₅₃⟩ : GL (Fin 2) (ZMod 7)) ^ 3 :=
        Units.ext (by rw [hg, Units.val_pow_eq_pow_val, h₃₃])
      rw [hg']
      exact pow_mem (Subgroup.subset_closure (by simp)) 3
    all_goals exact Subgroup.subset_closure (by simp [hg])
  · rcases hg with hg | hg | hg
    · have hg' : g = 1 := Units.ext (by rw [hg, Units.val_one, Matrix.one_fin_two])
      rw [hg']
      exact one_mem _
    all_goals exact Subgroup.subset_closure (by simp [hg])

end Matrix.GeneralLinearGroup
