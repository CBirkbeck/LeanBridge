import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2NonsplitNormalizer

/-!
# Sutherland's canonical label of a subgroup of `GL₂(𝔽_p)`

This file refines the relation `Matrix.GeneralLinearGroup.IsSutherlandLabel`, between subgroups of
`GL₂(𝔽_p)` and Sutherland's labels `ℓS.a.b.c[d]`, on the classes `Ns`, `Cn` and `Nn`, so that every
subgroup has exactly one label, and that label is the one computed by Sutherland's Magma script
`subgroups.m` (reference [68] of arXiv:1504.07618v7), which is the label the LMFDB stores. The
relation `IsSutherlandLabel` differs from the script in the following ways.

* On `Ns` it is not functional. A group with projective image the Klein group can lie in `C_s⁺` in
  two ways, with non-conjugate diagonal parts (Lemma 3.16 of the paper), which then fall into
  different forms. So the group of order `8` of `5Ns.2.1[2]` also has the label `5Ns.4.1.1[2]`. The
  script says "opt for the cyclic choice" (`IsNsCyclicPreferred`).
* On `Ns` it minimises the integers `b` and `c` over all the conjugates of the group, which makes
  the integer `b` of `Ns.a.b[d]` always `1`, where the script takes them in a specific conjugate,
  the one containing `!![0, 1; 1, 0]`, or `!![0, z; 1, 0]` with `z` the least primitive root to the
  power `[Z : H ∩ Z]` in the second case of Sutherland's Lemma 3.13 (`IsNsNormalForm`). So the
  script gives the group of order `48` and `d = 1` of `GL₂(𝔽₁₃)` that `IsSutherlandLabel` calls
  `13Ns.5.1` the label `13Ns.5.2`, which is the label of the modular curve `13.546.24.c.1` in the
  LMFDB; the paper's "a, b minimal" does not say over what `b` is minimised.
* On `Cn` and `Nn` it takes `(a, b)` lexicographically least among all the generators of the cyclic
  part, as the paper and the comment of the script say. The code of the script looks only among the
  generators `g` with `(tr g)² / det g = 2 + Tr(RootOfUnity(n, GF(p^2)))`, `n` the order of `g` in
  `PGL₂(𝔽_p)` (`IsScriptCartanGen`), which for `n` with `φ(n) > 2` can give larger integers, and the
  LMFDB follows the code: it has `17Nn.3.7.1`, `19Nn.1.8`, `19Nn.2.8`, `23Cn.1.11`, `23Nn.1.11`,
  `29Cn.1.14`, `29Nn.1.14`, where the lexicographically least integers are `(1, 1)`, `(1, 7)`,
  `(1, 6)`, `(1, 5)`, `(1, 5)`, `(1, 8)`, `(1, 8)`.

For the other classes this file keeps `IsSutherlandLabel`. All this has been compared with a port of
the script on all subgroups for `p ≤ 17`, with every row of the paper's tables, and with a sample of
`241` Sutherland labels of the LMFDB's modular curves of prime level up to `61`. On all this data
the root of unity of Magma is `z ^ ((p ^ 2 - 1) / n)`, for `z` a root of the Conway polynomial of
`GF(p^2)` (`IsConwayGen`).

## Main definitions

* `Matrix.GeneralLinearGroup.IsNsDetDisjoint`: `det(K ∩ C_s)` and `-det(K \ C_s)` are disjoint.
* `Matrix.GeneralLinearGroup.IsNsCyclicPreferred`: the diagonal part of `K` is cyclic if some
  conjugate of `K` in `C_s⁺` has a cyclic diagonal part.
* `Matrix.GeneralLinearGroup.IsNsNormalForm`: `K` contains the matrix of the script's conjugate.
* `Matrix.GeneralLinearGroup.IsConwayGen`, `Matrix.GeneralLinearGroup.conwayGen`: a generator of
  `C_ns = 𝔽_{p²}ˣ` that is a root of the Conway polynomial of `𝔽_{p²}`.
* `Matrix.GeneralLinearGroup.IsScriptCartanGen`,
  `Matrix.GeneralLinearGroup.IsScriptCartanPair`: the condition of the script on a generator of the
  cyclic part.
* `Matrix.GeneralLinearGroup.SutherlandGroupLabel.CanonicalParamsOf`: the conditions on `a`, `b`,
  `c`.
* `Matrix.GeneralLinearGroup.IsCanonicalSutherlandLabel` (LMFDB `ec.galois_rep_modell_image`): `L`
  is Sutherland's label of the subgroup `H`.

## Main results

* `Matrix.GeneralLinearGroup.isCanonicalSutherlandLabel_smul_iff`: it is a conjugacy invariant.
* `Matrix.GeneralLinearGroup.IsCanonicalSutherlandLabel.mem_subgroupConjClass`: two subgroups with
  the same label naming a subgroup are conjugate.
-/

open Matrix MulAction TauCeti

open scoped MatrixGroups Pointwise

namespace Matrix.GeneralLinearGroup

variable (p : ℕ) [Fact p.Prime] (H K : Subgroup (GL (Fin 2) (ZMod p))) (L : SutherlandGroupLabel)

/-- The determinants of the elements of `K` in `C_s` and the negatives of the determinants of the
elements of `K` outside `C_s` form disjoint sets: case (2b) of Lemma 3.13 of Sutherland
(arXiv:1504.07618v7). The script `subgroups.m` tests this condition on an element of `K \ C_s`, and
it does not depend on the element. -/
def IsNsDetDisjoint : Prop :=
  ∀ x ∈ K, x ∉ diagonalTorus (ZMod p) 2 → -det x ∉ (K ⊓ diagonalTorus (ZMod p) 2).map det

/-- The diagonal part of `K` is cyclic if some conjugate of `K` in `C_s⁺` has a cyclic diagonal
part: when conjugate subgroups of `C_s⁺` have non-conjugate diagonal parts, one of these is cyclic
and the other is not (Lemma 3.16 of Sutherland, arXiv:1504.07618v7), and his script `subgroups.m`
says "opt for the cyclic choice". -/
def IsNsCyclicPreferred : Prop :=
  IsCyclic ↥(K ⊓ diagonalTorus (ZMod p) 2) ∨ ∀ K' ∈ subgroupConjClass p K, K' ≤ labelNs p →
    ¬IsCyclic ↥(K' ⊓ diagonalTorus (ZMod p) 2)

/-- `K` contains the matrix of the conjugate of a subgroup of `C_s⁺` that Sutherland's script
`subgroups.m` chooses (function `NormalizerSplitCartanConjugate`, following Corollary 3.18 of
arXiv:1504.07618v7): `!![0, 1; 1, 0]`, unless `det(K ∩ C_s)` and `-det(K \ C_s)` are disjoint, and
then `!![0, ε ^ e; 1, 0]` for `ε` the least primitive root and `e = [Z : K ∩ Z]`. -/
def IsNsNormalForm : Prop :=
  (IsNsDetDisjoint p K → ∃ x ∈ K, x.val = !![0, (ZMod.leastPrimitiveRoot p : ZMod p) ^
    ((K ⊓ Subgroup.center _).relIndex (Subgroup.center _)); 1, 0]) ∧
    (¬IsNsDetDisjoint p K → swapGL (ZMod p) ∈ K)

/-- `δ` is a root of the **Conway polynomial** of `𝔽_{p²}`, in `C_ns = labelCn p ≅ 𝔽_{p²}ˣ`: a
generator of `C_ns` whose determinant is the least primitive root `ε` modulo `p` and whose trace is
least as a natural number, since the Conway polynomial `x² - a x + ε` is the first primitive
polynomial `x² - a x + ε` for this order of the coefficients `a`. The Conway polynomial defines
Magma's `GF(p^2)`. -/
def IsConwayGen (δ : GL (Fin 2) (ZMod p)) : Prop :=
  Subgroup.zpowers δ = labelCn p ∧ (det δ : ZMod p) = ZMod.leastPrimitiveRoot p ∧
    ∀ δ' : GL (Fin 2) (ZMod p), Subgroup.zpowers δ' = labelCn p →
      (det δ' : ZMod p) = ZMod.leastPrimitiveRoot p → δ.val.trace.val ≤ δ'.val.trace.val

/-- A root of the Conway polynomial of `𝔽_{p²}` in `C_ns` (`IsConwayGen`), chosen by
`Classical.epsilon`. There are two, conjugate over `𝔽_p`, and the traces of their powers, all that
is used of them, are the same (`IsConwayGen.trace_pow_eq`). -/
noncomputable def conwayGen : GL (Fin 2) (ZMod p) :=
  Classical.epsilon (IsConwayGen p)

/-- `g` satisfies the condition of the function `NonSplitCartanConjugate` of Sutherland's script
`subgroups.m` (arXiv:1504.07618v7, [68]): `(tr g)² / det g = 2 + Tr(ζ)`, for `ζ` the script's
`RootOfUnity(n, GF(p^2))`, `n` the order of `g` in `PGL₂(𝔽_p)`. On the LMFDB's data `ζ` is
`z ^ ((p ^ 2 - 1) / n)`, for `z` a root of the Conway polynomial (`conwayGen`), and the trace of
this matrix is `Tr(ζ)`. The value `(tr g)² / det g - 2` is `ξ + ξ⁻¹` for `ξ = g ^ (p - 1)` a
primitive `n`-th root of unity, so the condition holds for some of the generators of a subgroup
of `C_ns`, and for all of them if `φ(n) ≤ 2`. -/
def IsScriptCartanGen (g : GL (Fin 2) (ZMod p)) : Prop :=
  g.val.trace ^ 2 = (2 + (conwayGen p ^ ((p ^ 2 - 1) /
    orderOf (ProjGenLinGroup.mk g))).val.trace) * g.val.det

/-- The matrix `!![a, ε * b; b, a]` is invertible and satisfies the condition of Sutherland's script
on the generators of the cyclic part of a label `Cn.a.b[d]`, `Nn.a.b[d]` or `Nn.a.b.c[d]`
(`IsScriptCartanGen`). -/
def IsScriptCartanPair (a b : ℕ) : Prop :=
  ∃ g : GL (Fin 2) (ZMod p), g.val = !![(a : ZMod p), (ZMod.leastPrimitiveRoot p : ZMod p) * b;
    (b : ZMod p), a] ∧ IsScriptCartanGen p g

/-- Sutherland's conditions on the integers `a`, `b`, `c` of the label `L` of a subgroup `H` of
`GL₂(𝔽_p)`, as computed by his script `subgroups.m` (arXiv:1504.07618v7, §6.4 and [68]). For
classes other than `Ns`, `Cn`, `Nn` they are `SutherlandGroupLabel.ParamsOf`. For `Ns` the integers
`a`, `b`, `c` are those of the group named by the label, conjugate to `H`, which has determinant-one
part in `C_s` exactly for the form `Ns.a.b[d]`, with `IsDetOneDiagGen` fixing `a`, with diagonal
part as the script prefers (`IsNsCyclicPreferred`), and in the script's normal form
(`IsNsNormalForm`), `a`, `b`, `c` being lexicographically least with these properties. For `Cn` and
`Nn` they are those of `SutherlandGroupLabel.ParamsOf`, with `(a, b)` lexicographically least among
the pairs that also satisfy the condition of the script (`IsScriptCartanPair`). -/
def SutherlandGroupLabel.CanonicalParamsOf : Prop :=
  match L.cls, L.params with
  | .Cn, [a, b] => labelCnD p L.d ∉ subgroupConjClass p H ∧
      IsLexLeastPair a b fun a b ↦ 0 < b ∧ IsScriptCartanPair p a b ∧
        labelCnAB p a b ∈ subgroupConjClass p H
  | .Ns, [a, b] => labelNsD p L.d ∉ subgroupConjClass p H ∧ IsLexLeastPair a b fun a b ↦ 0 < a ∧
      0 < b ∧ IsDetOneDiagGen p a (labelNsABD p L.d a b) ∧
        labelNsABD p L.d a b ⊓ det.ker ≤ diagonalTorus (ZMod p) 2 ∧
          labelNsABD p L.d a b ∈ subgroupConjClass p H ∧
            IsNsCyclicPreferred p (labelNsABD p L.d a b) ∧ IsNsNormalForm p (labelNsABD p L.d a b)
  | .Ns, [a, b, c] => labelNsD p L.d ∉ subgroupConjClass p H ∧ IsLexLeastTriple a b c
      fun a b c ↦ 0 < a ∧ 0 < b ∧ 0 < c ∧ IsDetOneDiagGen p a (labelNsABCD p L.d a b c) ∧
        ¬labelNsABCD p L.d a b c ⊓ det.ker ≤ diagonalTorus (ZMod p) 2 ∧
          labelNsABCD p L.d a b c ∈ subgroupConjClass p H ∧
            IsNsCyclicPreferred p (labelNsABCD p L.d a b c) ∧
              IsNsNormalForm p (labelNsABCD p L.d a b c)
  | .Nn, [a, b] => labelNnD p L.d ∉ subgroupConjClass p H ∧
      IsLexLeastPair a b fun a b ↦ 0 < b ∧ IsScriptCartanPair p a b ∧
        labelNnAB p a b ∈ subgroupConjClass p H
  | .Nn, [a, b, c] => labelNnD p L.d ∉ subgroupConjClass p H ∧
      c = (H ⊓ Subgroup.center _).relIndex (Subgroup.center _) ∧
      IsLexLeastPair a b fun a b ↦ 0 < b ∧ IsScriptCartanPair p a b ∧
        H ⊓ Subgroup.center _ ≤ labelCnAB p a b ∧
          ∀ δ : GL (Fin 2) (ZMod p), Subgroup.zpowers δ = labelCn p →
            IsNnDetDisjoint p (labelNnABC p a b c δ) ∧ labelNnABC p a b c δ ∈ subgroupConjClass p H
  | _, _ => L.ParamsOf p H

/-- `L` is **Sutherland's label** `ℓS.a.b.c[d]` of the subgroup `H` of `GL₂(𝔽_p)`
(arXiv:1504.07618, §6.4; LMFDB `ec.galois_rep_modell_image`), as computed by his script
`subgroups.m`: `H` has class `S`, `d` is the index of `det H` in `𝔽_pˣ`, `H` is conjugate to the
group the label names (classes `G`, `B`, `Cs`, `Cn`, `Ns`, `Nn`), and the integers `a`, `b`, `c`
satisfy Sutherland's conditions (`SutherlandGroupLabel.CanonicalParamsOf`). Every subgroup has
exactly one such label, and two subgroups with the same label are conjugate. -/
def IsCanonicalSutherlandLabel : Prop :=
  HasSutherlandClass p H L.cls ∧ L.d = (H.map det).index ∧
    (∀ K ∈ L.namedSubgroup p, K ∈ subgroupConjClass p H) ∧ L.CanonicalParamsOf p H

variable {p H K} (g : ConjAct (GL (Fin 2) (ZMod p)))

lemma SutherlandGroupLabel.canonicalParamsOf_smul_iff :
    L.CanonicalParamsOf p (g • H) ↔ L.CanonicalParamsOf p H := by
  simp only [SutherlandGroupLabel.CanonicalParamsOf, orbit_smul, smul_inf_center,
    L.paramsOf_smul_iff]

/-- **Sutherland's label is a conjugacy invariant.** -/
lemma isCanonicalSutherlandLabel_smul_iff :
    IsCanonicalSutherlandLabel p (g • H) L ↔ IsCanonicalSutherlandLabel p H L := by
  rw [IsCanonicalSutherlandLabel, IsCanonicalSutherlandLabel, hasSutherlandClass_smul_iff,
    map_det_smul, L.canonicalParamsOf_smul_iff, subgroupConjClass, orbit_smul]

variable {L}

/-- **Two subgroups of `GL₂(𝔽_p)` with the same Sutherland label are conjugate**, when the label
names a subgroup. -/
lemma IsCanonicalSutherlandLabel.mem_subgroupConjClass {N : Subgroup (GL (Fin 2) (ZMod p))}
    (hH : IsCanonicalSutherlandLabel p H L) (hK : IsCanonicalSutherlandLabel p K L)
    (hN : N ∈ L.namedSubgroup p) : K ∈ subgroupConjClass p H :=
  orbit_eq_iff.mp <|
    (orbit_eq_iff.mpr (hK.2.2.1 N hN)).symm.trans (orbit_eq_iff.mpr (hH.2.2.1 N hN))

lemma isCanonicalSutherlandLabel_iff_of_cls_ne (hCn : L.cls ≠ .Cn) (hNs : L.cls ≠ .Ns)
    (hNn : L.cls ≠ .Nn) : IsCanonicalSutherlandLabel p H L ↔ IsSutherlandLabel p H L := by
  have h : L.CanonicalParamsOf p H ↔ L.ParamsOf p H := by
    rcases L with ⟨S, ps, d⟩
    cases S <;> first
      | exact absurd rfl hCn
      | exact absurd rfl hNs
      | exact absurd rfl hNn
      | exact Iff.rfl
  rw [IsCanonicalSutherlandLabel, IsSutherlandLabel, h]

end Matrix.GeneralLinearGroup
