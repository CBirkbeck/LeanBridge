import LeanBridge.ForMathlib.NumberTheory.ModularCurve.GassmannClass
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-!
# Arithmetically equivalent siblings of a transitive permutation group

Let `K` be a number field of degree `n` whose Galois closure `L` has Galois group `G ≤ S_n`, the
permutation group of the `n` embeddings of `K` into `L`, and let `H₁` be the stabiliser of a point,
so that `K` is the fixed field of `H₁`. By the Galois correspondence the subfields of `L` are the
fixed fields of the subgroups of `G`, two of them being isomorphic exactly when the subgroups are
conjugate (`IntermediateField.nonempty_algEquiv_fixedField_iff`). Perlis's theorem says that the
fixed field of `H₂` is arithmetically equivalent to `K` (same Dedekind zeta function, LMFDB
`nf.arithmetically_equivalent`) exactly when `H₂` is Gassmann equivalent to `H₁`:
`|H₁ ∩ C| = |H₂ ∩ C|` for every conjugacy class `C` of `G`. So the number of fields
arithmetically equivalent to `K`, other than `K` and up to isomorphism, is the number of conjugacy
classes of subgroups of `G` Gassmann equivalent to `H₁`, other than that of `H₁`: a function of the
permutation group `G`, independent of the chosen point since `G` is transitive. Perlis's theorem,
which needs the Chebotarev density theorem and the Artin formalism of zeta functions, is not
formalised; the count is defined group-theoretically, as the LMFDB computes it.

## Main definitions

* `Subgroup.arithmeticallyEquivalentSiblings` (LMFDB `gg.arithmetically_equivalent`): the
  conjugacy classes of subgroups Gassmann equivalent to `H`, other than that of `H`.
* `MulAction.arithmeticallyEquivalentCount` (LMFDB `gg.arithmetically_equivalent`): their number
  for the stabiliser of a point of a permutation group.

## Main results

* `Subgroup.isGassmannEquivalent_conjAct_smul`: conjugate subgroups are Gassmann equivalent.
* `Subgroup.IsGassmannEquivalent.natCard_eq` and `Subgroup.IsGassmannEquivalent.index_eq`:
  Gassmann equivalent subgroups of a finite group have the same order and the same index, so the
  arithmetically equivalent fields have the same degree.
* `Subgroup.arithmeticallyEquivalentSiblings_conjAct_smul`: the siblings depend only on the
  conjugacy class of `H`.
* `MulAction.arithmeticallyEquivalentCount_eq`: for a transitive permutation group the count does
  not depend on the point.
-/

open MulAction

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G] (H K : Subgroup G) (g : ConjAct G)

/-- **Conjugate subgroups are Gassmann equivalent**: conjugation by `g` maps `C ∩ H` bijectively
onto `C ∩ g H g⁻¹` for every conjugacy class `C`. -/
lemma isGassmannEquivalent_conjAct_smul : (g • H).IsGassmannEquivalent H :=
  fun C ↦ Nat.card_congr <| (toPerm g⁻¹ : Equiv.Perm G).subtypeEquiv fun x ↦ by
    refine and_congr ?_ mem_pointwise_smul_iff_inv_smul_mem
    rw [toPerm_apply, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj.mpr <| isConj_iff.mpr ⟨ConjAct.ofConjAct g⁻¹,
        (ConjAct.smul_def g⁻¹ x).symm⟩]

lemma natCard_eq_sum_natCard_inter [Finite G] [Fintype (ConjClasses G)] :
    Nat.card H = ∑ C : ConjClasses G, Nat.card ↥(C.carrier ∩ H) := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr <| (Equiv.sigmaFiberEquiv fun x : H ↦ ConjClasses.mk (x : G)).symm.trans <|
    Equiv.sigmaCongrRight fun _ ↦
      { toFun x := ⟨x.1, ConjClasses.mem_carrier_iff_mk_eq.mpr x.2, x.1.2⟩
        invFun x := ⟨⟨x.1, x.2.2⟩, ConjClasses.mem_carrier_iff_mk_eq.mp x.2.1⟩ }

variable {H K}

/-- **Gassmann equivalent subgroups of a finite group have the same order**: the order of `H` is
the sum of the `|C ∩ H|` over the conjugacy classes `C`. -/
lemma IsGassmannEquivalent.natCard_eq [Finite G] (h : H.IsGassmannEquivalent K) :
    Nat.card H = Nat.card K := by
  let hC : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [natCard_eq_sum_natCard_inter H, natCard_eq_sum_natCard_inter K]
  exact Finset.sum_congr rfl fun C _ ↦ h C

/-- **Gassmann equivalent subgroups of a finite group have the same index**: the fields that they
fix have the same degree. -/
lemma IsGassmannEquivalent.index_eq [Finite G] (h : H.IsGassmannEquivalent K) : H.index = K.index :=
  Nat.eq_of_mul_eq_mul_left Nat.card_pos <| by
    rw [card_mul_index, h.natCard_eq, card_mul_index]

variable (H)

/-- The **arithmetically equivalent siblings** (LMFDB `gg.arithmetically_equivalent`) of a
subgroup `H` of a group `G`: the conjugacy classes of subgroups `H₂` of `G`, other than that of
`H`, that are Gassmann equivalent to `H`, i.e. `|H ∩ C| = |H₂ ∩ C|` for every conjugacy class `C`
of `G`. Gassmann equivalence does not depend on the representative `H₂` of its class
(`isGassmannEquivalent_conjAct_smul`). For `G` the Galois group of the Galois closure of a number
field `F` and `H` the stabiliser of an embedding of `F`, they are the isomorphism classes of the
number fields arithmetically equivalent to `F`, other than `F` (Perlis's theorem, not formalised).
-/
def arithmeticallyEquivalentSiblings : Set (orbitRel.Quotient (ConjAct G) (Subgroup G)) :=
  {c | c ≠ Quotient.mk _ H ∧ ∃ H₂ : Subgroup G, Quotient.mk _ H₂ = c ∧ H₂.IsGassmannEquivalent H}

/-- **The arithmetically equivalent siblings of a subgroup depend only on its conjugacy class.** -/
lemma arithmeticallyEquivalentSiblings_conjAct_smul :
    (g • H).arithmeticallyEquivalentSiblings = H.arithmeticallyEquivalentSiblings := by
  have hc :
      (Quotient.mk _ (g • H) : orbitRel.Quotient (ConjAct G) (Subgroup G)) = Quotient.mk _ H :=
    Quotient.sound <| mem_orbit H g
  have hK (H₂ : Subgroup G) : H₂.IsGassmannEquivalent (g • H) ↔ H₂.IsGassmannEquivalent H :=
    ⟨fun h C ↦ (h C).trans (isGassmannEquivalent_conjAct_smul H g C),
      fun h C ↦ (h C).trans (isGassmannEquivalent_conjAct_smul H g C).symm⟩
  simp only [arithmeticallyEquivalentSiblings, hc, hK]

end Subgroup

namespace MulAction

variable (G : Type*) [Group G] {X : Type*} [MulAction G X] (x : X)

/-- The **number of arithmetically equivalent siblings** (LMFDB `gg.arithmetically_equivalent`,
`gg.arithmetically_equiv_input`) of a permutation group `G` of a set `X`, at a point `x`: the
number of conjugacy classes of subgroups of `G` Gassmann equivalent to the stabiliser `H₁` of `x`,
other than that of `H₁` (`Subgroup.arithmeticallyEquivalentSiblings`), and `0` if there are
infinitely many. For a transitive group `G ≤ S_n` it does not depend on `x`
(`arithmeticallyEquivalentCount_eq`); for the Galois group of the Galois closure of a number field
`F` of degree `n` it is, by Perlis's theorem (not formalised), the number of fields arithmetically
equivalent to `F`, not including `F`, up to isomorphism. -/
noncomputable def arithmeticallyEquivalentCount : ℕ :=
  (stabilizer G x).arithmeticallyEquivalentSiblings.ncard

lemma arithmeticallyEquivalentCount_smul (g : G) :
    arithmeticallyEquivalentCount G (g • x) = arithmeticallyEquivalentCount G x := by
  rw [arithmeticallyEquivalentCount, arithmeticallyEquivalentCount,
    stabilizer_smul_eq_stabilizer_map_conj]
  exact congrArg Set.ncard <|
    (stabilizer G x).arithmeticallyEquivalentSiblings_conjAct_smul (ConjAct.toConjAct g)

/-- **For a transitive permutation group, the number of arithmetically equivalent siblings does
not depend on the point**: it is a function of the permutation group. -/
lemma arithmeticallyEquivalentCount_eq [IsPretransitive G X] (y : X) :
    arithmeticallyEquivalentCount G x = arithmeticallyEquivalentCount G y := by
  rcases exists_smul_eq G x y with ⟨g, rfl⟩
  exact (arithmeticallyEquivalentCount_smul G x g).symm

end MulAction
