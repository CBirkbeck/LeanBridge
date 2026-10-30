import LeanBridge.ForMathlib.GroupTheory.Label.Group
import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.GaloisOrbitLabel
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.GassmannClass
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.GroupTheory.Index

/-!
# LMFDB labels of subgroups

The LMFDB labels a subgroup `H` of a finite group `G` (LMFDB `group.subgroup_label`) by
`N.i.m.a.j`, or by `N.i.m.a` for the ambient groups whose subgroups it only classifies up to
automorphism, and by the short labels `m.a.j` and `m.a` when `G` is clear from the context. Here
`N.i` is the label of `G` (LMFDB `group.label`) and `m` is the index of `H` in `G`; `a`
distinguishes the subgroups up to automorphisms of `G`, and `j` distinguishes the subgroups with the
same `a` up to conjugacy. Both `a` and `j` are a sequence of letters followed by an ordinal: the
letters write a number in base `26` with the digits `a`, …, `z` (`DirichletCharacter.letterCode`),
the position of the Gassmann class of `H` in an ordering of the Gassmann classes, and the ordinal
distinguishes the subgroups in the same Gassmann class. For `j` this is Gassmann equivalence
(`Subgroup.IsGassmannEquivalent`, LMFDB `group.gassmann_equivalence`); for `a` the LMFDB collects
together the conjugacy classes of `G` related by an automorphism (LMFDB
`group.computing_subgroup_labels`), that is, it compares subgroups on the orbits of `Aut(G)` on `G`
(`Subgroup.IsAutGassmannEquivalent`), a relation that, unlike Gassmann equivalence, is invariant
under automorphisms (`Subgroup.IsAutomorphic.isAutGassmannEquivalent`).

The orderings of the Gassmann classes and of the subgroups within them are database conventions
(LMFDB `group.computing_subgroup_labels`), which are not formalised; neither is the label `N.i` of
`G`. We record labels as data (`Subgroup.Label`), say when a label is consistent with a subgroup
(`Subgroup.Label.IsConsistent`), and when an assignment of labels to all subgroups of `G` is a
labelling: its labels are consistent, and the letters, the parts `a` and the whole labels identify
exactly the right classes of subgroups (`Subgroup.IsLabelling`, `Subgroup.IsAutLabelling`).

## Main definitions

* `Subgroup.IsAutomorphic` and `Subgroup.IsConjugate` (LMFDB `group.subgroup_label`): subgroups
  related by an automorphism of `G`, by an inner automorphism.
* `Subgroup.IsAutGassmannEquivalent` (LMFDB `group.subgroup_label`): Gassmann equivalence up to
  automorphism.
* `Subgroup.LabelPart`, `Subgroup.Label`, `Subgroup.Label.toString`,
  `Subgroup.Label.toShortString` and `Subgroup.Label.IsConsistent` (LMFDB `group.subgroup_label`):
  subgroup labels and their consistency with a subgroup.
* `Subgroup.IsLabelling` and `Subgroup.IsAutLabelling` (LMFDB `group.subgroup_label`): labellings of
  the subgroups up to conjugacy and up to automorphism.

## Main results

* `Subgroup.IsAutomorphic.index_eq`: automorphic subgroups have the same index.
* `Subgroup.IsConjugate.isGassmannEquivalent`: conjugate subgroups are Gassmann equivalent.
* `Subgroup.IsAutomorphic.isAutGassmannEquivalent`: automorphic subgroups are Gassmann equivalent
  up to automorphism.
* `Subgroup.exists_isLabelling` and `Subgroup.exists_isAutLabelling`: the subgroups of a finite
  group have labellings.
-/

open MulAction

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G] {H K : Subgroup G}

variable (H K) in
/-- Two subgroups `H` and `K` of `G` are **automorphic** (LMFDB `group.subgroup_label`) if an
automorphism of `G` maps `H` onto `K`. The part `a` of the LMFDB label of a subgroup identifies its
class for this relation. -/
def IsAutomorphic : Prop :=
  ∃ φ : MulAut G, φ • H = K

variable (H K) in
/-- Two subgroups `H` and `K` of `G` are **conjugate** (LMFDB `group.subgroup_label`) if
`K = g H g⁻¹` for some `g ∈ G`. The LMFDB label `N.i.m.a.j` of a subgroup identifies its class for
this relation. -/
def IsConjugate : Prop :=
  ∃ g : G, MulAut.conj g • H = K

variable (H K) in
/-- Two subgroups `H` and `K` of `G` are **Gassmann equivalent up to automorphism** (LMFDB
`group.subgroup_label`, `group.computing_subgroup_labels`) if `|O ∩ H| = |O ∩ K|` for every orbit
`O` of the automorphism group of `G` on `G`, a union of conjugacy classes. The letters of the part
`a` of the LMFDB label of a subgroup identify its class for this relation among the subgroups of the
same index. -/
def IsAutGassmannEquivalent : Prop :=
  ∀ x : G, Nat.card ↥(orbit (MulAut G) x ∩ H) = Nat.card ↥(orbit (MulAut G) x ∩ K)

lemma isAutomorphic_equivalence : Equivalence (IsAutomorphic (G := G)) where
  refl H := ⟨1, one_smul _ H⟩
  symm := fun ⟨φ, h⟩ ↦ ⟨φ⁻¹, inv_smul_eq_iff.mpr h.symm⟩
  trans := fun ⟨φ, h⟩ ⟨ψ, h'⟩ ↦ ⟨ψ * φ, by rw [mul_smul, h, h']⟩

lemma isConjugate_equivalence : Equivalence (IsConjugate (G := G)) where
  refl H := ⟨1, by rw [map_one, one_smul]⟩
  symm := fun ⟨g, h⟩ ↦ ⟨g⁻¹, by rw [map_inv, inv_smul_eq_iff, h]⟩
  trans := fun ⟨g, h⟩ ⟨g', h'⟩ ↦ ⟨g' * g, by rw [map_mul, mul_smul, h, h']⟩

lemma isAutGassmannEquivalent_equivalence : Equivalence (IsAutGassmannEquivalent (G := G)) :=
  ⟨fun _ _ ↦ rfl, fun h x ↦ (h x).symm, fun h h' x ↦ (h x).trans (h' x)⟩

lemma IsConjugate.isAutomorphic (h : H.IsConjugate K) : H.IsAutomorphic K :=
  h.imp' MulAut.conj fun _ ↦ id

/-- **Automorphic subgroups have the same index.** -/
lemma IsAutomorphic.index_eq (h : H.IsAutomorphic K) : H.index = K.index := by
  rcases h with ⟨φ, rfl⟩
  rw [pointwise_smul_def]
  exact (index_map_of_bijective (MulAction.bijective φ) H).symm

variable (H) in
private lemma natCard_inter_smul {S : Set G} {φ : MulAut G} (hS : φ • S = S) :
    Nat.card ↥(S ∩ ↑(φ • H)) = Nat.card ↥(S ∩ H) := by
  rw [coe_pointwise_smul, ← Set.natCard_smul_set φ (S ∩ H), Set.smul_set_inter, hS]

private lemma conj_smul_carrier (g : G) (C : ConjClasses G) :
    MulAut.conj g • C.carrier = C.carrier := by
  refine Set.ext fun x ↦ ?_
  rw [Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, by group⟩ : IsConj (g⁻¹ * x * g) x)]

/-- **Conjugate subgroups are Gassmann equivalent.** -/
lemma IsConjugate.isGassmannEquivalent (h : H.IsConjugate K) : H.IsGassmannEquivalent K := by
  rcases h with ⟨g, rfl⟩
  exact fun C ↦ (natCard_inter_smul H (conj_smul_carrier g C)).symm

/-- **Automorphic subgroups are Gassmann equivalent up to automorphism.** -/
lemma IsAutomorphic.isAutGassmannEquivalent (h : H.IsAutomorphic K) :
    H.IsAutGassmannEquivalent K := by
  rcases h with ⟨φ, rfl⟩
  exact fun x ↦ (natCard_inter_smul H (smul_orbit φ x)).symm

/-- The part `a` or `j` of the LMFDB label of a subgroup (LMFDB `group.subgroup_label`), as data:
the position of a Gassmann class, written in letters, and an ordinal distinguishing the subgroups
in that Gassmann class. Both come from database orderings, recorded here but not determined. -/
@[ext]
structure LabelPart where
  /-- The position of the Gassmann class, written in base `26` with the letters `a`, …, `z`. -/
  gassmannIndex : ℕ
  /-- The ordinal distinguishing the subgroups in the same Gassmann class. -/
  ordinal : ℕ

/-- The string of the part `a` or `j` of a subgroup label: the letters, then the ordinal in decimal,
as in `b1`. -/
def LabelPart.toString (p : LabelPart) : String :=
  DirichletCharacter.letterCode p.gassmannIndex ++ p.ordinal.repr

/-- The **label** `N.i.m.a.j` or `N.i.m.a` of a subgroup (LMFDB `group.subgroup_label`), as data:
the label `N.i` of the ambient group, the index `m`, the part `a` and, when the subgroups are
classified up to conjugacy, the part `j`. -/
@[ext]
structure Label where
  /-- The label `N.i` of the ambient group. -/
  ambient : Group.Label
  /-- The index `m` of the subgroup. -/
  index : ℕ
  /-- The part `a`, identifying the subgroup up to automorphism. -/
  aut : LabelPart
  /-- The part `j`, identifying the subgroup up to conjugacy, if present. -/
  conj : Option LabelPart

namespace Label

variable (ℓ : Label)

/-- The **short label** `m.a.j` or `m.a` of a subgroup (LMFDB `group.subgroup_label`), used when
the ambient group is clear from the context, as in `2.b1.a1`. -/
def toShortString : String :=
  ℓ.index.repr ++ "." ++ ℓ.aut.toString ++ (ℓ.conj.map fun p ↦ "." ++ p.toString).getD ""

/-- The string `N.i.m.a.j` or `N.i.m.a` of a subgroup label (LMFDB `group.subgroup_label`), as in
`8.3.2.b1.a1`. -/
def toString : String :=
  ℓ.ambient.toString ++ "." ++ ℓ.toShortString

variable (H) in
/-- A subgroup label is **consistent** with a subgroup `H` of `G` (LMFDB `group.subgroup_label`) if
its ambient label is consistent with `G` and its index is the index of `H`. The parts `a` and `j`,
database numberings, are only constrained through the other subgroups, by `Subgroup.IsLabelling`. -/
def IsConsistent : Prop :=
  ℓ.ambient.IsConsistent G ∧ ℓ.index = H.index

end Label

variable {ℓG : Group.Label} {ℓ : Subgroup G → Label}

variable (ℓG ℓ) in
/-- An assignment `ℓ` of labels `N.i.m.a.j` to the subgroups of `G` is a **labelling** (LMFDB
`group.subgroup_label`), with ambient label `ℓG`, if the labels start with `ℓG` and are consistent
with the subgroups, and: the letters of `a` identify the subgroups of the same index up to Gassmann
equivalence up to automorphism, `m.a` identifies the subgroups up to automorphism, the letters of
`j` identify the automorphic subgroups up to Gassmann equivalence, and the whole label identifies
the subgroups up to conjugacy. -/
structure IsLabelling : Prop where
  /-- Every label starts with the ambient label. -/
  ambient_eq : ∀ H, (ℓ H).ambient = ℓG
  /-- Every label is consistent with its subgroup. -/
  isConsistent : ∀ H, (ℓ H).IsConsistent H
  /-- The letters of `a` identify the subgroups of the same index up to Gassmann equivalence up to
  automorphism. -/
  gassmannIndex_eq_iff : ∀ H K, H.index = K.index →
    ((ℓ H).aut.gassmannIndex = (ℓ K).aut.gassmannIndex ↔ H.IsAutGassmannEquivalent K)
  /-- The index and `a` identify the subgroups up to automorphism. -/
  aut_eq_iff : ∀ H K, (ℓ H).index = (ℓ K).index ∧ (ℓ H).aut = (ℓ K).aut ↔ H.IsAutomorphic K
  /-- Every label has a part `j`. -/
  conj_isSome : ∀ H, (ℓ H).conj.isSome
  /-- The letters of `j` identify the automorphic subgroups up to Gassmann equivalence. -/
  conj_gassmannIndex_eq_iff : ∀ H K, H.IsAutomorphic K →
    ((ℓ H).conj.map LabelPart.gassmannIndex = (ℓ K).conj.map LabelPart.gassmannIndex ↔
      H.IsGassmannEquivalent K)
  /-- The whole label identifies the subgroups up to conjugacy. -/
  eq_iff : ∀ H K, ℓ H = ℓ K ↔ H.IsConjugate K

variable (ℓG ℓ) in
/-- An assignment `ℓ` of labels `N.i.m.a` to the subgroups of `G` is a **labelling up to
automorphism** (LMFDB `group.subgroup_label`), with ambient label `ℓG`, if the labels start with
`ℓG`, are consistent with the subgroups and have no part `j`, the letters of `a` identify the
subgroups of the same index up to Gassmann equivalence up to automorphism, and the whole label
identifies the subgroups up to automorphism. -/
structure IsAutLabelling : Prop where
  /-- Every label starts with the ambient label. -/
  ambient_eq : ∀ H, (ℓ H).ambient = ℓG
  /-- Every label is consistent with its subgroup. -/
  isConsistent : ∀ H, (ℓ H).IsConsistent H
  /-- No label has a part `j`. -/
  conj_eq_none : ∀ H, (ℓ H).conj = none
  /-- The letters of `a` identify the subgroups of the same index up to Gassmann equivalence up to
  automorphism. -/
  gassmannIndex_eq_iff : ∀ H K, H.index = K.index →
    ((ℓ H).aut.gassmannIndex = (ℓ K).aut.gassmannIndex ↔ H.IsAutGassmannEquivalent K)
  /-- The whole label identifies the subgroups up to automorphism. -/
  eq_iff : ∀ H K, ℓ H = ℓ K ↔ H.IsAutomorphic K

variable [Finite G]

private lemma exists_code {r : Subgroup G → Subgroup G → Prop} (hr : Equivalence r) :
    ∃ f : Subgroup G → ℕ, ∀ H K, f H = f K ↔ r H K := by
  rcases exists_injective_nat (Quotient ⟨r, hr⟩) with ⟨f, hf⟩
  exact ⟨fun H ↦ f ⟦H⟧, fun H K ↦ hf.eq_iff.trans Quotient.eq⟩

/-- **The subgroups of a finite group have a labelling** (LMFDB `group.subgroup_label`), for any
ambient label consistent with the group: for instance with letters and ordinals coding the
classes of subgroups for the four relations. -/
lemma exists_isLabelling (hG : ℓG.IsConsistent G) : ∃ ℓ : Subgroup G → Label, IsLabelling ℓG ℓ := by
  rcases exists_code (isAutGassmannEquivalent_equivalence (G := G)) with ⟨f₁, hf₁⟩
  rcases exists_code (isAutomorphic_equivalence (G := G)) with ⟨f₂, hf₂⟩
  rcases exists_code (isGassmannEquivalent_equivalence (G := G)) with ⟨f₃, hf₃⟩
  rcases exists_code (isConjugate_equivalence (G := G)) with ⟨f₄, hf₄⟩
  have haut (H K : Subgroup G) (h : H.IsAutomorphic K) :
      (⟨f₁ H, f₂ H⟩ : LabelPart) = ⟨f₁ K, f₂ K⟩ :=
    LabelPart.ext ((hf₁ H K).mpr h.isAutGassmannEquivalent) ((hf₂ H K).mpr h)
  refine ⟨fun H ↦ ⟨ℓG, H.index, ⟨f₁ H, f₂ H⟩, some ⟨f₃ H, f₄ H⟩⟩, fun H ↦ rfl, fun H ↦ ⟨hG, rfl⟩,
    fun H K _ ↦ hf₁ H K, fun H K ↦ ⟨fun h ↦ (hf₂ H K).mp (congrArg LabelPart.ordinal h.2),
    fun h ↦ ⟨h.index_eq, haut H K h⟩⟩, fun H ↦ rfl, fun H K _ ↦ Option.some_inj.trans (hf₃ H K),
    fun H K ↦ ⟨fun h ↦ (hf₄ H K).mp <| Option.some_injective _ <|
    congrArg (fun ℓ : Label ↦ ℓ.conj.map LabelPart.ordinal) h, fun h ↦ ?_⟩⟩
  exact Label.ext rfl h.isAutomorphic.index_eq (haut H K h.isAutomorphic) <| congrArg some <|
    LabelPart.ext ((hf₃ H K).mpr h.isGassmannEquivalent) ((hf₄ H K).mpr h)

/-- **The subgroups of a finite group have a labelling up to automorphism** (LMFDB
`group.subgroup_label`), for any ambient label consistent with the group: for instance a labelling
up to conjugacy with the parts `j` removed. -/
lemma exists_isAutLabelling (hG : ℓG.IsConsistent G) :
    ∃ ℓ : Subgroup G → Label, IsAutLabelling ℓG ℓ := by
  rcases exists_isLabelling hG with ⟨ℓ, hℓ⟩
  refine ⟨fun H ↦ {ℓ H with conj := none}, hℓ.ambient_eq, hℓ.isConsistent, fun H ↦ rfl,
    hℓ.gassmannIndex_eq_iff, fun H K ↦ ?_⟩
  simp only [Label.ext_iff, hℓ.ambient_eq, and_true, true_and, ← hℓ.aut_eq_iff]

end Subgroup
