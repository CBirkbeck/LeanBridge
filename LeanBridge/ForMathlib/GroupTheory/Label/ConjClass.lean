import LeanBridge.ForMathlib.GroupTheory.RationalConjugacy
import Mathlib.Algebra.Group.ConjFinite

/-!
# LMFDB labels of conjugacy classes and divisions

The LMFDB labels the divisions, or rational conjugacy classes (LMFDB `group.division`), and the
conjugacy classes of a finite group `G` (LMFDB `group.label_conjugacy_class`). A division has a
label `NA`: `N` is the order of its elements, which is the same for all of them, rationally
conjugate elements having the same order, and `A` is a sequence of capital letters. A conjugacy
class has a label `NAj`: `NA` is the label of the division containing it, so that `N` is the order
of its elements, and `j` numbers the conjugacy classes within that division, omitted when the
division is a single conjugacy class. The letters `A` and the numbers `j` come from the LMFDB's
algorithmic ordering of the divisions and of the classes within them (LMFDB
`group.division_computing_labels`), a database numbering which is not formalised: we record them as
data, and only say when labels are consistent with the classes they label and when an assignment of
labels is a labelling, that is, labels all classes consistently and injectively.

The conjugacy classes of a group of automorphisms of a curve are identified in the LMFDB by their
index in the list of conjugacy classes that Magma returns (LMFDB
`curve.highergenus.aut.conjugacyclasses`); that list is also a database ordering, not formalised,
of the conjugacy classes `ConjClasses G` of Mathlib, which are described by the order of their
elements (`ConjClasses.elementOrder`) and their division (`ConjClasses.toRatConjClasses`).

## Main definitions

* `ConjClasses.elementOrder` and `RatConjClasses.elementOrder` (LMFDB
  `group.label_conjugacy_class`): the order of the elements of a conjugacy class or of a division.
* `ConjClasses.toRatConjClasses` (LMFDB `group.label_conjugacy_class`): the division containing a
  conjugacy class; `RatConjClasses.conjClasses`: the conjugacy classes in a division.
* `RatConjClasses.Label`, `RatConjClasses.Label.toString`, `RatConjClasses.Label.IsConsistent` and
  `RatConjClasses.IsLabelling` (LMFDB `group.label_conjugacy_class`): labels `NA` of divisions.
* `ConjClasses.Label`, `ConjClasses.Label.toString`, `ConjClasses.Label.IsConsistent` and
  `ConjClasses.IsLabelling` (LMFDB `group.label_conjugacy_class`): labels `NAj` of conjugacy
  classes.

## Main results

* `ConjClasses.elementOrder_toRatConjClasses`: a conjugacy class and its division have the same
  order of elements.
* `ConjClasses.IsLabelling.isConsistent`: in a labelling, every label is consistent with its class.
* `ConjClasses.IsLabelling.division_eq_iff`: in a labelling, two conjugacy classes have the same
  division label if and only if they lie in the same division.
* `RatConjClasses.exists_isLabelling` and `ConjClasses.exists_isLabelling`: labellings of the
  divisions and of the conjugacy classes of a finite group exist.
-/

variable {G : Type*} [Group G] (x : G) (c c' : ConjClasses G) (d : RatConjClasses G)

namespace ConjClasses

/-- The **order of the elements** of a conjugacy class (LMFDB `group.label_conjugacy_class`), the
`N` of its label `NAj`: conjugate elements have the same order (`IsConj.orderOf_eq`). -/
noncomputable def elementOrder : ℕ :=
  Quotient.lift orderOf (fun _ _ h ↦ IsConj.orderOf_eq h) c

/-- The **division** (LMFDB `group.division`) containing a conjugacy class: conjugate elements are
rationally conjugate (`IsConj.isRationallyConj`), so every division is a union of conjugacy classes.
-/
def toRatConjClasses : RatConjClasses G :=
  Quotient.lift RatConjClasses.mk (fun _ _ h ↦ Quotient.sound <| IsConj.isRationallyConj h) c

lemma elementOrder_mk : (ConjClasses.mk x).elementOrder = orderOf x :=
  rfl

lemma toRatConjClasses_mk : (ConjClasses.mk x).toRatConjClasses = RatConjClasses.mk x :=
  rfl

end ConjClasses

namespace RatConjClasses

/-- The **order of the elements** of a division (LMFDB `group.label_conjugacy_class`), the `N` of
its label `NA`: rationally conjugate elements have the same order (`IsRationallyConj.orderOf_eq`).
-/
noncomputable def elementOrder : ℕ :=
  Quotient.lift orderOf (fun _ _ h ↦ IsRationallyConj.orderOf_eq h) d

/-- The conjugacy classes in a division. -/
def conjClasses : Set (ConjClasses G) :=
  {b | b.toRatConjClasses = d}

lemma elementOrder_mk : (RatConjClasses.mk x).elementOrder = orderOf x :=
  rfl

lemma mk_surjective : Function.Surjective (RatConjClasses.mk (G := G)) :=
  Quotient.mk_surjective

end RatConjClasses

namespace ConjClasses

lemma toRatConjClasses_surjective : Function.Surjective (toRatConjClasses (G := G)) :=
  fun d ↦ (RatConjClasses.mk_surjective d).imp' ConjClasses.mk fun _ ↦ id

/-- **A conjugacy class and its division have the same order of elements.** -/
lemma elementOrder_toRatConjClasses : c.toRatConjClasses.elementOrder = c.elementOrder := by
  rcases ConjClasses.mk_surjective c with ⟨y, rfl⟩
  rfl

lemma mem_conjClasses_toRatConjClasses : c ∈ c.toRatConjClasses.conjClasses :=
  rfl

end ConjClasses

namespace RatConjClasses

/-- The **label** `NA` of a division (LMFDB `group.label_conjugacy_class`), as data: the order `N`
of its elements and a sequence `A` of capital letters, which distinguishes the divisions whose
elements have order `N` and comes from the LMFDB's ordering of the divisions (LMFDB
`group.division_computing_labels`), a database numbering recorded here but not determined. -/
@[ext]
structure Label where
  /-- The order `N` of the elements of the division. -/
  order : ℕ
  /-- The capital letters `A`. -/
  letters : String

namespace Label

variable (ℓ : Label)

/-- The string `NA` of the label of a division: the order in decimal followed by the letters, as in
`4A`. -/
def toString : String :=
  ℓ.order.repr ++ ℓ.letters

/-- A label `NA` is **consistent** with a division `d` (LMFDB `group.label_conjugacy_class`) if `N`
is the order of the elements of `d` and `A` is a nonempty string of capital letters `A`, …, `Z`. -/
def IsConsistent : Prop :=
  ℓ.order = d.elementOrder ∧ ℓ.letters ≠ "" ∧ ∀ ch ∈ ℓ.letters.toList, ch.isUpper

end Label

/-- An assignment `ℓ` of labels `NA` to the divisions of `G` is a **labelling** (LMFDB
`group.label_conjugacy_class`) if every label is consistent with its division and distinct divisions
have distinct labels, so that `A` distinguishes the divisions whose elements have the same order. -/
def IsLabelling (ℓ : RatConjClasses G → Label) : Prop :=
  (∀ d, (ℓ d).IsConsistent d) ∧ Function.Injective ℓ

variable [Finite G] {n : ℕ}

instance : Finite (RatConjClasses G) :=
  Quotient.finite _

variable (n) in
/-- A nonempty string of capital letters for each natural number, injectively: `n + 1` letters `A`.
-/
private def capitalCode : String :=
  String.ofList (List.replicate (n + 1) 'A')

private lemma capitalCode_injective : Function.Injective capitalCode := by
  intro m n h
  simpa using congrArg List.length <| String.ofList_injective h

variable (n) in
private lemma capitalCode_ne_empty : capitalCode n ≠ "" := by
  simp [capitalCode]

private lemma isUpper_of_mem_capitalCode {ch : Char} (hch : ch ∈ (capitalCode n).toList) :
    ch.isUpper := by
  rw [capitalCode, String.toList_ofList, List.mem_replicate] at hch
  rw [hch.2]
  decide

variable (G) in
/-- **The divisions of a finite group have a labelling**: for instance by the order of their
elements followed by distinct sequences of letters `A`. -/
lemma exists_isLabelling : ∃ ℓ : RatConjClasses G → Label, IsLabelling ℓ := by
  rcases exists_injective_nat (RatConjClasses G) with ⟨f, hf⟩
  refine ⟨fun d ↦ ⟨d.elementOrder, capitalCode (f d)⟩, fun d ↦ ⟨rfl, capitalCode_ne_empty _,
    fun _ ↦ isUpper_of_mem_capitalCode⟩, fun d d' h ↦ hf <| capitalCode_injective ?_⟩
  exact congrArg Label.letters h

end RatConjClasses

namespace ConjClasses

/-- The **label** `NAj` of a conjugacy class (LMFDB `group.label_conjugacy_class`), as data: the
label `NA` of the division containing it and a number `j`, omitted (`none`) when the division is a
single conjugacy class. The letters `A` and the number `j` come from the LMFDB's ordering of the
divisions and of the classes within them (LMFDB `group.division_computing_labels`), a database
numbering recorded here but not determined. -/
@[ext]
structure Label where
  /-- The label `NA` of the division. -/
  division : RatConjClasses.Label
  /-- The number `j` of the class within its division, if the division has several classes. -/
  index : Option ℕ

namespace Label

variable (ℓ : Label)

/-- The string `NAj` of the label of a conjugacy class: the label of its division followed by `j`
in decimal, if present, as in `3A` or `3A1`. -/
def toString : String :=
  ℓ.division.toString ++ (ℓ.index.map Nat.repr).getD ""

/-- A label `NAj` is **consistent** with a conjugacy class `c` (LMFDB
`group.label_conjugacy_class`) if `NA` is consistent with the division of `c`, and `j` is omitted
exactly when that division is the single conjugacy class `c`. -/
def IsConsistent : Prop :=
  ℓ.division.IsConsistent c.toRatConjClasses ∧
    (ℓ.index = none ↔ c.toRatConjClasses.conjClasses.Subsingleton)

end Label

variable {ℓd : RatConjClasses G → RatConjClasses.Label} {ℓ : ConjClasses G → Label}

variable (ℓd ℓ) in
/-- An assignment `ℓ` of labels `NAj` to the conjugacy classes of `G` is a **labelling** (LMFDB
`group.label_conjugacy_class`), over a labelling `ℓd` of the divisions, if the label of every class
starts with the label of its division, `j` is omitted exactly for the divisions that are single
conjugacy classes, and distinct classes have distinct labels, so that `j` distinguishes the classes
within a division. -/
def IsLabelling : Prop :=
  RatConjClasses.IsLabelling ℓd ∧ (∀ c, (ℓ c).division = ℓd c.toRatConjClasses) ∧
    (∀ c, (ℓ c).index = none ↔ c.toRatConjClasses.conjClasses.Subsingleton) ∧ Function.Injective ℓ

/-- **In a labelling, every label is consistent with its conjugacy class.** -/
lemma IsLabelling.isConsistent (h : IsLabelling ℓd ℓ) : (ℓ c).IsConsistent c :=
  ⟨h.2.1 c ▸ h.1.1 _, h.2.2.1 c⟩

/-- **In a labelling, two conjugacy classes have the same division label if and only if they lie in
the same division.** -/
lemma IsLabelling.division_eq_iff (h : IsLabelling ℓd ℓ) :
    (ℓ c).division = (ℓ c').division ↔ c.toRatConjClasses = c'.toRatConjClasses := by
  rw [h.2.1, h.2.1]
  exact h.1.2.eq_iff

variable (G) [Finite G] in
/-- **The conjugacy classes of a finite group have a labelling**, over any labelling of its
divisions: for instance with distinct numbers `j` for the classes in divisions with several classes.
-/
lemma exists_isLabelling (hℓd : RatConjClasses.IsLabelling ℓd) :
    ∃ ℓ : ConjClasses G → Label, IsLabelling ℓd ℓ := by
  classical
  rcases exists_injective_nat (ConjClasses G) with ⟨f, hf⟩
  refine ⟨fun b ↦ ⟨ℓd b.toRatConjClasses,
    if b.toRatConjClasses.conjClasses.Subsingleton then none else some (f b)⟩, hℓd, fun b ↦ rfl,
    fun b ↦ by simp, fun b b' h ↦ ?_⟩
  have hd : b.toRatConjClasses = b'.toRatConjClasses := hℓd.2 <| congrArg Label.division h
  have hj : (if b.toRatConjClasses.conjClasses.Subsingleton then none else some (f b)) =
      if b'.toRatConjClasses.conjClasses.Subsingleton then none else some (f b') :=
    congrArg Label.index h
  rw [← hd] at hj
  split_ifs at hj with hb
  · exact hb b.mem_conjClasses_toRatConjClasses (hd ▸ b'.mem_conjClasses_toRatConjClasses)
  · exact hf <| Option.some_injective _ hj

end ConjClasses
