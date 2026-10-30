import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# LMFDB labels of finite groups

The LMFDB labels a finite group `G` by a string `N.i` (LMFDB `group.label`): `N` is the order of
`G`, and `i` distinguishes `G`, up to isomorphism, from the other groups of order `N`. For a group
in the SmallGroups library of GAP and Magma, which identifies its groups by pairs `[n, d]` (LMFDB
`group.small_group_label`), `i` is the small group id `d`; for any other group it is a letter code,
assigned in the order in which groups were added to the LMFDB. The values of `d` and of the letter
codes are database numberings, which the LMFDB does not define mathematically: they are not
formalised. What is mathematics is that `N` is the order and that the second part determines the
isomorphism class among the groups of order `N` (`Group.DistinguishesIsoClasses`).

We record a label as data (`Group.Label`), say when it is consistent with a group
(`Group.Label.IsConsistent`), and when an assignment of labels to all finite groups is a labelling
in the LMFDB's sense (`Group.IsLabelling`), to which the LMFDB's labels of the groups of its
database extend. Such labellings exist (`Group.exists_isLabelling`): the multiplication tables of a
group of order `n` on `{0, …, n - 1}` determine it up to isomorphism, and there are finitely many of
them.

## Main definitions

* `Group.DistinguishesIsoClasses` (LMFDB `group.label`, `group.small_group_label`): functions on
  finite groups that distinguish the groups of a given order up to isomorphism.
* `Group.IsLetterCode` (LMFDB `group.label`): the letter codes of LMFDB labels.
* `Group.LabelIndex`, `Group.Label`, `Group.Label.toString`, `Group.Label.IsConsistent` and
  `Group.IsLabelling` (LMFDB `group.label`).
* `Group.SmallGroupId`, `Group.SmallGroupId.IsConsistent`, `Group.SmallGroupId.toLabel` and
  `Group.IsSmallGroupIdentification` (LMFDB `group.small_group_label`).

## Main results

* `Group.IsLabelling.eq_iff`: in a labelling, two finite groups have the same label if and only if
  they are isomorphic.
* `Group.exists_isSmallGroupIdentification`: there are positive integers that distinguish the finite
  groups of each order up to isomorphism.
* `Group.exists_isLabelling`: labellings exist.
-/

universe u

namespace Group

variable (G H : Type u) (S : Set ℕ)

/-- A function `f` on finite groups **distinguishes the isomorphism classes** of the groups whose
orders lie in `S` if two finite groups of the same order `n ∈ S` have the same value of `f` exactly
when they are isomorphic. The second part `i` of the LMFDB label `N.i` of a finite group (LMFDB
`group.label`), for `S` the set of all orders, and the second entry `d` of its small group id
`[n, d]` (LMFDB `group.small_group_label`), for `S` the set of orders in the SmallGroups library,
are such functions; their values are database numberings. -/
def DistinguishesIsoClasses {α : Sort*} (f : ∀ (G : Type u) [Group G] [Finite G], α) : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Finite G] [Finite H], Nat.card G ∈ S →
    Nat.card G = Nat.card H → (f G = f H ↔ Nonempty (G ≃* H))

/-- A **letter code** in an LMFDB label (LMFDB `group.label`): a nonempty string of lower-case
letters `a`, …, `z`. Which encoding of numbers by letters the LMFDB uses is not specified by the
knowl, and not fixed here. -/
def IsLetterCode (s : String) : Prop :=
  s ≠ "" ∧ ∀ c ∈ s.toList, c.isLower

/-- The second part `i` of the LMFDB label `N.i` of a finite group (LMFDB `group.label`). -/
inductive LabelIndex
  /-- The small group id `d` of a group with small group id `[N, d]` (LMFDB
  `group.small_group_label`) in the SmallGroups library of GAP and Magma. -/
  | smallGroupId (d : ℕ)
  /-- A letter code, for a group outside the SmallGroups library, assigned in the order in which
  groups were added to the LMFDB. -/
  | letterCode (code : String)

namespace LabelIndex

/-- The second part of a group label is **well formed** if it is a positive small group id or a
nonempty string of lower-case letters `a`, …, `z`. -/
def IsWellFormed : LabelIndex → Prop
  | smallGroupId d => 0 < d
  | letterCode code => IsLetterCode code

/-- The second part of a group label as a string: the small group id in decimal, or the letter
code. -/
def toString : LabelIndex → String
  | smallGroupId d => d.repr
  | letterCode code => code

end LabelIndex

/-- The **label** `N.i` of a finite group (LMFDB `group.label`), as data: the order `N` and the
second part `i`, a small group id or a letter code. The value of `i` is a database numbering, which
is recorded here but not determined: the label of a given group is only constrained by
`Group.Label.IsConsistent` and, through the other groups, by `Group.IsLabelling`. -/
@[ext]
structure Label where
  /-- The order `N` of the group. -/
  order : ℕ
  /-- The second part `i`: a small group id or a letter code. -/
  index : LabelIndex

namespace Label

variable (ℓ : Label)

/-- The string `N.i` of a group label (LMFDB `group.label`): the order in decimal, a dot and the
second part, as in `24.3` for `SL(2, 3)`. -/
def toString : String :=
  ℓ.order.repr ++ "." ++ ℓ.index.toString

/-- A group label `N.i` is **consistent** with a finite group `G` (LMFDB `group.label`) if `N` is
the order of `G` and `i` is well formed. Which `i` labels `G` is a database numbering, not
determined here: consistency only depends on the order of `G`, and the group structure does not
enter. -/
def IsConsistent : Prop :=
  ℓ.order = Nat.card G ∧ ℓ.index.IsWellFormed

variable {G H} in
lemma isConsistent_congr (e : G ≃ H) : ℓ.IsConsistent G ↔ ℓ.IsConsistent H := by
  rw [IsConsistent, IsConsistent, Nat.card_congr e]

end Label

variable {ℓ : ∀ (G : Type u) [Group G] [Finite G], Label}

variable (ℓ) in
/-- An assignment `ℓ` of labels to the finite groups is a **labelling** (LMFDB `group.label`) if
the label of every group is consistent with it, and the second parts of the labels distinguish the
groups of each order up to isomorphism. The LMFDB's labels, defined on the groups of its database by
the SmallGroups library and the order in which groups were added to the LMFDB, extend to such an
assignment; which labelling they give is a database numbering, not determined here. -/
def IsLabelling : Prop :=
  (∀ (G : Type u) [Group G] [Finite G], (ℓ G).IsConsistent G) ∧ DistinguishesIsoClasses Set.univ
    fun G _ _ ↦ (ℓ G).index

variable [Group G] [Group H] [Finite G] [Finite H] in
/-- **In a labelling, two finite groups have the same label if and only if they are isomorphic.** -/
lemma IsLabelling.eq_iff (hℓ : IsLabelling ℓ) : ℓ G = ℓ H ↔ Nonempty (G ≃* H) := by
  rw [Label.ext_iff, (hℓ.1 G).1, (hℓ.1 H).1]
  refine ⟨fun h ↦ (hℓ.2 G H (Set.mem_univ _) h.1).mp h.2, fun ⟨e⟩ ↦ ?_⟩
  have h : Nat.card G = Nat.card H := Nat.card_congr e.toEquiv
  exact ⟨h, (hℓ.2 G H (Set.mem_univ _) h).mpr ⟨e⟩⟩

/-- The **small group id** `[n, d]` (LMFDB `group.small_group_label`) of a group in the SmallGroups
library of GAP and Magma, as data: the order `n` and the id `d`. The library includes all groups of
order at most `2000` except those of order `1024`, and the value of `d` is a database numbering, the
same in GAP and Magma, which is recorded here but not determined. -/
structure SmallGroupId where
  /-- The order `n` of the group. -/
  order : ℕ
  /-- The id `d`, distinguishing the group from the other groups of order `n`. -/
  id : ℕ

namespace SmallGroupId

variable (s : SmallGroupId)

/-- A small group id `[n, d]` is **consistent** with a finite group `G` (LMFDB
`group.small_group_label`) if `n` is the order of `G` and `d` is positive. Which `d` identifies `G`
is a database numbering, not determined here. -/
def IsConsistent : Prop :=
  s.order = Nat.card G ∧ 0 < s.id

/-- The LMFDB label `n.d` (LMFDB `group.label`) of a group with small group id `[n, d]`. -/
def toLabel : Label :=
  ⟨s.order, .smallGroupId s.id⟩

lemma isConsistent_toLabel_iff : s.toLabel.IsConsistent G ↔ s.IsConsistent G :=
  Iff.rfl

end SmallGroupId

/-- An assignment `d` of integers to the finite groups is a **small group identification**
(LMFDB `group.small_group_label`) of the groups whose orders lie in `S` if it is positive on these
groups and distinguishes those of the same order up to isomorphism, as the second entries `d` of the
small group ids `[n, d]` do for the orders `n` of the SmallGroups library. -/
def IsSmallGroupIdentification (d : ∀ (G : Type u) [Group G] [Finite G], ℕ) : Prop :=
  (∀ (G : Type u) [Group G] [Finite G], Nat.card G ∈ S → 0 < d G) ∧ DistinguishesIsoClasses S d

variable {G H} [Group G] [Group H] {n : ℕ}

variable (G n) in
/-- The multiplication tables of `G` on `Fin n`: the operations `t` with `t (e a) (e b) = e (a * b)`
for a bijection `e : G ≃ Fin n`. -/
private def mulTables : Set (Fin n → Fin n → Fin n) :=
  {t | ∃ e : G ≃ Fin n, ∀ a b, t (e a) (e b) = e (a * b)}

variable (n) in
private lemma mulTables_congr (e : G ≃* H) : mulTables G n = mulTables H n := by
  refine Set.ext fun t ↦ ⟨fun ⟨f, hf⟩ ↦ ⟨e.symm.toEquiv.trans f, fun a b ↦ ?_⟩,
    fun ⟨f, hf⟩ ↦ ⟨e.toEquiv.trans f, fun a b ↦ ?_⟩⟩ <;>
  simp [hf]

private lemma nonempty_mulEquiv_of_mem_mulTables {t : Fin n → Fin n → Fin n}
    (hG : t ∈ mulTables G n) (hH : t ∈ mulTables H n) : Nonempty (G ≃* H) := by
  rcases hG with ⟨f, hf⟩
  rcases hH with ⟨g, hg⟩
  refine ⟨.mk' (f.trans g.symm) fun a b ↦ ?_⟩
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, ← hf, g.symm_apply_eq, ← hg,
    g.apply_symm_apply, g.apply_symm_apply]

variable (G) in
private lemma mulTables_nonempty [Finite G] : (mulTables G (Nat.card G)).Nonempty :=
  ⟨fun a b ↦ Finite.equivFin G ((Finite.equivFin G).symm a * (Finite.equivFin G).symm b),
    Finite.equivFin G, fun a b ↦ by simp⟩

/-- **There are positive integers that distinguish the finite groups of each order up to
isomorphism**: for instance one more than the least code of a multiplication table of the group on
`{0, …, n - 1}`, for a fixed injective coding of the finitely many such tables. -/
lemma exists_isSmallGroupIdentification :
    ∃ d : ∀ (G : Type u) [Group G] [Finite G], ℕ, IsSmallGroupIdentification Set.univ d := by
  choose c hc using fun n ↦ exists_injective_nat (Fin n → Fin n → Fin n)
  refine ⟨fun G _ _ ↦ sInf (c (Nat.card G) '' mulTables G (Nat.card G)) + 1,
    fun G _ _ _ ↦ Nat.succ_pos _, fun G H _ _ _ _ _ h ↦ ⟨fun hGH ↦ ?_, fun ⟨e⟩ ↦ ?_⟩⟩
  · dsimp only at hGH
    rw [← h, Nat.add_right_cancel_iff] at hGH
    rcases Nat.sInf_mem <| (mulTables_nonempty G).image (c (Nat.card G)) with ⟨t, ht, htG⟩
    rcases Nat.sInf_mem <| (h ▸ mulTables_nonempty H).image (c (Nat.card G)) with ⟨t', ht', htH⟩
    rw [hc (Nat.card G) <| htG.trans <| hGH.trans htH.symm] at ht
    exact nonempty_mulEquiv_of_mem_mulTables ht ht'
  · dsimp only
    rw [← h, mulTables_congr _ e]

/-- **Labellings exist** (LMFDB `group.label`): for instance the labels `N.d` whose second parts
are positive integers distinguishing the finite groups of each order up to isomorphism. -/
lemma exists_isLabelling : ∃ ℓ : ∀ (G : Type u) [Group G] [Finite G], Label, IsLabelling ℓ := by
  rcases exists_isSmallGroupIdentification.{u} with ⟨d, hd, hd'⟩
  exact ⟨fun G _ _ ↦ ⟨Nat.card G, .smallGroupId (d G)⟩, fun G _ _ ↦ ⟨rfl, hd G trivial⟩,
    fun G H _ _ _ _ hG h ↦ by simpa using hd' G H hG h⟩

end Group
