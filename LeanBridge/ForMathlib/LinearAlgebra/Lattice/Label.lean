import TauCeti.LinearAlgebra.IntegralLattice.Level
import TauCeti.NumberTheory.IntegralLattice.Genus

/-!
# Labels of integral lattices

The LMFDB labels an integral lattice `L` by `n.d.N.h.c`: its dimension (rank) `n`, its determinant
`d`, its level `N` and its class number `h`, followed by a counter `c` enumerating the lattices
with the same four invariants. The counter follows an LMFDB enumeration of lattices that the knowl
does not specify: it is a database numbering, with nothing to formalise in it, and so is the
convention of writing `h = 0` when the class number is not available. The mathematically defined
part of the label is `n`, `d`, `N` and `h`.

The class number of `L` (LMFDB `lattice.class_number`) is the number of isometry classes in the
genus of `L`. Every lattice in the genus of `L` has the rank of `L`, so it is isometric to a lattice
in the ambient space `V` of `L` (not proved here), and the classes are counted among the lattices
in `V`. The class number is a cardinality, `0` when the genus contains infinitely many classes; it
is finite for nondegenerate lattices, in particular for the positive definite lattices of the
LMFDB (not proved here). Tau Ceti's `main` branch has the same definition, as
`TauCeti.IntegralLattice.classNumber`, which is not in the pinned version.

## Main definitions

* `TauCeti.IntegralLattice.isometricSetoid`: isometry of integral lattices in `V`.
* `TauCeti.IntegralLattice.genusClassNumber` (LMFDB `lattice.class_number`): the class number.
* `TauCeti.IntegralLattice.Label` (LMFDB `lattice.label`): the mathematically defined part of the
  label of an integral lattice.
* `TauCeti.IntegralLattice.label` (LMFDB `lattice.label`): that of `L`.

## Main results

* `TauCeti.IntegralLattice.SameGenus.genusClassNumber_eq`: lattices of the same genus have the same
  class number.
* `TauCeti.IntegralLattice.Isometry.label_eq`: isometric lattices have the same label.
-/

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L M : IntegralLattice V}

variable (V) in
/-- **Isometry** of integral lattices in `V`, as an equivalence relation: `L` and `M` are related
when there is an isometry from `L` to `M`. Tau Ceti's `main` branch has it as
`TauCeti.IntegralLattice.isometrySetoid`. -/
def isometricSetoid : Setoid (IntegralLattice V) where
  r L M := Nonempty (Isometry L M)
  iseqv := ⟨fun L ↦ ⟨.refl L⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

variable (L) in
/-- The **class number** (LMFDB `lattice.class_number`) of an integral lattice `L` in `V`: the
number of isometry classes of integral lattices in the genus of `L`, counted among the lattices in
`V`, which contain a representative of every class of the genus. It is `0` when the genus contains
infinitely many classes. This is the definition of `TauCeti.IntegralLattice.classNumber` in Tau
Ceti's `main` branch, which the pinned Tau Ceti lacks; it is a stopgap, to be replaced by that
declaration when the pin is bumped. -/
noncomputable def genusClassNumber : ℕ :=
  Nat.card (Quotient.mk (isometricSetoid V) '' {M | L.SameGenus M})

/-- **Lattices of the same genus have the same class number.** -/
lemma SameGenus.genusClassNumber_eq (h : L.SameGenus M) :
    L.genusClassNumber = M.genusClassNumber := by
  rw [genusClassNumber, genusClassNumber,
    (Set.ext fun N ↦ ⟨h.symm.trans, h.trans⟩ : {N | L.SameGenus N} = {N | M.SameGenus N})]

/-- The mathematically defined part `n.d.N.h` of the **label** `n.d.N.h.c` (LMFDB `lattice.label`)
of an integral lattice: its dimension, determinant, level and class number. The counter `c` is a
database numbering. -/
structure Label where
  /-- The dimension `n`, the rank of the lattice. -/
  dimension : ℕ
  /-- The determinant `d` of a Gram matrix. -/
  determinant : ℤ
  /-- The level `N`. -/
  level : ℕ
  /-- The class number `h`. -/
  classNumber : ℕ

variable (L) in
/-- The mathematically defined part `n.d.N.h` of the **label** `n.d.N.h.c` (LMFDB `lattice.label`)
of an integral lattice `L`: its dimension (the rank of its carrier), its determinant
(`TauCeti.IntegralLattice.determinant`), its level (`TauCeti.IntegralLattice.level`) and its class
number (`TauCeti.IntegralLattice.genusClassNumber`). -/
noncomputable def label : Label where
  dimension := finrank ℤ L
  determinant := L.determinant
  level := L.level
  classNumber := L.genusClassNumber

/-- **Isometric lattices have the same label.** -/
lemma Isometry.label_eq (e : Isometry L M) : L.label = M.label := by
  rw [label, label, L.finrank_carrier, M.finrank_carrier, e.determinant_eq, e.level_eq,
    e.sameGenus.genusClassNumber_eq]

end TauCeti.IntegralLattice
