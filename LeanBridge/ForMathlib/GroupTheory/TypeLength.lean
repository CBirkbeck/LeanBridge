import LeanBridge.ForMathlib.GroupTheory.ChiefSeries
import LeanBridge.ForMathlib.GroupTheory.DerivedLength
import LeanBridge.ForMathlib.GroupTheory.FiniteAbelian.AbelianInvariants
import Mathlib.GroupTheory.Nilpotent

/-!
# The type and length of a finite group

The LMFDB describes a finite group `G` by a "Type - length" descriptor:

* "Cyclic" if `G` is cyclic;
* "Abelian - n" if `G` is abelian but not cyclic, `n` the number of invariant factors of `G`;
* "Nilpotent - n" if `G` is nilpotent but not abelian, `n` its nilpotency class;
* "Solvable - n" if `G` is solvable but not nilpotent, `n` its derived length;
* "Simple" if `G` is simple (and not of the above kinds);
* "Non-solvable - n" otherwise, `n` the number of composition factors of `G`.

The number of composition factors is the least length of a composition series of `G`; by the
Jordan–Hölder theorem (not proved here) all composition series have the same length.

## Main definitions

* `Group.TypeLength` (LMFDB `group.type`): the possible descriptors.
* `Group.compositionLength` (LMFDB `group.type`): the number of composition factors.
* `Group.typeLength` (LMFDB `group.type`): the descriptor of a finite group.
-/

namespace Group

/-- The **Type - length** descriptors of finite groups used by the LMFDB (LMFDB `group.type`). -/
inductive TypeLength
  /-- "Cyclic". -/
  | cyclic
  /-- "Abelian - n", `n` the number of invariant factors. -/
  | abelian (n : ℕ)
  /-- "Nilpotent - n", `n` the nilpotency class. -/
  | nilpotent (n : ℕ)
  /-- "Solvable - n", `n` the derived length. -/
  | solvable (n : ℕ)
  /-- "Simple". -/
  | simple
  /-- "Non-solvable - n", `n` the number of composition factors. -/
  | nonsolvable (n : ℕ)
  deriving DecidableEq

variable (G : Type*) [Group G]

/-- The **composition length** of `G` (LMFDB `group.type`), its number of composition factors
("Jordan factors"): the least length of a composition series of `G`, a subnormal series with
simple factors (`0` if there is none). -/
noncomputable def compositionLength : ℕ :=
  sInf {n | ∃ s : Subgroup.SubnormalSeries G, s.IsComposition ∧ s.length = n}

open scoped Classical in
/-- The **Type - length** of a finite group `G` (LMFDB `group.type`): "Cyclic", "Abelian - n" with
`n` the number of invariant factors, "Nilpotent - n" with `n` the nilpotency class, "Solvable - n"
with `n` the derived length, "Simple", or "Non-solvable - n" with `n` the composition length, the
first that applies. -/
noncomputable def typeLength [Finite G] : TypeLength :=
  if IsCyclic G then .cyclic
  else if h : ∀ a b : G, a * b = b * a then
    letI : CommGroup G := { ‹Group G› with mul_comm := h }
    .abelian (AddCommGroup.smithAbelianInvariants (Additive G)).length
  else if IsNilpotent G then .nilpotent (nilpotencyClass G)
  else if IsSolvable G then .solvable (derivedLength G)
  else if IsSimpleGroup G then .simple
  else .nonsolvable (compositionLength G)

end Group
