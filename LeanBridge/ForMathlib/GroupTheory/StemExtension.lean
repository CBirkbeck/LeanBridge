import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Stem groups and stem extensions

## Main definitions

* `Group.IsStemGroup` (LMFDB `group.stem_group`): a group whose centre lies in its commutator
  subgroup.
* `Subgroup.IsStem` (LMFDB `group.stem_extension`): a stem subgroup, contained in the centre and in
  the commutator subgroup.
* `GroupExtension.IsStem` (LMFDB `group.stem_extension`): a stem extension.
-/

variable {N E G : Type*} [Group N] [Group E] [Group G]

variable (G) in
/-- A group `G` is a **stem group** (LMFDB `group.stem_group`) if its centre is contained in its
commutator subgroup. -/
def Group.IsStemGroup : Prop :=
  Subgroup.center G ≤ commutator G

/-- A subgroup `K` of a group `E` is a **stem subgroup** (LMFDB `group.stem_extension`) if it is
contained in both the centre and the commutator subgroup `commutator E = ⁅⊤, ⊤⁆` of `E`. -/
def Subgroup.IsStem (K : Subgroup E) : Prop :=
  K ≤ center E ⊓ ⁅(⊤ : Subgroup E), ⊤⁆

namespace GroupExtension

/-- An extension `1 → N → E → G → 1` is a **stem extension** (LMFDB `group.stem_extension`) if the
image of `N` is contained in both the centre and the commutator subgroup of `E`, i.e. it is a stem
subgroup of `E`. -/
def IsStem (S : GroupExtension N E G) : Prop :=
  S.inl.range.IsStem

end GroupExtension
