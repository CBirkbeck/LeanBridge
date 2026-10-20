import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Borel
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.CartanNormalizer

/-!
# Exceptional subgroups of `GL₂(𝔽_p)`

A subgroup of `GL₂(𝔽_p)` is exceptional if it does not contain `SL₂(𝔽_p)` and lies neither in a
Borel subgroup nor in the normalizer of a Cartan subgroup, the latter in the LMFDB's convention
(`Matrix.GeneralLinearGroup.IsCartanNormalizer`). By Dickson's classification its image in
`PGL₂(𝔽_p)` is then isomorphic to `A₄`, `S₄` or `A₅`, which is what Sutherland's labels `A4`, `S4`,
`A5` record; the classification itself is not proved here.

## Main definitions

* `Matrix.GeneralLinearGroup.IsExceptionalSubgroup` (LMFDB `gl2.exceptional`).
* `Matrix.GeneralLinearGroup.projectiveImage`: the image of a subgroup of `GL₂(𝔽_p)` in
  `PGL₂(𝔽_p)`.
* `Matrix.GeneralLinearGroup.ExceptionalType` and
  `Matrix.GeneralLinearGroup.HasExceptionalType` (LMFDB `gl2.exceptional`): the three possible
  projective images `A₄`, `S₄`, `A₅`, and the property of having one of them.
-/

open Matrix

namespace Matrix.GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] (H : Subgroup (GL (Fin 2) (ZMod p)))

/-- A subgroup `H` of `GL₂(𝔽_p)` is **exceptional** (LMFDB `gl2.exceptional`) if it does not contain
`SL₂(𝔽_p)` (the kernel of the determinant) and is contained neither in a Borel subgroup nor in the
normalizer of a Cartan subgroup, in the LMFDB's convention (`IsCartanNormalizer`). -/
def IsExceptionalSubgroup : Prop :=
  ¬(GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).ker ≤ H ∧
    (∀ B : Subgroup (GL (Fin 2) (ZMod p)), IsBorelSubgroup B → ¬H ≤ B) ∧
    ∀ N : Subgroup (GL (Fin 2) (ZMod p)), IsCartanNormalizer N → ¬H ≤ N

/-- The image of a subgroup of `GL₂(𝔽_p)` in `PGL₂(𝔽_p)`. -/
def projectiveImage : Subgroup (ProjGenLinGroup (Fin 2) (ZMod p)) :=
  H.map ProjGenLinGroup.mk

/-- The three possible isomorphism types of the image in `PGL₂(𝔽_p)` of an exceptional subgroup,
named as in Sutherland's labels (LMFDB `gl2.exceptional`). -/
inductive ExceptionalType
  /-- The image in `PGL₂(𝔽_p)` is isomorphic to the alternating group `A₄`. -/
  | A4
  /-- The image in `PGL₂(𝔽_p)` is isomorphic to the symmetric group `S₄`. -/
  | S4
  /-- The image in `PGL₂(𝔽_p)` is isomorphic to the alternating group `A₅`. -/
  | A5

/-- A subgroup of `GL₂(𝔽_p)` **has exceptional type** `A4`, `S4` or `A5` (LMFDB `gl2.exceptional`)
if its image in `PGL₂(𝔽_p)` is isomorphic to `A₄`, `S₄` or `A₅` respectively. -/
def HasExceptionalType : ExceptionalType → Prop
  | .A4 => Nonempty (projectiveImage H ≃* alternatingGroup (Fin 4))
  | .S4 => Nonempty (projectiveImage H ≃* Equiv.Perm (Fin 4))
  | .A5 => Nonempty (projectiveImage H ≃* alternatingGroup (Fin 5))

end Matrix.GeneralLinearGroup
