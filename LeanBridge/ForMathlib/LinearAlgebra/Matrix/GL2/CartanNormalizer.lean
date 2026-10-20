import Mathlib.Algebra.Field.ZMod
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Cartan

/-!
# Normalizers of Cartan subgroups of `GL₂(𝔽_p)`, in the LMFDB's convention

For `p > 2` the LMFDB's normalizer of a Cartan subgroup of `GL₂(𝔽_p)` is the normalizer in
`GL₂(𝔽_p)` of a (split, non-split) Cartan subgroup. For `p = 2` the Cartan subgroups of `GL₂(𝔽₂)`
are normal, and the LMFDB instead calls a subgroup containing a Cartan subgroup with index `2` a
normalizer of it: a subgroup of order `2` in the split case, all of `GL₂(𝔽₂)` in the non-split
case. The LMFDB knowls also call these groups maximal subgroups of `GL₂(𝔽_p)`; this is not part
of the definitions below, as it fails for the normalizer of a split Cartan subgroup when `p = 3`
or `p = 5`. For `p = 3` that group has order `8` and lies in a Sylow `2`-subgroup of order `16`;
for `p = 5` its image in `PGL₂(𝔽₅) ≃ S₅` is a dihedral group of order `8`, which lies in a
subgroup `S₄`, so the group lies in a subgroup of order `96`.

## Main definitions

* `Matrix.GeneralLinearGroup.IsCartanNormalizer` (LMFDB `gl2.normalizer_cartan`).
* `Matrix.GeneralLinearGroup.IsSplitCartanNormalizer` (LMFDB `gl2.normalizer_split_cartan`).
* `Matrix.GeneralLinearGroup.IsNonsplitCartanNormalizer` (LMFDB `gl2.normalizer_nonsplit_cartan`).
-/

namespace Matrix.GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] (H : Subgroup (GL (Fin 2) (ZMod p)))

/-- A subgroup `H` of `GL₂(𝔽_p)` is the **normalizer of a Cartan subgroup** (LMFDB
`gl2.normalizer_cartan`) in the LMFDB's convention: for `p > 2`, `H` is the normalizer in
`GL₂(𝔽_p)` of a Cartan subgroup; for `p = 2`, where Cartan subgroups are normal, `H` contains a
Cartan subgroup with index `2`. -/
def IsCartanNormalizer : Prop :=
  ∃ C : Subgroup (GL (Fin 2) (ZMod p)), IsCartanSubgroup C ∧
    if p = 2 then C ≤ H ∧ C.relIndex H = 2 else H = Subgroup.normalizer (C : Set _)

/-- A subgroup `H` of `GL₂(𝔽_p)` is the **normalizer of a split Cartan subgroup** (LMFDB
`gl2.normalizer_split_cartan`): for `p > 2`, `H` is the normalizer in `GL₂(𝔽_p)` of a split Cartan
subgroup; for `p = 2`, where the split Cartan subgroup is trivial and hence normal, `H` contains a
split Cartan subgroup with index `2`, so has order `2`. -/
def IsSplitCartanNormalizer : Prop :=
  ∃ C : Subgroup (GL (Fin 2) (ZMod p)), IsSplitCartanSubgroup C ∧
    if p = 2 then C ≤ H ∧ C.relIndex H = 2 else H = Subgroup.normalizer (C : Set _)

/-- A subgroup `H` of `GL₂(𝔽_p)` is the **normalizer of a non-split Cartan subgroup** (LMFDB
`gl2.normalizer_nonsplit_cartan`): for `p > 2`, `H` is the normalizer in `GL₂(𝔽_p)` of a non-split
Cartan subgroup; for `p = 2`, `H` contains a non-split Cartan subgroup with index `2`, which forces
`H` to be all of `GL₂(𝔽₂)`. -/
def IsNonsplitCartanNormalizer : Prop :=
  ∃ C : Subgroup (GL (Fin 2) (ZMod p)), IsNonsplitCartanSubgroup C ∧
    if p = 2 then C ≤ H ∧ C.relIndex H = 2 else H = Subgroup.normalizer (C : Set _)

end Matrix.GeneralLinearGroup
