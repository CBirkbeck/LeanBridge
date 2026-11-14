import LeanBridge.ForMathlib.GroupTheory.StemExtension
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow

/-!
# Implications between properties of subgroups

Some properties of a subgroup `H` of a group `G` imply others (LMFDB
`group.subgroup_properties_interdependencies`). Mathlib has most of these implications as
instances or lemmas: a characteristic subgroup is normal (`Subgroup.normal_of_characteristic`), a
cyclic group is abelian (`IsCyclic.isMulCommutative`), an abelian group is nilpotent
(`CommGroup.isNilpotent`), its centre being the whole group
(`Subgroup.upperCentralSeries_one_eq_top_iff`), a nilpotent group is solvable
(`IsNilpotent.to_isSolvable`), a Sylow subgroup is a `p`-group (`Sylow.isPGroup`) and a finite
`p`-group is nilpotent (`IsPGroup.isNilpotent`). We add the implications that the LMFDB lists and
Mathlib does not state: a stem subgroup is central (`Subgroup.IsStem.le_center`, beside the
definition), a central subgroup is abelian, and a Sylow subgroup of a finite group is nilpotent. We
also prove the reason that the LMFDB gives for nilpotent groups being solvable: the upper central
series has abelian subquotients.

## Main results

* `Subgroup.isMulCommutative_of_le_center`: a central subgroup is abelian.
* `Subgroup.isMulCommutative_upperCentralSeries_succ_quotient`: the subquotients `Z_{n+1} / Z_n`
  of the upper central series are abelian.
* `Sylow.isNilpotent`: a Sylow subgroup of a finite group is nilpotent.
-/

open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Subgroup

variable {H : Subgroup G}

/-- **A central subgroup is abelian** (LMFDB `group.subgroup_properties_interdependencies`): its
elements commute with the whole group. -/
lemma isMulCommutative_of_le_center (h : H ≤ center G) : IsMulCommutative H :=
  le_centralizer_iff_isMulCommutative.mp <| h.trans <| center_le_centralizer _

/-- **The upper central series has abelian subquotients** (LMFDB
`group.subgroup_properties_interdependencies`), the reason that the LMFDB gives for nilpotent groups
being solvable: the commutator of two elements of `Z_{n+1}` lies in `Z_n`. -/
lemma isMulCommutative_upperCentralSeries_succ_quotient (n : ℕ) :
    IsMulCommutative (upperCentralSeries G (n + 1) ⧸
      (upperCentralSeries G n).subgroupOf (upperCentralSeries G (n + 1))) := by
  refine ⟨⟨fun a b ↦ ?_⟩⟩
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
  have h : ⁅(y : G)⁻¹, (x : G)⁻¹⁆ ∈ upperCentralSeries G n :=
    mem_upperCentralSeries_succ_iff.mp (inv_mem y.2) _
  simpa [commutatorElement_def, mul_assoc] using h

end Subgroup

/-- **A Sylow subgroup of a finite group is nilpotent** (LMFDB
`group.subgroup_properties_interdependencies`): it is a `p`-group. -/
lemma Sylow.isNilpotent [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) : Group.IsNilpotent P :=
  P.isPGroup.isNilpotent
