import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Finitely generated abelian groups

A finitely generated abelian group `G` is the product of a free abelian group and of its torsion
subgroup, the free factor having rank `Module.finrank ℤ G`. Mathlib's structure theorem
`AddCommGroup.equiv_free_prod_directSum_zmod` writes `G` as `ℤ ^ n × ⨁ i, ZMod (p i ^ e i)` for
some `n`, but identifies neither `n` with the rank of `G` nor the second factor with its torsion
subgroup.

## Main results

* `AddCommGroup.nonempty_addEquiv_pi_int_prod_torsion`: a finitely generated abelian group `G` is
  isomorphic to `ℤ ^ r × G_tors`, where `r = Module.finrank ℤ G` and `G_tors` is the torsion
  subgroup of `G`.
-/

open Module

namespace AddCommGroup

variable (G : Type*) [AddCommGroup G] [Module.Finite ℤ G]

/-- **A finitely generated abelian group is the product of a free abelian group of its rank and of
its torsion subgroup**: `G ≃+ ℤ ^ r × G_tors`, where `r = Module.finrank ℤ G`. The quotient of `G`
by its torsion subgroup is free of rank `r`, so the quotient map has a section. -/
lemma nonempty_addEquiv_pi_int_prod_torsion :
    Nonempty (G ≃+ (Fin (finrank ℤ G) → ℤ) × torsion G) := by
  rcases projective_lifting_property (Submodule.torsion ℤ G).mkQ LinearMap.id
    (Submodule.torsion ℤ G).mkQ_surjective with ⟨f, hf⟩
  exact ⟨((LinearMap.exact_subtype_mkQ _).splitSurjectiveEquiv
    (Submodule.torsion ℤ G).injective_subtype ⟨f, hf⟩).1.toAddEquiv.trans <|
    AddEquiv.prodComm.trans <| (finBasisOfFinrankEq ℤ _ <| finrank_quotient_eq_of_le_torsion
    le_rfl).equivFun.toAddEquiv.prodCongr <| AddEquiv.addSubgroupCongr Submodule.torsion_int⟩

end AddCommGroup
