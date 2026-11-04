import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform

/-!
# The newform `Δ`

The discriminant `Δ`, a normalised Hecke eigenform of level one and weight twelve (Tau Ceti's
`TauCeti.discriminantEigenform`), is a newform, as every cusp form of level one is new.

## Main definitions

* `HeckeRing.GL2.deltaNewform`: the newform `Δ`.
-/

open TauCeti

namespace HeckeRing.GL2

/-- The **newform `Δ`** of level one and weight twelve, from Tau Ceti's `discriminantEigenform`. -/
noncomputable def deltaNewform : Newform 1 12 where
  toEigenformAwayFromLevel := discriminantEigenform.toEigenformAwayFromLevel
  isNew := Submodule.eq_top_iff'.mp (cuspFormsNew_one 12) _
  isNorm := ModularForm.discriminant_qExpansion_coeff_one

end HeckeRing.GL2
