import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Unramified.Field

/-!
# The local algebra of a number field is a product of `ℓ`-adic fields

For a number field `L` and a prime `ℓ`, the local `ℓ`-adic algebra `ℚ_ℓ ⊗ L` (LMFDB
`nf.local_algebra`) is a finite-dimensional `ℚ_ℓ`-algebra, so an Artinian ring, and it is reduced:
it is unramified over `ℚ_ℓ`, being the base change of the separable extension `L / ℚ`. So it is
the product of its quotients `(ℚ_ℓ ⊗ L) / 𝔪` by its maximal ideals, which are fields of finite
degree over `ℚ_ℓ`, that is `ℓ`-adic fields (LMFDB `modlgal.top_slope`).

## Main definitions

* `NumberField.localAlgebraEquivPi` (LMFDB `modlgal.top_slope`): the isomorphism of `ℚ_ℓ ⊗ L`
  with the product of the fields `(ℚ_ℓ ⊗ L) / 𝔪`.

## Main results

* `NumberField.finiteDimensional_localAlgebra_quotient` (LMFDB `modlgal.top_slope`): the factors
  `(ℚ_ℓ ⊗ L) / 𝔪` have finite degree over `ℚ_ℓ`.
-/

open Algebra TensorProduct

namespace NumberField

variable (L : Type*) [Field L] [NumberField L] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The **decomposition of the local algebra** `ℚ_ℓ ⊗ L` of a number field `L` (LMFDB
`nf.local_algebra`, `modlgal.top_slope`) into the product of its quotients `(ℚ_ℓ ⊗ L) / 𝔪` by its
maximal ideals, fields of finite degree over `ℚ_ℓ`: the local algebra is Artinian, being finite
over `ℚ_ℓ`, and reduced, being unramified over `ℚ_ℓ`. -/
noncomputable def localAlgebraEquivPi :
    ℚ_[ℓ] ⊗[ℚ] L ≃ₐ[ℚ_[ℓ]] ∀ 𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L), (ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal :=
  haveI : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  haveI : Algebra.FormallyUnramified ℚ L := .of_isSeparable ℚ L
  haveI : IsReduced (ℚ_[ℓ] ⊗[ℚ] L) := FormallyUnramified.isReduced_of_field ℚ_[ℓ] _
  (IsArtinianRing.equivPi _).restrictScalars ℚ_[ℓ]

/-- **The factors of the local algebra are `ℓ`-adic fields**: each quotient `(ℚ_ℓ ⊗ L) / 𝔪` by a
maximal ideal, a field, has finite degree over `ℚ_ℓ` (LMFDB `modlgal.top_slope`). -/
lemma finiteDimensional_localAlgebra_quotient (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L)) :
    FiniteDimensional ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
  inferInstance

end NumberField
