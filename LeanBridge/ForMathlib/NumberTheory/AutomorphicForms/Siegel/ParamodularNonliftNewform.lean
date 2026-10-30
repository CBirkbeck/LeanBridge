import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GritsenkoLift
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularNewform

/-!
# Paramodular newforms which are not Gritsenko lifts

A Hecke eigenform of weight `k` on the paramodular group `K(N)` is a paramodular newform in the
sense of the LMFDB knowl `mf.siegel.newform.paramodular` if it is not a Gritsenko lift and it is
not the image of a paramodular form of lower level under a level raising operator. Unlike the
newforms of `SiegelUpperHalfSpace.IsParamodularNewform`, which are defined by the Petersson
orthogonality to the old forms, these exclude the Gritsenko lifts, and are defined by the images of
the level raising operators rather than their orthogonal complement.

## Main definitions

* `SiegelUpperHalfSpace.IsGritsenkoLift`: `F = Grit(φ)` for a Jacobi cusp form `φ`.
* `SiegelUpperHalfSpace.IsParamodularNonliftNewform` (LMFDB `mf.siegel.newform.paramodular`):
  the paramodular newforms of the knowl.
-/

open ModularForm

namespace SiegelUpperHalfSpace

variable (k : ℤ) (N : ℕ+)

/-- A function `F : ℋ₂ → ℂ` is a **Gritsenko lift** of weight `k` and level `N` if `F = Grit(φ)`
(`SiegelUpperHalfSpace.gritsenkoLift`, LMFDB `mf.siegel.lift.gritsenko`) for a Jacobi cusp form
`φ ∈ J_{k,N}^cusp`. -/
def IsGritsenkoLift (F : SiegelUpperHalfSpace (Fin 2) → ℂ) : Prop :=
  ∃ φ ∈ jacobiCuspFormSpace k N, F = gritsenkoLift k N φ

/-- A **paramodular newform** (LMFDB `mf.siegel.newform.paramodular`) of weight `k` and level `N`:
a Hecke eigenform `F` on the paramodular group `K(N)` (`SiegelUpperHalfSpace.IsHeckeEigenform`)
which is not a Gritsenko lift (`SiegelUpperHalfSpace.IsGritsenkoLift`) and is not the image of a
paramodular cusp form of lower level under a level raising operator
(`SiegelUpperHalfSpace.IsNotFromLowerLevel`). The knowl names the level raising operators `V_m^±`
and `U_m` without defining them; those of Roberts and Schmidt, `θ`, `θ'` and `η` at the primes `p`,
whom it cites, are used here, `θ'` and `η` being identified without their book at hand. As in the
knowl, `F` is a paramodular form, not required to be a cusp form. -/
def IsParamodularNonliftNewform (F : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k)
    (heckeMonoidOf (paramodularLevel N)) (heckeGammaOf (paramodularLevel N))) : Prop :=
  IsHeckeEigenform (TauCeti.detPowerRep ℂ 2 k) F ∧ ¬IsGritsenkoLift k N F ∧
    IsNotFromLowerLevel (TauCeti.detPowerRep ℂ 2 k) N F

end SiegelUpperHalfSpace
