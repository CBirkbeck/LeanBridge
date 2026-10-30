import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.Level
import LeanBridge.ForMathlib.NumberTheory.NumberField.Label

/-!
# Labels of Bianchi newforms

The LMFDB labels a Bianchi newform of level `Γ₀(𝔑)` over an imaginary quadratic field `K` by
`field-level-suffix`. The field is the label `d.r.D.i` of `K`, which records its degree `d`, its
number `r` of real places and the absolute value `D` of its discriminant, followed by its index `i`
among the fields with the same `d`, `r` and `D`; for an imaginary quadratic field it is `2.0.D.1`,
as such a field is determined by its discriminant. The level is the label `N.i` of the ideal `𝔑`,
which records its norm `N`, followed by the index `i` of `𝔑` among the ideals of the same norm. The
suffix is a string of letters giving the index of the newform among the newforms of level `𝔑`,
sorted by dimension and then lexicographically by their Fourier coefficients, indexed by the
integral ideals in their standard order.

The index of `𝔑` among the ideals of the same norm, and the standard order of ideals on which the
suffix rests, follow the LMFDB's labelling of ideals, which depends on the LMFDB's choice of a
defining polynomial and which the knowl does not specify: they are database numberings, with
nothing to formalise in them. Bianchi newforms are moreover not formalised (only Bianchi modular
forms and their spaces are). The mathematically defined part of the label is the prefix `d.r.D` of
the label of `K`, which is `NumberField.labelPrefix K` and determines `d`, `r` and `D`
(`NumberField.labelPrefix_eq_iff`), and `N`; for imaginary quadratic `K`, the prefix determines the
whole label of `K`. That an imaginary quadratic field is determined by its discriminant is not
formalised. The knowl's example, the level `(219 - 117i)` of norm `219² + 117² = 61650` over `ℚ(i)`
of discriminant `-4`, is consistent with its label `2.0.4.1-61650.6-a`.

## Main definitions

* `HyperbolicThreeSpace.BianchiLabel` (LMFDB `mf.bianchi.labels`): the mathematically defined part
  of the label of a Bianchi newform.
* `HyperbolicThreeSpace.bianchiLabel` (LMFDB `mf.bianchi.labels`): that of a Bianchi newform of
  level `Γ₀(𝔑)` (`Ideal.gamma0GL`).
-/

open Module NumberField

namespace HyperbolicThreeSpace

/-- The mathematically defined part of the **label** `field-level-suffix` (LMFDB
`mf.bianchi.labels`) of a Bianchi newform over a field `K`: the prefix `d.r.D` of the label
`d.r.D.i` of `K`, which records its degree `d`, its number `r` of real places and the absolute
value `D` of its discriminant (the label is `2.0.D.1` for imaginary quadratic `K`), and the norm
`N` of the level, from its label `N.i`. The index `i` of the level and the suffix are database
numberings. -/
structure BianchiLabel where
  /-- The prefix `d.r.D` of the label of the base field (`NumberField.labelPrefix`), which
  determines `d`, `r` and `D` (`NumberField.labelPrefix_eq_iff`). -/
  fieldLabelPrefix : String
  /-- The norm `N` of the level. -/
  levelNorm : ℕ

variable {K : Type*} [Field K] [NumberField K] (𝔑 : Ideal (𝓞 K))

/-- The mathematically defined part of the **label** `field-level-suffix` (LMFDB
`mf.bianchi.labels`) of a Bianchi newform of level `Γ₀(𝔑)` (`Ideal.gamma0GL`) over `K`: the label
prefix `d.r.D` of `K`, which records its degree, its number of real places and its absolute
discriminant, and the norm of `𝔑`. -/
noncomputable def bianchiLabel : BianchiLabel where
  fieldLabelPrefix := labelPrefix K
  levelNorm := Ideal.absNorm 𝔑

variable [IsTotallyComplex K] in
lemma fieldLabelPrefix_bianchiLabel : (bianchiLabel 𝔑).fieldLabelPrefix = toString (finrank ℚ K) ++
    ".0." ++ toString (discr K).natAbs := by
  simp only [bianchiLabel, labelPrefix, IsTotallyComplex.nrRealPlaces_eq_zero, String.append_assoc]
  rfl

end HyperbolicThreeSpace
