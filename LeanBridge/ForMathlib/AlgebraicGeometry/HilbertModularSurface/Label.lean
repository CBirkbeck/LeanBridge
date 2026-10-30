import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.Level
import LeanBridge.ForMathlib.NumberTheory.NumberField.Label

/-!
# Labels of Hilbert modular surfaces

Let `F` be a real quadratic field, `𝔟` a nonzero fractional ideal of `F` (the component ideal) and
`𝔑` a nonzero ideal of `𝒪_F` (the level). The LMFDB labels a Hilbert modular surface by `F-N-b-t`,
where `F` is the label `d.r.D.i` of the number field `F`, `N` and `b` are the labels of the ideals
`𝔑` and `𝔟`, and `t`, which is `sl-0` or `gl-0`, is the type of its congruence subgroup.

The knowl does not say which congruence subgroups the two types stand for. We read them as the two
families of surfaces that the LMFDB's database prioritises (LMFDB `hmsurface.standard_hmsurfaces`):
`gl-0` for `X_0(𝔑)_𝔟`, the surface of the subgroup `Γ₀(𝔑)_𝔟` of `GL⁺(𝒪_F ⊕ 𝔟)` (LMFDB
`hmsurface.x0`), and `sl-0` for `X_0^1(𝔑)_𝔟`, that of the subgroup `Γ₀¹(𝔑)_𝔟` of `SL(𝒪_F ⊕ 𝔟)`
(LMFDB `hmsurface.x01`). Both groups are the inverse images of the upper triangular matrices
modulo `𝔑`, that is, the matrices `(a, b; c, d)` of the group with `c ∈ 𝔑𝔟`, which is
`HilbertModularGroup.gammaZero` of the group.

The label `d.r.D.i` of a number field records its degree `d`, its number `r` of real places and the
absolute value `D` of its discriminant, followed by the index `i` of the field among those with the
same `d`, `r` and `D`; for a real quadratic field it is `2.2.D.1`, as a quadratic field is
determined by its discriminant (not formalised). The label `N.i` of a nonzero ideal of `𝒪_F`
records its norm `N`, followed by the index `i` of the ideal among those of the same norm, which
follows an LMFDB ordering (depending on the LMFDB's choice of a defining polynomial of `F`) that the
knowl does not specify: a database numbering, with nothing to formalise in it. The mathematically
defined part of the label is the prefix `d.r.D` of the label of `F`, which is
`NumberField.labelPrefix F`, determines `d`, `r` and `D` (`NumberField.labelPrefix_eq_iff`) and
thereby the label of a quadratic field, the norms of `𝔑` and `𝔟`, and the type.

Ideal labels exist only for nonzero ideals of `𝒪_F`, while the component ideal may be fractional
(LMFDB `hmsurface.congruence_subgroup`, `hmsurface.component_ideal`), so the label requires an
integral `𝔟`. The norm of `𝔟` is taken here to be the rational number `FractionalIdeal.absNorm 𝔟`,
which is the norm of `𝔟` when `𝔟` is integral (`FractionalIdeal.coeIdeal_absNorm`).

## Main definitions

* `HilbertModularGroup.SurfaceType` (LMFDB `hmsurface.label`): the type `sl-0` or `gl-0`.
* `HilbertModularGroup.SurfaceType.toLabel`: the string `sl-0` or `gl-0` of a type.
* `HilbertModularGroup.SurfaceType.group`: the Hilbert modular group `SL(𝒪_F ⊕ 𝔟)` or
  `GL⁺(𝒪_F ⊕ 𝔟)` of a type.
* `HilbertModularGroup.SurfaceType.congruenceSubgroup` (LMFDB `hmsurface.label`,
  `hmsurface.x0`, `hmsurface.x01`): the congruence subgroup `Γ₀¹(𝔑)_𝔟` or `Γ₀(𝔑)_𝔟` of a type.
* `HilbertModularGroup.SurfaceLabel` (LMFDB `hmsurface.label`): the mathematically defined part of
  the label of a Hilbert modular surface.
* `HilbertModularGroup.surfaceLabel` (LMFDB `hmsurface.label`): that of the surface of the
  congruence subgroup of a type.

## Main results

* `HilbertModularGroup.SurfaceType.isCongruenceSubgroup_congruenceSubgroup`: `Γ₀¹(𝔑)_𝔟` and
  `Γ₀(𝔑)_𝔟` are congruence subgroups.
-/

open NumberField

open scoped nonZeroDivisors

namespace HilbertModularGroup

variable {F : Type*} [Field F] (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (𝔑 : Ideal (𝓞 F))

/-- The **type** `t` (LMFDB `hmsurface.label`) of the congruence subgroup of a Hilbert modular
surface in the LMFDB: `sl-0` for the subgroup `Γ₀¹(𝔑)_𝔟` of `SL(𝒪_F ⊕ 𝔟)` (LMFDB `hmsurface.x01`),
and `gl-0` for the subgroup `Γ₀(𝔑)_𝔟` of `GL⁺(𝒪_F ⊕ 𝔟)` (LMFDB `hmsurface.x0`), the two families
of LMFDB `hmsurface.standard_hmsurfaces`. The label knowl does not say which groups the types stand
for: this reading matches the names of the types with these two families. -/
inductive SurfaceType
  /-- The type `sl-0`: the congruence subgroup `Γ₀¹(𝔑)_𝔟` of `SL(𝒪_F ⊕ 𝔟)`. -/
  | sl
  /-- The type `gl-0`: the congruence subgroup `Γ₀(𝔑)_𝔟` of `GL⁺(𝒪_F ⊕ 𝔟)`. -/
  | gl

variable (t : SurfaceType)

namespace SurfaceType

/-- The string `sl-0` or `gl-0` of a type, as it appears in the label. -/
def toLabel : SurfaceType → String
  | sl => "sl-0"
  | gl => "gl-0"

/-- The Hilbert modular group of a type: `SL(𝒪_F ⊕ 𝔟)` for `sl-0` and `GL⁺(𝒪_F ⊕ 𝔟)` for
`gl-0`. -/
noncomputable def group : SurfaceType → Subgroup (GL (Fin 2) F)
  | sl => HilbertModularGroup.sl 𝔟
  | gl => glPlus 𝔟

/-- The **congruence subgroup** of level `𝔑` of a type (LMFDB `hmsurface.label`, `hmsurface.x0`,
`hmsurface.x01`): the inverse image of the upper triangular matrices modulo `𝔑` in the Hilbert
modular group of the type, that is, its matrices `(a, b; c, d)` with `c ∈ 𝔑𝔟`. It is `Γ₀¹(𝔑)_𝔟`
in `SL(𝒪_F ⊕ 𝔟)` for `sl-0`, and `Γ₀(𝔑)_𝔟` in `GL⁺(𝒪_F ⊕ 𝔟)` for `gl-0`. -/
noncomputable def congruenceSubgroup : Subgroup (GL (Fin 2) F) :=
  gammaZero 𝔟 (t.group 𝔟) 𝔑

/-- **`Γ₀¹(𝔑)_𝔟` and `Γ₀(𝔑)_𝔟` are congruence subgroups**, of `SL(𝒪_F ⊕ 𝔟)` and
`GL⁺(𝒪_F ⊕ 𝔟)` respectively, for a nonzero ideal `𝔑`. -/
lemma isCongruenceSubgroup_congruenceSubgroup (h𝔑 : 𝔑 ≠ ⊥) :
    IsCongruenceSubgroup 𝔟 (t.congruenceSubgroup 𝔟 𝔑) :=
  isCongruenceSubgroup_gammaZero 𝔟 _ 𝔑 (by cases t <;> simp [group]) h𝔑

end SurfaceType

/-- The mathematically defined part of the **label** `F-N-b-t` (LMFDB `hmsurface.label`) of a
Hilbert modular surface: the prefix `d.r.D` of the label `d.r.D.i` of `F`, which records its degree
`d`, its number `r` of real places and the absolute value `D` of its discriminant, the norms of the
level `𝔑` and of the component ideal `𝔟`, from their labels, and the type `t`. The index `i`
completing the label of `F` is `1` for a real quadratic field, and the indices completing the
labels of `𝔑` and `𝔟` are database numberings. -/
structure SurfaceLabel where
  /-- The prefix `d.r.D` of the label of `F` (`NumberField.labelPrefix`), which determines `d`,
  `r` and `D` (`NumberField.labelPrefix_eq_iff`). -/
  fieldLabelPrefix : String
  /-- The norm of the level `𝔑`. -/
  levelNorm : ℕ
  /-- The norm of the component ideal `𝔟`, which the label requires to be integral. -/
  componentNorm : ℚ
  /-- The type `t`, `sl-0` or `gl-0`. -/
  type : SurfaceType

variable [NumberField F]

/-- The mathematically defined part of the **label** `F-N-b-t` (LMFDB `hmsurface.label`) of the
Hilbert modular surface of the congruence subgroup `t.congruenceSubgroup 𝔟 𝔑` of the type `t`: the
label prefix `d.r.D` of `F`, which records its degree, its number of real places and its absolute
discriminant, the norms of `𝔑` and `𝔟` (the rational norm `FractionalIdeal.absNorm 𝔟`, which is
that of the ideal `𝔟` when `𝔟` is integral, as the label requires), and `t`. -/
noncomputable def surfaceLabel : SurfaceLabel where
  fieldLabelPrefix := labelPrefix F
  levelNorm := Ideal.absNorm 𝔑
  componentNorm := FractionalIdeal.absNorm 𝔟
  type := t

end HilbertModularGroup
