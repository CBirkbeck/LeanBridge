import LeanBridge.ForMathlib.NumberTheory.NumberField.Place
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion

/-!
# The completion of a field at a place

A place `v` of a field `K` (LMFDB `nf.place`) is a class of equivalent nontrivial absolute values.
Each absolute value `|·|` in the class gives `K` the metric `|x - y|`; two equivalent absolute
values `|·|` and `|·| ^ t` give different metrics, but the same uniform structure: the identity of
`K` is uniformly continuous both ways, since equivalent absolute values define the same topology
(`AbsoluteValue.isEquiv_iff_isHomeomorph`) and an additive map between uniform groups is uniformly
continuous as soon as it is continuous. So the completion `K_v` of `K` at `v` does not depend on the
absolute value chosen in `v`: equivalent absolute values have isomorphic completions, as topological
fields and compatibly with `K`. We define `K_v` as the completion at a chosen representative, a
complete topological field (indeed a normed field).

## Main definitions

* `AbsoluteValue.IsEquiv.uniformEquiv`: equivalent absolute values define the same uniform
  structure on `K`.
* `AbsoluteValue.IsEquiv.completionRingEquiv`: the isomorphism between the completions at
  equivalent absolute values that extends the identity of `K`.
* `AbsoluteValue.Place.absoluteValue`: a chosen absolute value in a place.
* `AbsoluteValue.Place.Completion` (LMFDB `nf.place`): the completion `K_v` of `K` at a place `v`.
* `AbsoluteValue.Place.completionRingEquiv` (LMFDB `nf.place`): the isomorphism between `K_v` and
  the completion of `K` at any absolute value in `v`.

## Main results

* `AbsoluteValue.IsEquiv.isHomeomorph_completionRingEquiv`,
  `AbsoluteValue.Place.isHomeomorph_completionRingEquiv`: these isomorphisms are homeomorphisms.
* `AbsoluteValue.Place.completionRingEquiv_coe`: they restrict to the identity on `K`.
-/

open UniformSpace

namespace AbsoluteValue

variable {K : Type*} [Field K] {v w : AbsoluteValue K ℝ}

lemma IsEquiv.continuous_congr (h : v.IsEquiv w) : Continuous (WithAbs.congr v w (.refl K)) :=
  ((isEquiv_iff_isHomeomorph v w).mp h).continuous

/-- **Equivalent absolute values define the same uniform structure** on `K`: the identity of `K`
is a uniform equivalence between `K` with the metric of `v` and `K` with the metric of `w`. -/
noncomputable def IsEquiv.uniformEquiv (h : v.IsEquiv w) : WithAbs v ≃ᵤ WithAbs w where
  toEquiv := (WithAbs.congr v w (.refl K)).toEquiv
  uniformContinuous_toFun := uniformContinuous_addMonoidHom_of_continuous h.continuous_congr
  uniformContinuous_invFun := uniformContinuous_addMonoidHom_of_continuous h.symm.continuous_congr

/-- The isomorphism between the completions of `K` at equivalent absolute values `v` and `w`: the
extension of the identity of `K` (`IsEquiv.completionRingEquiv_coe`), a homeomorphism
(`IsEquiv.isHomeomorph_completionRingEquiv`). -/
noncomputable def IsEquiv.completionRingEquiv (h : v.IsEquiv w) : v.Completion ≃+* w.Completion :=
  Completion.mapRingEquiv (WithAbs.congr v w (.refl K)) h.continuous_congr h.symm.continuous_congr

lemma IsEquiv.completionRingEquiv_coe (h : v.IsEquiv w) (x : K) : h.completionRingEquiv x = x :=
  Completion.mapRingHom_coe h.continuous_congr _

/-- **Equivalent absolute values have homeomorphic completions**: the isomorphism of completions
extending the identity of `K` is a homeomorphism. -/
lemma IsEquiv.isHomeomorph_completionRingEquiv (h : v.IsEquiv w) :
    IsHomeomorph h.completionRingEquiv :=
  (Homeomorph.mk h.completionRingEquiv.toEquiv Completion.continuous_map
    Completion.continuous_map).isHomeomorph

namespace Place

variable {p : Place K} {hv : v.IsNontrivial}

variable (p) in
/-- A chosen absolute value in the place `p`. -/
noncomputable def absoluteValue : AbsoluteValue K ℝ :=
  (Quotient.out p).1

variable (p) in
lemma isNontrivial_absoluteValue : p.absoluteValue.IsNontrivial :=
  (Quotient.out p).2

variable (p) in
lemma mk_absoluteValue : mk p.absoluteValue p.isNontrivial_absoluteValue = p :=
  Quotient.out_eq p

variable (p) in
/-- The **completion** `K_v` of a field `K` at a place `v` (LMFDB `nf.place`): the completion of `K`
for the metric of a chosen absolute value in `v`. It is a complete topological field, indeed a
normed field, and up to an isomorphism of topological fields extending the identity of `K` it does
not depend on the chosen absolute value (`Place.completionRingEquiv`). -/
abbrev Completion : Type _ :=
  p.absoluteValue.Completion

/-- The isomorphism between the completion `K_v` at a place `v` and the completion of `K` at any
absolute value in `v` (LMFDB `nf.place`): it extends the identity of `K`
(`Place.completionRingEquiv_coe`) and is a homeomorphism
(`Place.isHomeomorph_completionRingEquiv`). -/
noncomputable def completionRingEquiv (hp : mk v hv = p) : p.Completion ≃+* v.Completion :=
  (mk_eq_mk_iff.mp <| p.mk_absoluteValue.trans hp.symm).completionRingEquiv

/-- **The completion at a place does not depend on the absolute value, compatibly with `K`**: the
isomorphism between `K_v` and the completion at an absolute value in `v` restricts to the identity
of `K`. -/
lemma completionRingEquiv_coe (hp : mk v hv = p) (x : K) : completionRingEquiv hp x = x :=
  IsEquiv.completionRingEquiv_coe _ x

/-- **The completion at a place does not depend on the absolute value, as a topological field**:
the isomorphism between `K_v` and the completion at an absolute value in `v` is a homeomorphism. -/
lemma isHomeomorph_completionRingEquiv (hp : mk v hv = p) : IsHomeomorph (completionRingEquiv hp) :=
  IsEquiv.isHomeomorph_completionRingEquiv _

end Place

end AbsoluteValue
