import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# The splitting field of a torus

The splitting field of an algebraic torus `T` over a field `k` is the minimal Galois extension of
`k` over which `T` becomes isomorphic to a power of the multiplicative group `𝔾ₘ`. Tori are Tau
Ceti's `TauCeti.torusCommHopfAlgProperty`, given by their coordinate Hopf algebras `H`, and `T`
splits over an extension `E` when the base change `E ⊗[k] H` is the coordinate ring of a split
torus, `TauCeti.splitTorusCommHopfAlgProperty`.

Extensions are taken inside an algebraic closure `k̄` of `k`, so that the splitting field is a
well-defined intermediate field of `k̄ / k`. It is defined as the infimum of the Galois extensions
of `k` inside `k̄` that split `T`, and `TauCeti.IsTorusSplittingField` says that a given field is
the least of them. That this infimum splits `T` (it is the fixed field of the kernel of the Galois
action on the character lattice of `T`, a finite Galois extension) is not formalised.

## Main definitions

* `TauCeti.IsTorusSplitOver`: a torus splits over an intermediate field of `k̄ / k`.
* `TauCeti.IsTorusSplittingField` (LMFDB `ag.splitting_field`): an intermediate field is the
  splitting field of a torus.
* `TauCeti.torusSplittingField` (LMFDB `ag.splitting_field`): the splitting field of a torus.

## Main results

* `TauCeti.IsTorusSplittingField.torusSplittingField_eq`: a least Galois splitting field is the
  splitting field.
-/

namespace TauCeti

universe u

variable {k : Type u} [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- A torus over `k`, with coordinate Hopf algebra `H`, **splits** over an intermediate field `E` of
`k̄ / k` if it becomes a split torus `𝔾ₘⁿ` over `E`: the base change `E ⊗[k] H` is the coordinate
ring of a split torus of finite rank. -/
def IsTorusSplitOver (E : IntermediateField k (AlgebraicClosure k)) : Prop :=
  splitTorusCommHopfAlgProperty E (FiniteTypeCommHopfAlgCat.baseChange (K := E) H)

/-- An intermediate field `E` of `k̄ / k` is the **splitting field** (LMFDB `ag.splitting_field`) of
a torus `T` over `k`, with coordinate Hopf algebra `H`, if it is the least Galois extension of `k`
inside `k̄` over which `T` becomes isomorphic to a power of `𝔾ₘ`. -/
def IsTorusSplittingField (E : IntermediateField k (AlgebraicClosure k)) : Prop :=
  IsLeast {E' : IntermediateField k (AlgebraicClosure k) | IsGalois k E' ∧ IsTorusSplitOver H E'} E

/-- The **splitting field** (LMFDB `ag.splitting_field`) of a torus `T` over `k`, with coordinate
Hopf algebra `H`: the minimal Galois extension of `k` inside the algebraic closure `k̄` over which
`T` becomes isomorphic to a power of `𝔾ₘ`, defined as the infimum of all such extensions.

For a torus, these extensions are exactly the Galois extensions containing the fixed field of the
kernel of the Galois action on the character lattice, so the infimum is that field (not proved here,
see `TauCeti.IsTorusSplittingField.torusSplittingField_eq`). When `H` is not the coordinate ring of
a torus, nothing splits it and the value is the junk value `k̄`. -/
noncomputable def torusSplittingField : IntermediateField k (AlgebraicClosure k) :=
  sInf {E : IntermediateField k (AlgebraicClosure k) | IsGalois k E ∧ IsTorusSplitOver H E}

variable {H}

/-- **A least Galois splitting field of a torus is its splitting field.** -/
lemma IsTorusSplittingField.torusSplittingField_eq {E : IntermediateField k (AlgebraicClosure k)}
    (hE : IsTorusSplittingField H E) : torusSplittingField H = E :=
  hE.isGLB.sInf_eq

lemma IsTorusSplittingField.unique {E E' : IntermediateField k (AlgebraicClosure k)}
    (hE : IsTorusSplittingField H E) (hE' : IsTorusSplittingField H E') : E = E' :=
  IsLeast.unique hE hE'

end TauCeti
