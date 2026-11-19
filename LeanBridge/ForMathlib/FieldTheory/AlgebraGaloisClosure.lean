import LeanBridge.ForMathlib.NumberTheory.NumberField.Sibling
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableClosure

/-!
# Finiteness and Galois property of `Algebra.galoisClosure`

For a finite separable extension `L / K`, the Galois closure `Algebra.galoisClosure K L` (LMFDB
`nf.galois_closure`), the normal closure of `L` inside `AlgebraicClosure K`, is a finite Galois
extension of `K`. This file records both facts as instances, so that invariants of the Galois
closure of an extension of local fields can be defined. It also compares an intermediate field `E`
of `AlgebraicClosure K / K` with its Galois closure: `E` lies in it, a normal intermediate field
contains the Galois closure of `E` exactly when it contains `E`, and a normal `E` is its own Galois
closure.
-/

namespace Algebra

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

instance [FiniteDimensional K L] : FiniteDimensional K (galoisClosure K L) :=
  galoisClosure_eq_normalClosure (F := K) L ▸ inferInstance

instance [Algebra.IsSeparable K L] : IsGalois K (galoisClosure K L) where
  to_isSeparable := (IntermediateField.isSeparable_adjoin_iff_isSeparable K _).mpr <| by
    rintro - ⟨-, ⟨f, rfl⟩, x, rfl⟩
    exact (Algebra.IsSeparable.isSeparable K x).map f f.injective
  to_normal := (isNormalClosure_galoisClosure (F := K) L).normal

variable {K} {E N : IntermediateField K (AlgebraicClosure K)}

variable (E) in
lemma le_galoisClosure : E ≤ galoisClosure K E :=
  galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure

lemma galoisClosure_le_iff [Normal K N] : galoisClosure K E ≤ N ↔ E ≤ N :=
  galoisClosure_eq_normalClosure (F := K) E ▸ IntermediateField.normalClosure_le_iff_of_normal

variable (E) in
lemma galoisClosure_eq_of_normal [Normal K E] : galoisClosure K E = E :=
  (galoisClosure_le_iff.mpr le_rfl).antisymm (le_galoisClosure E)

end Algebra
