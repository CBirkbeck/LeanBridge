import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Integer powers of the units of a subring

For a subring `S` of a field `M`, the integer powers of a unit of `S`, computed in the group `Sˣ`,
are its integer powers in `M`.
-/

namespace Subring

lemma coe_units_zpow {M : Type*} [Field M] (S : Subring M) (u : Sˣ) (z : ℤ) :
    ((u : S) : M) ^ z = (((u ^ z : Sˣ) : S) : M) :=
  ((congrArg Units.val (map_zpow (Units.map S.subtype.toMonoidHom) u z)).trans
    (Units.val_zpow_eq_zpow_val _ z)).symm

end Subring
