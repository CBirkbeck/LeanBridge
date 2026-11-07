import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The general linear group over `ℤ/n` as an automorphism group

The automorphisms of an abelian group `M` killed by `n`, a `ZMod n`-module, are its `ZMod n`-linear
automorphisms, since every additive map between such groups is `ZMod n`-linear. For
`M = (ℤ/n)^ι` these are the invertible matrices, so `GL(ι, ℤ/n)` is the automorphism group of
`C_n^ι`; for `n = p` prime and `ι = Fin m`, `GL(m, p)` is the automorphism group of the abelian
group `C_p^m` (LMFDB `group.general_linear`). Mathlib's `AddAut M` is an additive group, so we
state this for the multiplicative group `C_n^ι = ι → Multiplicative (ZMod n)`, the product of
`|ι|` copies of the cyclic group `C_n = Multiplicative (ZMod n)`; any group isomorphic to it has an
isomorphic automorphism group (`MulAut.congr`).

## Main definitions

* `LinearEquiv.mulEquivMulAutMultiplicative`: the `ZMod n`-linear automorphisms of a module `M` are
  the automorphisms of the group `Multiplicative M`.
* `Matrix.GeneralLinearGroup.mulEquivMulAut` (LMFDB `group.general_linear`): the isomorphism
  `GL(ι, ℤ/n) ≃* Aut(C_n^ι)`, by the action of matrices on exponents.
-/

open LinearMap

variable (n : ℕ)

namespace LinearEquiv

variable (M : Type*) [AddCommGroup M] [Module (ZMod n) M]

/-- The `ZMod n`-linear automorphisms of a `ZMod n`-module `M` are the automorphisms of the group
`Multiplicative M`: every additive automorphism of `M` is `ZMod n`-linear. -/
def mulEquivMulAutMultiplicative : (M ≃ₗ[ZMod n] M) ≃* MulAut (Multiplicative M) where
  toFun f := AddEquiv.toMultiplicative f.toAddEquiv
  invFun φ := (AddEquiv.toMultiplicative.symm φ).toLinearEquiv (ZMod.map_smul _)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end LinearEquiv

namespace Matrix.GeneralLinearGroup

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- **`GL(ι, ℤ/n)` is the automorphism group of `C_n^ι`** (LMFDB `group.general_linear`, where
`n = p` is prime and `ι = Fin m`): the isomorphism `GL(ι, ℤ/n) ≃* Aut(C_n^ι)` letting an invertible
matrix `A` act on `C_n^ι = ι → Multiplicative (ZMod n)` by `v ↦ A *ᵥ v` on exponents. -/
def mulEquivMulAut : GL ι (ZMod n) ≃* MulAut (ι → Multiplicative (ZMod n)) :=
  toLin.trans <| (GeneralLinearGroup.generalLinearEquiv _ _).trans <|
    (LinearEquiv.mulEquivMulAutMultiplicative n _).trans <|
      MulAut.congr (MulEquiv.funMultiplicative ι (ZMod n))

lemma mulEquivMulAut_apply (A : GL ι (ZMod n)) (v : ι → Multiplicative (ZMod n)) (i : ι) :
    mulEquivMulAut n ι A v i =
      Multiplicative.ofAdd (((A : Matrix ι ι (ZMod n)) *ᵥ fun j ↦ (v j).toAdd) i) :=
  rfl

end Matrix.GeneralLinearGroup
