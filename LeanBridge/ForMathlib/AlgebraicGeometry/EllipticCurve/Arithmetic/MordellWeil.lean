import LeanBridge.ForMathlib.GroupTheory.FiniteAbelian.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated

/-!
# The weak Mordell–Weil theorem and the structure of `E(K)`

Let `E` be an elliptic curve over a number field `K`, given by any Weierstrass equation. By the
Mordell–Weil theorem (Tau Ceti's `WeierstrassCurve.Affine.fg_point_of_numberField`, LMFDB
`ec.mordell_weil_theorem`), the group `E(K)` is finitely generated. This file draws two classical
consequences of finite generation.

* The weak Mordell–Weil theorem: `E(K)/nE(K)` is finite for every `n ≠ 0`. Tau Ceti proves the case
  `n = 2` for equations `y² = f(x)` over the fraction field of a Dedekind domain, under class group
  and unit hypotheses, as the input of the descent
  (`WeierstrassCurve.Affine.finiteIndex_range_nsmulAddMonoidHom_two`); over a number field it holds
  for every `n` and every Weierstrass equation.
* The structure theorem `E(K) ≅ ℤ ^ r × E(K)_tors`, where `r = Module.finrank ℤ E(K)` is the rank
  of `E(K)` (LMFDB `ec.rank`) and `E(K)_tors` is its torsion subgroup.

## Main results

* `WeierstrassCurve.Affine.finiteIndex_range_nsmulAddMonoidHom_of_numberField`: **the weak
  Mordell–Weil theorem**, `E(K)/nE(K)` is finite for every `n ≠ 0`.
* `WeierstrassCurve.Affine.nonempty_addEquiv_pi_int_prod_torsion_of_numberField`: **the
  Mordell–Weil theorem** in structure form, `E(K) ≃+ ℤ ^ r × E(K)_tors` with `r` the rank of `E(K)`.
-/

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] (W : Affine K) [W.IsElliptic]

/-- **The weak Mordell–Weil theorem**: for an elliptic curve `E` over a number field `K`, given by
any Weierstrass equation, `E(K)/nE(K)` is finite for every `n ≠ 0`. -/
lemma finiteIndex_range_nsmulAddMonoidHom_of_numberField {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := W.Point) n).range.FiniteIndex :=
  have : AddGroup.FG W.Point := fg_point_of_numberField
  AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg _ hn

/-- **The Mordell–Weil theorem** in structure form: for an elliptic curve `E` over a number field
`K`, `E(K) ≃+ ℤ ^ r × E(K)_tors`, where `r = Module.finrank ℤ E(K)` is the rank of `E(K)` and
`E(K)_tors` is its torsion subgroup. -/
lemma nonempty_addEquiv_pi_int_prod_torsion_of_numberField :
    Nonempty (W.Point ≃+ (Fin (Module.finrank ℤ W.Point) → ℤ) × AddCommGroup.torsion W.Point) :=
  AddCommGroup.nonempty_addEquiv_pi_int_prod_torsion W.Point

end WeierstrassCurve.Affine
