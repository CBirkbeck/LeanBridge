import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Order.PiLex
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Class

/-!
# The LMFDB label of an elliptic curve over `ℚ`

The LMFDB label of an elliptic curve `E` over `ℚ`, such as `11.a1` or `10050.bf2`, is the
concatenation of three components.

1. The conductor `N` of `E`, in decimal: the norm of the algorithmic conductor
   `WeierstrassCurve.algorithmicConductor`, which is the conductor by Ogg's formula.
2. The isogeny class label: the isogeny class index of `E` in base `26`, with the letters `a`, …,
   `z` as digits. The isogeny classes of conductor `N` are sorted lexicographically by the
   `q`-expansions of their modular forms, that is, by the coefficients `(aₙ)` of the `L`-series of
   their curves (`WeierstrassCurve.LFunction`), and the isogeny class index of `E` is the position
   of its class in that order, counted from `0`.
3. The isomorphism class index: the curves in the isogeny class of `E` are sorted lexicographically
   by the coefficient vectors `[a₁, a₂, a₃, a₄, a₆]` of their reduced minimal equations
   (`WeierstrassCurve.reducedMinimalModel`), and the isomorphism class index of `E` is its position
   in that order, counted from `1`.

The two indices are defined here as the numbers of isogeny classes, and of isomorphism classes,
that come before `E`. That they are finite and give the LMFDB ordering rests on theorems not proved
here: the isogeny classes of a given conductor are finite in number (Shafarevich), isogenous
curves have the same conductor and `L`-series, and non-isogenous curves different `L`-series
(Faltings).

## Main definitions

* `WeierstrassCurve.coeffVector`: the coefficient vector `[a₁, a₂, a₃, a₄, a₆]` of a Weierstrass
  curve.
* `WeierstrassCurve.lmfdbIsogenyClassIndex` (LMFDB `ec.q.lmfdb_label`): the isogeny class index.
* `WeierstrassCurve.isogenyClassLetters` (LMFDB `ec.q.lmfdb_label`): the base `26` encoding of an
  isogeny class index by the letters `a`, …, `z`.
* `WeierstrassCurve.lmfdbIsomorphismClassIndex` (LMFDB `ec.q.lmfdb_label`): the isomorphism class
  index.
* `WeierstrassCurve.lmfdbLabel` (LMFDB `ec.q.lmfdb_label`): the LMFDB label.
-/

namespace WeierstrassCurve

/-- The **coefficient vector** `[a₁, a₂, a₃, a₄, a₆]` (LMFDB `ec.weierstrass_coeffs`) of a
Weierstrass curve `W`. -/
def coeffVector {R : Type*} (W : WeierstrassCurve R) : Fin 5 → R :=
  ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- The **isogeny class index** (LMFDB `ec.q.lmfdb_label`) of an elliptic curve `E` over `ℚ`: the
number of isogeny classes of elliptic curves over `ℚ` of the same conductor as `E` that come before
the isogeny class of `E` when the classes are sorted lexicographically by the coefficients `(aₙ)` of
the `L`-series of their curves (`WeierstrassCurve.LFunction`), which are the `q`-expansion
coefficients of their modular forms. -/
noncomputable def lmfdbIsogenyClassIndex : ℕ :=
  Set.ncard {S : Set (IsomorphismClass ℚ) | ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic),
    S = E'.isogenyClass ∧ Ideal.absNorm (algorithmicConductor ℤ E') =
    Ideal.absNorm (algorithmicConductor ℤ E) ∧ toLex ⇑E'.LFunction < toLex ⇑E.LFunction}

/-- The **isogeny class label** (LMFDB `ec.q.lmfdb_label`) of an isogeny class index `n`: `n` in
base `26` with the letters `a`, …, `z` as the digits `0`, …, `25`, so that `0`, `25`, `26` and `31`
are `a`, `z`, `ba` and `bf`. -/
def isogenyClassLetters (n : ℕ) : String :=
  if n = 0 then "a"
  else String.ofList <| (Nat.digits 26 n).reverse.map (Char.ofNat <| 'a'.toNat + ·)

/-- The **isomorphism class index** (LMFDB `ec.q.lmfdb_label`) of an elliptic curve `E` over `ℚ`:
the position, counted from `1`, of `E` in its isogeny class when the curves of the class are sorted
lexicographically by the coefficient vectors `[a₁, a₂, a₃, a₄, a₆]` (`coeffVector`) of their
reduced minimal equations (`WeierstrassCurve.reducedMinimalModel`). -/
noncomputable def lmfdbIsomorphismClassIndex : ℕ :=
  1 + Set.ncard {c ∈ E.isogenyClass | ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic), ⟦E'⟧ = c ∧
    toLex E'.reducedMinimalModel.coeffVector < toLex E.reducedMinimalModel.coeffVector}

/-- The **LMFDB label** (LMFDB `ec.q.lmfdb_label`) of an elliptic curve `E` over `ℚ`: the conductor
of `E` in decimal, a dot, the isogeny class label (`isogenyClassLetters` of
`lmfdbIsogenyClassIndex`), and the isomorphism class index (`lmfdbIsomorphismClassIndex`) in
decimal, as in `11.a1` or `10050.bf2`. -/
noncomputable def lmfdbLabel : String :=
  toString (Ideal.absNorm (algorithmicConductor ℤ E)) ++ "." ++
    isogenyClassLetters E.lmfdbIsogenyClassIndex ++ toString E.lmfdbIsomorphismClassIndex

lemma isogenyClassLetters_zero : isogenyClassLetters 0 = "a" :=
  rfl

lemma one_le_lmfdbIsomorphismClassIndex : 1 ≤ E.lmfdbIsomorphismClassIndex :=
  Nat.le_add_right 1 _

end WeierstrassCurve
