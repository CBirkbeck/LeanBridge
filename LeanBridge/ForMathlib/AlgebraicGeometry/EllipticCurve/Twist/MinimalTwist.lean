import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Order.PiLex
import Mathlib.Order.Prod.Lex.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Twist.Basic

/-!
# Minimal twists of elliptic curves over `ℚ`

The quadratic twists of an elliptic curve `E` over `ℚ` are the curves isomorphic over `ℚ` to its
twists `E^(d)` by `d ∈ ℚ*`, which become isomorphic to `E` over `ℚ(√d)`. Among them, the minimal
quadratic twist of `E` is determined in the LMFDB by the following steps.

1. Its conductor is minimal among the quadratic twists of `E`.
2. Among the quadratic twists of minimal conductor, the coefficients `(aₙ)` of its `L`-series
   (`WeierstrassCurve.LFunction`) are lexicographically minimal; equivalently, its isogeny class
   comes first in the LMFDB labelling. When `E` has no complex multiplication, this determines a
   unique curve.
3. Otherwise there are two such curves, and the absolute value of its minimal discriminant is the
   least of the two.
4. The two curves have the same minimal discriminant only for `j(E) = 66³`, where the minimal
   quadratic twist is the curve `32.a1`, `y² = x³ - 11x - 14`.

Steps 1 to 3 minimise the conductor, then the `L`-series, then the absolute value of the minimal
discriminant: they minimise these three invariants ordered lexicographically.

The minimal twist of `E` is its minimal quadratic twist, except when `j(E) = 1728`, where it is the
curve `32.a3`, `y² = x³ - x`, and when `j(E) = 0`, where it is the curve `27.a4`, `y² + y = x³`:
all the curves over `ℚ` with `j`-invariant `1728`, respectively `0`, are quartic, respectively
sextic, twists of each other.

The minimal quadratic twist and the minimal twist are defined here as properties of a curve `E'`,
with the steps above. Their existence and their uniqueness up to isomorphism rest on theorems
that are not proved here: the quadratic twists of minimal conductor lie in finitely many isogeny
classes, and the facts on curves with the same `j`-invariant in an isogeny class quoted in steps 2
and 3.

## Main definitions

* `WeierstrassCurve.IsQuadraticTwist` (LMFDB `ec.twists`): the curve is isomorphic over `ℚ` to a
  quadratic twist `E^(d)` of `E`.
* `WeierstrassCurve.minimalTwistKey` (LMFDB `ec.q.minimal_twist`): the conductor, the `L`-series and
  the absolute value of the minimal discriminant, ordered lexicographically.
* `WeierstrassCurve.IsMinimalQuadraticTwist` (LMFDB `ec.q.minimal_twist`): the curve is a minimal
  quadratic twist of `E`.
* `WeierstrassCurve.IsMinimalTwist` (LMFDB `ec.q.minimal_twist`): the curve is a minimal twist of
  `E`.

## Main results

* `WeierstrassCurve.isQuadraticTwist_self`: a curve is a quadratic twist of itself, by `d = 1`.
* `WeierstrassCurve.IsQuadraticTwist.isTwist`: a quadratic twist is a twist.
-/

namespace WeierstrassCurve

variable {E E' : WeierstrassCurve ℚ}

variable (E E') in
/-- An elliptic curve `E'` over `ℚ` is a **quadratic twist** (LMFDB `ec.twists`) of `E` if it is
isomorphic over `ℚ` to the twist `E^(d)` of `E` by some `d ∈ ℚ*`: the curve
`y² = x³ + d b₂/4 x² + d² b₄/2 x + d³ b₆/4`, which is `E.quadraticTwistOf 0 (-d / 4)`, the twist by
the trace `0` and the norm `-d/4` of `√d / 2`. It becomes isomorphic to `E` over `ℚ(√d)`, and `E` is
the twist by `d = 1`. -/
def IsQuadraticTwist : Prop :=
  ∃ d : ℚ, d ≠ 0 ∧ ∃ C : VariableChange ℚ, C • E' = E.quadraticTwistOf 0 (-d / 4)

variable (E) in
/-- **A curve is a quadratic twist of itself**, by `d = 1`: the quadratic `X² - 1/4` splits. -/
lemma isQuadraticTwist_self : E.IsQuadraticTwist E := by
  rcases E.exists_smul_eq_quadraticTwistOf_add_mul (-(1 / 2)) (1 / 2) (by norm_num) with ⟨C, hC⟩
  exact ⟨1, one_ne_zero, C, by rw [hC]; norm_num⟩

variable [E.IsElliptic]

/-- **A quadratic twist is a twist**: it has the same `j`-invariant. -/
lemma IsQuadraticTwist.isTwist [E'.IsElliptic] (h : E.IsQuadraticTwist E') : E.IsTwist E' := by
  rcases h with ⟨d, hd, C, hC⟩
  have : (E.quadraticTwistOf 0 (-d / 4)).IsElliptic := E.isElliptic_quadraticTwistOf _ _ <| by
    rwa [zero_pow two_ne_zero, zero_sub, mul_div_cancel₀ _ four_ne_zero, neg_neg]
  simp only [isTwist_iff_j_eq, ← variableChange_j E' C, hC, j_quadraticTwistOf]

variable (E) in
/-- The **sorting key** of an elliptic curve `E` over `ℚ` for minimal quadratic twists (LMFDB
`ec.q.minimal_twist`): its conductor, then the sequence `(aₙ)` of the coefficients of its
`L`-series, then the absolute value of its minimal discriminant, ordered lexicographically. The
conductor is the norm of `WeierstrassCurve.algorithmicConductor` and the absolute value of the
minimal discriminant that of `WeierstrassCurve.minimalDiscriminantIdeal`. -/
noncomputable def minimalTwistKey : ℕ ×ₗ Lex (ℕ → ℤ) ×ₗ ℕ :=
  toLex (Ideal.absNorm (algorithmicConductor ℤ E), toLex (toLex ⇑E.LFunction,
    Ideal.absNorm (minimalDiscriminantIdeal ℤ E)))

variable (E E') in
/-- An elliptic curve `E'` over `ℚ` is a **minimal quadratic twist** (LMFDB `ec.q.minimal_twist`)
of an elliptic curve `E` over `ℚ` if it is a quadratic twist of `E` whose sorting key
`minimalTwistKey` is least among the quadratic twists of `E`: its conductor is minimal, then among
those of the same conductor its sequence `(aₙ)` of `L`-series coefficients is lexicographically
minimal, then among those of the same conductor and `L`-series the absolute value of its minimal
discriminant is minimal. Moreover, when `j(E) = 66³`, it is isomorphic to the curve `32.a1`,
`y² = x³ - 11x - 14`, which settles the only tie that the sorting key leaves. -/
def IsMinimalQuadraticTwist : Prop :=
  ∃ _ : E'.IsElliptic, E.IsQuadraticTwist E' ∧ (∀ (E'' : WeierstrassCurve ℚ) (_ : E''.IsElliptic),
    E.IsQuadraticTwist E'' → E'.minimalTwistKey ≤ E''.minimalTwistKey) ∧
    (E.j = 66 ^ 3 → ∃ C : VariableChange ℚ, C • E' = ⟨0, 0, 0, -11, -14⟩)

variable (E E') in
/-- An elliptic curve `E'` over `ℚ` is a **minimal twist** (LMFDB `ec.q.minimal_twist`) of an
elliptic curve `E` over `ℚ` if it is isomorphic to the curve `32.a3`, `y² = x³ - x`, when
`j(E) = 1728` (the **minimal quartic twist**), to the curve `27.a4`, `y² + y = x³`, when `j(E) = 0`
(the **minimal sextic twist**), and if it is a minimal quadratic twist of `E` otherwise. -/
def IsMinimalTwist : Prop :=
  if E.j = 1728 then ∃ C : VariableChange ℚ, C • E' = ⟨0, 0, 0, -1, 0⟩
  else if E.j = 0 then ∃ C : VariableChange ℚ, C • E' = ⟨0, 0, 1, 0, 0⟩
  else E.IsMinimalQuadraticTwist E'

lemma isMinimalTwist_iff_of_j_ne (h₀ : E.j ≠ 0) (h₁₇₂₈ : E.j ≠ 1728) :
    E.IsMinimalTwist E' ↔ E.IsMinimalQuadraticTwist E' := by
  rw [IsMinimalTwist, ite_eq_right h₁₇₂₈, ite_eq_right h₀]

end WeierstrassCurve
