import LeanBridge.ForMathlib.NumberTheory.LocalField.HerbrandInvariantRams

/-!
# Eisenstein diagrams of Herbrand invariants

Let `I = [s_1, …, s_w]_ε^f` be a Herbrand invariant at a prime `p`, with means `m_k`, and let
`e = ε p ^ w`. The Eisenstein diagram of `I / K` (LMFDB `lf.eisenstein_diagram`), for `K` a
`p`-adic field with residue field of `q` elements, places the point `P_σ = (σ mod e, σ / e)` for
each `σ ≤ e s_w`, standing for the monomial `π^{j + 1} x^i` (`σ = j e + i`) of Monge's generic
Eisenstein polynomial, and sorts these points into types `A, B, C, D, Z` using the bands
`B_k = {m_k ≤ s < s_k}` and the index `k = w - v_p(gcd(i, p ^ w))` of `i = σ mod e`. The
diagram depends only on `I` and on whether `gcd(ε, q ^ f - 1) > 1`. Colours and shapes are display
conventions, and the mass formula `M(I / K) = (q ^ f - 1) ^ α q ^ (f β)` is a theorem of Monge which
is not formalised.

## Main definitions

* `IsNonarchimedeanLocalField.EisensteinPointType`: the types `A, B, C, D, Z` of points.
* `IsNonarchimedeanLocalField.HerbrandInvariant.band` (LMFDB `lf.eisenstein_diagram`): the band
  `B_k`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.pointIndex` (LMFDB `lf.eisenstein_diagram`): the
  index of an integer `i ∈ [0, e)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.pointType` (LMFDB `lf.eisenstein_diagram`): the type
  of the point `P_σ`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsCritical`,
  `IsNonarchimedeanLocalField.HerbrandInvariant.IsNegligible` (LMFDB `lf.eisenstein_diagram`).
* `IsNonarchimedeanLocalField.HerbrandInvariant.eisensteinDiagram` (LMFDB `lf.eisenstein_diagram`):
  the Eisenstein diagram, the type and criticality of each drawn point.
-/

namespace IsNonarchimedeanLocalField

/-- The **types of points** of an Eisenstein diagram (LMFDB `lf.eisenstein_diagram`): the
`D`-point `P_0`, and for `σ > 0` the `A`-, `B`-, `C`- and `Z`-points. -/
inductive EisensteinPointType
  | D | A | B | C | Z
  deriving DecidableEq

namespace HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p)

/-- The ramification index `e = ε p ^ w` of a Herbrand invariant `I = (r_1, …, r_w)_ε^f`. -/
def ramificationIndex : ℕ :=
  I.ε * p ^ I.w

/-- The **band** `B_k` (LMFDB `lf.eisenstein_diagram`) of a Herbrand invariant: the points `(i, s)`
of the strip `R = [0, e) × [0, s_w]` with `m_k ≤ s < s_k` for `1 ≤ k`, and with `s = 0` for
`k = 0`. Its vertical width `s_k - m_k` is the tiny ram `r_k'` (`tinyRam_eq_swanSlope_sub_mean`). -/
def band (k : ℕ) : Set (ℚ × ℚ) :=
  {x | x.1 ∈ Set.Ico 0 (I.ramificationIndex : ℚ) ∧
    if k = 0 then x.2 = 0 else x.2 ∈ Set.Ico (I.mean k) (I.swanSlope k)}

/-- The **index** (LMFDB `lf.eisenstein_diagram`) of an integer `i ∈ [0, e)`:
`w - v_p(gcd(i, p ^ w)) ∈ {0, …, w}` (for `p` prime). -/
def pointIndex (i : ℕ) : ℕ :=
  I.w - padicValNat p (i.gcd (p ^ I.w))

/-- The point `P_σ = (σ mod e, σ / e)` of the spiral of slope `1 / e`. -/
def point (σ : ℕ) : ℚ × ℚ :=
  ((σ % I.ramificationIndex : ℕ), σ / I.ramificationIndex)

/-- The band `B_k` is **geometric** if the small ram `r_k^*` is not an integer, and arithmetic
otherwise. -/
def IsGeometricBand (k : ℕ) : Prop :=
  (I.smallRam k).den ≠ 1

/-- The index `k` is **final** in its segment if `k = w` or `s_k < s_{k + 1}`. -/
def IsFinal (k : ℕ) : Prop :=
  k = I.w ∨ I.swanSlope k < I.swanSlope (k + 1)

open Classical in
/-- The **type** (LMFDB `lf.eisenstein_diagram`) of the point `P_σ` of the Eisenstein diagram of a
Herbrand invariant: `P_0` is the `D`-point; for `σ > 0`, with `s = σ / e` and `k` the index of
`σ mod e`, `P_σ` is a `Z`-point if `s < m_k` (beneath `B_k`), an `A`-point if `s = m_k` (on the
bottom edge of `B_k`) with `B_k` geometric and `k` final, a `B`-point if it is otherwise in `B_k`
(`m_k ≤ s < s_k`), and a `C`-point if `s ≥ s_k` (above `B_k`). For `k = 0`, where `B_0 = {s = 0}`,
every `P_σ` with `σ > 0` is a `C`-point. -/
noncomputable def pointType (σ : ℕ) : EisensteinPointType :=
  if σ = 0 then .D
  else if (I.point σ).2 < I.mean (I.pointIndex (σ % I.ramificationIndex)) then .Z
  else if (I.point σ).2 < I.swanSlope (I.pointIndex (σ % I.ramificationIndex)) then
    if (I.point σ).2 = I.mean (I.pointIndex (σ % I.ramificationIndex)) ∧
        I.IsGeometricBand (I.pointIndex (σ % I.ramificationIndex)) ∧
        I.IsFinal (I.pointIndex (σ % I.ramificationIndex)) then .A
    else .B
  else .C

/-- The point `P_σ` is **critical** (LMFDB `lf.eisenstein_diagram`), for a residue field of `K` with
`q` elements: the `D`-point `P_0` is critical if `gcd(ε, q ^ f - 1) > 1`, and a `C`-point is
critical if it is on the top border `s = s_j` of some band `B_j`, `1 ≤ j ≤ w`. -/
def IsCritical (q σ : ℕ) : Prop :=
  if σ = 0 then 1 < I.ε.gcd (q ^ I.f - 1)
  else I.pointType σ = .C ∧ ∃ j ∈ Finset.Icc 1 I.w, (I.point σ).2 = I.swanSlope j

/-- A `D`- or `C`-point is **negligible** (LMFDB `lf.eisenstein_diagram`) if it is not critical. -/
def IsNegligible (q σ : ℕ) : Prop :=
  (I.pointType σ = .D ∨ I.pointType σ = .C) ∧ ¬I.IsCritical q σ

open Classical in
/-- The **Eisenstein diagram of `I / K`** (LMFDB `lf.eisenstein_diagram`), for `K` with residue
field of `q` elements: for each point `P_σ` of the strip, `σ ≤ e s_w`, its type and whether it is
critical; `none` for `σ > e s_w`. The point itself is `point σ`. -/
noncomputable def eisensteinDiagram (q σ : ℕ) : Option (EisensteinPointType × Bool) :=
  if (σ : ℚ) ≤ I.ramificationIndex * I.swanSlope I.w then
    some (I.pointType σ, decide (I.IsCritical q σ))
  else none

end HerbrandInvariant

end IsNonarchimedeanLocalField
