import Mathlib

/-!
# Euler-factor certificate for an elliptic curve over `ℤ`

Every local Euler factor of the curve `E` below is recomputed here from a point count over `𝔽ₚ`
and checked against the `a_p` recorded in the LMFDB.  

| reduction at `p` | Euler factor       | `a_p`                             |
| ---------------- | ------------------ | --------------------------------- |
| good             | `1 - a_p X + p X²` | `p - N_p`                         |
| multiplicative   | `1 - a_p X`        | `±1` (`+1` split, `-1` non-split) |
| additive         | `1`                | `0`                               |

Throughout, `N_p` is the *affine* point count, which at a bad prime includes the singular point.
-/

open Polynomial

/-- `E : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` over `ℤ`, in its LMFDB minimal model. -/
def E : WeierstrassCurve ℤ := ⟨0, 0, 0, 4, 0⟩

/-- LMFDB `(p, a_p)` at the good primes. -/
def apGood : List (ℕ × ℤ) :=
  [(3, 0), (5, -2), (7, 0), (11, 0), (13, 6), (17, 2), (19, 0), (23, 0), (29, -10)]

/-- LMFDB `(p, a_p)` at the multiplicative primes; `a_p = 1` split, `-1` non-split. -/
def apMult : List (ℕ × ℤ) := []

/-- The additive primes, where `a_p = 0` and the Euler factor is `1`. -/
def apAdd : List ℕ := [2]

/-! ### Two ways to count `E(𝔽ₚ)` -/

/-- The affine points of `E` over `𝔽ₚ`, counted fibrewise over `x`. -/
def affineCount (p : ℕ) (h : Fact p.Prime) : ℕ :=
  ∑ x : (ZMod p),
  ({y : ZMod p
  | y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x^2 + E.a₄ * x + E.a₆} : Finset _).card

/-- The same count via Legendre symbols: the fibre over `x` has `legendreSym p (disc) + 1`
points, where `disc` is the discriminant of the quadratic in `y`.

Not used by the certificates below, which `decide` on `affineCount` directly (`O(p²)`, fine for
`p < 30`).  Kept, with `affineCount_eq_legendreCount`, for a later speed-up: evaluating the symbol
by Euler's criterion (`legendreSym.eq_pow`) brings the count to `O(p log p)` for `p ≠ 2`. -/
def legendreCount (p : ℕ) (h : Fact p.Prime) : ℤ :=
  ∑ x : ZMod p,
      (legendreSym p
        ((E.a₁ * x.val + E.a₃) ^ 2
        + 4 * (x.val ^ 3 + E.a₂ * x.val ^ 2 + E.a₄ * x.val + E.a₆))
        + 1)

/-- **Counting roots of a quadratic via its discriminant.**  Over a finite field in which `2 ≠ 0`,
completing the square — `y ↦ 2a·y + b` — is a bijection between the roots of `a·y² + b·y + c` and
the square roots of `b² - 4ac`, so the two solution sets are equinumerous. -/
theorem card_quadratic_roots_eq_card_sqrts_discrim {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    ({y : F | a * y ^ 2 + b * y + c = 0} : Finset F).card
      = ({z : F | z ^ 2 = discrim a b c} : Finset F).card := by
  have : NeZero (2 : F) := ⟨h2⟩
  have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
  refine Finset.card_nbij' (fun y => 2 * a * y + b) (fun z => (z - b) / (2 * a)) ?_ ?_ ?_ ?_
  <;> intro _ _ <;> grind [discrim]

/-- The two counts agree away from `p = 2`, where completing the square is unavailable. -/
theorem affineCount_eq_legendreCount (p : ℕ) (h : Fact p.Prime)
  (h2 : p ≠ 2) :
  affineCount p h = legendreCount p h := by
  rw [affineCount, legendreCount]
  -- Reduce to the per-x identity  #{y : Weierstrass eqn} = legendreSym p (discriminant) + 1.
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  rw [← legendreSym.card_sqrts _ h2]
  have two_ne : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr h2)
  norm_cast
  convert card_quadratic_roots_eq_card_sqrts_discrim two_ne one_ne_zero
      (E.a₁ * x + E.a₃) (-(x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)) using 2
  · grind
  · unfold discrim
    simp
    grind

/-! ### Local Euler factors -/

/-- Euler factor at a good prime: `1 - a_p X + p X²` with `a_p = p - N_p`. -/
noncomputable def eulerFactorGood (p : ℕ) (h : Fact p.Prime) : ℤ[X] :=
  1 - C (p - affineCount p h : ℤ) * X + C (p : ℤ) * X ^ 2

/-- Euler factor at a multiplicative prime: `1 - a_p X`, again with `a_p = p - N_p`.  The affine
count `N_p` now includes the node, which makes `a_p = ±1`. -/
noncomputable def eulerFactorMult (p : ℕ) (h : Fact p.Prime) : ℤ[X] :=
  1 - C (p - affineCount p h : ℤ) * X

/-- Euler factor at an additive prime: the constant `1`. -/
noncomputable def eulerFactorAdd (p : ℕ) (_ : Fact p.Prime) : ℤ[X] := 1

/-! ### Reduction type at a prime -/

/-- Good reduction at `p`, i.e. `p ∤ Δ`. -/
def GoodAt (p : ℕ) (_ : Fact p.Prime) := ¬ ((p : ℤ) ∣ E.Δ)
  deriving Decidable

/-- **Kraus' criterion.**  A pair `(c₄, c₆)` with `c₄³ - c₆² = 1728Δ ≠ 0` is the invariant pair of
an integral Weierstrass model over `ℤ_p` exactly when this holds; for `p ≥ 5` it always does,
since reaching `y² = x³ - 27c₄x - 54c₆` only needs `2` and `3` to be units.

The `p = 3` clause reads `v₃(c₆) ≠ 2`; no clause is needed for `v₃(c₆) = 1`, which cannot occur
(`c₆ ≡ -b₂³ + 9b₂b₄ mod 27`, so `v₃(c₆)` is `0` or `≥ 3`).  Here `%` is `Int.emod`, non-negative
for a positive modulus, so `c₆ % 4 = 3` is the correct spelling of `c₆ ≡ -1 (mod 4)`. -/
def KrausAt (p : ℕ) (c₄ c₆ : ℤ) : Prop :=
  if p = 2 then c₆ % 4 = 3 ∨ (c₄ % 16 = 0 ∧ (c₆ % 32 = 0 ∨ c₆ % 32 = 8))
  else if p = 3 then ¬ (9 ∣ c₆ ∧ ¬ (27 ∣ c₆))
  else True
  deriving Decidable

/-- `E` is minimal at `p`, i.e. admits no descent by `p`.  A descent needs `v_p(c₄) ≥ 4`,
`v_p(c₆) ≥ 6` and `v_p(Δ) ≥ 12` *and* the descended pair `(c₄/p⁴, c₆/p⁶)` to be realisable.  The
last condition is automatic for `p ≥ 5` (Silverman VII, Rem. 1.1) but not at `p = 2, 3`, where
dropping it reports genuinely minimal models as non-minimal.  Both divisions are exact wherever
they are reached, hence independent of the rounding convention. -/
def MinimalAt (p : ℕ) (_ : Fact p.Prime) :=
  ¬ ((p : ℤ) ^ 4 ∣ E.c₄ ∧ (p : ℤ) ^ 6 ∣ E.c₆ ∧ (p : ℤ) ^ 12 ∣ E.Δ
      ∧ KrausAt p (E.c₄ / (p : ℤ) ^ 4) (E.c₆ / (p : ℤ) ^ 6))
  deriving Decidable

/-- Multiplicative reduction at `p`: a node, i.e. `p ∣ Δ` and `p ∤ c₄` on a model minimal at `p`.
`MinimalAt` is already implied by `p ∤ c₄`, and is kept only for symmetry with `AdditiveAt`. -/
def MultiplicativeAt (p : ℕ) (h : Fact p.Prime) :=
  MinimalAt p h ∧ ((p : ℤ) ∣ E.Δ) ∧ (¬ ((p : ℤ) ∣ E.c₄))
  deriving Decidable

/-- Additive reduction at `p`: a cusp, i.e. `p ∣ Δ` and `p ∣ c₄` on a model minimal at `p`.
Here `MinimalAt` carries real weight, since `p ∣ c₄` says nothing about minimality. -/
def AdditiveAt (p : ℕ) (h : Fact p.Prime) :=
  MinimalAt p h ∧ ((p : ℤ) ∣ E.Δ) ∧ ((p : ℤ) ∣ E.c₄)
  deriving Decidable
  
/-! ### The certificates -/

/-- One iteration of the good-prime loop: the count `N_p` pins down the Euler factor.  Works
uniformly for positive and negative `a_p`. -/
theorem eulerFactorGood_of_count (p : ℕ) (h : Fact p.Prime) (a : ℤ)
    (hN : (affineCount p h : ℤ) = p - a) :
    eulerFactorGood p h = 1 + C (-a : ℤ) * X + C (p : ℤ) * X ^ 2 := by
  unfold eulerFactorGood
  simp only [hN, sub_sub_cancel, C_neg]
  ring

/-- One iteration of the multiplicative loop. -/
theorem eulerFactorMult_of_count (p : ℕ) (h : Fact p.Prime) (a : ℤ)
    (hN : (affineCount p h : ℤ) = p - a) :
    eulerFactorMult p h = 1 + C (-a : ℤ) * X := by
  unfold eulerFactorMult
  simp only [hN, sub_sub_cancel, C_neg]
  ring

-- The three certificates share one proof shape.  When a table is empty, `fin_cases` closes every
-- goal and the `all_goals` block is dead code, which the unused- and unreachable-tactic linters
-- would flag; they are switched off for each certificate so the template stays uniform.

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Every `(p, a_p)` row of `apGood` is certified. -/
theorem apGood_certified : ∀ pa ∈ apGood, ∀ h : Fact pa.1.Prime, GoodAt pa.1 h ∧
    eulerFactorGood pa.1 h = 1 + C (-pa.2 : ℤ) * X + C (pa.1 : ℤ) * X ^ 2 := by
  intro pa hpa h
  unfold apGood at hpa
  fin_cases hpa
  all_goals
    constructor
    · unfold GoodAt
      decide
    · exact eulerFactorGood_of_count _ ⟨by decide⟩ _ (by decide)


set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Every `(p, a_p)` row of `apMult` is certified. -/
theorem apMult_certified : ∀ pa ∈ apMult, ∀ h : Fact pa.1.Prime, MultiplicativeAt pa.1 h ∧
    eulerFactorMult pa.1 h = 1 + C (-pa.2 : ℤ) * X := by
  intro pa hpa h
  unfold apMult at hpa
  fin_cases hpa
  all_goals
    constructor
    · unfold MultiplicativeAt MinimalAt
      decide
    · exact eulerFactorMult_of_count _ ⟨by decide⟩ _ (by decide)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Every prime of `apAdd` is certified additive, with Euler factor `1`. -/
theorem apAdd_certified : ∀ p ∈ apAdd, ∀ h : Fact p.Prime, AdditiveAt p h ∧
    eulerFactorAdd p h = 1 := by
  intro p hp h
  unfold apAdd at hp
  fin_cases hp
  all_goals
    constructor
    · unfold AdditiveAt MinimalAt
      decide
    · rfl

/- TODO:
1. make it mathlib `WeierstrassCurve.localPolynomial` compatible
2. make it mathlib `goodReduction` compatible
3. (DONE): extend functionality to different reduction types  (done: `MultiplicativeAt` /
   `AdditiveAt`, `eulerFactorMult` / `eulerFactorAdd`, loops `apMult_certified` /
   `apAdd_certified`)
4. (DONE): a single check for all displayed primes  (done: `apGood_certified` loops over `apGood`)
5. `eulerFactorAdd` is definitionally `1`, so the second conjunct of `apAdd_certified` is closed
   by `rfl` and certifies nothing about `E`.  Replace it with the affine count `N_p = p`, which
   is what additive reduction actually forces.
-/
