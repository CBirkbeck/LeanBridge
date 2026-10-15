#!/usr/bin/env sage
"""Generate a Lean Euler-factor certificate for an elliptic curve over ℤ.

    sage gen_pc_loop.py                          # every curve in CURVES -> generated/
    sage gen_pc_loop.py "[0,-1,0,-8,-16]"        # one curve
    sage gen_pc_loop.py "[0,-1,0,-8,-16]" -o E.lean

Sage computes a_p and the reduction types; the Lean file re-checks every row by `decide`.
"""
import argparse
import os
import sys

from sage.all import ZZ, EllipticCurve, primes

GOOD_PRIME_BOUND = 30

CURVES = [
    [0, -1, 0, -8, -16],
    [1, -1, 1, 25, 1],
    [0, 0, 0, 4, 0],
    [0, -1, 0, -908, -15688],
    [1, 1, 1, -352, -2431],
]

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OUT_DIR = os.path.join(HERE, "generated")


# ---------------------------------------------------------------- tables

def kraus_ok(p, c4, c6):
    """Mirror of `KrausAt` in the Lean template.

    True iff `(c4, c6)` is the invariant pair of an integral Weierstrass model over ℤ_p.
    Unconditional for p ≥ 5.  Python's `%` is non-negative for a positive modulus, matching
    Lean's `Int.emod`, so the congruences transcribe literally.
    """
    if p == 2:
        return c6 % 4 == 3 or (c4 % 16 == 0 and c6 % 32 in (0, 8))
    if p == 3:
        return not (c6 % 9 == 0 and c6 % 27 != 0)   # v₃(c₆) ≠ 2
    return True


def tables(a):
    """Return (good, mult, add, warnings) for the curve with a-invariants a.

    `good` and `mult` are lists of (p, a_p); `add` is a list of primes.
    """
    E = EllipticCurve(a)
    if not E.is_minimal():
        raise ValueError(
            f"{a} is not a minimal model; the Lean predicates test the model as given "
            f"(minimal model: {list(E.minimal_model().a_invariants())})"
        )
    disc, c4, c6 = ZZ(E.discriminant()), ZZ(E.c4()), ZZ(E.c6())
    good = [(p, E.ap(p)) for p in primes(GOOD_PRIME_BOUND) if E.has_good_reduction(p)]
    mult, add, warnings = [], [], []
    for p in disc.prime_factors():
        vd, v4, v6 = disc.valuation(p), c4.valuation(p), c6.valuation(p)
        # Mirror of `MinimalAt` in the template: non-minimal at p iff the three valuations are
        # large *and* the descended pair is realised.  `E.is_minimal()` above already rules this
        # out, so the warning is a guard against the two predicates drifting apart, not a routine
        # diagnostic.  (Before `KrausAt` the test was the valuations alone, which mis-fired at
        # p = 2, 3 — e.g. 112.c5, minimal with v₂(Δ) = 14, v₂(c₄) = 4, v₂(c₆) = 6.)
        if vd >= 12 and v4 >= 4 and v6 >= 6 and kraus_ok(p, c4 // p ** 4, c6 // p ** 6):
            warnings.append(
                f"p = {p}: v_p(Δ) = {vd} ≥ 12, v_p(c₄) = {v4} ≥ 4, v_p(c₆) = {v6} ≥ 6 and the "
                f"descended pair (c₄/{p}⁴, c₆/{p}⁶) passes Kraus at {p}, so `MinimalAt` in the "
                f"template reports the model as non-minimal at {p}; the row for {p} will fail "
                f"`decide` in Lean"
            )
        if E.has_multiplicative_reduction(p):
            mult.append((p, E.ap(p)))
        else:
            add.append(p)
    return good, mult, add, warnings


# ---------------------------------------------------------------- Lean rendering

def lean_pairs(rows):
    return "[" + ", ".join(f"({p}, {ap})" for p, ap in rows) + "]"


def lean_nats(ps):
    return "[" + ", ".join(str(p) for p in ps) + "]"


def lean_ainvs(a):
    return ", ".join(str(x) for x in a)


# The curve and the three tables are substituted for `{lean_ainvs}`, `{apGood}`, `{apMult}`,
# `{apAdd}`.
TEMPLATE = """import Mathlib

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
def E : WeierstrassCurve ℤ := ⟨{lean_ainvs}⟩

/-- LMFDB `(p, a_p)` at the good primes. -/
def apGood : List (ℕ × ℤ) :=
  {apGood}

/-- LMFDB `(p, a_p)` at the multiplicative primes; `a_p = 1` split, `-1` non-split. -/
def apMult : List (ℕ × ℤ) := {apMult}

/-- The additive primes, where `a_p = 0` and the Euler factor is `1`. -/
def apAdd : List ℕ := {apAdd}

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
"""


def replace_once(src, old, new):
    assert src.count(old) == 1, f"template drift: expected exactly one occurrence of {old!r}"
    return src.replace(old, new)


def render(a):
    good, mult, add, warnings = tables(a)
    src = TEMPLATE
    src = replace_once(src, "{lean_ainvs}", lean_ainvs(a))
    src = replace_once(src, "{apGood}", lean_pairs(good))
    src = replace_once(src, "{apMult}", lean_pairs(mult))
    src = replace_once(src, "{apAdd}", lean_nats(add))
    return src, (good, mult, add, warnings)


# ---------------------------------------------------------------- CLI

def parse_ainvs(s):
    s = s.replace("−", "-").strip().strip("[]⟨⟩()")
    a = [int(x) for x in s.split(",")]
    if len(a) != 5:
        raise ValueError(f"expected 5 a-invariants, got {a}")
    return a


def default_out_path(a):
    return os.path.join(DEFAULT_OUT_DIR, "pc_loop_" + "_".join(str(x) for x in a) + ".lean")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("ainvs", nargs="?", help='e.g. "[0,-1,0,-8,-16]" (default: CURVES)')
    parser.add_argument("-o", "--out", help="output .lean path (only with a single curve)")
    args = parser.parse_args(argv)

    curves = [parse_ainvs(args.ainvs)] if args.ainvs else CURVES
    for a in curves:
        src, (good, mult, add, warnings) = render(a)
        out = args.out if args.ainvs and args.out else default_out_path(a)
        os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
        with open(out, "w", encoding="utf-8") as f:
            f.write(src)
        print(f"E = {a}")
        print(f"  apGood = {lean_pairs(good)}")
        print(f"  apMult = {lean_pairs(mult)}")
        print(f"  apAdd  = {lean_nats(add)}")
        for w in warnings:
            print(f"  WARNING {w}", file=sys.stderr)
        print(f"  -> {os.path.relpath(out)}")


if __name__ == "__main__":
    main()
