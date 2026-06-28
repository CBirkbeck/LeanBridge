import LeanBridge.ForMathlib.Irreduciblepolys.PolynomialsAsLists
import Mathlib.NumberTheory.Divisors

/-!
# PoC: Computational q-expansion of the modular discriminant Δ

This file provides truncated power-series operations on `List ℚ` and uses them to compute the
first few coefficients of the q-expansion of `Δ = (E₄³ - E₆²) / 1728`. The bridge from this
computation to the actual modular form `ModularForm.discriminant` lives in a separate file.
-/

namespace LeanBridge.QExpansion

/-! ## Truncated power series operations on `List ℚ` -/

/-- Truncating addition. -/
def addTrunc (n : ℕ) (l₁ l₂ : List ℚ) : List ℚ := (l₁.addPointwise l₂).take n

/-- Truncating subtraction. -/
def subTrunc (n : ℕ) (l₁ l₂ : List ℚ) : List ℚ :=
  (l₁.addPointwise (l₂.map Neg.neg)).take n

/-- Truncating multiplication (convolution). -/
def mulTrunc (n : ℕ) (l₁ l₂ : List ℚ) : List ℚ := (l₁.convolve l₂).take n

/-- Truncating scalar multiplication. -/
def smulTrunc (n : ℕ) (c : ℚ) (l : List ℚ) : List ℚ := (l.mulPointwise c).take n

/-- The unit power series truncated to length `n`. -/
def oneTrunc (n : ℕ) : List ℚ :=
  (List.range n).map fun i => if i = 0 then 1 else 0

/-- Truncating power. -/
def powTrunc (n : ℕ) (l : List ℚ) : ℕ → List ℚ
  | 0 => oneTrunc n
  | k + 1 => mulTrunc n l (powTrunc n l k)

/-! ## Divisor sums -/

/-- The divisor sum function `σ_k(n)`. -/
def sigmaKK (k n : ℕ) : ℕ := (Nat.divisors n).sum fun d => d ^ k

/-! ## q-expansions of `E₄` and `E₆` as lists -/

/-- The q-expansion of `E₄` truncated to length `n`. -/
def E4_qexpList (n : ℕ) : List ℚ :=
  (List.range n).map fun m => if m = 0 then 1 else 240 * (sigmaKK 3 m : ℚ)

/-- The q-expansion of `E₆` truncated to length `n`. -/
def E6_qexpList (n : ℕ) : List ℚ :=
  (List.range n).map fun m => if m = 0 then 1 else -504 * (sigmaKK 5 m : ℚ)

/-! ## q-expansion of Δ via `(E₄³ - E₆²) / 1728` -/

/-- The q-expansion of `Δ = (E₄³ - E₆²) / 1728` truncated to length `n`. -/
def Delta_qexpList (n : ℕ) : List ℚ :=
  smulTrunc n (1 / 1728)
    (subTrunc n (powTrunc n (E4_qexpList n) 3) (powTrunc n (E6_qexpList n) 2))

/-! ## Sanity checks against known values -/

/-- E₄ = 1 + 240q + 2160q² + 6720q³ + 17520q⁴ + 30240q⁵ + … -/
example : E4_qexpList 6 = [1, 240, 2160, 6720, 17520, 30240] := by decide +kernel

/-- E₆ = 1 - 504q - 16632q² - 122976q³ - 532728q⁴ - 1575504q⁵ - … -/
example : E6_qexpList 6 = [1, -504, -16632, -122976, -532728, -1575504] := by decide +kernel

/-- The first seven Ramanujan tau values:
`τ(0) = 0, τ(1) = 1, τ(2) = -24, τ(3) = 252, τ(4) = -1472, τ(5) = 4830, τ(6) = -6048`. -/
example : Delta_qexpList 7 = [0, 1, -24, 252, -1472, 4830, -6048] := by decide +kernel

end LeanBridge.QExpansion
