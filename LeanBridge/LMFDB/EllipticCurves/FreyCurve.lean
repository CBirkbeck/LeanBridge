import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic

/-!
# The Frey curve of `(3, 5)` is a global minimal model

The Frey–Hellegouarch curve of the coprime pair `(a, b) = (3, 5)`, with `c = a + b = 8`, is Tau
Ceti's `TauCeti.freyCurve 3 5`, the integral Weierstrass equation `y² = x (x - 3) (x + 5)`, that is
`y² = x³ + 2 x² - 15 x`. This file certifies the test case "minimal model for a concrete coprime
`(a, b)`" of LeanBridge issue #51: this equation is a global minimal model over `ℤ`, and its
discriminant is `16 (3 · 5 · 8)² = 230400 = 2¹⁰ · 3² · 5²`, which is therefore the minimal
discriminant. It is the case `a = 3`, `b = 5` of Tau Ceti's
`TauCeti.isGlobalMinimal_baseChange_freyCurve`: `3` and `5` are coprime, and `16` does not divide
`3 · 5 · 8 = 120`. The equation is elliptic over `ℚ` (the instance
`((freyCurve 3 5).baseChange ℚ).IsElliptic`).

## Main results

* `LeanBridge.FreyCurve.Δ_freyCurve_three_five`: the discriminant of `y² = x (x - 3) (x + 5)` is
  `230400`.
* `LeanBridge.FreyCurve.isGlobalMinimal_baseChange_freyCurve_three_five`: the equation is a global
  minimal model over `ℤ`.
* `LeanBridge.FreyCurve.minimalDiscriminantIdeal_freyCurve_three_five`: the minimal discriminant
  ideal is `(230400)`.
-/

open TauCeti WeierstrassCurve

namespace LeanBridge.FreyCurve

instance : ((freyCurve (3 : ℤ) 5).baseChange ℚ).IsElliptic :=
  isElliptic_baseChange_freyCurve (by decide)

/-- **The discriminant of the Frey curve of `(3, 5)`** is `16 (3 · 5 · 8)² = 230400`. -/
lemma Δ_freyCurve_three_five : (freyCurve (3 : ℤ) 5).Δ = 230400 :=
  rfl

/-- **The Frey curve of `(3, 5)` is a global minimal model over `ℤ`**: `3` and `5` are coprime and
`16` does not divide `3 · 5 · 8`. -/
lemma isGlobalMinimal_baseChange_freyCurve_three_five :
    IsGlobalMinimal ℤ ((freyCurve (3 : ℤ) 5).baseChange ℚ) :=
  isGlobalMinimal_baseChange_freyCurve ⟨2, -1, rfl⟩ (by decide)

/-- **The minimal discriminant of the Frey curve of `(3, 5)`** is `230400`, its discriminant. -/
lemma minimalDiscriminantIdeal_freyCurve_three_five :
    minimalDiscriminantIdeal ℤ ((freyCurve (3 : ℤ) 5).baseChange ℚ) = Ideal.span {230400} :=
  minimalDiscriminantIdeal_freyCurve_of_not_dvd ⟨2, -1, rfl⟩ (by decide)

end LeanBridge.FreyCurve
