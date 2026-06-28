import LeanBridge.ForMathlib.QExpansion.Eisenstein

/-!
# Generic q-expansion certificates for polynomials in `E₄` and `E₆`

This file provides the generic machinery for certifying q-expansion coefficients of any
level-1 modular form expressible as a polynomial in `E₄` and `E₆`. A polynomial is encoded
as a list of triples `(a, b, c) : ℕ × ℕ × ℚ`, representing the monomial `c · X₀^a · X₁^b`
(with `X₀ ↦ E₄`, `X₁ ↦ E₆`).

Top-level user-facing theorem: `qexp_coeff_via_E4E6`.
-/

namespace LeanBridge.QExpansion

open List PowerSeries EisensteinSeries ModularForm UpperHalfPlane

/-! ## List-side and PowerSeries-side polynomial evaluation -/

/-- Truncated q-expansion of the monomial `c · E₄^a · E₆^b`. -/
def monomialEisList (a b : ℕ) (c : ℚ) (N : ℕ) : List ℚ :=
  smulTrunc N c
    (mulTrunc N (powTrunc N (E4_qexpList N) a) (powTrunc N (E6_qexpList N) b))

/-- Truncated q-expansion of `Σ (a,b,c) ∈ P, c · E₄^a · E₆^b`. -/
def evalEisList (P : List (ℕ × ℕ × ℚ)) (N : ℕ) : List ℚ :=
  P.foldr (fun abc acc => addTrunc N (monomialEisList abc.1 abc.2.1 abc.2.2 N) acc) []

/-- The `PowerSeries ℂ` corresponding to the monomial `c · (qE₄)^a · (qE₆)^b`. -/
noncomputable def monomialEisPS (a b : ℕ) (c : ℚ) : PowerSeries ℂ :=
  (c : ℂ) • ((qExpansion 1 (↑E₄ : ℍ → ℂ)) ^ a * (qExpansion 1 (↑E₆ : ℍ → ℂ)) ^ b)

/-- The `PowerSeries ℂ` corresponding to `Σ (a,b,c) ∈ P, c · (qE₄)^a · (qE₆)^b`. -/
noncomputable def evalEisPS (P : List (ℕ × ℕ × ℚ)) : PowerSeries ℂ :=
  P.foldr (fun abc acc => monomialEisPS abc.1 abc.2.1 abc.2.2 + acc) 0

/-! ## Bridge: list evaluation matches PowerSeries evaluation on first N coefficients -/

lemma approxTo_monomialEis (a b : ℕ) (c : ℚ) (N : ℕ) :
    approxTo N (monomialEisList a b c N) (monomialEisPS a b c) := by
  unfold monomialEisList monomialEisPS
  exact approxTo_smul_C c
    (approxTo_mul (approxTo_pow (approxTo_E4 N) a) (approxTo_pow (approxTo_E6 N) b))

lemma approxTo_evalEisList (P : List (ℕ × ℕ × ℚ)) (N : ℕ) :
    approxTo N (evalEisList P N) (evalEisPS P) := by
  induction P with
  | nil =>
    show approxTo N [] (0 : PowerSeries ℂ)
    exact approxTo_zero
  | cons abc tl ih =>
    show approxTo N
      (addTrunc N (monomialEisList abc.1 abc.2.1 abc.2.2 N) (evalEisList tl N))
      (monomialEisPS abc.1 abc.2.1 abc.2.2 + evalEisPS tl)
    exact approxTo_add (approxTo_monomialEis abc.1 abc.2.1 abc.2.2 N) ih

/-! ## User-facing theorem -/

/-- If `f`'s q-expansion equals `evalEisPS P` (the symbolic E₄/E₆ polynomial expression),
then for any `n < N`, the `n`-th coefficient of `qExpansion 1 f` equals the `n`-th entry of
`evalEisList P N` (cast to `ℂ`). -/
theorem qexp_coeff_via_E4E6 (P : List (ℕ × ℕ × ℚ)) (f : ℍ → ℂ)
    (heq : qExpansion 1 f = evalEisPS P)
    (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 f)
      = ((evalEisList P N).getD n 0 : ℚ) := by
  rw [heq]
  exact approxTo_evalEisList P N n hn

/-! ## Convenience: building a monomial `E₄^a · E₆^b` as a `ModularForm 𝒮ℒ k` -/

open scoped MatrixGroups in
/-- A single `E₄^a · E₆^b` monomial, cast to weight `k = 4a + 6b`. -/
noncomputable def mkMonomForm (a b : ℕ) (k : ℤ)
    (h : (a : ℤ) * 4 + (b : ℤ) * 6 = k) : ModularForm 𝒮ℒ k :=
  ModularForm.mcast h ((E₄.pow a).mul (E₆.pow b))

open scoped MatrixGroups in
/-- The q-expansion of a monomial form factors through the q-expansions of `E₄, E₆`. -/
lemma qExpansion_mkMonomForm (a b : ℕ) (k : ℤ)
    (h : (a : ℤ) * 4 + (b : ℤ) * 6 = k) :
    qExpansion 1 ((mkMonomForm a b k h : ℍ → ℂ))
      = (qExpansion 1 (↑E₄ : ℍ → ℂ)) ^ a * (qExpansion 1 (↑E₆ : ℍ → ℂ)) ^ b := by
  show qExpansion 1 ⇑((E₄.pow a).mul (E₆.pow b)) = _
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL (E₄.pow a) (E₆.pow b),
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ a,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ b]

end LeanBridge.QExpansion
