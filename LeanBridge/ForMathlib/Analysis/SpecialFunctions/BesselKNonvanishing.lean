import LeanBridge.ForMathlib.Analysis.SpecialFunctions.BesselKLowerBound

/-!
# The `K`-Bessel function does not vanish identically

For every order `ν ∈ ℂ`, the `K`-Bessel function `K_ν` (`Complex.besselK`, LMFDB
`specialfunction.k_bessel`) takes a nonzero value on `(0, ∞)`: `|K_ν(x)| ≥ e^{-2x}` for all large
`x` (`Complex.eventually_exp_le_norm_besselK`). For real `ν` the function has no zero at all
(`Complex.besselK_ofReal_ne_zero`), but `K_{ir}` has zeros for real `r ≠ 0`: this is the
non-vanishing used for the Fourier coefficients of Maass forms of spectral parameter `r`.

## Main results

* `Complex.exists_besselK_ne_zero`: `K_ν(x) ≠ 0` for some `x > 0`.
-/

open Filter Real

namespace Complex

variable (ν : ℂ)

/-- **The `K`-Bessel function does not vanish identically on `(0, ∞)`**: for every order `ν ∈ ℂ`,
`K_ν(x) ≠ 0` for some `x > 0`. -/
lemma exists_besselK_ne_zero : ∃ x, 0 < x ∧ besselK ν x ≠ 0 := by
  rcases ((eventually_gt_atTop 0).and (eventually_exp_le_norm_besselK ν)).exists with ⟨x, hx, hK⟩
  exact ⟨x, hx, norm_pos_iff.mp <| (exp_pos _).trans_le hK⟩

end Complex
