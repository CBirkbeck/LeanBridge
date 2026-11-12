import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.QuasiModular

/-!
# The depth of `E₂`

The Eisenstein series `E₂(z) = 1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ` (Mathlib's `EisensteinSeries.E2`, whose
`q`-expansion is `EisensteinSeries.E2_eq_tsum_cexp`) is quasi-modular of weight `2` and depth at
most `1` on `SL(2, ℤ)` (LMFDB `mf.quasi_modular`), with `P(z, X) = E₂(z) - (6i/π) X`
(`ModularForm.isQuasiModularForm_E2`). Its depth is exactly `1`, as the knowl states. A
quasi-modular form `f` of depth `0` and trivial multiplier satisfies `f ∣[2] γ = f₀` with `f₀`
independent of `γ`, so `f₀ = f ∣[2] 1 = f` and `f` is invariant under `SL(2, ℤ)`; but `E₂` is not,
since `E₂ ∣[2] S = E₂ - 6i / (π z)` at the inversion `S`.

Unwinding the slash action in Mathlib's `EisensteinSeries.E2_slash_action`, with `ζ(2) = π² / 6`,
gives the transformation law of the knowl, `E₂(γz) = (cz + d)² E₂(z) - (6i/π) c (cz + d)`.

## Main results

* `ModularForm.E2_smul` (LMFDB `mf.quasi_modular`): the transformation law
  `E₂(γz) = (cz + d)² E₂(z) - (6i/π) c (cz + d)` on `SL(2, ℤ)`.
* `ModularForm.not_isQuasiModularForm_E2_zero`: `E₂` is not quasi-modular of depth `0`, that is,
  not invariant in weight `2` under `SL(2, ℤ)`.
* `ModularForm.hasQuasiModularDepth_E2` (LMFDB `mf.quasi_modular`): `E₂` has depth `1`.

## References

* M. Kaneko and D. Zagier, *A generalized Jacobi theta function and quasimodular forms*, in
  *The Moduli Space of Curves*, Progr. Math. 129, Birkhäuser, 1995, 165–172.
* D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer, 2008, §2.3 and §5.
-/

open Complex EisensteinSeries

open UpperHalfPlane hiding I I_re I_im

open scoped ModularForm MatrixGroups Real

namespace ModularForm

/-- **The transformation law of `E₂`** (LMFDB `mf.quasi_modular`): for `γ = (a, b; c, d)` in
`SL(2, ℤ)`, `E₂(γz) = (cz + d)² E₂(z) - (6i/π) c (cz + d)`. -/
lemma E2_smul (γ : SL(2, ℤ)) (z : ℍ) :
    E2 (γ • z) = denom γ z ^ 2 * E2 z - 6 * I / π * (γ 1 0 : ℂ) * denom γ z := by
  have h : (E2 ∣[(2 : ℤ)] γ) z = (E2 - (1 / (2 * riemannZeta 2)) • D2 γ) z :=
    congrFun (E2_slash_action γ) z
  rw [SL_slash_apply, Pi.sub_apply, Pi.smul_apply, D2, riemannZeta_two, zpow_neg, smul_eq_mul] at h
  field_simp at h
  field_simp
  linear_combination h

/-- **`E₂` is not quasi-modular of depth `0`**: with trivial multiplier, a polynomial `P` of degree
`0` in its transformation law would make `E₂` invariant in weight `2` under `SL(2, ℤ)`, while
`E₂ ∣[2] S - E₂ = -6i / (π z)` does not vanish. -/
lemma not_isQuasiModularForm_E2_zero : ¬IsQuasiModularForm 𝒮ℒ 2 0 1 E2 := by
  rintro ⟨-, -, F, -, hF⟩
  have hP (γ : 𝒮ℒ) : E2 ∣[(2 : ℤ)] (γ : GL (Fin 2) ℝ) = F 0 := by
    rw [hF γ]
    ext z
    simp [quasiModularPolynomial]
  have h : E2 ∣[(2 : ℤ)] ModularGroup.S = E2 :=
    (hP ⟨_, ModularGroup.S, rfl⟩).trans <| (hP 1).symm.trans <| SlashAction.slash_one _ _
  rw [E2_slash_action, sub_eq_self] at h
  simpa [D2_S, riemannZeta_two] using congrFun h UpperHalfPlane.I

/-- **`E₂` has depth `1`** (LMFDB `mf.quasi_modular`): it is quasi-modular of weight `2` and depth
`1` on `SL(2, ℤ)`, with trivial multiplier. -/
lemma hasQuasiModularDepth_E2 : HasQuasiModularDepth 𝒮ℒ 2 1 1 E2 :=
  ⟨isQuasiModularForm_E2, fun _ hq ↦ Nat.lt_one_iff.mp hq ▸ not_isQuasiModularForm_E2_zero⟩

end ModularForm
