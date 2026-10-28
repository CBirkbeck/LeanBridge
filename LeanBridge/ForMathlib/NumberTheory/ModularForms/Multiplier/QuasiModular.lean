import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Quasi-modular forms

A quasi-modular form of weight `k`, depth at most `p` and multiplier `v` on a subgroup `Γ` of
`GL(2, ℝ)` is a holomorphic function `f : ℍ → ℂ`, bounded at the cusps, such that
`(f ∣[k] γ)(z) = v(γ) P(z, c / (cz + d))` for every `γ = (a, b; c, d) ∈ Γ`, where
`P(z, X) = Σ_{j ≤ p} f_j(z) X^j` has holomorphic coefficients `f_j` not depending on `γ`. The
Eisenstein series `E₂` is the basic example, of weight `2` and depth `1` on `SL(2, ℤ)`.

## Main definitions

* `ModularForm.quasiModularPolynomial`: the value `Σ_j f_j(z) (c / (cz + d))^j`.
* `ModularForm.IsQuasiModularForm` (LMFDB `mf.quasi_modular`): quasi-modular forms of weight `k`,
  depth at most `p` and multiplier `v`.
* `ModularForm.HasQuasiModularDepth` (LMFDB `mf.quasi_modular`): the depth.

## Main results

* `ModularForm.isQuasiModularForm_E2`: `E₂` is quasi-modular of weight `2` and depth at most `1` on
  `SL(2, ℤ)`, with `P(z, X) = E₂(z) - (6i/π) X`.
-/

open UpperHalfPlane OnePoint EisensteinSeries Matrix SpecialLinearGroup

open scoped ModularForm Manifold MatrixGroups Real

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {p : ℕ} {f : ℍ → ℂ}

variable (p) in
/-- The value `P(z, c / (cz + d)) = Σ_{j ≤ p} f_j(z) (c / (cz + d))^j` at `z` of the polynomial
`P(z, X) = Σ_j f_j(z) X^j` with coefficients `F = (f_0, …, f_p)`, for `γ = (a, b; c, d)`. -/
noncomputable def quasiModularPolynomial (F : Fin (p + 1) → ℍ → ℂ) (γ : GL (Fin 2) ℝ) (z : ℍ) : ℂ :=
  ∑ j, F j z * ((γ 1 0 : ℂ) / denom γ z) ^ (j : ℕ)

variable (Γ k p) in
/-- A function `f : ℍ → ℂ` is a **quasi-modular form** (LMFDB `mf.quasi_modular`) of weight `k`,
depth at most `p` and multiplier `v : Γ → S¹` on a subgroup `Γ` of `GL(2, ℝ)` if it is holomorphic,
bounded at every cusp of `Γ` (the growth condition), and there are holomorphic `f_0, …, f_p` such
that `(f ∣[k] γ)(z) = v(γ) P(z, c / (cz + d))` for every `γ = (a, b; c, d) ∈ Γ`, where
`P(z, X) = Σ_j f_j(z) X^j`. The LMFDB's polynomial `P` "whose coefficients depend only on `f`" is
read as a polynomial in `X` whose coefficients are holomorphic functions of `z`, as in
Kaneko–Zagier; the depth is its degree in `X` (`HasQuasiModularDepth`). -/
def IsQuasiModularForm (v : Γ →* Circle) (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ (∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsBoundedAt f k) ∧
    ∃ F : Fin (p + 1) → ℍ → ℂ, (∀ j, MDiff (F j)) ∧
      ∀ γ : Γ, f ∣[k] (γ : GL (Fin 2) ℝ) = (v γ : ℂ) • quasiModularPolynomial p F γ

variable (Γ k p) in
/-- A quasi-modular form `f` of weight `k` and multiplier `v` **has depth** `p` (LMFDB
`mf.quasi_modular`) if `p` is the least degree of a polynomial `P` in its transformation law. -/
def HasQuasiModularDepth (v : Γ →* Circle) (f : ℍ → ℂ) : Prop :=
  IsQuasiModularForm Γ k p v f ∧ ∀ q < p, ¬IsQuasiModularForm Γ k q v f

private lemma isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) : IsBoundedAtImInfty (D2 γ) := by
  rw [isBoundedAtImInfty_iff]
  refine ⟨2 * π, 1, fun z hz ↦ ?_⟩
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · simp [D2, hc, Real.pi_pos.le]
  have hc' : (1 : ℝ) ≤ |(γ 1 0 : ℝ)| := by
    exact_mod_cast Int.one_le_abs hc
  have h : |(γ 1 0 : ℝ)| ≤ ‖denom γ z‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp [denom]
    exact le_mul_of_one_le_right (abs_nonneg _) <| hz.trans (le_abs_self _)
  rw [D2, norm_div, div_le_iff₀ (by linarith)]
  simp
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **`E₂` is quasi-modular** of weight `2` and depth at most `1` on `SL(2, ℤ)`, with trivial
multiplier and `P(z, X) = E₂(z) - (6i/π) X` (written `E₂(z) - (2πi / 2ζ(2)) X`). -/
lemma isQuasiModularForm_E2 : IsQuasiModularForm 𝒮ℒ 2 1 1 E2 := by
  refine ⟨E2_mdifferentiable, ?_, ![E2, fun _ ↦ -(1 / (2 * riemannZeta 2)) * (2 * π * Complex.I)],
    ?_, ?_⟩
  · intro c hc
    refine (isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦ ?_
    rw [E2_slash_action]
    exact isBoundedAtImInfty_E2.sub <| (isBoundedAtImInfty_D2 γ).const_smul_left _
  · exact Fin.forall_fin_two.mpr ⟨E2_mdifferentiable, mdifferentiable_const⟩
  · rintro ⟨_, g, rfl⟩
    rw [MonoidHom.one_apply, Circle.coe_one, one_smul]
    ext z
    have h : (E2 ∣[(2 : ℤ)] (mapGL ℝ g : GL (Fin 2) ℝ)) z =
        (E2 - (1 / (2 * riemannZeta 2)) • D2 g) z :=
      congrFun (E2_slash_action g) z
    rw [h]
    simp [quasiModularPolynomial, D2, Fin.sum_univ_two, mapGL]
    ring1

end ModularForm
