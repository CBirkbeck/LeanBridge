import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CoefficientsUnique
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.TrivialCharacter
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareSpanCuspForm

/-!
# The constant Maass newform

The constant function `1` is a Maass form of weight `0` on `SL(2, ℤ) = Γ₀(1)` with eigenvalue `0`
in the sense of the LMFDB (`mf.maass.mwf`: smooth, square-integrable on `SL(2, ℤ) \ ℍ`, which has
finite volume, invariant, `Δ 1 = 0`), a Hecke eigenform, and new, since level `1` has no oldforms:
it is a Maass newform (`UpperHalfPlane.IsMaassNewform`) of spectral parameter `R = ±i/2`. It has no
cosine and no sine expansion `∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` (or `sin`), for any `R`:
the constant term of such an expansion vanishes, and a sine expansion is odd. So the claim of the
LMFDB (`mf.maass.mwf.coefficients`) that every Maass newform has such an expansion holds for cusp
forms only (the forms in the LMFDB), and `UpperHalfPlane.maassCoefficients` gives this newform the
junk coefficients `0`.

## Main results

* `UpperHalfPlane.isMaassNewform_const_one`: the constant `1` is a Maass newform of level `1`.
* `UpperHalfPlane.not_hasMaassCosineExpansion_const_one`,
  `UpperHalfPlane.not_hasMaassSineExpansion_const_one`: it has no cosine or sine expansion.
* `UpperHalfPlane.maassCoefficients_const_one`: its coefficients are the junk value `0`.
-/

open MeasureTheory Real

namespace UpperHalfPlane

variable (r : ℂ) (c : ℕ+ → ℂ)

/-- **The constant function `1` is a Maass newform** of weight `0`, level `1`, trivial character
and eigenvalue `0`: it is smooth, square-integrable on `SL(2, ℤ) \ ℍ` (of finite volume), invariant,
killed by the Laplacian, an eigenfunction of every `T_p` (with eigenvalue `(1 + p) / √p`), and new,
level `1` having no oldforms. -/
lemma isMaassNewform_const_one : IsMaassNewform 1 1 0 fun _ ↦ 1 := by
  refine ⟨⟨⟨contDiffOn_const, ?_, fun γ hγ z ↦ ?_, fun z _ ↦ ?_⟩, fun G hG ↦ ?_⟩,
    fun h ↦ one_ne_zero <| congrFun h I, fun p _ _ ↦ ⟨((√p)⁻¹ : ℝ) * (1 + p), fun z ↦ ?_⟩⟩
  · simp only [Function.comp_apply]
    exact integrableOn_const (ModularGroup.volume_iUnion_out_inv_smul_fdo_lt_top _).ne
  · simp [dirichletCharacter_one_apply_of_mem_gamma0 hγ]
  · simp [hyperbolicLaplacian, Function.comp_def]
  · have h0 : maassOldSpace 1 1 0 = ⊥ := by
      refine Submodule.span_eq_bot.mpr fun F hF ↦ ?_
      rcases hF with ⟨-, M, -, hM, -, hMN, -⟩
      exact absurd (Nat.dvd_one.mp hM) hMN
    rw [h0, Submodule.mem_bot] at hG
    simp [maassPetersson, hG]
  · have hχ : (1 : DirichletCharacter ℂ 1) p = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
    simp [maassHeckeOperatorChar, hχ]

/-- **The constant newform has no cosine expansion**: `1 ≠ ∑_{n ≥ 1} c(n) √y K_{iR}(2πny) cos(2πnx)`
on `ℍ` for every spectral parameter `R` and all coefficients `c(n)`, since the right side has
vanishing constant term in `x`. -/
lemma not_hasMaassCosineExpansion_const_one : ¬HasMaassCosineExpansion (fun _ ↦ 1) r c := by
  intro h
  have ha : ∃ a : ℤ → ℂ, HasMaassFourierExpansion (fun _ ↦ 1) r a ∧ a 0 = 0 :=
    ⟨_, h.hasMaassFourierExpansion, by simp⟩
  rcases ha with ⟨a, hF, ha0⟩
  have hd : a 0 * √(1 : ℝ) * (Complex.I * r).besselK (2 * π * |(0 : ℤ)| * 1) -
      (if (0 : ℤ) = 0 then 1 else 0) = 0 :=
    eq_zero_of_forall_hasSum_mul_exp (d := fun n ↦ a n * √(1 : ℝ) *
      (Complex.I * r).besselK (2 * π * |n| * 1) - if n = 0 then 1 else 0) (fun x ↦ ?_) 0
  · simp [ha0] at hd
  · have h1 : HasSum (fun n : ℤ ↦ (if n = 0 then (1 : ℂ) else 0) *
        Complex.exp (2 * π * Complex.I * n * x)) 1 := by
      convert hasSum_ite_eq (0 : ℤ) (1 : ℂ) using 1
      funext n
      split_ifs with hn <;> simp [hn]
    convert (hF (mk (x + Complex.I) (by simp))).sub h1 using 1
    · funext n
      simp only [mk_im, mk_re, Complex.add_im, Complex.add_re, Complex.ofReal_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_add, add_zero]
      ring1
    · simp

/-- **The constant newform has no sine expansion**: `1 ≠ ∑_{n ≥ 1} c(n) √y K_{iR}(2πny) sin(2πnx)`
on `ℍ` for every spectral parameter `R` and all coefficients `c(n)`, since the right side is odd
under `z ↦ -z̄`. -/
lemma not_hasMaassSineExpansion_const_one : ¬HasMaassSineExpansion (fun _ ↦ 1) r c := by
  intro h
  have h1 : (1 : ℂ) = -1 := h.isOddMaassForm I
  norm_num at h1

/-- **The constant newform has the junk coefficients `0`**: having neither a cosine nor a sine
expansion, the constant Maass newform `1` of level `1` gets `maassCoefficients R 1 = 0` for every
spectral parameter `R`. -/
lemma maassCoefficients_const_one : maassCoefficients r (fun _ ↦ 1) = 0 := by
  rw [maassCoefficients, dite_eq_right fun ⟨c, h⟩ ↦ not_hasMaassCosineExpansion_const_one r c h,
    dite_eq_right fun ⟨c, h⟩ ↦ not_hasMaassSineExpansion_const_one r c h]

end UpperHalfPlane
