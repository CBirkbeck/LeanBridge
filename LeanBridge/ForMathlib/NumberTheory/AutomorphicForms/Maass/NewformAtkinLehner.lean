import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.ConstantTerm
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.EigenvalueReal
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.MainLemma
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformCoefficientsReal

/-!
# The coefficients of Maass newforms at every level

Let `F` be a Maass newform of weight `0` on `Γ₀(N)`, `N ≠ 0`, with trivial character and spectral
parameter `R` (`UpperHalfPlane.IsMaassNewform`), with a cosine or sine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` (resp. `sin(2πnx)`) (LMFDB
`mf.maass.mwf.coefficients`). Such an expansion exists for every even (odd) cusp newform and for
every even (odd) newform with real `R`. By the Main Lemma of Atkin and Lehner
(`UpperHalfPlane.mem_maassOldSpace_of_maassCoprimeFilter_eq_zero`), a form in the new space whose
coefficients vanish at every index prime to `N` is `0`. Hence:

* two elements of the new space with the same coefficients prime to `N` are equal (strong
  multiplicity one inside the new space);
* `a(1) ≠ 0`, since otherwise the Hecke relations make every coefficient prime to `N` vanish;
* the normalised newform `F / a(1)` (`UpperHalfPlane.maassNormalisedNewform`) is real-valued: the
  eigenvalue `1/4 + R²` is real (`UpperHalfPlane.conj_eigenvalue_of_mem_maassSpace`), so that `R` is
  real or purely imaginary and `K_{iR}` is real, the complex conjugate of the normalised newform
  lies in the new space with the conjugate coefficients, and these agree with the coefficients of
  the normalised newform at every index prime to `N`
  (`UpperHalfPlane.IsMaassNewform.conj_coeff_div_of_hasMaassCosineExpansion`);
* so all its coefficients `a(n) / a(1)` are real.

No statement on the operators `U_p`, `p ∣ N`, is needed for the reality.

This is the knowl `mf.maass.mwf.coefficients`, read for cusp newforms (of any spectral parameter)
and for newforms with real spectral parameter, normalised by `a(1) = 1`: the constant `1` of level
`1` is a newform in the sense of the linked knowl `mf.maass.mwf` with spectral parameter `R = ±i/2`
and has no expansion (`UpperHalfPlane.not_hasMaassCosineExpansion_const_one`), and a nonzero
multiple of a newform is a newform, so that the coefficients are only real after this
normalisation.

Outside this reading are the non-cuspidal newforms with non-real `R`. Such a form whose constant
term at `∞` vanishes has the expansion
(`UpperHalfPlane.IsMaassNewform.hasMaassCosineExpansion_of_integral_eq_zero` and its sine analogue),
and the results below apply to it. That the constant `1` of level `1` is the only other one (the
residual spectrum of `Γ₀(N)` consists of the constants) is classical and not proved here; no
statement of this file uses it.

## Main definitions

* `UpperHalfPlane.maassNormalisedNewform` (LMFDB `mf.maass.mwf.coefficients`): the newform
  `F / a(1)`, whose first coefficient is `1`.

## Main results

* `UpperHalfPlane.conj_mem_maassSpace`, `UpperHalfPlane.conj_mem_maassOldSpace`,
  `UpperHalfPlane.conj_mem_maassNewSpace`: complex conjugation preserves the space of Maass forms of
  trivial character, its old space and its new space, up to conjugating the eigenvalue.
* `UpperHalfPlane.eq_of_mem_maassNewSpace_of_cosine`,
  `UpperHalfPlane.eq_of_mem_maassNewSpace_of_sine`: strong multiplicity one inside the new space.
* `UpperHalfPlane.IsMaassNewform.coeff_one_ne_zero_of_cosine`,
  `UpperHalfPlane.IsMaassNewform.coeff_one_ne_zero_of_sine`: `a(1) ≠ 0` at every level.
* `UpperHalfPlane.IsMaassNewform.conj_smul_eq_of_cosine`,
  `UpperHalfPlane.IsMaassNewform.conj_smul_eq_of_sine`: `conj F / conj a(1) = F / a(1)`.
* `UpperHalfPlane.IsMaassNewform.conj_coeff_div_of_cosine`,
  `UpperHalfPlane.IsMaassNewform.conj_coeff_div_of_sine`: `a(n) / a(1)` is real for every `n`.
* `UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_even`,
  `UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_odd`,
  `UpperHalfPlane.IsMaassCuspNewform.conj_maassCoefficients_div_of_even`,
  `UpperHalfPlane.IsMaassCuspNewform.conj_maassCoefficients_div_of_odd`: the same for
  `a = maassCoefficients R F` of an even or odd cusp newform, with any spectral parameter.
* `UpperHalfPlane.IsMaassNewform.maassCoefficients_one_ne_zero_of_even_ofReal`,
  `UpperHalfPlane.IsMaassNewform.maassCoefficients_one_ne_zero_of_odd_ofReal`,
  `UpperHalfPlane.IsMaassNewform.conj_maassCoefficients_div_of_even_ofReal`,
  `UpperHalfPlane.IsMaassNewform.conj_maassCoefficients_div_of_odd_ofReal`: the same for an even or
  odd newform with real spectral parameter.
* `UpperHalfPlane.IsMaassCuspNewform.normalisedNewform_of_even`,
  `UpperHalfPlane.IsMaassCuspNewform.normalisedNewform_of_odd`: the normalised even or odd cusp
  newform is a cusp newform.
* `UpperHalfPlane.HasMaassCosineExpansion.normalisedNewform`,
  `UpperHalfPlane.HasMaassSineExpansion.normalisedNewform`: its expansion.
* `UpperHalfPlane.HasMaassCosineExpansion.maassCoefficients_normalisedNewform`,
  `UpperHalfPlane.HasMaassSineExpansion.maassCoefficients_normalisedNewform`: its coefficients are
  `a(n) / a(1)`.
* `UpperHalfPlane.IsMaassNewform.maassCoefficients_normalisedNewform_one_of_cosine`,
  `UpperHalfPlane.IsMaassNewform.maassCoefficients_normalisedNewform_one_of_sine`: its first
  coefficient is `1`.
* `UpperHalfPlane.IsMaassNewform.conj_maassCoefficients_normalisedNewform_of_cosine`,
  `UpperHalfPlane.IsMaassNewform.conj_maassCoefficients_normalisedNewform_of_sine`: its coefficients
  are real.
* `UpperHalfPlane.IsMaassNewform.conj_maassNormalisedNewform_of_cosine`,
  `UpperHalfPlane.IsMaassNewform.conj_maassNormalisedNewform_of_sine`: it is real-valued.
* `UpperHalfPlane.IsMaassCuspNewform.conj_maassNormalisedNewform` (LMFDB `portrait.maass`): the
  normalised newform of a cusp newform takes real values.
* `UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_normalisedNewform_one_of_even`,
  `UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_normalisedNewform_one_of_odd`,
  `UpperHalfPlane.IsMaassCuspNewform.conj_maassCoefficients_normalisedNewform_of_even`,
  `UpperHalfPlane.IsMaassCuspNewform.conj_maassCoefficients_normalisedNewform_of_odd`: for an even
  or odd cusp newform, with any spectral parameter and no expansion as a hypothesis, the first
  coefficient of the normalised newform is `1` and all its coefficients are real.
-/

open scoped ComplexConjugate

namespace UpperHalfPlane

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {eigenvalue r R : ℂ} {F G : ℍ → ℂ} {f : ℂ → ℂ}
  {c c' : ℕ+ → ℂ} {z : ℂ} {t : ℝ}

/-- **The complex conjugate of a Maass form is a Maass form**, with the conjugate eigenvalue:
`conj ∘ F` lies in `M(N, 1, conj λ)` for `F` in `M(N, 1, λ)`. -/
lemma conj_mem_maassSpace (hF : F ∈ maassSpace N 1 eigenvalue) :
    (fun τ ↦ conj (F τ)) ∈ maassSpace N 1 (conj eigenvalue) := by
  refine ⟨Complex.conjCLE.contDiff.comp_contDiffOn hF.1, ?_, fun γ hγ τ ↦ ?_, fun w hw ↦ ?_⟩
  · simpa using hF.2.1
  · simp only [Function.comp_apply, ofComplex_apply, dirichletCharacter_one_apply_of_mem_gamma0 hγ,
      one_mul]
    rw [smul_eq_of_mem_maassSpace_one hF hγ]
  · have h : hyperbolicLaplacian ((fun τ ↦ conj (F τ)) ∘ ofComplex) w =
        conj (hyperbolicLaplacian (F ∘ ofComplex) w) := hyperbolicLaplacian_conj
    rw [h]
    simpa only [map_add, map_mul, map_zero, Function.comp_apply] using
      congrArg conj (hF.2.2.2 w hw)

lemma conj_sq_of_mem_maassSpace (hF : F ∈ maassSpace N χ (maassEigenvalue r)) (hF0 : F ≠ 0) :
    conj (r ^ 2) = r ^ 2 := by
  have h : conj (maassEigenvalue r) = maassEigenvalue r := conj_eigenvalue_of_mem_maassSpace hF hF0
  simp only [maassEigenvalue, map_add, map_div₀, map_one, map_ofNat] at h
  exact add_left_cancel h

lemma conj_maassEigenvalue_of_conj_sq (hr : conj (r ^ 2) = r ^ 2) :
    conj (maassEigenvalue r) = maassEigenvalue r := by
  simp only [maassEigenvalue, map_add, map_div₀, map_one, map_ofNat, hr]

lemma HasMaassCosineExpansion.const_mul (a : ℂ) (h : HasMaassCosineExpansion (F ∘ ofComplex) r c) :
    HasMaassCosineExpansion ((a • F) ∘ ofComplex) r fun n ↦ a * c n := by
  intro z
  have h1 : ((a • F) ∘ ofComplex) z = a * (F ∘ ofComplex) z := rfl
  rw [h1]
  simpa only [mul_assoc] using (h z).mul_left a

lemma HasMaassSineExpansion.const_mul (a : ℂ) (h : HasMaassSineExpansion (F ∘ ofComplex) r c) :
    HasMaassSineExpansion ((a • F) ∘ ofComplex) r fun n ↦ a * c n := by
  intro z
  have h1 : ((a • F) ∘ ofComplex) z = a * (F ∘ ofComplex) z := rfl
  rw [h1]
  simpa only [mul_assoc] using (h z).mul_left a

variable (R F) in
/-- The **normalised newform** `F / a(1)` (LMFDB `mf.maass.mwf.coefficients`) of a function `F` on
`ℍ` with spectral parameter `R`, for `a = maassCoefficients R F`. An even (odd) cusp newform has the
cosine (sine) expansion (`IsMaassCuspNewform.hasMaassCosineExpansion`,
`IsMaassCuspNewform.hasMaassSineExpansion`), with unique coefficients
(`HasMaassCosineExpansion.unique`, `HasMaassSineExpansion.unique`), and this function is then again
a cusp newform (`IsMaassCuspNewform.normalisedNewform_of_even`,
`IsMaassCuspNewform.normalisedNewform_of_odd`) with first coefficient `1`
(`IsMaassCuspNewform.maassCoefficients_normalisedNewform_one_of_even`,
`IsMaassCuspNewform.maassCoefficients_normalisedNewform_one_of_odd`) and real coefficients
(`IsMaassCuspNewform.conj_maassCoefficients_normalisedNewform_of_even`,
`IsMaassCuspNewform.conj_maassCoefficients_normalisedNewform_of_odd`). More generally, for an even
or odd newform with a cosine or sine expansion, such as a newform with real `R`, the first
coefficient is `1`, the coefficients are real and this function is real-valued
(`IsMaassNewform.maassCoefficients_normalisedNewform_one_of_cosine`,
`IsMaassNewform.conj_maassCoefficients_normalisedNewform_of_cosine`,
`IsMaassNewform.conj_maassNormalisedNewform_of_cosine`, and the sine versions). The constant newform
`1` of level `1` has no expansion: its `a(1)` is the junk value `0`, and this function is `0`. The
LMFDB's coefficients and `L`-function `L(f, s) = ∑ a(n) n^{-s}` (`maassLFunction`) are those of this
form. -/
noncomputable def maassNormalisedNewform : ℍ → ℂ :=
  (maassCoefficients R (F ∘ ofComplex) 1)⁻¹ • F

/-- **The cosine expansion of the normalised newform**: if `F` has the cosine expansion with
coefficients `a(n)`, then `F / a(1)` has the cosine expansion with coefficients `a(n) / a(1)`. -/
lemma HasMaassCosineExpansion.normalisedNewform (hc : HasMaassCosineExpansion (F ∘ ofComplex) R c) :
    HasMaassCosineExpansion (maassNormalisedNewform R F ∘ ofComplex) R fun n ↦ c n / c 1 := by
  rw [maassNormalisedNewform, hc.maassCoefficients_eq]
  simpa only [inv_mul_eq_div] using hc.const_mul (c 1)⁻¹

/-- **The sine expansion of the normalised newform**: if `F` has the sine expansion with
coefficients `a(n)`, then `F / a(1)` has the sine expansion with coefficients `a(n) / a(1)`. -/
lemma HasMaassSineExpansion.normalisedNewform (hc : HasMaassSineExpansion (F ∘ ofComplex) R c) :
    HasMaassSineExpansion (maassNormalisedNewform R F ∘ ofComplex) R fun n ↦ c n / c 1 := by
  rw [maassNormalisedNewform, hc.maassCoefficients_eq]
  simpa only [inv_mul_eq_div] using hc.const_mul (c 1)⁻¹

/-- **The coefficients of the normalised even newform**: `maassCoefficients R (F / a(1))` is
`a(n) / a(1)`. -/
lemma HasMaassCosineExpansion.maassCoefficients_normalisedNewform
    (hc : HasMaassCosineExpansion (F ∘ ofComplex) R c) :
    maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) = fun n ↦ c n / c 1 :=
  hc.normalisedNewform.maassCoefficients_eq

/-- **The coefficients of the normalised odd newform**: `maassCoefficients R (F / a(1))` is
`a(n) / a(1)`. -/
lemma HasMaassSineExpansion.maassCoefficients_normalisedNewform
    (hc : HasMaassSineExpansion (F ∘ ofComplex) R c) :
    maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) = fun n ↦ c n / c 1 :=
  hc.normalisedNewform.maassCoefficients_eq

lemma IsMaassCuspNewform.const_smul (hF : IsMaassCuspNewform N R F) {a : ℂ} (ha : a ≠ 0) :
    IsMaassCuspNewform N R (a • F) := by
  refine ⟨⟨Submodule.smul_mem _ a hF.1.1, smul_ne_zero ha hF.1.2.1, fun p hp hpN ↦ ?_⟩,
    fun γ y hy ↦ ?_⟩
  · rcases hF.1.2.2 p hp hpN with ⟨e, he⟩
    refine ⟨e, fun z ↦ ?_⟩
    have h : e * (a • F) z = a * (e * F z) := by
      simp only [Pi.smul_apply]
      ring1
    rw [h, ← he z]
    simp only [maassHeckeOperatorChar, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum]
    ring1
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul, hF.2 γ y hy, mul_zero]

variable [NeZero N]

/-- **The complex conjugate of an oldform is old**: `conj ∘ G` lies in the old space of
`M(N, 1, conj λ)` for `G` in the old space of `M(N, 1, λ)`, `N ≠ 0`. -/
lemma conj_mem_maassOldSpace (hG : G ∈ maassOldSpace N 1 eigenvalue) :
    (fun τ ↦ conj (G τ)) ∈ maassOldSpace N 1 (conj eigenvalue) := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨hx, M, d, hM, χ', hMN, hd, hχ, G', hG', rfl⟩
    have hχ' : χ' = 1 := DirichletCharacter.changeLevel_injective hM <| by
      rw [hχ, DirichletCharacter.changeLevel_one]
    subst hχ'
    exact Submodule.subset_span ⟨conj_mem_maassSpace hx, M, d, hM, 1, hMN, hd, hχ, _,
      conj_mem_maassSpace hG', rfl⟩
  | zero =>
    convert zero_mem (maassOldSpace N 1 (conj eigenvalue)) using 1
    funext τ
    simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext τ
    simp
  | smul a x _ hx =>
    convert Submodule.smul_mem _ (conj a) hx using 1
    funext τ
    simp

/-- **The complex conjugate of a new form is new**: `conj ∘ F` lies in the new space of
`M(N, 1, conj λ)` for `F` in the new space of `M(N, 1, λ)`, `N ≠ 0`, since
`⟨conj F, G⟩ = conj ⟨F, conj G⟩`. -/
lemma conj_mem_maassNewSpace (hF : F ∈ maassNewSpace N 1 eigenvalue) :
    (fun τ ↦ conj (F τ)) ∈ maassNewSpace N 1 (conj eigenvalue) := by
  refine ⟨conj_mem_maassSpace hF.1, fun G hG ↦ ?_⟩
  have h : maassPetersson N F (fun τ ↦ conj (G τ)) = 0 := hF.2 _ <| by
    simpa using conj_mem_maassOldSpace hG
  have h1 :
      maassPetersson N (fun τ ↦ conj (F τ)) G = conj (maassPetersson N F fun τ ↦ conj (G τ)) := by
    simp only [maassPetersson]
    rw [← integral_conj]
    simp
  rw [h1, h, map_zero]

/-- **Strong multiplicity one inside the new space, for cosine expansions**: two elements `F`, `G`
of the new space of `M(N, 1, λ)`, `N ≠ 0`, whose cosine coefficients agree at every index prime to
`N` are equal, `F - G` being old by the Main Lemma and new. -/
lemma eq_of_mem_maassNewSpace_of_cosine (hF : F ∈ maassNewSpace N 1 eigenvalue)
    (hG : G ∈ maassNewSpace N 1 eigenvalue) (hcF : HasMaassCosineExpansion (F ∘ ofComplex) r c)
    (hcG : HasMaassCosineExpansion (G ∘ ofComplex) r c')
    (h : ∀ n : ℕ+, (n : ℕ).Coprime N → c n = c' n) : F = G := by
  have hsub : HasMaassCosineExpansion ((F - G) ∘ ofComplex) r fun n ↦ c n - c' n := fun z ↦ by
    refine ((hcF z).sub (hcG z)).congr_fun fun n ↦ ?_
    ring1
  exact sub_eq_zero.mp <| Submodule.disjoint_def.mp
    (disjoint_maassOldSpace_maassNewSpace N 1 eigenvalue) _
    (mem_maassOldSpace_of_hasMaassCosineExpansion (sub_mem hF.1 hG.1) hsub fun n hn ↦
      sub_eq_zero.mpr (h n hn)) (sub_mem hF hG)

/-- **Strong multiplicity one inside the new space, for sine expansions**: two elements `F`, `G` of
the new space of `M(N, 1, λ)`, `N ≠ 0`, whose sine coefficients agree at every index prime to `N`
are equal. -/
lemma eq_of_mem_maassNewSpace_of_sine (hF : F ∈ maassNewSpace N 1 eigenvalue)
    (hG : G ∈ maassNewSpace N 1 eigenvalue) (hcF : HasMaassSineExpansion (F ∘ ofComplex) r c)
    (hcG : HasMaassSineExpansion (G ∘ ofComplex) r c')
    (h : ∀ n : ℕ+, (n : ℕ).Coprime N → c n = c' n) : F = G := by
  have hsub : HasMaassSineExpansion ((F - G) ∘ ofComplex) r fun n ↦ c n - c' n := fun z ↦ by
    refine ((hcF z).sub (hcG z)).congr_fun fun n ↦ ?_
    ring1
  exact sub_eq_zero.mp <| Submodule.disjoint_def.mp
    (disjoint_maassOldSpace_maassNewSpace N 1 eigenvalue) _
    (mem_maassOldSpace_of_hasMaassSineExpansion (sub_mem hF.1 hG.1) hsub fun n hn ↦
      sub_eq_zero.mpr (h n hn)) (sub_mem hF hG)

/-- **An even Maass newform has `a(1) ≠ 0`** (LMFDB `mf.maass.mwf.coefficients`), at every level
`N ≠ 0`: for a Maass newform `F` of weight `0` on `Γ₀(N)` with trivial character and the cosine
expansion `F(x + iy) = ∑ a(n) √y K_{iR}(2πny) cos(2πnx)`, `a(1) ≠ 0`. If `a(1) = 0`, the Hecke
relations give `a(n) = 0` for every `n` prime to `N`, so `F` is old by the Main Lemma, and `F` is
also new, hence `F = 0`. -/
lemma IsMaassNewform.coeff_one_ne_zero_of_cosine (hF : IsMaassNewform N 1 eigenvalue F)
    (hc : HasMaassCosineExpansion (F ∘ ofComplex) r c) : c 1 ≠ 0 :=
  fun h1 ↦ hF.2.1 <| Submodule.disjoint_def.mp (disjoint_maassOldSpace_maassNewSpace N 1 eigenvalue)
    F (mem_maassOldSpace_of_hasMaassCosineExpansion hF.1.1 hc fun _ hn ↦
      coeff_eq_zero_of_coprime h1 (fun _ hp hpN ↦ (hF.exists_maassHeckeOperator_eq hp hpN).imp
        fun _ he ↦ hc.coeff_mul_add_eq hp he.2) hn) hF.1

/-- **An odd Maass newform has `a(1) ≠ 0`** (LMFDB `mf.maass.mwf.coefficients`), at every level
`N ≠ 0`: for a Maass newform `F` of weight `0` on `Γ₀(N)` with trivial character and the sine
expansion `F(x + iy) = ∑ a(n) √y K_{iR}(2πny) sin(2πnx)`, `a(1) ≠ 0`. -/
lemma IsMaassNewform.coeff_one_ne_zero_of_sine (hF : IsMaassNewform N 1 eigenvalue F)
    (hc : HasMaassSineExpansion (F ∘ ofComplex) r c) : c 1 ≠ 0 :=
  fun h1 ↦ hF.2.1 <| Submodule.disjoint_def.mp (disjoint_maassOldSpace_maassNewSpace N 1 eigenvalue)
    F (mem_maassOldSpace_of_hasMaassSineExpansion hF.1.1 hc fun _ hn ↦
      coeff_eq_zero_of_coprime h1 (fun _ hp hpN ↦ (hF.exists_maassHeckeOperator_eq hp hpN).imp
        fun _ he ↦ hc.coeff_mul_add_eq hp he.2) hn) hF.1

lemma IsMaassNewform.conj_mem_new (hF : IsMaassNewform N 1 (maassEigenvalue r) F) :
    (fun τ ↦ conj (F τ)) ∈ maassNewSpace N 1 (maassEigenvalue r) := by
  have h : (fun τ ↦ conj (F τ)) ∈ maassNewSpace N 1 (conj (maassEigenvalue r)) :=
    conj_mem_maassNewSpace hF.1
  rwa [conj_maassEigenvalue_of_conj_sq (conj_sq_of_mem_maassSpace hF.1.1 hF.2.1)] at h

/-- **The normalised even newform is real-valued** (LMFDB `mf.maass.mwf.coefficients`): for a Maass
newform `F` on `Γ₀(N)`, `N ≠ 0`, with spectral parameter `R` and the cosine expansion with
coefficients `a(n)`, the function `conj F / conj a(1)` equals `F / a(1)`. Both lie in the new space,
and their coefficients agree at every index prime to `N`. -/
lemma IsMaassNewform.conj_smul_eq_of_cosine (hF : IsMaassNewform N 1 (maassEigenvalue r) F)
    (hc : HasMaassCosineExpansion (F ∘ ofComplex) r c) :
    (conj (c 1))⁻¹ • (fun τ ↦ conj (F τ)) = (c 1)⁻¹ • F := by
  have hr : conj (r ^ 2) = r ^ 2 := conj_sq_of_mem_maassSpace hF.1.1 hF.2.1
  have hconj : HasMaassCosineExpansion ((fun τ ↦ conj (F τ)) ∘ ofComplex) r fun n ↦ conj (c n) :=
    hc.conj_of_conj_sq hr
  refine eq_of_mem_maassNewSpace_of_cosine (Submodule.smul_mem _ _ hF.conj_mem_new)
    (Submodule.smul_mem _ _ hF.1) (hconj.const_mul _) (hc.const_mul _) fun n hn ↦ ?_
  have h : conj (c n / c 1) = c n / c 1 :=
    hF.conj_coeff_div_of_hasMaassCosineExpansion hc (hF.coeff_one_ne_zero_of_cosine hc) hn
  rw [map_div₀] at h
  rw [inv_mul_eq_div, inv_mul_eq_div, h]

/-- **The normalised odd newform is real-valued** (LMFDB `mf.maass.mwf.coefficients`): for a Maass
newform `F` on `Γ₀(N)`, `N ≠ 0`, with spectral parameter `R` and the sine expansion with
coefficients `a(n)`, the function `conj F / conj a(1)` equals `F / a(1)`. -/
lemma IsMaassNewform.conj_smul_eq_of_sine (hF : IsMaassNewform N 1 (maassEigenvalue r) F)
    (hc : HasMaassSineExpansion (F ∘ ofComplex) r c) :
    (conj (c 1))⁻¹ • (fun τ ↦ conj (F τ)) = (c 1)⁻¹ • F := by
  have hr : conj (r ^ 2) = r ^ 2 := conj_sq_of_mem_maassSpace hF.1.1 hF.2.1
  have hconj : HasMaassSineExpansion ((fun τ ↦ conj (F τ)) ∘ ofComplex) r fun n ↦ conj (c n) :=
    hc.conj_of_conj_sq hr
  refine eq_of_mem_maassNewSpace_of_sine (Submodule.smul_mem _ _ hF.conj_mem_new)
    (Submodule.smul_mem _ _ hF.1) (hconj.const_mul _) (hc.const_mul _) fun n hn ↦ ?_
  have h : conj (c n / c 1) = c n / c 1 :=
    hF.conj_coeff_div_of_hasMaassSineExpansion hc (hF.coeff_one_ne_zero_of_sine hc) hn
  rw [map_div₀] at h
  rw [inv_mul_eq_div, inv_mul_eq_div, h]

/-- **The coefficients of the normalised even Maass newform are real at every index** (LMFDB
`mf.maass.mwf.coefficients`): for a Maass newform `F` on `Γ₀(N)`, `N ≠ 0`, with spectral parameter
`R` and the cosine expansion `F(x + iy) = ∑ a(n) √y K_{iR}(2πny) cos(2πnx)`, the coefficient
`a(n) / a(1)` of the newform normalised by `a(1) = 1` is real for every `n ≥ 1`. -/
lemma IsMaassNewform.conj_coeff_div_of_cosine (hF : IsMaassNewform N 1 (maassEigenvalue r) F)
    (hc : HasMaassCosineExpansion (F ∘ ofComplex) r c) (n : ℕ+) : conj (c n / c 1) = c n / c 1 := by
  have hconj : HasMaassCosineExpansion ((fun τ ↦ conj (F τ)) ∘ ofComplex) r fun n ↦ conj (c n) :=
    hc.conj_of_conj_sq (conj_sq_of_mem_maassSpace hF.1.1 hF.2.1)
  have h1 : HasMaassCosineExpansion (((conj (c 1))⁻¹ • fun τ ↦ conj (F τ)) ∘ ofComplex) r
      fun n ↦ (conj (c 1))⁻¹ * conj (c n) := hconj.const_mul _
  rw [hF.conj_smul_eq_of_cosine hc] at h1
  have h2 : (conj (c 1))⁻¹ * conj (c n) = (c 1)⁻¹ * c n :=
    congrFun (h1.unique (hc.const_mul (c 1)⁻¹)) n
  rw [map_div₀, div_eq_inv_mul, div_eq_inv_mul, h2]

/-- **The coefficients of the normalised odd Maass newform are real at every index** (LMFDB
`mf.maass.mwf.coefficients`): for a Maass newform `F` on `Γ₀(N)`, `N ≠ 0`, with spectral parameter
`R` and the sine expansion `F(x + iy) = ∑ a(n) √y K_{iR}(2πny) sin(2πnx)`, the coefficient
`a(n) / a(1)` of the newform normalised by `a(1) = 1` is real for every `n ≥ 1`. -/
lemma IsMaassNewform.conj_coeff_div_of_sine (hF : IsMaassNewform N 1 (maassEigenvalue r) F)
    (hc : HasMaassSineExpansion (F ∘ ofComplex) r c) (n : ℕ+) : conj (c n / c 1) = c n / c 1 := by
  have hconj : HasMaassSineExpansion ((fun τ ↦ conj (F τ)) ∘ ofComplex) r fun n ↦ conj (c n) :=
    hc.conj_of_conj_sq (conj_sq_of_mem_maassSpace hF.1.1 hF.2.1)
  have h1 : HasMaassSineExpansion (((conj (c 1))⁻¹ • fun τ ↦ conj (F τ)) ∘ ofComplex) r
      fun n ↦ (conj (c 1))⁻¹ * conj (c n) := hconj.const_mul _
  rw [hF.conj_smul_eq_of_sine hc] at h1
  have h2 : (conj (c 1))⁻¹ * conj (c n) = (c 1)⁻¹ * c n :=
    congrFun (h1.unique (hc.const_mul (c 1)⁻¹)) n
  rw [map_div₀, div_eq_inv_mul, div_eq_inv_mul, h2]

/-- **An even Maass cusp newform has `a(1) ≠ 0`** (LMFDB `mf.maass.mwf.coefficients`), at every
level `N ≠ 0`, for `a = maassCoefficients R F`. -/
lemma IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_even (hF : IsMaassCuspNewform N R F)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) : maassCoefficients R (F ∘ ofComplex) 1 ≠ 0 :=
  hF.1.coeff_one_ne_zero_of_cosine (hF.hasMaassCosineExpansion hs)

/-- **An odd Maass cusp newform has `a(1) ≠ 0`** (LMFDB `mf.maass.mwf.coefficients`), at every level
`N ≠ 0`, for `a = maassCoefficients R F`. -/
lemma IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_odd (hF : IsMaassCuspNewform N R F)
    (hs : IsOddMaassForm (F ∘ ofComplex)) : maassCoefficients R (F ∘ ofComplex) 1 ≠ 0 :=
  hF.1.coeff_one_ne_zero_of_sine (hF.hasMaassSineExpansion hs)

/-- **The normalised even cusp newform is a cusp newform**, `a(1)` being nonzero. -/
lemma IsMaassCuspNewform.normalisedNewform_of_even (hF : IsMaassCuspNewform N R F)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) : IsMaassCuspNewform N R (maassNormalisedNewform R F) :=
  hF.const_smul <| inv_ne_zero <| hF.maassCoefficients_one_ne_zero_of_even hs

/-- **The normalised odd cusp newform is a cusp newform**, `a(1)` being nonzero. -/
lemma IsMaassCuspNewform.normalisedNewform_of_odd (hF : IsMaassCuspNewform N R F)
    (hs : IsOddMaassForm (F ∘ ofComplex)) : IsMaassCuspNewform N R (maassNormalisedNewform R F) :=
  hF.const_smul <| inv_ne_zero <| hF.maassCoefficients_one_ne_zero_of_odd hs

/-- **All the coefficients of the normalised even Maass cusp newform are real** (LMFDB
`mf.maass.mwf.coefficients`), at every level `N ≠ 0`, for `a = maassCoefficients R F` and every
spectral parameter `R`: `a(n) / a(1)` is real for every `n ≥ 1`, with `a(1) ≠ 0`
(`IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_even`). -/
lemma IsMaassCuspNewform.conj_maassCoefficients_div_of_even (hF : IsMaassCuspNewform N R F)
    (hs : IsEvenMaassForm (F ∘ ofComplex)) (n : ℕ+) :
    conj (maassCoefficients R (F ∘ ofComplex) n / maassCoefficients R (F ∘ ofComplex) 1) =
      maassCoefficients R (F ∘ ofComplex) n / maassCoefficients R (F ∘ ofComplex) 1 :=
  hF.1.conj_coeff_div_of_cosine (hF.hasMaassCosineExpansion hs) n

/-- **All the coefficients of the normalised odd Maass cusp newform are real** (LMFDB
`mf.maass.mwf.coefficients`), at every level `N ≠ 0`, for `a = maassCoefficients R F` and every
spectral parameter `R`: `a(n) / a(1)` is real for every `n ≥ 1`, with `a(1) ≠ 0`
(`IsMaassCuspNewform.maassCoefficients_one_ne_zero_of_odd`). -/
lemma IsMaassCuspNewform.conj_maassCoefficients_div_of_odd (hF : IsMaassCuspNewform N R F)
    (hs : IsOddMaassForm (F ∘ ofComplex)) (n : ℕ+) :
    conj (maassCoefficients R (F ∘ ofComplex) n / maassCoefficients R (F ∘ ofComplex) 1) =
      maassCoefficients R (F ∘ ofComplex) n / maassCoefficients R (F ∘ ofComplex) 1 :=
  hF.1.conj_coeff_div_of_sine (hF.hasMaassSineExpansion hs) n

/-- **An even Maass newform with real spectral parameter has `a(1) ≠ 0`** (LMFDB
`mf.maass.mwf.coefficients`), at every level `N ≠ 0`, for `a = maassCoefficients R F`, with no
cuspidality hypothesis. -/
lemma IsMaassNewform.maassCoefficients_one_ne_zero_of_even_ofReal
    (hF : IsMaassNewform N 1 (maassEigenvalue t) F) (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    maassCoefficients t (F ∘ ofComplex) 1 ≠ 0 :=
  hF.coeff_one_ne_zero_of_cosine (hF.hasMaassCosineExpansion_ofReal hs)

/-- **An odd Maass newform with real spectral parameter has `a(1) ≠ 0`** (LMFDB
`mf.maass.mwf.coefficients`), at every level `N ≠ 0`, for `a = maassCoefficients R F`, with no
cuspidality hypothesis. -/
lemma IsMaassNewform.maassCoefficients_one_ne_zero_of_odd_ofReal
    (hF : IsMaassNewform N 1 (maassEigenvalue t) F) (hs : IsOddMaassForm (F ∘ ofComplex)) :
    maassCoefficients t (F ∘ ofComplex) 1 ≠ 0 :=
  hF.coeff_one_ne_zero_of_sine (hF.hasMaassSineExpansion_ofReal hs)

/-- **All the coefficients of the normalised even Maass newform with real spectral parameter are
real** (LMFDB `mf.maass.mwf.coefficients`), at every level `N ≠ 0`, for `a = maassCoefficients R F`,
with no cuspidality hypothesis: `a(n) / a(1)` is real for every `n ≥ 1`. -/
lemma IsMaassNewform.conj_maassCoefficients_div_of_even_ofReal
    (hF : IsMaassNewform N 1 (maassEigenvalue t) F) (hs : IsEvenMaassForm (F ∘ ofComplex))
    (n : ℕ+) :
    conj (maassCoefficients t (F ∘ ofComplex) n / maassCoefficients t (F ∘ ofComplex) 1) =
      maassCoefficients t (F ∘ ofComplex) n / maassCoefficients t (F ∘ ofComplex) 1 :=
  hF.conj_coeff_div_of_cosine (hF.hasMaassCosineExpansion_ofReal hs) n

/-- **All the coefficients of the normalised odd Maass newform with real spectral parameter are
real** (LMFDB `mf.maass.mwf.coefficients`), at every level `N ≠ 0`, for `a = maassCoefficients R F`,
with no cuspidality hypothesis: `a(n) / a(1)` is real for every `n ≥ 1`. -/
lemma IsMaassNewform.conj_maassCoefficients_div_of_odd_ofReal
    (hF : IsMaassNewform N 1 (maassEigenvalue t) F) (hs : IsOddMaassForm (F ∘ ofComplex)) (n : ℕ+) :
    conj (maassCoefficients t (F ∘ ofComplex) n / maassCoefficients t (F ∘ ofComplex) 1) =
      maassCoefficients t (F ∘ ofComplex) n / maassCoefficients t (F ∘ ofComplex) 1 :=
  hF.conj_coeff_div_of_sine (hF.hasMaassSineExpansion_ofReal hs) n

/-- **The first coefficient of the normalised even newform is `1`** (LMFDB
`mf.maass.mwf.coefficients`). -/
lemma IsMaassNewform.maassCoefficients_normalisedNewform_one_of_cosine
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F)
    (hc : HasMaassCosineExpansion (F ∘ ofComplex) R c) :
    maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) 1 = 1 := by
  rw [hc.maassCoefficients_normalisedNewform]
  exact div_self (hF.coeff_one_ne_zero_of_cosine hc)

/-- **The first coefficient of the normalised odd newform is `1`** (LMFDB
`mf.maass.mwf.coefficients`). -/
lemma IsMaassNewform.maassCoefficients_normalisedNewform_one_of_sine
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F)
    (hc : HasMaassSineExpansion (F ∘ ofComplex) R c) :
    maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) 1 = 1 := by
  rw [hc.maassCoefficients_normalisedNewform]
  exact div_self (hF.coeff_one_ne_zero_of_sine hc)

/-- **The coefficients of the normalised even newform are real** (LMFDB
`mf.maass.mwf.coefficients`): every coefficient of the normalised newform of a Maass newform with a
cosine expansion is real, at every level `N ≠ 0`. -/
lemma IsMaassNewform.conj_maassCoefficients_normalisedNewform_of_cosine
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F)
    (hc : HasMaassCosineExpansion (F ∘ ofComplex) R c) (n : ℕ+) :
    conj (maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) n) =
      maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) n := by
  rw [hc.maassCoefficients_normalisedNewform]
  exact hF.conj_coeff_div_of_cosine hc n

/-- **The coefficients of the normalised odd newform are real** (LMFDB
`mf.maass.mwf.coefficients`): every coefficient of the normalised newform of a Maass newform with a
sine expansion is real, at every level `N ≠ 0`. -/
lemma IsMaassNewform.conj_maassCoefficients_normalisedNewform_of_sine
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F) (hc : HasMaassSineExpansion (F ∘ ofComplex) R c)
    (n : ℕ+) : conj (maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) n) =
      maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) n := by
  rw [hc.maassCoefficients_normalisedNewform]
  exact hF.conj_coeff_div_of_sine hc n

/-- **The normalised even newform is real-valued** on `ℍ` (LMFDB `mf.maass.mwf.coefficients`). -/
lemma IsMaassNewform.conj_maassNormalisedNewform_of_cosine
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F)
    (hc : HasMaassCosineExpansion (F ∘ ofComplex) R c) (τ : ℍ) :
    conj (maassNormalisedNewform R F τ) = maassNormalisedNewform R F τ := by
  have h : (conj (c 1))⁻¹ * conj (F τ) = (c 1)⁻¹ * F τ :=
    congrFun (hF.conj_smul_eq_of_cosine hc) τ
  simp only [maassNormalisedNewform, hc.maassCoefficients_eq, Pi.smul_apply, smul_eq_mul, map_mul,
    map_inv₀, h]

/-- **The normalised odd newform is real-valued** on `ℍ` (LMFDB `mf.maass.mwf.coefficients`). -/
lemma IsMaassNewform.conj_maassNormalisedNewform_of_sine
    (hF : IsMaassNewform N 1 (maassEigenvalue R) F) (hc : HasMaassSineExpansion (F ∘ ofComplex) R c)
    (τ : ℍ) : conj (maassNormalisedNewform R F τ) = maassNormalisedNewform R F τ := by
  have h : (conj (c 1))⁻¹ * conj (F τ) = (c 1)⁻¹ * F τ :=
    congrFun (hF.conj_smul_eq_of_sine hc) τ
  simp only [maassNormalisedNewform, hc.maassCoefficients_eq, Pi.smul_apply, smul_eq_mul, map_mul,
    map_inv₀, h]

/-- **The LMFDB's Maass newforms take only real values** (LMFDB `portrait.maass`: "If the Maass
form `f` has squarefree level, then `f` takes only real values"): the normalised newform
`f = F / a(1)` of a Maass cusp newform `F` of weight `0` on `Γ₀(N)` with trivial character is
real-valued, at every level `N`. For an even or odd `F`, as every form of the LMFDB is, `f` is the
form with `a(1) = 1` in the cosine or sine expansion of `F`, whose coefficients are real
(`IsMaassCuspNewform.hasMaassCosineExpansion`, `IsMaassCuspNewform.hasMaassSineExpansion`). A cusp
newform that is neither even nor odd has no such expansion
(`HasMaassCosineExpansion.isEvenMaassForm`, `HasMaassSineExpansion.isOddMaassForm`), hence no
normalisation, and its normalised newform is the junk value `0`; classically there is no such
newform, which is not proved here. -/
lemma IsMaassCuspNewform.conj_maassNormalisedNewform (hF : IsMaassCuspNewform N R F) (τ : ℍ) :
    conj (maassNormalisedNewform R F τ) = maassNormalisedNewform R F τ := by
  by_cases hc : ∃ c, HasMaassCosineExpansion (F ∘ ofComplex) R c
  · exact hc.elim fun _ hc ↦ hF.1.conj_maassNormalisedNewform_of_cosine hc τ
  by_cases hs : ∃ c, HasMaassSineExpansion (F ∘ ofComplex) R c
  · exact hs.elim fun _ hs ↦ hF.1.conj_maassNormalisedNewform_of_sine hs τ
  simp [maassNormalisedNewform, maassCoefficients, hc, hs]

/-- **The first coefficient of the normalised even cusp newform is `1`** (LMFDB
`mf.maass.mwf.coefficients`), at every level `N ≠ 0` and for every spectral parameter `R`. -/
lemma IsMaassCuspNewform.maassCoefficients_normalisedNewform_one_of_even
    (hF : IsMaassCuspNewform N R F) (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) 1 = 1 :=
  hF.1.maassCoefficients_normalisedNewform_one_of_cosine (hF.hasMaassCosineExpansion hs)

/-- **The first coefficient of the normalised odd cusp newform is `1`** (LMFDB
`mf.maass.mwf.coefficients`), at every level `N ≠ 0` and for every spectral parameter `R`. -/
lemma IsMaassCuspNewform.maassCoefficients_normalisedNewform_one_of_odd
    (hF : IsMaassCuspNewform N R F) (hs : IsOddMaassForm (F ∘ ofComplex)) :
    maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) 1 = 1 :=
  hF.1.maassCoefficients_normalisedNewform_one_of_sine (hF.hasMaassSineExpansion hs)

/-- **The coefficients of the normalised even cusp newform are real at every index** (LMFDB
`mf.maass.mwf.coefficients`): for an even Maass cusp newform `F` of weight `0` on `Γ₀(N)`, `N ≠ 0`,
with any spectral parameter `R`, every coefficient `a(n)`, `n ≥ 1`, of the normalised newform
`maassNormalisedNewform R F` is real, `gcd(n, N) > 1` included; its first coefficient is `1`
(`IsMaassCuspNewform.maassCoefficients_normalisedNewform_one_of_even`). The odd version is
`IsMaassCuspNewform.conj_maassCoefficients_normalisedNewform_of_odd`. -/
lemma IsMaassCuspNewform.conj_maassCoefficients_normalisedNewform_of_even
    (hF : IsMaassCuspNewform N R F) (hs : IsEvenMaassForm (F ∘ ofComplex)) (n : ℕ+) :
    conj (maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) n) =
      maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) n :=
  hF.1.conj_maassCoefficients_normalisedNewform_of_cosine (hF.hasMaassCosineExpansion hs) n

/-- **The coefficients of the normalised odd cusp newform are real at every index** (LMFDB
`mf.maass.mwf.coefficients`): for an odd Maass cusp newform `F` of weight `0` on `Γ₀(N)`, `N ≠ 0`,
with any spectral parameter `R`, every coefficient `a(n)`, `n ≥ 1`, of the normalised newform
`maassNormalisedNewform R F` is real, `gcd(n, N) > 1` included; its first coefficient is `1`
(`IsMaassCuspNewform.maassCoefficients_normalisedNewform_one_of_odd`). -/
lemma IsMaassCuspNewform.conj_maassCoefficients_normalisedNewform_of_odd
    (hF : IsMaassCuspNewform N R F) (hs : IsOddMaassForm (F ∘ ofComplex)) (n : ℕ+) :
    conj (maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) n) =
      maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) n :=
  hF.1.conj_maassCoefficients_normalisedNewform_of_sine (hF.hasMaassSineExpansion hs) n

end UpperHalfPlane
