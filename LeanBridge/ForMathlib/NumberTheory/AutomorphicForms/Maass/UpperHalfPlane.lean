import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Maass forms of weight zero on the upper half-plane

A Maass form of weight `0` on a subgroup `Γ` of `GL(2, ℝ)` is a smooth function on the upper
half-plane `ℍ` that is invariant under `Γ`, square-integrable on `Γ \ ℍ`, and an eigenfunction
`(Δ + λ) f = 0` of the hyperbolic Laplacian `Δ = y² (∂²/∂x² + ∂²/∂y²)`. The eigenvalue is written
`λ = 1/4 + R²` with `R` the spectral parameter.

## Main definitions

* `UpperHalfPlane.hyperbolicLaplacian` (LMFDB `mf.maass.mwf.laplacian`): the hyperbolic Laplacian.
* `UpperHalfPlane.IsMaassForm` (LMFDB `mf.maass.mwf.weight0`, `mf.maass.mwf.eigenvalue`): Maass
  forms of weight `0` with eigenvalue `λ`.
* `UpperHalfPlane.maassEigenvalue` (LMFDB `mf.maass.mwf.eigenvalue`): the eigenvalue `1/4 + R²` of
  the spectral parameter `R`.
* `UpperHalfPlane.HasMaassSpectralParameter` (LMFDB `mf.maass.mwf.spectralparameter`).
* `UpperHalfPlane.IsMaassFormOfLevel` (LMFDB `mf.maass.mwf.level`).
* `UpperHalfPlane.maassReflection`, `UpperHalfPlane.IsEvenMaassForm`,
  `UpperHalfPlane.IsOddMaassForm` (LMFDB `mf.maass.mwf.symmetry`).
* `UpperHalfPlane.IsExceptionalMaassEigenvalue`, `UpperHalfPlane.SelbergEigenvalueConjecture`
  (LMFDB `mf.maass.exceptional_eigenvalue`).

## Main results

* `UpperHalfPlane.IsMaassForm.eigenvalue_eq`: a nonzero Maass form has a unique eigenvalue.
* `UpperHalfPlane.HasMaassSpectralParameter.eq_or_eq_neg`: its spectral parameter is unique up to
  sign.
* `UpperHalfPlane.coe_maassReflection_smul`: `diag(-1, 1)` acts on `ℍ` by `z ↦ -z̄`.
* `UpperHalfPlane.isExceptionalMaassEigenvalue_iff`: for a purely imaginary spectral parameter
  `R = it`, the eigenvalue is exceptional exactly when `0 < t² < 1/4`.
-/

open MeasureTheory Matrix CongruenceSubgroup

open scoped ContDiff MatrixGroups

namespace UpperHalfPlane

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {f : ℂ → ℂ} {z : ℂ} {a b R S : ℂ}

variable (f z) in
/-- The **hyperbolic Laplacian** (LMFDB `mf.maass.mwf.laplacian`) `Δ = y² (∂²/∂x² + ∂²/∂y²)` of a
function `f` on the upper half-plane at `z = x + iy`: the Laplace–Beltrami operator of the metric
`(dx² + dy²) / y²`, with the sign making it negative semi-definite, as in the LMFDB's equation
`(Δ + λ) f = 0` with `λ ≥ 0`. The knowl `mf.maass.mwf.laplacian` writes `Δ` with a minus sign,
which is incompatible with that equation; this is its negative. The function is given on `ℂ`; only
its values near `z` matter. -/
noncomputable def hyperbolicLaplacian : ℂ :=
  (z.im ^ 2 : ℝ) * (fderiv ℝ (fun w ↦ fderiv ℝ f w 1) z 1 +
    fderiv ℝ (fun w ↦ fderiv ℝ f w Complex.I) z Complex.I)

variable (Γ f) in
/-- A function `f` on the upper half-plane, given on `ℂ`, is a **Maass form** of weight `0` (LMFDB
`mf.maass.mwf.weight0`) on a subgroup `Γ` of `GL(2, ℝ)` with **eigenvalue** `λ` (LMFDB
`mf.maass.mwf.eigenvalue`) if it is smooth on `ℍ`, square-integrable on `Γ \ ℍ`, invariant under
`Γ` (acting through Mathlib's action of `GL(2, ℝ)` on `ℍ`, by `z ↦ σ(γ)((az + b)/(cz + d))` with
`σ` complex conjugation when `det γ < 0`), and an eigenfunction `(Δ + λ) f = 0` of the hyperbolic
Laplacian.

Square-integrability on `Γ \ ℍ` is the integrability of `|f|²` on a fundamental domain of the image
of `Γ` in `PGL(2, ℝ)`, which acts faithfully on `ℍ` (so that `Γ` may contain `-1`), for Mathlib's `GL(2, ℝ)`-invariant
measure `dx dy / y²` on `ℍ`; for a `Γ`-invariant `f` it does not
depend on the fundamental domain. The zero function satisfies the conditions for every `λ`: the
eigenvalue of a nonzero Maass form is unique (`IsMaassForm.eigenvalue_eq`). -/
def IsMaassForm (eigenvalue : ℂ) : Prop :=
  ContDiffOn ℝ ∞ f {z | 0 < z.im} ∧
    (∃ D : Set ℍ, IsFundamentalDomain (Γ.map ProjGenLinGroup.mk) D ∧
      IntegrableOn (fun z : ℍ ↦ ‖f z‖ ^ 2) D) ∧
    (∀ γ ∈ Γ, ∀ z : ℍ, f ↑(γ • z) = f z) ∧
    ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + eigenvalue * f z = 0

/-- **A nonzero Maass form has a unique eigenvalue**: if `f(z) ≠ 0` at some point `z` of `ℍ`, the
eigenvalue equation at `z` determines `λ`. -/
lemma IsMaassForm.eigenvalue_eq (ha : IsMaassForm Γ f a) (hb : IsMaassForm Γ f b) (hz : 0 < z.im)
    (hf : f z ≠ 0) : a = b := by
  have h : (a - b) * f z = 0 := by
    linear_combination ha.2.2.2 z hz - hb.2.2.2 z hz
  exact sub_eq_zero.mp <| (mul_eq_zero.mp h).resolve_right hf

/-- The **eigenvalue** `λ = 1/4 + R²` (LMFDB `mf.maass.mwf.eigenvalue`) of the spectral parameter
`R` of a Maass form. -/
noncomputable def maassEigenvalue (R : ℂ) : ℂ :=
  1 / 4 + R ^ 2

variable (Γ f R) in
/-- A Maass form `f` on `Γ` has **spectral parameter** `R` (LMFDB `mf.maass.mwf.spectralparameter`)
if its eigenvalue is `λ = 1/4 + R²`. The spectral parameter of a nonzero Maass form is unique up to
sign (`HasMaassSpectralParameter.eq_or_eq_neg`); the LMFDB lists the one with nonnegative real
part (nonnegative imaginary part when it is purely imaginary). -/
def HasMaassSpectralParameter : Prop :=
  IsMaassForm Γ f (maassEigenvalue R)

lemma hasMaassSpectralParameter_neg_iff :
    HasMaassSpectralParameter Γ f (-R) ↔ HasMaassSpectralParameter Γ f R := by
  simp only [HasMaassSpectralParameter, maassEigenvalue, neg_sq]

/-- The **spectral parameter** of a nonzero Maass form **is unique up to sign**. -/
lemma HasMaassSpectralParameter.eq_or_eq_neg (hR : HasMaassSpectralParameter Γ f R)
    (hS : HasMaassSpectralParameter Γ f S) (hz : 0 < z.im) (hf : f z ≠ 0) : S = R ∨ S = -R := by
  have h : S ^ 2 = R ^ 2 := by
    simpa only [maassEigenvalue, add_right_inj] using hS.eigenvalue_eq hR hz hf
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

variable (f) in
/-- A Maass form `f` with eigenvalue `λ` **has level** `N` (LMFDB `mf.maass.mwf.level`) if it is a
Maass form on the principal congruence subgroup `Γ(N)`, that is, invariant under `Γ(N)`. -/
def IsMaassFormOfLevel (N : ℕ) (eigenvalue : ℂ) : Prop :=
  IsMaassForm ((Gamma N).map (SpecialLinearGroup.mapGL ℝ)) f eigenvalue

/-- The **reflection** `diag(-1, 1)` (LMFDB `mf.maass.mwf.symmetry`) in `GL(2, ℝ)`, acting on `ℍ`
by `z ↦ -z̄` (`coe_maassReflection_smul`). -/
noncomputable def maassReflection : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp)

/-- **The reflection acts by `z ↦ -z̄`**. -/
lemma coe_maassReflection_smul (w : ℍ) : ↑(maassReflection • w) = -(starRingEnd ℂ) w := by
  norm_num [coe_smul, σ, num, denom, maassReflection]

variable (f) in
/-- A Maass form `f` is **even** (LMFDB `mf.maass.mwf.symmetry`) if `f(-z̄) = f(z)` on `ℍ`, that is,
`f` is invariant under the reflection `diag(-1, 1)`. -/
def IsEvenMaassForm : Prop :=
  ∀ w : ℍ, f ↑(maassReflection • w) = f w

variable (f) in
/-- A Maass form `f` is **odd** (LMFDB `mf.maass.mwf.symmetry`) if `f(-z̄) = -f(z)` on `ℍ`, where
`z ↦ -z̄` is the action of the reflection `diag(-1, 1)`. -/
def IsOddMaassForm : Prop :=
  ∀ w : ℍ, f ↑(maassReflection • w) = -f w

/-- An eigenvalue `λ` of a Maass form is **exceptional** (LMFDB `mf.maass.exceptional_eigenvalue`)
if it is real with `0 < λ < 1/4`, that is, if its spectral parameter is purely imaginary and nonzero
with absolute value less than `1/2` (`isExceptionalMaassEigenvalue_iff`). The knowl says "purely
real" for the spectral parameter here, which is a slip: a real `R` gives `λ ≥ 1/4`. -/
def IsExceptionalMaassEigenvalue (eigenvalue : ℂ) : Prop :=
  eigenvalue.im = 0 ∧ 0 < eigenvalue.re ∧ eigenvalue.re < 1 / 4

/-- **Exceptional eigenvalues in terms of the spectral parameter**: for a purely imaginary spectral
parameter `R = it`, the eigenvalue `1/4 - t²` is exceptional exactly when `0 < t² < 1/4`. -/
lemma isExceptionalMaassEigenvalue_iff (t : ℝ) :
    IsExceptionalMaassEigenvalue (maassEigenvalue (t * Complex.I)) ↔ 0 < t ^ 2 ∧ t ^ 2 < 1 / 4 := by
  simp [IsExceptionalMaassEigenvalue, maassEigenvalue, sq, and_comm]

/-- **Selberg's eigenvalue conjecture** (LMFDB `mf.maass.exceptional_eigenvalue`): no nonzero Maass
form on a principal congruence subgroup `Γ(N)`, `N ≥ 1`, has an exceptional eigenvalue. Maass forms
on any congruence subgroup are Maass forms on some `Γ(N)`. Selberg's conjecture is about cusp forms;
for congruence subgroups the only eigenvalue of `L²` Maass forms outside the cuspidal spectrum is
`λ = 0` (the constants), which is not exceptional, so the two statements agree; that fact is not
proved here. -/
def SelbergEigenvalueConjecture : Prop :=
  ∀ (N : ℕ) (f : ℂ → ℂ) (eigenvalue : ℂ) (z : ℂ), N ≠ 0 → 0 < z.im → f z ≠ 0 →
    IsMaassFormOfLevel f N eigenvalue → ¬IsExceptionalMaassEigenvalue eigenvalue

end UpperHalfPlane
