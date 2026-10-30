import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.UpperHalfPlane
import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.GaloisOrbitLabel
import Mathlib.Data.Set.Card

/-!
# The spectral index of a Maass form

The Laplace eigenvalues `λ = 1/4 + R²` of the Maass forms of a given level, weight and character
are discrete, real and nonnegative, and the LMFDB orders them: the spectral index of an eigenvalue
(LMFDB `mf.maass.spectral_index`) is `0` for `λ = 1/4`, that is `R = 0`; the standard eigenvalues
`λ > 1/4`, with real spectral parameter `R`, are ordered by `|R|`, that is by increasing `λ`, and
numbered `1, 2, …`; the exceptional eigenvalues `0 < λ < 1/4` (LMFDB
`mf.maass.exceptional_eigenvalue`), with purely imaginary `R`, are ordered by `|R|`, that is by
decreasing `λ`, numbered `1, 2, …` and written in base `26` with the letters `a, …, z`, so that the
first one is `b`. The knowl calls `R` purely imaginary for the standard eigenvalues and purely real
for the exceptional ones; it is the other way round, as `λ = 1/4 + R²` is less than `1/4` exactly
when `R² < 0`. Exceptional eigenvalues are conjectured not to exist for congruence subgroups
(`UpperHalfPlane.SelbergEigenvalueConjecture`).

The discreteness of the spectrum (Selberg's spectral theory of `L²(Γ \ ℍ)`) is not available, and
neither are the Maass newforms of a given level, weight and character whose eigenvalues the LMFDB
orders. So the spectral index is defined relative to a given set `S ⊆ ℝ` of eigenvalues, as the
number of elements of `S` between `1/4` and `λ`; it has the properties the knowl relies on when
`S` is discrete, that is, when it has finitely many elements below every bound: it is positive for
`λ ≠ 1/4`, increasing in the standard eigenvalues and decreasing in the exceptional ones, so that
it determines the eigenvalue on each side of `1/4`. The eigenvalues of the nonzero Maass forms of
weight `0` on a group `Γ` form the set `UpperHalfPlane.maassSpectrum Γ`: for `SL(2, ℤ)` its nonzero
elements are the eigenvalues of the Maass newforms of level `1`, which the LMFDB orders, but for
`Γ₀(N)`, `N > 1`, it also contains the eigenvalues of oldforms, which the LMFDB leaves out.

## Main definitions

* `UpperHalfPlane.maassSpectrum`: the eigenvalues of the nonzero Maass forms of weight `0` on `Γ`.
* `UpperHalfPlane.maassSpectralIndex` (LMFDB `mf.maass.spectral_index`): the spectral index of an
  eigenvalue in a set of eigenvalues.
* `UpperHalfPlane.maassSpectralIndexLabel` (LMFDB `mf.maass.spectral_index`): the spectral index as
  written in labels, in decimal or, for exceptional eigenvalues, in base `26` with letters.

## Main results

* `UpperHalfPlane.maassSpectralIndex_pos`: in a discrete set of eigenvalues, the spectral index of
  an eigenvalue `λ ≠ 1/4` is positive.
* `UpperHalfPlane.maassSpectralIndex_lt_maassSpectralIndex`: the spectral index is strictly
  increasing in the standard eigenvalues.
* `UpperHalfPlane.maassSpectralIndex_lt_maassSpectralIndex_of_lt_quarter`: the spectral index is
  strictly decreasing in the exceptional eigenvalues.
-/

open Set

namespace UpperHalfPlane

variable (Γ : Subgroup (GL (Fin 2) ℝ)) (S : Set ℝ) {eigenvalue eigenvalue' : ℝ}

/-- The **spectrum** of the Maass forms of weight `0` on a subgroup `Γ` of `GL(2, ℝ)`: the real
numbers `λ` that are the eigenvalue of a Maass form on `Γ` (`UpperHalfPlane.IsMaassForm`) not
vanishing everywhere on `ℍ`. For a congruence subgroup it is discrete and nonnegative, it contains
the eigenvalue `0` of the constants, and its elements below `1/4` other than `0` would be
exceptional eigenvalues. For `Γ = SL(2, ℤ)`, whose nonconstant Maass forms are cusp forms, sums of
newforms, its nonzero elements are the eigenvalues of the Maass newforms of level `1`, so that the
spectral index `UpperHalfPlane.maassSpectralIndex (maassSpectrum Γ) λ` of an eigenvalue `λ > 0` is
the LMFDB's; for `Γ₀(N)`, `N > 1`, it also contains the eigenvalues of oldforms, which the LMFDB's
ordering of the newforms of level `N` leaves out. These facts of spectral theory are not proved
here. -/
def maassSpectrum : Set ℝ :=
  {x | ∃ f : ℂ → ℂ, (∃ z : ℂ, 0 < z.im ∧ f z ≠ 0) ∧ IsMaassForm Γ f x}

variable (eigenvalue) in
/-- The **spectral index** (LMFDB `mf.maass.spectral_index`) of an eigenvalue `λ` in a set `S` of
eigenvalues `1/4 + R²`: `0` for `λ = 1/4`; for a standard eigenvalue `λ > 1/4`, the number of
elements of `S` in `(1/4, λ]`, its position when the standard eigenvalues are ordered by `|R|`, that
is increasingly; and for an exceptional eigenvalue `λ < 1/4`, the number of elements of `S` in
`[λ, 1/4)`, its position when the exceptional eigenvalues are ordered by `|R|`, that is
decreasingly. The LMFDB's set `S` is that of the eigenvalues of the Maass newforms of a given level,
weight and character, which is discrete; for an `S` with infinitely many elements in the relevant
interval the index is the junk value `0`. -/
noncomputable def maassSpectralIndex : ℕ :=
  if 1 / 4 < eigenvalue then (S ∩ Ioc (1 / 4) eigenvalue).ncard
  else if eigenvalue < 1 / 4 then (S ∩ Ico eigenvalue (1 / 4)).ncard else 0

variable (eigenvalue) in
/-- The **spectral index** of an eigenvalue `λ` in a set `S` of eigenvalues as written in the
labels of Maass forms (LMFDB `mf.maass.spectral_index`, `mf.maass.label`): the spectral index
`UpperHalfPlane.maassSpectralIndex` in decimal for `λ ≥ 1/4`, and in base `26` with the letters
`a, …, z` for the digits (`DirichletCharacter.letterCode`) for an exceptional eigenvalue `λ < 1/4`,
so that the first exceptional eigenvalue has index `b`. -/
noncomputable def maassSpectralIndexLabel : String :=
  if eigenvalue < 1 / 4 then DirichletCharacter.letterCode (maassSpectralIndex S eigenvalue)
  else toString (maassSpectralIndex S eigenvalue)

lemma maassSpectralIndex_quarter : maassSpectralIndex S (1 / 4) = 0 := by
  simp [maassSpectralIndex]

/-- **The spectral index of an eigenvalue `λ ≠ 1/4` is positive** in a set of eigenvalues with
finitely many elements below every bound, `λ` itself being counted. -/
lemma maassSpectralIndex_pos (hS : ∀ x : ℝ, (S ∩ Iic x).Finite) (h : eigenvalue ∈ S)
    (h' : eigenvalue ≠ 1 / 4) : 0 < maassSpectralIndex S eigenvalue := by
  rw [maassSpectralIndex]
  split_ifs with h₁ h₂
  · refine (ncard_pos <| (hS eigenvalue).subset ?_).mpr ⟨eigenvalue, h, h₁, le_rfl⟩
    exact inter_subset_inter_right S Ioc_subset_Iic_self
  · refine (ncard_pos <| (hS (1 / 4)).subset ?_).mpr ⟨eigenvalue, h, le_rfl, h₂⟩
    exact inter_subset_inter_right S <| Ico_subset_Iio_self.trans Iio_subset_Iic_self
  · exact absurd (le_antisymm (not_lt.mp h₁) (not_lt.mp h₂)) h'

/-- **The spectral index is strictly increasing in the standard eigenvalues**: in a set `S` of
eigenvalues with finitely many elements below every bound, a standard eigenvalue `λ' ∈ S` larger
than `λ > 1/4` has a larger spectral index. In particular the spectral index determines a standard
eigenvalue of `S`. -/
lemma maassSpectralIndex_lt_maassSpectralIndex (hS : ∀ x : ℝ, (S ∩ Iic x).Finite)
    (h : 1 / 4 < eigenvalue) (h' : eigenvalue' ∈ S) (hlt : eigenvalue < eigenvalue') :
    maassSpectralIndex S eigenvalue < maassSpectralIndex S eigenvalue' := by
  rw [maassSpectralIndex, ite_eq_left h, maassSpectralIndex, ite_eq_left (h.trans hlt)]
  refine ncard_lt_ncard ?_ <| (hS eigenvalue').subset <|
    inter_subset_inter_right S Ioc_subset_Iic_self
  refine ssubset_iff_subset_ne.mpr ⟨fun x hx ↦ ⟨hx.1, hx.2.1, hx.2.2.trans hlt.le⟩, fun he ↦ ?_⟩
  have hm : eigenvalue' ∈ S ∩ Ioc (1 / 4) eigenvalue := he ▸ ⟨h', h.trans hlt, le_rfl⟩
  exact hlt.not_ge hm.2.2

/-- **The spectral index is strictly decreasing in the exceptional eigenvalues**: in a set `S` of
eigenvalues with finitely many elements below every bound, an exceptional eigenvalue `λ ∈ S`
smaller than `λ' < 1/4` has a larger spectral index. In particular the spectral index determines
an exceptional eigenvalue of `S`. -/
lemma maassSpectralIndex_lt_maassSpectralIndex_of_lt_quarter (hS : ∀ x : ℝ, (S ∩ Iic x).Finite)
    (h : eigenvalue ∈ S) (hlt : eigenvalue < eigenvalue') (h' : eigenvalue' < 1 / 4) :
    maassSpectralIndex S eigenvalue' < maassSpectralIndex S eigenvalue := by
  rw [maassSpectralIndex, ite_eq_right h'.not_gt, ite_eq_left h', maassSpectralIndex,
    ite_eq_right (hlt.trans h').not_gt, ite_eq_left (hlt.trans h')]
  refine ncard_lt_ncard ?_ <| (hS (1 / 4)).subset <|
    inter_subset_inter_right S <| Ico_subset_Iio_self.trans Iio_subset_Iic_self
  refine ssubset_iff_subset_ne.mpr ⟨fun x hx ↦ ⟨hx.1, hlt.le.trans hx.2.1, hx.2.2⟩, fun he ↦ ?_⟩
  have hm : eigenvalue ∈ S ∩ Ico eigenvalue' (1 / 4) := he.symm ▸ ⟨h, le_rfl, hlt.trans h'⟩
  exact hlt.not_ge hm.2.1

end UpperHalfPlane
