import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CuspidalOfStandardEigenvalue
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.SpectralIndex

/-!
# The spectral index of a Maass newform

The knowl `mf.maass.spectral_index` orders "the eigenvalues" without naming the forms they belong
to. This file reads them as those of the cuspidal Maass newforms of weight `0`, level `N` and
character `χ`, the set `UpperHalfPlane.maassNewformSpectrum N χ`:

* the label `N.k.a.m.d` (LMFDB `mf.maass.label`) fixes the level, the weight and the character, and
  speaks of newforms; the database contains "cuspidal Maass newforms" (LMFDB
  `rcs.cande.maass_rigor`);
* in other weights the knowl's "nonnegative" and its "Exceptional eigenvalues are conjectured to not
  exist" fail: for a holomorphic cusp form `f` of weight `k`, `y^{k/2} f` is a Maass form of weight
  `k` with eigenvalue `(k/2)(1 - k/2)`, negative for `k > 2`, and `y^{1/4} η` has weight `1/2` and
  the exceptional eigenvalue `3/16`.

The cuspidality is a correction of the linked knowl `mf.maass.mwf`, which only asks for
square-integrability, in the same way as for `mf.maass.mwf.coefficients`. For `x ≥ 1/4` it changes
nothing, being automatic (`UpperHalfPlane.mem_maassNewformSpectrum_iff`,
`UpperHalfPlane.maassNewformSpectralIndex_eq_of_quarter_le`). Below `1/4`, the constant `1` of level
`1` is a Maass newform (`UpperHalfPlane.isMaassNewform_const_one`) whose eigenvalue `0` has no index
in the knowl, not being exceptional, and is left out. That it is the only square-integrable newform
with a nonzero constant term (the residual spectrum of `Γ₀(N)` consists of the constants) is
classical and not proved here; no statement of this file uses it.

The set is discrete, its elements being real and positive (LMFDB `mf.maass.spectral_index`:
"discrete, real, and nonnegative"), as a part of the spectrum of the Maass cusp forms
(`UpperHalfPlane.finite_maassCuspSpectrum_inter_Iic`). So the spectral index
(`UpperHalfPlane.maassNewformSpectralIndex`) of an eigenvalue is its position in the order of the
knowl: `0` for `1/4`; the eigenvalues above `1/4` are numbered `1, 2, …` in increasing order, and
those below `1/4` are numbered `1, 2, …` in decreasing order and written in base `26` with the
letters `a, …, z` (`UpperHalfPlane.maassNewformSpectralIndexLabel`), the first one being `b`. Both
are the order of the absolute values of the spectral parameter `R`
(`UpperHalfPlane.norm_sq_eq_abs_of_maassEigenvalue_eq`).

## Main definitions

* `UpperHalfPlane.maassNewformSpectrum`: the eigenvalues of the Maass cusp newforms of level `N` and
  character `χ`.
* `UpperHalfPlane.maassNewformSpectralIndex` (LMFDB `mf.maass.spectral_index`): the spectral index.
* `UpperHalfPlane.maassNewformSpectralIndexLabel` (LMFDB `mf.maass.spectral_index`,
  `mf.maass.label`): the spectral index as written in labels.

## Main results

* `UpperHalfPlane.finite_maassNewformSpectrum_inter_Iic`: the spectrum is discrete.
* `UpperHalfPlane.zero_lt_of_mem_maassNewformSpectrum`: its elements are positive.
* `UpperHalfPlane.isExceptionalMaassEigenvalue_of_mem_maassNewformSpectrum`: those below `1/4` are
  exceptional.
* `UpperHalfPlane.mem_maassNewformSpectrum_iff`: above `1/4`, it consists of the eigenvalues of all
  the Maass newforms.
* `UpperHalfPlane.maassNewformSpectralIndex_eq_of_quarter_le`: above `1/4`, the spectral index is
  the position among the eigenvalues of all the Maass newforms.
* `UpperHalfPlane.IsMaassCuspNewform.re_mem_maassNewformSpectrum`: the eigenvalue of a Maass cusp
  newform of trivial character lies in the spectrum.
* `UpperHalfPlane.norm_sq_eq_abs_of_maassEigenvalue_eq`: `|R|² = |λ - 1/4|`.
* `UpperHalfPlane.maassSpectralIndex_eq_one_of_forall_le`,
  `UpperHalfPlane.maassSpectralIndex_eq_add_one`,
  `UpperHalfPlane.maassSpectralIndex_eq_one_of_forall_ge`,
  `UpperHalfPlane.maassSpectralIndex_eq_add_one_of_lt_quarter`: the spectral index counts the
  eigenvalues from `1/4`, one by one, on each side.
* `UpperHalfPlane.maassSpectralIndexLabel_eq_b`: the first exceptional eigenvalue has index `b`.
* `UpperHalfPlane.maassNewformSpectralIndex_pos`: the index of an eigenvalue other than `1/4` is
  positive.
* `UpperHalfPlane.maassNewformSpectralIndex_injOn_standard`,
  `UpperHalfPlane.maassNewformSpectralIndex_injOn_exceptional`: it determines the eigenvalue on each
  side of `1/4`.
-/

open Set

namespace UpperHalfPlane

variable (N : ℕ) (χ : DirichletCharacter ℂ N) {S : Set ℝ} {x x' : ℝ} {R : ℂ} {F : ℍ → ℂ}

/-- The **spectrum of the Maass newforms** of weight `0`, level `N` and character `χ`: the real
numbers that are the eigenvalue of a Maass newform (`IsMaassNewform`) with vanishing constant terms
at all the cusps (`maassCuspidalSpace`), the forms of the LMFDB (`rcs.cande.maass_rigor`: "cuspidal
Maass newforms"). Every eigenvalue of a Maass form is real (`conj_eigenvalue_of_mem_maassSpace`),
and for `x ≥ 1/4` the cuspidality is automatic (`mem_maassNewformSpectrum_iff`). Below `1/4` it is
part of the definition: it leaves out the eigenvalue `0` of the constant newform of level `1`, and
that it leaves out nothing else is the classical theorem on the residual spectrum of `Γ₀(N)`, which
is not proved here and not used. This set is discrete (`finite_maassNewformSpectrum_inter_Iic`). -/
def maassNewformSpectrum : Set ℝ :=
  {x | ∃ F : ℍ → ℂ, IsMaassNewform N χ (x : ℂ) F ∧ F ∈ maassCuspidalSpace N χ}

lemma maassNewformSpectrum_subset : maassNewformSpectrum N χ ⊆ maassCuspSpectrum N χ := by
  rintro x ⟨F, hF, hc⟩
  exact ⟨F, hF.2.1, mem_maassCuspSpace_iff.mpr ⟨hF.1.1, hc⟩⟩

variable {N χ}

lemma IsMaassCuspNewform.mem_maassCuspidalSpace (hF : IsMaassCuspNewform N R F) :
    F ∈ maassCuspidalSpace N 1 :=
  ⟨continuous_of_mem_maassSpace hF.1.1.1, fun _ hγ _ ↦ smul_eq_of_mem_maassSpace hF.1.1.1 hγ,
    integrableOn_norm_sq_of_mem_maassSpace hF.1.1.1, hF.2⟩

lemma IsMaassCuspNewform.ofReal_re_maassEigenvalue (hF : IsMaassCuspNewform N R F) :
    (((maassEigenvalue R).re : ℝ) : ℂ) = maassEigenvalue R :=
  Complex.conj_eq_iff_re.mp (conj_eigenvalue_of_mem_maassSpace hF.1.1.1 hF.1.2.1)

/-- **The eigenvalue of a Maass cusp newform lies in the spectrum**: for a Maass cusp newform of
weight `0` on `Γ₀(N)` with trivial character and spectral parameter `R`, the eigenvalue `1/4 + R²`
is real, and it lies in the spectrum of level `N` and trivial character. -/
lemma IsMaassCuspNewform.re_mem_maassNewformSpectrum (hF : IsMaassCuspNewform N R F) :
    (maassEigenvalue R).re ∈ maassNewformSpectrum N 1 := by
  refine ⟨F, ?_, hF.mem_maassCuspidalSpace⟩
  rw [hF.ofReal_re_maassEigenvalue]
  exact hF.1

/-- **The order of the eigenvalues by `|R|`**: if `x = 1/4 + R²` with `x` real, then
`|R|² = |x - 1/4|`, whether `R` is real or purely imaginary. So `|R|` increases with `x` above
`1/4` and decreases with `x` below `1/4`. -/
lemma norm_sq_eq_abs_of_maassEigenvalue_eq (h : maassEigenvalue R = (x : ℂ)) :
    ‖R‖ ^ 2 = |x - 1 / 4| := by
  have h1 : R ^ 2 = ((x - 1 / 4 : ℝ) : ℂ) := by
    rw [maassEigenvalue] at h
    push_cast
    linear_combination h
  rw [← norm_pow, h1, Complex.norm_real, Real.norm_eq_abs]

/-- **The first standard eigenvalue has spectral index `1`**. -/
lemma maassSpectralIndex_eq_one_of_forall_le (h : x ∈ S) (hx : 1 / 4 < x)
    (hmin : ∀ y ∈ S, 1 / 4 < y → x ≤ y) : maassSpectralIndex S x = 1 := by
  have h1 : S ∩ Ioc (1 / 4) x = {x} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨⟨h, hx, le_rfl⟩, fun y hy ↦ ?_⟩
    exact le_antisymm hy.2.2 (hmin y hy.1 hy.2.1)
  rw [maassSpectralIndex, ite_eq_left hx, h1, ncard_singleton]

/-- **The next standard eigenvalue has the next spectral index**: if `x' ∈ S` follows `x > 1/4` in
`S`, a set with finitely many elements below every bound, the index of `x'` is that of `x` plus
`1`. -/
lemma maassSpectralIndex_eq_add_one (hS : ∀ y : ℝ, (S ∩ Iic y).Finite) (h' : x' ∈ S)
    (hx : 1 / 4 < x) (hlt : x < x') (hnext : ∀ y ∈ S, x < y → x' ≤ y) :
    maassSpectralIndex S x' = maassSpectralIndex S x + 1 := by
  have h1 : S ∩ Ioc (1 / 4) x' = insert x' (S ∩ Ioc (1 / 4) x) := by
    ext y
    constructor
    · rintro ⟨hy, hy1, hy2⟩
      rcases le_or_gt y x with hyx | hyx
      · exact Or.inr ⟨hy, hy1, hyx⟩
      · exact Or.inl (le_antisymm hy2 (hnext y hy hyx))
    · rintro (rfl | ⟨hy, hy1, hy2⟩)
      · exact ⟨h', hx.trans hlt, le_rfl⟩
      · exact ⟨hy, hy1, hy2.trans hlt.le⟩
  have hfin : (S ∩ Ioc (1 / 4) x).Finite :=
    (hS x).subset <| inter_subset_inter_right S Ioc_subset_Iic_self
  have hnot : x' ∉ S ∩ Ioc (1 / 4) x := fun hm ↦ hlt.not_ge hm.2.2
  rw [maassSpectralIndex, ite_eq_left (hx.trans hlt), maassSpectralIndex, ite_eq_left hx, h1,
    ncard_insert_of_notMem hnot hfin]

/-- **The first exceptional eigenvalue has spectral index `1`**, written `b` in base `26`
(`maassSpectralIndexLabel_eq_b`). -/
lemma maassSpectralIndex_eq_one_of_forall_ge (h : x ∈ S) (hx : x < 1 / 4)
    (hmax : ∀ y ∈ S, y < 1 / 4 → y ≤ x) : maassSpectralIndex S x = 1 := by
  have h1 : S ∩ Ico x (1 / 4) = {x} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨⟨h, le_rfl, hx⟩, fun y hy ↦ ?_⟩
    exact le_antisymm (hmax y hy.1 hy.2.2) hy.2.1
  rw [maassSpectralIndex, ite_eq_right hx.not_gt, ite_eq_left hx, h1, ncard_singleton]

/-- **The first exceptional eigenvalue has index `b`** in the labels. -/
lemma maassSpectralIndexLabel_eq_b (h : x ∈ S) (hx : x < 1 / 4)
    (hmax : ∀ y ∈ S, y < 1 / 4 → y ≤ x) : maassSpectralIndexLabel S x = "b" := by
  rw [maassSpectralIndexLabel, ite_eq_left hx, maassSpectralIndex_eq_one_of_forall_ge h hx hmax,
    DirichletCharacter.letterCode_one]

/-- **The next exceptional eigenvalue has the next spectral index**: if `x' ∈ S` follows `x < 1/4`
in the decreasing order of `S`, a set with finitely many elements below every bound, the index of
`x'` is that of `x` plus `1`. -/
lemma maassSpectralIndex_eq_add_one_of_lt_quarter (hS : ∀ y : ℝ, (S ∩ Iic y).Finite) (h' : x' ∈ S)
    (hx : x < 1 / 4) (hlt : x' < x) (hnext : ∀ y ∈ S, y < x → y ≤ x') :
    maassSpectralIndex S x' = maassSpectralIndex S x + 1 := by
  have h1 : S ∩ Ico x' (1 / 4) = insert x' (S ∩ Ico x (1 / 4)) := by
    ext y
    constructor
    · rintro ⟨hy, hy1, hy2⟩
      rcases le_or_gt x y with hyx | hyx
      · exact Or.inr ⟨hy, hyx, hy2⟩
      · exact Or.inl (le_antisymm (hnext y hy hyx) hy1)
    · rintro (rfl | ⟨hy, hy1, hy2⟩)
      · exact ⟨h', le_rfl, hlt.trans hx⟩
      · exact ⟨hy, hlt.le.trans hy1, hy2⟩
  have hfin : (S ∩ Ico x (1 / 4)).Finite :=
    (hS (1 / 4)).subset <| inter_subset_inter_right S <|
      Ico_subset_Iio_self.trans Iio_subset_Iic_self
  have hnot : x' ∉ S ∩ Ico x (1 / 4) := fun hm ↦ hlt.not_ge hm.2.1
  rw [maassSpectralIndex, ite_eq_right (hlt.trans hx).not_gt, ite_eq_left (hlt.trans hx),
    maassSpectralIndex, ite_eq_right hx.not_gt, ite_eq_left hx, h1,
    ncard_insert_of_notMem hnot hfin]

variable (N χ x) in
/-- The **spectral index** (LMFDB `mf.maass.spectral_index`) of a real number `x` among the
eigenvalues of the Maass cusp newforms of level `N` and character `χ` (`maassNewformSpectrum`): `0`
for `x = 1/4`; for `x > 1/4`, its position among those above `1/4`, in the increasing order, which
is the order of the absolute values of the spectral parameter `R`
(`norm_sq_eq_abs_of_maassEigenvalue_eq`), the first one having index `1`; for `x < 1/4`, its
position among those below `1/4`, in the decreasing order, which is the order of `|R|` again. The
eigenvalues are discrete (`finite_maassNewformSpectrum_inter_Iic`), so that these positions are
finite for `N ≠ 0`. This reads the knowl for weight `0`, for which its "nonnegative" holds
(`zero_lt_of_mem_maassNewformSpectrum`), and for cusp forms, which only matters below `1/4`
(`maassNewformSpectralIndex_eq_of_quarter_le`). The knowl calls `R` purely imaginary for the
standard eigenvalues and purely real for the exceptional ones; it is the other way round. -/
noncomputable def maassNewformSpectralIndex : ℕ :=
  maassSpectralIndex (maassNewformSpectrum N χ) x

variable (N χ x) in
/-- The **spectral index** (LMFDB `mf.maass.spectral_index`, `mf.maass.label`) as written in the
labels of Maass newforms: `maassNewformSpectralIndex` in decimal for an eigenvalue at least `1/4`,
and in base `26` with the letters `a, …, z` for an exceptional eigenvalue, so that the first
exceptional eigenvalue has index `b` (`maassSpectralIndexLabel_eq_b`). -/
noncomputable def maassNewformSpectralIndexLabel : String :=
  maassSpectralIndexLabel (maassNewformSpectrum N χ) x

variable [NeZero N]

/-- **The spectrum of the Maass newforms is discrete** (LMFDB `mf.maass.spectral_index`): it has
finitely many elements below every bound. -/
lemma finite_maassNewformSpectrum_inter_Iic (Λ : ℝ) : (maassNewformSpectrum N χ ∩ Iic Λ).Finite :=
  (finite_maassCuspSpectrum_inter_Iic Λ).subset <|
    inter_subset_inter_left _ (maassNewformSpectrum_subset N χ)

/-- **The eigenvalues of the Maass cusp newforms are positive** (LMFDB `mf.maass.spectral_index`,
`mf.maass.exceptional_eigenvalue`), so that those below `1/4` are exceptional. -/
lemma zero_lt_of_mem_maassNewformSpectrum (hx : x ∈ maassNewformSpectrum N χ) : 0 < x := by
  rcases hx with ⟨F, hF, hc⟩
  exact zero_lt_of_mem_maassCuspSpace (mem_maassCuspSpace_iff.mpr ⟨hF.1.1, hc⟩) hF.2.1

/-- **The elements of the spectrum below `1/4` are exceptional eigenvalues** (LMFDB
`mf.maass.exceptional_eigenvalue`: `0 < λ < 1/4`). -/
lemma isExceptionalMaassEigenvalue_of_mem_maassNewformSpectrum (hx : x ∈ maassNewformSpectrum N χ)
    (h : x < 1 / 4) : IsExceptionalMaassEigenvalue (x : ℂ) :=
  ⟨Complex.ofReal_im x, by simpa using zero_lt_of_mem_maassNewformSpectrum hx, by simpa using h⟩

/-- **Above `1/4`, the spectrum consists of the eigenvalues of all the Maass newforms**: the
constant terms of a square-integrable form with eigenvalue at least `1/4` vanish at every cusp
(`mem_maassCuspSpace_of_mem_maassSpace`). -/
lemma mem_maassNewformSpectrum_iff (hx : 1 / 4 ≤ x) :
    x ∈ maassNewformSpectrum N χ ↔ ∃ F : ℍ → ℂ, IsMaassNewform N χ (x : ℂ) F := by
  refine ⟨?_, ?_⟩
  · rintro ⟨F, hF, -⟩
    exact ⟨F, hF⟩
  rintro ⟨F, hF⟩
  refine ⟨F, hF, ?_⟩
  have hr : maassEigenvalue ((√(x - 1 / 4) : ℝ) : ℂ) = (x : ℂ) := by
    rw [maassEigenvalue]
    have h : ((√(x - 1 / 4) : ℝ) : ℂ) ^ 2 = ((x - 1 / 4 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    rw [h]
    push_cast
    ring1
  have h1 : F ∈ maassSpace N χ (maassEigenvalue ((√(x - 1 / 4) : ℝ) : ℂ)) := by
    rw [hr]
    exact hF.1.1
  exact (mem_maassCuspSpace_iff.mp (mem_maassCuspSpace_of_mem_maassSpace h1)).2

/-- **Above `1/4`, the spectral index is the position among the eigenvalues of all the Maass
newforms** (LMFDB `mf.maass.spectral_index`): for `x ≥ 1/4`, the index does not depend on the
cuspidality in `maassNewformSpectrum`. -/
lemma maassNewformSpectralIndex_eq_of_quarter_le (hx : 1 / 4 ≤ x) :
    maassNewformSpectralIndex N χ x =
      maassSpectralIndex {y : ℝ | ∃ F : ℍ → ℂ, IsMaassNewform N χ (y : ℂ) F} x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [maassNewformSpectralIndex, maassSpectralIndex_quarter, maassSpectralIndex_quarter]
  · rw [maassNewformSpectralIndex, maassSpectralIndex, ite_eq_left hx, maassSpectralIndex,
      ite_eq_left hx]
    congr 1
    ext y
    exact and_congr_left fun hy ↦ mem_maassNewformSpectrum_iff hy.1.le

/-- **The spectral index of an eigenvalue other than `1/4` is positive** (LMFDB
`mf.maass.spectral_index`). -/
lemma maassNewformSpectralIndex_pos (h : x ∈ maassNewformSpectrum N χ) (h' : x ≠ 1 / 4) :
    0 < maassNewformSpectralIndex N χ x :=
  maassSpectralIndex_pos _ finite_maassNewformSpectrum_inter_Iic h h'

/-- **The spectral index determines a standard eigenvalue** (LMFDB `mf.maass.spectral_index`,
`mf.maass.label`). -/
lemma maassNewformSpectralIndex_injOn_standard :
    InjOn (maassNewformSpectralIndex N χ) (maassNewformSpectrum N χ ∩ Ioi (1 / 4)) := by
  intro x hx y hy he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (maassSpectralIndex_lt_maassSpectralIndex _ finite_maassNewformSpectrum_inter_Iic hx.2
      hy.1 h).ne he
  · exact (maassSpectralIndex_lt_maassSpectralIndex _ finite_maassNewformSpectrum_inter_Iic hy.2
      hx.1 h).ne he.symm

/-- **The spectral index determines an exceptional eigenvalue** (LMFDB `mf.maass.spectral_index`,
`mf.maass.label`). -/
lemma maassNewformSpectralIndex_injOn_exceptional :
    InjOn (maassNewformSpectralIndex N χ) (maassNewformSpectrum N χ ∩ Iio (1 / 4)) := by
  intro x hx y hy he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (maassSpectralIndex_lt_maassSpectralIndex_of_lt_quarter _
      finite_maassNewformSpectrum_inter_Iic hx.1 h hy.2).ne he.symm
  · exact (maassSpectralIndex_lt_maassSpectralIndex_of_lt_quarter _
      finite_maassNewformSpectrum_inter_Iic hy.1 h hx.2).ne he

end UpperHalfPlane
