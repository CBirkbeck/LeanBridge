import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Places of a field

A place of a field `K` is an equivalence class of nontrivial absolute values on `K`. Being
archimedean is invariant under equivalence, so places are archimedean or nonarchimedean. For a
number field `K`, Mathlib represents the places by normalized absolute values: the infinite places
`NumberField.InfinitePlace K`, real or complex, which come from the complex embeddings of `K`, and
the finite places `NumberField.FinitePlace K`, which come from the maximal ideals of `𝓞 K`. This
file maps both into the places of `K`, injectively, onto archimedean and nonarchimedean places
respectively.

That every place of a number field arises in this way is Ostrowski's theorem for number fields,
proved in `LeanBridge.ForMathlib.NumberTheory.NumberField.Ostrowski`. The completions of `K` at its infinite and finite
places are `NumberField.InfinitePlace.Completion` and
`IsDedekindDomain.HeightOneSpectrum.adicCompletion`.

## Main definitions

* `AbsoluteValue.Place` (LMFDB `nf.place`): the places of a field.
* `AbsoluteValue.Place.IsArchimedean`: archimedean places.
* `NumberField.InfinitePlace.toPlace`, `NumberField.FinitePlace.toPlace`: the places of a number
  field given by its infinite and finite places.

## Main results

* `AbsoluteValue.IsEquiv.isNonarchimedean_iff`: equivalent absolute values are both
  nonarchimedean or both archimedean.
* `NumberField.InfinitePlace.toPlace_injective`, `NumberField.InfinitePlace.isArchimedean_toPlace`:
  distinct infinite places give distinct places, which are archimedean.
* `NumberField.FinitePlace.toPlace_injective`, `NumberField.FinitePlace.not_isArchimedean_toPlace`:
  distinct finite places give distinct places, which are nonarchimedean.
-/

open AbsoluteValue IsDedekindDomain

namespace AbsoluteValue

variable {K : Type*} [Field K] {v w : AbsoluteValue K ℝ} {hv : v.IsNontrivial} {hw : w.IsNontrivial}

/-- Equivalent absolute values are both nonarchimedean or both archimedean. -/
lemma IsEquiv.isNonarchimedean_iff (h : v.IsEquiv w) : IsNonarchimedean v ↔ IsNonarchimedean w :=
  forall₂_congr fun _ _ ↦ by rw [le_max_iff, le_max_iff, h.le_iff_le, h.le_iff_le]

variable (K) in
/-- A **place** of a field `K` (LMFDB `nf.place`): an equivalence class of nontrivial absolute
values on `K`, real-valued and satisfying the triangle inequality, for the equivalence
`AbsoluteValue.IsEquiv`; two absolute values are equivalent when one is a positive power of the
other (`AbsoluteValue.isEquiv_iff_exists_rpow_eq`). -/
def Place : Type _ :=
  Quotient
    (Setoid.comap Subtype.val inferInstance : Setoid {v : AbsoluteValue K ℝ // v.IsNontrivial})

namespace Place

variable (p : Place K)

variable (v hv) in
/-- The place of a nontrivial absolute value. -/
def mk : Place K :=
  Quotient.mk _ ⟨v, hv⟩

lemma mk_eq_mk_iff : mk v hv = mk w hw ↔ v.IsEquiv w :=
  Quotient.eq

lemma exists_mk : ∃ (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial), mk v hv = p := by
  induction p using Quotient.inductionOn with | h v => exact ⟨v.1, v.2, rfl⟩

/-- A place is **archimedean** when its absolute values do not satisfy the ultrametric inequality;
this does not depend on the absolute value (`IsEquiv.isNonarchimedean_iff`). -/
def IsArchimedean : Prop :=
  Quotient.liftOn p (fun v ↦ ¬IsNonarchimedean v.1) fun _ _ h ↦
    propext (not_congr h.isNonarchimedean_iff)

lemma isArchimedean_mk : (mk v hv).IsArchimedean ↔ ¬IsNonarchimedean v :=
  Iff.rfl

end Place

end AbsoluteValue

namespace NumberField

variable {K : Type*} [Field K] (w : InfinitePlace K)

/-- The place of a field given by an infinite place, real or complex. -/
def InfinitePlace.toPlace : AbsoluteValue.Place K :=
  .mk w.1 w.isNontrivial

/-- Distinct infinite places give distinct places. -/
lemma InfinitePlace.toPlace_injective : Function.Injective (InfinitePlace.toPlace (K := K)) :=
  fun _ _ h ↦ InfinitePlace.eq_iff_isEquiv.mpr (Place.mk_eq_mk_iff.mp h)

/-- The places given by infinite places are archimedean. -/
lemma InfinitePlace.isArchimedean_toPlace : w.toPlace.IsArchimedean := by
  intro h
  have h2 : w (2 : K) = 2 := by exact_mod_cast w.map_natCast 2
  have h11 : w (1 + 1) ≤ max (w 1) (w 1) := h 1 1
  rw [one_add_one_eq_two, h2, map_one, max_self] at h11
  norm_num at h11

variable [NumberField K] (v : FinitePlace K)

lemma FinitePlace.isNontrivial : v.1.IsNontrivial := by
  rcases Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot with ⟨x, hx, hx0⟩
  refine ⟨x, by exact_mod_cast hx0, ?_⟩
  have hlt : v x < 1 := by
    rw [← FinitePlace.norm_embedding_eq]
    exact (FinitePlace.norm_lt_one_iff_mem K v.maximalIdeal x).mpr hx
  exact hlt.ne

/-- The place of a number field given by a finite place, that is by a maximal ideal of `𝓞 K`. -/
def FinitePlace.toPlace : AbsoluteValue.Place K :=
  .mk v.1 v.isNontrivial

/-- Distinct finite places give distinct places. -/
lemma FinitePlace.toPlace_injective : Function.Injective (FinitePlace.toPlace (K := K)) := by
  intro v₁ v₂ h
  have hv : v₁.1.IsEquiv v₂.1 := Place.mk_eq_mk_iff.mp h
  have key (x : 𝓞 K) : x ∈ v₁.maximalIdeal.asIdeal ↔ x ∈ v₂.maximalIdeal.asIdeal := by
    rw [← FinitePlace.norm_lt_one_iff_mem K, ← FinitePlace.norm_lt_one_iff_mem K,
      FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding_eq]
    exact hv.lt_one_iff
  rw [← v₁.mk_maximalIdeal, ← v₂.mk_maximalIdeal, FinitePlace.mk_eq_iff]
  exact HeightOneSpectrum.ext (Ideal.ext key)

/-- The places given by finite places are nonarchimedean. -/
lemma FinitePlace.not_isArchimedean_toPlace : ¬v.toPlace.IsArchimedean :=
  not_not.mpr fun x y ↦ v.add_le x y

end NumberField
