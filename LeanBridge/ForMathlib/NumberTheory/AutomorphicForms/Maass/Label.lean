import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.SpectralIndex
import Mathlib.Order.PiLex

/-!
# The labels of Maass newforms

The label of a Maass newform `f ∈ M_k(Γ₀(N), χ)` (LMFDB `mf.maass.label`) is `N.k.a.m.d`, or `N.m`
when `k = 0`, `a = 1` and `d = 1`, where `N` is the level, `k` the weight, `N.a` the Conrey label
of the Dirichlet character `χ`, `m` the spectral index of the eigenvalue `λ` of `f`
(`UpperHalfPlane.maassSpectralIndexLabel`, LMFDB `mf.maass.spectral_index`), and `d` the index of
`f` among the finitely many Maass newforms of level `N`, character `χ` and eigenvalue `λ`, ordered
lexicographically by the sequences `(Re a(n), Im a(n))_{n ≥ 1}` of their coefficients.

The label is defined here from its five components (`UpperHalfPlane.maassLabel`), with the index `d`
relative to a given finite set of coefficient sequences (`UpperHalfPlane.maassCoeffIndex`) and the
spectral index relative to a given set of eigenvalues (`UpperHalfPlane.maassSpectralIndex`). For
weight `0` and level `N ≠ 0`: the Maass cusp forms with character `χ` and a given eigenvalue form a
finite-dimensional space (`UpperHalfPlane.finite_maassCuspSpace`); the Maass cusp newforms with
character `χ` have a discrete spectrum (`UpperHalfPlane.finite_maassNewformSpectrum_inter_Iic`), in
which `UpperHalfPlane.maassNewformSpectralIndexLabel` is the spectral index; and for the trivial
character, whose Conrey label is `N.1`, the even and odd cusp newforms with a given eigenvalue,
normalised by `a(1) = 1`, have finitely many coefficient sequences
(`UpperHalfPlane.finite_maassNewformCoeffSet`), and their label is
`UpperHalfPlane.maassNewformLabel`. Not available: the Conrey labels of the nontrivial characters,
at the pinned Mathlib and Tau Ceti; the coefficients of the newforms with a nontrivial character;
and the new space in weight `k ≠ 0`. The lexicographic order on the sequences
`(Re a(n), Im a(n))_{n ≥ 1}` is Mathlib's on `Lex (ℕ+ → Lex (ℝ × ℝ))`.

## Main definitions

* `UpperHalfPlane.maassCoeffKey`: the sequence `(Re a(n), Im a(n))_{n ≥ 1}`, with its lexicographic
  order.
* `UpperHalfPlane.maassCoeffIndex` (LMFDB `mf.maass.label`): the index `d` of a coefficient sequence
  in a finite set of them.
* `UpperHalfPlane.maassLabel` (LMFDB `mf.maass.label`): the label `N.k.a.m.d` or `N.m`.

## Main results

* `UpperHalfPlane.maassCoeffIndex_injOn`: the index `d` determines the coefficient sequence in the
  finite set.
-/

open Finset

namespace UpperHalfPlane

variable (F : Finset (ℕ+ → ℂ)) (c : ℕ+ → ℂ) {c' : ℕ+ → ℂ}

/-- The sequence `(Re c(n), Im c(n))_{n ≥ 1}` of the real and imaginary parts of a sequence `c` of
complex numbers, such as the coefficients of a Maass form, with the lexicographic order: first by
`(Re c(1), Im c(1))`, lexicographically, then by `(Re c(2), Im c(2))`, and so on. -/
def maassCoeffKey : Lex (ℕ+ → Lex (ℝ × ℝ)) :=
  toLex fun n ↦ toLex ((c n).re, (c n).im)

lemma maassCoeffKey_injective : Function.Injective maassCoeffKey :=
  fun _ _ h ↦ funext fun n ↦ Complex.ext_iff.mpr <| Prod.ext_iff.mp <| toLex.injective <|
    congrFun (toLex.injective h) n

open scoped Classical in
/-- The **index** `d` (LMFDB `mf.maass.label`) of a sequence `c` of coefficients in a finite set `F`
of them: one more than the number of sequences in `F` before `c` in the lexicographic order of the
sequences `(Re c(n), Im c(n))_{n ≥ 1}` (`UpperHalfPlane.maassCoeffKey`). For `F` the set of the
coefficient sequences of the normalised Maass newforms of a given level, character and eigenvalue,
it is the index `d` in the label of the newform with coefficients `c`; it determines `c` in `F`
(`maassCoeffIndex_injOn`). That set is finite for the even and odd cusp newforms of weight `0` with
trivial character and level `N ≠ 0` (`finite_maassNewformCoeffSet`), where the index is
`maassNewformCoeffIndex`; for the other newforms its finiteness is not proved here. -/
noncomputable def maassCoeffIndex : ℕ :=
  #{b ∈ F | maassCoeffKey b < maassCoeffKey c} + 1

/-- The **label** (LMFDB `mf.maass.label`) of a Maass newform of level `N`, weight `k`, Dirichlet
character of Conrey label `N.a`, spectral index `m` and index `d`: `N.m` when `k = 0`, `a = 1` and
`d = 1`, and `N.k.a.m.d` otherwise. The spectral index `m` of the eigenvalue `λ` in the set `S` of
the eigenvalues of the newforms of level `N`, weight `k` and character `χ` is written as
`UpperHalfPlane.maassSpectralIndexLabel S λ`, in base `26` with letters for exceptional eigenvalues,
and the index `d` is `UpperHalfPlane.maassCoeffIndex F c` for the coefficient sequence `c` of the
normalised newform and the set `F` of those of the normalised newforms of level `N`, character `χ`
and eigenvalue `λ`. In weight `0`, `S` is read as the spectrum of the Maass cusp newforms, with `m`
written as `UpperHalfPlane.maassNewformSpectralIndexLabel N χ λ`, and for the trivial character the
label of an even or odd cusp newform is `UpperHalfPlane.maassNewformLabel`. The Conrey index `a` is
given, the Conrey labels of the nontrivial characters not being available at the pinned Mathlib and
Tau Ceti. -/
def maassLabel (N : ℕ) (k : ℤ) (a : ℕ) (m : String) (d : ℕ) : String :=
  if k = 0 ∧ a = 1 ∧ d = 1 then s!"{N}.{m}" else s!"{N}.{k}.{a}.{m}.{d}"

variable {c} in
lemma maassCoeffIndex_lt_maassCoeffIndex (hc : c ∈ F) (h : maassCoeffKey c < maassCoeffKey c') :
    maassCoeffIndex F c < maassCoeffIndex F c' := by
  classical
  rw [maassCoeffIndex, maassCoeffIndex, add_lt_add_iff_right]
  refine card_lt_card <| (ssubset_iff_of_subset fun b hb ↦ ?_).mpr ⟨c, mem_filter.mpr ⟨hc, h⟩, ?_⟩
  · exact mem_filter.mpr ⟨(mem_filter.mp hb).1, (mem_filter.mp hb).2.trans h⟩
  · exact fun hc' ↦ (mem_filter.mp hc').2.false

/-- **The index `d` determines the coefficient sequence**: distinct sequences of a finite set `F`
have distinct indices, the earlier one in the lexicographic order having the smaller index. -/
lemma maassCoeffIndex_injOn : Set.InjOn (maassCoeffIndex F) F := by
  intro c hc c' hc' he
  by_contra hne
  rcases lt_or_gt_of_ne (maassCoeffKey_injective.ne hne) with h | h
  · exact (maassCoeffIndex_lt_maassCoeffIndex F hc h).ne he
  · exact (maassCoeffIndex_lt_maassCoeffIndex F hc' h).ne he.symm

end UpperHalfPlane
