import Mathlib.LinearAlgebra.Dimension.DivisionRing
import TauCeti.Geometry.Hodge.Dimension

/-!
# The signature of a motive

The Betti realisation of a motive over `ℚ`, such as a hypergeometric motive, is a rational Hodge
structure of some weight `w` together with the action `F_∞` of complex conjugation, a linear
involution whose complex-linear extension exchanges the Hodge components `H^{p,q}` and `H^{q,p}`.
It preserves the middle component `H^{w/2,w/2}` when `w` is even, and the signature of the motive
(LMFDB `hgm.signature`) is the difference between the numbers of eigenvalues `+1` and `-1` of
`F_∞` on it, the middle entry of the Hodge vector; it is `0` when there is no middle entry, that is
when the weight, equivalently the Hodge width, is odd.

Hypergeometric motives and their Betti realisations are not formalised, and the knowl gives no
formula for the signature of `H(A, B, t)` in terms of `A`, `B` and `t`, nor for the archimedean
root number it says is recovered from the signature and the Hodge vector. So the signature is
defined here for a pure Hodge structure on a complex vector space with conjugation (Tau Ceti's
`TauCeti.Hodge.HodgeStructureOn`) together with an infinite Frobenius
(`TauCeti.Hodge.HodgeStructureOn.InfiniteFrobenius`), the data the Betti realisation of a motive
provides, as the width of a motive is defined on Hodge types in `Hypergeometric.HodgeWidth`. Tau
Ceti's conjugation `ω`, which exchanges `H^{p,q}` and `H^{q,p}` antilinearly, is not `F_∞`.

## Main definitions

* `TauCeti.Hodge.HodgeStructureOn.InfiniteFrobenius`: an infinite Frobenius `F_∞` of a Hodge
  structure.
* `TauCeti.Hodge.HodgeStructureOn.InfiniteFrobenius.middlePlus`,
  `TauCeti.Hodge.HodgeStructureOn.InfiniteFrobenius.middleMinus`: the eigenspaces of `F_∞` for the
  eigenvalues `±1` in the middle Hodge component.
* `TauCeti.Hodge.HodgeStructureOn.InfiniteFrobenius.signature` (LMFDB `hgm.signature`): the
  signature.

## Main results

* `TauCeti.Hodge.HodgeStructureOn.InfiniteFrobenius.signature_of_odd`: the signature vanishes in
  odd weight.
* `TauCeti.Hodge.HodgeStructureOn.InfiniteFrobenius.finrank_middlePlus_add_finrank_middleMinus`:
  `F_∞` is diagonalisable on the middle Hodge component, with eigenvalues `±1`, so that the numbers
  of eigenvalues `+1` and `-1` add up to the middle Hodge number.
-/

open Module

namespace TauCeti.Hodge.HodgeStructureOn

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ω : Conjugation W} {n : ℤ}
    (hs : HodgeStructureOn W ω n)

/-- An **infinite Frobenius** `F_∞` of a pure Hodge structure `hs` of weight `n` on a complex
vector space `W` with conjugation `ω`: a complex-linear involution of `W` commuting with `ω`, so
that it is defined over the real structure, which exchanges the Hodge components `H^{p,q}` and
`H^{q,p}`. The action of complex conjugation on the Betti realisation of a motive over `ℚ`, or over
`ℝ`, extended linearly to its complexification, is such an involution. -/
structure InfiniteFrobenius where
  /-- The linear map `F_∞`. -/
  toLinearMap : W →ₗ[ℂ] W
  /-- `F_∞` is an involution. -/
  apply_apply (w : W) : toLinearMap (toLinearMap w) = w
  /-- `F_∞` commutes with the conjugation. -/
  apply_conj (w : W) : toLinearMap (ω.toEquiv w) = ω.toEquiv (toLinearMap w)
  /-- `F_∞` maps `H^{p,n-p}` onto `H^{n-p,p}`. -/
  map_piece (p : ℤ) : (hs.piece p).map toLinearMap = hs.piece (n - p)

namespace InfiniteFrobenius

variable {hs} (F : hs.InfiniteFrobenius)

/-- The eigenspace of an infinite Frobenius `F_∞` for the eigenvalue `+1` in the middle Hodge
component `H^{n/2,n/2}` of a Hodge structure of even weight `n`. -/
noncomputable def middlePlus : Submodule ℂ W :=
  hs.piece (n / 2) ⊓ (F.toLinearMap - 1).ker

/-- The eigenspace of an infinite Frobenius `F_∞` for the eigenvalue `-1` in the middle Hodge
component `H^{n/2,n/2}` of a Hodge structure of even weight `n`. -/
noncomputable def middleMinus : Submodule ℂ W :=
  hs.piece (n / 2) ⊓ (F.toLinearMap + 1).ker

/-- The **signature** (LMFDB `hgm.signature`) of a Hodge structure of weight `n` with an infinite
Frobenius `F_∞`, such as the Betti realisation of a motive: the number of eigenvalues `+1` minus
the number of eigenvalues `-1` of `F_∞` on the middle Hodge component `H^{n/2,n/2}` when `n` is
even, which are the dimensions of the eigenspaces `middlePlus` and `middleMinus` as `F_∞` is
diagonalisable there (`finrank_middlePlus_add_finrank_middleMinus`); and `0` when `n` is odd and
there is no middle component (`signature_of_odd`). -/
noncomputable def signature : ℤ :=
  if Even n then (finrank ℂ F.middlePlus : ℤ) - finrank ℂ F.middleMinus else 0

/-- **The signature vanishes in odd weight**, where there is no middle Hodge component. -/
lemma signature_of_odd (hn : Odd n) : F.signature = 0 :=
  ite_eq_right (Int.not_even_iff_odd.mpr hn)

lemma apply_mem_piece (hn : Even n) {w : W} (hw : w ∈ hs.piece (n / 2)) :
    F.toLinearMap w ∈ hs.piece (n / 2) := by
  have h : n - n / 2 = n / 2 := by
    rcases hn with ⟨m, rfl⟩
    omega
  rw [← h, ← F.map_piece]
  exact Submodule.mem_map_of_mem hw

/-- **`F_∞` is diagonalisable on the middle Hodge component**: in even weight, for a
finite-dimensional space, the dimensions of its eigenspaces for `+1` and `-1` in the middle
component `H^{n/2,n/2}` add up to the middle Hodge number `h^{n/2,n/2}`. -/
lemma finrank_middlePlus_add_finrank_middleMinus [FiniteDimensional ℂ W] (hn : Even n) :
    finrank ℂ F.middlePlus + finrank ℂ F.middleMinus = hs.hodgeNumber (n / 2) := by
  have hinf : F.middlePlus ⊓ F.middleMinus = ⊥ := by
    refine eq_bot_iff.mpr fun w hw ↦ (Submodule.mem_bot ℂ).mpr ?_
    have h₁ : F.toLinearMap w - w = 0 :=
      hw.1.2
    have h₂ : F.toLinearMap w + w = 0 :=
      hw.2.2
    have h : (2 : ℂ) • w = 0 := by
      rw [two_smul, ← h₂, sub_eq_zero.mp h₁]
    exact (smul_eq_zero.mp h).resolve_left two_ne_zero
  have hsup : F.middlePlus ⊔ F.middleMinus = hs.piece (n / 2) := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw ↦ ?_
    have hFw : F.toLinearMap w ∈ hs.piece (n / 2) :=
      F.apply_mem_piece hn hw
    have h₁ : (2 : ℂ)⁻¹ • (w + F.toLinearMap w) ∈ F.middlePlus := by
      refine ⟨Submodule.smul_mem _ _ (add_mem hw hFw), ?_⟩
      simp [F.apply_apply, add_comm]
    have h₂ : (2 : ℂ)⁻¹ • (w - F.toLinearMap w) ∈ F.middleMinus := by
      refine ⟨Submodule.smul_mem _ _ (sub_mem hw hFw), ?_⟩
      simp [F.apply_apply]
    have h : w = (2 : ℂ)⁻¹ • (w + F.toLinearMap w) + (2 : ℂ)⁻¹ • (w - F.toLinearMap w) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ w, smul_smul, inv_mul_cancel₀ two_ne_zero,
        one_smul]
    exact h ▸ Submodule.add_mem_sup h₁ h₂
  rw [hodgeNumber, ← hsup, ← Submodule.finrank_sup_add_finrank_inf_eq, hinf, finrank_bot, add_zero]

end InfiniteFrobenius

end TauCeti.Hodge.HodgeStructureOn
