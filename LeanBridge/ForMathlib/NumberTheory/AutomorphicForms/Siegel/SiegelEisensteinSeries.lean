import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IbukiyamaRings

/-!
# Siegel Eisenstein series

The Siegel Eisenstein series of degree `g` and weight `k` is `ψ_k(Z) = ∑_{(C, D)} det(CZ + D)^{-k}`,
summed over the bottom rows `(C, D)` of the elements of `Sp(2g, ℤ)` up to left multiplication by
`GL(g, ℤ)`, that is over the right cosets `Pγ` of the Siegel parabolic subgroup
`P = {(A, B; 0, D)}` of `Sp(2g, ℤ)`: left multiplication by `(A, B; 0, D) ∈ P` changes the bottom
row `(C, D')` into `(DC, DD')`, and `D` runs over `GL(g, ℤ)`, with `A = D^{-T}` and `B = 0`. For
`γ ∈ P`, `det(C_{γδ}Z + D_{γδ}) = det(D_γ) det(C_δ Z + D_δ)` with `det D_γ = ±1`, so for even `k`
the terms only depend on the cosets. Siegel proved that for even `k > g + 1` the series converges
absolutely to a Siegel modular form of weight `k` on `Sp(2g, ℤ)`; this is not proved here. It is
the Klingen Eisenstein series of the constant `1` of degree `0` (`klingenEisensteinSeries` with
`r = 0`), which lives on the Siegel upper half-space indexed by `Empty ⊕ l`; it is defined here
directly on the one indexed by `l`, as the knowl defines it.

## Main definitions

* `SymplecticGroup.SiegelParabolicCosets`: the right cosets `P \ Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.siegelEisensteinTerm`: the term `det(CZ + D)^{-k}`.
* `SiegelUpperHalfSpace.siegelEisensteinSeries` (LMFDB `mf.siegel.eisenstein_series`): the Siegel
  Eisenstein series `ψ_k`.

## Main results

* `SiegelUpperHalfSpace.siegelEisensteinTerm_mul`: for even `k`, the terms only depend on the cosets
  of the Siegel parabolic subgroup.
-/

open Matrix

namespace SymplecticGroup

variable (l : Type*) [Fintype l] [DecidableEq l]

/-- The right cosets `Pγ` of the Siegel parabolic subgroup `P = {(A, B; 0, D)}` in `Sp(2g, ℤ)`, in
bijection with the bottom rows `(C, D)` of the elements of `Sp(2g, ℤ)` up to left multiplication by
`GL(g, ℤ)`. -/
abbrev SiegelParabolicCosets : Type _ :=
  Quotient (QuotientGroup.rightRel (siegelParabolic l ℤ))

end SymplecticGroup

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] (k : ℤ) (Z : SiegelUpperHalfSpace l)
    (δ : symplecticGroup l ℤ)

/-- The term `det(CZ + D)^{-k}` of the Siegel Eisenstein series of weight `k`, for
`δ = (A, B; C, D) ∈ Sp(2g, ℤ)` and `Z ∈ ℋ_g`. -/
noncomputable def siegelEisensteinTerm : ℂ :=
  (denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val).det ^ (-k)

/-- **The terms of the Siegel Eisenstein series only depend on the coset `Pδ`** of the Siegel
parabolic subgroup `P`, for even `k`: for `γ = (A, B; 0, D) ∈ P`,
`det(C_{γδ}Z + D_{γδ}) = det(D) det(C_δ Z + D_δ)` and `det D = ±1`. -/
lemma siegelEisensteinTerm_mul (hk : Even k) (γ : SymplecticGroup.siegelParabolic l ℤ) :
    siegelEisensteinTerm k Z ((γ : symplecticGroup l ℤ) * δ) = siegelEisensteinTerm k Z δ := by
  have hC (i j : l) : (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ) (.inr i) (.inl j) = 0 :=
    congrFun (congrFun γ.2 i) j
  have hD (W : SiegelUpperHalfSpace l) :
      (denom (SymplecticGroup.map (Int.castRingHom ℝ) (γ : symplecticGroup l ℤ)) W.val).det =
        ((γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂.det : ℂ) := by
    have h : denom (SymplecticGroup.map (Int.castRingHom ℝ) (γ : symplecticGroup l ℤ)) W.val =
        (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂.map (Int.castRingHom ℂ) := by
      ext i j
      simp [denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, hC]
    rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
  have hv : ((γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂.det : ℂ) ^ (-k) = 1 := by
    rcases Int.isUnit_iff.mp (SymplecticGroup.isUnit_det_toBlocks₂₂ γ) with h | h <;>
      simp [h, hk.neg.neg_one_zpow]
  rw [siegelEisensteinTerm, siegelEisensteinTerm, map_mul, denom_mul, det_mul, mul_zpow, hD, hv,
    one_mul]

lemma siegelEisensteinTerm_out (hk : Even k) :
    siegelEisensteinTerm k Z (⟦δ⟧ : SymplecticGroup.SiegelParabolicCosets l).out =
      siegelEisensteinTerm k Z δ := by
  have h : δ * (⟦δ⟧ : SymplecticGroup.SiegelParabolicCosets l).out⁻¹ ∈
      SymplecticGroup.siegelParabolic l ℤ :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out δ)
  conv_rhs => rw [← inv_mul_cancel_right δ (⟦δ⟧ : SymplecticGroup.SiegelParabolicCosets l).out]
  exact (siegelEisensteinTerm_mul k Z _ hk ⟨_, h⟩).symm

/-- The **Siegel Eisenstein series** `ψ_k` (LMFDB `mf.siegel.eisenstein_series`) of degree `g` and
weight `k`: `ψ_k(Z) = ∑_{(C, D)} det(CZ + D)^{-k}`, the sum over the bottom rows `(C, D)` of the
elements of `Sp(2g, ℤ)` up to left multiplication by `GL(g, ℤ)`, that is over the right cosets of
the Siegel parabolic subgroup `{(A, B; 0, D)}`, with chosen representatives; for even `k` the terms
do not depend on them (`siegelEisensteinTerm_mul`). The knowl takes `k` even with `k > g + 1`, where
the series converges absolutely to a Siegel modular form of weight `k` on `Sp(2g, ℤ)`, with
constant term `1` (Siegel); this is not proved here. The `tsum` is the sum of the series wherever it
converges absolutely, and the junk value `0` elsewhere. -/
noncomputable def siegelEisensteinSeries : ℂ :=
  ∑' x : SymplecticGroup.SiegelParabolicCosets l, siegelEisensteinTerm k Z x.out

end SiegelUpperHalfSpace
