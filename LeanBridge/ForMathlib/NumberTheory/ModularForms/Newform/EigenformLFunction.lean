import TauCeti.NumberTheory.ModularForms.LFunction.EulerProduct
import TauCeti.NumberTheory.ModularForms.LFunction.FunctionalEquation

/-!
# The functional equation of the L-function of a Hecke eigenform

Hecke, building on Mordell, introduced operators acting on spaces of modular forms, and a
normalised simultaneous eigenform of these operators has multiplicative Fourier coefficients, so
that its Dirichlet series has an Euler product and a functional equation (LMFDB
`lfunction.history.hecke_operators`). The eigenforms are Tau Ceti's full Hecke eigenforms
`HeckeRing.GL2.Eigenform N k`: nonzero cusp forms of weight `k` on `Γ₁(N)` with a nebentypus that
are eigenforms of every Hecke operator `T_n`. For such an `f`, normalised by `a₁ = 1`, Tau Ceti
proves that the coefficients are multiplicative (`HeckeRing.GL2.Eigenform.qExpansion_coeff_mul`)
and that the Dirichlet series `L(s, f) = ∑ aₙ n⁻ˢ` is the product of its Euler factors
(`HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd`).

This file gives the functional equation of the Dirichlet series. It needs no eigenform: let `f` be
a cusp form of weight `k > 0` on `Γ₁(N)`. On `Re s > k/2 + 1` the Dirichlet series is completed by
`Λ_M(s, f) = M^{s/2} (2π)^{-s} Γ(s) L(s, f)`, Tau Ceti's level-`M` completed L-function, which is
entire (`CuspForm.differentiable_frickeCompletedL`). Hecke's equation is
`Λ_N(k - s, f) = i^k Λ_N(s, 𝒲_N f)` (`CuspForm.frickeCompletedL_functional_equation_gamma1`), where
`𝒲_N f` is the normalised Fricke transform of `f`. At level `1`, where Hecke worked, `𝒲_1 f = f`,
and the equation reads `Λ(k - s, f) = i^k Λ(s, f)`. For a newform `f` of any level, `𝒲_N f` is a
multiple of the newform with the conjugate coefficients, and the equation becomes
`Λ(s, f) = ε conj (Λ(1 - conj s, f))` in the analytic normalisation
(`HeckeRing.GL2.Newform.analyticCompletedL_eq_rootNumber_mul`).

## Main results

* `CuspForm.frickeCompletedL_eq_mul_LSeries`: the completed L-function of a cusp form on `Γ₁(N)`
  completes its Dirichlet series.
* `CuspForm.normalizedFrickeOperatorCusp_eq_self`: at level `1` the normalised Fricke operator is
  the identity.
* `CuspForm.frickeCompletedL_sub_eq_of_level_one`: the functional equation of a cusp form of level
  `1`.

## References

* E. Hecke, *Über Modulfunktionen und die Dirichletschen Reihen mit Eulerscher
  Produktentwicklung. I, II*, Math. Ann. 114 (1937), 1–28 and 316–351.
-/

open Complex CongruenceSubgroup Matrix SpecialLinearGroup

open UpperHalfPlane hiding I

open scoped MatrixGroups Real

lemma TauCeti.frickeGL_one_eq_mapGL_S : frickeGL ℝ 1 = mapGL ℝ ModularGroup.S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

namespace CuspForm

variable {k : ℤ} {s : ℂ}

/-- **The completed L-function completes the Dirichlet series** (LMFDB
`lfunction.history.hecke_operators`): for a cusp form `f` of weight `k > 0` on `Γ₁(N)`, in
particular for a Hecke eigenform, Tau Ceti's level-`M` completed L-function is
`Λ_M(s, f) = M^{s/2} (2π)^{-s} Γ(s) ∑ aₙ n⁻ˢ` on `Re s > k/2 + 1`. -/
lemma frickeCompletedL_eq_mul_LSeries {N : ℕ} [NeZero N] (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : ℕ+) (hk : 0 < k) (hs : (k : ℝ) / 2 + 1 < s.re) : f.frickeCompletedL M s =
      ((M : ℕ) : ℂ) ^ (s / 2) * (2 * π) ^ (-s) * Gamma s *
          LSeries (fun n ↦ (qExpansion 1 f).coeff n) s := by
  have hs0 : 0 < s.re := by
    have hk' : (0 : ℝ) < k := mod_cast hk
    linarith
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
  have hpow : (2 * (π : ℂ)) ^ (-s) ≠ 0 := by
    simp
  have hL : LSeries (fun n ↦ (qExpansion 1 f).coeff n) s = ModularForm.L hk f s := by
    simpa using LSeries_qExpansion_coeff_eq hk f hs
  rw [f.frickeCompletedL_eq_cpow_mul_Λ M hk s, hL,
    ModularForm.L_apply_of_ne_zero hk _ fun h ↦ by simp [h] at hs0, Gammaℂ_def]
  field_simp

variable (f : CuspForm ((Gamma1 1).map (mapGL ℝ)) k)

/-- **At level `1` the normalised Fricke operator is the identity**: the Fricke matrix
`!![0, -1; 1, 0]` is the inversion `S` of `SL(2, ℤ)`, under which a cusp form of level `1` is
invariant, and the normalising constant `(√1)^{2 - k}` is `1`. -/
lemma normalizedFrickeOperatorCusp_eq_self : TauCeti.normalizedFrickeOperatorCusp k f = f := by
  have hmem : mapGL ℝ ModularGroup.S ∈ (Gamma1 1).map (mapGL ℝ) := by
    rw [TauCeti.Gamma1_one_map_eq_SL]
    exact ⟨ModularGroup.S, rfl⟩
  ext z
  rw [TauCeti.coe_normalizedFrickeOperatorCusp, TauCeti.frickeGL_one_eq_mapGL_S,
    SlashInvariantFormClass.slash_action_eq f _ hmem, TauCeti.atkinLehnerNormalizer_def]
  simp

variable (s) in
/-- **The functional equation of a cusp form of level `1`** (LMFDB
`lfunction.history.hecke_operators`), Hecke's case: `Λ(k - s, f) = i^k Λ(s, f)` for a cusp form
`f` of level `1` and weight `k > 0`, in particular for a Hecke eigenform, where
`Λ(s, f) = (2π)^{-s} Γ(s) ∑ aₙ n⁻ˢ` on `Re s > k/2 + 1`
(`CuspForm.frickeCompletedL_eq_mul_LSeries`). -/
lemma frickeCompletedL_sub_eq_of_level_one (hk : 0 < k) :
    f.frickeCompletedL 1 ((k : ℂ) - s) = I ^ k * f.frickeCompletedL 1 s := by
  have h : f.frickeCompletedL 1 ((k : ℂ) - s) =
      I ^ k * (TauCeti.normalizedFrickeOperatorCusp k f).frickeCompletedL 1 s :=
    f.frickeCompletedL_functional_equation_gamma1 hk s
  rwa [normalizedFrickeOperatorCusp_eq_self] at h

end CuspForm
