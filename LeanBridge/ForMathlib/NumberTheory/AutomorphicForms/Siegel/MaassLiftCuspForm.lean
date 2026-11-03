import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.WeightTwoVanishing
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CuspCriterion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GritsenkoLiftCuspForm
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftModularity

/-!
# The theorem of Maass

The Maass lift `F = Vφ` (`SiegelUpperHalfSpace.maassLift`, LMFDB `mf.siegel.lift.maass`) of a
Jacobi cusp form `φ ∈ J_{k,1}^cusp` is the Gritsenko lift of level `1`
(`SiegelUpperHalfSpace.maassLift_eq_gritsenkoLift`), so it is a Siegel cusp form:
`Φ(F ∣ γ) = 0` for every `γ ∈ Sp(4, ℚ)` (`SiegelUpperHalfSpace.isCuspForm_gritsenkoLift`).

With `J_{2,1} = 0` (`ModularForm.eq_zero_of_mem_jacobiFormSpace_two`), this proves the theorem of
Maass `SiegelUpperHalfSpace.MaassLiftTheorem` in full: the series of `Vφ` converges absolutely on
`ℋ₂`, `Vφ ∈ M_k(Sp(4, ℤ))` for every `φ ∈ J_{k,1}`, and `Vφ ∈ S_k(Sp(4, ℤ))` for every Jacobi cusp
form `φ` (Eichler and Zagier, Theorem 6.2). The Fourier coefficients of `F` then have positive
definite support (`SiegelUpperHalfSpace.posDef_of_siegelOperatorVanishes`), so that
`F(p diag(τ', it)) → 0` as `t → ∞` for `p` in the Siegel parabolic subgroup of `Sp(4, ℝ)`
(`SiegelUpperHalfSpace.tendsto_dual_smul_diagPoint_of_posDef`). The lift is a linear map
`V : J_{k,1} → M_k(Sp(4, ℤ))`, the series being additive in the Fourier coefficients.

## Main definitions

* `SiegelUpperHalfSpace.maassLiftLinearMap` (LMFDB `mf.siegel.lift.maass`): the Maass lift
  `J_{k,1} → M_k(Sp(4, ℤ))` as a linear map.

## Main results

* `SiegelUpperHalfSpace.isCuspForm_maassLift`: the Maass lift of a Jacobi cusp form is a cusp form.
* `SiegelUpperHalfSpace.maassLiftTheorem`: the theorem of Maass.
* `SiegelUpperHalfSpace.tendsto_maassLift_smul_diagPoint`: `F(p diag(τ', it)) → 0` as `t → ∞` for
  `p` in the Siegel parabolic subgroup of `Sp(4, ℝ)`.
* `SiegelUpperHalfSpace.siegelOperatorVanishes_slash_maassLift`: `Φ(F ∣ p) = 0` for such `p`.
-/

open Filter Matrix ModularForm SymplecticGroup Topology

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} {P : symplecticGroup (Fin 2) ℝ} (τ' : ℍ) (n r m : ℤ)
    (c c' : ℤ × ℤ → ℂ) (u : ℂ)

/-- **The Maass lift of a Jacobi cusp form is a cusp form** (LMFDB `mf.siegel.lift.maass`): for
`φ ∈ J_{k,1}^cusp`, `Φ(Vφ ∣ γ) = 0` for every `γ ∈ Sp(4, ℚ)`, as `Vφ` is the Gritsenko lift of level
`1` of `φ`. -/
lemma isCuspForm_maassLift (hφ : φ ∈ jacobiCuspFormSpace k 1) :
    IsCuspForm (TauCeti.detPowerRep ℂ 2 k) (maassLift k φ) := by
  rw [maassLift_eq_gritsenkoLift hφ]
  exact isCuspForm_gritsenkoLift (L := 1) hφ

/-- **The theorem of Maass** (LMFDB `mf.siegel.lift.maass`; Eichler and Zagier, Theorem 6.2): for
every Jacobi form `φ ∈ J_{k,1}` the series of the Maass lift `Vφ` converges absolutely on `ℋ₂`,
`Vφ` is a Siegel modular form of weight `k` on `Sp(4, ℤ)`, and it is a cusp form if `φ` is one.
So `V` is a map `J_{k,1} → M_k(Sp(4, ℤ))` sending `J_{k,1}^cusp` to `S_k(Sp(4, ℤ))`. -/
lemma maassLiftTheorem : MaassLiftTheorem := by
  have hm (k : ℤ) (φ : ℍ × ℂ → ℂ) (hφ : φ ∈ jacobiFormSpace k 1) :
      maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) := by
    rcases eq_or_ne k 2 with rfl | hk
    · rw [eq_zero_of_mem_jacobiFormSpace_two hφ, maassLift_zero]
      exact zero_mem _
    · exact maassLift_mem_scalarModularForms_of_ne_two hφ hk
  exact ⟨fun _ _ hφ ↦ summable_maassLift_of_mem_jacobiFormSpace hφ, hm,
    fun k φ hφ ↦ ⟨hm k φ hφ.1, isCuspForm_maassLift hφ⟩⟩

private lemma exists_hasSiegelFourierExpansion_maassLift (hφ : φ ∈ jacobiCuspFormSpace k 1) : ∃ b,
    HasSiegelFourierExpansion (integral (Fin 2)) (maassLift k φ) b ∧ ∀ n, b n ≠ 0 →
      (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef := by
  have hF : maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) :=
    maassLiftTheorem.mem_modularForms k φ hφ.1
  rcases exists_hasSiegelFourierExpansion _ (isArithmetic_integral (Fin 2)) hF with ⟨b, hb⟩
  have hv : SiegelOperatorVanishes (maassLift k φ) := by
    simpa [slash_one] using isCuspForm_maassLift hφ 1
  exact ⟨b, hb, posDef_of_siegelOperatorVanishes hF hb hv⟩

/-- **The Maass lift of a Jacobi cusp form vanishes at the cusp `diag(τ', i∞)` after any element of
the Siegel parabolic subgroup**: for `φ ∈ J_{k,1}^cusp` and `p = (A, B; 0, D) ∈ Sp(4, ℝ)`,
`(Vφ)(p diag(τ', it)) → 0` as `t → ∞`, the Fourier coefficients of `Vφ` having positive definite
support. -/
lemma tendsto_maassLift_smul_diagPoint (hφ : φ ∈ jacobiCuspFormSpace k 1)
    (hP : P ∈ siegelParabolic (Fin 2) ℝ) :
    Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ maassLift k φ (P • diagPoint τ' t)) atTop (𝓝 0) := by
  rcases exists_hasSiegelFourierExpansion_maassLift hφ with ⟨b, hb, hpd⟩
  exact tendsto_dual_smul_diagPoint_of_posDef τ' LinearMap.id hP hb hpd

/-- **The Siegel operator vanishes on the Maass lift of a Jacobi cusp form slashed by the Siegel
parabolic subgroup**: `Φ(Vφ ∣ p) = 0` for `φ ∈ J_{k,1}^cusp` and `p = (A, B; 0, D) ∈ Sp(4, ℝ)`. -/
lemma siegelOperatorVanishes_slash_maassLift (hφ : φ ∈ jacobiCuspFormSpace k 1)
    (hP : P ∈ siegelParabolic (Fin 2) ℝ) :
    SiegelOperatorVanishes (slash (TauCeti.detPowerRep ℂ 2 k) P (maassLift k φ)) := by
  rcases exists_hasSiegelFourierExpansion_maassLift hφ with ⟨b, hb, hpd⟩
  exact siegelOperatorVanishes_slash_of_posDef _ hP hb hpd

private lemma maassCoeff_add :
    maassCoeff k (c + c') n r m = maassCoeff k c n r m + maassCoeff k c' n r m := by
  simp only [maassCoeff, liftDivisorSum]
  split_ifs <;> simp [mul_add, Finset.sum_add_distrib]

private lemma maassCoeff_smul : maassCoeff k (u • c) n r m = u * maassCoeff k c n r m := by
  simp only [maassCoeff, liftDivisorSum]
  split_ifs <;> simp [Finset.mul_sum, mul_left_comm]

private lemma maassLift_add {ψ : ℍ × ℂ → ℂ} (hφ : φ ∈ jacobiFormSpace k 1)
    (hψ : ψ ∈ jacobiFormSpace k 1) : maassLift k (φ + ψ) = maassLift k φ + maassLift k ψ :=
  funext fun Z ↦ by
    rw [Pi.add_apply, maassLift, maassLift, maassLift,
      ← (summable_maassLift_of_mem_jacobiFormSpace hφ Z).tsum_add
        (summable_maassLift_of_mem_jacobiFormSpace hψ Z)]
    refine tsum_congr fun p ↦ ?_
    rw [((hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ).add
      (hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hψ)).jacobiCoeff_eq,
      maassCoeff_add, add_mul]

private lemma maassLift_smul (hφ : φ ∈ jacobiFormSpace k 1) :
    maassLift k (u • φ) = u • maassLift k φ :=
  funext fun Z ↦ by
    rw [Pi.smul_apply, smul_eq_mul, maassLift, maassLift, ← tsum_mul_left]
    refine tsum_congr fun p ↦ ?_
    rw [((hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ).const_smul
      u).jacobiCoeff_eq, maassCoeff_smul, mul_assoc]

variable (k) in
/-- The **Maass lift** (LMFDB `mf.siegel.lift.maass`) as a linear map `V : J_{k,1} → M_k(Sp(4, ℤ))`
from the Jacobi forms of weight `k` and index `1` to the Siegel modular forms of weight `k` and
degree `2` on the Siegel modular group: `φ ↦ maassLift k φ`, which lies in `M_k(Sp(4, ℤ))` by the
theorem of Maass (`SiegelUpperHalfSpace.maassLiftTheorem`). It sends Jacobi cusp forms to cusp
forms. -/
noncomputable def maassLiftLinearMap :
    jacobiFormSpace k 1 →ₗ[ℂ] scalarModularForms k (integral (Fin 2)) where
  toFun φ := ⟨maassLift k φ, maassLiftTheorem.mem_modularForms k φ φ.2⟩
  map_add' φ ψ := Subtype.ext <| maassLift_add φ.2 ψ.2
  map_smul' u φ := Subtype.ext <| maassLift_smul u φ.2

end SiegelUpperHalfSpace
