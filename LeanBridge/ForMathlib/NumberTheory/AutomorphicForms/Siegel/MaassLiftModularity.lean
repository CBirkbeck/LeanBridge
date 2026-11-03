import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftHolomorphic

/-!
# Modularity of the Maass lift

The Fourier coefficients of a Jacobi form `φ ∈ J_{k,1}` grow polynomially
(`ModularForm.norm_jacobiCoeff_le_of_mem_jacobiFormSpace`), which is the hypothesis of the
reduction of the theorem of Maass to a coefficient bound
(`SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_norm_jacobiCoeff_le`), and
`J_{k,1} = 0` for `k ≤ 0` (`ModularForm.eq_zero_of_mem_jacobiFormSpace_of_nonpos`) and for
odd `k`. So the series of the Maass lift `V : J_{k,1} → M_k(Sp(4, ℤ))`
(`SiegelUpperHalfSpace.maassLift`, LMFDB `mf.siegel.lift.maass`) converges absolutely on `ℋ₂` for
every `φ ∈ J_{k,1}`, and `Vφ` is a Siegel modular form of weight `k` on `Sp(4, ℤ)` for every
weight `k ≠ 2` (Maass; Eichler and Zagier, Theorem 6.2), with no hypothesis left.

The theorem of Maass `SiegelUpperHalfSpace.MaassLiftTheorem` then follows from the vanishing of
`J_{2,1}` (Eichler and Zagier, Theorem 3.5, from `M_2(SL(2, ℤ)) = S_4(SL(2, ℤ)) = 0` and the
Taylor development of Jacobi forms) and from the cusp-form condition `Φ(Vφ ∣ γ) = 0`,
`γ ∈ Sp(4, ℚ)`, for the Jacobi cusp forms `φ`. These are proved in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.WeightTwoVanishing` and
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftCuspForm`, which proves
`MaassLiftTheorem`.

## Main results

* `SiegelUpperHalfSpace.summable_maassLift_of_mem_jacobiFormSpace`: the series of the Maass lift
  of every `φ ∈ J_{k,1}` converges absolutely on `ℋ₂`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_three_le`: the Maass lift of
  `φ ∈ J_{k,1}`, `k ≥ 3`, is a Siegel modular form of weight `k` on `Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_ne_two`: the same for every weight
  `k ≠ 2`.
-/

open ModularForm SymplecticGroup

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {φ : ℍ × ℂ → ℂ}

private lemma maassCoeff_jacobiCoeff_zero (n r m : ℤ) :
    maassCoeff k (jacobiCoeff (0 : ℍ × ℂ → ℂ)) n r m = 0 := by
  rw [hasJacobiFourierExpansion_zero.jacobiCoeff_eq]
  simp [maassCoeff, liftDivisorSum]

lemma maassLift_zero : maassLift k (0 : ℍ × ℂ → ℂ) = 0 :=
  funext fun Z ↦ by
    simp [maassLift, maassCoeff_jacobiCoeff_zero]

private lemma eq_zero_of_mem_jacobiFormSpace_one_of_lt_three (hφ : φ ∈ jacobiFormSpace k 1)
    (hk : k < 3) (hk2 : k ≠ 2) : φ = 0 := by
  rcases le_or_gt k 0 with hk0 | hk0
  · exact eq_zero_of_mem_jacobiFormSpace_of_nonpos one_pos hφ hk0
  · exact eq_zero_of_mem_jacobiFormSpace_one_of_odd hφ ⟨0, by omega⟩

/-- **The series of the Maass lift converges absolutely** on `ℋ₂` for every Jacobi form
`φ ∈ J_{k,1}`: for `k ≥ 1` the Fourier coefficients of `φ` grow polynomially, and `φ = 0` for
`k ≤ 0`. -/
lemma summable_maassLift_of_mem_jacobiFormSpace (hφ : φ ∈ jacobiFormSpace k 1)
    (Z : SiegelUpperHalfSpace (Fin 2)) : Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z := by
  rcases le_or_gt 1 k with hk | hk
  · exact summable_maassLift_of_norm_jacobiCoeff_le Z hφ hk fun n r ↦
      norm_jacobiCoeff_le_of_mem_jacobiFormSpace n r one_pos hφ
  · rw [eq_zero_of_mem_jacobiFormSpace_of_nonpos one_pos hφ (by omega)]
    simp [maassCoeff_jacobiCoeff_zero]

/-- **The theorem of Maass in weight `k ≥ 3`** (LMFDB `mf.siegel.lift.maass`; Eichler and Zagier,
Theorem 6.2): the Maass lift of a Jacobi form `φ ∈ J_{k,1}` of weight `k ≥ 3` is a Siegel modular
form of weight `k` on `Sp(4, ℤ)`. -/
lemma maassLift_mem_scalarModularForms_of_three_le (hφ : φ ∈ jacobiFormSpace k 1) (hk : 3 ≤ k) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) :=
  maassLift_mem_scalarModularForms_of_norm_jacobiCoeff_le hφ hk fun n r ↦
    norm_jacobiCoeff_le_of_mem_jacobiFormSpace n r one_pos hφ

/-- **The theorem of Maass in weight `k ≠ 2`** (LMFDB `mf.siegel.lift.maass`): the Maass lift of
a Jacobi form `φ ∈ J_{k,1}` is a Siegel modular form of weight `k` on `Sp(4, ℤ)` for every
`k ≠ 2`, as `J_{k,1} = 0` for `k ≤ 1`. -/
lemma maassLift_mem_scalarModularForms_of_ne_two (hφ : φ ∈ jacobiFormSpace k 1) (hk : k ≠ 2) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) := by
  rcases le_or_gt 3 k with hk3 | hk3
  · exact maassLift_mem_scalarModularForms_of_three_le hφ hk3
  · rw [eq_zero_of_mem_jacobiFormSpace_one_of_lt_three hφ hk3 hk, maassLift_zero]
    exact zero_mem _

end SiegelUpperHalfSpace
