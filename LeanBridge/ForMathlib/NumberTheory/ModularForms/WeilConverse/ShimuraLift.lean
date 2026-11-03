import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraCorrespondence
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.Basic

/-!
# The Shimura lift from the functional equations

Shimura's theorem (LMFDB `cmf.shimura_correspondence`) says that for `g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`
the sequence `A = Sh_t(a)` of `ModularForm.shimuraCoeff` is the sequence of Fourier coefficients of
a modular form of weight `k - 1`. His proof has two parts: the Rankin–Selberg method with theta
series and Eisenstein series, which gives the functional equations of the twists of the Dirichlet
series of `A`, and Weil's converse theorem, which turns them into modularity. The second part is
`ModularForm.HasWeilFunctionalEquations.modularForm_mem`. This file records the consequence, which
is conditional and is not Shimura's theorem: what remains of modularity is
`HasWeilFunctionalEquations (shimuraCoeff χ k t a) b (k - 1) χ'`, for some character `χ'` modulo
some `M` and a dual sequence `b`. Shimura's theorem also says that one may take `χ' = χ²` and,
by Niwa for `k ≥ 7` and Cipra for `k = 3, 5`, the level `M = N / 2`. For `k ≥ 3` the theorem is
`ModularForm.shimuraCorrespondence`, proved by a theta kernel without the converse theorem; with
`ModularForm.hasWeilFunctionalEquations_qExpansion_coeff`, the modular form it gives satisfies the
hypothesis of `ModularForm.HasWeilFunctionalEquations.isShimuraLift` for every `g`.

## Main results

* `ModularForm.HasWeilFunctionalEquations.coeff_qExpansion_modularForm`: the Fourier coefficients of
  the modular form of Weil's converse theorem are the given sequence.
* `ModularForm.HasWeilFunctionalEquations.isShimuraLift`: the functional equations of the sequence
  `Sh_t(a)` give a Shimura lift of `g`, a modular form.
-/

open Complex CongruenceSubgroup Function

open scoped Real Manifold ModularForm MatrixGroups

open UpperHalfPlane hiding I I_re I_im

open Matrix SpecialLinearGroup

namespace ModularForm

variable {M : ℕ} [NeZero M] {χ' : DirichletCharacter ℂ M} {a b : ℕ → ℂ} {κ : ℤ}

/-- **The Fourier coefficients of the form of Weil's converse theorem** are the given sequence. -/
lemma HasWeilFunctionalEquations.coeff_qExpansion_modularForm
    (h : HasWeilFunctionalEquations a b κ χ') (hκ : 0 < κ) (n : ℕ) :
    (qExpansion 1 (h.modularForm hκ)).coeff n = a n := by
  refine (ModularFormClass.qExpansion_coeff_unique one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map M) (fun τ ↦ ?_) n).symm
  simp only [qParam_one_pow]
  exact (h.polyGrowth_left.summable_mul_cexp τ.im_pos).hasSum

/-- **Shimura's lift from the functional equations.** Let `g ∈ S_{k/2}(N, χ)` have coefficients `a`.
If the sequence `Sh_t(a)` and a sequence `b` satisfy the functional equations of Weil's converse
theorem in weight `k - 1 > 0` for a character `χ'` modulo `M`, then the modular form of that theorem
is a Shimura lift of `g`. -/
lemma HasWeilFunctionalEquations.isShimuraLift {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ} {t : ℕ}
    (g : halfIntegralWeightCuspSpace χ k)
    (h : HasWeilFunctionalEquations
      (shimuraCoeff χ k t fun m ↦ (qExpansion 1 (g : ℍ → ℂ)).coeff m) b (k - 1) χ')
    (hk : 0 < k - 1) : IsShimuraLift χ k t g (h.modularForm hk) :=
  fun n _ ↦ h.coeff_qExpansion_modularForm hk n

end ModularForm
