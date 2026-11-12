import LeanBridge.ForMathlib.NumberTheory.LFunction.Completed
import LeanBridge.ForMathlib.NumberTheory.LFunction.SelbergClass

/-!
# The functional equation of an analytic L-function in Selberg's form

The LMFDB writes the functional equation of an analytic L-function (LMFDB
`lfunction.functional_equation`) as `Λ(s) = N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ) L(s)` and
`Λ(s) = ε conj (Λ (1 - conj s))`, with the restrictions of `AnalyticLFunction.SelbergData` on `N`,
`μⱼ` and `νₖ`, and adds that the axioms of the Selberg class are less restrictive. The sentence
compares this equation with Selberg's functional equation axiom (LMFDB
`lfunction.selberg_class.axioms`, `LSeries.SelbergFunctionalEquation`): `γ(s) L(s)` is invariant
under `s ↦ 1 - conj s` up to conjugation, for a gamma factor `γ(s) = ε' Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)` with
`|ε'| = 1`, `Q > 0`, `λᵢ > 0` and `re μᵢ ≥ 0`. The comparison is between the restrictions that the
two equations put on their data, as the knowl has just listed its own. The other axioms do not
enter: they add restrictions of their own, such as the Ramanujan hypothesis, which is expected but
not assumed for analytic L-functions.

Every functional equation of the LMFDB's form is one of Selberg's form. Since
`Γ_ℝ(s + μ) = π ^ (-μ / 2) π ^ (-s / 2) Γ(s / 2 + μ / 2)` and
`Γ_ℂ(s + ν) = 2 (2π) ^ (-ν) (2π) ^ (-s) Γ(s + ν)`, the factor `N ^ (s / 2) L_∞(s)` is
`C Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)`, with `Q = √N π ^ (-J / 2) (2π) ^ (-K)`, the pairs `(1 / 2, μⱼ / 2)` and
`(1, νₖ)`, and the constant `C = ∏ⱼ π ^ (-μⱼ / 2) ∏ₖ 2 (2π) ^ (-νₖ)`. Multiplying it by `ω / |C|`,
where `ω = exp (-i arg ε / 2)` is a square root of `conj ε`, absorbs `C` and the sign `ε`.

Selberg's form is strictly more general: its gamma factor `Γ(s / 3)` is not `c N ^ (s / 2) L_∞(s)`
for any Selberg data and any constant `c`, not even on the half-plane `re s > 0`. Otherwise the
inverses, which are entire, would agree on `ℂ`. But `1 / Γ(s / 3)` vanishes exactly at
`0, -3, -6, …`, while a zero of `1 / L_∞(s)` at `0` comes with a zero at `-2` (from a factor `Γ_ℝ`)
or at `-1` (from a factor `Γ_ℂ`). This compares the gamma factors that the two forms allow; it says
nothing about which Dirichlet series satisfy such an equation.

## Main definitions

* `AnalyticLFunction.SelbergData.gammaConst`: the constant `C`.
* `AnalyticLFunction.SelbergData.selbergGammaFactor`: the gamma factor of Selberg's form of the
  functional equation with given Selberg data.
* `LSeries.SelbergGammaFactor.gammaDivThree`: the gamma factor `Γ(s / 3)` of Selberg's form.

## Main results

* `AnalyticLFunction.SelbergData.conductor_cpow_mul_gammaFactor`: the LMFDB's gamma factor
  `N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` is `C Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)`.
* `AnalyticLFunction.SelbergData.toFun_selbergGammaFactor_mul_eq_conj_iff`: a function satisfies
  the LMFDB's functional equation with given Selberg data at a point if and only if it satisfies
  Selberg's there, with the gamma factor `AnalyticLFunction.SelbergData.selbergGammaFactor`.
* `AnalyticLFunction.SelbergData.not_eqOn_gammaDivThree` (LMFDB `lfunction.functional_equation`):
  the gamma factor `Γ(s / 3)` of Selberg's form is not of the LMFDB's form.
* `AnalyticLFunction.selbergFunctionalEquation_coeff` (LMFDB `lfunction.functional_equation`):
  every analytic L-function satisfies Selberg's functional equation axiom.
-/

open Complex LSeries Set

open scoped ComplexConjugate Real

namespace LSeries.SelbergGammaFactor

/-- The gamma factor `γ(s) = Γ(s / 3)` of Selberg's form (LMFDB `lfunction.selberg_class.axioms`),
with `ε = 1`, `Q = 1` and the single pair `(λ, μ) = (1 / 3, 0)`. It is not of the LMFDB's form
(`AnalyticLFunction.SelbergData.not_eqOn_gammaDivThree`). -/
noncomputable def gammaDivThree : SelbergGammaFactor where
  ε := 1
  Q := 1
  factors := {(1 / 3, 0)}
  norm_ε := norm_one
  Q_pos := one_pos
  fst_pos_of_mem_factors x hx := by
    rw [Multiset.mem_singleton.mp hx]
    norm_num
  re_snd_nonneg_of_mem_factors x hx := by
    rw [Multiset.mem_singleton.mp hx]
    simp

lemma toFun_gammaDivThree (s : ℂ) : gammaDivThree.toFun s = Gamma (s / 3) := by
  simp [toFun, gammaDivThree, div_eq_inv_mul]

end LSeries.SelbergGammaFactor

namespace AnalyticLFunction.SelbergData

variable (D : SelbergData) {s : ℂ}

/-- The constant `C = ∏ⱼ π ^ (-μⱼ / 2) ∏ₖ 2 (2π) ^ (-νₖ)` of a functional equation with Selberg
data `(N, μ, ν, ε)` written in Selberg's form: `N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` is `C`
times a gamma factor `Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)` (`conductor_cpow_mul_gammaFactor`). -/
noncomputable def gammaConst : ℂ :=
  (D.μ.map fun x ↦ (π : ℂ) ^ (-x / 2)).prod * (D.ν.map fun x ↦ 2 * (2 * π : ℂ) ^ (-x)).prod

lemma gammaConst_ne_zero : D.gammaConst ≠ 0 := by
  simp [gammaConst]

/-- The gamma factor `γ(s) = ε' Q ^ s ∏ᵢ Γ(λᵢ s + μᵢ)` of Selberg's form (LMFDB
`lfunction.selberg_class.axioms`) of the functional equation with Selberg data `(N, μ, ν, ε)` (LMFDB
`lfunction.functional_equation`): `Q = √N π ^ (-J / 2) (2π) ^ (-K)`, the pairs `(λ, μ)` are
`(1 / 2, μⱼ / 2)` and `(1, νₖ)`, and `ε' = ω C / |C|`, where `C` is `gammaConst` and
`ω = exp (-i arg ε / 2)` is a square root of `conj ε` when `|ε| = 1`. -/
noncomputable def selbergGammaFactor : SelbergGammaFactor where
  ε := exp (↑(-arg D.sign / 2) * I) * (D.gammaConst / ‖D.gammaConst‖)
  Q := √(D.conductor : ℝ) * π ^ (-(D.μ.card : ℝ) / 2) * (2 * π) ^ (-(D.ν.card : ℝ))
  factors := D.μ.map (fun x ↦ (1 / 2, x / 2)) + D.ν.map (fun x ↦ (1, x))
  norm_ε := by
    rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
    simp [D.gammaConst_ne_zero]
  Q_pos := mul_pos (mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr D.conductor_pos))
    (Real.rpow_pos_of_pos Real.pi_pos _)) (Real.rpow_pos_of_pos Real.two_pi_pos _)
  fst_pos_of_mem_factors x hx := by
    rcases Multiset.mem_add.mp hx with hx | hx <;>
      rcases Multiset.mem_map.mp hx with ⟨y, -, rfl⟩ <;> norm_num
  re_snd_nonneg_of_mem_factors x hx := by
    rcases Multiset.mem_add.mp hx with hx | hx <;> rcases Multiset.mem_map.mp hx with ⟨y, hy, rfl⟩
    · rcases D.re_eq_zero_or_one_of_mem_μ y hy with h | h <;> simp [h]
    · rcases D.exists_two_mul_re_eq_of_mem_ν y hy with ⟨k, -, hk⟩
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- **The LMFDB's gamma factor in Selberg's form** (LMFDB `lfunction.gamma_factor`,
`lfunction.selberg_class.axioms`): by `Γ_ℝ(s) = π ^ (-s / 2) Γ(s / 2)` and
`Γ_ℂ(s) = 2 (2π) ^ (-s) Γ(s)`, the factor `N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` is
`C Q ^ s ∏ⱼ Γ(s / 2 + μⱼ / 2) ∏ₖ Γ(s + νₖ)`, where `C` is `gammaConst`, and `Q` and the pairs
`(λ, μ)` are those of `selbergGammaFactor`. -/
lemma conductor_cpow_mul_gammaFactor : (D.conductor : ℂ) ^ (s / 2) * D.gammaFactor s =
    D.gammaConst * (D.selbergGammaFactor.Q : ℂ) ^ s *
        (D.selbergGammaFactor.factors.map fun x ↦ Gamma (x.1 * s + x.2)).prod := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hℝ (x : ℂ) : Gammaℝ (s + x) =
      (π : ℂ) ^ (-x / 2) * (π : ℂ) ^ (-s / 2) * Gamma ((1 / 2 : ℝ) * s + x / 2) := by
    rw [Gammaℝ_def, ← cpow_add _ _ hπ]
    congr 2 <;> push_cast <;> ring1
  have hℂ (x : ℂ) : Gammaℂ (s + x) =
      2 * (2 * π : ℂ) ^ (-x) * (2 * π : ℂ) ^ (-s) * Gamma ((1 : ℝ) * s + x) := by
    rw [Gammaℂ_def, neg_add_rev, cpow_add _ _ (mul_ne_zero two_ne_zero hπ), ofReal_one, one_mul,
      ← mul_assoc 2]
  have hN : ((√(D.conductor : ℝ) : ℝ) : ℂ) ^ s = (D.conductor : ℂ) ^ (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← cpow_mul_ofReal_nonneg (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring1
  have hJ : ((π ^ (-(D.μ.card : ℝ) / 2) : ℝ) : ℂ) ^ s = ((π : ℂ) ^ (-s / 2)) ^ D.μ.card := by
    rw [← cpow_mul_ofReal_nonneg Real.pi_pos.le, ← cpow_nat_mul]
    congr 1
    push_cast
    ring1
  have hK : (((2 * π) ^ (-(D.ν.card : ℝ)) : ℝ) : ℂ) ^ s = ((2 * π : ℂ) ^ (-s)) ^ D.ν.card := by
    rw [← cpow_mul_ofReal_nonneg Real.two_pi_pos.le, ← cpow_nat_mul]
    congr 1 <;> push_cast <;> ring1
  simp only [selbergGammaFactor]
  rw [ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (by positivity), ofReal_mul,
    mul_cpow_ofReal_nonneg (by positivity) (by positivity), hN, hJ, hK]
  simp only [gammaFactor, hℝ, hℂ, Multiset.prod_map_mul, Multiset.map_const',
    Multiset.prod_replicate, Multiset.map_add, Multiset.prod_add, Multiset.map_map,
    Function.comp_def, gammaConst]
  ring1

lemma toFun_selbergGammaFactor : D.selbergGammaFactor.toFun s =
    D.selbergGammaFactor.ε / D.gammaConst * ((D.conductor : ℂ) ^ (s / 2) * D.gammaFactor s) := by
  rw [conductor_cpow_mul_gammaFactor, SelbergGammaFactor.toFun, div_mul_eq_mul_div,
    eq_div_iff D.gammaConst_ne_zero]
  ring1

/-- **The LMFDB's functional equation is one of Selberg's form** (LMFDB
`lfunction.functional_equation`, `lfunction.selberg_class.axioms`): if `|ε| = 1`, a function `F`
satisfies `N ^ (s / 2) L_∞(s) F(s) = ε conj (N ^ (s' / 2) L_∞(s') F(s'))`, where `s' = 1 - conj s`
and `L_∞` is the gamma factor `∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` of the Selberg data
`(N, μ, ν, ε)`, if and only if `γ(s) F(s) = conj (γ(s') F(s'))` for the gamma factor
`γ = selbergGammaFactor` of Selberg's form. -/
lemma toFun_selbergGammaFactor_mul_eq_conj_iff {F : ℂ → ℂ} (hD : ‖D.sign‖ = 1) :
    D.selbergGammaFactor.toFun s * F s =
      conj (D.selbergGammaFactor.toFun (1 - conj s) * F (1 - conj s)) ↔
    (D.conductor : ℂ) ^ (s / 2) * D.gammaFactor s * F s = D.sign *
      conj ((D.conductor : ℂ) ^ ((1 - conj s) / 2) * D.gammaFactor (1 - conj s) *
        F (1 - conj s)) := by
  have hθ (θ : ℝ) : conj (exp (↑(-θ / 2) * I)) = exp (θ * I) * exp (↑(-θ / 2) * I) := by
    rw [← exp_conj, ← exp_add]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring1
  have hε :
      D.selbergGammaFactor.ε / D.gammaConst = exp (↑(-arg D.sign / 2) * I) / ‖D.gammaConst‖ := by
    rw [selbergGammaFactor, mul_div_assoc, div_div_cancel_left' D.gammaConst_ne_zero,
      ← div_eq_mul_inv]
  have hω : conj (D.selbergGammaFactor.ε / D.gammaConst) =
      D.sign * (D.selbergGammaFactor.ε / D.gammaConst) := by
    rw [hε, map_div₀, conj_ofReal, hθ,
      (by simpa [hD] using norm_mul_exp_arg_mul_I D.sign : exp (arg D.sign * I) = D.sign),
      mul_div_assoc]
  have hne : D.selbergGammaFactor.ε / D.gammaConst ≠ 0 :=
    div_ne_zero (norm_ne_zero_iff.mp <| D.selbergGammaFactor.norm_ε ▸ one_ne_zero)
      D.gammaConst_ne_zero
  simp only [toFun_selbergGammaFactor, map_mul, hω]
  exact ⟨fun h ↦ mul_left_cancel₀ hne (by linear_combination h),
    fun h ↦ by linear_combination D.selbergGammaFactor.ε / D.gammaConst * h⟩

/-- **The axioms of the Selberg class allow more gamma factors than the LMFDB's functional
equation** (LMFDB `lfunction.functional_equation`): the gamma factor `Γ(s / 3)` of Selberg's form
is not `c N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` for any Selberg data `(N, μ, ν, ε)` and any
constant `c`, not even on the half-plane `re s > 0`, where both sides are holomorphic. The proof
uses only the spacing of the poles, not the LMFDB's restrictions on `N`, `μⱼ` and `νₖ`. -/
lemma not_eqOn_gammaDivThree (c : ℂ) : ¬EqOn SelbergGammaFactor.gammaDivThree.toFun
    (fun s ↦ c * ((D.conductor : ℂ) ^ (s / 2) * D.gammaFactor s)) {s | 0 < s.re} := by
  intro h
  have hN : (D.conductor : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr D.conductor_pos.ne'
  have hf : Differentiable ℂ fun z : ℂ ↦ (Gamma (z / 3))⁻¹ :=
    differentiable_one_div_Gamma.comp (differentiable_id.div_const 3)
  have hg :
      Differentiable ℂ fun z : ℂ ↦ c⁻¹ * (((D.conductor : ℂ) ^ (z / 2))⁻¹ * (D.gammaFactor z)⁻¹) :=
    (differentiable_const _).mul ((((differentiable_id.div_const 2).const_cpow (.inl hN)).inv
      fun z ↦ by simp [hN]).mul D.differentiable_inv_gammaFactor)
  have heq : (fun z : ℂ ↦ (Gamma (z / 3))⁻¹) =
      fun z ↦ c⁻¹ * (((D.conductor : ℂ) ^ (z / 2))⁻¹ * (D.gammaFactor z)⁻¹) := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (fun z _ ↦ hf.analyticAt z) (fun z _ ↦ hg.analyticAt z)
      (z₀ := 1) ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by simp : (1 : ℂ) ∈ {z : ℂ | 0 < z.re})] with z hz
    rw [← SelbergGammaFactor.toFun_gammaDivThree, h hz, mul_inv, mul_inv]
  have hc : c ≠ 0 := by
    rintro rfl
    simpa using congrFun heq 3
  have hzero (z : ℂ) : Gamma (z / 3) = 0 ↔ D.gammaFactor z = 0 := by
    rw [← inv_eq_zero, congrFun heq z]
    simp [hc, hN]
  rcases D.gammaFactor_eq_zero_iff.mp ((hzero 0).mp (by simp)) with ⟨x, hx, n, hn⟩ | ⟨x, hx, n, hn⟩
  · rcases (Gamma_eq_zero_iff _).mp <| (hzero (-2)).mpr <| D.gammaFactor_eq_zero_iff.mpr <|
      .inl ⟨x, hx, n + 1, by push_cast; linear_combination hn⟩ with ⟨m, hm⟩
    have hm₃ : 3 * m = 2 :=
      mod_cast (by linear_combination 3 * hm : (3 * m : ℂ) = 2)
    omega
  · rcases (Gamma_eq_zero_iff _).mp <| (hzero (-1)).mpr <| D.gammaFactor_eq_zero_iff.mpr <|
      .inr ⟨x, hx, n + 1, by push_cast; linear_combination hn⟩ with ⟨m, hm⟩
    have hm₃ : 3 * m = 1 :=
      mod_cast (by linear_combination 3 * hm : (3 * m : ℂ) = 1)
    omega

end AnalyticLFunction.SelbergData

namespace AnalyticLFunction

/-- **Every analytic L-function satisfies Selberg's functional equation axiom** (LMFDB
`lfunction.functional_equation`, `lfunction.selberg_class.axioms`): its functional equation
`Λ(s) = ε conj (Λ (1 - conj s))`, with `Λ(s) = N ^ (s / 2) L_∞(s) L(s)`, is one of Selberg's form,
with the gamma factor `AnalyticLFunction.SelbergData.selbergGammaFactor` of its Selberg data. -/
lemma selbergFunctionalEquation_coeff (L : AnalyticLFunction) :
    SelbergFunctionalEquation L.coeff := by
  refine ⟨L.toFun, L.differentiableOn_toFun, fun _ ↦ L.toFun_eq_LSeries,
    L.selbergData.selbergGammaFactor, fun s hs₀ hs₁ ↦
    (L.selbergData.toFun_selbergGammaFactor_mul_eq_conj_iff L.norm_sign).mpr ?_⟩
  have h (z : ℂ) (hz₀ : 0 < z.re) (hz₁ : z.re < 1) :
      (L.conductor : ℂ) ^ (z / 2) * L.selbergData.gammaFactor z * L.toFun z = L.completed z :=
    (L.completed_eq_of_notMem_gammaPoles (L.selbergData.notMem_gammaPoles_of_re_pos hz₀)
      (ne_zero_of_re_pos hz₀) (ne_of_apply_ne re hz₁.ne)).symm
  exact (h s hs₀ hs₁).trans <| (L.completed_eq_sign_mul_conj (ne_zero_of_re_pos hs₀)
    (ne_of_apply_ne re hs₁.ne)).trans <| congrArg (L.sign * conj ·)
      (h _ (by simpa using hs₁) (by simpa using hs₀)).symm

end AnalyticLFunction
