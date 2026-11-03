import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareUnfolding
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraKernelLevel
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraStrip
import TauCeti.NumberTheory.Modular

/-!
# The Petersson product against Niwa's kernel is the Shimura lift

For `g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `l ≥ 1`, `4 ∣ N`, the Petersson product of `g`
against Niwa's kernel `Θ^(l)(·, w)` is `2 (i v² / 2) ^ l / l! ∑ A(n) e(n w)`, with `A = Sh₁(a)` the
sequence of the Shimura lift. The law of the kernel in `w` then gives the law of the Shimura lift on
`Γ₀(N / 2)`.

## Main results

* `ModularForm.halfIntegralPetersson_shimuraTheta`: the Petersson product against the kernel.
* `ModularForm.expSum_shimuraCoeff_smul`: the law of the Shimura lift `Sh₁(g)` on `Γ₀(N / 2)`.
-/

open Complex CongruenceSubgroup MeasureTheory ModularGroup Set

open scoped Real MatrixGroups ComplexConjugate Nat Pointwise

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {l : ℕ} {g : ℍ → ℂ}

/-- **The Petersson product against Niwa's kernel** (LMFDB `cmf.shimura_correspondence`): for
`g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `l ≥ 1`, `4 ∣ N`,
`∫_{Γ₀(N) \ ℍ} g conj(Θ^(l)(·, w)) y^{k/2} dμ = 2 (i v² / 2) ^ l / l! ∑ A(n) e(n w)`, where `A` is
the sequence of the Shimura lift `Sh₁(g)` and `v = Im w`. -/
lemma halfIntegralPetersson_shimuraTheta (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) (hl : l ≠ 0) (w : ℍ) : halfIntegralPetersson N (2 * l + 1) g
      (fun z ↦ shimuraTheta (shimuraThetaCharacter χ l h4) z w l) =
        2 * (expSum (shimuraCoeff χ (2 * l + 1) 1 fun m ↦ (qExpansion 1 g).coeff m) w *
          ((I * (w.im : ℂ) ^ 2 / 2) ^ l / (l ! : ℂ))) := by
  have : Countable PSL(2, ℤ) :=
    inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel (Subgroup.center SL(2, ℤ)))))
  have hT : T ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp
  have hF : IsFundamentalDomain (pslCuspStabilizer (Gamma0 N) (1 : SL(2, ℤ)))
      {z : ℍ | z.re ∈ Ico 0 (1 : ℝ)} := by
    simpa only [one_smul, Nat.cast_one] using isFundamentalDomain_smul_re_mem_Ico_psl
      (G := Gamma0 N) (t := ⟨T, hT⟩) (1 : SL(2, ℤ)) 1 one_pos (fun h _ ↦ by simp) (.inl (by simp))
  rw [halfIntegralPetersson]
  simp_rw [integrand_shimuraTheta_eq_tsum h4 hg.1 w]
  rw [integral_const_mul, ← setIntegral_shimuraSeed w l hg h4 hl]
  congr 1
  refine isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter (Gamma0 N)
    |>.setIntegral_tsum_smul_eq hF (bijective_mk_inv_subgroupMap_out 1) (fun h x ↦ ?_)
      (integrableOn_shimuraSeed _ w l hg h4)
  rcases h with ⟨_, h, hh, rfl⟩
  have hx : (⟨_, h, hh, rfl⟩ : pslCuspStabilizer (Gamma0 N) (1 : SL(2, ℤ))) • x =
      ((h : Gamma0 N) : SL(2, ℤ)) • x :=
    rfl
  have h10 : ((h : Gamma0 N) : SL(2, ℤ)) 1 0 = 0 := by
    simpa using (mem_cuspStabilizer_iff (1 : SL(2, ℤ))).mp hh
  rw [hx]
  exact shimuraSeed_smul_of_apply_one_zero h4 hg.1 w h.2 h10 x

private lemma law_algebra {F F' p A B Q f : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hQ : Q ≠ 0) (hf : f ≠ 0)
    (h : 2 * (F' * (Q / (A * B) / f)) = p ^ 2 * B⁻¹ * (2 * (F * (Q / f)))) :
    F' = p ^ 2 * A * F := by
  field_simp at h
  linear_combination h

/-- **The law of the Shimura lift** (LMFDB `cmf.shimura_correspondence`): for
`g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `l ≥ 1`, `N = 4 M`, and
`γ = (α, β; γ', δ) ∈ SL(2, ℤ)` with `2 M ∣ γ'`, the sum `F = ∑ A(n) e(n w)` of the sequence `A` of
`Sh₁(g)` satisfies `F(γ w) = ψ(δ) ^ 2 (γ' w + δ) ^ (2 l) F(w)`, with `ψ = χ χ₄ ^ l`. -/
lemma expSum_shimuraCoeff_smul (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N)
    (hl : l ≠ 0) {M c : ℤ} (hM : (N : ℤ) = 4 * M) {γ : SL(2, ℤ)} (hc : γ 1 0 = 2 * M * c) (w : ℍ) :
    expSum (shimuraCoeff χ (2 * l + 1) 1 fun m ↦ (qExpansion 1 g).coeff m) (γ • w) =
      shimuraThetaCharacter χ l h4 ((γ 1 1 : ℤ) : ZMod N) ^ 2 *
        ((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l) *
          expSum (shimuraCoeff χ (2 * l + 1) 1 fun m ↦ (qExpansion 1 g).coeff m) w := by
  have hJ : (γ 1 0 : ℂ) * w + γ 1 1 ≠ 0 := by
    simpa only [ModularGroup.denom_apply] using denom_ne_zero γ w
  have hJb : conj ((γ 1 0 : ℂ) * w + γ 1 1) ≠ 0 := (map_ne_zero _).mpr hJ
  have hv : (w.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr w.im_ne_zero
  have him : (((γ • w : ℍ).im : ℝ) : ℂ) = (w.im : ℂ) /
      (((γ 1 0 : ℂ) * w + γ 1 1) * conj ((γ 1 0 : ℂ) * w + γ 1 1)) := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, Complex.mul_conj]
    push_cast
    rfl
  have h3 : halfIntegralPetersson N (2 * l + 1) g
      (fun z ↦ shimuraTheta (shimuraThetaCharacter χ l h4) z (γ • w) l) =
        conj ((shimuraThetaCharacter χ l h4)⁻¹ ((γ 1 1 : ℤ) : ZMod N) ^ 2 *
          (((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l))⁻¹) * halfIntegralPetersson N (2 * l + 1) g
            (fun z ↦ shimuraTheta (shimuraThetaCharacter χ l h4) z w l) := by
    simp only [halfIntegralPetersson, halfIntegralPeterssonIntegrand,
      shimuraTheta_smul_right _ w γ _ hM hc l]
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    simp only [map_mul]
    ring1
  rw [halfIntegralPetersson_shimuraTheta hg h4 hl (γ • w),
    halfIntegralPetersson_shimuraTheta hg h4 hl w, him] at h3
  simp only [map_mul, map_pow, conj_inv_apply, map_inv₀] at h3
  have e1 : (I * ((w.im : ℂ) / (((γ 1 0 : ℂ) * w + γ 1 1) *
      conj ((γ 1 0 : ℂ) * w + γ 1 1))) ^ 2 / 2) ^ l = (I * (w.im : ℂ) ^ 2 / 2) ^ l /
        (((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l) * conj ((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l)) := by
    rw [pow_mul, pow_mul, ← mul_pow, ← mul_pow, ← div_pow]
    congr 1
    field_simp
  rw [e1] at h3
  exact law_algebra (pow_ne_zero _ hJ) (pow_ne_zero _ hJb)
    (pow_ne_zero _ (div_ne_zero (mul_ne_zero I_ne_zero (pow_ne_zero 2 hv)) two_ne_zero))
    (Nat.cast_ne_zero.mpr l.factorial_ne_zero) h3

end ModularForm
