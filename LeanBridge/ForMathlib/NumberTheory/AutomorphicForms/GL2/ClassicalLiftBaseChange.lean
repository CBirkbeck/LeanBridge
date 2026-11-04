import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.BaseChange
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.ClassicalLiftHecke
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.BaseChange

/-!
# Base change of the adelic lift of a classical newform

Let `f` be a newform of level `N`, weight `k` and nebentypus `χ`, and `φ_f` its adelic lift, a Hecke
eigenform on `GL₂(𝔸_ℚ)` (`AdelicGL2.isHeckeEigenform_adelicLift`). A modular form `g` on `GL(2)`
over a number field `K` is a base change of `φ_f` (`AdelicGL2.IsBaseChangeOf`, LMFDB
`mf.base_change`) if `L_𝔮(g, T) = L_p^{(r)}(φ_f, T)` at almost all primes `𝔮` of `K`, where `𝔮` lies
over `p ∤ N` with residue degree `r`. In the arithmetic normalisation of weight `k - 1` the Euler
factor `L_p(φ_f, T)` is the LMFDB's `1 - a_p T + χ(p) p ^ (k - 1) T²`
(`AdelicGL2.arithmeticEulerFactor_adelicLift`), and the relation does not depend on the
normalisation (`AdelicGL2.isBaseChangeOf_arithmetic_iff`). So `g` is a base change of `φ_f` exactly
when its Euler factor at almost every `𝔮` is `1 - s_r T + (χ(p) p ^ (k - 1)) ^ r T²`, where
`s_r = α_p ^ r + β_p ^ r` is the power sum of the roots of `T² - a_p T + χ(p) p ^ (k - 1)`
(`HeckeRing.GL2.Newform.frobeniusPowerSum`, `HeckeRing.GL2.Newform.rootPowers_eulerFactor`).

## Main results

* `AdelicGL2.isBaseChangeOf_adelicLift_iff` (LMFDB `mf.base_change`): `g` is a base change of the
  adelic lift of `f` exactly when its Euler factors are `1 - s_r T + (χ(p) p ^ (k - 1)) ^ r T²` at
  almost all primes.
-/

open Filter IsDedekindDomain HeightOneSpectrum NumberField Polynomial TauCeti GlobalNumberFields
  HeckeRing GL2

open scoped AdeleRing Classical

namespace AdelicGL2

variable {N : ℕ} [NeZero N] {k : ℤ} {K : Type*} [Field K] [NumberField K] {ω : HeckeCharacter K}
  {g : AdelicGL2 K → ℂ} (f : Newform N k)

lemma dirichletLift_mul_zpow_ne_zero {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) : f.dirichletLift (Ideal.absNorm v.asIdeal) *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (k - 1) ≠ 0 := by
  rw [f.dirichletLift_apply_of_coprime (coprime_absNorm_of_not_le hv)]
  exact mul_ne_zero (Units.ne_zero _)
    (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (prime_absNorm_asIdeal v).ne_zero))

/-- **The base changes of the adelic lift of a newform** (LMFDB `mf.base_change`): a modular form
`g` on `GL(2)` over `K` is a base change of the adelic lift of the newform `f` exactly when, at
almost all primes `𝔮` of `K`, above a prime `p ∤ N` with residue degree `r`, its Euler factor in the
arithmetic normalisation of weight `k - 1` is `1 - s_r T + (χ(p) p ^ (k - 1)) ^ r T²`, with `s_r`
the power sum `α_p ^ r + β_p ^ r` of the roots of `T² - a_p T + χ(p) p ^ (k - 1)`. -/
lemma isBaseChangeOf_adelicLift_iff : IsBaseChangeOf (Ideal.span {(N : 𝓞 ℚ)})
    (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) f.dirichletLift)
      (adelicLift N k f.toCuspForm) ω g ↔
    ∀ᶠ 𝔮 in cofinite, ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal = 𝔮 →
      ¬Ideal.span {(N : 𝓞 ℚ)} ≤ (v.under (𝓞 ℚ)).asIdeal →
        arithmeticEulerFactor v ω g (k - 1) = 1 -
          C (f.frobeniusPowerSum (Ideal.absNorm (v.under (𝓞 ℚ)).asIdeal) (𝔮.inertiaDeg (𝓞 ℚ))) *
            X + C ((f.dirichletLift (Ideal.absNorm (v.under (𝓞 ℚ)).asIdeal) *
              ((Ideal.absNorm (v.under (𝓞 ℚ)).asIdeal : ℕ) : ℂ) ^ (k - 1)) ^
                𝔮.inertiaDeg (𝓞 ℚ)) * X ^ 2 := by
  rw [← isBaseChangeOf_arithmetic_iff (k - 1)]
  refine eventually_congr (Eventually.of_forall fun 𝔮 ↦ ⟨fun h v hv hN ↦ ?_, fun h h𝔮 h𝔮₀ hN ↦ ?_⟩)
  · subst hv
    rw [← arithmeticEulerFactorOfIdeal_eq, h v.isPrime v.ne_bot hN]
    have hu : v.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) = (v.under (𝓞 ℚ)).asIdeal := rfl
    rw [hu, arithmeticEulerFactorOfIdeal_eq, arithmeticEulerFactor_adelicLift f hN,
      f.rootPowers_eulerFactor _ (dirichletLift_mul_zpow_ne_zero f hN)]
  · let v : HeightOneSpectrum (𝓞 K) := ⟨𝔮, h𝔮, h𝔮₀⟩
    have hu : 𝔮.comap (algebraMap (𝓞 ℚ) (𝓞 K)) = (v.under (𝓞 ℚ)).asIdeal := rfl
    have hv : 𝔮 = v.asIdeal := rfl
    rw [hu] at hN ⊢
    rw [hv, arithmeticEulerFactorOfIdeal_eq, arithmeticEulerFactorOfIdeal_eq,
      arithmeticEulerFactor_adelicLift f hN, f.rootPowers_eulerFactor _
        (dirichletLift_mul_zpow_ne_zero f hN)]
    exact h v rfl hN

end AdelicGL2
