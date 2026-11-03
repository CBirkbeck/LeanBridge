import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.BaseChangeAutomorphism
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.Hecke
import Mathlib.RingTheory.RamificationInertia.Inertia
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Base change of automorphic forms on `GL(2)` between number fields

Let `K ⊇ F` be a finite extension of number fields, `f` a Hecke eigenform on `GL(2)` over `F` of
level `𝔑` and `g` a Hecke eigenform on `GL(2)` over `K`. Then `g` is a **base change** of `f` (LMFDB
`mf.base_change`) if `L_𝔮(g, T) = L_𝔭^{(r)}(f, T)` for all but finitely many primes `𝔮` of `K`,
where `𝔮` lies over `𝔭 ∤ 𝔑` and `r` is the residue degree of `𝔮` over `𝔭`; this is
`NumberField.IsBaseChangeOfEulerFactors` for the Euler factors of `AdelicGL2.eulerFactor`. The
relation does not depend on the normalisation of the Euler factors: it is the same for the
arithmetic normalisation of any motivic weight (`AdelicGL2.isBaseChangeOf_arithmetic_iff`). A form
`g` over `K` **is a base change** if it is the base change of a Hecke eigenform over a proper
subfield of `K`.

If `g` is a base change from `F`, then `a_{σ(𝔮)}(g) = a_𝔮(g)` at almost all primes `𝔮` of `K`, for
every automorphism `σ` of `𝒪_K` over `𝒪_F`, in particular for all `σ ∈ Aut(K)` if `F = ℚ`. For
every prime this needs strong multiplicity one, which is not proved here.

## Main definitions

* `AdelicGL2.IsBaseChangeOf` (LMFDB `mf.base_change`): `g` is a base change of `f`.
* `AdelicGL2.IsBaseChange` (LMFDB `mf.base_change`): `g` is a base change from a proper subfield.

## Main results

* `AdelicGL2.isBaseChangeOf_arithmetic_iff`: the base change relation in the arithmetic
  normalisation of any weight is the same as in the analytic one.
* `AdelicGL2.IsBaseChangeOf.eventually_heckeEigenvalue_smul_eq` (LMFDB `mf.base_change`): the
  Hecke eigenvalues of a base change from `F` are invariant under the automorphisms over `F`, at
  almost all primes.
* `AdelicGL2.IsBaseChangeOf.eventually_heckeEigenvalue_aut_smul_eq` (LMFDB `mf.base_change`): the
  last sentence of the knowl, at almost all primes: the Hecke eigenvalues of a base change from `ℚ`
  are invariant under `Aut(K)`.
-/

open Filter IsDedekindDomain HeightOneSpectrum Matrix NumberField Polynomial TauCeti
  GlobalNumberFields

open scoped AdeleRing MatrixGroups Classical Pointwise

namespace Polynomial

variable (c : ℂ)

private lemma comp_mul (α β : ℂ) :
    ((1 - C α * X) * (1 - C β * X) : ℂ[X]).comp (C c * X) =
      (1 - C (α * c) * X) * (1 - C (β * c) * X) := by
  simp only [mul_comp, sub_comp, one_comp, C_comp, X_comp, C_mul]
  ring1

lemma rootPowers_comp (hc : c ≠ 0) {a b : ℂ} (hb : b ≠ 0) (r : ℕ) :
    ((1 - C a * X + C b * X ^ 2 : ℂ[X]).comp (C c * X)).rootPowers r =
      ((1 - C a * X + C b * X ^ 2 : ℂ[X]).rootPowers r).comp (C (c ^ r) * X) := by
  rcases exists_eq_mul_of_quadratic a b hb with ⟨α, β, hα, hβ, he⟩
  rw [he, comp_mul, rootPowers_mul _ _ (mul_ne_zero hα hc) (mul_ne_zero hβ hc),
    rootPowers_mul _ _ hα hβ, comp_mul, mul_pow, mul_pow]

variable {c} in
private lemma comp_C_mul_X_injective (hc : c ≠ 0) :
    Function.Injective fun p : ℂ[X] ↦ p.comp (C c * X) := by
  intro p q h
  have h₂ : (p.comp (C c * X)).comp (C c⁻¹ * X) = (q.comp (C c * X)).comp (C c⁻¹ * X) :=
    congrArg (fun r : ℂ[X] ↦ r.comp (C c⁻¹ * X)) h
  simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1,
    one_mul, comp_X] at h₂
  exact h₂

end Polynomial

namespace AdelicGL2

variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]

/-- A modular form `g` on `GL(2)` over `K` is a **base change** of the modular form `f` on `GL(2)`
over `F ⊆ K` of level `𝔑` (LMFDB `mf.base_change`), with central characters `ω_f` and `ω_g`:
`L_𝔮(g, T) = L_𝔭^{(r)}(f, T)` for all but finitely many primes `𝔮` of `K`, where `𝔮` lies over
`𝔭 ∤ 𝔑` and `r` is the residue degree of `𝔮` over `𝔭`. The Euler factors are those of
`AdelicGL2.eulerFactor`, which are meaningful when `f` and `g` are Hecke eigenforms. -/
def IsBaseChangeOf (𝔑 : Ideal (𝓞 F)) (ω_f : HeckeCharacter F) (f : AdelicGL2 F → ℂ)
    (ω_g : HeckeCharacter K) (g : AdelicGL2 K → ℂ) : Prop :=
  IsBaseChangeOfEulerFactors 𝔑 (eulerFactorOfIdeal ω_f f) (eulerFactorOfIdeal ω_g g)

/-- A modular form `g` on `GL(2)` over `K` **is a base change** (LMFDB `mf.base_change`): it is the
base change of a Hecke eigenform on `GL(2)` over a proper subfield `K₀ ⊊ K`. -/
def IsBaseChange (ω : HeckeCharacter K) (g : AdelicGL2 K → ℂ) : Prop :=
  ∃ K₀ : Subfield K, K₀ ≠ ⊤ ∧ ∃ (𝔑₀ : Ideal (𝓞 K₀)) (ω₀ : HeckeCharacter K₀)
    (g₀ : AdelicGL2 K₀ → ℂ), IsHeckeEigenform ω₀ 𝔑₀ g₀ ∧ IsBaseChangeOf 𝔑₀ ω₀ g₀ ω g

variable {𝔑 : Ideal (𝓞 F)} {ω_f : HeckeCharacter F} {f : AdelicGL2 F → ℂ} {ω_g : HeckeCharacter K}
  {g : AdelicGL2 K → ℂ}

lemma eulerFactorOfIdeal_eq (ω : HeckeCharacter F) (φ : AdelicGL2 F → ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : eulerFactorOfIdeal ω φ v.asIdeal = eulerFactor v ω φ := by
  simp [eulerFactorOfIdeal, v.isPrime, v.ne_bot]

lemma arithmeticEulerFactorOfIdeal_eq (ω : HeckeCharacter F) (φ : AdelicGL2 F → ℂ) (w : ℤ)
    (v : HeightOneSpectrum (𝓞 F)) :
    arithmeticEulerFactorOfIdeal ω φ w v.asIdeal = arithmeticEulerFactor v ω φ w := by
  simp [arithmeticEulerFactorOfIdeal, v.isPrime, v.ne_bot]

variable (F) in
lemma absNorm_eq_pow (v : HeightOneSpectrum (𝓞 K)) : Ideal.absNorm v.asIdeal =
    Ideal.absNorm (v.under (𝓞 F)).asIdeal ^ v.asIdeal.inertiaDeg (𝓞 F) := by
  have hl : v.asIdeal.LiesOver (v.under (𝓞 F)).asIdeal := ⟨rfl⟩
  exact (Ideal.absNorm_pow_inertiaDeg (v.under (𝓞 F)).asIdeal v.asIdeal).symm

lemma sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) : ∀ r : ℕ, Real.sqrt (x ^ r) = Real.sqrt x ^ r
  | 0 => by simp
  | r + 1 => by rw [pow_succ, Real.sqrt_mul (pow_nonneg hx r), sqrt_pow_eq hx r, pow_succ]

private lemma eulerFactor_comp_rootPowers (v : HeightOneSpectrum (𝓞 F)) (ω : HeckeCharacter F)
    (φ : AdelicGL2 F → ℂ) {c : ℂ} (hc : c ≠ 0) (r : ℕ) :
    ((eulerFactor v ω φ).comp (C c * X)).rootPowers r =
      ((eulerFactor v ω φ).rootPowers r).comp (C (c ^ r) * X) :=
  rootPowers_comp c hc (characterAt v ω).ne_zero r

/-- **The base change relation does not depend on the normalisation of the Euler factors**: it is
the same for the arithmetic normalisation of any motivic weight `w`, as for the analytic one. -/
lemma isBaseChangeOf_arithmetic_iff (w : ℤ) :
    IsBaseChangeOfEulerFactors 𝔑 (arithmeticEulerFactorOfIdeal ω_f f w)
      (arithmeticEulerFactorOfIdeal ω_g g w) ↔ IsBaseChangeOf 𝔑 ω_f f ω_g g := by
  refine eventually_congr (Eventually.of_forall fun 𝔮 ↦ ?_)
  refine imp_congr_right fun h𝔮 ↦ imp_congr_right fun h𝔮₀ ↦ imp_congr_right fun _ ↦ ?_
  let v : HeightOneSpectrum (𝓞 K) := ⟨𝔮, h𝔮, h𝔮₀⟩
  have hc : ((Real.sqrt (Ideal.absNorm (v.under (𝓞 F)).asIdeal) ^ w : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact zpow_ne_zero _ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (v.under (𝓞 F)).ne_bot))))
  have hcv : ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ w : ℝ) : ℂ) =
      ((Real.sqrt (Ideal.absNorm (v.under (𝓞 F)).asIdeal) ^ w : ℝ) : ℂ) ^
        v.asIdeal.inertiaDeg (𝓞 F) := by
    rw [absNorm_eq_pow F v, ← Complex.ofReal_pow, Nat.cast_pow, sqrt_pow_eq (by positivity),
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hu : 𝔮.comap (algebraMap (𝓞 F) (𝓞 K)) = (v.under (𝓞 F)).asIdeal := rfl
  have hv : 𝔮 = v.asIdeal := rfl
  rw [hu, hv, arithmeticEulerFactorOfIdeal_eq, arithmeticEulerFactorOfIdeal_eq,
    eulerFactorOfIdeal_eq, eulerFactorOfIdeal_eq, arithmeticEulerFactor, arithmeticEulerFactor,
    eulerFactor_comp_rootPowers _ _ _ hc, hcv]
  exact (comp_C_mul_X_injective (pow_ne_zero _ hc)).eq_iff

variable {G : Type*} [Group G] [MulSemiringAction G (𝓞 K)]

private lemma absNorm_smul (σ : G) (𝔮 : Ideal (𝓞 K)) : Ideal.absNorm (σ • 𝔮) = Ideal.absNorm 𝔮 := by
  rw [Ideal.pointwise_smul_eq_comap]
  exact Ideal.absNorm_comap_of_ringEquiv _ _

/-- **The Hecke eigenvalues of a base change are invariant under the automorphisms of the field**
(LMFDB `mf.base_change`): if `g` is a base change of `f`, then `a_{σ(𝔮)}(g) = a_𝔮(g)` for almost
all primes `𝔮` of `K` and every automorphism `σ` of `𝒪_K` over `𝒪_F`, given by the action of a
group `G` such as `Aut(K / F)`. For `F = ℚ`, these are all the automorphisms of `K`. The knowl
states this at every prime, which follows by strong multiplicity one, not proved here. -/
lemma IsBaseChangeOf.eventually_heckeEigenvalue_smul_eq [SMulCommClass G (𝓞 F) (𝓞 K)]
    (h : IsBaseChangeOf 𝔑 ω_f f ω_g g) (σ : G) : ∀ᶠ 𝔮 in cofinite,
      ∀ v v' : HeightOneSpectrum (𝓞 K), v.asIdeal = 𝔮 → v'.asIdeal = σ • 𝔮 →
        ¬𝔑 ≤ 𝔮.comap (algebraMap (𝓞 F) (𝓞 K)) → heckeEigenvalue v' g = heckeEigenvalue v g := by
  filter_upwards [IsBaseChangeOfEulerFactors.eventually_smul_eq h σ] with 𝔮 h𝔮 v v' hv hv' h𝔑
  subst hv
  have he : eulerFactorOfIdeal ω_g g (σ • v.asIdeal) = eulerFactorOfIdeal ω_g g v.asIdeal :=
    h𝔮 v.isPrime v.ne_bot h𝔑
  rw [← hv', eulerFactorOfIdeal_eq, eulerFactorOfIdeal_eq] at he
  have hN : Ideal.absNorm v'.asIdeal = Ideal.absNorm v.asIdeal := by
    rw [hv', absNorm_smul]
  have hc : (eulerFactor v' ω_g g).coeff 1 = (eulerFactor v ω_g g).coeff 1 :=
    congrArg (fun p : ℂ[X] ↦ p.coeff 1) he
  simp only [eulerFactor, hN, coeff_add, coeff_sub, coeff_one, coeff_C_mul, coeff_X_one,
    coeff_X_pow, OfNat.one_ne_ofNat, ite_false, mul_zero, add_zero, zero_sub, neg_inj, mul_one,
    one_ne_zero] at hc
  have hs : (((Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))))
  exact mul_left_cancel₀ hs hc

/-- **The Hecke eigenvalues of a base change from `ℚ` are invariant under `Aut(K)`** (LMFDB
`mf.base_change`, its last sentence, at almost all primes): if `g` over `K` is a base change of `f`
over `ℚ`, then `a_{σ(𝔮)}(g) = a_𝔮(g)` for every `σ ∈ Aut(K)` and almost all primes `𝔮` of `K`. The
knowl states it at every prime, which needs strong multiplicity one, not proved here. -/
lemma IsBaseChangeOf.eventually_heckeEigenvalue_aut_smul_eq {N : Ideal (𝓞 ℚ)}
    {ω₀ : HeckeCharacter ℚ} {f₀ : AdelicGL2 ℚ → ℂ} (h : IsBaseChangeOf N ω₀ f₀ ω_g g)
    (σ : K ≃ₐ[ℚ] K) : ∀ᶠ 𝔮 in cofinite,
      ∀ v v' : HeightOneSpectrum (𝓞 K), v.asIdeal = 𝔮 → v'.asIdeal = σ • 𝔮 →
        ¬N ≤ 𝔮.comap (algebraMap (𝓞 ℚ) (𝓞 K)) → heckeEigenvalue v' g = heckeEigenvalue v g :=
  h.eventually_heckeEigenvalue_smul_eq σ

end AdelicGL2
