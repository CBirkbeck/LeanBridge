import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraLiftLaw
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ThetaDiscriminant
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# The Shimura correspondence

Let `k = 2 l + 1 ≥ 3` be odd, `N` divisible by `4`, `χ` a Dirichlet character modulo `N` and `t ≥ 1`
square-free. The Shimura correspondence (LMFDB `cmf.shimura_correspondence`) is the linear map
`Sh_t : S_{k/2}(N, χ) → M_{k-1}(N / 2, χ²)`, with `Sh_t(g) = ∑ A(n) qⁿ` where `A` is the sequence
`∑_{d ∣ n} χ_t(d) d ^ (l - 1) a(t (n / d)²)` of `ModularForm.shimuraCoeff`, for `g = ∑ a(n) qⁿ`,
that is, `L(s, Sh_t(g)) = L(χ_t, s + 1 - l) ∑ a(t n²) n ^ (-s)`. It is Hecke linear, and it takes
cusp forms to cusp forms for `k ≥ 5`.

The proof is the theta kernel of Niwa, who assumes `k ≥ 7`, and Cipra, who reaches the weights `5/2`
and `3/2`, with a direct unfolding valid for every `k ≥ 3`, without Eisenstein series or a converse
theorem, and it reaches every `g` and the exact level `N / 2`, which Shimura's original argument
does not. For `k ≥ 5` the bound `|A(n)| ≪ n ^ (l + 1/2)` gives the vanishing at the cusps, again
with no Eisenstein series.

The knowl takes `k` odd, with target `S_{k-1}(N / 2, χ²)`. Following Shimura, here `k ≥ 3`: for
`k < 0` the space is zero (`ModularForm.eq_zero_of_mem_halfIntegralWeightCuspSpace_of_neg`), and
`k = 1`, which would need `S_{1/2}(N, χ) = 0`, the cuspidal case of the theorem of Serre and Stark,
is not treated. For `k = 3` the target is `M_2(N / 2, χ²)`, since the lift need not be a cusp form.
The Hecke linearity is stated for `g, g' ∈ S_{k/2}(N, χ)` with `g' = T_{p²} g` on `q`-expansions:
Shimura's Hecke operator `T_{p²}` on `S_{k/2}(N, χ)` itself is not defined here.

## Main definitions

* `ModularForm.shimuraLift` (LMFDB `cmf.shimura_correspondence`): the linear map `Sh_t`.
* `ModularForm.shimuraCorrespondence` (LMFDB `cmf.shimura_correspondence`): `Sh_t` as a linear map
  into `M_{k-1}(N / 2, χ²)`.
* `ModularForm.shimuraLiftCusp` (LMFDB `cmf.shimura_correspondence`): for `k ≥ 5`, the linear map
  `Sh_t` into cusp forms.
* `ModularForm.shimuraCorrespondenceCusp` (LMFDB `cmf.shimura_correspondence`): for `k ≥ 5`, `Sh_t`
  as a linear map into `S_{k-1}(N / 2, χ²)`.

## Main results

* `ModularForm.shimuraLiftFun_slash`: the law of `Sh_t(g)` on `Γ₀(N / 2)`.
* `ModularForm.coeff_qExpansion_shimuraLift`: the `q`-expansion of `Sh_t(g)`.
* `ModularForm.isShimuraLift_shimuraLift`: `Sh_t(g)` is a Shimura lift of `g`.
* `ModularForm.shimuraLift_mem_modFormCharSpace`: `Sh_t(g)` has character `χ²`.
* `ModularForm.shimuraLift_eq_heckeTNat`: **the Hecke linearity of `Sh_t`**.
* `ModularForm.isZeroAtImInfty_shimuraLiftFun_slash`: for `k ≥ 5`, `Sh_t(g)` vanishes at the cusps.
* `ModularForm.shimuraLiftCusp_mem_cuspFormCharSpace`: for `k ≥ 5`, `Sh_t(g)` lies in
  `S_{k-1}(N / 2, χ²)`.
* `ModularForm.LSeries_shimuraLift`: the identity of `L`-series that defines `Sh_t`.
* `ModularForm.exists_shimuraLift_ne_zero`: the lifts `Sh_t(g)` of a nonzero `g` do not all vanish.
* `ModularForm.exists_shimuraLift_thetaSeries_mul_discriminant_ne_zero`: some `Sh_t(θ Δ)` is not
  zero, so the correspondence is not zero.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. 97 (1973), 440–481.
* S. Niwa, *Modular forms of half integral weight and the integral of certain theta-functions*,
  Nagoya Math. J. 56 (1975), 147–161.
* B. Cipra, *On the Niwa-Shintani theta-kernel lifting of modular forms*, Nagoya Math. J. 91 (1983),
  49–117.
-/

open Complex CongruenceSubgroup Matrix SpecialLinearGroup HeckeRing GL2

open scoped Real MatrixGroups Manifold ModularForm NumberTheorySymbols Nat

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {N : ℕ} {l t : ℕ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}

variable [NeZero N] in
lemma neZero_div_two (h4 : 4 ∣ N) : NeZero (N / 2) := by
  have h : N ≠ 0 := NeZero.ne N
  exact ⟨by omega⟩

variable (l t χ f) in
/-- The function `F_t = ∑ Sh_t(a)(n) e(n w)` of the **Shimura lift** (LMFDB
`cmf.shimura_correspondence`) of `f = ∑ a(n) qⁿ`, of weight `(2 l + 1) / 2` and character `χ`. -/
noncomputable def shimuraLiftFun : ℍ → ℂ :=
  expSum (shimuraCoeff χ (2 * l + 1) t fun m ↦ (qExpansion 1 f).coeff m)

private lemma coeff_qExpansion_add {g₁ g₂ : ℍ → ℂ} {k : ℤ}
    (h₁ : g₁ ∈ halfIntegralWeightCuspSpace χ k) (h₂ : g₂ ∈ halfIntegralWeightCuspSpace χ k)
    (m : ℕ) :
    (qExpansion 1 (g₁ + g₂)).coeff m = (qExpansion 1 g₁).coeff m + (qExpansion 1 g₂).coeff m := by
  refine coeff_qExpansion_eq_of_hasSum (add_mem h₁ h₂)
    (b := fun m ↦ (qExpansion 1 g₁).coeff m + (qExpansion 1 g₂).coeff m) (fun z ↦ ?_) m
  simpa only [add_mul, Pi.add_apply] using
    (hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace g₁ h₁ z).add
      (hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace g₂ h₂ z)

private lemma coeff_qExpansion_smul {g₁ : ℍ → ℂ} {k : ℤ} (c : ℂ)
    (h₁ : g₁ ∈ halfIntegralWeightCuspSpace χ k) (m : ℕ) :
    (qExpansion 1 (c • g₁)).coeff m = c * (qExpansion 1 g₁).coeff m := by
  refine coeff_qExpansion_eq_of_hasSum (Submodule.smul_mem _ c h₁)
    (b := fun m ↦ c * (qExpansion 1 g₁).coeff m) (fun z ↦ ?_) m
  simpa only [mul_assoc, smul_eq_mul, Pi.smul_apply] using
    (hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace g₁ h₁ z).mul_left c

lemma shimuraCoeff_eq_of_forall_lt {k : ℤ} {m : ℕ} {a : ℕ → ℂ} (hm0 : m ≠ 0)
    (hm : ∀ m' < m, m' ≠ 0 → a (t * m' ^ 2) = 0) : shimuraCoeff χ k t a m = a (t * m ^ 2) := by
  rw [shimuraCoeff_apply, Finset.sum_eq_single 1]
  · simp [shimuraCharacter]
  · intro d hd hd1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    rw [hm (m / d) (Nat.div_lt_self (Nat.pos_of_ne_zero hm0) (by omega))
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm) hd0).ne', mul_zero]
  · exact fun h1 ↦ absurd (Nat.one_mem_divisors.mpr hm0) h1

variable [NeZero N]

/-- **The law of the Shimura lift, as a slash action** (LMFDB `cmf.shimura_correspondence`). -/
lemma shimuraLiftFun_slash (hf : f ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (h4 : 4 ∣ N)
    (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / 2)) :
    shimuraLiftFun l t χ f ∣[2 * (l : ℤ)] γ =
      shimuraLiftCharacter χ h4 ((γ 1 1 : ℤ) : ZMod (N / 2)) • shimuraLiftFun l t χ f := by
  funext z
  have hJ : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := denomZ_ne_zero γ z
  have e : ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-(2 * (l : ℤ))) =
      (((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * l))⁻¹ := by
    rw [zpow_neg ((γ 1 0 : ℂ) * z + γ 1 1)]
    congr 1
  rw [SL_slash_apply, Pi.smul_apply, smul_eq_mul, shimuraLiftFun,
    expSum_shimuraCoeff_smul_of_mem hf h4 hl ht hsq hγ z, ModularGroup.denom_apply, e]
  have hJl : ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * l) ≠ 0 := pow_ne_zero _ hJ
  field_simp

variable (g : halfIntegralWeightCuspSpace χ (2 * l + 1))

variable (χ) in
/-- The **Shimura lift** `Sh_t(g)` (LMFDB `cmf.shimura_correspondence`) of `g ∈ S_{k/2}(N, χ)`,
`k = 2 l + 1 ≥ 3`, `4 ∣ N`, `t ≥ 1` square-free, as a modular form of weight `k - 1` for
`Γ₁(N / 2)`. -/
noncomputable def shimuraLiftForm (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) :
    ModularForm ((Gamma1 (N / 2)).map (mapGL ℝ)) (2 * (l : ℤ)) :=
  haveI : NeZero (N / 2) := neZero_div_two h4
  modularFormOfNebentypus (shimuraLiftCharacter χ h4)
    (mdifferentiable_expSum (hasPolyGrowth_shimuraCoeff g.2 h4 ht)) (by omega)
    (fun _ hγ ↦ shimuraLiftFun_slash g.2 h4 hl ht hsq hγ)
    (hasPolyGrowth_shimuraCoeff g.2 h4 ht).hasModerateGrowth

lemma coe_shimuraLiftForm (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) :
    ⇑(shimuraLiftForm χ g h4 hl ht hsq) = shimuraLiftFun l t χ g :=
  rfl

variable (χ) in
/-- The **Shimura correspondence** `Sh_t : S_{k/2}(N, χ) → M_{k-1}(N / 2, χ²)` (LMFDB
`cmf.shimura_correspondence`), for `k = 2 l + 1 ≥ 3`, `4 ∣ N` and `t ≥ 1` square-free, a linear map:
`L(s, Sh_t(g)) = L(χ_t, s + 1 - l) ∑ a(t n²) n ^ (-s)` for `g = ∑ a(n) qⁿ`. The knowl has target
`S_{k-1}(N / 2, χ²)`, which holds for `k ≥ 5` (`shimuraLiftCusp`); for `k = 3` the lift may be
Eisenstein. -/
noncomputable def shimuraLift (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) :
    halfIntegralWeightCuspSpace χ (2 * l + 1) →ₗ[ℂ]
      ModularForm ((Gamma1 (N / 2)).map (mapGL ℝ)) (2 * (l : ℤ)) where
  toFun g := shimuraLiftForm χ g h4 hl ht hsq
  map_add' g₁ g₂ := by
    refine DFunLike.ext _ _ fun w ↦ ?_
    have hA : (fun m ↦ (qExpansion 1 ((g₁ + g₂ : halfIntegralWeightCuspSpace χ (2 * l + 1)) :
        ℍ → ℂ)).coeff m) = (fun m ↦ (qExpansion 1 (g₁ : ℍ → ℂ)).coeff m) +
          fun m ↦ (qExpansion 1 (g₂ : ℍ → ℂ)).coeff m :=
      funext fun m ↦ coeff_qExpansion_add g₁.2 g₂.2 m
    have h1 : Summable fun n ↦ shimuraCoeff χ (2 * l + 1) t
        (fun m ↦ (qExpansion 1 (g₁ : ℍ → ℂ)).coeff m) n * cexp (2 * π * I * n * w) :=
      (hasPolyGrowth_shimuraCoeff g₁.2 h4 ht).summable_mul_cexp w.im_pos
    have h2 : Summable fun n ↦ shimuraCoeff χ (2 * l + 1) t
        (fun m ↦ (qExpansion 1 (g₂ : ℍ → ℂ)).coeff m) n * cexp (2 * π * I * n * w) :=
      (hasPolyGrowth_shimuraCoeff g₂.2 h4 ht).summable_mul_cexp w.im_pos
    have e : shimuraLiftFun l t χ ↑(g₁ + g₂) w =
        shimuraLiftFun l t χ g₁ w + shimuraLiftFun l t χ g₂ w := by
      simp only [shimuraLiftFun, expSum, hA, shimuraCoeff_add]
      rw [← h1.tsum_add h2]
      refine tsum_congr fun m ↦ ?_
      rw [Pi.add_apply, add_mul]
    exact e
  map_smul' c g₁ := by
    refine DFunLike.ext _ _ fun w ↦ ?_
    have hA : (fun m ↦ (qExpansion 1 ((c • g₁ : halfIntegralWeightCuspSpace χ (2 * l + 1)) :
        ℍ → ℂ)).coeff m) = c • fun m ↦ (qExpansion 1 (g₁ : ℍ → ℂ)).coeff m :=
      funext fun m ↦ coeff_qExpansion_smul c g₁.2 m
    have e : shimuraLiftFun l t χ ((c • g₁ : halfIntegralWeightCuspSpace χ (2 * l + 1)) : ℍ → ℂ) w =
        c * shimuraLiftFun l t χ g₁ w := by
      simp only [shimuraLiftFun, expSum, hA, shimuraCoeff_smul]
      rw [← tsum_mul_left]
      refine tsum_congr fun m ↦ ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact e

lemma coe_shimuraLift (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) :
    ⇑(shimuraLift χ h4 hl ht hsq g) = shimuraLiftFun l t χ g :=
  rfl

/-- **The `q`-expansion of the Shimura lift** (LMFDB `cmf.shimura_correspondence`). -/
lemma coeff_qExpansion_shimuraLift (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t)
    (n : ℕ) : (qExpansion 1 (shimuraLift χ h4 hl ht hsq g)).coeff n =
      shimuraCoeff χ (2 * l + 1) t (fun m ↦ (qExpansion 1 (g : ℍ → ℂ)).coeff m) n := by
  refine (ModularFormClass.qExpansion_coeff_unique one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map (N / 2)) (fun τ ↦ ?_) n).symm
  simp only [qParam_one_pow]
  exact ((hasPolyGrowth_shimuraCoeff g.2 h4 ht).summable_mul_cexp τ.im_pos).hasSum

/-- **The Shimura lift is a Shimura lift** (LMFDB `cmf.shimura_correspondence`): the Fourier
coefficients of `Sh_t(g)` are those of `L(χ_t, s + 1 - l) ∑ a(t n²) n ^ (-s)`. -/
lemma isShimuraLift_shimuraLift (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) :
    IsShimuraLift χ (2 * l + 1) t g (shimuraLift χ h4 hl ht hsq g) :=
  fun n _ ↦ coeff_qExpansion_shimuraLift g h4 hl ht hsq n

/-- **The Shimura lift has character `χ²`** (LMFDB `cmf.shimura_correspondence`): for
`g ∈ S_{k/2}(N, χ)`, `Sh_t(g) ∈ M_{k-1}(N / 2, χ²)`. -/
lemma shimuraLift_mem_modFormCharSpace (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) :
    haveI : NeZero (N / 2) := neZero_div_two h4
    shimuraLift χ h4 hl ht hsq g ∈
      modFormCharSpace (2 * (l : ℤ)) (shimuraLiftCharacter χ h4).toUnitHom :=
  haveI : NeZero (N / 2) := neZero_div_two h4
  modularFormOfNebentypus_mem (mdifferentiable_expSum (hasPolyGrowth_shimuraCoeff g.2 h4 ht))
    (by omega) (fun _ hγ ↦ shimuraLiftFun_slash g.2 h4 hl ht hsq hγ)
    (hasPolyGrowth_shimuraCoeff g.2 h4 ht).hasModerateGrowth

variable (χ) in
/-- The **Shimura correspondence** `Sh_t : S_{k/2}(N, χ) → M_{k-1}(N / 2, χ²)` (LMFDB
`cmf.shimura_correspondence`), for `k = 2 l + 1 ≥ 3`, `4 ∣ N` and `t ≥ 1` square-free: the linear
map `shimuraLift` into Tau Ceti's space `M_{k-1}(N / 2, χ²)` of modular forms of character `χ²`. The
knowl has target `S_{k-1}(N / 2, χ²)`, which holds for `k ≥ 5` (`shimuraCorrespondenceCusp`). -/
noncomputable def shimuraCorrespondence (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t)
    (hsq : Squarefree t) :
    haveI : NeZero (N / 2) := neZero_div_two h4
    halfIntegralWeightCuspSpace χ (2 * l + 1) →ₗ[ℂ]
      modFormCharSpace (2 * (l : ℤ)) (shimuraLiftCharacter χ h4).toUnitHom :=
  haveI : NeZero (N / 2) := neZero_div_two h4
  (shimuraLift χ h4 hl ht hsq).codRestrict _ fun g ↦
    shimuraLift_mem_modFormCharSpace g h4 hl ht hsq

lemma coe_shimuraCorrespondence (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) :
    haveI : NeZero (N / 2) := neZero_div_two h4
    ↑(shimuraCorrespondence χ h4 hl ht hsq g) = shimuraLift χ h4 hl ht hsq g :=
  rfl

variable {g} in
/-- **The Shimura correspondence is Hecke linear** (LMFDB `cmf.shimura_correspondence`): for a prime
`p ∤ N` and `g, g' ∈ S_{k/2}(N, χ)` with `g' = T_{p²} g` on `q`-expansions,
`Sh_t(g') = T_p (Sh_t(g))`, with `T_p` the Hecke operator of weight `k - 1` on `Γ₁(N / 2)`. -/
lemma shimuraLift_eq_heckeTNat (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) {p : ℕ}
    (hp : p.Prime) (hpN : p.Coprime (N / 2)) {g' : halfIntegralWeightCuspSpace χ (2 * l + 1)}
    (hgg' : (fun m ↦ (qExpansion 1 (g' : ℍ → ℂ)).coeff m) =
      halfIntegralHeckeCoeff χ (2 * l + 1) p fun m ↦ (qExpansion 1 (g : ℍ → ℂ)).coeff m) :
    haveI : NeZero (N / 2) := neZero_div_two h4
    haveI : NeZero p := ⟨hp.ne_zero⟩
    shimuraLift χ h4 hl ht hsq g' = heckeTNat (2 * (l : ℤ)) p (shimuraLift χ h4 hl ht hsq g) := by
  have hN2 : NeZero (N / 2) := neZero_div_two h4
  have hpn : NeZero p := ⟨hp.ne_zero⟩
  have ht2 : ¬p ^ 2 ∣ t := fun h ↦ by
    have h2 : p * p ∣ t := by rwa [← sq]
    exact hp.not_isUnit (hsq p h2)
  have e0 : (0 : ℤ) ≤ (2 * (l : ℤ) + 1 - 1) / 2 := by
    omega
  have hmem : shimuraLift χ h4 hl ht hsq g ∈
      modFormCharSpace (2 * (l : ℤ)) (shimuraLiftCharacter χ h4).toUnitHom :=
    shimuraLift_mem_modFormCharSpace g h4 hl ht hsq
  have hchi : (((shimuraLiftCharacter χ h4).toUnitHom (ZMod.unitOfCoprime p hpN) : ℂˣ) : ℂ) =
      χ ((p ^ 2 : ℕ) : ZMod N) := by
    have hu : IsUnit (((p : ℤ)) : ZMod (N / 2)) := by
      have h1 : IsUnit ((p : ℕ) : ZMod (N / 2)) := by
        simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime p hpN).isUnit
      exact_mod_cast h1
    have h2 : shimuraLiftCharacter χ h4 ((p : ℤ) : ZMod (N / 2)) = χ ((p : ℤ) : ZMod N) ^ 2 :=
      shimuraLiftCharacter_intCast χ h4 hu
    rw [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]
    push_cast at h2 ⊢
    rw [h2, map_pow]
  refine (ModularForm.qExpansion_inj one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map _)).1 (PowerSeries.ext fun n ↦ ?_)
  rw [heckeTNat_def,
    qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace _ hp hpN
      _ hmem n]
  simp only [coeff_qExpansion_shimuraLift]
  rw [hgg']
  rcases eq_or_ne n 0 with rfl | hn
  · simp [shimuraCoeff]
  have e1 : (2 * (l : ℤ) + 1 - 2) = 2 * (l : ℤ) - 1 := by
    ring1
  rw [shimuraCoeff_halfIntegralHeckeCoeff hp ht2 e0 hn, hchi, e1]
  split_ifs
  · rw [Nat.cast_pow]
  · rw [mul_zero]

private lemma exists_norm_shimuraLiftFun_le (hf : f ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) (ht : 0 < t) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ,
      ‖shimuraLiftFun l t χ f z‖ ≤ K * z.im ^ (-((l : ℝ) + 1 / 2 + 1 + 1 / 4)) := by
  rcases exists_norm_shimuraCoeff_le hf h4 ht with ⟨K, hK0, hK⟩
  exact exists_norm_expSum_le_rpow hK0 hK (LSeries.convolution_map_zero _ _) (by positivity)
    (by norm_num)

/-- **The Shimura lift vanishes at the cusps for `k ≥ 5`** (LMFDB `cmf.shimura_correspondence`). -/
lemma isZeroAtImInfty_shimuraLiftFun_slash (hf : f ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) (hl : 2 ≤ l) (ht : 0 < t) (hsq : Squarefree t) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (shimuraLiftFun l t χ f ∣[2 * (l : ℤ)] γ) := by
  have hN2 : NeZero (N / 2) := neZero_div_two h4
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  rcases exists_norm_shimuraLiftFun_le hf h4 ht with ⟨K, hK0, hK⟩
  refine isZeroAtImInfty_slash_of_norm_le γ
    (fun _ hγ ↦ shimuraLiftFun_slash hf h4 (by omega) ht hsq hγ) hK0 hK ?_ ?_
  · push_cast
    linarith
  · push_cast
    linarith

variable (χ) in
/-- The **Shimura lift** `Sh_t(g)` (LMFDB `cmf.shimura_correspondence`) of `g ∈ S_{k/2}(N, χ)`,
`k = 2 l + 1 ≥ 5`, `4 ∣ N`, `t ≥ 1` square-free, as a cusp form of weight `k - 1` for
`Γ₁(N / 2)`. -/
noncomputable def shimuraLiftCuspForm (h4 : 4 ∣ N) (hl : 2 ≤ l) (ht : 0 < t) (hsq : Squarefree t) :
    CuspForm ((Gamma1 (N / 2)).map (mapGL ℝ)) (2 * (l : ℤ)) where
  toSlashInvariantForm := (shimuraLift χ h4 (by omega) ht hsq g).toSlashInvariantForm
  holo' := (shimuraLift χ h4 (by omega) ht hsq g).holo'
  zero_at_cusps' {c} hc := by
    have hc' : IsCusp c 𝒮ℒ := hc.mono (by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩)
    exact (OnePoint.isZeroAt_iff_forall_SL2Z hc').mpr fun γ _ ↦
      isZeroAtImInfty_shimuraLiftFun_slash g.2 h4 hl ht hsq γ

variable (χ) in
/-- The **Shimura correspondence** `Sh_t : S_{k/2}(N, χ) → S_{k-1}(N / 2, χ²)` (LMFDB
`cmf.shimura_correspondence`) for `k = 2 l + 1 ≥ 5`, `4 ∣ N` and `t ≥ 1` square-free, a linear
map. -/
noncomputable def shimuraLiftCusp (h4 : 4 ∣ N) (hl : 2 ≤ l) (ht : 0 < t) (hsq : Squarefree t) :
    halfIntegralWeightCuspSpace χ (2 * l + 1) →ₗ[ℂ]
      CuspForm ((Gamma1 (N / 2)).map (mapGL ℝ)) (2 * (l : ℤ)) where
  toFun g := shimuraLiftCuspForm χ g h4 hl ht hsq
  map_add' g₁ g₂ := DFunLike.ext _ _ fun w ↦
    congrArg (fun F : ModularForm ((Gamma1 (N / 2)).map (mapGL ℝ)) (2 * (l : ℤ)) ↦ F w)
      (map_add (shimuraLift χ h4 (by omega) ht hsq) g₁ g₂)
  map_smul' c g₁ := DFunLike.ext _ _ fun w ↦
    congrArg (fun F : ModularForm ((Gamma1 (N / 2)).map (mapGL ℝ)) (2 * (l : ℤ)) ↦ F w)
      (map_smul (shimuraLift χ h4 (by omega) ht hsq) c g₁)

lemma coe_shimuraLiftCusp (h4 : 4 ∣ N) (hl : 2 ≤ l) (ht : 0 < t) (hsq : Squarefree t) :
    ⇑(shimuraLiftCusp χ h4 hl ht hsq g) = shimuraLift χ h4 (by omega) ht hsq g :=
  rfl

/-- **The Shimura lift has character `χ²`, on cusp forms** (LMFDB `cmf.shimura_correspondence`): for
`k ≥ 5` and `g ∈ S_{k/2}(N, χ)`, `Sh_t(g) ∈ S_{k-1}(N / 2, χ²)`. -/
lemma shimuraLiftCusp_mem_cuspFormCharSpace (h4 : 4 ∣ N) (hl : 2 ≤ l) (ht : 0 < t)
    (hsq : Squarefree t) :
    haveI : NeZero (N / 2) := neZero_div_two h4
    shimuraLiftCusp χ h4 hl ht hsq g ∈
      cuspFormCharSpace (2 * (l : ℤ)) (shimuraLiftCharacter χ h4).toUnitHom := by
  have hN2 : NeZero (N / 2) := neZero_div_two h4
  rw [mem_cuspFormCharSpace_iff_nebentypus]
  intro γ
  have h2 : (((shimuraLiftCharacter χ h4).toUnitHom ((Gamma0Map (N / 2)).toHomUnits γ) : ℂˣ) : ℂ) =
      shimuraLiftCharacter χ h4 (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (N / 2)) := by
    simp [Gamma0Map_apply]
  rw [h2]
  exact shimuraLiftFun_slash g.2 h4 (by omega) ht hsq γ.2

variable (χ) in
/-- The **Shimura correspondence** `Sh_t : S_{k/2}(N, χ) → S_{k-1}(N / 2, χ²)` (LMFDB
`cmf.shimura_correspondence`) for `k = 2 l + 1 ≥ 5`, `4 ∣ N` and `t ≥ 1` square-free: the linear map
`shimuraLiftCusp` into Tau Ceti's space `S_{k-1}(N / 2, χ²)` of cusp forms of character `χ²`. -/
noncomputable def shimuraCorrespondenceCusp (h4 : 4 ∣ N) (hl : 2 ≤ l) (ht : 0 < t)
    (hsq : Squarefree t) :
    haveI : NeZero (N / 2) := neZero_div_two h4
    halfIntegralWeightCuspSpace χ (2 * l + 1) →ₗ[ℂ]
      cuspFormCharSpace (2 * (l : ℤ)) (shimuraLiftCharacter χ h4).toUnitHom :=
  haveI : NeZero (N / 2) := neZero_div_two h4
  (shimuraLiftCusp χ h4 hl ht hsq).codRestrict _ fun g ↦
    shimuraLiftCusp_mem_cuspFormCharSpace g h4 hl ht hsq

lemma coe_shimuraCorrespondenceCusp (h4 : 4 ∣ N) (hl : 2 ≤ l) (ht : 0 < t)
    (hsq : Squarefree t) :
    haveI : NeZero (N / 2) := neZero_div_two h4
    ↑(shimuraCorrespondenceCusp χ h4 hl ht hsq g) = shimuraLiftCusp χ h4 hl ht hsq g :=
  rfl

/-- **The `L`-series of the Shimura lift** (LMFDB `cmf.shimura_correspondence`): where both series
on the right converge absolutely, `L(s, Sh_t(g)) = L(χ_t, s + 1 - l) ∑ a(t n²) n ^ (-s)`. -/
lemma LSeries_shimuraLift (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) {s : ℂ}
    (h₁ : LSeriesSummable (shimuraCharacter χ (2 * l + 1) t)
      (s + 1 - ((2 * (l : ℤ) + 1 - 1) / 2 : ℤ)))
    (h₂ : LSeriesSummable (fun m ↦ (qExpansion 1 (g : ℍ → ℂ)).coeff (t * m ^ 2)) s) :
    LSeries (fun n ↦ (qExpansion 1 (shimuraLift χ h4 hl ht hsq g)).coeff n) s =
      LSeries (shimuraCharacter χ (2 * l + 1) t) (s + 1 - ((2 * (l : ℤ) + 1 - 1) / 2 : ℤ)) *
        LSeries (fun m ↦ (qExpansion 1 (g : ℍ → ℂ)).coeff (t * m ^ 2)) s := by
  simp only [coeff_qExpansion_shimuraLift]
  exact LSeries_shimuraCoeff h₁ h₂

variable {g} in
/-- **The Shimura lifts of a nonzero form do not all vanish** (LMFDB `cmf.shimura_correspondence`):
for `g ≠ 0` in `S_{k/2}(N, χ)`, `k = 2 l + 1 ≥ 3`, some square-free `t ≥ 1` has `Sh_t(g) ≠ 0`. Write
`n = t m²` for an `n` with `a(n) ≠ 0`, `t` square-free; for the least such `m`, the coefficient of
`Sh_t(g)` at `m` is `a(t m²)`. -/
lemma exists_shimuraLift_ne_zero (h4 : 4 ∣ N) (hl : l ≠ 0) (hg : g ≠ 0) :
    ∃ (t : ℕ) (ht : 0 < t) (hsq : Squarefree t), shimuraLift χ h4 hl ht hsq g ≠ 0 := by
  have hex : ∃ n, (qExpansion 1 (g : ℍ → ℂ)).coeff n ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    refine hg (Subtype.ext (funext fun z ↦ ?_))
    have h1 : HasSum (fun m : ℕ ↦ (qExpansion 1 (g : ℍ → ℂ)).coeff m * cexp (2 * π * I * m * z))
        ((g : ℍ → ℂ) z) := hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace _ g.2 z
    simp only [h, zero_mul] at h1
    exact h1.unique hasSum_zero
  rcases hex with ⟨n, hn⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (coeff_zero_qExpansion_of_mem_halfIntegralWeightCuspSpace _ g.2)
  rcases Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn0) with ⟨t, m, ht, -, rfl, hsq⟩
  have hb : ∃ m, (qExpansion 1 (g : ℍ → ℂ)).coeff (t * m ^ 2) ≠ 0 := ⟨m, by rwa [mul_comm]⟩
  refine ⟨t, ht, hsq, fun h0 ↦ Nat.find_spec hb ?_⟩
  have hm₀ : Nat.find hb ≠ 0 := fun h ↦ Nat.find_spec hb (by
    rw [h, zero_pow two_ne_zero, mul_zero]
    exact coeff_zero_qExpansion_of_mem_halfIntegralWeightCuspSpace _ g.2)
  have h1 : shimuraCoeff χ (2 * l + 1) t (fun m ↦ (qExpansion 1 ↑g).coeff m) (Nat.find hb) =
      (qExpansion 1 ↑g).coeff (t * Nat.find hb ^ 2) :=
    shimuraCoeff_eq_of_forall_lt hm₀ fun m' hm' _ ↦ not_not.mp (Nat.find_min hb hm')
  rw [← h1, ← coeff_qExpansion_shimuraLift g h4 hl ht hsq, h0]
  simp [qExpansion_zero]

/-- **The Shimura correspondence is not zero** (LMFDB `cmf.shimura_correspondence`): for the cusp
form `θ Δ ∈ S_{25/2}(4, 1)`, some square-free `t ≥ 1` has `Sh_t(θ Δ) ≠ 0` in `M_24(Γ₁(2))`. -/
lemma exists_shimuraLift_thetaSeries_mul_discriminant_ne_zero : ∃ (t : ℕ) (ht : 0 < t)
    (hsq : Squarefree t), shimuraLift (1 : DirichletCharacter ℂ 4) (dvd_refl 4) (by norm_num) ht
      hsq ⟨_, thetaSeries_mul_discriminant_mem_halfIntegralWeightCuspSpace⟩ ≠ 0 :=
  exists_shimuraLift_ne_zero _ _ fun h ↦
    thetaSeries_mul_discriminant_ne_zero (congrArg Subtype.val h)

end ModularForm
