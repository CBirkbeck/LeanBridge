import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.HalfIntegralWeight
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.ExponentialSum
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# Hecke's bound for cusp forms of half-integral weight

Let `g ∈ S_{k/2}(N, χ)`, with `k` odd and `4 ∣ N`. The square of the theta multiplier is
`j(γ, z)² = ε_d⁻² (c z + d)`, so that `g²` is a cusp form of weight `k` for `Γ₁(N)` in Mathlib's
sense. Mathlib's bound for cusp forms then gives Hecke's bound `|g(z)| ≤ K y ^ (-k/4)` on `ℍ`, with
no expansion of `g` at the other cusps. The function `g` is `1`-periodic, holomorphic and vanishes
at `i∞`, so it is the sum of its `q`-expansion, without constant term, and integrating over a
horizontal segment at height `1 / n` gives `|a(n)| ≤ K e^{2π} n ^ (k/4)`.

## Main definitions

* `ModularForm.halfIntegralSquareCuspForm`: the square of a cusp form of half-integral weight, as a
  cusp form of integral weight.

## Main results

* `ModularForm.thetaFactor_sq`: the square of the theta multiplier.
* `ModularForm.exists_norm_mul_rpow_le_of_mem_halfIntegralWeightCuspSpace`: **Hecke's bound** on
  `ℍ`.
* `ModularForm.hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace`: the `q`-expansion.
* `ModularForm.coeff_zero_qExpansion_of_mem_halfIntegralWeightCuspSpace`: there is no constant term.
* `ModularForm.exists_norm_coeff_qExpansion_le`: **Hecke's bound for the coefficients**.
* `ModularForm.eq_zero_of_mem_halfIntegralWeightCuspSpace_of_neg`: there are no cusp forms of
  negative weight.
-/

open Complex CongruenceSubgroup Filter ModularGroup Function Matrix SpecialLinearGroup

open scoped Real MatrixGroups Manifold NumberTheorySymbols ModularForm

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ} {g : ℍ → ℂ} (γ : SL(2, ℤ)) (z : ℍ)

private lemma shimuraSymbol_sq : (shimuraSymbol (γ 1 0) (γ 1 1) : ℂ) ^ 2 = 1 := by
  have hgcd : (γ 1 0).gcd ((γ 1 1).natAbs : ℤ) = 1 := by
    have e : (γ 1 0).gcd ((γ 1 1).natAbs : ℤ) = (γ 1 0).gcd (γ 1 1) := by
      simp [Int.gcd, Int.natAbs_abs]
    rw [e]
    refine Int.isCoprime_iff_gcd_eq_one.mp ⟨-γ 0 1, γ 0 0, ?_⟩
    linear_combination γ.fin_two_mul_sub_mul_eq_one
  have h : (jacobiSym (γ 1 0) (γ 1 1).natAbs) ^ 2 = 1 := jacobiSym.sq_one hgcd
  have h2 : (shimuraSymbol (γ 1 0) (γ 1 1)) ^ 2 = 1 := by
    rw [shimuraSymbol]
    split_ifs
    · rw [neg_sq, h]
    · exact h
  exact_mod_cast h2

/-- **The square of the theta multiplier**: `j(γ, z)² = ε_d⁻² (c z + d)`. -/
lemma thetaFactor_sq : thetaFactor γ z ^ 2 = ((thetaEpsilon (γ 1 1))⁻¹) ^ 2 * denom γ z := by
  rw [thetaFactor, mul_pow, mul_pow, shimuraSymbol_sq, one_mul, ← cpow_nat_mul]
  norm_num

private lemma weightFactor_sq (hk : Odd k) :
    weightFactor k γ z ^ 2 = (((thetaEpsilon (γ 1 1))⁻¹) ^ 2 * denom γ z) ^ k := by
  have hk' : ¬Even k := Int.not_even_iff_odd.mpr hk
  have e : weightFactor k γ z = thetaFactor γ z ^ k := by
    simp [weightFactor, hk']
  rw [e, ← thetaFactor_sq, ← zpow_natCast (thetaFactor γ z ^ k) 2,
    ← zpow_natCast (thetaFactor γ z) 2, ← zpow_mul (thetaFactor γ z) k,
    ← zpow_mul (thetaFactor γ z), mul_comm]

private lemma thetaEpsilon_of_mem_Gamma1 (h4 : 4 ∣ N) (hγ : γ ∈ Gamma1 N) :
    thetaEpsilon (γ 1 1) = 1 := by
  have h1 : ((γ 1 1 : ℤ) : ZMod N) = 1 := ((Gamma1_mem N γ).mp hγ).2.1
  have h2 : ((N : ℕ) : ℤ) ∣ γ 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h1, sub_self]
  have h3 : (4 : ℤ) ∣ γ 1 1 - 1 := (Int.natCast_dvd_natCast.mpr h4).trans h2
  have h5 : γ 1 1 % 4 = 1 := by omega
  simp [thetaEpsilon, h5]

variable [NeZero N] in
/-- The **square** `g²` of a cusp form `g ∈ S_{k/2}(N, χ)` of half-integral weight, `k` odd and
`4 ∣ N`, as a cusp form of weight `k` for `Γ₁(N)`. -/
noncomputable def halfIntegralSquareCuspForm (hg : g ∈ halfIntegralWeightCuspSpace χ k) (hk : Odd k)
    (h4 : 4 ∣ N) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := g * g
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    funext z
    have h1 : ((γ 1 1 : ℤ) : ZMod N) = 1 := ((Gamma1_mem N γ).mp hγ).2.1
    have h0 : γ ∈ Gamma0 N := Gamma0_mem.mpr ((Gamma1_mem N γ).mp hγ).2.2
    have h2 : g (γ • z) = weightFactor k γ z * g z := by
      rw [hg.1.2.1 γ h0 z, h1, map_one, one_mul]
    have h3 : weightFactor k γ z ^ 2 = denom γ z ^ k := by
      rw [weightFactor_sq γ z hk, thetaEpsilon_of_mem_Gamma1 γ h4 hγ, inv_one, one_pow, one_mul]
    have hd : denom γ z ≠ 0 := denom_ne_zero γ z
    have e : ((g * g) ∣[k] mapGL ℝ γ) z = (g * g) (γ • z) * denom γ z ^ (-k) :=
      ModularForm.SL_slash_apply (f := g * g) γ z
    rw [e, Pi.mul_apply, Pi.mul_apply, h2, zpow_neg (denom γ z) k]
    have hdk : denom γ z ^ k ≠ 0 := zpow_ne_zero k hd
    field_simp
    linear_combination (g z) ^ 2 * h3
  holo' := hg.1.1.mul hg.1.1
  zero_at_cusps' {c} hc := by
    have hc' : IsCusp c 𝒮ℒ := hc.mono (by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩)
    refine (OnePoint.isZeroAt_iff_forall_SL2Z hc').mpr fun γ _ ↦ ?_
    have h1 : Tendsto (halfIntegralWeightSlash k γ g) atImInfty (nhds 0) := hg.2 γ
    have hnorm (z : ℍ) : ‖((g * g) ∣[k] γ) z‖ = ‖halfIntegralWeightSlash k γ g z‖ ^ 2 := by
      have hd : 0 < ‖denom γ z‖ := norm_pos_iff.mpr (denom_ne_zero γ z)
      have e : (‖denom γ z‖ ^ (-((k : ℝ) / 2))) ^ 2 = ‖denom γ z‖ ^ (-k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le, ← Real.rpow_intCast]
        congr 1
        push_cast
        ring1
      rw [ModularForm.SL_slash_apply, norm_mul, Pi.mul_apply, norm_mul, norm_zpow,
        halfIntegralWeightSlash, norm_mul, norm_real, Real.norm_of_nonneg (by positivity), mul_pow,
        e]
      ring1
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simp_rw [hnorm]
    simpa using (tendsto_zero_iff_norm_tendsto_zero.mp h1).pow 2

variable [NeZero N] in
/-- **Hecke's bound for cusp forms of half-integral weight**: for `g ∈ S_{k/2}(N, χ)`, `k` odd and
`4 ∣ N`, the function `|g(z)| y ^ (k/4)` is bounded on `ℍ`. -/
lemma exists_norm_mul_rpow_le_of_mem_halfIntegralWeightCuspSpace
    (hg : g ∈ halfIntegralWeightCuspSpace χ k) (hk : Odd k) (h4 : 4 ∣ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, ‖g z‖ * z.im ^ ((k : ℝ) / 4) ≤ K := by
  rcases CuspFormClass.exists_bound (halfIntegralSquareCuspForm hg hk h4) with ⟨C, hC⟩
  refine ⟨Real.sqrt |C|, Real.sqrt_nonneg _, fun z ↦ ?_⟩
  have hy : 0 < z.im := z.im_pos
  have h1 : ‖g z‖ ^ 2 ≤ C / z.im ^ ((k : ℝ) / 2) := by
    have h2 : ‖halfIntegralSquareCuspForm hg hk h4 z‖ ≤ C / z.im ^ ((k : ℝ) / 2) := hC z
    have e : (halfIntegralSquareCuspForm hg hk h4) z = g z * g z := rfl
    rwa [e, norm_mul, ← sq] at h2
  have h3 : (‖g z‖ * z.im ^ ((k : ℝ) / 4)) ^ 2 ≤ |C| := by
    have e : (z.im ^ ((k : ℝ) / 4)) ^ 2 = z.im ^ ((k : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
      congr 1
      push_cast
      ring1
    have hp : 0 < z.im ^ ((k : ℝ) / 2) := by positivity
    rw [mul_pow, e]
    rw [le_div_iff₀ hp] at h1
    exact h1.trans (le_abs_self C)
  exact Real.le_sqrt_of_sq_le h3

variable (k) in
private lemma weightFactor_T : weightFactor k T z = 1 := by
  have hd : denom T z = 1 := by
    rw [ModularGroup.denom_apply]
    simp
  rw [weightFactor]
  split_ifs with hk
  · rw [hd]
    exact one_zpow _
  · have e : thetaFactor T z = 1 := by
      rw [thetaFactor, hd]
      simp [shimuraSymbol, thetaEpsilon]
    rw [e]
    exact one_zpow k

variable (g) in
private lemma periodic_of_mem (hg : g ∈ halfIntegralWeightSpace χ k) (τ : ℍ) :
    g ((1 : ℝ) +ᵥ τ) = g τ := by
  have hT : T ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp
  have h1 : g (T • τ) = χ (T 1 1) * weightFactor k T τ * g τ := hg.2.1 T hT τ
  have h2 : (T • τ : ℍ) = (1 : ℝ) +ᵥ τ := by
    have h3 : ((T ^ (1 : ℤ) • τ : ℍ) : ℂ) = (τ : ℂ) + ((1 : ℤ) : ℂ) :=
      ModularGroup.coe_T_zpow_smul_eq τ
    ext
    simp only [zpow_one] at h3
    rw [h3]
    simp [add_comm]
  have hd : ((T 1 1 : ℤ) : ZMod N) = 1 := by
    simp
  rw [h2, weightFactor_T, hd, map_one, one_mul, one_mul] at h1
  exact h1

private lemma isZeroAtImInfty_of_mem (hg : g ∈ halfIntegralWeightCuspSpace χ k) :
    IsZeroAtImInfty g := by
  have h1 : halfIntegralWeightSlash k 1 g = g := by
    funext z
    have hd : denom (1 : SL(2, ℤ)) z = 1 := by
      rw [ModularGroup.denom_apply]
      simp
    rw [halfIntegralWeightSlash, hd]
    simp
  have h2 : IsZeroAtImInfty (halfIntegralWeightSlash k 1 g) := hg.2 1
  rwa [h1] at h2

variable (g) in
/-- **The `q`-expansion of a cusp form of half-integral weight.** -/
lemma hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace
    (hg : g ∈ halfIntegralWeightCuspSpace χ k) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion 1 g).coeff m * cexp (2 * π * I * m * τ)) (g τ) := by
  have hp : Periodic (g ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex (periodic_of_mem g hg.1)
  simpa only [qParam_one_pow, smul_eq_mul] using UpperHalfPlane.hasSum_qExpansion one_pos hp hg.1.1
    (isZeroAtImInfty_of_mem hg).isBoundedAtImInfty τ

variable (g) in
/-- **A cusp form of half-integral weight has no constant term.** -/
lemma coeff_zero_qExpansion_of_mem_halfIntegralWeightCuspSpace
    (hg : g ∈ halfIntegralWeightCuspSpace χ k) : (qExpansion 1 g).coeff 0 = 0 := by
  have h : Tendsto g atImInfty (nhds ((qExpansion 1 g).coeff 0)) :=
    UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion one_pos fun τ ↦ by
      simpa only [qParam_one_pow, smul_eq_mul] using
        hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace g hg τ
  exact tendsto_nhds_unique h (isZeroAtImInfty_of_mem hg)

private lemma norm_coeff_qExpansion_le (hg : g ∈ halfIntegralWeightCuspSpace χ k) {K : ℝ}
    (hK : ∀ z : ℍ, ‖g z‖ * z.im ^ ((k : ℝ) / 4) ≤ K) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖(qExpansion 1 g).coeff n‖ ≤ K * y ^ (-((k : ℝ) / 4)) * Real.exp (2 * π * n * y) := by
  have hp : Periodic (g ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex (periodic_of_mem g hg.1)
  rw [UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral one_pos hp hg.1.1
    (isZeroAtImInfty_of_mem hg).isBoundedAtImInfty n hy]
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) 1, ‖1 / Periodic.qParam 1 ((u : ℂ) + y * I) ^ n *
      g ⟨(u : ℂ) + y * I, by simpa using hy⟩‖ ≤
        K * y ^ (-((k : ℝ) / 4)) * Real.exp (2 * π * n * y) := by
    intro u _
    have h1 : ‖g ⟨(u : ℂ) + y * I, by simpa using hy⟩‖ *
        (⟨(u : ℂ) + y * I, by simpa using hy⟩ : ℍ).im ^ ((k : ℝ) / 4) ≤ K :=
      hK ⟨(u : ℂ) + y * I, by simpa using hy⟩
    have him : (⟨(u : ℂ) + y * I, by simpa using hy⟩ : ℍ).im = y := by
      simp
    rw [him] at h1
    have h2 : ‖1 / Periodic.qParam 1 ((u : ℂ) + y * I) ^ n‖ = Real.exp (2 * π * n * y) := by
      have e : ((u : ℂ) + y * I).im = y := by
        simp
      have e2 : (n : ℝ) * (-2 * π * y / 1) = -(2 * π * n * y) := by
        ring1
      rw [norm_div, norm_one, norm_pow, Periodic.norm_qParam, ← Real.exp_nat_mul, e, e2,
        Real.exp_neg, one_div, inv_inv]
    have hy3 : 0 < y ^ ((k : ℝ) / 4) := by
      positivity
    have h3 : ‖g ⟨(u : ℂ) + y * I, by simpa using hy⟩‖ ≤ K * y ^ (-((k : ℝ) / 4)) := by
      rw [Real.rpow_neg hy.le, ← div_eq_mul_inv, le_div_iff₀ hy3]
      exact h1
    rw [norm_mul, h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  have h5 : ‖∫ u in (0 : ℝ)..1, 1 / Periodic.qParam 1 ((u : ℂ) + y * I) ^ n *
      g ⟨(u : ℂ) + y * I, by simpa using hy⟩‖ ≤
        K * y ^ (-((k : ℝ) / 4)) * Real.exp (2 * π * n * y) * |(1 : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_one, mul_one] at h5
  rw [ofReal_one, div_one, one_mul]
  exact h5

variable [NeZero N] in
/-- **Hecke's bound for the coefficients**: for `g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k` odd and
`4 ∣ N`, `|a(n)| ≤ K n ^ (k/4)` for `n ≥ 1`. -/
lemma exists_norm_coeff_qExpansion_le (hg : g ∈ halfIntegralWeightCuspSpace χ k) (hk : Odd k)
    (h4 : 4 ∣ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, n ≠ 0 → ‖(qExpansion 1 g).coeff n‖ ≤ K * (n : ℝ) ^ ((k : ℝ) / 4) := by
  rcases exists_norm_mul_rpow_le_of_mem_halfIntegralWeightCuspSpace hg hk h4 with ⟨K, hK0, hK⟩
  refine ⟨K * Real.exp (2 * π), by positivity, fun n hn ↦ ?_⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have e1 : ((n : ℝ)⁻¹) ^ (-((k : ℝ) / 4)) = (n : ℝ) ^ ((k : ℝ) / 4) := by
    rw [Real.inv_rpow hn'.le, Real.rpow_neg hn'.le, inv_inv]
  have e2 : 2 * π * n * (n : ℝ)⁻¹ = 2 * π := by
    field_simp
  refine (norm_coeff_qExpansion_le hg hK n (y := (n : ℝ)⁻¹) (by positivity)).trans_eq ?_
  rw [e1, e2]
  ring1

variable [NeZero N] in
/-- **There are no cusp forms of negative half-integral weight**: for `k < 0` odd and `4 ∣ N`, every
`g ∈ S_{k/2}(N, χ)` vanishes, since Hecke's bound `|a(n)| ≤ K y ^ (-k/4) e^{2 π n y}` tends to `0`
as `y → 0`. -/
lemma eq_zero_of_mem_halfIntegralWeightCuspSpace_of_neg (hg : g ∈ halfIntegralWeightCuspSpace χ k)
    (hk : Odd k) (h4 : 4 ∣ N) (hk0 : k < 0) : g = 0 := by
  rcases exists_norm_mul_rpow_le_of_mem_halfIntegralWeightCuspSpace hg hk h4 with ⟨K, -, hK⟩
  have hk' : (k : ℝ) < 0 := by
    exact_mod_cast hk0
  have hpos : 0 < -((k : ℝ) / 4) := by
    linarith
  have hcoeff (n : ℕ) : (qExpansion 1 g).coeff n = 0 := by
    have hcont :
        ContinuousAt (fun y : ℝ ↦ K * y ^ (-((k : ℝ) / 4)) * Real.exp (2 * π * n * y)) 0 := by
      have h1 : ContinuousAt (fun y : ℝ ↦ y ^ (-((k : ℝ) / 4))) 0 :=
        Real.continuousAt_rpow_const 0 _ (.inr hpos.le)
      exact (continuousAt_const.mul h1).mul (by fun_prop)
    have hlim : Tendsto (fun y : ℝ ↦ K * y ^ (-((k : ℝ) / 4)) * Real.exp (2 * π * n * y))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa only [Real.zero_rpow hpos.ne', mul_zero, zero_mul] using
        hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    have h3 : ‖(qExpansion 1 g).coeff n‖ ≤ 0 :=
      ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy ↦
        norm_coeff_qExpansion_le hg hK n hy)
    exact norm_le_zero_iff.mp h3
  funext z
  have h : HasSum (fun m : ℕ ↦ (qExpansion 1 g).coeff m * cexp (2 * π * I * m * z)) (g z) :=
    hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace g hg z
  simp only [hcoeff, zero_mul] at h
  exact h.unique hasSum_zero

end ModularForm
