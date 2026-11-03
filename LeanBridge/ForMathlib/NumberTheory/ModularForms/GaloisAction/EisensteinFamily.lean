import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Eisenstein
import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Forms
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Eisenstein series of `Γ₁(N)` used as a primitive element

For a residue pair `a` modulo `N` and a weight `K ≥ 3`, let `G_a` be the Eisenstein series
`∑_{x ≡ a} (x₀ z + x₁)^(-K) + (-1)^K ∑_{x ≡ -a} (x₀ z + x₁)^(-K)`. Slashing by `γ ∈ SL₂(ℤ)` sends
`G_a` to `G_{a γ}`, so that the series `G_{(0, e)}` is a modular form of level `Γ₁(N)`.

Normalised by the constant `2 (-2πi)^K / ((K - 1)! N^K)`, the series `θ_e = G_{(0, e)}` has the
`q`-expansion `t(e) + ∑_{n ≥ 1} (∑_{c m = n} (ζ^(e m) + (-1)^K ζ^(-e m)) m^(K - 1)) qⁿ`, where
`ζ = exp(2πi / N)`, and `t(e)` is a rational combination of powers of `ζ^e`, given by Bernoulli
polynomials. So a field endomorphism `σ` of `ℂ` with `σ(ζ) = ζ^u` sends the `q`-expansion of `θ_e`
to that of `θ_{u e}`.

If `K` is odd and `N ≥ 3`, or `K` is even and `N ≤ 2`, the translates of `θ_1` by the cosets of
`Γ₁(N)` are distinct: `θ_1` is a primitive element for `Γ₁(N)` over level one.

## Main definitions

* `TauCeti.GaloisAction.symWeight`: the weight of the series `G_a`.
* `TauCeti.GaloisAction.symResidue`: the function of residues modulo `N` attached to `e`.
* `TauCeti.GaloisAction.rowNormalizer`: the constant normalising the series `θ_e`.
* `TauCeti.GaloisAction.rowForm`: the modular form `θ_e` of level `Γ₁(N)`.
* `TauCeti.GaloisAction.bernoulliValue`: the rational values of Bernoulli polynomials giving the
  constant term of `θ_e`.
* `TauCeti.GaloisAction.IsPrimitiveWeight`: the hypothesis on the weight and the level under which
  `θ_1` is a primitive element.

## Main results

* `TauCeti.GaloisAction.map_qExpansion_rowForm`: a field endomorphism `σ` of `ℂ` with `σ(ζ) = ζ^u`
  sends the `q`-expansion of `θ_e` to that of `θ_{u e}`.
* `TauCeti.GaloisAction.quotientFunc_rowForm_one_ne`: the translates of `θ_1` by the cosets of
  `Γ₁(N)` are distinct.
-/

open Complex ZMod ModularForm CongruenceSubgroup SlashInvariantForm Function Periodic Subgroup

open UpperHalfPlane hiding I

open Matrix hiding zpow_neg

open scoped Real MatrixGroups

namespace TauCeti.GaloisAction

variable {N K : ℕ}

variable (K) in
/-- The weight on residue pairs modulo `N` of the Eisenstein series `G_a`: the indicator function
of `a` plus `(-1)^K` times the indicator function of `-a`. -/
noncomputable def symWeight (a b : Fin 2 → ZMod N) : ℂ :=
  (if b = a then 1 else 0) + (-1) ^ K * if b = -a then 1 else 0

variable (K) in
/-- The function of residues modulo `N` that is `1` at `e` and `(-1)^K` at `-e`, added together if
`e = -e`, and `0` elsewhere. -/
noncomputable def symResidue (e r : ZMod N) : ℂ :=
  (if r = e then 1 else 0) + (-1) ^ K * if r = -e then 1 else 0

variable (K) in
/-- The value at `j / N` of the Bernoulli polynomial `B_K`, a rational number. -/
noncomputable def bernoulliValue (j : ZMod N) : ℚ :=
  (Polynomial.bernoulli K).eval ((j.val : ℚ) / N)

variable (N K) in
/-- The hypothesis on the weight `K` and the level `N` under which `θ_1` is a primitive element for
`Γ₁(N)`: `K` is odd if `N ≥ 3`, where `-1 ∉ Γ₁(N)`, and `K` is even if `N ≤ 2`, where
`-1 ∈ Γ₁(N)`. -/
def IsPrimitiveWeight : Prop :=
  (Odd K ∧ 3 ≤ N) ∨ (Even K ∧ N ≤ 2)

variable (a b : Fin 2 → ZMod N) (e r : ZMod N) (γ : SL(2, ℤ))

lemma one_ne_neg_one_of_three_le (hN : 3 ≤ N) : (1 : ZMod N) ≠ -1 := fun h ↦ by
  have h₁ : N = 1 ∨ N = 2 := neg_one_eq_one_iff.mp h.symm
  omega

lemma coe_bernoulliFun (j : ZMod N) :
    ((bernoulliFun K (j.val / (N : ℝ)) : ℝ) : ℂ) = (bernoulliValue K j : ℂ) := by
  have h : bernoulliFun K (j.val / (N : ℝ)) = (bernoulliValue K j : ℝ) := by
    have hc : (j.val / (N : ℝ) : ℝ) = algebraMap ℚ ℝ ((j.val : ℚ) / N) := by
      rw [eq_ratCast, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
    rw [bernoulliFun, hc, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  rw [h]
  simp

lemma vecMul_inv_eq_iff (c : Fin 2 → ZMod N) : b ᵥ*
    (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = c ↔
      b = c ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  simpa using
    SpecialLinearGroup.vecMul_eq_iff_eq_vecMul_inv ((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) b c

variable {γ} in
lemma vecMul_zero_row (hγ : γ ∈ Gamma0 N) : ![0, e] ᵥ* ((γ : SL(2, ZMod N)) :
    Matrix (Fin 2) (Fin 2) (ZMod N)) = ![0, e * ((γ 1 1 : ℤ) : ZMod N)] := by
  have h₀ : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  ext i
  fin_cases i <;> simp [vecMul, dotProduct, h₀]

lemma slash_weightedEisensteinSeries_symWeight : EisensteinSeries.weightedEisensteinSeries
    (symWeight K a) K ∣[(K : ℤ)] γ =
      EisensteinSeries.weightedEisensteinSeries (symWeight K
        (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) K := by
  rw [EisensteinSeries.weightedEisensteinSeries_slash_apply]
  congr 1
  ext b
  simp only [symWeight, vecMul_inv_eq_iff, neg_vecMul]

lemma symWeight_zero_eq_rowWeight : symWeight K ![0, e] = rowWeight (symResidue K e) := by
  ext b
  have h₁ (c : ZMod N) : b = ![0, c] ↔ b 0 = 0 ∧ b 1 = c := by
    constructor
    · rintro rfl
      simp
    · rintro ⟨h₀, h₁⟩
      ext i
      fin_cases i <;> simp [h₀, h₁]
  by_cases h₀ : b 0 = 0 <;> simp [symWeight, rowWeight, symResidue, h₁, h₀]

lemma symResidue_neg : symResidue K e (-r) = (-1) ^ K * symResidue K e r := by
  have h₁ : -r = e ↔ r = -e := neg_eq_iff_eq_neg
  have h₂ : -r = -e ↔ r = e := neg_inj
  simp only [symResidue, h₁, h₂]
  linear_combination (-(if r = -e then (1 : ℂ) else 0)) * neg_one_pow_mul_self (K := K)

variable [NeZero N] (hK : 3 ≤ K)

lemma dft_symResidue (j : ZMod N) :
    𝓕 (symResidue K e) j = stdAddChar (-(j * e)) + (-1) ^ K * stdAddChar (j * e) := by
  have h₁ : ∑ r : ZMod N, stdAddChar (-(r * j)) • (if r = e then (1 : ℂ) else 0) =
      stdAddChar (-(j * e)) := by
    simp [mul_comm]
  have h₂ : ∑ r : ZMod N, stdAddChar (-(r * j)) • ((-1) ^ K * if r = -e then (1 : ℂ) else 0) =
      (-1) ^ K * stdAddChar (j * e) := by
    simp [mul_comm]
  simp only [dft_apply, symResidue, smul_add, Finset.sum_add_distrib, h₁, h₂]

variable (N K) in
/-- The constant normalising the Eisenstein series `θ_e`, the coefficient of the Lipschitz formula
times two. -/
noncomputable def rowNormalizer : ℂ :=
  2 * (-2 * π * I) ^ K / ((K - 1).factorial * N ^ K)

lemma rowNormalizer_ne_zero : rowNormalizer N K ≠ 0 := by
  have hf : ((K - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hA : (-2 * π * I : ℂ) ≠ 0 := by
    simp
  exact div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ hA))
    (mul_ne_zero hf (pow_ne_zero _ (NeZero.ne (N : ℂ))))

/-- The Eisenstein series `θ_s` of weight `K`, as a modular form of level `Γ₁(N)`: the series
`G_{(0, s)}`, normalised so that the coefficient of `qⁿ` is
`∑_{c m = n} (ζ^(s m) + (-1)^K ζ^(-s m)) m^(K - 1)` for `n ≥ 1`. -/
noncomputable def rowForm (s : ZMod N) :
    ModularForm ((Gamma1 N).map (SpecialLinearGroup.mapGL ℝ)) K :=
  (rowNormalizer N K)⁻¹ • ModularForm.ofSlashInvariant IsArithmetic.isCusp_of_isCusp
    (EisensteinSeries.weightedEisensteinSeriesMF (symWeight K ![0, s]) (by exact_mod_cast hK))
    fun γ hγ ↦ by
      rcases Subgroup.mem_map.mp hγ with ⟨g, hg, rfl⟩
      rcases mem_Gamma1_iff.mp hg with ⟨hg0, hg1⟩
      have hslash : EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, s]) K ∣[(K : ℤ)]
          SpecialLinearGroup.mapGL ℝ g = _ :=
        (SL_slash _ g).symm.trans (slash_weightedEisensteinSeries_symWeight (K := K) ![0, s] g)
      rw [EisensteinSeries.coe_weightedEisensteinSeriesMF, hslash, vecMul_zero_row s hg0, hg1,
        mul_one]

lemma coe_rowForm : ⇑(rowForm hK e) =
    (rowNormalizer N K)⁻¹ • EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, e]) K := by
  rw [rowForm, FunLike.coe_smul, ModularForm.coe_ofSlashInvariant,
    EisensteinSeries.coe_weightedEisensteinSeriesMF]

lemma rowForm_slash {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 N) :
    ⇑(rowForm hK e) ∣[(K : ℤ)] δ = rowForm hK (e * ((δ 1 1 : ℤ) : ZMod N)) := by
  rw [coe_rowForm, coe_rowForm, SL_smul_slash, slash_weightedEisensteinSeries_symWeight,
    vecMul_zero_row e hδ]

lemma qExpansion_rowForm_coeff (n : ℕ) : (qExpansion 1 (rowForm hK e)).coeff n =
    if n = 0 then (rowNormalizer N K)⁻¹ * ∑' d : ℤ, symResidue K e d * (d : ℂ) ^ (-(K : ℤ))
    else ∑ x ∈ n.divisorsAntidiagonal,
      𝓕 (symResidue K e) (-(x.2 : ZMod N)) * (x.2 : ℂ) ^ (K - 1) := by
  have h (τ : ℍ) : HasSum (fun m : ℕ ↦ (if m = 0 then
      (rowNormalizer N K)⁻¹ * ∑' d : ℤ, symResidue K e d * (d : ℂ) ^ (-(K : ℤ))
      else ∑ x ∈ m.divisorsAntidiagonal,
        𝓕 (symResidue K e) (-(x.2 : ZMod N)) * (x.2 : ℂ) ^ (K - 1)) •
      qParam 1 τ ^ m) (rowForm hK e τ) := by
    have h₁ : HasSum (fun m : ℕ ↦ (rowNormalizer N K)⁻¹ * ((if m = 0 then
        ∑' d : ℤ, symResidue K e d * (d : ℂ) ^ (-(K : ℤ))
        else 2 * (-2 * π * I) ^ K / ((K - 1).factorial * N ^ K) * ∑ x ∈ m.divisorsAntidiagonal,
          𝓕 (symResidue K e) (-(x.2 : ZMod N)) * (x.2 : ℂ) ^ (K - 1)) •
        qParam 1 τ ^ m)) ((rowNormalizer N K)⁻¹ *
          EisensteinSeries.weightedEisensteinSeries (rowWeight (symResidue K e)) K τ) :=
      (hasSum_rowEisenstein (symResidue K e) τ hK (symResidue_neg e)).mul_left _
    rw [coe_rowForm, symWeight_zero_eq_rowWeight]
    convert h₁ using 2 with m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · rw [ite_eq_right hm, ite_eq_right hm, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← rowNormalizer,
        ← mul_assoc, inv_mul_cancel₀ rowNormalizer_ne_zero, one_mul]
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma1_map N) h
    n).symm

lemma rowNormalizer_inv_mul (h₁ : 1 ≤ K) : (rowNormalizer N K)⁻¹ *
    ((N : ℂ)⁻¹ * (-(2 * π * I) ^ K / K.factorial)) =
      ((-(-1) ^ K * (N : ℚ) ^ (K - 1) / (2 * K) : ℚ) : ℂ) := by
  have hN : (N : ℂ) ≠ 0 := NeZero.ne (N : ℂ)
  have hf : ((K - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hA : (2 * π * I : ℂ) ^ K ≠ 0 := pow_ne_zero _ (by simp)
  have hK0 : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac : (K.factorial : ℂ) = (K : ℂ) * (K - 1).factorial := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : K ≠ 0)).symm
  have hneg : (-2 * π * I : ℂ) ^ K = (-1) ^ K * (2 * π * I) ^ K := by
    rw [← mul_pow]
    congr 1
    ring1
  have hpow : (N : ℂ) ^ K = (N : ℂ) ^ (K - 1) * N := by
    rw [← pow_succ, Nat.sub_add_cancel h₁]
  rw [rowNormalizer, hneg, hfac, hpow]
  push_cast
  field_simp
  linear_combination neg_one_pow_mul_self (K := K)

lemma rowNormalizer_inv_mul_tsum (h₂ : 2 ≤ K) : (rowNormalizer N K)⁻¹ * ∑' d : ℤ,
    symResidue K e d * (d : ℂ) ^ (-(K : ℤ)) =
      ((-(-1) ^ K * (N : ℚ) ^ (K - 1) / (2 * K) : ℚ) : ℂ) * ∑ j : ZMod N,
        (stdAddChar (-(j * e)) + (-1) ^ K * stdAddChar (j * e)) * (bernoulliValue K j : ℂ) := by
  rw [tsum_mul_zpow_eq_sum_bernoulliFun _ h₂, ← mul_assoc, rowNormalizer_inv_mul (by omega)]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by rw [dft_symResidue, coe_bernoulliFun]

variable (σ : ℂ →+* ℂ) {u : ZMod N}

/-- **The action of a field endomorphism of `ℂ` on the Eisenstein series `θ_e`**: if `σ` sends the
root of unity `ζ^x` to `ζ^(u x)` for all `x`, it sends the `q`-expansion of `θ_e` to that of
`θ_{u e}`. -/
lemma map_qExpansion_rowForm (hu : ∀ x : ZMod N, σ (stdAddChar x) = stdAddChar (u * x)) :
    PowerSeries.map σ (qExpansion 1 (rowForm hK e)) = qExpansion 1 (rowForm hK (u * e)) := by
  ext n
  rw [PowerSeries.coeff_map, qExpansion_rowForm_coeff, qExpansion_rowForm_coeff]
  split_ifs with hn
  · rw [rowNormalizer_inv_mul_tsum e (by omega), rowNormalizer_inv_mul_tsum (u * e) (by omega),
      map_mul, map_ratCast, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_add, map_mul, map_pow, hu, hu, map_neg σ, map_one, map_ratCast, mul_neg,
      mul_left_comm u j e]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [dft_symResidue, dft_symResidue, map_mul, map_add, map_mul, map_pow, map_pow, hu, hu,
      map_neg σ, map_one, map_natCast, mul_neg u, mul_left_comm u _ e]

lemma exists_map_stdAddChar :
    ∃ u : (ZMod N)ˣ, ∀ x : ZMod N, σ (stdAddChar x) = stdAddChar ((u : ZMod N) * x) := by
  have hζ : IsPrimitiveRoot (stdAddChar (1 : ZMod N)) N := by
    have h : IsPrimitiveRoot (cexp (2 * π * I / N)) N :=
      Complex.isPrimitiveRoot_exp N (NeZero.ne N)
    have h₁ : stdAddChar ((1 : ℤ) : ZMod N) = cexp (2 * π * I * (1 : ℤ) / N) :=
      stdAddChar_coe (N := N) 1
    simp only [Int.cast_one, mul_one] at h₁
    rwa [h₁]
  have hσ : IsPrimitiveRoot (σ (stdAddChar (1 : ZMod N))) N := hζ.map_of_injective σ.injective
  rcases hζ.eq_pow_of_pow_eq_one hσ.pow_eq_one with ⟨i, -, hi⟩
  have hcop : i.Coprime N := (hζ.pow_iff_coprime (NeZero.pos N) i).mp (hi ▸ hσ)
  refine ⟨ZMod.unitOfCoprime i hcop, fun x ↦ ?_⟩
  have hx (y : ZMod N) : stdAddChar y = stdAddChar (1 : ZMod N) ^ y.val := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_one, ZMod.natCast_zmod_val]
  rw [hx x, map_pow, ← hi, ← pow_mul, ZMod.coe_unitOfCoprime, ← AddChar.map_nsmul_eq_pow,
    nsmul_one]
  push_cast
  rw [ZMod.natCast_zmod_val]

/-! ### The translates of `θ_1` are distinct -/

lemma tsum_mul_zpow_ne_zero {g : ZMod N → ℂ} (h₂ : 2 ≤ K) (hpar : ∀ r, g (-r) = (-1) ^ K * g r)
    (hg : ∀ r, ‖g r‖ ≤ ‖g 1‖) (hg1 : g 1 ≠ 0) : ∑' d : ℤ, g d * (d : ℂ) ^ (-(K : ℤ)) ≠ 0 := by
  have hs : Summable fun d : ℤ ↦ g d * (d : ℂ) ^ (-(K : ℤ)) :=
    (hasSum_mul_zpow_sum_bernoulliFun g h₂).summable
  have heven : Function.Even fun d : ℤ ↦ g d * (d : ℂ) ^ (-(K : ℤ)) := by
    intro d
    simp only [Int.cast_neg, hpar]
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, neg_pow (d : ℂ), mul_inv, inv_neg_one_pow]
    linear_combination (g d * ((d : ℂ) ^ K)⁻¹) * neg_one_pow_mul_self (K := K)
  have h0 : (0 : ℂ) ^ (-(K : ℤ)) = 0 := zero_zpow _ (by omega)
  have hfs : Summable fun n : ℕ ↦ g ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) : ℂ) ^ (-(K : ℤ)) :=
    hs.comp_injective (i := fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ)) fun a b hab ↦ by
      simpa using hab
  have hsplit : ∑' n : ℕ+, g ((n : ℕ) : ℤ) * (((n : ℕ) : ℤ) : ℂ) ^ (-(K : ℤ)) =
      g 1 + ∑' n : ℕ, g ((n + 2 : ℕ) : ℤ) * (((n + 2 : ℕ) : ℤ) : ℂ) ^ (-(K : ℤ)) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ g (n : ℤ) * ((n : ℤ) : ℂ) ^ (-(K : ℤ))),
      hfs.tsum_eq_zero_add]
    simp [add_assoc]
  have hbound : ‖∑' n : ℕ, g ((n + 2 : ℕ) : ℤ) * (((n + 2 : ℕ) : ℤ) : ℂ) ^ (-(K : ℤ))‖ ≤
      ‖g 1‖ * (π ^ 2 / 6 - 1) := by
    have hz : HasSum (fun n : ℕ ↦ (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6 - 1) := by
      have hz₂ : HasSum (fun n : ℕ ↦ (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2)
          (π ^ 2 / 6 - ∑ i ∈ Finset.range 2, (1 : ℝ) / (i : ℝ) ^ 2) :=
        (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
      simpa [Finset.sum_range_succ] using hz₂
    refine tsum_of_norm_bounded (hz.mul_left ‖g 1‖) fun n ↦ ?_
    rw [norm_mul]
    refine mul_le_mul (hg _) ?_ (norm_nonneg _) (norm_nonneg _)
    rw [zpow_neg, zpow_natCast, norm_inv, norm_pow, Int.cast_natCast, Complex.norm_natCast,
      one_div]
    have hm : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ n + 2)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hm h₂)
  have hpi : π ^ 2 / 6 - 1 < 1 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs]
  simp only [Int.cast_zero, h0, mul_zero, zero_add, nsmul_eq_mul]
  intro hzero
  have h₁ : ∑' n : ℕ+, g ((n : ℕ) : ℤ) * (((n : ℕ) : ℤ) : ℂ) ^ (-(K : ℤ)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left two_ne_zero
  rw [hsplit] at h₁
  have h₂ : ‖g 1‖ ≤ ‖g 1‖ * (π ^ 2 / 6 - 1) :=
    (congrArg norm (eq_neg_of_add_eq_zero_left h₁)).trans_le ((norm_neg _).trans_le hbound)
  exact absurd h₂ (not_le.mpr (mul_lt_of_lt_one_right (norm_pos_iff.mpr hg1) hpi))

lemma tsum_symResidue_one_ne_zero (hN : IsPrimitiveWeight N K) (h₂ : 2 ≤ K) :
    ∑' d : ℤ, symResidue K (1 : ZMod N) d * (d : ℂ) ^ (-(K : ℤ)) ≠ 0 := by
  rcases hN with ⟨-, hN⟩ | ⟨heven, hN⟩
  · have hne : (1 : ZMod N) ≠ -1 := one_ne_neg_one_of_three_le hN
    have h1 : symResidue K (1 : ZMod N) 1 = 1 := by
      simp [symResidue, hne]
    refine tsum_mul_zpow_ne_zero h₂ (symResidue_neg _) (fun r ↦ ?_) (by simp [h1])
    rw [h1, norm_one]
    by_cases hr : r = 1
    · simp [hr, h1]
    · by_cases hr' : r = -1
      · simp [symResidue, hr', hne.symm]
      · simp [symResidue, hr, hr']
  · have hpos : 0 < N := NeZero.pos N
    have hneg : (-1 : ZMod N) = 1 := neg_one_eq_one_iff.mpr <| by omega
    have hs₁ : (-1 : ℂ) ^ K = 1 := heven.neg_one_pow
    have hfun (r : ZMod N) : symResidue K (1 : ZMod N) r = if r = 1 then 2 else 0 := by
      split_ifs with hr <;> simp [symResidue, hneg, hs₁, hr]
      norm_num
    refine tsum_mul_zpow_ne_zero h₂ (symResidue_neg _) (fun r ↦ ?_) (by simp [hfun])
    by_cases hr : r = 1 <;> simp [hfun, hr]

lemma valueAtInfty_weightedEisensteinSeries_rowForm (h₃ : 3 ≤ K) : valueAtInfty
    (EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, e]) K) =
      ∑' d : ℤ, symResidue K e d * (d : ℂ) ^ (-(K : ℤ)) := by
  rw [EisensteinSeries.valueAtInfty_weightedEisensteinSeries _ (by exact_mod_cast h₃),
    symWeight_zero_eq_rowWeight]
  refine tsum_congr fun n ↦ ?_
  rw [rowWeight_intCast]
  simp

lemma valueAtInfty_weightedEisensteinSeries_eq_zero (h₃ : 3 ≤ K) (ha : a 0 ≠ 0) :
    valueAtInfty (EisensteinSeries.weightedEisensteinSeries (symWeight K a) K) = 0 := by
  rw [EisensteinSeries.valueAtInfty_weightedEisensteinSeries _ (by exact_mod_cast h₃)]
  refine (tsum_congr fun n ↦ ?_).trans tsum_zero
  have h₁ : ((↑) ∘ ![0, n] : Fin 2 → ZMod N) ≠ a := fun h ↦ ha <| by
    rw [← h]
    simp
  have h₂ : ((↑) ∘ ![0, n] : Fin 2 → ZMod N) ≠ -a := fun h ↦ ha <| by
    have h₀ : ((↑) ∘ ![0, n] : Fin 2 → ZMod N) 0 = (-a) 0 := congrFun h 0
    simpa using h₀.symm
  simp [symWeight, h₁, h₂]

lemma qExpansion_rowForm_coeff_one :
    (qExpansion 1 (rowForm hK e)).coeff 1 = stdAddChar e + (-1) ^ K * stdAddChar (-e) := by
  rw [qExpansion_rowForm_coeff]
  simp [dft_symResidue]

lemma qExpansion_rowForm_coeff_two : (qExpansion 1 (rowForm hK e)).coeff 2 =
    (stdAddChar (2 * e) + (-1) ^ K * stdAddChar (-(2 * e))) * 2 ^ (K - 1) +
      stdAddChar e + (-1) ^ K * stdAddChar (-e) := by
  have h : Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} := by decide
  rw [qExpansion_rowForm_coeff, h]
  simp [dft_symResidue]
  ring1

lemma eq_of_sub_inv_eq {z w C : ℂ} (hz : z ≠ 0) (hC : C ≠ 0) (hz2 : z ^ 2 ≠ 1)
    (h₁ : z - z⁻¹ = w - w⁻¹) (h₂ : (z ^ 2 - (z ^ 2)⁻¹) * C = (w ^ 2 - (w ^ 2)⁻¹) * C) : z = w := by
  have h₄ : z ^ 2 - (z ^ 2)⁻¹ = w ^ 2 - (w ^ 2)⁻¹ := mul_right_cancel₀ hC h₂
  rw [← inv_pow, ← inv_pow] at h₄
  have h₃ : (z - z⁻¹) * (z + z⁻¹) = (z - z⁻¹) * (w + w⁻¹) := by
    linear_combination h₄ - (w + w⁻¹) * h₁
  have hne : z - z⁻¹ ≠ 0 := by
    intro h
    refine hz2 ?_
    rw [sq]
    nth_rw 2 [sub_eq_zero.mp h]
    exact mul_inv_cancel₀ hz
  have h₅ : z + z⁻¹ = w + w⁻¹ := mul_left_cancel₀ hne h₃
  linear_combination (1 / 2 : ℂ) * h₁ + (1 / 2 : ℂ) * h₅

lemma stdAddChar_two_mul (x : ZMod N) : stdAddChar (2 * x) = stdAddChar x ^ 2 := by
  rw [two_mul, AddChar.map_add_eq_mul, sq]

variable {e} in
lemma eq_one_of_rowForm_coe_eq (hN : IsPrimitiveWeight N K) (he : IsUnit e)
    (h : ⇑(rowForm hK (1 : ZMod N)) = rowForm hK e) : e = 1 := by
  rcases hN with ⟨hodd, hN⟩ | ⟨-, hN⟩
  · have hs : (-1 : ℂ) ^ K = -1 := hodd.neg_one_pow
    have hc1 : stdAddChar (1 : ZMod N) - (stdAddChar (1 : ZMod N))⁻¹ =
        stdAddChar e - (stdAddChar e)⁻¹ := by
      have h₁ : (qExpansion 1 (rowForm hK (1 : ZMod N))).coeff 1 =
          (qExpansion 1 (rowForm hK e)).coeff 1 := by
        rw [h]
      rw [qExpansion_rowForm_coeff_one, qExpansion_rowForm_coeff_one, hs, AddChar.map_neg_eq_inv,
        AddChar.map_neg_eq_inv] at h₁
      linear_combination h₁
    have hc2 : (stdAddChar (1 : ZMod N) ^ 2 - (stdAddChar (1 : ZMod N) ^ 2)⁻¹) * (2 : ℂ) ^ (K - 1) =
        (stdAddChar e ^ 2 - (stdAddChar e ^ 2)⁻¹) * (2 : ℂ) ^ (K - 1) := by
      have h₂ : (qExpansion 1 (rowForm hK (1 : ZMod N))).coeff 2 =
          (qExpansion 1 (rowForm hK e)).coeff 2 := by
        rw [h]
      rw [qExpansion_rowForm_coeff_two, qExpansion_rowForm_coeff_two, hs, AddChar.map_neg_eq_inv,
        AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, stdAddChar_two_mul,
        stdAddChar_two_mul] at h₂
      linear_combination h₂ - hc1
    have hz : stdAddChar (1 : ZMod N) ≠ 0 := by
      rw [stdAddChar_apply]
      exact Circle.coe_ne_zero _
    have hz2 : stdAddChar (1 : ZMod N) ^ 2 ≠ 1 := fun h₃ ↦ by
      rw [← stdAddChar_two_mul, ← AddChar.map_zero_eq_one (stdAddChar (N := N))] at h₃
      refine one_ne_neg_one_of_three_le hN ?_
      linear_combination injective_stdAddChar h₃
    exact (injective_stdAddChar (eq_of_sub_inv_eq hz (pow_ne_zero _ two_ne_zero) hz2 hc1 hc2)).symm
  · rcases eq_or_ne N 1 with rfl | hN₁
    · exact Subsingleton.elim _ _
    · have hN₂ : N = 2 := by
        have hpos : 0 < N := NeZero.pos N
        omega
      subst hN₂
      revert he
      fin_cases e
      · intro he
        exact absurd he not_isUnit_zero
      · exact fun _ ↦ rfl

variable {γ} in
lemma mem_Gamma1_of_eisenstein_eq (hN : IsPrimitiveWeight N K) (h₃ : 3 ≤ K)
    (h : EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, (1 : ZMod N)]) K =
      EisensteinSeries.weightedEisensteinSeries (symWeight K
        (![0, 1] ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) K) :
    γ ∈ Gamma1 N := by
  have hv : valueAtInfty (EisensteinSeries.weightedEisensteinSeries
      (symWeight K ![0, (1 : ZMod N)]) K) = valueAtInfty (EisensteinSeries.weightedEisensteinSeries
        (symWeight K (![0, 1] ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))))
          K) :=
    congrArg valueAtInfty h
  rw [valueAtInfty_weightedEisensteinSeries_rowForm _ h₃] at hv
  by_cases hγ : γ ∈ Gamma0 N
  · rw [vecMul_zero_row _ hγ, one_mul] at h
    refine mem_Gamma1_iff.mpr ⟨hγ, eq_one_of_rowForm_coe_eq h₃ hN ?_ ?_⟩
    · exact isUnit_iff_exists_inv'.mpr
        ⟨_, intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγ⟩
    · rw [coe_rowForm, coe_rowForm, h]
  · refine absurd ?_ (tsum_symResidue_one_ne_zero hN (by omega))
    rw [hv]
    refine valueAtInfty_weightedEisensteinSeries_eq_zero _ h₃ fun h₀ ↦ hγ ?_
    rw [Gamma0_mem]
    simpa [vecMul, dotProduct] using h₀

/-- **The translates of `θ_1` by the cosets of `Γ₁(N)` are distinct**, if `K ≥ 3` is odd and
`N ≥ 3`, or `K` is even and `N ≤ 2`: the Eisenstein series `θ_1` is a primitive element for `Γ₁(N)`
over level one. Its translate by `γ` is the series `G_{(c, d)}` for the lower row `(c, d)` of `γ`
modulo `N`. Its constant term vanishes unless `c = 0`, and the coefficients of `q` and `q²` of
`G_{(0, d)}` determine `d`. -/
lemma quotientFunc_rowForm_one_ne (hN : IsPrimitiveWeight N K)
    (q q' : 𝒮ℒ ⧸ ((Gamma1 N).map (SpecialLinearGroup.mapGL ℝ)).subgroupOf 𝒮ℒ) (hq : q ≠ q') :
    quotientFunc (rowForm hK (1 : ZMod N)) q ≠ quotientFunc (rowForm hK (1 : ZMod N)) q' := by
  rcases exists_cosetOf_eq q with ⟨δ, rfl⟩
  rcases exists_cosetOf_eq q' with ⟨δ', rfl⟩
  intro heq
  rw [quotientFunc_cosetOf, quotientFunc_cosetOf, coe_rowForm, SL_smul_slash, SL_smul_slash] at heq
  have h₁ : EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, (1 : ZMod N)]) K ∣[(K : ℤ)]
      δ = EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, (1 : ZMod N)]) K ∣[(K : ℤ)]
        δ' :=
    smul_right_injective _ (inv_ne_zero rowNormalizer_ne_zero) heq
  have h₂ : EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, (1 : ZMod N)]) K =
      EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, (1 : ZMod N)]) K ∣[(K : ℤ)]
        (δ' * δ⁻¹) := by
    have h₃ : (EisensteinSeries.weightedEisensteinSeries (symWeight K ![0, (1 : ZMod N)]) K
        ∣[(K : ℤ)] δ) ∣[(K : ℤ)] δ⁻¹ = (EisensteinSeries.weightedEisensteinSeries
          (symWeight K ![0, (1 : ZMod N)]) K ∣[(K : ℤ)] δ') ∣[(K : ℤ)] δ⁻¹ := by
      rw [h₁]
    simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at h₃
    exact h₃
  rw [slash_weightedEisensteinSeries_symWeight] at h₂
  have hmem : δ' * δ⁻¹ ∈ Gamma1 N := mem_Gamma1_of_eisenstein_eq hN hK h₂
  refine hq <| Quotient.sound <| QuotientGroup.leftRel_apply.mpr <| Subgroup.mem_subgroupOf.mpr ?_
  refine ⟨(δ' * δ⁻¹)⁻¹, inv_mem hmem, ?_⟩
  simp

end TauCeti.GaloisAction
