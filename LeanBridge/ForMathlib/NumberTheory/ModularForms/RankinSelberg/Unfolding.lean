import LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.LatticeSum
import LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.Strip
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import TauCeti.NumberTheory.Modular

/-!
# The Rankin–Selberg unfolding

Let `h` be a continuous function on the upper half plane, decaying at every cusp, that transforms
under `Γ₀(L)` through a character `ω` of `(ℤ / L)ˣ`. Unfolding over the standard fundamental domain
`𝒟ᵒ` of `PSL₂(ℤ)` writes the integral of `h(τ) (Im τ) ^ σ` over the strip `0 ≤ Re τ < 1` as half the
integral over `𝒟ᵒ` of `(Im τ) ^ σ ∑_{(c, d) = 1} h(γ_{c,d} τ) |c τ + d| ^ (-2σ)`.

The value `h(γ_{c,d} τ)` depends only on `(c, d)` modulo `L`, and a nontrivial `ω` makes these
values have mean zero, so the lattice sums of
`LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.LatticeSum` give no pole at `σ = 1`.
For `h ≥ 0` with `ω = 1`, the term of the identity coset gives a pole. Only the qualitative
behaviour as `σ → 1⁺` is obtained: no analytic continuation, functional equation or Euler product
is used.

## Main definitions

* `RankinSelberg.row`: the bottom row of a matrix of `SL₂(ℤ)`.
* `RankinSelberg.stripLift`: the element of `SL₂(ℤ)` with a given bottom row taking `τ` into the
  strip.
* `RankinSelberg.HasNebentypus`: `h` transforms under `Γ₀(L)` through a character.
* `RankinSelberg.rowVal`: the value `h(γ τ)` as a function of the bottom row of `γ` modulo `L`.
* `RankinSelberg.cosetSum`: the unfolded form of the Rankin–Selberg integrand.
* `RankinSelberg.HasDecay`: `h` decays at every cusp.

## Main results

* `RankinSelberg.integral_eq_half_mul_setIntegral_tsum`: unfolding over the standard fundamental
  domain.
* `RankinSelberg.integral_stripFun_eq_setIntegral_cosetSum`: the Rankin–Selberg unfolding.
* `RankinSelberg.tendsto_sub_one_mul_integral_stripFun`: the Rankin–Selberg integral of a function
  with a nontrivial character has no pole at `σ = 1`.
* `RankinSelberg.exists_le_sub_one_mul_re_integral_stripFun`: the Rankin–Selberg integral of a
  nonnegative function has a pole at `σ = 1`.
-/

open MeasureTheory UpperHalfPlane Set ModularGroup Matrix SpecialLinearGroup Filter Topology
    EisensteinSeries

open scoped MatrixGroups Real

namespace RankinSelberg

variable {h : ℍ → ℂ} {L : ℕ} {τ : ℍ} {σ : ℝ} {γ γ' : SL(2, ℤ)} {ξ : gammaSet 1 1 0}
    {ω : (ZMod L)ˣ →* ℂˣ} {v : Fin 2 → ZMod L} {w : (ZMod L)ˣ} {u : ℍ → ℝ} {g : ℕ} {x : Fin 2 → ℤ}

lemma card_center_SL : Nat.card (Subgroup.center SL(2, ℤ)) = 2 :=
  card_center_eq_two fun h ↦ by
    have h00 : (-1 : SL(2, ℤ)) 0 0 = (1 : SL(2, ℤ)) 0 0 := congrArg (fun g : SL(2, ℤ) ↦ g 0 0) h
    simp at h00

lemma tsum_sl_eq_two_mul_tsum_psl (A : PSL(2, ℤ) → ℂ) :
    ∑' γ : SL(2, ℤ), A (γ : PSL(2, ℤ)) = 2 * ∑' g, A g := by
  let e : SL(2, ℤ) ≃ PSL(2, ℤ) × Subgroup.center SL(2, ℤ) :=
    Subgroup.groupEquivQuotientProdSubgroup
  have hfst : ∀ z, ((e.symm z : SL(2, ℤ)) : PSL(2, ℤ)) = z.1 := fun z ↦ by
    have h : (e (e.symm z)).1 = ((e.symm z : SL(2, ℤ)) : PSL(2, ℤ)) := rfl
    rw [← h, e.apply_symm_apply]
  by_cases hA : Summable A
  · have hfin : Finite (Subgroup.center SL(2, ℤ)) := Nat.finite_of_card_ne_zero (by
      rw [card_center_SL]
      norm_num)
    have hone : ∑' _ : Subgroup.center SL(2, ℤ), (1 : ℂ) = 2 := by
      rw [tsum_const, card_center_SL]
      norm_num
    have hprod : (∑' g, A g) * 2 = ∑' z : PSL(2, ℤ) × Subgroup.center SL(2, ℤ), A z.1 * 1 :=
      hone ▸ tsum_mul_tsum_of_summable_norm hA.norm Summable.of_finite
    rw [← e.symm.tsum_eq, mul_comm, hprod]
    exact tsum_congr fun z ↦ by rw [hfst, mul_one]
  · rw [tsum_eq_zero_of_not_summable hA, mul_zero]
    refine tsum_eq_zero_of_not_summable fun hsum ↦ hA ?_
    have hinj : Function.Injective fun g : PSL(2, ℤ) ↦ e.symm (g, 1) := fun g g' h ↦
      congrArg Prod.fst (e.symm.injective h)
    refine (hsum.comp_injective hinj).congr fun g ↦ ?_
    simp only [Function.comp_apply]
    rw [hfst]

/-- **Unfolding over the standard fundamental domain**: for `φ` integrable on `ℍ`,
`∫ φ = ½ ∫_{𝒟ᵒ} ∑_{γ ∈ SL₂(ℤ)} φ(γ τ) dμ(τ)`, the factor `½` because `±γ` act alike. -/
lemma integral_eq_half_mul_setIntegral_tsum {φ : ℍ → ℂ} (hφ : Integrable φ) :
    ∫ τ, φ τ = (1 / 2) * ∫ τ in fdo, ∑' γ : SL(2, ℤ), φ (γ • τ) := by
  have hfd : IsFundamentalDomain PSL(2, ℤ) fdo := isFundamentalDomain_fdo
  have hmeas : ∀ g : PSL(2, ℤ), AEStronglyMeasurable (fun τ ↦ φ (g • τ))
      ((volume : Measure ℍ).restrict fdo) := fun g ↦
    (hφ.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul g volume)).restrict
  have hfin : ∑' g : PSL(2, ℤ), ∫⁻ τ in fdo, ‖φ (g • τ)‖ₑ ≠ ⊤ := by
    rw [← hfd.lintegral_eq_tsum'' fun τ ↦ ‖φ τ‖ₑ]
    exact hφ.hasFiniteIntegral.ne
  rw [hfd.integral_eq_tsum'' φ hφ, ← integral_tsum hmeas hfin, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ ↦ ?_)
  have h : ∑' γ : SL(2, ℤ), φ (γ • τ) = 2 * ∑' g : PSL(2, ℤ), φ (g • τ) := by
    simpa only [pslMk_smul] using tsum_sl_eq_two_mul_tsum_psl fun g ↦ φ (g • τ)
  beta_reduce
  rw [h]
  ring1

variable (γ) in
/-- The bottom row of a matrix of `SL(2, ℤ)`, as a vector of integers. -/
def row : Fin 2 → ℤ :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ) 1

variable (γ) in
lemma row_mem_gammaSet : row γ ∈ gammaSet 1 1 0 :=
  (mem_gammaSet_one _).mpr (bottom_row_coprime γ)

lemma row_T_zpow_mul (n : ℤ) : row (T ^ n * γ) = row γ := by
  funext j
  simp [row]

variable (ξ) in
lemma exists_row_eq : ∃ γ : SL(2, ℤ), row γ = ξ.1 := by
  rcases bottom_row_surj ((mem_gammaSet_one _).mp ξ.2) with ⟨γ, -, hγ⟩
  exact ⟨γ, hγ⟩

lemma im_smul_rpow : (γ • τ).im ^ σ = τ.im ^ σ * latticeTerm τ σ (row γ) := by
  have hne : ((row γ 0 : ℂ) * τ + row γ 1) ≠ 0 := by
    simpa [denom, row] using denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have hnorm : 0 < ‖(row γ 0 : ℂ) * τ + row γ 1‖ := norm_pos_iff.mpr hne
  have him : (γ • τ).im = τ.im / ‖(row γ 0 : ℂ) * τ + row γ 1‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
    simp [denom, row]
  have hpow :
      (‖(row γ 0 : ℂ) * τ + row γ 1‖ ^ 2) ^ σ = (‖(row γ 0 : ℂ) * τ + row γ 1‖ ^ (-(2 * σ)))⁻¹ := by
    rw [Real.rpow_neg hnorm.le, inv_inv, ← Real.rpow_two, ← Real.rpow_mul hnorm.le]
  rw [him, Real.div_rpow τ.im_pos.le (by positivity), hpow, div_inv_eq_mul, latticeTerm]

lemma mul_inv_apply_one_zero : (γ' * γ⁻¹) 1 0 = γ' 1 0 * γ 1 1 - γ' 1 1 * γ 1 0 := by
  rw [γ'.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, inv_apply_zero_zero, inv_apply_one_zero]
  ring1

lemma mul_inv_apply_one_one : (γ' * γ⁻¹) 1 1 = γ' 1 1 * γ 0 0 - γ' 1 0 * γ 0 1 := by
  rw [γ'.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, inv_apply_zero_one, inv_apply_one_one]
  ring1

lemma eq_of_row_eq_of_re_mem (hrow : row γ = row γ') (hγ : (γ • τ).re ∈ Ico (0 : ℝ) 1)
    (hγ' : (γ' • τ).re ∈ Ico (0 : ℝ) 1) : γ = γ' := by
  have h0 : γ' 1 0 = γ 1 0 := (congrFun hrow 0).symm
  have h1 : γ' 1 1 = γ 1 1 := (congrFun hrow 1).symm
  have hc : (γ' * γ⁻¹) 1 0 = 0 := by
    rw [mul_inv_apply_one_zero, h0, h1]
    ring1
  have hd : (γ' * γ⁻¹) 1 1 = 1 := by
    rw [mul_inv_apply_one_one, h0, h1]
    linarith [γ.fin_two_mul_sub_mul_eq_one]
  have ha : (γ' * γ⁻¹) 0 0 = 1 := by
    have hdet : (γ' * γ⁻¹) 0 0 * (γ' * γ⁻¹) 1 1 - (γ' * γ⁻¹) 0 1 * (γ' * γ⁻¹) 1 0 = 1 :=
      (γ' * γ⁻¹).fin_two_mul_sub_mul_eq_one
    rw [hc, hd] at hdet
    linarith
  have hT : γ' * γ⁻¹ = T ^ ((γ' * γ⁻¹) 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, coe_T_zpow]
  have hγ'' : γ' = T ^ ((γ' * γ⁻¹) 0 1) * γ := by
    rw [← hT, inv_mul_cancel_right]
  have hre : (γ' • τ).re = (γ • τ).re + ((γ' * γ⁻¹) 0 1 : ℤ) := by
    conv_lhs => rw [hγ'', mul_smul, re_T_zpow_smul]
  have hn : (γ' * γ⁻¹) 0 1 = 0 := by
    have hlt : |(((γ' * γ⁻¹) 0 1 : ℤ) : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hγ.1, hγ.2, hγ'.1, hγ'.2]
    exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
  rw [hγ'', hn, zpow_zero, one_mul]

variable (τ ξ) in
/-- The element of `SL(2, ℤ)` with bottom row `ξ` taking `τ` into the strip. -/
noncomputable def stripLift : SL(2, ℤ) :=
  T ^ (-⌊((exists_row_eq ξ).choose • τ).re⌋) * (exists_row_eq ξ).choose

variable (τ ξ) in
lemma row_stripLift : row (stripLift τ ξ) = ξ.1 := by
  rw [stripLift, row_T_zpow_mul]
  exact (exists_row_eq ξ).choose_spec

variable (τ ξ) in
lemma re_stripLift_smul_mem : (stripLift τ ξ • τ).re ∈ Ico (0 : ℝ) 1 := by
  rw [stripLift, mul_smul, re_T_zpow_smul, Int.cast_neg, ← sub_eq_add_neg, Int.self_sub_floor]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

lemma stripLift_row (hγ : (γ • τ).re ∈ Ico (0 : ℝ) 1) :
    stripLift τ ⟨row γ, row_mem_gammaSet γ⟩ = γ :=
  eq_of_row_eq_of_re_mem (row_stripLift τ _) (re_stripLift_smul_mem τ _) hγ

lemma tsum_stripFun_smul : ∑' γ : SL(2, ℤ), stripFun h σ (γ • τ) =
    ∑' ξ : gammaSet 1 1 0, h (stripLift τ ξ • τ) * ((τ.im ^ σ * latticeTerm τ σ ξ.1 : ℝ) : ℂ) := by
  have hinj : Function.Injective (stripLift τ) := fun ξ ξ' hξ ↦
    Subtype.ext ((row_stripLift τ ξ).symm.trans ((congrArg row hξ).trans (row_stripLift τ ξ')))
  have hsupp :
      Function.support (fun γ : SL(2, ℤ) ↦ stripFun h σ (γ • τ)) ⊆ range (stripLift τ) := by
    intro γ hγ
    have hmem : γ • τ ∈ strip := by
      by_contra hn
      exact hγ <| indicator_of_notMem hn _
    exact ⟨⟨row γ, row_mem_gammaSet γ⟩, stripLift_row hmem⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun ξ ↦ ?_
  have hmem : stripLift τ ξ • τ ∈ strip := re_stripLift_smul_mem τ ξ
  rw [stripFun, indicator_of_mem hmem, im_smul_rpow, row_stripLift]

variable (h ω) in
/-- The function `h` on `ℍ` **transforms under `Γ₀(L)` through the character `ω`**:
`h(γ τ) = ω(d) h(τ)` for every `γ` in `SL₂(ℤ)` with `L ∣ c`, for `d` the lower right entry of
`γ`. -/
def HasNebentypus : Prop :=
  ∀ (γ : SL(2, ℤ)) (w : (ZMod L)ˣ), ((γ 1 0 : ℤ) : ZMod L) = 0 → ((γ 1 1 : ℤ) : ZMod L) = w →
    ∀ τ : ℍ, h (γ • τ) = (ω w : ℂ) * h τ

open scoped Classical in
variable (h L τ v) in
/-- The value `h(γ τ)` as a function of the bottom row of `γ` modulo `L`: well defined when `h` is
invariant under `Γ₁(L)`, and `0` at the vectors that are not the reduction of a bottom row. -/
noncomputable def rowVal : ℂ :=
  if hv : ∃ γ : SL(2, ℤ), reduceMod L (row γ) = v then h (hv.choose • τ) else 0

lemma rowVal_reduceMod_row (hh : HasNebentypus h ω) :
    rowVal h L τ (reduceMod L (row γ)) = h (γ • τ) := by
  have hv : ∃ γ' : SL(2, ℤ), reduceMod L (row γ') = reduceMod L (row γ) := ⟨γ, rfl⟩
  rw [rowVal, dite_eq_left hv]
  have h0 : ((hv.choose 1 0 : ℤ) : ZMod L) = ((γ 1 0 : ℤ) : ZMod L) := congrFun hv.choose_spec 0
  have h1 : ((hv.choose 1 1 : ℤ) : ZMod L) = ((γ 1 1 : ℤ) : ZMod L) := congrFun hv.choose_spec 1
  have hdet : ((hv.choose 0 0 : ℤ) : ZMod L) * ((hv.choose 1 1 : ℤ) : ZMod L) -
      ((hv.choose 0 1 : ℤ) : ZMod L) * ((hv.choose 1 0 : ℤ) : ZMod L) = 1 :=
    hv.choose.intCast_fin_two_mul_sub_mul_eq_one
  have hc : (((γ * hv.choose⁻¹) 1 0 : ℤ) : ZMod L) = 0 := by
    rw [mul_inv_apply_one_zero]
    push_cast
    rw [h0, h1]
    ring1
  have hd : (((γ * hv.choose⁻¹) 1 1 : ℤ) : ZMod L) = ((1 : (ZMod L)ˣ) : ZMod L) := by
    rw [mul_inv_apply_one_one]
    push_cast
    rw [← h0, ← h1]
    linear_combination hdet
  have h2 : h (γ • τ) = ((ω 1 : ℂˣ) : ℂ) * h (hv.choose • τ) := by
    simpa only [← mul_smul, inv_mul_cancel_right] using hh _ 1 hc hd (hv.choose • τ)
  rw [h2, map_one, Units.val_one, one_mul]

lemma reduceMod_row_mul {δ : SL(2, ℤ)} (hc : ((δ 1 0 : ℤ) : ZMod L) = 0) :
    reduceMod L (row (δ * γ)) = ((δ 1 1 : ℤ) : ZMod L) • reduceMod L (row γ) := by
  funext j
  simp only [reduceMod, row, δ.coe_mul γ, Matrix.mul_apply, Fin.sum_univ_two, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  rw [hc, zero_mul, zero_add]

lemma reduceMod_nsmul : reduceMod L (g • x) = (g : ZMod L) • reduceMod L x :=
  funext fun j ↦ by simp [reduceMod]

variable (h L τ σ) in
/-- The sum `∑_{(c, d) = 1} h(γ_{c,d} τ) |c τ + d| ^ (-2σ)` over the coprime bottom rows, the
unfolded form of the Rankin–Selberg integrand. -/
noncomputable def cosetSum : ℂ :=
  ∑' ξ : gammaSet 1 1 0, rowVal h L τ (reduceMod L ξ.1) * (latticeTerm τ σ ξ.1 : ℂ)

lemma tsum_stripFun_smul_eq (hh : HasNebentypus h ω) :
    ∑' γ : SL(2, ℤ), stripFun h σ (γ • τ) = ((τ.im ^ σ : ℝ) : ℂ) * cosetSum h L τ σ := by
  rw [tsum_stripFun_smul, cosetSum, ← tsum_mul_left]
  refine tsum_congr fun ξ ↦ ?_
  have hv : rowVal h L τ (reduceMod L ξ.1) = h (stripLift τ ξ • τ) := by
    rw [← rowVal_reduceMod_row hh, row_stripLift]
  rw [hv]
  push_cast
  ring1

/-- **The Rankin–Selberg unfolding**: the integral of `h(τ) (Im τ) ^ σ` over the strip is half the
integral over `𝒟ᵒ` of `(Im τ) ^ σ ∑_{(c, d) = 1} h(γ_{c,d} τ) |c τ + d| ^ (-2σ)`. -/
lemma integral_stripFun_eq_setIntegral_cosetSum (hh : HasNebentypus h ω)
    (hint : Integrable (stripFun h σ)) :
    ∫ τ, stripFun h σ τ = (1 / 2) * ∫ τ in fdo, ((τ.im ^ σ : ℝ) : ℂ) * cosetSum h L τ σ := by
  rw [integral_eq_half_mul_setIntegral_tsum hint]
  simp_rw [tsum_stripFun_smul_eq hh]

lemma half_le_r (hτ : τ ∈ fd) : 1 / 2 ≤ r τ := by
  have h3 : 3 ≤ 4 * τ.im ^ 2 := three_le_four_mul_im_sq_of_mem_fd hτ
  have him : 0 < τ.im := τ.im_pos
  have hre : τ.re ^ 2 ≤ 1 / 4 := by
    have h : -(1 / 2) ≤ τ.re ∧ τ.re ≤ 1 / 2 := abs_le.mp hτ.2
    nlinarith
  refine le_min (by nlinarith) (Real.le_sqrt_of_sq_le ?_)
  rw [r1, le_div_iff₀ (by positivity)]
  nlinarith

lemma rpow_le_one_add_sq {y : ℝ} (hy : 0 < y) (hσ : σ ∈ Ioc (1 : ℝ) 2) : y ^ σ ≤ 1 + y ^ 2 := by
  rcases le_total y 1 with h1 | h1
  · linarith [Real.rpow_le_one hy.le h1 (by linarith [hσ.1] : 0 ≤ σ), sq_nonneg y]
  · have h2 : y ^ σ ≤ y ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hσ.2
    rw [Real.rpow_two] at h2
    linarith

lemma tsum_latticeTerm_le_of_mem_fd (hτ : τ ∈ fd) (hσ : σ ∈ Ioc (1 : ℝ) 2) :
    ∑' x : Fin 2 → ℤ, latticeTerm τ σ x ≤ 16 * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * σ)) := by
  rw [← tsum_mul_left]
  refine (summable_latticeTerm τ hσ.1).tsum_le_tsum (fun x ↦ ?_)
    ((summable_norm_rpow hσ.1).mul_left 16)
  refine (latticeTerm_le τ x (by linarith [hσ.1])).trans
    (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have h1 : r τ ^ (-(2 * σ)) ≤ (1 / 2 : ℝ) ^ (-(2 * σ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (half_le_r hτ) (by linarith [hσ.1])
  have h2 : (1 / 2 : ℝ) ^ (-(2 * σ)) ≤ (1 / 2 : ℝ) ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith [hσ.2])
  have h3 : (1 / 2 : ℝ) ^ (-4 : ℝ) = 16 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_ofNat]
    norm_num
  linarith

variable (h) in
/-- The function `h` **decays at every cusp**: each `h(γ τ) (1 + (Im τ) ^ 2)` is bounded. -/
def HasDecay : Prop :=
  ∀ γ : SL(2, ℤ), ∃ C : ℝ, ∀ τ : ℍ, ‖h (γ • τ)‖ * (1 + τ.im ^ 2) ≤ C

variable (γ) in
lemma continuous_smul_sl : Continuous fun τ : ℍ ↦ γ • τ := by
  simp only [MulAction.compHom_smul_def]
  exact continuous_const_smul <| mapGL ℝ γ

lemma continuous_rowVal (hcont : Continuous h) : Continuous fun τ ↦ rowVal h L τ v := by
  by_cases hv : ∃ γ : SL(2, ℤ), reduceMod L (row γ) = v
  · simp only [rowVal, dite_eq_left hv]
    exact hcont.comp <| continuous_smul_sl _
  · simp only [rowVal, dite_eq_right hv]
    exact continuous_const

variable (σ x) in
lemma measurable_latticeTerm : Measurable fun τ : ℍ ↦ latticeTerm τ σ x := by
  have hcoe : Continuous ((↑) : ℍ → ℂ) := UpperHalfPlane.continuous_coe
  have hcont : Continuous fun τ : ℍ ↦ ‖(x 0 : ℂ) * τ + x 1‖ := by fun_prop
  exact hcont.measurable.pow_const _

lemma measurable_cosetSum (hcont : Continuous h) : Measurable fun τ ↦ cosetSum h L τ σ :=
  Measurable.tsum fun ξ ↦ (continuous_rowVal hcont).measurable.mul <|
    Complex.measurable_ofReal.comp <| measurable_latticeTerm σ ξ.1

lemma integrable_stripFun_of_hasDecay (hcont : Continuous h) (hdec : HasDecay h)
    (hσ : σ ∈ Ioc (1 : ℝ) 2) : Integrable (stripFun h σ) := by
  rcases hdec 1 with ⟨C₁, hC₁⟩
  have hC : ∀ τ : ℍ, ‖h τ‖ * (1 + τ.im ^ 2) ≤ C₁ := fun τ ↦ by
    simpa only [one_smul] using hC₁ τ
  refine integrable_stripFun hcont (C := C₁) (fun τ ↦ ?_) (fun τ ↦ ?_) hσ <;>
    nlinarith [norm_nonneg (h τ), hC τ]

variable (τ v) in
lemma rowVal_ofReal_eq (hu : ∀ τ, 0 ≤ u τ) :
    ∃ r : ℝ, 0 ≤ r ∧ rowVal (fun τ ↦ (u τ : ℂ)) L τ v = r := by
  by_cases hv : ∃ γ : SL(2, ℤ), reduceMod L (row γ) = v
  · exact ⟨u (hv.choose • τ), hu _, by rw [rowVal, dite_eq_left hv]⟩
  · exact ⟨0, le_rfl, by rw [rowVal, dite_eq_right hv, Complex.ofReal_zero]⟩

lemma re_rowVal_nonneg (hu : ∀ τ, 0 ≤ u τ) : 0 ≤ (rowVal (fun τ ↦ (u τ : ℂ)) L τ v).re := by
  rcases rowVal_ofReal_eq τ v hu with ⟨r, hr, he⟩
  rwa [he, Complex.ofReal_re]

lemma ofReal_re_rowVal (hu : ∀ τ, 0 ≤ u τ) :
    (((rowVal (fun τ ↦ (u τ : ℂ)) L τ v).re : ℝ) : ℂ) = rowVal (fun τ ↦ (u τ : ℂ)) L τ v := by
  rcases rowVal_ofReal_eq τ v hu with ⟨r, -, he⟩
  rw [he, Complex.ofReal_re]

lemma cosetSum_eq_ofReal (hu : ∀ τ, 0 ≤ u τ) : cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ =
    ((∑' ξ : gammaSet 1 1 0,
      (rowVal (fun τ ↦ (u τ : ℂ)) L τ (reduceMod L ξ.1)).re * latticeTerm τ σ ξ.1 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum, cosetSum]
  exact tsum_congr fun ξ ↦ by rw [Complex.ofReal_mul, ofReal_re_rowVal hu]

lemma ofReal_re_cosetSum (hu : ∀ τ, 0 ≤ u τ) :
    (((cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re : ℝ) : ℂ) = cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ := by
  rw [cosetSum_eq_ofReal hu, Complex.ofReal_re]

lemma re_cosetSum_nonneg (hu : ∀ τ, 0 ≤ u τ) : 0 ≤ (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := by
  rw [cosetSum_eq_ofReal hu, Complex.ofReal_re]
  exact tsum_nonneg fun ξ ↦ mul_nonneg (re_rowVal_nonneg hu) (latticeTerm_nonneg τ σ _)

variable [NeZero L]

variable (w) in
lemma exists_lift_unit :
    ∃ δ : SL(2, ℤ), ((δ 1 0 : ℤ) : ZMod L) = 0 ∧ ((δ 1 1 : ℤ) : ZMod L) = w := by
  have hcop : IsCoprime ((![(L : ℤ), ((w : ZMod L).val : ℤ)] : Fin 2 → ℤ) 0)
      ((![(L : ℤ), ((w : ZMod L).val : ℤ)] : Fin 2 → ℤ) 1) :=
    (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime w)).symm
  rcases bottom_row_surj hcop with ⟨δ, -, hδ⟩
  have h0 : δ 1 0 = L := congrFun hδ 0
  have h1 : δ 1 1 = ((w : ZMod L).val : ℤ) := congrFun hδ 1
  exact ⟨δ, by simp [h0], by simp [h1]⟩

lemma rowVal_unit_smul (hh : HasNebentypus h ω) :
    rowVal h L τ ((w : ZMod L) • v) = (ω w : ℂ) * rowVal h L τ v := by
  by_cases hv : ∃ γ : SL(2, ℤ), reduceMod L (row γ) = v
  · rcases hv with ⟨γ, rfl⟩
    rcases exists_lift_unit w with ⟨δ, hc, hd⟩
    rw [← hd, ← reduceMod_row_mul hc, rowVal_reduceMod_row hh, rowVal_reduceMod_row hh, mul_smul,
      hh δ w hc hd]
  · have hv' : ¬∃ γ : SL(2, ℤ), reduceMod L (row γ) = (w : ZMod L) • v := by
      rintro ⟨γ, hγ⟩
      rcases exists_lift_unit w⁻¹ with ⟨δ, hc, hd⟩
      refine hv ⟨δ * γ, ?_⟩
      rw [reduceMod_row_mul hc, hγ, hd, smul_smul, Units.inv_mul, one_smul]
    rw [rowVal, dite_eq_right hv', rowVal, dite_eq_right hv, mul_zero]

lemma rowVal_nsmul (hh : HasNebentypus h ω) : rowVal h L τ (reduceMod L (g • ξ.1)) =
    (MulChar.ofUnitHom ω : MulChar (ZMod L) ℂ) (g : ZMod L) * rowVal h L τ (reduceMod L ξ.1) := by
  by_cases hg : IsUnit (g : ZMod L)
  · rcases hg with ⟨w, hw⟩
    rw [reduceMod_nsmul, ← hw, rowVal_unit_smul hh, MulChar.ofUnitHom_coe]
  · rw [MulChar.map_nonunit _ hg, zero_mul, rowVal, dite_eq_right]
    rintro ⟨γ, hγ⟩
    have hgc : ¬g.Coprime L := fun hc ↦ hg ((ZMod.isUnit_iff_coprime g L).mpr hc)
    rcases Nat.exists_prime_and_dvd hgc with ⟨p, hp, hpd⟩
    rcases Nat.dvd_gcd_iff.mp hpd with ⟨hpg, hpL⟩
    have hdvd : ∀ j, (p : ℤ) ∣ row γ j := fun j ↦ by
      have hj : ((row γ j : ℤ) : ZMod L) = ((g • ξ.1) j : ℤ) := congrFun hγ j
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hj
      have h1 : (p : ℤ) ∣ (g • ξ.1) j - row γ j := (Int.natCast_dvd_natCast.mpr hpL).trans hj
      have h2 : (p : ℤ) ∣ (g • ξ.1) j := by
        simpa using (Int.natCast_dvd_natCast.mpr hpg).mul_right (ξ.1 j)
      simpa using dvd_sub h2 h1
    exact (Nat.prime_iff_prime_int.mp hp).not_isUnit
      ((bottom_row_coprime γ).isUnit_of_dvd' (hdvd 0) (hdvd 1))

lemma sum_rowVal_eq_zero (hh : HasNebentypus h ω) (hω : ω ≠ 1) : ∑ v, rowVal h L τ v = 0 := by
  have hex : ∃ w : (ZMod L)ˣ, ω w ≠ 1 := by
    by_contra hn
    push Not at hn
    exact hω <| MonoidHom.ext hn
  rcases hex with ⟨w, hw⟩
  have hsum : ∑ v, rowVal h L τ ((w : ZMod L) • v) = ∑ v, rowVal h L τ v :=
    Equiv.sum_comp (MulAction.toPerm w) (rowVal h L τ)
  simp_rw [rowVal_unit_smul hh, ← Finset.mul_sum] at hsum
  have hne : (ω w : ℂ) ≠ 1 := fun h1 ↦ hw (Units.ext h1)
  have h0 : ((ω w : ℂ) - 1) * ∑ v, rowVal h L τ v = 0 := by
    rw [sub_mul, hsum, one_mul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

lemma exists_sum_norm_rowVal_le (hh : HasNebentypus h ω) (hdec : HasDecay h) :
    ∃ C : ℝ, ∀ τ : ℍ, (∑ v, ‖rowVal h L τ v‖) * (1 + τ.im ^ 2) ≤ C := by
  have hv : ∀ v : Fin 2 → ZMod L, ∃ C : ℝ, ∀ τ : ℍ, ‖rowVal h L τ v‖ * (1 + τ.im ^ 2) ≤ C := by
    intro v
    by_cases hv : ∃ γ : SL(2, ℤ), reduceMod L (row γ) = v
    · rcases hv with ⟨γ, rfl⟩
      rcases hdec γ with ⟨C, hC⟩
      exact ⟨C, fun τ ↦ rowVal_reduceMod_row hh ▸ hC τ⟩
    · exact ⟨0, fun τ ↦ by rw [rowVal, dite_eq_right hv, norm_zero, zero_mul]⟩
  choose C hC using hv
  exact ⟨∑ v, C v, fun τ ↦ (Finset.sum_mul _ _ _).trans_le <| Finset.sum_le_sum fun v _ ↦ hC v τ⟩

lemma norm_mul_cosetSum_le (hτ : τ ∈ fd) (hσ : σ ∈ Ioc (1 : ℝ) 2) {C : ℝ}
    (hC : (∑ v, ‖rowVal h L τ v‖) * (1 + τ.im ^ 2) ≤ C) :
    ‖((τ.im ^ σ : ℝ) : ℂ) * cosetSum h L τ σ‖ ≤ C * (16 * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * σ))) := by
  have him : 0 < τ.im := τ.im_pos
  have hS : 0 ≤ ∑' x : Fin 2 → ℤ, latticeTerm τ σ x := tsum_nonneg <| latticeTerm_nonneg τ σ
  have hv : 0 ≤ ∑ v, ‖rowVal h L τ v‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h4 : τ.im ^ σ * ‖cosetSum h L τ σ‖ ≤ (1 + τ.im ^ 2) * ((∑ v, ‖rowVal h L τ v‖) *
      ∑' x : Fin 2 → ℤ, latticeTerm τ σ x) :=
    mul_le_mul (rpow_le_one_add_sq him hσ) (norm_tsum_coprime_le τ (rowVal h L τ) hσ.1)
      (norm_nonneg _) (by positivity)
  refine h4.trans ?_
  have h5 : (1 + τ.im ^ 2) * ((∑ v, ‖rowVal h L τ v‖) * ∑' x : Fin 2 → ℤ, latticeTerm τ σ x) =
      ((∑ v, ‖rowVal h L τ v‖) * (1 + τ.im ^ 2)) * ∑' x : Fin 2 → ℤ, latticeTerm τ σ x := by
    ring1
  rw [h5]
  exact mul_le_mul hC (tsum_latticeTerm_le_of_mem_fd hτ hσ) hS
    ((mul_nonneg hv (by positivity)).trans hC)

/-- **The Rankin–Selberg integral of a function with a nontrivial character has no pole at
`σ = 1`.** If `h` is continuous, decays at every cusp and transforms under `Γ₀(L)` through a
nontrivial character `ω`, then `(σ - 1) ∫_{strip} h(τ) (Im τ) ^ σ dμ(τ) → 0` as `σ → 1⁺`. -/
lemma tendsto_sub_one_mul_integral_stripFun (hcont : Continuous h) (hh : HasNebentypus h ω)
    (hdec : HasDecay h) (hω : ω ≠ 1) :
    Tendsto (fun σ : ℝ ↦ ((σ - 1 : ℝ) : ℂ) * ∫ τ, stripFun h σ τ) (𝓝[>] 1) (𝓝 0) := by
  rcases exists_sum_norm_rowVal_le hh hdec with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (mul_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    (by positivity)).trans (hC UpperHalfPlane.I)
  have hfin : IsFiniteMeasure ((volume : Measure ℍ).restrict fdo) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono fdo_subset_fd).trans_lt volume_fd_lt_top⟩
  -- dominated convergence on `𝒟ᵒ`
  have hlim : Tendsto (fun σ : ℝ ↦ ∫ τ in fdo, ((σ - 1 : ℝ) : ℂ) *
      (((τ.im ^ σ : ℝ) : ℂ) * cosetSum h L τ σ)) (𝓝[>] 1) (𝓝 (∫ _ in fdo, (0 : ℂ))) := by
    refine tendsto_integral_filter_of_norm_le_const ?_ ⟨C * (16 * 5), ?_⟩ ?_
    · refine .of_forall fun σ ↦ ?_
      have him : Measurable fun τ : ℍ ↦ ((τ.im ^ σ : ℝ) : ℂ) := by
        refine Complex.measurable_ofReal.comp (Measurable.pow_const ?_ _)
        exact Continuous.measurable (by fun_prop)
      exact ((him.mul (measurable_cosetSum hcont)).const_mul _).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2),
        eventually_sub_one_mul_tsum_norm_rpow_le] with σ hσ h5
      refine ae_restrict_of_forall_mem isOpen_fdo.measurableSet fun τ hτ ↦ ?_
      have hσ1 : 0 ≤ σ - 1 := by linarith [hσ.1]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ1]
      refine (mul_le_mul_of_nonneg_left (norm_mul_cosetSum_le (fdo_subset_fd hτ) hσ (hC τ))
        hσ1).trans ?_
      have h3 : (σ - 1) * (C * (16 * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * σ)))) =
          C * (16 * ((σ - 1) * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * σ)))) := by
        ring1
      rw [h3]
      gcongr
    · refine ae_of_all _ fun τ ↦ ?_
      have hlim₀ : Tendsto (fun σ : ℝ ↦ ((σ - 1 : ℝ) : ℂ) * ∑' ξ : gammaSet 1 1 0,
          rowVal h L τ (reduceMod L ξ.1) * (latticeTerm τ σ ξ.1 : ℂ)) (𝓝[>] 1) (𝓝 0) :=
        tendsto_sub_one_mul_tsum_coprime τ (fun n ↦ DirichletCharacter.norm_le_one _ _) (by simp)
          (fun _ _ _ ↦ rowVal_nsmul hh) (sum_rowVal_eq_zero hh hω)
      have him :
          Tendsto (fun σ : ℝ ↦ ((τ.im ^ σ : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 ((τ.im ^ (1 : ℝ) : ℝ) : ℂ)) := by
        refine (Complex.continuous_ofReal.tendsto _).comp (Tendsto.mono_left ?_ nhdsWithin_le_nhds)
        exact (Real.continuousAt_const_rpow τ.im_pos.ne').tendsto
      have hmul : Tendsto (fun σ : ℝ ↦ ((τ.im ^ σ : ℝ) : ℂ) * (((σ - 1 : ℝ) : ℂ) *
          ∑' ξ : gammaSet 1 1 0, rowVal h L τ (reduceMod L ξ.1) * (latticeTerm τ σ ξ.1 : ℂ)))
          (𝓝[>] 1) (𝓝 0) := by
        simpa only [mul_zero] using him.mul hlim₀
      refine hmul.congr fun σ ↦ ?_
      rw [cosetSum]
      ring1
  have hlim' : Tendsto (fun σ : ℝ ↦ (1 / 2 : ℂ) * ∫ τ in fdo, ((σ - 1 : ℝ) : ℂ) *
      (((τ.im ^ σ : ℝ) : ℂ) * cosetSum h L τ σ)) (𝓝[>] 1) (𝓝 0) := by
    simpa only [integral_zero, mul_zero] using hlim.const_mul (1 / 2 : ℂ)
  refine hlim'.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ
  rw [integral_stripFun_eq_setIntegral_cosetSum hh (integrable_stripFun_of_hasDecay hcont hdec hσ),
    integral_const_mul]
  ring1

lemma le_re_cosetSum (hu : ∀ τ, 0 ≤ u τ)
    (hh : HasNebentypus (fun τ ↦ (u τ : ℂ)) (1 : (ZMod L)ˣ →* ℂˣ)) (hσ : σ ∈ Ioc (1 : ℝ) 2) :
    u τ * ∑' m : Fin 2 → ℤ, latticeTerm τ σ (liftMod (reduceMod L (row 1)) + (L : ℤ) • m) ≤
      π ^ 2 / 6 * (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := by
  let c : ℕ → ℂ := fun n ↦
    (MulChar.ofUnitHom (1 : (ZMod L)ˣ →* ℂˣ) : MulChar (ZMod L) ℂ) (n : ZMod L)
  have hE : ∑ v, rowVal (fun τ ↦ (u τ : ℂ)) L τ v *
      ((∑' m : Fin 2 → ℤ, latticeTerm τ σ (liftMod v + (L : ℤ) • m) : ℝ) : ℂ) =
      (∑' n : ℕ, c n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)) * cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ :=
    (hasSum_mul_latticeTerm τ _ hσ.1).tsum_eq.symm.trans
      (tsum_mul_latticeTerm_eq_mul_tsum_coprime τ _ hσ.1 fun _ _ _ ↦ rowVal_nsmul hh)
  have hD : ‖∑' n : ℕ, c n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ ≤ π ^ 2 / 6 :=
    norm_tsum_mul_rpow_le (fun n ↦ DirichletCharacter.norm_le_one _ _) hσ.1.le
  have hnormE : ‖cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ‖ = (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := by
    rw [← ofReal_re_cosetSum hu, Complex.norm_real, Complex.ofReal_re,
      Real.norm_of_nonneg (re_cosetSum_nonneg hu)]
  have hZ : ∀ v : Fin 2 → ZMod L, 0 ≤ ∑' m : Fin 2 → ℤ, latticeTerm τ σ (liftMod v + (L : ℤ) • m) :=
    fun v ↦ tsum_nonneg fun m ↦ latticeTerm_nonneg τ σ _
  have hlow :
      u τ * ∑' m : Fin 2 → ℤ, latticeTerm τ σ (liftMod (reduceMod L (row 1)) + (L : ℤ) • m) ≤
        (∑ v, rowVal (fun τ ↦ (u τ : ℂ)) L τ v * ((∑' m : Fin 2 → ℤ,
          latticeTerm τ σ (liftMod v + (L : ℤ) • m) : ℝ) : ℂ)).re := by
    have hval : rowVal (fun τ ↦ (u τ : ℂ)) L τ (reduceMod L (row 1)) = u τ := by
      rw [rowVal_reduceMod_row hh, one_smul]
    simp only [Complex.re_sum, Complex.re_mul_ofReal]
    refine le_trans (le_of_eq ?_) <| Finset.single_le_sum
      (fun v _ ↦ mul_nonneg (re_rowVal_nonneg hu) (hZ v)) (Finset.mem_univ (reduceMod L (row 1)))
    simp only [hval, Complex.ofReal_re]
  refine hlow.trans ((Complex.re_le_norm _).trans ?_)
  rw [hE, norm_mul]
  refine (mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans_eq ?_
  rw [hnormE]

/-- **The Rankin–Selberg integral of a nonnegative function has a pole at `σ = 1`.** If `u ≥ 0` is
continuous, decays at every cusp, is invariant under `Γ₀(L)` and is positive at a point of `𝒟ᵒ`,
then `(σ - 1) ∫_{strip} u(τ) (Im τ) ^ σ dμ(τ)` stays above a positive constant as `σ → 1⁺`. -/
lemma exists_le_sub_one_mul_re_integral_stripFun (hucont : Continuous u) (hu : ∀ τ, 0 ≤ u τ)
    (hh : HasNebentypus (fun τ ↦ (u τ : ℂ)) (1 : (ZMod L)ˣ →* ℂˣ))
    (hdec : HasDecay fun τ ↦ (u τ : ℂ)) {τ₀ : ℍ} (hτ₀ : τ₀ ∈ fdo) (hpos : 0 < u τ₀) :
    ∃ c > 0, ∀ᶠ σ : ℝ in 𝓝[>] 1, c ≤ (σ - 1) * (∫ τ, stripFun (fun τ ↦ (u τ : ℂ)) σ τ).re := by
  have hcont : Continuous fun τ ↦ (u τ : ℂ) := Complex.continuous_ofReal.comp hucont
  rcases exists_sum_norm_rowVal_le hh hdec with ⟨C₀, hC₀⟩
  have hL : (1 : ℝ) ≤ L := Nat.one_le_cast.mpr <| NeZero.pos L
  let a : Fin 2 → ℤ := liftMod (reduceMod L (row 1))
  let ρ : ℝ := ‖(τ₀ : ℂ)‖ + 1
  have hρ : 0 < ρ := by positivity
  let C : ℝ := (|a 0| + L) * ρ + |a 1| + L
  have hC1 : 1 ≤ C := by
    have h1 : (0 : ℝ) ≤ ((|a 0| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (a 0)
    have h2 : (0 : ℝ) ≤ ((|a 1| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (a 1)
    simp only [C]
    nlinarith
  have hcoe : Continuous fun τ : ℍ ↦ ‖(τ : ℂ)‖ := continuous_norm.comp UpperHalfPlane.continuous_coe
  let B : Set ℍ := fdo ∩ ({τ | u τ₀ / 2 < u τ} ∩ {τ | ‖(τ : ℂ)‖ < ρ})
  have hBopen : IsOpen B := isOpen_fdo.inter
    ((isOpen_lt continuous_const hucont).inter (isOpen_lt hcoe continuous_const))
  have hBsub : B ⊆ fdo := inter_subset_left
  have hτ₀B : τ₀ ∈ B := ⟨hτ₀, half_lt_self hpos, lt_add_one ‖(τ₀ : ℂ)‖⟩
  have hfin : (volume : Measure ℍ) fdo ≠ ⊤ :=
    ((measure_mono fdo_subset_fd).trans_lt volume_fd_lt_top).ne
  have hBfin : (volume : Measure ℍ) B ≠ ⊤ := ((measure_mono hBsub).trans_lt hfin.lt_top).ne
  have hκ : 0 < (volume : Measure ℍ).real B :=
    ENNReal.toReal_pos (hBopen.measure_pos volume ⟨τ₀, hτ₀B⟩).ne' hBfin
  have hπ : 0 < π ^ 2 / 6 := by positivity
  let K : ℝ := 1 / 4 * ((π ^ 2 / 6)⁻¹ * (u τ₀ / 2 * C ^ (-4 : ℝ)))
  have hK : 0 < K := by positivity
  -- the integrand on `B`
  have hB : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ τ ∈ B, K * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1) ≤
      τ.im ^ σ * (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := by
    intro σ hσ τ hτ
    have hre : 0 ≤ (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := re_cosetSum_nonneg hu
    have hlat : C ^ (-(2 * σ)) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1) ≤
        ∑' m : Fin 2 → ℤ, latticeTerm τ σ (a + (L : ℤ) • m) :=
      le_tsum_latticeTerm_add_smul τ a (liftMod_nonneg _ 0) hσ.1 (le_of_lt hτ.2.2)
    have hζ : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1) := tsum_nonneg fun n ↦ by positivity
    have hC4 : C ^ (-4 : ℝ) ≤ C ^ (-(2 * σ)) :=
      Real.rpow_le_rpow_of_exponent_le hC1 (by linarith [hσ.2])
    have hum : u τ₀ / 2 ≤ u τ := le_of_lt hτ.2.1
    have hlow : u τ₀ / 2 * (C ^ (-4 : ℝ) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1)) ≤
        π ^ 2 / 6 * (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := by
      refine le_trans ?_ (le_re_cosetSum hu hh hσ)
      refine mul_le_mul hum ?_ (by positivity) (hu τ)
      exact (mul_le_mul_of_nonneg_right hC4 hζ).trans hlat
    have him : (1 / 2 : ℝ) ≤ τ.im := (half_le_r (fdo_subset_fd hτ.1)).trans (min_le_left _ _)
    have him4 : (1 / 4 : ℝ) ≤ τ.im ^ σ := by
      have h1 : (1 / 2 : ℝ) ^ (2 : ℝ) ≤ (1 / 2 : ℝ) ^ σ :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hσ.2
      have h2 : (1 / 2 : ℝ) ^ σ ≤ τ.im ^ σ :=
        Real.rpow_le_rpow (by norm_num) him (by linarith [hσ.1])
      have h3 : (1 / 2 : ℝ) ^ (2 : ℝ) = 1 / 4 := by rw [Real.rpow_two]; norm_num
      linarith
    have hEre : (π ^ 2 / 6)⁻¹ * (u τ₀ / 2 * (C ^ (-4 : ℝ) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1))) ≤
        (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := by
      rw [inv_mul_le_iff₀ hπ]
      exact hlow
    have hKeq : K * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1) = 1 / 4 * ((π ^ 2 / 6)⁻¹ *
        (u τ₀ / 2 * (C ^ (-4 : ℝ) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1)))) := by
      simp only [K]
      ring1
    rw [hKeq]
    exact mul_le_mul him4 hEre (by positivity) (by positivity)
  -- integrability on `𝒟ᵒ`
  have hmeasg :
      ∀ σ : ℝ, Measurable fun τ : ℍ ↦ τ.im ^ σ * (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re :=
    fun σ ↦ by
      have him : Measurable fun τ : ℍ ↦ τ.im ^ σ :=
        (Continuous.measurable (by fun_prop)).pow_const σ
      exact him.mul <| Complex.measurable_re.comp <| measurable_cosetSum hcont
  have hIg : ∀ σ ∈ Ioc (1 : ℝ) 2, IntegrableOn (fun τ : ℍ ↦
      τ.im ^ σ * (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re) fdo := fun σ hσ ↦ by
    refine Measure.integrableOn_of_bounded hfin (hmeasg σ).aestronglyMeasurable
      (M := C₀ * (16 * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * σ))))
      (ae_restrict_of_forall_mem isOpen_fdo.measurableSet fun τ hτ ↦ ?_)
    rw [← Complex.norm_real, Complex.ofReal_mul, ofReal_re_cosetSum hu]
    exact norm_mul_cosetSum_le (fdo_subset_fd hτ) hσ (hC₀ τ)
  have hinteq : ∀ σ ∈ Ioc (1 : ℝ) 2, (∫ τ, stripFun (fun τ ↦ (u τ : ℂ)) σ τ).re =
      1 / 2 * ∫ τ in fdo, τ.im ^ σ * (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := fun σ hσ ↦ by
    rw [integral_stripFun_eq_setIntegral_cosetSum hh
      (integrable_stripFun_of_hasDecay hcont hdec hσ)]
    have h1 : ∀ τ : ℍ, ((τ.im ^ σ : ℝ) : ℂ) * cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ =
        ((τ.im ^ σ * (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re : ℝ) : ℂ) := fun τ ↦ by
      rw [Complex.ofReal_mul, ofReal_re_cosetSum hu]
    simp_rw [h1]
    rw [integral_complex_ofReal]
    norm_num
  refine ⟨1 / 2 * (K * (volume : Measure ℍ).real B) * (1 / 4), by positivity, ?_⟩
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2),
    tendsto_sub_one_mul_tsum_nat_rpow.eventually (lt_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))]
    with σ hσ h4
  have hσ1 : 0 ≤ σ - 1 := by linarith [hσ.1]
  have hlow : (K * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1)) * (volume : Measure ℍ).real B ≤
      ∫ τ in fdo, τ.im ^ σ * (cosetSum (fun τ ↦ (u τ : ℂ)) L τ σ).re := by
    refine (setIntegral_ge_of_const_le_real hBopen.measurableSet hBfin (hB σ hσ)
      ((hIg σ hσ).mono_set hBsub)).trans ?_
    refine setIntegral_mono_set (hIg σ hσ) ?_ (ae_of_all _ hBsub)
    refine ae_restrict_of_forall_mem isOpen_fdo.measurableSet fun τ _ ↦ ?_
    exact mul_nonneg (Real.rpow_nonneg τ.im_pos.le σ) (re_cosetSum_nonneg hu)
  rw [hinteq σ hσ]
  have h5 : 1 / 2 * (K * (volume : Measure ℍ).real B) * (1 / 4) ≤ (σ - 1) * (1 / 2) *
      ((K * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1)) * (volume : Measure ℍ).real B) := by
    have hpos' : 0 ≤ 1 / 2 * (K * (volume : Measure ℍ).real B) := by positivity
    refine (mul_le_mul_of_nonneg_left (le_of_lt h4) hpos').trans_eq ?_
    ring1
  refine h5.trans ((mul_le_mul_of_nonneg_left hlow
    (mul_nonneg hσ1 (by norm_num : (0 : ℝ) ≤ 1 / 2))).trans_eq ?_)
  ring1

end RankinSelberg
