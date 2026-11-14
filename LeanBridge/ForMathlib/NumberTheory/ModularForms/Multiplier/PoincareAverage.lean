import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareConvergence
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Averaging over `⟨T⟩ \ SL(2, ℤ)`: Eisenstein series and Poincaré series

A function with the modular transformation property of modular forms of weight `k ∈ ℤ` is obtained
by averaging over the group action (LMFDB `mf.gl2.history.poincare`): for a `1`-periodic function
`h` on the upper half-plane,
`f(z) = ∑_{γ ∈ ⟨T⟩ \ Γ} h(γz) (cz + d)^{-k}`, where `Γ = SL(2, ℤ)`, `T = !![1, 1; 0, 1]`, and the
sum runs over the right cosets `⟨T⟩γ`. The term `h(γz) (cz + d)^{-k}` depends only on the coset,
since `T` translates by `1` and has denominator `1`. This file defines the average, as an
unconditional sum (`tsum`, `0` when the series does not converge) over the cosets, and proves the
following.

* The average has the transformation property `f(γz) = (cz + d)^k f(z)` for every `γ ∈ Γ`. The
  series converges absolutely in weight `k ≥ 3` when `h` is bounded on the orbit of `z`, and its
  sum is `0` in odd weight, where the terms at `γ` and `-γ` cancel.
* For `h = 1` it is the Eisenstein series `∑_{(c, d) = 1} (cz + d)^{-k}`, which is Mathlib's
  `eisensteinSeries` of level `1` and equals `2 E_k`. The subgroup `⟨T⟩` does not contain `-I`,
  while the knowl `cmf.eisenstein` sums over the cosets of `Γ_∞ = ±⟨T⟩`.
* For `h(z) = e^{2πinz}`, `n ∈ ℤ`, which is `1`-periodic, it is twice the Poincaré series
  `P_k^n(Γ, 1; z; ∞)` of `specialfunction.poincare` (LeanBridge's `ModularForm.poincareSeries`), in
  even weight `k ≥ 3`, for the same reason.
* For `2 ≤ n ≤ k - 2`, the series `∑_{γ ∈ Γ} (γz)^{-n} (cz + d)^{-k}` over the whole group
  converges absolutely and has the transformation property. It is the average of the `1`-periodic
  function `w ↦ ∑_{m ∈ ℤ} (w + m)^{-n}`, so for it dividing by the action of `T` is not necessary.
  It is necessary for `h = 1`, where the terms at the powers of `T` are all `1`.

## Main definitions

* `ModularForm.averageTerm`, `ModularForm.averageSeries` (LMFDB `mf.gl2.history.poincare`): the
  average of `h` over `⟨T⟩ \ Γ`.
* `ModularForm.fullAverageSeries` (LMFDB `mf.gl2.history.poincare`): the series
  `∑_{γ ∈ Γ} (γz)^{-n} (cz + d)^{-k}`.

## Main results

* `ModularForm.averageSeries_smul`: the transformation property of the average.
* `ModularForm.summable_norm_averageTerm`: absolute convergence of the average in weight `k ≥ 3`,
  for `h` bounded on the orbit of `z`.
* `ModularForm.averageSeries_eq_zero_of_odd`: the average vanishes in odd weight.
* `ModularForm.averageSeries_one`, `ModularForm.averageSeries_one_eq_E`: for `h = 1`, the average is
  the Eisenstein series `∑_{(c, d) = 1} (cz + d)^{-k} = 2 E_k`.
* `ModularForm.cexp_smul_T`: `e^{2πinz}` is `1`-periodic.
* `ModularForm.averageSeries_cexp`: for `h(z) = e^{2πinz}`, the average is twice the Poincaré
  series.
* `ModularForm.summable_norm_averageTerm_zpow`: absolute convergence of `∑_{γ ∈ Γ}` for
  `2 ≤ n ≤ k - 2`.
* `ModularForm.fullAverageSeries_smul`: its transformation property.
* `ModularForm.tsum_zpow_smul_T`: `w ↦ ∑_{m ∈ ℤ} (w + m)^{-n}` is `1`-periodic.
* `ModularForm.fullAverageSeries_eq_averageSeries`: the series over `Γ` is the average of
  `w ↦ ∑_{m ∈ ℤ} (w + m)^{-n}`.
* `ModularForm.not_summable_averageTerm_one`: the sum of `(cz + d)^{-k}` over all of `Γ` diverges.

## References

* H. Cohen and F. Strömberg, *Modular forms: a classical approach*, Graduate Studies in
  Mathematics 179, AMS, 2017.
* H. Cohen, *An introduction to modular forms*, arXiv:1809.10907: the series over `Γ` for
  `2 ≤ n ≤ k - 2`.
* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular forms (Durham,
  1983)*, Ellis Horwood, 1984, 197–249: the series over `Γ` and the periods of cusp forms.
-/

open Matrix SpecialLinearGroup ModularGroup EisensteinSeries QuotientGroup Complex

open UpperHalfPlane hiding I

open scoped MatrixGroups ModularForm Real

local notation "𝒬" => Quotient (rightRel (Subgroup.zpowers T))

namespace ModularGroup

variable {γ γ' : SL(2, ℤ)}

lemma mem_zpowers_T_iff : γ ∈ Subgroup.zpowers T ↔ γ 1 0 = 0 ∧ γ 1 1 = 1 := by
  refine ⟨?_, fun ⟨h10, h11⟩ ↦ ⟨γ 0 1, ?_⟩⟩
  · rintro ⟨m, rfl⟩
    simp [coe_T_zpow]
  · have h00 : γ 0 0 = 1 := by
      simpa [h10, h11] using γ.fin_two_mul_sub_mul_eq_one
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, h00, h10, h11]

lemma rightRel_zpowers_T_iff : rightRel (Subgroup.zpowers T) γ γ' ↔ γ' 1 = γ 1 := by
  rw [rightRel_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Subgroup.mem_zpowers_iff.mp h with ⟨m, hm⟩
    rw [← T_pow_mul_apply_one m γ, hm, inv_mul_cancel_right]
  · have h1 : (γ' * γ⁻¹) 1 = (1 : SL(2, ℤ)) 1 := by
      rw [← mul_inv_cancel γ, γ'.coe_mul, γ.coe_mul, Matrix.mul_apply_eq_vecMul,
        Matrix.mul_apply_eq_vecMul, h]
    exact mem_zpowers_T_iff.mpr ⟨by simpa using congrFun h1 0, by simpa using congrFun h1 1⟩

lemma mem_zpowers_T_or_neg_mem (hγ : γ 1 0 = 0) :
    γ ∈ Subgroup.zpowers T ∨ -γ ∈ Subgroup.zpowers T := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  rw [hγ, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, h11⟩ | ⟨-, h11⟩
  · exact .inl (mem_zpowers_T_iff.mpr ⟨hγ, h11⟩)
  · exact .inr (mem_zpowers_T_iff.mpr ⟨by simp [hγ], by simp [h11]⟩)

lemma injective_T_zpow : Function.Injective fun m : ℤ ↦ T ^ m := by
  intro m m' hm
  simpa [coe_T_zpow] using congrArg (fun g : SL(2, ℤ) ↦ g 0 1) hm

variable (γ)

lemma S_mul_apply_zero : (S * γ) 0 = -γ 1 := by
  ext j
  simp [Matrix.mul_apply]

lemma S_mul_apply_one : (S * γ) 1 = γ 0 := by
  ext j
  simp [Matrix.mul_apply]

lemma denom_T_zpow_mul (m : ℤ) (z : ℍ) : denom (T ^ m * γ : SL(2, ℤ)) z = denom γ z := by
  rw [denom_apply, denom_apply, T_pow_mul_apply_one]

end ModularGroup

namespace ModularForm

lemma injective_bottomRow : Function.Injective fun q : 𝒬 ↦ q.out 1 := fun _ _ h ↦
  Quotient.out_equiv_out.mp (rightRel_zpowers_T_iff.mpr h.symm)

lemma exists_bottomRow_eq {v : Fin 2 → ℤ} (hv : IsCoprime (v 0) (v 1)) : ∃ q : 𝒬, q.out 1 = v := by
  rcases bottom_row_surj (R := ℤ) hv with ⟨g, -, hg⟩
  exact ⟨⟦g⟧, (rightRel_zpowers_T_iff.mp <| Quotient.exact <| Quotient.out_eq ⟦g⟧).symm.trans hg⟩

variable (h : ℍ → ℂ) (k : ℤ) (z : ℍ)

/-- The term `h(γz) (cz + d)^{-k}` at `γ = !![a, b; c, d] ∈ SL(2, ℤ)` of the average of a function
`h` on the upper half-plane over `⟨T⟩ \ SL(2, ℤ)` in weight `k` (LMFDB
`mf.gl2.history.poincare`). -/
noncomputable def averageTerm (γ : SL(2, ℤ)) : ℂ :=
  h (γ • z) * denom γ z ^ (-k)

/-- The **average** `∑_{γ ∈ ⟨T⟩ \ Γ} h(γz) (cz + d)^{-k}` of a function `h` on the upper
half-plane over the right cosets of `⟨T⟩` in `Γ = SL(2, ℤ)`, in weight `k` (LMFDB
`mf.gl2.history.poincare`). It is an unconditional sum (`tsum`, `0` when not summable) over the
cosets, each represented by a chosen element. For `1`-periodic `h` the terms do not depend on the
representatives, and the average has the transformation property of modular forms of weight `k`
(`ModularForm.averageSeries_smul`). The series converges absolutely in weight `k ≥ 3` when `h` is
bounded on the orbit of `z` (`ModularForm.summable_norm_averageTerm`). -/
noncomputable def averageSeries : ℂ :=
  ∑' q : 𝒬, averageTerm h k z q.out

lemma averageTerm_eq_slash (γ : SL(2, ℤ)) : averageTerm h k z γ = (h ∣[k] γ) z :=
  (SL_slash_apply h γ z).symm

variable {h}

lemma apply_T_zpow_smul (hh : ∀ w : ℍ, h (T • w) = h w) (m : ℤ) (w : ℍ) : h (T ^ m • w) = h w := by
  induction m using Int.induction_on generalizing w with
  | zero => simp
  | succ m ih => rw [zpow_add_one, mul_smul, ih, hh]
  | pred m ih => rw [zpow_sub_one, mul_smul, ih, ← hh (T⁻¹ • w), smul_inv_smul]

lemma averageTerm_T_zpow_mul (hh : ∀ w : ℍ, h (T • w) = h w) (m : ℤ) (γ : SL(2, ℤ)) :
    averageTerm h k z (T ^ m * γ) = averageTerm h k z γ := by
  rw [averageTerm, averageTerm, mul_smul, apply_T_zpow_smul hh, denom_T_zpow_mul]

lemma averageTerm_eq_of_rightRel (hh : ∀ w : ℍ, h (T • w) = h w) {γ γ' : SL(2, ℤ)}
    (hγ : rightRel (Subgroup.zpowers T) γ γ') : averageTerm h k z γ' = averageTerm h k z γ := by
  rcases Subgroup.mem_zpowers_iff.mp (rightRel_apply.mp hγ) with ⟨m, hm⟩
  have hγ' : T ^ m * γ = γ' := by
    rw [hm, inv_mul_cancel_right]
  rw [← hγ', averageTerm_T_zpow_mul k z hh]

lemma averageTerm_neg (γ : SL(2, ℤ)) : averageTerm h k z (-γ) = (-1) ^ k * averageTerm h k z γ := by
  have hden : denom (-γ : SL(2, ℤ)) z = -denom γ z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply, γ.coe_neg, Matrix.neg_apply,
      Matrix.neg_apply, Int.cast_neg, Int.cast_neg, neg_mul, ← neg_add]
  rw [averageTerm, averageTerm, SL_neg_smul, hden, neg_eq_neg_one_mul (denom _ _), mul_zpow,
    zpow_neg, ← inv_zpow, inv_neg_one]
  ring1

variable (h) in
lemma averageTerm_smul (γ δ : SL(2, ℤ)) :
    averageTerm h k (δ • z) γ = averageTerm h k z (γ * δ) * denom δ z ^ k := by
  rw [averageTerm_eq_slash, averageTerm_eq_slash, SlashAction.slash_mul,
    SL_slash_apply (h ∣[k] γ) δ z, mul_assoc, ← zpow_add₀ (denom_ne_zero _ z), neg_add_cancel,
    zpow_zero, mul_one]

lemma tsum_averageTerm_equiv (hh : ∀ w : ℍ, h (T • w) = h w) (φ : SL(2, ℤ) ≃ SL(2, ℤ))
    (hφ : ∀ a b, rightRel (Subgroup.zpowers T) a b ↔ rightRel (Subgroup.zpowers T) (φ a) (φ b)) :
    ∑' q : 𝒬, averageTerm h k z (φ q.out) = averageSeries h k z := by
  have hterm (q : 𝒬) :
      averageTerm h k z (φ q.out) = averageTerm h k z (Quotient.congr φ hφ q).out :=
    (averageTerm_eq_of_rightRel k z hh <| Quotient.exact <| by
      rw [Quotient.out_eq, ← Quotient.congr_mk φ hφ, Quotient.out_eq]).symm
  rw [tsum_congr hterm, (Quotient.congr φ hφ).tsum_eq fun q ↦ averageTerm h k z q.out,
    averageSeries]

/-- **The average has the modular transformation property** (LMFDB `mf.gl2.history.poincare`):
for a `1`-periodic `h`, `f(γz) = (cz + d)^k f(z)` for every `γ = !![a, b; c, d] ∈ SL(2, ℤ)`. The
average is a `tsum`, so this holds also where the series diverges, both sides being `0`. -/
lemma averageSeries_smul (hh : ∀ w : ℍ, h (T • w) = h w) (γ : SL(2, ℤ)) :
    averageSeries h k (γ • z) = denom γ z ^ k * averageSeries h k z := by
  have hγ : ∑' q : 𝒬, averageTerm h k z (q.out * γ) = averageSeries h k z := by
    simpa only [Equiv.coe_mulRight] using tsum_averageTerm_equiv k z hh (Equiv.mulRight γ)
      fun a b ↦ by
        rw [rightRel_apply, rightRel_apply, Equiv.coe_mulRight,
          show b * γ * (a * γ)⁻¹ = b * a⁻¹ by group]
  rw [averageSeries, tsum_congr fun q : 𝒬 ↦ averageTerm_smul h k z q.out γ, tsum_mul_right, hγ,
    mul_comm]

variable {k} in
/-- **The average converges absolutely in weight `k ≥ 3` when `h` is bounded on the orbit of `z`**
(LMFDB `mf.gl2.history.poincare`), in particular when `h` is bounded: the bottom rows `(c, d)` of
the cosets `⟨T⟩γ` are distinct, so the series is dominated by the Eisenstein series of weight
`k`. -/
lemma summable_norm_averageTerm (hk : 3 ≤ k) {C : ℝ} (hC : ∀ γ : SL(2, ℤ), ‖h (γ • z)‖ ≤ C) :
    Summable fun q : 𝒬 ↦ ‖averageTerm h k z q.out‖ := by
  refine ((summable_norm_eisSummand hk z).comp_injective injective_bottomRow).mul_left C
    |>.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun q ↦ ?_
  rw [averageTerm, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC q.out) (norm_nonneg _)

variable {k} in
/-- **In odd weight the average vanishes** (LMFDB `mf.gl2.history.poincare`): for a `1`-periodic
`h` and odd `k`, the terms at the cosets `⟨T⟩γ` and `⟨T⟩(-γ)`, which are distinct, are opposite,
so the sum is `0`. The Eisenstein series and the Poincaré series of the linked knowls have even
weight. -/
lemma averageSeries_eq_zero_of_odd (hh : ∀ w : ℍ, h (T • w) = h w) (hk : Odd k) :
    averageSeries h k z = 0 := by
  have hneg : ∑' q : 𝒬, averageTerm h k z (-q.out) = averageSeries h k z := by
    simpa only [Equiv.neg_apply] using tsum_averageTerm_equiv k z hh (Equiv.neg _) fun a b ↦ by
      rw [rightRel_apply, rightRel_apply, Equiv.neg_apply, inv_neg, neg_mul_neg]
  refine CharZero.eq_neg_self_iff.mp (hneg.symm.trans ?_)
  rw [averageSeries, ← tsum_neg]
  exact tsum_congr fun q ↦ by rw [averageTerm_neg, hk.neg_one_zpow, neg_one_mul]

/-! ### The Eisenstein series -/

/-- **For `h = 1` the average is the Eisenstein series** `∑_{(c, d) = 1} (cz + d)^{-k}` (LMFDB
`mf.gl2.history.poincare`), Mathlib's `eisensteinSeries` of level `1`: the bottom row `(c, d)`
identifies `⟨T⟩ \ SL(2, ℤ)` with the coprime pairs. -/
lemma averageSeries_one : averageSeries (fun _ ↦ 1) k z = eisensteinSeries (N := 1) 0 k z := by
  have hmem (q : 𝒬) : q.out 1 ∈ gammaSet 1 1 0 :=
    (mem_gammaSet_one _).mpr (bottom_row_coprime q.out)
  let e : 𝒬 ≃ gammaSet 1 1 0 := Equiv.ofBijective (fun q ↦ ⟨_, hmem q⟩)
    ⟨fun q q' hqq ↦ injective_bottomRow (congrArg Subtype.val hqq), fun v ↦ by
      rcases exists_bottomRow_eq ((mem_gammaSet_one v.1).mp v.2) with ⟨q, hq⟩
      exact ⟨q, Subtype.ext hq⟩⟩
  rw [eisensteinSeries, averageSeries, ← e.tsum_eq]
  refine tsum_congr fun q ↦ ?_
  rw [averageTerm, one_mul]
  rfl

/-- **For `h = 1` the average is `2 E_k`** (LMFDB `mf.gl2.history.poincare`): twice Mathlib's
normalised Eisenstein series of weight `l ≥ 3`, which is the sum over the cosets of `±⟨T⟩`. -/
lemma averageSeries_one_eq_E {l : ℕ} (hl : 3 ≤ l) : averageSeries (fun _ ↦ 1) l z = 2 * E hl z := by
  have hE : E hl z = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 l z :=
    rfl
  rw [averageSeries_one, hE, eisensteinSeriesSIF_apply, smul_eq_mul]
  ring1

/-! ### The Poincaré series -/

/-- **`e^{2πinz}` is `1`-periodic** (LMFDB `mf.gl2.history.poincare`): its value does not change
under `T : z ↦ z + 1`, for every `n ∈ ℤ`. -/
lemma cexp_smul_T (n : ℤ) (w : ℍ) : cexp (2 * π * I * n * ↑(T • w)) = cexp (2 * π * I * n * w) := by
  have hT : ((T • w : ℍ) : ℂ) = w + 1 := by
    simpa using coe_T_zpow_smul_eq (z := w) (n := 1)
  have h1 : cexp (2 * π * I * n) = 1 := by
    rw [show 2 * π * I * n = n * (2 * π * I) by ring1]
    exact exp_int_mul_two_pi_mul_I n
  rw [hT, mul_add, exp_add, mul_one, h1, mul_one]

variable {k} in
lemma summable_norm_averageTerm_cexp (hk : 3 ≤ k) (n : ℤ) :
    Summable fun q : 𝒬 ↦ ‖averageTerm (fun w ↦ cexp (2 * π * I * n * w)) k z q.out‖ := by
  rcases exists_max_im z with ⟨g, hg⟩
  refine summable_norm_averageTerm z hk (C := Real.exp (2 * π * |(n : ℝ)| * (g • z).im)) fun γ ↦ ?_
  rw [norm_exp, Real.exp_le_exp]
  have hre : (2 * π * I * n * ↑(γ • z)).re = -(2 * π * n * (γ • z).im) := by
    simp
  have hle : -((n : ℝ) * (γ • z).im) ≤ |(n : ℝ)| * (g • z).im := by
    nlinarith [neg_le_abs (n : ℝ), abs_nonneg (n : ℝ), hg γ, (γ • z).im_pos]
  rw [hre]
  nlinarith [Real.pi_pos]

local notation "𝒫" => Quotient (rightRel (cuspStabilizer (⊤ : Subgroup SL(2, ℤ)) 1))

lemma mem_cuspStabilizer_top_one_iff {g : (⊤ : Subgroup SL(2, ℤ))} :
    g ∈ cuspStabilizer ⊤ 1 ↔ (g : SL(2, ℤ)) 1 0 = 0 := by
  rw [mem_cuspStabilizer_iff]
  simp

variable {k} in
/-- **For `h(z) = e^{2πinz}` the average is twice the Poincaré series** (LMFDB
`mf.gl2.history.poincare`): in even weight `k ≥ 3` and for every `n ∈ ℤ`, the average of
`e^{2πinz}` over `⟨T⟩ \ SL(2, ℤ)` is twice the `n`-th Poincaré series `P_k^n(Γ, 1; z; ∞)` of
`specialfunction.poincare` (LeanBridge's `ModularForm.poincareSeries`), which sums over the cosets
of the stabiliser `Γ_∞ = ±⟨T⟩` of `∞`: each coset `±⟨T⟩γ` is the union of `⟨T⟩γ` and `⟨T⟩(-γ)`,
whose terms agree in even weight. -/
lemma averageSeries_cexp (hk : 3 ≤ k) (hk2 : Even k) (n : ℤ) :
    averageSeries (fun w ↦ cexp (2 * π * I * n * w)) k z =
      2 * poincareSeries (G := ⊤) 1 1 k n 1 z := by
  have hh : ∀ w : ℍ, cexp (2 * π * I * n * ↑(T • w)) = cexp (2 * π * I * n * w) := cexp_smul_T n
  let σ : Bool → SL(2, ℤ) → SL(2, ℤ) := fun b g ↦ bif b then -g else g
  let f : 𝒫 × Bool → 𝒬 := fun pb ↦ ⟦σ pb.2 pb.1.out⟧
  have hinj : Function.Injective f := by
    rintro ⟨p, b⟩ ⟨p', b'⟩ hpp
    have hT : σ b' p'.out * (σ b p.out)⁻¹ ∈ Subgroup.zpowers T :=
      rightRel_apply.mp (Quotient.exact hpp)
    have hp : p = p' := by
      refine Quotient.out_equiv_out.mp (rightRel_apply.mpr ?_)
      rw [mem_cuspStabilizer_top_one_iff]
      cases b <;> cases b' <;> simpa [σ] using (mem_zpowers_T_iff.mp hT).1
    subst hp
    cases b <;> cases b' <;> simp [σ, mem_zpowers_T_iff] at hT ⊢
  have hsurj : Function.Surjective f := by
    intro q
    let p : 𝒫 := ⟦⟨q.out, Subgroup.mem_top _⟩⟧
    have hrel : rightRel (cuspStabilizer ⊤ 1) p.out ⟨q.out, Subgroup.mem_top _⟩ :=
      Quotient.exact (Quotient.out_eq p)
    rw [rightRel_apply, mem_cuspStabilizer_top_one_iff] at hrel
    have hb : ∃ b, σ b (q.out * (p.out : SL(2, ℤ))⁻¹) ∈ Subgroup.zpowers T :=
      (mem_zpowers_T_or_neg_mem hrel).elim (fun hT ↦ ⟨false, hT⟩) fun hT ↦ ⟨true, hT⟩
    rcases hb with ⟨b, hb⟩
    refine ⟨(p, b), ?_⟩
    rw [← Quotient.out_eq q]
    exact Quotient.sound (rightRel_apply.mpr (by cases b <;> simpa [σ] using hb))
  let e : 𝒫 × Bool ≃ 𝒬 := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hF : Summable fun pb ↦ averageTerm (fun w ↦ cexp (2 * π * I * n * w)) k z (e pb).out :=
    e.summable_iff.mpr (summable_norm_averageTerm_cexp z hk n).of_norm
  have hterm (pb : 𝒫 × Bool) : averageTerm (fun w ↦ cexp (2 * π * I * n * w)) k z (e pb).out =
      poincareTerm 1 1 k n 1 z pb.1.out := by
    rw [← averageTerm_eq_of_rightRel (h := fun w ↦ cexp (2 * π * I * n * w)) k z hh
      (Quotient.exact (Quotient.out_eq (e pb)))]
    rcases pb with ⟨p, b⟩
    have hσ : averageTerm (fun w ↦ cexp (2 * π * I * n * w)) k z (σ b p.out) =
        averageTerm (fun w ↦ cexp (2 * π * I * n * w)) k z p.out := by
      cases b
      · rfl
      · exact (averageTerm_neg k z _).trans (by rw [hk2.neg_one_zpow, one_mul])
    rw [hσ]
    simp [averageTerm, poincareTerm]
  rw [averageSeries, ← e.tsum_eq, hF.tsum_prod' fun p ↦ hF.prod_factor p, poincareSeries,
    ← tsum_mul_left]
  refine tsum_congr fun p ↦ ?_
  rw [tsum_fintype, Fintype.sum_bool, hterm, hterm]
  ring1

/-! ### The series over the whole group -/

/-- The series `∑_{γ ∈ Γ} (γz)^{-n} (cz + d)^{-k}` over the whole group `Γ = SL(2, ℤ)` (LMFDB
`mf.gl2.history.poincare`), as an unconditional sum (`tsum`, `0` when not summable): the sum of the
terms of the average of `w ↦ w^{-n}` over all of `Γ` instead of over `⟨T⟩ \ Γ`. It converges
absolutely for `2 ≤ n ≤ k - 2` (`ModularForm.summable_norm_averageTerm_zpow`). -/
noncomputable def fullAverageSeries (n : ℤ) : ℂ :=
  ∑' γ : SL(2, ℤ), averageTerm (fun w ↦ (w : ℂ) ^ (-n)) k z γ

lemma averageTerm_zpow (n : ℤ) (γ : SL(2, ℤ)) : averageTerm (fun w ↦ (w : ℂ) ^ (-n)) k z γ =
    eisSummand n (γ 0) z * eisSummand (k - n) (γ 1) z := by
  have hd : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
    simpa [ModularGroup.denom_apply] using denom_ne_zero (γ : GL (Fin 2) ℝ) z
  rw [averageTerm, coe_specialLinearGroup_apply, ModularGroup.denom_apply]
  simp only [eq_intCast, ofReal_intCast]
  rw [div_zpow, div_mul_eq_mul_div, mul_div_assoc, ← zpow_sub₀ hd]
  congr 2
  ring1

private lemma norm_mul_norm_I_add_round_le {u v : ℂ} (hu : u ≠ 0) (huv : ‖u‖ ≤ ‖v‖) :
    ‖u‖ * ‖I + (round (v / u).re : ℂ)‖ ≤ 3 * ‖v‖ := by
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have h1 : ‖I + (round (v / u).re : ℂ)‖ ≤ 1 + |(round (v / u).re : ℝ)| := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_I, norm_intCast]
  have h2 : |(v / u).re - round (v / u).re| ≤ 1 / 2 := abs_sub_round _
  have h3 : |(v / u).re| ≤ ‖v‖ / ‖u‖ := (abs_re_le_norm _).trans_eq (norm_div _ _)
  have h4 : |(round (v / u).re : ℝ)| - |(v / u).re| ≤ |(v / u).re - round (v / u).re| :=
    (abs_sub_abs_le_abs_sub _ _).trans_eq (abs_sub_comm _ _)
  have h5 : ‖u‖ * ‖I + (round (v / u).re : ℂ)‖ ≤ ‖u‖ * (‖v‖ / ‖u‖ + 3 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hu'.le
  rw [mul_add, mul_div_cancel₀ _ hu'.ne'] at h5
  linarith

private lemma zpow_neg_mul_zpow_neg_le {U V W : ℝ} (hU : 0 < U) (hW : 0 < W) (h : U * W ≤ 3 * V)
    (p : ℤ) {q : ℤ} (hq : 0 ≤ q) : U ^ (-p) * V ^ (-q) ≤ 3 ^ q * (U ^ (-(p + q)) * W ^ (-q)) := by
  have hUW : 0 < U * W / 3 := by
    positivity
  have h1 : V ^ (-q) ≤ (U * W / 3) ^ (-q) := by
    rw [zpow_neg, zpow_neg]
    exact inv_anti₀ (zpow_pos hUW q) (zpow_le_zpow_left₀ hq hUW.le (by linarith))
  refine (mul_le_mul_of_nonneg_left h1 (zpow_nonneg hU.le _)).trans_eq ?_
  rw [div_zpow, mul_zpow, zpow_neg 3 q, div_inv_eq_mul, neg_add, zpow_add₀ hU.ne']
  ring1

private lemma I_add_intCast_ne_zero (m : ℤ) : I + (m : ℂ) ≠ 0 := fun h ↦ by
  simpa using congrArg Complex.im h

private lemma norm_eisSummand_neg (v : Fin 2 → ℤ) : ‖eisSummand k (-v) z‖ = ‖eisSummand k v z‖ := by
  rw [eisSummand, eisSummand, norm_zpow, norm_zpow, Pi.neg_apply, Pi.neg_apply, Int.cast_neg,
    Int.cast_neg, neg_mul, ← neg_add, norm_neg]

private lemma apply_zero_mul_add_ne_zero (γ : SL(2, ℤ)) : (γ 0 0 : ℂ) * z + γ 0 1 ≠ 0 := by
  have h : denom (S * γ : SL(2, ℤ)) z ≠ 0 := denom_ne_zero _ z
  rwa [ModularGroup.denom_apply, S_mul_apply_one] at h

/-- The bound `3^q |az + b|^{-(p + q)} |m + i|^{-q}` for the term `|az + b|^{-p} |cz + d|^{-q}` at
`γ = !![a, b; c, d] ∈ SL(2, ℤ)` with `|az + b| ≤ |cz + d|`, where `m` is the integer nearest to the
real part of `(cz + d) / (az + b)`. -/
private noncomputable def zpowBound (p q : ℤ) (γ : SL(2, ℤ)) : ℝ :=
  3 ^ q * (‖eisSummand (p + q) (γ 0) z‖ *
    ‖I + (round (((γ 1 0 : ℂ) * z + γ 1 1) / ((γ 0 0 : ℂ) * z + γ 0 1)).re : ℂ)‖ ^ (-q))

private lemma zpowBound_nonneg (p q : ℤ) (γ : SL(2, ℤ)) : 0 ≤ zpowBound z p q γ := by
  rw [zpowBound]
  positivity

private lemma norm_eisSummand_mul_norm_eisSummand_le (p : ℤ) {q : ℤ} (hq : 0 ≤ q) (γ : SL(2, ℤ))
    (h : ‖(γ 0 0 : ℂ) * z + γ 0 1‖ ≤ ‖(γ 1 0 : ℂ) * z + γ 1 1‖) :
    ‖eisSummand p (γ 0) z‖ * ‖eisSummand q (γ 1) z‖ ≤ zpowBound z p q γ := by
  have hu : (γ 0 0 : ℂ) * z + γ 0 1 ≠ 0 := apply_zero_mul_add_ne_zero z γ
  simp only [zpowBound, eisSummand, norm_zpow]
  exact zpow_neg_mul_zpow_neg_le (norm_pos_iff.mpr hu)
    (norm_pos_iff.mpr (I_add_intCast_ne_zero _)) (norm_mul_norm_I_add_round_le hu h) p hq

private lemma injective_apply_zero_round : Function.Injective fun γ : SL(2, ℤ) ↦
    (γ 0, round (((γ 1 0 : ℂ) * z + γ 1 1) / ((γ 0 0 : ℂ) * z + γ 0 1)).re) := by
  intro γ γ' h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hrow, hround⟩
  have h00 : γ' 0 0 = γ 0 0 := (congrFun hrow 0).symm
  have h01 : γ' 0 1 = γ 0 1 := (congrFun hrow 1).symm
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  have hdet' : γ 0 0 * γ' 1 1 - γ 0 1 * γ' 1 0 = 1 := by
    rw [← h00, ← h01]
    exact γ'.fin_two_mul_sub_mul_eq_one
  have hex : ∃ j : ℤ, γ' 1 0 = γ 1 0 + j * γ 0 0 ∧ γ' 1 1 = γ 1 1 + j * γ 0 1 :=
    ⟨γ' 1 0 * γ 1 1 - γ' 1 1 * γ 1 0, by linear_combination -γ' 1 0 * hdet + γ 1 0 * hdet',
      by linear_combination -γ' 1 1 * hdet + γ 1 1 * hdet'⟩
  rcases hex with ⟨j, h10, h11⟩
  have hv : ((γ' 1 0 : ℂ) * z + γ' 1 1) / ((γ 0 0 : ℂ) * z + γ 0 1) =
      ((γ 1 0 : ℂ) * z + γ 1 1) / ((γ 0 0 : ℂ) * z + γ 0 1) + j := by
    have hu : (γ 0 0 : ℂ) * z + γ 0 1 ≠ 0 := apply_zero_mul_add_ne_zero z γ
    rw [h10, h11]
    push_cast
    field_simp
    ring1
  rw [h00, h01, hv, add_re, intCast_re, round_add_intCast] at hround
  have hj : j = 0 := by
    omega
  ext i l
  fin_cases i <;> fin_cases l
  · exact h00.symm
  · exact h01.symm
  · simpa [hj] using h10.symm
  · simpa [hj] using h11.symm

private lemma summable_zpowBound {p q : ℤ} (hpq : 3 ≤ p + q) (hq : 2 ≤ q) :
    Summable (zpowBound z p q) := by
  have hg : Summable fun m : ℤ ↦ ‖I + (m : ℂ)‖ ^ (-q) := by
    refine (linear_right_summable I 1 hq).norm.congr fun m ↦ ?_
    simp
  unfold zpowBound
  simpa only [Function.comp_def] using (((summable_norm_eisSummand hpq z).mul_of_nonneg hg
    (fun _ ↦ norm_nonneg _) fun _ ↦ zpow_nonneg (norm_nonneg _) _).comp_injective
      (injective_apply_zero_round z)).mul_left (3 ^ q)

variable {k} in
/-- **The series over the whole group converges absolutely for `2 ≤ n ≤ k - 2`** (LMFDB
`mf.gl2.history.poincare`). Its terms are `(az + b)^{-n} (cz + d)^{-(k - n)}`. Where
`|az + b| ≤ |cz + d|`, the matrix `γ = !![a, b; c, d]` is determined by its top row `(a, b)` and
the integer `m` nearest to the real part of `(cz + d) / (az + b)`, and
`|cz + d| ≥ |az + b| |m + i| / 3`, so that the term is at most
`3^{k - n} |az + b|^{-k} |m + i|^{-(k - n)}`, which is summable over `(a, b)` and `m`. Elsewhere
the same holds with the rows exchanged. -/
lemma summable_norm_averageTerm_zpow {n : ℤ} (hn : 2 ≤ n) (hkn : 2 ≤ k - n) :
    Summable fun γ : SL(2, ℤ) ↦ ‖averageTerm (fun w ↦ (w : ℂ) ^ (-n)) k z γ‖ := by
  have hS : Summable fun γ : SL(2, ℤ) ↦ zpowBound z (k - n) n (S * γ) :=
    (Equiv.mulLeft S).summable_iff.mpr (summable_zpowBound z (by omega) hn)
  refine ((summable_zpowBound z (p := n) (by omega) hkn).add hS).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun γ ↦ ?_
  rw [averageTerm_zpow, norm_mul]
  rcases le_total ‖(γ 0 0 : ℂ) * z + γ 0 1‖ ‖(γ 1 0 : ℂ) * z + γ 1 1‖ with h | h
  · exact (norm_eisSummand_mul_norm_eisSummand_le z n (by omega) γ h).trans
      (le_add_of_nonneg_right (zpowBound_nonneg ..))
  · have hγ : ‖((S * γ) 0 0 : ℂ) * z + (S * γ) 0 1‖ ≤ ‖((S * γ) 1 0 : ℂ) * z + (S * γ) 1 1‖ := by
      rwa [S_mul_apply_zero, S_mul_apply_one, Pi.neg_apply, Pi.neg_apply, Int.cast_neg,
        Int.cast_neg, neg_mul, ← neg_add, norm_neg]
    have hL : ‖eisSummand n (γ 0) z‖ * ‖eisSummand (k - n) (γ 1) z‖ =
        ‖eisSummand (k - n) ((S * γ) 0) z‖ * ‖eisSummand n ((S * γ) 1) z‖ := by
      rw [S_mul_apply_zero, S_mul_apply_one, norm_eisSummand_neg, mul_comm]
    exact hL.trans_le <| (norm_eisSummand_mul_norm_eisSummand_le z (k - n) (by omega) (S * γ)
      hγ).trans (le_add_of_nonneg_left (zpowBound_nonneg ..))

/-- **The series over the whole group has the modular transformation property** (LMFDB
`mf.gl2.history.poincare`): `F(γz) = (cz + d)^k F(z)` for every `γ = !![a, b; c, d] ∈ SL(2, ℤ)`,
the sum over `Γ` being invariant under right multiplication by `γ`. -/
lemma fullAverageSeries_smul (n : ℤ) (γ : SL(2, ℤ)) :
    fullAverageSeries k (γ • z) n = denom γ z ^ k * fullAverageSeries k z n := by
  have he : ∑' δ : SL(2, ℤ), averageTerm (fun w ↦ (w : ℂ) ^ (-n)) k z (δ * γ) =
      ∑' δ : SL(2, ℤ), averageTerm (fun w ↦ (w : ℂ) ^ (-n)) k z δ :=
    (Equiv.mulRight γ).tsum_eq fun δ ↦ averageTerm (fun w ↦ (w : ℂ) ^ (-n)) k z δ
  rw [fullAverageSeries, tsum_congr fun δ ↦ averageTerm_smul _ k z δ γ, tsum_mul_right, he,
    mul_comm, fullAverageSeries]

/-- **`w ↦ ∑_{m ∈ ℤ} (w + m)^{-n}` is `1`-periodic** (LMFDB `mf.gl2.history.poincare`): its value
does not change under `T : w ↦ w + 1`, the sum over `ℤ` being reindexed by `m ↦ 1 + m`. -/
lemma tsum_zpow_smul_T (n : ℤ) (w : ℍ) :
    ∑' m : ℤ, (((T • w : ℍ) : ℂ) + m) ^ (-n) = ∑' m : ℤ, ((w : ℂ) + m) ^ (-n) := by
  have hT : ((T • w : ℍ) : ℂ) = w + 1 := by
    simpa using coe_T_zpow_smul_eq (z := w) (n := 1)
  rw [hT]
  conv_rhs => rw [← (Equiv.addLeft (1 : ℤ)).tsum_eq]
  refine tsum_congr fun m ↦ ?_
  simp only [Equiv.coe_addLeft, Int.cast_add, Int.cast_one, add_assoc]

variable {k} in
/-- **The series over the whole group is the average of `∑_m (w + m)^{-n}`** (LMFDB
`mf.gl2.history.poincare`): for `2 ≤ n ≤ k - 2`, grouping the terms by the cosets `⟨T⟩γ`, the sum
over `Γ` is the average over `⟨T⟩ \ Γ` of the `1`-periodic function `w ↦ ∑_{m ∈ ℤ} (w + m)^{-n}`
(`ModularForm.tsum_zpow_smul_T`). -/
lemma fullAverageSeries_eq_averageSeries {n : ℤ} (hn : 2 ≤ n) (hkn : 2 ≤ k - n) :
    fullAverageSeries k z n = averageSeries (fun w ↦ ∑' m : ℤ, ((w : ℂ) + m) ^ (-n)) k z := by
  let f : 𝒬 × ℤ → SL(2, ℤ) := fun qm ↦ T ^ qm.2 * qm.1.out
  have hinj : Function.Injective f := by
    rintro ⟨q, m⟩ ⟨q', m'⟩ hqm
    have hqm' : T ^ m * q.out = T ^ m' * q'.out := hqm
    have hq : q = q' := injective_bottomRow <| (T_pow_mul_apply_one m q.out).symm.trans <|
      (congrArg (fun g : SL(2, ℤ) ↦ g 1) hqm').trans (T_pow_mul_apply_one m' q'.out)
    subst hq
    have hm : T ^ m = T ^ m' := mul_right_cancel hqm
    rw [injective_T_zpow hm]
  have hsurj : Function.Surjective f := by
    intro γ
    rcases Subgroup.mem_zpowers_iff.mp
      (rightRel_apply.mp (Quotient.exact (Quotient.out_eq (⟦γ⟧ : 𝒬)))) with ⟨m, hm⟩
    exact ⟨(⟦γ⟧, m), by simp only [f, hm, inv_mul_cancel_right]⟩
  let e : 𝒬 × ℤ ≃ SL(2, ℤ) := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hS : Summable fun qm ↦ averageTerm (fun w ↦ (w : ℂ) ^ (-n)) k z (e qm) :=
    e.summable_iff.mpr (summable_norm_averageTerm_zpow z hn hkn).of_norm
  rw [fullAverageSeries, ← e.tsum_eq, hS.tsum_prod' fun q ↦ hS.prod_factor q, averageSeries]
  refine tsum_congr fun q ↦ ?_
  have hterm (m : ℤ) : averageTerm (fun w ↦ (w : ℂ) ^ (-n)) k z (e (q, m)) =
      (((q.out • z : ℍ) : ℂ) + m) ^ (-n) * denom q.out z ^ (-k) := by
    have he : e (q, m) = T ^ m * q.out :=
      rfl
    rw [he, averageTerm, mul_smul, coe_T_zpow_smul_eq, denom_T_zpow_mul]
  rw [tsum_congr hterm, tsum_mul_right, averageTerm]

/-- **Over the whole group, the series for `h = 1` diverges** (LMFDB `mf.gl2.history.poincare`):
the terms `(cz + d)^{-k}` at the powers `T^m` of `T` are all `1`, so dividing by the action of `T`
is necessary for the Eisenstein series. -/
lemma not_summable_averageTerm_one :
    ¬Summable fun γ : SL(2, ℤ) ↦ averageTerm (fun _ ↦ 1) k z γ := by
  intro hS
  have hT (m : ℤ) : averageTerm (fun _ ↦ 1) k z (T ^ m) = 1 := by
    rw [averageTerm, ModularGroup.denom_apply]
    simp [coe_T_zpow]
  have h1 : Summable fun _ : ℤ ↦ (1 : ℂ) := by
    simpa only [Function.comp_def, hT] using hS.comp_injective injective_T_zpow
  exact one_ne_zero ((summable_const_iff (1 : ℂ)).mp h1)

end ModularForm
