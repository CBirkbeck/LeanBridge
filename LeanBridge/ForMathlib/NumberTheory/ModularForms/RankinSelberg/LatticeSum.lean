import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.ZetaValues

/-!
# Lattice sums with a periodic weight

For `z` in the upper half plane and `σ > 1`, this file studies the sums of
`Φ(c, d) |c z + d| ^ (-2σ)`, for a function `Φ` of the residues of `(c, d)` modulo `L`, over all
vectors of integers and over the coprime ones, as `σ → 1⁺`. These sums are the real-analytic
Eisenstein series that appear when a Rankin–Selberg integral is unfolded.

Each residue class contributes the same polar part, because `|c z + d| ^ (-2σ)` changes by
`O(‖m‖ ^ (-3))`, uniformly in `σ ∈ (1, 2]`, when the vector `L m` is shifted by a fixed vector. So
when `Φ` has mean zero the sum over all vectors stays bounded. The sum over the coprime vectors is
obtained by dividing out the Dirichlet series `∑ c(g) g ^ (-2σ)`, whose absolute value is at least
`2 - ζ(2) > 0` for any coefficients `|c(g)| ≤ 1` with `c(1) = 1`: this is what replaces a
nonvanishing statement for an `L`-function at `σ = 1`.

## Main definitions

* `RankinSelberg.latticeTerm`: the term `|c z + d| ^ (-2σ)`.
* `RankinSelberg.reduceMod`: the reduction modulo `L` of a vector of integers.
* `RankinSelberg.liftMod`: the lift to `[0, L)` of a vector modulo `L`.

## Main results

* `RankinSelberg.tsum_mul_latticeTerm_eq_mul_tsum_coprime`: the sum over all vectors is a Dirichlet
  series times the sum over the coprime vectors.
* `RankinSelberg.tendsto_sub_one_mul_tsum_coprime`: the sum over the coprime vectors has no pole at
  `σ = 1` when `Φ` has mean zero.
* `RankinSelberg.le_tsum_latticeTerm_add_smul`: the sum over a residue class has at least a pole at
  `σ = 1`, uniformly for bounded `z`.
-/

open UpperHalfPlane EisensteinSeries Filter Topology Real

namespace RankinSelberg

variable {L : ℕ} (z : ℍ) {σ : ℝ} (x a m : Fin 2 → ℤ) {u : ℕ → ℂ}

variable (σ) in
/-- The term `|c z + d| ^ (-2σ)` of the real-analytic Eisenstein series, for a vector `x = (c, d)`
of integers. It is `0` at the zero vector, since `σ ≠ 0` in every use. -/
noncomputable def latticeTerm : ℝ :=
  ‖(x 0 : ℂ) * z + x 1‖ ^ (-(2 * σ))

variable (σ) in
lemma latticeTerm_nonneg : 0 ≤ latticeTerm z σ x :=
  Real.rpow_nonneg (norm_nonneg _) _

lemma latticeTerm_le (hσ : 0 ≤ σ) : latticeTerm z σ x ≤ r z ^ (-(2 * σ)) * ‖x‖ ^ (-(2 * σ)) :=
  summand_bound z (by positivity) x

lemma summable_norm_rpow (hσ : 1 < σ) : Summable fun x : Fin 2 → ℤ ↦ ‖x‖ ^ (-(2 * σ)) :=
  summable_one_div_norm_rpow (by linarith)

lemma summable_latticeTerm (hσ : 1 < σ) : Summable (latticeTerm z σ) :=
  Summable.of_nonneg_of_le (latticeTerm_nonneg z σ) (fun x ↦ latticeTerm_le z x (by linarith))
    ((summable_norm_rpow hσ).mul_left _)

lemma tsum_norm_rpow (hσ : 1 < σ) :
    ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * σ)) = 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1) := by
  have hne : -(2 * σ) ≠ 0 := by linarith
  have hsum : Summable fun p : ℤ × ℤ ↦ ‖![p.1, p.2]‖ ^ (-(2 * σ)) :=
    (finTwoArrowEquiv ℤ).symm.summable_iff.mpr (summable_norm_rpow hσ)
  let κ : ℤ × ℤ → ℕ := fun p ↦ max p.1.natAbs p.2.natAbs
  have hκ : ∀ p : ℤ × ℤ, ‖![p.1, p.2]‖ = κ p := fun p ↦ by
    simp [norm_eq_max_natAbs, κ]
  have hsig :
      Summable fun q : Σ n : ℕ, {p : ℤ × ℤ // κ p = n} ↦ ‖![q.2.1.1, q.2.1.2]‖ ^ (-(2 * σ)) :=
    (Equiv.sigmaFiberEquiv κ).summable_iff.mpr hsum
  have hfib : ∀ n : ℕ, HasSum (fun p : {p : ℤ × ℤ // κ p = n} ↦ ‖![p.1.1, p.1.2]‖ ^ (-(2 * σ)))
      (8 * (1 / (n : ℝ) ^ (2 * σ - 1))) := by
    intro n
    let hfin : Fintype {p : ℤ × ℤ // κ p = n} :=
      Fintype.subtype (Finset.box n) fun p ↦ by simp [κ]
    have hcard : Fintype.card {p : ℤ × ℤ // κ p = n} = if n = 0 then 1 else 8 * n := by
      rw [Fintype.card_of_subtype (Finset.box n) fun p ↦ by simp [κ]]
      split_ifs with hn
      · simp [hn]
      · exact Int.card_box hn
    have hval :
        ∀ p : {p : ℤ × ℤ // κ p = n}, ‖![p.1.1, p.1.2]‖ ^ (-(2 * σ)) = (n : ℝ) ^ (-(2 * σ)) :=
      fun p ↦ by rw [hκ, p.2]
    simp_rw [hval]
    convert hasSum_fintype (fun _ : {p : ℤ × ℤ // κ p = n} ↦ (n : ℝ) ^ (-(2 * σ))) using 1
    rw [Finset.sum_const, Finset.card_univ, hcard]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow hne, Real.zero_rpow (by linarith : 2 * σ - 1 ≠ 0)]
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn
      rw [ite_eq_right hn, nsmul_eq_mul, Real.rpow_sub_one hn0.ne', Real.rpow_neg hn0.le]
      push_cast
      field_simp
  have hser : HasSum (fun n : ℕ ↦ 8 * (1 / (n : ℝ) ^ (2 * σ - 1)))
      (8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1)) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith)).hasSum.mul_left 8
  refine Eq.trans ?_ (hsig.hasSum.sigma hfib |>.unique hser)
  rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  exact ((Equiv.sigmaFiberEquiv κ).tsum_eq _).symm

lemma tendsto_sub_one_mul_tsum_nat_rpow :
    Tendsto (fun σ : ℝ ↦ (σ - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1)) (𝓝[>] 1) (𝓝 (1 / 2)) := by
  have hmap : Tendsto (fun σ : ℝ ↦ 2 * σ - 1) (𝓝[>] 1) (𝓝[>] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨Tendsto.mono_left (Continuous.tendsto' (by fun_prop) 1 1
      (by norm_num)) nhdsWithin_le_nhds, eventually_mem_nhdsWithin.mono fun σ hσ ↦ by
        simp only [Set.mem_Ioi] at hσ ⊢
        linarith⟩
  have h : Tendsto (fun σ : ℝ ↦ 1 / 2 * ((2 * σ - 1 - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1)))
      (𝓝[>] 1) (𝓝 (1 / 2)) := by
    simpa only [mul_one, Function.comp_def] using
      (tendsto_sub_mul_tsum_nat_rpow.comp hmap).const_mul (1 / 2 : ℝ)
  refine h.congr fun σ ↦ ?_
  ring1

lemma eventually_sub_one_mul_tsum_norm_rpow_le :
    ∀ᶠ σ : ℝ in 𝓝[>] 1, (σ - 1) * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * σ)) ≤ 5 := by
  filter_upwards [tendsto_sub_one_mul_tsum_nat_rpow.eventually (gt_mem_nhds
    (by norm_num : (1 / 2 : ℝ) < 5 / 8)), self_mem_nhdsWithin] with σ h hσ
  rw [tsum_norm_rpow hσ]
  linarith

lemma abs_rpow_neg_sub_rpow_neg_le {A B α : ℝ} (hA : 0 < A) (hB : 0 < B) (hα : 1 ≤ α) :
    |A ^ (-α) - B ^ (-α)| ≤ α * |A - B| * min A B ^ (-α - 1) := by
  wlog hAB : A ≤ B generalizing A B
  · have h : |B ^ (-α) - A ^ (-α)| ≤ α * |B - A| * min B A ^ (-α - 1) :=
      this hB hA (le_of_not_ge hAB)
    rwa [abs_sub_comm, abs_sub_comm B, min_comm] at h
  have hratio : 1 + α * (A / B - 1) ≤ (A / B) ^ α := by
    have hs : -1 ≤ A / B - 1 := by
      have h0 : 0 ≤ A / B := by positivity
      linarith
    simpa using one_add_mul_self_le_rpow_one_add hs hα
  have hB' : B ^ (-α) = A ^ (-α) * (A / B) ^ α := by
    rw [Real.div_rpow hA.le hB.le, Real.rpow_neg hA.le, Real.rpow_neg hB.le]
    have h0 : A ^ α ≠ 0 := (Real.rpow_pos_of_pos hA α).ne'
    field_simp
  have hAα : 0 < A ^ (-α) := Real.rpow_pos_of_pos hA _
  have hle : B ^ (-α) ≤ A ^ (-α) := Real.rpow_le_rpow_of_nonpos hA hAB (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonpos (sub_nonpos.mpr hAB), min_eq_left hAB,
    Real.rpow_sub_one hA.ne', neg_sub, hB']
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  have h1 : α * (B - A) * (A ^ (-α) / A) - (A ^ (-α) - A ^ (-α) * (A / B) ^ α) =
      A ^ (-α) * ((A / B) ^ α - (1 + α * (A / B - 1)) + α * (B - A) * (1 / A - 1 / B)) := by
    have hB0 : B ≠ 0 := hB.ne'
    have hA0 : A ≠ 0 := hA.ne'
    field_simp
    ring1
  have h2 : 0 ≤ 1 / A - 1 / B := sub_nonneg.mpr <| one_div_le_one_div_of_le hA hAB
  have h3 : 0 ≤ α * (B - A) * (1 / A - 1 / B) := by positivity
  nlinarith

lemma two_sub_pi_sq_div_six_pos : 0 < 2 - π ^ 2 / 6 := by
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

lemma norm_mul_rpow_le (hu : ∀ n, ‖u n‖ ≤ 1) (hσ : 1 ≤ σ) (n : ℕ) :
    ‖u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ ≤ 1 / (n : ℝ) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr <| Nat.pos_of_ne_zero hn
    have hle : (n : ℝ) ^ (-(2 * σ)) ≤ (n : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine (mul_le_of_le_one_left (by positivity) (hu n)).trans (hle.trans_eq ?_)
    rw [Real.rpow_neg (by positivity), one_div]
    norm_num

lemma norm_tsum_mul_rpow_le (hu : ∀ n, ‖u n‖ ≤ 1) (hσ : 1 ≤ σ) :
    ‖∑' n : ℕ, u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ ≤ π ^ 2 / 6 :=
  tsum_of_norm_bounded hasSum_zeta_two (norm_mul_rpow_le hu hσ)

lemma two_sub_pi_sq_le_norm_tsum (hu : ∀ n, ‖u n‖ ≤ 1) (hu1 : u 1 = 1) (hσ : 1 ≤ σ) :
    2 - π ^ 2 / 6 ≤ ‖∑' n : ℕ, u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ := by
  have hbound : ∀ n : ℕ, ‖u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ ≤ 1 / (n : ℝ) ^ 2 :=
    norm_mul_rpow_le hu hσ
  have hsum : Summable fun n : ℕ ↦ u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ) :=
    Summable.of_norm_bounded hasSum_zeta_two.summable hbound
  have hrest :
      ‖∑' n : ℕ, if n = 1 then 0 else u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ ≤ π ^ 2 / 6 - 1 := by
    have hg : HasSum (fun n : ℕ ↦ if n = 1 then (0 : ℝ) else 1 / (n : ℝ) ^ 2) (π ^ 2 / 6 - 1) := by
      simpa using hasSum_ite_sub_hasSum hasSum_zeta_two 1
    refine tsum_of_norm_bounded hg fun n ↦ ?_
    split_ifs
    · simp
    · exact hbound n
  have h1 : (1 : ℂ) * (((1 : ℕ) : ℝ) ^ (-(2 * σ)) : ℝ) = 1 := by simp
  have h2 : ‖(1 : ℂ)‖ - ‖-∑' n : ℕ, if n = 1 then 0 else u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ ≤
      ‖(1 : ℂ) - -∑' n : ℕ, if n = 1 then 0 else u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ :=
    norm_sub_norm_le _ _
  rw [norm_neg, norm_one, sub_neg_eq_add] at h2
  rw [hsum.tsum_eq_add_tsum_ite 1, hu1, h1]
  linarith

lemma latticeTerm_le_const (hσ : σ ∈ Set.Ioc (1 : ℝ) 2) :
    latticeTerm z σ x ≤ 1 + r z ^ (-4 : ℝ) := by
  have hr : 0 < r z := r_pos z
  have h4 : 0 ≤ r z ^ (-4 : ℝ) := by positivity
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [latticeTerm, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    rw [Real.zero_rpow (by linarith [hσ.1])]
    positivity
  have hx1 : (1 : ℝ) ≤ ‖x‖ := by
    rw [norm_eq_max_natAbs]
    have h1 : 1 ≤ max (x 0).natAbs (x 1).natAbs := by
      by_contra h
      simp only [not_le, Nat.lt_one_iff, Nat.max_eq_zero_iff, Int.natAbs_eq_zero] at h
      exact hx (funext fun i ↦ by fin_cases i <;> simp [h.1, h.2])
    exact_mod_cast h1
  have hle : r z ≤ ‖(x 0 : ℂ) * z + x 1‖ :=
    (le_mul_of_one_le_right hr.le hx1).trans (r_mul_max_le z hx)
  refine (Real.rpow_le_rpow_of_nonpos hr hle (by linarith [hσ.1])).trans ?_
  rcases le_total 1 (r z) with h1 | h1
  · linarith [Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith [hσ.1] : -(2 * σ) ≤ 0)]
  · linarith [Real.rpow_le_rpow_of_exponent_ge hr h1 (by linarith [hσ.2] : (-4 : ℝ) ≤ -(2 * σ))]

lemma sub_norm_le_norm_add_smul (hL : L ≠ 0) : ‖m‖ - ‖a‖ ≤ ‖a + (L : ℤ) • m‖ := by
  rw [sub_le_iff_le_add]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ ?_
  have h1 : ‖a i + (L : ℤ) * m i‖ ≤ ‖a + (L : ℤ) • m‖ := norm_le_pi_norm (a + (L : ℤ) • m) i
  have h2 : ‖a i‖ ≤ ‖a‖ := norm_le_pi_norm a i
  have h3 : ‖m i‖ ≤ ‖(L : ℤ) * m i‖ := by
    rw [norm_mul]
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    rw [Int.norm_natCast]
    exact Nat.one_le_cast.mpr <| Nat.pos_of_ne_zero hL
  have h4 : ‖a i + (L : ℤ) * m i - a i‖ ≤ ‖a i + (L : ℤ) * m i‖ + ‖a i‖ := norm_sub_le _ _
  rw [add_sub_cancel_left] at h4
  linarith

lemma exists_bound_latticeTerm_sub (hL : L ≠ 0) : ∃ g : (Fin 2 → ℤ) → ℝ, Summable g ∧
    ∀ σ ∈ Set.Ioc (1 : ℝ) 2, ∀ m : Fin 2 → ℤ,
      ‖latticeTerm z σ (a + (L : ℤ) • m) - latticeTerm z σ ((L : ℤ) • m)‖ ≤ g m := by
  have hr : 0 < r z := r_pos z
  let δ : ℝ := ‖(a 0 : ℂ) * z + a 1‖
  let M₀ : ℝ := 2 * ‖a‖ + 2 / r z + 1
  let C : ℝ := 4 * δ * (r z / 2) ^ (-3 : ℝ)
  let K : ℝ := 1 + r z ^ (-4 : ℝ)
  have hδ : 0 ≤ δ := norm_nonneg _
  have hK : 0 ≤ K := by positivity
  have hC : 0 ≤ C := by positivity
  refine ⟨fun m ↦ if ‖m‖ < M₀ then K else C * ‖m‖ ^ (-3 : ℝ), ?_, fun σ hσ m ↦ ?_⟩
  · refine Summable.of_norm_bounded_eventually
      ((summable_one_div_norm_rpow (k := 3) (by norm_num)).mul_left C) ?_
    filter_upwards [(tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
      IsClosedEmbedding.id).eventually_ge_atTop M₀] with m hm
    have hm' : M₀ ≤ ‖m‖ := hm
    rw [ite_eq_right (not_lt.mpr hm'), Real.norm_of_nonneg (by positivity)]
  · have hu : 0 ≤ latticeTerm z σ (a + (L : ℤ) • m) := latticeTerm_nonneg z σ _
    have hv : 0 ≤ latticeTerm z σ ((L : ℤ) • m) := latticeTerm_nonneg z σ _
    beta_reduce
    split_ifs with hm
    · rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [latticeTerm_le_const z (a + (L : ℤ) • m) hσ,
        latticeTerm_le_const z ((L : ℤ) • m) hσ]
    · have hm' : 2 * ‖a‖ + 2 / r z + 1 ≤ ‖m‖ := not_lt.mp hm
      have hdiv : 0 < 2 / r z := by positivity
      have hanorm : 0 ≤ ‖a‖ := norm_nonneg a
      have hν : 1 ≤ r z / 2 * ‖m‖ := by
        have h2 : 2 / r z ≤ ‖m‖ := by linarith
        rw [div_le_iff₀ hr] at h2
        linarith
      have hmpos : 0 < ‖m‖ := by linarith
      have h₀ : ‖m‖ ≤ ‖(L : ℤ) • m‖ := by simpa using sub_norm_le_norm_add_smul 0 m hL
      have h₁ : ‖m‖ - ‖a‖ ≤ ‖a + (L : ℤ) • m‖ := sub_norm_le_norm_add_smul a m hL
      have hA0 : a + (L : ℤ) • m ≠ 0 := fun h0 ↦ by
        rw [h0, norm_zero] at h₁
        linarith
      have hB0 : (L : ℤ) • m ≠ 0 := fun h0 ↦ by
        rw [h0, norm_zero] at h₀
        linarith
      let A : ℝ := ‖((a + (L : ℤ) • m) 0 : ℂ) * z + (a + (L : ℤ) • m) 1‖
      let B : ℝ := ‖(((L : ℤ) • m) 0 : ℂ) * z + ((L : ℤ) • m) 1‖
      have hAν : r z / 2 * ‖m‖ ≤ A := by
        refine le_trans ?_ (r_mul_max_le z hA0)
        nlinarith
      have hBν : r z / 2 * ‖m‖ ≤ B := by
        refine le_trans ?_ (r_mul_max_le z hB0)
        nlinarith
      have hAB : |A - B| ≤ δ := by
        have heq : ((a + (L : ℤ) • m) 0 : ℂ) * z + (a + (L : ℤ) • m) 1 = ((a 0 : ℂ) * z + a 1) +
            (((L : ℤ) • m) 0 * z + ((L : ℤ) • m) 1) := by
          simp only [Pi.add_apply, Int.cast_add]
          ring1
        simp only [A, heq]
        exact (abs_norm_sub_norm_le _ _).trans_eq (by rw [add_sub_cancel_right])
      have hνpos : 0 < r z / 2 * ‖m‖ := by linarith
      have hpow : min A B ^ (-(2 * σ) - 1) ≤ (r z / 2) ^ (-3 : ℝ) * ‖m‖ ^ (-3 : ℝ) := by
        rw [← Real.mul_rpow (by positivity) hmpos.le]
        exact (Real.rpow_le_rpow_of_nonpos hνpos (le_min hAν hBν) (by linarith [hσ.1])).trans
          (Real.rpow_le_rpow_of_exponent_le hν (by linarith [hσ.1]))
      have h0 : 0 ≤ min A B ^ (-(2 * σ) - 1) :=
        Real.rpow_nonneg (le_min (norm_nonneg _) (norm_nonneg _)) _
      rw [Real.norm_eq_abs]
      refine (abs_rpow_neg_sub_rpow_neg_le (hνpos.trans_le hAν) (hνpos.trans_le hBν)
        (by linarith [hσ.1] : (1 : ℝ) ≤ 2 * σ)).trans ?_
      refine (mul_le_mul (mul_le_mul (by linarith [hσ.2] : 2 * σ ≤ 4) hAB (abs_nonneg _)
        (by norm_num)) hpow h0 (by positivity)).trans_eq ?_
      simp only [C]
      ring1

variable (L) in
/-- The reduction modulo `L` of a vector of integers. -/
def reduceMod : Fin 2 → ZMod L :=
  fun i ↦ (x i : ZMod L)

variable (v : Fin 2 → ZMod L) (Φ : (Fin 2 → ZMod L) → ℂ) {c : ℕ → ℂ}

/-- The vector of integers in `[0, L)` lifting a vector modulo `L`. -/
def liftMod : Fin 2 → ℤ :=
  fun i ↦ ((v i).val : ℤ)

lemma reduceMod_add_smul : reduceMod L (a + (L : ℤ) • m) = reduceMod L a :=
  funext fun i ↦ by simp [reduceMod]

lemma liftMod_nonneg (i : Fin 2) : 0 ≤ liftMod v i :=
  Int.natCast_nonneg _

lemma add_smul_injective (hL : L ≠ 0) : Function.Injective fun m : Fin 2 → ℤ ↦ a + (L : ℤ) • m :=
  fun _ _ h ↦ funext fun i ↦ mul_left_cancel₀ (Int.natCast_ne_zero.mpr hL)
    (add_left_cancel (congrFun h i))

variable [NeZero L]

lemma reduceMod_liftMod : reduceMod L (liftMod v) = v :=
  funext fun i ↦ by simp [reduceMod, liftMod]

variable (L) in
lemma exists_liftMod_reduceMod_add_smul_eq :
    ∃ m : Fin 2 → ℤ, liftMod (reduceMod L x) + (L : ℤ) • m = x := by
  have hd : ∀ i, (L : ℤ) ∣ x i - liftMod (reduceMod L x) i := fun i ↦ by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact congrFun (reduceMod_liftMod (reduceMod L x)) i
  choose m hm using hd
  refine ⟨m, funext fun i ↦ ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith [hm i]

lemma hasSum_mul_latticeTerm (hσ : 1 < σ) : HasSum
    (fun x : Fin 2 → ℤ ↦ Φ (reduceMod L x) * (latticeTerm z σ x : ℂ))
    (∑ v, Φ v * ((∑' m : Fin 2 → ℤ, latticeTerm z σ (liftMod v + (L : ℤ) • m) : ℝ) : ℂ)) := by
  classical
  have key : ∀ v : Fin 2 → ZMod L, HasSum (fun x : Fin 2 → ℤ ↦ if reduceMod L x = v then
      (latticeTerm z σ x : ℂ) else 0)
      ((∑' m : Fin 2 → ℤ, latticeTerm z σ (liftMod v + (L : ℤ) • m) : ℝ) : ℂ) := by
    intro v
    have he : Function.Injective fun m : Fin 2 → ℤ ↦ liftMod v + (L : ℤ) • m :=
      add_smul_injective _ (NeZero.ne L)
    refine (he.hasSum_iff fun x hx ↦ ite_eq_right fun hxv ↦ ?_).mp ?_
    · subst hxv
      rcases exists_liftMod_reduceMod_add_smul_eq L x with ⟨m, hm⟩
      exact hx ⟨m, hm⟩
    · have hfun : ((fun x : Fin 2 → ℤ ↦ if reduceMod L x = v then (latticeTerm z σ x : ℂ) else 0) ∘
          fun m : Fin 2 → ℤ ↦ liftMod v + (L : ℤ) • m) =
          fun m ↦ (latticeTerm z σ (liftMod v + (L : ℤ) • m) : ℂ) := by
        funext m
        rw [Function.comp_apply, reduceMod_add_smul, reduceMod_liftMod, ite_eq_left rfl]
      rw [hfun]
      exact Complex.hasSum_ofReal.mpr ((summable_latticeTerm z hσ).comp_injective he).hasSum
  refine (hasSum_sum fun v _ ↦ (key v).mul_left (Φ v)).congr_fun fun x ↦ ?_
  simp

variable {Φ} in
lemma exists_norm_tsum_mul_latticeTerm_le (hΦ : ∑ v, Φ v = 0) : ∃ K : ℝ, ∀ σ ∈ Set.Ioc (1 : ℝ) 2,
    ‖∑' x : Fin 2 → ℤ, Φ (reduceMod L x) * (latticeTerm z σ x : ℂ)‖ ≤ K := by
  choose g hg hgb using fun v : Fin 2 → ZMod L ↦
    exists_bound_latticeTerm_sub z (liftMod v) (NeZero.ne L)
  refine ⟨∑ v, ‖Φ v‖ * ∑' m, g v m, fun σ hσ ↦ ?_⟩
  have hsum : ∀ a : Fin 2 → ℤ, Summable fun m : Fin 2 → ℤ ↦ latticeTerm z σ (a + (L : ℤ) • m) :=
    fun a ↦ (summable_latticeTerm z hσ.1).comp_injective (add_smul_injective a (NeZero.ne L))
  have hsum₀ : Summable fun m : Fin 2 → ℤ ↦ latticeTerm z σ ((L : ℤ) • m) := by
    simpa using hsum 0
  have hZ : ∀ v : Fin 2 → ZMod L, ‖(∑' m : Fin 2 → ℤ, latticeTerm z σ (liftMod v + (L : ℤ) • m)) -
      ∑' m : Fin 2 → ℤ, latticeTerm z σ ((L : ℤ) • m)‖ ≤ ∑' m, g v m := fun v ↦ by
    rw [← (hsum (liftMod v)).tsum_sub hsum₀]
    exact tsum_of_norm_bounded (hg v).hasSum <| hgb v σ hσ
  have heq : ∑ v, Φ v * ((∑' m : Fin 2 → ℤ, latticeTerm z σ (liftMod v + (L : ℤ) • m) : ℝ) : ℂ) =
      ∑ v, Φ v * (((∑' m : Fin 2 → ℤ, latticeTerm z σ (liftMod v + (L : ℤ) • m)) -
        ∑' m : Fin 2 → ℤ, latticeTerm z σ ((L : ℤ) • m) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hΦ, zero_mul,
      sub_zero]
  rw [(hasSum_mul_latticeTerm z Φ hσ.1).tsum_eq, heq]
  refine norm_sum_le_of_le _ fun v _ ↦ ?_
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (hZ v) (norm_nonneg _)

lemma norm_le_sum_norm : ‖Φ v‖ ≤ ∑ v, ‖Φ v‖ :=
  Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ v)

variable (σ) in
lemma latticeTerm_nsmul (g : ℕ) :
    latticeTerm z σ (g • x) = (g : ℝ) ^ (-(2 * σ)) * latticeTerm z σ x := by
  have h : ((g • x) 0 : ℂ) * z + (g • x) 1 = (g : ℂ) * ((x 0 : ℂ) * z + x 1) := by
    simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    ring1
  rw [latticeTerm, latticeTerm, h, norm_mul, Complex.norm_natCast,
    Real.mul_rpow (Nat.cast_nonneg g) (norm_nonneg _)]

/-- **The sum over all vectors factors through the sum over the coprime vectors.** If `Φ` scales by
`c g` under multiplication of a primitive vector by `g`, the sum of `Φ(x) |c z + d| ^ (-2σ)` over
all vectors `x = (c, d)` is the Dirichlet series `∑ c(g) g ^ (-2σ)` times the sum over the coprime
vectors. -/
lemma tsum_mul_latticeTerm_eq_mul_tsum_coprime (hσ : 1 < σ)
    (hΦ : ∀ (g : ℕ) (ξ : gammaSet 1 1 0), g ≠ 0 → Φ (reduceMod L (g • ξ.1)) =
      c g * Φ (reduceMod L ξ.1)) : ∑' x : Fin 2 → ℤ, Φ (reduceMod L x) * (latticeTerm z σ x : ℂ) =
    (∑' n : ℕ, c n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)) *
      ∑' ξ : gammaSet 1 1 0, Φ (reduceMod L ξ.1) * (latticeTerm z σ ξ.1 : ℂ) := by
  have hne : -(2 * σ) ≠ 0 := by linarith
  have hsumm : Summable fun x : Fin 2 → ℤ ↦ Φ (reduceMod L x) * (latticeTerm z σ x : ℂ) :=
    (hasSum_mul_latticeTerm z Φ hσ).summable
  simp_rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq]
  rw [Summable.tsum_sigma (gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr hsumm |>.congr <|
    by simp), ← tsum_mul_right]
  refine tsum_congr fun b ↦ ?_
  rcases eq_or_ne b 0 with rfl | hb
  · have h0 : ∀ v : gammaSet 1 0 0, (latticeTerm z σ v.1 : ℂ) = 0 := fun v ↦ by
      rw [gammaSet_eq_gcd_mul_divIntMap v.2]
      simp [latticeTerm, Real.zero_rpow hne]
    simp [h0, Real.zero_rpow hne]
  · have hb' : NeZero b := ⟨hb⟩
    rw [← (gammaSetDivGcdEquiv b).tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun v ↦ ?_
    rw [gammaSetDivGcdEquiv_eq]
    have hv : v.1 = b • divIntMap b v.1 := gammaSet_eq_gcd_mul_divIntMap v.2
    have hΦv : Φ (reduceMod L v.1) = c b * Φ (reduceMod L (divIntMap b v.1)) := by
      have h : Φ (reduceMod L (b • (gammaSetDivGcdEquiv b v).1)) =
          c b * Φ (reduceMod L (gammaSetDivGcdEquiv b v).1) := hΦ b (gammaSetDivGcdEquiv b v) hb
      rwa [gammaSetDivGcdEquiv_eq, ← hv] at h
    have ht : latticeTerm z σ v.1 = (b : ℝ) ^ (-(2 * σ)) * latticeTerm z σ (divIntMap b v.1) :=
      (congrArg (latticeTerm z σ) hv).trans (latticeTerm_nsmul z σ _ b)
    refine (congrArg₂ (· * ·) hΦv (congrArg (fun t : ℝ ↦ (t : ℂ)) ht)).trans ?_
    push_cast
    ring1

variable {Φ} in
/-- **The sum of `Φ(c, d) |c z + d| ^ (-2σ)` over the coprime vectors has no pole at `σ = 1`** when
the values of `Φ` have mean zero: `(σ - 1)` times it tends to `0` as `σ → 1⁺`. -/
lemma tendsto_sub_one_mul_tsum_coprime (hc : ∀ n, ‖c n‖ ≤ 1) (hc1 : c 1 = 1)
    (hΦ : ∀ (g : ℕ) (ξ : gammaSet 1 1 0), g ≠ 0 → Φ (reduceMod L (g • ξ.1)) =
      c g * Φ (reduceMod L ξ.1)) (hΦ₀ : ∑ v, Φ v = 0) : Tendsto (fun σ : ℝ ↦ ((σ - 1 : ℝ) : ℂ) *
      ∑' ξ : gammaSet 1 1 0, Φ (reduceMod L ξ.1) * (latticeTerm z σ ξ.1 : ℂ)) (𝓝[>] 1) (𝓝 0) := by
  rcases exists_norm_tsum_mul_latticeTerm_le z hΦ₀ with ⟨K, hK⟩
  have hδ : 0 < 2 - π ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hlim : Tendsto (fun σ : ℝ ↦ (σ - 1) * (K / (2 - π ^ 2 / 6))) (𝓝[>] 1) (𝓝 0) := by
    have h : Tendsto (fun σ : ℝ ↦ (σ - 1) * (K / (2 - π ^ 2 / 6))) (𝓝 1)
        (𝓝 ((1 - 1) * (K / (2 - π ^ 2 / 6)))) := Continuous.tendsto (by fun_prop) 1
    simpa using h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ
  have hσ1 : 0 ≤ σ - 1 := by linarith [hσ.1]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ1]
  refine mul_le_mul_of_nonneg_left ?_ hσ1
  rw [le_div_iff₀ hδ]
  have hKσ : ‖(∑' n : ℕ, c n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)) *
      ∑' ξ : gammaSet 1 1 0, Φ (reduceMod L ξ.1) * (latticeTerm z σ ξ.1 : ℂ)‖ ≤ K :=
    tsum_mul_latticeTerm_eq_mul_tsum_coprime z Φ hσ.1 hΦ ▸ hK σ hσ
  rw [norm_mul] at hKσ
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_right (two_sub_pi_sq_le_norm_tsum hc hc1 hσ.1.le)
    (norm_nonneg _)).trans hKσ

lemma summable_coprime (hσ : 1 < σ) :
    Summable fun ξ : gammaSet 1 1 0 ↦ Φ (reduceMod L ξ.1) * (latticeTerm z σ ξ.1 : ℂ) := by
  refine Summable.of_norm_bounded (((summable_latticeTerm z hσ).subtype _).mul_left (∑ v, ‖Φ v‖))
    fun ξ ↦ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (latticeTerm_nonneg z σ _)]
  exact mul_le_mul_of_nonneg_right (norm_le_sum_norm _ Φ) (latticeTerm_nonneg z σ _)

lemma norm_tsum_coprime_le (hσ : 1 < σ) :
    ‖∑' ξ : gammaSet 1 1 0, Φ (reduceMod L ξ.1) * (latticeTerm z σ ξ.1 : ℂ)‖ ≤
      (∑ v, ‖Φ v‖) * ∑' x : Fin 2 → ℤ, latticeTerm z σ x := by
  have hsum : Summable fun ξ : gammaSet 1 1 0 ↦ (∑ v, ‖Φ v‖) * latticeTerm z σ ξ.1 :=
    ((summable_latticeTerm z hσ).subtype _).mul_left _
  refine (tsum_of_norm_bounded hsum.hasSum fun ξ ↦ ?_).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (latticeTerm_nonneg z σ _)]
    exact mul_le_mul_of_nonneg_right (norm_le_sum_norm _ Φ) (latticeTerm_nonneg z σ _)
  · rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    exact tsum_comp_le_tsum_of_inj (summable_latticeTerm z hσ) (latticeTerm_nonneg z σ)
      Subtype.val_injective

/-- **A lower bound for the lattice sum over a residue class**: the sum of `|c z + d| ^ (-2σ)` over
the vectors `a + L m` is at least `C ^ (-2σ) ∑ n ^ (1 - 2σ)`, for `C` depending only on `a`, `L` and
an upper bound for `|z|`. So it has at least a pole at `σ = 1`, uniformly for bounded `z`. -/
lemma le_tsum_latticeTerm_add_smul (ha : 0 ≤ a 0) {ρ : ℝ} (hσ : 1 < σ) (hz : ‖(z : ℂ)‖ ≤ ρ) :
    ((|a 0| + L) * ρ + |a 1| + L : ℝ) ^ (-(2 * σ)) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1) ≤
      ∑' m : Fin 2 → ℤ, latticeTerm z σ (a + (L : ℤ) • m) := by
  have hL : (1 : ℝ) ≤ L := Nat.one_le_cast.mpr <| NeZero.pos L
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hz
  let C : ℝ := (|(a 0 : ℝ)| + L) * ρ + |(a 1 : ℝ)| + L
  have hC : 0 < C := by positivity
  have hne : -(2 * σ) ≠ 0 := by linarith
  have hsumm : Summable fun m : Fin 2 → ℤ ↦ latticeTerm z σ (a + (L : ℤ) • m) :=
    (summable_latticeTerm z hσ).comp_injective (add_smul_injective a (NeZero.ne L))
  -- the family `m = (n, j + 1)` with `j < n`
  let e : (Σ n : ℕ, Fin n) → Fin 2 → ℤ := fun q ↦ ![(q.1 : ℤ), ((q.2 : ℕ) : ℤ) + 1]
  have he : Function.Injective e := by
    rintro ⟨n, j⟩ ⟨n', j'⟩ h
    have h0 : (n : ℤ) = n' := congrFun h 0
    have h1 : ((j : ℕ) : ℤ) + 1 = ((j' : ℕ) : ℤ) + 1 := congrFun h 1
    have hn : n = n' := by exact_mod_cast h0
    subst hn
    have hj : j = j' := Fin.ext (by exact_mod_cast add_right_cancel h1)
    rw [hj]
  have hterm :
      ∀ q : Σ n : ℕ, Fin n, (C * (q.1 : ℝ)) ^ (-(2 * σ)) ≤ latticeTerm z σ (a + (L : ℤ) • e q) := by
    rintro ⟨n, j⟩
    have hn0 : 0 < n := Fin.pos_iff_nonempty.mpr ⟨j⟩
    have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn0
    have hjn : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.2
    have hx : ((a + (L : ℤ) • e ⟨n, j⟩) 0 : ℂ) * z + (a + (L : ℤ) • e ⟨n, j⟩) 1 =
        ((a 0 + L * n : ℤ) : ℂ) * z + ((a 1 + L * (j + 1) : ℤ) : ℂ) := by
      simp [e]
    have hup : ‖((a + (L : ℤ) • e ⟨n, j⟩) 0 : ℂ) * z + (a + (L : ℤ) • e ⟨n, j⟩) 1‖ ≤ C * n := by
      rw [hx]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast]
      have h1 : |((a 0 + L * n : ℤ) : ℝ)| ≤ (|(a 0 : ℝ)| + L) * n := by
        push_cast
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, Nat.abs_cast, Nat.abs_cast]
        nlinarith [abs_nonneg (a 0 : ℝ)]
      have h2 : |((a 1 + L * (j + 1) : ℤ) : ℝ)| ≤ (|(a 1 : ℝ)| + L) * n := by
        push_cast
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, Nat.abs_cast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℕ) + 1)]
        nlinarith [abs_nonneg (a 1 : ℝ)]
      have h3 : |((a 0 + L * n : ℤ) : ℝ)| * ‖(z : ℂ)‖ ≤ (|(a 0 : ℝ)| + L) * n * ρ :=
        mul_le_mul h1 hz (norm_nonneg _) (by positivity)
      simp only [C]
      nlinarith
    have hx0 : (a + (L : ℤ) • e ⟨n, j⟩) ≠ 0 := by
      intro h0
      have h00 : a 0 + L * n = 0 := by simpa [e] using congrFun h0 0
      have hL0 : (0 : ℤ) < L := by exact_mod_cast NeZero.pos L
      have hn0' : (0 : ℤ) < n := by exact_mod_cast hn0
      have hLn : (0 : ℤ) < L * n := by positivity
      linarith
    have hpos : 0 < ‖((a + (L : ℤ) • e ⟨n, j⟩) 0 : ℂ) * z + (a + (L : ℤ) • e ⟨n, j⟩) 1‖ :=
      lt_of_lt_of_le (mul_pos (r_pos z) (norm_pos_iff.mpr hx0)) (r_mul_max_le z hx0)
    exact Real.rpow_le_rpow_of_nonpos hpos hup (by linarith)
  -- sum over the family
  have hfib : ∀ n : ℕ, HasSum (fun j : Fin n ↦ (C * ((⟨n, j⟩ : Σ n : ℕ, Fin n).1 : ℝ)) ^ (-(2 * σ)))
      (C ^ (-(2 * σ)) * (1 / (n : ℝ) ^ (2 * σ - 1))) := by
    intro n
    convert hasSum_fintype (fun _ : Fin n ↦ (C * (n : ℝ)) ^ (-(2 * σ))) using 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Real.mul_rpow hC.le (Nat.cast_nonneg n)]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (by linarith : 2 * σ - 1 ≠ 0)]
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn
      rw [Real.rpow_sub_one hn0.ne', Real.rpow_neg hn0.le]
      field_simp
  have hsig : Summable fun q : Σ n : ℕ, Fin n ↦ (C * (q.1 : ℝ)) ^ (-(2 * σ)) :=
    Summable.of_nonneg_of_le (fun q ↦ by positivity) hterm (hsumm.comp_injective he)
  have hser : HasSum (fun n : ℕ ↦ C ^ (-(2 * σ)) * (1 / (n : ℝ) ^ (2 * σ - 1)))
      (C ^ (-(2 * σ)) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ - 1)) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith)).hasSum.mul_left _
  have hC' : ((|a 0| + L) * ρ + |a 1| + L : ℝ) = C := by simp [C]
  rw [hC', hser.unique (hsig.hasSum.sigma hfib)]
  exact (hsig.tsum_le_tsum hterm (hsumm.comp_injective he)).trans
    (tsum_comp_le_tsum_of_inj hsumm (fun m ↦ latticeTerm_nonneg z σ _) he)

end RankinSelberg
