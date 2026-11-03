import LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.LatticeSum

/-!
# Dirichlet series differing only at square factors

Two Dirichlet series whose coefficients agree away from a family of square factors differ by a
Dirichlet series in `t ^ (-2σ)`, which at `σ ≥ 1` is bounded above by `ζ(2)` and bounded away from
`0` by `2 - ζ(2) > 0`, whatever its coefficients of absolute value at most `1`. So one series can be
bounded below by a multiple of the other, with no Euler product and no bound on the coefficients.
This is the arithmetic input of the comparison of Rankin–Selberg series in
`LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NebentypusRigidity`.

## Main results

* `RankinSelberg.mul_le_norm_of_hasSum_of_hasSum`: the comparison.
-/

open Set

open scoped Real

namespace RankinSelberg

variable {𝓜 𝓣 : Set ℕ} {A : ℕ → ℝ} {σ : ℝ} {v u : ℕ → ℂ} {x : ℝ} {y : ℂ}

lemma eq_tsum_mul_tsum_of_hasSum (hσ : 1 ≤ σ) (hX : Summable fun m : 𝓜 ↦ A m)
    (hinj : Function.Injective fun z : 𝓜 × 𝓣 ↦ (z.1 : ℕ) * (z.2 : ℕ) ^ 2)
    (hoff : ∀ n, (∀ m ∈ 𝓜, ∀ t ∈ 𝓣, n ≠ m * t ^ 2) → v n = 0) (hu : ∀ n, ‖u n‖ ≤ 1)
    (hu0 : ∀ n, n ∉ 𝓣 → u n = 0)
    (hv : ∀ m ∈ 𝓜, ∀ t ∈ 𝓣, v (m * t ^ 2) = (A m : ℂ) * (u t * (((t : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)))
    (hy : HasSum v y) :
    y = ((∑' m : 𝓜, A m : ℝ) : ℂ) * ∑' n : ℕ, u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ) := by
  have hX' : HasSum (fun m : 𝓜 ↦ (A m : ℂ)) ((∑' m : 𝓜, A m : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr hX.hasSum
  have hs : Summable fun n : ℕ ↦ u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ) :=
    Summable.of_norm_bounded hasSum_zeta_two.summable (norm_mul_rpow_le hu hσ)
  have hZ : HasSum (fun t : 𝓣 ↦ u t * (((t : ℕ) : ℝ) ^ (-(2 * σ)) : ℝ))
      (∑' n : ℕ, u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)) := by
    refine (Subtype.val_injective.hasSum_iff fun n hn ↦ ?_).mpr hs.hasSum
    rw [hu0 n fun hn' ↦ hn ⟨⟨n, hn'⟩, rfl⟩, zero_mul]
  have hoff' : ∀ n, n ∉ range (fun z : 𝓜 × 𝓣 ↦ (z.1 : ℕ) * (z.2 : ℕ) ^ 2) → v n = 0 := fun n hn ↦
    hoff n fun m hm t ht hne ↦ hn ⟨(⟨m, hm⟩, ⟨t, ht⟩), hne.symm⟩
  have hcomp : (v ∘ fun z : 𝓜 × 𝓣 ↦ (z.1 : ℕ) * (z.2 : ℕ) ^ 2) =
      fun z : 𝓜 × 𝓣 ↦ (A z.1 : ℂ) * (u z.2 * (((z.2 : ℕ) : ℝ) ^ (-(2 * σ)) : ℝ)) :=
    funext fun z ↦ hv z.1 z.1.2 z.2 z.2.2
  have hy₁ : HasSum (v ∘ fun z : 𝓜 × 𝓣 ↦ (z.1 : ℕ) * (z.2 : ℕ) ^ 2) y :=
    (hinj.hasSum_iff hoff').mpr hy
  have hy' :
      HasSum (fun z : 𝓜 × 𝓣 ↦ (A z.1 : ℂ) * (u z.2 * (((z.2 : ℕ) : ℝ) ^ (-(2 * σ)) : ℝ))) y := by
    rwa [hcomp] at hy₁
  exact hy'.unique <| HasSum.mul (g := fun t : 𝓣 ↦ u t * (((t : ℕ) : ℝ) ^ (-(2 * σ)) : ℝ)) hX' hZ
    hy'.summable

/-- **Comparing two Dirichlet series differing only at square factors.** Let `A ≥ 0` be supported on
the products `m t ^ 2` of two families `𝓜`, `𝓣` of integers, with `A(m t ^ 2) = A(m) t ^ (-2σ)`,
and let `v` be supported there too, with `v(m t ^ 2) = A(m) u(t) t ^ (-2σ)` for a function `u`
vanishing off `𝓣`, bounded by `1`, with `u(1) = 1`. Then the sum of `v` is at least a fixed
multiple of the sum of `A`: both are the sum of `A` over `𝓜` times a Dirichlet series in
`t ^ (-2σ)`, the first of which is at most `ζ(2)` and the second of which is at least `2 - ζ(2)` in
absolute value. -/
lemma mul_le_norm_of_hasSum_of_hasSum (hσ : 1 ≤ σ) (hA0 : ∀ n, 0 ≤ A n)
    (hinj : Function.Injective fun z : 𝓜 × 𝓣 ↦ (z.1 : ℕ) * (z.2 : ℕ) ^ 2)
    (hoffA : ∀ n, (∀ m ∈ 𝓜, ∀ t ∈ 𝓣, n ≠ m * t ^ 2) → A n = 0)
    (hoffv : ∀ n, (∀ m ∈ 𝓜, ∀ t ∈ 𝓣, n ≠ m * t ^ 2) → v n = 0)
    (hA : ∀ m ∈ 𝓜, ∀ t ∈ 𝓣, A (m * t ^ 2) = A m * (t : ℝ) ^ (-(2 * σ)))
    (hv : ∀ m ∈ 𝓜, ∀ t ∈ 𝓣, v (m * t ^ 2) = (A m : ℂ) * (u t * (((t : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)))
    (hu : ∀ n, ‖u n‖ ≤ 1) (hu0 : ∀ n, n ∉ 𝓣 → u n = 0) (hu1 : u 1 = 1) (hx : HasSum A x)
    (hy : HasSum v y) : (2 - π ^ 2 / 6) / (π ^ 2 / 6) * x ≤ ‖y‖ := by
  classical
  have hπ : 0 < π ^ 2 / 6 := by positivity
  have hδ : 0 < 2 - π ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hX : Summable fun m : 𝓜 ↦ A m := hx.summable.comp_injective Subtype.val_injective
  have hX0 : 0 ≤ ∑' m : 𝓜, A m := tsum_nonneg fun m ↦ hA0 m
  have hu₁ : ∀ n, ‖(fun n ↦ if n ∈ 𝓣 then (1 : ℂ) else 0) n‖ ≤ 1 := fun n ↦ by
    beta_reduce
    split_ifs <;> simp
  have hxeq : (x : ℂ) = ((∑' m : 𝓜, A m : ℝ) : ℂ) *
      ∑' n : ℕ, (if n ∈ 𝓣 then (1 : ℂ) else 0) * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ) :=
    eq_tsum_mul_tsum_of_hasSum hσ hX hinj
      (fun n hn ↦ by rw [hoffA n hn, Complex.ofReal_zero]) hu₁ (fun n hn ↦ ite_eq_right hn)
      (fun m hm t ht ↦ by rw [hA m hm t ht, ite_eq_left ht, one_mul, Complex.ofReal_mul])
      (Complex.hasSum_ofReal.mpr hx)
  have hyeq : y = ((∑' m : 𝓜, A m : ℝ) : ℂ) * ∑' n : ℕ, u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ) :=
    eq_tsum_mul_tsum_of_hasSum hσ hX hinj hoffv hu hu0 hv hy
  have hZ₁le :
      ‖∑' n : ℕ, (if n ∈ 𝓣 then (1 : ℂ) else 0) * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ ≤ π ^ 2 / 6 :=
    norm_tsum_mul_rpow_le hu₁ hσ
  have hZ₂ge : 2 - π ^ 2 / 6 ≤ ‖∑' n : ℕ, u n * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ :=
    two_sub_pi_sq_le_norm_tsum hu hu1 hσ
  have hxle : x ≤ (∑' m : 𝓜, A m) * (π ^ 2 / 6) := by
    have h : ‖(x : ℂ)‖ = ‖((∑' m : 𝓜, A m : ℝ) : ℂ) *
        ∑' n : ℕ, (if n ∈ 𝓣 then (1 : ℂ) else 0) * (((n : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)‖ :=
      congrArg norm hxeq
    rw [Complex.norm_real, norm_mul, Complex.norm_real, Real.norm_of_nonneg hX0] at h
    exact (Real.le_norm_self x).trans (h.trans_le (mul_le_mul_of_nonneg_left hZ₁le hX0))
  have hyge : (∑' m : 𝓜, A m) * (2 - π ^ 2 / 6) ≤ ‖y‖ := by
    rw [hyeq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hX0]
    exact mul_le_mul_of_nonneg_left hZ₂ge hX0
  have hquot : (2 - π ^ 2 / 6) / (π ^ 2 / 6) * x ≤ (∑' m : 𝓜, A m) * (2 - π ^ 2 / 6) := by
    have h0 : 0 ≤ (2 - π ^ 2 / 6) / (π ^ 2 / 6) := by positivity
    refine (mul_le_mul_of_nonneg_left hxle h0).trans_eq ?_
    field_simp
  exact hquot.trans hyge

end RankinSelberg
