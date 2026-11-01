import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.CoefficientGrowth
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Jacobi forms of weight 2 and index 1

For a Jacobi form `φ ∈ J_{k,1}` the function `τ ↦ φ(τ, 0)` is a modular form of weight `k` on
`SL(2, ℤ)`: the transformation law of `φ` at `z = 0` is that of a modular form, and `φ(τ, 0)` is
bounded on `Im τ ≥ 1/2` by the bound of `ModularForm.jacobiSupBound`. As there are no nonzero
modular forms of weight `2` on `SL(2, ℤ)`, `φ(τ, 0) = 0` for every `φ ∈ J_{2,1}`, so that
`∑_r c(n, r) = 0` for every `n`.

A Jacobi form of index `1` is determined by its Taylor coefficients of order `0` and `2` at `z = 0`
(Eichler and Zagier, Theorem 3.5): on Fourier coefficients, `∑_r c(n, r) = 0` and
`∑_r r² c(n, r) = 0` for every `n` force `c = 0`, by induction on `n` with the elliptic
transformation law `c(n, r) = c(n - |r| + 1, |r| - 2)`. So `J_{2,1} = 0` as soon as the coefficient
of `z²` in `φ(τ, z)` vanishes; that coefficient is a cusp form of weight `4` on `SL(2, ℤ)`, hence
`0`, which is not proved here.

## Main definitions

* `ModularForm.jacobiRestrictZero`: the modular form `τ ↦ φ(τ, 0)` of a Jacobi form of index `1`.

## Main results

* `ModularForm.apply_zero_of_mem_jacobiFormSpace_two`: `φ(τ, 0) = 0` for `φ ∈ J_{2,1}`.
* `ModularForm.tsum_jacobiCoeff_eq_zero`: if `φ(τ, 0) = 0` for all `τ`, then `∑_r c(n, r) = 0`.
* `ModularForm.jacobiCoeff_eq_zero_of_tsum_eq_zero`: the Fourier coefficients vanish if
  `∑_r c(n, r) = 0` and `∑_r r² c(n, r) = 0` for every `n`.
* `ModularForm.eq_zero_of_mem_jacobiFormSpace_two_of_tsum_sq`: `φ ∈ J_{2,1}` vanishes if
  `∑_r r² c(n, r) = 0` for every `n`.
-/

open Complex UpperHalfPlane

open scoped MatrixGroups

namespace ModularForm

variable {k : ℤ} {φ : ℍ × ℂ → ℂ}

private lemma slash_jacobiRestrictZero (hφ : φ ∈ jacobiFormSpace k 1) (γ : SL(2, ℤ)) :
    (fun τ : ℍ ↦ φ (τ, 0)) ∣[k] γ = fun τ ↦ φ (τ, 0) := by
  ext τ
  have h : φ (γ • τ, 0 / denom γ τ) = jacobiFactor k 1 (τ, 0) γ * φ (τ, 0) := hφ.2.1 γ (τ, 0)
  simp only [zero_div, jacobiFactor, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, Complex.exp_zero, mul_one] at h
  rw [SL_slash_apply, h, zpow_neg, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero k (denom_ne_zero _ τ)), one_mul]

/-- The restriction `τ ↦ φ(τ, 0)` of a Jacobi form `φ ∈ J_{k,1}`, a modular form of weight `k` on
`SL(2, ℤ)`. -/
noncomputable def jacobiRestrictZero (hφ : φ ∈ jacobiFormSpace k 1) : ModularForm 𝒮ℒ k where
  toFun τ := φ (τ, 0)
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ slash_jacobiRestrictZero hφ γ
  holo' := hφ.1.comp (mdifferentiable_id.prodMk mdifferentiable_const)
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (slash_jacobiRestrictZero hφ γ).symm ▸ isBoundedAtImInfty_iff.mpr
      ⟨jacobiSupBound φ, 1 / 2, fun τ hτ ↦ norm_le_jacobiSupBound hφ hτ <| by
        rw [zero_im, abs_zero]
        positivity⟩

/-- **A Jacobi form of weight `2` and index `1` vanishes at `z = 0`**: `τ ↦ φ(τ, 0)` is a modular
form of weight `2` on `SL(2, ℤ)`, and there are none but `0`. -/
lemma apply_zero_of_mem_jacobiFormSpace_two (hφ : φ ∈ jacobiFormSpace 2 1) (τ : ℍ) : φ (τ, 0) = 0 :=
  congrArg (fun F : ModularForm 𝒮ℒ 2 ↦ F τ) <|
    rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero (jacobiRestrictZero hφ)

/-- **The coefficients of the restriction to `z = 0`**: if a Jacobi form `φ` of index `1`
vanishes on `z = 0`, then `∑_r c(n, r) = 0` for every `n`, these being the coefficients of the
`q`-expansion `φ(τ, 0) = ∑_n (∑_r c(n, r)) qⁿ`. -/
lemma tsum_jacobiCoeff_eq_zero (hφ : φ ∈ jacobiFormSpace k 1) (h : ∀ τ : ℍ, φ (τ, 0) = 0) (n : ℤ) :
    ∑' r : ℤ, jacobiCoeff φ (n, r) = 0 := by
  have hc : HasJacobiFourierExpansion φ (jacobiCoeff φ) :=
    hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ
  have hd : (fun p : ℤ × ℤ ↦ if p.2 = 0 then ∑' r : ℤ, jacobiCoeff φ (p.1, r) else 0) = 0 := by
    refine eq_zero_of_hasSum_jacobiFourierExp fun x ↦ ?_
    have he (p : ℤ × ℤ) : jacobiFourierExp p (x.1, 0) = jacobiFourierExp (p.1, 0) x := by
      simp [jacobiFourierExp]
    have h1 :
        HasSum (fun m : ℤ ↦ (∑' r : ℤ, jacobiCoeff φ (m, r)) * jacobiFourierExp (m, 0) x) 0 := by
      rw [← h x.1]
      refine (hc (x.1, 0)).prod_fiberwise fun m ↦ ?_
      have hs : Summable fun r : ℤ ↦ jacobiCoeff φ (m, r) * jacobiFourierExp (m, 0) x := by
        simpa only [he] using (hc (x.1, 0)).summable.prod_factor m
      have hs' : Summable fun r : ℤ ↦ jacobiCoeff φ (m, r) :=
        (summable_mul_right_iff (Complex.exp_ne_zero _)).mp hs
      simpa only [he] using hs'.hasSum.mul_right (jacobiFourierExp (m, 0) x)
    refine ((Prod.mk_left_injective (0 : ℤ)).hasSum_iff fun p hp ↦ ?_).mp ?_
    · have h0 : p.2 ≠ 0 := fun h0 ↦ hp ⟨p.1, Prod.ext rfl h0.symm⟩
      simp [h0]
    · simpa [Function.comp_def] using h1
  simpa using congrFun hd (n, 0)

/-- **A Jacobi form of index `1` is determined by its Taylor coefficients at `z = 0` of order `0`
and `2`** (Eichler and Zagier, Theorem 3.5), on Fourier coefficients: if `∑_r c(n, r) = 0` and
`∑_r r² c(n, r) = 0` for every `n`, then all the coefficients vanish. As `c(n, r)` only depends on
`4n - r²` (the elliptic transformation law), `c(n, r) = c(n - |r| + 1, |r| - 2)`: every coefficient
with `|r| ≥ 2` is one with a smaller `n`, so by induction on `n` the two sums are
`c(n, 0) + 2c(n, 1)` and `2c(n, 1)`. -/
lemma jacobiCoeff_eq_zero_of_tsum_eq_zero (hφ : φ ∈ jacobiFormSpace k 1)
    (h0 : ∀ n : ℤ, ∑' r : ℤ, jacobiCoeff φ (n, r) = 0)
    (h2 : ∀ n : ℤ, ∑' r : ℤ, (r : ℂ) ^ 2 * jacobiCoeff φ (n, r) = 0) : jacobiCoeff φ = 0 := by
  have key (m : ℕ) (n r : ℤ) (hn : n < m) : jacobiCoeff φ (n, r) = 0 := by
    induction m generalizing n r with
    | zero =>
      refine jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2.2 fun hp ↦ ?_
      simp only [Set.mem_ofPred_eq] at hp
      omega
    | succ m ih =>
      rcases lt_or_ge n m with h | h
      · exact ih n r h
      rcases (by omega : n = m) with rfl
      have hsupp (r : ℤ) (hr : r ∉ ({-1, 0, 1} : Finset ℤ)) : jacobiCoeff φ (m, r) = 0 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        have h2r : 2 ≤ |r| := le_abs.mpr (by omega)
        refine (jacobiCoeff_eq_of_mem_jacobiFormSpace_one hφ (n' := m - |r| + 1) (r' := |r| - 2)
          ?_).trans (ih _ _ (by omega))
        rw [← sq_abs r]
        ring1
      have hsym : jacobiCoeff φ (m, -1) = jacobiCoeff φ (m, 1) :=
        jacobiCoeff_eq_of_mem_jacobiFormSpace_one hφ (by ring1)
      have hs0 : ∑' r : ℤ, jacobiCoeff φ (m, r) =
          jacobiCoeff φ (m, -1) + jacobiCoeff φ (m, 0) + jacobiCoeff φ (m, 1) := by
        rw [tsum_eq_sum hsupp]
        simp [add_assoc]
      have hs2 : ∑' r : ℤ, (r : ℂ) ^ 2 * jacobiCoeff φ (m, r) =
          jacobiCoeff φ (m, -1) + jacobiCoeff φ (m, 1) := by
        rw [tsum_eq_sum (s := {-1, 0, 1}) fun r hr ↦ by rw [hsupp r hr, mul_zero]]
        simp
      have hc1 : jacobiCoeff φ (m, 1) = 0 := by
        linear_combination (h2 m - hs2 - hsym) / 2
      by_cases hr : r ∈ ({-1, 0, 1} : Finset ℤ)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hsym, hc1]
        · linear_combination h0 m - hs0 - hsym - 2 * hc1
        · exact hc1
      · exact hsupp r hr
  funext p
  exact key (p.1.toNat + 1) p.1 p.2 (by omega)

/-- **The vanishing of `J_{2,1}`, reduced to the `z²`-Taylor coefficient**: a Jacobi form
`φ ∈ J_{2,1}` vanishes as soon as `∑_r r² c(n, r) = 0` for every `n`, that is, as soon as the
coefficient `-2π² ∑_n (∑_r r² c(n, r)) qⁿ` of `z²` in `φ(τ, z)` vanishes; the coefficient of `z⁰`,
`φ(τ, 0)`, vanishes since there are no nonzero modular forms of weight `2` on `SL(2, ℤ)`. The
coefficient of `z²` is a cusp form of weight `4` on `SL(2, ℤ)`, hence `0` (Eichler and Zagier,
Theorem 3.5), which is not proved here. -/
lemma eq_zero_of_mem_jacobiFormSpace_two_of_tsum_sq (hφ : φ ∈ jacobiFormSpace 2 1)
    (h2 : ∀ n : ℤ, ∑' r : ℤ, (r : ℂ) ^ 2 * jacobiCoeff φ (n, r) = 0) : φ = 0 :=
  eq_zero_of_jacobiCoeff_eq_zero hφ <| jacobiCoeff_eq_zero_of_tsum_eq_zero hφ
    (tsum_jacobiCoeff_eq_zero hφ (apply_zero_of_mem_jacobiFormSpace_two hφ)) h2

end ModularForm
