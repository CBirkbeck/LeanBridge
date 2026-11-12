import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.HalfIntegralWeight
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.QuadraticGaussSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# The theta multiplier

Let `θ(z) = ∑_{n ∈ ℤ} e(n² z)`, where `e(x) = e^{2πix}`. Shimura's theta multiplier
`j(γ, z) = (c / d) ε_d⁻¹ (c z + d) ^ (1/2)`, `ModularForm.thetaFactor`, is the automorphy factor of
`θ` on `Γ₀(4)`: `θ(γ z) = j(γ, z) θ(z)`. The LMFDB defines the multiplier in
`mf.half_integral_weight` as the quotient `θ(γ z) / θ(z)`, and `ModularForm.halfIntegralWeightSpace`
left this unproved. The law is stated as a product; that the quotient is `j(γ, z)` at every `z`
also needs `θ(z) ≠ 0`, which `ModularForm.thetaSeries_apply_ne_zero` proves from the valence formula
for `θ²` (`ModularForm.thetaFactor_eq_div`).

The proof needs no cocycle computation and no reciprocity law. For `γ = (a, b; 4 c, d)` with `a > 0`
and `c > 0`, the inversion `θ(-1 / (4 w)) = (-2 i w) ^ (1/2) θ(w)` at `w = γ z` moves the problem to
the point `-c / a`, of odd denominator, where Poisson summation over the classes modulo `a` gives
`θ(-c / a + x) = (-i τ) ^ (-1/2) ∑_k G(-c, k; a) e^{-π i k² / τ}`, `τ = 2 a² x`. With
`x = -1 / (4 a (a z + b))` the exponential is `e(k² (z + b / a))`, and completing the square gives
`G(-c, k; a) = e(-b k² / a) G(-c, a)`, so that the sum over `k` is exactly `G(-c, a) θ(z)`. The two
square roots combine to `√a⁻¹ (4 c z + d) ^ (1/2)`, and
`G(-c, a) = (-c / a) ε_a √a` by the evaluation of quadratic Gauss sums of odd modulus.

## Main definitions

* `ModularForm.thetaSeries`: the theta function `θ`.

## Main results

* `ModularForm.tsum_cexp_add_sq`: Poisson summation for a shifted theta series.
* `ModularForm.jacobiTheta_two_mul_div_add`: the expansion of `θ` at a rational point.
* `ModularForm.jacobiTheta_mobius_mul_sqrt`: the multiplier of `θ` as a Gauss sum modulo `a`.
* `ModularForm.quadraticGaussSum_neg_eq`: the value of that Gauss sum.
* `ModularForm.thetaSeries_smul`: **the transformation law** `θ(γ z) = j(γ, z) θ(z)` on `Γ₀(4)`.
* `ModularForm.isBoundedAtImInfty_slash_thetaSeries`: `θ` is holomorphic at every cusp.
* `ModularForm.thetaSeries_mem_halfIntegralWeightSpace`: `θ ∈ M_{1/2}(4, 1)`.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. 97 (1973), 440–481.
* N. Koblitz, *Introduction to Elliptic Curves and Modular Forms*, 2nd ed., GTM 97, Chapter IV.
-/

open Complex CongruenceSubgroup Filter

open scoped Real MatrixGroups NumberTheorySymbols Manifold ComplexConjugate

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {a : ℕ} {b c d : ℤ} {x w : ℂ}

/-- Poisson summation for the shifted theta series:
`∑_q e^{π i τ (q + α)²} = (-i τ) ^ (-1/2) ∑_k e^{2π i k α} e^{-π i k² / τ}`. -/
lemma tsum_cexp_add_sq {τ : ℂ} (hτ : 0 < τ.im) (α : ℂ) : ∑' q : ℤ, cexp (π * I * τ * (q + α) ^ 2) =
    1 / (-I * τ) ^ (1 / 2 : ℂ) * ∑' k : ℤ, cexp (2 * π * I * k * α - π * I * k ^ 2 / τ) := by
  have hτ0 : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have h1 : jacobiTheta₂ (τ * α) τ = 1 / (-I * τ) ^ (1 / 2 : ℂ) *
      cexp (-π * I * (τ * α) ^ 2 / τ) * jacobiTheta₂ (τ * α / τ) (-1 / τ) :=
    jacobiTheta₂_functional_equation (τ * α) τ
  have h2 : (τ * α) / τ = α := mul_div_cancel_left₀ α hτ0
  have h3 : -π * I * (τ * α) ^ 2 / τ = -(π * I * τ * α ^ 2) := by
    field_simp
  rw [h2, h3] at h1
  have h4 : ∑' q : ℤ, cexp (π * I * τ * (q + α) ^ 2) =
      cexp (π * I * τ * α ^ 2) * jacobiTheta₂ (τ * α) τ := by
    rw [jacobiTheta₂, ← tsum_mul_left]
    refine tsum_congr fun q ↦ ?_
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    congr 1
    ring1
  have h5 : jacobiTheta₂ α (-1 / τ) = ∑' k : ℤ, cexp (2 * π * I * k * α - π * I * k ^ 2 / τ) := by
    refine tsum_congr fun k ↦ ?_
    rw [jacobiTheta₂_term]
    congr 1
    field_simp
    ring1
  rw [h4, h1, h5]
  have h6 : cexp (π * I * τ * α ^ 2) * cexp (-(π * I * τ * α ^ 2)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (norm := skip)
    (1 / (-I * τ) ^ (1 / 2 : ℂ) * ∑' k : ℤ, cexp (2 * π * I * k * α - π * I * k ^ 2 / τ)) * h6
  ring1

variable (a b) [NeZero a] in
/-- **The expansion of `θ` at a rational point**: for `a ≥ 1`, an integer `b` and `Im x > 0`,
`θ(b / a + x) = (-i τ) ^ (-1/2) ∑_k G(b, k; a) e^{-π i k² / τ}`, where `θ(z) = ∑_n e(n² z)` is
`jacobiTheta (2 z)`, `τ = 2 a² x` and `G(b, k; a) = ∑_{r mod a} e((b r² + k r) / a)`. -/
lemma jacobiTheta_two_mul_div_add (hx : 0 < x.im) : jacobiTheta (2 * ((b : ℂ) / a + x)) =
    1 / (-I * (2 * a ^ 2 * x)) ^ (1 / 2 : ℂ) * ∑' k : ℤ,
      (∑ r : ZMod a, ZMod.stdAddChar ((b : ZMod a) * r ^ 2 + (k : ZMod a) * r)) *
        cexp (-π * I * k ^ 2 / (2 * a ^ 2 * x)) := by
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr (NeZero.pos a)
  have hτ : 0 < (2 * (a : ℂ) ^ 2 * x).im := by
    have e : (2 * (a : ℂ) ^ 2 * x) = ((2 * (a : ℝ) ^ 2 : ℝ) : ℂ) * x := by
      push_cast
      rfl
    rw [e, im_ofReal_mul]
    positivity
  have hτ₀ : 0 < (2 * ((b : ℂ) / a + x)).im := by
    have e : (2 * ((b : ℂ) / a + x)).im = 2 * x.im := by
      have e1 : ((b : ℂ) / a) = (((b : ℝ) / a : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [e1]
      simp
    rw [e]
    positivity
  have hs : Summable fun n : ℤ ↦ cexp (π * I * (n : ℂ) ^ 2 * (2 * ((b : ℂ) / a + x))) := by
    refine ((summable_jacobiTheta₂_term_iff 0 _).mpr hτ₀).congr fun n ↦ ?_
    simp [jacobiTheta₂_term]
  have hτ0 : (2 * (a : ℂ) ^ 2 * x) ≠ 0 := fun h ↦ by simp [h] at hτ
  have hτ' : 0 < (-1 / (2 * (a : ℂ) ^ 2 * x)).im := by
    rw [neg_div, one_div, neg_im, inv_im, neg_div, neg_neg]
    exact div_pos hτ (normSq_pos.mpr hτ0)
  have hsk : ∀ r : ℕ, Summable fun k : ℤ ↦
      cexp (2 * π * I * k * ((r : ℂ) / a) - π * I * k ^ 2 / (2 * a ^ 2 * x)) := fun r ↦ by
    refine ((summable_jacobiTheta₂_term_iff ((r : ℂ) / a) _).mpr hτ').congr fun k ↦ ?_
    rw [jacobiTheta₂_term]
    congr 1
    ring1
  have hq : ∀ r : Fin a, ∑' q : ℤ, cexp (π * I * ((q * a + (r : ℕ) : ℤ) : ℂ) ^ 2 *
      (2 * ((b : ℂ) / a + x))) = cexp (2 * π * I * b * ((r : ℕ) : ℂ) ^ 2 / a) *
        (1 / (-I * (2 * a ^ 2 * x)) ^ (1 / 2 : ℂ) * ∑' k : ℤ,
          cexp (2 * π * I * k * (((r : ℕ) : ℂ) / a) - π * I * k ^ 2 / (2 * a ^ 2 * x))) := by
    intro r
    rw [← tsum_cexp_add_sq hτ, ← tsum_mul_left]
    refine tsum_congr fun q ↦ ?_
    rw [← Complex.exp_add]
    have hm : ((b * (q ^ 2 * a + 2 * q * (r : ℕ)) : ℤ) : ℂ) * (2 * π * I) +
        (2 * π * I * b * ((r : ℕ) : ℂ) ^ 2 / a + π * I * (2 * a ^ 2 * x) *
          ((q : ℂ) + ((r : ℕ) : ℂ) / a) ^ 2) = π * I * ((q * a + (r : ℕ) : ℤ) : ℂ) ^ 2 *
            (2 * ((b : ℂ) / a + x)) := by
      push_cast
      field_simp
      ring1
    rw [← hm, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  have hk : ∀ k : ℤ, (∑ r : ZMod a, ZMod.stdAddChar ((b : ZMod a) * r ^ 2 + (k : ZMod a) * r)) *
      cexp (-π * I * k ^ 2 / (2 * a ^ 2 * x)) = ∑ r : Fin a,
        cexp (2 * π * I * b * ((r : ℕ) : ℂ) ^ 2 / a) *
          cexp (2 * π * I * k * (((r : ℕ) : ℂ) / a) - π * I * k ^ 2 / (2 * a ^ 2 * x)) := fun k ↦ by
    rw [← ZMod.sum_range_natCast_eq, ← Fin.sum_univ_eq_sum_range (fun r : ℕ ↦
      ZMod.stdAddChar ((b : ZMod a) * (r : ZMod a) ^ 2 + (k : ZMod a) * (r : ZMod a))) a,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have e : (b : ZMod a) * (((r : ℕ) : ℕ) : ZMod a) ^ 2 + (k : ZMod a) * (((r : ℕ) : ℕ) : ZMod a) =
        ((b * ((r : ℕ) : ℤ) ^ 2 + k * ((r : ℕ) : ℤ) : ℤ) : ZMod a) := by
      push_cast
      rfl
    rw [e, ZMod.stdAddChar_coe, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring1
  simp only [hk]
  have hswap : ∑' k : ℤ, ∑ r : Fin a, cexp (2 * π * I * b * ((r : ℕ) : ℂ) ^ 2 / a) *
      cexp (2 * π * I * k * (((r : ℕ) : ℂ) / a) - π * I * k ^ 2 / (2 * a ^ 2 * x)) =
        ∑ r : Fin a, ∑' k : ℤ, cexp (2 * π * I * b * ((r : ℕ) : ℂ) ^ 2 / a) *
          cexp (2 * π * I * k * (((r : ℕ) : ℂ) / a) - π * I * k ^ 2 / (2 * a ^ 2 * x)) :=
    Summable.tsum_finsetSum fun r _ ↦ (hsk r).mul_left _
  rw [jacobiTheta, TauCeti.tsum_int_eq_sum_fin_tsum hs a, hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [tsum_mul_left]
  refine (hq r).trans ?_
  ring1

variable (a b) in
private lemma im_two_mul_div_add (hx : 0 < x.im) : 0 < (2 * ((b : ℂ) / a + x)).im := by
  have e : (2 * ((b : ℂ) / a + x)).im = 2 * x.im := by
    have e1 : ((b : ℂ) / a) = (((b : ℝ) / a : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [e1]
    simp
  rw [e]
  positivity

variable (a) [NeZero a] in
private lemma sum_stdAddChar_complete_square (k : ℤ) (h : ((4 * b * c : ℤ) : ZMod a) = -1) :
    ∑ r : ZMod a, ZMod.stdAddChar (((-c : ℤ) : ZMod a) * r ^ 2 + (k : ZMod a) * r) =
      ZMod.stdAddChar ((-b * k ^ 2 : ℤ) : ZMod a) * ZMod.quadraticGaussSum (-c) a := by
  have hs : ∀ r : ZMod a, ((-c : ℤ) : ZMod a) * r ^ 2 + (k : ZMod a) * r =
      ((-b * k ^ 2 : ℤ) : ZMod a) + ((-c : ℤ) : ZMod a) * (r + ((2 * b * k : ℤ) : ZMod a)) ^ 2 := by
    intro r
    push_cast at h ⊢
    linear_combination ((r : ZMod a) * k + (b : ZMod a) * k ^ 2) * h
  simp only [hs, AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum, ZMod.quadraticGaussSum]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight ((2 * b * k : ℤ) : ZMod a))
    fun r ↦ ZMod.stdAddChar (((-c : ℤ) : ZMod a) * r ^ 2)

private lemma cpow_half_mul_eq_sqrt {A B : ℂ} {r : ℝ} (hA : 0 < A.re) (hB : 0 < B.re)
    (hw : 0 < w.im) (hr : 0 < r) (h : A * B * w = r) :
    A ^ (1 / 2 : ℂ) * B ^ (1 / 2 : ℂ) * w ^ (1 / 2 : ℂ) = (Real.sqrt r : ℂ) := by
  have hA0 : A ≠ 0 := fun h0 ↦ by simp [h0] at hA
  have hB0 : B ≠ 0 := fun h0 ↦ by simp [h0] at hB
  have hw0 : w ≠ 0 := fun h0 ↦ by simp [h0] at hw
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hargA : |A.arg| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)
  have hargB : |B.arg| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB)
  have hargw : 0 ≤ w.arg := arg_nonneg_iff.mpr hw.le
  have hargw' : w.arg ≤ π := arg_le_pi w
  have hexp : cexp (log A + log B + log w - log r) = 1 := by
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_add, exp_log hA0, exp_log hB0, exp_log hw0,
      exp_log hr0, h, div_self hr0]
  rcases Complex.exp_eq_one_iff.mp hexp with ⟨n, hn⟩
  have hE : A.arg + B.arg + w.arg = n * (2 * π) := by
    simpa [log_im, arg_ofReal_of_nonneg hr.le] using congrArg Complex.im hn
  have hpi : 0 < π := Real.pi_pos
  rcases abs_lt.mp hargA with ⟨hA1, hA2⟩
  rcases abs_lt.mp hargB with ⟨hB1, hB2⟩
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) < 1 := by
      by_contra hcon
      nlinarith [not_lt.mp hcon]
    have h2 : (-1 : ℝ) < n := by
      by_contra hcon
      nlinarith [not_lt.mp hcon]
    have h3 : n < 1 := by exact_mod_cast h1
    have h4 : -1 < n := by exact_mod_cast h2
    omega
  rw [hn0, Int.cast_zero, zero_mul, sub_eq_zero] at hn
  rw [cpow_def_of_ne_zero hA0, cpow_def_of_ne_zero hB0, cpow_def_of_ne_zero hw0, ← Complex.exp_add,
    ← Complex.exp_add, ← add_mul, ← add_mul, hn, ← cpow_def_of_ne_zero hr0, Real.sqrt_eq_rpow,
    ofReal_cpow hr.le]
  push_cast
  rfl

private lemma jacobiTheta_eq_one_div_mul (τ : ℂ) :
    jacobiTheta τ = 1 / (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta (-1 / τ) := by
  simpa [jacobiTheta_eq_jacobiTheta₂] using jacobiTheta₂_functional_equation 0 τ

private lemma im_neg_one_div_pos {t : ℂ} (ht : 0 < t.im) : 0 < (-1 / t).im := by
  have ht0 : t ≠ 0 := fun h ↦ by simp [h] at ht
  rw [neg_div, one_div, neg_im, inv_im, neg_div, neg_neg]
  exact div_pos ht (normSq_pos.mpr ht0)

variable [NeZero a] in
/-- **The multiplier of `θ` at `(a, b; 4 c, d)` as a Gauss sum modulo the entry `a > 0`**: for
`c > 0` and `a d - 4 b c = 1`, `θ((a z + b) / (4 c z + d)) √a = G(-c, a) (4 c z + d) ^ (1/2) θ(z)`,
where `θ(z) = jacobiTheta (2 z)` and the square root is principal. The proof applies the inversion
`θ(-1 / (4 z)) = (-2 i z) ^ (1/2) θ(z)` and the expansion of `θ` at the point `-c / a` of odd
denominator, whose Gauss sums are `G(-c, k; a) = e(-b k² / a) G(-c, a)` by completing the square; no
reciprocity law is needed. -/
lemma jacobiTheta_mobius_mul_sqrt (hc : 0 < c) (hdet : (a : ℤ) * d - b * (4 * c) = 1) (z : ℍ) :
    jacobiTheta (2 * (((a : ℂ) * z + b) / (4 * c * z + d))) * (Real.sqrt a : ℂ) =
      ZMod.quadraticGaussSum (-c) a * (4 * c * (z : ℂ) + d) ^ (1 / 2 : ℂ) *
        jacobiTheta (2 * z) := by
  have ha : (0 : ℝ) < a := Nat.cast_pos.mpr (NeZero.pos a)
  have hac : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hy : 0 < (z : ℂ).im := z.im_pos
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have him₁ : 0 < ((a : ℂ) * z + b).im := by
    have e : ((a : ℂ) * z + b).im = a * (z : ℂ).im := by simp
    rw [e]
    positivity
  have himw : 0 < (4 * c * (z : ℂ) + d).im := by
    have e : (4 * c * (z : ℂ) + d).im = 4 * c * (z : ℂ).im := by simp
    rw [e]
    positivity
  have hw₁ : ((a : ℂ) * z + b) ≠ 0 := fun h ↦ by simp [h] at him₁
  have hw : (4 * c * (z : ℂ) + d) ≠ 0 := fun h ↦ by simp [h] at himw
  have hdetc : (a : ℂ) * d - b * (4 * c) = 1 := by exact_mod_cast hdet
  have hx : 0 < (-1 / (4 * (a : ℂ) * ((a : ℂ) * z + b))).im := by
    refine im_neg_one_div_pos ?_
    have e : (4 * (a : ℂ) * ((a : ℂ) * z + b)) = ((4 * a : ℝ) : ℂ) * ((a : ℂ) * z + b) := by
      push_cast
      rfl
    rw [e, im_ofReal_mul]
    positivity
  have hτ' : 0 < (2 * (a : ℂ) ^ 2 * (-1 / (4 * (a : ℂ) * ((a : ℂ) * z + b)))).im := by
    have e : (2 * (a : ℂ) ^ 2 * (-1 / (4 * (a : ℂ) * ((a : ℂ) * z + b)))) =
        ((2 * (a : ℝ) ^ 2 : ℝ) : ℂ) * (-1 / (4 * (a : ℂ) * ((a : ℂ) * z + b))) := by
      push_cast
      rfl
    rw [e, im_ofReal_mul]
    positivity
  have hT : 0 < (2 * (((-c : ℤ) : ℂ) / a + -1 / (4 * (a : ℂ) * ((a : ℂ) * z + b)))).im :=
    im_two_mul_div_add a (-c) hx
  have e1 : 2 * (((-c : ℤ) : ℂ) / a + -1 / (4 * (a : ℂ) * ((a : ℂ) * z + b))) =
      -1 / (2 * (((a : ℂ) * z + b) / (4 * c * z + d))) := by
    push_cast
    field_simp
    linear_combination 4 * hdetc
  have hτ : 2 * (((a : ℂ) * z + b) / (4 * c * z + d)) =
      -1 / (2 * (((-c : ℤ) : ℂ) / a + -1 / (4 * (a : ℂ) * ((a : ℂ) * z + b)))) := by
    rw [e1]
    field_simp
  have himτ : 0 < (2 * (((a : ℂ) * z + b) / (4 * c * z + d))).im := by
    rw [hτ]
    exact im_neg_one_div_pos hT
  have hmod : ((4 * b * c : ℤ) : ZMod a) = -1 := by
    have h1 : (((a : ℤ) * d - b * (4 * c) : ℤ) : ZMod a) = ((1 : ℤ) : ZMod a) :=
      congrArg (Int.cast : ℤ → ZMod a) hdet
    push_cast at h1 ⊢
    rw [ZMod.natCast_self, zero_mul, zero_sub] at h1
    linear_combination -h1
  have hterm : ∀ k : ℤ, (∑ r : ZMod a, ZMod.stdAddChar (((-c : ℤ) : ZMod a) * r ^ 2 +
      (k : ZMod a) * r)) * cexp (-π * I * k ^ 2 /
        (2 * (a : ℂ) ^ 2 * (-1 / (4 * (a : ℂ) * ((a : ℂ) * z + b))))) =
          ZMod.quadraticGaussSum (-c) a * cexp (π * I * (k : ℂ) ^ 2 * (2 * z)) := fun k ↦ by
    rw [sum_stdAddChar_complete_square a k hmod, ZMod.stdAddChar_coe, mul_right_comm,
      ← Complex.exp_add, mul_comm]
    congr 2
    push_cast
    field_simp
    ring1
  have hθT : jacobiTheta (2 * (((-c : ℤ) : ℂ) / a + -1 / (4 * (a : ℂ) * ((a : ℂ) * z + b)))) =
      1 / (-I * (2 * (a : ℂ) ^ 2 * (-1 / (4 * (a : ℂ) * ((a : ℂ) * z + b))))) ^ (1 / 2 : ℂ) *
        (ZMod.quadraticGaussSum (-c) a * jacobiTheta (2 * z)) := by
    rw [jacobiTheta_two_mul_div_add a (-c) hx]
    simp only [hterm]
    rw [tsum_mul_left]
    rfl
  have hF : jacobiTheta (2 * (((a : ℂ) * z + b) / (4 * c * z + d))) =
      1 / (-I * (2 * (((a : ℂ) * z + b) / (4 * c * z + d)))) ^ (1 / 2 : ℂ) *
        jacobiTheta (-1 / (2 * (((a : ℂ) * z + b) / (4 * c * z + d)))) :=
    jacobiTheta_eq_one_div_mul _
  rw [← e1, hθT] at hF
  have hprod : (-I * (2 * (((a : ℂ) * z + b) / (4 * c * z + d)))) *
      (-I * (2 * (a : ℂ) ^ 2 * (-1 / (4 * (a : ℂ) * ((a : ℂ) * z + b))))) * (4 * c * (z : ℂ) + d) =
        ((a : ℝ) : ℂ) := by
    have hII : (-I) * (-I) = -1 := by
      rw [neg_mul_neg, I_mul_I]
    have e : ∀ W₁ W : ℂ, W₁ ≠ 0 → W ≠ 0 → (-I * (2 * (W₁ / W))) *
        (-I * (2 * (a : ℂ) ^ 2 * (-1 / (4 * (a : ℂ) * W₁)))) * W = ((-I) * (-I)) * (-(a : ℂ)) := by
      intro W₁ W h₁ h₂
      field_simp
      ring1
    rw [e _ _ hw₁ hw, hII, ofReal_natCast]
    ring1
  have hbr : (-I * (2 * (((a : ℂ) * z + b) / (4 * c * z + d)))) ^ (1 / 2 : ℂ) *
      (-I * (2 * (a : ℂ) ^ 2 * (-1 / (4 * (a : ℂ) * ((a : ℂ) * z + b))))) ^ (1 / 2 : ℂ) *
        (4 * c * (z : ℂ) + d) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) :=
    cpow_half_mul_eq_sqrt (by simpa using himτ) (by simpa using hτ') himw ha hprod
  have hs0 : (Real.sqrt a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
  rw [← hbr] at hs0
  have haux : ∀ {Sa Sb Sw G θ : ℂ}, Sa ≠ 0 → Sb ≠ 0 →
      1 / Sa * (1 / Sb * (G * θ)) * (Sa * Sb * Sw) = G * Sw * θ := by
    intro Sa Sb Sw G θ h₁ h₂
    field_simp
  rw [hF, ← hbr]
  exact haux (left_ne_zero_of_mul (left_ne_zero_of_mul hs0))
    (right_ne_zero_of_mul (left_ne_zero_of_mul hs0))

variable (c) in
private lemma jacobiSym_four_mul {n : ℕ} (hn : Odd n) : J(4 * c | n) = J(c | n) := by
  have h1 : J((2 : ℤ) ^ 2 | n) = 1 := jacobiSym.sq_one' (by
    have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
    simpa [Int.gcd] using h2)
  have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
  rw [jacobiSym.mul_left, h4, h1, one_mul]

private lemma jacobiSym_eq_of_mul_mod (hc : 0 < c) {n : ℕ} (ha : Odd a) (hn : Odd n)
    (h : (a * n) % (4 * c.natAbs) = 1 ∨ (a * n) % (4 * c.natAbs) = 4 * c.natAbs - 1) :
    J(c | a) = J(c | n) := by
  have hc' : 1 ≤ c.natAbs := by omega
  have h1 : J(c | a * n) = 1 := by
    rw [jacobiSym.mod_right c (ha.mul hn)]
    rcases h with h | h
    · rw [h, jacobiSym.one_right]
    · rw [h]
      have hm : Odd (4 * c.natAbs - 1) := by
        rw [Nat.odd_iff]
        omega
      have h2 : ((4 * c) % ((4 * c.natAbs - 1 : ℕ) : ℤ)) = (1 % ((4 * c.natAbs - 1 : ℕ) : ℤ)) := by
        have h3 : ((4 * c.natAbs - 1 : ℕ) : ℤ) = 4 * c - 1 := by
          omega
        rw [h3]
        have h4 : 4 * c = 1 + (4 * c - 1) := by ring1
        exact (congrArg (· % (4 * c - 1)) h4).trans (Int.add_emod_right 1 (4 * c - 1))
      rw [← jacobiSym_four_mul c hm, jacobiSym.mod_left' h2, jacobiSym.one_left]
  rw [jacobiSym.mul_right' c ha.pos.ne' hn.pos.ne'] at h1
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3]

private lemma thetaEpsilon_eq_of_mul {A : ℤ} (h : (A * d) % 4 = 1) :
    thetaEpsilon A = thetaEpsilon d := by
  have hA : A % 4 = 0 ∨ A % 4 = 1 ∨ A % 4 = 2 ∨ A % 4 = 3 := by omega
  have hd : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
  rw [Int.mul_emod] at h
  simp only [thetaEpsilon]
  rcases hA with hA | hA | hA | hA <;> rcases hd with hd | hd | hd | hd <;> rw [hA, hd] at h <;>
    first
    | exact absurd h (by decide)
    | simp [hA, hd]

private lemma thetaEpsilon_of_emod_eq_one (h : d % 4 = 1) : thetaEpsilon d = 1 := by
  simp [thetaEpsilon, h]

private lemma thetaEpsilon_of_emod_ne_one (h : ¬d % 4 = 1) : thetaEpsilon d = I := by
  simp [thetaEpsilon, h]

private lemma jacobiSym_neg_one_mul_thetaEpsilon (ha : Odd a) :
    (J(-1 | a) : ℂ) * thetaEpsilon a = (thetaEpsilon a)⁻¹ := by
  rw [jacobiSym.at_neg_one ha]
  have h1 : a % 4 = 1 ∨ a % 4 = 3 := by
    rcases ha with ⟨t, rfl⟩
    omega
  rcases h1 with h1 | h1
  · have h2 : (a : ℤ) % 4 = 1 := by omega
    rw [ZMod.χ₄_nat_one_mod_four h1, thetaEpsilon_of_emod_eq_one h2]
    simp
  · have h2 : ¬(a : ℤ) % 4 = 1 := by omega
    rw [ZMod.χ₄_nat_three_mod_four h1, thetaEpsilon_of_emod_ne_one h2, inv_I]
    simp

variable [NeZero a] in
/-- **The multiplier of `θ` as a symbol.** For `c > 0` and `a d - 4 b c = 1` with `a > 0`, the Gauss
sum `G(-c, a)` is `(4 c / d) ε_d⁻¹ √a`. -/
lemma quadraticGaussSum_neg_eq (hc : 0 < c) (hdet : (a : ℤ) * d - b * (4 * c) = 1) :
    ZMod.quadraticGaussSum (-c) a =
      shimuraSymbol (4 * c) d * (thetaEpsilon d)⁻¹ * (Real.sqrt a : ℂ) := by
  have hodd : Odd a := by
    rcases Nat.even_or_odd a with ⟨t, ht⟩ | h
    · refine absurd (⟨t * d - 2 * (b * c), ?_⟩ : (2 : ℤ) ∣ 1) (by omega)
      rw [← hdet, ht]
      push_cast
      ring1
    · exact h
  have hoddd : Odd d.natAbs := by
    refine Int.natAbs_odd.mpr ?_
    rcases Int.even_or_odd d with ⟨t, ht⟩ | h
    · refine absurd (⟨a * t - 2 * (b * c), ?_⟩ : (2 : ℤ) ∣ 1) (by omega)
      rw [← hdet, ht]
      ring1
    · exact h
  have hcop : IsCoprime (-c) (a : ℤ) := ⟨4 * b, d, by linarith⟩
  have hsqrt : (Real.sqrt a : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos a))).ne'
  have hG : ZMod.quadraticGaussSum 1 a = thetaEpsilon a * (Real.sqrt a : ℂ) := by
    have h1 : a % 4 = 1 ∨ a % 4 = 3 := by
      rcases hodd with ⟨t, rfl⟩
      omega
    rcases h1 with h1 | h1
    · have h2 : (a : ℤ) % 4 = 1 := by omega
      rw [ZMod.quadraticGaussSum_one_of_mod_four_eq_one a h1, thetaEpsilon_of_emod_eq_one h2,
        one_mul]
    · have h2 : ¬(a : ℤ) % 4 = 1 := by omega
      rw [ZMod.quadraticGaussSum_one_of_mod_four_eq_three a h1, thetaEpsilon_of_emod_ne_one h2]
  have hmod4 : ((a : ℤ) * d) % 4 = 1 := by
    have h1 : (a : ℤ) * d = 1 + 4 * (b * c) := by linarith
    rw [h1]
    omega
  have hC : (c.natAbs : ℤ) = c := by omega
  have hJ : J(c | a) = J(c | d.natAbs) := by
    refine jacobiSym_eq_of_mul_mod hc hodd hoddd ?_
    have hprod : ((a * d.natAbs : ℕ) : ℤ) = (a : ℤ) * |d| := by
      push_cast
      rfl
    rcases abs_cases d with ⟨h1, -⟩ | ⟨h1, -⟩
    · left
      have h2 : ((a * d.natAbs : ℕ) : ℤ) = 1 + 4 * (c.natAbs : ℤ) * b := by
        rw [hprod, h1, hC]
        linarith
      have h3 : ((a * d.natAbs : ℕ) : ℤ) % (4 * (c.natAbs : ℤ)) = 1 := by
        rw [h2, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by norm_num) (by omega)
      exact_mod_cast h3
    · right
      have h2 :
          ((a * d.natAbs : ℕ) : ℤ) = (4 * (c.natAbs : ℤ) - 1) + 4 * (c.natAbs : ℤ) * (-b - 1) := by
        rw [hprod, h1, hC]
        linarith
      have h3 : ((a * d.natAbs : ℕ) : ℤ) % (4 * (c.natAbs : ℤ)) = 4 * (c.natAbs : ℤ) - 1 := by
        rw [h2, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      have h4 : 1 ≤ 4 * c.natAbs := by omega
      have h5 : ((a * d.natAbs % (4 * c.natAbs) : ℕ) : ℤ) = ((4 * c.natAbs - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub h4]
        push_cast at h3 ⊢
        exact h3
      exact_mod_cast h5
  have hsym : shimuraSymbol (4 * c) d = J(c | d.natAbs) := by
    have h1 : ¬(4 * c < 0 ∧ d < 0) := by omega
    simp only [shimuraSymbol, h1]
    exact jacobiSym_four_mul c hoddd
  have hneg : J(-c | a) = J(-1 | a) * J(c | a) := by
    rw [← jacobiSym.mul_left]
    simp
  rw [ZMod.quadraticGaussSum_eq_jacobiSym_mul (-c) a hodd hcop, hG, hneg, hsym, ← hJ,
    ← thetaEpsilon_eq_of_mul hmod4, ← jacobiSym_neg_one_mul_thetaEpsilon hodd]
  push_cast
  ring1

private lemma jacobiTheta_two_mul_add_intCast (n : ℤ) :
    jacobiTheta (2 * (x + n)) = jacobiTheta (2 * x) := by
  have hp : Function.Periodic jacobiTheta 2 := fun τ ↦ by
    rw [add_comm]
    exact jacobiTheta_two_add τ
  have e : 2 * (x + n) = 2 * x + n * 2 := by ring1
  rw [e]
  exact hp.int_mul n _

variable {γ : SL(2, ℤ)} (z : ℍ)

variable (γ) in
lemma coe_smul_eq_div :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
  simpa only [eq_intCast, ofReal_intCast] using UpperHalfPlane.coe_specialLinearGroup_apply γ z

variable (γ) in
lemma denomZ_ne_zero : (γ 1 0 : ℂ) * (z : ℂ) + γ 1 1 ≠ 0 := by
  rw [← ModularGroup.denom_apply]
  exact denom_ne_zero γ z

variable (γ) in
lemma denomZ_conj_ne_zero : (γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1 ≠ 0 := by
  intro h
  have h1 : conj ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1) = conj 0 := congrArg conj h
  simp only [map_add, map_mul, conj_conj, map_intCast, map_zero] at h1
  exact denomZ_ne_zero γ z h1

variable (γ) in
lemma conj_coe_smul : conj ((γ • z : ℍ) : ℂ) =
    ((γ 0 0 : ℂ) * conj (z : ℂ) + γ 0 1) / ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1) := by
  rw [coe_smul_eq_div]
  simp only [map_div₀, map_add, map_mul, map_intCast]

variable (γ) in
lemma coe_im_smul : (((γ • z : ℍ).im : ℝ) : ℂ) =
    (z.im : ℂ) / (((γ 1 0 : ℂ) * z + γ 1 1) * ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1)) := by
  have h1 : (γ • z : ℍ).im = z.im / normSq (denom γ z) := ModularGroup.im_smul_eq_div_normSq γ z
  have h2 : ((normSq (denom γ z) : ℝ) : ℂ) =
      ((γ 1 0 : ℂ) * z + γ 1 1) * ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1) := by
    rw [← Complex.mul_conj, ModularGroup.denom_apply]
    simp only [map_add, map_mul, map_intCast]
  rw [h1]
  push_cast
  rw [h2]

private lemma jacobiTheta_smul_of_pos (hγ : γ ∈ Gamma0 4) (hc : 0 < γ 1 0) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) = thetaFactor γ z * jacobiTheta (2 * z) := by
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 4).mp (Gamma0_mem.mp hγ) with ⟨c, hc4⟩
  have hc4' : γ 1 0 = 4 * c := by
    rw [hc4]
    rfl
  have hc0 : 0 < c := by omega
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  have hapos : 0 < γ 0 0 + (|γ 0 0| + 1) * γ 1 0 := by
    have h1 : 1 ≤ γ 1 0 := hc
    have h2 : -|γ 0 0| ≤ γ 0 0 := neg_abs_le (γ 0 0)
    nlinarith [abs_nonneg (γ 0 0)]
  rcases Int.eq_ofNat_of_zero_le hapos.le with ⟨a, ha⟩
  have ha0 : NeZero a := ⟨fun h ↦ by rw [h] at ha; simp at ha; omega⟩
  have hdet' : (a : ℤ) * γ 1 1 - (γ 0 1 + (|γ 0 0| + 1) * γ 1 1) * (4 * c) = 1 := by
    rw [← ha, ← hc4']
    linear_combination hdet
  have key : jacobiTheta (2 * (((a : ℂ) * z + ((γ 0 1 + (|γ 0 0| + 1) * γ 1 1 : ℤ) : ℂ)) /
      (4 * c * z + γ 1 1))) * (Real.sqrt a : ℂ) = ZMod.quadraticGaussSum (-c) a *
        (4 * c * (z : ℂ) + γ 1 1) ^ (1 / 2 : ℂ) * jacobiTheta (2 * z) :=
    jacobiTheta_mobius_mul_sqrt hc0 hdet' z
  rw [quadraticGaussSum_neg_eq hc0 hdet'] at key
  have hs0 : (Real.sqrt a : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos a))).ne'
  have hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / (4 * c * z + γ 1 1) := by
    rw [coe_smul_eq_div, hc4']
    push_cast
    rfl
  have hden : denom γ z = 4 * c * z + γ 1 1 := by
    rw [ModularGroup.denom_apply, hc4']
    push_cast
    rfl
  have hD : (4 * c * (z : ℂ) + γ 1 1) ≠ 0 := hden ▸ denom_ne_zero γ z
  have ha' : (a : ℂ) = γ 0 0 + (|γ 0 0| + 1 : ℤ) * (4 * c) := by
    have h1 : (a : ℤ) = γ 0 0 + (|γ 0 0| + 1) * (4 * c) := by
      rw [← ha, hc4']
    exact_mod_cast h1
  have harg : ((a : ℂ) * z + ((γ 0 1 + (|γ 0 0| + 1) * γ 1 1 : ℤ) : ℂ)) / (4 * c * z + γ 1 1) =
      ((γ • z : ℍ) : ℂ) + ((|γ 0 0| + 1 : ℤ) : ℂ) := by
    rw [hsm, ha']
    field_simp
    push_cast
    ring1
  rw [harg, jacobiTheta_two_mul_add_intCast] at key
  have hsym : ((shimuraSymbol (γ 1 0) (γ 1 1) : ℤ) : ℂ) = shimuraSymbol (4 * c) (γ 1 1) := by
    rw [hc4']
  refine mul_right_cancel₀ hs0 (key.trans ?_)
  rw [thetaFactor, hden, hsym]
  ring1

private lemma cpow_half_neg (hw : w.im < 0) : (-w) ^ (1 / 2 : ℂ) = I * w ^ (1 / 2 : ℂ) := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  have hlog : log (-w) = log w + π * I := by
    rw [log, log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hw]
    push_cast
    ring1
  rw [cpow_def_of_ne_zero (neg_ne_zero.mpr hw0), cpow_def_of_ne_zero hw0, hlog, add_mul,
    Complex.exp_add, mul_comm]
  congr 1
  have e : (π : ℂ) * I * (1 / 2) = π / 2 * I := by ring1
  rw [e, exp_pi_div_two_mul_I]

private lemma odd_of_det_right (hγ : γ 1 0 = 0 ∨ γ ∈ Gamma0 4) : Odd (γ 1 1) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  rcases Int.even_or_odd (γ 1 1) with ⟨t, ht⟩ | h
  · rcases hγ with h0 | hγ
    · rw [h0, ht] at hdet
      refine absurd (⟨γ 0 0 * t, ?_⟩ : (2 : ℤ) ∣ 1) (by omega)
      linear_combination -hdet
    · rcases (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 4).mp (Gamma0_mem.mp hγ) with ⟨c, hc4⟩
      have hc4' : γ 1 0 = 4 * c := by
        rw [hc4]
        rfl
      rw [hc4', ht] at hdet
      refine absurd (⟨γ 0 0 * t - 2 * (γ 0 1 * c), ?_⟩ : (2 : ℤ) ∣ 1) (by omega)
      linear_combination -hdet
  · exact h

private lemma symbol_neg (hc : c < 0) (hd : Odd d) : (shimuraSymbol (-c) (-d) : ℂ) *
    (thetaEpsilon (-d))⁻¹ * I = shimuraSymbol c d * (thetaEpsilon d)⁻¹ := by
  have hn : Odd d.natAbs := Int.natAbs_odd.mpr hd
  have hJ : J(c | d.natAbs) = J(-1 | d.natAbs) * J(-c | d.natAbs) := by
    rw [← jacobiSym.mul_left]
    simp
  have h1 : ¬(-c < 0 ∧ -d < 0) := by omega
  have hs1 : shimuraSymbol (-c) (-d) = J(-c | d.natAbs) := by
    simp only [shimuraSymbol, h1, ↓reduceIte, Int.natAbs_neg]
  have hd4 : d % 4 = 1 ∨ d % 4 = 3 := by
    rcases hd with ⟨t, rfl⟩
    omega
  rcases lt_or_gt_of_ne (show d ≠ 0 by rintro rfl; simp at hd) with hneg | hpos
  · have hs2 : shimuraSymbol c d = -J(c | d.natAbs) := by
      simp only [shimuraSymbol, hc, hneg, and_self, ↓reduceIte]
    rcases hd4 with h4 | h4
    · have h5 : (d.natAbs) % 4 = 3 := by omega
      rw [hs1, hs2, hJ, jacobiSym.at_neg_one hn, ZMod.χ₄_nat_three_mod_four h5,
        thetaEpsilon_of_emod_eq_one h4, thetaEpsilon_of_emod_ne_one (by omega), inv_I]
      push_cast
      linear_combination (-(J(-c | d.natAbs) : ℂ)) * I_sq
    · have h5 : (d.natAbs) % 4 = 1 := by omega
      rw [hs1, hs2, hJ, jacobiSym.at_neg_one hn, ZMod.χ₄_nat_one_mod_four h5,
        thetaEpsilon_of_emod_ne_one (d := d) (by omega),
        thetaEpsilon_of_emod_eq_one (d := -d) (by omega), inv_I]
      push_cast
      ring1
  · have h2 : ¬(c < 0 ∧ d < 0) := by omega
    have hs2 : shimuraSymbol c d = J(c | d.natAbs) := by
      simp only [shimuraSymbol, h2, ↓reduceIte]
    rcases hd4 with h4 | h4
    · have h5 : (d.natAbs) % 4 = 1 := by omega
      rw [hs1, hs2, hJ, jacobiSym.at_neg_one hn, ZMod.χ₄_nat_one_mod_four h5,
        thetaEpsilon_of_emod_eq_one h4, thetaEpsilon_of_emod_ne_one (by omega), inv_I]
      push_cast
      linear_combination (-(J(-c | d.natAbs) : ℂ)) * I_sq
    · have h5 : (d.natAbs) % 4 = 3 := by omega
      rw [hs1, hs2, hJ, jacobiSym.at_neg_one hn, ZMod.χ₄_nat_three_mod_four h5,
        thetaEpsilon_of_emod_ne_one (d := d) (by omega),
        thetaEpsilon_of_emod_eq_one (d := -d) (by omega), inv_I]
      push_cast
      ring1

private lemma thetaFactor_neg_of_neg (hc : γ 1 0 < 0) (hd : Odd (γ 1 1)) :
    thetaFactor (-γ) z = thetaFactor γ z := by
  have h10 : (-γ) 1 0 = -γ 1 0 := by simp
  have h11 : (-γ) 1 1 = -γ 1 1 := by simp
  have hden : denom (-γ : SL(2, ℤ)) z = -denom γ z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply, h10, h11]
    push_cast
    ring1
  have hIm : (denom γ z).im < 0 := by
    rw [ModularGroup.denom_apply]
    simp only [add_im, mul_im, intCast_im, zero_mul, add_zero]
    have h1 : ((γ 1 0 : ℤ) : ℝ) < 0 := by exact_mod_cast hc
    exact mul_neg_of_neg_of_pos h1 z.im_pos
  rw [thetaFactor, thetaFactor, hden, cpow_half_neg hIm, h10, h11, ← symbol_neg hc hd]
  ring1

private lemma thetaFactor_eq_one_of_eq_zero (hc : γ 1 0 = 0) : thetaFactor γ z = 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  rw [hc, mul_zero, sub_zero] at hdet
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨-, h1⟩ | ⟨-, h1⟩
  · rw [thetaFactor, ModularGroup.denom_apply, hc, h1]
    simp [shimuraSymbol, thetaEpsilon]
  · have h3 : (-1 : ℂ) ^ (2⁻¹ : ℂ) = I := by
      rw [cpow_def_of_ne_zero (neg_ne_zero.mpr one_ne_zero), log_neg_one, mul_assoc,
        mul_comm I, ← mul_assoc, ← div_eq_mul_inv, exp_pi_div_two_mul_I]
    rw [thetaFactor, ModularGroup.denom_apply, hc, h1]
    simp [shimuraSymbol, thetaEpsilon, h3]

private lemma jacobiTheta_smul_of_eq_zero (hc : γ 1 0 = 0) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) = thetaFactor γ z * jacobiTheta (2 * z) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  rw [hc, mul_zero, sub_zero] at hdet
  have hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / (0 * z + γ 1 1) := by
    rw [coe_smul_eq_div, hc, Int.cast_zero]
  rw [thetaFactor_eq_one_of_eq_zero z hc, one_mul]
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have e : ((γ • z : ℍ) : ℂ) = z + ((γ 0 1 : ℤ) : ℂ) := by
      rw [hsm, h0, h1]
      simp
    rw [e, jacobiTheta_two_mul_add_intCast]
  · have e : ((γ • z : ℍ) : ℂ) = z + ((-γ 0 1 : ℤ) : ℂ) := by
      rw [hsm, h0, h1]
      push_cast
      field_simp
      ring1
    rw [e, jacobiTheta_two_mul_add_intCast]

/-- The **theta function** `θ(z) = ∑_{n ∈ ℤ} e(n² z)` on the upper half plane, which is
`jacobiTheta (2 z)`. -/
noncomputable def thetaSeries : ℂ :=
  ∑' n : ℤ, cexp (2 * π * I * (n : ℂ) ^ 2 * z)

lemma thetaSeries_eq : thetaSeries z = jacobiTheta (2 * z) := by
  refine tsum_congr fun n ↦ ?_
  congr 1
  ring1

/-- **The transformation law of the theta function.** For `γ = (a, b; c, d) ∈ Γ₀(4)`,
`θ(γ z) = j(γ, z) θ(z)` with Shimura's theta multiplier `j(γ, z) = (c / d) ε_d⁻¹ (c z + d) ^ (1/2)`:
the theta multiplier `ModularForm.thetaFactor` is the automorphy factor of `θ`. -/
lemma thetaSeries_smul (hγ : γ ∈ Gamma0 4) :
    thetaSeries (γ • z) = thetaFactor γ z * thetaSeries z := by
  simp only [thetaSeries_eq]
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · have h0 : -γ ∈ Gamma0 4 := by
      rw [Gamma0_mem] at hγ ⊢
      simpa using hγ
    have h1 : 0 < (-γ) 1 0 := by simpa using hc
    have h2 : jacobiTheta (2 * ((-γ • z : ℍ) : ℂ)) = thetaFactor (-γ) z * jacobiTheta (2 * z) :=
      jacobiTheta_smul_of_pos z h0 h1
    rw [ModularGroup.SL_neg_smul, thetaFactor_neg_of_neg z hc (odd_of_det_right (Or.inr hγ))] at h2
    exact h2
  · exact jacobiTheta_smul_of_eq_zero z hc
  · exact jacobiTheta_smul_of_pos z hγ hc

private lemma summable_exp_neg_sq {u : ℝ} (hu : 0 < u) :
    Summable fun k : ℤ ↦ Real.exp (-(π * (k : ℝ) ^ 2 * u)) := by
  have h1 : 0 < ((u : ℂ) * I).im := by simpa using hu
  refine ((summable_jacobiTheta₂_term_iff 0 _).mpr h1).norm.congr fun k ↦ ?_
  rw [jacobiTheta₂_term, Complex.norm_exp]
  congr 1
  simp only [mul_zero, zero_add]
  have e : (π * I * (k : ℂ) ^ 2 * ((u : ℂ) * I)) = ((-(π * (k : ℝ) ^ 2 * u) : ℝ) : ℂ) := by
    push_cast
    linear_combination (π * (k : ℂ) ^ 2 * u) * I_sq
  rw [e, ofReal_re]

variable (a b) [NeZero a] in
private lemma norm_jacobiTheta_two_mul_div_add_le (hx : 0 < x.im) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (hu : u₀ ≤ (-1 / (2 * (a : ℂ) ^ 2 * x)).im) : ‖jacobiTheta (2 * ((b : ℂ) / a + x))‖ ≤
      ‖((-I * (2 * a ^ 2 * x)) ^ (1 / 2 : ℂ))‖⁻¹ *
        (a * ∑' k : ℤ, Real.exp (-(π * (k : ℝ) ^ 2 * u₀))) := by
  rw [jacobiTheta_two_mul_div_add a b hx, norm_mul, norm_div, norm_one, one_div]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hE : ∀ k : ℤ, ‖(∑ r : ZMod a, ZMod.stdAddChar ((b : ZMod a) * r ^ 2 + (k : ZMod a) * r)) *
      cexp (-π * I * k ^ 2 / (2 * a ^ 2 * x))‖ ≤ a * Real.exp (-(π * (k : ℝ) ^ 2 * u₀)) := by
    intro k
    have h1 : ‖∑ r : ZMod a, ZMod.stdAddChar ((b : ZMod a) * r ^ 2 + (k : ZMod a) * r)‖ ≤ a := by
      refine (norm_sum_le _ _).trans ?_
      simp
    have h2 : ‖cexp (-π * I * k ^ 2 / (2 * a ^ 2 * x))‖ ≤ Real.exp (-(π * (k : ℝ) ^ 2 * u₀)) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have e : (-π * I * (k : ℂ) ^ 2 / (2 * a ^ 2 * x)) =
          ((π * (k : ℝ) ^ 2 : ℝ) : ℂ) * (I * (-1 / (2 * (a : ℂ) ^ 2 * x))) := by
        push_cast
        ring1
      rw [e, re_ofReal_mul, I_mul_re]
      have h3 : 0 ≤ π * (k : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hu h3]
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg a)
  have hs : Summable fun k : ℤ ↦ a * Real.exp (-(π * (k : ℝ) ^ 2 * u₀)) :=
    (summable_exp_neg_sq hu₀).mul_left _
  rw [← tsum_mul_left]
  exact tsum_of_norm_bounded hs.hasSum hE

private lemma isBoundedAtImInfty_slash_thetaSeries_of_pos (hc : 0 < γ 1 0) :
    IsBoundedAtImInfty (halfIntegralWeightSlash 1 γ thetaSeries) := by
  rcases Int.eq_ofNat_of_zero_le hc.le with ⟨C, hC⟩
  have hC0 : NeZero C := ⟨fun h ↦ by rw [h] at hC; simp at hC; omega⟩
  have hCr : (0 : ℝ) < C := Nat.cast_pos.mpr (NeZero.pos C)
  have hCc : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  rw [hC] at hdet
  have hdetc : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * C = 1 := by exact_mod_cast hdet
  refine isBoundedAtImInfty_iff.mpr ⟨((2 * (C : ℝ)) ^ (1 / 2 : ℝ))⁻¹ *
    (C * ∑' k : ℤ, Real.exp (-(π * (k : ℝ) ^ 2 * (1 / 2)))), 1, fun z hy ↦ ?_⟩
  have hden : denom γ z = C * z + γ 1 1 := by
    rw [ModularGroup.denom_apply, hC]
    push_cast
    rfl
  have hD : ((C : ℂ) * z + γ 1 1) ≠ 0 := hden ▸ denom_ne_zero γ z
  have hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / (C * z + γ 1 1) := by
    rw [coe_smul_eq_div, hC]
    push_cast
    rfl
  have hy0 : 0 < (z : ℂ).im := z.im_pos
  have himw : 0 < ((C : ℂ) * z + γ 1 1).im := by
    have e : ((C : ℂ) * z + γ 1 1).im = C * (z : ℂ).im := by simp
    rw [e]
    positivity
  have hx : 0 < (-1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1))).im := by
    refine im_neg_one_div_pos ?_
    have e : ((C : ℂ) * ((C : ℂ) * z + γ 1 1)) = ((C : ℝ) : ℂ) * ((C : ℂ) * z + γ 1 1) := by
      push_cast
      rfl
    rw [e, im_ofReal_mul]
    positivity
  have harg : ((γ • z : ℍ) : ℂ) = (γ 0 0 : ℂ) / C + -1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1)) := by
    have key : ∀ W : ℂ, W ≠ 0 → W = (C : ℂ) * z + γ 1 1 →
        ((γ 0 0 : ℂ) * z + γ 0 1) / W = (γ 0 0 : ℂ) / C + -1 / ((C : ℂ) * W) := by
      intro W hW hWe
      field_simp
      rw [hWe]
      linear_combination -hdetc
    rw [hsm]
    exact key _ hD rfl
  have hτ : 2 * (C : ℂ) ^ 2 * (-1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1))) =
      -(2 * C) / ((C : ℂ) * z + γ 1 1) := by
    field_simp
  have hu :
      (1 / 2 : ℝ) ≤ (-1 / (2 * (C : ℂ) ^ 2 * (-1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1))))).im := by
    have e : (-1 / (2 * (C : ℂ) ^ 2 * (-1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1))))) =
        ((1 / (2 * C) : ℝ) : ℂ) * ((C : ℂ) * z + γ 1 1) := by
      rw [hτ]
      push_cast
      field_simp
    rw [e, im_ofReal_mul]
    have e1 : ((C : ℂ) * z + γ 1 1).im = C * (z : ℂ).im := by simp
    rw [e1]
    have hy1 : 1 ≤ (z : ℂ).im := hy
    have e2 : 1 / (2 * (C : ℝ)) * (C * (z : ℂ).im) = (z : ℂ).im / 2 := by
      field_simp
    rw [e2]
    linarith
  have hb : ‖jacobiTheta (2 * ((γ 0 0 : ℂ) / C + -1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1))))‖ ≤
      ‖(-I * (2 * (C : ℂ) ^ 2 * (-1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1))))) ^ (1 / 2 : ℂ)‖⁻¹ *
        (C * ∑' k : ℤ, Real.exp (-(π * (k : ℝ) ^ 2 * (1 / 2)))) :=
    norm_jacobiTheta_two_mul_div_add_le C (γ 0 0) hx one_half_pos hu
  rw [← harg, ← thetaSeries_eq] at hb
  have hR : 0 < ‖(C : ℂ) * z + γ 1 1‖ := norm_pos_iff.mpr hD
  have hτ0 : -I * (2 * (C : ℂ) ^ 2 * (-1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1)))) ≠ 0 := by
    rw [hτ]
    refine mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (div_ne_zero ?_ hD)
    simp [hCc]
  have hnorm : ‖(-I * (2 * (C : ℂ) ^ 2 * (-1 / ((C : ℂ) * ((C : ℂ) * z + γ 1 1))))) ^ (1 / 2 : ℂ)‖ =
      (2 * (C : ℝ) / ‖(C : ℂ) * z + γ 1 1‖) ^ (1 / 2 : ℝ) := by
    rw [norm_cpow_of_ne_zero hτ0, hτ]
    simp
  have hslash : ‖halfIntegralWeightSlash 1 γ thetaSeries z‖ =
      ‖(C : ℂ) * z + γ 1 1‖ ^ (-(1 / 2 : ℝ)) * ‖thetaSeries (γ • z)‖ := by
    rw [halfIntegralWeightSlash, norm_mul, hden, norm_real, Real.norm_of_nonneg
      (Real.rpow_nonneg (norm_nonneg _) _)]
    norm_num
  rw [hnorm] at hb
  rw [hslash]
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
  rw [Real.div_rpow (by positivity) hR.le, Real.rpow_neg hR.le]
  have h1 : 0 < ‖(C : ℂ) * z + γ 1 1‖ ^ (1 / 2 : ℝ) := by positivity
  have h2 : 0 < (2 * (C : ℝ)) ^ (1 / 2 : ℝ) := by positivity
  field_simp

lemma mdifferentiable_thetaSeries : MDiff thetaSeries := by
  refine UpperHalfPlane.mdifferentiable_iff.mpr fun w hw ↦ ?_
  have hw' : 0 < (2 * w).im := by
    have e : (2 * w).im = 2 * w.im := by simp
    rw [e]
    exact mul_pos two_pos hw
  have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ jacobiTheta (2 * w)) w :=
    DifferentiableAt.comp (f := fun w : ℂ ↦ 2 * w) w (differentiableAt_jacobiTheta hw')
      (by fun_prop)
  refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with v hv
  rw [Function.comp_apply, thetaSeries_eq, ofComplex_apply_of_im_pos hv]

private lemma tendsto_thetaSeries_atImInfty : Tendsto thetaSeries atImInfty (nhds 1) := by
  rw [funext thetaSeries_eq]
  refine TauCeti.tendsto_jacobiTheta_comap_im_atTop.comp (tendsto_comap_iff.mpr ?_)
  have h2 : (Complex.im ∘ fun z : ℍ ↦ 2 * (z : ℂ)) = fun z : ℍ ↦ 2 * z.im := by
    ext z
    simp
  rw [h2]
  exact Tendsto.const_mul_atTop two_pos tendsto_comap

lemma thetaSeries_ne_zero : thetaSeries ≠ 0 :=
  fun h ↦ zero_ne_one <| tendsto_nhds_unique (h ▸ tendsto_const_nhds) tendsto_thetaSeries_atImInfty

private lemma isBoundedAtImInfty_thetaSeries : IsBoundedAtImInfty thetaSeries :=
  tendsto_thetaSeries_atImInfty.isBigO_one ℝ

variable (γ) in
/-- **The theta function is holomorphic at every cusp**: `|c z + d| ^ (-1/2) θ(γ z)` is bounded as
`Im z → ∞`, for every `γ ∈ SL(2, ℤ)`. -/
lemma isBoundedAtImInfty_slash_thetaSeries :
    IsBoundedAtImInfty (halfIntegralWeightSlash 1 γ thetaSeries) := by
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · have h1 : halfIntegralWeightSlash 1 γ thetaSeries =
        halfIntegralWeightSlash 1 (-γ) thetaSeries := by
      ext z
      have h10 : (-γ) 1 0 = -γ 1 0 := by simp
      have h11 : (-γ) 1 1 = -γ 1 1 := by simp
      have h2 : denom (-γ : SL(2, ℤ)) z = -denom γ z := by
        rw [ModularGroup.denom_apply, ModularGroup.denom_apply, h10, h11]
        push_cast
        ring1
      rw [halfIntegralWeightSlash, halfIntegralWeightSlash, h2, norm_neg, ModularGroup.SL_neg_smul]
    rw [h1]
    exact isBoundedAtImInfty_slash_thetaSeries_of_pos (by simpa using hc)
  · have h1 : halfIntegralWeightSlash 1 γ thetaSeries = thetaSeries := by
      ext z
      have h2 : ‖denom γ z‖ = 1 := by
        have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
        rw [hc, mul_zero, sub_zero] at hdet
        rw [ModularGroup.denom_apply, hc]
        rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨-, h3⟩ | ⟨-, h3⟩ <;> simp [h3]
      have h3 : jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) = thetaFactor γ z * jacobiTheta (2 * z) :=
        jacobiTheta_smul_of_eq_zero z hc
      rw [thetaFactor_eq_one_of_eq_zero z hc, one_mul] at h3
      rw [halfIntegralWeightSlash, h2, Real.one_rpow, ofReal_one, one_mul, thetaSeries_eq, h3,
        thetaSeries_eq]
    rw [h1]
    exact isBoundedAtImInfty_thetaSeries
  · exact isBoundedAtImInfty_slash_thetaSeries_of_pos hc

/-- **The theta function is a modular form of weight `1/2`**: `θ ∈ M_{1/2}(4, 1)`. So
`ModularForm.halfIntegralWeightSpace` is not vacuous, and its multiplier is that of `θ`. -/
lemma thetaSeries_mem_halfIntegralWeightSpace :
    thetaSeries ∈ halfIntegralWeightSpace (1 : DirichletCharacter ℂ 4) 1 := by
  refine ⟨mdifferentiable_thetaSeries, fun γ hγ z ↦ ?_, isBoundedAtImInfty_slash_thetaSeries⟩
  have hodd : Odd (γ 1 1) := odd_of_det_right (Or.inr hγ)
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod 4) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]
    rcases hodd with ⟨t, ht⟩
    have h2 : IsCoprime (γ 1 1) 2 := ⟨1, -t, by rw [ht]; ring1⟩
    have h3 : IsCoprime (γ 1 1) (2 ^ 2) := h2.pow_right
    norm_num at h3
    exact_mod_cast h3
  have hw : weightFactor 1 γ z = thetaFactor γ z := by
    simp [weightFactor]
  rw [MulChar.one_apply hunit, hw, one_mul]
  exact thetaSeries_smul z hγ

end ModularForm
