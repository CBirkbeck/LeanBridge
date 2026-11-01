import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.CoefficientsUnique

/-!
# Hecke operators and sine expansions of Maass forms

If `f` has the sine expansion `f(x + iy) = ∑_{n ≥ 1} c(n) √y K_{iR}(2πny) sin(2πnx)`, then `T_p f`
has the sine expansion with coefficients `c(pn) + c(n/p)` (the second term only for `p ∣ n`),
with no hypothesis of absolute convergence: `∑_{j < p} sin(2πn(x + j)/p)` is `p sin(2πnx/p)` if
`p ∣ n` and `0` otherwise. With the uniqueness of the sine coefficients, an odd `T_p`-eigenfunction
with eigenvalue `λ_p` has `c(p) = λ_p c(1)` (LMFDB `mf.maass.mwf.coefficients`): this removes the
hypothesis of absolute convergence from `UpperHalfPlane.HasMaassSineExpansion.coeff_prime_eq`. For
cosine expansions, the non-vanishing of `K_{iR}` somewhere on `(0, ∞)` removes the hypothesis on
`K_{iR}` from `UpperHalfPlane.HasMaassCosineExpansion.coeff_prime_eq`.

## Main results

* `UpperHalfPlane.hasMaassSineExpansion_maassHeckeOperator`: the sine coefficients of `T_p f`.
* `UpperHalfPlane.HasMaassSineExpansion.coeff_prime_eq_mul`,
  `UpperHalfPlane.HasMaassCosineExpansion.coeff_prime_eq_mul`: `c(p) = λ_p c(1)`.
-/

open Real

namespace UpperHalfPlane

variable {p : ℕ} (hp : p.Prime) {f : ℂ → ℂ} {r : ℂ} {c : ℕ+ → ℂ} {heckeEigenvalue : ℂ}

lemma sum_range_sin_two_pi_mul (hp₀ : p ≠ 0) (n : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range p, (sin (2 * π * n * ((x + j) / p)) : ℂ) =
      (if p ∣ n then (p : ℂ) else 0) * sin (2 * π * n * x / p) := by
  have e (j : ℕ) : (sin (2 * π * n * ((x + j) / p)) : ℂ) =
      Complex.I / 2 * (Complex.exp (-((2 * π * n * x / p : ℝ) : ℂ) * Complex.I) *
        Complex.exp (2 * π * Complex.I * ((-n : ℤ) : ℂ) * j / p) -
          Complex.exp (((2 * π * n * x / p : ℝ) : ℂ) * Complex.I) *
            Complex.exp (2 * π * Complex.I * ((n : ℤ) : ℂ) * j / p)) := by
    have h1 : -((2 * π * n * ((x + j) / p) : ℝ) : ℂ) * Complex.I =
        -((2 * π * n * x / p : ℝ) : ℂ) * Complex.I +
          2 * π * Complex.I * ((-n : ℤ) : ℂ) * j / p := by
      push_cast
      ring1
    have h2 : ((2 * π * n * ((x + j) / p) : ℝ) : ℂ) * Complex.I =
        ((2 * π * n * x / p : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I * ((n : ℤ) : ℂ) * j / p := by
      push_cast
      ring1
    rw [Complex.ofReal_sin, Complex.sin, h1, h2, Complex.exp_add, Complex.exp_add]
    ring1
  rw [Finset.sum_congr rfl fun j _ ↦ e j, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_range_exp_two_pi_I_mul_div hp₀,
    sum_range_exp_two_pi_I_mul_div hp₀, Complex.ofReal_sin, Complex.sin]
  simp only [dvd_neg, Int.natCast_dvd_natCast]
  split_ifs <;> ring1

lemma ite_dvd_eq_zero (hp₀ : p ≠ 0) {a : ℂ} {m : ℕ+} (hm : m ∉ Set.range fun n ↦ p.toPNat' * n) :
    (if p ∣ (m : ℕ) then a else 0) = 0 := by
  refine ite_eq_right fun ⟨k, hk⟩ ↦ hm ⟨k.toPNat', PNat.eq ?_⟩
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h0 ↦ m.ne_zero <| by rw [hk, h0, mul_zero]
  rw [PNat.mul_coe, PNat.toPNat'_coe (Nat.pos_of_ne_zero hp₀), PNat.toPNat'_coe hk0, hk]

/-- **The sine coefficients of `T_p f`**: if `f` has the sine expansion
`f(x + iy) = ∑ c(n) √y K_{iR}(2πny) sin(2πnx)`, then `T_p f` has the sine expansion with
coefficients `c(pn) + c(n/p)`, where the second term is present only when `p ∣ n`. -/
lemma hasMaassSineExpansion_maassHeckeOperator (hp₀ : p ≠ 0) (h : HasMaassSineExpansion f r c) :
    HasMaassSineExpansion (maassHeckeOperator p f) r fun m ↦
      c (p.toPNat' * m) + if p ∣ (m : ℕ) then c ((m : ℕ) / p).toPNat' else 0 := by
  intro z
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp₀)
  have hinj : Function.Injective fun n : ℕ+ ↦ p.toPNat' * n := mul_right_injective _
  have hA : HasSum (fun m : ℕ+ ↦ (if p ∣ (m : ℕ) then (√p : ℂ) * c ((m : ℕ) / p).toPNat' else 0) *
      √z.im * (Complex.I * r).besselK (2 * π * m * z.im) * sin (2 * π * m * z.re))
      (f (p * z)) := by
    refine (hinj.hasSum_iff fun m hm ↦ ?_).mp ?_
    · rw [ite_dvd_eq_zero hp₀ hm, zero_mul, zero_mul, zero_mul]
    · convert h (mk (p * z) (by simpa using mul_pos hp' z.im_pos)) using 2 with n
      have hpn : ((p.toPNat' * n : ℕ+) : ℕ) = p * n := by
        rw [PNat.mul_coe, PNat.toPNat'_coe (Nat.pos_of_ne_zero hp₀)]
      have hK : 2 * π * (p * n) * z.im = 2 * π * n * (p * z.im) := by
        ring1
      have hE : 2 * π * (p * n) * z.re = 2 * π * n * (p * z.re) := by
        ring1
      simp only [Function.comp_apply, hpn, dvd_mul_right,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp₀), PNat.coe_toPNat', mk_im, mk_re,
        Complex.mul_im, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, coe_re, coe_im,
        zero_mul, add_zero, sub_zero, Nat.cast_mul, hK, hE, Real.sqrt_mul hp'.le]
      push_cast
      ring1
  have hB : HasSum (fun m : ℕ+ ↦ (√p : ℂ) * c (p.toPNat' * m) * √z.im *
      (Complex.I * r).besselK (2 * π * m * z.im) * sin (2 * π * m * z.re))
      (∑ j ∈ Finset.range p, f ((z + j) / p)) := by
    have hpos (j : ℕ) : 0 < ((z + j) / p : ℂ).im := by
      simpa using div_pos z.im_pos hp'
    have hs : HasSum (fun n : ℕ+ ↦ (if p ∣ (n : ℕ) then (p : ℂ) else 0) * (c n * √(z.im / p) *
        (Complex.I * r).besselK (2 * π * n * (z.im / p)) * sin (2 * π * n * z.re / p)))
        (∑ j ∈ Finset.range p, f ((z + j) / p)) := by
      convert hasSum_sum fun j (_ : j ∈ Finset.range p) ↦ h (mk _ (hpos j)) using 1
      funext n
      simp only [mk_im, mk_re, Complex.div_natCast_im, Complex.div_natCast_re, Complex.add_im,
        Complex.add_re, Complex.natCast_im, Complex.natCast_re, coe_im, coe_re, add_zero]
      rw [← Finset.mul_sum, sum_range_sin_two_pi_mul hp₀]
      ring1
    refine ((hinj.hasSum_iff fun m hm ↦ ?_).mpr hs).congr_fun fun m ↦ ?_
    · rw [ite_dvd_eq_zero hp₀ hm, zero_mul]
    · have hpm : ((p.toPNat' * m : ℕ+) : ℕ) = p * m := by
        rw [PNat.mul_coe, PNat.toPNat'_coe (Nat.pos_of_ne_zero hp₀)]
      have hK : 2 * π * (p * m) * (z.im / p) = 2 * π * m * z.im := by
        field_simp
      have hE : 2 * π * (p * m) * z.re / p = 2 * π * m * z.re := by
        field_simp
      have hS : (√(z.im / p) : ℂ) * p = √p * √z.im := by
        have hp2 : (√p : ℂ) * √p = p := by
          exact_mod_cast Real.mul_self_sqrt hp'.le
        have hp0 : (√p : ℂ) ≠ 0 := by
          exact_mod_cast (Real.sqrt_pos.mpr hp').ne'
        rw [Real.sqrt_div' _ hp'.le]
        push_cast
        field_simp
        linear_combination -√z.im * hp2
      simp only [Function.comp_apply, hpm, dvd_mul_right, ite_true, Nat.cast_mul, hK, hE]
      linear_combination -(c (p.toPNat' * m) * (Complex.I * r).besselK (2 * π * m * z.im) *
        sin (2 * π * m * z.re)) * hS
  have hp0 : (√p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hp').ne'
  convert (hA.add hB).mul_left (((√p)⁻¹ : ℝ) : ℂ) using 1
  · funext m
    push_cast
    split_ifs
    · field_simp
      ring1
    · field_simp
      ring1
  · rfl

/-- **The sine coefficients of an odd `T_p`-eigenfunction**: if `f` has the sine expansion
`f(x + iy) = ∑ c(n) √y K_{iR}(2πny) sin(2πnx)` and `T_p f = λ_p f` on `ℍ` for a prime `p`, then
`c(p) = λ_p c(1)`, with no hypothesis of absolute convergence or on `K_{iR}`. -/
lemma HasMaassSineExpansion.coeff_prime_eq_mul (h : HasMaassSineExpansion f r c)
    (hT : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p f z = heckeEigenvalue * f z) :
    c ⟨p, hp.pos⟩ = heckeEigenvalue * c 1 := by
  have hb : HasMaassSineExpansion (maassHeckeOperator p f) r fun n ↦ heckeEigenvalue * c n := by
    intro z
    rw [hT z z.im_pos]
    simpa only [mul_assoc] using (h z).mul_left heckeEigenvalue
  have hP : p.toPNat' * 1 = ⟨p, hp.pos⟩ :=
    PNat.eq <| by rw [PNat.mul_coe, PNat.one_coe, mul_one, PNat.toPNat'_coe hp.pos, PNat.mk_coe]
  have key : c (p.toPNat' * 1) + (if p ∣ ((1 : ℕ+) : ℕ) then c (((1 : ℕ+) : ℕ) / p).toPNat'
      else 0) = heckeEigenvalue * c 1 :=
    congrFun ((hasMaassSineExpansion_maassHeckeOperator hp.ne_zero h).unique hb) 1
  simpa only [hP, PNat.one_coe, hp.not_dvd_one, ite_false, add_zero] using key

/-- **The cosine coefficients of an even `T_p`-eigenfunction**: if `f` has the cosine expansion
`f(x + iy) = ∑ c(n) √y K_{iR}(2πny) cos(2πnx)` and `T_p f = λ_p f` on `ℍ` for a prime `p`, then
`c(p) = λ_p c(1)`, with no hypothesis on `K_{iR}`. -/
lemma HasMaassCosineExpansion.coeff_prime_eq_mul (h : HasMaassCosineExpansion f r c)
    (hT : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p f z = heckeEigenvalue * f z) :
    c ⟨p, hp.pos⟩ = heckeEigenvalue * c 1 := by
  rcases (Complex.I * r).exists_besselK_ne_zero with ⟨x, hx, hK⟩
  refine h.coeff_prime_eq hp hT (div_pos hx two_pi_pos) ?_
  rwa [mul_div_cancel₀ x two_pi_pos.ne']

end UpperHalfPlane
