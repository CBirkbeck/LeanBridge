import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.FourierExpansion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Hecke

/-!
# Hecke operators and Fourier coefficients of Maass forms

If `f` has the Fourier expansion `f(z) = ∑_{n ∈ ℤ} a(n) √y K_{ir}(2π|n|y) e^{2πinx}`, then
`T_p f` has the expansion with coefficients `a(pn) + a(n/p)` (the second term only for `p ∣ n`).
The coefficients of such an expansion are determined by `f` wherever the Bessel factor does not
vanish, so for a `T_p`-eigenfunction with eigenvalue `λ_p`, `a(p) = λ_p a(1)`: this is the LMFDB's
statement that `c(p)` is the Hecke eigenvalue (`mf.maass.mwf.fourierexpansion`,
`mf.maass.mwf.coefficients`), for the normalisation `c(1) = 1`. The cosine and sine expansions of
even and odd forms are Fourier expansions with `a(±n) = c(n)/2`, resp. `a(±n) = ±c(n)/(2i)`.

## Main results

* `UpperHalfPlane.hasMaassFourierExpansion_maassHeckeOperator`: the Fourier coefficients of
  `T_p f`.
* `UpperHalfPlane.HasMaassFourierExpansion.mul_besselK_eq`: uniqueness of the Fourier coefficients.
* `UpperHalfPlane.HasMaassFourierExpansion.coeff_prime_eq`,
  `UpperHalfPlane.IsMaassHeckeEigenform.coeff_prime_eq`: `a(p) = λ_p a(1)`.
* `UpperHalfPlane.HasMaassCosineExpansion.hasMaassFourierExpansion`,
  `UpperHalfPlane.HasMaassSineExpansion.hasMaassFourierExpansion`: cosine and sine expansions are
  Fourier expansions.
* `UpperHalfPlane.HasMaassCosineExpansion.coeff_prime_eq`,
  `UpperHalfPlane.HasMaassSineExpansion.coeff_prime_eq`: `c(p) = λ_p c(1)`.
-/

open Real

namespace UpperHalfPlane

variable {p : ℕ} {f : ℂ → ℂ} {r : ℂ} {a b : ℤ → ℂ} {c u v : ℕ+ → ℂ} {y : ℝ} {heckeEigenvalue : ℂ}

lemma sum_range_exp_two_pi_I_mul_div (hp : p ≠ 0) (n : ℤ) :
    ∑ j ∈ Finset.range p, Complex.exp (2 * π * Complex.I * n * j / p) =
      if (p : ℤ) ∣ n then (p : ℂ) else 0 := by
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hpow (j : ℕ) : Complex.exp (2 * π * Complex.I * n * j / p) =
      Complex.exp (2 * π * Complex.I * n / p) ^ j := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring1
  simp only [hpow]
  split_ifs with h
  · rcases h with ⟨m, rfl⟩
    have h1 : Complex.exp (2 * π * Complex.I * ((p * m : ℤ) : ℂ) / p) = 1 := by
      rw [Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      push_cast
      field_simp
    simp only [h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have h1 : Complex.exp (2 * π * Complex.I * n / p) ≠ 1 := by
      rw [Ne, Complex.exp_eq_one_iff]
      rintro ⟨m, hm⟩
      refine h ⟨m, ?_⟩
      have hm' : (n : ℂ) = p * m := by
        field_simp at hm
        linear_combination hm
      exact_mod_cast hm'
    rw [geom_sum_eq h1, ← Complex.exp_nat_mul, div_eq_zero_iff, sub_eq_zero]
    left
    rw [Complex.exp_eq_one_iff]
    exact ⟨n, by field_simp⟩

/-- **The Fourier coefficients of `T_p f`**: if `f` has the Fourier expansion with coefficients
`a(n)`, then `T_p f` has the Fourier expansion with coefficients `a(pn) + a(n/p)`, where the
second term is present only when `p ∣ n`. -/
lemma hasMaassFourierExpansion_maassHeckeOperator (hp : p ≠ 0)
    (h : HasMaassFourierExpansion f r a) :
    HasMaassFourierExpansion (maassHeckeOperator p f) r
      fun n ↦ a (p * n) + if (p : ℤ) ∣ n then a (n / p) else 0 := by
  intro z
  have hp' : (0 : ℝ) < p := by positivity
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hinj : Function.Injective fun n : ℤ ↦ (p : ℤ) * n :=
    mul_right_injective₀ <| Int.natCast_ne_zero.mpr hp
  have hA : HasSum (fun m : ℤ ↦ if (p : ℤ) ∣ m then (√p : ℂ) * (a (m / p) * √z.im *
      (Complex.I * r).besselK (2 * π * |m| * z.im) * Complex.exp (2 * π * Complex.I * m * z.re))
      else 0) (f (p * z)) := by
    refine (hinj.hasSum_iff ?_).mp ?_
    · rintro m hm
      refine ite_eq_right_iff.mpr ?_
      rintro ⟨n, rfl⟩
      exact absurd ⟨n, rfl⟩ hm
    · convert h (mk (p * z) (by simpa using mul_pos hp' z.im_pos)) using 2 with n
      simp only [Function.comp_apply, dvd_mul_right, ite_true, mk_im, mk_re,
        Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hp), abs_mul, Nat.abs_cast]
      simp [Real.sqrt_mul hp'.le]
      have hK : 2 * π * (p * |(n : ℝ)|) * z.im = 2 * π * |(n : ℝ)| * (p * z.im) := by
        ring1
      have hE : 2 * π * Complex.I * (p * n) * z.re = 2 * π * Complex.I * n * (p * z.re) := by
        ring1
      rw [hK, hE]
      ring1
  have hB : HasSum (fun m : ℤ ↦ (√p : ℂ) * (a (p * m) * √z.im *
      (Complex.I * r).besselK (2 * π * |m| * z.im) * Complex.exp (2 * π * Complex.I * m * z.re)))
      (∑ j ∈ Finset.range p, f ((z + j) / p)) := by
    have hpos (j : ℕ) : 0 < ((z + j) / p : ℂ).im := by
      simpa using div_pos z.im_pos hp'
    have hs : HasSum (fun n : ℤ ↦ (if (p : ℤ) ∣ n then (p : ℂ) else 0) * (a n * √(z.im / p) *
        (Complex.I * r).besselK (2 * π * |n| * (z.im / p)) *
        Complex.exp (2 * π * Complex.I * n * (z.re / p))))
        (∑ j ∈ Finset.range p, f ((z + j) / p)) := by
      convert hasSum_sum fun j (_ : j ∈ Finset.range p) ↦ h (mk _ (hpos j)) using 1
      funext n
      rw [← sum_range_exp_two_pi_I_mul_div hp n, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [mk_im, mk_re, Complex.div_natCast_im, Complex.div_natCast_re, Complex.add_im,
        Complex.add_re, Complex.natCast_im, Complex.natCast_re, coe_im, coe_re, add_zero]
      push_cast
      have hE : 2 * π * Complex.I * n * ((z.re + j) / p) =
          2 * π * Complex.I * n * j / p + 2 * π * Complex.I * n * (z.re / p) := by
        ring1
      rw [hE, Complex.exp_add]
      ring1
    refine (hinj.hasSum_iff ?_).mpr hs |>.congr_fun ?_
    · rintro n hn
      have hpn : ¬(p : ℤ) ∣ n := fun ⟨m, hm⟩ ↦ hn ⟨m, hm.symm⟩
      simp [hpn]
    · intro m
      simp only [Function.comp_apply, dvd_mul_right, ite_true, abs_mul, Nat.abs_cast]
      push_cast
      have hK : 2 * π * (p * |(m : ℝ)|) * (z.im / p) = 2 * π * |(m : ℝ)| * z.im := by
        field_simp
      have hE : 2 * π * Complex.I * (p * m) * (z.re / p) = 2 * π * Complex.I * m * z.re := by
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
      rw [hK, hE]
      linear_combination -(a (p * m) * (Complex.I * r).besselK (2 * π * |(m : ℝ)| * z.im) *
        Complex.exp (2 * π * Complex.I * m * z.re)) * hS
  have hp0 : (√p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hp').ne'
  convert (hA.add hB).mul_left (((√p)⁻¹ : ℝ) : ℂ) using 1
  · funext n
    push_cast
    split_ifs
    · field_simp
      ring1
    · field_simp
      ring1
  · rfl

lemma intervalIntegral_exp_two_pi_I_mul (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * π * Complex.I * k * x) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · simp [hk]
  · have hc : 2 * π * Complex.I * k ≠ 0 := by
      simp [hk, Real.pi_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * k) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨k, by ring1⟩
    simp [h1]

lemma eq_zero_of_forall_hasSum_mul_exp {d : ℤ → ℂ}
    (h : ∀ x : ℝ, HasSum (fun n ↦ d n * Complex.exp (2 * π * Complex.I * n * x)) 0) (m : ℤ) :
    d m = 0 := by
  have hd : Summable fun n ↦ ‖d n‖ :=
    summable_norm_iff.mpr <| by simpa using (h 0).summable
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := 1)
    (F := fun n x ↦ d n * Complex.exp (2 * π * Complex.I * n * x) *
      Complex.exp (-(2 * π * Complex.I * m * x)))
    (f := fun _ ↦ 0) (fun n _ ↦ ‖d n‖) (fun n ↦ by fun_prop)
    (fun n ↦ .of_forall fun t _ ↦ le_of_eq <| by simp [Complex.norm_exp])
    (.of_forall fun _ _ ↦ hd) intervalIntegrable_const
    (.of_forall fun t _ ↦ by
      simpa using (h t).mul_right (Complex.exp (-(2 * π * Complex.I * m * t))))
  have hI (n : ℤ) : ∫ x in (0 : ℝ)..1, d n * Complex.exp (2 * π * Complex.I * n * x) *
      Complex.exp (-(2 * π * Complex.I * m * x)) = if n = m then d m else 0 := by
    have hF (x : ℝ) : d n * Complex.exp (2 * π * Complex.I * n * x) *
        Complex.exp (-(2 * π * Complex.I * m * x)) =
        d n * Complex.exp (2 * π * Complex.I * ((n - m : ℤ) : ℂ) * x) := by
      rw [mul_assoc, ← Complex.exp_add]
      push_cast
      congr 2
      ring1
    rw [intervalIntegral.integral_congr fun x _ ↦ hF x, intervalIntegral.integral_const_mul,
      intervalIntegral_exp_two_pi_I_mul]
    split_ifs with h1 h2 h2
    · rw [h2, mul_one]
    · exact absurd (sub_eq_zero.mp h1) h2
    · exact absurd (sub_eq_zero.mpr h2) h1
    · rw [mul_zero]
  simp only [hI, intervalIntegral.integral_zero] at key
  exact (key.unique (hasSum_ite_eq m (d m))).symm

/-- **The Fourier coefficients of a Maass form are unique** up to the Bessel factor: two Fourier
expansions of `f` with coefficients `a` and `b` satisfy `a(n) K_{ir}(2π|n|y) = b(n) K_{ir}(2π|n|y)`
for every `n` and `y > 0`. -/
lemma HasMaassFourierExpansion.mul_besselK_eq (ha : HasMaassFourierExpansion f r a)
    (hb : HasMaassFourierExpansion f r b) (n : ℤ) (hy : 0 < y) :
    a n * (Complex.I * r).besselK (2 * π * |n| * y) =
      b n * (Complex.I * r).besselK (2 * π * |n| * y) := by
  have h : (a n - b n) * √y * (Complex.I * r).besselK (2 * π * |n| * y) = 0 :=
    eq_zero_of_forall_hasSum_mul_exp (d := fun k ↦ (a k - b k) * √y *
      (Complex.I * r).besselK (2 * π * |k| * y)) (fun x ↦ ?_) n
  · have hy' : (√y : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
    have h2 : (a n - b n) * (Complex.I * r).besselK (2 * π * |n| * y) * √y = 0 * √y := by
      linear_combination h
    linear_combination mul_right_cancel₀ hy' h2
  · convert (ha (mk (x + y * Complex.I) (by simpa using hy))).sub
      (hb (mk (x + y * Complex.I) (by simpa using hy))) using 1
    · funext k
      simp
      ring1
    · rw [sub_self]

/-- **The `p`-th Fourier coefficient of a `T_p`-eigenfunction**: if `f` has the Fourier expansion
`∑ a(n) √y K_{ir}(2π|n|y) e^{2πinx}` and `T_p f = λ_p f` on `ℍ` for a prime `p`, then
`a(p) = λ_p a(1)`, provided `K_{ir}(2πy) ≠ 0` for some `y > 0`. -/
lemma HasMaassFourierExpansion.coeff_prime_eq (hp : p.Prime) (ha : HasMaassFourierExpansion f r a)
    (hT : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p f z = heckeEigenvalue * f z) (hy : 0 < y)
    (hK : (Complex.I * r).besselK (2 * π * y) ≠ 0) :
    a p = heckeEigenvalue * a 1 := by
  have hb : HasMaassFourierExpansion (maassHeckeOperator p f) r fun n ↦ heckeEigenvalue * a n := by
    intro z
    rw [hT z z.im_pos]
    simpa only [mul_assoc] using (ha z).mul_left heckeEigenvalue
  have hp1 : ¬(p : ℤ) ∣ 1 := by
    exact_mod_cast hp.not_dvd_one
  have h : a p * (Complex.I * r).besselK (2 * π * y) =
      heckeEigenvalue * a 1 * (Complex.I * r).besselK (2 * π * y) := by
    simpa only [mul_one, hp1, ite_false, add_zero, abs_one, Int.cast_one] using
      (hasMaassFourierExpansion_maassHeckeOperator hp.ne_zero ha).mul_besselK_eq hb 1 hy
  exact mul_right_cancel₀ hK h

/-- **The Fourier coefficients of a Maass Hecke eigenform at good primes are its Hecke
eigenvalues**: `a(p) = λ_p a(1)` for every prime `p ∤ N`, provided `K_{ir}(2πy) ≠ 0` for some
`y > 0`. -/
lemma IsMaassHeckeEigenform.coeff_prime_eq {N : ℕ} {eigenvalue : ℂ} {hecke : ℕ → ℂ}
    (hf : IsMaassHeckeEigenform f N eigenvalue hecke) (ha : HasMaassFourierExpansion f r a)
    (hp : p.Prime) (hpN : ¬p ∣ N) (hy : 0 < y) (hK : (Complex.I * r).besselK (2 * π * y) ≠ 0) :
    a p = hecke p * a 1 :=
  ha.coeff_prime_eq hp (hf.2.2 p hp hpN) hy hK

lemma hasMaassFourierExpansion_of_pnat
    (hu : ∀ z : ℍ, Summable fun k : ℕ+ ↦ u k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im) *
      Complex.exp (2 * π * Complex.I * k * z.re))
    (hv : ∀ z : ℍ, Summable fun k : ℕ+ ↦ v k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im) *
      Complex.exp (2 * π * Complex.I * (-k : ℤ) * z.re))
    (h : ∀ z : ℍ, HasSum (fun k : ℕ+ ↦ u k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im) *
      Complex.exp (2 * π * Complex.I * k * z.re) + v k * √z.im *
        (Complex.I * r).besselK (2 * π * k * z.im) *
          Complex.exp (2 * π * Complex.I * (-k : ℤ) * z.re)) (f z)) :
    HasMaassFourierExpansion f r fun n ↦
      if 0 < n then u n.toNat.toPNat' else if n < 0 then v (-n).toNat.toPNat' else 0 := by
  intro z
  rw [← ((hu z).hasSum.add (hv z).hasSum).unique (h z)]
  have hP := (Function.Injective.hasSum_iff (g := fun k : ℕ+ ↦ (k : ℤ))
    (f := fun n : ℤ ↦ if 0 < n then u n.toNat.toPNat' * √z.im *
      (Complex.I * r).besselK (2 * π * |n| * z.im) * Complex.exp (2 * π * Complex.I * n * z.re)
      else 0) (Nat.cast_injective.comp PNat.coe_injective) ?_).mp ((hu z).hasSum.congr_fun ?_)
  · have hN := (Function.Injective.hasSum_iff (g := fun k : ℕ+ ↦ -(k : ℤ))
      (f := fun n : ℤ ↦ if n < 0 then v (-n).toNat.toPNat' * √z.im *
        (Complex.I * r).besselK (2 * π * |n| * z.im) * Complex.exp (2 * π * Complex.I * n * z.re)
        else 0) (neg_injective.comp <| Nat.cast_injective.comp PNat.coe_injective) ?_).mp
      ((hv z).hasSum.congr_fun ?_)
    · convert hP.add hN using 1
      funext n
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · simp [hn, hn.not_gt]
      · simp
      · simp [hn, hn.not_gt]
    · rintro n hn
      refine ite_eq_right_iff.mpr fun hpos ↦ absurd ⟨(-n).toNat.toPNat', ?_⟩ hn
      simp [hpos]
      omega
    · intro k
      simp
  · rintro n hn
    refine ite_eq_right_iff.mpr fun hpos ↦ absurd ⟨n.toNat.toPNat', ?_⟩ hn
    simp [hpos, hpos.le]
  · intro k
    simp

/-- **A cosine expansion is a Fourier expansion** with `a(n) = a(-n) = c(n)/2` for `n ≥ 1` and
`a(0) = 0`. -/
lemma HasMaassCosineExpansion.hasMaassFourierExpansion (h : HasMaassCosineExpansion f r c) :
    HasMaassFourierExpansion f r fun n ↦
      if 0 < n then c n.toNat.toPNat' / 2 else if n < 0 then c (-n).toNat.toPNat' / 2 else 0 := by
  have hs (z : ℍ) :
      Summable fun k : ℕ+ ↦ ‖c k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im)‖ := by
    refine summable_norm_iff.mpr ?_
    have h0 := (h (mk (z.im * Complex.I) (by simpa using z.im_pos))).summable
    simp only [mk_im, mk_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, sub_zero, cos_zero,
      Complex.ofReal_one] at h0
    exact h0
  refine hasMaassFourierExpansion_of_pnat (u := fun k ↦ c k / 2) (v := fun k ↦ c k / 2)
    (fun z ↦ ?_) (fun z ↦ ?_) fun z ↦ (h z).congr_fun fun k ↦ ?_
  · refine ((hs z).div_const 2).of_norm_bounded fun k ↦ le_of_eq ?_
    simp [Complex.norm_exp]
    ring1
  · refine ((hs z).div_const 2).of_norm_bounded fun k ↦ le_of_eq ?_
    simp [Complex.norm_exp]
    ring1
  · have e1 : 2 * π * Complex.I * (k : ℕ) * z.re = ((2 * π * k * z.re : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring1
    have e2 :
        2 * π * Complex.I * ((-k : ℤ) : ℂ) * z.re = -((2 * π * k * z.re : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring1
    rw [e1, e2, Complex.ofReal_cos, Complex.cos]
    ring1

/-- **An absolutely convergent sine expansion is a Fourier expansion** with `a(n) = c(n)/(2i)`
and `a(-n) = -c(n)/(2i)` for `n ≥ 1` and `a(0) = 0`. -/
lemma HasMaassSineExpansion.hasMaassFourierExpansion (h : HasMaassSineExpansion f r c)
    (hs : ∀ z : ℍ,
      Summable fun k : ℕ+ ↦ ‖c k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im)‖) :
    HasMaassFourierExpansion f r fun n ↦ if 0 < n then c n.toNat.toPNat' / (2 * Complex.I)
      else if n < 0 then -c (-n).toNat.toPNat' / (2 * Complex.I) else 0 := by
  refine hasMaassFourierExpansion_of_pnat (u := fun k ↦ c k / (2 * Complex.I))
    (v := fun k ↦ -c k / (2 * Complex.I)) (fun z ↦ ?_) (fun z ↦ ?_)
    fun z ↦ (h z).congr_fun fun k ↦ ?_
  · refine ((hs z).div_const 2).of_norm_bounded fun k ↦ le_of_eq ?_
    simp [Complex.norm_exp]
    ring1
  · refine ((hs z).div_const 2).of_norm_bounded fun k ↦ le_of_eq ?_
    simp [Complex.norm_exp]
    ring1
  · have e1 : 2 * π * Complex.I * (k : ℕ) * z.re = ((2 * π * k * z.re : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring1
    have e2 :
        2 * π * Complex.I * ((-k : ℤ) : ℂ) * z.re = -((2 * π * k * z.re : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring1
    rw [e1, e2, Complex.ofReal_sin, Complex.sin]
    field_simp
    rw [Complex.I_sq]
    ring1

/-- **The cosine coefficients of an even `T_p`-eigenfunction**: if `f` has the cosine expansion
`∑ c(n) √y K_{ir}(2πny) cos(2πnx)` and `T_p f = λ_p f` on `ℍ` for a prime `p`, then
`c(p) = λ_p c(1)`, provided `K_{ir}(2πy) ≠ 0` for some `y > 0`. -/
lemma HasMaassCosineExpansion.coeff_prime_eq (hp : p.Prime) (h : HasMaassCosineExpansion f r c)
    (hT : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p f z = heckeEigenvalue * f z) (hy : 0 < y)
    (hK : (Complex.I * r).besselK (2 * π * y) ≠ 0) :
    c ⟨p, hp.pos⟩ = heckeEigenvalue * c 1 := by
  have hp' : p.toPNat' = ⟨p, hp.pos⟩ := PNat.eq <| PNat.toPNat'_coe hp.pos
  have h1 : Nat.toPNat' 1 = 1 := rfl
  have h' : c ⟨p, hp.pos⟩ / 2 = heckeEigenvalue * (c 1 / 2) := by
    simpa only [Nat.cast_pos, hp.pos, ite_true, Int.toNat_natCast, hp', zero_lt_one,
      Int.toNat_one, h1] using h.hasMaassFourierExpansion.coeff_prime_eq hp hT hy hK
  linear_combination 2 * h'

/-- **The sine coefficients of an odd `T_p`-eigenfunction**: if `f` has an absolutely convergent
sine expansion `∑ c(n) √y K_{ir}(2πny) sin(2πnx)` and `T_p f = λ_p f` on `ℍ` for a prime `p`,
then `c(p) = λ_p c(1)`, provided `K_{ir}(2πy) ≠ 0` for some `y > 0`. -/
lemma HasMaassSineExpansion.coeff_prime_eq (hp : p.Prime) (h : HasMaassSineExpansion f r c)
    (hs : ∀ z : ℍ,
      Summable fun k : ℕ+ ↦ ‖c k * √z.im * (Complex.I * r).besselK (2 * π * k * z.im)‖)
    (hT : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p f z = heckeEigenvalue * f z) (hy : 0 < y)
    (hK : (Complex.I * r).besselK (2 * π * y) ≠ 0) :
    c ⟨p, hp.pos⟩ = heckeEigenvalue * c 1 := by
  have hp' : p.toPNat' = ⟨p, hp.pos⟩ := PNat.eq <| PNat.toPNat'_coe hp.pos
  have h1 : Nat.toPNat' 1 = 1 := rfl
  have h' : c ⟨p, hp.pos⟩ / (2 * Complex.I) = heckeEigenvalue * (c 1 / (2 * Complex.I)) := by
    simpa only [Nat.cast_pos, hp.pos, ite_true, Int.toNat_natCast, hp', zero_lt_one,
      Int.toNat_one, h1] using (h.hasMaassFourierExpansion hs).coeff_prime_eq hp hT hy hK
  field_simp at h'
  exact h'

end UpperHalfPlane
