import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeSineExpansion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.LevelOperators

/-!
# The Main Lemma of Atkin and Lehner for Maass forms

The Main Lemma of Atkin and Lehner (*Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), Theorem 1;
Miyake, *Modular forms*, 4.6.8; Diamond–Shurman, *A first course in modular forms*,
Theorem 5.7.1) says that a cusp form on `Γ₀(N)` whose Fourier coefficients vanish at every index
prime to `N` is old. This file proves the analogue for square-integrable Maass forms of weight `0`
on `Γ₀(N)` with trivial character (`UpperHalfPlane.maassSpace`), by the induction on the primes of
Atkin and Lehner, which involves no holomorphy.

The vanishing of the coefficients is written without coefficients: for primes `q_1, …, q_r`, the
function `(1 - E_{q_r}) ⋯ (1 - E_{q_1}) F` (`UpperHalfPlane.maassCoprimeFilter`), with
`(E_q F)(z) = q⁻¹ ∑_{j < q} F(z + j/q)`, keeps exactly the terms of the Fourier expansion of `F`
whose index is prime to every `q_i`. If it vanishes, then `F` lies in the span of the `G(q_i z)`,
`G` of level `N / q_i`. The induction removes the prime `q = q_1`: `H = F - E_q F` has level `Nq`,
so by induction `H` is a sum of `G_p(pz)` with `G_p` of level `Nq / p`, `p ≠ q`; applying the trace
from `Γ₀(Nq)` to `Γ₀(N)`, which fixes `F`, commutes with the level raising, and sends `E_q F` to
`(1 - c) F + c Z(q ·)` with `c ≠ 0` and `Z` of level `N / q`
(`UpperHalfPlane.sub_maassLevelTrace_maassPeriodAverage`), gives
`c (F - Z(q ·)) = ∑_p (Tr G_p)(p ·)`.

## Main definitions

* `UpperHalfPlane.maassPrimeFilter`: the function `F - E_q F`.
* `UpperHalfPlane.maassCoprimeFilter`: the function `(1 - E_{q_r}) ⋯ (1 - E_{q_1}) F`.
* `UpperHalfPlane.maassOldPart`: the part of the old space coming from a list of primes.

## Main results

* `UpperHalfPlane.mem_maassOldPart_of_maassCoprimeFilter_eq_zero`: the Main Lemma for a list of
  primes.
* `UpperHalfPlane.mem_maassOldSpace_of_maassCoprimeFilter_eq_zero`: the Main Lemma.
* `UpperHalfPlane.HasMaassCosineExpansion.primeFilter`,
  `UpperHalfPlane.HasMaassSineExpansion.primeFilter`: the filter on expansions.
* `UpperHalfPlane.mem_maassOldSpace_of_hasMaassCosineExpansion`,
  `UpperHalfPlane.mem_maassOldSpace_of_hasMaassSineExpansion`: a form whose cosine or sine
  coefficients vanish at every index prime to the level is old.
-/

open Real

namespace UpperHalfPlane

variable {N q : ℕ} {F G H : ℍ → ℂ} {eigenvalue r : ℂ} {c : ℕ+ → ℂ} {S S' : List ℕ}

variable (q F) in
/-- The function `F - E_q F` on `ℍ`, with `E_q` of `maassPeriodAverage`: for `F` with a Fourier
expansion in `x`, it keeps exactly the terms whose index is prime to `q`, for `q` prime. -/
noncomputable def maassPrimeFilter : ℍ → ℂ :=
  fun z ↦ F z - maassPeriodAverage q F z

/-- The function `(1 - E_{q_r}) ⋯ (1 - E_{q_1}) F` on `ℍ` for a list `q_1, …, q_r` of primes: for
`F` with a Fourier expansion in `x`, it keeps exactly the terms whose index is prime to every
`q_i`. -/
noncomputable def maassCoprimeFilter : List ℕ → (ℍ → ℂ) → ℍ → ℂ
  | [], F => F
  | q :: S, F => maassCoprimeFilter S (maassPrimeFilter q F)

variable (N eigenvalue S) in
/-- The part of the old space of level `N` coming from a list `S` of primes: the span of the
functions `z ↦ G(pz)` with `p` in `S` and `G` in `M(N / p, 1, λ)`. -/
noncomputable def maassOldPart : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ {F | ∃ p ∈ S, ∃ G ∈ maassSpace (N / p) 1 eigenvalue, maassLevelRaise p G = F}

lemma maassOldPart_mono (h : S ⊆ S') : maassOldPart N eigenvalue S ≤ maassOldPart N eigenvalue S' :=
  Submodule.span_mono fun _ ⟨p, hp, hG⟩ ↦ ⟨p, h hp, hG⟩

lemma maassLevelTrace_add :
    maassLevelTrace N q (G + H) = maassLevelTrace N q G + maassLevelTrace N q H := by
  funext z
  simp only [maassLevelTrace, Pi.add_apply, Finset.sum_add_distrib, mul_add]

lemma maassLevelTrace_smul (a : ℂ) : maassLevelTrace N q (a • H) = a • maassLevelTrace N q H := by
  funext z
  simp only [maassLevelTrace, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring1

lemma maassLevelTrace_zero : maassLevelTrace N q (0 : ℍ → ℂ) = 0 := by
  funext z
  simp [maassLevelTrace]

lemma maassLevelTrace_mem_maassOldPart [hq : Fact q.Prime] [NeZero N] (hqS : q ∉ S)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ N) (hqN : q ∣ N) (hH : H ∈ maassOldPart (N * q) eigenvalue S) :
    maassLevelTrace N q H ∈ maassOldPart N eigenvalue S := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, G, hG, rfl⟩
    rcases hS p hp with ⟨hpp, N', hN'⟩
    subst hN'
    have hN0 : NeZero N' := ⟨right_ne_zero_of_mul (NeZero.ne (p * N'))⟩
    have hqN' : q ∣ N' := (hq.out.dvd_mul.mp hqN).resolve_left fun h ↦ hqS <| by
      rwa [(Nat.prime_dvd_prime_iff_eq hq.out hpp).mp h]
    have hG' : G ∈ maassSpace (N' * q) 1 eigenvalue := by
      rwa [mul_assoc, Nat.mul_div_cancel_left _ hpp.pos] at hG
    rw [maassLevelTrace_maassLevelRaise hpp.pos]
    refine Submodule.subset_span ⟨p, hp, _, ?_, rfl⟩
    rw [Nat.mul_div_cancel_left _ hpp.pos]
    exact maassLevelTrace_mem_maassSpace hqN' hG'
  | zero =>
    rw [maassLevelTrace_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [maassLevelTrace_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [maassLevelTrace_smul]
    exact Submodule.smul_mem _ a hx

/-- **The Main Lemma of Atkin and Lehner, for a list of primes**: for a list `S` of distinct primes
dividing `N ≠ 0` and `F` in `M(N, 1, λ)`, if `(1 - E_{q_r}) ⋯ (1 - E_{q_1}) F = 0`, then `F` lies in
the span of the functions `G(pz)` with `p` in `S` and `G` in `M(N / p, 1, λ)`. The induction on `S`
goes through the level `Nq`: `H = F - E_q F` lies in `M(Nq, 1, λ)`, so `H` is a sum of `G_p(pz)`
with `G_p` of level `Nq / p`, and the trace from `Γ₀(Nq)` to `Γ₀(N)` gives
`Tr H = c (F - Z(qz))` (`sub_maassLevelTrace_maassPeriodAverage`) on one side and a sum of
`(Tr G_p)(pz)` on the other, with `Tr G_p` of level `N / p`. -/
lemma mem_maassOldPart_of_maassCoprimeFilter_eq_zero [NeZero N] (hS0 : S.Nodup)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ N) (hF : F ∈ maassSpace N 1 eigenvalue)
    (h : maassCoprimeFilter S F = 0) : F ∈ maassOldPart N eigenvalue S := by
  induction S generalizing N F with
  | nil =>
    have h0 : F = 0 := h
    rw [h0]
    exact zero_mem _
  | cons q S ih =>
    rcases List.nodup_cons.mp hS0 with ⟨hqS, hS1⟩
    rcases hS q List.mem_cons_self with ⟨hqp, hqN⟩
    have hS2 : ∀ p ∈ S, p.Prime ∧ p ∣ N := fun p hp ↦ hS p (List.mem_cons_of_mem q hp)
    have : Fact q.Prime := ⟨hqp⟩
    have : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) hqp.ne_zero⟩
    have hH : maassPrimeFilter q F ∈ maassSpace (N * q) 1 eigenvalue :=
      sub_mem (maassSpace_le_of_dvd (dvd_mul_right N q) hF)
        (maassPeriodAverage_mem_maassSpace hqN hF)
    have hold : maassPrimeFilter q F ∈ maassOldPart (N * q) eigenvalue S :=
      ih hS1 (fun p hp ↦ (hS2 p hp).imp_right (·.mul_right q)) hH h
    have htr : maassLevelTrace N q (maassPrimeFilter q F) ∈ maassOldPart N eigenvalue S :=
      maassLevelTrace_mem_maassOldPart hqS hS2 hqN hold
    rcases hqN with ⟨M, rfl⟩
    have : NeZero M := ⟨right_ne_zero_of_mul (NeZero.ne (q * M))⟩
    have ha : maassTraceConstant M q ≠ 0 := maassTraceConstant_ne_zero
    have hsub : maassLevelTrace (q * M) q (maassPrimeFilter q F) =
        fun z ↦ F z - maassLevelTrace (q * M) q (maassPeriodAverage q F) z := by
      funext z
      have h1 : maassLevelTrace (q * M) q F z = F z :=
        congrFun (maassLevelTrace_eq_self hF) z
      rw [← h1]
      simp only [maassPrimeFilter, maassLevelTrace, ← mul_sub, ← Finset.sum_sub_distrib]
    have hFeq : F = (maassTraceConstant M q)⁻¹ • maassLevelTrace (q * M) q (maassPrimeFilter q F) +
        maassLevelRaise q (maassTraceRemainder M q F) := by
      funext z
      rw [hsub]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        sub_maassLevelTrace_maassPeriodAverage hF]
      field_simp
      ring1
    rw [hFeq]
    refine add_mem (Submodule.smul_mem _ _ (maassOldPart_mono (List.subset_cons_self q S) htr)) ?_
    refine Submodule.subset_span ⟨q, List.mem_cons_self, _, ?_, rfl⟩
    rw [Nat.mul_div_cancel_left _ hqp.pos]
    exact maassTraceRemainder_mem_maassSpace hF

lemma maassOldPart_le_maassOldSpace [NeZero N] (hS : ∀ p ∈ S, p.Prime ∧ p ∣ N) :
    maassOldPart N eigenvalue S ≤ maassOldSpace N 1 eigenvalue := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨p, hp, G, hG, rfl⟩
  rcases hS p hp with ⟨hpp, hpN⟩
  have hdvd : p * (N / p) ∣ N := dvd_of_eq (Nat.mul_div_cancel' hpN)
  have hne : N / p ≠ N := (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne N)) hpp.one_lt).ne
  have h : maassLevelRaise p G ∈ maassOldSpace N ((1 : DirichletCharacter ℂ (N / p)).changeLevel
      (dvd_of_mul_left_dvd hdvd)) eigenvalue :=
    maassLevelRaise_mem_maassOldSpace hG hdvd hne
  rwa [DirichletCharacter.changeLevel_one] at h

/-- **The Main Lemma of Atkin and Lehner for Maass forms** (the analogue of Atkin and Lehner, *Hecke
operators on `Γ₀(m)`*, Theorem 1; Miyake, *Modular forms*, 4.6.8): for `F` in `M(N, 1, λ)`,
`N ≠ 0`, if `(∏_{p ∣ N} (1 - E_p)) F = 0`, that is, if the Fourier coefficients of `F` vanish at
every index prime to `N`, then `F` lies in the old space of `M(N, 1, λ)`. -/
lemma mem_maassOldSpace_of_maassCoprimeFilter_eq_zero [NeZero N]
    (hF : F ∈ maassSpace N 1 eigenvalue) (h : maassCoprimeFilter N.primeFactors.toList F = 0) :
    F ∈ maassOldSpace N 1 eigenvalue := by
  have hS : ∀ p ∈ N.primeFactors.toList, p.Prime ∧ p ∣ N := fun p hp ↦ by
    have hp' : p ∈ N.primeFactors := Finset.mem_toList.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hp', Nat.dvd_of_mem_primeFactors hp'⟩
  exact maassOldPart_le_maassOldSpace hS <|
    mem_maassOldPart_of_maassCoprimeFilter_eq_zero (Finset.nodup_toList _) hS hF h

lemma sum_range_cos_two_pi_mul_add (hq : q ≠ 0) (n : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range q, (cos (2 * π * n * (x + j / q)) : ℂ) =
      (if q ∣ n then (q : ℂ) else 0) * cos (2 * π * n * x) := by
  have e (j : ℕ) : (cos (2 * π * n * (x + j / q)) : ℂ) =
      1 / 2 * (Complex.exp (((2 * π * n * x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (2 * π * Complex.I * ((n : ℤ) : ℂ) * j / q) +
          Complex.exp (-((2 * π * n * x : ℝ) : ℂ) * Complex.I) *
            Complex.exp (2 * π * Complex.I * ((-n : ℤ) : ℂ) * j / q)) := by
    have h1 : ((2 * π * n * (x + j / q) : ℝ) : ℂ) * Complex.I =
        ((2 * π * n * x : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I * ((n : ℤ) : ℂ) * j / q := by
      push_cast
      ring1
    have h2 : -((2 * π * n * (x + j / q) : ℝ) : ℂ) * Complex.I =
        -((2 * π * n * x : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I * ((-n : ℤ) : ℂ) * j / q := by
      push_cast
      ring1
    rw [Complex.ofReal_cos, Complex.cos, h1, h2, Complex.exp_add, Complex.exp_add]
    ring1
  rw [Finset.sum_congr rfl fun j _ ↦ e j, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_range_exp_two_pi_I_mul_div hq,
    sum_range_exp_two_pi_I_mul_div hq, Complex.ofReal_cos, Complex.cos]
  simp only [dvd_neg, Int.natCast_dvd_natCast]
  split_ifs <;> ring1

lemma sum_range_sin_two_pi_mul_add (hq : q ≠ 0) (n : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range q, (sin (2 * π * n * (x + j / q)) : ℂ) =
      (if q ∣ n then (q : ℂ) else 0) * sin (2 * π * n * x) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have h : ∑ j ∈ Finset.range q, (sin (2 * π * n * ((q * x + j) / q)) : ℂ) =
      (if q ∣ n then (q : ℂ) else 0) * sin (2 * π * n * (q * x) / q) :=
    sum_range_sin_two_pi_mul hq n (q * x)
  have h1 (j : ℕ) : 2 * π * n * ((q * x + j) / q) = 2 * π * n * (x + j / q) := by
    field_simp
  have h2 : 2 * π * n * (q * x) / q = 2 * π * n * x := by
    field_simp
  simpa only [h1, h2] using h

lemma hasSum_maassPrimeFilter {e : ℝ → ℝ} (hq : q ≠ 0)
    (he : ∀ (n : ℕ) (x : ℝ), ∑ j ∈ Finset.range q, (e (2 * π * n * (x + j / q)) : ℂ) =
      (if q ∣ n then (q : ℂ) else 0) * e (2 * π * n * x))
    (h : ∀ z : ℍ, HasSum (fun n : ℕ+ ↦ c n * √z.im * (Complex.I * r).besselK (2 * π * n * z.im) *
      e (2 * π * n * z.re)) (F z)) (z : ℍ) :
    HasSum (fun n : ℕ+ ↦ (if q ∣ (n : ℕ) then 0 else c n) * √z.im *
      (Complex.I * r).besselK (2 * π * n * z.im) * e (2 * π * n * z.re))
      (maassPrimeFilter q F z) := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hpos (j : ℕ) : 0 < ((z : ℂ) + j / q).im := by
    simpa using z.im_pos
  have hj (j : ℕ) : HasSum (fun n : ℕ+ ↦ c n * √z.im * (Complex.I * r).besselK (2 * π * n * z.im) *
      e (2 * π * n * (z.re + j / q))) (F (ofComplex ((z : ℂ) + j / q))) := by
    have him : (ofComplex ((z : ℂ) + j / q)).im = z.im := by
      rw [ofComplex_apply_of_im_pos (hpos j)]
      simp
    have hre : (ofComplex ((z : ℂ) + j / q)).re = z.re + j / q := by
      rw [ofComplex_apply_of_im_pos (hpos j)]
      simp
    have h1 : HasSum (fun n : ℕ+ ↦ c n * √(ofComplex ((z : ℂ) + j / q)).im *
        (Complex.I * r).besselK (2 * π * n * (ofComplex ((z : ℂ) + j / q)).im) *
          e (2 * π * n * (ofComplex ((z : ℂ) + j / q)).re)) (F (ofComplex ((z : ℂ) + j / q))) :=
      h (ofComplex ((z : ℂ) + j / q))
    rwa [him, hre] at h1
  have hs : HasSum (fun n : ℕ+ ↦ (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, (c n * √z.im *
      (Complex.I * r).besselK (2 * π * n * z.im) * e (2 * π * n * (z.re + j / q))))
      ((q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, F (ofComplex ((z : ℂ) + j / q))) :=
    (hasSum_sum fun j _ ↦ hj j).mul_left (q : ℂ)⁻¹
  refine ((h z).sub hs).congr_fun fun n ↦ ?_
  rw [← Finset.mul_sum, he]
  split_ifs
  · field_simp
    ring1
  · ring1

/-- **The filter on cosine expansions**: if `F` has the cosine expansion with coefficients `c(n)`,
then `F - E_q F` has the cosine expansion with coefficients `c(n)` for `q ∤ n` and `0` for
`q ∣ n`. -/
lemma HasMaassCosineExpansion.primeFilter (hq : q ≠ 0)
    (h : HasMaassCosineExpansion (F ∘ ofComplex) r c) :
    HasMaassCosineExpansion (maassPrimeFilter q F ∘ ofComplex) r
      fun n ↦ if q ∣ (n : ℕ) then 0 else c n := by
  intro z
  simpa using hasSum_maassPrimeFilter (F := F) (e := cos) hq (sum_range_cos_two_pi_mul_add hq)
    (fun z ↦ by simpa using h z) z

/-- **The filter on sine expansions**: if `F` has the sine expansion with coefficients `c(n)`, then
`F - E_q F` has the sine expansion with coefficients `c(n)` for `q ∤ n` and `0` for `q ∣ n`. -/
lemma HasMaassSineExpansion.primeFilter (hq : q ≠ 0)
    (h : HasMaassSineExpansion (F ∘ ofComplex) r c) :
    HasMaassSineExpansion (maassPrimeFilter q F ∘ ofComplex) r
      fun n ↦ if q ∣ (n : ℕ) then 0 else c n := by
  intro z
  simpa using hasSum_maassPrimeFilter (F := F) (e := sin) hq (sum_range_sin_two_pi_mul_add hq)
    (fun z ↦ by simpa using h z) z

lemma ite_exists_mem_cons_dvd (n : ℕ) (a : ℂ) : (if ∃ p ∈ q :: S, p ∣ n then 0 else a) =
    if ∃ p ∈ S, p ∣ n then 0 else if q ∣ n then 0 else a := by
  by_cases hq : q ∣ n <;> simp [hq]

lemma HasMaassCosineExpansion.coprimeFilter (hS : ∀ p ∈ S, p ≠ 0)
    (h : HasMaassCosineExpansion (F ∘ ofComplex) r c) :
    HasMaassCosineExpansion (maassCoprimeFilter S F ∘ ofComplex) r
      fun n ↦ if ∃ p ∈ S, p ∣ (n : ℕ) then 0 else c n := by
  induction S generalizing F c with
  | nil =>
    simpa [maassCoprimeFilter] using h
  | cons q S ih =>
    simpa only [ite_exists_mem_cons_dvd, maassCoprimeFilter] using
      ih (fun p hp ↦ hS p (List.mem_cons_of_mem q hp)) (h.primeFilter (hS q List.mem_cons_self))

lemma HasMaassSineExpansion.coprimeFilter (hS : ∀ p ∈ S, p ≠ 0)
    (h : HasMaassSineExpansion (F ∘ ofComplex) r c) :
    HasMaassSineExpansion (maassCoprimeFilter S F ∘ ofComplex) r
      fun n ↦ if ∃ p ∈ S, p ∣ (n : ℕ) then 0 else c n := by
  induction S generalizing F c with
  | nil =>
    simpa [maassCoprimeFilter] using h
  | cons q S ih =>
    simpa only [ite_exists_mem_cons_dvd, maassCoprimeFilter] using
      ih (fun p hp ↦ hS p (List.mem_cons_of_mem q hp)) (h.primeFilter (hS q List.mem_cons_self))

lemma ne_zero_of_mem_primeFactors_toList {p : ℕ} (hp : p ∈ N.primeFactors.toList) : p ≠ 0 :=
  (Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp)).ne_zero

variable [NeZero N]

lemma ite_exists_prime_dvd_eq_zero (hc : ∀ n : ℕ+, (n : ℕ).Coprime N → c n = 0) :
    (fun n : ℕ+ ↦ if ∃ p ∈ N.primeFactors.toList, p ∣ (n : ℕ) then 0 else c n) = 0 := by
  funext n
  split_ifs with h
  · rfl
  · refine hc n ?_
    by_contra hn
    rcases Nat.exists_prime_and_dvd hn with ⟨p, hp, hpg⟩
    exact h ⟨p, Finset.mem_toList.mpr <| Nat.mem_primeFactors.mpr
      ⟨hp, hpg.trans (Nat.gcd_dvd_right _ _), NeZero.ne N⟩, hpg.trans (Nat.gcd_dvd_left _ _)⟩

/-- **A form with vanishing cosine coefficients prime to the level is old**: if `F` in
`M(N, 1, λ)`, `N ≠ 0`, has a cosine expansion whose coefficients vanish at every index prime to `N`,
then `F` lies in the old space (LMFDB `mf.maass.mwf.coefficients`). -/
lemma mem_maassOldSpace_of_hasMaassCosineExpansion (hF : F ∈ maassSpace N 1 eigenvalue)
    (h : HasMaassCosineExpansion (F ∘ ofComplex) r c) (hc : ∀ n : ℕ+, (n : ℕ).Coprime N → c n = 0) :
    F ∈ maassOldSpace N 1 eigenvalue := by
  refine mem_maassOldSpace_of_maassCoprimeFilter_eq_zero hF (funext fun z ↦ ?_)
  have h1 : HasMaassCosineExpansion (maassCoprimeFilter N.primeFactors.toList F ∘ ofComplex) r
      fun n ↦ if ∃ p ∈ N.primeFactors.toList, p ∣ (n : ℕ) then 0 else c n :=
    h.coprimeFilter fun p hp ↦ ne_zero_of_mem_primeFactors_toList hp
  rw [ite_exists_prime_dvd_eq_zero hc] at h1
  have h2 : maassCoprimeFilter N.primeFactors.toList F (ofComplex z) = 0 :=
    (h1 z).unique (by simp)
  simpa using h2

/-- **A form with vanishing sine coefficients prime to the level is old**: if `F` in
`M(N, 1, λ)`, `N ≠ 0`, has a sine expansion whose coefficients vanish at every index prime to `N`,
then `F` lies in the old space (LMFDB `mf.maass.mwf.coefficients`). -/
lemma mem_maassOldSpace_of_hasMaassSineExpansion (hF : F ∈ maassSpace N 1 eigenvalue)
    (h : HasMaassSineExpansion (F ∘ ofComplex) r c) (hc : ∀ n : ℕ+, (n : ℕ).Coprime N → c n = 0) :
    F ∈ maassOldSpace N 1 eigenvalue := by
  refine mem_maassOldSpace_of_maassCoprimeFilter_eq_zero hF (funext fun z ↦ ?_)
  have h1 : HasMaassSineExpansion (maassCoprimeFilter N.primeFactors.toList F ∘ ofComplex) r
      fun n ↦ if ∃ p ∈ N.primeFactors.toList, p ∣ (n : ℕ) then 0 else c n :=
    h.coprimeFilter fun p hp ↦ ne_zero_of_mem_primeFactors_toList hp
  rw [ite_exists_prime_dvd_eq_zero hc] at h1
  have h2 : maassCoprimeFilter N.primeFactors.toList F (ofComplex z) = 0 :=
    (h1 z).unique (by simp)
  simpa using h2

end UpperHalfPlane
