import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraCorrespondence
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraDecomposition

/-!
# Hecke equivariance of the Shimura correspondence on coefficients

The Shimura correspondence `Sh_t` is Hecke linear (LMFDB `cmf.shimura_correspondence`): it takes
Shimura's operator `T_{p²}` of weight `k/2` and character `χ` to the operator `T_p` of weight
`k - 1` and character `χ²`. On Fourier coefficients this is an identity of Dirichlet convolutions:
with `e(d) = χ_t(d) d ^ (λ - 1)`, `b(m) = a(t m²)`, `A = e * b`, `c = χ(p²) p ^ (k - 2)` and
`a' = T_{p²} a`,

`∑_{d ∣ n} e(d) a'(t (n/d)²) = A(p n) + c A(n / p)`,

for `p² ∤ t`, where `A(n / p) = 0` unless `p ∣ n`. It needs neither Shimura's theorem nor the
modularity of `g`, only that `e` is completely multiplicative.

## Main results

* `LSeries.convolution_mul_prime_of_dvd_eq_zero`: `(e * f)(p n) = e(p) (e * f)(n)` when `f` vanishes
  on the multiples of `p`.
* `LSeries.convolution_ite_dvd_of_pos`: `(e * V f)(n) = (e * f)(n / t)`, where `V f(m) = f(m / t)`.
* `LSeries.convolution_hecke`: the action of `T_{p²}` on a Dirichlet convolution.
* `ModularForm.halfIntegralHeckeCoeff_mul_sq`: the coefficients `a'(t m²)` of `T_{p²}` on `a`.
* `ModularForm.shimuraCoeff_halfIntegralHeckeCoeff`: **the Hecke equivariance of `Sh_t`**.
-/

open Finset Complex LSeries

open scoped «notation» NumberTheorySymbols

open jacobiSym (legendreSym.to_jacobiSym)

namespace LSeries

variable {e f : ℕ → ℂ} {p t n : ℕ}

/-- **The convolution with a function vanishing on the multiples of `p`**: if `f` vanishes on the
multiples of the prime `p` and `e(p d) = e(p) e(d)`, then `(e * f)(p n) = e(p) (e * f)(n)`. -/
lemma convolution_mul_prime_of_dvd_eq_zero (hp : p.Prime) (he : ∀ d, d ≠ 0 → e (p * d) = e p * e d)
    (hf : ∀ m, p ∣ m → f m = 0) (hn : n ≠ 0) : (e ⍟ f) (p * n) = e p * (e ⍟ f) n := by
  have hpn : p * n ≠ 0 := mul_ne_zero hp.ne_zero hn
  simp only [convolution_def]
  rw [mul_sum]
  have hinj :
      Set.InjOn (fun x : ℕ × ℕ ↦ (p * x.1, x.2)) (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    rintro ⟨x₁, x₂⟩ - ⟨y₁, y₂⟩ - h
    simp only [Prod.mk_inj] at h
    simp [Nat.eq_of_mul_eq_mul_left hp.pos h.1, h.2]
  have hsub : image (fun x : ℕ × ℕ ↦ (p * x.1, x.2)) n.divisorsAntidiagonal ⊆
      (p * n).divisorsAntidiagonal := by
    intro y hy
    rcases mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Nat.mem_divisorsAntidiagonal.mp hx with ⟨h1, -⟩
    refine Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hpn⟩
    simp only [mul_assoc, h1]
  rw [← sum_subset hsub, sum_image hinj]
  · refine sum_congr rfl fun x hx ↦ ?_
    rcases Nat.mem_divisorsAntidiagonal.mp hx with ⟨h1, -⟩
    have hx1 : x.1 ≠ 0 := fun h ↦ hn (by rw [← h1, h, zero_mul])
    rw [he _ hx1]
    ring1
  · intro y hy hy'
    rcases Nat.mem_divisorsAntidiagonal.mp hy with ⟨h1, -⟩
    have h2 : p ∣ y.1 * y.2 := h1 ▸ dvd_mul_right p n
    rcases hp.dvd_mul.mp h2 with h3 | h3
    · rcases h3 with ⟨q, hq⟩
      refine absurd (mem_image.mpr ⟨(q, y.2), Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hn⟩, ?_⟩) hy'
      · refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
        rw [← h1, hq, mul_assoc]
      · exact Prod.ext hq.symm rfl
    · rw [hf _ h3, mul_zero]

/-- **The convolution with the shift by `t`**: for `t > 0`, `(e * V f)(n) = (e * f)(n / t)` if
`t ∣ n` and `0` otherwise, where `V f(m) = f(m / t)` if `t ∣ m` and `0` otherwise. -/
lemma convolution_ite_dvd_of_pos (ht : 0 < t) :
    (e ⍟ fun m ↦ if t ∣ m then f (m / t) else 0) n = if t ∣ n then (e ⍟ f) (n / t) else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [convolution_def]
  split_ifs with hd
  · rcases hd with ⟨q, rfl⟩
    have hq : q ≠ 0 := right_ne_zero_of_mul hn
    rw [Nat.mul_div_cancel_left _ ht]
    have hinj :
        Set.InjOn (fun x : ℕ × ℕ ↦ (x.1, t * x.2)) (q.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
      rintro ⟨x₁, x₂⟩ - ⟨y₁, y₂⟩ - h
      simp only [Prod.mk_inj] at h
      simp [Nat.eq_of_mul_eq_mul_left ht h.2, h.1]
    have hsub : image (fun x : ℕ × ℕ ↦ (x.1, t * x.2)) q.divisorsAntidiagonal ⊆
        (t * q).divisorsAntidiagonal := by
      intro y hy
      rcases mem_image.mp hy with ⟨x, hx, rfl⟩
      rcases Nat.mem_divisorsAntidiagonal.mp hx with ⟨h1, -⟩
      refine Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hn⟩
      rw [← h1]
      ring1
    rw [← sum_subset hsub, sum_image hinj]
    · refine sum_congr rfl fun x _ ↦ ?_
      simp [Nat.mul_div_cancel_left _ ht]
    · intro y hy hy'
      rcases Nat.mem_divisorsAntidiagonal.mp hy with ⟨h1, -⟩
      have hnd : ¬t ∣ y.2 := by
        rintro ⟨r, hr⟩
        refine hy' (mem_image.mpr ⟨(y.1, r), Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hq⟩, ?_⟩)
        · refine Nat.eq_of_mul_eq_mul_left ht ?_
          rw [← h1, hr]
          ring1
        · exact Prod.ext rfl hr.symm
      simp [hnd]
  · refine sum_eq_zero fun x hx ↦ ?_
    rcases Nat.mem_divisorsAntidiagonal.mp hx with ⟨h1, -⟩
    have hnd : ¬t ∣ x.2 := fun h ↦ hd (h1 ▸ h.mul_left _)
    simp [hnd]

/-- **The action of `T_{p²}` on a Dirichlet convolution.** If `e(p d) = e(p) e(d)`, then for the
sequence `f'(m) = f(p m) + e(p) f(m) [p ∤ m] + c f(m / p) [p ∣ m]`,
`(e * f')(n) = (e * f)(p n) + c (e * f)(n / p) [p ∣ n]`, for `n ≠ 0`. -/
lemma convolution_hecke (hp : p.Prime) (he : ∀ d, d ≠ 0 → e (p * d) = e p * e d) (c : ℂ)
    (hn : n ≠ 0) : (e ⍟ fun m ↦ f (p * m) + e p * (if p ∣ m then 0 else f m) +
      c * if p ∣ m then f (m / p) else 0) n = (e ⍟ f) (p * n) +
        c * if p ∣ n then (e ⍟ f) (n / p) else 0 := by
  have hsplit : (e ⍟ f) (p * n) = (e ⍟ fun m ↦ if p ∣ m then 0 else f m) (p * n) +
      (e ⍟ fun m ↦ if p ∣ m then f m else 0) (p * n) := by
    simp only [convolution_def]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> ring1
  have hV : (fun m ↦ if p ∣ m then f m else 0) = fun m ↦ if p ∣ m then f (p * (m / p)) else 0 := by
    ext m
    split_ifs with hm
    · rw [Nat.mul_div_cancel' hm]
    · rfl
  have h1 : (e ⍟ fun m ↦ if p ∣ m then f m else 0) (p * n) = (e ⍟ fun m ↦ f (p * m)) n := by
    rw [hV, convolution_ite_dvd_of_pos (f := fun m ↦ f (p * m)) hp.pos]
    simp [Nat.mul_div_cancel_left _ hp.pos]
  have h2 : (e ⍟ fun m ↦ if p ∣ m then 0 else f m) (p * n) =
      e p * (e ⍟ fun m ↦ if p ∣ m then 0 else f m) n :=
    convolution_mul_prime_of_dvd_eq_zero hp he (fun m hm ↦ by simp [hm]) hn
  have h3 : (e ⍟ fun m ↦ if p ∣ m then f (m / p) else 0) n = if p ∣ n then (e ⍟ f) (n / p) else 0 :=
    convolution_ite_dvd_of_pos hp.pos
  rw [hsplit, h1, h2, ← h3]
  simp only [convolution_def, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  ring1

end LSeries

namespace ModularForm

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ} {t p n x y : ℕ} {a : ℕ → ℂ}

private lemma shimuraCharacter_mul (hx : x ≠ 0) (hy : y ≠ 0) :
    shimuraCharacter χ k t (x * y) = shimuraCharacter χ k t x * shimuraCharacter χ k t y := by
  simp only [shimuraCharacter, jacobiSym.mul_right' _ hx hy]
  push_cast
  rw [map_mul, mul_zpow]
  ring1

private lemma shimuraWeight_mul (hx : x ≠ 0) (hy : y ≠ 0) : shimuraCharacter χ k t (x * y) *
    ((x * y : ℕ) : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1) =
      (shimuraCharacter χ k t x * (x : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1)) *
        (shimuraCharacter χ k t y * (y : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1)) := by
  rw [shimuraCharacter_mul hx hy, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring1

/-- **The coefficients of `T_{p²}` on the square classes**: for a prime `p` with `p² ∤ t` and
`λ ≥ 0`, the coefficient of `T_{p²} a` at `t m²` is
`a(t (p m)²) + χ_t(p) p ^ (λ - 1) a(t m²) [p ∤ m] + χ(p²) p ^ (k - 2) a(t (m / p)²) [p ∣ m]`. -/
lemma halfIntegralHeckeCoeff_mul_sq (hp : p.Prime) (ht : ¬p ^ 2 ∣ t) (hl : 0 ≤ (k - 1) / 2)
    (m : ℕ) : halfIntegralHeckeCoeff χ k p a (t * m ^ 2) = a (t * (p * m) ^ 2) +
      (shimuraCharacter χ k t p * (p : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1)) *
        (if p ∣ m then 0 else a (t * m ^ 2)) +
      χ (p ^ 2) * (p : ℂ) ^ (k - 2) * if p ∣ m then a (t * (m / p) ^ 2) else 0 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have e1 : p ^ 2 * (t * m ^ 2) = t * (p * m) ^ 2 := by ring1
  rw [halfIntegralHeckeCoeff, e1]
  have hdiv : p ^ 2 ∣ t * m ^ 2 ↔ p ∣ m := by
    constructor
    · intro h
      by_contra hm
      have hc : Nat.Coprime (p ^ 2) (m ^ 2) := (hp.coprime_iff_not_dvd.mpr hm).pow 2 2
      exact ht (hc.dvd_of_dvd_mul_right h)
    · rintro ⟨q, rfl⟩
      exact ⟨t * q ^ 2, by ring1⟩
  by_cases hd : p ∣ m
  · rcases hd with ⟨q, rfl⟩
    have hJ : jacobiSym ((-1) ^ ((k - 1) / 2).toNat * ((t * (p * q) ^ 2 : ℕ) : ℤ)) p = 0 := by
      rw [← legendreSym.to_jacobiSym, legendreSym.eq_zero_iff]
      push_cast
      simp
    have hdvd : p ^ 2 ∣ t * (p * q) ^ 2 := ⟨t * q ^ 2, by ring1⟩
    have hquot : t * (p * q) ^ 2 / p ^ 2 = t * q ^ 2 := by
      refine Nat.div_eq_of_eq_mul_right (pow_pos hp.pos 2) ?_
      ring1
    simp only [hJ, dvd_mul_right, hdvd, hquot, Nat.mul_div_cancel_left _ hp.pos]
    push_cast
    ring1
  · have hnd : ¬p ^ 2 ∣ t * m ^ 2 := fun h ↦ hd (hdiv.mp h)
    have hm1 : J(((m : ℕ) : ℤ) | p) ^ 2 = 1 := by
      refine jacobiSym.sq_one ?_
      have h1 : Nat.Coprime m p := (hp.coprime_iff_not_dvd.mpr hd).symm
      simpa using h1
    have hJ : jacobiSym ((-1) ^ ((k - 1) / 2).toNat * ((t * m ^ 2 : ℕ) : ℤ)) p =
        jacobiSym (-1) p ^ ((k - 1) / 2).toNat * jacobiSym t p := by
      push_cast
      rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.pow_left, hm1,
        mul_one]
    have hz : ((jacobiSym (-1) p : ℤ) : ℂ) ^ ((k - 1) / 2) =
        ((jacobiSym (-1) p : ℤ) : ℂ) ^ ((k - 1) / 2).toNat := by
      nth_rw 1 [← Int.toNat_of_nonneg hl]
      rw [zpow_natCast]
    have hc : (p : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1) = (p : ℂ) ^ ((k - 1) / 2 - 1) := by
      rw [← cpow_intCast]
      push_cast
      rfl
    simp only [hJ, hd, hnd, shimuraCharacter, hz, hc]
    push_cast
    ring1

/-- **The Shimura correspondence is Hecke equivariant on coefficients** (LMFDB
`cmf.shimura_correspondence`): for a prime `p` with `p² ∤ t`, the lift `Sh_t` of `T_{p²} a` is `T_p`
of weight `k - 1` and character `χ²` applied to the lift `A = Sh_t a`:
`(Sh_t (T_{p²} a))(n) = A(p n) + χ(p²) p ^ (k - 2) A(n / p)`, with `A(n / p) = 0` unless `p ∣ n`. -/
lemma shimuraCoeff_halfIntegralHeckeCoeff (hp : p.Prime) (ht : ¬p ^ 2 ∣ t) (hl : 0 ≤ (k - 1) / 2)
    (hn : n ≠ 0) : shimuraCoeff χ k t (halfIntegralHeckeCoeff χ k p a) n =
      shimuraCoeff χ k t a (p * n) +
        χ (p ^ 2) * (p : ℂ) ^ (k - 2) * if p ∣ n then shimuraCoeff χ k t a (n / p) else 0 := by
  have he : ∀ d, d ≠ 0 → shimuraCharacter χ k t (p * d : ℕ) *
      ((p * d : ℕ) : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1) =
        (shimuraCharacter χ k t p * (p : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1)) *
          (shimuraCharacter χ k t d * (d : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1)) := fun d hd ↦
    shimuraWeight_mul hp.ne_zero hd
  simp only [shimuraCoeff, halfIntegralHeckeCoeff_mul_sq hp ht hl]
  exact LSeries.convolution_hecke (f := fun m ↦ a (t * m ^ 2))
    (e := fun d ↦ shimuraCharacter χ k t d * (d : ℂ) ^ ((((k - 1) / 2 : ℤ) : ℂ) - 1)) hp he
    (χ (p ^ 2) * (p : ℂ) ^ (k - 2)) hn

end ModularForm
