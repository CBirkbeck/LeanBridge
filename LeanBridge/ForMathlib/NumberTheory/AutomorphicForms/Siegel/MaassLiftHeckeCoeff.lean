import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.BinaryQuadraticFormLines
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoHeckeT1Fourier

/-!
# The Hecke operators on the Fourier coefficients of the Maass lift

The Maass lift of a Jacobi cusp form of index `1` and weight `k + 1` has the Fourier coefficient
`A(f) = ∑_{d ∣ cont f} d^k C(Δ/d²)` at a positive definite binary quadratic form `f`, with
`Δ = -disc f` and `C(N)` the coefficients of the Jacobi form by discriminant
(`SiegelUpperHalfSpace.maassFormCoeff`). The Hecke operators `T(p)` and `T_1(p²)` of `Sp(4, ℤ)`
act on Fourier coefficients through the forms `f/p`, `pf`, the forms `f ∘ g_ℓ` on the sublattices
of index `p` and their quotients by `p` and `p²` (`SiegelUpperHalfSpace.heckeTpCoeff`,
`SiegelUpperHalfSpace.heckeT₁Coeff`). Writing `f = p^v f₀` with `f₀` primitive at `p`, splitting
each divisor of the content into its prime-to-`p` part `d` and a power of `p`, and counting the
lines with `TauCeti.BinaryQuadraticForm.lineCount`, both actions reduce to local identities in the
coefficients `u_j = C(p²Δ/(d p^j)²)`. These follow from the Jacobi relation
`C(p²N) + (-N/p) p^{k-1} C(N) + p^{2k-1} C(N/p²) = a_p C(N)`
(`ModularForm.jacobiDiscrCoeff_hecke`), used at `N = Δ/(d p^j)²`, where `(-N/p) = 0` for `j < v`,
and from the vanishing of `C(N)` at `N ≡ 1, 2 (mod 4)`. Both identities were checked numerically on
the Fourier coefficients of `χ₁₀` at `p = 2, 3`.

## Main definitions

* `SiegelUpperHalfSpace.divForm`: the form `f/m`.
* `SiegelUpperHalfSpace.maassFormCoeff`: the Maass coefficients `A(f)`.
* `SiegelUpperHalfSpace.discrCoeff`: the coefficient `C(N/m²)`, `0` unless `m² ∣ N`.
* `SiegelUpperHalfSpace.swapForm`: the form `[c, b, a]` of `[a, b, c]`.

## Main results

* `SiegelUpperHalfSpace.heckeTp_maassFormCoeff`: `T(p)` multiplies the Maass coefficients by
  `a_p + p^{k-1} + p^k`.
* `SiegelUpperHalfSpace.heckeT₁_maassFormCoeff`: `T_1(p²)` multiplies the Maass coefficients by
  `(p + 1) p^{k-2} a_p + p^{2k-2} - p^{2k-4}`.
-/

open Finset TauCeti BinaryQuadraticForm

open ModularForm (negKronecker negKronecker_eq_zero_of_dvd negKronecker_mul_sq)

namespace SiegelUpperHalfSpace

/-! ### The local identities -/

variable {p : ℕ} {t P W U ap χ : ℂ} {u : ℕ → ℂ} {a : ℕ}

lemma tp_local_identity (ht : t = p * P) (hW : W = P * t)
    (hrel : ∀ j < a, ap * u (j + 1) = u j + W * u (j + 2))
    (hrela : ap * u (a + 1) = u a + χ * P * u (a + 1) + W * u (a + 2)) :
    W * ∑ j ∈ range a, t ^ j * u (j + 2) + P * ((p + 1) * ∑ j ∈ range a, t ^ j * u (j + 1) +
      (1 + χ) * t ^ a * u (a + 1) + t ^ (a + 1) * u (a + 2)) + ∑ j ∈ range (a + 2), t ^ j * u j =
        (ap + P + t) * ∑ j ∈ range (a + 1), t ^ j * u (j + 1) := by
  have hsum : ap * ∑ j ∈ range a, t ^ j * u (j + 1) =
      ∑ j ∈ range a, t ^ j * u j + W * ∑ j ∈ range a, t ^ j * u (j + 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ by
      linear_combination t ^ j * hrel j (Finset.mem_range.mp hj)
  have e₁ : ∑ j ∈ range (a + 2), t ^ j * u j =
      ∑ j ∈ range a, t ^ j * u j + t ^ a * u a + t ^ (a + 1) * u (a + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have e₂ : ∑ j ∈ range (a + 1), t ^ j * u (j + 1) =
      ∑ j ∈ range a, t ^ j * u (j + 1) + t ^ a * u (a + 1) :=
    Finset.sum_range_succ _ _
  rw [e₁, e₂]
  linear_combination (-1 : ℂ) * hsum - t ^ a * hrela - (∑ j ∈ range a, t ^ j * u (j + 1)) * ht -
    t ^ a * u (a + 2) * hW

lemma t1_local_identity_zero (hP : P = p * U) (ht : t = p * P) (hW : W = P * t)
    (hrela : ap * u (0 + 1) = u 0 + χ * P * u (0 + 1) + W * u (0 + 2)) :
    W * U * u 2 + U ^ 2 * (p * (1 + χ) - p - 1) * ∑ j ∈ range 1, t ^ j * u (j + 1) +
      U * ((p + 1) * ∑ j ∈ range 1, t ^ j * u j + (1 + χ) * t ^ 1 * u 1 + t ^ 2 * u 2) =
        ((p + 1) * U * ap + P ^ 2 - U ^ 2) * ∑ j ∈ range 1, t ^ j * u (j + 1) := by
  simp only [Finset.sum_range_one] at hrela ⊢
  subst hW ht hP
  linear_combination -((p + 1) * U) * hrela

lemma t1_local_identity_succ (hP : P = p * U) (ht : t = p * P) (hW : W = P * t)
    (hrel : ∀ j < a + 1, ap * u (j + 1) = u j + W * u (j + 2))
    (hrela : ap * u (a + 2) = u (a + 1) + χ * P * u (a + 2) + W * u (a + 3)) :
    W * U * ((p + 1) * ∑ j ∈ range a, t ^ j * u (j + 2) + (1 + χ) * t ^ a * u (a + 2) +
      t ^ (a + 1) * u (a + 3)) +
      U ^ 2 * (p * (p + 1) - p - 1) * ∑ j ∈ range (a + 2), t ^ j * u (j + 1) +
      U * ((p + 1) * ∑ j ∈ range (a + 2), t ^ j * u j + (1 + χ) * t ^ (a + 2) * u (a + 2) +
        t ^ (a + 3) * u (a + 3)) =
      ((p + 1) * U * ap + P ^ 2 - U ^ 2) * ∑ j ∈ range (a + 2), t ^ j * u (j + 1) := by
  have hsum : ap * ∑ j ∈ range a, t ^ j * u (j + 1) =
      ∑ j ∈ range a, t ^ j * u j + W * ∑ j ∈ range a, t ^ j * u (j + 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ by
      linear_combination t ^ j * hrel j (by have hj' : j < a := Finset.mem_range.mp hj; omega)
  have e₁ : ∑ j ∈ range (a + 2), t ^ j * u j =
      ∑ j ∈ range a, t ^ j * u j + t ^ a * u a + t ^ (a + 1) * u (a + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have e₂ : ∑ j ∈ range (a + 2), t ^ j * u (j + 1) =
      ∑ j ∈ range a, t ^ j * u (j + 1) + t ^ a * u (a + 1) + t ^ (a + 1) * u (a + 2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hrela' : ap * u (a + 1) = u a + W * u (a + 2) := hrel a (lt_add_one a)
  rw [e₁, e₂]
  subst hW ht hP
  linear_combination -((p + 1) * U) * (hsum + ((p : ℂ) * (p * U)) ^ a * hrela' +
    ((p : ℂ) * (p * U)) ^ (a + 1) * hrela)

/-! ### Binary quadratic forms -/

/-- The form `f/m` with coefficients `f.a/m, f.b/m, f.c/m`, which is `g` if `f = m • g`. -/
def divForm (m : ℤ) (f : BinaryQuadraticForm ℤ) : BinaryQuadraticForm ℤ :=
  ⟨f.a / m, f.b / m, f.c / m⟩

variable (k : ℤ) (C : ℤ → ℂ) {f : BinaryQuadraticForm ℤ}

lemma smul_divForm {m : ℤ} (h : (m.natAbs : ℕ) ∣ f.content) : m • divForm m f = f := by
  rw [dvd_content_iff] at h
  rcases h with ⟨ha, hb, hc⟩
  rw [Int.natCast_natAbs, abs_dvd] at ha hb hc
  ext <;> exact Int.mul_ediv_cancel' ‹_›

lemma divForm_smul {m : ℤ} (hm : m ≠ 0) : divForm m (m • f) = f := by
  ext <;> exact Int.mul_ediv_cancel_left _ hm

lemma posDef_smul_iff {r : ℤ} (hr : 0 < r) :
    (0 < (r • f).a ∧ (r • f).discrim < 0) ↔ (0 < f.a ∧ f.discrim < 0) := by
  rw [discrim_smul', smul_a', smul_eq_mul]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨pos_of_mul_pos_right h₁ hr.le, neg_of_mul_neg_right h₂ (sq_nonneg r)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨mul_pos hr h₁, mul_neg_of_pos_of_neg (pow_pos hr 2) h₂⟩

lemma posDef_lineForm_iff (hp : p ≠ 0) (ℓ : Option (Fin p)) :
    (0 < (f.lineForm p ℓ).a ∧ (f.lineForm p ℓ).discrim < 0) ↔ (0 < f.a ∧ f.discrim < 0) := by
  have hp' : (0 : ℤ) < p := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hp)
  rw [discrim_lineForm]
  rcases ℓ with - | c <;> simp only [lineForm]
  · exact and_congr Iff.rfl ⟨fun h ↦ neg_of_mul_neg_right h (sq_nonneg _),
      fun h ↦ mul_neg_of_pos_of_neg (pow_pos hp' 2) h⟩
  · exact and_congr
      ⟨fun h ↦ pos_of_mul_pos_right h (sq_nonneg _), fun h ↦ mul_pos (pow_pos hp' 2) h⟩
      ⟨fun h ↦ neg_of_mul_neg_right h (sq_nonneg _),
        fun h ↦ mul_neg_of_pos_of_neg (pow_pos hp' 2) h⟩

/-! ### The Maass coefficients -/

variable (f) in
/-- The **Maass coefficient** of weight `k + 1` at a binary quadratic form `f = [n, r, m]`, for
coefficients `C(N)` by discriminant: `∑_{d ∣ gcd(n, r, m)} d^k C(Δ/d²)` with
`Δ = 4nm - r² = -disc f` for `f` positive definite, and `0` otherwise. For a Jacobi cusp form `φ`
of index `1` with `C(N) = c(N)` this is the coefficient `a(n, r, m)` of its Maass lift
(`SiegelUpperHalfSpace.maassCoeff`). -/
noncomputable def maassFormCoeff : ℂ :=
  if 0 < f.a ∧ f.discrim < 0 then
    ∑ d ∈ f.content.divisors, (d : ℂ) ^ k * C (-f.discrim / (d : ℤ) ^ 2) else 0

lemma maassFormCoeff_eq_sum (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0) {J : ℕ}
    (hJ : f.content.factorization p < J) : maassFormCoeff k C f =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k * ∑ j ∈ range J,
        if p ^ j ∣ f.content then ((p : ℂ) ^ k) ^ j * C (-f.discrim / ((d * p ^ j : ℕ) : ℤ) ^ 2)
          else 0 := by
  have he : f.content ≠ 0 := fun h ↦ hf.1.ne' (by rw [(content_eq_zero_iff f).mp h]; rfl)
  have he' : ordCompl[p] f.content ≠ 0 := (Nat.ordCompl_pos p he).ne'
  have hnd {d : ℕ} (hd : d ∈ (ordCompl[p] f.content).divisors) : ¬p ∣ d := fun h ↦
    Nat.not_dvd_ordCompl hp he (h.trans (Nat.dvd_of_mem_divisors hd))
  rw [maassFormCoeff, ite_eq_left hf]
  have hfilter : (range J).filter (fun j ↦ p ^ j ∣ f.content) =
      range (f.content.factorization p + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, hp.pow_dvd_iff_le_factorization he]
    omega
  simp only [← Finset.sum_filter, hfilter, Finset.mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun d ↦ (ordCompl[p] d, d.factorization p)) (fun x ↦ x.1 * p ^ x.2)
    (fun d hd ↦ ?_) (fun x hx ↦ ?_) (fun d hd ↦ ?_) (fun x hx ↦ ?_) fun d hd ↦ ?_
  · have hd' : d ∣ f.content := Nat.dvd_of_mem_divisors hd
    have hd₀ : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    simp only [Finset.mem_product, Nat.mem_divisors, Finset.mem_range]
    exact ⟨⟨Nat.ordCompl_dvd_ordCompl_of_dvd hd' p, he'⟩,
      Nat.lt_succ_of_le ((Nat.factorization_le_iff_dvd hd₀ he).mpr hd' p)⟩
  · simp only [Finset.mem_product, Nat.mem_divisors, Finset.mem_range] at hx
    refine Nat.mem_divisors.mpr ⟨?_, he⟩
    rw [← Nat.ordProj_mul_ordCompl_eq_self f.content p, mul_comm (p ^ f.content.factorization p)]
    exact mul_dvd_mul hx.1.1 (pow_dvd_pow p (Nat.lt_succ_iff.mp hx.2))
  · exact (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self d p)
  · have hx₁ : ¬p ∣ x.1 := hnd (Finset.mem_product.mp hx).1
    have hx₀ : x.1 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Finset.mem_product.mp hx).1)
    refine Prod.ext ?_ ?_
    · simp only
      rw [mul_comm, Nat.ordCompl_pow_mul_of_not_dvd _ hp hx₁]
    · simp only
      rw [Nat.factorization_mul hx₀ (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hx₁, zero_add, hp.factorization_pow,
        Finsupp.single_eq_same]
  · have hd' : ordCompl[p] d * p ^ d.factorization p = d :=
      (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self d p)
    have hpow :
        (d : ℂ) ^ k = ((ordCompl[p] d : ℕ) : ℂ) ^ k * ((p : ℂ) ^ k) ^ d.factorization p := by
      conv_lhs => rw [← hd']
      rw [Nat.cast_mul, Nat.cast_pow, mul_zpow, ← zpow_natCast (p : ℂ), ← zpow_mul, mul_comm _ k,
        zpow_mul, zpow_natCast]
    simp only
    rw [hd', hpow]
    ring1

/-! ### Auxiliary facts -/

/-- The coefficient `C(N/m²)` if `m² ∣ N`, and `0` otherwise. -/
noncomputable def discrCoeff (N : ℤ) (m : ℕ) : ℂ :=
  if (m : ℤ) ^ 2 ∣ N then C (N / (m : ℤ) ^ 2) else 0

variable {k C}

lemma discrCoeff_mul (hp : p ≠ 0) (N : ℤ) (m : ℕ) :
    discrCoeff C ((p : ℤ) ^ 2 * N) (p * m) = discrCoeff C N m := by
  have hp' : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp)
  have e : ((p * m : ℕ) : ℤ) ^ 2 = (p : ℤ) ^ 2 * (m : ℤ) ^ 2 := by push_cast; ring1
  rw [discrCoeff, discrCoeff, e]
  by_cases h : (m : ℤ) ^ 2 ∣ N
  · rw [ite_eq_left (mul_dvd_mul_left _ h), ite_eq_left h, Int.mul_ediv_mul_of_pos _ _
      (pow_pos (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hp)) 2)]
  · rw [ite_eq_right fun h' ↦ h ((mul_dvd_mul_iff_left hp').mp h'), ite_eq_right h]

lemma discrCoeff_one (N : ℤ) : discrCoeff C N 1 = C N := by
  simp [discrCoeff]

lemma discrCoeff_of_dvd {N : ℤ} {m : ℕ} (h : (m : ℤ) ^ 2 ∣ N) :
    discrCoeff C N m = C (N / (m : ℤ) ^ 2) :=
  ite_eq_left h

lemma sq_dvd_discrim_of_dvd_content {m : ℕ} (h : m ∣ f.content) : (m : ℤ) ^ 2 ∣ f.discrim := by
  rw [← smul_divForm (f := f) (m := (m : ℤ)) (by simpa using h), discrim_smul']
  exact dvd_mul_right _ _

lemma neg_discrim_eq_sq_mul {m : ℕ} (h : m ∣ f.content) :
    -f.discrim = (m : ℤ) ^ 2 * -(divForm m f).discrim := by
  conv_lhs => rw [← smul_divForm (f := f) (m := (m : ℤ)) (by simpa using h)]
  rw [discrim_smul', mul_neg]

lemma neg_discrim_div_sq {m : ℕ} (hm : m ≠ 0) (h : m ∣ f.content) :
    -f.discrim / (m : ℤ) ^ 2 = -(divForm m f).discrim := by
  rw [neg_discrim_eq_sq_mul h, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (by exact_mod_cast hm))]

lemma neg_discrim_emod_four (g : BinaryQuadraticForm ℤ) :
    -g.discrim % 4 = 0 ∨ -g.discrim % 4 = 3 := by
  rcases discrim_emod_four_eq_zero_or_one g with h | h <;> omega

lemma ordCompl_eq_of_dvd_of_dvd {b s : ℕ} (hp : p.Prime) (h₁ : a ∣ b) (h₂ : b ∣ p ^ s * a) :
    ordCompl[p] b = ordCompl[p] a :=
  Nat.dvd_antisymm (Nat.ordCompl_self_pow_mul a s hp ▸ Nat.ordCompl_dvd_ordCompl_of_dvd h₂ p)
    (Nat.ordCompl_dvd_ordCompl_of_dvd h₁ p)

lemma sum_range_ite_lt {J n : ℕ} (h : n ≤ J) (F : ℕ → ℂ) :
    ∑ j ∈ range J, (if j < n then F j else 0) = ∑ j ∈ range n, F j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma mul_pow_dvd_content {d j : ℕ} (hd : d ∈ (ordCompl[p] f.content).divisors)
    (hj : j ≤ f.content.factorization p) : d * p ^ j ∣ f.content := by
  rw [← Nat.ordProj_mul_ordCompl_eq_self f.content p, mul_comm (p ^ f.content.factorization p)]
  exact mul_dvd_mul (Nat.dvd_of_mem_divisors hd) (pow_dvd_pow p hj)

lemma content_ne_zero (hf : 0 < f.a ∧ f.discrim < 0) : f.content ≠ 0 :=
  fun h ↦ hf.1.ne' (by rw [(content_eq_zero_iff f).mp h]; rfl)

lemma maassFormCoeff_eq_sum_self (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0) :
    maassFormCoeff k C f = ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
      ∑ j ∈ range (f.content.factorization p + 1),
        ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) := by
  rw [maassFormCoeff_eq_sum k C hp hf (lt_add_one _)]
  refine Finset.sum_congr rfl fun d hd ↦ congrArg _ (Finset.sum_congr rfl fun j hj ↦ ?_)
  have hj' : j ≤ f.content.factorization p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdvd : d * p ^ j ∣ f.content := mul_pow_dvd_content hd hj'
  have e : d * p ^ (j + 1) = p * (d * p ^ j) := by ring1
  rw [ite_eq_left ((pow_dvd_pow p hj').trans (Nat.ordProj_dvd _ _)), e, discrCoeff_mul hp.ne_zero,
    discrCoeff_of_dvd (dvd_neg.mpr (sq_dvd_discrim_of_dvd_content hdvd))]

lemma factorization_mul_self (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    (p * n).factorization p = n.factorization p + 1 := by
  rw [Nat.factorization_mul hp.ne_zero hn, Finsupp.add_apply, hp.factorization_self, add_comm]

lemma ordCompl_mul_self (hp : p.Prime) (n : ℕ) : ordCompl[p] (p * n) = ordCompl[p] n := by
  simpa using Nat.ordCompl_self_pow_mul n 1 hp

lemma maassFormCoeff_smul_eq_sum (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0) :
    maassFormCoeff k C ((p : ℤ) • f) = ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
      ∑ j ∈ range (f.content.factorization p + 2),
        ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j) := by
  have hpf : 0 < ((p : ℤ) • f).a ∧ ((p : ℤ) • f).discrim < 0 :=
    (posDef_smul_iff (Int.natCast_pos.mpr hp.pos)).mpr hf
  have hc : ((p : ℤ) • f).content = p * f.content := by rw [content_smul', Int.natAbs_natCast]
  have hv : (((p : ℤ) • f).content).factorization p = f.content.factorization p + 1 := by
    rw [hc, factorization_mul_self hp (content_ne_zero hf)]
  have hoc : ordCompl[p] ((p : ℤ) • f).content = ordCompl[p] f.content := by
    rw [hc, ordCompl_mul_self hp]
  rw [maassFormCoeff_eq_sum k C hp hpf (J := f.content.factorization p + 2) (by omega), hoc]
  refine Finset.sum_congr rfl fun d hd ↦ congrArg _ (Finset.sum_congr rfl fun j hj ↦ ?_)
  have hj' : j ≤ (((p : ℤ) • f).content).factorization p := by
    rw [hv]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdvd : d * p ^ j ∣ ((p : ℤ) • f).content := mul_pow_dvd_content (hoc ▸ hd) hj'
  have e : -((p : ℤ) • f).discrim = (p : ℤ) ^ 2 * -f.discrim := by
    rw [discrim_smul', mul_neg]
  rw [ite_eq_left ((pow_dvd_pow p hj').trans (Nat.ordProj_dvd _ _)), ← e,
    discrCoeff_of_dvd (dvd_neg.mpr (sq_dvd_discrim_of_dvd_content hdvd))]

lemma maassFormCoeff_divForm_eq_sum (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0)
    (hpe : p ∣ f.content) : maassFormCoeff k C (divForm p f) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p),
          ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2)) := by
  have hfg : (p : ℤ) • divForm p f = f := smul_divForm (by simpa using hpe)
  have hg : 0 < (divForm p f).a ∧ (divForm p f).discrim < 0 :=
    (posDef_smul_iff (Int.natCast_pos.mpr hp.pos)).mp (hfg.symm ▸ hf)
  have hc : f.content = p * (divForm p f).content := by
    conv_lhs => rw [← hfg]
    rw [content_smul', Int.natAbs_natCast]
  have hv : f.content.factorization p = (divForm p f).content.factorization p + 1 := by
    rw [hc, factorization_mul_self hp (content_ne_zero hg)]
  have hoc : ordCompl[p] (divForm p f).content = ordCompl[p] f.content := by
    rw [hc, ordCompl_mul_self hp]
  have hd : -f.discrim = (p : ℤ) ^ 2 * -(divForm p f).discrim := by
    conv_lhs => rw [← hfg]
    rw [discrim_smul', mul_neg]
  rw [maassFormCoeff_eq_sum k C hp hg (J := f.content.factorization p) (by omega), hoc]
  refine Finset.sum_congr rfl fun d hd' ↦ congrArg _ (Finset.sum_congr rfl fun j hj ↦ ?_)
  have hj' : j ≤ (divForm p f).content.factorization p := by
    have hj₁ : j < f.content.factorization p := Finset.mem_range.mp hj
    omega
  have hdvd : d * p ^ j ∣ (divForm p f).content := mul_pow_dvd_content (hoc ▸ hd') hj'
  have e : d * p ^ (j + 2) = p * (p * (d * p ^ j)) := by ring1
  rw [ite_eq_left ((pow_dvd_pow p hj').trans (Nat.ordProj_dvd _ _)), hd, e,
    discrCoeff_mul hp.ne_zero, discrCoeff_mul hp.ne_zero,
    discrCoeff_of_dvd (dvd_neg.mpr (sq_dvd_discrim_of_dvd_content hdvd))]

lemma maassFormCoeff_divForm_lineForm (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0)
    (ℓ : Option (Fin p)) (hℓ : p ∣ (f.lineForm p ℓ).content) :
    maassFormCoeff k C (divForm p (f.lineForm p ℓ)) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p + 3), if p ^ (j + 1) ∣ (f.lineForm p ℓ).content then
          ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) else 0 := by
  have he : f.content ≠ 0 := content_ne_zero hf
  have hX : (p : ℤ) • divForm p (f.lineForm p ℓ) = f.lineForm p ℓ :=
    smul_divForm (by simpa using hℓ)
  have hpX : 0 < (divForm p (f.lineForm p ℓ)).a ∧ (divForm p (f.lineForm p ℓ)).discrim < 0 :=
    (posDef_smul_iff (Int.natCast_pos.mpr hp.pos)).mp
      (hX.symm ▸ (posDef_lineForm_iff hp.ne_zero ℓ).mpr hf)
  have hc : (f.lineForm p ℓ).content = p * (divForm p (f.lineForm p ℓ)).content := by
    conv_lhs => rw [← hX]
    rw [content_smul', Int.natAbs_natCast]
  have hoc : ordCompl[p] (divForm p (f.lineForm p ℓ)).content = ordCompl[p] f.content := by
    rw [← ordCompl_mul_self hp, ← hc]
    exact ordCompl_eq_of_dvd_of_dvd hp (content_dvd_content_lineForm ℓ) (content_lineForm_dvd ℓ)
  have hcX : (divForm p (f.lineForm p ℓ)).content ≠ 0 := content_ne_zero hpX
  have hv :
      (divForm p (f.lineForm p ℓ)).content.factorization p < f.content.factorization p + 3 := by
    have hG : (f.lineForm p ℓ).content ≠ 0 := by
      rw [hc]
      exact mul_ne_zero hp.ne_zero hcX
    have h₁ : (f.lineForm p ℓ).content.factorization p ≤ (p ^ 2 * f.content).factorization p :=
      (Nat.factorization_le_iff_dvd hG (mul_ne_zero (pow_ne_zero 2 hp.ne_zero) he)).mpr
        (content_lineForm_dvd ℓ) p
    rw [Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) he, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same, hc, factorization_mul_self hp hcX] at h₁
    omega
  have hd : -(divForm p (f.lineForm p ℓ)).discrim = -f.discrim := by
    have h₁ : (f.lineForm p ℓ).discrim = p ^ 2 * f.discrim := discrim_lineForm ℓ
    rw [← hX, discrim_smul'] at h₁
    rw [mul_left_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.ne_zero)) h₁]
  rw [maassFormCoeff_eq_sum k C hp hpX hv, hoc]
  refine Finset.sum_congr rfl fun d hd' ↦ congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  have hiff : p ^ (j + 1) ∣ (f.lineForm p ℓ).content ↔
      p ^ j ∣ (divForm p (f.lineForm p ℓ)).content := by
    rw [hc, pow_succ, mul_comm (p ^ j), Nat.mul_dvd_mul_iff_left hp.pos]
  by_cases hj : p ^ j ∣ (divForm p (f.lineForm p ℓ)).content
  · have hd₁ : d ∣ ordCompl[p] f.content := Nat.dvd_of_mem_divisors hd'
    have hcop : Nat.Coprime d (p ^ j) :=
      ((Nat.coprime_ordCompl hp he).symm.coprime_dvd_left hd₁).pow_right j
    have hdX : d ∣ (divForm p (f.lineForm p ℓ)).content :=
      hd₁.trans (hoc ▸ Nat.ordCompl_dvd _ _)
    have hdvd : d * p ^ j ∣ (divForm p (f.lineForm p ℓ)).content :=
      hcop.mul_dvd_of_dvd_of_dvd hdX hj
    have e : d * p ^ (j + 1) = p * (d * p ^ j) := by ring1
    rw [ite_eq_left hj, ite_eq_left (hiff.mpr hj), e, discrCoeff_mul hp.ne_zero, ← hd,
      discrCoeff_of_dvd (dvd_neg.mpr (sq_dvd_discrim_of_dvd_content hdvd))]
  · rw [ite_eq_right hj, ite_eq_right fun h ↦ hj (hiff.mp h)]

/-! ### The line counts of `f = p^a f₀` -/

variable (f) in
lemma smul_divForm_ordProj :
    ((p : ℤ) ^ f.content.factorization p) • divForm ((p : ℤ) ^ f.content.factorization p) f = f :=
  smul_divForm (by simpa using Nat.ordProj_dvd _ _)

lemma content_divForm_ordProj (hp : p.Prime) :
    (divForm ((p : ℤ) ^ f.content.factorization p) f).content = ordCompl[p] f.content := by
  have h : f.content = p ^ f.content.factorization p *
      (divForm ((p : ℤ) ^ f.content.factorization p) f).content := by
    conv_lhs => rw [← smul_divForm_ordProj (p := p) f]
    rw [content_smul', Int.natAbs_pow, Int.natAbs_natCast]
  exact (Nat.div_eq_of_eq_mul_right (pow_pos hp.pos _) h).symm

variable (f) in
lemma discrim_divForm_ordProj :
    f.discrim = (p : ℤ) ^ (2 * f.content.factorization p) *
      (divForm ((p : ℤ) ^ f.content.factorization p) f).discrim := by
  conv_lhs => rw [← smul_divForm_ordProj (p := p) f]
  rw [discrim_smul', ← pow_mul, mul_comm (f.content.factorization p)]

lemma lineCount_of_le {i : ℕ} (hi : i ≤ f.content.factorization p) : f.lineCount p i = p + 1 :=
  (congrArg (fun g ↦ g.lineCount p i) (smul_divForm_ordProj (p := p) f)).symm.trans
    (lineCount_pow_smul_of_le hi)

lemma lineCount_add (hp : p.Prime) (i : ℕ) : f.lineCount p (f.content.factorization p + i) =
    (divForm ((p : ℤ) ^ f.content.factorization p) f).lineCount p i :=
  (congrArg (fun g ↦ g.lineCount p (f.content.factorization p + i))
    (smul_divForm_ordProj (p := p) f)).symm.trans (lineCount_pow_smul_add hp.ne_zero _ _)

lemma not_dvd_content_divForm_ordProj (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0) :
    ¬p ∣ (divForm ((p : ℤ) ^ f.content.factorization p) f).content := by
  rw [content_divForm_ordProj hp]
  exact Nat.not_dvd_ordCompl hp (content_ne_zero hf)

lemma mul_sq_emod_four {x : ℤ} (hx : x % 4 = 0 ∨ x % 4 = 3) (y : ℤ) :
    x * y ^ 2 % 4 = 0 ∨ x * y ^ 2 % 4 = 3 := by
  rcases Int.even_or_odd' y with ⟨s, rfl | rfl⟩
  · left
    have e : x * (2 * s) ^ 2 = 4 * (x * s ^ 2) := by ring1
    rw [e, Int.mul_emod_right]
  · have e : x * (2 * s + 1) ^ 2 = x + 4 * (x * (s ^ 2 + s)) := by ring1
    rw [e, Int.add_mul_emod_self_left]
    exact hx

/-! ### The coefficients of `T(p)` through forms -/

lemma divForm_lineForm_none (hp : p ≠ 0) :
    divForm p (f.lineForm p none) = ⟨f.a / p, f.b, p * f.c⟩ := by
  ext <;> simp [divForm, lineForm, hp, pow_two, mul_assoc]

lemma divForm_lineForm_some (hp : p ≠ 0) (c : Fin p) : divForm p (f.lineForm p (some c)) =
    ⟨p * f.a, f.b + 2 * c * f.a, (f.c + f.b * c + f.a * c ^ 2) / p⟩ := by
  ext <;> simp [divForm, lineForm, hp, pow_two, mul_assoc]

lemma heckeTpCoeff_eq (hp : p ≠ 0) (κ : ℤ) (A : BinaryQuadraticForm ℤ → ℂ) :
    heckeTpCoeff p κ (fun T ↦ A ⟨T.1, T.2.1, T.2.2⟩) (f.a, f.b, f.c) =
      (p : ℂ) ^ (2 * κ - 3) * (if p ∣ f.content then A (divForm p f) else 0) +
        (p : ℂ) ^ (κ - 2) * ∑ ℓ : Option (Fin p),
          (if p ∣ (f.lineForm p ℓ).content then A (divForm p (f.lineForm p ℓ)) else 0) +
        A ((p : ℤ) • f) := by
  simp only [Fintype.sum_option, dvd_content_lineForm_none_iff, dvd_content_lineForm_some_iff,
    divForm_lineForm_none hp, divForm_lineForm_some hp, dvd_content_iff f p]
  rfl

lemma sum_linear_eq {s : Finset ℕ} {X Y Z R : ℕ → ℂ} {x y r : ℂ}
    (h : ∀ d ∈ s, x * X d + y * Y d + Z d = r * R d) :
    x * ∑ d ∈ s, X d + y * ∑ d ∈ s, Y d + ∑ d ∈ s, Z d = r * ∑ d ∈ s, R d := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl h

lemma sum_linear_eq₃ {s : Finset ℕ} {X Y Z R : ℕ → ℂ} {x y z r : ℂ}
    (h : ∀ d ∈ s, x * X d + y * Y d + z * Z d = r * R d) :
    x * ∑ d ∈ s, X d + y * ∑ d ∈ s, Y d + z * ∑ d ∈ s, Z d = r * ∑ d ∈ s, R d := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl h

lemma ite_maassFormCoeff_divForm (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0) :
    (if p ∣ f.content then maassFormCoeff k C (divForm p f) else 0) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p),
          ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2)) := by
  by_cases hpc : p ∣ f.content
  · rw [ite_eq_left hpc, maassFormCoeff_divForm_eq_sum hp hf hpc]
  · rw [ite_eq_right hpc, Nat.factorization_eq_zero_of_not_dvd hpc]
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Finset.sum_const_zero]

lemma ite_maassFormCoeff_divForm_lineForm (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0)
    (ℓ : Option (Fin p)) : (if p ∣ (f.lineForm p ℓ).content then
      maassFormCoeff k C (divForm p (f.lineForm p ℓ)) else 0) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p + 3), if p ^ (j + 1) ∣ (f.lineForm p ℓ).content then
          ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) else 0 := by
  by_cases hℓ : p ∣ (f.lineForm p ℓ).content
  · rw [ite_eq_left hℓ, maassFormCoeff_divForm_lineForm hp hf ℓ hℓ]
  · rw [ite_eq_right hℓ]
    refine (Finset.sum_eq_zero fun d _ ↦ ?_).symm
    rw [Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦
      hℓ ((dvd_pow_self p j.succ_ne_zero).trans h), mul_zero]

lemma sum_ite_maassFormCoeff_divForm_lineForm (hp : p.Prime) (hf : 0 < f.a ∧ f.discrim < 0) :
    ∑ ℓ : Option (Fin p), (if p ∣ (f.lineForm p ℓ).content then
      maassFormCoeff k C (divForm p (f.lineForm p ℓ)) else 0) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p + 3), (f.lineCount p (j + 1) : ℂ) *
          (((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1))) := by
  rw [Fintype.sum_congr _ _ (ite_maassFormCoeff_divForm_lineForm hp hf), Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

lemma maassFormCoeff_eq_zero (hf : ¬(0 < f.a ∧ f.discrim < 0)) : maassFormCoeff k C f = 0 :=
  ite_eq_right hf

lemma ite_maassFormCoeff_divForm_eq_zero (hp : p ≠ 0) (hf : ¬(0 < f.a ∧ f.discrim < 0)) :
    (if p ∣ f.content then maassFormCoeff k C (divForm p f) else 0) = 0 := by
  refine ite_eq_right_iff.mpr fun hpc ↦ maassFormCoeff_eq_zero fun h ↦ hf ?_
  rw [← smul_divForm (f := f) (m := (p : ℤ)) (by simpa using hpc)]
  exact (posDef_smul_iff (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hp))).mpr h

/-- The form `[c, b, a]` of `f = [a, b, c]`. -/
def swapForm (f : BinaryQuadraticForm ℤ) : BinaryQuadraticForm ℤ :=
  ⟨f.c, f.b, f.a⟩

lemma content_swapForm : (swapForm f).content = f.content := by
  refine Nat.dvd_antisymm ((dvd_content_iff _ _).mpr ?_) ((dvd_content_iff _ _).mpr ?_)
  · rcases (dvd_content_iff _ _).mp (dvd_refl (swapForm f).content) with ⟨h₁, h₂, h₃⟩
    exact ⟨h₃, h₂, h₁⟩
  · rcases (dvd_content_iff _ _).mp (dvd_refl f.content) with ⟨h₁, h₂, h₃⟩
    exact ⟨h₃, h₂, h₁⟩

lemma discrim_swapForm : (swapForm f).discrim = f.discrim := by
  simp only [swapForm, discrim_def, discrim]
  ring1

lemma divForm_one : divForm 1 f = f := by
  ext <;> simp [divForm]

lemma lineCount_swapForm_one_of_pos (hv : 0 < f.content.factorization p) :
    ((swapForm f).lineCount p 1 : ℂ) = p + 1 := by
  rw [lineCount_of_le (by rw [content_swapForm]; omega), Nat.cast_add, Nat.cast_one]

/-! ### The Jacobi relation on the coefficients `u_j` -/

variable [Fact p.Prime]

lemma jacobi_discrCoeff (hJ : ∀ N : ℤ, 0 < N → (N % 4 = 0 ∨ N % 4 = 3) →
      C ((p : ℤ) ^ 2 * N) + negKronecker p N * (p : ℂ) ^ (k - 1) * C N +
        (p : ℂ) ^ (2 * k - 1) * (if (p : ℤ) ^ 2 ∣ N then C (N / (p : ℤ) ^ 2) else 0) = ap * C N)
    (hf : 0 < f.a ∧ f.discrim < 0) {d : ℕ} (hd : d ∈ (ordCompl[p] f.content).divisors) {j : ℕ}
    (hj : j ≤ f.content.factorization p) :
    ap * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) =
      discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j) +
        negKronecker p (-f.discrim / ((d * p ^ j : ℕ) : ℤ) ^ 2) * (p : ℂ) ^ (k - 1) *
          discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) +
        (p : ℂ) ^ (2 * k - 1) * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2)) := by
  have hp : p.Prime := Fact.out
  have hm : d * p ^ j ∣ f.content := mul_pow_dvd_content hd hj
  have hm₀ : d * p ^ j ≠ 0 := ne_zero_of_dvd_ne_zero (content_ne_zero hf) hm
  have hfm : ((d * p ^ j : ℕ) : ℤ) • divForm (d * p ^ j : ℕ) f = f :=
    smul_divForm (by rw [Int.natAbs_natCast]; exact hm)
  have hpm : 0 < (divForm (d * p ^ j : ℕ) f).a ∧ (divForm (d * p ^ j : ℕ) f).discrim < 0 :=
    (posDef_smul_iff (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hm₀))).mp (hfm.symm ▸ hf)
  have hND : -f.discrim / ((d * p ^ j : ℕ) : ℤ) ^ 2 = -(divForm (d * p ^ j : ℕ) f).discrim :=
    neg_discrim_div_sq hm₀ hm
  have e₀ : (p : ℤ) ^ 2 * -f.discrim =
      ((d * p ^ j : ℕ) : ℤ) ^ 2 * ((p : ℤ) ^ 2 * -(divForm (d * p ^ j : ℕ) f).discrim) := by
    rw [neg_discrim_eq_sq_mul hm]
    ring1
  have hu₀ : discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j) =
      C ((p : ℤ) ^ 2 * -(divForm (d * p ^ j : ℕ) f).discrim) := by
    rw [e₀, discrCoeff_of_dvd (dvd_mul_right _ _),
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hm₀))]
  have hu₁ : discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) =
      C (-(divForm (d * p ^ j : ℕ) f).discrim) := by
    have e : d * p ^ (j + 1) = d * p ^ j * (p * 1) := by ring1
    rw [e₀, e, discrCoeff_mul hm₀, discrCoeff_mul hp.ne_zero, discrCoeff_one]
  have hu₂ : discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2)) =
      discrCoeff C (-(divForm (d * p ^ j : ℕ) f).discrim) p := by
    have e : d * p ^ (j + 2) = d * p ^ j * (p * p) := by ring1
    rw [e₀, e, discrCoeff_mul hm₀, discrCoeff_mul hp.ne_zero]
  rw [hND, hu₀, hu₁, hu₂, discrCoeff]
  linear_combination -(hJ _ (neg_pos.mpr hpm.2) (neg_discrim_emod_four _))

lemma negKronecker_neg_discrim_div_eq_zero {d : ℕ} (hd : d ∈ (ordCompl[p] f.content).divisors)
    {j : ℕ} (hj : j < f.content.factorization p) :
    negKronecker p (-f.discrim / ((d * p ^ j : ℕ) : ℤ) ^ 2) = 0 := by
  have hp : p.Prime := Fact.out
  have hm₀ : d * p ^ j ≠ 0 :=
    mul_ne_zero (Nat.pos_of_mem_divisors hd).ne' (pow_ne_zero _ hp.ne_zero)
  rcases sq_dvd_discrim_of_dvd_content (mul_pow_dvd_content (j := j + 1) hd hj) with ⟨X, hX⟩
  refine negKronecker_eq_zero_of_dvd ⟨-(p * X), ?_⟩
  have e : -f.discrim = ((d * p ^ j : ℕ) : ℤ) ^ 2 * (p * -(p * X)) := by
    rw [hX]
    push_cast
    ring1
  rw [e, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hm₀))]

lemma negKronecker_neg_discrim_div_factorization (hf : 0 < f.a ∧ f.discrim < 0) {d : ℕ}
    (hd : d ∈ (ordCompl[p] f.content).divisors) :
    negKronecker p (-f.discrim / ((d * p ^ f.content.factorization p : ℕ) : ℤ) ^ 2) =
      negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim) := by
  have hp : p.Prime := Fact.out
  have hm : d * p ^ f.content.factorization p ∣ f.content := mul_pow_dvd_content hd le_rfl
  have hm₀ : d * p ^ f.content.factorization p ≠ 0 :=
    ne_zero_of_dvd_ne_zero (content_ne_zero hf) hm
  have hpd : ¬p ∣ d := fun h ↦
    Nat.not_dvd_ordCompl hp (content_ne_zero hf) (h.trans (Nat.dvd_of_mem_divisors hd))
  have h₁ : f.discrim = (p : ℤ) ^ (2 * f.content.factorization p) *
      (divForm ((p : ℤ) ^ f.content.factorization p) f).discrim :=
    discrim_divForm_ordProj f
  have h₂ : ((d * p ^ f.content.factorization p : ℕ) : ℤ) ^ 2 =
      (d : ℤ) ^ 2 * (p : ℤ) ^ (2 * f.content.factorization p) := by
    push_cast
    ring1
  have e : -(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim =
      -(divForm ((d * p ^ f.content.factorization p : ℕ) : ℤ) f).discrim * (d : ℤ) ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero (2 * f.content.factorization p)
      (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℤ) ≠ 0)) ?_
    linear_combination h₁ + neg_discrim_eq_sq_mul hm +
      -(divForm ((d * p ^ f.content.factorization p : ℕ) : ℤ) f).discrim * h₂
  rw [neg_discrim_div_sq hm₀ hm, e, negKronecker_mul_sq _ hpd]

lemma posDef_divForm_ordProj (hf : 0 < f.a ∧ f.discrim < 0) :
    0 < (divForm ((p : ℤ) ^ f.content.factorization p) f).a ∧
      (divForm ((p : ℤ) ^ f.content.factorization p) f).discrim < 0 :=
  (posDef_smul_iff (pow_pos (Int.natCast_pos.mpr (Fact.out : p.Prime).pos) _)).mp
    ((smul_divForm_ordProj f).symm ▸ hf)

lemma lineCount_add_one_factorization (hf : 0 < f.a ∧ f.discrim < 0) :
    (f.lineCount p (f.content.factorization p + 1) : ℂ) =
      1 + negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim) := by
  have h : ((divForm ((p : ℤ) ^ f.content.factorization p) f).lineCount p 1 : ℤ) =
      1 + negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim) :=
    lineCount_one (not_dvd_content_divForm_ordProj Fact.out hf)
  rw [lineCount_add Fact.out]
  exact_mod_cast h

lemma lineCount_mul_discrCoeff (hf : 0 < f.a ∧ f.discrim < 0)
    (h0 : ∀ N : ℤ, 0 < N → (N % 4 = 1 ∨ N % 4 = 2) → C N = 0) {d : ℕ}
    (hd : d ∈ (ordCompl[p] f.content).divisors) :
    (f.lineCount p (f.content.factorization p + 2) : ℂ) *
      discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) =
      discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) := by
  have hp : p.Prime := Fact.out
  have hpos : 0 < -(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim :=
    neg_pos.mpr (posDef_divForm_ordProj hf).2
  have e₁ : (p : ℤ) ^ 2 * -f.discrim = ((p ^ (f.content.factorization p + 1) : ℕ) : ℤ) ^ 2 *
      -(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim := by
    rw [discrim_divForm_ordProj (p := p) f]
    push_cast
    ring1
  have e₂ : d * p ^ (f.content.factorization p + 2) =
      p ^ (f.content.factorization p + 1) * (d * p) := by
    ring1
  rw [lineCount_add hp 2, e₁, e₂, discrCoeff_mul (pow_ne_zero _ hp.ne_zero)]
  by_cases h : (p : ℤ) ^ 2 ∣ (divForm ((p : ℤ) ^ f.content.factorization p) f).discrim ∧
      (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim / p ^ 2 % 4 = 0 ∨
        -(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim / p ^ 2 % 4 = 3)
  · rw [lineCount_two (not_dvd_content_divForm_ordProj hp hf) h.1 h.2, Nat.cast_one, one_mul]
  · rw [discrCoeff]
    split_ifs with hdp
    · rcases hdp with ⟨N, hN⟩
      have hne : ((d * p : ℕ) : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2
        (Nat.cast_ne_zero.mpr (mul_ne_zero (Nat.pos_of_mem_divisors hd).ne' hp.ne_zero))
      have e : -(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim =
          (p : ℤ) ^ 2 * (N * (d : ℤ) ^ 2) := by
        rw [hN]
        push_cast
        ring1
      have h4 : ¬(N * (d : ℤ) ^ 2 % 4 = 0 ∨ N * (d : ℤ) ^ 2 % 4 = 3) := fun h4 ↦ h ⟨dvd_neg.mp
        ⟨_, e⟩, by rwa [e, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr
          hp.ne_zero))]⟩
      have h5 : ¬(N % 4 = 0 ∨ N % 4 = 3) := fun h5 ↦ h4 (mul_sq_emod_four h5 d)
      rw [hN, Int.mul_ediv_cancel_left _ hne,
        h0 N (pos_of_mul_pos_right (hN ▸ hpos) (sq_nonneg _)) (by omega), mul_zero]
    · rw [mul_zero]

lemma sum_range_lineCount_mul (hf : 0 < f.a ∧ f.discrim < 0)
    (h0 : ∀ N : ℤ, 0 < N → (N % 4 = 1 ∨ N % 4 = 2) → C N = 0) {d : ℕ}
    (hd : d ∈ (ordCompl[p] f.content).divisors) (w : ℂ) :
    ∑ j ∈ range (f.content.factorization p + 3), (f.lineCount p (j + 1) : ℂ) *
      (w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1))) =
      (p + 1) * ∑ j ∈ range (f.content.factorization p),
        w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) +
      (1 + negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim)) *
        w ^ f.content.factorization p *
          discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 1)) +
      w ^ (f.content.factorization p + 1) *
        discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) := by
  have hp : p.Prime := Fact.out
  have h₁ : ∑ j ∈ range (f.content.factorization p), (f.lineCount p (j + 1) : ℂ) *
      (w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1))) =
      (p + 1) * ∑ j ∈ range (f.content.factorization p),
        w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [lineCount_of_le (Finset.mem_range.mp hj), Nat.cast_add, Nat.cast_one]
  have h₃ : f.lineCount p (f.content.factorization p + 3) = 0 :=
    (lineCount_add hp 3).trans (lineCount_three hp (not_dvd_content_divForm_ordProj hp hf))
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, h₁]
  simp only [Nat.add_assoc]
  rw [h₃, lineCount_add_one_factorization hf, Nat.cast_zero, zero_mul, add_zero]
  linear_combination w ^ (f.content.factorization p + 1) * lineCount_mul_discrCoeff hf h0 hd

/-- **The Hecke operator `T(p)` on the Maass coefficients**: if the coefficients `C(N)` satisfy the
Jacobi relation `C(p²N) + (-N/p) p^{k-1} C(N) + p^{2k-1} C(N/p²) = a_p C(N)` and vanish at the
positive `N ≡ 1, 2 (mod 4)`, then for every binary quadratic form `f`
`p^{2k-1} A(f/p) + p^{k-1} ∑_ℓ A((f ∘ g_ℓ)/p) + A(pf) = (a_p + p^{k-1} + p^k) A(f)` for the Maass
coefficients `A`, a term being `0` where the form is not integral. -/
lemma heckeTp_maassFormCoeff (hJ : ∀ N : ℤ, 0 < N → (N % 4 = 0 ∨ N % 4 = 3) →
      C ((p : ℤ) ^ 2 * N) + negKronecker p N * (p : ℂ) ^ (k - 1) * C N +
        (p : ℂ) ^ (2 * k - 1) * (if (p : ℤ) ^ 2 ∣ N then C (N / (p : ℤ) ^ 2) else 0) = ap * C N)
    (h0 : ∀ N : ℤ, 0 < N → (N % 4 = 1 ∨ N % 4 = 2) → C N = 0) :
    (p : ℂ) ^ (2 * k - 1) * (if p ∣ f.content then maassFormCoeff k C (divForm p f) else 0) +
      (p : ℂ) ^ (k - 1) * ∑ ℓ : Option (Fin p), (if p ∣ (f.lineForm p ℓ).content then
        maassFormCoeff k C (divForm p (f.lineForm p ℓ)) else 0) + maassFormCoeff k C ((p : ℤ) • f) =
      (ap + (p : ℂ) ^ (k - 1) + (p : ℂ) ^ k) * maassFormCoeff k C f := by
  have hp : p.Prime := Fact.out
  have hp₀ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  by_cases hf : 0 < f.a ∧ f.discrim < 0
  · rw [ite_maassFormCoeff_divForm hp hf, sum_ite_maassFormCoeff_divForm_lineForm hp hf,
      maassFormCoeff_smul_eq_sum hp hf, maassFormCoeff_eq_sum_self hp hf]
    refine sum_linear_eq fun d hd ↦ ?_
    rw [sum_range_lineCount_mul hf h0 hd]
    have ht : (p : ℂ) ^ k = p * (p : ℂ) ^ (k - 1) := by
      rw [← zpow_one_add₀ hp₀, add_sub_cancel]
    have hW : (p : ℂ) ^ (2 * k - 1) = (p : ℂ) ^ (k - 1) * (p : ℂ) ^ k := by
      rw [← zpow_add₀ hp₀]
      exact congrArg _ (by ring1)
    have hrel : ∀ j < f.content.factorization p,
        ap * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) =
          discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j) +
            (p : ℂ) ^ (2 * k - 1) * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2)) :=
      fun j hj ↦ (jacobi_discrCoeff hJ hf hd hj.le).trans (by
        rw [negKronecker_neg_discrim_div_eq_zero hd hj, Int.cast_zero, zero_mul, zero_mul,
          add_zero])
    have hrela : ap * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim)
        (d * p ^ (f.content.factorization p + 1)) =
        discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ f.content.factorization p) +
          negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim) *
            (p : ℂ) ^ (k - 1) *
              discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 1)) +
          (p : ℂ) ^ (2 * k - 1) *
            discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) := by
      rw [← negKronecker_neg_discrim_div_factorization hf hd]
      exact jacobi_discrCoeff hJ hf hd le_rfl
    linear_combination (d : ℂ) ^ k * tp_local_identity
      (u := fun j ↦ discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j)) ht hW hrel hrela
  · have h₁ (ℓ : Option (Fin p)) : (if p ∣ (f.lineForm p ℓ).content then
        maassFormCoeff k C (divForm p (f.lineForm p ℓ)) else 0) = 0 :=
      ite_maassFormCoeff_divForm_eq_zero hp.ne_zero fun h ↦
        hf ((posDef_lineForm_iff hp.ne_zero ℓ).mp h)
    have h₂ : maassFormCoeff k C ((p : ℤ) • f) = 0 :=
      maassFormCoeff_eq_zero fun h ↦ hf ((posDef_smul_iff (Int.natCast_pos.mpr hp.pos)).mp h)
    rw [ite_maassFormCoeff_divForm_eq_zero hp.ne_zero hf, Fintype.sum_eq_zero _ h₁, h₂,
      maassFormCoeff_eq_zero hf]
    ring1

/-! ### The Hecke operator `T_1(p²)` -/

lemma t1RootCount_eq : t1RootCount p (f.a, f.b, f.c) = (swapForm f).lineCount p 1 := by
  rw [t1RootCount, Finset.card_filter, Fintype.sum_option, ← Finset.card_filter, lineCount_eq,
    pow_one, ← card_filter_fin]
  congr 1
  · simp [lineVec, swapForm, dvd_content_lineForm_none_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  · congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, dvd_content_lineForm_some_iff,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, lineVec, swapForm]
    push_cast
    simp [pow_two]

lemma divForm_sq_lineForm_none :
    divForm ((p : ℤ) ^ 2) (f.lineForm p none) = ⟨f.a / p ^ 2, f.b / p, f.c⟩ := by
  have hp : (0 : ℤ) < p := Int.natCast_pos.mpr (Fact.out : p.Prime).pos
  ext
  · rfl
  · simp only [divForm, lineForm]
    rw [pow_two, Int.mul_ediv_mul_of_pos _ _ hp]
  · exact Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp.ne')

lemma divForm_sq_lineForm_some (c : Fin p) : divForm ((p : ℤ) ^ 2) (f.lineForm p (some c)) =
    ⟨f.a, (f.b + 2 * c * f.a) / p, (f.c + f.b * c + f.a * c ^ 2) / p ^ 2⟩ := by
  have hp : (0 : ℤ) < p := Int.natCast_pos.mpr (Fact.out : p.Prime).pos
  ext
  · exact Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp.ne')
  · simp only [divForm, lineForm]
    rw [pow_two, Int.mul_ediv_mul_of_pos _ _ hp]
  · rfl

lemma heckeT₁Coeff_eq (κ : ℤ) (A : BinaryQuadraticForm ℤ → ℂ) :
    heckeT₁Coeff p κ (fun T ↦ A ⟨T.1, T.2.1, T.2.2⟩) (f.a, f.b, f.c) =
      (p : ℂ) ^ (3 * κ - 6) * ∑ ℓ : Option (Fin p), (if p ^ 2 ∣ (f.lineForm p ℓ).content then
        A (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)) else 0) +
      (p : ℂ) ^ (2 * κ - 6) * (p * (swapForm f).lineCount p 1 - p - 1) * A f +
      (p : ℂ) ^ (κ - 3) * ∑ ℓ : Option (Fin p), A (f.lineForm p ℓ) := by
  simp only [Fintype.sum_option, pow_two_dvd_content_lineForm_none_iff,
    pow_two_dvd_content_lineForm_some_iff, divForm_sq_lineForm_none, divForm_sq_lineForm_some]
  rw [heckeT₁Coeff, t1RootCount_eq]
  rfl

lemma maassFormCoeff_lineForm (hf : 0 < f.a ∧ f.discrim < 0) (ℓ : Option (Fin p)) :
    maassFormCoeff k C (f.lineForm p ℓ) = ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
      ∑ j ∈ range (f.content.factorization p + 3), if p ^ j ∣ (f.lineForm p ℓ).content then
        ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j) else 0 := by
  have hp : p.Prime := Fact.out
  have he : f.content ≠ 0 := content_ne_zero hf
  have hG : 0 < (f.lineForm p ℓ).a ∧ (f.lineForm p ℓ).discrim < 0 :=
    (posDef_lineForm_iff hp.ne_zero ℓ).mpr hf
  have hoc : ordCompl[p] (f.lineForm p ℓ).content = ordCompl[p] f.content :=
    ordCompl_eq_of_dvd_of_dvd hp (content_dvd_content_lineForm ℓ) (content_lineForm_dvd ℓ)
  have hv : (f.lineForm p ℓ).content.factorization p < f.content.factorization p + 3 := by
    have h₁ : (f.lineForm p ℓ).content.factorization p ≤ (p ^ 2 * f.content).factorization p :=
      (Nat.factorization_le_iff_dvd (content_ne_zero hG)
        (mul_ne_zero (pow_ne_zero 2 hp.ne_zero) he)).mpr (content_lineForm_dvd ℓ) p
    rw [Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) he, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same] at h₁
    omega
  have hd : -(f.lineForm p ℓ).discrim = (p : ℤ) ^ 2 * -f.discrim := by
    rw [discrim_lineForm, mul_neg]
  rw [maassFormCoeff_eq_sum k C hp hG hv, hoc]
  refine Finset.sum_congr rfl fun d hd' ↦ congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  by_cases hj : p ^ j ∣ (f.lineForm p ℓ).content
  · have hd₁ : d ∣ ordCompl[p] f.content := Nat.dvd_of_mem_divisors hd'
    have hcop : Nat.Coprime d (p ^ j) :=
      ((Nat.coprime_ordCompl hp he).symm.coprime_dvd_left hd₁).pow_right j
    have hdvd : d * p ^ j ∣ (f.lineForm p ℓ).content :=
      hcop.mul_dvd_of_dvd_of_dvd (hd₁.trans (hoc ▸ Nat.ordCompl_dvd _ _)) hj
    rw [ite_eq_left hj, ite_eq_left hj, ← hd,
      discrCoeff_of_dvd (dvd_neg.mpr (sq_dvd_discrim_of_dvd_content hdvd))]
  · rw [ite_eq_right hj, ite_eq_right hj]

lemma maassFormCoeff_divForm_sq_lineForm (hf : 0 < f.a ∧ f.discrim < 0) (ℓ : Option (Fin p))
    (hℓ : p ^ 2 ∣ (f.lineForm p ℓ).content) :
    maassFormCoeff k C (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p + 1), if p ^ (j + 2) ∣ (f.lineForm p ℓ).content
          then ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2))
            else 0 := by
  have hp : p.Prime := Fact.out
  have he : f.content ≠ 0 := content_ne_zero hf
  have hX : ((p : ℤ) ^ 2) • divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ) = f.lineForm p ℓ :=
    smul_divForm (by simpa using hℓ)
  have hpX : 0 < (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).a ∧
      (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).discrim < 0 :=
    (posDef_smul_iff (pow_pos (Int.natCast_pos.mpr hp.pos) 2)).mp
      (hX.symm ▸ (posDef_lineForm_iff hp.ne_zero ℓ).mpr hf)
  have hc :
      (f.lineForm p ℓ).content = p ^ 2 * (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).content := by
    conv_lhs => rw [← hX]
    rw [content_smul', Int.natAbs_pow, Int.natAbs_natCast]
  have hcX : (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).content ≠ 0 := content_ne_zero hpX
  have hoc : ordCompl[p] (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).content =
      ordCompl[p] f.content := by
    rw [← Nat.ordCompl_self_pow_mul _ 2 hp, ← hc]
    exact ordCompl_eq_of_dvd_of_dvd hp (content_dvd_content_lineForm ℓ) (content_lineForm_dvd ℓ)
  have hv : (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).content.factorization p <
      f.content.factorization p + 1 := by
    have h₁ : (f.lineForm p ℓ).content.factorization p ≤ (p ^ 2 * f.content).factorization p :=
      (Nat.factorization_le_iff_dvd (by rw [hc]; exact mul_ne_zero (pow_ne_zero 2 hp.ne_zero) hcX)
        (mul_ne_zero (pow_ne_zero 2 hp.ne_zero) he)).mpr (content_lineForm_dvd ℓ) p
    rw [Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) he, hc,
      Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hcX, Finsupp.add_apply, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same] at h₁
    omega
  have hd : -f.discrim = (p : ℤ) ^ 2 * -(divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).discrim := by
    have h₁ : (f.lineForm p ℓ).discrim = p ^ 2 * f.discrim := discrim_lineForm ℓ
    rw [← hX, discrim_smul'] at h₁
    have h₂ : (p : ℤ) ^ 2 * (p ^ 2 * (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).discrim) =
        p ^ 2 * f.discrim := by
      rw [← h₁]
      ring1
    rw [← mul_left_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.ne_zero)) h₂, mul_neg]
  rw [maassFormCoeff_eq_sum k C hp hpX hv, hoc]
  refine Finset.sum_congr rfl fun d hd' ↦ congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  have hiff : p ^ (j + 2) ∣ (f.lineForm p ℓ).content ↔
      p ^ j ∣ (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).content := by
    rw [hc, pow_add, mul_comm (p ^ j), Nat.mul_dvd_mul_iff_left (pow_pos hp.pos 2)]
  by_cases hj : p ^ j ∣ (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).content
  · have hd₁ : d ∣ ordCompl[p] f.content := Nat.dvd_of_mem_divisors hd'
    have hcop : Nat.Coprime d (p ^ j) :=
      ((Nat.coprime_ordCompl hp he).symm.coprime_dvd_left hd₁).pow_right j
    have hdvd : d * p ^ j ∣ (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)).content :=
      hcop.mul_dvd_of_dvd_of_dvd (hd₁.trans (hoc ▸ Nat.ordCompl_dvd _ _)) hj
    have e : d * p ^ (j + 2) = p * (p * (d * p ^ j)) := by ring1
    rw [ite_eq_left hj, ite_eq_left (hiff.mpr hj), e, hd, discrCoeff_mul hp.ne_zero,
      discrCoeff_mul hp.ne_zero,
      discrCoeff_of_dvd (dvd_neg.mpr (sq_dvd_discrim_of_dvd_content hdvd))]
  · rw [ite_eq_right hj, ite_eq_right fun h ↦ hj (hiff.mp h)]

lemma sum_maassFormCoeff_lineForm (hf : 0 < f.a ∧ f.discrim < 0) :
    ∑ ℓ : Option (Fin p), maassFormCoeff k C (f.lineForm p ℓ) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p + 3), (f.lineCount p j : ℂ) *
          (((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j)) := by
  rw [Fintype.sum_congr _ _ (maassFormCoeff_lineForm hf), Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

lemma sum_ite_maassFormCoeff_divForm_sq_lineForm (hf : 0 < f.a ∧ f.discrim < 0) :
    ∑ ℓ : Option (Fin p), (if p ^ 2 ∣ (f.lineForm p ℓ).content then
      maassFormCoeff k C (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)) else 0) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p + 1), (f.lineCount p (j + 2) : ℂ) *
          (((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2))) := by
  have h (ℓ : Option (Fin p)) : (if p ^ 2 ∣ (f.lineForm p ℓ).content then
      maassFormCoeff k C (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)) else 0) =
      ∑ d ∈ (ordCompl[p] f.content).divisors, (d : ℂ) ^ k *
        ∑ j ∈ range (f.content.factorization p + 1), if p ^ (j + 2) ∣ (f.lineForm p ℓ).content
          then ((p : ℂ) ^ k) ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2))
            else 0 := by
    by_cases hℓ : p ^ 2 ∣ (f.lineForm p ℓ).content
    · rw [ite_eq_left hℓ, maassFormCoeff_divForm_sq_lineForm hf ℓ hℓ]
    · rw [ite_eq_right hℓ]
      refine (Finset.sum_eq_zero fun d _ ↦ ?_).symm
      rw [Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦
        hℓ ((pow_dvd_pow p (Nat.le_add_left 2 j)).trans h), mul_zero]
  rw [Fintype.sum_congr _ _ h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

lemma sum_range_lineCount_mul_self (hf : 0 < f.a ∧ f.discrim < 0)
    (h0 : ∀ N : ℤ, 0 < N → (N % 4 = 1 ∨ N % 4 = 2) → C N = 0) {d : ℕ}
    (hd : d ∈ (ordCompl[p] f.content).divisors) (w : ℂ) :
    ∑ j ∈ range (f.content.factorization p + 3), (f.lineCount p j : ℂ) *
      (w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j)) =
      (p + 1) * ∑ j ∈ range (f.content.factorization p + 1),
        w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j) +
      (1 + negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim)) *
        w ^ (f.content.factorization p + 1) *
          discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 1)) +
      w ^ (f.content.factorization p + 2) *
        discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) := by
  have h₁ : ∑ j ∈ range (f.content.factorization p + 1), (f.lineCount p j : ℂ) *
      (w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j)) =
      (p + 1) * ∑ j ∈ range (f.content.factorization p + 1),
        w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [lineCount_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, h₁, lineCount_add_one_factorization hf]
  linear_combination w ^ (f.content.factorization p + 2) * lineCount_mul_discrCoeff hf h0 hd

lemma sum_range_lineCount_add_two_mul_of_eq_zero (hf : 0 < f.a ∧ f.discrim < 0)
    (h0 : ∀ N : ℤ, 0 < N → (N % 4 = 1 ∨ N % 4 = 2) → C N = 0) {d : ℕ}
    (hd : d ∈ (ordCompl[p] f.content).divisors) (w : ℂ) (hv : f.content.factorization p = 0) :
    ∑ j ∈ range (f.content.factorization p + 1), (f.lineCount p (j + 2) : ℂ) *
      (w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2))) =
      discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ 2) := by
  have h : (f.lineCount p (f.content.factorization p + 2) : ℂ) *
      discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) =
      discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) :=
    lineCount_mul_discrCoeff hf h0 hd
  rw [hv, zero_add] at h ⊢
  rw [Finset.sum_range_one, pow_zero, one_mul, zero_add]
  exact h

lemma sum_range_lineCount_add_two_mul_of_eq_succ (hf : 0 < f.a ∧ f.discrim < 0)
    (h0 : ∀ N : ℤ, 0 < N → (N % 4 = 1 ∨ N % 4 = 2) → C N = 0) {d : ℕ}
    (hd : d ∈ (ordCompl[p] f.content).divisors) (w : ℂ) (hv : f.content.factorization p = a + 1) :
    ∑ j ∈ range (f.content.factorization p + 1), (f.lineCount p (j + 2) : ℂ) *
      (w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2))) =
      (p + 1) * ∑ j ∈ range a, w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2)) +
      (1 + negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim)) * w ^ a *
        discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (a + 2)) +
      w ^ (a + 1) * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (a + 3)) := by
  have h₀ : ∑ j ∈ range a, (f.lineCount p (j + 2) : ℂ) *
      (w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2))) =
      (p + 1) * ∑ j ∈ range a,
        w ^ j * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j + 2 ≤ f.content.factorization p := by
      have hj₁ : j < a := Finset.mem_range.mp hj
      omega
    rw [lineCount_of_le hj', Nat.cast_add, Nat.cast_one]
  have h₁ : (f.lineCount p (f.content.factorization p + 1) : ℂ) =
      1 + negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim) :=
    lineCount_add_one_factorization hf
  have h₂ : (f.lineCount p (f.content.factorization p + 2) : ℂ) *
      discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) =
      discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) :=
    lineCount_mul_discrCoeff hf h0 hd
  rw [hv] at h₁ h₂ ⊢
  rw [Finset.sum_range_succ, Finset.sum_range_succ, h₀]
  simp only [Nat.add_assoc] at h₁ h₂ ⊢
  rw [h₁]
  linear_combination w ^ (a + 1) * h₂

lemma lineCount_swapForm_one_of_eq_zero (hf : 0 < f.a ∧ f.discrim < 0)
    (hv : f.content.factorization p = 0) : ((swapForm f).lineCount p 1 : ℂ) =
      1 + negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim) := by
  have hp : p.Prime := Fact.out
  have hpf : ¬p ∣ (swapForm f).content := fun h ↦ by
    rw [content_swapForm] at h
    have h₀ : 0 < f.content.factorization p := hp.factorization_pos_of_dvd (content_ne_zero hf) h
    omega
  have h : ((swapForm f).lineCount p 1 : ℤ) = 1 + negKronecker p (-(swapForm f).discrim) :=
    lineCount_one hpf
  rw [hv, pow_zero, divForm_one, ← discrim_swapForm]
  exact_mod_cast h

/-- **The Hecke operator `T_1(p²)` on the Maass coefficients**: if the coefficients `C(N)` satisfy
the Jacobi relation and vanish at the positive `N ≡ 1, 2 (mod 4)`, then for every binary quadratic
form `f`, `p^{3k-3} ∑_ℓ A((f ∘ g_ℓ)/p²) + p^{2k-4} (p ν - p - 1) A(f) + p^{k-2} ∑_ℓ A(f ∘ g_ℓ)`
is `((p + 1) p^{k-2} a_p + p^{2k-2} - p^{2k-4}) A(f)` for the Maass coefficients `A`, with `ν` the
number of roots of `f` on `P¹(𝔽_p)`. -/
lemma heckeT₁_maassFormCoeff (hJ : ∀ N : ℤ, 0 < N → (N % 4 = 0 ∨ N % 4 = 3) →
      C ((p : ℤ) ^ 2 * N) + negKronecker p N * (p : ℂ) ^ (k - 1) * C N +
        (p : ℂ) ^ (2 * k - 1) * (if (p : ℤ) ^ 2 ∣ N then C (N / (p : ℤ) ^ 2) else 0) = ap * C N)
    (h0 : ∀ N : ℤ, 0 < N → (N % 4 = 1 ∨ N % 4 = 2) → C N = 0) :
    (p : ℂ) ^ (3 * k - 3) * ∑ ℓ : Option (Fin p), (if p ^ 2 ∣ (f.lineForm p ℓ).content then
      maassFormCoeff k C (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)) else 0) +
      (p : ℂ) ^ (2 * k - 4) * (p * (swapForm f).lineCount p 1 - p - 1) * maassFormCoeff k C f +
      (p : ℂ) ^ (k - 2) * ∑ ℓ : Option (Fin p), maassFormCoeff k C (f.lineForm p ℓ) =
      ((p + 1) * (p : ℂ) ^ (k - 2) * ap + (p : ℂ) ^ (2 * k - 2) - (p : ℂ) ^ (2 * k - 4)) *
        maassFormCoeff k C f := by
  have hp : p.Prime := Fact.out
  have hp₀ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  by_cases hf : 0 < f.a ∧ f.discrim < 0
  · have hP : (p : ℂ) ^ (k - 1) = p * (p : ℂ) ^ (k - 2) := by
      rw [← zpow_one_add₀ hp₀]
      exact congrArg _ (by ring1)
    have ht : (p : ℂ) ^ k = p * (p : ℂ) ^ (k - 1) := by
      rw [← zpow_one_add₀ hp₀, add_sub_cancel]
    have hW : (p : ℂ) ^ (2 * k - 1) = (p : ℂ) ^ (k - 1) * (p : ℂ) ^ k := by
      rw [← zpow_add₀ hp₀]
      exact congrArg _ (by ring1)
    have h₃ : (p : ℂ) ^ (3 * k - 3) = (p : ℂ) ^ (2 * k - 1) * (p : ℂ) ^ (k - 2) := by
      rw [← zpow_add₀ hp₀]
      exact congrArg _ (by ring1)
    have h₄ : (p : ℂ) ^ (2 * k - 4) = ((p : ℂ) ^ (k - 2)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul]
      exact congrArg _ (by push_cast; ring1)
    have h₂ : (p : ℂ) ^ (2 * k - 2) = ((p : ℂ) ^ (k - 1)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul]
      exact congrArg _ (by push_cast; ring1)
    rw [sum_ite_maassFormCoeff_divForm_sq_lineForm hf, sum_maassFormCoeff_lineForm hf,
      maassFormCoeff_eq_sum_self hp hf, h₃, h₄, h₂]
    refine sum_linear_eq₃ fun d hd ↦ ?_
    rw [sum_range_lineCount_mul_self hf h0 hd]
    have hrel : ∀ j < f.content.factorization p,
        ap * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 1)) =
          discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j) +
            (p : ℂ) ^ (2 * k - 1) * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (j + 2)) :=
      fun j hj ↦ (jacobi_discrCoeff hJ hf hd hj.le).trans (by
        rw [negKronecker_neg_discrim_div_eq_zero hd hj, Int.cast_zero, zero_mul, zero_mul,
          add_zero])
    have hrela : ap * discrCoeff C ((p : ℤ) ^ 2 * -f.discrim)
        (d * p ^ (f.content.factorization p + 1)) =
        discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ f.content.factorization p) +
          negKronecker p (-(divForm ((p : ℤ) ^ f.content.factorization p) f).discrim) *
            (p : ℂ) ^ (k - 1) *
              discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 1)) +
          (p : ℂ) ^ (2 * k - 1) *
            discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ (f.content.factorization p + 2)) := by
      rw [← negKronecker_neg_discrim_div_factorization hf hd]
      exact jacobi_discrCoeff hJ hf hd le_rfl
    rcases Nat.eq_zero_or_pos (f.content.factorization p) with hv | hv
    · rw [sum_range_lineCount_add_two_mul_of_eq_zero hf h0 hd _ hv,
        lineCount_swapForm_one_of_eq_zero hf hv]
      rw [hv] at hrela ⊢
      simp only [zero_add] at hrela ⊢
      linear_combination (d : ℂ) ^ k * t1_local_identity_zero
        (u := fun j ↦ discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j)) hP ht hW hrela
    · rcases (⟨_, (Nat.succ_pred_eq_of_pos hv).symm⟩ :
        ∃ a, f.content.factorization p = a + 1) with ⟨a, ha⟩
      rw [sum_range_lineCount_add_two_mul_of_eq_succ hf h0 hd _ ha,
        lineCount_swapForm_one_of_pos hv]
      rw [ha] at hrel hrela ⊢
      simp only [Nat.add_assoc] at hrela ⊢
      linear_combination (d : ℂ) ^ k * t1_local_identity_succ
        (u := fun j ↦ discrCoeff C ((p : ℤ) ^ 2 * -f.discrim) (d * p ^ j)) hP ht hW hrel hrela
  · have h₁ (ℓ : Option (Fin p)) : (if p ^ 2 ∣ (f.lineForm p ℓ).content then
        maassFormCoeff k C (divForm ((p : ℤ) ^ 2) (f.lineForm p ℓ)) else 0) = 0 := by
      refine ite_eq_right_iff.mpr fun hℓ ↦ maassFormCoeff_eq_zero fun h ↦ hf ?_
      rw [← posDef_lineForm_iff hp.ne_zero ℓ,
        ← smul_divForm (f := f.lineForm p ℓ) (m := (p : ℤ) ^ 2) (by simpa using hℓ)]
      exact (posDef_smul_iff (pow_pos (Int.natCast_pos.mpr hp.pos) 2)).mpr h
    have h₂ (ℓ : Option (Fin p)) : maassFormCoeff k C (f.lineForm p ℓ) = 0 :=
      maassFormCoeff_eq_zero fun h ↦ hf ((posDef_lineForm_iff hp.ne_zero ℓ).mp h)
    rw [Fintype.sum_eq_zero _ h₁, Fintype.sum_eq_zero _ h₂, maassFormCoeff_eq_zero hf]
    ring1

end SiegelUpperHalfSpace
