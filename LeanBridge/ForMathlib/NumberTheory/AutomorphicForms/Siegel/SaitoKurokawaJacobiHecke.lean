import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SaitoKurokawaLift
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraHecke
import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Eigenvector
import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# The Hecke relation of the Jacobi form of a Saito–Kurokawa lift

Let `φ ∈ J_{k+1,1}` have coefficients `c(N)` by discriminant whose Kohnen `D`-th Shimura lifts
are `c(|D|) f` for every fundamental discriminant `D < 0`, `f ∈ S_{2k}(SL(2, ℤ))` a normalised
Hecke eigenform, as in `SiegelUpperHalfSpace.IsSaitoKurokawaLift`. Then the coefficients satisfy
the Hecke relation of index `1` of Eichler and Zagier (Theorem 4.5): for every prime `p` and every
discriminant `N > 0`, `N ≡ 0, 3 (mod 4)`,
`c(p²N) + (-N/p) p^{k-1} c(N) + p^{2k-1} c(N/p²) = a_p(f) c(N)`,
where `(-N/p)` is the Kronecker symbol (`ModularForm.negKronecker`) and `c(N/p²) = 0` unless
`p² ∣ N`. Writing `N = |D| f²` with `D` fundamental, `g(n) = c(|D| n²)` satisfies
`∑_{d ∣ n} χ_D(d) d^{k-1} g(n/d) = c(|D|) a_n(f)`; convolving the relation with
`χ_D(d) d^{k-1}`, which is invertible, turns it into the Hecke relation
`a(pn) + p^{2k-1} a(n/p) = a_p a(n)` of `f`. The relation was checked numerically on
`φ_{10,1}` (`k = 9`, `f = Δ E₆`) at `p = 2, 3, 5, 7` and `N < 200`. At `p = 2` it fails for
`N ≡ 1, 2 (mod 4)`, where `c(N) = 0` but `c(4N)` need not vanish (`c(4) = -2` for `φ_{10,1}`).

The Kronecker symbol `(-N/p)` is defined here (`ModularForm.negKronecker`) because the pinned Tau
Ceti has none; Tau Ceti's main has it as `TauCeti.kroneckerSym (-N) p` (`kroneckerSym_two_right`,
`kroneckerSym_eq_legendreSym`), which should replace it after the bump.

## Main definitions

* `ModularForm.negKronecker`: the Kronecker symbol `(-N/p)` at a prime `p`.

## Main results

* `ModularForm.sum_divisors_mul_hecke_eq_zero`: a Hecke operator through a Dirichlet convolution.
* `ModularForm.jacobiDiscrCoeff_hecke`: the Hecke relation of the coefficients by discriminant.
-/

open TauCeti Multiquadratic UpperHalfPlane HeckeRing GL2 LSeries

namespace ModularForm

variable {p n : ℕ} {h g a : ℕ → ℂ} {c₀ w : ℂ}

/-! ### Dirichlet convolution and Hecke operators -/

/-- **A Hecke operator through a Dirichlet convolution**: if `∑_{d ∣ n} h(d) g(n/d) = c₀ a(n)` for
every `n ≥ 1`, with `h` completely multiplicative, and `a` is an eigenvector of the Hecke operator
`a ↦ a(p ·) + w a(· / p)` at the prime `p`, then the convolution of `h` with
`E(m) = g(pm) + [p ∤ m] h(p) g(m) + [p ∣ m] w g(m/p) - a(p) g(m)` vanishes. The action of the
Hecke operator on the convolution is `LSeries.convolution_hecke`. -/
lemma sum_divisors_mul_hecke_eq_zero (hp : p.Prime) (hh : ∀ m n, h (m * n) = h m * h n)
    (hK : ∀ n, 0 < n → ∑ d ∈ n.divisors, h d * g (n / d) = c₀ * a n)
    (ha : ∀ m, 0 < m → a (p * m) = a p * a m - if p ∣ m then w * a (m / p) else 0) (hn : 0 < n) :
    ∑ d ∈ n.divisors, h d * (g (p * (n / d)) + (if p ∣ n / d then 0 else h p * g (n / d)) +
      (if p ∣ n / d then w * g (n / d / p) else 0) - a p * g (n / d)) = 0 := by
  have hc (G : ℕ → ℂ) (m : ℕ) : convolution h G m = ∑ d ∈ m.divisors, h d * G (m / d) := by
    rw [convolution_def]
    exact Nat.sum_divisorsAntidiagonal fun x y ↦ h x * G y
  have hK' (m : ℕ) (hm : 0 < m) : convolution h g m = c₀ * a m := (hc g m).trans (hK m hm)
  have e : ∑ d ∈ n.divisors, h d * (g (p * (n / d)) + (if p ∣ n / d then 0 else h p * g (n / d)) +
      (if p ∣ n / d then w * g (n / d / p) else 0) - a p * g (n / d)) =
      convolution h (fun m ↦ g (p * m) + h p * (if p ∣ m then 0 else g m) +
        w * if p ∣ m then g (m / p) else 0) n - a p * convolution h g n := by
    rw [hc, hc, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    split_ifs <;> ring1
  rw [e, convolution_hecke hp (fun d _ ↦ hh p d) w hn.ne', hK' _ (Nat.mul_pos hp.pos hn),
    hK' n hn, ha n hn]
  split_ifs with hpn
  · rw [hK' _ (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)]
    ring1
  · ring1

lemma eq_zero_of_sum_divisors_mul_eq_zero (hh : h 1 = 1) {E : ℕ → ℂ}
    (hE : ∀ n, 0 < n → ∑ d ∈ n.divisors, h d * E (n / d) = 0) {m : ℕ} (hm : 0 < m) : E m = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have e : ∑ d ∈ m.divisors, h d * E (m / d) = ∑ e ∈ m.divisors, h (m / e) * E e := by
      rw [← Nat.sum_div_divisors m (fun e ↦ h (m / e) * E e)]
      exact Finset.sum_congr rfl fun d hd ↦ by rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd)
        hm.ne']
    have h₀ : ∑ d ∈ m.divisors, h d * E (m / d) = 0 := hE m hm
    rw [e, ← Nat.insert_self_properDivisors hm.ne',
      Finset.sum_insert Nat.self_notMem_properDivisors, Nat.div_self hm, hh, one_mul,
      Finset.sum_eq_zero fun e he ↦ ?_, add_zero] at h₀
    · exact h₀
    · rw [Nat.mem_properDivisors] at he
      rw [ih e he.2 (Nat.pos_of_dvd_of_pos he.1 hm), mul_zero]

/-! ### The Kronecker symbol `(-N/p)` -/

variable (p) in
/-- The **Kronecker symbol** `(-N/p)` at a prime `p`: the Legendre symbol `(-N/p)` for odd `p`,
and `χ₈(N)` for `p = 2`, that is `0` for even `N`, `1` for `N ≡ ±1 (mod 8)` and `-1` for
`N ≡ ±3 (mod 8)`. For `-N = D f²` with `D` a fundamental discriminant it is `χ_D(p)` if `p ∤ f`
and `0` if `p ∣ f` (`ModularForm.negKronecker_natAbs_mul_sq`); `1 + (-N/p)` is the number of
roots modulo `p` of a binary quadratic form of discriminant `-N` primitive at `p`. -/
def negKronecker [Fact p.Prime] (N : ℤ) : ℤ :=
  if p = 2 then ZMod.χ₈ (N : ZMod 8) else legendreSym p (-N)

lemma fundamentalDiscriminantChar_two {D : ℤ} (hD : D.IsFundamentalDiscr) :
    fundamentalDiscriminantChar D hD ((2 : ℕ) : ZMod D.natAbs) = ZMod.χ₈ (D : ZMod 8) := by
  rcases hD.exists_finset_primeDiscriminant with ⟨s, hs, -, hprod⟩
  have h₂ : fundamentalDiscriminantChar D hD (((2 : ℕ) : ℤ) : ZMod D.natAbs) =
      genusCharFun s ((2 : ℕ) : ℤ) :=
    fundamentalDiscriminantChar_apply_int hD hs hprod _
  rw [Int.cast_natCast] at h₂
  rw [h₂, genusCharFun_def, ← hprod, Int.cast_prod, map_prod]
  exact Finset.prod_congr rfl fun P hP ↦ primeDiscriminantCharFun_two (hs P hP)

variable [Fact p.Prime]

lemma negKronecker_natAbs_mul_sq {D : ℤ} (hD : D.IsFundamentalDiscr) (hD₀ : D < 0) (f : ℕ) :
    negKronecker p ((D.natAbs * f ^ 2 : ℕ) : ℤ) =
      fundamentalDiscriminantChar D hD (p : ZMod D.natAbs) * if p ∣ f then 0 else 1 := by
  have hp : p.Prime := Fact.out
  have habs : (D.natAbs : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hD₀.le
  rw [negKronecker]
  split_ifs with h₂ hpf hpf
  · subst h₂
    rw [mul_zero, Int.cast_natCast, ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_left (by
      rcases hpf with ⟨f', rfl⟩
      have e : (2 * f') ^ 2 = 2 * (2 * f' ^ 2) := by ring1
      rw [Nat.mul_mod, e, Nat.mul_mod_right]
      simp)]
  · subst h₂
    rw [mul_one, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
    have hf : ZMod.χ₈ (f : ZMod 8) ^ 2 = 1 := by
      rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega)]
      split_ifs <;> norm_num
    have h₁ : ZMod.χ₈ (-1) = 1 := by
      decide
    rw [hf, mul_one, fundamentalDiscriminantChar_two hD, ← Int.cast_natCast, habs, Int.cast_neg,
      ← neg_one_mul, map_mul, h₁, one_mul]
  · rw [mul_zero, legendreSym.eq_zero_iff]
    rcases hpf with ⟨f', rfl⟩
    push_cast
    rw [ZMod.natCast_self]
    ring1
  · have hχ : fundamentalDiscriminantChar D hD (p : ZMod D.natAbs) = legendreSym p D := by
      rw [← Int.cast_natCast]
      exact fundamentalDiscriminantChar_natCast_eq_legendreSym hD h₂
    rw [mul_one, hχ]
    have e : -(((D.natAbs * f ^ 2 : ℕ) : ℤ)) = D * (f : ℤ) ^ 2 := by
      push_cast
      rw [abs_of_neg hD₀]
      ring1
    rw [e, legendreSym.mul, legendreSym.sq_one' p (by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact hpf), mul_one]

lemma negKronecker_eq_zero_of_dvd {N : ℤ} (h : (p : ℤ) ∣ N) : negKronecker p N = 0 := by
  rw [negKronecker]
  split_ifs with hp2
  · subst hp2
    rw [ZMod.χ₈_int_eq_if_mod_eight, ite_eq_left (by push_cast at h; omega)]
  · rw [legendreSym.eq_zero_iff, Int.cast_neg, neg_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h

lemma negKronecker_mul_sq (N : ℤ) {d : ℕ} (hd : ¬p ∣ d) :
    negKronecker p (N * d ^ 2) = negKronecker p N := by
  rw [negKronecker, negKronecker]
  split_ifs with hp2
  · subst hp2
    have h₁ : ZMod.χ₈ (d : ZMod 8) ^ 2 = 1 := by
      rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega)]
      split_ifs <;> norm_num
    push_cast
    rw [map_mul, map_pow, h₁, mul_one]
  · rw [neg_mul_eq_neg_mul, legendreSym.mul, legendreSym.sq_one' p (by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact hd), mul_one]

lemma exists_isFundamentalDiscr_mul_sq (Δ : ℤ) (hΔ : Δ ≠ 0) (h4 : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    ∃ D : ℤ, ∃ f : ℕ, D.IsFundamentalDiscr ∧ 0 < f ∧ Δ = D * f ^ 2 := by
  by_cases hD : Δ.IsFundamentalDiscr
  · exact ⟨Δ, 1, hD, one_pos, by ring1⟩
  · rw [Int.isFundamentalDiscr_iff_forall_prime] at hD
    push Not at hD
    rcases hD h4 with ⟨q, hq, e, rfl, he⟩
    have he₀ : e ≠ 0 := right_ne_zero_of_mul hΔ
    have hlt : e.natAbs < ((q : ℤ) ^ 2 * e).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      exact lt_mul_left (Int.natAbs_pos.mpr he₀) (Nat.one_lt_pow two_ne_zero hq.one_lt)
    rcases exists_isFundamentalDiscr_mul_sq e he₀ he with ⟨D, f, hD', hf, rfl⟩
    exact ⟨D, q * f, hD', Nat.mul_pos hq.pos hf, by push_cast; ring1⟩
termination_by Δ.natAbs

/-! ### The Hecke relation -/

variable {k : ℤ} {f : Newform 1 (2 * k)} {φ : ℍ × ℂ → ℂ}

lemma jacobiDiscrCoeff_eq_zero_of_emod_four {N : ℕ} (h : N % 4 = 1 ∨ N % 4 = 2) :
    jacobiDiscrCoeff φ N = 0 := by
  rw [jacobiDiscrCoeff, ite_eq_right (by omega), ite_eq_right (by omega)]

variable (f) in
lemma qExpansion_coeff_prime_mul (m : ℕ) : (qExpansion 1 f.toCuspForm).coeff (p * m) =
    (qExpansion 1 f.toCuspForm).coeff p * (qExpansion 1 f.toCuspForm).coeff m -
      if p ∣ m then (p : ℂ) ^ (2 * k - 1) * (qExpansion 1 f.toCuspForm).coeff (m / p) else 0 := by
  rw [(heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom (Fact.out : p.Prime)
    f.mem_charSpace _).mp (f.heckeTCuspNat_eq_qExpansion_coeff_smul Fact.out) m,
    Subsingleton.elim (p : ZMod 1) 1, map_one, one_mul]

/-- **The Hecke relation of the coefficients of a Saito–Kurokawa Jacobi form**: if the Kohnen
`D`-th Shimura lifts of `φ` are `c(|D|) f` for every fundamental discriminant `D < 0`, then for
every prime `p` and every `N > 0`, `N ≡ 0, 3 (mod 4)`,
`c(p²N) + (-N/p) p^{k-1} c(N) + p^{2k-1} c(N/p²) = a_p(f) c(N)`, the term `c(N/p²)` being `0`
unless `p² ∣ N` (Eichler and Zagier, Theorem 4.5, in index `1`). -/
lemma jacobiDiscrCoeff_hecke (hK : ∀ (D : ℤ) (hD : D.IsFundamentalDiscr), D < 0 →
    ∀ n : ℕ, 0 < n → jacobiShimuraCoeff k φ D hD n =
      jacobiDiscrCoeff φ D.natAbs * (qExpansion 1 f.toCuspForm).coeff n) {N : ℕ} (hN : 0 < N)
    (h4 : N % 4 = 0 ∨ N % 4 = 3) : jacobiDiscrCoeff φ (p ^ 2 * N) +
      negKronecker p N * (p : ℂ) ^ (k - 1) * jacobiDiscrCoeff φ N +
        (p : ℂ) ^ (2 * k - 1) * (if p ^ 2 ∣ N then jacobiDiscrCoeff φ (N / p ^ 2) else 0) =
      (qExpansion 1 f.toCuspForm).coeff p * jacobiDiscrCoeff φ N := by
  have hp : p.Prime := Fact.out
  rcases exists_isFundamentalDiscr_mul_sq (-N) (by omega) (by omega) with ⟨D, f', hD, hf', hDf⟩
  have hD₀ : D < 0 := by
    by_contra h
    have h₁ : (0 : ℤ) ≤ D * (f' : ℤ) ^ 2 := mul_nonneg (not_lt.mp h) (sq_nonneg _)
    omega
  have hN' : N = D.natAbs * f' ^ 2 := by
    zify
    rw [abs_of_neg hD₀]
    linarith
  let h : ℕ → ℂ := fun d ↦
    (fundamentalDiscriminantChar D hD (d : ZMod D.natAbs) : ℂ) * (d : ℂ) ^ (k - 1)
  let g : ℕ → ℂ := fun n ↦ jacobiDiscrCoeff φ (D.natAbs * n ^ 2)
  have hh (m n : ℕ) : h (m * n) = h m * h n := by
    simp only [h, Nat.cast_mul, map_mul, Int.cast_mul, mul_zpow]
    ring1
  have hh₁ : h 1 = 1 := by
    simp [h]
  have hE : g (p * f') + (if p ∣ f' then 0 else h p * g f') +
      (if p ∣ f' then (p : ℂ) ^ (2 * k - 1) * g (f' / p) else 0) -
        (qExpansion 1 f.toCuspForm).coeff p * g f' = 0 :=
    eq_zero_of_sum_divisors_mul_eq_zero (E := fun m ↦ g (p * m) +
      (if p ∣ m then 0 else h p * g m) + (if p ∣ m then (p : ℂ) ^ (2 * k - 1) * g (m / p) else 0) -
        (qExpansion 1 f.toCuspForm).coeff p * g m) hh₁ (fun n hn ↦
      sum_divisors_mul_hecke_eq_zero (g := g) (a := fun n ↦ (qExpansion 1 f.toCuspForm).coeff n)
        (c₀ := jacobiDiscrCoeff φ D.natAbs) hp hh (fun n hn ↦ by rw [← hK D hD hD₀ n hn]; rfl)
          (fun m _ ↦ qExpansion_coeff_prime_mul f m) hn) hf'
  have hκ : (negKronecker p N : ℂ) = (fundamentalDiscriminantChar D hD (p : ZMod D.natAbs) : ℂ) *
      if p ∣ f' then 0 else 1 := by
    rw [hN', negKronecker_natAbs_mul_sq hD hD₀ f']
    push_cast
    rfl
  have hg : g (p * f') = jacobiDiscrCoeff φ (p ^ 2 * N) := by
    simp only [g, hN']
    congr 1
    ring1
  have hg' : g f' = jacobiDiscrCoeff φ N := by
    simp only [g, hN']
  have hdiv : (if p ∣ f' then (p : ℂ) ^ (2 * k - 1) * g (f' / p) else 0) =
      (p : ℂ) ^ (2 * k - 1) * (if p ^ 2 ∣ N then jacobiDiscrCoeff φ (N / p ^ 2) else 0) := by
    by_cases hpf : p ∣ f'
    · rcases hpf with ⟨f₁, rfl⟩
      have e : N = p ^ 2 * (D.natAbs * f₁ ^ 2) := by
        rw [hN']
        ring1
      rw [ite_eq_left (dvd_mul_right p f₁), ite_eq_left ⟨D.natAbs * f₁ ^ 2, e⟩,
        Nat.mul_div_cancel_left _ hp.pos, e, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
    · rw [ite_eq_right hpf]
      split_ifs with hp2
      · rw [jacobiDiscrCoeff_eq_zero_of_emod_four, mul_zero]
        have hcop : Nat.Coprime (p ^ 2) (f' ^ 2) := (hp.coprime_iff_not_dvd.mpr hpf).pow 2 2
        have hpD : p ^ 2 ∣ D.natAbs := hcop.dvd_of_dvd_mul_right (hN' ▸ hp2)
        have hp₂ : p = 2 := by
          rcases hp.eq_two_or_odd' with h₂ | h₂
          · exact h₂
          · exact absurd (Int.ofNat_dvd_left.mpr (by exact_mod_cast hpD)) (hD.2.2 p hp h₂)
        subst hp₂
        have h4D : (4 : ℤ) ∣ D := Int.ofNat_dvd_left.mpr (by simpa using hpD)
        have hx : ¬4 ∣ D / 4 ∧ D / 4 % 4 ≠ 1 := hD.2.1 (D / 4) (Int.mul_ediv_cancel' h4D).symm
        have hxabs : ((D / 4).natAbs : ℤ) = -(D / 4) := Int.ofNat_natAbs_of_nonpos (by omega)
        have hx4 : (D / 4).natAbs % 4 = 1 ∨ (D / 4).natAbs % 4 = 2 := by
          omega
        have hDabs : D.natAbs = 4 * (D / 4).natAbs := by
          have e : D.natAbs = (4 * (D / 4)).natAbs := by
            rw [Int.mul_ediv_cancel' h4D]
          rw [e, Int.natAbs_mul]
          rfl
        have hf₂ : f' ^ 2 % 4 = 1 := by
          rcases Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hpf) with ⟨t, rfl⟩
          have e : (2 * t + 1) ^ 2 = 4 * (t ^ 2 + t) + 1 := by ring1
          rw [e, Nat.mul_add_mod]
        simp only [Nat.reducePow]
        rw [hN', hDabs, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_mod, hf₂,
          mul_one, Nat.mod_mod]
        exact hx4
      · rw [mul_zero]
  rw [hg, hg', hdiv] at hE
  rw [hκ]
  simp only [h] at hE
  split_ifs at hE ⊢ <;> linear_combination hE

end ModularForm
