import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.IndexRaising
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeFourier
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftEisenstein

/-!
# The theorem of Maass from the index raising operators

The Fourier–Jacobi coefficient `φ_m(τ, z) = ∑_{n, r} a(n, r, m) e^{2πi(nτ + rz)}` of index
`m ≥ 1` of the Maass lift of `φ ∈ J_{k,1}` (`SiegelUpperHalfSpace.maassFourierJacobi`, LMFDB
`mf.siegel.lift.maass`) is the image `φ ∣ V_m` of `φ` under the index raising operator of Eichler
and Zagier (`ModularForm.indexRaising`), `(φ ∣ V_m)(τ, z) = m⁻¹ ∑ a^k φ((aτ + b)/d, az)` over
`ad = m`, `0 ≤ b < d`. Expanding each `φ((aτ + b)/d, az) = ∑ c(n, r) e^{2πi(n(aτ + b)/d + raz)}`,
the sum over `b` keeps the frequencies `n` divisible by `d` (with the factor `d`), and the
substitution `(N, R) = (an/d, ar)` turns the term of `(a, d)` into
`a^{k-1} c(Nd/a, R/a) e^{2πi(Nτ + Rz)}` for `a ∣ N`, `a ∣ R`; summed over the divisors `a` of `m`,
this is the coefficient `∑_{a ∣ (N, R, m)} a^{k-1} c(Nm/a², R/a)` of the lift. As `φ ∣ V_m`
transforms like a Jacobi form of index `m` under `(0, -1; 1, 0)` (`ModularForm.indexRaising_S`),
the theorem of Maass reduces to the absolute convergence of the series of the lift and its
holomorphy, in weight `k ≥ 3`.

## Main results

* `SiegelUpperHalfSpace.maassCoeff_eq_liftDivisorSum`: for `m ≥ 1`, the coefficient `a(n, r, m)`
  is the divisor sum `∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` for all `n`.
* `SiegelUpperHalfSpace.maassFourierJacobi_eq_indexRaising`: `φ_m = φ ∣ V_m` for `m ≥ 1`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_summable_of_isHolomorphic`: for
  `φ ∈ J_{k,1}` with `k ≥ 3`, the Maass lift is a Siegel modular form of weight `k` on `Sp(4, ℤ)`
  if its series converges absolutely and it is holomorphic.
-/

open Complex ModularForm ModularGroup Real SymplecticGroup

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℕ} {φ : ℍ × ℂ → ℂ} {m a : ℕ} (x : ℍ × ℂ)

private lemma sum_cosetReps (hm : 0 < m) (f : ℕ × ℕ × ℕ → ℂ) :
    ∑ t ∈ cosetReps m, f t = ∑ a ∈ m.divisors, ∑ b ∈ Finset.range (m / a), f (a, b, m / a) := by
  rw [Finset.sum_finset_product (cosetReps m) m.divisors
    (fun a ↦ Finset.range (m / a) ×ˢ {m / a}) fun t ↦ ?_]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_product, Finset.sum_congr rfl fun b _ ↦ Finset.sum_singleton _ _]
  · rw [mem_cosetReps hm, Nat.mem_divisors, Finset.mem_product, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      have ha : 0 < t.1 := Nat.pos_of_ne_zero fun h ↦ hm.ne <| by rw [← h1, h, zero_mul]
      have hd : t.2.2 = m / t.1 := by
        rw [← h1, Nat.mul_div_cancel_left _ ha]
      exact ⟨⟨⟨t.2.2, h1.symm⟩, hm.ne'⟩, hd ▸ h2, hd⟩
    · rintro ⟨⟨h1, -⟩, h2, h3⟩
      exact ⟨by rw [h3, Nat.mul_div_cancel' h1], h3 ▸ h2⟩

private lemma hasSum_coset (hφ : φ ∈ jacobiFormSpace k 1) (ha : a ∈ m.divisors) :
    HasSum (fun q : ℤ × ℤ ↦ if ((m / a : ℕ) : ℤ) ∣ q.1 then (a : ℂ) ^ ((k : ℤ) - 1) *
      jacobiCoeff φ q * cexp (2 * π * I * (q.1 * a * x.1 / (m / a : ℕ) + q.2 * a * x.2)) else 0)
      ((m : ℂ)⁻¹ * ∑ b ∈ Finset.range (m / a),
        (a : ℂ) ^ (k : ℤ) * φ (affinePoint a b (m / a : ℕ) x.1, a * x.2)) := by
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
  have hd0 : 0 < m / a := Nat.div_pos (Nat.divisor_le ha) ha0
  have hmad : (m : ℂ) = a * (m / a : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)).symm
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hd' : ((m / a : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hc : HasJacobiFourierExpansion φ (jacobiCoeff φ) :=
    hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ
  rw [← Finset.mul_sum, ← mul_assoc]
  refine ((hasSum_sum (s := Finset.range (m / a)) fun (b : ℕ) _ ↦
    hc (affinePoint a b (m / a : ℕ) x.1, a * x.2)).mul_left
      ((m : ℂ)⁻¹ * (a : ℂ) ^ (k : ℤ))).congr_fun fun q ↦ ?_
  have hexp (b : ℕ) : jacobiFourierExp q (affinePoint a b (m / a : ℕ) x.1, a * x.2) =
      cexp (2 * π * I * (q.1 * a * x.1 / (m / a : ℕ) + q.2 * a * x.2)) *
        cexp (2 * π * I * q.1 * b / (m / a : ℕ)) := by
    rw [jacobiFourierExp, coe_affinePoint _ _ (by exact_mod_cast ha0) (by exact_mod_cast hd0),
      ← Complex.exp_add]
    congr 1
    simp only [Int.cast_natCast]
    field_simp
    ring1
  simp only [hexp, ← Finset.mul_sum, UpperHalfPlane.sum_range_exp_two_pi_I_mul_div hd0.ne']
  split_ifs with h
  · rw [hmad, zpow_sub_one₀ ha']
    field_simp
  · simp

private lemma hasSum_coset_reindex (hφ : φ ∈ jacobiFormSpace k 1) (ha : a ∈ m.divisors) :
    HasSum (fun q : ℤ × ℤ ↦ if (a : ℤ) ∣ q.1 ∧ (a : ℤ) ∣ q.2 then (a : ℂ) ^ ((k : ℤ) - 1) *
      jacobiCoeff φ (q.1 / a * (m / a : ℕ), q.2 / a) * jacobiFourierExp q x else 0)
      ((m : ℂ)⁻¹ * ∑ b ∈ Finset.range (m / a),
        (a : ℂ) ^ (k : ℤ) * φ (affinePoint a b (m / a : ℕ) x.1, a * x.2)) := by
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
  have hd0 : 0 < m / a := Nat.div_pos (Nat.divisor_le ha) ha0
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hd' : ((m / a : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hι : Function.Injective fun p : ℤ × ℤ ↦ (((m / a : ℕ) : ℤ) * p.1, p.2) := fun p p' h ↦
    Prod.ext (mul_left_cancel₀ hd' (Prod.ext_iff.mp h).1) (Prod.ext_iff.mp h).2
  have hκ : Function.Injective fun p : ℤ × ℤ ↦ ((a : ℤ) * p.1, (a : ℤ) * p.2) := fun p p' h ↦
    Prod.ext (mul_left_cancel₀ ha' (Prod.ext_iff.mp h).1)
      (mul_left_cancel₀ ha' (Prod.ext_iff.mp h).2)
  refine (hκ.hasSum_iff fun q hq ↦ ite_eq_right fun h ↦ hq ?_).mp
    (((hι.hasSum_iff fun q hq ↦ ite_eq_right fun h ↦ hq ?_).mpr (hasSum_coset x hφ ha)).congr_fun
      fun p ↦ ?_)
  · rcases h with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨(u, v), Prod.ext hu.symm hv.symm⟩
  · rcases h with ⟨u, hu⟩
    exact ⟨(u, q.2), Prod.ext hu.symm rfl⟩
  · simp only [Function.comp_apply]
    rw [ite_eq_left ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, ite_eq_left (dvd_mul_right _ _),
      Int.mul_ediv_cancel_left _ ha', Int.mul_ediv_cancel_left _ ha', mul_comm p.1,
      jacobiFourierExp]
    congr 2
    have hdC : ((m / a : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    simp only [Int.cast_mul, Int.cast_natCast]
    field_simp

/-- **The Fourier coefficients of the Fourier–Jacobi coefficients of index `m ≥ 1` of the Maass
lift**: for `φ ∈ J_{k,1}` and `m ≥ 1`, `a(n, r, m) = ∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)` for
all `n, r`, also for `n < 0`, where both sides vanish. -/
lemma maassCoeff_eq_liftDivisorSum (hφ : φ ∈ jacobiFormSpace k 1) (hm : 0 < m) (n r : ℤ) :
    maassCoeff k (jacobiCoeff φ) n r m = liftDivisorSum k (jacobiCoeff φ) n r m := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  rw [maassCoeff, ite_eq_right fun h ↦ hm'.ne' h.2.2]
  split_ifs with h
  · rfl
  · have hn : n < 0 := by
      by_contra hn
      exact h ⟨not_lt.mp hn, hm'.le⟩
    exact (liftDivisorSum_eq_zero n r m hφ (by nlinarith [sq_nonneg r])).symm

private lemma sum_divisors_coeff (hφ : φ ∈ jacobiFormSpace k 1) (hm : 0 < m) (q : ℤ × ℤ) :
    ∑ a ∈ m.divisors, (if (a : ℤ) ∣ q.1 ∧ (a : ℤ) ∣ q.2 then (a : ℂ) ^ ((k : ℤ) - 1) *
      jacobiCoeff φ (q.1 / a * (m / a : ℕ), q.2 / a) * jacobiFourierExp q x else 0) =
        maassCoeff k (jacobiCoeff φ) q.1 q.2 m * jacobiFourierExp q x := by
  have hm0 : m ≠ 0 := hm.ne'
  have hfilter : m.divisors.filter (fun a : ℕ ↦ (a : ℤ) ∣ q.1 ∧ (a : ℤ) ∣ q.2) =
      ((q.1.gcd q.2 : ℤ).gcd m).divisors := by
    ext a
    simp only [Finset.mem_filter, Nat.mem_divisors, Int.dvd_gcd_iff, Int.natCast_dvd_natCast,
      ne_eq, Int.gcd_eq_zero_iff, Nat.cast_eq_zero]
    tauto
  rw [← Finset.sum_filter, hfilter, maassCoeff_eq_liftDivisorSum hφ hm, liftDivisorSum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have hg : (a : ℤ) ∣ ((q.1.gcd q.2 : ℤ).gcd m : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_divisors ha)
  have ha0 : (a : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors ha).ne'
  have h1 : q.1 / a * ((m / a : ℕ) : ℤ) = q.1 * m / (a : ℤ) ^ 2 := by
    rcases (hg.trans (Int.gcd_dvd_left _ _)).trans (Int.gcd_dvd_left _ _) with ⟨u, hu⟩
    rcases hg.trans (Int.gcd_dvd_right _ _) with ⟨w, hw⟩
    have h2 : (a : ℤ) * u * ((a : ℤ) * w) = (a : ℤ) ^ 2 * (u * w) := by
      ring1
    rw [Int.natCast_div, hu, hw, Int.mul_ediv_cancel_left _ ha0, Int.mul_ediv_cancel_left _ ha0, h2,
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 ha0)]
  rw [h1]

/-- **The Fourier–Jacobi coefficients of the Maass lift are the images of `φ` under the index
raising operators**: for `φ ∈ J_{k,1}` and `m ≥ 1`, `φ_m = φ ∣ V_m`, where
`φ_m(τ, z) = ∑_{n, r} a(n, r, m) e^{2πi(nτ + rz)}` is defined by the Fourier coefficients of the
lift and `(φ ∣ V_m)(τ, z) = m⁻¹ ∑ a^k φ((aτ + b)/d, az)` by the cosets of the matrices of
determinant `m` (Eichler and Zagier, Theorem 4.2). In particular the series of `φ_m` converges. -/
lemma maassFourierJacobi_eq_indexRaising (hφ : φ ∈ jacobiFormSpace k 1) (hm : 0 < m) :
    maassFourierJacobi k φ m = indexRaising k φ m := by
  funext x
  refine ((hasSum_sum fun a ha ↦ hasSum_coset_reindex x hφ ha).congr_fun fun q ↦
    (sum_divisors_coeff x hφ hm q).symm).tsum_eq.trans ?_
  rw [indexRaising, sum_cosetReps hm, Finset.mul_sum]
  rfl

/-- **The theorem of Maass, reduced to convergence and holomorphy** (LMFDB `mf.siegel.lift.maass`):
for a Jacobi form `φ ∈ J_{k,1}` of weight `k ≥ 3`, if the series of the Maass lift converges
absolutely on `ℋ₂` and the lift is holomorphic, then the Maass lift is a Siegel modular form of
weight `k` on `Sp(4, ℤ)`. Its Fourier–Jacobi coefficients `φ_m = φ ∣ V_m` transform like Jacobi
forms of index `m` under `(0, -1; 1, 0)`, which gives the law under the partial inversion `J₁`, and
the law under the Siegel parabolic subgroup holds without convergence. -/
lemma maassLift_mem_scalarModularForms_of_summable_of_isHolomorphic
    (hφ : φ ∈ jacobiFormSpace k 1) (hk : 3 ≤ k) (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2),
      Summable fun p : ℤ × ℤ × ℤ ↦
        maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hF : IsHolomorphic (maassLift k φ)) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) :=
  maassLift_mem_scalarModularForms_of_summable_of_three_le hφ hk hs hF fun _ hm x ↦ by
    rw [maassFourierJacobi_eq_indexRaising hφ hm, indexRaising_S x hφ.2.1 hm]

end SiegelUpperHalfSpace
