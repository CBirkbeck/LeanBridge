import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.BaseChange
import Mathlib.RingTheory.Ideal.Int

/-!
# The base change formulas of Bianchi modular forms as power sums

LMFDB `mf.bianchi.base_change` gives the eigenvalues of the base change of a classical newform `f`
to an imaginary quadratic field `K` according to the splitting of `p`: `a_𝔭 = a_p` if `p` splits or
ramifies, `a_𝔭 = a_p² - 2χ(p)p^{w-1}` if `p` is inert, `p𝒪_K = 𝔭`. The general notion of LMFDB
`mf.base_change` asks for `L_𝔭(F, T) = L_p^{(r)}(f, T)` with `r` the residue degree of `𝔭`, whose
coefficients of `T` are `a_𝔭 = α_p^r + β_p^r` (`HeckeRing.GL2.Newform.rootPowers_eulerFactor`). In a
quadratic field the residue degree of a prime `𝔭 ∋ p` is `2` exactly when `p𝒪_K = 𝔭`, and `1`
otherwise, as `N(𝔭) = p^r` divides `N(p𝒪_K) = p²`, with equality only for `𝔭 = p𝒪_K`. So the
knowl's case distinction is the residue degree, and the base change relation of
`mf.bianchi.base_change` is the eigenvalue part of the relation of `mf.base_change`: `a_𝔭` is the
power sum `α_p^r + β_p^r` for the residue degree `r` of `𝔭`. With the central character
`χ ∘ N_{K/ℚ}` of the base change, which the forms here do not determine, the whole Euler factors
then satisfy the relation `NumberField.IsBaseChangeOfEulerFactors` of `mf.base_change` over `ℚ`, the
residue degrees over `𝒪_ℚ` being those over `ℤ`.

## Main results

* `Ideal.inertiaDeg_eq_ite_of_finrank_eq_two`: in a quadratic field, the residue degree of a prime
  `𝔭 ∋ p` is `2` if `p𝒪_K = 𝔭` and `1` otherwise.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.isBaseChange_iff_frobeniusPowerSum` and
  `HyperbolicThreeSpace.BianchiNewformOfWeight.isBaseChange_iff_frobeniusPowerSum` (LMFDB
  `mf.bianchi.base_change`, `mf.base_change`): over a quadratic field, a Bianchi form is the base
  change of `f` exactly when its eigenvalues are the power sums `α_p^r + β_p^r` for the residue
  degrees `r`.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.IsBaseChange.isBaseChangeOfEulerFactors` (LMFDB
  `mf.bianchi.base_change`, `mf.base_change`): a base change in the sense of
  `mf.bianchi.base_change` is one in the sense of `mf.base_change`.
-/

open HeckeRing GL2 NumberField Ideal Polynomial UpperHalfPlane

open scoped nonZeroDivisors

lemma Ideal.inertiaDeg_int_eq_one_of_rat {𝔭 : Ideal (𝓞 ℚ)} [𝔭.IsPrime] [NeZero 𝔭] :
    𝔭.inertiaDeg ℤ = 1 := by
  have hp : (absNorm (under ℤ 𝔭)).Prime := Nat.absNorm_under_prime 𝔭
  have hf : absNorm (under ℤ 𝔭) ^ 𝔭.inertiaDeg ℤ = absNorm 𝔭 := pow_inertiaDeg _ 𝔭
  have h₁ : absNorm (span {((absNorm (under ℤ 𝔭) : ℕ) : 𝓞 ℚ)}) = absNorm (under ℤ 𝔭) ^ 1 := by
    rw [absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self]
  have hdvd : absNorm (under ℤ 𝔭) ^ 𝔭.inertiaDeg ℤ ∣ absNorm (under ℤ 𝔭) ^ 1 := by
    rw [hf, ← h₁]
    exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr (Int.absNorm_under_mem 𝔭))
  have hle : 𝔭.inertiaDeg ℤ ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hpos : 0 < 𝔭.inertiaDeg ℤ := inertiaDeg_pos 𝔭 ℤ
  omega

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

lemma Ideal.inertiaDeg_rat_eq_inertiaDeg_int (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] (h𝔮 : 𝔮 ≠ ⊥) :
    𝔮.inertiaDeg (𝓞 ℚ) = 𝔮.inertiaDeg ℤ := by
  have h₀ : NeZero (𝔮.under (𝓞 ℚ)) := ⟨fun h ↦ h𝔮 (eq_bot_of_under_eq_bot h)⟩
  rw [inertiaDeg_tower (𝔮.under (𝓞 ℚ)) 𝔮 (R := ℤ), inertiaDeg_int_eq_one_of_rat, one_mul]

/-- **The residue degrees in a quadratic field**: if `[K : ℚ] = 2`, the residue degree of a prime
`𝔭` of `𝒪_K` containing the prime number `p` is `2` if `p` is inert, `p𝒪_K = 𝔭`, and `1` otherwise:
`N(𝔭) = p^r` divides `N(p𝒪_K) = p²`, and `N(𝔭) = p²` forces `𝔭 = p𝒪_K`. -/
lemma Ideal.inertiaDeg_eq_ite_of_finrank_eq_two (hK : Module.finrank ℚ K = 2) (hp : p.Prime)
    {𝔭 : Ideal (𝓞 K)} [𝔭.IsPrime] (hp𝔭 : (p : 𝓞 K) ∈ 𝔭) :
    𝔭.inertiaDeg ℤ = if span {(p : 𝓞 K)} = 𝔭 then 2 else 1 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hlies : 𝔭.LiesOver (span {(p : ℤ)}) := by
    rw [liesOver_iff]
    refine IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
    rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
    exact hp𝔭
  have hf : p ^ 𝔭.inertiaDeg ℤ = absNorm 𝔭 := pow_inertiaDeg p 𝔭
  have hp₂ : absNorm (span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [absNorm_span_natCast, RingOfIntegers.rank, hK]
  split_ifs with h
  · subst h
    rw [hp₂] at hf
    exact Nat.pow_right_injective hp.two_le hf
  · rcases dvd_iff_le.mpr ((span_singleton_le_iff_mem _).mpr hp𝔭) with ⟨𝔪, h𝔪⟩
    have hN : p ^ 2 = p ^ 𝔭.inertiaDeg ℤ * absNorm 𝔪 := by
      rw [← hp₂, h𝔪, map_mul, hf]
    have hle : 𝔭.inertiaDeg ℤ ≤ 2 :=
      (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (Dvd.intro _ hN.symm)
    have hpos : 0 < 𝔭.inertiaDeg ℤ := inertiaDeg_pos 𝔭 ℤ
    have hne : 𝔭.inertiaDeg ℤ ≠ 2 := fun h₂ ↦ h <| by
      rw [h₂] at hN
      rw [h𝔪, absNorm_eq_one_iff.mp ((Nat.mul_eq_left (pow_ne_zero 2 hp.ne_zero)).mp hN.symm),
        mul_top]
    omega

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {w : ℤ} (f : Newform N w) {𝔭 : Ideal (𝓞 K)}

lemma quadraticBaseChangeEigenvalue_eq_frobeniusPowerSum_inertiaDeg (hK : Module.finrank ℚ K = 2)
    (hp : p.Prime) [𝔭.IsPrime] (hp𝔭 : (p : 𝓞 K) ∈ 𝔭) :
    f.quadraticBaseChangeEigenvalue p 𝔭 = f.frobeniusPowerSum p (𝔭.inertiaDeg ℤ) := by
  rw [quadraticBaseChangeEigenvalue_eq_frobeniusPowerSum,
    inertiaDeg_eq_ite_of_finrank_eq_two hK hp hp𝔭]

end HeckeRing.GL2.Newform

namespace HyperbolicThreeSpace

variable {σ : K →+* ℂ} {k : ℕ} {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑] {N : ℕ} [NeZero N] {w : ℤ}
  {f : Newform N w} {𝔟 : NarrowClassGroup K → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
  {Φ : bianchiClassGroupForms σ k 𝔑 𝔟} {hΦ : IsBianchiHeckeEigenform Φ}

namespace IsBianchiHeckeEigenform

variable (hΦ) in
/-- **The Bianchi base change relation is that of LMFDB `mf.base_change`**: over a quadratic field
`K`, a Hecke eigenform `Φ` of any class number is the base change of `f` (LMFDB
`mf.bianchi.base_change`) exactly when it has weight `2w - 2` and its eigenvalue at every prime
`𝔭 ∤ 𝔑` above `p ∤ N` is the power sum `α_p^r + β_p^r` for the residue degree `r` of `𝔭`, the
coefficient of `T` in `L_p^{(r)}(f, T)`. -/
lemma isBaseChange_iff_frobeniusPowerSum (hK : Module.finrank ℚ K = 2) :
    hΦ.IsBaseChange f ↔ (k : ℤ) = 2 * w - 2 ∧ ∀ p : ℕ, p.Prime → ¬p ∣ N →
      ∀ 𝔭 : {𝔭 : (Ideal (𝓞 K))⁰ // (𝔭 : Ideal (𝓞 K)).IsPrime ∧ ¬𝔑 ≤ 𝔭},
        (p : 𝓞 K) ∈ (𝔭.1 : Ideal (𝓞 K)) →
          hΦ.eigenvalue 𝔭 = f.frobeniusPowerSum p ((𝔭.1 : Ideal (𝓞 K)).inertiaDeg ℤ) := by
  refine and_congr_right fun _ ↦ forall₃_congr fun p hp _ ↦ forall₂_congr fun 𝔭 hp𝔭 ↦ ?_
  have h𝔭 : (𝔭.1 : Ideal (𝓞 K)).IsPrime := 𝔭.2.1
  rw [f.quadraticBaseChangeEigenvalue_eq_frobeniusPowerSum_inertiaDeg hK hp hp𝔭]

open scoped Classical in
/-- **A Bianchi base change is a base change in the sense of LMFDB `mf.base_change`**: over a
quadratic field `K`, if `Φ` is the base change of `f` (LMFDB `mf.bianchi.base_change`), then its
good Euler factors `L_𝔮(Φ, T) = 1 - a_𝔮 T + χ(N𝔮) N𝔮^{w-1} T²`, with the central character
`χ ∘ N_{K/ℚ}` of the base change, and those `L_p(f, T) = 1 - a_p T + χ(p) p^{w-1} T²` of `f` satisfy
`L_𝔮(Φ, T) = L_p^{(r)}(f, T)` at all but finitely many primes `𝔮` of `K`, `p` being the prime
below `𝔮` and `r` its residue degree (`NumberField.IsBaseChangeOfEulerFactors`). -/
lemma IsBaseChange.isBaseChangeOfEulerFactors (hK : Module.finrank ℚ K = 2)
    (h : hΦ.IsBaseChange f) : IsBaseChangeOfEulerFactors (span {(N : 𝓞 ℚ)})
      (fun 𝔭 ↦ 1 - C ((qExpansion 1 f.toCuspForm).coeff (absNorm (under ℤ 𝔭))) * X +
        C (f.dirichletLift (absNorm (under ℤ 𝔭)) * (absNorm (under ℤ 𝔭) : ℂ) ^ (w - 1)) * X ^ 2)
      (fun 𝔮 ↦ if h𝔮 : 𝔮 ∈ (Ideal (𝓞 K))⁰ ∧ 𝔮.IsPrime ∧ ¬𝔑 ≤ 𝔮 then
        1 - C (hΦ.eigenvalue ⟨⟨𝔮, h𝔮.1⟩, h𝔮.2⟩) * X +
          C (f.dirichletLift (absNorm 𝔮) * (absNorm 𝔮 : ℂ) ^ (w - 1)) * X ^ 2 else 1) := by
  have hfin : {𝔮 : Ideal (𝓞 K) | 𝔑 ≤ 𝔮}.Finite :=
    (finite_setOfPred_absNorm_le (absNorm 𝔑)).subset fun 𝔮 h𝔮 ↦ Nat.le_of_dvd
      (Nat.pos_of_ne_zero (absNorm_ne_zero_of_nonZeroDivisors
        ⟨𝔑, mem_nonZeroDivisors_of_ne_zero (NeZero.ne 𝔑)⟩)) (absNorm_dvd_absNorm_of_le h𝔮)
  filter_upwards [hfin.compl_mem_cofinite] with 𝔮 h𝔮𝔑 h𝔮 h𝔮0 hN
  have hne : NeZero 𝔮 := ⟨h𝔮0⟩
  have hp : (absNorm (under ℤ 𝔮)).Prime := Nat.absNorm_under_prime 𝔮
  have hp𝔮 : ((absNorm (under ℤ 𝔮) : ℕ) : 𝓞 K) ∈ 𝔮 := Int.absNorm_under_mem 𝔮
  have hpN : ¬absNorm (under ℤ 𝔮) ∣ N := by
    rintro ⟨m, hm⟩
    refine hN ((span_singleton_le_iff_mem _).mpr ?_)
    rw [mem_comap, map_natCast, hm, Nat.cast_mul]
    exact mul_mem_right _ _ hp𝔮
  have hunder : under ℤ (𝔮.comap (algebraMap (𝓞 ℚ) (𝓞 K))) = under ℤ 𝔮 := under_under 𝔮
  have hχ :
      f.dirichletLift (absNorm (under ℤ 𝔮)) * ((absNorm (under ℤ 𝔮) : ℕ) : ℂ) ^ (w - 1) ≠ 0 := by
    refine mul_ne_zero ?_ (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))
    rw [f.dirichletLift_apply_of_coprime (hp.coprime_iff_not_dvd.mpr hpN)]
    exact Units.ne_zero _
  have hpow : absNorm (under ℤ 𝔮) ^ 𝔮.inertiaDeg ℤ = absNorm 𝔮 := pow_inertiaDeg _ 𝔮
  have hz : (((absNorm (under ℤ 𝔮) : ℕ) : ℂ) ^ 𝔮.inertiaDeg ℤ) ^ (w - 1) =
      (((absNorm (under ℤ 𝔮) : ℕ) : ℂ) ^ (w - 1)) ^ 𝔮.inertiaDeg ℤ := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have h𝔭 : hΦ.eigenvalue ⟨⟨𝔮, mem_nonZeroDivisors_of_ne_zero h𝔮0⟩, h𝔮, h𝔮𝔑⟩ =
      f.frobeniusPowerSum (absNorm (under ℤ 𝔮)) (𝔮.inertiaDeg ℤ) := by
    rw [h.2 _ hp hpN _ hp𝔮,
      f.quadraticBaseChangeEigenvalue_eq_frobeniusPowerSum_inertiaDeg hK hp hp𝔮]
  rw [dite_eq_left ⟨mem_nonZeroDivisors_of_ne_zero h𝔮0, h𝔮, h𝔮𝔑⟩, h𝔭, hunder,
    inertiaDeg_rat_eq_inertiaDeg_int 𝔮 h𝔮0, f.rootPowers_eulerFactor _ hχ, ← hpow]
  simp only [Nat.cast_pow, map_pow, hz, mul_pow]

end IsBianchiHeckeEigenform

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] in
/-- **The base change relation for Bianchi newforms is that of LMFDB `mf.base_change`**: over a
quadratic field `K` of class number `1`, a Bianchi newform `F` is the base change of `f` exactly
when it has weight `2w - 2` and its eigenvalue at every prime `𝔭` above `p ∤ N` is the power sum
`α_p^r + β_p^r` for the residue degree `r` of `𝔭`. -/
lemma BianchiNewformOfWeight.isBaseChange_iff_frobeniusPowerSum (hK : Module.finrank ℚ K = 2)
    (F : BianchiNewformOfWeight σ k 𝔑) :
    F.IsBaseChange f ↔ (k : ℤ) = 2 * w - 2 ∧ ∀ p : ℕ, p.Prime → ¬p ∣ N →
      ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (p : 𝓞 K) ∈ 𝔭.1 →
        F.eigenvalue 𝔭 = f.frobeniusPowerSum p (𝔭.1.inertiaDeg ℤ) := by
  refine and_congr_right fun _ ↦ forall₃_congr fun p hp _ ↦ forall₂_congr fun 𝔭 hp𝔭 ↦ ?_
  have h𝔭 : 𝔭.1.IsPrime := 𝔭.2.1
  rw [f.quadraticBaseChangeEigenvalue_eq_frobeniusPowerSum_inertiaDeg hK hp hp𝔭]

end HyperbolicThreeSpace
