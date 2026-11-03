import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwistQuadratic
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.TraceOfTwist

/-!
# The conductor of a self twist

A self twist of a newform `f` of level `N` is a primitive Dirichlet character `ψ` of modulus `M`
with `a_p(f) = ψ(p) a_p(f)` at almost all primes `p` (LMFDB `cmf.self_twist`). It is quadratic, and
`M` is the absolute value of a fundamental discriminant, by
`HeckeRing.GL2.Newform.HasSelfTwist.exists_kroneckerChar_of_ne_one`. This file shows that a prime
dividing `M` exactly once divides `N`. So `M ∣ 8 N`, and `f` has finitely many self twists, which is
what the finiteness of the group of inner twists rests on. Neither strong multiplicity one across
levels nor Galois representations are used. The sharp statement, that `M ∣ N`, is not proved here.

Suppose that `q` divides `M` exactly once and does not divide `N`. Let `P₀` be the product of `N`,
of `M / q` and of the primes other than `q` at which the relation between `a_p(f)` and
`ψ(p) a_p(f)` fails, so that `q ∤ P₀`, and let `F` be `f` with its coefficients at the indices not
prime to `P₀` removed (`HeckeRing.GL2.Newform.coprimeFilter`), a cusp form of level `P₀²` with
`a₁(F) = 1`. By the Hecke recursion, `ψ(n) a_n(F) = a_n(F)` for all `n` prime to `q`, against
`TauCeti.qExpansion_coeff_one_eq_zero_of_forall_coprime_apply_mul_eq`.

## Main results

* `HeckeRing.GL2.Newform.HasSelfTwist.dvd_level_of_dvd_of_not_sq_dvd`: a prime dividing the modulus
  of a self twist exactly once divides the level.
* `HeckeRing.GL2.Newform.HasSelfTwist.dvd_eight_mul_level`: the modulus of a self twist divides
  `8 N`.
* `HeckeRing.GL2.Newform.finite_setOf_hasSelfTwist`: a newform has finitely many self twists.
-/

open UpperHalfPlane TauCeti

namespace HeckeRing.GL2.Newform

variable {N M : ℕ} [NeZero N] {k : ℤ} {f : Newform N k} {ψ : DirichletCharacter ℂ M}

/-- **A prime dividing the modulus of a self twist exactly once divides the level**: if `f` of level
`N` has a self twist by the primitive character `ψ` of modulus `M`, and a prime `q` divides `M` but
`q²` does not, then `q` divides `N`. -/
lemma HasSelfTwist.dvd_level_of_dvd_of_not_sq_dvd (hf : f.HasSelfTwist ψ) {q : ℕ} (hq : q.Prime)
    (hqM : q ∣ M) (hq2 : ¬q ^ 2 ∣ M) : q ∣ N := by
  by_contra hqN
  have : NeZero q := ⟨hq.ne_zero⟩
  rcases hqM with ⟨M', rfl⟩
  have hM'₀ : M' ≠ 0 := right_ne_zero_of_mul hf.1
  have : NeZero M' := ⟨hM'₀⟩
  have hqM' : ¬q ∣ M' := fun ⟨c, hc⟩ ↦ hq2 ⟨c, by rw [hc]; ring1⟩
  have hfin : {p : ℕ | ¬(p.Prime → (qExpansion 1 f.toCuspForm).coeff p =
      ψ p * (qExpansion 1 f.toCuspForm).coeff p)}.Finite := Filter.eventually_cofinite.mp hf.2.2
  have hT : ∀ p ∈ hfin.toFinset.erase q, p.Prime ∧ p ≠ q := fun p hp ↦ by
    rcases Finset.mem_erase.mp hp with ⟨hpq, hp'⟩
    exact ⟨(Classical.not_imp.mp (hfin.mem_toFinset.mp hp')).1, hpq⟩
  let P₀ : ℕ := N * M' * ∏ p ∈ hfin.toFinset.erase q, p
  have hP₀ : NeZero P₀ := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) hM'₀)
    (Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hT p hp).1.ne_zero)⟩
  have hqP₀ : ¬q ∣ P₀ := fun hd ↦ by
    rcases hq.dvd_mul.mp hd with hd | hd
    · exact (hq.dvd_mul.mp hd).elim hqN hqM'
    · rcases hq.prime.exists_mem_finset_dvd hd with ⟨p, hp, hqp⟩
      exact (hT p hp).2 ((Nat.prime_dvd_prime_iff_eq hq (hT p hp).1).mp hqp).symm
  have hNP₀ : N ∣ P₀ := (dvd_mul_right N M').mul_right _
  have hM'P₀ : M' ∣ P₀ := (dvd_mul_left M' N).mul_right _
  have hψ : ¬ψ.FactorsThrough M' := fun h ↦ by
    have hle : ψ.conductor ≤ M' := Nat.sInf_le h
    rw [hf.2.1] at hle
    exact absurd hle (not_le.mpr (lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hM'₀) hq.one_lt))
  have key : (qExpansion 1 (f.coprimeFilter hNP₀)).coeff 1 = 0 := by
    refine qExpansion_coeff_one_eq_zero_of_forall_coprime_apply_mul_eq ψ hq (hM'P₀.mul_left P₀)
      (fun hd ↦ (hq.dvd_mul.mp hd).elim hqP₀ hqP₀) (f.coprimeFilter_mem_cuspFormCharSpace hNP₀) hψ
      fun n hn ↦ ?_
    rw [qExpansion_coeff_coprimeFilter]
    split_ifs with hnP
    · refine (qExpansion_coeff_eq_apply_mul_of_forall_prime (L := P₀ * q) (hNP₀.mul_right q)
        (hNP₀.mul_right q) (fun p hp hpL ↦ ?_) (fun p hp hpL ↦ ?_) (hnP.mul_right hn)).symm
      · have hpM : p.Coprime (q * M') := (hpL.coprime_dvd_right (dvd_mul_left q P₀)).mul_right
          (hpL.coprime_dvd_right (hM'P₀.mul_right q))
        rw [← MulChar.pow_apply' _ two_ne_zero,
          MulChar.isQuadratic_iff_sq_eq_one.mp hf.isQuadratic_character,
          MulChar.one_apply ((ZMod.isUnit_iff_coprime p (q * M')).mpr hpM), one_mul]
      · by_contra hne
        have hmem : p ∈ hfin.toFinset := hfin.mem_toFinset.mpr fun h' ↦ hne (h' hp)
        have hpq : p ≠ q := fun h ↦ hp.ne_one
          (Nat.eq_one_of_dvd_coprimes (hpL.coprime_dvd_right (dvd_mul_left q P₀)) dvd_rfl h.dvd)
        have hd : p ∣ P₀ :=
          (Finset.dvd_prod_of_mem (fun p ↦ p) (Finset.mem_erase.mpr ⟨hpq, hmem⟩)).mul_left _
        exact hp.ne_one
          (Nat.eq_one_of_dvd_coprimes (hpL.coprime_dvd_right (dvd_mul_right _ _)) dvd_rfl hd)
    · rw [mul_zero]
  rw [qExpansion_coeff_coprimeFilter, ite_eq_left (Nat.coprime_one_left P₀), f.isNorm] at key
  exact one_ne_zero key

/-- **The modulus of a self twist divides `8 N`**: if `f` of level `N` has a self twist by the
primitive character `ψ` of modulus `M`, then `M ∣ 8 N`. The odd part of `M` is squarefree, as `ψ` is
the Kronecker character of a quadratic field, and its prime factors divide `N`. -/
lemma HasSelfTwist.dvd_eight_mul_level (hf : f.HasSelfTwist ψ) : M ∣ 8 * N := by
  have hNe : NeZero M := ⟨hf.1⟩
  by_cases hψ : ψ = 1
  · subst hψ
    have hM : M = 1 := hf.2.1.symm.trans DirichletCharacter.conductor_one
    rw [hM]
    exact one_dvd _
  rcases hf.exists_kroneckerChar_of_ne_one hψ with ⟨D, hD, h, -⟩
  have hMD : M = D.natAbs := congrArg (fun x : Σ M : ℕ+, DirichletCharacter ℂ M ↦ (x.1 : ℕ)) h
  have hN₈ : 8 * N ≠ 0 := mul_ne_zero (by norm_num) (NeZero.ne N)
  refine (Nat.factorization_prime_le_iff_dvd hf.1 hN₈).mp fun p hp ↦ ?_
  rw [← hp.pow_dvd_iff_le_factorization hN₈]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have he : M.factorization 2 ≤ 3 := by
      by_contra hlt
      have h16 : 2 ^ 4 ∣ M := (hp.pow_dvd_iff_le_factorization hf.1).mpr (by omega)
      rcases Int.natCast_dvd.mpr (hMD ▸ h16 : 2 ^ 4 ∣ D.natAbs) with ⟨y, hy⟩
      exact (hD.2.1 (4 * y) (by rw [hy]; push_cast; ring1)).1 ⟨y, rfl⟩
    exact (pow_dvd_pow 2 he).trans (dvd_mul_right 8 N)
  · by_cases hpM : p ∣ M
    · have hsq : ¬p ^ 2 ∣ M := fun hd ↦ hD.2.2 p hp hodd <| by
        have hd' : ((p ^ 2 : ℕ) : ℤ) ∣ D := Int.natCast_dvd.mpr (hMD ▸ hd)
        rwa [Nat.cast_pow] at hd'
      have he : M.factorization p ≤ 1 := by
        by_contra hlt
        exact hsq ((hp.pow_dvd_iff_le_factorization hf.1).mpr (by omega))
      exact (pow_dvd_pow p he).trans (by
        simpa using (hf.dvd_level_of_dvd_of_not_sq_dvd hp hpM hsq).mul_left 8)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpM, pow_zero]
      exact one_dvd _

variable (f) in
/-- **A newform has finitely many self twists**: their moduli divide `8 N`. -/
lemma finite_setOf_hasSelfTwist :
    {x : Σ M : ℕ+, DirichletCharacter ℂ M | f.HasSelfTwist x.2}.Finite := by
  have hs : {M : ℕ+ | (M : ℕ) ∣ 8 * N}.Finite :=
    ((Nat.divisors (8 * N)).finite_toSet.preimage PNat.coe_injective.injOn).subset fun M hM ↦
      Nat.mem_divisors.mpr ⟨hM, mul_ne_zero (by norm_num) (NeZero.ne N)⟩
  exact (hs.sigma (t := fun _ ↦ Set.univ) fun _ _ ↦ Set.finite_univ).subset fun x hx ↦
    ⟨hx.dvd_eight_mul_level, Set.mem_univ _⟩

end HeckeRing.GL2.Newform
