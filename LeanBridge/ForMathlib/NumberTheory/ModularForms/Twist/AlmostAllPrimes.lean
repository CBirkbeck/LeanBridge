import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NebentypusRigidity
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.StrongMainLemma
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Multiplicity

/-!
# Twists at almost all primes

The LMFDB defines self twists and inner twists through the condition `a_p(g) = ψ(p) a_p(f)` at all
but finitely many primes `p` (LMFDB `cmf.self_twist`, `cmf.inner_twist`), and the twist `f ⊗ ψ`
through `a_n(g) = ψ(n) a_n(f)` at all `n` prime to the level of `f` and the conductor of `ψ`
(LMFDB `cmf.twist`). This file shows that, for a primitive `ψ` of positive modulus, the first
condition implies the second when `g` has the level and weight of `f`, with its consequences for the
multiplicity of `[f]` as a twist of itself (LMFDB `cmf.twist_multiplicity`) and for the coefficients
of a newform with a self twist (LMFDB `cmf.self_twist`).

Let `f` and `h` be newforms of the same weight and of levels `N` and `N'`, with `a_p(h) = a_p(f)` at
almost all primes `p`. Read at level `N N'`, they have the same nebentypus, by nebentypus rigidity,
so their difference is a good Hecke eigenvector with `a₁ = 0`. It therefore vanishes at the indices
prime to `N N'` and to the exceptional primes, and the Main Lemma away from the level
(`TauCeti.qExpansion_coeff_eq_zero_of_forall_coprime_qExpansion_coeff_eq_zero`) removes the
exceptional primes. So `a_n(h) = a_n(f)` at every `n` prime to `N N'`. Strong multiplicity one
across levels is not used, and it is not proved here: the equality says nothing at the `n` sharing
a prime factor with `N N'`, nor that `N = N'`. This is why the converse of
`HeckeRing.GL2.Newform.IsTwistBy.isTwistAtAlmostAllPrimes` is stated for `g` of the level and weight
of `f`: then the indices prime to the level of `f` and the modulus of `ψ` are prime to the level of
the twist `f ⊗ ψ` (`HeckeRing.GL2.Newform.exists_isTwistBy`) and to the level of `g`. For `g` of
another level it is not proved here, and neither is it proved that twist equivalent newforms have
the same weight.

The clauses of `cmf.self_twist` that a nontrivial self twist character has order `2` and is the
Kronecker character of a quadratic field are
`HeckeRing.GL2.Newform.HasSelfTwist.isQuadratic_character` and
`HeckeRing.GL2.Newform.HasSelfTwist.exists_kroneckerChar_of_ne_one`, in
`LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwistQuadratic`, and the clause on `a_p`
at all primes is proved here. That only newforms of weight one with dihedral projective image can
have real multiplication, and that a newform has several nontrivial self twists exactly when it has
weight one and projective image `D₂ = C₂ × C₂`, are theorems resting on Galois representations,
which are not proved here.

## Main results

* `HeckeRing.GL2.Newform.qExpansion_coeff_eq_of_eventually_coeff_eq`: newforms of the same weight
  and of any levels with the same `a_p` at almost all primes have the same `a_n` at every `n` prime
  to both levels.
* `HeckeRing.GL2.Newform.IsTwistAtAlmostAllPrimes.isTwistBy`: for `g` of the level and weight of `f`
  and a primitive `ψ` of positive modulus, `a_p(g) = ψ(p) a_p(f)` at almost all primes gives
  `g = f ⊗ ψ`.
* `HeckeRing.GL2.Newform.twistMultiplicity_self_eq_innerTwistMultiplicity`: the multiplicity of
  `[f]` as a twist of itself by `[ψ]` is the inner twist multiplicity of `f` for `[ψ]`.
* `HeckeRing.GL2.Newform.HasSelfTwist.coeff_eq_zero_of_apply_eq_neg_one`: for a self twist `ψ`, the
  coefficient `a_n(f)` vanishes at every `n` prime to the level with `ψ(n) = -1`.
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Matrix SpecialLinearGroup

namespace HeckeRing.GL2.Newform

variable {N N' M n : ℕ} [NeZero N] [NeZero N'] {k : ℤ} {f g : Newform N k} {h : Newform N' k}
  {ψ : DirichletCharacter ℂ M}

/-- **Newforms of any levels with the same `a_p` at almost all primes have the same `a_n` at every
`n` prime to both levels**: for newforms `f` and `h` of the same weight and of levels `N` and `N'`,
if `a_p(h) = a_p(f)` at all but finitely many primes `p`, then `a_n(h) = a_n(f)` at every `n` prime
to `N N'`. Their difference, read at level `N N'`, is a good Hecke eigenvector with `a₁ = 0`, so it
vanishes away from finitely many primes, and then at every index prime to the level by the Main
Lemma away from the level. -/
lemma qExpansion_coeff_eq_of_eventually_coeff_eq (hfh : ∀ᶠ p in Filter.cofinite, p.Prime →
    (qExpansion 1 h.toCuspForm).coeff p = (qExpansion 1 f.toCuspForm).coeff p)
    (hn : n.Coprime (N * N')) :
    (qExpansion 1 h.toCuspForm).coeff n = (qExpansion 1 f.toCuspForm).coeff n := by
  have hL : NeZero (N * N') := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N')⟩
  have h₁ : 1 * N ∣ N * N' := by simp
  have h₂ : 1 * N' ∣ N * N' := by simp
  let D : CuspForm ((Gamma1 (N * N')).map (mapGL ℝ)) k :=
    CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h₂) h.toCuspForm -
      CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h₁) f.toCuspForm
  have hχ : f.χ.comp (ZMod.unitsMap (dvd_mul_right N N')) =
      h.χ.comp (ZMod.unitsMap (dvd_mul_left N' N)) :=
    comp_unitsMap_eq_of_eventually_coeff_eq f h _ _ hfh
  have hD : D ∈ cuspFormCharSpace k (f.χ.comp (ZMod.unitsMap (dvd_mul_right N N'))) :=
    Submodule.sub_mem _
      (hχ ▸ CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h₂ h.χ h.mem_charSpace)
      (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h₁ f.χ f.mem_charSpace)
  have hfin : {p : ℕ | ¬(p.Prime → (qExpansion 1 h.toCuspForm).coeff p =
      (qExpansion 1 f.toCuspForm).coeff p)}.Finite := Filter.eventually_cofinite.mp hfh
  have hT₀ : N * N' * ∏ q ∈ hfin.toFinset, q ≠ 0 :=
    mul_ne_zero hL.out <| Finset.prod_ne_zero_iff.mpr fun q hq ↦
      (Classical.not_imp.mp (hfin.mem_toFinset.mp hq)).1.ne_zero
  have hdiv : N * N' ∣ N * N' * ∏ q ∈ hfin.toFinset, q := dvd_mul_right _ _
  have hcoeff (m : ℕ) : (qExpansion 1 ⇑D).coeff m =
      (qExpansion 1 h.toCuspForm).coeff m - (qExpansion 1 f.toCuspForm).coeff m := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _),
      map_sub, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
        (one_mem_strictPeriods_Gamma1_map _), CuspForm.qExpansion_levelRaise_coeff
        (one_mem_strictPeriods_Gamma1_map _) (one_mem_strictPeriods_Gamma1_map _),
      ite_eq_left (one_dvd m), ite_eq_left (one_dvd m), Nat.div_one]
  have hvan :
      ∀ m : ℕ, m.Coprime (N * N' * ∏ q ∈ hfin.toFinset, q) → (qExpansion 1 ⇑D).coeff m = 0 := by
    refine qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_coprime
      (F := ⟨_, hD⟩) hdiv (fun p hp hpT ↦ ?_) ?_
    · have : NeZero p := ⟨hp.ne_zero⟩
      have hpNN : p.Coprime (N * N') := hpT.coprime_dvd_right hdiv
      have hpN : p.Coprime N := hpNN.coprime_dvd_right (dvd_mul_right N N')
      have hpN' : p.Coprime N' := hpNN.coprime_dvd_right (dvd_mul_left N' N)
      refine ⟨f.eigenvalue ⟨p, hp.pos⟩ hpN,
        heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul_of_heckeTCuspNat_eq_smul hp ?_⟩
      have hap : (qExpansion 1 h.toCuspForm).coeff p = (qExpansion 1 f.toCuspForm).coeff p := by
        by_contra hne
        exact hp.ne_one <| Nat.eq_one_of_dvd_coprimes hpT dvd_rfl <| dvd_mul_of_dvd_right
          (Finset.dvd_prod_of_mem (fun q ↦ q) (hfin.mem_toFinset.mpr fun h' ↦ hne (h' hp))) _
      have heig : h.eigenvalue ⟨p, hp.pos⟩ hpN' = f.eigenvalue ⟨p, hp.pos⟩ hpN := by
        rw [← h.qExpansion_coeff_eq_eigenvalue h.isNorm ⟨p, hp.pos⟩ hpN',
          ← f.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩ hpN]
        exact hap
      rw [map_sub, h.heckeTCuspNat_levelRaise_eq_eigenvalue_smul h₂ hp hpNN,
        f.heckeTCuspNat_levelRaise_eq_eigenvalue_smul h₁ hp hpNN, heig, smul_sub]
    · exact (hcoeff 1).trans (by rw [h.isNorm, f.isNorm, sub_self])
  exact sub_eq_zero.mp <| (hcoeff n).symm.trans <|
    qExpansion_coeff_eq_zero_of_forall_coprime_qExpansion_coeff_eq_zero hT₀ hD hvan hn

/-- **A twist at almost all primes, of the level and weight of `f`, is the twist**: if `g` has the
level and weight of `f`, and `a_p(g) = ψ(p) a_p(f)` at all but finitely many primes `p` for a
primitive character `ψ` of positive modulus, then `g = f ⊗ ψ`, that is `a_n(g) = ψ(n) a_n(f)` at
every `n` prime to the level of `f` and the modulus of `ψ`. -/
lemma IsTwistAtAlmostAllPrimes.isTwistBy (hfg : f.IsTwistAtAlmostAllPrimes ψ g) (hM : M ≠ 0)
    (hψ : ψ.IsPrimitive) : f.IsTwistBy ψ g := by
  have : NeZero M := ⟨hM⟩
  rcases f.exists_isTwistBy hψ with ⟨R, g', hR, hg'⟩
  refine ⟨hM, hψ, fun n hn ↦ ?_⟩
  rw [← hg'.2.2 n hn]
  refine qExpansion_coeff_eq_of_eventually_coeff_eq ?_ ?_
  · filter_upwards [hfg, hg'.isTwistAtAlmostAllPrimes] with p hp hp' hpp
    rw [hp hpp, hp' hpp]
  · have hnM : n.Coprime M := hn.coprime_dvd_right (dvd_mul_left M N)
    have hnN : n.Coprime N := hn.coprime_dvd_right (dvd_mul_right N M)
    have hnL : n.Coprime (M * N.lcm M) := hnM.mul_right (hn.coprime_dvd_right (N.lcm_dvd_mul M))
    exact (hnL.coprime_dvd_right hR).mul_right hnN

/-- **The multiplicity of `[f]` as a twist of itself is the inner twist multiplicity** of `f` for
`[ψ]`, the number of characters in `[ψ]` by which `f` admits an inner twist. The same then holds for
the multiplicity of `[g]`, for any `g` in the Galois orbit of `f`
(`IsGaloisConjugate.twistMultiplicity_eq`). The LMFDB says the inner twist count instead
(`cmf.twist_multiplicity`), which is the sum of these numbers over the Galois orbits `[ψ]`. -/
lemma twistMultiplicity_self_eq_innerTwistMultiplicity :
    f.twistMultiplicity ψ f = f.innerTwistMultiplicity ψ :=
  congrArg Set.ncard <| Set.ext fun _ ↦ and_congr_right fun _ ↦
    ⟨fun ⟨g, hg, hfg⟩ ↦ ⟨hfg.1, hfg.2.1, g, hg, hfg.isTwistAtAlmostAllPrimes⟩,
      fun ⟨hM, hprim, g, hg, hfg⟩ ↦ ⟨g, hg, hfg.isTwistBy hM hprim⟩⟩

/-- **The clause of `cmf.self_twist` at all primes**: if `f` admits a self twist by `ψ`, then
`a_n(f) = 0` at every `n` prime to the level of `f` with `ψ(n) = -1`, in particular at every prime
`p` not dividing the level with `ψ(p) = -1`, with no prime excepted. -/
lemma HasSelfTwist.coeff_eq_zero_of_apply_eq_neg_one (hf : f.HasSelfTwist ψ) (hn : n.Coprime N)
    (hψ : ψ n = -1) : (qExpansion 1 f.toCuspForm).coeff n = 0 := by
  have hnM : n.Coprime M := by
    refine (ZMod.isUnit_iff_coprime n M).mp ?_
    by_contra hu
    rw [MulChar.map_nonunit _ hu] at hψ
    norm_num at hψ
  have hfn : (qExpansion 1 f.toCuspForm).coeff n = ψ n * (qExpansion 1 f.toCuspForm).coeff n :=
    (hf.2.2.isTwistBy hf.1 hf.2.1).2.2 n (hn.mul_right hnM)
  rw [hψ, neg_mul, one_mul] at hfn
  exact self_eq_neg.mp hfn

end HeckeRing.GL2.Newform
