import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.OldSpaceDecomposition
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.StrongMainLemma
import TauCeti.NumberTheory.ModularForms.Newforms.EigenvectorVanishing
import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue

/-!
# Strong multiplicity one across comparable levels

`HeckeRing.GL2.Newform.CrossLevelMultiplicityOne N k` is strong multiplicity one across the levels
dividing `N` (Atkin–Lehner, Li; Miyake, Theorem 4.6.19): two newforms of weight `k` and levels
`M₁, M₂ ∣ N`, whose nebentypes induce the same character modulo `N` and whose eigenvalues agree
at every prime not dividing `N`, have the same level and are the same function. It is the
hypothesis under which the old-space decompositions (LMFDB `cmf.decomposition.old.gamma1` and
`cmf.decomposition.old.gamma0chi`) are direct.

This file proves it whenever one of the two levels divides the other, with agreement asked only at
the primes not dividing `N`; the pinned Tau Ceti has that case only with agreement at every prime
prime to the larger level (`HeckeRing.GL2.Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`).
For `M₁ ∣ M₂`, the difference `g₂ - g₁` at level `M₂` is a good Hecke eigenvector with `a₁ = 0`,
so its coefficients vanish at every index coprime to `N`, hence (Main Lemma away from the level,
`TauCeti.qExpansion_coeff_eq_zero_of_forall_coprime_qExpansion_coeff_eq_zero`) at every index
coprime to `M₂`, and it is old. If `M₁ ≠ M₂`, `g₁` is old at level `M₂`, so `g₂` is old and new,
which is absurd; if `M₁ = M₂`, the difference is also new, hence zero.

So `CrossLevelMultiplicityOne N k` is equivalent to its case of two levels neither of which
divides the other, `HeckeRing.GL2.Newform.IncomparableLevelMultiplicityOne N k`, which stays
open: it needs the local theory of Atkin–Lehner and Li (or Rankin–Selberg). When `N` is a prime
power, the divisors of `N` form a chain, and the old-space decompositions are unconditional.
For `S_k(N, χ)` only the newforms whose nebentypus induces `χ` matter, hence only the levels
through which `χ` factors: the decomposition rests on the case of the incomparable-level statement
for `χ` alone, and is unconditional when those levels form a chain.

## Main definitions

* `HeckeRing.GL2.Newform.IncomparableLevelMultiplicityOne`: strong multiplicity one across two
  levels dividing `N` neither of which divides the other, the remaining case.
* `HeckeRing.GL2.Newform.IncomparableLevelMultiplicityOneChar`: the same, for the newforms whose
  nebentypus induces a given character `χ` modulo `N`.

## Main results

* `HeckeRing.GL2.Newform.eq_of_dvd_of_forall_prime_eigenvalue_eq`: strong multiplicity one when
  one level divides the other.
* `HeckeRing.GL2.Newform.eq_of_forall_prime_notMem_eigenvalue_eq`: strong multiplicity one at a
  fixed level, with finitely many exceptional primes (Miyake, Theorem 4.6.12).
* `HeckeRing.GL2.Newform.crossLevelMultiplicityOne_iff`: `CrossLevelMultiplicityOne N k` is
  equivalent to `IncomparableLevelMultiplicityOne N k`.
* `HeckeRing.GL2.Newform.crossLevelMultiplicityOne_of_dvd_or_dvd`,
  `HeckeRing.GL2.Newform.crossLevelMultiplicityOne_of_isPrimePow`: it holds when the divisors of
  `N` form a chain, in particular at prime-power level.
* `HeckeRing.GL2.Newform.isInternal_newformLevelRaise_of_isPrimePow`,
  `HeckeRing.GL2.Newform.iSupIndep_newformCharLevelRaise_of_isPrimePow`: the old-space
  decompositions at prime-power level (LMFDB `cmf.decomposition.old.gamma1`,
  `cmf.decomposition.old.gamma0chi`), unconditionally.
* `HeckeRing.GL2.Newform.isInternal_newformLevelRaise_of_incomparableLevelMultiplicityOne`: the
  old-space decomposition of `S_k(Γ₁(N))` at any level, given the remaining case.
* `HeckeRing.GL2.Newform.incomparableLevelMultiplicityOneChar_of_crossLevelMultiplicityOne`: the
  remaining case for one character follows from strong multiplicity one across levels.
* `HeckeRing.GL2.Newform.linearIndependent_levelRaise_of_incomparableLevelMultiplicityOneChar`,
  `HeckeRing.GL2.Newform.iSupIndep_newformCharLevelRaise_of_incomparableLevelMultiplicityOneChar`:
  the level-raised newforms of nebentypus inducing `χ` are independent, and so are the images
  `α_{M,d}(S_k^new(M, χ_M))`, given the remaining case for `χ`.
* `HeckeRing.GL2.Newform.iSupIndep_newformCharLevelRaise_of_dvd_or_dvd`: the old-space
  decomposition of `S_k(N, χ)`, unconditionally when the levels through which `χ` factors form a
  chain.
-/

open Matrix SpecialLinearGroup CongruenceSubgroup UpperHalfPlane TauCeti Module

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)

/-- **Strong multiplicity one across comparable levels**: two newforms `g₁, g₂` of weight `k` and
levels `M₁ ∣ M₂ ∣ N`, whose nebentypes induce the same character modulo `N` and whose eigenvalues
agree at every prime not dividing `N`, have the same level and are the same function. -/
lemma eq_of_dvd_of_forall_prime_eigenvalue_eq {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] (h₁₂ : M₁ ∣ M₂)
    (h₂ : M₂ ∣ N) (g₁ : Newform M₁ k) (g₂ : Newform M₂ k)
    (hχ : g₁.χ.comp (ZMod.unitsMap (h₁₂.trans h₂)) = g₂.χ.comp (ZMod.unitsMap h₂))
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N), g₁.eigenvalue ⟨p, hp.pos⟩
      (hpN.coprime_dvd_right (h₁₂.trans h₂)) = g₂.eigenvalue ⟨p, hp.pos⟩
        (hpN.coprime_dvd_right h₂)) :
    ((M₁, ⇑g₁.toCuspForm) : ℕ × (ℍ → ℂ)) = (M₂, ⇑g₂.toCuspForm) := by
  rw [← ZMod.unitsMap_comp h₁₂ h₂, ← MonoidHom.comp_assoc] at hχ
  have h1 : 1 * M₁ ∣ M₂ := by rwa [one_mul]
  have hGχ : CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1) g₁.toCuspForm ∈
      cuspFormCharSpace k g₂.χ :=
    (MonoidHom.cancel_right (ZMod.unitsMap_surjective h₂)).mp hχ ▸
      CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h1 g₁.χ g₁.mem_charSpace
  have hDχ : g₂.toCuspForm - CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1)
      g₁.toCuspForm ∈ cuspFormCharSpace k g₂.χ :=
    Submodule.sub_mem _ g₂.mem_charSpace hGχ
  -- the difference is a good Hecke eigenvector with `a₁ = 0`, so it vanishes off `N`
  have hDeig : ∀ p : ℕ, p.Prime → p.Coprime N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k g₂.χ (heckeTCompositeGamma0 M₂ p) ⟨_, hDχ⟩ = c • ⟨_, hDχ⟩ := by
    intro p hp hpN
    have : NeZero p := ⟨hp.ne_zero⟩
    refine ⟨g₂.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right h₂),
      heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul_of_heckeTCuspNat_eq_smul hp ?_⟩
    rw [map_sub, g₂.heckeTCuspNat_eq_eigenvalue_smul hp (hpN.coprime_dvd_right h₂),
      g₁.heckeTCuspNat_levelRaise_eq_eigenvalue_smul h1 hp (hpN.coprime_dvd_right h₂), h p hp hpN,
      smul_sub]
  have hD1 : (qExpansion 1 ⇑(g₂.toCuspForm - CuspForm.levelRaise 1
      (Gamma1_map_le_conjAct_scaleGL_of_dvd h1) g₁.toCuspForm)).coeff 1 = 0 := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _),
      map_sub, g₂.isNorm, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
        (one_mem_strictPeriods_Gamma1_map _), ite_eq_left (one_dvd 1), Nat.div_one, g₁.isNorm,
      sub_self]
  have hvan : ∀ n, n.Coprime N → (qExpansion 1 ⇑(g₂.toCuspForm - CuspForm.levelRaise 1
      (Gamma1_map_le_conjAct_scaleGL_of_dvd h1) g₁.toCuspForm)).coeff n = 0 :=
    qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_coprime
      (F := ⟨_, hDχ⟩) h₂ hDeig hD1
  -- so it vanishes off `M₂`, and it is old
  have hDold : g₂.toCuspForm - CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1)
      g₁.toCuspForm ∈ cuspFormsOld M₂ k :=
    mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero_of_ne_zero (NeZero.ne N) hDχ hvan
  rcases eq_or_ne M₁ M₂ with rfl | hM
  · -- at equal levels the difference is also new, hence zero
    have hG : CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1) g₁.toCuspForm =
        g₁.toCuspForm :=
      DFunLike.coe_injective (by rw [CuspForm.levelRaise_one, CuspForm.coe_restrict])
    rw [hG] at hDold
    rw [sub_eq_zero.mp ((Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew M₁ k)) _
      hDold (Submodule.sub_mem _ g₂.isNew g₁.isNew))]
  · -- at a proper divisor level, `g₂ = (g₂ - V₁ g₁) + V₁ g₁` would be old
    exact absurd ((Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew M₂ k)) _
      (sub_add_cancel g₂.toCuspForm _ ▸ Submodule.add_mem _ hDold
        (levelRaise_mem_cuspFormsOld h1 hM k g₁.toCuspForm)) g₂.isNew) g₂.ne_zero

/-- **Strong multiplicity one with finitely many exceptional primes** (Miyake, Theorem 4.6.12):
two newforms of level `M` with the same nebentypus whose eigenvalues agree at every prime not
dividing `M` outside a finite set are equal. Tau Ceti's
`HeckeRing.GL2.Newform.eq_of_forall_notMem_eigenvalue_eq` allows finitely many exceptional
indices, not primes. -/
lemma eq_of_forall_prime_notMem_eigenvalue_eq {M : ℕ} [NeZero M] {f g : Newform M k}
    (hχ : f.χ = g.χ) {S : Finset ℕ} (h : ∀ (p : ℕ) (hp : p.Prime) (hpM : p.Coprime M), p ∉ S →
      f.eigenvalue ⟨p, hp.pos⟩ hpM = g.eigenvalue ⟨p, hp.pos⟩ hpM) : f = g := by
  have : NeZero ((S.filter Nat.Prime).prod id) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun q hq ↦ (Finset.mem_filter.mp hq).2.ne_zero⟩
  exact Newform.ext <| DFunLike.coe_injective <| (Prod.mk_inj.mp <|
    eq_of_dvd_of_forall_prime_eigenvalue_eq dvd_rfl (dvd_mul_right M _) f g (by rw [hχ])
      fun p hp hpN ↦ h p hp _ fun hpS ↦ hp.ne_one (Nat.eq_one_of_dvd_coprimes hpN dvd_rfl
        ((Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hpS, hp⟩)).mul_left M))).2

variable (N k) in
/-- **Strong multiplicity one across incomparable levels**: there are no two newforms of weight
`k` and levels `M₁, M₂ ∣ N`, neither of which divides the other, whose nebentypes induce the same
character modulo `N` and whose eigenvalues agree at every prime not dividing `N`. It is the case
of `HeckeRing.GL2.Newform.CrossLevelMultiplicityOne` that this file leaves open
(`HeckeRing.GL2.Newform.crossLevelMultiplicityOne_iff`), a consequence of strong multiplicity one
across levels (Atkin–Lehner, Li; Miyake, Theorem 4.6.19) that is not proved here; it holds
trivially when the divisors of `N` form a chain. -/
def IncomparableLevelMultiplicityOne : Prop :=
  ∀ (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (h₁ : M₁ ∣ N) (h₂ : M₂ ∣ N), ¬M₁ ∣ M₂ → ¬M₂ ∣ M₁ →
    ∀ (g₁ : Newform M₁ k) (g₂ : Newform M₂ k),
      g₁.χ.comp (ZMod.unitsMap h₁) = g₂.χ.comp (ZMod.unitsMap h₂) →
      (∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N), g₁.eigenvalue ⟨p, hp.pos⟩
        (hpN.coprime_dvd_right h₁) = g₂.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right h₂)) →
      False

/-- **Strong multiplicity one across levels reduces to incomparable levels**:
`CrossLevelMultiplicityOne N k` holds exactly when `IncomparableLevelMultiplicityOne N k` does,
the comparable case being `HeckeRing.GL2.Newform.eq_of_dvd_of_forall_prime_eigenvalue_eq`. -/
lemma crossLevelMultiplicityOne_iff :
    CrossLevelMultiplicityOne N k ↔ IncomparableLevelMultiplicityOne N k := by
  refine ⟨fun h M₁ M₂ _ _ h₁ h₂ h₁₂ _ g₁ g₂ hχ heig ↦
    h₁₂ (dvd_of_eq (Prod.mk_inj.mp (h M₁ M₂ h₁ h₂ g₁ g₂ hχ heig)).1),
    fun h M₁ M₂ _ _ h₁ h₂ g₁ g₂ hχ heig ↦ ?_⟩
  by_cases h₁₂ : M₁ ∣ M₂
  · exact eq_of_dvd_of_forall_prime_eigenvalue_eq h₁₂ h₂ g₁ g₂ hχ heig
  by_cases h₂₁ : M₂ ∣ M₁
  · exact (eq_of_dvd_of_forall_prime_eigenvalue_eq h₂₁ h₁ g₂ g₁ hχ.symm
      fun p hp hpN ↦ (heig p hp hpN).symm).symm
  · exact (h M₁ M₂ h₁ h₂ h₁₂ h₂₁ g₁ g₂ hχ heig).elim

/-- **Strong multiplicity one across levels forming a chain**: if any two divisors of `N` are
comparable under divisibility, `CrossLevelMultiplicityOne N k` holds. -/
lemma crossLevelMultiplicityOne_of_dvd_or_dvd
    (hN : ∀ M₁ M₂ : ℕ, M₁ ∣ N → M₂ ∣ N → M₁ ∣ M₂ ∨ M₂ ∣ M₁) : CrossLevelMultiplicityOne N k :=
  crossLevelMultiplicityOne_iff.mpr fun M₁ M₂ _ _ h₁ h₂ h₁₂ h₂₁ _ _ _ _ ↦
    (hN M₁ M₂ h₁ h₂).elim h₁₂ h₂₁

/-- **Strong multiplicity one across levels at prime-power level**: `CrossLevelMultiplicityOne N k`
holds when `N` is a prime power. -/
lemma crossLevelMultiplicityOne_of_isPrimePow (hN : IsPrimePow N) :
    CrossLevelMultiplicityOne N k := by
  rcases (isPrimePow_nat_iff N).mp hN with ⟨p, a, hp, -, rfl⟩
  refine crossLevelMultiplicityOne_of_dvd_or_dvd fun M₁ M₂ h₁ h₂ ↦ ?_
  rcases (Nat.dvd_prime_pow hp).mp h₁ with ⟨i, -, rfl⟩
  rcases (Nat.dvd_prime_pow hp).mp h₂ with ⟨j, -, rfl⟩
  exact (le_total i j).imp (pow_dvd_pow p) (pow_dvd_pow p)

/-- **The old-space decomposition of `S_k(Γ₁(N))` at prime-power level** (LMFDB
`cmf.decomposition.old.gamma1`; Diamond–Shurman, Theorem 5.8.3): for a prime power `N`,
`S_k(Γ₁(N))` is the internal direct sum of the images `α_{M,t}(S_k^new(Γ₁(M)))` over the pairs
`(M, t)` with `t M ∣ N`. -/
lemma isInternal_newformLevelRaise_of_isPrimePow (hN : IsPrimePow N) :
    DirectSum.IsInternal (newformLevelRaise N k) :=
  isInternal_newformLevelRaise (crossLevelMultiplicityOne_of_isPrimePow hN)

/-- **The old-space decomposition of `S_k(N, χ)` at prime-power level** (LMFDB
`cmf.decomposition.old.gamma0chi`): for a prime power `N`, the images `α_{M,d}(S_k^new(M, χ_M))`
are independent; they span `S_k(N, χ)` by `HeckeRing.GL2.Newform.iSup_newformCharLevelRaise`. -/
lemma iSupIndep_newformCharLevelRaise_of_isPrimePow (hN : IsPrimePow N) :
    iSupIndep (newformCharLevelRaise k χ) :=
  iSupIndep_newformCharLevelRaise χ (crossLevelMultiplicityOne_of_isPrimePow hN)

/-- **The old-space decomposition of `S_k(Γ₁(N))`** (LMFDB `cmf.decomposition.old.gamma1`), given
only the incomparable-level case of strong multiplicity one. -/
lemma isInternal_newformLevelRaise_of_incomparableLevelMultiplicityOne
    (h : IncomparableLevelMultiplicityOne N k) : DirectSum.IsInternal (newformLevelRaise N k) :=
  isInternal_newformLevelRaise (crossLevelMultiplicityOne_iff.mpr h)

variable (k) in
/-- **Strong multiplicity one across incomparable levels, for one character** `χ` modulo `N`:
there are no two newforms of weight `k` and levels `M₁, M₂ ∣ N`, neither of which divides the
other, whose nebentypes both induce `χ` and whose eigenvalues agree at every prime not dividing
`N`. Only the levels through which `χ` factors occur, so this is the case of
`HeckeRing.GL2.Newform.IncomparableLevelMultiplicityOne` that the decomposition of `S_k(N, χ)`
needs; it holds trivially when those levels form a chain under divisibility. -/
def IncomparableLevelMultiplicityOneChar : Prop :=
  ∀ (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (h₁ : M₁ ∣ N) (h₂ : M₂ ∣ N), ¬M₁ ∣ M₂ → ¬M₂ ∣ M₁ →
    ∀ (g₁ : Newform M₁ k) (g₂ : Newform M₂ k), g₁.χ.comp (ZMod.unitsMap h₁) = χ →
      g₂.χ.comp (ZMod.unitsMap h₂) = χ →
      (∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N), g₁.eigenvalue ⟨p, hp.pos⟩
        (hpN.coprime_dvd_right h₁) = g₂.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right h₂)) →
      False

/-- **Strong multiplicity one across levels implies its incomparable-level case for one
character**: `CrossLevelMultiplicityOne N k` (equivalently `IncomparableLevelMultiplicityOne N k`)
implies `IncomparableLevelMultiplicityOneChar k χ`, since two nebentypes that both induce `χ`
induce the same character modulo `N`. -/
lemma incomparableLevelMultiplicityOneChar_of_crossLevelMultiplicityOne
    (h : CrossLevelMultiplicityOne N k) : IncomparableLevelMultiplicityOneChar k χ :=
  fun M₁ M₂ _ _ h₁ h₂ h₁₂ h₂₁ g₁ g₂ hχ₁ hχ₂ ↦ crossLevelMultiplicityOne_iff.mp h M₁ M₂ h₁ h₂ h₁₂ h₂₁
    g₁ g₂ (hχ₁.trans hχ₂.symm)

/-- **The level-raised newforms of nebentypus inducing `χ` are linearly independent**, given the
incomparable-level case of strong multiplicity one for `χ`: the forms `f(q^t)`, for the newforms
`f` of the levels `M` whose nebentypus induces `χ` and the `t` with `t M ∣ N`, are linearly
independent. Eigenvectors of the good Hecke operators with different eigenvalues are
independent; those with the same eigenvalues come from a single newform `f` (by strong
multiplicity one across comparable levels and the hypothesis), and the `f(q^t)` are independent
by their `q`-expansions. -/
lemma linearIndependent_levelRaise_of_incomparableLevelMultiplicityOneChar
    (h : IncomparableLevelMultiplicityOneChar k χ) :
    LinearIndependent ℂ fun j : {j : Σ i : LevelRaiseIndex N, Newform i.1.1 k //
      j.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd j.1.2)) = χ} ↦
        CuspForm.levelRaise j.1.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd j.1.1.2)
          j.1.2.toCuspForm := by
  classical
  let J : Type := {j : Σ i : LevelRaiseIndex N, Newform i.1.1 k //
    j.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd j.1.2)) = χ}
  let v : J → CuspForm ((Gamma1 N).map (mapGL ℝ)) k := fun j ↦
    CuspForm.levelRaise j.1.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd j.1.1.2) j.1.2.toCuspForm
  -- the good Hecke operators, and the eigenvalues of each `v j`
  let T : {p : ℕ // p.Prime ∧ p.Coprime N} → End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    fun p ↦ have : NeZero p.1 := ⟨p.2.1.ne_zero⟩
      heckeTCuspNat k p.1
  let sig : J → {p : ℕ // p.Prime ∧ p.Coprime N} → ℂ := fun j p ↦
    j.1.2.eigenvalue ⟨p.1, p.2.1.pos⟩ (p.2.2.coprime_dvd_right (dvd_of_mul_left_dvd j.1.1.2))
  have hmem : ∀ j, v j ∈ ⨅ o, (T o).eigenspace (sig j o) := by
    rintro ⟨⟨i, g⟩, -⟩
    exact Submodule.mem_iInf _ |>.mpr fun p ↦ End.mem_eigenspace_iff.mpr
      (g.heckeTCuspNat_levelRaise_eq_eigenvalue_smul i.2 p.2.1 p.2.2)
  -- the fibres of `sig` lie in independent joint eigenspaces
  have hspan : ∀ s, Submodule.span ℂ (Set.range fun x : {j // sig j = s} ↦ v x.1) ≤
      ⨅ o, (T o).eigenspace (s o) := fun s ↦ Submodule.span_le.mpr <| by
    rintro _ ⟨⟨j, rfl⟩, rfl⟩
    exact hmem j
  have hd : ∀ s, ∀ t : Set ({p : ℕ // p.Prime ∧ p.Coprime N} → ℂ), t.Finite →
      s ∉ t → Disjoint (Submodule.span ℂ (Set.range fun x : {j // sig j = s} ↦ v x.1))
        (⨆ s' ∈ t, Submodule.span ℂ (Set.range fun x : {j // sig j = s'} ↦ v x.1)) :=
    fun s _ _ hst ↦ ((iSupIndep_iInf_eigenspace T).disjoint_biSup hst).mono (hspan s)
      (iSup₂_mono fun s' _ ↦ hspan s')
  -- in a fibre all the newforms are one newform, raised by distinct `t`
  have hindep : ∀ s, LinearIndependent ℂ fun x : {j // sig j = s} ↦ v x.1 := by
    intro s
    rcases isEmpty_or_nonempty {j // sig j = s} with hs | hs
    · exact linearIndependent_empty_type
    rcases hs with ⟨j₀⟩
    have hsame : ∀ x : {j // sig j = s}, ((x.1.1.1.1.1, ⇑x.1.1.2.toCuspForm) : ℕ × (ℍ → ℂ)) =
        (j₀.1.1.1.1.1, ⇑j₀.1.1.2.toCuspForm) := by
      intro x
      have heig : ∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N), sig x.1 ⟨p, hp, hpN⟩ =
          sig j₀.1 ⟨p, hp, hpN⟩ := fun p hp hpN ↦ congrFun (x.2.trans j₀.2.symm) ⟨p, hp, hpN⟩
      by_cases h₁₂ : x.1.1.1.1.1 ∣ j₀.1.1.1.1.1
      · exact eq_of_dvd_of_forall_prime_eigenvalue_eq h₁₂ (dvd_of_mul_left_dvd j₀.1.1.1.2) _ _
          (x.1.2.trans j₀.1.2.symm) heig
      by_cases h₂₁ : j₀.1.1.1.1.1 ∣ x.1.1.1.1.1
      · exact (eq_of_dvd_of_forall_prime_eigenvalue_eq h₂₁ (dvd_of_mul_left_dvd x.1.1.1.2) _ _
          (j₀.1.2.trans x.1.2.symm) fun p hp hpN ↦ (heig p hp hpN).symm).symm
      · exact (h _ _ _ _ h₁₂ h₂₁ _ _ x.1.2 j₀.1.2 heig).elim
    have ht : Function.Injective fun x : {j // sig j = s} ↦ x.1.1.1.1.2 := by
      rintro ⟨⟨⟨i, g⟩, hg⟩, hx⟩ ⟨⟨⟨i', g'⟩, hg'⟩, hx'⟩ htt
      rcases Prod.mk_inj.mp ((hsame ⟨⟨_, hg⟩, hx⟩).trans (hsame ⟨⟨_, hg'⟩, hx'⟩).symm) with
        ⟨hM, hgg⟩
      have hi : i = i' := Subtype.ext (Prod.ext hM htt)
      subst hi
      have hgg' : g = g' := Newform.ext (DFunLike.coe_injective hgg)
      subst hgg'
      rfl
    have hA : (qExpansion 1 j₀.1.1.2.toCuspForm).coeff 1 ≠ 0 := by
      rw [j₀.1.1.2.isNorm]
      exact one_ne_zero
    refine LinearIndependent.of_comp ((ModularForm.qExpansionLinearMap one_pos
      (one_mem_strictPeriods_Gamma1_map N) k).comp CuspForm.toModularFormₗ) ?_
    convert PowerSeries.linearIndependent_expand ht (fun x ↦ NeZero.ne x.1.1.1.1.2) hA using 1
    funext x
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [ModularForm.qExpansionLinearMap_apply, CuspForm.toModularFormₗ_eq_coe,
      ModularFormClass.coe_modularForm, CuspForm.qExpansion_levelRaise
        (one_mem_strictPeriods_Gamma1_map _) (one_mem_strictPeriods_Gamma1_map _),
      (Prod.mk_inj.mp (hsame x)).2]
  have hfib : LinearIndependent ℂ fun ji : Σ s, {j // sig j = s} ↦ v ji.2.1 :=
    linearIndependent_iUnion_finite (ιs := fun s ↦ {j // sig j = s})
      (f := fun s (x : {j // sig j = s}) ↦ v x.1) hindep hd
  exact (linearIndependent_equiv' (Equiv.sigmaFiberEquiv sig) (f := v)
    (g := fun ji : Σ s, {j // sig j = s} ↦ v ji.2.1) rfl).mp hfib

lemma newformCharLevelRaise_le_span (i : LevelRaiseIndex N) : newformCharLevelRaise k χ i ≤
    Submodule.span ℂ ((fun j : {j : Σ i : LevelRaiseIndex N, Newform i.1.1 k //
      j.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd j.1.2)) = χ} ↦
        CuspForm.levelRaise j.1.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd j.1.1.2)
          j.1.2.toCuspForm) '' {j | j.1.1 = i}) := by
  refine iSup₂_le fun ψ hψ ↦ ?_
  rw [← span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace ψ, Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  exact ⟨⟨⟨i, g⟩, by rwa [hg]⟩, rfl, rfl⟩

/-- **The images `α_{M,d}(S_k^new(M, χ_M))` are independent** (LMFDB
`cmf.decomposition.old.gamma0chi`), given only the incomparable-level case of strong multiplicity
one for `χ`. -/
lemma iSupIndep_newformCharLevelRaise_of_incomparableLevelMultiplicityOneChar
    (h : IncomparableLevelMultiplicityOneChar k χ) : iSupIndep (newformCharLevelRaise k χ) := by
  refine iSupIndep_def.mpr fun i ↦
    ((linearIndependent_levelRaise_of_incomparableLevelMultiplicityOneChar χ h).disjoint_span_image
      (s := {j | j.1.1 = i}) (t := {j | j.1.1 ≠ i}) ?_).mono (newformCharLevelRaise_le_span χ i)
        (iSup₂_le fun i' hi' ↦ (newformCharLevelRaise_le_span χ i').trans (Submodule.span_mono ?_))
  · exact Set.disjoint_left.mpr fun j hj hj' ↦ hj' hj
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, (hj : j.1.1 = i').trans_ne hi', rfl⟩

/-- **The old-space decomposition of `S_k(N, χ)` when the levels of `χ` form a chain** (LMFDB
`cmf.decomposition.old.gamma0chi`): if any two divisors of `N` through which `χ` factors are
comparable under divisibility (for instance when `N` divided by the conductor of `χ` is a prime
power), the images `α_{M,d}(S_k^new(M, χ_M))` are independent, unconditionally; they span
`S_k(N, χ)` by `HeckeRing.GL2.Newform.iSup_newformCharLevelRaise`. -/
lemma iSupIndep_newformCharLevelRaise_of_dvd_or_dvd
    (hN : ∀ (M₁ M₂ : ℕ) (h₁ : M₁ ∣ N) (h₂ : M₂ ∣ N) (ψ₁ : (ZMod M₁)ˣ →* ℂˣ) (ψ₂ : (ZMod M₂)ˣ →* ℂˣ),
      ψ₁.comp (ZMod.unitsMap h₁) = χ → ψ₂.comp (ZMod.unitsMap h₂) = χ → M₁ ∣ M₂ ∨ M₂ ∣ M₁) :
    iSupIndep (newformCharLevelRaise k χ) :=
  iSupIndep_newformCharLevelRaise_of_incomparableLevelMultiplicityOneChar χ
    fun M₁ M₂ _ _ h₁ h₂ h₁₂ h₂₁ g₁ g₂ hχ₁ hχ₂ _ ↦ (hN M₁ M₂ h₁ h₂ g₁.χ g₂.χ hχ₁ hχ₂).elim h₁₂ h₂₁

end HeckeRing.GL2.Newform
