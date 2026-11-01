import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CharacterSpace
import TauCeti.NumberTheory.ModularForms.Newforms.MainLemma
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# The Main Lemma away from the level

Tau Ceti's Main Lemma (`TauCeti.mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero`;
Miyake, Lemma 4.6.8; Diamond–Shurman, Theorem 5.7.1) puts a cusp form of `S_k(Γ₁(N), χ)` whose
coefficients vanish at every index coprime to `N` in the old subspace. Miyake states it for an
arbitrary auxiliary integer `L`: vanishing at every index coprime to `L` suffices, the primes of
`L` not dividing `N` contributing nothing. This is the form strong multiplicity one needs when
eigenvalues are compared only away from finitely many primes, and it is proved here.

The new input is the case of one prime: a cusp form of `S_k(Γ₁(N), χ)` supported on the multiples
of a prime `ℓ ∤ N` is zero. Read at level `N ℓ`, Tau Ceti's descent writes such a form `F` as
`V_ℓ G` with `G` of level `N`; the Hecke operator `T_ℓ`, which is good at `N`, then gives
`V_ℓ F = (χ(ℓ) ℓ^{k-1})⁻¹ (T_ℓ F - G)` at level `N` again. Iterating, `V_{ℓ^m} F` lies in
`S_k(Γ₁(N), χ)` for every `m`, and vanishes to order at least `ℓ^m` at the cusp `∞`; the Sturm
bound makes it zero for large `m`, hence `F = 0`. Coprime-index filters (Tau Ceti's
`TauCeti.exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd`) then remove the extra primes one
at a time.

## Main results

* `TauCeti.eq_zero_of_qExpansionSupportedOnDvd_of_coprime`: a cusp form of `S_k(Γ₁(N), χ)`
  supported on the multiples of a prime `ℓ ∤ N` is zero.
* `TauCeti.qExpansion_coeff_eq_zero_of_forall_coprime_qExpansion_coeff_eq_zero`: a cusp form of
  `S_k(Γ₁(N), χ)` whose coefficients vanish at every index coprime to some `L ≠ 0` has
  coefficients vanishing at every index coprime to `N`.
* `TauCeti.mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero_of_ne_zero`: the Main
  Lemma with an arbitrary auxiliary integer (Miyake, Lemma 4.6.8): such a form is old.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.8.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.7.1.
-/

open Matrix SpecialLinearGroup CongruenceSubgroup UpperHalfPlane HeckeRing GL2

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {ℓ L : ℕ}
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}

lemma eq_zero_of_forall_qExpansion_coeff_eq_zero {M : ℕ} {G : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (h : ∀ n, (qExpansion 1 G).coeff n = 0) : G = 0 := by
  refine CuspForm.toModularFormₗ_injective ?_
  rw [CuspForm.toModularFormₗ_eq_coe, map_zero]
  exact (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_Gamma1_map M) _).mp
    (PowerSeries.ext fun n ↦ by simpa using h n)

lemma exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_qExpansionSupportedOnDvd
    (hℓ : 0 < ℓ) (hF : F ∈ cuspFormCharSpace k χ) (hsupp : QExpansionSupportedOnDvd ℓ F) :
    ∃ G ∈ cuspFormCharSpace k χ, ∀ n, (qExpansion 1 G).coeff n =
      (qExpansion 1 F).coeff (ℓ * n) := by
  have : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.ne'⟩
  have hNM : N ∣ N * ℓ := dvd_mul_right N ℓ
  have hℓM : ℓ ∣ N * ℓ := dvd_mul_left ℓ N
  have hdiv : N * ℓ / ℓ = N := Nat.mul_div_cancel N hℓ
  have h₁ : N ∣ N * ℓ / ℓ := dvd_of_eq hdiv.symm
  have h₂ : N * ℓ / ℓ ∣ N := dvd_of_eq hdiv
  -- read at level `N ℓ`, `F` descends along `ℓ` to level `N ℓ / ℓ = N`
  have hFχ : CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hNM) F ∈ cuspFormCharSpace k
      ((χ.comp (ZMod.unitsMap h₁)).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hℓM))) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
    exact CuspForm.restrict_mem_cuspFormCharSpace χ hNM hF
  have hχ : (χ.comp (ZMod.unitsMap h₁)).comp (ZMod.unitsMap h₂) = χ := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp, ZMod.unitsMap_self, MonoidHom.comp_id]
  rcases exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd hℓM
    (χ.comp (ZMod.unitsMap h₁)) hFχ hsupp with ⟨G, hG, hGF⟩
  refine ⟨_, hχ ▸ CuspForm.restrict_mem_cuspFormCharSpace _ h₂ hG, fun n ↦ ?_⟩
  rw [CuspForm.coe_restrict]
  exact ((hGF (ℓ * n)).trans (by rw [ite_eq_left (dvd_mul_right ℓ n),
    Nat.mul_div_cancel_left n hℓ])).symm

lemma exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_coprime (hℓ : ℓ.Prime)
    (hℓN : ℓ.Coprime N) (hF : F ∈ cuspFormCharSpace k χ) (hsupp : QExpansionSupportedOnDvd ℓ F) :
    ∃ H ∈ cuspFormCharSpace k χ, ∀ n, (qExpansion 1 H).coeff n =
      if ℓ ∣ n then (qExpansion 1 F).coeff (n / ℓ) else 0 := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rcases exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_qExpansionSupportedOnDvd
    hℓ.pos hF hsupp with ⟨G, hG, hGF⟩
  have hc : (χ (ZMod.unitOfCoprime ℓ hℓN) : ℂ) * (ℓ : ℂ) ^ (k - 1) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ.ne_zero))
  -- `T_ℓ F = U_ℓ F + χ(ℓ) ℓ^{k-1} V_ℓ F`, and `U_ℓ F = G`
  refine ⟨((χ (ZMod.unitOfCoprime ℓ hℓN) : ℂ) * (ℓ : ℂ) ^ (k - 1))⁻¹ • (heckeTCuspNat k ℓ F - G),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (heckeTCuspNat_mem_cuspFormCharSpace k χ hℓ hF) hG),
    fun n ↦ ?_⟩
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, FunLike.coe_sub,
    ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map N), map_sub,
    heckeTCuspNat_def,
    qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace k hℓ hℓN
      χ hF n, hGF n, add_sub_cancel_left, smul_eq_mul]
  split_ifs
  · exact inv_mul_cancel_left₀ hc _
  · exact mul_zero _

/-- **A cusp form supported on the multiples of a prime not dividing the level is zero**: if
`F ∈ S_k(Γ₁(N), χ)` has `a_n(F) = 0` at every `n` prime to a prime `ℓ ∤ N`, then `F = 0`. The
forms `V_{ℓ^m} F` all lie in `S_k(Γ₁(N), χ)` and vanish to order at least `ℓ^m` at `∞`, so the
Sturm bound kills them. -/
lemma eq_zero_of_qExpansionSupportedOnDvd_of_coprime (hℓ : ℓ.Prime) (hℓN : ℓ.Coprime N)
    (hF : F ∈ cuspFormCharSpace k χ) (hsupp : QExpansionSupportedOnDvd ℓ F) : F = 0 := by
  -- `V_{ℓ^(m+1)} F` lies in `S_k(Γ₁(N), χ)` for every `m`
  have hV : ∀ m : ℕ, ∃ H ∈ cuspFormCharSpace k χ, ∀ n, (qExpansion 1 H).coeff n =
      if ℓ ^ (m + 1) ∣ n then (qExpansion 1 F).coeff (n / ℓ ^ (m + 1)) else 0 := by
    intro m
    induction m with
    | zero =>
      simpa using exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_coprime hℓ hℓN hF
        hsupp
    | succ m ih =>
      rcases ih with ⟨H, hH, hHF⟩
      have hHsupp : QExpansionSupportedOnDvd ℓ H := by
        refine qExpansionSupportedOnDvd_iff.mpr (PowerSeries.isSupportedOnDvd_iff.mpr fun n hn ↦ ?_)
        rw [hHF n, ite_eq_right fun h ↦ hn ((dvd_pow_self ℓ m.succ_ne_zero).trans h)]
      rcases exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_coprime hℓ hℓN hH hHsupp
        with ⟨H', hH', hH'H⟩
      refine ⟨H', hH', fun n ↦ ?_⟩
      rw [hH'H n]
      by_cases hn : ℓ ∣ n
      · rcases hn with ⟨n, rfl⟩
        rw [ite_eq_left (dvd_mul_right ℓ n), Nat.mul_div_cancel_left n hℓ.pos, hHF n,
          pow_succ' ℓ (m + 1)]
        simp only [Nat.mul_dvd_mul_iff_left hℓ.pos, Nat.mul_div_mul_left _ _ hℓ.pos]
      · rw [ite_eq_right hn,
          ite_eq_right fun h ↦ hn ((dvd_pow_self ℓ (m + 1).succ_ne_zero).trans h)]
  -- past the Sturm bound it vanishes, and its coefficients are those of `F`
  rcases hV ((k * (Gamma1 N).index).toNat / 12) with ⟨H, -, hHF⟩
  have hH : H = 0 := by
    refine CuspForm.toModularFormₗ_injective ?_
    rw [map_zero]
    refine ModularForm.sturm_bound_finiteIndex_SL2Z _ ?_
    rw [strictWidthInfty_Gamma1]
    refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _)
      (PowerSeries.nat_le_order _ _ fun i hi ↦ ?_)
    rw [CuspForm.toModularFormₗ_eq_coe, ModularFormClass.coe_modularForm, hHF i]
    split_ifs with h
    · rw [Nat.eq_zero_of_dvd_of_lt h (hi.trans (Nat.lt_pow_self hℓ.one_lt)), Nat.zero_div]
      exact CuspFormClass.qExpansion_coeff_zero F one_pos (one_mem_strictPeriods_Gamma1_map N)
    · rfl
  refine eq_zero_of_forall_qExpansion_coeff_eq_zero fun n ↦ ?_
  have hn : (qExpansion 1 ⇑F).coeff n =
      (qExpansion 1 ⇑H).coeff (ℓ ^ ((k * (Gamma1 N).index).toNat / 12 + 1) * n) := by
    rw [hHF, ite_eq_left (dvd_mul_right _ n), Nat.mul_div_cancel_left n (pow_pos hℓ.pos _)]
  rw [hn, hH, FunLike.coe_zero, qExpansion_zero, map_zero]

lemma eq_zero_of_forall_coprime_prod_qExpansion_coeff_eq_zero {S : Finset ℕ} (hS : ∀ ℓ ∈ S, ℓ.Prime)
    (hSN : ∀ ℓ ∈ S, ℓ.Coprime N) (hF : F ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, n.Coprime (S.prod id) → (qExpansion 1 F).coeff n = 0) : F = 0 := by
  induction S using Finset.induction_on with
  | empty => exact eq_zero_of_forall_qExpansion_coeff_eq_zero fun n ↦ hvan n (by simp)
  | insert ℓ S hℓS ih =>
    rw [Finset.forall_mem_insert] at hS hSN
    rcases hS with ⟨hℓ, hS⟩
    rcases hSN with ⟨hℓN, hSN⟩
    have : NeZero (S.prod id) := ⟨Finset.prod_ne_zero_iff.mpr fun q hq ↦ (hS q hq).ne_zero⟩
    have : NeZero ((S.prod id).primeFactors.prod id) :=
      ⟨ne_zero_of_dvd_ne_zero (NeZero.ne _) (Nat.prod_primeFactors_dvd _)⟩
    have hℓP : ℓ.Coprime (S.prod id) := Nat.coprime_prod_right_iff.mpr fun q hq ↦
      (Nat.coprime_primes hℓ (hS q hq)).mpr fun h ↦ hℓS (h ▸ hq)
    -- the coprime-to-`∏ S` filter of `F` is supported on the multiples of `ℓ`, so it is zero
    rw [Finset.prod_insert hℓS] at hvan
    rcases exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd _
      (CuspForm.restrict_mem_cuspFormCharSpace χ (dvd_mul_left N (S.prod id)) hF) hℓ
      (Nat.primeFactors_mono (dvd_mul_right _ N) (NeZero.ne _)) hvan with ⟨g, hg, hgsupp, hgF⟩
    have hg0 : g = 0 := eq_zero_of_qExpansionSupportedOnDvd_of_coprime hℓ
      ((hℓP.coprime_dvd_right (Nat.prod_primeFactors_dvd _)).mul_right (hℓP.mul_right hℓN)) hg
      hgsupp
    refine ih hS hSN fun n hn ↦ ?_
    have hn' : (qExpansion 1 ⇑F).coeff n = (qExpansion 1 ⇑g).coeff n := by
      rw [hgF n, ite_eq_left hn, CuspForm.coe_restrict]
    rw [hn', hg0, FunLike.coe_zero, qExpansion_zero, map_zero]

/-- **The Main Lemma away from the level, on coefficients**: if `F ∈ S_k(Γ₁(N), χ)` has
`a_n(F) = 0` at every `n` coprime to some `L ≠ 0`, then `a_n(F) = 0` at every `n` coprime to
`N`. The coprime-to-`N` filter of `F` is supported on the indices divisible by a prime of `L` not
dividing `N`, and such a form is zero. -/
lemma qExpansion_coeff_eq_zero_of_forall_coprime_qExpansion_coeff_eq_zero (hL : L ≠ 0)
    (hF : F ∈ cuspFormCharSpace k χ) (hvan : ∀ n, n.Coprime L → (qExpansion 1 F).coeff n = 0)
    {n : ℕ} (hn : n.Coprime N) : (qExpansion 1 F).coeff n = 0 := by
  have : NeZero (N.primeFactors.prod id) :=
    ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) N.prod_primeFactors_dvd⟩
  rcases exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime χ hF subset_rfl with
    ⟨g, hg, hgF⟩
  have hg0 : g = 0 := by
    refine eq_zero_of_forall_coprime_prod_qExpansion_coeff_eq_zero
      (S := L.primeFactors \ N.primeFactors)
      (fun q hq ↦ Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1) (fun q hq ↦ ?_) hg
      fun m hm ↦ ?_
    · rcases Finset.mem_sdiff.mp hq with ⟨hqL, hqN⟩
      have hq' : q.Coprime N :=
        (Nat.prime_of_mem_primeFactors hqL).coprime_iff_not_dvd.mpr fun h ↦
          hqN (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hqL, h, NeZero.ne N⟩)
      exact (hq'.coprime_dvd_right (Nat.prod_primeFactors_dvd N)).mul_right hq'
    · rw [hgF m]
      split_ifs with hmN
      · refine hvan m (Nat.coprime_of_dvd fun q hq hqm hqL ↦ ?_)
        by_cases hqN : q ∣ N
        · exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hmN hqm hqN)
        · exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hm hqm (Finset.dvd_prod_of_mem id
            (Finset.mem_sdiff.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqL, hL⟩,
              fun h ↦ hqN (Nat.dvd_of_mem_primeFactors h)⟩)))
      · rfl
  have hn' : (qExpansion 1 ⇑F).coeff n = (qExpansion 1 ⇑g).coeff n := by
    rw [hgF n, ite_eq_left hn]
  rw [hn', hg0, FunLike.coe_zero, qExpansion_zero, map_zero]

/-- **The Main Lemma with an arbitrary auxiliary integer** (Miyake, Lemma 4.6.8): a cusp form of
`S_k(Γ₁(N), χ)` whose coefficients vanish at every index coprime to some `L ≠ 0` lies in the old
subspace. -/
lemma mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero_of_ne_zero (hL : L ≠ 0)
    (hF : F ∈ cuspFormCharSpace k χ) (hvan : ∀ n, n.Coprime L → (qExpansion 1 F).coeff n = 0) :
    F ∈ cuspFormsOld N k :=
  mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero hF fun _ hn ↦
    qExpansion_coeff_eq_zero_of_forall_coprime_qExpansion_coeff_eq_zero hL hF hvan hn

end TauCeti
