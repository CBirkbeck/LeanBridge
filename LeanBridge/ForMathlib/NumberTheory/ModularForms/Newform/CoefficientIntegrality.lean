import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Gamma1
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Finite
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import TauCeti.NumberTheory.ModularForms.Newforms.NumberField
import TauCeti.NumberTheory.ModularForms.QExpansion.Positive

/-!
# The coefficients of a newform are algebraic integers, in every weight

Tau Ceti proves that the Fourier coefficients of a newform of weight at least two are algebraic
integers, as the integral Hecke algebra acts on modular symbols. This file adds weight one. For a
newform `f` of weight `k ≥ 1`, the form `f E₄` has weight at least two. The integral Hecke algebra
in that weight is a finite `ℤ`-module, and the coefficient `a_m(T_p g)` of a form `g` of nebentypus
`χ` is `a_{pm}(g) + χ(p) p^(k-1) a_{m/p}(g)`, so the coefficients of `f E₄` lie in a finitely
generated `ℤ`-module, and so do those of `f`, as `E₄ = 1 + 240 q + ⋯` has integer coefficients. The
Hecke recurrence at a prime `p` then makes a finitely generated `ℤ`-module stable under
multiplication by `a_p`. There are no newforms of weight at most zero.

That the coefficients of `E₄` are integers is a short helper here; it is on Tau Ceti's main as
`TauCeti.ModularForm.exists_E₄_qExpansion_coeff_eq_intCast`, not at the pin, and can be replaced by
it after the bump.

## Main results

* `TauCeti.exists_fg_forall_qExpansion_coeff_mem`: in weight at least two, the coefficients of a
  form of nebentypus `χ` lie in a finitely generated `ℤ`-module.
* `HeckeRing.GL2.Newform.one_le_weight`: newforms have positive weight.
* `HeckeRing.GL2.Newform.isIntegral_coeff`: the coefficients of a newform are algebraic integers.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup HeckeRing GL2 EisensteinSeries TauCeti
  GaloisAction Matrix SpecialLinearGroup Finset Module

open scoped MatrixGroups ArithmeticFunction.sigma

namespace TauCeti

variable {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

lemma natCast_zpow_mem (hk : 1 ≤ k) (S : Subalgebra ℤ ℂ) (p : ℕ) : (p : ℂ) ^ (k - 1) ∈ S := by
  have hk' : k - 1 = ((k - 1).toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  rw [hk', zpow_natCast]
  exact pow_mem (natCast_mem S p) _

lemma mem_cuspFormCharSpace_of_coe_eq_mul {w : ℤ} {h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hh : h ∈ cuspFormCharSpace k χ) (E : ModularForm 𝒮ℒ w)
    {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) (k + w)} (hG : ⇑G = ⇑h * ⇑E) :
    G ∈ cuspFormCharSpace (k + w) χ := by
  rw [mem_cuspFormCharSpace_iff]
  intro d
  rcases Gamma0Map_toHomUnits_surjective (N := N) d with ⟨γ, hγ⟩
  refine DFunLike.coe_injective ?_
  have hE : ⇑E ∣[w] (γ : SL(2, ℤ)) = ⇑E := E.slash_action_eq' _ ⟨γ, rfl⟩
  have hh₁ : ⇑h ∣[k] (γ : SL(2, ℤ)) = ⇑((χ d : ℂ) • h) := by
    rw [← diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ d hh]
    exact (coe_diamondOpCusp k d γ hγ h).symm
  have hG₁ : ⇑(diamondOpCusp (k + w) d G) = ⇑G ∣[k + w] (γ : SL(2, ℤ)) :=
    coe_diamondOpCusp (k + w) d γ hγ G
  rw [diamondOpCuspHom_apply, hG₁, hG, mul_slash_SL2, hE, hh₁, FunLike.coe_smul, FunLike.coe_smul,
    hG, smul_mul_assoc]

variable [NeZero N] {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}

lemma qExpansion_coeff_prime_mul_of_mem_cuspFormCharSpace {p : ℕ} (hp : p.Prime)
    (hg : g ∈ cuspFormCharSpace k χ) (m : ℕ) : (qExpansion 1 g).coeff (p * m) =
      (qExpansion 1 (heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) g)).coeff m -
        if p ∣ m then (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 g).coeff (m / p) else 0 := by
  have h : (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p)
      (⟨g, hg⟩ : cuspFormCharSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
        ∑ d ∈ (m.gcd p).divisors, (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) d *
          (d : ℂ) ^ (k - 1) * (qExpansion 1 g).coeff (m * p / d ^ 2) :=
    qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 hp.ne_zero _ m
  rw [heckeTCompositeGamma0_prime N hp, coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp]
    at h
  rw [h]
  by_cases hpm : p ∣ m
  · rcases hpm with ⟨t, rfl⟩
    have hgcd : (p * t).gcd p = p := Nat.gcd_mul_right_left t p
    have ht : p * t * p / p ^ 2 = t := by
      rw [pow_two, mul_right_comm]
      exact Nat.mul_div_cancel_left t (Nat.mul_pos hp.pos hp.pos)
    rw [hgcd, hp.divisors, Finset.sum_pair hp.one_lt.ne, ht, ite_eq_left (Dvd.intro t rfl),
      Nat.mul_div_cancel_left t hp.pos]
    simp [mul_comm p]
  · have hgcd : m.gcd p = 1 := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpm)
    rw [hgcd, Nat.divisors_one, Finset.sum_singleton, ite_eq_right hpm]
    simp [mul_comm p]

lemma map_mem_cuspFormCharSpace_of_mem_heckeTCuspPrimeAlgebra
    {t : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)} (ht : t ∈ heckeTCuspPrimeAlgebra N k)
    (hg : g ∈ cuspFormCharSpace k χ) : t g ∈ cuspFormCharSpace k χ := by
  induction ht using Algebra.adjoin_induction generalizing g with
  | mem t ht =>
    rcases ht with ⟨p, rfl⟩
    exact heckeTCuspNat_mem_cuspFormCharSpace k χ p.2 hg
  | algebraMap r =>
    simpa using (cuspFormCharSpace k χ).smul_of_tower_mem r hg
  | add t t' _ _ ih ih' => exact add_mem (ih hg) (ih' hg)
  | mul t t' _ _ ih ih' => exact ih (ih' hg)

/-- **The coefficients of a form of nebentypus `χ` lie in a finitely generated `ℤ`-module**, in
weight at least two: for the finite `ℤ`-algebra `T` generated by the Hecke operators `T_p`, and the
ring `S` generated by the values of `χ`, they lie in the `S`-module generated by the `a₁(t g)`,
for `t ∈ T`. -/
lemma exists_fg_forall_qExpansion_coeff_mem (hk : 2 ≤ k) (hg : g ∈ cuspFormCharSpace k χ) :
    ∃ M : Submodule ℤ ℂ, M.FG ∧ ∀ n, (qExpansion 1 g).coeff n ∈ M := by
  have h1 : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map N
  have hfin : Module.Finite ℤ (heckeTCuspPrimeAlgebra N k) := heckeTCuspPrimeAlgebra_finite N k hk
  let S : Subalgebra ℤ ℂ := Algebra.adjoin ℤ (Set.range fun u : (ZMod N)ˣ ↦ (χ u : ℂ))
  have hSfg : (Subalgebra.toSubmodule S).FG := fg_adjoin_of_finite (Set.finite_range _) <| by
    rintro _ ⟨u, rfl⟩
    exact χ.isIntegral_coe_apply u
  let φ : heckeTCuspPrimeAlgebra N k →ₗ[ℤ] ℂ :=
    { toFun t := CuspForm.qExpansionCoeffₗ one_pos h1 k 1
        ((t : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) g)
      map_add' t t' := by simp only [AddMemClass.coe_add, LinearMap.add_apply, map_add]
      map_smul' n t := by simp }
  let M : Submodule ℤ ℂ := Subalgebra.toSubmodule S * LinearMap.range φ
  have hM : M.FG := hSfg.mul <| LinearMap.range_eq_map φ ▸ Finite.fg_top.map φ
  have hsmul {s : ℂ} (hs : s ∈ S) {x : ℂ} (hx : x ∈ M) : s * x ∈ M := by
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      have hsa : s * a ∈ S := mul_mem hs ha
      rw [← mul_assoc]
      exact Submodule.mul_mem_mul hsa hb
    | add x _ y _ ihx ihy =>
      rw [mul_add]
      exact add_mem ihx ihy
  have hc {p : ℕ} (hp : p.Prime) :
      (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) ∈ S := by
    have hχ : (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p ∈ S :=
      MulChar.apply_mem_of_forall_unit _ S (fun u ↦ by
        rw [MulChar.ofUnitHom_coe]
        exact Algebra.subset_adjoin ⟨u, rfl⟩) _
    exact mul_mem hχ (natCast_zpow_mem (by omega) S p)
  have key (n : ℕ) : ∀ t : heckeTCuspPrimeAlgebra N k, (qExpansion 1
      ((t : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) g)).coeff n ∈ M := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t
      have ht : (t : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) g ∈
          cuspFormCharSpace k χ :=
        map_mem_cuspFormCharSpace_of_mem_heckeTCuspPrimeAlgebra t.2 hg
      rcases n with _ | _ | n
      · rw [CuspFormClass.qExpansion_coeff_zero _ one_pos h1]
        exact zero_mem M
      · have h₁ : (1 : ℂ) * φ t ∈ M := Submodule.mul_mem_mul (one_mem S) ⟨t, rfl⟩
        rw [one_mul] at h₁
        simpa [φ] using h₁
      · let p : ℕ := (n + 1 + 1).minFac
        have hp : p.Prime := Nat.minFac_prime (by omega)
        rcases Nat.minFac_dvd (n + 1 + 1) with ⟨m, hm⟩
        have hmlt : m < n + 1 + 1 := by
          have hp₂ : 2 ≤ p := hp.two_le
          have hm₀ : 0 < m := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hm
          nlinarith
        have hp₁ : p * m = n + 1 + 1 := hm.symm
        rw [← hp₁, qExpansion_coeff_prime_mul_of_mem_cuspFormCharSpace hp ht m]
        refine sub_mem ?_ ?_
        · let T : heckeTCuspPrimeAlgebra N k := ⟨heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩),
            heckeTCuspNat_mem_heckeTCuspPrimeAlgebra N k hp⟩ * t
          have hT : (qExpansion 1
              ((T : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) g)).coeff m ∈ M :=
            ih m hmlt T
          exact hT
        · split_ifs with hpm
          · exact hsmul (hc hp) (ih (m / p) ((Nat.div_le_self m p).trans_lt hmlt) t)
          · exact zero_mem M
  refine ⟨M, hM, fun n ↦ ?_⟩
  simpa using key n 1

end TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)

lemma exists_qExpansion_E₄_coeff_eq_intCast (j : ℕ) : ∃ e : ℤ, (qExpansion 1 E₄).coeff j = e := by
  have hb : bernoulli 4 = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩]
  split_ifs
  · exact ⟨1, by simp⟩
  · refine ⟨240 * σ 3 j, ?_⟩
    norm_num [hb]

lemma exists_fg_forall_coeff_mem (hk : 1 ≤ k) :
    ∃ M : Submodule ℤ ℂ, M.FG ∧ ∀ n, (qExpansion 1 f.toCuspForm).coeff n ∈ M := by
  have h1 : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map N
  rcases (isCuspForm_coe f.toCuspForm).mul_isForm
    ((isForm_coe E₄).restrict (Subgroup.map_le_range _ _)) with ⟨G, hG⟩
  rcases exists_fg_forall_qExpansion_coeff_mem (by omega)
    (mem_cuspFormCharSpace_of_coe_eq_mul f.mem_charSpace E₄ hG) with ⟨M, hM, hcoeff⟩
  have hQ : qExpansion 1 G = qExpansion 1 f.toCuspForm * qExpansion 1 E₄ := by
    rw [hG]
    exact qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f.toCuspForm one_pos h1)
      (ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL)
  refine ⟨M, hM, fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h : (qExpansion 1 G).coeff n ∈ M := hcoeff n
    rw [hQ, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Nat.sub_self, E_qExpansion_coeff_zero _ ⟨2, rfl⟩, mul_one] at h
    refine (add_mem_cancel_left (Submodule.sum_mem _ fun i hi ↦ ?_)).mp h
    rcases exists_qExpansion_E₄_coeff_eq_intCast (n - i) with ⟨e, he⟩
    rw [he, mul_comm, ← zsmul_eq_mul]
    exact M.smul_mem e (ih i (Finset.mem_range.mp hi))

lemma ofUnitHom_apply_mul_zpow_mem (hk : 1 ≤ k) (p : ℕ) :
    (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) ∈ integralClosure ℤ ℂ :=
  mul_mem (MulChar.apply_mem_of_forall_unit _ _ (fun u ↦ by
    rw [MulChar.ofUnitHom_coe]
    exact f.χ.isIntegral_coe_apply u) _) (natCast_zpow_mem hk _ p)

lemma isIntegral_coeff_prime (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime) :
    IsIntegral ℤ ((qExpansion 1 f.toCuspForm).coeff p) := by
  rcases f.exists_fg_forall_coeff_mem hk with ⟨M, hM, hcoeff⟩
  let c : ℂ := (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1)
  have hc : IsIntegral ℤ c := f.ofUnitHom_apply_mul_zpow_mem hk p
  let S : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {c}
  have hSfg : (Subalgebra.toSubmodule S).FG := hc.fg_adjoin_singleton
  let a : ℕ → ℂ := fun j ↦ (qExpansion 1 f.toCuspForm).coeff (p ^ j)
  let V : Submodule ℤ ℂ := Submodule.span ℤ (Set.range a)
  have hV : V.FG := isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian M hM) V <|
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun j ↦ hcoeff _
  let U : Submodule ℤ ℂ := Subalgebra.toSubmodule S * V
  have hmem {s : ℂ} (hs : s ∈ S) {v : ℂ} (hv : v ∈ V) : s * v ∈ U :=
    Submodule.mul_mem_mul hs hv
  have hcS : c ∈ S := Algebra.subset_adjoin rfl
  have ha₀ : a 0 = 1 := by simp [a]
  have hstep {v : ℂ} (hv : v ∈ V) : a 1 * v ∈ U := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨j, rfl⟩
      rcases j with _ | r
      · rw [ha₀, mul_one]
        simpa using hmem (one_mem S) (Submodule.subset_span ⟨1, rfl⟩)
      · have hrec : (qExpansion 1 f.toEigenform.toCuspForm).coeff (p ^ (r + 2)) =
            (qExpansion 1 f.toEigenform.toCuspForm).coeff p *
              (qExpansion 1 f.toEigenform.toCuspForm).coeff (p ^ (r + 1)) -
                (MulChar.ofUnitHom f.toEigenform.χ : DirichletCharacter ℂ N) p *
                  (p : ℂ) ^ (k - 1) * (qExpansion 1 f.toEigenform.toCuspForm).coeff (p ^ r) :=
          f.toEigenform.qExpansion_coeff_prime_pow_add_two f.toEigenform_qExpansion_coeff_one hp r
        rw [toEigenform_toCuspForm, toEigenform_χ] at hrec
        have hrec' : a 1 * a (r + 1) = a (r + 2) + c * a r := by
          simp only [a, pow_one, hrec]
          ring1
        rw [hrec']
        refine add_mem ?_ (hmem hcS (Submodule.subset_span ⟨r, rfl⟩))
        simpa using hmem (one_mem S) (Submodule.subset_span ⟨r + 2, rfl⟩)
    | zero =>
      rw [mul_zero]
      exact zero_mem U
    | add x y _ _ ihx ihy =>
      rw [mul_add]
      exact add_mem ihx ihy
    | smul n x _ ihx =>
      rw [mul_smul_comm]
      exact U.smul_mem n ihx
  have hU : U ≠ ⊥ := fun h ↦ by
    have h₁ : (1 : ℂ) * a 0 ∈ U := hmem (one_mem S) (Submodule.subset_span ⟨0, rfl⟩)
    rw [h, ha₀, mul_one, Submodule.mem_bot] at h₁
    exact one_ne_zero h₁
  have hfix (u : ℂ) (hu : u ∈ U) : a 1 • u ∈ U := by
    induction hu using Submodule.mul_induction_on' with
    | mem_mul_mem s hs v hv =>
      have h₂ : a 1 * v ∈ U := hstep hv
      have hsmul : ∀ w ∈ U, s * w ∈ U := fun w hw ↦ by
        induction hw using Submodule.mul_induction_on' with
        | mem_mul_mem s' hs' v' hv' =>
          have hss' : s * s' ∈ S := mul_mem hs hs'
          rw [← mul_assoc]
          exact hmem hss' hv'
        | add x _ y _ ihx ihy =>
          rw [mul_add]
          exact add_mem ihx ihy
      rw [smul_eq_mul, mul_left_comm]
      exact hsmul _ h₂
    | add x _ y _ ihx ihy =>
      rw [smul_add]
      exact add_mem ihx ihy
  simpa [a] using isIntegral_of_smul_mem_submodule U hU (hSfg.mul hV) (a 1) hfix

/-- **Newforms have positive weight**: a cusp form of negative weight vanishes, and one of weight
zero is constant. -/
lemma one_le_weight (g : Newform N k) : 1 ≤ k := by
  by_contra hk
  let G : ModularForm ((Gamma1 N).map (mapGL ℝ)) k := g.toCuspForm
  have hG : (qExpansion 1 G).coeff 1 ≠ 0 := g.isNorm.trans_ne one_ne_zero
  have hk₀ : k ≠ 0 := ModularForm.weight_ne_zero_of_pos_qExpansion_coeff_ne_zero one_pos
    (one_mem_strictPeriods_Gamma1_map N) one_pos hG
  have h : G = 0 := isZero_of_neg_weight (by omega) _
  exact g.ne_zero <| CuspForm.ext fun τ ↦ DFunLike.congr_fun h τ

/-- **The coefficients of a newform are algebraic integers** (LMFDB `cmf.embedding`), in every
weight. Tau Ceti's `HeckeRing.GL2.Newform.isIntegral_qExpansion_coeff` is the case of weight at
least two. -/
lemma isIntegral_coeff (n : ℕ) : IsIntegral ℤ ((qExpansion 1 f.toCuspForm).coeff n) := by
  have hk : 1 ≤ k := f.one_le_weight
  have hn : (qExpansion 1 f.toEigenform.toCuspForm).coeff n ∈ integralClosure ℤ ℂ :=
    f.toEigenform.qExpansion_coeff_mem_of_forall_prime f.toEigenform_qExpansion_coeff_one
      (integralClosure ℤ ℂ) (fun p hp ↦ by
        rw [toEigenform_toCuspForm]
        exact f.isIntegral_coeff_prime hk hp) (fun p _ ↦ by
        rw [toEigenform_χ]
        exact f.ofUnitHom_apply_mul_zpow_mem hk p) n
  rw [toEigenform_toCuspForm] at hn
  exact hn

end HeckeRing.GL2.Newform
