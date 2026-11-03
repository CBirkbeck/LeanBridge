import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.Basic
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.Discriminant
import TauCeti.NumberTheory.ModularForms.Fricke.Normalized

/-!
# Modular forms satisfy the hypotheses of Weil's converse theorem

This is the direct half of `ModularForm.HasWeilFunctionalEquations.modularForm_mem`, and it shows
that the hypotheses of that theorem are the right ones, constants and poles included: every modular
form of positive weight, level `N` and character `χ`, Eisenstein series included, satisfies them,
with `a` its Fourier coefficients and `b` those of its normalised Fricke image.

Hecke's direct theorem is Mellin's functional equation, which Mathlib proves for a `WeakFEPair`. The
functions `t ↦ F(i t)` and `t ↦ G(i t / A)` form such a pair, whose poles are exactly those of
`ModularForm.addPoles`, and whose entire part is bounded on vertical strips as a Mellin transform.
For the twists, the law comes from `ModularForm.hasTwistedTransformation_of_nebentypus` and
`ModularForm.hasTwistedTransformation_iff_expSum_slash_frickeGL`.

Tau Ceti's main, but not its pin, has `TauCeti.FEPairWithLevel`, which packages the rescaling by `A`
done here in `ModularForm.weakFEPairOfSlash`.

## Main definitions

* `ModularForm.weakFEPairOfSlash`: the `WeakFEPair` of two exponential sums related by `W_A`.

## Main results

* `ModularForm.HasFunctionalEquation.of_expSum_slash_frickeGL`: Hecke's direct theorem, from the
  Fricke law to the functional equation with its poles.
* `ModularForm.hasFunctionalEquation_iff_expSum_slash_frickeGL`: Hecke's theorem, both directions.
* `ModularForm.hasWeilFunctionalEquations_of_nebentypus`: the nebentypus law and the Fricke law
  imply the hypotheses of Weil's converse theorem.
* `ModularForm.hasWeilFunctionalEquations_qExpansion_coeff`: every `f ∈ M_k(N, χ)`, `k > 0`,
  satisfies them.
* `ModularForm.hasWeilFunctionalEquations_discriminant`: so does the discriminant `Δ`.
-/

open Matrix hiding zpow_neg

open Asymptotics Complex CongruenceSubgroup Filter Function MeasureTheory Set TauCeti
  GeneralLinearGroup SpecialLinearGroup SlashInvariantForm

open scoped Real Manifold ModularForm MatrixGroups

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {a b c : ℕ → ℂ} {k : ℤ} {A N r : ℕ} {ε : ℂ} {B x y : ℝ} {φ : ℝ → ℂ} {s : ℂ} {F : Type*}
    [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {χ : DirichletCharacter ℂ N}

lemma norm_mellin_le (hx : MellinConvergent φ x) (hy : MellinConvergent φ y) (h1 : x ≤ s.re)
    (h2 : s.re ≤ y) : ‖mellin φ s‖ ≤
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((x : ℂ) - 1) • φ t‖ + ‖(t : ℂ) ^ ((y : ℂ) - 1) • φ t‖ := by
  refine norm_integral_le_of_norm_le (hx.norm.add hy.norm)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t (ht : 0 < t) ↦ ?_))
  simp only [norm_smul, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  simp only [norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, ofReal_re]
  have h3 : 0 ≤ t ^ (x - 1) := (Real.rpow_pos_of_pos ht _).le
  have h4 : 0 ≤ t ^ (y - 1) := (Real.rpow_pos_of_pos ht _).le
  rcases le_total 1 t with h | h
  · have h5 : t ^ (s.re - 1) ≤ t ^ (y - 1) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    linarith
  · have h5 : t ^ (s.re - 1) ≤ t ^ (x - 1) := Real.rpow_le_rpow_of_exponent_ge ht h (by linarith)
    linarith

private lemma isBigO_resToImagAxis_expSum_sub (hc : HasPolyGrowth c) (hB : 0 < B) (q : ℝ) :
    (fun t : ℝ ↦ resToImagAxis (expSum c) (t / B) - c 0) =O[atTop] (· ^ q) := by
  rcases hc.update_zero with ⟨C, m, hC⟩
  rcases exists_nat_ge (-q) with ⟨M₀, hM₀⟩
  rcases exists_norm_expSum_le (M := m + 2 + M₀) hC (update_self _ _ _) (by omega) with ⟨K, hK⟩
  refine IsBigO.of_bound (|K| * B ^ (m + 2 + M₀)) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have hy : 0 < t / B := div_pos ht0 hB
  have him : 0 < (I * ((t / B : ℝ) : ℂ)).im := by simpa using hy
  have h1 : resToImagAxis (expSum c) (t / B) - c 0 =
      expSum (update c 0 0) ⟨I * ((t / B : ℝ) : ℂ), him⟩ := by
    rw [resToImagAxis_of_pos _ hy, expSum_eq_add_expSum_update hc, add_sub_cancel_left]
  have h2 : ‖expSum (update c 0 0) ⟨I * ((t / B : ℝ) : ℂ), him⟩‖ ≤
      K * (t / B) ^ (-((m + 2 + M₀ : ℕ) : ℝ)) := by
    have h3 : (⟨I * ((t / B : ℝ) : ℂ), him⟩ : ℍ).im = t / B := by
      simp
    simpa only [h3] using hK ⟨I * ((t / B : ℝ) : ℂ), him⟩
  have h5 :
      (t / B) ^ (-((m + 2 + M₀ : ℕ) : ℝ)) = B ^ (m + 2 + M₀) * t ^ (-((m + 2 + M₀ : ℕ) : ℝ)) := by
    rw [Real.div_rpow ht0.le hB.le, Real.rpow_neg hB.le, Real.rpow_natCast]
    field_simp
  have h6 : t ^ (-((m + 2 + M₀ : ℕ) : ℝ)) ≤ t ^ q := by
    refine Real.rpow_le_rpow_of_exponent_le ht ?_
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h7 : 0 ≤ B ^ (m + 2 + M₀) := (pow_pos hB _).le
  rw [h1, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), mul_assoc]
  rw [h5] at h2
  exact h2.trans (mul_le_mul (le_abs_self K) (mul_le_mul_of_nonneg_left h6 h7)
    (mul_nonneg h7 (Real.rpow_nonneg ht0.le _)) (abs_nonneg K))

private lemma exists_mellin_resToImagAxis_expSum_sub (hc : HasPolyGrowth c) (hB : 0 < B) : ∃ σ₁ : ℝ,
    ∀ s : ℂ, σ₁ < s.re → mellin (fun t : ℝ ↦ resToImagAxis (expSum c) (t / B) - c 0) s =
      (B : ℂ) ^ s * completedLSeries c s := by
  rcases hc.update_zero with ⟨C, m, hC⟩
  refine ⟨(m : ℝ) + 2, fun s hs ↦ ?_⟩
  have h1 : mellin (resToImagAxis (expSum (update c 0 0))) s = completedLSeries c s :=
    (mellin_resToImagAxis_expSum hC (update_self _ _ _) hs).trans completedLSeries_update
  have h2 : mellin (fun t : ℝ ↦ resToImagAxis (expSum c) (t / B) - c 0) s =
      mellin (fun t : ℝ ↦ resToImagAxis (expSum (update c 0 0)) (t * B⁻¹)) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    have hy : 0 < t * B⁻¹ := mul_pos ht (inv_pos.mpr hB)
    simp only [div_eq_mul_inv t B]
    rw [resToImagAxis_of_pos _ hy, resToImagAxis_of_pos _ hy, expSum_eq_add_expSum_update hc,
      add_sub_cancel_left]
  have harg : (B : ℂ).arg ≠ π := by
    rw [arg_ofReal_of_nonneg hB.le]
    exact Real.pi_pos.ne
  rw [h2, mellin_comp_mul_right _ s (inv_pos.mpr hB), h1, smul_eq_mul, ofReal_inv,
    inv_cpow _ _ harg, cpow_neg, inv_inv]

private lemma continuousOn_resToImagAxis_div (hc : HasPolyGrowth c) (hB : 0 < B) :
    ContinuousOn (fun t : ℝ ↦ resToImagAxis (expSum c) (t / B)) (Ioi 0) :=
  hc.continuousOn_resToImagAxis.comp (continuousOn_id.div_const B) fun _ ht ↦ div_pos ht hB

variable [NeZero A]

/-- The **`WeakFEPair` of two exponential sums related by `W_A`**: if `F = ∑ a n e(n z)` and
`G = ∑ b n e(n z)` satisfy `F ∣[k] W_A = ε i ^ (-k) A ^ (k / 2 - 1) G`, the functions `t ↦ F(i t)`
and `t ↦ G(i t / A)`, with weight `k`, root number `ε A ^ (-k / 2)` and constant terms `a 0`,
`b 0`. -/
noncomputable def weakFEPairOfSlash (ha : HasPolyGrowth a) (hb : HasPolyGrowth b) (hk : 0 < k)
    (hε : ε ≠ 0)
    (h : expSum a ∣[k] frickeGL ℝ A = (ε * I ^ (-k) * (A : ℂ) ^ ((k : ℂ) / 2 - 1)) • expSum b) :
    WeakFEPair ℂ where
  f t := resToImagAxis (expSum a) (t / 1)
  g t := resToImagAxis (expSum b) (t / A)
  k := k
  ε := ε * (A : ℂ) ^ (-(k : ℂ) / 2)
  f₀ := a 0
  g₀ := b 0
  hf_int := (continuousOn_resToImagAxis_div ha one_pos).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_resToImagAxis_div hb
    (Nat.cast_pos.mpr (NeZero.pos A))).locallyIntegrableOn measurableSet_Ioi
  hk := by exact_mod_cast hk
  hε := mul_ne_zero hε (cpow_ne_zero_iff_of_exponent_ne_zero
    (div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hk.ne')) two_ne_zero) |>.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne A)))
  h_feq x hx := by
    have hx' : 0 < x := hx
    have hA : (0 : ℝ) < A := Nat.cast_pos.mpr (NeZero.pos A)
    have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
    have hsc : ((Real.sqrt A : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx'.ne'
    have hss : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA.le
    have h1 : resToImagAxis (expSum a ∣[k] frickeGL ℝ A) (x / Real.sqrt A / Real.sqrt A) =
        ((Real.sqrt A : ℝ) : ℂ) ^ (k - 2) * I ^ (-k) * ((x / Real.sqrt A : ℝ) : ℂ) ^ (-k) *
          resToImagAxis (expSum a) (1 / (x / Real.sqrt A) / Real.sqrt A) :=
      UpperHalfPlane.resToImagAxis_slash_frickeGL _ (div_pos hx' hs)
    have e1 : x / Real.sqrt A / Real.sqrt A = x / A := by
      rw [div_div, hss]
    have e2 : 1 / (x / Real.sqrt A) / Real.sqrt A = 1 / x := by
      field_simp
    rw [e1, e2, h, resToImagAxis_smul, Pi.smul_apply, smul_eq_mul,
      natCast_cpow_div_two_sub_one] at h1
    have hQ : ((Real.sqrt A : ℝ) : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ hsc
    have hI : I ^ (-k) ≠ 0 := zpow_ne_zero _ I_ne_zero
    have e3 : ((x / Real.sqrt A : ℝ) : ℂ) ^ (-k) * ((x ^ (k : ℝ) : ℝ) : ℂ) =
        ((Real.sqrt A : ℝ) : ℂ) ^ k := by
      have h3 : (x : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hxc
      have h4 : ((Real.sqrt A : ℝ) : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hsc
      rw [Real.rpow_intCast, ofReal_zpow, ofReal_div, div_zpow, zpow_neg, zpow_neg]
      field_simp
    have e4 : (A : ℂ) ^ (-(k : ℂ) / 2) * ((Real.sqrt A : ℝ) : ℂ) ^ k = 1 := by
      rw [neg_div, cpow_neg, natCast_cpow_div_two_eq]
      exact inv_mul_cancel₀ (zpow_ne_zero _ hsc)
    rw [div_one, smul_eq_mul]
    refine mul_left_cancel₀ (mul_ne_zero hQ hI) ?_
    linear_combination (-(((x ^ (k : ℝ) : ℝ) : ℂ) * (A : ℂ) ^ (-(k : ℂ) / 2))) * h1 -
      ((Real.sqrt A : ℝ) : ℂ) ^ (k - 2) * I ^ (-k) * resToImagAxis (expSum a) (1 / x) *
        ((A : ℂ) ^ (-(k : ℂ) / 2) * e3 + e4)
  hf_top := isBigO_resToImagAxis_expSum_sub ha one_pos
  hg_top := isBigO_resToImagAxis_expSum_sub hb (Nat.cast_pos.mpr (NeZero.pos A))

/-- **Hecke's direct theorem.** Let `a, b` be sequences of polynomial growth, `k > 0` and `ε ≠ 0`.
If `F = ∑ a n e(n z)` and `G = ∑ b n e(n z)` satisfy `F ∣[k] W_A = ε i ^ (-k) A ^ (k / 2 - 1) G`,
then `a` and `b` satisfy the functional equation `HasFunctionalEquation a b k A ε`, with the poles
of the completed Dirichlet series of `a` at `0` and `k` given by the constant terms. -/
lemma HasFunctionalEquation.of_expSum_slash_frickeGL (ha : HasPolyGrowth a) (hb : HasPolyGrowth b)
    (hk : 0 < k) (hε : ε ≠ 0)
    (h : expSum a ∣[k] frickeGL ℝ A = (ε * I ^ (-k) * (A : ℂ) ^ ((k : ℂ) / 2 - 1)) • expSum b) :
    HasFunctionalEquation a b k A ε := by
  have hA : (0 : ℝ) < A := Nat.cast_pos.mpr (NeZero.pos A)
  have hAc : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne A)
  let P : WeakFEPair ℂ := weakFEPairOfSlash ha hb hk hε h
  have hPk : (P.k : ℂ) = k := by
    simp [P, weakFEPairOfSlash]
  rcases exists_mellin_resToImagAxis_expSum_sub ha one_pos with ⟨σ₁, hσ₁⟩
  rcases exists_mellin_resToImagAxis_expSum_sub hb hA with ⟨σ₂, hσ₂⟩
  have hε' : P.ε = ε * (A : ℂ) ^ (-(k : ℂ) / 2) := rfl
  have hadd : ∀ s : ℂ, addPoles P.Λ₀ (a 0) (ε * (A : ℂ) ^ (-(k : ℂ) / 2) * b 0) k s = P.Λ s :=
    fun s ↦ by
      have hf₀ : P.f₀ = a 0 := rfl
      have hg₀ : P.g₀ = b 0 := rfl
      rw [WeakFEPair.Λ, hPk, addPoles, hε', hf₀, hg₀, smul_eq_mul, smul_eq_mul, one_div,
        div_mul_eq_mul_div, inv_mul_eq_div]
  have hconv : ∀ s : ℂ, MellinConvergent P.f_modif s := fun s ↦
    (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hk1 : (k : ℝ) ≤ max (k : ℝ) (max σ₁ σ₂) := le_max_left _ _
  have h1 : σ₁ ≤ max (k : ℝ) (max σ₁ σ₂) := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : σ₂ ≤ max (k : ℝ) (max σ₁ σ₂) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨P.Λ₀, max (k : ℝ) (max σ₁ σ₂), P.differentiable_Λ₀, fun x y ↦ ⟨_, fun s hx hy ↦
    norm_mellin_le (hconv x) (hconv y) hx hy⟩, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · have h3 : mellin (fun t : ℝ ↦ resToImagAxis (expSum a) (t / 1) - a 0) s = P.Λ s :=
      (P.hasMellin (hk1.trans_lt hs)).2
    have h4 : mellin (fun t : ℝ ↦ resToImagAxis (expSum a) (t / 1) - a 0) s =
        ((1 : ℝ) : ℂ) ^ s * completedLSeries a s :=
      hσ₁ s (h1.trans_lt hs)
    rw [hadd, ← h3, h4, ofReal_one, one_cpow, one_mul]
  · have h3 : max (k : ℝ) (max σ₁ σ₂) < ((k : ℂ) - s).re := by
      simp only [sub_re, intCast_re]
      linarith
    have h4 : mellin (fun t : ℝ ↦ resToImagAxis (expSum b) (t / A) - b 0) ((k : ℂ) - s) =
        P.symm.Λ ((k : ℂ) - s) :=
      (P.symm.hasMellin (hk1.trans_lt h3)).2
    have h5 : mellin (fun t : ℝ ↦ resToImagAxis (expSum b) (t / A) - b 0) ((k : ℂ) - s) =
        ((A : ℝ) : ℂ) ^ ((k : ℂ) - s) * completedLSeries b ((k : ℂ) - s) :=
      hσ₂ _ (h2.trans_lt h3)
    have h6 : P.Λ (P.k - ((k : ℂ) - s)) = P.ε • P.symm.Λ ((k : ℂ) - s) := P.functional_equation _
    rw [hPk, sub_sub_cancel] at h6
    have h7 : (A : ℂ) ^ (-(k : ℂ) / 2) * (A : ℂ) ^ ((k : ℂ) - s) = (A : ℂ) ^ ((k : ℂ) / 2 - s) := by
      rw [← cpow_add _ _ hAc]
      congr 1
      ring1
    rw [hadd, h6, ← h4, h5, ofReal_natCast, ← h7, hε', smul_eq_mul]
    ring1

/-- **Hecke's theorem.** For sequences `a, b` of polynomial growth, `k > 0` and `ε ≠ 0`, the
functional equation `HasFunctionalEquation a b k A ε` holds exactly when
`∑ a n e(n z) ∣[k] W_A = ε i ^ (-k) A ^ (k / 2 - 1) ∑ b n e(n z)`. -/
lemma hasFunctionalEquation_iff_expSum_slash_frickeGL (ha : HasPolyGrowth a) (hb : HasPolyGrowth b)
    (hk : 0 < k) (hε : ε ≠ 0) : HasFunctionalEquation a b k A ε ↔
      expSum a ∣[k] frickeGL ℝ A = (ε * I ^ (-k) * (A : ℂ) ^ ((k : ℂ) / 2 - 1)) • expSum b :=
  ⟨fun h ↦ h.expSum_slash_frickeGL hk ha hb, .of_expSum_slash_frickeGL ha hb hk hε⟩

lemma HasPolyGrowth.of_isBigO {m : ℤ} (h : c =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ m) :
    HasPolyGrowth c := by
  rcases h.bound with ⟨C, hC⟩
  rcases eventually_atTop.mp hC with ⟨n₀, hn₀⟩
  refine ⟨|C| + ∑ n ∈ Finset.range n₀, ‖c n‖, m.toNat, fun n hn ↦ ?_⟩
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
  have hS : 0 ≤ ∑ n ∈ Finset.range n₀, ‖c n‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ m.toNat := one_le_pow₀ hn1
  rcases le_or_gt n₀ n with hle | hlt
  · have h1 : ‖(n : ℝ) ^ m‖ ≤ (n : ℝ) ^ m.toNat := by
      rw [Real.norm_of_nonneg (zpow_nonneg (Nat.cast_nonneg n) m), ← zpow_natCast]
      exact zpow_le_zpow_right₀ hn1 (Int.self_le_toNat m)
    have h2 : ‖c n‖ ≤ |C| * (n : ℝ) ^ m.toNat :=
      (hn₀ n hle).trans (mul_le_mul (le_abs_self C) h1 (norm_nonneg _) (abs_nonneg C))
    exact h2.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  · have h2 : ‖c n‖ ≤ ∑ n ∈ Finset.range n₀, ‖c n‖ :=
      Finset.single_le_sum (f := fun n ↦ ‖c n‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.mpr hlt)
    have h3 : 0 ≤ |C| := abs_nonneg C
    nlinarith

lemma hasPolyGrowth_qExpansion_coeff [Γ.IsArithmetic] [ModularFormClass F Γ k] (hk : 0 ≤ k)
    (hΓ : Γ.strictWidthInfty = 1) (f : F) : HasPolyGrowth fun n ↦ (qExpansion 1 f).coeff n :=
  .of_isBigO (hΓ ▸ ModularFormClass.qExpansion_isBigO hk f)

lemma expSum_qExpansion_coeff [ModularFormClass F Γ k] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) :
    expSum (fun n ↦ (qExpansion 1 f).coeff n) = f := by
  have hfact : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  ext τ
  simpa only [expSum, qParam_one_pow] using (hasSum_qExpansion f one_pos hΓ τ).tsum_eq

variable [Fact r.Prime] in
private lemma twist_sign_ne_zero (hrN : ¬r ∣ N) {ψ : DirichletCharacter ℂ r} (hψ : ψ ≠ 1) :
    I ^ k * χ r * ψ N * gaussSum ψ ZMod.stdAddChar ^ 2 / r ≠ 0 := by
  have hp : r.Prime := Fact.out
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have h1 : χ r ≠ 0 :=
    (IsUnit.map χ ((ZMod.isUnit_iff_coprime r N).mpr (hp.coprime_iff_not_dvd.mpr hrN))).ne_zero
  have h2 : ψ N ≠ 0 :=
    (IsUnit.map ψ (Ne.isUnit fun h0 ↦ hrN ((ZMod.natCast_eq_zero_iff N r).mp h0))).ne_zero
  have h3 : gaussSum ψ ZMod.stdAddChar ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial (by simpa using hr) hψ (ZMod.isPrimitive_stdAddChar r)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ I_ne_zero) h1) h2)
    (pow_ne_zero 2 h3)) hr

variable [NeZero N]

/-- **The direct half of Weil's converse theorem.** Let `a, b` be sequences of polynomial growth,
`k > 0` and `χ` a Dirichlet character modulo `N`. If `∑ a n e(n z)` satisfies the nebentypus law of
`χ` on `Γ₀(N)` and `∑ a n e(n z) ∣[k] W_N = N ^ (k / 2 - 1) ∑ b n e(n z)`, then
`HasWeilFunctionalEquations a b k χ` holds, for every nontrivial character modulo every prime not
dividing `N`. -/
lemma hasWeilFunctionalEquations_of_nebentypus (hk : 0 < k) (ha : HasPolyGrowth a)
    (hb : HasPolyGrowth b) (hlaw : ∀ γ ∈ Gamma0 N, expSum a ∣[k] γ = χ (γ 1 1 : ℤ) • expSum a)
    (hW : expSum a ∣[k] frickeGL ℝ N = (N : ℂ) ^ ((k : ℂ) / 2 - 1) • expSum b) :
    HasWeilFunctionalEquations a b k χ := by
  have hI : I ^ k * I ^ (-k) = 1 := by
    rw [← zpow_add₀ I_ne_zero, add_neg_cancel, zpow_zero]
  have hdet : 0 < ((upperRightHom (1 : ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp
  have hg₁ :
      (expSum a ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = expSum a ∣[k] frickeGL ℝ N := by
    rw [hW, smul_slash_of_det_pos k hdet, expSum_slash_upperRightHom_one]
  refine ⟨ha, hb, .of_expSum_slash_frickeGL ha hb hk (zpow_ne_zero _ I_ne_zero) ?_, 0,
    fun r _ _ hrN ψ hψ ↦ .of_expSum_slash_frickeGL (ha.twistSeq ψ) (hb.twistSeq ψ⁻¹) hk
      (twist_sign_ne_zero hrN hψ) ?_⟩
  · rw [hI, one_mul]
    exact hW
  · exact (hasTwistedTransformation_iff_expSum_slash_frickeGL k χ ha hb hW hψ).mp
      (hasTwistedTransformation_of_nebentypus expSum_slash_upperRightHom_one hg₁
        (fun h0 ↦ hrN ((ZMod.natCast_eq_zero_iff N r).mp h0)) hlaw ψ)

/-- **Every modular form satisfies the hypotheses of Weil's converse theorem.** For `k > 0` and
`f ∈ M_k(N, χ)`, Eisenstein series included, `HasWeilFunctionalEquations a b k χ` holds, where `a`
are the Fourier coefficients of `f` and `b` those of its normalised Fricke image. So the hypotheses
of `HasWeilFunctionalEquations.modularForm_mem` characterise `M_k(N, χ)`. -/
lemma hasWeilFunctionalEquations_qExpansion_coeff (hk : 0 < k)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ.toUnitHom) :
    HasWeilFunctionalEquations (fun n ↦ (qExpansion 1 f).coeff n)
      (fun n ↦ (qExpansion 1 (normalizedFrickeOperator k f)).coeff n) k χ := by
  have hΓ : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map N
  have hw : ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty = 1 := by simp
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hQ : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  refine hasWeilFunctionalEquations_of_nebentypus hk (hasPolyGrowth_qExpansion_coeff hk.le hw f)
    (hasPolyGrowth_qExpansion_coeff hk.le hw _) (fun γ hγ ↦ ?_) ?_
  · have h1 : (f : ℍ → ℂ) ∣[k] γ = (↑(χ.toUnitHom ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩)) : ℂ) • f :=
      (mem_modFormCharSpace_iff_nebentypus k χ.toUnitHom f).mp hf ⟨γ, hγ⟩
    have h2 : ((χ.toUnitHom ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂˣ) : ℂ) = χ (γ 1 1 : ℤ) := by
      simp [Gamma0Map_apply]
    rw [expSum_qExpansion_coeff hΓ f, ← h2]
    exact h1
  · rw [expSum_qExpansion_coeff hΓ f, expSum_qExpansion_coeff hΓ (normalizedFrickeOperator k f),
      coe_normalizedFrickeOperator, atkinLehnerNormalizer_def, natCast_cpow_div_two_sub_one,
      smul_smul, ← zpow_add₀ hQ]
    simp

/-- **The discriminant satisfies the hypotheses of Weil's converse theorem**, in weight `12` and
level `1`, with the sequence `τ` of its Fourier coefficients on both sides. -/
lemma hasWeilFunctionalEquations_discriminant : HasWeilFunctionalEquations
    (fun n ↦ (qExpansion 1 discriminant).coeff n) (fun n ↦ (qExpansion 1 discriminant).coeff n) 12
      (1 : DirichletCharacter ℂ 1) := by
  have hP : HasPolyGrowth fun n ↦ (qExpansion 1 discriminant).coeff n :=
    hasPolyGrowth_qExpansion_coeff (k := 12) (by norm_num) Subgroup.strictWidthInfty_SL2Z
      CuspForm.discriminant
  have hE : expSum (fun n ↦ (qExpansion 1 discriminant).coeff n) = discriminant :=
    expSum_qExpansion_coeff (k := 12) one_mem_strictPeriods_SL CuspForm.discriminant
  have hS : frickeGL ℝ 1 = mapGL ℝ ModularGroup.S := by
    have h1 : ∀ i j : Fin 2,
        ((mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
          (((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) := fun _ _ ↦ rfl
    ext i j
    rw [h1, ModularGroup.coe_S]
    fin_cases i <;> fin_cases j <;> simp
  refine hasWeilFunctionalEquations_of_nebentypus (by norm_num) hP hP (fun γ _ ↦ ?_) ?_
  · have h1 : (1 : DirichletCharacter ℂ 1) (γ 1 1 : ℤ) = 1 :=
      MulChar.one_apply (isUnit_of_subsingleton _)
    rw [hE, h1, one_smul]
    exact slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ
  · rw [hE, hS, Nat.cast_one, one_cpow, one_smul]
    exact discriminant_S_invariant

end ModularForm
