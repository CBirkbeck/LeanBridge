import LeanBridge.ForMathlib.NumberTheory.LFunction.AnalyticRankParity
import LeanBridge.ForMathlib.NumberTheory.LFunction.Completed

/-!
# The sign of a self-dual L-function

An analytic L-function `L(s) = ∑ aₙ n ^ (-s)` with real Dirichlet coefficients (LMFDB
`lfunction.self-dual`) has sign `ε = ±1`, and `L(1 / 2) = 0` when `ε = -1` (LMFDB
`lfunction.root_number`). This holds for the Selberg data bundled with `L`, whether or not the
Selberg data of `L` is unique.

Since `L(conj s) = conj L(s)`, conjugating the functional equation `Λ(s) = ε conj (Λ (1 - conj s))`
gives a second functional equation for `L`, with the gamma factor `conj L_∞(conj s)` of the dual
Selberg data `(N, conj μ, conj ν, conj ε)`. Comparing the two on the strip `0 < re s < 1` gives
`L_∞(s) L_∞(1 - s) = ε² conj L_∞(conj s) conj L_∞(conj (1 - s))`, an identity of entire functions
once the gamma factors are inverted. The poles of `L_∞(s)` lie in `re s ≤ 0` and those of
`L_∞(1 - s)` in `re s ≥ 1`, so `L_∞` and its conjugate have the same poles, with multiplicities. As
`Γ_ℂ(s) = Γ_ℝ(s) Γ_ℝ(s + 1)`, the gamma factor is the product of the `Γ_ℝ(s + a)` over the multiset
of shifts `μⱼ`, `νₖ` and `νₖ + 1`, and by `Γ_ℝ(s + 2) = s / (2π) Γ_ℝ(s)` the multiplicity of `a`
among the shifts is the order of the pole at `-a` minus that at `-a + 2`. So the shifts are closed
under conjugation, the gamma factor is real at the central point `s = 1 / 2`, and comparing the
leading terms of the functional equation there gives `ε = (-1)ʳ`, where `r` is the analytic rank
(`AnalyticLFunction.sign_eq_neg_one_pow_analyticRank`, which assumes the reality of the gamma
factor at `s = 1 / 2`).

## Main definitions

* `AnalyticLFunction.SelbergData.dual`: the dual Selberg data `(N, conj μ, conj ν, conj ε)`.
* `AnalyticLFunction.SelbergData.gammaℝShifts`: the shifts `a` of the gamma factor written as a
  product of factors `Γ_ℝ(s + a)`.

## Main results

* `Complex.eq_of_forall_analyticOrderAt_prod_inv_Gammaℝ_eq`: a multiset `A` of shifts is
  determined by the orders of the zeros of the entire function `∏_{a ∈ A} Γ_ℝ(s + a)⁻¹`.
* `AnalyticLFunction.gammaFactor_dual_eq`: the dual Selberg data of a self-dual L-function has the
  same gamma factor.
* `AnalyticLFunction.conj_gammaFactor_conj`: the gamma factor of a self-dual L-function satisfies
  `conj L_∞(conj s) = L_∞(s)`.
* `AnalyticLFunction.sign_eq_neg_one_pow_analyticRank_of_selfDual` (LMFDB `lfunction.sign`): the
  sign of a self-dual L-function is `(-1)ʳ`, where `r` is its analytic rank.
* `AnalyticLFunction.sign_eq_one_or_eq_neg_one` (LMFDB `lfunction.root_number`): the sign of a
  self-dual L-function is `±1`.
* `AnalyticLFunction.toFun_one_half_eq_zero_of_sign_eq_neg_one` (LMFDB `lfunction.root_number`): a
  self-dual L-function of sign `-1` vanishes at the central point `s = 1 / 2`.
-/

open Complex Filter Set

open scoped ComplexConjugate Real Topology

namespace Complex

variable {A B : Multiset ℂ} {s z : ℂ}

variable (s) in
lemma inv_Gammaℝ_eq_mul_inv_Gammaℝ_add_two : (Gammaℝ s)⁻¹ = s / (2 * π) * (Gammaℝ (s + 2))⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Gammaℝ_eq_zero_iff]
  · rw [Gammaℝ_add_two hs]
    field_simp

variable (A) in
lemma differentiable_prod_inv_Gammaℝ :
    Differentiable ℂ fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod :=
  fun s ↦ .multiset_prod fun a _ ↦ differentiable_Gammaℝ_inv.comp (differentiable_id.add_const a) s

lemma prod_inv_Gammaℝ_ne_zero (hA : ∀ a ∈ A, 0 ≤ a.re) (hs : 0 < s.re) :
    (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod ≠ 0 :=
  Multiset.prod_ne_zero fun h ↦ by
    rcases Multiset.mem_map.mp h with ⟨a, ha, h⟩
    refine inv_ne_zero (Gammaℝ_ne_zero_of_re_pos ?_) h
    simpa using add_pos_of_pos_of_nonneg hs (hA a ha)

variable (A s) in
lemma prod_inv_Gammaℝ_eq_mul_prod_inv_Gammaℝ_add_two : (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod =
    (A.map fun a ↦ (s + a) / (2 * π)).prod * (A.map fun a ↦ (Gammaℝ (s + 2 + a))⁻¹).prod := by
  rw [← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun a _ ↦ ?_)
  rw [inv_Gammaℝ_eq_mul_inv_Gammaℝ_add_two, add_right_comm]

variable (A) in
lemma differentiable_prod_add_div_two_pi :
    Differentiable ℂ fun s : ℂ ↦ (A.map fun a ↦ (s + a) / (2 * π)).prod :=
  fun _ ↦ .multiset_prod fun _ _ ↦ by fun_prop

variable (A z) in
lemma analyticOrderAt_prod_add_div_two_pi :
    analyticOrderAt (fun s : ℂ ↦ (A.map fun a ↦ (s + a) / (2 * π)).prod) z = A.count (-z) := by
  induction A using Multiset.induction_on with
  | empty => simp [analyticOrderAt_eq_zero]
  | cons b A ih =>
    have hπ : (2 * π : ℂ) ≠ 0 :=
      mod_cast Real.two_pi_pos.ne'
    have hb : AnalyticAt ℂ (fun s ↦ (s + b) / (2 * π)) z := by
      fun_prop
    have h : analyticOrderAt (fun s ↦ (s + b) / (2 * π)) z = if -z = b then 1 else 0 := by
      split_ifs with h
      · subst h
        have hf : (fun s ↦ (s + -z) / (2 * π)) = (· - z) * fun _ ↦ (2 * π : ℂ)⁻¹ := by
          funext s
          simp [div_eq_mul_inv, sub_eq_add_neg]
        rw [hf, analyticOrderAt_mul (by fun_prop) analyticAt_const,
          analyticOrderAt_id_sub_const_self]
        simp [analyticOrderAt_eq_zero]
      · refine analyticOrderAt_eq_zero.mpr <| .inr <| div_ne_zero (fun h' ↦ h ?_) hπ
        linear_combination -h'
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.count_cons]
    rw [Nat.cast_add, ← ih, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← h]
    exact (analyticOrderAt_mul hb ((differentiable_prod_add_div_two_pi A).analyticAt z)).trans
      (add_comm _ _)

lemma analyticOrderAt_prod_inv_Gammaℝ_ne_top (hA : ∀ a ∈ A, 0 ≤ a.re) :
    analyticOrderAt (fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod) z ≠ ⊤ := by
  rw [Ne, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
    fun w ↦ (differentiable_prod_inv_Gammaℝ A).analyticAt w]
  exact fun h ↦ prod_inv_Gammaℝ_ne_zero hA (by norm_num) (congrFun h 1)

variable (A z) in
lemma analyticOrderAt_prod_inv_Gammaℝ :
    analyticOrderAt (fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod) z = A.count (-z) +
      analyticOrderAt (fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod) (z + 2) := by
  have h : (fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod) =
      (fun s : ℂ ↦ (A.map fun a ↦ (s + a) / (2 * π)).prod) *
          ((fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod) ∘ (· + 2)) :=
    funext fun s ↦ prod_inv_Gammaℝ_eq_mul_prod_inv_Gammaℝ_add_two A s
  have hQ : AnalyticAt ℂ ((fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod) ∘ (· + 2)) z :=
    ((differentiable_prod_inv_Gammaℝ A).comp (differentiable_id.add_const 2)).analyticAt z
  refine (congrArg (analyticOrderAt · z) h).trans ?_
  rw [analyticOrderAt_mul ((differentiable_prod_add_div_two_pi A).analyticAt z) hQ,
    analyticOrderAt_prod_add_div_two_pi, analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop)
    (by simp)]

/-- **A multiset of shifts is determined by the zeros of `∏ₐ Γ_ℝ(s + a)⁻¹`**: if the entire
functions `∏_{a ∈ A} Γ_ℝ(s + a)⁻¹` and `∏_{b ∈ B} Γ_ℝ(s + b)⁻¹` vanish to the same order at every
point, and the shifts in `B` have nonnegative real parts, then `A = B`. Indeed
`Γ_ℝ(s)⁻¹ = s / (2π) Γ_ℝ(s + 2)⁻¹`, so the multiplicity of `a` in `A` is the order of vanishing at
`-a` minus that at `-a + 2`. -/
lemma eq_of_forall_analyticOrderAt_prod_inv_Gammaℝ_eq (hB : ∀ b ∈ B, 0 ≤ b.re)
    (h : ∀ z, analyticOrderAt (fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod) z =
      analyticOrderAt (fun s ↦ (B.map fun b ↦ (Gammaℝ (s + b))⁻¹).prod) z) : A = B := by
  refine Multiset.ext.mpr fun w ↦ ?_
  have h₁ : analyticOrderAt (fun s ↦ (A.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod) (-w) =
      analyticOrderAt (fun s ↦ (B.map fun b ↦ (Gammaℝ (s + b))⁻¹).prod) (-w) :=
    h (-w)
  rw [analyticOrderAt_prod_inv_Gammaℝ, analyticOrderAt_prod_inv_Gammaℝ B, h (-w + 2),
    neg_neg] at h₁
  exact ENat.natCast_inj.mp <| WithTop.add_right_cancel
    (analyticOrderAt_prod_inv_Gammaℝ_ne_top hB) h₁

lemma analyticOrderAt_eq_of_forall_mul_one_sub_eq {f g : ℂ → ℂ} {c : ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf₀ : ∀ s, 0 < s.re → f s ≠ 0) (hg₀ : ∀ s, 0 < s.re → g s ≠ 0)
    (hc : c ≠ 0) (h : ∀ s, f s * f (1 - s) = c * (g s * g (1 - s))) :
    analyticOrderAt f z = analyticOrderAt g z := by
  rcases lt_or_ge 0 z.re with hz | hz
  · rw [analyticOrderAt_eq_zero.mpr (.inr (hf₀ z hz)),
      analyticOrderAt_eq_zero.mpr (.inr (hg₀ z hz))]
  have hz₁ : 0 < (1 - z).re := by
    simp only [sub_re, one_re]
    linarith
  have hσ : Differentiable ℂ fun s : ℂ ↦ 1 - s :=
    (differentiable_const 1).sub differentiable_id
  have hf₁ : Differentiable ℂ fun s ↦ f (1 - s) :=
    hf.comp hσ
  have hg₁ : Differentiable ℂ fun s ↦ g (1 - s) :=
    hg.comp hσ
  have h₁ : analyticOrderAt (fun s ↦ f (1 - s)) z = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (hf₀ _ hz₁))
  have h₂ : analyticOrderAt (fun s ↦ g (1 - s)) z = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (hg₀ _ hz₁))
  have h₃ : analyticOrderAt (fun _ ↦ c) z = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr hc)
  have e₁ : analyticOrderAt (fun s ↦ f s * f (1 - s)) z = analyticOrderAt f z +
      analyticOrderAt (fun s ↦ f (1 - s)) z :=
    analyticOrderAt_mul (hf.analyticAt z) (hf₁.analyticAt z)
  have e₂ : analyticOrderAt (fun s ↦ c * (g s * g (1 - s))) z = analyticOrderAt (fun _ ↦ c) z +
      (analyticOrderAt g z + analyticOrderAt (fun s ↦ g (1 - s)) z) :=
    (analyticOrderAt_mul analyticAt_const ((hg.mul hg₁).analyticAt z)).trans
      (congrArg (analyticOrderAt (fun _ ↦ c) z + ·)
        (analyticOrderAt_mul (hg.analyticAt z) (hg₁.analyticAt z)))
  rw [h₁, add_zero] at e₁
  rw [h₂, h₃, zero_add, add_zero] at e₂
  rw [← e₁, ← e₂, funext h]

end Complex

namespace AnalyticLFunction.SelbergData

variable (D : SelbergData) (s : ℂ)

/-- The **dual** Selberg data `(N, conj μ, conj ν, conj ε)` of `(N, μ, ν, ε)`. Conjugating the
functional equation `Λ(s) = ε conj (Λ (1 - conj s))` of an L-function `∑ aₙ n ^ (-s)` gives the
functional equation of its dual `∑ conj aₙ n ^ (-s)`, whose completion `conj Λ(conj s)` has the
gamma factor `conj L_∞(conj s)` of these data. -/
def dual : SelbergData where
  conductor := D.conductor
  μ := D.μ.map conj
  ν := D.ν.map conj
  sign := conj D.sign
  conductor_pos := D.conductor_pos
  re_eq_zero_or_one_of_mem_μ x hx := by
    rcases Multiset.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa using D.re_eq_zero_or_one_of_mem_μ y hy
  exists_two_mul_re_eq_of_mem_ν x hx := by
    rcases Multiset.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa using D.exists_two_mul_re_eq_of_mem_ν y hy
  im_sum_add_two_mul_sum := by
    have h : (D.μ.sum + 2 * D.ν.sum).im = 0 := D.im_sum_add_two_mul_sum
    simp only [← map_multiset_sum]
    norm_num at h ⊢
    linarith

/-- The **shifts** of the gamma factor written with `Γ_ℝ` alone: the multiset of the `μⱼ`, the `νₖ`
and the `νₖ + 1`, so that `∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ) = ∏ₐ Γ_ℝ(s + a)`, as
`Γ_ℂ(s) = Γ_ℝ(s) Γ_ℝ(s + 1)`. -/
def gammaℝShifts : Multiset ℂ :=
  D.μ + D.ν + D.ν.map (· + 1)

lemma re_nonneg_of_mem_gammaℝShifts {a : ℂ} (ha : a ∈ D.gammaℝShifts) : 0 ≤ a.re := by
  rcases Multiset.mem_add.mp ha with ha | ha
  · rcases Multiset.mem_add.mp ha with ha | ha
    · rcases D.re_eq_zero_or_one_of_mem_μ a ha with h | h <;> simp [h]
    · rcases D.exists_two_mul_re_eq_of_mem_ν a ha with ⟨k, -, hk⟩
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · rcases Multiset.mem_map.mp ha with ⟨b, hb, rfl⟩
    rcases D.exists_two_mul_re_eq_of_mem_ν b hb with ⟨k, -, hk⟩
    simp only [add_re, one_re]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma gammaℝShifts_dual : D.dual.gammaℝShifts = D.gammaℝShifts.map conj := by
  simp [gammaℝShifts, dual]

lemma gammaFactor_eq_prod : D.gammaFactor s = (D.gammaℝShifts.map fun a ↦ Gammaℝ (s + a)).prod := by
  rw [gammaFactor, gammaℝShifts, Multiset.map_add, Multiset.map_add, Multiset.prod_add,
    Multiset.prod_add, mul_assoc, Multiset.map_map, ← Multiset.prod_map_mul]
  congr 2
  exact Multiset.map_congr rfl fun x _ ↦ by simp [← Gammaℝ_mul_Gammaℝ_add_one, add_assoc]

lemma inv_gammaFactor_eq_prod :
    (D.gammaFactor s)⁻¹ = (D.gammaℝShifts.map fun a ↦ (Gammaℝ (s + a))⁻¹).prod := by
  rw [gammaFactor_eq_prod, Multiset.prod_map_inv]

lemma gammaFactor_dual : D.dual.gammaFactor s = conj (D.gammaFactor (conj s)) := by
  rw [gammaFactor_eq_prod, gammaFactor_eq_prod, gammaℝShifts_dual, map_multiset_prod,
    Multiset.map_map, Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun a _ ↦ by simp [← Gammaℝ_conj])

end AnalyticLFunction.SelbergData

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {s : ℂ}

lemma completingFactor_mul_toFun_eq_sign_mul (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n)
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1) : L.completingFactor s * L.toFun s =
    L.sign * (conj (L.completingFactor (conj (1 - s))) * L.toFun (1 - s)) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs₀
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs₁
  rw [← L.completed_eq_of_re_pos hs₀ hs1, sign, L.completed_eq_sign_mul_conj hs0 hs1,
    L.completed_eq_of_re_pos (by simpa using hs₁) (by simpa using hs0), map_mul,
    ← L.conj_toFun_conj hL (s := 1 - s) (by simpa using hs0), map_sub, map_one]

lemma gammaFactor_mul_gammaFactor_one_sub (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n)
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1) (hs : L.toFun s ≠ 0) (hs' : L.toFun (1 - s) ≠ 0) :
    L.selbergData.gammaFactor s * L.selbergData.gammaFactor (1 - s) =
      L.sign ^ 2 * (L.selbergData.dual.gammaFactor s * L.selbergData.dual.gammaFactor (1 - s)) := by
  have h₀ : 0 < (1 - s).re := by
    simpa using hs₁
  have h₁ : (1 - s).re < 1 := by
    simpa using hs₀
  have hN (w : ℂ) : conj ((L.conductor : ℂ) ^ (conj w / 2)) = (L.conductor : ℂ) ^ (w / 2) := by
    simpa [map_ofNat] using conj_natCast_cpow_conj L.conductor (w / 2)
  have E₁ : L.completingFactor s * L.toFun s =
      L.sign * (conj (L.completingFactor (conj (1 - s))) * L.toFun (1 - s)) :=
    L.completingFactor_mul_toFun_eq_sign_mul hL hs₀ hs₁
  have E₂ : L.completingFactor (1 - s) * L.toFun (1 - s) =
      L.sign * (conj (L.completingFactor (conj s)) * L.toFun s) := by
    simpa only [sub_sub_cancel] using L.completingFactor_mul_toFun_eq_sign_mul hL h₀ h₁
  simp only [completingFactor, map_mul, hN, ← SelbergData.gammaFactor_dual] at E₁ E₂
  refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (L.conductor_cpow_ne_zero s)
    (L.conductor_cpow_ne_zero (1 - s))) (mul_ne_zero hs hs')) ?_
  linear_combination ((L.conductor : ℂ) ^ ((1 - s) / 2) * L.selbergData.gammaFactor (1 - s) *
    L.toFun (1 - s)) * E₁ + (L.sign * (L.conductor : ℂ) ^ ((1 - s) / 2) *
    L.selbergData.dual.gammaFactor (1 - s) * L.toFun (1 - s)) * E₂

variable (s) in
lemma inv_gammaFactor_dual_mul_eq (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n) :
    (L.selbergData.dual.gammaFactor s)⁻¹ * (L.selbergData.dual.gammaFactor (1 - s))⁻¹ =
      L.sign ^ 2 * ((L.selbergData.gammaFactor s)⁻¹ * (L.selbergData.gammaFactor (1 - s))⁻¹) := by
  have hσ : Differentiable ℂ fun s : ℂ ↦ 1 - s :=
    (differentiable_const 1).sub differentiable_id
  have hd : Differentiable ℂ fun s ↦ (L.selbergData.dual.gammaFactor s)⁻¹ :=
    L.selbergData.dual.differentiable_inv_gammaFactor
  have hd' : Differentiable ℂ fun s ↦ (L.selbergData.gammaFactor s)⁻¹ :=
    L.selbergData.differentiable_inv_gammaFactor
  have hF : Differentiable ℂ fun s ↦ (L.selbergData.dual.gammaFactor s)⁻¹ *
      (L.selbergData.dual.gammaFactor (1 - s))⁻¹ -
      L.sign ^ 2 * ((L.selbergData.gammaFactor s)⁻¹ * (L.selbergData.gammaFactor (1 - s))⁻¹) :=
    (hd.mul (hd.comp hσ)).sub ((hd'.mul (hd'.comp hσ)).const_mul _)
  have hL₁ : ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ), L.toFun z ≠ 0 :=
    (L.analyticAt_toFun (by norm_num)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun h ↦ L.analyticOrderAt_toFun_ne_top (by norm_num) (analyticOrderAt_eq_top.mpr h)
  have ht : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] (1 / 2)) (𝓝[≠] (1 / 2)) :=
    tendsto_nhdsWithin_iff.mpr ⟨((continuous_const.sub continuous_id).tendsto' _ _
      (by norm_num)).mono_left nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall
      fun z hz h ↦ hz <| mem_singleton_iff.mpr <| by linear_combination -mem_singleton_iff.mp h⟩
  have hstrip : ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ), 0 < z.re ∧ z.re < 1 :=
    nhdsWithin_le_nhds <| ((continuous_re.isOpen_preimage _ isOpen_Ioi).inter
      (continuous_re.isOpen_preimage _ isOpen_Iio)).mem_nhds (by norm_num)
  refine sub_eq_zero.mp (AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun z _ ↦ hF.analyticAt z) isPreconnected_univ (mem_univ (1 / 2)) ?_ (mem_univ s))
  refine ((hstrip.and (hL₁.and (ht.eventually hL₁))).mono fun z hz ↦ ?_).frequently
  have h : L.selbergData.gammaFactor z * L.selbergData.gammaFactor (1 - z) =
      L.sign ^ 2 * (L.selbergData.dual.gammaFactor z * L.selbergData.dual.gammaFactor (1 - z)) :=
    L.gammaFactor_mul_gammaFactor_one_sub hL hz.1.1 hz.1.2 hz.2.1 hz.2.2
  have h₀ : 0 < (1 - z).re := by
    simpa using hz.1.2
  have ha : L.selbergData.gammaFactor z ≠ 0 :=
    L.selbergData.gammaFactor_ne_zero hz.1.1
  have ha' : L.selbergData.gammaFactor (1 - z) ≠ 0 :=
    L.selbergData.gammaFactor_ne_zero h₀
  have hb : L.selbergData.dual.gammaFactor z ≠ 0 :=
    L.selbergData.dual.gammaFactor_ne_zero hz.1.1
  have hb' : L.selbergData.dual.gammaFactor (1 - z) ≠ 0 :=
    L.selbergData.dual.gammaFactor_ne_zero h₀
  rw [sub_eq_zero]
  field_simp
  linear_combination h

lemma gammaℝShifts_dual_eq (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n) :
    L.selbergData.dual.gammaℝShifts = L.selbergData.gammaℝShifts := by
  have hε : L.sign ^ 2 ≠ 0 :=
    pow_ne_zero 2 <| norm_ne_zero_iff.mp <| L.norm_sign ▸ one_ne_zero
  refine eq_of_forall_analyticOrderAt_prod_inv_Gammaℝ_eq
    (fun _ ↦ L.selbergData.re_nonneg_of_mem_gammaℝShifts) fun z ↦ ?_
  simp only [← SelbergData.inv_gammaFactor_eq_prod]
  exact analyticOrderAt_eq_of_forall_mul_one_sub_eq
    L.selbergData.dual.differentiable_inv_gammaFactor L.selbergData.differentiable_inv_gammaFactor
    (fun s hs ↦ inv_ne_zero (L.selbergData.dual.gammaFactor_ne_zero hs))
    (fun s hs ↦ inv_ne_zero (L.selbergData.gammaFactor_ne_zero hs)) hε
    fun s ↦ L.inv_gammaFactor_dual_mul_eq s hL

/-- **The dual Selberg data of a self-dual L-function has the same gamma factor**: if the Dirichlet
coefficients of `L` are real, then `conj L_∞(conj s)`, the gamma factor of the conjugated
functional equation, is `L_∞(s)`. -/
lemma gammaFactor_dual_eq (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n) :
    L.selbergData.dual.gammaFactor = L.selbergData.gammaFactor :=
  funext fun s ↦ by
    rw [SelbergData.gammaFactor_eq_prod, L.gammaℝShifts_dual_eq hL,
      SelbergData.gammaFactor_eq_prod]

variable (s) in
/-- **The gamma factor of a self-dual L-function commutes with conjugation**:
`conj L_∞(conj s) = L_∞(s)`, so `L_∞` is real on the real line. -/
lemma conj_gammaFactor_conj (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n) :
    conj (L.selbergData.gammaFactor (conj s)) = L.selbergData.gammaFactor s := by
  rw [← SelbergData.gammaFactor_dual, L.gammaFactor_dual_eq hL]

/-- **The sign of a self-dual L-function is `(-1)ʳ`** (LMFDB `lfunction.sign`), where `r` is its
analytic rank: `AnalyticLFunction.sign_eq_neg_one_pow_analyticRank` without the assumption that the
gamma factor is real at `s = 1 / 2`. -/
lemma sign_eq_neg_one_pow_analyticRank_of_selfDual (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n) :
    L.sign = (-1) ^ L.analyticRank :=
  L.sign_eq_neg_one_pow_analyticRank hL <| by
    simpa [map_ofNat] using L.conj_gammaFactor_conj (1 / 2) hL

/-- **The sign of a self-dual L-function is `±1`** (LMFDB `lfunction.root_number`): if the Dirichlet
coefficients are real, then `ε = 1` or `ε = -1`. -/
lemma sign_eq_one_or_eq_neg_one (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n) :
    L.sign = 1 ∨ L.sign = -1 :=
  L.sign_eq_neg_one_pow_analyticRank_of_selfDual hL ▸ neg_one_pow_eq_or ℂ L.analyticRank

/-- **A self-dual L-function of sign `-1` vanishes at the central point** (LMFDB
`lfunction.root_number`): if the Dirichlet coefficients are real and `ε = -1`, then
`L(1 / 2) = 0`. -/
lemma toFun_one_half_eq_zero_of_sign_eq_neg_one (hL : ∀ n ≠ 0, conj (L.coeff n) = L.coeff n)
    (hε : L.sign = -1) : L.toFun (1 / 2) = 0 := by
  by_contra h
  rw [L.sign_eq_neg_one_pow_analyticRank_of_selfDual hL, L.analyticRank_eq_zero_iff.mpr h,
    pow_zero] at hε
  norm_num at hε

end AnalyticLFunction
