import LeanBridge.ForMathlib.NumberTheory.LFunction.SymmetricPower
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.NumberTheory.LSeries.Conjugate

/-!
# Dirichlet L-functions as analytic L-functions

The L-function `L(s, χ) = ∑ χ(n) n ^ (-s)` of a primitive Dirichlet character `χ` modulo `N`
(LMFDB `lfunction.dirichlet`) is the analytic L-function of degree `1` and conductor `N` with Euler
factors `(1 - χ(p) p ^ (-s))⁻¹`, spectral parameter `μ = δ` and sign the root number `ε_χ`, where
`δ` is `0` for even `χ` and `1` for odd `χ`: its completion
`Λ(s, χ) = N ^ (s / 2) Γ_ℝ(s + δ) L(s, χ)` satisfies `Λ(s, χ) = ε_χ conj (Λ(1 - conj s, χ))`. This
combines Mathlib's functional equation `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`,
which relates `Λ(1 - s, χ)` and `Λ(s, χ⁻¹)`, with the conjugation symmetry
`Λ(conj s, χ) = conj (Λ(s, χ⁻¹))`, which holds for `re s > 1` by the Dirichlet series and then for
every `s ≠ 1` by the identity theorem. Hence the root number of a primitive character has absolute
value `1`, and for the trivial character modulo `1` this is the Riemann zeta function.

The LMFDB states the functional equation with the gamma factor `Γ_ℝ(s)` for every Dirichlet
character `χ`, with `q` the conductor of `χ`. The gamma factor of an odd character is `Γ_ℝ(s + 1)`,
and the equation fails for the imprimitive characters whose modulus has a prime factor that does not
divide the conductor, such as the trivial character modulo `2`, whose L-function is
`(1 - 2 ^ (-s)) ζ(s)`.

## Main definitions

* `AnalyticLFunction.SelbergData.dirichlet`: the Selberg data `(1, N, (δ : ), ε_χ)` of the
  L-function of a primitive Dirichlet character.
* `AnalyticLFunction.dirichlet` (LMFDB `lfunction.dirichlet`): the L-function of a primitive
  Dirichlet character as an analytic L-function.

## Main results

* `DirichletCharacter.LFunction_eulerProduct_hasProd` (LMFDB `lfunction.history.dirichlet`): the
  Euler product of the L-function of a Dirichlet character, for `re s > 1`.
* `DirichletCharacter.completedLFunction_conj`: the conjugation symmetry
  `Λ(conj s, χ) = conj (Λ(s, χ⁻¹))` of the completed L-function of a Dirichlet character, for
  `s ≠ 1`.
* `AnalyticLFunction.eulerPolynomial_dirichlet` (LMFDB `lfunction.dirichlet`): the Euler factor of
  `L(s, χ)` at a prime `p` is `1 - χ(p) T`.
* `AnalyticLFunction.dirichlet_eq_zeta`: modulo `1`, the Dirichlet L-function is the Riemann zeta
  function `AnalyticLFunction.zeta`.
* `DirichletCharacter.IsPrimitive.norm_rootNumber`: the root number of a primitive Dirichlet
  character has absolute value `1`.
-/

open Complex TauCeti

open Polynomial (C X)

open scoped ComplexConjugate Polynomial PowerSeries Topology

variable {N p : ℕ} {χ : DirichletCharacter ℂ N} {s : ℂ}

namespace DirichletCharacter

variable (s) in
lemma gammaFactor_conj : gammaFactor χ (conj s) = conj (gammaFactor χ s) := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def, hχ.gammaFactor_def, Gammaℝ_conj]
  · rw [hχ.gammaFactor_def, hχ.gammaFactor_def, ← Gammaℝ_conj, map_add, map_one]

lemma gammaFactor_inv : gammaFactor χ⁻¹ = gammaFactor χ := by
  ext s
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def, Even.gammaFactor_def]
    rwa [Even, MulChar.inv_apply_eq_inv', inv_eq_one]
  · rw [hχ.gammaFactor_def, Odd.gammaFactor_def]
    rwa [Odd, MulChar.inv_apply_eq_inv', inv_eq_iff_eq_inv, inv_neg_one]

lemma gammaFactor_ne_zero (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simpa using add_pos hs one_pos)

variable (χ s) in
lemma LSeries_conj : LSeries (χ ·) (conj s) = conj (LSeries (χ⁻¹ ·) s) :=
  (congrArg (LSeries · (conj s)) <| funext fun n ↦ by
    rw [Pi.star_apply, MulChar.star_apply', inv_inv]).trans <| LSeries.LSeries_star _ s

lemma one_sub_C_mul_X_mul_mk_eq_one :
    ((1 - C (χ p) * X : ℂ[X]) : ℂ⟦X⟧) * PowerSeries.mk (fun k ↦ χ ↑(p ^ k)) = 1 := by
  simpa [PowerSeries.rescale_mk] using congrArg (PowerSeries.rescale (χ p))
    ((mul_comm _ _).trans (PowerSeries.mk_one_mul_one_sub_eq_one ℂ))

lemma natDegree_one_sub_C_mul_X_eq_one_iff : (1 - C (χ p) * X : ℂ[X]).natDegree = 1 ↔ χ p ≠ 0 := by
  rcases eq_or_ne (χ p) 0 with h | h
  · simp [h]
  · exact iff_of_true (by compute_degree!) h

variable [NeZero N]

lemma IsPrimitive.ne_one (hχ : χ.IsPrimitive) (hN : N ≠ 1) : χ ≠ 1 :=
  fun h ↦ hN <| hχ.symm.trans <| eq_one_iff_conductor_eq_one.mp h

lemma completedLFunction_eq_gammaFactor_mul (hs : 0 < s.re) :
    completedLFunction χ s = gammaFactor χ s * LFunction χ s := by
  rw [LFunction_eq_completed_div_gammaFactor χ s (.inl (ne_zero_of_re_pos hs)),
    mul_div_cancel₀ _ (gammaFactor_ne_zero hs)]

variable (χ) in
/-- **The Euler product of a Dirichlet L-function** (LMFDB `lfunction.history.dirichlet`):
`L(s, χ) = ∏ (1 - χ(p) p ^ (-s))⁻¹` over the primes `p`, for `re s > 1`. This is Mathlib's
`DirichletCharacter.LSeries_eulerProduct_hasProd`, stated for the continued L-function
`DirichletCharacter.LFunction`. -/
lemma LFunction_eulerProduct_hasProd (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (LFunction χ s) :=
  χ.LFunction_eq_LSeries hs ▸ χ.LSeries_eulerProduct_hasProd hs

variable (χ) in
/-- **Conjugation symmetry of the completed L-function of a Dirichlet character**:
`Λ(conj s, χ) = conj (Λ(s, χ⁻¹))` for `s ≠ 1`, where `Λ(s, χ) = Γ_ℝ(s + δ) L(s, χ)` is Mathlib's
`DirichletCharacter.completedLFunction`. For `re s > 1` it follows from the Dirichlet series, since
`conj (χ(n)) = χ⁻¹(n)`, and the identity theorem extends it to every `s ≠ 1`. -/
lemma completedLFunction_conj (hs : s ≠ 1) :
    completedLFunction χ (conj s) = conj (completedLFunction χ⁻¹ s) := by
  rcases eq_or_ne N 1 with rfl | hN
  · simp [completedLFunction_modOne_eq]
  have hf : AnalyticOnNhd ℂ (conj ∘ completedLFunction χ ∘ conj) {1}ᶜ := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) isOpen_compl_singleton
    refine (differentiableAt_conj_conj_iff.mpr <| differentiableAt_completedLFunction χ _ (.inr hN)
      (.inl ?_)).differentiableWithinAt
    exact (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hz
  have hg : AnalyticOnNhd ℂ (completedLFunction χ⁻¹) {1}ᶜ :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦ (differentiableAt_completedLFunction χ⁻¹ z (.inr hN)
      (.inl hz)).differentiableWithinAt) isOpen_compl_singleton
  have hfg : (conj ∘ completedLFunction χ ∘ conj) =ᶠ[𝓝 2] completedLFunction χ⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz' : 1 < (conj z).re := by
      rwa [conj_re]
    rw [Function.comp_apply, Function.comp_apply,
      completedLFunction_eq_gammaFactor_mul (zero_lt_one.trans hz'),
      completedLFunction_eq_gammaFactor_mul (zero_lt_one.trans hz), LFunction_eq_LSeries χ hz',
      LFunction_eq_LSeries χ⁻¹ hz, gammaFactor_conj, LSeries_conj, gammaFactor_inv, map_mul,
      conj_conj, conj_conj]
  rw [← hf.eqOn_of_preconnected_of_eventuallyEq hg
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected (by simp) hfg hs,
    Function.comp_apply, Function.comp_apply, conj_conj]

end DirichletCharacter

namespace AnalyticLFunction

open DirichletCharacter

variable [NeZero N]

namespace SelbergData

variable (χ)

open scoped Classical in
/-- The **Selberg data** `(1, N, (δ : ), ε_χ)` of the L-function of a primitive Dirichlet character
`χ` modulo `N`: the conductor `N`, the single spectral parameter `μ = δ`, where `δ` is `0` for even
`χ` and `1` for odd `χ`, and the sign `ε_χ`, the root number `DirichletCharacter.rootNumber χ`. -/
noncomputable def dirichlet : SelbergData where
  conductor := N
  μ := {if χ.Even then 0 else 1}
  ν := 0
  sign := rootNumber χ
  conductor_pos := Nat.pos_of_neZero N
  re_eq_zero_or_one_of_mem_μ x hx := by
    rw [Multiset.mem_singleton.mp hx]
    split_ifs <;> simp
  exists_two_mul_re_eq_of_mem_ν x hx := absurd hx (Multiset.notMem_zero x)
  im_sum_add_two_mul_sum := by
    split_ifs <;> simp

@[simp]
lemma conductor_dirichlet : (dirichlet χ).conductor = N :=
  rfl

@[simp]
lemma sign_dirichlet : (dirichlet χ).sign = rootNumber χ :=
  rfl

@[simp]
lemma degree_dirichlet : (dirichlet χ).degree = 1 :=
  rfl

@[simp]
lemma gammaFactor_dirichlet : (dirichlet χ).gammaFactor = χ.gammaFactor := by
  ext s
  rcases χ.even_or_odd with hχ | hχ
  · simp [gammaFactor, dirichlet, hχ, hχ.gammaFactor_def]
  · simp [gammaFactor, dirichlet, hχ.not_even, hχ.gammaFactor_def]

end SelbergData

variable (hχ : χ.IsPrimitive)

/-- The **Dirichlet L-function** `L(s, χ)` (LMFDB `lfunction.dirichlet`) of a primitive Dirichlet
character `χ` modulo `N` as an analytic L-function: the Dirichlet series `∑ χ(n) n ^ (-s)`, with
Euler factors `(1 - χ(p) p ^ (-s))⁻¹`, continued by `DirichletCharacter.LFunction` and completed by
`Λ(s, χ) = N ^ (s / 2) Γ_ℝ(s + δ) L(s, χ)`, with the Selberg data
`AnalyticLFunction.SelbergData.dirichlet`, where `δ` is `0` for even `χ` and `1` for odd `χ`.
Mathlib's `DirichletCharacter.completedLFunction` is `Γ_ℝ(s + δ) L(s, χ)`, without the factor
`N ^ (s / 2)`. -/
noncomputable def dirichlet : AnalyticLFunction where
  coeff n := χ n
  toFun := LFunction χ
  completed s := (N : ℂ) ^ (s / 2) * completedLFunction χ s
  selbergData := .dirichlet χ
  coeff_one := by simp
  coeff_mul_of_coprime _ := by simp
  exists_eulerFactor p hp :=
    ⟨1 - C (χ p) * X, (by compute_degree : (1 - C (χ p) * X : ℂ[X]).natDegree ≤ 1),
      natDegree_one_sub_C_mul_X_eq_one_iff.trans
        (MulChar.apply_ne_zero_iff.trans (ZMod.isUnit_prime_iff_not_dvd hp)),
      one_sub_C_mul_X_mul_mk_eq_one⟩
  LSeriesSummable_coeff hs := LSeriesSummable_of_one_lt_re χ hs
  toFun_eq_LSeries hs := LFunction_eq_LSeries χ hs
  differentiableOn_toFun s hs := (differentiableAt_LFunction χ s (.inl hs)).differentiableWithinAt
  meromorphicAt_toFun := by
    rcases eq_or_ne N 1 with rfl | hN
    · rw [LFunction_modOne_eq]
      exact zeta.meromorphicAt_toFun
    · exact ((differentiable_LFunction (hχ.ne_one hN)).analyticAt 1).meromorphicAt
  completed_eq {s} hs := by
    rw [SelbergData.conductor_dirichlet, SelbergData.gammaFactor_dirichlet, mul_assoc,
      ← completedLFunction_eq_gammaFactor_mul (zero_lt_one.trans hs)]
  differentiableOn_completed s hs :=
    (((differentiableAt_id.div_const 2).const_cpow (.inl (NeZero.ne _))).mul
      (differentiableAt_completedLFunction χ s (.inl fun h ↦ hs (.inl h))
        (.inl fun h ↦ hs (.inr h)))).differentiableWithinAt
  completed_eq_sign_mul_conj {s} hs₀ _ := by
    have h₁ : conj (completedLFunction χ (1 - conj s)) = completedLFunction χ⁻¹ (1 - s) := by
      rw [← conj_conj (completedLFunction χ⁻¹ (1 - s)),
        ← completedLFunction_conj χ fun h ↦ hs₀ (sub_eq_self.mp h), map_sub, map_one]
    have h₂ : conj ((N : ℂ) ^ ((1 - conj s) / 2)) = (N : ℂ) ^ ((1 - s) / 2) := by
      rw [(by rw [map_div₀, map_sub, map_one, map_ofNat] : (1 - conj s) / 2 = conj ((1 - s) / 2)),
        ← conj_cpow _ _ (natCast_arg ▸ Real.pi_ne_zero.symm), conj_natCast]
    have h₃ : completedLFunction χ s =
        (N : ℂ) ^ (1 - s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ (1 - s) := by
      rw [← hχ.completedLFunction_one_sub, sub_sub_cancel]
    rw [SelbergData.sign_dirichlet, map_mul, h₁, h₂, h₃, ← mul_assoc, ← mul_assoc,
      ← cpow_add _ _ (NeZero.ne _), (by ring1 : s / 2 + (1 - s - 1 / 2) = (1 - s) / 2)]
    ring1

@[simp]
lemma dirichlet_coeff : (dirichlet hχ).coeff = fun n : ℕ ↦ χ n :=
  rfl

@[simp]
lemma dirichlet_toFun : (dirichlet hχ).toFun = LFunction χ :=
  rfl

@[simp]
lemma dirichlet_completed :
    (dirichlet hχ).completed = fun s ↦ (N : ℂ) ^ (s / 2) * completedLFunction χ s :=
  rfl

@[simp]
lemma dirichlet_selbergData : (dirichlet hχ).selbergData = .dirichlet χ :=
  rfl

@[simp]
lemma degree_dirichlet : (dirichlet hχ).degree = 1 :=
  rfl

@[simp]
lemma conductor_dirichlet : (dirichlet hχ).conductor = N :=
  rfl

@[simp]
lemma sign_dirichlet : (dirichlet hχ).sign = rootNumber χ :=
  rfl

/-- **The Euler factor of a Dirichlet L-function** (LMFDB `lfunction.dirichlet`) at a prime `p` is
`1 - χ(p) T`. -/
lemma eulerPolynomial_dirichlet (hp : p.Prime) :
    (dirichlet hχ).eulerPolynomial p = 1 - C (χ p) * X :=
  eulerPolynomial_eq hp one_sub_C_mul_X_mul_mk_eq_one

/-- **Modulo `1`, the Dirichlet L-function is the Riemann zeta function**
`AnalyticLFunction.zeta`. -/
lemma dirichlet_eq_zeta (hN : N = 1) : dirichlet hχ = zeta := by
  subst hN
  rcases level_one χ with rfl
  simp only [dirichlet, zeta]
  congr 1
  · exact funext fun n ↦ MulChar.one_apply (isUnit_of_subsingleton _)
  · exact LFunction_modOne_eq
  · ext s
    rw [Nat.cast_one, one_cpow, one_mul, completedLFunction_modOne_eq]
  · simp only [SelbergData.dirichlet]
    congr 1
    · exact congrArg singleton <| ite_eq_left <| MulChar.one_apply <| isUnit_of_subsingleton _
    · exact rootNumber_modOne 1

end AnalyticLFunction

namespace DirichletCharacter

variable [NeZero N] in
/-- **The root number of a primitive Dirichlet character has absolute value `1`**: it is the sign
of the functional equation of `AnalyticLFunction.dirichlet`. -/
lemma IsPrimitive.norm_rootNumber (hχ : χ.IsPrimitive) : ‖rootNumber χ‖ = 1 :=
  (AnalyticLFunction.dirichlet hχ).norm_sign

end DirichletCharacter
