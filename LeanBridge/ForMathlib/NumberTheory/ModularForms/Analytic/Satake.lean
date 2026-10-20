import TauCeti.NumberTheory.ModularForms.Newforms.Satake

/-!
# Satake parameters and Satake angles of a newform, in the LMFDB normalisation

Let `f` be a newform of level `N`, weight `k` and character `χ`, and let `p` be a good prime. The
LMFDB's Satake parameters of `f` at `p` are the reciprocal roots `α_p` of `L_p(p^{-(k-1)/2} t)`,
where `L_p(t) = 1 - a_p t + χ(p) p^{k-1} t²`; that is, the roots of
`X² - a_p p^{-(k-1)/2} X + χ(p)`. They are Tau Ceti's Satake parameters
`HeckeRing.GL2.Newform.satakeParameters`, the roots of `X² - a_p X + χ(p) p^{k-1}`, divided by
`p^{(k-1)/2}`. Their product is `χ(p)`, so they are `α_p` and `α_p⁻¹ χ(p)`, and by the
Ramanujan–Deligne bound (not proved here) they lie on the unit circle. The Satake angles are their
arguments `θ_p = arg α_p`.

## Main definitions

* `HeckeRing.GL2.Newform.normalizedSatakeParameters` (LMFDB `cmf.satake_parameters`).
* `HeckeRing.GL2.Newform.satakeAngles` (LMFDB `cmf.satake_angles`).

## Main results

* `HeckeRing.GL2.Newform.normalizedSatakeParameters_eq_pair_iff`: `{α, β}` are the Satake
  parameters exactly when `α + β = a_p p^{-(k-1)/2}` and `α β = χ(p)`.
* `HeckeRing.GL2.Newform.prod_map_one_sub_mul_normalizedSatakeParameters`: they are the
  reciprocal roots of `L_p(p^{-(k-1)/2} t)`.
* `HeckeRing.GL2.Newform.normalizedSatakeParameters_eq_map_div`: they are Tau Ceti's Satake
  parameters divided by `p^{(k-1)/2}`.
* `HeckeRing.GL2.Newform.normalizedSatakeParameters_eq_pair_inv_mul`: at a good prime they are
  `α_p` and `α_p⁻¹ χ(p)`.
* `HeckeRing.GL2.Newform.satakeAngles_eq_map_arg_satakeParameters`: the Satake angles are also the
  arguments of Tau Ceti's Satake parameters.
* `HeckeRing.GL2.Newform.normalizedSatakeParameters_eq_map_exp_satakeAngles`: when the Satake
  parameters lie on the unit circle, they are the `e^{i θ_p}`.
* `HeckeRing.GL2.Newform.satakeAngles_eq_pair_satakeAngle`: at a prime with `χ(p) = 1` and under
  the Ramanujan–Deligne bound, the Satake angles are `±θ_p`, for Tau Ceti's Satake angle
  `θ_p ∈ [0, π)`.
-/

open Polynomial UpperHalfPlane
open scoped ComplexConjugate Real

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (p : ℕ) (hp : p ≠ 0) {α β : ℂ} {θ r : ℝ}
    (hr : 0 < r)

private lemma X_sq_sub_C_mul_X_add_C_eq (b c : ℂ) :
    X ^ 2 - C b * X + C c = C 1 * X ^ 2 + C (-b) * X + C c := by
  simp [sub_eq_add_neg]

private lemma ofReal_rpow_sq :
    (((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) ^ 2 = (p : ℂ) ^ (k - 1) := by
  have hk : ((k : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = ((k - 1 : ℤ) : ℝ) := by
    push_cast
    ring1
  rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul p.cast_nonneg, hk,
    Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast]

include hp in
private lemma ofReal_rpow_ne_zero : (((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

/-- The **Satake parameters** (LMFDB `cmf.satake_parameters`) of a newform `f` at `p`, in the
LMFDB's unitary normalisation: the reciprocal roots, counted with multiplicity, of
`L_p(p^{-(k-1)/2} t) = 1 - a_p p^{-(k-1)/2} t + χ(p) t²`, i.e. the roots of
`X² - a_p p^{-(k-1)/2} X + χ(p)`, where `a_p` is the `p`-th Fourier coefficient of `f` and the
character `χ` is extended by zero to the integers not coprime to the level
(`prod_map_one_sub_mul_normalizedSatakeParameters`).

They are Tau Ceti's Satake parameters `satakeParameters`, which are taken in the arithmetic
normalisation, divided by `p^{(k-1)/2}` (`normalizedSatakeParameters_eq_map_div`). The definition
is stated for every natural number `p`, but the LMFDB defines the Satake parameters only at the
good primes `p ∤ N`, where they are `α_p` and `α_p⁻¹ χ(p)`
(`normalizedSatakeParameters_eq_pair_inv_mul`). -/
noncomputable def normalizedSatakeParameters : Multiset ℂ :=
  (X ^ 2 - C ((qExpansion 1 f.toCuspForm).coeff p / ((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ)) * X + C
    (f.dirichletLift p)).roots

/-- **The Satake parameters are characterised by their sum and product**: `{α, β}` are the
Satake parameters of `f` at `p` exactly when `α + β = a_p p^{-(k-1)/2}` and `α β = χ(p)`. -/
lemma normalizedSatakeParameters_eq_pair_iff : f.normalizedSatakeParameters p = {α, β} ↔ α + β =
    (qExpansion 1 f.toCuspForm).coeff p / ((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) ∧ α * β =
    f.dirichletLift p := by
  rw [normalizedSatakeParameters, X_sq_sub_C_mul_X_add_C_eq,
    roots_quadratic_eq_pair_iff_of_ne_zero one_ne_zero]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linear_combination h₁, by linear_combination -h₂⟩

lemma exists_normalizedSatakeParameters_eq_pair :
    ∃ α β : ℂ, f.normalizedSatakeParameters p = {α, β} := by
  apply Multiset.card_eq_two.mp
  rw [normalizedSatakeParameters, IsAlgClosed.card_roots_eq_natDegree,
    X_sq_sub_C_mul_X_add_C_eq, natDegree_quadratic one_ne_zero]

@[simp]
lemma card_normalizedSatakeParameters : Multiset.card (f.normalizedSatakeParameters p) = 2 := by
  rcases f.exists_normalizedSatakeParameters_eq_pair p with ⟨α, β, h⟩
  rw [h, Multiset.card_pair]

@[simp]
lemma sum_normalizedSatakeParameters : (f.normalizedSatakeParameters p).sum =
    (qExpansion 1 f.toCuspForm).coeff p / ((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) := by
  rcases f.exists_normalizedSatakeParameters_eq_pair p with ⟨α, β, h⟩
  rw [h, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
    ((f.normalizedSatakeParameters_eq_pair_iff p).mp h).1]

@[simp]
lemma prod_normalizedSatakeParameters :
    (f.normalizedSatakeParameters p).prod = f.dirichletLift p := by
  rcases f.exists_normalizedSatakeParameters_eq_pair p with ⟨α, β, h⟩
  rw [h, Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton,
    ((f.normalizedSatakeParameters_eq_pair_iff p).mp h).2]

include hp in
/-- **The Satake parameters are the reciprocal roots of `L_p(p^{-(k-1)/2} t)`**:
`(1 - α_p t) (1 - β_p t) = L_p(p^{-(k-1)/2} t)`, where `L_p(t) = 1 - a_p t + χ(p) p^{k-1} t²`. -/
lemma prod_map_one_sub_mul_normalizedSatakeParameters (x : ℂ) :
    ((f.normalizedSatakeParameters p).map fun α ↦ 1 - α * x).prod = 1 -
    (qExpansion 1 f.toCuspForm).coeff p * (x / ((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ)) +
    f.dirichletLift p * (p : ℂ) ^ (k - 1) * (x / ((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ)) ^ 2 := by
  rcases f.exists_normalizedSatakeParameters_eq_pair p with ⟨α, β, h⟩
  rcases (f.normalizedSatakeParameters_eq_pair_iff p).mp h with ⟨hsum, hprod⟩
  rw [h, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, ← ofReal_rpow_sq, div_pow, mul_assoc (f.dirichletLift p),
    mul_div_cancel₀ _ (pow_ne_zero 2 (ofReal_rpow_ne_zero p hp))]
  linear_combination (-x) * hsum + x ^ 2 * hprod

include hp in
/-- **The Satake parameters are Tau Ceti's divided by `p^{(k-1)/2}`**: the LMFDB's unitary
normalisation of Tau Ceti's arithmetically normalised `satakeParameters`. -/
lemma normalizedSatakeParameters_eq_map_div : f.normalizedSatakeParameters p =
    (f.satakeParameters p).map fun α : ℂ ↦ α / ((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) := by
  rcases f.exists_satakeParameters_eq_pair p with ⟨α, β, h⟩
  rcases (f.satakeParameters_eq_pair_iff p).mp h with ⟨hsum, hprod⟩
  rw [h, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    ← Multiset.insert_eq_cons, normalizedSatakeParameters_eq_pair_iff, ← add_div, hsum,
    div_mul_div_comm, hprod, ← ofReal_rpow_sq, sq,
    mul_div_cancel_right₀ _ (mul_ne_zero (ofReal_rpow_ne_zero p hp) (ofReal_rpow_ne_zero p hp))]
  exact ⟨rfl, rfl⟩

/-- **The Satake parameters at a good prime are `α_p` and `α_p⁻¹ χ(p)`**, for either of them
`α_p`: the factorisation `L_p(t) = (1 - α_p p^{(k-1)/2} t) (1 - α_p⁻¹ χ(p) p^{(k-1)/2} t)`. -/
lemma normalizedSatakeParameters_eq_pair_inv_mul (hpN : p.Coprime N)
    (hα : α ∈ f.normalizedSatakeParameters p) :
    f.normalizedSatakeParameters p = {α, α⁻¹ * f.dirichletLift p} := by
  rcases f.exists_normalizedSatakeParameters_eq_pair p with ⟨β, γ, h⟩
  rcases (f.normalizedSatakeParameters_eq_pair_iff p).mp h with ⟨-, hprod⟩
  have hχ : f.dirichletLift p ≠ 0 := by
    rw [f.dirichletLift_apply_of_coprime hpN]
    exact Units.ne_zero _
  rw [h, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hα
  rw [h]
  rcases hα with rfl | rfl
  · rw [← hprod, inv_mul_cancel_left₀ (left_ne_zero_of_mul (hprod ▸ hχ))]
  · rw [← hprod, mul_comm, mul_inv_cancel_right₀ (right_ne_zero_of_mul (hprod ▸ hχ)),
      Multiset.pair_comm]

/-- The **Satake angles** (LMFDB `cmf.satake_angles`) of a newform `f` at `p`: the arguments
`θ_p = arg α_p` of its Satake parameters `normalizedSatakeParameters`, a multiset of two real
numbers. The newform `f` is complex-valued, so it is one complex embedding of the LMFDB's newform.
The LMFDB writes the range of the angles as `[-π, π]`; Mathlib's `Complex.arg` takes values in
`(-π, π]`. When the Satake parameters lie on the unit circle, as they do at the good primes by
the Ramanujan–Deligne bound, they are the `e^{i θ_p}`
(`normalizedSatakeParameters_eq_map_exp_satakeAngles`). -/
noncomputable def satakeAngles : Multiset ℝ :=
  (f.normalizedSatakeParameters p).map Complex.arg

@[simp]
lemma card_satakeAngles : Multiset.card (f.satakeAngles p) = 2 := by
  rw [satakeAngles, Multiset.card_map, card_normalizedSatakeParameters]

lemma mem_Ioc_of_mem_satakeAngles (hθ : θ ∈ f.satakeAngles p) : θ ∈ Set.Ioc (-π) π := by
  rcases Multiset.mem_map.mp hθ with ⟨α, -, rfl⟩
  exact ⟨α.neg_pi_lt_arg, α.arg_le_pi⟩

include hp in
/-- **The Satake angles are the arguments of Tau Ceti's Satake parameters**: dividing by the
positive real number `p^{(k-1)/2}` does not change the arguments. -/
lemma satakeAngles_eq_map_arg_satakeParameters :
    f.satakeAngles p = (f.satakeParameters p).map Complex.arg := by
  rw [satakeAngles, f.normalizedSatakeParameters_eq_map_div p hp, Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ ↦ ?_
  rw [Function.comp_apply, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.arg_mul_real (by positivity)]

/-- **The Satake parameters on the unit circle are the `e^{i θ_p}`**: when they have absolute
value `1`, as the Ramanujan–Deligne bound gives at the good primes, the Satake parameters are
determined by the Satake angles. -/
lemma normalizedSatakeParameters_eq_map_exp_satakeAngles
    (h : ∀ α ∈ f.normalizedSatakeParameters p, ‖α‖ = 1) : f.normalizedSatakeParameters p =
    (f.satakeAngles p).map fun θ : ℝ ↦ Complex.exp (θ * Complex.I) := by
  rw [satakeAngles, Multiset.map_map]
  refine (Multiset.map_id _).symm.trans (Multiset.map_congr rfl fun α hα ↦ ?_)
  rw [id, Function.comp_apply, ← one_mul (Complex.exp _), ← Complex.ofReal_one, ← h α hα,
    Complex.norm_mul_exp_arg_mul_I]

include hr in
private lemma arg_ofReal_mul_exp_mul_I (hθ : θ ∈ Set.Ioc (-π) π) :
    Complex.arg (r * Complex.exp (θ * Complex.I)) = θ := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_mul_cos_add_sin_mul_I hr hθ

include hr in
private lemma map_arg_pair_ofReal_mul_exp (h₀ : 0 ≤ θ) (hπ : θ < π) : Multiset.map Complex.arg
    {(r : ℂ) * Complex.exp (θ * Complex.I), (r : ℂ) * Complex.exp (-θ * Complex.I)} = {θ, -θ} := by
  rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, ← Multiset.insert_eq_cons,
    ← Complex.ofReal_neg, arg_ofReal_mul_exp_mul_I hr ⟨by linarith [Real.pi_pos], hπ.le⟩,
    arg_ofReal_mul_exp_mul_I hr ⟨by linarith, by linarith [Real.pi_pos]⟩]

/-- **The Satake angles at a prime with `χ(p) = 1`**: under the Ramanujan–Deligne bound
`|a_p| ≤ 2 p^{(k-1)/2}`, they are `±θ_p` for Tau Ceti's Satake angle `θ_p`, the unique angle in
`[0, π]` with `a_p = 2 p^{(k-1)/2} cos θ_p`, provided `θ_p ≠ π`. Tau Ceti's angle takes as an
argument that `a_p` is real, which follows from `χ(p) = 1`
(`conj_qExpansion_coeff_eq_self_of_dirichletLift_eq_one`). -/
lemma satakeAngles_eq_pair_satakeAngle (hpp : p.Prime) (hχ : f.dirichletLift p = 1)
    (hreal : conj ((qExpansion 1 f.toCuspForm).coeff p) = (qExpansion 1 f.toCuspForm).coeff p)
    (hR : ‖(qExpansion 1 f.toCuspForm).coeff p‖ ≤ 2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2))
    (hπ : f.satakeAngle hpp hreal hR ≠ π) :
    f.satakeAngles p = {f.satakeAngle hpp hreal hR, -f.satakeAngle hpp hreal hR} := by
  rw [f.satakeAngles_eq_map_arg_satakeParameters p hpp.ne_zero,
    f.satakeParameters_eq_exp_satakeAngle hpp hR hχ]
  exact map_arg_pair_ofReal_mul_exp (Real.rpow_pos_of_pos (mod_cast hpp.pos) _)
    (f.satakeAngle_nonneg hpp _ hR) ((f.satakeAngle_le_pi hpp _ hR).lt_of_ne hπ)

end HeckeRing.GL2.Newform
