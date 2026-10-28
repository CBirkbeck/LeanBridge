import LeanBridge.ForMathlib.NumberTheory.LFunction.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The central character of an analytic L-function

An analytic L-function of degree `d` and conductor `N` has an Euler product
`L(s) = ∏ₚ Lₚ(p ^ (-s))⁻¹` with `Lₚ(x) = 1 + a_p x + ⋯ + (-1) ^ d χ(p) x ^ d`, and the Dirichlet
character `χ` modulo `N` is its central character. The axioms of an analytic L-function do not
force the top coefficients of the Euler factors to come from a Dirichlet character, so the central
character is a predicate on Dirichlet characters modulo `N`; by Dirichlet's theorem on primes in
arithmetic progressions there is at most one.

## Main definitions

* `AnalyticLFunction.eulerFactor`: the Euler factor `Lₚ(x)` of an analytic L-function, as a power
  series.
* `AnalyticLFunction.IsCentralCharacter` (LMFDB `lfunction.central_character`): a Dirichlet
  character modulo the conductor is the central character of an analytic L-function.

## Main results

* `AnalyticLFunction.eulerFactor_eq`: the Euler factor at a prime is the polynomial of the Euler
  product of an analytic L-function.
* `AnalyticLFunction.coeff_degree_eulerFactor_of_dvd`: at a prime dividing the conductor, the
  coefficient of `x ^ d` of the Euler factor vanishes, like `χ(p)`.
* `AnalyticLFunction.IsCentralCharacter.eq`: an analytic L-function has at most one central
  character.
-/

open PowerSeries
open scoped Polynomial

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {p : ℕ} {χ χ' : DirichletCharacter ℂ L.conductor}

variable (p) in
/-- The **Euler factor** `Lₚ(x)` of an analytic L-function at `p`, as a power series: the inverse
of the local series `∑ₖ a_{pᵏ} xᵏ`, so that `L(s) = ∏ₚ Lₚ(p ^ (-s))⁻¹`. At a prime it is a
polynomial of degree at most the degree of the L-function (`eulerFactor_eq`). -/
noncomputable def eulerFactor : ℂ⟦X⟧ :=
  (PowerSeries.mk fun k ↦ L.coeff (p ^ k))⁻¹

/-- The Euler factor at a prime is the polynomial `Fₚ` of the Euler product of an analytic
L-function, the polynomial with `Fₚ(x) ∑ₖ a_{pᵏ} xᵏ = 1`. -/
lemma eulerFactor_eq {F : ℂ[X]}
    (hF : (F : ℂ⟦X⟧) * PowerSeries.mk (fun k ↦ L.coeff (p ^ k)) = 1) : L.eulerFactor p = F :=
  ((eq_inv_iff_mul_eq_one <| by simp [L.coeff_one]).mpr hF).symm

/-- At a prime dividing the conductor, the coefficient of `x ^ d` of the Euler factor vanishes,
where `d` is the degree. -/
lemma coeff_degree_eulerFactor_of_dvd (hp : p.Prime) (hpN : p ∣ L.conductor) :
    PowerSeries.coeff L.degree (L.eulerFactor p) = 0 := by
  rcases L.exists_eulerFactor p hp with ⟨F, hFd, hFN, hF⟩
  rw [L.eulerFactor_eq hF, Polynomial.coeff_coe]
  exact F.coeff_eq_zero_of_natDegree_lt <| hFd.lt_of_ne fun h ↦ hFN.mp h hpN

/-- A Dirichlet character `χ` modulo the conductor `N` is the **central character** (LMFDB
`lfunction.central_character`) of an analytic L-function of degree `d` when every Euler factor
has the form `Lₚ(x) = 1 + a_p x + ⋯ + (-1) ^ d χ(p) x ^ d`. At a prime `p ∣ N` both sides of the
condition vanish (`coeff_degree_eulerFactor_of_dvd`), so it is a condition on the primes `p ∤ N`.
The axioms of an analytic L-function do not imply that such a character exists, but there is at
most one (`IsCentralCharacter.eq`). -/
def IsCentralCharacter (χ : DirichletCharacter ℂ L.conductor) : Prop :=
  ∀ p : ℕ, p.Prime → PowerSeries.coeff L.degree (L.eulerFactor p) = (-1) ^ L.degree * χ p

variable {L} in
/-- An analytic L-function has at most one central character. -/
lemma IsCentralCharacter.eq (hχ : L.IsCentralCharacter χ) (hχ' : L.IsCentralCharacter χ') :
    χ = χ' := by
  have hN : NeZero L.conductor :=
    ⟨L.selbergData.conductor_pos.ne'⟩
  refine MulChar.ext fun u ↦ ?_
  rcases Nat.forall_exists_prime_gt_and_eq_mod u.isUnit 0 with ⟨p, -, hp, hpu⟩
  rw [← hpu]
  exact mul_left_cancel₀ (pow_ne_zero _ <| neg_ne_zero.mpr one_ne_zero) <|
    (hχ p hp).symm.trans (hχ' p hp)

end AnalyticLFunction
