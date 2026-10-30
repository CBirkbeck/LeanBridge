import LeanBridge.ForMathlib.NumberTheory.LFunction.CentralCharacter
import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannZeta
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.List.Sym
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Symmetric powers of an L-function

Let `L(s) = ∏_{p ∉ S} ∏ⱼ (1 - αⱼ(p) p ^ (-s))⁻¹ × ∏_{p ∈ S} L_p(s)` be an L-function with an Euler
product, of degree `r` outside a finite set `S` of primes. Its symmetric `n`-th power (LMFDB
`lfunction.symm`) is the L-function

`L(s, symⁿ) = ∏_{p ∉ S} ∏_m (1 - m(α₁(p), …, α_r(p)) p ^ (-s))⁻¹ × ∏_{p ∈ S} L_p(s, symⁿ)`,

where `m` runs over the degree-`n` monomials in `r` variables. The knowl leaves the Euler factors
at the primes of `S` to "a more complicated recipe", which needs more information on the underlying
object than `L`.

For an analytic L-function (`AnalyticLFunction`) of degree `d` and conductor `N`, `S` is the set of
primes dividing `N`: at the other primes the Euler factor `L_p(T)` has degree `d`, and its
reciprocal roots are the `d` **Satake parameters** `αⱼ(p)`, so that `L_p(T) = ∏ⱼ (1 - αⱼ(p) T)`. An
analytic L-function `M` is the symmetric `n`-th power of `L` when its Euler factor at every prime
`p ∤ N` is `∏_m (1 - m(α(p)) T)`. Its existence, that is the analytic continuation and functional
equation of `L(s, symⁿ)`, is symmetric-power functoriality, known only in special cases. Its degree
is the number `multichoose d n = (d + n - 1).choose n` of monomials, the symmetric first power of
`L` is `L` and the symmetric zeroth power of `L` is the Riemann zeta function.

## Main definitions

* `AnalyticLFunction.eulerPolynomial`: the Euler factor `L_p(T)` of an analytic L-function at `p`,
  as a polynomial.
* `AnalyticLFunction.satakeParameters`: the Satake parameters, the reciprocal roots of `L_p(T)`.
* `AnalyticLFunction.symmetricPowerSatakeParameters` (LMFDB `lfunction.symm`): the degree-`n`
  monomials in the Satake parameters.
* `AnalyticLFunction.symmetricPowerEulerFactor` (LMFDB `lfunction.symm`): the Euler factor
  `∏_m (1 - m T)` of the symmetric `n`-th power at a prime not dividing the conductor.
* `AnalyticLFunction.IsSymmetricPower` (LMFDB `lfunction.symm`): an analytic L-function is the
  symmetric `n`-th power of another.

## Main results

* `AnalyticLFunction.coe_eulerPolynomial`: at a prime, `eulerPolynomial` is the Euler factor.
* `AnalyticLFunction.prod_one_sub_C_mul_X_satakeParameters`: `L_p(T) = ∏ⱼ (1 - αⱼ(p) T)`.
* `AnalyticLFunction.card_satakeParameters`: at a prime not dividing the conductor there are `d`
  Satake parameters.
* `AnalyticLFunction.card_symmetricPowerSatakeParameters`: there are `multichoose r n` monomials of
  degree `n` in `r` Satake parameters.
* `AnalyticLFunction.isSymmetricPower_one`: an analytic L-function is its own symmetric first power.
* `AnalyticLFunction.isSymmetricPower_zero_zeta`: the Riemann zeta function is the symmetric zeroth
  power of every analytic L-function.
* `AnalyticLFunction.IsSymmetricPower.degree_eq`: the symmetric `n`-th power of an analytic
  L-function of degree `d` has degree `multichoose d n`.
-/

open Polynomial

open scoped PowerSeries

namespace AnalyticLFunction

variable (L : AnalyticLFunction) (n p : ℕ)

/-- The **Euler factor** `L_p(T)` of an analytic L-function `L` of degree `d` at `p`, as a
polynomial: the truncation in degree at most `d` of the power series
`AnalyticLFunction.eulerFactor`, which at a prime is the polynomial of the Euler product
(`coe_eulerPolynomial`), so that `L(s) = ∏ₚ L_p(p ^ (-s))⁻¹`. -/
noncomputable def eulerPolynomial : ℂ[X] :=
  PowerSeries.trunc (L.degree + 1) (L.eulerFactor p)

/-- The **Satake parameters** `α₁(p), …, α_r(p)` of an analytic L-function at `p`: the reciprocal
roots of its Euler factor `L_p(T)`, so that `L_p(T) = ∏ⱼ (1 - αⱼ(p) T)`
(`prod_one_sub_C_mul_X_satakeParameters`). At a prime not dividing the conductor there are `d` of
them, `d` the degree (`card_satakeParameters`). -/
noncomputable def satakeParameters : Multiset ℂ :=
  (L.eulerPolynomial p).roots.map (·⁻¹)

/-- The **Satake parameters of the symmetric `n`-th power** (LMFDB `lfunction.symm`) of an analytic
L-function at `p`: the degree-`n` monomials `α_{i₁} ⋯ α_{iₙ}` in its Satake parameters
`α₁, …, α_r`, one for each multiset `{i₁, …, iₙ}` of `n` indices, of which there are
`multichoose r n` (`card_symmetricPowerSatakeParameters`). The indices are the positions in the
list `Multiset.toList` of the Satake parameters, so that a repeated parameter is counted as often
as it occurs. -/
noncomputable def symmetricPowerSatakeParameters : Multiset ℂ :=
  ((L.satakeParameters p).toList.sym n).map fun s : Sym ℂ n ↦ (s : Multiset ℂ).prod

/-- The **Euler factor of the symmetric `n`-th power** (LMFDB `lfunction.symm`) of an analytic
L-function at a prime `p` not dividing its conductor: `∏_m (1 - m T)`, where `m` runs over the
degree-`n` monomials in the Satake parameters at `p`. -/
noncomputable def symmetricPowerEulerFactor : ℂ[X] :=
  ((L.symmetricPowerSatakeParameters n p).map fun m ↦ 1 - C m * X).prod

/-- An analytic L-function `M` is the **symmetric `n`-th power** `L(s, symⁿ)` of an analytic
L-function `L` (LMFDB `lfunction.symm`) if its Euler factor at every prime `p` not dividing the
conductor of `L` is `∏_m (1 - m T)`, where `m` runs over the degree-`n` monomials in the Satake
parameters of `L` at `p`. The Euler factors at the primes dividing the conductor of `L` are given in
the knowl by a recipe that needs more information than `L` and that it does not state, so they are
not constrained. The knowl also claims that they have smaller degree than the others, which fails
in general: twisting an elliptic curve with good reduction at `p` by a quadratic character ramified
at `p` gives a curve with additive reduction at `p`, whose symmetric square, the same as that of the
untwisted curve, has an Euler factor of full degree `3` at `p`. -/
def IsSymmetricPower (M : AnalyticLFunction) : Prop :=
  ∀ p : ℕ, p.Prime → ¬p ∣ L.conductor → M.eulerFactor p = L.symmetricPowerEulerFactor n p

variable {L n p} {M : AnalyticLFunction}

/-- **At a prime, `eulerPolynomial` is the Euler factor** of the Euler product. -/
lemma coe_eulerPolynomial (hp : p.Prime) : (L.eulerPolynomial p : ℂ⟦X⟧) = L.eulerFactor p := by
  rcases L.exists_eulerFactor p hp with ⟨F, hFd, -, hF⟩
  rw [eulerPolynomial, L.eulerFactor_eq hF,
    PowerSeries.trunc_coe_eq_self (n := L.degree + 1) (Nat.lt_add_one_of_le hFd)]

lemma eulerPolynomial_eq (hp : p.Prime) {F : ℂ[X]}
    (hF : (F : ℂ⟦X⟧) * PowerSeries.mk (fun k ↦ L.coeff (p ^ k)) = 1) : L.eulerPolynomial p = F :=
  coe_inj.mp <| (coe_eulerPolynomial hp).trans (L.eulerFactor_eq hF)

lemma natDegree_eulerPolynomial (hp : p.Prime) (hpN : ¬p ∣ L.conductor) :
    (L.eulerPolynomial p).natDegree = L.degree := by
  rcases L.exists_eulerFactor p hp with ⟨F, -, hFN, hF⟩
  rw [eulerPolynomial_eq hp hF]
  exact hFN.mpr hpN

lemma coeff_zero_eulerPolynomial : (L.eulerPolynomial p).coeff 0 = 1 := by
  rw [eulerPolynomial, PowerSeries.coeff_trunc, ite_eq_left (Nat.succ_pos _), eulerFactor,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv]
  simp [L.coeff_one]

lemma ne_zero_of_mem_roots_eulerPolynomial {r : ℂ} (hr : r ∈ (L.eulerPolynomial p).roots) :
    r ≠ 0 := by
  rintro rfl
  rw [mem_roots', IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero_eulerPolynomial] at hr
  exact one_ne_zero hr.2

lemma ne_zero_of_mem_satakeParameters {α : ℂ} (hα : α ∈ L.satakeParameters p) : α ≠ 0 := by
  rcases Multiset.mem_map.mp hα with ⟨r, hr, rfl⟩
  exact inv_ne_zero <| ne_zero_of_mem_roots_eulerPolynomial hr

/-- **The Euler factor is `L_p(T) = ∏ⱼ (1 - αⱼ(p) T)`** over the Satake parameters `αⱼ(p)`: over
`ℂ` the Euler factor splits, and its constant coefficient is `1`. -/
lemma prod_one_sub_C_mul_X_satakeParameters :
    ((L.satakeParameters p).map fun α ↦ 1 - C α * X).prod = L.eulerPolynomial p := by
  have h₁ : C (L.eulerPolynomial p).leadingCoeff *
      ((L.eulerPolynomial p).roots.map fun r ↦ X - C r).prod = L.eulerPolynomial p :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have h₂ : (L.eulerPolynomial p).leadingCoeff *
      ((L.eulerPolynomial p).roots.map fun r ↦ -r).prod = 1 := by
    have h : eval 0 (C (L.eulerPolynomial p).leadingCoeff *
        ((L.eulerPolynomial p).roots.map fun r ↦ X - C r).prod) = eval 0 (L.eulerPolynomial p) :=
      congrArg (eval 0) h₁
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, ← coeff_zero_eq_eval_zero,
      coeff_zero_eulerPolynomial] at h
    simpa using h
  have h₃ :
      ((L.eulerPolynomial p).roots.map fun r ↦ -r⁻¹).prod = (L.eulerPolynomial p).leadingCoeff := by
    rw [eq_inv_of_mul_eq_one_left h₂, ← Multiset.prod_map_inv]
    simp only [neg_inv]
  rw [← h₁, satakeParameters, Multiset.map_map, ← h₃, map_multiset_prod, Multiset.map_map,
    ← Multiset.prod_map_mul]
  refine congrArg Multiset.prod <| Multiset.map_congr rfl fun r hr ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, map_neg, mul_sub, neg_mul, neg_mul, ← C_mul,
    inv_mul_cancel₀ (ne_zero_of_mem_roots_eulerPolynomial hr), C_1]
  ring1

/-- **There are `d` Satake parameters at a prime not dividing the conductor**, `d` the degree,
where the Euler factor has degree `d`. -/
lemma card_satakeParameters (hp : p.Prime) (hpN : ¬p ∣ L.conductor) :
    (L.satakeParameters p).card = L.degree := by
  rw [satakeParameters, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree,
    natDegree_eulerPolynomial hp hpN]

/-- **There are `multichoose r n` monomials of degree `n` in `r` Satake parameters**, that is
`(r + n - 1).choose n`. -/
lemma card_symmetricPowerSatakeParameters :
    (L.symmetricPowerSatakeParameters n p).card = (L.satakeParameters p).card.multichoose n := by
  rw [symmetricPowerSatakeParameters, Multiset.coe_card, List.length_map, List.length_sym,
    Multiset.length_toList]

lemma ne_zero_of_mem_symmetricPowerSatakeParameters {m : ℂ}
    (hm : m ∈ L.symmetricPowerSatakeParameters n p) : m ≠ 0 := by
  rcases List.mem_map.mp (Multiset.mem_coe.mp hm) with ⟨s, hs, rfl⟩
  exact Multiset.prod_ne_zero fun h ↦ ne_zero_of_mem_satakeParameters
    (Multiset.mem_toList.mp <| List.mem_of_mem_of_mem_sym h hs) rfl

lemma symmetricPowerSatakeParameters_zero : L.symmetricPowerSatakeParameters 0 p = {1} := by
  simp [symmetricPowerSatakeParameters, List.sym]

lemma symmetricPowerSatakeParameters_one :
    L.symmetricPowerSatakeParameters 1 p = L.satakeParameters p := by
  have h : ((fun s : Sym ℂ 1 ↦ (s : Multiset ℂ).prod) ∘ fun x ↦ x ::ₛ Sym.nil) = id :=
    funext fun x ↦ by simp [Sym.coe_cons]
  rw [symmetricPowerSatakeParameters, List.sym_one_eq, List.map_map, h, List.map_id,
    Multiset.coe_toList]

lemma symmetricPowerEulerFactor_zero : L.symmetricPowerEulerFactor 0 p = 1 - X := by
  simp [symmetricPowerEulerFactor, symmetricPowerSatakeParameters_zero]

lemma symmetricPowerEulerFactor_one : L.symmetricPowerEulerFactor 1 p = L.eulerPolynomial p := by
  rw [symmetricPowerEulerFactor, symmetricPowerSatakeParameters_one,
    prod_one_sub_C_mul_X_satakeParameters]

lemma natDegree_symmetricPowerEulerFactor :
    (L.symmetricPowerEulerFactor n p).natDegree = (L.symmetricPowerSatakeParameters n p).card := by
  have h (m : ℂ) (hm : m ∈ L.symmetricPowerSatakeParameters n p) :
      (natDegree ∘ fun a ↦ 1 - C a * X) m = 1 := by
    have hm₀ : m ≠ 0 :=
      ne_zero_of_mem_symmetricPowerSatakeParameters hm
    rw [Function.comp_apply, natDegree_sub_eq_right_of_natDegree_lt (by simp [hm₀]),
      natDegree_C_mul_X m hm₀]
  rw [symmetricPowerEulerFactor, natDegree_multiset_prod, Multiset.map_map,
    Multiset.map_congr rfl h, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  intro h₀
  rcases Multiset.mem_map.mp h₀ with ⟨m, -, hm⟩
  simpa using congrArg (fun q : ℂ[X] ↦ q.coeff 0) hm

variable (L) in
/-- **An analytic L-function is its own symmetric first power**: the degree-`1` monomials in the
Satake parameters are the Satake parameters. -/
lemma isSymmetricPower_one : L.IsSymmetricPower 1 L :=
  fun _ hp _ ↦ by rw [symmetricPowerEulerFactor_one, coe_eulerPolynomial hp]

variable (L) in
/-- **The Riemann zeta function is the symmetric zeroth power of every analytic L-function**: the
only monomial of degree `0` is `1`, which gives the Euler factors `1 - T` of `ζ`. -/
lemma isSymmetricPower_zero_zeta : L.IsSymmetricPower 0 zeta := by
  intro _ _ _
  rw [symmetricPowerEulerFactor_zero]
  refine zeta.eulerFactor_eq ?_
  rw [mul_comm, coe_sub, coe_one, coe_X]
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℂ

/-- **The symmetric `n`-th power of an analytic L-function of degree `d` has degree
`multichoose d n`**, that is `(d + n - 1).choose n`: at a prime dividing neither conductor, both
sides are the degree of the Euler factor, a product of `multichoose d n` factors `1 - m T` with
`m ≠ 0`. -/
lemma IsSymmetricPower.degree_eq (h : L.IsSymmetricPower n M) :
    M.degree = L.degree.multichoose n := by
  rcases Nat.exists_infinite_primes (L.conductor * M.conductor + 1) with ⟨p, hpN, hp⟩
  have hpL : ¬p ∣ L.conductor :=
    Nat.not_dvd_of_pos_of_lt L.selbergData.conductor_pos
      ((Nat.le_mul_of_pos_right _ M.selbergData.conductor_pos).trans_lt hpN)
  have hpM : ¬p ∣ M.conductor :=
    Nat.not_dvd_of_pos_of_lt M.selbergData.conductor_pos
      ((Nat.le_mul_of_pos_left _ L.selbergData.conductor_pos).trans_lt hpN)
  rw [← natDegree_eulerPolynomial hp hpM, ← card_satakeParameters hp hpL,
    ← card_symmetricPowerSatakeParameters, ← natDegree_symmetricPowerEulerFactor,
    coe_inj.mp <| (coe_eulerPolynomial hp).trans (h p hp hpL)]

end AnalyticLFunction
