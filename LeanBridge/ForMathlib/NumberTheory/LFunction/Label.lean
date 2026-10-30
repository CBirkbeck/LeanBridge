import LeanBridge.ForMathlib.NumberTheory.LFunction.CentralCharacter
import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannZeta

/-!
# The label of an L-function

The LMFDB label of an L-function `L` has the form `d-N-q.k-x-y-i` (LMFDB `lfunction.label`), where
`d` is the degree of `L`, `N` its conductor, `q.k` the Conrey label of the primitive Dirichlet
character from which the central character of `L` is induced, `x-y` the spectral label of `L`
(LeanBridge's `AnalyticLFunction.spectralLabel`), and `i` an index that tells apart L-functions
that would otherwise have the same label.

For an analytic L-function (`AnalyticLFunction`) we formalise the prefix `d-N-q`. The modulus `q`
of the primitive character `χ.primitiveCharacter` inducing the central character `χ`
(`AnalyticLFunction.IsCentralCharacter`; `χ` is induced from it by
`DirichletCharacter.changeLevel_primitiveCharacter`) is the conductor of `χ`. The Conrey index
`k` is not formalised: the Conrey labelling of Dirichlet characters is not available in the
pinned versions of Mathlib, Tau Ceti and LeanBridge. The index `i` is a numbering of the database,
which the knowl does not specify, and is not formalised either. The conductor is written in
decimal; the knowl's abbreviation `men` of some perfect powers `N = m ^ n`, a display convention,
is not reproduced.

## Main definitions

* `AnalyticLFunction.centralCharacterConductor` (LMFDB `lfunction.label`): the modulus `q` of the
  primitive character inducing the central character.
* `AnalyticLFunction.labelPrefix` (LMFDB `lfunction.label`): the prefix `d-N-q` of the label.

## Main results

* `AnalyticLFunction.IsCentralCharacter.centralCharacterConductor_eq`: `q` is the conductor of the
  central character.
* `AnalyticLFunction.isCentralCharacter_zeta`: the central character of the Riemann zeta function
  is trivial.
* `AnalyticLFunction.labelPrefix_zeta`: the label prefix of the Riemann zeta function is `1-1-1`,
  as in its label `1-1-1.1-r0-0-0`.
-/

open Polynomial (X)

open scoped Polynomial PowerSeries

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {χ : DirichletCharacter ℂ L.conductor}

open scoped Classical in
/-- The **modulus `q` of the primitive character inducing the central character** (LMFDB
`lfunction.label`) of an analytic L-function `L`: the conductor (Mathlib's
`DirichletCharacter.conductor`) of the central character `χ` of `L`
(`IsCentralCharacter.centralCharacterConductor_eq`), which is the modulus of the primitive
character `χ.primitiveCharacter` from which `χ` is induced
(`DirichletCharacter.changeLevel_primitiveCharacter`). The axioms of an analytic L-function do
not force a central character to exist; it is unique when it does (`IsCentralCharacter.eq`), and
`q` takes the junk value `0` when it does not. -/
noncomputable def centralCharacterConductor : ℕ :=
  if h : ∃ χ, L.IsCentralCharacter χ then h.choose.conductor else 0

/-- The **label prefix** `d-N-q` of an analytic L-function `L` (LMFDB `lfunction.label`): its
degree `d`, its conductor `N` and the modulus `q` of the primitive character inducing its central
character (`centralCharacterConductor`), in decimal and separated by hyphens. The LMFDB label of
`L` is `d-N-q.k-x-y-i`, where `x-y` is the spectral label `AnalyticLFunction.spectralLabel`, `k`
is the Conrey index of the primitive character, which is not formalised, and `i` is an index of
the database, which the knowl does not specify. -/
noncomputable def labelPrefix : String :=
  toString L.degree ++ "-" ++ toString L.conductor ++ "-" ++ toString L.centralCharacterConductor

variable {L} in
/-- **The modulus `q` of the label is the conductor of the central character.** -/
lemma IsCentralCharacter.centralCharacterConductor_eq (hχ : L.IsCentralCharacter χ) :
    L.centralCharacterConductor = χ.conductor := by
  have h : ∃ χ, L.IsCentralCharacter χ := ⟨χ, hχ⟩
  rw [centralCharacterConductor, dite_eq_left h, h.choose_spec.eq hχ]

/-- **The central character of the Riemann zeta function is trivial**: its Euler factors are
`1 - x`, whose coefficient of `x` is `-1 = (-1) ^ 1 · 1`. -/
lemma isCentralCharacter_zeta : zeta.IsCentralCharacter 1 := by
  rintro p -
  have hF : ((1 - X : ℂ[X]) : ℂ⟦X⟧) * PowerSeries.mk (fun k ↦ zeta.coeff (p ^ k)) = 1 := by
    rw [mul_comm, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]
    exact PowerSeries.mk_one_mul_one_sub_eq_one ℂ
  have hp : IsUnit (p : ZMod zeta.conductor) := isUnit_of_subsingleton (p : ZMod 1)
  rw [zeta.eulerFactor_eq hF, degree_zeta, Polynomial.coeff_coe, MulChar.one_apply hp]
  simp [Polynomial.coeff_one]

/-- **The label prefix of the Riemann zeta function is `1-1-1`**, as in its LMFDB label
`1-1-1.1-r0-0-0`: it has degree `1`, conductor `1` and a trivial central character, of conductor
`1`. -/
lemma labelPrefix_zeta : zeta.labelPrefix = "1-1-1" := by
  have : NeZero zeta.conductor := ⟨zeta.selbergData.conductor_pos.ne'⟩
  rw [labelPrefix, degree_zeta, isCentralCharacter_zeta.centralCharacterConductor_eq,
    DirichletCharacter.conductor_one, conductor_zeta]
  rfl

end AnalyticLFunction
