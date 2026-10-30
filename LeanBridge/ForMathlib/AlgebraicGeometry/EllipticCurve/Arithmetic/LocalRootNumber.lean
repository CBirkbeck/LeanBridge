import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.LocalData
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Modularity.AssociatedNewform
import TauCeti.NumberTheory.ModularForms.LFunction.Sign
import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.AtkinLehner

/-!
# The local root number of an elliptic curve

The local root number `w_𝔭 = ±1` of an elliptic curve `E` over a number field at a prime `𝔭`
(LMFDB `ec.local_root_number`) is the sign of the local functional equation of `E` at `𝔭`: the
local constant of the Weil–Deligne representation of `E` at `𝔭`, whose definition (Deligne and
Langlands) is out of reach. This file formalises the two descriptions of it that the knowl gives.

* At a prime of good or multiplicative reduction it depends only on the reduction type: it is `1`
  at good and non-split multiplicative reduction and `-1` at split multiplicative reduction. At
  multiplicative reduction it is `-a_𝔭`, where `1 - a_𝔭 T` is the local Euler factor of Mathlib's
  L-function of `E`. At additive reduction it is `±1` with no simple characterisation, and it is not
  a function of the reduction type.
* For `E` over `ℚ` it is, at every prime `p`, the eigenvalue `ε_p(f) = ±1` of the Atkin–Lehner
  involution `W_{p^e}`, `p^e ∥ N`, on the newform `f` associated to `E`, which exists by the
  modularity theorem (`WeierstrassCurve.IsAssociatedNewform`). It is `1` at the primes not dividing
  the conductor `N`, the primes of good reduction, and `-a_p(E)` at the primes exactly dividing
  `N`, the primes of multiplicative reduction, in accordance with the first description, since
  `a_p(E)` is `1` at split and `-1` at non-split multiplicative reduction. With the local root
  number `-1` at the infinite place, the local root numbers multiply to the sign of the functional
  equation of `L(E, s) = L(f, s)`. That the Atkin–Lehner eigenvalues are the local constants of
  `E`, as the knowl states, is a theorem not proved here.

## Main definitions

* `WeierstrassCurve.ReductionType.localRootNumber` (LMFDB `ec.local_root_number`): the local root
  number at a prime of good or multiplicative reduction, as a function of the reduction type.
* `WeierstrassCurve.IsAssociatedNewform.localRootNumber` (LMFDB `ec.local_root_number`): the local
  root number of an elliptic curve over `ℚ`, the Atkin–Lehner eigenvalue of its newform.

## Main results

* `WeierstrassCurve.localPolynomial_eq_one_add_C_mul_X`: at a prime of multiplicative reduction
  with local root number `w`, the local Euler factor of the L-function is `1 + w T`.
* `WeierstrassCurve.IsAssociatedNewform.localRootNumber_eq_one`: over `ℚ` the local root number is
  `1` at the primes not dividing the conductor.
* `WeierstrassCurve.IsAssociatedNewform.localRootNumber_eq_neg`: over `ℚ` the local root number is
  `-a_p(E)` at the primes exactly dividing the conductor.
* `WeierstrassCurve.IsAssociatedNewform.frickeCompletedL_two_sub`: over `ℚ` the root number
  `-∏_{p ∣ N} w_p` is the sign of the functional equation of `L(E, s)`.
-/

open HeckeRing GL2 TauCeti Polynomial

namespace WeierstrassCurve.ReductionType

/-- The **local root number** (LMFDB `ec.local_root_number`) of an elliptic curve at a prime of
reduction type `t`, where `t` determines it: `1` at good and at non-split multiplicative reduction,
and `-1` at split multiplicative reduction. At additive reduction the local root number is `±1`
with no simple characterisation and is not a function of the reduction type; the value is then
`none`. -/
def localRootNumber : ReductionType → Option ℤˣ
  | good => some 1
  | multiplicative split => some (if split then -1 else 1)
  | additive => none

variable {t : ReductionType}

lemma localRootNumber_eq_none_iff : t.localRootNumber = none ↔ t = additive := by
  cases t <;> simp [localRootNumber]

lemma localRootNumber_eq_some_neg_one_iff :
    t.localRootNumber = some (-1) ↔ t = multiplicative true := by
  cases t <;> simp [localRootNumber]

lemma localRootNumber_eq_some_one_iff :
    t.localRootNumber = some 1 ↔ t = good ∨ t = multiplicative false := by
  cases t <;> simp [localRootNumber]

end WeierstrassCurve.ReductionType

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) (R : Type*) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]

/-- **At multiplicative reduction the local Euler factor is `1 + w T`**, where `w` is the local
root number: Mathlib's local polynomial of the L-function is `1 - T` at split and `1 + T` at
non-split multiplicative reduction, so the local root number is `-a_𝔭` for the local Euler factor
`1 - a_𝔭 T`. -/
lemma localPolynomial_eq_one_add_C_mul_X {w : ℤˣ} (h : (W.minimal R).HasMultiplicativeReduction R)
    (hw : (W.reductionType R).localRootNumber = some w) :
    W.localPolynomial R = 1 + C (w : ℤ) * X := by
  have hg : ¬(W.minimal R).HasGoodReduction R := h.not_hasGoodReduction R
  by_cases hs : (W.minimal R).HasSplitMultiplicativeReduction R <;>
    simp only [reductionType, hg, ite_false, h, ite_true, hs, ReductionType.localRootNumber,
      Option.some.injEq, localPolynomial] at hw ⊢ <;>
    simp [← hw, sub_eq_add_neg]

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {M : ℕ} [NeZero M] {f : Newform M 2} {p : ℕ}
  (hf : E.IsAssociatedNewform f)

variable (p) in
/-- The **local root number** `w_p` (LMFDB `ec.local_root_number`) at a prime `p` of an elliptic
curve `E` over `ℚ` with associated newform `f`: the eigenvalue `ε_p(f) = ±1` of the normalised
Atkin–Lehner involution `W_{p^e}` on `f`, where `p^e ∥ N` is the exact power of `p` dividing the
conductor `N`. By the knowl, it is the sign of the local functional equation of `E` at `p`. The
associated newform is unique (`IsAssociatedNewform.eq`), so this depends only on `E`; it exists by
the modularity theorem. At the primes `p ∤ N` it is `1` (`localRootNumber_eq_one`). -/
noncomputable def IsAssociatedNewform.localRootNumber : ℂ :=
  f.atkinLehnerSign hf.χ_eq_one (Nat.isExactDivisor_primePow (p := p))

lemma IsAssociatedNewform.localRootNumber_eq_one_or_eq_neg_one :
    hf.localRootNumber p = 1 ∨ hf.localRootNumber p = -1 :=
  f.atkinLehnerSign_eq_one_or_neg_one _ _

/-- **The local root number is `1` at the primes not dividing the conductor**, the primes of good
reduction, where the Atkin–Lehner involution is the identity. -/
lemma IsAssociatedNewform.localRootNumber_eq_one (hp : ¬p ∣ M) : hf.localRootNumber p = 1 := by
  rw [localRootNumber, f.atkinLehnerSign_congr _ _ Nat.isExactDivisor_one
    (by rw [Nat.factorization_eq_zero_of_not_dvd hp, pow_zero]), f.atkinLehnerSign_one]

/-- **The local root number is `-a_p(E)` at the primes exactly dividing the conductor**, the primes
of multiplicative reduction, where `a_p(E)` is the `p`-th Dirichlet coefficient of the L-function
of `E`, `1` at split and `-1` at non-split multiplicative reduction. This is the eigenvalue
`a_p(f) = -ε_p(f)` of `U_p` on a newform of weight `2` (Atkin–Lehner). -/
lemma IsAssociatedNewform.localRootNumber_eq_neg (hp : p.Prime) (hpM : p ∣ M) (hpM₂ : ¬p ^ 2 ∣ M) :
    hf.localRootNumber p = -E.LFunction p := by
  rw [← hf.qExpansion_coeff, f.qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul hf.χ_eq_one hp hpM
    hpM₂, neg_neg, sub_self, zpow_zero, mul_one, localRootNumber]
  refine f.atkinLehnerSign_congr _ _ _ ?_
  have h₁ : 1 ≤ M.factorization p :=
    (hp.pow_dvd_iff_le_factorization (NeZero.ne M)).mp (by rwa [pow_one])
  have h₂ : ¬2 ≤ M.factorization p :=
    (hp.pow_dvd_iff_le_factorization (NeZero.ne M)).not.mp hpM₂
  rw [show M.factorization p = 1 by omega, pow_one]

/-- **The local root numbers multiply to the sign of the functional equation**: with the local root
number `-1` at the infinite place, the root number `-∏_{p ∣ N} w_p` of `E` is the sign of the
functional equation `Λ(2 - s) = ε Λ(s)` of the completed L-function `Λ(s) = Λ(f, s)` of the
associated newform `f`, the L-function of `E`. -/
lemma IsAssociatedNewform.frickeCompletedL_two_sub (s : ℂ) :
    CuspForm.frickeCompletedL f.toCuspForm (M.toPNat (NeZero.pos M)) (2 - s) =
      -(∏ p ∈ M.primeFactors, hf.localRootNumber p) *
          CuspForm.frickeCompletedL f.toCuspForm (M.toPNat (NeZero.pos M)) s := by
  simpa only [← f.prod_atkinLehnerSign_primePow_eq_frickeSign hf.χ_eq_one, Int.cast_ofNat,
    zpow_ofNat, Complex.I_sq, neg_one_mul, localRootNumber] using
    f.frickeCompletedL_sub_eq hf.χ_eq_one (by norm_num) s

end WeierstrassCurve
