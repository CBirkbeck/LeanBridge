import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.AngleRank
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.PowTrace

/-!
# Point counts of the curve of a Weil polynomial

If an abelian variety `A` of dimension `g` over `𝔽_q` is the Jacobian of a curve `X`, the number of
points of `X` over `𝔽_{qⁿ}` is `qⁿ + 1 - ∑ αᵢⁿ`, where `α₁, …, α_{2g}` are the complex roots of the
Weil polynomial of `A`, by the rationality `Z(X, T) = L(T) / ((1 - T) (1 - qT))` of the zeta
function of `X`. The LMFDB computes these numbers for every isogeny class of abelian varieties over
`𝔽_q`, from its Weil polynomial, as the point counts of a virtual curve (LMFDB
`av.fq.curve_point_counts`); when one of them is negative, or smaller over `𝔽_{qⁿ}` than over a
subfield `𝔽_{qᵈ}`, the isogeny class contains no Jacobian.

The power sums `∑ αᵢⁿ` are integers: they are polynomials with integer coefficients in the
elementary symmetric functions of the roots, which are the coefficients of the polynomial up to
sign. We define them in this way, for a polynomial over any commutative ring, and show that they are
the power sums of the roots wherever a monic polynomial splits, and in terms of the Frobenius angles
`θᵢ` of a Weil `q`-polynomial (LMFDB `av.fq.frobenius_angles`), `∑ αᵢⁿ = ∑ (√q)ⁿ e^{inθᵢ}`.

For `g = 1`, where the curve is the elliptic curve itself, the virtual point counts of the Weil
polynomial `T² - a_q T + q` of an elliptic curve over `𝔽_q` are its point counts over the finite
extensions of `𝔽_q`, by Tau Ceti's computation of the traces of the powers of Frobenius; in
particular they are nonnegative and increase along divisibility, as the LMFDB's test for Jacobians
requires. For `g ≥ 2` the zeta function of a curve is not available, nor therefore the comparison
with the point counts of an actual curve.

## Main definitions

* `Polynomial.rootPowerSum`: the power sums of the roots of a polynomial, from its coefficients.
* `Polynomial.virtualPointCount` (LMFDB `av.fq.curve_point_counts`): the virtual point counts
  `qⁿ + 1 - ∑ αᵢⁿ` of a Weil `q`-polynomial.

## Main results

* `Polynomial.Monic.algebraMap_rootPowerSum`: for a monic polynomial which splits, `rootPowerSum`
  is the power sum of its roots.
* `Polynomial.Monic.virtualPointCount_eq`: the virtual point counts of a monic integer polynomial
  are `qⁿ + 1 - ∑ αᵢⁿ`, over its complex roots `αᵢ`.
* `Polynomial.IsWeilPolynomial.virtualPointCount_eq`: the virtual point counts of a Weil
  `q`-polynomial with Frobenius angles `θᵢ` are `qⁿ + 1 - ∑ (√q)ⁿ e^{inθᵢ}`.
* `WeierstrassCurve.virtualPointCount_eq_pointCount`: the virtual point counts of the Weil
  polynomial `T² - a_q T + q` of an elliptic curve over `𝔽_q` are its point counts over the finite
  extensions of `𝔽_q`.
* `WeierstrassCurve.virtualPointCount_nonneg` and
  `WeierstrassCurve.virtualPointCount_le_virtualPointCount`: the virtual point counts of an elliptic
  curve are nonnegative and increase along embeddings of finite extensions of `𝔽_q`.
-/

open Complex Polynomial

namespace Polynomial

open MvPolynomial symmetricSubalgebra

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] {p : R[X]} (q : ℕ)
  (h : ℤ[X]) (n : ℕ)

variable (p) in
/-- The `n`-th **power sum of the roots** `∑ αᵢⁿ` of a polynomial `p` of degree `d`, computed from
its coefficients: the value at `eₖ = (-1)ᵏ p_{d - k}` of the polynomial with coefficients in `R`
which expresses the power sum `∑ Xᵢⁿ` of `d` variables in their elementary symmetric polynomials
`e₁, …, e_d`, by the fundamental theorem of symmetric polynomials. When `p` is monic and splits over
a domain `A`, it is the power sum of the roots of `p` in `A`, with multiplicity
(`Polynomial.Monic.algebraMap_rootPowerSum`). -/
noncomputable def rootPowerSum : R :=
  MvPolynomial.aeval (fun i : Fin (Fintype.card (Fin p.natDegree)) ↦
      (-1) ^ (i + 1 : ℕ) * p.coeff (p.natDegree - (i + 1)))
    ((MvPolynomial.esymmAlgEquiv (Fin p.natDegree) R rfl).symm
      (sumPolynomial (Fin p.natDegree) (X ^ n)))

variable {n} in
/-- **The power sums of the roots of a monic polynomial which splits**: `rootPowerSum p n` is the
power sum `∑ αᵢⁿ` of the roots `αᵢ` of `p` in `A`, with multiplicity. -/
lemma Monic.algebraMap_rootPowerSum (hp : p.Monic) (hs : (p.map (algebraMap R A)).Splits) :
    algebraMap R A (p.rootPowerSum n) = ((p.aroots A).map (· ^ n)).sum := by
  have hcard : Multiset.card (p.aroots A) = Fintype.card (Fin p.natDegree) := by
    rw [Fintype.card_fin, ← hs.natDegree_eq_card_roots, hp.natDegree_map]
  have hsum : ((p.aroots A).map (· ^ n)).sum = ((p.aroots A).map (aeval · (X ^ n : R[X]))).sum := by
    simp only [map_pow, aeval_X]
  rw [hsum, ← aevalMultiset_sumPolynomial hcard, aevalMultiset_apply, rootPowerSum,
    ← Algebra.ofId_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2 with i
  have hi : (i : ℕ) + 1 ≤ p.natDegree := i.2.trans_eq (Fintype.card_fin _)
  have hk : p.natDegree - ((i : ℕ) + 1) ≤ (p.map (algebraMap R A)).natDegree := by
    rw [hp.natDegree_map]
    omega
  have hv : algebraMap R A (p.coeff (p.natDegree - (i + 1))) =
      (-1) ^ ((i : ℕ) + 1) * (p.aroots A).esymm (i + 1) := by
    rw [← coeff_map, coeff_eq_esymm_roots_of_card hs.natDegree_eq_card_roots.symm hk,
      (hp.map _).leadingCoeff, hp.natDegree_map, Nat.sub_sub_self hi, one_mul, aroots_def]
  rw [Algebra.ofId_apply, map_mul, hv, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow,
    neg_one_mul, neg_neg, one_pow, one_mul]

/-- The **virtual point counts** (LMFDB `av.fq.curve_point_counts`) of a Weil `q`-polynomial `h`:
the integers `Nₙ = qⁿ + 1 - ∑ αᵢⁿ`, over the complex roots `αᵢ` of `h` with multiplicity
(`Polynomial.Monic.virtualPointCount_eq`). When `h` is the Weil polynomial of the Jacobian of a
curve `X` over `𝔽_q`, `Nₙ` is the number of points of `X` over `𝔽_{qⁿ}`, for `n ≥ 1`: this is
proved here for `g = 1` (`WeierstrassCurve.virtualPointCount_eq_pointCount`), while for `g ≥ 2` it
needs the zeta function of curves, which is not available. The LMFDB computes `Nₙ` for every
isogeny class of abelian varieties over `𝔽_q`, as the point count of a virtual curve, which
certifies that the isogeny class contains no Jacobian when it is negative or smaller than `N_d` for
some divisor `d` of `n`. The definition makes sense for every integer polynomial. -/
noncomputable def virtualPointCount : ℤ :=
  q ^ n + 1 - h.rootPowerSum n

variable {h}

/-- **The virtual point counts of a monic integer polynomial** `h` are `qⁿ + 1 - ∑ αᵢⁿ`, over the
complex roots `αᵢ` of `h` with multiplicity. -/
lemma Monic.virtualPointCount_eq (hh : h.Monic) : (h.virtualPointCount q n : ℂ) = q ^ n + 1 -
    ((h.map (Int.castRingHom ℂ)).roots.map (· ^ n)).sum := by
  rw [virtualPointCount, ← algebraMap_int_eq, ← aroots_def,
    ← hh.algebraMap_rootPowerSum (IsAlgClosed.splits _), algebraMap_int_eq, eq_intCast]
  push_cast
  rfl

variable {q}

/-- **The virtual point counts in terms of the Frobenius angles** (LMFDB `av.fq.frobenius_angles`):
the virtual point counts of a Weil `q`-polynomial with Frobenius angles `θᵢ` are
`Nₙ = qⁿ + 1 - ∑ (√q)ⁿ e^{inθᵢ}`. -/
lemma IsWeilPolynomial.virtualPointCount_eq (hh : h.IsWeilPolynomial q) :
    (h.virtualPointCount q n : ℂ) = q ^ n + 1 -
      (h.frobeniusAngles.map fun θ : ℝ ↦ (√q : ℂ) ^ n * exp (n * (θ * I))).sum := by
  rw [hh.1.virtualPointCount_eq, frobeniusAngles, Multiset.map_map]
  refine congrArg (_ - ·) <| congrArg Multiset.sum <| Multiset.map_congr rfl fun α hα ↦ ?_
  rw [Function.comp_apply, exp_nat_mul, ← mul_pow, hh.sqrt_mul_exp_arg_mul_I hα]

lemma rootPowerSum_X_sq_sub_C_mul_X_add_C {b : ℤ} {t : ℕ → ℤ} (h₀ : t 0 = 2)
    (h₂ : ∀ n, t (n + 2) = t 1 * t (n + 1) - b * t n) :
    (X ^ 2 - C (t 1) * X + C b).rootPowerSum n = t n := by
  have hm : (X ^ 2 - C (t 1) * X + C b).Monic := by
    monicity!
  have hd : (X ^ 2 - C (t 1) * X + C b).natDegree = 2 := by
    compute_degree!
  have hs : ((X ^ 2 - C (t 1) * X + C b).map (algebraMap ℤ ℂ)).Splits := IsAlgClosed.splits _
  refine Int.cast_injective (α := ℂ) ?_
  rw [← eq_intCast (algebraMap ℤ ℂ), hm.algebraMap_rootPowerSum hs]
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [h₀]
    simp only [pow_zero, Multiset.map_const']
    rw [aroots_def, ← hs.natDegree_eq_card_roots, hm.natDegree_map, hd]
    norm_num
  | one =>
    have hc : (X ^ 2 - C (t 1) * X + C b).coeff 1 = -t 1 := by
      rw [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C]
      norm_num
    have h : -(t 1 : ℂ) = -((X ^ 2 - C (t 1) * X + C b).map (algebraMap ℤ ℂ)).roots.sum := by
      rw [← hs.nextCoeff_eq_neg_sum_roots_of_monic (hm.map _),
        nextCoeff_of_natDegree_pos (by rw [hm.natDegree_map, hd]; omega), hm.natDegree_map, hd,
        coeff_map, hc, map_neg, eq_intCast]
    simp only [pow_one, Multiset.map_id']
    linear_combination h
  | more n ih₀ ih₁ =>
    have hr (α : ℂ) (hα : α ∈ (X ^ 2 - C (t 1) * X + C b).aroots ℂ) :
        α ^ (n + 2) = t 1 * α ^ (n + 1) - b * α ^ n := by
      have h : α ^ 2 - t 1 * α + b = 0 := by
        simpa using (mem_aroots.mp hα).2
      linear_combination α ^ n * h
    rw [Multiset.map_congr rfl hr, Multiset.sum_map_sub, Multiset.sum_map_mul_left,
      Multiset.sum_map_mul_left, ih₀, ih₁, h₂]
    push_cast
    ring1

end Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (E : Type*) {E' : Type*} [Field E]
  [Algebra F E] [Field E'] [Algebra F E'] [Finite E']

variable {E} in
lemma pointCount_le_pointCount (φ : E →ₐ[F] E') : (W⁄E).pointCount ≤ (W⁄E').pointCount := by
  rw [pointCount_def, pointCount_def]
  refine Nat.add_le_add_right (Nat.card_le_card_of_injective
    (fun p ↦ ⟨(φ p.1.1, φ p.1.2), Affine.Equation.baseChange φ p.2⟩) fun p p' h ↦ ?_) 1
  rcases Prod.mk.inj (congrArg Subtype.val h) with ⟨h₁, h₂⟩
  exact Subtype.ext <| Prod.ext (φ.toRingHom.injective h₁) (φ.toRingHom.injective h₂)

variable [Finite F] [W.IsElliptic] [Finite E]

lemma rootPowerSum_eq_frobeniusPowTrace (n : ℕ) :
    (X ^ 2 - C W.frobeniusTrace * X + C (Nat.card F : ℤ)).rootPowerSum n = W.frobeniusPowTrace n :=
  W.frobeniusPowTrace_one ▸ rootPowerSum_X_sq_sub_C_mul_X_add_C n W.frobeniusPowTrace_zero
    fun k ↦ W.frobeniusPowTrace_one.symm ▸ W.frobeniusPowTrace_add_two k

/-- **The virtual point counts of an elliptic curve are its point counts** (LMFDB
`av.fq.curve_point_counts` for `g = 1`, where the curve is the elliptic curve itself): for an
elliptic curve `W` over a finite field `F` with `q` elements and a finite extension `E` of `F` of
degree `n`, the virtual point count `Nₙ` of the Weil polynomial `T² - a_q T + q` of `W` is the
number `#W(E)` of points of `W` over `E`, the point at infinity included. -/
lemma virtualPointCount_eq_pointCount :
    (X ^ 2 - C W.frobeniusTrace * X + C (Nat.card F : ℤ)).virtualPointCount (Nat.card F)
      (Module.finrank F E) = ((W⁄E).pointCount : ℤ) := by
  rw [virtualPointCount, rootPowerSum_eq_frobeniusPowTrace, frobeniusPowTrace_finrank,
    frobeniusTrace_def, Module.natCard_eq_pow_finrank (K := F) (V := E)]
  push_cast
  ring1

/-- **The virtual point counts of an elliptic curve are nonnegative** (LMFDB
`av.fq.curve_point_counts`): they are its point counts. -/
lemma virtualPointCount_nonneg : 0 ≤
    (X ^ 2 - C W.frobeniusTrace * X + C (Nat.card F : ℤ)).virtualPointCount (Nat.card F)
      (Module.finrank F E) := by
  rw [virtualPointCount_eq_pointCount]
  exact Nat.cast_nonneg _

variable {E} in
/-- **The virtual point counts of an elliptic curve increase along extensions** (LMFDB
`av.fq.curve_point_counts`): if a finite extension `E` of `F` embeds in another `E'`, as
`𝔽_{q^d}` does in `𝔽_{qⁿ}` for `d ∣ n`, the virtual point count over `E` is at most that over `E'`,
since the points over `E` are points over `E'`. Elliptic curves thus pass the LMFDB's test for
Jacobians, the virtual counts being nonnegative and increasing along divisibility. -/
lemma virtualPointCount_le_virtualPointCount (φ : E →ₐ[F] E') :
    (X ^ 2 - C W.frobeniusTrace * X + C (Nat.card F : ℤ)).virtualPointCount (Nat.card F)
      (Module.finrank F E) ≤ (X ^ 2 - C W.frobeniusTrace * X + C (Nat.card F : ℤ)).virtualPointCount
      (Nat.card F) (Module.finrank F E') := by
  rw [virtualPointCount_eq_pointCount, virtualPointCount_eq_pointCount]
  exact Nat.cast_le.mpr (W.pointCount_le_pointCount φ)

end WeierstrassCurve
