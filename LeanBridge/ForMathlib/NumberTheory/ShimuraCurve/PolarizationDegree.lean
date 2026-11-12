import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrderDiscriminant

/-!
# The polarization degree of a polarized quaternion order

Let `(O, μ)` be a polarized order of an indefinite division quaternion algebra `B` over `ℚ` (LMFDB
`shimcurve.polarized_order`): `μ ∈ B^×` with `μ² ∈ ℤ_{<0}` and `trd(μ x) ∈ ℤ` for all `x ∈ O`. The
LMFDB defines its polarization degree `deg(μ)` (LMFDB `shimcurve.nrdmu`) as the square-free part of
"the integer" `nrd(μ) / discrd(O)`. That quotient need not be an integer: in `B = (-1, 3 / ℚ)` the
order `O = ℤ + ℤi + ℤj + ℤij` has `discrd(O) = 12` and `μ = i` is a polarization with
`nrd(μ) = 1`. It is always a positive rational number, since `nrd(μ) = (trd(μ)² - trd(μ²)) / 2`
is at least `-μ² > 0`, and the corrected definition takes the square-free part of that rational
number: the unique square-free positive integer `d` such that `nrd(μ) / (discrd(O) d)` is the
square of a rational number. When the quotient is an integer this is the square-free part of the
integer, `PolarizedQuaternionOrder.degree`.

The square-free part of a natural number `n` is `∏_p p ^ (v_p(n) mod 2)`, and that of a rational
number `q` is the square-free part of `|num(q)| den(q)`, which lies in the square class of
`|q| = |num(q)| den(q) / den(q)²`.

## Main definitions

* `Nat.squarefreePart`: the square-free part `∏_p p ^ (v_p(n) mod 2)` of a natural number.
* `Rat.squarefreePart`: the square-free part of a rational number.
* `PolarizedQuaternionOrder.polarizationDegree` (LMFDB `shimcurve.nrdmu`): the polarization degree
  `deg(μ)`, the square-free part of the rational number `nrd(μ) / discrd(O)`.

## Main results

* `Rat.isSquare_abs_div_squarefreePart`, `Rat.eq_squarefreePart_of_isSquare`: the square-free part
  of a nonzero rational number `q` is the unique square-free natural number `d` such that `|q| / d`
  is a square.
* `PolarizedQuaternionOrder.reducedNorm_pos`: the reduced norm of a polarization is positive.
* `PolarizedQuaternionOrder.isSquare_div_polarizationDegree`,
  `PolarizedQuaternionOrder.eq_polarizationDegree_of_isSquare` (LMFDB `shimcurve.nrdmu`):
  `deg(μ)` is the unique square-free natural number `d` such that `nrd(μ) / (discrd(O) d)` is a
  square.
* `PolarizedQuaternionOrder.polarizationDegree_eq_degree` (LMFDB `shimcurve.nrdmu`): when
  `nrd(μ) / discrd(O)` is an integer, `deg(μ)` is the square-free part of that integer.
-/

open Module QuaternionAlgebra

namespace Nat

variable (n : ℕ)

/-- The **square-free part** `∏_p p ^ (v_p(n) mod 2)` of a natural number `n`: the square-free
natural number `d` with `n = d m²` for some natural number `m` (`Nat.squarefreePart_mul_sq`). It is
`1` for `n = 0`. -/
def squarefreePart : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)

lemma factorization_squarefreePart :
    n.squarefreePart.factorization = n.factorization.mapRange (· % 2) (zero_mod 2) := by
  have h : n.squarefreePart = (n.factorization.mapRange (· % 2) (zero_mod 2)).prod (· ^ ·) := by
    rw [Finsupp.prod_of_support_subset _
      (Finsupp.support_mapRange.trans_eq (support_factorization n)) _ fun _ _ ↦ pow_zero _]
    rfl
  rw [h, factorization_prod_pow_eq_self fun p hp ↦
    prime_of_mem_primeFactors (support_factorization n ▸ Finsupp.support_mapRange hp)]

lemma squarefreePart_ne_zero : n.squarefreePart ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp ↦ pow_ne_zero _ (prime_of_mem_primeFactors hp).ne_zero

lemma squarefree_squarefreePart : Squarefree n.squarefreePart := by
  refine (squarefree_iff_factorization_le_one (squarefreePart_ne_zero n)).mpr fun p ↦ ?_
  rw [factorization_squarefreePart, Finsupp.mapRange_apply]
  omega

variable {n} in
lemma squarefreePart_mul_sq (hn : n ≠ 0) :
    n.squarefreePart * (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2 = n := by
  conv_rhs => rw [← prod_factorization_pow_eq_self hn]
  rw [squarefreePart, ← Finset.prod_pow, ← Finset.prod_mul_distrib, Finsupp.prod,
    support_factorization]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [← pow_mul, ← pow_add, mod_add_div']

lemma eq_of_squarefree_of_mul_sq_eq {d₁ d₂ : ℕ} (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂)
    {r₁ r₂ : ℚ} (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (h : (d₁ : ℚ) * r₁ ^ 2 = d₂ * r₂ ^ 2) : d₁ = d₂ := by
  refine eq_of_factorization_eq hd₁.ne_zero hd₂.ne_zero fun p ↦ ?_
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hv : padicValRat p ((d₁ : ℚ) * r₁ ^ 2) = padicValRat p ((d₂ : ℚ) * r₂ ^ 2) := by
      rw [h]
    rw [padicValRat.mul (cast_ne_zero.mpr hd₁.ne_zero) (pow_ne_zero 2 hr₁),
      padicValRat.mul (cast_ne_zero.mpr hd₂.ne_zero) (pow_ne_zero 2 hr₂), padicValRat.pow,
      padicValRat.pow, padicValRat.of_nat, padicValRat.of_nat] at hv
    have h₁ : d₁.factorization p ≤ 1 := hd₁.natFactorization_le_one p
    have h₂ : d₂.factorization p ≤ 1 := hd₂.natFactorization_le_one p
    simp only [factorization_def _ hp] at h₁ h₂ ⊢
    omega
  · rw [factorization_eq_zero_of_not_prime _ hp, factorization_eq_zero_of_not_prime _ hp]

end Nat

namespace Rat

variable (q : ℚ)

/-- The **square-free part** of a rational number `q`: the square-free part of the natural number
`|num(q)| den(q)`, which lies in the square class of `|q| = |num(q)| den(q) / den(q)²`. For
`q ≠ 0` it is the unique square-free natural number `d` such that `|q| / d` is the square of a
rational number (`Rat.isSquare_abs_div_squarefreePart`, `Rat.eq_squarefreePart_of_isSquare`). -/
def squarefreePart : ℕ :=
  (q.num.natAbs * q.den).squarefreePart

lemma squarefree_squarefreePart : Squarefree q.squarefreePart :=
  Nat.squarefree_squarefreePart _

variable {q}

/-- **The square-free part of a rational number lies in its square class**: for `q ≠ 0`, `|q| / d`
is the square of a rational number, `d` the square-free part of `q`. -/
lemma isSquare_abs_div_squarefreePart (hq : q ≠ 0) : IsSquare (|q| / q.squarefreePart) := by
  let N : ℕ := q.num.natAbs * q.den
  let s : ℕ := ∏ p ∈ N.primeFactors, p ^ (N.factorization p / 2)
  have hN : N ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr (num_ne_zero.mpr hq)) q.den_ne_zero
  have h : (N.squarefreePart : ℚ) * (s : ℚ) ^ 2 = N := by
    exact_mod_cast Nat.squarefreePart_mul_sq hN
  have hd : (q.squarefreePart : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (squarefree_squarefreePart q).ne_zero
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  refine ⟨s / q.den, ?_⟩
  rw [abs_def, divInt_eq_div, Int.cast_natCast, div_eq_iff hd, squarefreePart]
  push_cast [N] at h ⊢
  field_simp
  linear_combination -h

/-- **The square-free part of a rational number is unique**: a square-free natural number `d` such
that `|q| / d` is the square of a rational number, for `q ≠ 0`, is the square-free part of `q`. -/
lemma eq_squarefreePart_of_isSquare (hq : q ≠ 0) {d : ℕ} (hd : Squarefree d)
    (h : IsSquare (|q| / d)) : d = q.squarefreePart := by
  rcases h with ⟨r, hr⟩
  rcases isSquare_abs_div_squarefreePart hq with ⟨s, hs⟩
  have hd₀ : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne_zero
  have hs₀ : (q.squarefreePart : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (squarefree_squarefreePart q).ne_zero
  have hq₀ : |q| ≠ 0 := abs_ne_zero.mpr hq
  refine Nat.eq_of_squarefree_of_mul_sq_eq hd (squarefree_squarefreePart q) (r₁ := r) (r₂ := s)
    (fun h0 ↦ hq₀ ?_) (fun h0 ↦ hq₀ ?_) ?_
  · rwa [h0, mul_zero, div_eq_zero_iff, or_iff_left hd₀] at hr
  · rwa [h0, mul_zero, div_eq_zero_iff, or_iff_left hs₀] at hs
  · rw [div_eq_iff hd₀] at hr
    rw [div_eq_iff hs₀] at hs
    linear_combination hs - hr

lemma squarefreePart_intCast (n : ℤ) : (n : ℚ).squarefreePart = n.natAbs.squarefreePart := by
  rw [squarefreePart, num_intCast, den_intCast, mul_one]

end Rat

namespace QuaternionAlgebra

lemma reducedTrace_intCast {B : Type*} [Ring B] [Algebra ℚ B] (h4 : finrank ℚ B = 4) (m : ℤ) :
    reducedTrace B (m : B) = 2 * m := by
  have : FiniteDimensional ℚ B := .of_finrank_pos (by omega)
  have h : LinearMap.mulLeft ℚ (m : B) = (m : ℚ) • LinearMap.id := by
    ext x
    rw [LinearMap.mulLeft_apply, LinearMap.smul_apply, LinearMap.id_apply, Algebra.smul_def,
      map_intCast]
  rw [reducedTrace, h, map_smul, LinearMap.trace_id, h4, smul_eq_mul]
  ring1

end QuaternionAlgebra

namespace PolarizedQuaternionOrder

variable {B : Type*} [Ring B] [Algebra ℚ B] (O : PolarizedQuaternionOrder B)

/-- The **polarization degree** `deg(μ)` of a polarized order `(O, μ)` (LMFDB `shimcurve.nrdmu`):
the square-free part of the positive rational number `nrd(μ) / discrd(O)`, the unique square-free
natural number `d` such that `nrd(μ) / (discrd(O) d)` is the square of a rational number
(`PolarizedQuaternionOrder.isSquare_div_polarizationDegree`,
`PolarizedQuaternionOrder.eq_polarizationDegree_of_isSquare`). The LMFDB calls `nrd(μ) / discrd(O)`
an integer, which it need not be; when it is, `deg(μ)` is the square-free part of that integer
(`PolarizedQuaternionOrder.polarizationDegree_eq_degree`). -/
noncomputable def polarizationDegree : ℕ :=
  (reducedNorm B O.polarization / O.order.quaternionDiscrd).squarefreePart

lemma squarefree_polarizationDegree : Squarefree O.polarizationDegree :=
  Rat.squarefree_squarefreePart _

/-- **The reduced norm of a polarization is positive**: `nrd(μ) = (trd(μ)² - trd(μ²)) / 2` is at
least `-μ² > 0`, for `B` of dimension `4`. -/
lemma reducedNorm_pos (h4 : finrank ℚ B = 4) : 0 < reducedNorm B O.polarization := by
  rcases O.isPolarization.exists_sq_eq with ⟨m, hm, hμ⟩
  have hm' : (m : ℚ) < 0 := Int.cast_lt_zero.mpr hm
  rw [reducedNorm, hμ, reducedTrace_intCast h4]
  nlinarith [sq_nonneg (reducedTrace B (O.polarization : B))]

/-- **For an integral quotient, the polarization degree is the square-free part of the integer**
(LMFDB `shimcurve.nrdmu`): when `nrd(μ) / discrd(O)` is an integer, as the LMFDB says, `deg(μ)` is
the square-free part `∏_p p ^ (v_p(n) mod 2)` of that integer `n`,
`PolarizedQuaternionOrder.degree`. -/
lemma polarizationDegree_eq_degree {n : ℤ}
    (h : reducedNorm B O.polarization / O.order.quaternionDiscrd = n) :
    O.polarizationDegree = O.degree := by
  rw [polarizationDegree, degree, h, Rat.squarefreePart_intCast, Rat.num_intCast]
  rfl

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B]

lemma div_quaternionDiscrd_pos (h4 : finrank ℚ B = 4) :
    0 < reducedNorm B O.polarization / O.order.quaternionDiscrd :=
  div_pos (O.reducedNorm_pos h4) (O.order.quaternionDiscrd_pos h4 O.isQuaternionOrder)

/-- **The polarization degree lies in the square class of `nrd(μ) / discrd(O)`** (LMFDB
`shimcurve.nrdmu`): `nrd(μ) / (discrd(O) deg(μ))` is the square of a rational number, for `B` a
quaternion algebra over `ℚ`. -/
lemma isSquare_div_polarizationDegree (h4 : finrank ℚ B = 4) :
    IsSquare (reducedNorm B O.polarization / O.order.quaternionDiscrd / O.polarizationDegree) := by
  rw [← abs_of_pos (O.div_quaternionDiscrd_pos h4)]
  exact Rat.isSquare_abs_div_squarefreePart (O.div_quaternionDiscrd_pos h4).ne'

/-- **The polarization degree is the square-free part of `nrd(μ) / discrd(O)`** (LMFDB
`shimcurve.nrdmu`): a square-free natural number `d` such that `nrd(μ) / (discrd(O) d)` is the
square of a rational number is `deg(μ)`, for `B` a quaternion algebra over `ℚ`. -/
lemma eq_polarizationDegree_of_isSquare (h4 : finrank ℚ B = 4) {d : ℕ} (hd : Squarefree d)
    (h : IsSquare (reducedNorm B O.polarization / O.order.quaternionDiscrd / d)) :
    d = O.polarizationDegree := by
  rw [← abs_of_pos (O.div_quaternionDiscrd_pos h4)] at h
  exact Rat.eq_squarefreePart_of_isSquare (O.div_quaternionDiscrd_pos h4).ne' hd h

end PolarizedQuaternionOrder
