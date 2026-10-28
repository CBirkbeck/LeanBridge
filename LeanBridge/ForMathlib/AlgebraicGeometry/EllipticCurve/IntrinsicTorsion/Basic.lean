import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.TorsionDivisor
import TauCeti.FieldTheory.FunctionField.Divisor.DisjointSupport
import TauCeti.FieldTheory.FunctionField.Divisor.Eval
import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula

/-!
# The intrinsic subgroup of the torsion of an elliptic curve

For torsion points `P` and `Q` of an elliptic curve `E` over a field `k`, the intrinsic pairing of
Yamazaki et al. (arXiv:2512.00787) is `⟨P, Q⟩ = ∏ⱼ N_{k(Qⱼ)/k}(f(Qⱼ)) ^ eⱼ ⊗ 1/n` in `kˣ ⊗ ℚ/ℤ`,
for a nonzero integer `n` with `nP = O`, a function `f` with divisor `n(P) - n(O)` and a divisor
`D = ∑ eⱼ Qⱼ` linearly equivalent to `(Q) - (O)` whose support avoids `P` and `O`. Such data always
exist, by the Abel–Jacobi theorem and the moving lemma of Tau Ceti, and the value does not depend
on `n` and `f`. Its independence of `D` rests on Weil reciprocity on `E`, which Tau Ceti proves only
on the rational function field `k(x)`, so the intrinsic subgroup, the torsion points pairing
trivially with all torsion points, is defined by requiring the value to vanish for all admissible
data; by Weil reciprocity this is the LMFDB's definition. The LMFDB calls it a subgroup since the
pairing is biadditive, which is not proved here either, so it is defined as a set of points. The
divisors of `E` are the divisors of its function field over `k`, and its closed points are the
places, of any degree.

## Main definitions

* `WeierstrassCurve.Affine.ofPointSubInfinity`: the divisor `(P) - (O)` of a point.
* `WeierstrassCurve.Affine.IsIntrinsicPairingDatum`: the data `(n, f, D)` admissible for computing
  `⟨P, Q⟩`.
* `WeierstrassCurve.Affine.intrinsicPairingValue` (LMFDB `ec.intrinsic_torsion`): the value
  `f(D) ⊗ 1/n` of the intrinsic pairing computed from such data.
* `WeierstrassCurve.Affine.intrinsicTorsion` (LMFDB `ec.intrinsic_torsion`): the intrinsic
  subgroup, as a set of points.

## Main results

* `WeierstrassCurve.Affine.IsIntrinsicPairingDatum.intrinsicPairingValue_eq_prod`: the value is the
  LMFDB's product of norms.
* `WeierstrassCurve.Affine.IsIntrinsicPairingDatum.intrinsicPairingValue_eq`: the value does not
  depend on `n` and `f`.
* `WeierstrassCurve.Affine.exists_isIntrinsicPairingDatum`: admissible data exist for all torsion
  points `P` and all points `Q`.
* `WeierstrassCurve.Affine.zero_mem_intrinsicTorsion`: the point at infinity is in the intrinsic
  subgroup.
-/

open TauCeti TauCeti.AlgebraicGeometry TensorProduct

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

lemma normResidueOrOne_algebraMap (c : kˣ) :
    P.normResidueOrOne (Units.map (algebraMap k F) c) = c ^ P.degree := by
  rw [normResidueOrOne_of_ord_eq_zero (P.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap _))]
  ext
  rw [coe_normResidue, coe_residueUnit, Units.val_pow_eq_pow_val, degree_eq_finrank,
    ← Algebra.norm_algebraMap]
  congr 1

end TauCeti.Place

namespace TauCeti.Divisor

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

lemma eval_algebraMap (D : Divisor k F) (c : kˣ) :
    D.eval (Units.map (algebraMap k F) c) = c ^ degree D := by
  induction D using Finsupp.induction_linear with
  | zero => rw [eval_zero, map_zero, zpow_zero]
  | add D E hD hE => rw [eval_add, map_add, zpow_add, hD, hE]
  | single P n => rw [eval_single, P.normResidueOrOne_algebraMap,
      WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul, degree_ofPoint, smul_eq_mul, zpow_mul',
      zpow_natCast]

end TauCeti.Divisor

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [W.IsElliptic] {P Q : W.Point}
  {n : ℤ} {f : W.FunctionFieldˣ} {D : Divisor F W.FunctionField}

variable (W P) in
/-- The divisor `(P) - (O)` of a point `P` of an elliptic curve `E` over a field `k`, as a divisor
of the function field `k(E)`: the difference of the places of `P` and of the point at infinity. -/
noncomputable def ofPointSubInfinity : Divisor F W.FunctionField :=
  WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace P).1 - WeilDivisor.ofPoint (Place.infinity W)

variable (W) in
lemma ofPointSubInfinity_zero : W.ofPointSubInfinity 0 = 0 := by
  rw [ofPointSubInfinity, Point.zero_def, coe_pointEquivDegreeOnePlace_zero, sub_self]

variable (W P) in
lemma degree_ofPointSubInfinity : Divisor.degree (W.ofPointSubInfinity P) = 0 := by
  rw [ofPointSubInfinity, map_sub, Divisor.degree_ofPoint, Divisor.degree_ofPoint,
    (W.pointEquivDegreeOnePlace P).2, Place.degree_infinity, sub_self]

lemma exists_units_algebraMap_eq_of_principal_eq_zero
    (hf : Divisor.principal W.isFunctionField f = 0) :
    ∃ c : Fˣ, Units.map (algebraMap F W.FunctionField) c = f := by
  rcases Divisor.exists_units_algebraMap_mul_of_principal_eq W.isFunctionField
    W.isIntegrallyClosedIn_functionField (hf.trans (Divisor.principal_one _).symm) with ⟨c, hc⟩
  exact ⟨c, Units.ext <| by rw [hc, Units.val_one, mul_one, Units.coe_map, MonoidHom.coe_ofClass]⟩

variable (W n f D) in
/-- The **value of the intrinsic pairing** `⟨P, Q⟩ = ∏ⱼ N_{k(Qⱼ)/k}(f(Qⱼ)) ^ eⱼ ⊗ 1/n` in
`kˣ ⊗ ℚ/ℤ` (LMFDB `ec.intrinsic_torsion`) computed from data `n`, `f` and `D = ∑ eⱼ Qⱼ`, admissible
for `P` and `Q` (`WeierstrassCurve.Affine.IsIntrinsicPairingDatum`), with `ℚ/ℤ` the additive
circle `AddCircle (1 : ℚ)`. The product is Tau Ceti's evaluation `TauCeti.Divisor.eval` of `f` at
`D` (`WeierstrassCurve.Affine.IsIntrinsicPairingDatum.intrinsicPairingValue_eq_prod`). -/
noncomputable def intrinsicPairingValue : Additive Fˣ ⊗[ℤ] AddCircle (1 : ℚ) :=
  Additive.ofMul (D.eval f) ⊗ₜ (((n : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ))

variable [DecidableEq F]

variable (P Q n f D) in
/-- **Admissible data for the intrinsic pairing** `⟨P, Q⟩` of two points `P` and `Q` of an elliptic
curve `E` over a field `k` (LMFDB `ec.intrinsic_torsion`): a nonzero integer `n` with `nP = O`, a
function `f` on `E` with divisor `n(P) - n(O)`, and a divisor `D = ∑ eⱼ Qⱼ` on `E`, a finite
integer combination of closed points `Qⱼ` (places of the function field `k(E)` over `k`), linearly
equivalent to `(Q) - (O)` (so of degree `0`) and whose support avoids `P` and `O`. -/
structure IsIntrinsicPairingDatum : Prop where
  /-- The integer `n` is nonzero. -/
  ne_zero : n ≠ 0
  /-- The integer `n` kills `P`. -/
  zsmul_eq_zero : n • P = 0
  /-- The function `f` has divisor `n(P) - n(O)`. -/
  principal_eq : Divisor.principal W.isFunctionField f = n • W.ofPointSubInfinity P
  /-- The divisor `D` is linearly equivalent to `(Q) - (O)`. -/
  exists_principal_eq :
    ∃ z : W.FunctionFieldˣ, Divisor.principal W.isFunctionField z = D - W.ofPointSubInfinity Q
  /-- The support of `D` avoids `P`. -/
  notMem_support : (W.pointEquivDegreeOnePlace P).1 ∉ D.support
  /-- The support of `D` avoids `O`. -/
  infinity_notMem_support : Place.infinity W ∉ D.support

namespace IsIntrinsicPairingDatum

variable (h : IsIntrinsicPairingDatum P Q n f D)

include h

lemma isUnitAtSupport : D.IsUnitAtSupport f := by
  intro R hR
  have hRP : R ≠ (W.pointEquivDegreeOnePlace P).1 := fun h' ↦ h.notMem_support (h' ▸ hR)
  have hRO : R ≠ Place.infinity W := fun h' ↦ h.infinity_notMem_support (h' ▸ hR)
  rw [← Divisor.coeff_principal W.isFunctionField, h.principal_eq, WeilDivisor.coeff_zsmul,
    ofPointSubInfinity, WeilDivisor.coeff_sub, WeilDivisor.coeff_ofPoint_of_ne hRP,
    WeilDivisor.coeff_ofPoint_of_ne hRO, sub_zero, mul_zero]

lemma degree_eq_zero : Divisor.degree D = 0 := by
  rcases h.exists_principal_eq with ⟨z, hz⟩
  rw [← sub_add_cancel D (W.ofPointSubInfinity Q), ← hz, map_add, Divisor.degree_principal,
    degree_ofPointSubInfinity, add_zero]

/-- **The value of the intrinsic pairing computed from admissible data is the LMFDB's product**
`∏ⱼ N_{k(Qⱼ)/k}(f(Qⱼ)) ^ eⱼ ⊗ 1/n`, the function `f` being a unit at every point of the support of
`D`. -/
lemma intrinsicPairingValue_eq_prod : W.intrinsicPairingValue n f D = Additive.ofMul
    (∏ R : D.support, R.1.normResidue f (h.isUnitAtSupport R.1 R.2) ^ D.coeff R.1) ⊗ₜ
      (((n : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) := by
  rw [intrinsicPairingValue, Divisor.eval_eq_prod_normResidue h.isUnitAtSupport]

/-- **The value of the intrinsic pairing does not depend on `n` and `f`**: for admissible data
`(n, f, D)` and `(n', f', D)`, the function `f ^ n' / f' ^ n` has trivial divisor, so it is a
constant, whose value at the degree-zero divisor `D` is `1`; hence `f(D) ^ n' = f'(D) ^ n`, and
`f(D) ⊗ 1/n = f(D) ^ n' ⊗ 1/(n n') = f'(D) ^ n ⊗ 1/(n n') = f'(D) ⊗ 1/n'`. -/
lemma intrinsicPairingValue_eq {n' : ℤ} {f' : W.FunctionFieldˣ}
    (h' : IsIntrinsicPairingDatum P Q n' f' D) :
    W.intrinsicPairingValue n f D = W.intrinsicPairingValue n' f' D := by
  have hu : Divisor.principal W.isFunctionField (f ^ n' / f' ^ n) = 0 := by
    rw [Divisor.principal_div, Divisor.principal_zpow, Divisor.principal_zpow, h.principal_eq,
      h'.principal_eq, smul_smul, smul_smul, mul_comm, sub_self]
  rcases exists_units_algebraMap_eq_of_principal_eq_zero hu with ⟨c, hc⟩
  have hval : D.eval f ^ n' = D.eval f' ^ n := by
    have heval : D.eval (f ^ n' / f' ^ n) = c ^ Divisor.degree D := hc ▸ D.eval_algebraMap c
    rwa [h.degree_eq_zero, zpow_zero, Divisor.eval_div (h.isUnitAtSupport.zpow n')
      (h'.isUnitAtSupport.zpow n), Divisor.eval_zpow, Divisor.eval_zpow, div_eq_one] at heval
  have hq {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : (((a : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) =
      b • ((((a * b : ℤ) : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) := by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
    congr 1
    push_cast
    field_simp
  rw [intrinsicPairingValue, intrinsicPairingValue, hq h.ne_zero h'.ne_zero,
    hq h'.ne_zero h.ne_zero, mul_comm n' n, ← smul_tmul, ← smul_tmul, ← ofMul_zpow, ← ofMul_zpow,
    hval]

end IsIntrinsicPairingDatum

variable (Q) in
/-- **Admissible data for the intrinsic pairing exist** at every torsion point `P`: `n` can be the
order of `P`, a function with divisor `n(P) - n(O)` exists as `n • P = O` (Tau Ceti's
`WeierstrassCurve.Affine.exists_principal_eq_zsmul_ofPoint_sub_infinity`), and the class of
`(Q) - (O)` has a representative avoiding `P` and `O` (Tau Ceti's
`TauCeti.Divisor.exists_linearlyEquivalent_disjoint_support`). -/
lemma exists_isIntrinsicPairingDatum (hP : IsOfFinAddOrder P) :
    ∃ n f D, IsIntrinsicPairingDatum P Q n f D := by
  classical
  have : IsIntegrallyClosed W.CoordinateRing := W.isIntegrallyClosed_coordinateRing
  have : IsDedekindDomain W.CoordinateRing :=
    W.isDedekindDomain_coordinateRing_of_isIntegrallyClosed
  have hn : (addOrderOf P : ℤ) • P = 0 := by rw [natCast_zsmul, addOrderOf_nsmul_eq_zero]
  rcases W.exists_principal_eq_zsmul_ofPoint_sub_infinity hn with ⟨f, hf⟩
  rcases Divisor.exists_linearlyEquivalent_disjoint_support W.isFunctionField
    (W.ofPointSubInfinity Q) {(W.pointEquivDegreeOnePlace P).1, Place.infinity W} with
    ⟨D, hD, hdisj⟩
  rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right] at hdisj
  rcases (Divisor.linearlyEquivalent_iff W.isFunctionField).mp hD with ⟨z, hz⟩
  refine ⟨_, f, D, Nat.cast_ne_zero.mpr hP.addOrderOf_pos.ne', hn, hf, ⟨z⁻¹, ?_⟩, hdisj.1, hdisj.2⟩
  rw [Divisor.principal_inv, hz, neg_sub]

variable (W) in
/-- The **intrinsic subgroup** `E(k)_torsⁱˢ` (LMFDB `ec.intrinsic_torsion`) of an elliptic curve `E`
over a field `k`, as a set of points: the torsion points `P` with `⟨P, Q⟩ = 0` for every torsion
point `Q`, for the intrinsic pairing `⟨·, ·⟩ : E(k)_tors × E(k)_tors → kˣ ⊗ ℚ/ℤ`,
`⟨P, Q⟩ = f(D) ⊗ 1/n`. The value is computed from data `n`, `f`, `D` admissible for `P` and `Q`,
which always exist (`WeierstrassCurve.Affine.exists_isIntrinsicPairingDatum`), and the condition is
imposed for all of them. The value does not depend on `n` and `f`
(`WeierstrassCurve.Affine.IsIntrinsicPairingDatum.intrinsicPairingValue_eq`); it does not depend
on `D` either, by Weil reciprocity on `E`, which is not proved here, so that this set is the
LMFDB's through that theorem. The LMFDB calls it a subgroup since the pairing is biadditive
(Yamazaki et al., arXiv:2512.00787), which is not proved here either: hence a set. -/
def intrinsicTorsion : Set W.Point :=
  {P | IsOfFinAddOrder P ∧ ∀ Q, IsOfFinAddOrder Q → ∀ n f D, IsIntrinsicPairingDatum P Q n f D →
    W.intrinsicPairingValue n f D = 0}

/-- **The point at infinity is in the intrinsic subgroup**: a function with divisor
`n(O) - n(O) = 0` is a constant, whose value at a divisor of degree `0` is `1`. -/
lemma zero_mem_intrinsicTorsion : (0 : W.Point) ∈ W.intrinsicTorsion := by
  refine ⟨IsOfFinAddOrder.zero, fun Q _ n f D h ↦ ?_⟩
  rcases exists_units_algebraMap_eq_of_principal_eq_zero (by
    rw [h.principal_eq, ofPointSubInfinity_zero, smul_zero]) with ⟨c, rfl⟩
  rw [intrinsicPairingValue, D.eval_algebraMap, h.degree_eq_zero, zpow_zero, ofMul_one, zero_tmul]

end WeierstrassCurve.Affine
