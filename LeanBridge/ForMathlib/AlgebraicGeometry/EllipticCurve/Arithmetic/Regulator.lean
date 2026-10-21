import LeanBridge.ForMathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated

/-!
# The regulator of an elliptic curve over a number field

Tau Ceti's `WeierstrassCurve.Affine.regulator` is the absolute determinant of the Gram matrix of
the Néron–Tate pairing `⟨P, Q⟩ = (ĥ(P + Q) - ĥ(P) - ĥ(Q)) / 2` on a basis of `E(K)/E(K)_tors`.
Over a number field `K` its canonical height `ĥ` is built from Mathlib's height
`Height.logHeight₁ x = ∑ᵥ [K_v : ℚ_v] log⁺ |x|_v`, which is relative to `K`: it is the
**non-normalised** canonical height of LMFDB `ec.canonical_height`. So Tau Ceti's regulator is the
Néron–Tate regulator `Reg_NT(E/K)` of LMFDB `ec.regulator`, the one in the conjecture of Birch and
Swinnerton-Dyer. The regulator `Reg(E/K)` recorded by the LMFDB is taken with respect to the
height `ĥ / [K : ℚ]`, which is invariant under base change, and
`Reg_NT(E/K) = [K : ℚ] ^ r Reg(E/K)` for the rank `r` of `E(K)`.

The pairing is positive definite on `E(K) ⊗ ℝ`, so both regulators are positive. Positivity of
`ĥ` on the nonzero points of the lattice `E(K)/E(K)_tors` would not suffice for this; what does is
Northcott finiteness for `ĥ` over a number field, through `Matrix.IsSymm.posDef_of_northcott`.

## Main definitions

* `WeierstrassCurve.Affine.normalizedRegulator`: the regulator `Reg(E/K)` (LMFDB `ec.regulator`).

## Main results

* `WeierstrassCurve.Affine.regulator_eq_pow_mul_normalizedRegulator`:
  `Reg_NT(E/K) = [K : ℚ] ^ r Reg(E/K)`.
* `WeierstrassCurve.Affine.normalizedRegulator_eq_abs_det`: `Reg(E/K)` is the absolute
  determinant of the Gram matrix of the normalised height pairing on any basis of `E(K)/E(K)_tors`.
* `WeierstrassCurve.Affine.posDef_neronTateGramMatrix`: the Néron–Tate pairing is positive
  definite on `E(K) ⊗ ℝ`, that is, its Gram matrix on any basis of `E(K)/E(K)_tors` is.
* `WeierstrassCurve.Affine.regulator_pos` and `WeierstrassCurve.Affine.normalizedRegulator_pos`:
  `Reg_NT(E/K) > 0` and `Reg(E/K) > 0`.
* `WeierstrassCurve.Affine.normalizedRegulator_eq_one_of_finrank_eq_zero`: in rank `0`,
  `Reg(E/K) = 1`.
* `WeierstrassCurve.Affine.normalizedRegulator_eq_canonicalHeight_div`: in rank `1`,
  `Reg(E/K) = ĥ(P) / [K : ℚ]` for a generator `P` of `E(K)/E(K)_tors`.
* `WeierstrassCurve.Affine.normalizedRegulator_eq_regulator_of_finrank_eq_one`: over `ℚ` the two
  regulators agree.
-/

open Module Submodule

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] (W : Affine K) [W.IsElliptic]
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ (PointModTorsion W))

/-- The **regulator** `Reg(E/K)` (LMFDB `ec.regulator`) of an elliptic curve over a number field
`K`: the volume of `E(K)/E(K)_tors` for the height pairing of the normalised canonical height
`ĥ / [K : ℚ]`, that is, the Néron–Tate regulator `WeierstrassCurve.Affine.regulator` divided by
`[K : ℚ] ^ r`, where `r` is the rank of `E(K)`. This is the LMFDB normalisation, invariant under
base change; the Néron–Tate regulator itself is the one in the conjecture of Birch and
Swinnerton-Dyer. -/
noncomputable def normalizedRegulator : ℝ :=
  W.regulator / (finrank ℚ K : ℝ) ^ finrank ℤ (PointModTorsion W)

/-- **The Néron–Tate regulator is `[K : ℚ] ^ r` times the normalised one**:
`Reg_NT(E/K) = [K : ℚ] ^ r Reg(E/K)`. -/
lemma regulator_eq_pow_mul_normalizedRegulator :
    W.regulator = (finrank ℚ K : ℝ) ^ finrank ℤ (PointModTorsion W) * W.normalizedRegulator := by
  rw [normalizedRegulator, mul_div_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr finrank_pos.ne'))]

variable [DecidableEq ι] in
/-- **The normalised regulator is a volume**: on any basis `b` of `E(K)/E(K)_tors` it is the
absolute determinant of the Gram matrix of the normalised height pairing
`[K : ℚ]⁻¹ ⟨-, -⟩`. In particular it does not depend on the basis. -/
lemma normalizedRegulator_eq_abs_det :
    W.normalizedRegulator = |((finrank ℚ K : ℝ)⁻¹ • W.neronTateGramMatrix b).det| := by
  rw [Matrix.det_smul, abs_mul, abs_pow, abs_inv, Nat.abs_cast, normalizedRegulator,
    W.regulator_eq_abs_det_neronTateGramMatrix b, ← finrank_eq_card_basis b, inv_pow,
    inv_mul_eq_div]

lemma normalizedRegulator_nonneg : 0 ≤ W.normalizedRegulator :=
  div_nonneg W.regulator_nonneg (by positivity)

/-- **The Néron–Tate pairing is positive definite on `E(K) ⊗ ℝ`**: its Gram matrix on any basis
`b` of `E(K)/E(K)_tors` is positive definite. The quadratic form of the Gram matrix at an integer
vector `c` is the canonical height `ĥ(P)` of a point `P` lifting `∑ᵢ cᵢ bᵢ`, so it has finitely
many integer points of bounded value, the canonical height being Northcott over a number field. -/
lemma posDef_neronTateGramMatrix : (W.neronTateGramMatrix b).PosDef := by
  refine (isSymm_neronTateGramMatrix b).posDef_of_northcott ⟨fun C ↦ (((Northcott.finite_le
    (h := Point.canonicalHeight (W := W)) C).image (torsion ℤ W.Point).mkQ).preimage
    b.equivFun.symm.injective.injOn).subset fun c hc ↦ ?_⟩
  rcases mkQ_surjective _ (b.equivFun.symm c) with ⟨P, hP⟩
  refine ⟨P, ?_, hP⟩
  rw [Set.mem_ofPred_eq, ← neronTatePairing_self, ← neronTatePairingModTorsion_mk, ← mkQ_apply, hP]
  simpa [dotProduct, Matrix.mulVec, mul_comm, neronTatePairingModTorsion_comm] using hc

/-- **The Néron–Tate regulator is positive**: `Reg_NT(E/K) > 0`, the Néron–Tate pairing being
positive definite on `E(K) ⊗ ℝ`. -/
lemma regulator_pos : 0 < W.regulator :=
  (abs_pos.mpr (W.posDef_neronTateGramMatrix (finBasis ℤ _)).det_pos.ne').trans_eq
    (W.regulator_eq_abs_det_neronTateGramMatrix _).symm

/-- **The regulator is positive**: `Reg(E/K) > 0`. -/
lemma normalizedRegulator_pos : 0 < W.normalizedRegulator :=
  div_pos W.regulator_pos <| pow_pos (Nat.cast_pos.mpr finrank_pos) _

/-- **The rank-zero convention**: when `E(K)` has rank `0`, `Reg(E/K) = 1`. -/
lemma normalizedRegulator_eq_one_of_finrank_eq_zero (h : finrank ℤ (PointModTorsion W) = 0) :
    W.normalizedRegulator = 1 := by
  rw [normalizedRegulator, W.regulator_eq_one_of_finrank_eq_zero h, h, pow_zero, div_one]

/-- **The rank-one case**: when `E(K)` has rank `1` and the class of `P` generates
`E(K)/E(K)_tors`, the regulator is the normalised canonical height `ĥ(P) / [K : ℚ]` of `P`. -/
lemma normalizedRegulator_eq_canonicalHeight_div (h : finrank ℤ (PointModTorsion W) = 1)
    {P : W.Point} (hP : span ℤ {(torsion ℤ W.Point).mkQ P} = ⊤) :
    W.normalizedRegulator = P.canonicalHeight / finrank ℚ K := by
  have hP0 : (torsion ℤ W.Point).mkQ P ≠ 0 := by
    intro h0
    rw [h0, span_zero_singleton] at hP
    have : Subsingleton (PointModTorsion W) :=
      (subsingleton_iff ℤ).mp (subsingleton_iff_bot_eq_top.mp hP)
    rw [finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  let b : Basis (Fin 1) ℤ (PointModTorsion W) :=
    Basis.mk (v := fun _ ↦ (torsion ℤ W.Point).mkQ P) (linearIndependent_unique_iff.mpr hP0)
      (by rw [Set.range_const, hP])
  rw [normalizedRegulator, W.regulator_eq_abs_det_neronTateGramMatrix b, h, pow_one,
    Matrix.det_unique, neronTateGramMatrix_apply, Basis.mk_apply, mkQ_apply,
    neronTatePairingModTorsion_mk, neronTatePairing_self, abs_of_nonneg P.canonicalHeight_nonneg]

/-- **Over `ℚ` the two regulators agree**: when `[K : ℚ] = 1` the normalised regulator is the
Néron–Tate regulator. -/
lemma normalizedRegulator_eq_regulator_of_finrank_eq_one (h : finrank ℚ K = 1) :
    W.normalizedRegulator = W.regulator := by
  rw [normalizedRegulator, h, Nat.cast_one, one_pow, div_one]

end WeierstrassCurve.Affine
