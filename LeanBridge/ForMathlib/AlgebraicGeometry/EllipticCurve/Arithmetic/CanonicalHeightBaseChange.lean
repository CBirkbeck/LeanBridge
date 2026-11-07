import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Limit
import TauCeti.NumberTheory.Height.NumberField

/-!
# The canonical height under base change

Let `L / K` be an extension of number fields and `W` an elliptic curve over `K`. Tau Ceti's
canonical height `ĥ = lim h(n P) / n²` is built from Mathlib's logarithmic height
`logHeight₁ x = ∑ᵥ [K_v : ℚ_v] log⁺ |x|_v`, which is relative to the base field, and
`logHeight₁` over `L` of an element of `K` is `[L : K]` times its height over `K` (Tau Ceti's
`NumberField.logHeight₁_algebraMap`). Hence the canonical height over `L` of a point of `W(K)` is
`[L : K]` times its canonical height over `K`
(`WeierstrassCurve.Affine.Point.canonicalHeight_mapAlong`), and the normalised canonical height
`ĥ / [K : ℚ]` used for the LMFDB regulator is invariant under base change
(`WeierstrassCurve.Affine.Point.canonicalHeight_mapAlong_div_finrank`). Points of `W(K)` are carried
to `W(L)` by Tau Ceti's `WeierstrassCurve.Affine.Point.mapAlong`.

## Main results

* `WeierstrassCurve.Affine.Point.canonicalHeight_mapAlong`: `ĥ_L(P) = [L : K] ĥ_K(P)`.
* `WeierstrassCurve.Affine.Point.canonicalHeight_mapAlong_div_finrank` (LMFDB `ec.regulator`):
  `ĥ_L(P) / [L : ℚ] = ĥ_K(P) / [K : ℚ]`.
-/

open Module NumberField

namespace WeierstrassCurve.Affine.Point

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {W : Affine K} (P : W.Point)

variable [NumberField K] [NumberField L] in
lemma naiveHeight_mapAlong :
    (P.mapAlong (algebraMap K L) (algebraMap K L).injective).naiveHeight =
      finrank K L * P.naiveHeight := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← zero_def, mapAlong_zero, naiveHeight_zero, naiveHeight_zero, mul_zero]
  · rw [mapAlong_some, naiveHeight_eq_logHeight₁, naiveHeight_eq_logHeight₁, xRep_some, xRep_some]
    exact logHeight₁_algebraMap x

variable [DecidableEq K] [DecidableEq L] in
lemma mapAlong_nsmul (n : ℕ) :
    (n • P).mapAlong (algebraMap K L) (algebraMap K L).injective =
      n • P.mapAlong (algebraMap K L) (algebraMap K L).injective := by
  rw [← natCast_zsmul, mapAlong_zsmul, natCast_zsmul]

variable [NumberField K] [NumberField L] [DecidableEq K] [DecidableEq L] [W.IsElliptic]

/-- **The canonical height over a finite extension `L / K` is `[L : K]` times the canonical height
over `K`**: `ĥ_L(P) = [L : K] ĥ_K(P)` for a point `P` of `W(K)`. -/
lemma canonicalHeight_mapAlong :
    (P.mapAlong (algebraMap K L) (algebraMap K L).injective).canonicalHeight =
      finrank K L * P.canonicalHeight := by
  refine tendsto_nhds_unique (tendsto_naiveHeight_nsmul_div_sq _)
    ((P.tendsto_naiveHeight_nsmul_div_sq.const_mul (finrank K L : ℝ)).congr fun n ↦ ?_)
  rw [← mapAlong_nsmul, naiveHeight_mapAlong, mul_div_assoc]

/-- **The normalised canonical height `ĥ / [K : ℚ]` is invariant under base change** (LMFDB
`ec.regulator`): for a finite extension `L / K` of number fields and a point `P` of `W(K)`,
`ĥ_L(P) / [L : ℚ] = ĥ_K(P) / [K : ℚ]`. -/
lemma canonicalHeight_mapAlong_div_finrank :
    (P.mapAlong (algebraMap K L) (algebraMap K L).injective).canonicalHeight / finrank ℚ L =
      P.canonicalHeight / finrank ℚ K := by
  rw [canonicalHeight_mapAlong, ← finrank_mul_finrank ℚ K L, Nat.cast_mul,
    mul_comm (finrank ℚ K : ℝ), mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr finrank_pos.ne')]

end WeierstrassCurve.Affine.Point
