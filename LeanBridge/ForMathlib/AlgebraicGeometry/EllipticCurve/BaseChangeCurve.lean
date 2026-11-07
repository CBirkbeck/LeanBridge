import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Data.Rat.Lemmas
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
import TauCeti.NumberTheory.NumberField.QuadraticAlgebra

/-!
# Base-change curves

Let `L` be a field extension of a field `K`. The base change `E⁄L` of a Weierstrass curve `E` over
`K` is Mathlib's `WeierstrassCurve.baseChange`, the same equation read over `L`. A Weierstrass
curve over `L` is a **base-change curve from `K`** (`WeierstrassCurve.IsBaseChangeCurve`) if it is
isomorphic over `L`, that is, related by a change of variables over `L`, to the base change of an
elliptic curve over `K`.

A curve whose coefficients lie in `K` is a base-change curve
(`WeierstrassCurve.isBaseChangeCurve_baseChange`), but not conversely: over `ℚ(√2)`, the
translation `x ↦ x + √2` takes `y² = x³ + 1` to a base-change curve with `a₂ = 3 √2`
(`WeierstrassCurve.isBaseChangeCurve_translate_x_cube_add_one` and
`WeierstrassCurve.not_exists_baseChange_eq_translate_x_cube_add_one`). The `j`-invariant of a
base-change curve lies in `K` (`WeierstrassCurve.IsBaseChangeCurve.j_mem_range`), but not
conversely: over `ℚ(√2)`, `y² = x³ + 1 + √2` has `j = 0` and is not a base-change curve from `ℚ`
(`WeierstrassCurve.j_x_cube_add_one_add_sqrt_two` and
`WeierstrassCurve.not_isBaseChangeCurve_x_cube_add_one_add_sqrt_two`). Indeed a change of variables
multiplies `c₆` by a sixth power, so `c₆` of a base-change curve is an element of `K` times a
square of `L` (`WeierstrassCurve.not_isBaseChangeCurve_of_c₆`), while `-864 (1 + √2)` is not:
`1 + √2` has norm `-1`, which is not a square in `ℚ`. Here `ℚ(√2)` is Mathlib's
`QuadraticAlgebra ℚ 2 0`, whose elements are `a + b √2` with `a, b ∈ ℚ`. It is a field, by a local
instance recording that `2` is not a square in `ℚ`, and a number field, by Tau Ceti's instance
`QuadraticAlgebra.instNumberField`.

## Main definitions

* `WeierstrassCurve.IsBaseChangeCurve` (LMFDB `ec.base_change`): a base-change curve.

## Main results

* `WeierstrassCurve.isBaseChangeCurve_baseChange`: a curve with coefficients in `K` is a
  base-change curve.
* `WeierstrassCurve.isBaseChangeCurve_translate_x_cube_add_one` and
  `WeierstrassCurve.not_exists_baseChange_eq_translate_x_cube_add_one`: a base-change curve whose
  coefficients do not lie in `ℚ`.
* `WeierstrassCurve.IsBaseChangeCurve.j_mem_range`: the `j`-invariant of a base-change curve lies
  in `K`.
* `WeierstrassCurve.not_isBaseChangeCurve_of_c₆`: a curve whose `c₆` is not an element of `K` times
  a square is not a base-change curve.
* `WeierstrassCurve.j_x_cube_add_one_add_sqrt_two` and
  `WeierstrassCurve.not_isBaseChangeCurve_x_cube_add_one_add_sqrt_two`: a curve with `j ∈ ℚ` that
  is not a base-change curve from `ℚ`.
-/

open QuadraticAlgebra

namespace WeierstrassCurve

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] {W : WeierstrassCurve L}

variable (K W) in
/-- A Weierstrass curve `W` over a field extension `L` of `K` is a **base-change curve from `K` to
`L`** (LMFDB `ec.base_change`): it is isomorphic over `L`, by a change of variables, to the base
change `E⁄L` of an elliptic curve `E` over `K`. -/
def IsBaseChangeCurve : Prop :=
  ∃ E : WeierstrassCurve K, E.IsElliptic ∧ ∃ C : VariableChange L, C • E⁄L = W

/-- **A curve whose coefficients lie in `K` is a base-change curve from `K`.** -/
lemma isBaseChangeCurve_baseChange (E : WeierstrassCurve K) [(E⁄L).IsElliptic] :
    IsBaseChangeCurve K (E⁄L) :=
  ⟨E, ⟨isUnit_iff_ne_zero.mpr fun h0 ↦ (E⁄L).isUnit_Δ.ne_zero <| by
    rw [baseChange, map_Δ, h0, map_zero]⟩, 1, one_smul _ _⟩

/-- **The `j`-invariant of a base-change curve from `K` lies in `K`.** -/
lemma IsBaseChangeCurve.j_mem_range [W.IsElliptic] (h : IsBaseChangeCurve K W) :
    W.j ∈ (algebraMap K L).range := by
  rcases h with ⟨E, hE, C, rfl⟩
  exact ⟨E.j, by rw [variableChange_j]; exact (map_j E _).symm⟩

/-- **A curve whose `c₆` is not an element of `K` times a square is not a base-change curve from
`K`**: a change of variables multiplies `c₆` by the sixth power of a unit. -/
lemma not_isBaseChangeCurve_of_c₆ (h : ∀ (q : K) (z : L), W.c₆ ≠ algebraMap K L q * z ^ 2) :
    ¬IsBaseChangeCurve K W := by
  rintro ⟨E, -, C, rfl⟩
  refine h E.c₆ ((C.u⁻¹ : Lˣ) ^ 3) ?_
  rw [variableChange_c₆, baseChange, map_c₆]
  ring1

local instance : Fact (¬IsSquare (2 : ℚ)) :=
  ⟨Rat.isSquare_ofNat_iff.not.mpr Nat.prime_two.prime.not_isSquare⟩

instance : (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr <| by norm_num [Δ, b₄, b₆, b₈]⟩

/-- **The translate by `√2` of `y² = x³ + 1` is a base-change curve from `ℚ` to `ℚ(√2)`.** -/
lemma isBaseChangeCurve_translate_x_cube_add_one : IsBaseChangeCurve ℚ
    ((⟨1, ω, 0, 0⟩ : VariableChange (QuadraticAlgebra ℚ 2 0)) •
      (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℚ)⁄(QuadraticAlgebra ℚ 2 0)) :=
  ⟨_, inferInstance, _, rfl⟩

/-- **The translate by `√2` of `y² = x³ + 1` does not have its coefficients in `ℚ`**: its `a₂`
is `3 √2`. -/
lemma not_exists_baseChange_eq_translate_x_cube_add_one :
    ¬∃ E : WeierstrassCurve ℚ, E⁄(QuadraticAlgebra ℚ 2 0) =
      (⟨1, ω, 0, 0⟩ : VariableChange (QuadraticAlgebra ℚ 2 0)) •
        (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℚ)⁄(QuadraticAlgebra ℚ 2 0) := by
  rintro ⟨E, hE⟩
  simpa [baseChange, variableChange_a₂] using congrArg (fun W ↦ W.a₂.im) hE

instance : (⟨0, 0, 0, 0, 1 + ω⟩ : WeierstrassCurve (QuadraticAlgebra ℚ 2 0)).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr fun h ↦ ?_⟩
  simpa [Δ, b₄, b₆, b₈, pow_two] using congrArg QuadraticAlgebra.im h

/-- **The curve `y² = x³ + 1 + √2` over `ℚ(√2)` has `j = 0`**, which lies in `ℚ`. -/
lemma j_x_cube_add_one_add_sqrt_two :
    (⟨0, 0, 0, 0, 1 + ω⟩ : WeierstrassCurve (QuadraticAlgebra ℚ 2 0)).j = 0 :=
  j_eq_zero _ <| by simp [c₄, b₂, b₄]

/-- **The curve `y² = x³ + 1 + √2` over `ℚ(√2)` is not a base-change curve from `ℚ`**: its `c₆`
is `-864 (1 + √2)`, which is not a rational number times a square. -/
lemma not_isBaseChangeCurve_x_cube_add_one_add_sqrt_two :
    ¬IsBaseChangeCurve ℚ (⟨0, 0, 0, 0, 1 + ω⟩ : WeierstrassCurve (QuadraticAlgebra ℚ 2 0)) := by
  refine not_isBaseChangeCurve_of_c₆ fun q ⟨a, b⟩ h ↦ ?_
  have hre : -(216 * 4) = q * (a * a + 2 * b * b) := by
    simpa [c₆, b₂, b₆, pow_two] using congrArg QuadraticAlgebra.re h
  have him : -(216 * 4) = q * (a * b + b * a) := by
    simpa [c₆, b₂, b₆, pow_two] using congrArg QuadraticAlgebra.im h
  have h0 : q * ((a - b) ^ 2 + b ^ 2) = 0 := by linear_combination him - hre
  rcases mul_eq_zero.mp h0 with hq | hab
  · norm_num [hq] at hre
  · have hb : b = 0 := (pow_eq_zero_iff two_ne_zero).mp <| by
      linarith [sq_nonneg (a - b), sq_nonneg b]
    norm_num [hb] at him

end WeierstrassCurve
