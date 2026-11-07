import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The simple Chevalley groups `A(1, q) = SL(2, q)` for even `q ≥ 4`

The Chevalley groups `A(n, q) = SL(n + 1, q)`, `B(n, q) = Ω(2n + 1, q)`, `C(n, q) = Sp(2n, q)` and
`D(n, q) = Ω⁺(2n, q)` are in many cases simple (LMFDB `group.chevalley`). Mathlib proves the
simplicity of `PSL(2, F)` for `|F| ≥ 4`. In characteristic `2` the centre of `SL(2, F)` is trivial,
since `r² = 1` forces `r = 1`, so `SL(2, F) = PSL(2, F)` is simple. In particular
`A(1, q) = SL(2, q)` is simple for every `q = 2 ^ k` with `k ≥ 2`, an infinite family of the listed
matrix groups that are simple.

## Main results

* `Matrix.SpecialLinearGroup.center_eq_bot_two`: `SL(2, F)` has trivial centre in characteristic
  `2`.
* `Matrix.SpecialLinearGroup.isSimpleGroup_two` (LMFDB `group.chevalley`): `SL(2, F)` is simple in
  characteristic `2` when `|F| ≥ 4`.
* `Matrix.SpecialLinearGroup.isSimpleGroup_two_galoisField` (LMFDB `group.chevalley`):
  `A(1, 2 ^ k) = SL(2, 2 ^ k)` is simple for `k ≥ 2`.
-/

open Subgroup

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {F : Type*} [Field F] [CharP F 2]

/-- **`SL(2, F)` has trivial centre in characteristic `2`**: its centre consists of the scalars
`r` with `r² = 1`, and squaring is injective in characteristic `2`. -/
lemma center_eq_bot_two : center SL(2, F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rcases mem_center_iff.mp hA with ⟨r, hr, hA'⟩
  rw [Fintype.card_fin] at hr
  have h : r = 1 := frobenius_inj F 2 <| by rw [frobenius_def, frobenius_def, hr, one_pow]
  rw [mem_bot]
  exact Subtype.ext <| by rw [← hA', h, map_one, coe_one]

/-- **`SL(2, F)` is simple in characteristic `2` when `|F| ≥ 4`** (LMFDB `group.chevalley`): it
is isomorphic to `PSL(2, F)`, its centre being trivial. -/
lemma isSimpleGroup_two (hF : 4 ≤ Nat.card F) : IsSimpleGroup SL(2, F) := by
  have h : IsSimpleGroup PSL(2, F) := ProjectiveSpecialLinearGroup.rank_two_simple hF
  exact ((QuotientGroup.quotientMulEquivOfEq center_eq_bot_two).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

/-- **The Chevalley group `A(1, 2 ^ k) = SL(2, 2 ^ k)` is simple for `k ≥ 2`** (LMFDB
`group.chevalley`). -/
lemma isSimpleGroup_two_galoisField {k : ℕ} (hk : 2 ≤ k) : IsSimpleGroup SL(2, GaloisField 2 k) :=
  isSimpleGroup_two <| by
    rw [GaloisField.card 2 k (by omega)]
    exact Nat.pow_le_pow_right two_pos hk

end Matrix.SpecialLinearGroup
