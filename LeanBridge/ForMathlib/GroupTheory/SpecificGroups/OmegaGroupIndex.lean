import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.OmegaGroup
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.LowRank

/-!
# The index of `Ω(n, q)` in `SO(n, q)` for odd `q`

For odd `q`, the group `Ω(Q)` of a nondegenerate quadratic form `Q` on `V = 𝔽_q^n`
(`QuadraticForm.omegaGroup`, LMFDB `group.omega`) is the kernel of the spinor norm
`SO(Q) → 𝔽_q^× / (𝔽_q^×)²`, a group of order `2`. When `n ≥ 2`, `Q` takes every value in `𝔽_q`: it
is equivalent to a diagonal form `a₁ x₁² + ⋯ + aₙ xₙ²` with `aᵢ ≠ 0`, and `a₁ x² + a₂ y² = c` has a
solution since `a₁ x²` and `c - a₂ y²` take `(q + 1) / 2` values each
(`FiniteField.exists_root_sum_quadratic`). The product of the reflections in vectors of norms `a`
and `1` has spinor norm the class of `a`, so the spinor norm is onto and `Ω(Q)` has index `2` in
`SO(Q)`. This covers the isotropic and the anisotropic planes (`n = 2`) as well as every `n ≥ 3`,
so `Ω(2m + 1, q)` and `Ω^±(2m, q)` have index `2` for `m ≥ 1`. For `n ≤ 1` the group `SO(Q)` is
trivial and `Ω(Q) = SO(Q)` has index `1`: the index `2` of the LMFDB's text fails for `Ω(1, q)`.

## Main results

* `FiniteField.index_square_units`: the squares have index `2` in `𝔽_q^×`, `q` odd.
* `QuadraticForm.exists_apply_eq_of_two_le_finrank`: a nondegenerate quadratic form in at least two
  variables over `𝔽_q`, `q` odd, takes every value.
* `QuadraticForm.spinorNorm_surjective_of_two_le_finrank`: the spinor norm of such a form is onto.
* `QuadraticForm.index_omegaGroup` (LMFDB `group.omega`): for `n ≥ 2`, `Ω(Q)` has index `2` in
  `SO(Q)`.
* `QuadraticForm.index_omegaGroup_eq_two_iff` (LMFDB `group.omega`): `Ω(Q)` has index `2` in `SO(Q)`
  exactly when `n ≥ 2`.
* `QuadraticForm.index_chevalleyB`, `QuadraticForm.index_chevalleyD`,
  `QuadraticForm.index_omegaMinusGroup` (LMFDB `group.omega`): `Ω(2m + 1, q)` and `Ω⁺(2m, q)` for
  `m ≥ 1`, and `Ω⁻(2m + 2, q)`, have index `2`.
* `QuadraticForm.index_chevalleyB_zero` (LMFDB `group.omega`): `Ω(1, q) = SO(1, q)`.
-/

open Module Polynomial TauCeti QuadraticMap

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

namespace QuadraticForm

lemma index_omegaGroup_of_finrank_le_one (hQ : Q.Nondegenerate) (hV : finrank F V ≤ 1) :
    (omegaGroup Q hQ).index = 1 := by
  rw [omegaGroup, CliffordAlgebra.spinorNorm_eq_one_of_finrank_le_one Q hQ hV, MonoidHom.ker_one,
    Subgroup.index_top]

variable (F) in
/-- **`Ω(1, q) = SO(1, q)`** (LMFDB `group.omega`): in dimension `1` the special orthogonal group is
trivial, so the index of `Ω(1, q)` is `1`, not `2`. -/
lemma index_chevalleyB_zero : (chevalleyB F 0).index = 1 :=
  index_omegaGroup_of_finrank_le_one _ (by simp [Module.finrank_pi_fintype])

end QuadraticForm

variable [Finite F]

namespace FiniteField

variable (F)

/-- **The squares have index `2` in the unit group of a finite field of odd characteristic**: a
unit `u` is a square exactly when `u ^ (q / 2) = 1`, and otherwise `u ^ (q / 2) = -1`. -/
lemma index_square_units : (Subgroup.square Fˣ).index = 2 := by
  have : Fintype F := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := fun h ↦ Invertible.ne_zero (2 : F) <| by
    rw [← Nat.cast_ofNat (R := F) (n := 2), ← h, ringChar.Nat.cast_ringChar]
  have hsq (u : Fˣ) : IsSquare u ↔ (u : F) ^ (Fintype.card F / 2) = 1 := by
    rw [unit_isSquare_iff hF, ← Units.val_eq_one, Units.val_pow_eq_pow_val]
  rcases exists_nonsquare hF with ⟨a, ha⟩
  have ha₀ : a ≠ 0 := fun h ↦ ha (h ▸ IsSquare.zero)
  have ha₁ : a ^ (Fintype.card F / 2) = -1 := (pow_dichotomy hF ha₀).resolve_left fun h ↦ ha <| by
    simpa using ((hsq (Units.mk0 a ha₀)).mpr h).map (Units.coeHom F)
  refine Subgroup.index_eq_two_iff.mpr ⟨Units.mk0 a ha₀, fun b ↦ ?_⟩
  rw [Subgroup.mem_square, Subgroup.mem_square, hsq, hsq, Units.val_mul, Units.val_mk0, mul_pow,
    ha₁]
  rcases pow_dichotomy hF b.ne_zero with hb | hb <;>
    simp [hb, Ring.neg_one_ne_one_of_char_ne_two hF]

lemma natCard_squareClassGroup_eq_two : Nat.card (SquareClassGroup F) = 2 :=
  natCard_multiplicativeSquareClassGroup.symm.trans (index_square_units F)

end FiniteField

namespace QuadraticForm

/-- **A nondegenerate quadratic form in at least two variables over a finite field of odd
characteristic takes every value**: it is equivalent to a diagonal form `∑ aᵢ xᵢ²`, and
`a₁ x² + a₂ y² = c` has a solution. -/
lemma exists_apply_eq_of_two_le_finrank (hQ : Q.Nondegenerate) (hV : 2 ≤ finrank F V) (c : F) :
    ∃ v, Q v = c := by
  have : Fintype F := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := fun h ↦ Invertible.ne_zero (2 : F) <| by
    rw [← Nat.cast_ofNat (R := F) (n := 2), ← h, ringChar.Nat.cast_ringChar]
  rcases Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (nondegenerate_associated_iff.mpr hQ).1 with ⟨w, ⟨e⟩⟩
  let i : Fin (finrank F V) := ⟨0, by omega⟩
  let j : Fin (finrank F V) := ⟨1, by omega⟩
  have hij : i ≠ j := fun h ↦ zero_ne_one (Fin.mk.inj_iff.mp h)
  have hi : (C (w i : F) * X ^ 2).degree = 2 := degree_C_mul_X_pow 2 (w i).ne_zero
  have hf : (C (w i : F) * X ^ 2 - C c).degree = 2 := by
    rw [degree_sub_C (by rw [hi]; decide), hi]
  rcases FiniteField.exists_root_sum_quadratic hf (degree_C_mul_X_pow 2 (w j).ne_zero)
    (FiniteField.odd_card_of_char_ne_two hF) with ⟨x, y, hxy⟩
  refine ⟨e.symm (Pi.single i x + Pi.single j y), ?_⟩
  rw [e.symm.map_app, weightedSumSquares_apply,
    Fintype.sum_eq_add i j hij fun k hk ↦ by simp [hk.1, hk.2]]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hxy
  simp [hij.symm, Units.smul_def]
  linear_combination hxy

/-- **The spinor norm of a nondegenerate quadratic form in at least two variables over a finite
field of odd characteristic is onto**: the reflections in vectors of norms `a` and `1` have
product of spinor norm the class of `a`. -/
lemma spinorNorm_surjective_of_two_le_finrank (hQ : Q.Nondegenerate) (hV : 2 ≤ finrank F V) :
    Function.Surjective (CliffordAlgebra.spinorNorm Q hQ) := by
  intro s
  rcases squareClassHom_surjective s with ⟨a, rfl⟩
  rcases exists_apply_eq_of_two_le_finrank hQ hV a with ⟨x, hx⟩
  rcases exists_apply_eq_of_two_le_finrank hQ hV 1 with ⟨y, hy⟩
  let _ : Invertible (Q x) := invertibleOfNonzero (hx ▸ a.ne_zero)
  let _ : Invertible (Q y) := invertibleOfNonzero (hy ▸ one_ne_zero)
  refine ⟨reflectionPairSpecialOrthogonal Q x y, ?_⟩
  rw [Q.spinorNorm_reflectionPairSpecialOrthogonal hQ, show unitOfInvertible (Q x) = a from
    Units.ext hx, show unitOfInvertible (Q y) = 1 from Units.ext hy, mul_one]

/-- **`Ω(n, q)` has index `2` in `SO(n, q)` for odd `q` and `n ≥ 2`** (LMFDB `group.omega`): the
spinor norm, whose kernel is `Ω(Q)`, maps `SO(Q)` onto the group `𝔽_q^× / (𝔽_q^×)²` of order `2`,
for every nondegenerate quadratic form `Q` in `n ≥ 2` variables, isotropic or not. -/
lemma index_omegaGroup (hQ : Q.Nondegenerate) (hV : 2 ≤ finrank F V) :
    (omegaGroup Q hQ).index = 2 := by
  rw [omegaGroup, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (spinorNorm_surjective_of_two_le_finrank hQ hV), Subgroup.card_top]
  exact FiniteField.natCard_squareClassGroup_eq_two F

/-- **`Ω(n, q)` has index `2` in `SO(n, q)` exactly when `n ≥ 2`** (LMFDB `group.omega`), for odd
`q`: for `n ≤ 1` the group `SO(n, q)` is trivial. -/
lemma index_omegaGroup_eq_two_iff (hQ : Q.Nondegenerate) :
    (omegaGroup Q hQ).index = 2 ↔ 2 ≤ finrank F V := by
  refine ⟨fun h ↦ not_lt.mp fun hV ↦ ?_, index_omegaGroup hQ⟩
  rw [index_omegaGroup_of_finrank_le_one hQ (by omega)] at h
  exact absurd h (by decide)

variable (F)

/-- **`Ω(2m + 1, q)` has index `2` in `SO(2m + 1, q)` for odd `q` and `m ≥ 1`** (LMFDB
`group.omega`). -/
lemma index_chevalleyB {m : ℕ} (hm : m ≠ 0) : (chevalleyB F m).index = 2 :=
  index_omegaGroup _ (by simp [Module.finrank_pi_fintype]; omega)

/-- **`Ω⁺(2m, q)` has index `2` in `SO⁺(2m, q)` for odd `q` and `m ≥ 1`** (LMFDB `group.omega`). -/
lemma index_chevalleyD {m : ℕ} (hm : m ≠ 0) : (chevalleyD F m).index = 2 :=
  index_omegaGroup _ (by simp [Module.finrank_pi_fintype]; omega)

/-- **`Ω⁻(2m + 2, q)` has index `2` in `SO⁻(2m + 2, q)` for odd `q`** (LMFDB `group.omega`). -/
lemma index_omegaMinusGroup (m : ℕ) : (omegaMinusGroup F m).index = 2 :=
  index_omegaGroup _ (by simp)

end QuadraticForm
