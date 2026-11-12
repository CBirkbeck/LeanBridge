import Mathlib.FieldTheory.Finite.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic

/-!
# The spinor norm through products of reflections

The orthogonal group `GO(n, q)` of a nondegenerate quadratic form `Q` on `V = 𝔽_q^n` and its
subgroup `SO(n, q)` of the elements of determinant `1` are Tau Ceti's
`TauCeti.QuadraticMap.orthogonalGroup Q` and `TauCeti.QuadraticMap.specialOrthogonalGroup Q`
(LMFDB `group.spinor_norm`). The reflection in a vector `v` with `Q(v) ≠ 0` is
`x ↦ x - f(x, v) / Q(v) v`, where `f(x, y) = Q(x + y) - Q(x) - Q(y)` is Mathlib's polar form
`QuadraticMap.polar`; it is `TauCeti.QuadraticMap.reflection Q v`
(`TauCeti.QuadraticMap.reflection_apply_eq_sub_div`). It lies in `GO(n, q)` and has determinant
`-1` (`TauCeti.QuadraticMap.det_reflection`), so for odd `q` it does not lie in `SO(n, q)`, contrary
to the knowl's text.

For odd `q`, by the Cartan–Dieudonné theorem every `g ∈ SO(n, q)` is a product
`r_{v_1} ⋯ r_{v_k}` of reflections. The spinor norm of `g` is the class of `Q(v_1) ⋯ Q(v_k)` in
`𝔽_q^× / (𝔽_q^×)²` for every such factorisation, since Tau Ceti's `CliffordAlgebra.spinorNorm` is a
homomorphism sending the reflection in `v` to the class of `Q(v)`. So the knowl's definition does
not depend on the factorisation. For even `q` every element of `𝔽_q` is a square, so the
square-class group is trivial, and so is the spinor norm.

Tau Ceti's main branch, beyond the pin, has the statement for `O(Q)`,
`CliffordAlgebra.orthogonalSpinorNorm_prod_ofFn_reflectionOrthogonal`; its two-line proof is
inlined here.

## Main results

* `TauCeti.QuadraticMap.reflection_notMem_specialOrthogonalGroup` (LMFDB `group.spinor_norm`): in
  characteristic not `2`, a reflection does not lie in `SO(Q)`.
* `TauCeti.QuadraticMap.exists_prod_ofFn_reflectionOrthogonal_eq` (LMFDB `group.spinor_norm`): in
  characteristic not `2`, every element of `SO(Q)` is a product of reflections.
* `CliffordAlgebra.spinorNorm_eq_squareClassHom_prod` (LMFDB `group.spinor_norm`): the spinor norm
  of a product of the reflections in `v_1, …, v_k` is the square class of `Q(v_1) ⋯ Q(v_k)`.
* `TauCeti.subsingleton_squareClassGroup_of_ringChar_eq_two` (LMFDB `group.spinor_norm`): the
  square-class group of a finite field of characteristic `2` is trivial.
-/

open Module TauCeti QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

namespace TauCeti.QuadraticMap

variable [NeZero (2 : K)]

/-- **A reflection does not lie in the special orthogonal group** in characteristic not `2` (LMFDB
`group.spinor_norm`): its determinant is `-1 ≠ 1`. So the reflection in `v` is an element of
`GO(n, q)`, not of `SO(n, q)`, for odd `q`. -/
lemma reflection_notMem_specialOrthogonalGroup (v : V) [Invertible (Q v)] :
    reflection Q v ∉ specialOrthogonalGroup Q := fun h ↦ by
  have hdet : LinearEquiv.det (reflection Q v) = 1 := (mem_specialOrthogonalGroup_iff.mp h).2
  rw [det_reflection] at hdet
  have h1 : (-1 : K) = 1 := congrArg Units.val hdet
  exact NeZero.ne (2 : K) <| by linear_combination -h1

variable (Q) in
/-- **Every element of the special orthogonal group is a product of reflections** in
characteristic not `2` (LMFDB `group.spinor_norm`), `g = r_{v_1} ⋯ r_{v_k}` with `Q(v_i) ≠ 0`:
the Cartan–Dieudonné theorem `TauCeti.QuadraticMap.exists_even_reflectionOrthogonal_list_prod_eq`,
which moreover gives `k` even and at most `dim V`. -/
lemma exists_prod_ofFn_reflectionOrthogonal_eq (hQ : Q.Nondegenerate)
    (g : specialOrthogonalGroup Q) : ∃ (k : ℕ) (v : Fin k → V) (_ : ∀ i, Invertible (Q (v i))),
      (List.ofFn fun i ↦ reflectionOrthogonal Q (v i)).prod =
        specialOrthogonalToOrthogonal Q g := by
  rcases exists_even_reflectionOrthogonal_list_prod_eq Q hQ g with ⟨l, hl, -, -, hprod⟩
  choose v hv hvl using hl
  refine ⟨l.length, fun i ↦ v _ (l.get_mem i), fun i ↦ hv _ _, ?_⟩
  simp only [hvl, List.ofFn_get]
  exact hprod

end TauCeti.QuadraticMap

namespace CliffordAlgebra

variable [Invertible (2 : K)] (hQ : Q.Nondegenerate) {k : ℕ} (v : Fin k → V)
  [∀ i, Invertible (Q (v i))]

/-- **The spinor norm of `g = r_{v_1} ⋯ r_{v_k}` is the square class of `Q(v_1) ⋯ Q(v_k)`**
(LMFDB `group.spinor_norm`), for every factorisation of `g ∈ SO(Q)` into reflections: the spinor
norm is a homomorphism sending the reflection in `v` to the class of `Q(v)`. -/
lemma spinorNorm_eq_squareClassHom_prod {g : specialOrthogonalGroup Q}
    (hg : (List.ofFn fun i ↦ reflectionOrthogonal Q (v i)).prod =
      specialOrthogonalToOrthogonal Q g) :
    spinorNorm Q hQ g = squareClassHom (∏ i, unitOfInvertible (Q (v i))) := by
  rw [spinorNorm_apply, ← hg]
  simp only [map_list_prod, List.map_ofFn, map_prod, Function.comp_def,
    orthogonalSpinorNorm_reflectionOrthogonal]
  exact Fin.prod_ofFn (M := Multiplicative (SquareClassGroup K)) _

end CliffordAlgebra

namespace TauCeti

/-- **The square-class group of a finite field of characteristic `2` is trivial** (LMFDB
`group.spinor_norm`): every element is a square, so the spinor norm over `𝔽_q` with `q` even takes
values in the trivial group. -/
lemma subsingleton_squareClassGroup_of_ringChar_eq_two {F : Type*} [Field F] [Finite F]
    (hF : ringChar F = 2) : Subsingleton (SquareClassGroup F) := by
  have h0 (x : SquareClassGroup F) : x = 0 := by
    rw [← squareClass_toMul_out x, squareClass_eq_zero_iff]
    exact isSquare_units_val_iff.mp (FiniteField.isSquare_of_char_two hF _)
  exact ⟨fun x y ↦ (h0 x).trans (h0 y).symm⟩

end TauCeti
