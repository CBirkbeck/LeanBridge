import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Aut

/-!
# Nonabelian automorphism groups in characteristic `2` and `3`

Over an algebraically closed field `K` of characteristic `2` or `3`, the automorphism group of an
elliptic curve `E` with `j(E) = 0` (`= 1728`) is nonabelian (LMFDB `ec.twists`). (Its order is
`24`, resp. `12`; this is not proved here, and the knowl does not state it.) Since all curves
with `j = 0` are isomorphic over `K`, and conjugation by an isomorphism identifies their
automorphism groups, it suffices to exhibit two automorphisms that do not commute on one curve
with `j = 0`:

* in characteristic `2`, on `y² + y = x³`, the changes of variables `(u, r, s, t) = (1, ω², ω, ω)`
  and `(1, ω, ω², ω²)`, for `ω` a primitive cube root of unity;
* in characteristic `3`, on `y² = x³ - x`, the changes of variables `(i, 0, 0, 0)` and
  `(1, 1, 0, 0)`, for `i` a square root of `-1`.

Over a field that is not algebraically closed the automorphism group need not be nonabelian: over
`𝔽₂`, `y² + y = x³` has only the automorphisms `(1, 0, 0, 0)` and `(1, 0, 0, 1)`. So the knowl's
sentence holds with `Aut(E)` read over the algebraic closure of `K`, as for the `H¹` that follows
it. The automorphisms are Tau Ceti's `WeierstrassCurve.autGroup`, the stabiliser of `E` under
changes of variables.

## Main results

* `WeierstrassCurve.exists_mul_ne_mul_autGroup_of_charTwo` (LMFDB `ec.twists`): in characteristic
  `2`, an elliptic curve with `j = 0` has two automorphisms that do not commute.
* `WeierstrassCurve.exists_mul_ne_mul_autGroup_of_charThree` (LMFDB `ec.twists`): the same in
  characteristic `3`.
-/

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K] {E E' : WeierstrassCurve K} {C₀ A B : VariableChange K}

lemma conj_mem_autGroup (hC₀ : C₀ • E = E') (hA : A ∈ E'.autGroup) :
    C₀⁻¹ * A * C₀ ∈ E.autGroup := by
  rw [MulAction.mem_stabilizer_iff] at hA ⊢
  rw [mul_smul, mul_smul, hC₀, hA, ← hC₀, inv_smul_smul]

lemma exists_mul_ne_mul_of_smul_eq (hC₀ : C₀ • E = E') (hA : A ∈ E'.autGroup)
    (hB : B ∈ E'.autGroup) (hAB : A * B ≠ B * A) :
    ∃ C ∈ E.autGroup, ∃ D ∈ E.autGroup, C * D ≠ D * C := by
  refine ⟨_, conj_mem_autGroup hC₀ hA, _, conj_mem_autGroup hC₀ hB, fun h ↦ hAB ?_⟩
  simpa [mul_assoc] using congrArg (fun X ↦ C₀ * X * C₀⁻¹) h

variable [IsAlgClosed K] (E) [E.IsElliptic]

/-- **In characteristic `2`, the automorphism group of an elliptic curve with `j = 0` over an
algebraically closed field is nonabelian** (LMFDB `ec.twists`). -/
lemma exists_mul_ne_mul_autGroup_of_charTwo [CharP K 2] (hj : E.j = 0) :
    ∃ C ∈ E.autGroup, ∃ D ∈ E.autGroup, C * D ≠ D * C := by
  have h₂ : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rcases IsAlgClosed.exists_root (X ^ 2 + X + 1 : K[X])
    (by
      have h : (X ^ 2 + X + 1 : K[X]).degree = 2 := by compute_degree!
      rw [h]
      decide) with ⟨ω, hω⟩
  have hω' : ω ^ 2 + ω + 1 = 0 := by simpa using hω
  let E₀ : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩
  have hΔ : E₀.Δ = 1 := by
    simp [E₀, Δ, b₂, b₄, b₆, b₈]
    grind
  have : E₀.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
  have hj₀ : E₀.j = 0 := by
    simp [E₀, j, c₄, b₂, b₄]
  rcases exists_variableChange_of_j_eq E E₀ (hj.trans hj₀.symm) with ⟨C₀, hC₀⟩
  refine exists_mul_ne_mul_of_smul_eq (A := ⟨1, ω ^ 2, ω, ω⟩) (B := ⟨1, ω, ω ^ 2, ω ^ 2⟩) hC₀
    ?_ ?_ fun h ↦ ?_
  · refine MulAction.mem_stabilizer_iff.mpr ?_
    ext <;> simp [E₀, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆] <;> grind
  · refine MulAction.mem_stabilizer_iff.mpr ?_
    ext <;> simp [E₀, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆] <;> grind
  · rw [VariableChange.mul_def, VariableChange.mul_def] at h
    have ht := congrArg VariableChange.t h
    simp at ht
    grind

/-- **In characteristic `3`, the automorphism group of an elliptic curve with `j = 0` over an
algebraically closed field is nonabelian** (LMFDB `ec.twists`). -/
lemma exists_mul_ne_mul_autGroup_of_charThree [CharP K 3] (hj : E.j = 0) :
    ∃ C ∈ E.autGroup, ∃ D ∈ E.autGroup, C * D ≠ D * C := by
  have h₃ : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rcases IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos with ⟨i, hi'⟩
  have hi₀ : i ≠ 0 := fun h ↦ by simp [h] at hi'
  let E₀ : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩
  have hΔ : E₀.Δ = 1 := by
    simp [E₀, Δ, b₂, b₄, b₆, b₈]
    grind
  have : E₀.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
  have hj₀ : E₀.j = 0 := by
    simp [E₀, j, c₄, b₂, b₄]
    grind
  rcases exists_variableChange_of_j_eq E E₀ (hj.trans hj₀.symm) with ⟨C₀, hC₀⟩
  refine exists_mul_ne_mul_of_smul_eq (A := ⟨Units.mk0 i hi₀, 0, 0, 0⟩) (B := ⟨1, 1, 0, 0⟩) hC₀
    ?_ ?_ fun h ↦ ?_
  · refine MulAction.mem_stabilizer_iff.mpr ?_
    ext <;> simp [E₀, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆]
    grind
  · refine MulAction.mem_stabilizer_iff.mpr ?_
    ext <;> simp [E₀, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆] <;> grind
  · rw [VariableChange.mul_def, VariableChange.mul_def] at h
    have hr := congrArg VariableChange.r h
    simp at hr
    grind

end WeierstrassCurve
