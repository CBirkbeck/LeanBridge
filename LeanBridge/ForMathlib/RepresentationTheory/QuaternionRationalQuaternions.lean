import LeanBridge.ForMathlib.RepresentationTheory.FaithfulIrreducibleCharacter
import LeanBridge.ForMathlib.RepresentationTheory.QuaternionRationalDegree

/-!
# Two copies of the two-dimensional character of `Q₈` are afforded over `ℚ`

The two-dimensional irreducible character `χ` of the quaternion group `Q₈` takes rational values
(`QuaternionGroup.isRational_two`), so it is its own Galois-orbit sum, a `ℚ`-valued character. It
is not the character of a representation with matrix entries in `ℚ`: such a representation would
have degree `χ(1) = 2` and be faithful, as `χ` is, while `Q₈` has no faithful representation of
degree `2` over `ℚ` (`QuaternionGroup.three_le_linearDegree_rat`). Two copies of `χ` are afforded
over `ℚ`, by the rational quaternions: `Q₈ = {±1, ±i, ±j, ±k}` acts on `ℍ_ℚ = ℚ⁴` by left
multiplication, and the trace of left multiplication by a quaternion `q` is `4 Re q`, which is
`2 χ`. This is the example behind the Schur-index sentence of LMFDB `group.min_faithful_linear`:
multiple copies of a `k`-valued character may be needed to produce a representation with matrix
entries in `k`.

## Main definitions

* `QuaternionGroup.ratMatrixI`, `QuaternionGroup.ratMatrixJ`: left multiplication by `i` and `j` on
  `ℍ_ℚ`, in the basis `1, i, j, k`.
* `QuaternionGroup.ratQuaternionHom`: the representation of `Q₈` on `ℍ_ℚ` by left multiplication.

## Main results

* `QuaternionGroup.not_exists_trace_eq_twoDimHom` (LMFDB `group.min_faithful_linear`): the
  two-dimensional character of `Q₈` is not the character of a representation over `ℚ`.
* `QuaternionGroup.trace_ratQuaternionHom` (LMFDB `group.min_faithful_linear`): twice that character
  is the character of the representation of `Q₈` on the rational quaternions.
-/

open Matrix GeneralLinearGroup PresentedGroup

namespace Matrix.GeneralLinearGroup

lemma character_representation {k G : Type*} [Field k] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) k)
    (g : G) : (representation ρ).character g = (ρ g : Matrix (Fin n) (Fin n) k).trace :=
  trace_toLin'_eq _

end Matrix.GeneralLinearGroup

namespace QuaternionGroup

/-- **The two-dimensional character of `Q₈` is not afforded over `ℚ`** (LMFDB
`group.min_faithful_linear`): although it takes rational values, it is not the character of a
representation with matrix entries in `ℚ`, which would be faithful of degree `2`. -/
lemma not_exists_trace_eq_twoDimHom : ¬∃ (n : ℕ) (ρ : QuaternionGroup 2 →* GL (Fin n) ℚ),
    ∀ g, ((ρ g : Matrix (Fin n) (Fin n) ℚ).trace : ℂ) =
      (twoDimHom g : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  rintro ⟨n, ρ, hρ⟩
  have hn : n = 2 := mod_cast (by simpa using hρ 1 : (n : ℂ) = 2)
  subst hn
  have hχ (g : QuaternionGroup 2) (hg : (twoDimHom g : Matrix (Fin 2) (Fin 2) ℂ).trace =
      (twoDimHom 1 : Matrix (Fin 2) (Fin 2) ℂ).trace) : g = 1 := by
    refine (Representation.injective_iff_character_eq_character_one _).mp
      ((injective_representation_iff twoDimHom).mpr injective_twoDimHom) g ?_
    rw [character_representation, character_representation, hg]
  refine not_injective_rat_two ρ <| (injective_representation_iff ρ).mp <|
    (Representation.injective_iff_character_eq_character_one _).mpr fun g hg ↦ hχ g ?_
  rw [character_representation, character_representation] at hg
  rw [← hρ, ← hρ, hg]

/-- The matrix of left multiplication by `i` on the rational quaternions `ℍ_ℚ = ℚ⁴`, in the basis
`1, i, j, k`. -/
def ratMatrixI : GL (Fin 4) ℚ where
  val := !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]
  inv := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The matrix of left multiplication by `j` on the rational quaternions `ℍ_ℚ = ℚ⁴`, in the basis
`1, i, j, k`. -/
def ratMatrixJ : GL (Fin 4) ℚ where
  val := !![0, 0, -1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, -1, 0, 0]
  inv := !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

lemma ratMatrixI_pow_four : ratMatrixI ^ (2 * 2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratMatrixI, pow_succ]

lemma ratMatrixI_sq_eq_ratMatrixJ_sq : ratMatrixI ^ 2 = ratMatrixJ ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratMatrixI, ratMatrixJ, pow_succ]

lemma ratMatrixJ_mul_ratMatrixI_mul_inv :
    ratMatrixJ * ratMatrixI * ratMatrixJ⁻¹ * ratMatrixI = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratMatrixI, ratMatrixJ]

lemma lift_relators_rat : ∀ w ∈ relators 2, FreeGroup.lift ![ratMatrixI, ratMatrixJ] w = 1 := by
  rintro w (rfl | rfl | rfl)
  · simpa using ratMatrixI_pow_four
  · simp [ratMatrixI_sq_eq_ratMatrixJ_sq]
  · simpa using ratMatrixJ_mul_ratMatrixI_mul_inv

/-- The **representation of `Q₈` on the rational quaternions** `ℍ_ℚ = ℚ⁴` by left
multiplication, sending `a 1` to `i` and `xa 0` to `j`, defined through the presentation of
`Dic₂`. -/
noncomputable def ratQuaternionHom : QuaternionGroup 2 →* GL (Fin 4) ℚ :=
  (toGroup lift_relators_rat).comp (presentedGroupMulEquiv 2).symm.toMonoidHom

lemma ratQuaternionHom_a_one : ratQuaternionHom (a 1) = ratMatrixI := by
  rw [ratQuaternionHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    presentedGroupMulEquiv_symm_a_one]
  exact toGroup.of _

lemma ratQuaternionHom_xa_zero : ratQuaternionHom (xa 0) = ratMatrixJ := by
  rw [ratQuaternionHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    presentedGroupMulEquiv_symm_xa_zero]
  exact toGroup.of _

/-- **Twice the two-dimensional character of `Q₈` is afforded over `ℚ`** (LMFDB
`group.min_faithful_linear`), by the representation on the rational quaternions: the trace of left
multiplication by a quaternion `q` is `4 Re q`, twice the trace of the two-dimensional complex
representation. -/
lemma trace_ratQuaternionHom (g : QuaternionGroup 2) :
    ((ratQuaternionHom g : Matrix (Fin 4) (Fin 4) ℚ).trace : ℂ) =
      2 * (twoDimHom g : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  rcases (by decide : ∀ g : QuaternionGroup 2, g = 1 ∨ g = a 1 ∨ g = a 1 ^ 2 ∨ g = a 1 ^ 3 ∨
    g = xa 0 ∨ g = xa 0 * a 1 ∨ g = xa 0 * a 1 ^ 2 ∨ g = xa 0 * a 1 ^ 3) g with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [map_one, map_mul, map_pow, ratQuaternionHom_a_one, ratQuaternionHom_xa_zero,
    twoDimHom_a_one, twoDimHom_xa_zero] <;>
  simp [ratMatrixI, ratMatrixJ, matrixI, matrixJ, pow_succ, trace, Fin.sum_univ_four] <;>
  norm_num

end QuaternionGroup
