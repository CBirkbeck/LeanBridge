import Mathlib.RepresentationTheory.Character
import TauCeti.LinearAlgebra.End.FiniteOrder

/-!
# The center of a complex character

For a complex representation `V` of a finite group `G` with character `χ`, the elements `g` with
`|χ(g)| = χ(1)` are exactly those acting on `V` by a scalar, so they form a subgroup of `G`.

## Main definitions

* `FDRep.characterCenter` (LMFDB `group.representation.center`): the center
  `Z(χ) = {g ∈ G : |χ(g)| = χ(1)}` of the character `χ` of `V`.

## Main results

* `FDRep.norm_character_eq_finrank_iff`: `|χ(g)| = χ(1)` exactly when `g` acts by a scalar of
  absolute value `1`.
* `FDRep.mem_characterCenter_iff`: membership in the center in the knowl's form `|χ(g)| = χ(1)`.
-/

open Module

namespace FDRep

variable {G : Type*} [Group G] [Finite G] (V : FDRep ℂ G) {g : G}

/-- **`|χ(g)| = χ(1)` exactly when `g` acts by a scalar of absolute value `1`.** -/
lemma norm_character_eq_finrank_iff :
    ‖V.character g‖ = finrank ℂ V ↔ ∃ μ : ℂ, ‖μ‖ = 1 ∧ V.ρ g = μ • 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨μ, hμ, h⟩ ↦ ?_⟩
  · have hg : (V.ρ g) ^ orderOf g = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases End.exists_eq_smul_of_norm_trace_eq_finrank (orderOf_pos g).ne' hg h with ⟨μ, hμ, h⟩
    exact ⟨μ, Complex.norm_eq_one_of_pow_eq_one hμ (orderOf_pos g).ne', h⟩
  · rw [character, h, map_smul, LinearMap.trace_one, smul_eq_mul, norm_mul, hμ, one_mul,
      Complex.norm_natCast]

/-- The **center** of the character `χ` of a complex representation `V` of a finite group `G`
(LMFDB `group.representation.center`): the subgroup `Z(χ) = {g ∈ G : |χ(g)| = χ(1)}` of the
elements acting on `V` by a scalar. -/
def characterCenter : Subgroup G where
  carrier := {g | ‖V.character g‖ = finrank ℂ V}
  mul_mem' {g h} hg hh := by
    rcases (V.norm_character_eq_finrank_iff).mp hg with ⟨μ, hμ, hg⟩
    rcases (V.norm_character_eq_finrank_iff).mp hh with ⟨ν, hν, hh⟩
    exact (V.norm_character_eq_finrank_iff).mpr
      ⟨μ * ν, by rw [norm_mul, hμ, hν, one_mul], by rw [map_mul, hg, hh, smul_mul_smul, one_mul]⟩
  one_mem' := by
    simp
  inv_mem' {g} hg := by
    rcases (V.norm_character_eq_finrank_iff).mp hg with ⟨μ, hμ, hg⟩
    have hμ0 : μ ≠ 0 := norm_ne_zero_iff.mp <| hμ ▸ one_ne_zero
    refine (V.norm_character_eq_finrank_iff).mpr ⟨μ⁻¹, by rw [norm_inv, hμ, inv_one], ?_⟩
    rw [← inv_smul_smul₀ hμ0 (V.ρ g⁻¹), ← one_mul (V.ρ g⁻¹), ← smul_mul_assoc, ← hg, ← map_mul,
      mul_inv_cancel, map_one]

/-- **Membership in the center of a character**, in the knowl's form `|χ(g)| = χ(1)`. -/
lemma mem_characterCenter_iff : g ∈ V.characterCenter ↔ (‖V.character g‖ : ℂ) = V.character 1 := by
  rw [char_one, ← Complex.ofReal_natCast, Complex.ofReal_inj]
  rfl

end FDRep
