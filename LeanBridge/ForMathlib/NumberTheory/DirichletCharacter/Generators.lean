import LeanBridge.ForMathlib.GroupTheory.FiniteAbelian.ProdZPowers
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Duality

/-!
# Generators of the group of Dirichlet characters

A set of generators of the group `G` of Dirichlet characters of modulus `q` is a set `S` of
characters that generate `G` under multiplication, `Subgroup.closure S = ⊤`. As `G` is a finite
commutative group, the generators may be chosen so that `G` is the internal direct product of the
cyclic subgroups that they generate (`CommGroup.exists_bijective_prod_zpowers`).

## Main results

* `DirichletCharacter.exists_generators_bijective_prod_zpowers` (LMFDB
  `character.dirichlet.group.generators`): the group of Dirichlet characters of modulus `q` has
  generators `χ_i` such that it is the direct product of the cyclic subgroups `⟨χ_i⟩`.
-/

open Subgroup

namespace DirichletCharacter

/-- **The group of Dirichlet characters of modulus `q` has generators `χ_i` such that it is the
direct product of the cyclic subgroups `⟨χ_i⟩`**: the `χ_i` generate it under multiplication, and
the map `∏ᵢ ⟨χ_i⟩ → G`, `(x_i) ↦ ∏ᵢ x_i`, is bijective. -/
lemma exists_generators_bijective_prod_zpowers (q : ℕ) : ∃ (ι : Type) (_ : Fintype ι)
    (χ : ι → DirichletCharacter ℂ q), closure (Set.range χ) = ⊤ ∧ Function.Bijective
    fun x : (Π i, zpowers (χ i)) ↦ ∏ i, (x i : DirichletCharacter ℂ q) := by
  rcases CommGroup.exists_bijective_prod_zpowers (DirichletCharacter ℂ q) with ⟨ι, hι, χ, h⟩
  exact ⟨ι, hι, χ, CommGroup.closure_range_eq_top_of_surjective_prod_zpowers h.2, h⟩

end DirichletCharacter
