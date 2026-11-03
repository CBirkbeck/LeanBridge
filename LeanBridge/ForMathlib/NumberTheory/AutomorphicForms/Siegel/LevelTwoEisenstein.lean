import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ArithmeticSiegelOperator
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoIsotypic

/-!
# The Eisenstein part of the vector-valued Siegel modular forms of level 2

The knowl `mf.siegel.family.gamma_2` splits `M_{k,j}(Γ[2]) = S_{k,j}(Γ[2]) ⊕ E_{k,j}(Γ[2])`, with
`E_{k,j}(Γ[2])` "the space of Eisenstein series". It is defined here as the orthogonal complement of
the cusp forms for the Petersson product, in every weight. The spaces `M_{k,j}(Γ[2])` and
`S_{k,j}(Γ[2])` are finite-dimensional, so that the multiplicities of the knowl are numbers of
copies.

Not proved here: that `E_{k,j}(Γ[2])` is stable under `S₆`, and the relation
`m_{s[λ]} = l_{s[λ]} + n_{s[λ]}` of the multiplicities.

## Main definitions

* `SiegelUpperHalfSpace.levelTwoEisenstein` (LMFDB `mf.siegel.family.gamma_2`): the space
  `E_{k,j}(Γ[2])`.

## Main results

* `SiegelUpperHalfSpace.isArithmetic_principal`: `Γ[2]` is arithmetic.
* `SiegelUpperHalfSpace.finiteDimensional_modularFormsKJ_principal`: `M_{k,j}(Γ[2])` is
  finite-dimensional.
* `SiegelUpperHalfSpace.finiteDimensional_cuspFormsKJ_principal`: `S_{k,j}(Γ[2])` is
  finite-dimensional.
* `SiegelUpperHalfSpace.modularFormsKJ_principal_eq_sup`,
  `SiegelUpperHalfSpace.disjoint_cuspFormsKJ_levelTwoEisenstein` (LMFDB `mf.siegel.family.gamma_2`):
  `M_{k,j}(Γ[2]) = S_{k,j}(Γ[2]) ⊕ E_{k,j}(Γ[2])`.
-/

open SymplecticGroup

open scoped ComplexOrder TensorProduct

namespace SiegelUpperHalfSpace

/-- **The principal congruence subgroup `Γ[2]` is arithmetic.** -/
lemma isArithmetic_principal : IsArithmetic IgusaLevelTwo.principal := by
  have : (Gamma (Fin 2) 2).FiniteIndex := Subgroup.finiteIndex_ker _
  exact isArithmetic_map (Gamma (Fin 2) 2)

variable (k : ℤ) (j : ℕ)

/-- **The space `M_{k,j}(Γ[2])` is finite-dimensional.** -/
lemma finiteDimensional_modularFormsKJ_principal :
    FiniteDimensional ℂ (modularFormsKJ k j IgusaLevelTwo.principal) :=
  finiteDimensional_modularFormsKJ_of_isArithmetic k j isArithmetic_principal

/-- **The space `S_{k,j}(Γ[2])` is finite-dimensional.** -/
lemma finiteDimensional_cuspFormsKJ_principal :
    FiniteDimensional ℂ (cuspFormsKJ k j IgusaLevelTwo.principal) :=
  finiteDimensional_cuspFormsKJ_of_isArithmetic k j isArithmetic_principal

/-- The space `E_{k,j}(Γ[2])` of the **Eisenstein part** (LMFDB `mf.siegel.family.gamma_2`): the
orthogonal complement of the cusp forms in `M_{k,j}(Γ[2])`, for the Petersson product of the
Hermitian form `SiegelUpperHalfSpace.symHermitianForm`. -/
noncomputable abbrev levelTwoEisenstein :
    Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) :=
  cuspFormsOrthogonalKJ IgusaLevelTwo.principal k j (symHermitianForm j)

/-- **`M_{k,j}(Γ[2]) = S_{k,j}(Γ[2]) + E_{k,j}(Γ[2])`** (LMFDB `mf.siegel.family.gamma_2`); the sum
is direct (`SiegelUpperHalfSpace.disjoint_cuspFormsKJ_levelTwoEisenstein`). -/
lemma modularFormsKJ_principal_eq_sup : modularFormsKJ k j IgusaLevelTwo.principal =
    cuspFormsKJ k j IgusaLevelTwo.principal ⊔ levelTwoEisenstein k j :=
  have : FiniteDimensional ℂ (cuspFormsKJ k j IgusaLevelTwo.principal) :=
    finiteDimensional_cuspFormsKJ_principal k j
  modularForms_eq_cuspForms_sup_cuspFormsOrthogonal (isModerateForm_rhoKJ k _)
    (isAdmissibleForm_symHermitianForm k) (fun _ hv ↦ symHermitianForm_pos hv)
    (fun g _ hf ↦ hf.slash_rhoKJ k g) isArithmetic_principal

/-- **The sum `S_{k,j}(Γ[2]) + E_{k,j}(Γ[2])` is direct** (LMFDB `mf.siegel.family.gamma_2`). -/
lemma disjoint_cuspFormsKJ_levelTwoEisenstein :
    Disjoint (cuspFormsKJ k j IgusaLevelTwo.principal) (levelTwoEisenstein k j) :=
  disjoint_cuspForms_cuspFormsOrthogonal (isModerateForm_rhoKJ k _)
    (isAdmissibleForm_symHermitianForm k) (fun _ hv ↦ symHermitianForm_pos hv)
    (fun g _ hf ↦ hf.slash_rhoKJ k g) isArithmetic_principal

end SiegelUpperHalfSpace
