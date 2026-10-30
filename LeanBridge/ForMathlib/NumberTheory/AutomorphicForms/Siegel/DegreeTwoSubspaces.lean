import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwo
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonProduct

/-!
# The orthogonal complement of the cusp forms in degree 2

The space `M_{k,j}(Γ)` of Siegel modular forms of degree `2` and weight `ρ_{k,j} = det^k ⊗ Sym^j`
decomposes as `M_{k,j}(Γ) = S_{k,j}(Γ) ⊕ N_{k,j}(Γ)`, where `N_{k,j}(Γ)` is the orthogonal
complement of the cusp forms for the Petersson inner product, which converges as soon as one of
the forms is a cusp form. For `Γ = Sp(4, ℤ)` the LMFDB further decomposes `N_{k,j}` into the
subspaces of Siegel Eisenstein series and Klingen–Eisenstein series. The decomposition and its
stability under the Hecke operators are theorems which are not proved here, and vector-valued
Siegel and Klingen–Eisenstein series of weight `ρ_{k,j}` are not available.

## Main definitions

* `SiegelUpperHalfSpace.cuspFormsOrthogonal` (LMFDB `mf.siegel.subspace.degree.two`): the
  orthogonal complement `N_ρ(Γ)` of the cusp forms in `M_ρ(Γ)`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ` (LMFDB `mf.siegel.subspace.degree.two`): the space
  `N_{k,j}(Γ)`.
-/

open scoped TensorProduct

namespace SiegelUpperHalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (Γ : Subgroup (Matrix.symplecticGroup (Fin 2) ℚ)) (b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

/-- The **orthogonal complement of the cusp forms** `N_ρ(Γ)` (LMFDB
`mf.siegel.subspace.degree.two`) in the space `M_ρ(Γ)` of Siegel modular forms of degree `2`,
weight `ρ` and trivial character on `Γ`: the forms `F ∈ M_ρ(Γ)` with `⟨F, G⟩ = 0` for every cusp
form `G ∈ S_ρ(Γ)`, for the Petersson inner product with respect to a Hermitian form `b` on `V`
(`SiegelUpperHalfSpace.peterssonOrthogonal`), which is the Petersson inner product when `b` is an
admissible inner product (`SiegelUpperHalfSpace.IsAdmissibleForm`). -/
def cuspFormsOrthogonal : Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → V) :=
  peterssonOrthogonal Γ ρ b (modularForms ρ Γ 1) (cuspForms ρ Γ 1)

lemma cuspFormsOrthogonal_le : cuspFormsOrthogonal ρ Γ b ≤ modularForms ρ Γ 1 :=
  fun _ hF ↦ hF.1

variable (k : ℤ) (j : ℕ) (c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ)

/-- The space `N_{k,j}(Γ)` (LMFDB `mf.siegel.subspace.degree.two`): the orthogonal complement of
the cusp forms `S_{k,j}(Γ)` in the space `M_{k,j}(Γ)` of Siegel modular forms of degree `2` and
weight `ρ_{k,j} = det^k ⊗ Sym^j` (`SiegelUpperHalfSpace.rhoKJ`), for the Petersson inner product
with respect to a Hermitian form `c` on `Sym^j(ℂ²)`. The LMFDB takes `Γ = Γ₂ = Sp(4, ℤ)`. -/
noncomputable abbrev cuspFormsOrthogonalKJ :
    Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) :=
  cuspFormsOrthogonal (rhoKJ k j) Γ c

end SiegelUpperHalfSpace
