import LeanBridge.ForMathlib.NumberTheory.LocalField.AssociatedInertia
import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamily
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic

/-!
# The subfamilies of a family of extensions of `p`-adic fields

Let `I / K` be a family of extensions of a `p`-adic field `K`, for a Herbrand invariant
`I = (r_1, …, r_w)_ε^f`: the `K`-isomorphism classes of the extensions `L / K` inside `K̄` with
Herbrand invariant `I`. Every such `L` contains the unramified extension `K_f` of `K` of degree `f`
inside `K̄`, which is its maximal unramified subextension `L^un`, so `L / K_f` is totally ramified
and the residue field of `K_f` is that of `L`. The list of residual polynomials of `L / K` (LMFDB
`lf.residual_polynomials`) at a uniformiser `α` of `L` is that of the Eisenstein minimal polynomial
of `α` over `L^un`: a list of polynomials over the residue field of `L`, which we compare with lists
of polynomials over the residue field of `K_f`. The subfamily of `I / K` corresponding to a set `𝒜`
of such lists (LMFDB `lf.subfamily`), for `𝒜` an equivalence class of residual polynomials, consists
of the extensions in `I / K` with a list of residual polynomials in `𝒜`. By the invariance of the
class of residual polynomials
(`IsNonarchimedeanLocalField.residualPolynomialClass_eq_of_irreducible` in
`LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialInvariance`), the lists of an
extension at its uniformisers form one class.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.subfamily` (LMFDB `lf.subfamily`): the subfamily of
  `I / K` corresponding to a set `𝒜` of lists of polynomials over the residue field of `K_f`.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.subfamily_subset_family` (LMFDB `lf.subfamily`): a
  subfamily of `I / K` is a subset of `I / K`.
-/

open IntermediateField Polynomial TauCeti ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {p : ℕ} (I : HerbrandInvariant p)
  (𝒜 : Set (List 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f][X]))

/-- The **subfamily** of a family `I / K` of extensions of a `p`-adic field `K` corresponding to a
set `𝒜` of lists of polynomials over the residue field of the unramified extension `K_f` of `K` of
degree `f` inside `K̄` (LMFDB `lf.subfamily`), for `𝒜` an equivalence class of residual polynomials:
the `K`-isomorphism classes in `I / K` of the extensions `L` inside `K̄` with a list of residual
polynomials in `𝒜`. Such an `L` contains `K_f` (`unramifiedExtension_le_of_isInvariantOf`), its
maximal unramified subextension `L^un`, and its list of residual polynomials at a uniformiser `α`,
the residual polynomials of the segments of the ramification polygon of the minimal polynomial of
`α` over `L^un`, is read over the residue field of `K_f` through the inclusion `K_f ⊆ L`. -/
def subfamily : ExtensionFamily K :=
  Quotient.mk _ '' {E : FiniteExtension K | haveI : FiniteDimensional K E.1 := E.2
    ∃ hE : I.IsInvariantOf K E.1, ∃ α : 𝒪[E.1], Irreducible α ∧
      letI : Algebra (unramifiedExtension K (AlgebraicClosure K) I.f) E.1 :=
        (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).toAlgebra
      haveI : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) I.f) E.1 :=
        (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).valuativeExtension
      residualPolynomials (ramificationPolynomial
        (minpoly (unramifiedExtension K E.1 (inertiaDegree K E.1)) (α : E.1)) (α : E.1)) (α : E.1) ∈
          List.map (map (algebraMap 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] 𝓀[E.1])) '' 𝒜}

/-- **A subfamily of `I / K` is a subset of `I / K`** (LMFDB `lf.subfamily`). -/
lemma subfamily_subset_family : I.subfamily K 𝒜 ⊆ I.family K := by
  rintro _ ⟨E, ⟨hE, -⟩, rfl⟩
  exact ⟨E, hE, rfl⟩

end IsNonarchimedeanLocalField.HerbrandInvariant
