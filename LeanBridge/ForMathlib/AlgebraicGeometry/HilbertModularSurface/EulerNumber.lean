import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.KrullDimension
import TauCeti.AlgebraicTopology.Cohomology.Basic

/-!
# The topological Euler number of a complex variety

Let `X` be a scheme over a field `k` with an embedding `k → ℂ`, typically a smooth projective
variety over a field of characteristic zero, such as a Hilbert modular surface. Its complex points
`X(ℂ)` are the morphisms `Spec ℂ ⟶ X` over `Spec k`, and carry the analytic topology: the coarsest
topology for which, for every open subscheme `U` of `X`, the points of `U` form an open set
on which every regular function on `U` is continuous. For `X` locally of finite type over `k`, this
is the usual analytic topology of the complex points of `X ×_k ℂ`: on the complex points of an
affine open subscheme `Spec A` of `X`, the topology induced by the embedding in `ℂⁿ` given by
generators of the `k`-algebra `A`, as these generators are regular functions, and the regular
functions on the open subschemes of `Spec A` are locally quotients of polynomials in them with
nonvanishing denominators; this comparison is not formalised. The **topological Euler number**
(LMFDB `hmsurface.euler_number`) of `X` is the alternating sum
`χ = ∑_{i = 0}^{2 dim X} (-1)ⁱ rank Hⁱ(X(ℂ), ℤ)` of the ranks of the singular cohomology groups of
`X(ℂ)`, Tau Ceti's `TopCat.singularCohomology`. The knowl writes the groups `Hⁱ(X(ℂ), ℤ)` for their
ranks in this sum. For a smooth projective variety the Euler number does not depend on the
embedding `k → ℂ`, by comparison with étale cohomology, which is not formalised here.

The dimension of `X` is the Krull dimension of its topological space, read as a natural number.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoint`: the complex points `X(ℂ)`, with the analytic topology.
* `AlgebraicGeometry.Scheme.ComplexPoint.eval`: the value at a complex point of a regular function.
* `AlgebraicGeometry.Scheme.bettiNumber`: the rank of `Hⁱ(X(ℂ), ℤ)`.
* `AlgebraicGeometry.Scheme.topologicalEulerNumber` (LMFDB `hmsurface.euler_number`).

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoint.isOpen_setOf_le_preimage`: the complex points of an open
  subscheme form an open set.
* `AlgebraicGeometry.Scheme.ComplexPoint.continuous_eval`: a regular function on an open subscheme
  is continuous on its complex points.
-/

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (k : Type) [Field k] [Algebra k ℂ] (X : Scheme.{0}) [X.Over (Spec (.of k))]

/-- The **complex points** `X(ℂ)` of a scheme `X` over a field `k`, for the embedding `k → ℂ`
given by the algebra structure: the morphisms `Spec ℂ ⟶ X` over `Spec k`. They carry the analytic
topology, the coarsest topology making the complex points of every open subscheme `U` an open set
on which the regular functions on `U` are continuous
(`ComplexPoint.isOpen_setOf_le_preimage`, `ComplexPoint.continuous_eval`). -/
def ComplexPoint : Type :=
  {x : Spec (.of ℂ) ⟶ X // x.IsOver (Spec (.of k))}

variable {k X} (U : X.Opens) (f : Γ(X, U))

/-- The **value** `f(x) ∈ ℂ` of a regular function `f` on an open subscheme `U` of `X` at a complex
point `x` of `U`: the pullback of `f` along `x : Spec ℂ ⟶ X`, a global function on `Spec ℂ`. -/
noncomputable def ComplexPoint.eval (x : X.ComplexPoint k) (h : ⊤ ≤ x.1 ⁻¹ᵁ U) : ℂ :=
  (ΓSpecIso (.of ℂ)).hom (x.1.appLE U ⊤ h f)

instance : TopologicalSpace (X.ComplexPoint k) :=
  .generateFrom {S | ∃ (V : X.Opens) (g : Γ(X, V)) (W : Set ℂ), IsOpen W ∧
    S = {x | ∃ h : ⊤ ≤ x.1 ⁻¹ᵁ V, x.eval V g h ∈ W}}

namespace ComplexPoint

lemma isOpen_setOf_eval_mem {W : Set ℂ} (hW : IsOpen W) :
    IsOpen {x : X.ComplexPoint k | ∃ h : ⊤ ≤ x.1 ⁻¹ᵁ U, x.eval U f h ∈ W} :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f, W, hW, rfl⟩

/-- **The complex points of an open subscheme `U` of `X` form an open set** of `X(ℂ)`. -/
lemma isOpen_setOf_le_preimage : IsOpen {x : X.ComplexPoint k | ⊤ ≤ x.1 ⁻¹ᵁ U} := by
  simpa using isOpen_setOf_eval_mem (k := k) U 0 isOpen_univ

/-- **A regular function on an open subscheme `U` of `X` is continuous on the complex points of
`U`.** -/
lemma continuous_eval :
    Continuous fun x : {x : X.ComplexPoint k // ⊤ ≤ x.1 ⁻¹ᵁ U} ↦ x.1.eval U f x.2 := by
  refine continuous_def.mpr fun W hW ↦ ?_
  convert (isOpen_setOf_eval_mem U f hW).preimage continuous_subtype_val using 1
  ext x
  exact ⟨fun h ↦ ⟨x.2, h⟩, fun ⟨_, h⟩ ↦ h⟩

end ComplexPoint

variable (k X)

/-- The `i`-th **Betti number** of the complex points of `X`: the rank of the singular cohomology
group `Hⁱ(X(ℂ), ℤ)`, `0` if the rank is infinite. -/
noncomputable def bettiNumber (i : ℕ) : ℕ :=
  Module.finrank ℤ
    ((TopCat.of (X.ComplexPoint k)).singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ ℤ) i)

/-- The **topological Euler number** (LMFDB `hmsurface.euler_number`) of a scheme `X` over a field
`k` with an embedding `k → ℂ`, typically a smooth projective variety over a field of characteristic
zero: the alternating sum `∑_{i = 0}^{2 dim X} (-1)ⁱ rank Hⁱ(X(ℂ), ℤ)` of the Betti numbers of its
complex points with the analytic topology. -/
noncomputable def topologicalEulerNumber : ℤ :=
  ∑ i ∈ Finset.range (2 * ((topologicalKrullDim X).unbotD 0).toNat + 1),
    (-1) ^ i * (X.bettiNumber k i : ℤ)

end AlgebraicGeometry.Scheme
