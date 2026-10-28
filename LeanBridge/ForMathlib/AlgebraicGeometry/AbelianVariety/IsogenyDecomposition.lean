import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Simple
import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial

/-!
# Isogeny decompositions and squarefree abelian varieties

Every abelian variety `A` is isogenous to a product `B₁ × ⋯ × Bₙ` of simple abelian varieties, its
isogeny factors, unique up to isogeny and order (Poincaré's complete reducibility theorem, which
needs polarisations and is not formalised here). An abelian variety is squarefree if no simple
factor occurs twice up to isogeny, and geometrically squarefree if it is squarefree over an
algebraic closure of its base field.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.listProd`: the product `B₁ × (B₂ × ⋯ × (Bₙ × 0))` of a
  list of abelian varieties.
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenyDecomposition` (LMFDB `av.decomposition`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsSquarefree` (LMFDB `av.squarefree`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsGeometricallySquarefree` (LMFDB
  `av.geometrically_squarefree`).

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.isIsogenyDecomposition_trivial_nil`: the trivial
  abelian variety has the empty isogeny decomposition.
* `TauCeti.AlgebraicGeometry.AbelianVariety.isIsogenyDecomposition_congr`,
  `TauCeti.AlgebraicGeometry.AbelianVariety.isSquarefree_congr` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.isGeometricallySquarefree_congr`: these notions only
  depend on the isomorphism class of the abelian variety.
-/

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open CategoryTheory

universe u

variable {K : Type u} [Field K] {A B : AbelianVariety K} (l : List (AbelianVariety K))

variable (K) in
/-- The **product** `B₁ × (B₂ × ⋯ × (Bₙ × 0))` of a list `[B₁, …, Bₙ]` of abelian varieties over
`K`, the trivial abelian variety for the empty list. -/
noncomputable def listProd : List (AbelianVariety K) → AbelianVariety K
  | [] => trivial K
  | B :: l => B.prod (listProd l)

variable (A) in
/-- A list `[B₁, …, Bₙ]` of abelian varieties over `K` is an **isogeny decomposition** of `A`, with
**isogeny factors** `B₁, …, Bₙ` (LMFDB `av.decomposition`), if every `Bᵢ` is simple and `A` is
isogenous to the product `B₁ × ⋯ × Bₙ`.

Factors may repeat, up to isogeny or even up to isomorphism: the LMFDB's isogeny factors come with
multiplicities. Every abelian variety has an isogeny decomposition, unique up to reordering and
replacing the factors by isogenous ones (Poincaré's complete reducibility theorem); this needs
polarisations and is not formalised here, so the definition is a predicate on lists rather than a
function of `A`. Being isogenous is symmetric (not formalised here), so the direction of the
isogeny `A ⟶ B₁ × ⋯ × Bₙ` does not matter, as in
`TauCeti.AlgebraicGeometry.AbelianVariety.IsSimple`. -/
def IsIsogenyDecomposition : Prop :=
  (∀ B ∈ l, B.IsSimple) ∧ IsIsogenous A (listProd K l)

/-- The trivial abelian variety has the empty isogeny decomposition. -/
lemma isIsogenyDecomposition_trivial_nil : (trivial K).IsIsogenyDecomposition [] :=
  ⟨fun _ h ↦ (List.not_mem_nil h).elim, .refl _⟩

/-- Being an isogeny decomposition only depends on the isomorphism class of the abelian variety. -/
lemma isIsogenyDecomposition_congr (e : A ≅ B) :
    A.IsIsogenyDecomposition l ↔ B.IsIsogenyDecomposition l :=
  and_congr_right' <| isIsogenous_congr e (Iso.refl _)

variable (A) in
/-- An abelian variety `A` over `K` is **squarefree** (LMFDB `av.squarefree`) if no simple factor
occurs twice up to isogeny in its isogeny decomposition: `A` has an isogeny decomposition
`[B₁, …, Bₙ]` in which no `Bᵢ` is isogenous to a `Bⱼ` with `i < j`.

The LMFDB speaks of the isogeny decomposition of `A`, which exists and is unique up to reordering and
replacing the factors by isogenous ones (Poincaré's complete reducibility theorem, not formalised
here), so asking it of one decomposition is the same as asking it of all; asking it of all would make
every abelian variety without an isogeny decomposition vacuously squarefree. Being isogenous is
symmetric (not formalised here), so it does not matter that only the pairs `i < j` are compared. -/
def IsSquarefree : Prop :=
  ∃ l, A.IsIsogenyDecomposition l ∧ l.Pairwise fun B C ↦ ¬IsIsogenous B C

/-- Squarefreeness only depends on the isomorphism class of the abelian variety. -/
lemma isSquarefree_congr (e : A ≅ B) : A.IsSquarefree ↔ B.IsSquarefree :=
  exists_congr fun l ↦ and_congr_left' <| isIsogenyDecomposition_congr l e

variable (A) in
/-- An abelian variety `A` over `K` is **geometrically squarefree** (LMFDB
`av.geometrically_squarefree`) if its base change to the algebraic closure of `K` is squarefree. -/
def IsGeometricallySquarefree : Prop :=
  (A.baseChange (AlgebraicClosure K)).IsSquarefree

/-- Geometric squarefreeness only depends on the isomorphism class of the abelian variety. -/
lemma isGeometricallySquarefree_congr (e : A ≅ B) :
    A.IsGeometricallySquarefree ↔ B.IsGeometricallySquarefree :=
  isSquarefree_congr <| (baseChangeFunctor (AlgebraicClosure K)).mapIso e

end TauCeti.AlgebraicGeometry.AbelianVariety
