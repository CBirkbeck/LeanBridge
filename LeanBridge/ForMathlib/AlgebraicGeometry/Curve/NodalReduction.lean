import TauCeti.AlgebraicGeometry.Curves.Node.Nodal
import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic

/-!
# Nodal reduction of curves

A curve `C` over a local field `K` has semistable reduction (LMFDB `g2c.semistable_reduction`) if
it has a model over the ring of integers `𝒪_K` whose special fibre is semistable: a geometrically
reduced curve with at most nodal singularities, each of whose components of geometric genus zero
has at least two singular points, counted with multiplicity.

This file formalises the first part of this condition, over a discrete valuation ring `R` with
fraction field `K`: `C` has **nodal reduction** if it has a proper model over `R` (Tau Ceti's
`TauCeti.Model`) which is a nodal relative curve (Tau Ceti's
`TauCeti.AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne`: syntomic of relative dimension
one, with relative singular subscheme unramified over `R`), so that its special fibre is a
geometrically reduced curve with at most nodal singularities. This is the Stacks Project's notion
of semistable reduction. The condition on the components of geometric genus zero of the special
fibre is not formalised, as the irreducible components of geometric fibres, with their
normalisations and the singular points on them, are not available. For a curve of genus at least
one, nodal reduction is equivalent to semistable reduction in the LMFDB's sense, by contracting the
rational tails of the special fibre of a nodal model; this is not proved here either.

## Main definitions

* `AlgebraicGeometry.Scheme.HasNodalReduction` (LMFDB `g2c.semistable_reduction`, without the
  condition on the components of geometric genus zero): nodal reduction.

## Main results

* `AlgebraicGeometry.Scheme.HasNodalReduction.of_smooth`: a curve with a proper smooth model of
  relative dimension one, a curve with good reduction, has nodal reduction.
-/

open CategoryTheory TauCeti AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (R : Type u) {K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} (toK : C ⟶ Spec (.of K))

/-- A curve `C` over the fraction field `K` of a discrete valuation ring `R` has **nodal
reduction** (LMFDB `g2c.semistable_reduction`, without the condition on the components of genus
zero) if it is the generic fibre of a proper model over `R` (Tau Ceti's `TauCeti.Model`, flat and
finitely presented with an identification of its generic fibre with `C`) which is a nodal relative
curve (`TauCeti.AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne`), so that its special fibre
is a geometrically reduced curve with at most nodal singularities.

The LMFDB's semistable reduction asks moreover that each component of geometric genus zero of the
special fibre has at least two singular points, counted with multiplicity; for a curve of genus at
least one, this does not change the existence of such a model (not proved here). -/
def HasNodalReduction : Prop :=
  ∃ M : Model R K C toK, M.IsProper ∧ AtWorstNodalOfRelativeDimensionOne M.toBase

variable {R toK}

/-- **Good reduction implies nodal reduction**: a curve with a proper model over `R` which is
smooth of relative dimension one has nodal reduction. -/
lemma HasNodalReduction.of_smooth (M : Model R K C toK) (hM : M.IsProper)
    [SmoothOfRelativeDimension 1 M.toBase] : HasNodalReduction R toK := by
  let _ : M.total.Over (Spec (.of R)) := ⟨M.toBase⟩
  have h : SmoothOfRelativeDimension 1 (M.total ↘ Spec (.of R)) :=
    ‹SmoothOfRelativeDimension 1 M.toBase›
  exact ⟨M, hM, AtWorstNodalOfRelativeDimensionOne.of_smooth⟩

end AlgebraicGeometry.Scheme
