import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamilyInvariants
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolynomial

/-!
# The ramification polygon of an extension of `p`-adic fields

Let `L / K` be a finite extension of nonarchimedean local fields and `K'` its maximal unramified
subextension, Tau Ceti's `TauCeti.unramifiedExtension K L (TauCeti.inertiaDegree K L)`, the only
intermediate field unramified over `K` over which `L` is totally ramified
(`TauCeti.eq_unramifiedExtension_inertiaDegree_iff`). The minimal polynomial over `𝒪[K']` of a
uniformiser `α` of `L` is Eisenstein, and the minimal polynomial `φ` of `α` over the field `K'` is
its image. The ramification polygon of `L / K` (LMFDB `lf.ramification_polygon`) is the lower convex
hull of the points `(-i, v_L(ρ_i))` of the ramification polynomial `ρ(x) = α ^ (-n) φ(α x + α)`.

We prove that it is the ramification polygon of the Herbrand invariant `I` of `L / K`, for every
uniformiser `α`: in a tower `M / L / K` with `M / K` finite Galois, through Monge's Proposition 1
and Lemma 1, which the committed files prove for the minimal polynomial of a uniformiser over an
unramified base, and inside `K̄`, for the Herbrand invariant
`IsNonarchimedeanLocalField.visibleHerbrandInvariant`. So the ramification polygon does not depend
on the uniformiser, it is the same for all the extensions in a family `I / K` (the extensions with
Herbrand invariant `I`), and its nonzero slopes are the rams of `L / K`. For `ε > 1` it has a
segment of slope `0`, which is not a ram, so the knowl's "The slopes of the segments of `P` are
the rams" needs "nonzero slopes".

## Main results

* `IsNonarchimedeanLocalField.isEisensteinAt_minpoly_unramifiedExtension` (LMFDB
  `lf.ramification_polygon`): the minimal polynomial of a uniformiser over the maximal unramified
  subextension is Eisenstein.
* `IsNonarchimedeanLocalField.ramificationPolygonOf_minpoly_unramifiedExtension` (LMFDB
  `lf.ramification_polygon`): in a tower `M / L / K` with `M / K` finite Galois, the ramification
  polygon of `L / K` at every uniformiser is that of the Herbrand invariant of `L / K`.
* `IsNonarchimedeanLocalField.ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant` (LMFDB
  `lf.ramification_polygon`): the same for a finite extension inside `K̄`.
* `IsNonarchimedeanLocalField.ramificationPolygonOf_minpoly_eq_of_irreducible` (LMFDB
  `lf.ramification_polygon`): the ramification polygon does not depend on the uniformiser.
* `IsNonarchimedeanLocalField.setOf_mem_segmentSlopes_ramificationPolygonOf_minpoly_ne_zero` (LMFDB
  `lf.ramification_polygon`): the nonzero slopes of the segments of the ramification polygon of
  `L / K` are the rams of `L / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.ramificationPolygonOf_minpoly` (LMFDB
  `lf.ramification_polygon`): the ramification polygon of every extension in a family `I / K`, at
  every uniformiser, is the ramification polygon of `I`.

## References

* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, Proposition 1 and Lemma 1.
-/

open IntermediateField TauCeti ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

open HerbrandInvariant

variable (K : Type*) {L : Type*} (M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] {α : 𝒪[L]}

/-- **The minimal polynomial of a uniformiser over the maximal unramified subextension is
Eisenstein** (LMFDB `lf.ramification_polygon`): for a finite extension `L / K` of nonarchimedean
local fields with maximal unramified subextension `K'`, over which `L` is totally ramified
(`TauCeti.isTotallyRamified_unramifiedExtension_inertiaDegree`), the minimal polynomial over
`𝒪[K']` of a uniformiser `α` of `L` is Eisenstein. The minimal polynomial of `α` over the field
`K'` is its image (Mathlib's `minpoly.isIntegrallyClosed_eq_field_fractions`). -/
lemma isEisensteinAt_minpoly_unramifiedExtension (hα : Irreducible α) :
    (minpoly 𝒪[unramifiedExtension K L (inertiaDegree K L)] α).IsEisensteinAt
      𝓂[unramifiedExtension K L (inertiaDegree K L)] :=
  (isTotallyRamified_unramifiedExtension_inertiaDegree K L).isEisensteinAt_minpoly hα

variable [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M] [Algebra L M]
  [ValuativeExtension L M] [Module.Finite L M] [IsScalarTower K L M]

/-- **The ramification polygon of an extension is that of its Herbrand invariant** (LMFDB
`lf.ramification_polygon`): let `L / K` be a finite extension of nonarchimedean local fields, inside
a finite Galois extension `M / K`, with maximal unramified subextension `K'`. For every uniformiser
`α` of `L`, with minimal polynomial `φ` over `K'`, the ramification polygon of `L / K` at `α`, the
lower convex hull of the points `(-i, v_L(ρ_i))` of `ρ(x) = α ^ (-n) φ(α x + α)`, is the
ramification polygon of the Herbrand invariant of `L / K`. So it does not depend on `α`. -/
lemma ramificationPolygonOf_minpoly_unramifiedExtension (hα : Irreducible α) :
    ramificationPolygonOf (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)) (α : L) =
      (herbrandInvariantOfTower K M L).reflectedPolygon := by
  have hFM : ValuativeExtension (unramifiedExtension K L (inertiaDegree K L)) M :=
    .trans _ L M
  have fFM : Module.Finite (unramifiedExtension K L (inertiaDegree K L)) M :=
    .of_restrictScalars_finite K _ M
  have hur : IsUnramified K (unramifiedExtension K L (inertiaDegree K L)) :=
    isUnramified_unramifiedExtension_inertiaDegree K L
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  exact ((isMongeStage_minpoly (isTotallyRamified_unramifiedExtension_inertiaDegree K L)
    hα).isRamificationPolygon_of_hasSameRams K M (.refl _)).ramificationPolygonOf_minpoly hα

variable {K} [CharZero K] (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
  {π π' : 𝒪[E]}

/-- **The ramification polygon of an extension inside `K̄` is that of its Herbrand invariant**
(LMFDB `lf.ramification_polygon`): let `E` be a finite extension of a `p`-adic field `K` inside
`K̄`, with maximal unramified subextension `K'`. For every uniformiser `π` of `E`, with minimal
polynomial `φ` over `K'`, the ramification polygon of `E / K` at `π`, the lower convex hull of the
points `(-i, v_E(ρ_i))` of `ρ(x) = π ^ (-n) φ(π x + π)`, is the ramification polygon of the
Herbrand invariant of `E / K`, for Tau Ceti's spectral-norm local-field structure on `E`. -/
lemma ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant (hπ : Irreducible π) :
    ramificationPolygonOf (minpoly (unramifiedExtension K E (inertiaDegree K E)) (π : E)) (π : E) =
      (visibleHerbrandInvariant E).reflectedPolygon := by
  have hEM : E ≤ Algebra.galoisClosure K E :=
    Algebra.galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
  let aEM : Algebra E (Algebra.galoisClosure K E) := (inclusion hEM).toAlgebra
  have sEM : IsScalarTower K E (Algebra.galoisClosure K E) := .of_algebraMap_eq fun _ ↦ rfl
  have vEM : ValuativeExtension E (Algebra.galoisClosure K E) := (inclusion hEM).valuativeExtension
  have fEM : Module.Finite E (Algebra.galoisClosure K E) := .of_restrictScalars_finite K E _
  rw [visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
  exact ramificationPolygonOf_minpoly_unramifiedExtension K (Algebra.galoisClosure K E) hπ

/-- **The ramification polygon does not depend on the uniformiser** (LMFDB
`lf.ramification_polygon`): for a finite extension `E` of a `p`-adic field `K` inside `K̄`, with
maximal unramified subextension `K'`, and two uniformisers `π` and `π'` of `E`, the ramification
polygons of `E / K` at `π` and at `π'` agree. -/
lemma ramificationPolygonOf_minpoly_eq_of_irreducible (hπ : Irreducible π) (hπ' : Irreducible π') :
    ramificationPolygonOf (minpoly (unramifiedExtension K E (inertiaDegree K E)) (π : E)) (π : E) =
      ramificationPolygonOf (minpoly (unramifiedExtension K E (inertiaDegree K E)) (π' : E))
        (π' : E) :=
  (ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant E hπ).trans
    (ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant E hπ').symm

/-- **The nonzero slopes of the ramification polygon of an extension are its rams** (LMFDB
`lf.ramification_polygon`, with "nonzero slopes" for "slopes"): for a finite extension `E` of a
`p`-adic field `K` inside `K̄` and a uniformiser `π` of `E`, the nonzero slopes of the segments of
the ramification polygon of `E / K` at `π` are the rams of `E / K`, Deligne's positive lower
ramification breaks `IsNonarchimedeanLocalField.visibleRams`. -/
lemma setOf_mem_segmentSlopes_ramificationPolygonOf_minpoly_ne_zero (hπ : Irreducible π) :
    {s | s ≠ 0 ∧ s ∈ segmentSlopes (ramificationPolygonOf
      (minpoly (unramifiedExtension K E (inertiaDegree K E)) (π : E)) (π : E))} =
      {s | ∃ r ∈ visibleRams E, (r : ℝ) = s} := by
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  rw [ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant E hπ,
    setOf_mem_segmentSlopes_reflectedPolygon_ne_zero,
    (isInvariantOf_visibleHerbrandInvariant E).visibleRams_eq rfl]
  simp

namespace HerbrandInvariant

variable {p p' : ℕ} {I : HerbrandInvariant p} {J : HerbrandInvariant p'}

lemma HasSameRams.ramificationPolygon_eq (h : I.HasSameRams J) :
    I.ramificationPolygon = J.ramificationPolygon := by
  rcases h with ⟨rfl, hw, hε, hram⟩
  rcases I with ⟨w, ram, ε⟩
  rcases J with ⟨w', ram', ε'⟩
  dsimp only at hw hε hram
  subst hw hε hram
  rfl

variable {E} in
/-- **The ramification polygon of the extensions in a family** (LMFDB `lf.ramification_polygon`):
for a Herbrand invariant `I` at the residue characteristic of a `p`-adic field `K`, an extension `E`
inside `K̄` in the family `I / K`, with maximal unramified subextension `K'`, and a uniformiser `π`
of `E`, the ramification polygon of `E / K` at `π` is the ramification polygon of `I`. So the
ramification polygon of the family `I / K` is that of any extension in `I / K`, at any uniformiser;
its nonzero slopes are the rams of `I`
(`IsNonarchimedeanLocalField.HerbrandInvariant.setOf_mem_segmentSlopes_reflectedPolygon_ne_zero`),
which are those of every extension in `I / K`. -/
lemma IsInvariantOf.ramificationPolygonOf_minpoly (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) (hπ : Irreducible π) :
    ramificationPolygonOf (minpoly (unramifiedExtension K E (inertiaDegree K E)) (π : E)) (π : E) =
      I.reflectedPolygon := by
  rw [ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant E hπ, reflectedPolygon,
    reflectedPolygon, (hE.hasSameRams_visibleHerbrandInvariant hp).ramificationPolygon_eq]

end HerbrandInvariant

end IsNonarchimedeanLocalField
