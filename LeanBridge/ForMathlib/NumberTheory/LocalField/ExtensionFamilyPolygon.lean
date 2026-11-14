import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamilyInvariants
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolygonHull

/-!
# The ramification polygon of a family of extensions

Let `K` be a `p`-adic field, `I = (r_1, …, r_w)_ε^f` a Herbrand invariant at the residue
characteristic `p` of `K`, and `K_f` the unramified extension of `K` of degree `f` inside `K̄`.
Every extension `L` inside `K̄` in the family `I / K` contains `K_f` and is totally ramified over
it, so the minimal polynomial over `𝒪_{K_f}` of a uniformiser `π` of `L` is Eisenstein, and the
ramification polygon of `L` (LMFDB `lf.ramification_polygon`) is the Newton polygon of the
ramification polynomial `ρ(x) = π ^ (-e) φ(π x + π)` of this minimal polynomial `φ`: the lower
convex hull of the points `(i, v_L(ρ_i))`, which the LMFDB reflects through the vertical axis.

We prove that it is the ramification polygon of `I`
(`IsNonarchimedeanLocalField.HerbrandInvariant.ramificationPolygon`), with the vertices
`(p ^ (w - k), e m_k)` and `(e, 0)`, for every extension in the family and every uniformiser: so the
ramification polygon of the family `I / K` is well defined, as LMFDB `lf.ramification_polygon`
states. Its slopes between the consecutive powers of `p` are `-r_1, …, -r_w`
(`IsNonarchimedeanLocalField.HerbrandInvariant.unitSlope_ramificationPolygon`), the negatives of
the rams of every extension in the family, these rams being those of `I`
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.visibleRams_eq`). When `ε > 1` the
polygon also has the horizontal segment from `(p ^ w, 0)` to `(e, 0)`
(`IsNonarchimedeanLocalField.HerbrandInvariant.unitSlope_ramificationPolygon_of_pow_le`), whose
slope `0` is not a ram: the nonzero slopes of the LMFDB's reflected polygon are the rams of every
extension in the family, which is the statement of LMFDB `lf.family_diagrams` and
`lf.ramification_polygon` with "nonzero slopes" for "slopes".

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.isRamificationPolygon_minpoly` (LMFDB
  `lf.family_diagrams`, `lf.ramification_polygon`): the ramification polygon of every extension in
  `I / K`, at every uniformiser, is the polygon of `I` in the sense of Monge's Proposition 1.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.lowerConvexEnvelope_minpoly` (LMFDB
  `lf.family_diagrams`, `lf.ramification_polygon`): the lower convex hull of the points of the
  ramification polynomial of every extension in `I / K`, at every uniformiser, is the ramification
  polygon of `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.map_visibleRams_eq_map_neg_unitSlope`
  (LMFDB `lf.family_diagrams`): the rams of every extension in `I / K` are the negatives of the
  slopes of the ramification polygon of `I` between the consecutive powers of `p`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.setOf_neg_unitSlope_ne_zero` (LMFDB
  `lf.family_diagrams`): the nonzero slopes of the reflection of the ramification polygon of `I`
  are the rams of every extension in `I / K`.

## References

* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, Proposition 1.
-/

open ValuativeRel TauCeti IntermediateField

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {E : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E] {p : ℕ}
  {I : HerbrandInvariant p}

/-- **The ramification polygon of the extensions in a family** (LMFDB `lf.family_diagrams`,
`lf.ramification_polygon`): let `E` be an extension inside `K̄` in the family `I / K`, for
`I = (r_1, …, r_w)_ε^f` at the residue characteristic of `K`, and `K_f ⊆ E` the unramified extension
of `K` of degree `f`, over which `E` is totally ramified. For every uniformiser `π` of `E`, the
ramification polygon of the minimal polynomial of `π` over `𝒪_{K_f}` at `π` is the polygon of `I`
in the sense of `IsRamificationPolygon`: the points of the ramification polynomial lie above the
lines of slope `-r_k` through `(p ^ (w - k), e m_k)`, which they meet at the vertices. -/
lemma IsInvariantOf.isRamificationPolygon_minpoly (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) :
    letI : ValuativeRel (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateFieldValuativeRel K _ _
    letI : TopologicalSpace (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateFieldTopology K _ _
    haveI : IsNonarchimedeanLocalField (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ _
    haveI : ValuativeExtension K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateField_valuativeExtension K _ _
    letI : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
    letI : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
    haveI : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
    haveI : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
    letI : Algebra (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
      (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).toAlgebra
    haveI : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
      (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).valuativeExtension
    ∀ π : 𝒪[E], Irreducible π →
      I.IsRamificationPolygon (minpoly 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f] π) π := by
  subst hp
  let vF : ValuativeRel (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tF : TopologicalSpace (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateFieldTopology K _ _
  have hF : IsNonarchimedeanLocalField (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKF : ValuativeExtension K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateField_valuativeExtension K _ _
  let vE : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
  have hE' : IsNonarchimedeanLocalField E :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
  let vM : ValuativeRel (Algebra.galoisClosure K E) := finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (Algebra.galoisClosure K E) := finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (Algebra.galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (Algebra.galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hFE : unramifiedExtension K (AlgebraicClosure K) I.f ≤ E :=
    unramifiedExtension_le_of_isInvariantOf hE
  have hEM : E ≤ Algebra.galoisClosure K E :=
    Algebra.galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
  let aFE : Algebra (unramifiedExtension K (AlgebraicClosure K) I.f) E := (inclusion hFE).toAlgebra
  let aFM : Algebra (unramifiedExtension K (AlgebraicClosure K) I.f) (Algebra.galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).toAlgebra
  let aEM : Algebra E (Algebra.galoisClosure K E) := (inclusion hEM).toAlgebra
  have sFE : IsScalarTower K (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sFM : IsScalarTower K (unramifiedExtension K (AlgebraicClosure K) I.f)
      (Algebra.galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sEM : IsScalarTower K E (Algebra.galoisClosure K E) := .of_algebraMap_eq fun _ ↦ rfl
  have sFEM : IsScalarTower (unramifiedExtension K (AlgebraicClosure K) I.f) E
      (Algebra.galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have vFE : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    (inclusion hFE).valuativeExtension
  have vFM : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) I.f)
      (Algebra.galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).valuativeExtension
  have vEM : ValuativeExtension E (Algebra.galoisClosure K E) := (inclusion hEM).valuativeExtension
  have fFM : Module.Finite (unramifiedExtension K (AlgebraicClosure K) I.f)
      (Algebra.galoisClosure K E) :=
    .of_restrictScalars_finite K _ _
  have fEM : Module.Finite E (Algebra.galoisClosure K E) := .of_restrictScalars_finite K E _
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  have hf₀ : I.f ≠ 0 := I.f_pos.ne'
  have hur : IsUnramified K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    isUnramified_unramifiedExtension hf₀
  have hs : I.HasSameRams (herbrandInvariantOfTower K (Algebra.galoisClosure K E) E) := by
    rw [← visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
    exact hasSameRams_of_isInvariantOf hE (isInvariantOf_visibleHerbrandInvariant E)
  have htr : IsTotallyRamified (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    (IsUnramified.isTotallyRamified_iff_finrank_eq K _ E).mpr
      ((finrank_unramifiedExtension hf₀).trans hE.1.symm)
  exact fun π hπ ↦
    IsMongeStage.isRamificationPolygon_of_hasSameRams K _ hs (isMongeStage_minpoly htr hπ)

/-- **The ramification polygon of a family is well defined** (LMFDB `lf.family_diagrams`,
`lf.ramification_polygon`): let `E` be an extension inside `K̄` in the family `I / K`, for
`I = (r_1, …, r_w)_ε^f` at the residue characteristic of `K`, and `K_f ⊆ E` the unramified extension
of `K` of degree `f`. For every uniformiser `π` of `E`, with minimal polynomial `φ` over `𝒪_{K_f}`,
the lower convex hull of the points `(n, v_E(ρ_n))`, for the coefficients `ρ_n ≠ 0` of the
ramification polynomial `ρ(x) = π ^ (-e) φ(π x + π)`, is the ramification polygon of `I`. So the
ramification polygon is the same for all the extensions in the family and all their uniformisers:
it has the vertices `(p ^ (w - k), e m_k)` and `(e, 0)`, its slopes between the consecutive powers
of `p` are `-r_1, …, -r_w`, and for `ε > 1` it has a horizontal segment from `(p ^ w, 0)` to
`(e, 0)`. The LMFDB draws the reflection through the vertical axis, whose nonzero slopes are the
rams. -/
lemma IsInvariantOf.lowerConvexEnvelope_minpoly (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) :
    letI : ValuativeRel (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateFieldValuativeRel K _ _
    letI : TopologicalSpace (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateFieldTopology K _ _
    haveI : IsNonarchimedeanLocalField (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ _
    haveI : ValuativeExtension K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateField_valuativeExtension K _ _
    letI : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
    letI : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
    haveI : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
    haveI : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
    letI : Algebra (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
      (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).toAlgebra
    haveI : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
      (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).valuativeExtension
    ∀ π : 𝒪[E], Irreducible π → lowerConvexEnvelope
      (ramificationHeight (minpoly 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f] π) π) =
        I.ramificationPolygon := by
  subst hp
  let vF : ValuativeRel (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tF : TopologicalSpace (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateFieldTopology K _ _
  have hF : IsNonarchimedeanLocalField (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKF : ValuativeExtension K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateField_valuativeExtension K _ _
  let vE : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
  have hE' : IsNonarchimedeanLocalField E :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
  let aFE : Algebra (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).toAlgebra
  have vFE : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).valuativeExtension
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  exact fun π hπ ↦ (hE.isRamificationPolygon_minpoly rfl π hπ).lowerConvexEnvelope_eq hπ
    (minpoly.monic <| IsIntegral.of_finite _ π) (minpoly.aeval _ π)

/-- **The slopes of the ramification polygon of a family are the rams of every extension in the
family** (LMFDB `lf.family_diagrams`, with "nonzero slopes" for "slopes"): the rams of an extension
`E` inside `K̄` in the family `I / K`, for `I = (r_1, …, r_w)_ε^f` at the residue characteristic of
`K`, are the negatives of the slopes of the ramification polygon of `I` from `p ^ (w - k)` to
`p ^ (w - k + 1)`, for `k = 1, …, w`, that is the slopes of its reflection through the vertical
axis, which the LMFDB draws. The only other slope is the slope `0` on `[p ^ w, e]`, for
`ε > 1`. -/
lemma IsInvariantOf.map_visibleRams_eq_map_neg_unitSlope (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) : (visibleRams E).map (↑) =
    (Multiset.range I.w).map fun j ↦ -unitSlope I.ramificationPolygon (p ^ (I.w - (j + 1))) := by
  subst hp
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  rw [I.map_neg_unitSlope_ramificationPolygon, hE.visibleRams_eq rfl, Multiset.map_map]
  rfl

/-- **The nonzero slopes of the ramification polygon of a family are the rams of every extension
in the family** (LMFDB `lf.family_diagrams`, with "nonzero slopes" for "slopes"): for an extension
`E` inside `K̄` in the family `I / K`, for `I = (r_1, …, r_w)_ε^f` at the residue characteristic of
`K`, the nonzero slopes of the reflection through the vertical axis of the ramification polygon of
`I`, on its edges from `n` to `n + 1` for `1 ≤ n < e`, are the rams of `E`. This polygon is the
ramification polygon of `E` at every uniformiser
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.lowerConvexEnvelope_minpoly`). -/
lemma IsInvariantOf.setOf_neg_unitSlope_ne_zero (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) :
    {s : ℝ | s ≠ 0 ∧ ∃ n ∈ Set.Ico 1 I.ramificationIndex, -unitSlope I.ramificationPolygon n = s} =
      {s | ∃ r ∈ visibleRams E, (r : ℝ) = s} := by
  subst hp
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  rw [I.setOf_neg_unitSlope_ramificationPolygon_ne_zero, hE.visibleRams_eq rfl]
  simp

end IsNonarchimedeanLocalField.HerbrandInvariant
