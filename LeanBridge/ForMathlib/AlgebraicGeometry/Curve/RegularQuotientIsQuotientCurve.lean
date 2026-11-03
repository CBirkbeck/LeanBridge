import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Quotient
import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.RegularQuotientUniversal

/-!
# The quotient of a regular proper curve is a quotient curve

LeanBridge's `AlgebraicGeometry.Scheme.IsQuotientCurve` (LMFDB `ag.quotient_curve`) characterizes
the quotient curve `X / H` of an algebraic curve `X` over `k` by a finite group `H` of automorphisms
of `X` over `k` by its universal property among all schemes over `k`, and asks for `X` and `X / H`
to be algebraic curves, in particular geometrically integral. This file proves it for the quotient
`TauCeti.AlgebraicGeometry.RegularProperCurveCat.quotient` of a geometrically integral regular
proper curve, such as a smooth projective curve, with the projection
`TauCeti.AlgebraicGeometry.RegularProperCurveCat.toQuotient`: the universal property is
`TauCeti.AlgebraicGeometry.RegularProperCurveCat.toQuotient_comp_desc` and
`TauCeti.AlgebraicGeometry.RegularProperCurveCat.eq_desc_iff`, and `X / H` is geometrically integral
by `TauCeti.AlgebraicGeometry.RegularProperCurveCat.geometricallyIntegral_quotient`.

Every automorphism of `X` as a scheme over `k` is an automorphism of the regular proper curve `X`,
so every finite group of automorphisms of `X` over `k` has a quotient curve. In particular, every
algebraic curve over `k` in the sense of `AlgebraicGeometry.Scheme.IsAlgebraicCurveOver` that is
proper and regular, such as a smooth projective curve, has a quotient curve by every finite group
of its automorphisms. As two quotient curves of `X` by `H` are uniquely isomorphic, the projection
onto any quotient curve of `X` is surjective and its fibres are the `H`-orbits, so that the
quotient curve is obtained from `X` by identifying the points of each `H`-orbit, as in the knowl.

The quotient of an algebraic curve that is not regular or not proper is constructed in
`LeanBridge.ForMathlib.AlgebraicGeometry.Curve.QuotientExistence`
(`AlgebraicGeometry.Scheme.exists_isQuotientCurve`), from an `H`-stable affine open cover, which
exists since every finite set of closed points lies in an affine open
(`AlgebraicGeometry.Scheme.exists_isAffineOpen_forall_mem`), and the gluing of the invariant
quotients of its members.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.toOver`: the functor sending a regular proper
  curve over `k` to its underlying scheme over `k`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.autMulEquivToOver`: the automorphisms of a
  regular proper curve are its automorphisms as a scheme over `k`.

## Main results

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.isQuotientCurve_toQuotient` (LMFDB
  `ag.quotient_curve`): the projection `X ⟶ X / H` exhibits `X / H` as the quotient curve of `X`
  by `H`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.isQuotientCurve_toQuotient_comap`: the same for
  any finite group of automorphisms of `X` over `k`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.isQuotientCurve_toQuotient_of_isProper` (LMFDB
  `ag.quotient_curve`): every proper regular algebraic curve has a quotient curve by every finite
  group of its automorphisms.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.surjective_left_of_isQuotientCurve`: the
  projection onto a quotient curve is surjective.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.left_apply_eq_iff_of_isQuotientCurve`: the
  fibres of the projection onto a quotient curve are the `H`-orbits.
-/

open CategoryTheory Over AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.RegularProperCurveCat

universe u

variable {k : Type u} [Field k]

variable (k) in
/-- The **functor from regular proper curves over `k` to schemes over `k`**, sending a curve to its
underlying scheme over `k` and a dominant `k`-morphism to the underlying morphism over `k`, through
which `AlgebraicGeometry.Scheme.IsQuotientCurve` (LMFDB `ag.quotient_curve`) applies to regular
proper curves. -/
@[simps]
noncomputable def toOver : RegularProperCurveCat k ⥤ Over (Spec (.of k)) where
  obj X := X.toScheme.asOver (Spec (.of k))
  map f := f.hom.asOver (Spec (.of k))

variable {X : RegularProperCurveCat k}

lemma mapAut_toOver_injective : Function.Injective ((toOver k).mapAut X) :=
  fun _ _ h ↦ Aut.ext <| Iso.ext <| hom_ext <|
    congrArg (fun τ : Aut ((toOver k).obj X) ↦ τ.asIso.hom.left) h

lemma mapAut_toOver_surjective : Function.Surjective ((toOver k).mapAut X) := by
  intro τ
  let e : X.toScheme ≅ X.toScheme := (Over.forget _).mapIso τ.asIso
  have he : e.hom.IsOver (Spec (.of k)) := ⟨Over.w τ.asIso.hom⟩
  exact ⟨.of (isoMk e), Aut.ext <| Iso.ext <| OverMorphism.ext rfl⟩

/-- The **automorphisms of a regular proper curve** `X` over `k` (LMFDB `g2c.aut_grp`) are its
automorphisms as a scheme over `k`, through
`TauCeti.AlgebraicGeometry.RegularProperCurveCat.toOver`: every automorphism of the scheme `X` over
`k` is dominant. -/
noncomputable def autMulEquivToOver : Aut X ≃* Aut ((toOver k).obj X) :=
  .ofBijective ((toOver k).mapAut X) ⟨mapAut_toOver_injective, mapAut_toOver_surjective⟩

variable (H' : Subgroup (Aut ((toOver k).obj X))) [Finite H']

instance : Finite (H'.comap ((toOver k).mapAut X)) :=
  .of_injective (fun σ ↦ (⟨_, σ.2⟩ : H')) fun _ _ h ↦
    Subtype.ext (mapAut_toOver_injective (congrArg Subtype.val h))

variable (H : Subgroup (Aut X)) [Finite H] [GeometricallyIntegral (X.toScheme ↘ Spec (.of k))]

/-- **The quotient of a regular proper curve is a quotient curve** (LMFDB `ag.quotient_curve`):
for a geometrically integral regular proper curve `X` over `k`, such as a smooth projective curve,
and a finite group `H` of automorphisms of `X`, the projection `X ⟶ X / H` onto the regular proper
curve with function field `k(X)^H` satisfies `AlgebraicGeometry.Scheme.IsQuotientCurve`: `X / H`
is an algebraic curve over `k`, and every morphism over `k` from `X` to a scheme over `k`
invariant under `H` factors uniquely through the projection. -/
lemma isQuotientCurve_toQuotient :
    IsQuotientCurve (H.map ((toOver k).mapAut X)) ((toOver k).map (toQuotient H)) where
  isAlgebraicCurveOver_left :=
    (IsCurveOver.isAlgebraicCurveOver : X.toScheme.IsAlgebraicCurveOver k)
  finite := .of_surjective _ (((toOver k).mapAut X).subgroupMap_surjective H)
  isAlgebraicCurveOver_right := by
    have hint : GeometricallyIntegral ((quotient H).toScheme ↘ Spec (.of k)) :=
      geometricallyIntegral_quotient H
    exact (IsCurveOver.isAlgebraicCurveOver : (quotient H).toScheme.IsAlgebraicCurveOver k)
  hom_comp := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [Functor.mapAut_apply_asIso, Functor.mapIso_hom, ← Functor.map_comp, hom_comp_toQuotient hσ]
  existsUnique_comp_eq Z f hf := by
    let f₀ : X.toScheme ⟶ Z.left := f.left
    have hf₀ : ∀ σ ∈ H, σ.asIso.hom.hom ≫ f₀ = f₀ :=
      fun σ hσ ↦ congrArg CommaMorphism.left (hf _ ⟨σ, hσ, rfl⟩)
    have hk : f₀.IsOver (Spec (.of k)) := ⟨Over.w f⟩
    exact ⟨Over.homMk (desc hf₀) (desc_comp_over hf₀), OverMorphism.ext (toQuotient_comp_desc hf₀),
      fun g hg ↦ OverMorphism.ext <| (eq_desc_iff hf₀).mpr <| congrArg CommaMorphism.left hg⟩

/-- **Every finite group of automorphisms of a regular proper curve has a quotient curve** (LMFDB
`ag.quotient_curve`): for a geometrically integral regular proper curve `X` over `k` and a finite
group `H'` of automorphisms of `X` as a scheme over `k`, the projection onto the quotient of `X` by
the corresponding group of automorphisms of the regular proper curve `X` satisfies
`AlgebraicGeometry.Scheme.IsQuotientCurve`. -/
lemma isQuotientCurve_toQuotient_comap :
    IsQuotientCurve H' ((toOver k).map (toQuotient (H'.comap ((toOver k).mapAut X)))) := by
  have h : (H'.comap ((toOver k).mapAut X)).map ((toOver k).mapAut X) = H' :=
    H'.map_comap_eq_self_of_surjective mapAut_toOver_surjective
  exact (congrArg (fun S ↦ IsQuotientCurve S
    ((toOver k).map (toQuotient (H'.comap ((toOver k).mapAut X))))) h).mp
      (isQuotientCurve_toQuotient _)

variable {Y : Over (Spec (.of k))} {π : (toOver k).obj X ⟶ Y}

/-- **The projection onto a quotient curve is surjective**: if `π : X ⟶ Y` exhibits `Y` as the
quotient curve of a geometrically integral regular proper curve `X` by a finite group `H'` of
automorphisms of `X` over `k`, in the sense of `AlgebraicGeometry.Scheme.IsQuotientCurve`, then
`π` is surjective, since `Y` is isomorphic to `X / H'` compatibly with the projections. -/
lemma surjective_left_of_isQuotientCurve (hπ : IsQuotientCurve H' π) : Surjective π.left := by
  rw [← (isQuotientCurve_toQuotient_comap H').comp_uniqueUpToIso_hom hπ, Over.comp_left]
  have hs : Surjective ((toOver k).map (toQuotient (H'.comap ((toOver k).mapAut X)))).left :=
    surjective_toQuotient _
  infer_instance

/-- **The fibres of the projection onto a quotient curve are the orbits**: if `π : X ⟶ Y` exhibits
`Y` as the quotient curve of a geometrically integral regular proper curve `X` by a finite group
`H'` of automorphisms of `X` over `k`, in the sense of `AlgebraicGeometry.Scheme.IsQuotientCurve`,
then two points of `X` have the same image exactly when an element of `H'` maps one to the other,
so that `Y` is obtained from `X` by identifying the points of each orbit. -/
lemma left_apply_eq_iff_of_isQuotientCurve (hπ : IsQuotientCurve H' π) {x y : X.toScheme} :
    π.left x = π.left y ↔ ∃ σ ∈ H', σ.asIso.hom.left x = y := by
  let e : (toOver k).obj (quotient (H'.comap ((toOver k).mapAut X))) ≅ Y :=
    (isQuotientCurve_toQuotient_comap H').uniqueUpToIso hπ
  have he : ∀ z : X.toScheme, π.left z = e.hom.left ((toQuotient _).hom z) :=
    fun z ↦ (congrArg (fun g ↦ g.left z)
      ((isQuotientCurve_toQuotient_comap H').comp_uniqueUpToIso_hom hπ)).symm
  rw [he, he]
  refine (e.hom.left.isOpenEmbedding.injective.eq_iff.trans toQuotient_apply_eq_iff).trans
    ⟨fun ⟨σ, hσ, hσx⟩ ↦ ⟨_, hσ, hσx⟩, fun ⟨τ, hτ, hτx⟩ ↦ ?_⟩
  rcases mapAut_toOver_surjective τ with ⟨σ, rfl⟩
  exact ⟨σ, hτ, hτx⟩

variable {C : Over (Spec (.of k))} [C.left.IsAlgebraicCurveOver k]
  [IsProper (C.left ↘ Spec (.of k))]
  [∀ y : CodimensionOnePoint C.left, IsDiscreteValuationRing (C.left.presheaf.stalk y.1)]
  (G : Subgroup (Aut C)) [Finite G]

/-- **Every proper regular algebraic curve has a quotient curve by every finite group of
automorphisms** (LMFDB `ag.quotient_curve`): for an algebraic curve `C` over `k`, in the sense of
`AlgebraicGeometry.Scheme.IsAlgebraicCurveOver`, that is proper over `k` and whose local rings at
the closed points are discrete valuation rings, such as a smooth projective curve, and a finite
group `G` of automorphisms of `C` over `k`, the projection of the regular proper curve `C` onto its
quotient by `G` satisfies `AlgebraicGeometry.Scheme.IsQuotientCurve`. -/
lemma isQuotientCurve_toQuotient_of_isProper :
    letI G' : Subgroup (Aut ((toOver k).obj (of C.left))) := G
    haveI : Finite G' := ‹Finite G›
    IsQuotientCurve G ((toOver k).map (toQuotient (G'.comap ((toOver k).mapAut (of C.left))))) := by
  let G' : Subgroup (Aut ((toOver k).obj (of C.left))) := G
  have hG' : Finite G' := ‹Finite G›
  exact isQuotientCurve_toQuotient_comap G'

end TauCeti.AlgebraicGeometry.RegularProperCurveCat
