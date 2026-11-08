import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.LocallySolvable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Points of a scheme of finite type over a finite field

A scheme `X` of finite type over a finite field `K` (LMFDB `ag.fq.point_counts`), such as a variety
over `𝔽_q`, has finitely many points over every finite extension `L` of `K`
(`AlgebraicGeometry.Scheme.finite_pointOver`): the set `X(L)` of morphisms `Spec L ⟶ X` over
`Spec K` (LeanBridge's `AlgebraicGeometry.Scheme.PointOver`) is finite, so that its number of
elements `Nat.card (X.PointOver K L)` is the number of points of `X` over `L`, for `L = K` and for
`L = 𝔽_{q^n}`.

Indeed `X` is quasi-compact, so finitely many affine charts `Spec Rⱼ ⟶ X` cover it, and the rings
`Rⱼ` are finitely generated over `K`, hence as rings, `K` being finite. A morphism `Spec L ⟶ X`
from the spectrum of a field has image a point, so it factors through one of these charts, where it
is given by a ring homomorphism `Rⱼ → L`; and there are finitely many ring homomorphisms from a
finitely generated ring to the finite ring `L`, determined by the images of the generators.

## Main results

* `AlgebraicGeometry.Scheme.finite_pointOver` (LMFDB `ag.fq.point_counts`): a scheme of finite type
  over a finite field `K` has finitely many points over every finite extension of `K`.
-/

open CategoryTheory

universe u

lemma finite_ringHom_of_finiteType_int {A B : Type*} [CommRing A] [CommRing B] [Finite B]
    (hA : (Int.castRingHom A).FiniteType) : Finite (A →+* B) := by
  have hA' : Algebra.FiniteType ℤ A :=
    RingHom.finiteType_algebraMap.mp (by rwa [algebraMap_int_eq])
  rcases hA'.out with ⟨s, hs⟩
  refine Finite.of_injective (fun φ : A →+* B ↦ fun x : s ↦ φ x) fun φ ψ h ↦ ?_
  have h₁ : φ.toIntAlgHom = ψ.toIntAlgHom :=
    AlgHom.ext_of_adjoin_eq_top hs fun x hx ↦ congrFun h ⟨x, hx⟩
  exact RingHom.ext (AlgHom.congr_fun h₁)

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (L : Type u) [Field L]

lemma finite_hom_spec_of_finiteType [CompactSpace X] [Finite L]
    (hX : ∀ j, (Int.castRingHom (X.affineOpenCover.X j)).FiniteType) :
    Finite (Spec (.of L) ⟶ X) := by
  rcases isCompact_univ.elim_finite_subcover (fun j ↦ Set.range (X.affineOpenCover.f j))
    (fun j ↦ (X.affineOpenCover.f j).isOpenEmbedding.isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨X.affineOpenCover.idx x, X.affineOpenCover.covers x⟩)
    with ⟨t, ht⟩
  have hfin (j : X.affineOpenCover.I₀) :
      {P : Spec (.of L) ⟶ X | Set.range P ⊆ Set.range (X.affineOpenCover.f j)}.Finite := by
    have : Finite (X.affineOpenCover.X j →+* L) := finite_ringHom_of_finiteType_int (hX j)
    have : Finite (X.affineOpenCover.X j ⟶ .of L) :=
      Finite.of_injective (fun φ ↦ φ.hom) fun φ ψ h ↦ CommRingCat.hom_ext h
    refine Set.finite_coe_iff.mp (Finite.of_injective (fun P : {P : Spec (.of L) ⟶ X |
      Set.range P ⊆ Set.range (X.affineOpenCover.f j)} ↦
        Spec.preimage (IsOpenImmersion.lift (X.affineOpenCover.f j) P.1 P.2)) fun P Q h ↦ ?_)
    have h₁ : IsOpenImmersion.lift (X.affineOpenCover.f j) P.1 P.2 =
        IsOpenImmersion.lift (X.affineOpenCover.f j) Q.1 Q.2 :=
      (Spec.map_preimage _).symm.trans ((congrArg Spec.map h).trans (Spec.map_preimage _))
    exact Subtype.ext ((IsOpenImmersion.lift_fac _ _ P.2).symm.trans
      ((congrArg (· ≫ X.affineOpenCover.f j) h₁).trans (IsOpenImmersion.lift_fac _ _ Q.2)))
  refine Set.finite_univ_iff.mp ((t.finite_toSet.biUnion fun j _ ↦ hfin j).subset fun P _ ↦ ?_)
  rcases Set.mem_iUnion₂.mp (ht (Set.mem_univ (P (IsLocalRing.closedPoint L)))) with ⟨j, hj, hP⟩
  refine Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
  rintro _ ⟨y, rfl⟩
  rwa [Subsingleton.elim y (IsLocalRing.closedPoint L)]

lemma finiteType_int_affineOpenCover (K : Type u) [Field K] [Finite K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (j : X.affineOpenCover.I₀) :
    (Int.castRingHom (X.affineOpenCover.X j)).FiniteType := by
  let φ : CommRingCat.of K ⟶ X.affineOpenCover.X j :=
    Spec.preimage (X.affineOpenCover.f j ≫ X ↘ Spec (.of K))
  have h₁ : LocallyOfFiniteType (Spec.map φ) := by
    rw [Spec.map_preimage]
    infer_instance
  have h₂ : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp h₁
  have h₃ : (Int.castRingHom K).FiniteType :=
    (RingHom.finite_algebraMap.mpr inferInstance).finiteType
  have h₄ : (φ.hom.comp (Int.castRingHom K)).FiniteType := h₂.comp h₃
  rwa [RingHom.ext_int (φ.hom.comp (Int.castRingHom K)) (Int.castRingHom _)] at h₄

variable {K : Type u} [Field K] [Finite K] [X.Over (Spec (.of K))]
  [LocallyOfFiniteType (X ↘ Spec (.of K))]

/-- **A scheme `X` of finite type over a finite field `K` has finitely many points over every finite
extension `L` of `K`** (LMFDB `ag.fq.point_counts`): in particular finitely many rational points,
and finitely many points over `𝔽_{q^n}` for `K = 𝔽_q`. -/
lemma finite_pointOver [QuasiCompact (X ↘ Spec (.of K))] [Algebra K L] [FiniteDimensional K L] :
    Finite (X.PointOver K L) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))
  have : Finite L := Module.finite_of_finite K
  have : Finite (Spec (.of L) ⟶ X) :=
    X.finite_hom_spec_of_finiteType L (X.finiteType_int_affineOpenCover K)
  exact Subtype.finite

end AlgebraicGeometry.Scheme
