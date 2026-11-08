import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.CurveX3SubX
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication

/-!
# The geometric endomorphism ring of an elliptic curve

The **geometric endomorphism ring** (LMFDB `ec.geom_endomorphism_ring`) of an elliptic curve `E`
over a field `F` is `End(E_F̄)`, the endomorphism ring of the base change of `E` to an algebraic
closure `F̄` of `F`. For a Weierstrass curve `W` it is Tau Ceti's endomorphism ring
`TauCeti.Isogeny.Hom (W⁄F̄) (W⁄F̄)`, with addition the group law on morphisms and multiplication
composition, here with `F̄` Mathlib's `AlgebraicClosure F`
(`WeierstrassCurve.GeometricEndAlgClosure`).

The ring does not depend on the choice of the algebraic closure. Base change of endomorphisms
along a homomorphism `σ : K →ₐ[F] L` of extensions of `F` is an injective ring homomorphism
`End(W_K) → End(W_L)`, functorial in `σ`; so an isomorphism of extensions gives an isomorphism of
endomorphism rings, and any two algebraic closures of `F` are isomorphic over `F`.

Tau Ceti's `WeierstrassCurve.GeometricEnd` is the endomorphism ring over the separable closure
`SeparableClosure F` instead. It embeds into the ring of this file, so geometric complex
multiplication in Tau Ceti's sense gives elements of `End(W_F̄)` outside `ℤ`. The separable
closure is an algebraic closure exactly when `F` is perfect, and then the two rings are
isomorphic. Over an imperfect field, such as `𝔽_p(t)`, every endomorphism over `F̄` is in fact
defined over the separable closure, so that the two rings still agree; this is not proved here,
and is not needed: the ring of this file is defined over an algebraic closure for every field.

## Main definitions

* `WeierstrassCurve.baseChangeEndHom`: base change of endomorphisms along `K →ₐ[F] L`.
* `WeierstrassCurve.baseChangeEndEquiv`: base change of endomorphisms along `K ≃ₐ[F] L`.
* `WeierstrassCurve.GeometricEndAlgClosure` (LMFDB `ec.geom_endomorphism_ring`): the
  endomorphism ring of `W` over `AlgebraicClosure F`.
* `WeierstrassCurve.geometricEndAlgClosureEquiv` (LMFDB `ec.geom_endomorphism_ring`): its
  isomorphism with the endomorphism ring of `W` over any algebraic closure of `F`.
* `WeierstrassCurve.geometricEndEquivAlgClosure`: over a perfect field, its isomorphism with Tau
  Ceti's `WeierstrassCurve.GeometricEnd`.

## Main results

* `WeierstrassCurve.baseChangeEndHom_injective`: base change of endomorphisms is injective.
* `WeierstrassCurve.HasGeometricCM.exists_notMem_range_intCast`: geometric complex multiplication
  in Tau Ceti's sense gives an element of `W.GeometricEndAlgClosure` that is not an integer.
* `WeierstrassCurve.exists_notMem_range_intCast_curveX3SubX`: so does the curve `y² = x³ - x`
  over `ℚ`.
-/

open TauCeti Isogeny CurveX3SubX

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F) {K L M : Type*} [Field K] [Field L]
  [Field M]

lemma heq_hom_map_of_heq {f₁ f₂ : F →+* L} (hf : f₁ = f₂)
    {a : Hom (W.map f₁).toAffine (W.map f₁).toAffine}
    {b : Hom (W.map f₂).toAffine (W.map f₂).toAffine} (h : a ≍ b) (τ : L →+* M) :
    a.map τ ≍ b.map τ := by
  subst hf
  rw [eq_of_heq h]

variable [W.IsElliptic] [Algebra F K] [Algebra F L] [Algebra F M] (σ : K →ₐ[F] L)
  (g : Hom (W⁄K).toAffine (W⁄K).toAffine)

/-- **Base change of endomorphisms** of an elliptic curve `W` over `F` along a homomorphism
`σ : K →ₐ[F] L` of extensions of `F`: the ring homomorphism `End(W_K) → End(W_L)` sending an
endomorphism of `W⁄K` to its base change along `σ`, an endomorphism of `(W⁄K).map σ`, which is
`W⁄L`. -/
noncomputable def baseChangeEndHom :
    Hom (W⁄K).toAffine (W⁄K).toAffine →+* Hom (W⁄L).toAffine (W⁄L).toAffine :=
  (RingEquiv.cast (R := fun f : F →+* L ↦ Hom (W.map f).toAffine (W.map f).toAffine)
    σ.comp_algebraMap).toRingHom.comp (Hom.mapRingHom (σ : K →+* L))

lemma heq_baseChangeEndHom : W.baseChangeEndHom σ g ≍ g.map (σ : K →+* L) :=
  cast_heq _ _

lemma baseChangeEndHom_baseChangeEndHom (τ : L →ₐ[F] M) :
    W.baseChangeEndHom τ (W.baseChangeEndHom σ g) = W.baseChangeEndHom (τ.comp σ) g :=
  eq_of_heq <| (W.heq_baseChangeEndHom τ _).trans <| (W.heq_hom_map_of_heq σ.comp_algebraMap.symm
    (W.heq_baseChangeEndHom σ g) (τ : L →+* M)).trans <|
      (heq_of_eq <| Hom.map_map g (σ : K →+* L) (τ : L →+* M)).trans
        (W.heq_baseChangeEndHom (τ.comp σ) g).symm

lemma baseChangeEndHom_id_apply : W.baseChangeEndHom (AlgHom.id F K) g = g :=
  eq_of_heq <| (W.heq_baseChangeEndHom (AlgHom.id F K) g).trans <| heq_of_eq <| Hom.map_id g

/-- **Base change of endomorphisms is injective**: an endomorphism of `W⁄K` is determined by its
base change along any homomorphism `σ : K →ₐ[F] L` of extensions of `F`. -/
lemma baseChangeEndHom_injective : Function.Injective (W.baseChangeEndHom σ) :=
  fun a b h ↦ Hom.map_injective (σ : K →+* L) <| eq_of_heq <|
    (W.heq_baseChangeEndHom σ a).symm.trans <| (heq_of_eq h).trans <| W.heq_baseChangeEndHom σ b

/-- **Base change of endomorphisms along an isomorphism** `e : K ≃ₐ[F] L` of extensions of `F`:
the ring isomorphism `End(W_K) ≃ End(W_L)` given by base change along `e`, with inverse the base
change along `e⁻¹`. -/
noncomputable def baseChangeEndEquiv (e : K ≃ₐ[F] L) :
    Hom (W⁄K).toAffine (W⁄K).toAffine ≃+* Hom (W⁄L).toAffine (W⁄L).toAffine :=
  RingEquiv.ofRingHom (W.baseChangeEndHom e) (W.baseChangeEndHom e.symm)
    (RingHom.ext fun a ↦ by
      rw [RingHom.comp_apply, baseChangeEndHom_baseChangeEndHom, e.comp_symm,
        baseChangeEndHom_id_apply, RingHom.id_apply])
    (RingHom.ext fun a ↦ by
      rw [RingHom.comp_apply, baseChangeEndHom_baseChangeEndHom, e.symm_comp,
        baseChangeEndHom_id_apply, RingHom.id_apply])

/-- The **geometric endomorphism ring** (LMFDB `ec.geom_endomorphism_ring`) of an elliptic curve
`W` over `F`: the endomorphism ring `End(W_F̄)` of its base change to an algebraic closure `F̄` of
`F`, here Mathlib's `AlgebraicClosure F`. Any other algebraic closure of `F` gives an isomorphic
ring (`WeierstrassCurve.geometricEndAlgClosureEquiv`). -/
abbrev GeometricEndAlgClosure : Type _ :=
  Hom (W⁄(AlgebraicClosure F)).toAffine (W⁄(AlgebraicClosure F)).toAffine

variable (K) in
/-- **The geometric endomorphism ring does not depend on the algebraic closure** (LMFDB
`ec.geom_endomorphism_ring`): for every algebraic closure `K` of `F`, the endomorphism ring of
`W⁄K` is isomorphic to `W.GeometricEndAlgClosure`, by base change along an isomorphism
`AlgebraicClosure F ≃ₐ[F] K`. -/
noncomputable def geometricEndAlgClosureEquiv [IsAlgClosure F K] :
    W.GeometricEndAlgClosure ≃+* Hom (W⁄K).toAffine (W⁄K).toAffine :=
  W.baseChangeEndEquiv (IsAlgClosure.equiv F (AlgebraicClosure F) K)

/-- The **isomorphism of Tau Ceti's geometric endomorphism ring with that of this file** over a
perfect field `F`: Tau Ceti's `W.GeometricEnd`, over the separable closure `SeparableClosure F`, is
isomorphic to the geometric endomorphism ring `W.GeometricEndAlgClosure` over the algebraic
closure, since the separable closure of a perfect field is an algebraic closure. -/
noncomputable def geometricEndEquivAlgClosure [PerfectField F] :
    W.GeometricEnd ≃+* W.GeometricEndAlgClosure :=
  W.baseChangeEndEquiv (IsAlgClosure.equiv F (SeparableClosure F) (AlgebraicClosure F))

variable {W} in
/-- **Geometric complex multiplication is seen over the algebraic closure**: if some endomorphism
of `W` over the separable closure is not an integer (Tau Ceti's `WeierstrassCurve.HasGeometricCM`),
then some element of the geometric endomorphism ring `W.GeometricEndAlgClosure` is not an integer,
over every field. -/
lemma HasGeometricCM.exists_notMem_range_intCast (h : W.HasGeometricCM) :
    ∃ f : W.GeometricEndAlgClosure, f ∉ Set.range ((↑) : ℤ → W.GeometricEndAlgClosure) := by
  rcases h with ⟨f, hf⟩
  let ι : SeparableClosure F →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  refine ⟨W.baseChangeEndHom ι f, fun ⟨n, hn⟩ ↦ hf ⟨n, W.baseChangeEndHom_injective ι ?_⟩⟩
  rw [map_intCast, hn]

/-- **The curve `y² = x³ - x` over `ℚ` has a geometric endomorphism that is not an integer**: over
`ℚ̄` it has the automorphism `(x, y) ↦ (-x, iy)`. -/
lemma exists_notMem_range_intCast_curveX3SubX : ∃ f : (curve ℚ).GeometricEndAlgClosure,
    f ∉ Set.range ((↑) : ℤ → (curve ℚ).GeometricEndAlgClosure) := by
  have : (curve ℚ).IsShortNF := ⟨rfl, rfl, rfl⟩
  exact (hasGeometricCM_of_a₆_eq_zero (curve ℚ).toAffine rfl).exists_notMem_range_intCast

end WeierstrassCurve
