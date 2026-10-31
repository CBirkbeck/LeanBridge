import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Isogenous
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
import TauCeti.CategoryTheory.Monoidal.Grp.KernelPair

/-!
# Isogenies are the surjective homomorphisms with finite kernel

An isogeny of abelian varieties (LMFDB `av.isogeny`) is a surjective homomorphism with finite
kernel. Tau Ceti's `TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny` asks instead for a
homomorphism whose underlying morphism of schemes is finite and surjective. This file proves that
the two notions agree: a surjective homomorphism `f : A ⟶ B` of abelian varieties whose kernel
`A ×_B Spec K`, its fibre over the zero section of `B`, is finite over `K` is a finite morphism.

The proof is the classical one. As `A` is proper and `B` is separated over `K`, `f` is proper, and
by Zariski's main theorem a proper quasi-finite morphism is finite
(`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`). The fibres of `f` are finite since
they are translates of the kernel: the kernel pair `A ×_B A` of `f` is `ker f ×_K A`, through
`(k, a) ↦ (k + a, a)` (Tau Ceti's `TauCeti.isPullback_mul_of_isPullback_one`), so that its second
projection, the base change of the finite morphism `ker f ⟶ Spec K` along `A ⟶ Spec K`, is finite,
and the fibre of `f` through a point `x` of `A` is the image of the finite fibre of this projection
over `x` under the first projection.

That being isogenous is an equivalence relation, as the knowl states, needs its symmetry, from the
factorisation of multiplication by the degree `n` of an isogeny through it and the fact that
multiplication by `n ≠ 0` is an isogeny; neither is available in Tau Ceti.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.isFinite_toSchemeHom_of_surjective`: a surjective
  homomorphism of abelian varieties with finite kernel is finite.
* `TauCeti.AlgebraicGeometry.AbelianVariety.isIsogeny_iff_surjective_and_isFinite_kernel`
  (LMFDB `av.isogeny`): a homomorphism of abelian varieties is an isogeny if and only if it is
  surjective with finite kernel.
-/

open CategoryTheory Limits CartesianMonoidalCategory AlgebraicGeometry Scheme Pullback

open scoped MonObj

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] {A B : AbelianVariety K} {f : A ⟶ B}

lemma isFinite_kernel_hom_of_isFinite_pullback
    (hk : IsFinite (pullback.snd (Hom.toSchemeHom f) B.zeroSection)) :
    IsFinite (kernel f.hom.hom).X.hom := by
  rw [← (GroupScheme.isPullback_kernel_left f.hom.hom).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback (Hom.toSchemeHom f) B.zeroSection)]
  infer_instance

variable (f) in
lemma isPullback_kernelPair : IsPullback ((fst (kernel f.hom.hom).X A.toOver ≫
    (kernel.ι f.hom.hom).hom.hom) * snd _ _) (snd _ _) (Hom.toOverHom f) (Hom.toOverHom f) :=
  isPullback_mul_of_isPullback_one _ _ (GroupScheme.isPullback_kernel_hom f.hom.hom)

/-- **A surjective homomorphism of abelian varieties with finite kernel is finite**: if the kernel
`A ×_B Spec K` of a surjective homomorphism `f : A ⟶ B` of abelian varieties over `K` is finite over
`K`, then `f` is a finite morphism of schemes. -/
lemma isFinite_toSchemeHom_of_surjective (hs : Surjective (Hom.toSchemeHom f))
    (hk : IsFinite (pullback.snd (Hom.toSchemeHom f) B.zeroSection)) :
    IsFinite (Hom.toSchemeHom f) := by
  have hN : IsFinite (kernel f.hom.hom).X.hom := isFinite_kernel_hom_of_isFinite_pullback hk
  have hpb : IsPullback ((fst (kernel f.hom.hom).X A.toOver ≫ (kernel.ι f.hom.hom).hom.hom) *
      snd _ _).left (snd (kernel f.hom.hom).X A.toOver).left (Hom.toSchemeHom f)
      (Hom.toSchemeHom f) :=
    (isPullback_kernelPair f).map (Over.forget _)
  have h₁ : IsFinite (snd (kernel f.hom.hom).X A.toOver).left := by
    rw [Over.snd_left]
    infer_instance
  have hp : IsProper (Hom.toSchemeHom f) := by
    have h : IsProper (Hom.toSchemeHom f ≫ B.toOver.hom) := by
      rw [Hom.toSchemeHom_comp_hom]
      infer_instance
    exact IsProper.of_comp _ B.toOver.hom
  have hq : LocallyQuasiFinite (Hom.toSchemeHom f) := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y ↦ ?_
    rcases (Hom.toSchemeHom f).surjective y with ⟨x, rfl⟩
    refine (((snd (kernel f.hom.hom).X A.toOver).left.finite_preimage_singleton x).image
      ((fst (kernel f.hom.hom).X A.toOver ≫ (kernel.ι f.hom.hom).hom.hom) * snd _ _).left).subset
      fun x' hx' ↦ ?_
    rcases exists_preimage_pullback x' x hx' with ⟨w, hw₁, hw₂⟩
    refine ⟨hpb.isoPullback.inv w, ?_, ?_⟩
    · rw [Set.mem_preimage, Set.mem_singleton_iff, ← hw₂, ← hpb.isoPullback_inv_snd]
      rfl
    · rw [← hw₁, ← hpb.isoPullback_inv_fst]
      rfl
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **An isogeny is a surjective homomorphism with finite kernel** (LMFDB `av.isogeny`): a
homomorphism `f : A ⟶ B` of abelian varieties over `K` is an isogeny, a finite and surjective
morphism of schemes, if and only if it is surjective and its kernel `A ×_B Spec K` is finite over
`K`. -/
lemma isIsogeny_iff_surjective_and_isFinite_kernel : IsIsogeny f ↔ Surjective (Hom.toSchemeHom f) ∧
    IsFinite (pullback.snd (Hom.toSchemeHom f) B.zeroSection) :=
  ⟨fun hf ↦ ⟨hf.surjective, hf.isFinite_pullback_snd_zeroSection⟩, fun h ↦
    (isIsogeny_iff f).mpr ⟨isFinite_toSchemeHom_of_surjective h.1 h.2, h.1⟩⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
