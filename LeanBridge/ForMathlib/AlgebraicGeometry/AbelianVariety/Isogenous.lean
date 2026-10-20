import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny

/-!
# Isogenous abelian varieties

An isogeny of abelian varieties (LMFDB `av.isogeny`) is Tau Ceti's
`TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny`: a homomorphism whose underlying morphism of
schemes is finite and surjective. The LMFDB asks instead for a surjective homomorphism with finite
kernel, which is equivalent for a homomorphism of abelian varieties. Only one half of this
equivalence is proved here: the kernel of an isogeny in Tau Ceti's sense is finite.

Two abelian varieties are isogenous if there is an isogeny from one to the other. Being isogenous
is reflexive and transitive, it only depends on the isomorphism classes of the two abelian
varieties, and it is preserved by extension of the base field. Its symmetry, which makes it the
equivalence relation whose classes are the isogeny classes of LMFDB `av.isogeny_class`, needs the
quasi-inverse of an isogeny of degree `n` up to multiplication by `n`, which Tau Ceti does not have
yet.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenous` (LMFDB `av.isogeny`).

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny.isFinite_pullback_snd_zeroSection`: the
  kernel of an isogeny is finite.
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenous.refl` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenous.trans`: being isogenous is reflexive and
  transitive.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] {A B C : AbelianVariety K} {f : A ⟶ B} (hf : IsIsogeny f)

include hf in
/-- The kernel `A ×_B Spec K` of an isogeny `f : A ⟶ B`, its fibre over the zero section of `B`, is
finite over `K`: an isogeny is a surjective homomorphism with finite kernel. -/
lemma IsIsogeny.isFinite_pullback_snd_zeroSection :
    IsFinite (pullback.snd (Hom.toSchemeHom f) B.zeroSection) :=
  have : IsFinite (Hom.toSchemeHom f) := hf.isFinite
  inferInstance

variable (A B) in
/-- Two abelian varieties `A` and `B` over `K` are **isogenous** (LMFDB `av.isogeny`) if there is
an isogeny `A ⟶ B`, that is a homomorphism whose underlying morphism of schemes is finite and
surjective. -/
def IsIsogenous : Prop :=
  ∃ f : A ⟶ B, IsIsogeny f

include hf in
lemma IsIsogeny.isIsogenous : IsIsogenous A B :=
  ⟨f, hf⟩

variable (A) in
/-- Every abelian variety is isogenous to itself. -/
lemma IsIsogenous.refl : IsIsogenous A A :=
  (isIsogeny_id A).isIsogenous

/-- Being isogenous is transitive. -/
lemma IsIsogenous.trans (hAB : IsIsogenous A B) (hBC : IsIsogenous B C) : IsIsogenous A C :=
  hAB.elim fun _ hf ↦ hBC.elim fun _ hg ↦ (hf.comp hg).isIsogenous

lemma IsIsogenous.of_iso (e : A ≅ B) : IsIsogenous A B :=
  (isIsogeny_of_isIso e.hom).isIsogenous

lemma isIsogenous_congr {A' B' : AbelianVariety K} (eA : A ≅ A') (eB : B ≅ B') :
    IsIsogenous A B ↔ IsIsogenous A' B' :=
  ⟨fun h ↦ ((IsIsogenous.of_iso eA.symm).trans h).trans (.of_iso eB),
    fun h ↦ ((IsIsogenous.of_iso eA).trans h).trans (.of_iso eB.symm)⟩

lemma IsIsogenous.baseChange (h : IsIsogenous A B) (L : Type u) [Field L] [Algebra K L] :
    IsIsogenous (A.baseChange L) (B.baseChange L) :=
  h.elim fun _ hf ↦ (hf.baseChange L).isIsogenous

end TauCeti.AlgebraicGeometry.AbelianVariety
