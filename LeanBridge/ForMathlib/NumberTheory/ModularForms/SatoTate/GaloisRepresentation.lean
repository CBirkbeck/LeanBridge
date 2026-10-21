import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.RingTheory.Frobenius
import LeanBridge.ForMathlib.NumberTheory.Artin.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# The Galois representation of a newform of weight one

Deligne and Serre attached to every newform `f` of weight one, level `N` and character `χ` a
Galois representation `ρ : Gal(ℚ̄/ℚ) → GL₂(ℂ)`: a continuous representation for the discrete
topology on `GL₂(ℂ)` (an Artin representation), unramified at the primes `p ∤ N`, at which the
Frobenius elements have characteristic polynomial `X² - a_p X + χ(p)`. By the Chebotarev density
theorem and the Brauer–Nesbitt theorem these properties determine `ρ` up to isomorphism.

The existence of `ρ` (the Deligne–Serre theorem), its uniqueness, the identification of its
Artin conductor with `N` and the converse construction of newforms from odd irreducible
two-dimensional Artin representations are out of reach. Following the LMFDB, which defines the
Artin and projective fields and images of `f` in terms of `ρ`, the representation is taken here
as given: `HeckeRing.GL2.Newform.GaloisRep f` is the structure of a representation with the
properties above, and the fields and images are defined relative to it. Nothing here depends on
the choice of `ρ` beyond its kernel and image, which are determined up to conjugacy.

The Artin image is finite, of order the degree of the Artin field, and the same holds for the
projective image and field (`HeckeRing.GL2.Newform.GaloisRep.finrank_artinField`,
`HeckeRing.GL2.Newform.GaloisRep.finrank_projectiveField`). The classification of the finite
subgroups of `PGL₂(ℂ)`, which says that the projective image has one of the four types of
`HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType`, is not formalised.

## Main definitions

* `HeckeRing.GL2.Newform.GaloisRep` (LMFDB `cmf.galois_representation`): a Galois representation
  attached to a newform of weight one.
* `HeckeRing.GL2.Newform.GaloisRep.projective` (LMFDB `cmf.galois_representation`): the
  projective Galois representation `Gal(ℚ̄/ℚ) → PGL₂(ℂ)`.
* `HeckeRing.GL2.Newform.GaloisRep.toRepresentation`: the Galois representation as an Artin
  representation of `Gal(ℚ̄/ℚ)` on `ℂ²`.
* `HeckeRing.GL2.Newform.GaloisRep.artinField` (LMFDB `cmf.artin_field`): the Artin field
  `Representation.artinField` of that representation.
* `HeckeRing.GL2.Newform.GaloisRep.artinImage` (LMFDB `cmf.artin_image`).
* `HeckeRing.GL2.Newform.GaloisRep.projectiveField` (LMFDB `cmf.projective_field`).
* `HeckeRing.GL2.Newform.GaloisRep.projectiveImage` (LMFDB `cmf.projective_image`).
* `HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType` (LMFDB `cmf.projective_image`): the
  types `D_n`, `A₄`, `S₄`, `A₅` of the projective images.

## Main results

* `HeckeRing.GL2.Newform.GaloisRep.finrank_artinField`: the Artin field is a number field whose
  degree is the order of the Artin image.
* `HeckeRing.GL2.Newform.GaloisRep.finrank_projectiveField`: the projective field is a number
  field whose degree is the order of the projective image.
* `HeckeRing.GL2.Newform.GaloisRep.projectiveField_le_artinField`: the projective field is a
  subfield of the Artin field.
-/

open IntermediateField Matrix Polynomial UpperHalfPlane

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N]

/-- A **Galois representation** (LMFDB `cmf.galois_representation`) attached to a newform `f` of
weight one, level `N` and character `χ`, as constructed by Deligne and Serre: a representation
`ρ : Gal(ℚ̄/ℚ) → GL₂(ℂ)` that is continuous for the discrete topology on `GL₂(ℂ)` (an Artin
representation), unramified at every prime `p ∤ N`, and such that the arithmetic Frobenius
elements at `p ∤ N` have characteristic polynomial `X² - a_p X + χ(p)`, where `a_p` is the `p`-th
Fourier coefficient of `f`. The primes of `ℚ̄` and the Frobenius elements are those of the
integral closure of `ℤ` in `ℚ̄`. The existence of such a representation is the Deligne–Serre
theorem, not formalised here. -/
structure GaloisRep (f : Newform N 1) where
  /-- The representation `ρ : Gal(ℚ̄/ℚ) → GL₂(ℂ)`. -/
  toMonoidHom : Gal(AlgebraicClosure ℚ/ℚ) →* GL (Fin 2) ℂ
  /-- `ρ` is continuous for the discrete topology on `GL₂(ℂ)`: its kernel is open. -/
  isOpen_ker : IsOpen (toMonoidHom.ker : Set Gal(AlgebraicClosure ℚ/ℚ))
  /-- `ρ` is unramified at the primes `p ∤ N`: the inertia group of every prime of `ℚ̄` above `p`
  lies in its kernel. -/
  inertia_le_ker (p : ℕ) (hp : p.Prime) (hpN : ¬p ∣ N)
    (Q : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) (hQ : Q.IsPrime)
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) : Q.inertia Gal(AlgebraicClosure ℚ/ℚ) ≤ toMonoidHom.ker
  /-- At a prime `p ∤ N`, every arithmetic Frobenius element at a prime of `ℚ̄` above `p` acts with
  characteristic polynomial `X² - a_p X + χ(p)`. -/
  charpoly_frob (p : ℕ) (hp : p.Prime) (hpN : ¬p ∣ N)
    (Q : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) (hQ : Q.IsPrime)
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) (σ : Gal(AlgebraicClosure ℚ/ℚ))
    (hσ : IsArithFrobAt ℤ σ Q) : (toMonoidHom σ : Matrix (Fin 2) (Fin 2) ℂ).charpoly = X ^ 2 - C
    ((qExpansion 1 f.toCuspForm).coeff p) * X + C (f.dirichletLift p)

namespace GaloisRep

variable {f : Newform N 1} (ρ : GaloisRep f)

/-- The Galois representation of a weight-one newform as a representation of `Gal(ℚ̄/ℚ)` on `ℂ²`,
through the identification of `GL₂(ℂ)` with the automorphisms of `ℂ²`. -/
noncomputable def toRepresentation : Representation ℂ Gal(AlgebraicClosure ℚ/ℚ) (Fin 2 → ℂ) :=
  (Units.coeHom _).comp <| GeneralLinearGroup.toLin.toMonoidHom.comp ρ.toMonoidHom

lemma ker_toRepresentation : ρ.toRepresentation.ker = ρ.toMonoidHom.ker :=
  Subgroup.ext fun _ ↦ (map_eq_one_iff _ toLinAlgEquiv'.injective).trans Units.val_eq_one

lemma isArtin_toRepresentation : ρ.toRepresentation.IsArtin :=
  ⟨inferInstance, ρ.ker_toRepresentation ▸ ρ.isOpen_ker⟩

/-- The **projective Galois representation** (LMFDB `cmf.galois_representation`)
`ρ̄ : Gal(ℚ̄/ℚ) → PGL₂(ℂ)` of a weight-one newform: the composite of its Galois representation
with the quotient map `GL₂(ℂ) → PGL₂(ℂ)`, with `PGL₂(ℂ)` the quotient of `GL₂(ℂ)` by its centre,
the scalar matrices. -/
noncomputable def projective :
    Gal(AlgebraicClosure ℚ/ℚ) →* GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ) :=
  (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) ℂ))).comp ρ.toMonoidHom

/-- The **Artin field** (LMFDB `cmf.artin_field`) of a weight-one newform: the subfield of `ℚ̄`
fixed by the kernel of its Galois representation. It is a number field, of degree the order of
the Artin image (`finrank_artinField`). -/
noncomputable def artinField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ρ.toRepresentation.artinField

/-- The **Artin image** (LMFDB `cmf.artin_image`) of a weight-one newform: the image of its Galois
representation in `GL₂(ℂ)`. It is finite, of order the degree of the Artin field
(`finrank_artinField`). -/
noncomputable def artinImage : Subgroup (GL (Fin 2) ℂ) :=
  ρ.toMonoidHom.range

/-- The **projective field** (LMFDB `cmf.projective_field`) of a weight-one newform: the subfield
of `ℚ̄` fixed by the kernel of its projective Galois representation. It is a number field, of
degree the order of the projective image (`finrank_projectiveField`). -/
noncomputable def projectiveField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  fixedField ρ.projective.ker

/-- The **projective image** (LMFDB `cmf.projective_image`) of a weight-one newform: the image of
its projective Galois representation in `PGL₂(ℂ)`. It is finite, of order the degree of the
projective field (`finrank_projectiveField`). -/
noncomputable def projectiveImage : Subgroup (GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ)) :=
  ρ.projective.range

/-- The **types** (LMFDB `cmf.projective_image`) of the finite subgroups of `PGL₂(ℂ)`: the
dihedral groups `D_n`, `n ≥ 2`, of order `2n` (with `D₂` the Klein four-group), and the
tetrahedral, octahedral and icosahedral groups `A₄`, `S₄` and `A₅`. -/
inductive ProjectiveImageType
  /-- The dihedral type `D_n`. -/
  | dihedral (n : ℕ)
  /-- The tetrahedral type `A₄`. -/
  | tetrahedral
  /-- The octahedral type `S₄`. -/
  | octahedral
  /-- The icosahedral type `A₅`. -/
  | icosahedral

/-- A subgroup of `PGL₂(ℂ)` **has type** `t` (LMFDB `cmf.projective_image`) if it is isomorphic to
the dihedral group `D_n` of order `2n` for some `n ≥ 2`, to `A₄`, to `S₄` or to `A₅`, as `t`
says. -/
def ProjectiveImageType.IsTypeOf :
    ProjectiveImageType → Subgroup (GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ)) → Prop
  | .dihedral n, H => 2 ≤ n ∧ Nonempty (H ≃* DihedralGroup n)
  | .tetrahedral, H => Nonempty (H ≃* alternatingGroup (Fin 4))
  | .octahedral, H => Nonempty (H ≃* Equiv.Perm (Fin 4))
  | .icosahedral, H => Nonempty (H ≃* alternatingGroup (Fin 5))

lemma artinField_eq_fixedField : ρ.artinField = fixedField ρ.toMonoidHom.ker :=
  congrArg fixedField ρ.ker_toRepresentation

lemma ker_le_ker_projective : ρ.toMonoidHom.ker ≤ ρ.projective.ker :=
  ρ.toMonoidHom.ker_le_comap (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) ℂ))).ker

lemma isOpen_ker_projective : IsOpen (ρ.projective.ker : Set Gal(AlgebraicClosure ℚ/ℚ)) :=
  Subgroup.isOpen_mono ρ.ker_le_ker_projective ρ.isOpen_ker

instance : FiniteDimensional ℚ ρ.artinField :=
  ρ.isArtin_toRepresentation.finiteDimensional

instance : IsGalois ℚ ρ.artinField :=
  ρ.isArtin_toRepresentation.isGalois

instance : FiniteDimensional ℚ ρ.projectiveField :=
  ρ.projective.finiteDimensional_fixedField_ker ρ.isOpen_ker_projective

/-- **The degree of the Artin field is the order of the Artin image**: the Artin field is a finite
Galois extension of `ℚ`, with Galois group the Artin image. -/
lemma finrank_artinField : Module.finrank ℚ ρ.artinField = Nat.card ρ.artinImage :=
  ρ.artinField_eq_fixedField ▸ ρ.toMonoidHom.finrank_fixedField_ker ρ.isOpen_ker

/-- **The degree of the projective field is the order of the projective image.** -/
lemma finrank_projectiveField : Module.finrank ℚ ρ.projectiveField = Nat.card ρ.projectiveImage :=
  ρ.projective.finrank_fixedField_ker ρ.isOpen_ker_projective

instance : Finite ρ.artinImage :=
  Nat.finite_of_card_ne_zero (ρ.finrank_artinField ▸ Module.finrank_pos.ne')

instance : Finite ρ.projectiveImage :=
  Nat.finite_of_card_ne_zero (ρ.finrank_projectiveField ▸ Module.finrank_pos.ne')

/-- **The projective field is a subfield of the Artin field**, the kernel of `ρ` being contained in
that of `ρ̄`. -/
lemma projectiveField_le_artinField : ρ.projectiveField ≤ ρ.artinField :=
  ρ.artinField_eq_fixedField ▸ fixedField_antitone ρ.ker_le_ker_projective

end GaloisRep

end HeckeRing.GL2.Newform
