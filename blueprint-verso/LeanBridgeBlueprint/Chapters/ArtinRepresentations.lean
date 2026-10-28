import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Artin representations" =>

This chapter lists the LMFDB definitions relating to *Artin representations*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "artin.determinant" (lean := "LinearMap.det, Representation.IsArtin")
*Determinant of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.determinant))

Given an {bpref "artin"}[Artin representation] $`\rho:\Gal(\overline{\Q}/\Q)\to\GL(V)`, where $`V` is a finite dimensional vector space over $`\C`, we can compose with the $`\det:\GL(V)\to \C^\times` to get a one-dimensional Artin representation. This one-dimensional representation is called the *determinant* of $`\rho`.

Depends on: {uses "artin"}[]
:::

:::definition "artin.dimension" (lean := "Module.finrank, Representation.IsArtin")
*Dimension of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.dimension))

The *dimension* of an {bpref "artin"}[Artin representation]
$`\rho:\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to\mathrm{GL}(V)` is the dimension
of the associated vector space $`V`.

Depends on: {uses "artin"}[]
:::

:::definition "artin.frobenius_schur_indicator" (lean := "FDRep.frobeniusSchurIndicator, TauCeti.Representation.frobeniusSchurIndicator")
*Frobenius-Schur indicator of a representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.frobenius_schur_indicator))

If $`G` is a finite {bpref "group"}[group] and $`\chi` is the {bpref "group.representation.character"}[character] of an irreducible complex representation of $`G`, then its *Frobenius-Schur indicator* is given by

$$`\frac{1}{|G|}\sum_{g\in G} \chi(g^2).`

It is $`0`, $`1`, or $`-1` depending on whether the {bpref "group.representation.type"}[type] of the representation is complex type, real, or quaternionic (symplectic) respectively.

Depends on: {uses "group"}[] {uses "group.representation.character"}[] {uses "group.representation.type"}[]
:::

:::definition "artin.galois_orbit"
*Galois orbit of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.galois_orbit))

The {bpref "group.galois.absolute"}[absolute Galois group] $`\Gal(\overline{\Q}/\Q)` acts on the set of {bpref "artin"}[Artin representations] for an extension by pre-composition, so we consider two representations to be Galois conjugate if they differ by such an automorphism.  The action, for a given representation, in fact factors through a finite degree abelian extension.

The *Galois orbit* of a representation is its orbit under this action.

Depends on: {uses "artin"}[] {uses "group.galois.absolute"}[]
:::

:::definition "artin.gg_quotient" (lean := "MonoidHom.range, Representation.artinField, MonoidHom.finrank_fixedField_ker, InfiniteGalois.normalAutEquivQuotient")
*Image of the representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.gg_quotient))

An {bpref "artin"}[Artin representation] $`\rho:\textrm{Gal}(\overline{\Q}/\Q)\to \GL(V)` factors through the Galois group of a finite extension of $`\Q`. Thus its image is a finite group $`G \subset \GL(V)` which is canonically isomorphic to the Galois group of a finite extension $`K/\Q` where $`K` is the fixed field of $`\ker(\rho)` and is called the {bpref "artin.number_field"}[Artin field] of $`\rho`. We sometimes say that $`\Gal(K/\Q)` is the *image of the Artin representation* $`\rho`.

Depends on: {uses "artin"}[] {uses "artin.number_field"}[]
:::

:::definition "artin.permutation_container" (lean := "Representation.Contains, Representation.minPermutationDegree, Representation.contains_ofMulAction_quotient_iff, Representation.contains_ofMulAction_quotient_bot, Representation.ofMulAction")
*Containing permutation representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.permutation_container))

If $`\rho:G\to \GL_n(\C)` is a representation of a finite group $`G`, then $`\rho` is equivalent to a direct sum of irreducible representations.  We say that $`\rho` *contains* each of these representations.

Given an irreducible representation, we can then ask which permutation representations contain it.  There is at least one because the regular representation of $`G` contains all irreducible representations of $`G`.

To determine the smallest permutation representation, we pick one of smallest degree.  If the degree is small enough (less than 48 and not equal to 32), we pick one with the smallest T-number.  Otherwise we give just the degree.
:::

:::definition "artin.projective_field" (lean := "IntermediateField.fixedField, Matrix.ProjGenLinGroup.mk, MonoidHom.ker, MonoidHom.finrank_fixedField_ker")
*Projective Artin field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.projective_field))

Given a {bpref "artin.projective_image"}[projective Artin representation] $`\rho:\Gal(\overline{\Q}/\Q)\to \PGL_n(\C)`, the fixed field of the kernel of $`\rho` is the *projective Artin field* of the representation.

Depends on: {uses "artin.projective_image"}[]
:::

:::definition "artin.projective_image" (lean := "Matrix.ProjGenLinGroup, Matrix.ProjGenLinGroup.mk, MonoidHom.range, Representation.IsArtin")
*Projective image of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.projective_image))

Composing an {bpref "artin"}[Artin representation] $`\Gal(\overline{\Q}/\Q)\to\GL_n(\C)` with the natural projection $`\GL_n(\C)\to\PGL_n(\C)` gives a continuous homomorphism $`\rho:\Gal(\overline{\Q}/\Q)\to\PGL_n(\C)` with finite image.

The image of $`\rho` is the *projective image* of the Artin representation.

Depends on: {uses "artin"}[]
:::

:::definition "artin.projective_stem_field" (lean := "IsNormalClosure, IntermediateField.fixedField, Matrix.ProjGenLinGroup.mk")
*Projective stem field of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.projective_stem_field))

An *projective stem field* is a {bpref "nf.stem_field"}[stem field] for the {bpref "artin.projective_field"}[projective field] of an {bpref "artin"}[Artin representation].

Depends on: {uses "artin"}[] {uses "artin.projective_field"}[] {uses "nf.stem_field"}[]
:::

:::definition "artin.root_number"
*Root number of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.root_number))

The *root number* of an {bpref "artin"}[Artin representation] $`\rho`,
also called the *sign*, is the constant $`W(\rho)` appearing in the
{bpref "lfunction.functional_equation"}[functional equation]
of the associated L-function, i.e. the complex number $`W(\rho)` of absolute value $`1` such that $`\Lambda(s,\rho)=W(\rho)\Lambda(1-s,\overline{\rho})`.  It can be expressed as a product of local root numbers.

Depends on: {uses "artin"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "artin.stem_field" (lean := "IsNormalClosure, Representation.artinField")
*Artin stem field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.stem_field))

An *Artin stem field* is a {bpref "nf.stem_field"}[stem field] for the {bpref "artin.number_field"}[Artin field] of an {bpref "artin"}[Artin representation].

Depends on: {uses "artin"}[] {uses "artin.number_field"}[] {uses "nf.stem_field"}[]
:::
