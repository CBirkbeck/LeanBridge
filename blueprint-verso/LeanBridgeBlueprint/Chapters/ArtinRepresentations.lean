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

:::definition "artin.dimensionone"
*Dirichlet character associated with a 1-dimensional Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.dimensionone))

A one-dimensional {bpref "artin"}[Artin representation] $`\rho:\Gal(\overline{\Q}/\Q)\to \GL_1(\C)\cong \C^\times`.  Since the image is abelian and every Artin representation factors through the Galois group of a number field, we can view $`\rho` as a map $`\Gal(K/\Q)\to \C^\times` for an {bpref "nf.abelian"}[abelian] number field $`K`.

By the Kronecker-Weber theorem, $`K` is contained in a cyclotomic extension $`\Q(\zeta_n)` for some positive integer $`n`.  Using the canonical isomorphism $`\Gal(\Q(\zeta_n)/\Q)\cong(\Z/n\Z)^\times`, the Artin representation corresponds to a homomorphism $`(\Z/n\Z)^\times\to \C^\times`.

Extending it to $`\Z/n\Z` by defining it to be $`0` off of $`(\Z/n\Z)^\times`, and then viewing it as a function on $`\Z` via the natural map $`\Z\to\Z/n\Z`, we get the corresponding {bpref "character.dirichlet"}[Dirichlet character], whose modulus is the same as that of the one-dimensional Artin representation.

Depends on: {uses "artin"}[] {uses "character.dirichlet"}[] {uses "nf.abelian"}[]
:::

:::definition "artin.frobenius_schur_indicator" (lean := "FDRep.frobeniusSchurIndicator, TauCeti.Representation.frobeniusSchurIndicator")
*Frobenius-Schur indicator of a representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.frobenius_schur_indicator))

If $`G` is a finite {bpref "group"}[group] and $`\chi` is the {bpref "group.representation.character"}[character] of an irreducible complex representation of $`G`, then its *Frobenius-Schur indicator* is given by

$$`\frac{1}{|G|}\sum_{g\in G} \chi(g^2).`

It is $`0`, $`1`, or $`-1` depending on whether the {bpref "group.representation.type"}[type] of the representation is complex type, real, or quaternionic (symplectic) respectively.

Depends on: {uses "group"}[] {uses "group.representation.character"}[] {uses "group.representation.type"}[]
:::

:::definition "artin.galois_orbit" (lean := "Representation.IsGaloisConjugate, Representation.galoisOrbit, Representation.IsGaloisConjugate.symm, Representation.IsGaloisConjugate.trans, Representation.IsGaloisConjugate.isArtin")
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

:::definition "artin.label"
*Label for an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.label))

The label for an {bpref "artin"}[Artin representation] takes the form A.B.C.DcE where

- A is the {bpref "artin.dimension"}[dimension] of the representation;

- B is the {bpref "artin.conductor"}[conductor] of the representation, the format for which is explained below;

- C is the {bpref "artin.permutation_container"}[smallest permutation representation] for which this representation is a factor.  If the degree is small enough, we give the degree <i>d</i> and {bpref "gg.tnumber"}[t-number] <i>j</i> in the form <code>dtj</code>; otherwise we use just the degree <code>d</code>;

- D is an index to distinguish cases where non-Galois conjugate representations have the same dimension, conductor, and smallest permutation representation;

- E is an index for the representation within its {bpref "artin.galois_orbit"}[Galois conjugates].

The conductor is given in factored form with the following encoding.  Underscores (\_) are to be interpreted as multiplication signs and "e" indicates exponentiation.  So, 2e3\_59 converts to $`2^3\cdot 59`.

Depends on: {uses "artin"}[] {uses "artin.conductor"}[] {uses "artin.dimension"}[] {uses "artin.galois_orbit"}[] {uses "artin.permutation_container"}[] {uses "gg.tnumber"}[]
:::

:::definition "artin.lfunction"
*Artin L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.lfunction))

The {bpref "lfunction"}[L-function] associated to an
{bpref "artin"}[Artin representation]
$`\rho:\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to\mathrm{GL}(V)`
is given by an
{bpref "lfunction.euler_product"}[Euler product] of the form
$`\prod_p\det(I-\rho(\mathrm{Frob}(p))p^{-s})^{-1}`, where $`\mathrm{Frob}(p)`
denotes the {bpref "gg.conjugacy_classes"}[conjugacy class] of Frobenius elements above $`p`.  When $`\rho` is {bpref "artin.ramified_primes"}[ramified]
at $`p`, $`\rho(\mathrm{Frob}(p))` should be interpreted as acting on the
invariant subspace $`V^{I_p}` of the {bpref "lf.inertia_group"}[inertia group] at $`p`.

Depends on: {uses "artin"}[] {uses "artin.ramified_primes"}[] {uses "gg.conjugacy_classes"}[] {uses "lf.inertia_group"}[] {uses "lfunction"}[] {uses "lfunction.euler_product"}[]
:::

:::definition "artin.permutation_container" (lean := "Representation.Contains, Representation.minPermutationDegree, Representation.contains_ofMulAction_quotient_iff, Representation.contains_ofMulAction_quotient_bot, Representation.ofMulAction")
*Containing permutation representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.permutation_container))

If $`\rho:G\to \GL_n(\C)` is a representation of a finite group $`G`, then $`\rho` is equivalent to a direct sum of irreducible representations.  We say that $`\rho` *contains* each of these representations.

Given an irreducible representation, we can then ask which permutation representations contain it.  There is at least one because the regular representation of $`G` contains all irreducible representations of $`G`.

To determine the smallest permutation representation, we pick one of smallest degree.  If the degree is small enough (less than 48 and not equal to 32), we pick one with the smallest {bpref "gg.tnumber"}[T-number].  Otherwise we give just the degree.
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

:::definition "artin.projective_image_type" (lean := "HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType, HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType.IsTypeOf, Matrix.ProjGenLinGroup")
*Projective image type.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.projective_image_type))

The {bpref "artin.projective_image"}[projective image] of an {bpref "artin"}[Artin representation] is a finite {bpref "group.subgroup"}[subgroup] of $`\PGL_n(\C)`.  Possible subgroups have been classified for small $`n`.  The case which has garnered the most interest is when $`n=2`, in which case the image is isomorphic to either $`A_4`, $`S_4`, $`A_5`, or $`D_n` for some $`n\geq 2` (where $`D_2` is the Klein group).

Depends on: {uses "artin"}[] {uses "artin.projective_image"}[] {uses "group.subgroup"}[]
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
of the associated {bpref "artin.lfunction"}[L-function], i.e. the complex number $`W(\rho)` of absolute value $`1` such that $`\Lambda(s,\rho)=W(\rho)\Lambda(1-s,\overline{\rho})`.  It can be expressed as a product of local root numbers.

Depends on: {uses "artin"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "artin.stem_field" (lean := "IsNormalClosure, Representation.artinField")
*Artin stem field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.stem_field))

An *Artin stem field* is a {bpref "nf.stem_field"}[stem field] for the {bpref "artin.number_field"}[Artin field] of an {bpref "artin"}[Artin representation].

Depends on: {uses "artin"}[] {uses "artin.number_field"}[] {uses "nf.stem_field"}[]
:::

:::definition "artin.trace_of_complex_conj" (lean := "Representation.character, Field.absoluteGaloisGroup.complexConjugation, Field.absoluteGaloisGroup.exists_complexConjugation_eq_conj, Representation.char_conj")
*Trace of complex conjugation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.trace_of_complex_conj))

For an {bpref "artin"}[Artin Representation], complex conjugation gives a well-defined conjugacy class $`c` in the Galois group, so it has a well-defined character value.

Depends on: {uses "artin"}[]
:::
