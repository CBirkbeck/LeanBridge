import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Mod-ℓ Galois representations" =>
%%%
file := "Mod-l-Galois-representations"
%%%

This chapter lists the LMFDB definitions relating to *mod-ℓ Galois representations*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "modlgal" (lean := "MonoidHom.IsModEllGaloisRep, MonoidHom.splittingField, MonoidHom.galoisFactor, Field.absoluteGaloisGroup")
*Mod-$`l` Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal))

A *mod-$`\ell` Galois representation* is a representation of the {bpref "group.galois.absolute"}[abolute Galois group] $`\Gal_K` of a {bpref "nf"}[number field] $`K` with values in the $`\F_{\ell}`-points of an algebraic group.

Depends on: {uses "group.galois.absolute"}[] {uses "nf"}[]
:::

:::definition "modlgal.abelian" (lean := "MonoidHom.range, IsMulCommutative")
*Abelian.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.abelian))

A {bpref "modlgal"}[mod-$`\ell` Galois representation] with {bpref "modlgal.codomain"}[codomain] $`G(\F_{\ell})` is *abelian*
 if its {bpref "modlgal.image"}[image] is an {bpref "group.abelian"}[abelian] subgroup of the {bpref "modlgal.codomain"}[codomain] $`G(\F_{\ell})`.  Otherwise the representation is *nonabelian*.

Depends on: {uses "group.abelian"}[] {uses "modlgal"}[] {uses "modlgal.codomain"}[] {uses "modlgal.image"}[]
:::

:::definition "modlgal.absolutely_irreducible" (lean := "Representation.baseChange")
*Absolutely irreducible.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.absolutely_irreducible))

A {bpref "modlgal"}[mod-$`\ell` Galois representation] with {bpref "modlgal.codomain"}[codomain] $`G(\F_{\ell})` is *absolutely irreducible*
 if it is {bpref "group.representation.irrep"}[irreducible]  after extending the codoman to $`G(\overline{\F_{\ell}})`.

Depends on: {uses "group.representation.irrep"}[] {uses "modlgal"}[] {uses "modlgal.codomain"}[]
:::

:::definition "modlgal.base_ring_characteristic" (lean := "ringChar, CharP")
*Base ring characteristic.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.base_ring_characteristic))

The *base ring characteristic* of a {bpref "modlgal"}[mod-$`\ell` Galois representation] is the {bpref "ring.characteristic"}[characteristic] of the base ring of its {bpref "modlgal.codomain"}[codomain].

Depends on: {uses "modlgal"}[] {uses "modlgal.codomain"}[] {uses "ring.characteristic"}[]
:::

:::definition "modlgal.characteristic" (lean := "ringChar, CharP, ZMod.charP")
*Characteristic of a mod-$`l` Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.characteristic))

The *characteristic* of a {bpref "modlgal"}[mod-$`\ell` Galois representation] is the characteristic of the base ring of its {bpref "modlgal.codomain"}[codomain], which is a {bpref "ring"}[ring] of characteristic $`\ell`.

Depends on: {uses "modlgal"}[] {uses "modlgal.codomain"}[] {uses "ring"}[]
:::

:::definition "modlgal.codomain" (lean := "Matrix.GeneralLinearGroup")
*Codomain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.codomain))

The *codomain* of a {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho:\Gal_K \to G(\F_{\ell})`, with values in the $`\F_{\ell}`-points of an algebraic group $`G`, is the finite group $`G(\F_{\ell})`.

Depends on: {uses "modlgal"}[]
:::

:::definition "modlgal.conductor" (lean := "Representation.modEllConductor, Representation.conductorExponent, Representation.conductorExponentAt, Representation.conductorExponent_eq, Representation.conductorExponent_eq_zero")
*Conductor.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.conductor))

The *conductor* of an {bpref "modlgal"}[mod-$`\ell` Galois representation] is a positive integer coprime to $`\ell` that measures ramification.  It can be expressed as a product of local conductors.

Let $`K/\Q` be a {bpref "nf.is_galois"}[Galois] extension and $`\rho:\Gal(K/\Q)\to\GL(V)` a mod-$`\ell` Galois representation.  Then the conductor of $`\rho` is
$`\prod_{p\nmid \ell} p^{f(\rho,p)}`
for non-negative integers $`f(\rho,p)`, where the product is taken over prime numbers $`p\neq \ell`.

To define the exponents $`f(\rho,p)`, fix a {bpref "nf.prime"}[prime] $`\mathfrak{p}` of $`K` above $`p` and consider the corresponding extension of {bpref "lf.padic_field"}[local fields] $`K_{\mathfrak{p}}/\Q_p` with {bpref "gg.galois_group"}[Galois group] $`G`.  Then $`G` has a filtration of higher ramification groups in lower numbering $`G_i`, as defined in Chapter IV of Serre's _Local Fields_ .  In particular, $`G_{-1}=G`, $`G_0` is the {bpref "lf.inertia_group"}[inertia group] of $`K_{\mathfrak{p}}/\Q_p`, and $`G_1` is the {bpref "lf.wild_inertia_group"}[wild inertia group], which is a finite $`p`-group.

Let $`g_i = |G_i|`.  Then

$$`f(\rho, p) = \sum_{i\geq 0} \frac{g_i}{g_0} (\dim(V) - \dim(V^{G_i}))`

where $`V^{G_i}` is the subspace of $`V` fixed by $`G_i`.

Note that if $`p` is {bpref "artin.unramified_primes"}[unramified] in $`K`, then $`f(\rho,p)=0` and conversely, if $`\rho` is faithful and $`p` is ramified in $`K`, then $`f(\rho,p)>0`.

Depends on: {uses "artin.unramified_primes"}[] {uses "gg.galois_group"}[] {uses "lf.inertia_group"}[] {uses "lf.padic_field"}[] {uses "lf.wild_inertia_group"}[] {uses "modlgal"}[] {uses "nf.is_galois"}[] {uses "nf.prime"}[]
:::

:::definition "modlgal.det_surjective" (lean := "Matrix.GeneralLinearGroup.det, MonoidHom.range_eq_top, MonoidHom.range")
*Determinant is surjective.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.det_surjective))

For a {bpref "modlgal"}[mod-$`\ell` Galois representation], its determinant is {bpref "modlgal.surjective"}[surjective] is the image of its determinant map is $`\GL_1(\F_{\ell})`.

Depends on: {uses "modlgal"}[] {uses "modlgal.surjective"}[]
:::

:::definition "modlgal.determinant" (lean := "Matrix.GeneralLinearGroup.det")
*Determinant character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.determinant))

To each {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho:\Gal_K \to G(\F_{\ell})`, with values in the $`\F_{\ell}`-points of an algebraic group $`G`, is associated a *determinant character* $`\det\rho:\Gal_K \to \F_{\ell}^*`, defined by composing $`\rho` with the determinant map $`G(\F_{\ell}) \to \F_{\ell}^*`.

The determinant character is a $`1`-dimensional {bpref "modlgal"}[mod-$`\ell` Galois representation].  If $`\rho` has {bpref "modlgal.dimension"}[dimension] $`1`, the determinant character is the same as the original representation.

Depends on: {uses "modlgal"}[] {uses "modlgal.dimension"}[]
:::

:::definition "modlgal.determinant_index" (lean := "Subgroup.index, MonoidHom.range, Matrix.GeneralLinearGroup.det")
*Determinant index.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.determinant_index))

Given a {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho:\Gal_K\to G(\F_{\ell})`, the *determinant index* is the index of $`\det(\rho(\Gal_K))` in $`\F_{\ell}^\times`.

Depends on: {uses "modlgal"}[]
:::

:::definition "modlgal.dimension" (lean := "Module.finrank")
*Dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.dimension))

The *dimension* of a  {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho: \Gal_K\to G(\F_{\ell})` is the dimension of the $`\F_{\ell}`-vector space on which $`G(\F_{\ell})` acts.

$`1`-dimensional {bpref "modlgal"}[mod-$`\ell` Galois representations] are also called *Galois characters*.

Depends on: {uses "modlgal"}[]
:::

:::definition "modlgal.dual_pair_of_algebras" (lean := "LinearMap.IsDualPairOfAlgebras, LinearMap.leftComul, LinearMap.rightComul, LinearMap.tensorPairing, LinearMap.tensorPairing_leftComul")
*Dual pair of algebras.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.dual_pair_of_algebras))

Let $`R` be a ring. A dual pair of algebras over $`R` is a triple $`(A, B, \phi)`, where $`A` and $`B` are finite locally free $`R`-algebras and where $`\phi: A \times B \to R` is a perfect $`R`-bilinear map such that the following identities hold for all $`a, a' \in A` and $`b, b' \in B`:

1. $`\phi(1_A,1_B)=1`;
2. $`\phi(aa',1_B) = \phi(a,1_B)\phi(a',1_B)`;
3. $`\phi(1_A, bb') = \phi(1_A, b)\phi(1_A, b')`;
4. $`Φ^{(2)}(\mu_1^\phi(a)\mu_1^\phi(a'), b \otimes b') = \phi(aa', bb')= Φ^{( 2 )}( a \otimes a' , \mu_2^\phi( b )\mu_1^\phi( b') )`; here $`Φ^{( 2 )} : (A \otimes_R A ) \times ( B \otimes_R B ) \to R` is the $`R`-bilinear map sending $`(a \otimes a', b \otimes b')` to $`\phi(a, b)\phi(a', b')`, the map $`\mu_1^\phi: A \to A \otimes_R A` is obtained by taking the $`R`-linear dual of the multiplication map $`B \otimes_R B \to B` and applying the isomorphism $`\Hom_{R\text{-mod}}(B,R)\cong A` of $`R`-modules given by $`\phi`, and similarly for $`\mu_2^\phi: B \to B \otimes_R B`.

Dual pairs of algebras and group schemes are related via an (anti)-equivalence of categories. Therefore, all information about a group scheme is encoded in the corresponding dual pair of algebras: see the article  for further details, as well as the associated [SageMath package](https://dual-pairs.readthedocs.io/en/latest/).
:::

:::definition "modlgal.frobenius_charpoly" (lean := "MonoidHom.frobeniusCharpoly, MonoidHom.frobeniusCharpoly_eq, MonoidHom.frobeniusClass, NumberField.artinSymbol")
*Characteristic polynomial of Frobenius.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.frobenius_charpoly))

Let $`\rho:\Gal_K\to G(\F_{\ell})` be a {bpref "modlgal"}[mod-$`\ell` Galois representation].   The *characteristic polynomial of Frobenius* of a {bpref "nf.prime"}[prime] $`\frak{p}` of $`K` at which $`\rho` is {bpref "modlgal.ramified"}[unramified] is the characteristic polynomial of $`\rho(\text{Frob}_{\frak{p}})`.

Note that {bpref "modlgal.ramified"}[unramified] primes $`\frak{p}` of $`K` are, by definition, unramified in the {bpref "modlgal.splitting_field"}[splitting field] $`L/K` of $`\rho`, so the Frobenius automorphism $`\text{Frob}_{\frak{p}}` is well-defined up to conjugacy in $`\Gal(L/K)`, and hence the characteristic polynomial of  $`\rho(\text{Frob}_{\frak{p}})` is well-defined.

Depends on: {uses "modlgal"}[] {uses "modlgal.ramified"}[] {uses "modlgal.splitting_field"}[] {uses "nf.prime"}[]
:::

:::definition "modlgal.frobenius_determinant" (lean := "MonoidHom.frobeniusDet, MonoidHom.frobeniusDet_eq, MonoidHom.frobeniusClass")
*Frobenius determinant.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.frobenius_determinant))

Let $`\rho:\Gal_K\to G(\F_{\ell})` be a {bpref "modlgal"}[mod-$`\ell` Galois representation].   The *Frobenius determinant* of a {bpref "nf.prime"}[prime] $`\frak{p}` of $`K` at which $`\rho` is {bpref "modlgal.ramified"}[unramified] is the determinant of $`\rho(\text{Frob}_{\frak{p}})`.  This is the same as the value of the {bpref "modlgal.determinant"}[determinant character] at $`\text{Frob}_{\frak{p}}`.

Note that {bpref "modlgal.ramified"}[unramified] primes $`\frak{p}` of $`K` are, by definition, unramified in the {bpref "modlgal.splitting_field"}[splitting field] $`L/K` of $`\rho`, so the Frobenius automorphism $`\text{Frob}_{\frak{p}}` is well-defined up to conjugacy in $`\Gal(L/K)`, and hence the determinant of  $`\rho(\text{Frob}_{\frak{p}})` is well-defined.

Depends on: {uses "modlgal"}[] {uses "modlgal.determinant"}[] {uses "modlgal.ramified"}[] {uses "modlgal.splitting_field"}[] {uses "nf.prime"}[]
:::

:::definition "modlgal.frobenius_matrix" (lean := "MonoidHom.IsFrobeniusMatrix, MonoidHom.frobeniusClass, MonoidHom.galoisFactor_restrictNormalHom")
*Frobenius matrix.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.frobenius_matrix))

A *Frobenius matrix* for a {bpref "modlgal"}[mod-$`\ell` Galois representation]  is an element of the conjugacy class of the image of the absolute Frobenius element associated to a particular prime.

Depends on: {uses "modlgal"}[]
:::

:::definition "modlgal.frobenius_order" (lean := "MonoidHom.frobeniusOrder, MonoidHom.frobeniusOrder_eq, MonoidHom.frobeniusClass")
*Frobenius order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.frobenius_order))

Let $`\rho:\Gal_K\to G(\F_{\ell})` be a {bpref "modlgal"}[mod-$`\ell` Galois representation].   The *Frobenius order* of a {bpref "nf.prime"}[prime] $`\frak{p}` of $`K` at which $`\rho` is {bpref "modlgal.ramified"}[unramified] is the {bpref "group.order"}[order] of $`\rho(\text{Frob}_{\frak{p}})` as an element of the finite group $`G(\F_{\ell})`.

Note that {bpref "modlgal.ramified"}[unramified] primes $`\frak{p}` of $`K` are, by definition, unramified in the {bpref "modlgal.splitting_field"}[splitting field] $`L/K` of $`\rho`, so the Frobenius automorphism $`\text{Frob}_{\frak{p}}` is well-defined up to conjugacy in $`\Gal(L/K)`, and hence the order of  $`\rho(\text{Frob}_{\frak{p}})` is well-defined.

Depends on: {uses "group.order"}[] {uses "modlgal"}[] {uses "modlgal.ramified"}[] {uses "modlgal.splitting_field"}[] {uses "nf.prime"}[]
:::

:::definition "modlgal.frobenius_prime" (lean := "Algebra.IsUnramifiedIn, IntermediateField.fixedField, MonoidHom.ker")
*Frobenius prime.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.frobenius_prime))

A *Frobenius prime* or *good prime* for a {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho: \text{Gal}_K \to G(\F_{\ell})` with {bpref "modlgal.splitting_field"}[splitting field] $`L/K` is a {bpref "nf.prime"}[prime] $`\frak{p}` of $`K` which does not divide the characteristic $`\ell` and which is {bpref "modlgal.ramified"}[unramified] in $`L/K`.

Depends on: {uses "modlgal"}[] {uses "modlgal.ramified"}[] {uses "modlgal.splitting_field"}[] {uses "nf.prime"}[]
:::

:::definition "modlgal.frobenius_trace" (lean := "MonoidHom.frobeniusTrace, MonoidHom.frobeniusTrace_eq, MonoidHom.frobeniusClass")
*Frobenius trace.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.frobenius_trace))

Let $`\rho:\Gal_K\to G(\F_{\ell})` be a {bpref "modlgal"}[mod-$`\ell` Galois representation].   The *Frobenius trace* of a {bpref "nf.prime"}[prime] $`\frak{p}` of $`K` at which $`\rho` is {bpref "modlgal.ramified"}[unramified] is the trace of $`\rho(\text{Frob}_{\frak{p}})`.

Note that {bpref "modlgal.ramified"}[unramified] primes $`\frak{p}` of $`K` are, by definition, unramified in the {bpref "modlgal.splitting_field"}[splitting field] $`L/K` of $`\rho`, so the Frobenius automorphism $`\text{Frob}_{\frak{p}}` is well-defined up to conjugacy in $`\Gal(L/K)`, and hence the trace of  $`\rho(\text{Frob}_{\frak{p}})` is well-defined.

Depends on: {uses "modlgal"}[] {uses "modlgal.ramified"}[] {uses "modlgal.splitting_field"}[] {uses "nf.prime"}[]
:::

:::definition "modlgal.generating_primes" (lean := "MonoidHom.IsGeneratingPrimes, MonoidHom.generatingPrimes, MonoidHom.isGeneratingPrimes_generatingPrimes, MonoidHom.IsGeneratingPrimes.eq, MonoidHom.frobeniusImage")
*Generating Frobenius classes.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.generating_primes))

The {bpref "modlgal.image"}[image] of a {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho` is generated by the images under $`\rho` of the Frobenius conjugacy classes associated to a finite set of {bpref "modlgal.ramified"}[unramified] primes of the base field.  We may canonicalize this set by choosing the minimal sequence of increasing unramified primes $`p_1,\ldots,p_n` such that the cardinalities of the subgroups generated by the images of Frobenius conjugacy classes
$$`H_k:=\langle \rho(\mathrm{Frob}_{p_1}).\ldots\rho(\mathrm{Frob}_{p_k})\rangle`
 are strictly increasing for every $`1\le k\le n`.

Depends on: {uses "modlgal"}[] {uses "modlgal.image"}[] {uses "modlgal.ramified"}[]
:::

:::definition "modlgal.image" (lean := "MonoidHom.range")
*Image.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.image))

The *image* of a  {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho: \Gal_K\to G(\F_{\ell})` is the {bpref "group.subgroup"}[subgroup] $`\rho(\Gal_K)` of the {bpref "modlgal.codomain"}[codomain] $`G(\F_{\ell})`.

Depends on: {uses "group.subgroup"}[] {uses "modlgal"}[] {uses "modlgal.codomain"}[]
:::

:::definition "modlgal.image_abstract_group" (lean := "MonoidHom.range, MulEquiv")
*Abstract image of a mod-$`l` representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.image_abstract_group))

For a {bpref "modlgal"}[mod-$`\ell` representation] $`\rho:\Gal_K\to G(\F_{\ell})`, the *abstract image* is the isomorphism type of the {bpref "modlgal.image"}[image]  $`\rho(\Gal_K)` as an abstract group.

Depends on: {uses "modlgal"}[] {uses "modlgal.image"}[]
:::

:::definition "modlgal.image_index" (lean := "Subgroup.index, MonoidHom.range, Subgroup.index_eq_one")
*Index of the image of a mod-$`l` Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.image_index))

The *index* of a {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho:\Gal_K\to G(\F_{\ell})` is the {bpref "group.subgroup"}[subgroup] index $`[G(\F_{\ell}):\rho(\Gal_K)]`.

The index is $`1` if and only if the representation is {bpref "modlgal.surjective"}[surjective].

Depends on: {uses "group.subgroup"}[] {uses "modlgal"}[] {uses "modlgal.surjective"}[]
:::

:::definition "modlgal.image_order" (lean := "Nat.card, MonoidHom.range")
*Order of the image of a mod-$`l` Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.image_order))

The *image order* of a {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho:\Gal_K\to G(\F_{\ell})` is the  order (or cardinality) of the {bpref "modlgal.image"}[image]  $`\rho(\Gal_K)`.

Depends on: {uses "modlgal"}[] {uses "modlgal.image"}[]
:::

:::definition "modlgal.label"
*Labels of mod-$`l` Galois representations.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.label))

The label of a {bpref "modlgal"}[mod-$`\ell` Galois representation] has the form $`\texttt{l.d.N.n}` where

- $`l` is the {bpref "modlgal.characteristic"}[characteristic]

- $`d` is the {bpref "modlgal.dimension"}[dimension]

- $`N` is the {bpref "modlgal.conductor"}[conductor]

- $`n` is an identifier that distinguishes representations of the same dimension, characteristic, and conductor.  When $`d\geq 2`, $`n` is simply an integer.  When $`d=1`, $`n` takes the form $`a`-$`b` where the Dirichlet character a.b is a lift of the one-dimensional representation modulo $`\ell`.

Depends on: {uses "modlgal"}[] {uses "modlgal.characteristic"}[] {uses "modlgal.conductor"}[] {uses "modlgal.dimension"}[]
:::

:::definition "modlgal.min_sib_splitting_field"
*Minimal sibling of splitting field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.min_sib_splitting_field))

The *minimal sibling of the splitting field* of a {bpref "modlgal"}[mod-$`\ell` Galois representation] is the {bpref "nf.minimal_sibling"}[minimal sibling] of its {bpref "modlgal.splitting_field"}[splitting field].

Depends on: {uses "modlgal"}[] {uses "modlgal.splitting_field"}[] {uses "nf.minimal_sibling"}[]
:::

:::definition "modlgal.projective_kernel_polynomial"
*Projective kernel polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.projective_kernel_polynomial))

The *projective kernel polynomial* is the
{bpref "nf.minimal_sibling"}[minimal sibling]  of the
  {bpref "modlgal.splitting_field"}[splitting field]
  of the {bpref "modlgal.projective_representation"}[projective representation]
of a {bpref "modlgal"}[mod-$`\ell` Galois representation].

Depends on: {uses "modlgal"}[] {uses "modlgal.projective_representation"}[] {uses "modlgal.splitting_field"}[] {uses "nf.minimal_sibling"}[]
:::

:::definition "modlgal.projective_representation" (lean := "Matrix.ProjGenLinGroup, Matrix.ProjGenLinGroup.mk, Matrix.GeneralLinearGroup.center_eq_range_scalar")
*Projective representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.projective_representation))

To each {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho:\Gal_K \to G(\F_{\ell})`, with values in the $`\F_{\ell}`-points of an algebraic group $`G`, is associated a *projective representation* $`\mathbb{P}\rho:\Gal_K \to G(\F_{\ell})/\F_{\ell}^*`, defined by composing $`\rho` with the projection $`G(\F_{\ell}) \to G(\F_{\ell})/\F_{\ell}^*`.

In case $`\ell=2`, the projective representation is the same as the original representation.

Depends on: {uses "modlgal"}[]
:::

:::definition "modlgal.ramified" (lean := "Algebra.IsUnramifiedIn, IntermediateField.fixedField, MonoidHom.ker, Ideal.inertia")
*Ramified primes of a mod-$`l` Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.ramified))

If $`\rho\colon\Gal_K\to G(\F_{\ell})` is an {bpref "modlgal"}[mod-$`\ell` Galois representation] with {bpref "modlgal.splitting_field"}[splitting field] $`L`,   then a {bpref "nf.prime"}[prime] $`\frak{p}\nmid\ell` of $`K` is *ramified* if it is {bpref "nf.ramified_primes"}[ramified] in $`L/K`.

Equivalently, a prime is ramified if the inertia subgroup of $`\Gal_K` for a prime above $`\frak{p}` is not contained in the kernel of $`\rho`.

A prime which is not ramified is *unramified*.

Depends on: {uses "modlgal"}[] {uses "modlgal.splitting_field"}[] {uses "nf.prime"}[] {uses "nf.ramified_primes"}[]
:::

:::definition "modlgal.solvable" (lean := "Group.IsSolvable, MonoidHom.range")
*Solvable.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.solvable))

A {bpref "modlgal"}[mod-$`\ell` Galois representation] with {bpref "modlgal.codomain"}[codomain] $`G(\F_{\ell})` is *solvable*
 if its {bpref "modlgal.image"}[image] is a {bpref "group.solvable"}[solvable] subgroup of the {bpref "modlgal.codomain"}[codomain] $`G(\F_{\ell})`.  Otherwise the representation is *nonsolvable*.

Depends on: {uses "group.solvable"}[] {uses "modlgal"}[] {uses "modlgal.codomain"}[] {uses "modlgal.image"}[]
:::

:::definition "modlgal.splitting_field" (lean := "IntermediateField.fixedField, MonoidHom.ker, MonoidHom.isGalois_fixedField_ker, MonoidHom.finrank_fixedField_ker")
*Splitting field of a mod-$`l` Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.splitting_field))

The *splitting field* of a {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho:\Gal_K \to G(\F_{\ell})` is the fixed field of the kernel of $`\rho`.  This is a finite Galois extension $`L/K` with $`\Gal(L/K)` isomorphic to the {bpref "modlgal.image"}[image] of $`\rho`.

Depends on: {uses "modlgal"}[] {uses "modlgal.image"}[]
:::

:::definition "modlgal.surjective" (lean := "MonoidHom.range, MonoidHom.range_eq_top")
*Surjective.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.surjective))

A {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho: \Gal_K\to G(\F_{\ell})` is *surjective* if the {bpref "modlgal.image"}[image] is equal to all of the {bpref "modlgal.codomain"}[codomain]; that is, if $`\rho(\Gal_K)=G(\F_{\ell})`.

Depends on: {uses "modlgal"}[] {uses "modlgal.codomain"}[] {uses "modlgal.image"}[]
:::

:::definition "modlgal.top_slope" (lean := "MonoidHom.topArtinSlope, NumberField.topArtinSlopeAt, NumberField.topArtinSlopeAt_eq, NumberField.galoisClosure_quotient_eq, IsNonarchimedeanLocalField.topArtinSlope")
*Top slope.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modlgal.top_slope))

Given a {bpref "modlgal"}[mod-$`\ell` Galois representation] $`\rho`, let $`K` be its  {bpref "modlgal.splitting_field"}[splitting field].  Then the {bpref "nf.local_algebra"}[local $`\ell`-adic algebra] $`K\otimes\mathbb{\Q}_{\ell}` is isomorphic to a product of {bpref "lf"}[$`\ell`-adic fields].  The *top Artin slope* of the representation is the largest {bpref "lf.slopes"}[Artin slope] among these fields, which equals the {bpref "lf.top_slope"}[top Artin slope] for their compositum.

Note that a top slope of $`0` signifies that the field is unramified at $`\ell`, and a top slope of $`1` indicates that it is ramified, but only tamely.  Otherwise the top slope is the largest {bpref "lf.slopes"}[wild slope].

Depends on: {uses "lf.slopes"}[] {uses "lf.top_slope"}[] {uses "modlgal"}[] {uses "modlgal.splitting_field"}[] {uses "nf.local_algebra"}[]
:::
