import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Miscellaneous" =>
%%%
tag := "varieties-miscellaneous"
file := "Varieties-miscellaneous"
%%%

This section lists the LMFDB definitions in the category `av`, apart from those in `av.fq`. Each definition links back to its LMFDB knowl.

:::definition "av.aut_group" (lean := "CategoryTheory.Aut, AlgebraicGeometry.Scheme.IsVarietyOver")
*Automorphism group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.aut_group))

An *automorphism* of an {bpref "ag.variety"}[algebraic variety] is an isomorphism from the variety to itself.
The set of automorphisms of an {bpref "ag.variety"}[algebraic variety] $`X` form a group $`\mathrm{Aut}(X)` under composition; this is the *automorphism group* of the {bpref "ag.variety"}[algebraic variety].

Depends on: {uses "ag.variety"}[]
:::

:::definition "av.decomposition" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenyDecomposition, TauCeti.AlgebraicGeometry.AbelianVariety.listProd, TauCeti.AlgebraicGeometry.AbelianVariety.isIsogenyDecomposition_trivial_nil, TauCeti.AlgebraicGeometry.AbelianVariety.IsSimple, TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenous")
*Decomposition into isogeny factors.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.decomposition))

Any abelian variety $`A` is isogenous to a product of {bpref "av.simple"}[simple] abelian varieties $`B_i`, called the *isogeny factors* of $`A`:

$$`A \sim B_1 \times \cdots \times B_n.`

We say that $`A` decomposes up to isogeny into the product of the $`B_i`.
Note that two elements of this product might be isogenous; in other words, elements of the decomposition may appear with multiplicity.

Depends on: {uses "av.simple"}[]
:::

:::definition "av.deligne_module" (lean := "Module.End.IsDeligneModule, Module.End.IsDeligneModule.exists_mul_eq_natCast, Polynomial.frobeniusOrder, Polynomial.IsWeilPolynomial, LinearMap.charpoly")
*Deligne module.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.deligne_module))

A *Deligne module* is a finitely generated free $`\mathbb{Z}`-module $`M` together with a $`\mathbb{Z}`-linear endomorphism $`F` inducing an action of the Frobenius order $`\mathbb{Z}[F,V]` of some isogeny class determined by a Weil polynomial $`h(x)` such that the action of $`F` on $`M` has characteristic polynomial $`h(x)`.
If the characteristic polynomial $`h(x)` is squarefree, than $`M` can be identified with a fractional $`\mathbb{Z}[F,V]`-ideal in in the étale $`\mathbb{Q}`-algebra $`\mathbb{Q}[F]`.
The whole category of ordinary abelian variety over any finite field $`\mathbb{F}_q` can be described using Deligne modules, by a result of Deligne .
The same holds for the category of abelian varieties over a prime finite field $`\mathbb{F}_p` whose characteristic polynomials don't have real roots, thanks to a result by Centeleghe-Stix .
:::

:::definition "av.endomorphism_field" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.endomorphismField, TauCeti.AlgebraicGeometry.AbelianVariety.endRange, TauCeti.AlgebraicGeometry.AbelianVariety.End.baseChangeTower, TauCeti.AlgebraicGeometry.AbelianVariety.endomorphismField_le, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange")
*Endomorphism field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.endomorphism_field))

The *endomorphism field* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a field $`k` is the minimal extension $`L \supset k` in $`\overline{k}` such that $`\End A_L = \End A_{\overline{k}}`.  It is a finite Galois extension of $`k`.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.endomorphism_ring_conductor" (lean := "Subalgebra.relativeConductor, integralClosure, TauCeti.GlobalNumberFields.NumberFieldOrder.conductor")
*Conductor.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.endomorphism_ring_conductor))

The conductor $`\mathfrak{f}_R` of an order $`R` is the colon ideal $`(R:\mathcal{O})`, where $`\mathcal{O}` is the maximal order. Recall that a maximal ideal $`\mathfrak{m}` of $`R` is non-invertible if and only if $`\mathfrak{f}_R\subseteq \mathfrak{m}`.
:::

:::definition "av.galois_rep"
*Galois representations attached to an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.galois_rep))

If $`A` is an abelian variety defined over a field $`K` and $`m` is a positive integer, then the *mod-$`m` Galois representation* attached to $`A` is the continuous homomorphism

$$`\overline{\rho}_{A,m}: \Gal(\overline{K}/K) \to \Aut(A[m])`

describing the action of the {bpref "group.galois.absolute"}[absolute Galois group] of $`K` on the $`m`-torsion subgroup $`A[m]`.

When the characteristic of $`K` does not divide $`m > 1`, we may identify the finite abelian group $`A[m]` with $`(\Z/m\Z)^{2g}`. Since the Weil pairing is a non-degenerate, alternating, bilinear pairing $`A[m] \times A[m] \to \mu_m` equivariant with respect to the natural Galois action, we may view the representation as a map

$$`\overline{\rho}_{A,m}: \Gal(\overline{K}/K) \to \GSp_{2g}(\Z/m\Z)`

defined up to conjugation. In particular, when $`m=\ell` is prime different from the characteristic of $`K`, we have the *mod-$`\ell` Galois representation*

$$`\overline{\rho}_{A,\ell}: \Gal(\overline{K}/K) \to \GSp_{2g}(\Z/\ell\Z).`

Taking the inverse limit over prime powers $`m=\ell^n` yields the *$`\ell`-adic Galois representation* attached to $`A`,

$$`\rho_{A,\ell}: \Gal(\overline{K}/K) \to \Aut(T_{\ell}(E)) \cong \GSp_{2g}(\Z_{\ell}),`

which describes the action of the {bpref "group.galois.absolute"}[absolute Galois group] of $`K` on $`T_{\ell}(A)`, the {bpref "av.tate_module"}[$`\ell`-adic Tate module of $`A`].

When $`K` has characteristic zero one can take the inverse limit over all positive integers $`m` (ordered by divisibility) to obtain the *adelic Galois representation*

$$`\rho_{A}: \Gal(\overline{K}/K) \to \GSp_{2g}(\hat{\Z}).`

Depends on: {uses "av.tate_module"}[] {uses "group.galois.absolute"}[]
:::

:::definition "av.geometrically_simple" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsGeometricallySimple, TauCeti.AlgebraicGeometry.AbelianVariety.IsSimple, TauCeti.AlgebraicGeometry.AbelianVariety.isGeometricallySimple_congr")
*Geometrically simple.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.geometrically_simple))

An {bpref "ag.abelian_variety"}[abelian variety] is *geometrically simple* if its {bpref "ag.base_change"}[base change] to an algebraic closure of the ground field is {bpref "av.simple"}[simple].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_change"}[] {uses "av.simple"}[]
:::

:::definition "av.geometrically_squarefree" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsGeometricallySquarefree, TauCeti.AlgebraicGeometry.AbelianVariety.isGeometricallySquarefree_congr, TauCeti.AlgebraicGeometry.AbelianVariety.IsSquarefree, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange")
*Geometrically squarefree abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.geometrically_squarefree))

An {bpref "ag.abelian_variety"}[abelian variety] is *geometrically squarefree* if its {bpref "ag.base_change"}[base change] to an algebraic closure of the ground field is {bpref "av.squarefree"}[squarefree].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_change"}[] {uses "av.squarefree"}[]
:::

:::definition "av.hyperelliptic_count"
*Number of hyperelliptic Jacobians.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.hyperelliptic_count))

The number of {bpref "ag.jacobian"}[Jacobians] of {bpref "ag.hyperelliptic_curve"}[hyperelliptic curves] in each {bpref "av.isogeny_class"}[isogeny class] (up to isomorphism of {bpref "av.princ_polarizable"}[principally polarized abelian varieties]) has been computed for $`g \le 2` and $`q \le 211`; and for $`g = 3` and $`q \le 13` that are either prime or odd.

Depends on: {uses "ag.hyperelliptic_curve"}[] {uses "ag.jacobian"}[] {uses "av.isogeny_class"}[] {uses "av.princ_polarizable"}[]
:::

:::definition "av.is_product" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.prod")
*Product abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.is_product))

Given two {bpref "ag.abelian_variety"}[abelian variety] $`A_1` and $`A_2` over the same field, one can construct the *product abelian variety* $`A_1\times A_2`.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.isogeny"
*Isogeny of abelian varieties.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.isogeny))

An *isogeny* of {bpref "ag.abelian_variety"}[abelian varieties] is a surjective algebraic group homomorphism with finite kernel.

Two abelian varieties are *isogenous* if there is an isogeny between them. This defines an equivalence relation on the set of isomorphism classes.  Equivalence classes are called {bpref "av.isogeny_class"}[isogeny classes].

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.isogeny_class" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenous, TauCeti.AlgebraicGeometry.AbelianVariety.isIsogenous_congr, CategoryTheory.isIsomorphicSetoid")
*Isogeny class of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.isogeny_class))

The *isogeny class* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a field $`K` is the set of isomorphism classes of abelian varieties over $`K` that are {bpref "av.isogeny"}[isogenous] to $`A` (over $`K`).

When $`K` is a number field, LMFDB entries for isogeny classes typically list only those elements of the isogeny class that are present in the LMFDB; for abelian varieties of dimension greater than 1, this means that the list of elements of the isogeny class will often be incomplete.

When $`K` is a finite field, if the LMFDB contains information about an isogeny class of abelian varieties of dimension $`g` over a field of cardinality $`q`, then it contains every isogeny class for that dimension over that field. The LMFDB does not contain at present information on individual isomorphism classes of abelian varieties contained in the isogeny classes.

Isogeny class information listed on LFMDB pages for curves refer to the isogeny class of its {bpref "ag.jacobian"}[Jacobian].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "av.isogeny"}[]
:::

:::definition "av.jacobian_count"
*Number of Jacobians.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.jacobian_count))

The number of {bpref "ag.jacobian"}[Jacobians] in each {bpref "av.isogeny_class"}[isogeny class] (up to isomorphism of {bpref "av.princ_polarizable"}[principally polarized abelian varieties]) has been computed for $`g \le 2` and $`q \le 211`; and for $`g = 3` and $`q \le 5`.

Depends on: {uses "ag.jacobian"}[] {uses "av.isogeny_class"}[] {uses "av.princ_polarizable"}[]
:::

:::definition "av.polarization"
*Polarization.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.polarization))

A *polarization* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` is an {bpref "av.isogeny"}[isogeny] from $`A` to its dual abelian variety that is symmetric with respect to double-duality for abelian varieties and for which the pullback of the Poincare bundle along the associated graph morphism is ample.

The *degree* (resp. *kernel*) of a polarization is the degree (resp. kernel) of this isogeny.

Any abelian variety admits at least one polarization. In fact, over $`\C` the existence of a polarization distinguishes abelian varieties among complex tori.

Depends on: {uses "ag.abelian_variety"}[] {uses "av.isogeny"}[]
:::

:::definition "av.potential_toric_rank"
*Potential toric rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.potential_toric_rank))

Let $`A` be an {bpref "ag.abelian_variety"}[abelian variety] over a {bpref "nf"}[number field] $`K`, and let $`\mathfrak{p}` be a {bpref "nf.prime"}[prime] of $`K`. Then after a finite extension $`K \subset L`, there is an integral model of $`A` whose reduction is a {bpref "av.semiabelian_variety"}[semiabelian variety], i.e. the extension of an abelian variety by a torus. The *potential toric rank* of $`A` at $`\mathfrak{p}` is the dimension of that torus.

As a special case, $`A` has {bpref "ag.potential_good_reduction"}[potential good reduction] if and only if its potential toric rank is 0.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.potential_good_reduction"}[] {uses "av.semiabelian_variety"}[] {uses "nf"}[] {uses "nf.prime"}[]
:::

:::definition "av.princ_polarizable"
*Principally polarizable.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.princ_polarizable))

An {bpref "ag.abelian_variety"}[abelian variety] is *principally polarizable* if it admits a {bpref "av.polarization"}[polarization] that is an isomorphism. For example, the {bpref "ag.jacobian"}[Jacobian] of a curve admits a canonical principal polarization; by the Torelli theorem, the curve is uniquely determined by its Jacobian together with this polarization.

An isogeny class of abelian varieties is principally polarizable if one of its members admits a principal polarization.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "av.polarization"}[]
:::

:::definition "av.semiabelian_variety" (lean := "TauCeti.AlgebraicGeometry.SemiabelianVariety, TauCeti.AlgebraicGeometry.IsTorusGroupScheme, TauCeti.AlgebraicGeometry.AbelianVariety.toSemiabelianVariety, TauCeti.AlgebraicGeometry.isTorusGroupScheme_of_isZero, TauCeti.AlgebraicGeometry.AbelianVariety")
*Semiabelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.semiabelian_variety))

A *semiabelian variety* is a commutative group variety which is an extension of an {bpref "ag.abelian_variety"}[abelian variety] by a torus.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.simple" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsSimple, TauCeti.AlgebraicGeometry.AbelianVariety.isSimple_congr, TauCeti.AlgebraicGeometry.AbelianVariety.not_isSimple_trivial, TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenous, TauCeti.AlgebraicGeometry.AbelianVariety.prod")
*Simple abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.simple))

An {bpref "ag.abelian_variety"}[abelian variety] is *simple* if it is nonzero and not {bpref "av.decomposition"}[isogenous] to a product of abelian varieties of lower dimension.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.squarefree" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsSquarefree, TauCeti.AlgebraicGeometry.AbelianVariety.isSquarefree_congr, TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenyDecomposition")
*Squarefree abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.squarefree))

An {bpref "ag.abelian_variety"}[abelian variety] is *squarefree* if, in its {bpref "av.decomposition"}[isogeny decomposition], no simple factor occurs up to isogeny with exponent larger than 1.

Depends on: {uses "ag.abelian_variety"}[] {uses "av.decomposition"}[]
:::

:::definition "av.tate_module" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety, TauCeti.GroupScheme.torsion, TauCeti.TateModule, WeierstrassCurve.tateModuleGaloisRepresentation")
*Tate module of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.tate_module))

Let $`p \in \mathbb{Z}_{\geq 0}` be a prime and $`A` an abelian variety of dimension $`g` defined over a field $`K`. The *$`p`-adic Tate module* of $`A` is the inverse limit

$$`T_p(A) = \lim_{\xleftarrow[n \in \mathbb{N}]{}} A[p^n].`

Here for $`m\in\mathbb{Z}_{> 0}`, $`A[m]` denotes the $`m`-torsion subgroup of $`A`, which is the kernel of the multiplication-by-$`m` {bpref "av.isogeny"}[isogeny] of $`A`.

If $`K` has characteristic not equal to $`p`, then $`T_p(A)` is a free $`\Z_p`-module of rank $`2g`. It carries an action of the {bpref "group.galois.absolute"}[absolute Galois group] of $`K`, and thus has an associated {bpref "av.galois_rep"}[Galois representation].

Depends on: {uses "av.isogeny"}[] {uses "group.galois.absolute"}[]
:::

:::definition "av.theta_divisor"
*Theta divisor on a principally polarized abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.theta_divisor))

Let $`A` be a principally polarized {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] $`g` over a field $`k`. A *theta divisor* is an effective divisor $`\Theta` on $`A_{\overline{k}}` whose associated homomorphism $`A_{\overline{k}} \to A^\vee_{\overline{k}}` is the principal polarization.  It is determined up to translation on $`A_{\overline{k}}`.
Any theta divisor is ample.  The divisor $`[-1]^* \Theta` is another theta divisor, hence a translate of $`\Theta`.  If $`\operatorname{char} k \ne 2`, then there are exactly $`2^{2g}` translates of $`\Theta` that are *symmetric*, meaning that $`[-1]^* \Theta = \Theta`.

If $`A` is the {bpref "ag.jacobian"}[Jacobian] of a curve $`C` of {bpref "ag.curve.genus"}[genus] $`g` over $`k=\overline{k}`, then a theta divisor can be constructed as as the image of $`C^{g-1} \to \mathrm{Pic}^{g-1}_C \stackrel{\sim}\to A`, where the last isomorphism is subtraction by the class of some fixed degree $`g-1` divisor.

A symmetric theta divisor on $`A` descends to a divisor on the Kummer variety $`A / \{\pm 1\}`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.curve.genus"}[] {uses "ag.dimension"}[] {uses "ag.jacobian"}[]
:::

:::definition "av.twist" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange")
*Twist of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.twist))

A *twist* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` is an abelian variety $`A'` over the same field that becomes isomorphic to $`A` upon {bpref "ag.base_change"}[base change] to an algebraic closure.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_change"}[]
:::

:::definition "av.weak_equivalence_class" (lean := "FractionalIdeal.WeaklyEquivalent, FractionalIdeal.weakEquivalenceSetoid, FractionalIdeal.weaklyEquivalent_of_linearEquiv, LocalizedModule, Localization.AtPrime")
*weak equivalence.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.weak_equivalence_class))

Let $`R` be an order in an étale $`\mathbf{Q}`-algebra. Two fractional $`R`-ideals $`I` and $`J` are *weakly equivalent* if $`I_{\mathfrak{p}}\simeq J_{\mathfrak{p}}` as $`R_{\mathfrak{p}}`-modules for every maximal ideal $`\mathfrak{p}` of $`R`. If $`I` and $`J` are weakly equivalent then $`(I:I)=(J:J)`. Such ideals are also said to be locally isomorphic or in the same genus.
:::
