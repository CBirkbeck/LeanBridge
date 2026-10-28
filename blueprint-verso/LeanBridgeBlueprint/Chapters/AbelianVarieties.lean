import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Abelian varieties" =>

This chapter lists the LMFDB definitions relating to *abelian varieties*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "av.aut_group" (lean := "CategoryTheory.Aut, AlgebraicGeometry.Scheme.IsVarietyOver")
*Automorphism group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.aut_group))

An *automorphism* of an {bpref "ag.variety"}[algebraic variety] is an isomorphism from the variety to itself.
The set of automorphisms of an {bpref "ag.variety"}[algebraic variety] $`X` form a group $`\mathrm{Aut}(X)` under composition; this is the *automorphism group* of the {bpref "ag.variety"}[algebraic variety].

Depends on: {uses "ag.variety"}[]
:::

:::definition "av.decomposition"
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

:::definition "av.endomorphism_field"
*Endomorphism field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.endomorphism_field))

The *endomorphism field* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a field $`k` is the minimal extension $`L \supset k` in $`\overline{k}` such that $`\End A_L = \End A_{\overline{k}}`.  It is a finite Galois extension of $`k`.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.fq.all_polarizations_product"
*(In)decomposable polarized abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.all_polarizations_product))

A polarized {bpref "ag.abelian_variety"}[abelian variety] $`(A,\lambda)` is *decomposable* if there are polarized abelian varieties $`(A_1,\lambda_1)` and $`(A_2,\lambda_2)` and an isomorphism

$$`(A,\lambda) \simeq (A_1,\lambda_1) \times (A_2,\lambda_2).`

If this is not the case, we say that $`(A,\lambda)` is *indecomposable*.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.fq.angle_rank"
*Angle rank of a set.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.angle_rank))

For any set $`\{\alpha_1, \alpha_2, \ldots, \alpha_s\}` of non-zero complex numbers, the *angle rank* of the set is the quantity

$$`\delta = \dim_{\Q}\left({\rm Span}_{\Q}\left\{ \frac{ {\rm Arg}( \alpha_i)}{2\pi}\right\} \cup \{1\} \right)-1.`

The angle rank of a polynomial is the angle rank of the set of its non-zero roots, and the angle rank of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a finite field is the angle rank of its {bpref "av.fq.weil_polynomial"}[Weil polynomial].  If $`A` has {bpref "ag.dimension"}[dimension] $`g` then $`0 \le \delta \le g`, and $`\delta = 0` if and only if $`A` is {bpref "av.fq.supersingular"}[supersingular].  We define the *angle corank* of $`A` to be $`g - \delta`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "av.fq.supersingular"}[] {uses "av.fq.weil_polynomial"}[]
:::

:::definition "av.fq.bass_zfv"
*Bass Frobenius order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.bass_zfv))

The Frobenius order of an {bpref "av.isogeny_class"}[isogeny class] of abelian varieties over a finite field is *Bass* if all over-orders for the order $`\mathbb{Z}[F,V]` are Gorenstein, where $`F` is the Frobenius endomorphism and $`V` is the Verschiebung endomorphism.

Depends on: {uses "av.isogeny_class"}[]
:::

:::definition "av.fq.conductor" (lean := "Submodule.mem_div_iff_forall_mul_mem, integralClosure, conductor, TauCeti.GlobalNumberFields.NumberFieldOrder.conductor")
*Conductor of an order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.conductor))

The *conductor* $`\mathfrak{f}_R` of an {bpref "av.fq.order"}[order] $`R` in an étale algebra $`K` over $`\Q` with maximal order $`\mathcal{O}_K` is the biggest $`\mathcal{O}_K`-ideal contained in $`R`, that is,

$$`\mathfrak{f}_R = (R:\mathcal{O}_K) = \{ x \in K :\ x\mathcal{O}_K \subseteq R \}.`

If $`R\subseteq S` the *(relative) conductor* of $`R` in $`S` is the biggest $`S`-ideal contained in $`R`, that is,

$$`(R:S) = \{ x \in K :\ xS \subseteq R \}.`

Depends on: {uses "av.fq.order"}[]
:::

:::definition "av.fq.conjugate_stable" (lean := "Polynomial.IsWeilPolynomial.cmInvolution, Polynomial.IsWeilPolynomial.IsConjugateStable, Polynomial.IsWeilPolynomial.algHom_cmInvolution, Polynomial.IsWeilPolynomial.isConjugateStable_frobeniusOrder, Polynomial.EtaleAlgebra")
*Conjugate stable order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.conjugate_stable))

The étale algebra $`K=\Q[F]` generated by the Frobenius endomorphism of an abelian variety over $`\F_q` comes equipped with an algebra involution  induced by $`F\mapsto V=q/F`.
This is the *CM-involution* of $`K` and it is denoted by $`\overline{\cdot}`.
An order $`R` in $`K` is *conjugate stable* if $`R = \overline{R}`.
:::

:::definition "av.fq.cyclic_group_points"
*Cyclic group of points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.cyclic_group_points))

We say that an {bpref "av.isogeny_class"}[isogeny class] of {bpref "ag.abelian_variety"}[abelian varieties] over a finite field $`\F_q` is *cyclic* if the group of points $`A(\F_q)` is {bpref "group.cyclic"}[cyclic] for every abelian variety $`A` in the isogeny class.

Depends on: {uses "ag.abelian_variety"}[] {uses "av.isogeny_class"}[] {uses "group.cyclic"}[]
:::

:::definition "av.fq.endomorphism_ring_notation"
*Endomorphism ring notation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.endomorphism_ring_notation))

In the graph, each vertex correspond to an {bpref "ag.endomorphism_ring"}[endomorphism] of abelian varieties in the {bpref "av.isogeny_class"}[isogeny class] and each edge correspond to an inclusion.

For each {bpref "ag.endomorphism_ring"}[endomorphism ring] $`S`, we use the following *notation* $`[\mathrm{index}]^{\#\mathrm{weak}\cdot \#\mathrm{Pic}}_i` :

- *$`\mathrm{index}`* is the index of the inclusion (of additive groups) $`S\subseteq \mathcal{O}`, where $`\mathcal{O}` is the maximal order of the étale $`\mathbb{Q}`-algebra $`\mathbb{Q}[F]`;

- *$`i`* is a counter that uniquely identifies the order $`S` among all the overorders of $`\mathbb{Z}[F,V]` with index in $`\mathcal{O}` equal to $`\mathrm{index}`. See also {bpref "av.fq.lmfdb_label"}[isogeny label].

- *$`\#\mathrm{weak}`* is the number of

{bpref "av.weak_equivalence_class"}[weak equivalence classes] represented
by fractional $`\mathbb{Z}[F,V]`-ideals $`I` with multiplicator ring equal to $`S`, that is, satisfying $`(I:I)=S`; if $`S` is Gorenstein, that is, *$`\#\mathrm{weak} = 1`* this number is omitted from the notation.

- *$`\#\mathrm{Pic}`* is the size of the Picard groups of $`S`, that is, the number of invertible fractional $`S`-ideals.

Depends on: {uses "ag.endomorphism_ring"}[] {uses "av.fq.lmfdb_label"}[] {uses "av.isogeny_class"}[] {uses "av.weak_equivalence_class"}[]
:::

:::definition "av.fq.frobenius_angles"
*Frobenius angles.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.frobenius_angles))

Given an {bpref "av.isogeny_class"}[isogeny class of abelian varieties] {bpref "ag.base_field"}[defined] over a finite field $`\F_q`, its {bpref "av.fq.weil_polynomial"}[Weil polynomial] is such that all of its roots $`\alpha_1,\alpha_2, \ldots, \alpha_{2g}` have absolute value $`\sqrt{q}`. Therefore all of the information on the roots is contained in the quantities

$$`{\rm Arg}(\alpha_i),`

which we call the *Frobenius angles* of the Weil polynomial.

Depends on: {uses "ag.base_field"}[] {uses "av.fq.weil_polynomial"}[] {uses "av.isogeny_class"}[]
:::

:::definition "av.fq.group_structure" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety, TauCeti.GroupScheme.baseChangePointMulEquiv")
*Group of points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.group_structure))

The set of *rational $`k`-points* $`A(k)` of an {bpref "ag.abelian_variety"}[abelian variety] $`A` defined over a field $`k` is an abelian group. If $`k\subseteq K` is a field extension, then we have an inlcusion of abelian groups $`A(k)\subseteq A(K)`.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.fq.index_of_order" (lean := "AddSubgroup.relIndex, integralClosure, TauCeti.GlobalNumberFields.NumberFieldOrder.index")
*Index of an order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.index_of_order))

Let $`R` be an {bpref "av.fq.order"}[order] in an étale algebra $`K` with maximal order $`\mathcal{O}_K`.
Then the *index* $`[\mathcal{O}_K:R]` is a finite positive integer.

Depends on: {uses "av.fq.order"}[]
:::

:::definition "av.fq.initial_coefficients"
*Initial coefficients of the L-polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.initial_coefficients))

The LMFDB allows one to search for {bpref "av.isogeny_class"}[isogeny classes of abelian varieties] over finite fields by specifying the first few coefficients of the {bpref "av.fq.l-polynomial"}[L-polynomial] of the isogeny class. The coefficients are ordered in increasing order of the degree of the term, and the initial coefficients *do not include* the leading constant term 1.

Depends on: {uses "av.fq.l-polynomial"}[] {uses "av.isogeny_class"}[]
:::

:::definition "av.fq.l-polynomial"
*L-polynomial of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.l-polynomial))

Let $`A` be an {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] $`g` {bpref "ag.base_field"}[defined] over $`\F_q`.  Let $`F_q` be the inverse of the field automorphism $`x \mapsto x^q` in $`\Gal(\overline{\F}_q/\F_q)`, which acts on $`\ell`-adic etale cohomology.  The *L-polynomial* of $`A` is

$$`L_A(t) = \det(1-t F_q|H^1(A_{\overline{\F}_q}, \Q_{\ell})).`

This is a polynomial of degree $`2g` with integer coefficients that are independent of $`\ell`.  Its constant term is $`1`.

The L-polynomial $`L_A(t)` is the reverse of the {bpref "av.fq.weil_polynomial"}[characteristic polynomial] $`P_A(t)`, which is a {bpref "nf.weil_polynomial"}[Weil $`q`-polynomial].  Thus the complex roots of $`L_A(t)` have absolute value $`q^{-1/2}`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_field"}[] {uses "ag.dimension"}[] {uses "av.fq.weil_polynomial"}[] {uses "nf.weil_polynomial"}[]
:::

:::definition "av.fq.lmfdb_label"
*Labels for isogeny classes of abelian varieties over finite fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.lmfdb_label))

The LMFDB uses a systematic system to label
{bpref "av.isogeny_class"}[isogeny classes],
{bpref "ag.endomorphism_ring"}[endomorphism ring],
{bpref "av.weak_equivalence_class"}[weak equivalence classes],
{bpref "av.deligne_module"}[Deligne module], and
{bpref "av.polarization"}[polarizations] defined over finite fields.

The *label* format for an {bpref "av.isogeny_class"}[isogeny class] defined over a finite field is  *g.q.isog*, where

- *$`g`* is the dimension of the abelian varieties contained in the isogeny class,

- *$`q`* is the cardinality of the field over which the abelian varieties and the isogenies are defined, and

- *isog* specifies the isogeny class.

The label *isog* is obtained in the following manner: If the {bpref "av.fq.weil_polynomial"}[Weil $`q`-polynomial] of the isogeny class is

$$`1 + a_1 x + a_2 x^2 + \cdots +a_gx^g+ qa_{g-1}x^{g+1} \cdots + q^{g-1}a_1 x^{2g-1} + q^g x^{2g},`

the label contains the integer coefficients $`a_1, \ldots a_g`, encoded in base 26 with the symbols a, b, c... z, where a = 0, and separated by underscores. Negative numbers are distinguished from positive numbers by a leading a. For example, ae\\_j\\_ap denotes the polynomial

$$`1 -4x + 9x^2 - 15x^3 +9qx^4 - 4q^2 x^5 + q^3 x^6,`

where $`q` is the cardinality of the field, because e = 4, j = 9 and p = 15.

Each {bpref "ag.endomorphism_ring"}[endomorphism ring] of an {bpref "av.fq.ordinary"}[ordinary] abelian variety has a label  of the form  *g.q.isog.N.i*, where

- *$`N :=[\mathcal{O}_{\mathbb{Q}[F]}:R]`* is the index of the endomorphism ring $`R` in the maximal order $`\mathcal{O}_{\mathbb{Q}[F]}` of the field generated by the Frobenius endomorphism $`\mathbb{Q}[F]`,

- *$`i`* is an index that uniquely determines the endomorphism ring among all the overorders of $`\Z[F,V]` with index $`N` in $`\mathcal{O}_{\mathbb{Q}[F]}`.

Each {bpref "av.weak_equivalence_class"}[weak equivalence class] of an {bpref "av.fq.ordinary"}[ordinary] isogeny class has a label  of the form  *g.q.isog.N.i.w*, where

- *$`w`* is an index that uniquely determines the {bpref "av.weak_equivalence_class"}[weak equivalence class] class among all the with the same {bpref "ag.endomorphism_ring"}[endomorphism ring].

Each {bpref "av.deligne_module"}[Deligne module] of an {bpref "av.fq.ordinary"}[ordinary] isogeny class has a label  of the form  *g.q.isog.N.i.w.j*, where

- *$`j`* is an index that uniquely determines the isomorphism class of the Deligne module representing the unpolarized abelian variety within the same {bpref "av.weak_equivalence_class"}[weak equivalence class].

Each {bpref "av.polarization"}[polarizations] of an {bpref "av.fq.ordinary"}[ordinary] isogeny class has a label  of the form  *g.q.isog.N.i.w.j.d.k*, where

- *$`d`* is the degree of the polarization,

- *$`k`* is an index that determines the polarization among all the ones with the same degree.

Depends on: {uses "ag.endomorphism_ring"}[] {uses "av.deligne_module"}[] {uses "av.fq.ordinary"}[] {uses "av.fq.weil_polynomial"}[] {uses "av.isogeny_class"}[] {uses "av.polarization"}[] {uses "av.weak_equivalence_class"}[]
:::

:::definition "av.fq.maximal_zfv" (lean := "Polynomial.HasMaximalFrobeniusOrder, Polynomial.frobeniusOrder, Polynomial.EtaleAlgebra, Polynomial.IsWeilPolynomial.hasMaximalFrobeniusOrder_iff, integralClosure")
*Maximal Frobenius order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.maximal_zfv))

The Frobenius order of the abelian variety is *maximal* if it equals $`\mathcal{O}_K`.
:::

:::definition "av.fq.newton_elevation"
*Newton polygon elevation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.newton_elevation))

The {bpref "lf.newton_polygon"}[Newton polygon] $`P` of an {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] $`g` over a finite field is a piecewise linear function satisfying the following conditions:

- Its left endpoint is $`(0,0)` and its right endpoint is $`(2g, g)`.

- Its vertices are nonnegative integer lattice points.

- Its vertices are symmetric: $`(i,j)` is a vertex if and only if $`(2g-i, g-j)` is.

We call the set of polygons satisfying these conditions *eligible*.  The *elevation* of such a polygon is the number of nonnegative lattice points $`(x,y)` with $`0 \le x \le g` lying strictly below $`P`.  The set of eligible polygons forms a partially ordered set: $`P_1 \le P_2` if every point of $`P_1` is below $`P_2`.  This poset is catenary: any two maximal chains between two eligible polygons have the same length, the difference in their elevations.

The Newton polygon of an {bpref "av.fq.ordinary"}[ordinary] abelian variety has vertices $`(0,0)`, $`(g,0)`, and $`(2g,g)` and is the minimal element in this poset, with elevation $`0`.  The Newton polygon of a {bpref "av.fq.supersingular"}[supersingular] abelian variety has vertices $`(0,0)` and $`(2g,g)` and is the maximal element in this poset, with elevation $`\frac{(g+1)^2}{4}` ($`g` odd) or $`\frac{g(g+2)}{4}` ($`g` even).  There is a unique Newton polygon of elevation $`1`, with vertices $`(0,0)`, $`(g-1,0)`, $`(g+1,1)`, and $`(2g, g)`; abelian varieties with this Newton polygon are called *almost ordinary*.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "av.fq.ordinary"}[] {uses "av.fq.supersingular"}[] {uses "lf.newton_polygon"}[]
:::

:::definition "av.fq.noncyclic_primes"
*Non-cyclic primes.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.noncyclic_primes))

We say that an {bpref "av.isogeny_class"}[isogeny class] of {bpref "ag.abelian_variety"}[abelian varieties] over a finite field $`\F_q` is *non-cyclic at $`\ell`* if the {bpref "group.primary_decomposition"}[$`\ell`-primary part] of the group of points $`A(\F_q)` is {bpref "group.cyclic"}[non-cyclic] for some abelian variety $`A` in the isogeny class.  If an isogeny class is not {bpref "av.fq.cyclic_group_points"}[cyclic] then there exists at least one prime $`\ell` so that it is non-cyclic at $`\ell`.

Depends on: {uses "ag.abelian_variety"}[] {uses "av.fq.cyclic_group_points"}[] {uses "av.isogeny_class"}[] {uses "group.cyclic"}[] {uses "group.primary_decomposition"}[]
:::

:::definition "av.fq.number_field"
*Number field of an isogeny class of abelian varieties.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.number_field))

If the {bpref "av.fq.weil_polynomial"}[Weil polynomial] of an {bpref "av.isogeny_class"}[isogeny class of abelian varieties] {bpref "ag.base_field"}[defined] over a finite field is irreducible, then the *number field* attached to this isogeny class is the finite extension of $`\Q` defined by this irreducible polynomial.

Depends on: {uses "ag.base_field"}[] {uses "av.fq.weil_polynomial"}[] {uses "av.isogeny_class"}[]
:::

:::definition "av.fq.order" (lean := "Algebra.Etale, Algebra.Etale.iff_exists_algEquiv_prod, Submodule.IsLattice, integralClosure, TauCeti.GlobalNumberFields.NumberFieldOrder")
*Order in an étale algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.order))

An *étale algebra* over $`\Q` is a finite product of number fields.

An *order* $`R` in an étale algebra $`K` over $`\Q` is a subring $`R` of $`K` whose underlying
additive group is free of maximal rank, that is with rank equal to $`\dim_{\Q} K`.

If $`R` and $`S` are orders satisfying $`R \subseteq S`, we say that $`S` is an *overorder* of $`R`.

The product $`\mathcal{O}_K` of the {bpref "nf.ring_of_integers"}[ring of integers] of the {bpref "av.fq.number_field"}[number fields] that are the components of $`K` is called the *maximal order* of $`K`. It contains every order in $`K`.

The Frobenius order of an {bpref "av.isogeny_class"}[isogeny class] is an example of order.

Depends on: {uses "av.fq.number_field"}[] {uses "av.isogeny_class"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "av.fq.ordinary"
*Ordinary.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.ordinary))

An {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] $`g` {bpref "ag.base_field"}[defined] over a finite field $`\F_q` with $`q = p^r` is *ordinary* if it has {bpref "av.fq.p_rank"}[$`p`-rank] equal to $`g`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_field"}[] {uses "ag.dimension"}[] {uses "av.fq.p_rank"}[]
:::

:::definition "av.fq.p_rank" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.pRank, TauCeti.AlgebraicGeometry.AbelianVariety.pCorank, Polynomial.pRank, Polynomial.pRank_eq, Polynomial.pCorank")
*p-rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.p_rank))

Let $`A` be a $`g`-dimensional abelian variety over $`\F_q` where $`q=p^r`.
The *$`p`-rank* of $`A` is the dimension of the geometric $`p`-torsion as an $`\F_p`-vector space:
$$`p\operatorname{-rank}(A) = \dim_{\F_p}( A(\overline{\F}_p)[p] ).`
 The $`p`-rank is at most $`g`, with equality if and only if $`A` is {bpref "av.fq.ordinary"}[ordinary].  The difference between $`g` and the $`p`-rank is the *$`p`-corank* of $`A`.
:::

:::definition "av.fq.picard_group" (lean := "CommRing.Pic, ClassGroup, ClassGroup.equivPic, TauCeti.GlobalNumberFields.Pic")
*Picard Group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.picard_group))

Let $`S` be an {bpref "av.fq.order"}[order] in an étale algebra $`K` over $`\Q`.
The *Picard group* $`\Pic(S)` of $`S` is the group of invertible fractional $`S`-ideals modulo $`S`-linear isomorphism. The group operation is ideal multiplication.

The Picard group $`\Pic(\mathcal{O}_K)` of the {bpref "nf.ring_of_integers"}[ring of integers] $`\mathcal{O}_K` of a {bpref "av.fq.number_field"}[number field] $`K` is also referred to as the {bpref "nf.ideal_class_group"}[ideal class group] of $`K`. Its size is the {bpref "nf.class_number"}[class number] of $`K`.

Depends on: {uses "av.fq.number_field"}[] {uses "av.fq.order"}[] {uses "nf.class_number"}[] {uses "nf.ideal_class_group"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "av.fq.singular_dimensions"
*Dimension of a fractional ideal at residue fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.singular_dimensions))

Let $`R` be an {bpref "av.fq.order"}[order] in an étale algebra $`K` and $`I` a fractional $`R`-ideal.
For every prime $`\mathfrak{P}` of $`R`, the quotient $`I/\mathfrak{P} I` is a finite dimensional vector space over the finite field $`R/\mathfrak{P}`.
This dimension is $`1` if and only if the localization $`I_{\mathfrak{P}}` of $`I` at $`\mathfrak{P}` is a principal $`R_{\mathfrak{P}}`-ideal.
The ideal $`I` is *invertible* if and only if it is *locally principal* at every prime of $`R`.

If the ideal $`I` is not locally principal at $`\mathfrak{P}` then $`\mathfrak{P}` is a {bpref "av.fq.singular_primes"}[singular prime] of $`R`.

If $`R` is Gorenstein then every fractional $`R`-ideal $`I` with multiplicator ring $`(I:I)=R` is invertible (as an $`R`-ideal).

For each fractional $`R`-ideal $`I` with $`(I:I)=R`, we record the dimensions of $`I/\mathfrak{P}I` over $`R/\mathfrak{P}` where $`\mathfrak{P}` runs over the singular primes of $`R`.

Depends on: {uses "av.fq.order"}[] {uses "av.fq.singular_primes"}[]
:::

:::definition "av.fq.singular_primes"
*Singular primes and singular support.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.singular_primes))

A maximal ideal, or prime, $`\mathfrak{P}` of an {bpref "av.fq.order"}[order] $`R` in an étale algebra over $`\Q` is a *singular primes* if it divides the {bpref "av.fq.conductor"}[conductor] $`\mathfrak{f}_R=(R:\mathcal{O}_K)` of $`R`.

The *singular support* of an {bpref "av.fq.order"}[overorder] $`S` of the Frobenius order $`\Z[F,V]` is the set of singular primes of $`\Z[F,V]` that contain the {bpref "av.fq.conductor"}[relative conductor] $`(\Z[F,V]:S)`.

Depends on: {uses "av.fq.conductor"}[] {uses "av.fq.order"}[]
:::

:::definition "av.fq.supersingular"
*Supersingular abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.supersingular))

An {bpref "ag.abelian_variety"}[abelian variety] {bpref "ag.base_field"}[defined] over a finite field is *supersingular* if all of the {bpref "lf.newton_slopes"}[slopes] of the {bpref "lf.newton_polygon"}[Newton polygon] of its {bpref "av.fq.weil_polynomial"}[associated Weil polynomial] have value $`1/2`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_field"}[] {uses "av.fq.weil_polynomial"}[] {uses "lf.newton_polygon"}[] {uses "lf.newton_slopes"}[]
:::

:::definition "av.fq.weak_equivalence_class" (lean := "FractionalIdeal.WeakEquivalenceClass, FractionalIdeal.weakEquivalenceSetoid, FractionalIdeal.WeaklyEquivalent, FractionalIdeal.weaklyEquivalent_iff_tensorProduct, LocalizedModule")
*Weak equivalence class.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.weak_equivalence_class))

Two fractional $`S`-ideals $`I` and $`J` are in the same *weak equivalence class* if $`I_{\mathfrak{l}}=I\otimes_S S_{\mathfrak{l}}` and $`J_{\mathfrak{l}}=J\otimes_S S_{\mathfrak{l}}` are isomorphic as $`S_{\mathfrak{l}}`-modules for every maximal ideal $`\mathfrak{l}` of $`S`.
In the literature, weak equivalence classes are also called local isomorphism classes of genera.
:::

:::definition "av.fq.weil_polynomial"
*Characteristic polynomial of an abelian variety over a finite field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.weil_polynomial))

Let $`A` be an abelian variety of {bpref "ag.dimension"}[dimension] $`g` {bpref "ag.base_field"}[defined] over $`\F_q`.  Fix a prime $`\ell \nmid q`.  The $`q`-power Frobenius endomorphism $`F` of $`A` induces an endomorphism of the Tate module $`T_{\ell} A`.  The *characteristic polynomial* (or *Weil polynomial*) of $`A` is the characteristic polynomial of the latter endomorphism:

$$`P_A(t) = \det(t-F|T_{\ell} A).`

It is a monic polynomial of degree $`2g` with integer coefficients that are independent of $`\ell`.  It is the reverse of the {bpref "av.fq.l-polynomial"}[$`L`-polynomial].  By a theorem of Weil, $`P_A(t)` is a {bpref "nf.weil_polynomial"}[Weil $`q`-polynomial].

Alternatively, $`P_A(t)` can be defined using $`\ell`-adic etale cohomology:
If $`F_q` is the \*inverse\* of the field automorphism $`x \mapsto x^q` in $`\Gal(\overline{\F}_q/\F_q)`, then

$$`P_A(t) = \det(t-F_q|H^1(A_{\overline{\F}_q}, \Q_{\ell})).`

Depends on: {uses "ag.base_field"}[] {uses "ag.dimension"}[] {uses "nf.weil_polynomial"}[]
:::

:::definition "av.fq.zfv_index" (lean := "Polynomial.frobeniusOrderIndex, Polynomial.frobeniusOrder, Polynomial.IsWeilPolynomial.frobeniusOrder_le_integralClosure, AddSubgroup.relIndex, integralClosure")
*Index of maximal order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.zfv_index))

The *index* of the Frobenius order is the index of the ring $`\mathbb{Z}[F,V]` in $`\mathcal{O}_K`, where $`F` is the Frobenius endomorphism and $`V` is the Verschiebung endomorphism.
:::

:::definition "av.fq.zfv_real_index" (lean := "Polynomial.realIndex, Polynomial.realOrder, Polynomial.realSubalgebra, Polynomial.IsWeilPolynomial.realOrder_le_integralClosure, AddSubgroup.relIndex")
*Index of Real Order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.zfv_real_index))

The *real index* is the index of $`\mathbb{Z}[F+V]` in the totally real ring $`\mathcal{O}_{K^+}`, where $`F` is the Frobenius endomorphism, $`V` is the Verschiebung endomorphism, and $`K^+=\mathbb{Q}[F+V]` is the totally real subfield of $`K=\mathbb{Q}[F,V]`.
:::

:::definition "av.fq.zfv_rel_disc_norm" (lean := "Polynomial.relativeDiscriminantNorm, Polynomial.EtaleAlgebra, Polynomial.EtaleAlgebra.frobenius, Polynomial.EtaleAlgebra.verschiebung, Algebra.norm")
*Relative discriminant norm.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.fq.zfv_rel_disc_norm))

The *relative discriminant* norm is $`N_{K/\mathbb{Q}}(F-V)`, where $`F` is the Frobenius endomorphism, $`V` is the Verschiebung endomorphism, and $`K=\mathbb{Q}[F,V]`.  For this value, we have

$$`|N_{K/\mathbb{Q}}(F-V)|=|\Delta_R|/\Delta_{R^+}^2,`

where $`R=\mathbb{Q}[F,V]` is the Frobenius order and $`R^+=\mathbb{Z}[F+V]` is the real order.
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

:::definition "av.geometrically_squarefree"
*Geometrically squarefree abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.geometrically_squarefree))

An {bpref "ag.abelian_variety"}[abelian variety] is *geometrically squarefree* if its {bpref "ag.base_change"}[base change] to an algebraic closure of the ground field is {bpref "av.squarefree"}[squarefree].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_change"}[] {uses "av.squarefree"}[]
:::

:::definition "av.is_product" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.prod")
*Product abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.is_product))

Given two {bpref "ag.abelian_variety"}[abelian variety] $`A_1` and $`A_2` over the same field, one can construct the *product abelian variety* $`A_1\times A_2`.

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

:::definition "av.semiabelian_variety"
*Semiabelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.semiabelian_variety))

A *semiabelian variety* is a commutative group variety which is an extension of an {bpref "ag.abelian_variety"}[abelian variety] by a torus.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.squarefree"
*Squarefree abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.squarefree))

An {bpref "ag.abelian_variety"}[abelian variety] is *squarefree* if, in its {bpref "av.decomposition"}[isogeny decomposition], no simple factor occurs up to isogeny with exponent larger than 1.

Depends on: {uses "ag.abelian_variety"}[] {uses "av.decomposition"}[]
:::

:::definition "av.theta_divisor"
*Theta divisor on a principally polarized abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.theta_divisor))

Let $`A` be a principally polarized {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] $`g` over a field $`k`. A *theta divisor* is an effective divisor $`\Theta` on $`A_{\overline{k}}` whose associated homomorphism $`A_{\overline{k}} \to A^\vee_{\overline{k}}` is the principal polarization.  It is determined up to translation on $`A_{\overline{k}}`.
Any theta divisor is ample.  The divisor $`[-1]^* \Theta` is another theta divisor, hence a translate of $`\Theta`.  If $`\operatorname{char} k \ne 2`, then there are exactly $`2^{2g}` translates of $`\Theta` that are *symmetric*, meaning that $`[-1]^* \Theta = \Theta`.

If $`A` is the {bpref "ag.jacobian"}[Jacobian] of a curve $`C` of {bpref "ag.curve.genus"}[genus] $`g` over $`k=\overline{k}`, then a theta divisor can be constructed as as the image of $`C^{g-1} \to \mathrm{Pic}^{g-1}_C \stackrel{\sim}\to A`, where the last isomorphism is subtraction by the class of some fixed degree $`g-1` divisor.

A symmetric theta divisor on $`A` descends to a divisor on the Kummer variety $`A / \{\pm 1\}`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.curve.genus"}[] {uses "ag.dimension"}[] {uses "ag.jacobian"}[]
:::

:::definition "av.weak_equivalence_class" (lean := "FractionalIdeal.WeaklyEquivalent, FractionalIdeal.weakEquivalenceSetoid, FractionalIdeal.weaklyEquivalent_of_linearEquiv, LocalizedModule, Localization.AtPrime")
*weak equivalence.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.weak_equivalence_class))

Let $`R` be an order in an étale $`\mathbf{Q}`-algebra. Two fractional $`R`-ideals $`I` and $`J` are *weakly equivalent* if $`I_{\mathfrak{p}}\simeq J_{\mathfrak{p}}` as $`R_{\mathfrak{p}}`-modules for every maximal ideal $`\mathfrak{p}` of $`R`. If $`I` and $`J` are weakly equivalent then $`(I:I)=(J:J)`. Such ideals are also said to be locally isomorphic or in the same genus.
:::
