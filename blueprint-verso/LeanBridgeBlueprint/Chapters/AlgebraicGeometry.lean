import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic geometry" =>

This section lists the LMFDB definitions in the category `ag`. Each definition links back to its LMFDB knowl.

:::definition "ag.abelian_surface" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety, TauCeti.AlgebraicGeometry.AbelianVariety.dim, TauCeti.AlgebraicGeometry.AbelianVariety.prod")
*Abelian surface.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.abelian_surface))

An *abelian surface* is an {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] 2.

Examples are given by the product of two {bpref "ec"}[elliptic curves], or the {bpref "ag.jacobian"}[Jacobian] of a curve of {bpref "ag.curve.genus"}[genus] 2.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.curve.genus"}[] {uses "ag.dimension"}[] {uses "ag.jacobian"}[] {uses "ec"}[]
:::

:::definition "ag.abelian_variety" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety")
*Abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.abelian_variety))

An *abelian variety* defined over the field $`K` is a smooth connected projective {bpref "ag.variety"}[variety] equipped with the structure of an algebraic group. The group law is automatically commutative.

An abelian variety of dimension 1 is the same as an {bpref "ec"}[elliptic curve].

Depends on: {uses "ag.variety"}[] {uses "ec"}[]
:::

:::definition "ag.affine_space" (lean := "AlgebraicGeometry.AffineSpace, AlgebraicGeometry.AffineSpace.homOverEquiv, AlgebraicGeometry.AffineSpace.coord")
*Affine space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.affine_space))

*Affine space* $`\mathbb{A}^n(K)` of {bpref "ag.dimension"}[dimension] $`n` over a {bpref "ring.field"}[field] $`K` is the set $`K^n`.

If $`P=(x_1,\dots,x_n)` is a point in $`\mathbb{A}^n(K)`, the $`x_i` are called the \*affine coordinates\* of $`P`.  Thus

$$`\mathbb{A}^n(K) = \{(x_1,\dots,x_n)\mid x_1,\dots,x_n\in K\}.`

Depends on: {uses "ring.field"}[]
:::

:::definition "ag.arithmetic_genus" (lean := "AlgebraicGeometry.Scheme.Modules.eulerCharBelow, AlgebraicGeometry.Scheme.genus")
*Arithmetic genus.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.arithmetic_genus))

The *arithmetic genus* of a projective scheme $`X` is $`p_a(X) = (-1)^{\dim X}(\chi(X)-1)` where $`\chi(X)` is the
{bpref "ag.holomorphic_euler_char"}[holomorphic Euler characteristic].

Depends on: {uses "ag.holomorphic_euler_char"}[]
:::

:::definition "ag.aut_group" (lean := "CategoryTheory.Aut, CategoryTheory.Over, AlgebraicGeometry.Scheme.IsVarietyOver")
*Automorphism group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.aut_group))

An *automorphism* of an {bpref "ag.variety"}[algebraic variety] is an isomorphism from the variety to itself.
The set of automorphisms of an {bpref "ag.variety"}[algebraic variety] $`X` form a group $`\mathrm{Aut}(X)` under composition; this is the *automorphism group* of the {bpref "ag.variety"}[algebraic variety].

Depends on: {uses "ag.variety"}[]
:::

:::definition "ag.bad_prime" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.badPrimes, TauCeti.AlgebraicGeometry.AbelianVariety.HasGoodReductionAt, AlgebraicGeometry.Scheme.HasGoodReductionAt, TauCeti.AlgebraicGeometry.AbelianVariety")
*Prime of bad reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.bad_prime))

For an abelian variety $`A` of dimension $`g` over a number field $`K`, a *prime of bad reduction* (for $`A`) is a prime $`\mathfrak{p}` of $`K` for which the reduction of $`A` modulo $`\mathfrak{p}` is not an abelian variety of dimension $`g` over the residue field at $`\mathfrak{p}`.  The number of primes of bad reduction is always finite; these are precisely the primes that divide the {bpref "ag.conductor"}[conductor] of $`A`.

Depends on: {uses "ag.conductor"}[]
:::

:::definition "ag.base_change" (lean := "AlgebraicGeometry.Scheme.IsBaseChangeFromSubfield, AlgebraicGeometry.Scheme.isBaseChangeFromSubfield_iff, AlgebraicGeometry.Scheme.isBaseChangeFromSubfield_pullback, CategoryTheory.Over.pullback, AlgebraicGeometry.Scheme.IsVarietyOver")
*Base change.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.base_change))

Let $`V` be an {bpref "ag.variety"}[algebraic variety] defined over a {bpref "ring.field"}[field] $`K`. If $`L/K` is a field extension, then any set of equations that define $`V` over $`K` can be used to define an algebraic variety over $`L`, the *base change* of $`V` from $`K` to $`L` (typically denoted $`V_L`).

An algebraic variety over a field $`L` is said to be a *base change* if it is the base change of an algebraic variety defined over a proper subfield of $`L`, equivalently, if its {bpref "ag.base_field"}[base field] is not a {bpref "ag.minimal_field"}[minimal field of definition].

Depends on: {uses "ag.variety"}[] {uses "ring.field"}[]
:::

:::definition "ag.base_field" (lean := "AlgebraicGeometry.Scheme.Over")
*Base field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.base_field))

The *base field*, of an {bpref "ag.abelian_variety"}[algebraic variety] is the field over which it is defined; it necessarily contains the coefficients of a set of defining equations for the variety, but it is not necessarily a {bpref "ag.minimal_field"}[minimal field of definition].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.minimal_field"}[]
:::

:::definition "ag.bielliptic_curve" (lean := "AlgebraicGeometry.Scheme.IsBiellipticCurveOver, AlgebraicGeometry.Scheme.IsBiellipticInvolution, TauCeti.IsBiellipticFunctionField, TauCeti.IsBiellipticInvolution, TauCeti.IsEllipticFunctionField")
*Bielliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.bielliptic_curve))

A smooth projective {bpref "ag.curve"}[algebraic curve] $`X` defined over a field $`k` of {bpref "ag.curve.genus"}[genus] $`g\ge 2` is a *bielliptic curve* if and only if it satisfies one of the following conditions:

- $`X` admits a 2-to-1 map $`X\to E` defined over the algebraic closure $`\bar k` onto an elliptic curve $`E`.

- There exists an involution $`w \in \Aut(X)` defined over $`k` such that $`X/\langle w \rangle` has genus $`1` and $`X/\langle w \rangle (k) \ne \empty`.

- There exists an involution $`w \in \Aut(X)` defined over $`k` having exactly $`2g -2` fixed points.

The involution above is called the *bielliptic involution*.

Depends on: {uses "ag.curve"}[] {uses "ag.curve.genus"}[]
:::

:::definition "ag.canonical_height"
*Canonical height of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.canonical_height))

Let $`A` be a {bpref "av.princ_polarizable"}[principally polarised] {bpref "ag.abelian_variety"}[abelian variety] defined over a {bpref "nf"}[number field] $`L`.  The *canonical height* on $`A` is a function

$$`\hat{h}: A(L) \to \R_{ {}\ge0}`

defined on the {bpref "ag.mordell_weil"}[Mordell-Weil group] $`A(L)`
which induces a positive definite quadratic form on $`A(L)\otimes\R`.

One definition of $`\hat{h}(P)` is $`\hat{h}(P)= h_{\mathrm{Kum}}(\sigma(P))`, where $`\sigma \colon A \to K` is the natural map from $`A` to its Kummer surface $`K : = A/\{\pm 1\}`, and $`h_{\mathrm{kum}} \colon K(L) \to \R` the canonical height pairing associated to a theta divisor $`\Theta` on $`K`, which can be defined by

$$`h_{\mathrm{Kum}}(Q)=\lim_{n\to\infty} n^{-2}h_{\Theta}\bigl(nQ\bigr),`

where $`h_{\Theta}` is the {bpref "nf.weil_height"}[Weil height] associated to a {bpref "av.theta_divisor"}[theta divisor] $`\Theta` on $`K`.

Related to the canonical height is the *height pairing*

$$`\langle-,-\rangle : A(L)\times A(L) \to \R`

defined by $`\langle P,Q\rangle = \frac{1}{2}(\hat{h}(P+Q)-\hat{h}(P)-\hat{h}(Q))`, which is a positive definite quadratic form on $`A(L)\otimes\R`, used in defining the {bpref "ag.regulator"}[regulator] of $`A/L`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.mordell_weil"}[] {uses "av.princ_polarizable"}[] {uses "av.theta_divisor"}[] {uses "nf"}[] {uses "nf.weil_height"}[]
:::

:::definition "ag.canonical_model" (lean := "AlgebraicGeometry.Scheme.canonicalMap, AlgebraicGeometry.Scheme.canonicalModel, AlgebraicGeometry.Scheme.linearSystemMap, TauCeti.canonicalDivisor, AlgebraicGeometry.Scheme.eq_linearSystemMap_iff")
*Canonical model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.canonical_model))

The *canonical map* of a curve $`C` of {bpref "ag.curve.genus"}[genus] $`g` is the map to $`\mathbb{P}^{g-1}` defined by the canonical class.  For {bpref "ag.hyperelliptic_curve"}[non-hyperelliptic] curves of genus larger than 1, this map is an embedding, and its image is a normal curve called the *canonical model* of $`C`.

Depends on: {uses "ag.curve.genus"}[] {uses "ag.hyperelliptic_curve"}[]
:::

:::definition "ag.cluster_picture" (lean := "Polynomial.IsPadicCluster, Polynomial.padicClusterSize, Polynomial.padicClusterDepth, Polynomial.padicClusterRelDepth, Polynomial.isPadicCluster_rootSet")
*Cluster picture.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.cluster_picture))

Let $`H` be an {bpref "ec"}[elliptic] or {bpref "ag.hyperelliptic_curve"}[hyperelliptic curve] over $`\Q` given by an equation $`y^2 = f(x)`, and let $`p` be an odd prime number. Then the *cluster picture* of $`H` at $`p` associated to this particular equation for $`H`, is a graphical representation of the $`p`-adic distances between the roots of $`f`.

The *size* of a cluster is the number of roots of $`f(x)` that it contains.

The *depth* of a cluster, is the valuation of the radius of a minimal $`p`-adic disk containing all the roots in that particular cluster. The numbers that are depicted in a cluster picture represent the *relative depth*: the difference between the depth of a certain cluster and the smallest other cluster in which that certain cluster is contained. For the top cluster, which contains all the roots of $`f(x)`, the depth is depicted instead of the relative depth (as there is no relative depth in this case).

More information about cluster pictures can be found in _A user's guide to the local arithmetic of hyperelliptic curves_ .

Depends on: {uses "ag.hyperelliptic_curve"}[] {uses "ec"}[]
:::

:::definition "ag.cohen_macaulay_type" (lean := "Subalgebra.cohenMacaulayType, Subalgebra.cohenMacaulayTypeAt, Subalgebra.traceDual, TauCeti.GlobalNumberFields.NumberFieldOrder.cohenMacaulayType_eq_one_iff_isGorenstein, TauCeti.GlobalNumberFields.NumberFieldOrder.cohenMacaulayType_eq_one_iff_forall_isUnit")
*Cohen-Macaulay type.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.cohen_macaulay_type))

The *Cohen-Macaulay* type of an order $`R`, is the minimal number of generators (as an $`R`-module) of a canonical module of $`R`.
Note that the trace dual ideal $`R^t =\{ a : \mathrm{Tr}(aR) \subseteq \mathbb{Z} \}` is a canonical module for $`R`. In particular, the Cohen-Macaulay type equals
$`\max \{ \dim_{R/\mathfrak{l}} \frac{R^t}{\mathfrak{l}R^t} \}_{\mathfrak{l}}`, where $`\mathfrak{l}` runs over the maximal ideals of $`R`. The order is called Gorenstein if the Cohen-Macaulay type equals $`1`. This is the case precisely when every fractional $`R`-ideal $`I` with $`(I:I)` is invertible.
:::

:::definition "ag.complex_multiplication" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.HasComplexMultiplication, TauCeti.AlgebraicGeometry.AbelianVariety.EndAlgebra, TauCeti.AlgebraicGeometry.AbelianVariety.hasComplexMultiplication_congr, TauCeti.AlgebraicGeometry.AbelianVariety.End, NumberField.IsCMField")
*Complex multiplication.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.complex_multiplication))

A {bpref "ag.geom_simple"}[simple] {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] $`g` is said to have *complex multiplication* (CM) if its
{bpref "ag.endomorphism_algebra"}[endomorphism algebra] is a {bpref "nf.cm_field"}[CM field] of {bpref "nf.degree"}[degree] $`2g`, or equivalently, if its {bpref "ag.endomorphism_ring"}[endomorphism ring] is an {bpref "nf.order"}[order] in a CM field of degree $`2g`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "ag.endomorphism_algebra"}[] {uses "ag.endomorphism_ring"}[] {uses "ag.geom_simple"}[] {uses "nf.cm_field"}[] {uses "nf.degree"}[] {uses "nf.order"}[]
:::

:::definition "ag.conductor"
*Conductor of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.conductor))

The *conductor* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over $`\Q` is a positive integer $`N` whose prime factors are the primes $`p` where $`A` has bad reduction. The power to which $`p` divides $`N` depends on the type of bad reduction; it can be expressed in terms of ramification in the $`\ell`-adic representation associated to $`A` for any prime $`\ell \ne p`.

The conductor of an abelian variety over a number field is defined similarly; it is an ideal that is a product of positive powers of the prime ideals where $`A` has bad reduction.  The conductor of a curve $`C` over a number field is defined to be the conductor of the {bpref "ag.jacobian"}[Jacobian] of $`C`.

Isogenous abelian varieties have the same conductor.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[]
:::

:::definition "ag.curve" (lean := "AlgebraicGeometry.Scheme.IsAlgebraicCurveOver, AlgebraicGeometry.Scheme.isAlgebraicCurveOver_iff_isCurveOver_and_geometricallyIntegral, AlgebraicGeometry.Scheme.IsAlgebraicCurveOver.isFunctionField, AlgebraicGeometry.Scheme.IsVarietyOver, AlgebraicGeometry.Scheme.IsCurveOver")
*Algebraic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.curve))

An *algebraic curve* is an {bpref "ag.variety"}[algebraic variety] of dimension $`1.`

Depends on: {uses "ag.variety"}[]
:::

:::definition "ag.curve.genus" (lean := "AlgebraicGeometry.Scheme.IsCurveOver, AlgebraicGeometry.Scheme.genus, TauCeti.genus")
*Genus of a smooth curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.curve.genus))

The *genus* of a smooth projective geometrically integral curve $`C` defined over a field $`k` is the dimension of the $`k`-vector space of regular differentials $`H^0(C, \omega_C)`.  When $`k=\C` this coincides with the topological genus of the corresponding {bpref "ag.riemann_surface"}[Riemann surface].

The quantity defined above is sometimes also called the *algebraic genus* or the *geometric genus* of $`C`. Because of our assumption on the smoothness of $`C`, it coincides with the *arithmetic genus* $`H^1(C,\mathcal{O}_C)`.

Depends on: {uses "ag.riemann_surface"}[]
:::

:::definition "ag.curve.smooth" (lean := "AlgebraicGeometry.Smooth, AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff")
*Smoothness of an algebraic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.curve.smooth))

Let $`C` be an {bpref "ag.curve"}[algebraic curve] over a perfect field $`k`. Then $`C` is called *smooth* if the extension of $`C` to the algebraic closure of $`k` is {bpref "ag.singular_point"}[non-singular] at all of its points.

Depends on: {uses "ag.curve"}[] {uses "ag.singular_point"}[]
:::

:::definition "ag.cyclic_trigonal" (lean := "AlgebraicGeometry.Scheme.IsCyclicTrigonalCurveOver, TauCeti.IsCyclicTrigonalFunctionField, TauCeti.IsTrigonalAutomorphism, TauCeti.isCyclicTrigonalFunctionField_iff_exists_isTrigonalAutomorphism")
*Cyclic trigonal curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.cyclic_trigonal))

An {bpref "ag.curve"}[algebraic curve] $`X` is a *cyclic trigonal curve* if there is an order $`3` subgroup $`H` of its {bpref "g2c.aut_grp"}[automorphism group] such that the {bpref "ag.quotient_curve"}[quotient curve] $`X/H` is isomorphic to $`\mathbb{P}^1`.

A generator of such a subgroup $`H` is called a *trigonal automorphism*.

Depends on: {uses "ag.curve"}[] {uses "ag.quotient_curve"}[] {uses "g2c.aut_grp"}[]
:::

:::definition "ag.dimension" (lean := "topologicalKrullDim, TopologicalSpace.IrreducibleCloseds")
*Dimension of an algebraic variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.dimension))

The *dimension* of an {bpref "ag.variety"}[algebraic variety] $`V` is the maximal length $`d` of a chain

$$`V_0 \subset V_1 \subset \cdots \subset V_d`

of distinct {bpref "ag.irreducible"}[irreducible] subvarieties of $`V`.

Depends on: {uses "ag.irreducible"}[] {uses "ag.variety"}[]
:::

:::definition "ag.endomorphism_algebra" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.End")
*Endomorphism algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.endomorphism_algebra))

The *endomorphism algebra* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` is the $`\Q`-algebra $`\textrm{End}(A)\otimes\Q`, where $`\textrm{End}(A)` is the {bpref "ag.endomorphism_ring"}[endomorphism ring] of $`A`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_ring"}[]
:::

:::definition "ag.endomorphism_ring" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.End")
*Endomorphism ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.endomorphism_ring))

An *endomorphism* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a field $`k` is a homomorphism $`\varphi \colon A \to A` defined over $`k`.  The set of endomorphisms of an abelian variety $`A` can be given the structure of a ring in which addition is defined pointwise (using the group operation of $`A`) and multiplication is composition; this ring is called the *endomorphism ring* of $`A`, denoted $`\textrm{End}(A)`.

For endomorphisms defined over an extension of $`k`, we instead speak about the {bpref "ag.geom_endomorphism_ring"}[geometric endomorphism ring].

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "ag.fq.point_counts" (lean := "AlgebraicGeometry.Scheme.PointOver, Nat.card, GaloisField")
*Point counts of a variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.fq.point_counts))

If $`X` is a {bpref "ag.variety"}[variety] {bpref "ag.base_field"}[defined] over a finite field $`\mathbb{F}_q`, one can show that it will have finitely many points that are defined over that field. Upon extending the base field to $`\mathbb{F}_{q^2}`, $`\mathbb{F}_{q^3}`, $`\mathbb{F}_{q^4}`, etc. the number of points of $`X` defined over those fields remains finite, as long as we consider only field extensions of finite degree over $`\mathbb{F}_q`.

Depends on: {uses "ag.base_field"}[] {uses "ag.variety"}[]
:::

:::definition "ag.geom_component" (lean := "irreducibleComponents, AlgebraicGeometry.Scheme.geometricBaseChange")
*Geometric component.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.geom_component))

A *geometric component* of a smooth scheme $`X` of finite type over a field $`k` is an irreducible component of the base change $`X_{\overline{k}}`.  (Because $`X_{\overline{k}}` is smooth, irreducible components are the same as connected components.)

The set $`\pi_0(X_{\overline{k}})` of geometric components is a finite set with an action of the {bpref "group.galois.absolute"}[absolute Galois group] $`\Gal_k`.

Depends on: {uses "group.galois.absolute"}[]
:::

:::definition "ag.geom_endomorphism_algebra" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.End, TauCeti.AlgebraicGeometry.AbelianVariety.End.baseChange, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange")
*Geometric endomorphism algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.geom_endomorphism_algebra))

For an abelian variety $`A` over a field $`F`, the *geometric endomorphism algebra* of $`A` is the $`\Q`-algebra $`\End(A_{\overline{F}}) \otimes \Q`, where $`\End(A_{\overline{F}})` is the {bpref "ag.geom_endomorphism_ring"}[geometric endomorphism ring] of $`A`.

Depends on: {uses "ag.geom_endomorphism_ring"}[]
:::

:::definition "ag.geom_endomorphism_ring" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.End, TauCeti.AlgebraicGeometry.AbelianVariety.End.baseChange, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange")
*Geometric endomorphism ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.geom_endomorphism_ring))

For an abelian variety $`A` over a field $`F`, the *geometric endomorphism ring* of $`A` is $`\End(A_{\overline{F}})`, the {bpref "ag.endomorphism_ring"}[endomorphism ring] of the base change of $`A` to an algebraic closure $`\overline{F}` of $`F`.

Depends on: {uses "ag.endomorphism_ring"}[]
:::

:::definition "ag.geom_simple" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsGeometricallySimple, TauCeti.AlgebraicGeometry.AbelianVariety.isGeometricallySimple_congr, TauCeti.AlgebraicGeometry.AbelianVariety.IsSimple, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange")
*Geometrically simple.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.geom_simple))

An {bpref "ag.abelian_variety"}[abelian variety] over a field $`k` is *geometrically (or absolutely) simple* if it is {bpref "ag.simple"}[simple] when viewed as a variety over $`\bar k`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.simple"}[]
:::

:::definition "ag.gonality" (lean := "TauCeti.gonality, AlgebraicGeometry.Scheme.gonality, TauCeti.IsFunctionField.exists_finrank_eq_gonality, TauCeti.IsFunctionField.gonality_pos")
*Gonality of a curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.gonality))

The *gonality* (or *$`k`-gonality*) of an integral {bpref "ag.curve"}[algebraic curve] $`X` over a field $`k` is the minimal degree of a dominant $`k`-morphism $`X \to \mathbb{P}^1_k`.  Equivalently, it is the minimum of $`[k(X):k(t)]` as $`t` ranges over (transcendental) elements of the function field $`k(X)` of $`X`.

The base extension of any dominant morphism $`X \to \mathbb{P}^1_k`  is a dominant morphism $`X_{\overline{k}} \to \mathbb{P}^1_{\overline{k}}`, so the {bpref "ag.gonality_geom"}[geometric gonality] of $`X` is less than or equal to the $`k`-gonality of $`X`.

Depends on: {uses "ag.curve"}[]
:::

:::definition "ag.gonality_geom" (lean := "AlgebraicGeometry.Scheme.geometricGonality, AlgebraicGeometry.Scheme.IsHyperellipticCurveOver.geometricGonality_le_two, AlgebraicGeometry.Scheme.geometricBaseChange, TauCeti.gonality")
*Geometric gonality.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.gonality_geom))

Let $`X` be a geometrically integral {bpref "ag.curve"}[algebraic curve] over a field $`k`.
Let $`\overline{k}` be an {bpref "nf.algebraic_closure"}[algebraic closure] of $`k`.
Let $`X_{\overline{k}}` be the base extension.
The *geometric gonality* (or *$`\overline{k}`-gonality*) of $`X` is the {bpref "ag.gonality"}[gonality] of $`X_{\overline{k}}`, that is, the minimal degree of a dominant morphism $`X_{\overline{k}} \to \mathbb{P}^1_{\overline{k}}`.

Depends on: {uses "ag.curve"}[] {uses "ag.gonality"}[]
:::

:::definition "ag.good_reduction" (lean := "AlgebraicGeometry.Scheme.HasGoodReductionAt, AlgebraicGeometry.Scheme.badReductionPrimes, TauCeti.Model, TauCeti.Model.IsProper, AlgebraicGeometry.Smooth")
*Good and bad reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.good_reduction))

A smooth proper {bpref "ag.variety"}[variety] $`X` over a {bpref "nf"}[number field] $`K` is said to have *good reduction* at a {bpref "nf.prime"}[prime] $`\mathfrak{p}` if it has a model over $`\mathcal{O}_{K, \mathfrak{p}}` whose reduction modulo $`\mathfrak{p}` is a smooth variety over the residue field; more precisely, $`X` has good reduction if it is the generic fiber of a smooth proper scheme over $`\mathcal{O}_{K, \mathfrak{p}}`.  Otherwise, $`\mathfrak{p}` is said to be a prime of *bad reduction*.

The set of primes at which a given $`X` has bad reduction is finite.

For an {bpref "ag.abelian_variety"}[abelian variety] $`X`, the primes of bad reduction are the primes that divide the {bpref "ag.conductor"}[conductor] of $`X`.

If a curve has good reduction at $`\mathfrak{p}`, then its {bpref "ag.jacobian"}[Jacobian] does too.  The converse need not hold.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.conductor"}[] {uses "ag.jacobian"}[] {uses "ag.variety"}[] {uses "nf"}[] {uses "nf.prime"}[]
:::

:::definition "ag.holomorphic_euler_char" (lean := "AlgebraicGeometry.Scheme.Modules.eulerCharBelow")
*Holomorphic Euler characteristic.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.holomorphic_euler_char))

The *holomorphic Euler characteristic* of a projective scheme $`X` is the alternating sum $`\chi(X)=\chi(\mathcal{O}_X) = \sum_{i=0}^{\dim X} (-1)^i \dim H^i(X, \mathcal{O}_X)`.

See also the {bpref "ag.arithmetic_genus"}[arithmetic genus].
:::

:::definition "ag.hyperelliptic_curve" (lean := "AlgebraicGeometry.Scheme.IsHyperellipticCurveOver, AlgebraicGeometry.Scheme.isHyperellipticCurveOver_iff, HyperellipticEquation, HyperellipticEquation.FunctionField, HyperellipticEquation.isHyperellipticFunctionField, MvPolynomial.IsHomogeneous")
*Hyperelliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.hyperelliptic_curve))

A *hyperelliptic curve* $`X` over a field $`k` is a smooth projective  {bpref "ag.curve"}[algebraic curve] of {bpref "ag.curve.genus"}[genus] $`g\ge 2` that admits a 2-to-1 map $`X\to \mathbb{P}^1` defined over the algebraic closure $`\bar k`.

If $`X` is a hyperelliptic curve over $`k`, then the canonical map $`X \to \mathbb{P}^{g-1}` is a 2-to-1 map onto a smooth genus 0 curve $`Y`.  The curve $`Y` is isomorphic to $`\mathbb{P}^1` if and only if $`Y` has a $`k`-rational point.

If $`X` admits a 2-to-1 map to $`\mathbb{P}^1` that is defined over $`k`, then $`X` has a *Weierstrass model* of the form $`y^2+h(x)y=f(x)`; when the characteristic of $`k` is not $`2` one can complete the square to put this model in the form $`y^2=f(x)`.

In general, there is always a model for $`X` in $`\mathbb{P}^3` of the form

$$`h(x,y,z)=0\qquad w^2=f(x,y,z)`

where $`h(x,y,z)` is a homogeneous polynomial of degree $`2` (a *conic*) and $`f(x,y,z)` is a homogeneous polynomial of degree $`g+1`.

Depends on: {uses "ag.curve"}[] {uses "ag.curve.genus"}[]
:::

:::definition "ag.irreducible" (lean := "IrreducibleSpace, AlgebraicGeometry.GeometricallyIrreducible")
*Irreducible variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.irreducible))

A {bpref "ag.variety"}[variety] defined over a field $`F` is *irreducible* if it is nonempty and cannot be decomposed as the union of two strictly smaller varieties over $`F`. It is *geometrically irreducible* if it remains irreducible when seen as a variety over the {bpref "nf.algebraic_closure"}[algebraic closure] of $`F`.

Depends on: {uses "ag.variety"}[]
:::

:::definition "ag.isolated_point"
*Isolated point.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.isolated_point))

A closed point $`x` on a curve $`C` is isolated if it is not contained in a family of effective degree $`d` divisors parametrized by $`\mathbb{P}^1` or a positive rank abelian variety.
:::

:::definition "ag.jacobian"
*Jacobian of a curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.jacobian))

The *Jacobian* of a (smooth, projective, geometrically integral) curve $`X` of genus $`g` over a field $`k` is a $`g`-dimensional principally polarized {bpref "ag.abelian_variety"}[abelian variety] $`J` that is canonically associated to $`X`.

If $`X` has a $`k`-rational point, then $`J(k)` is isomorphic to the group of degree zero divisors on $`X` modulo linear equivalence.  A choice of rational point on $`X` determines a morphism $`X \to J` called an Abel-Jacobi map; it is an embedding if and only if $`g \ge 1`, and an isomorphism if and only if $`g=1`.

The Torelli theorem states that if $`X` and $`Y` are curves whose Jacobians are isomorphic as \*principally polarized\* abelian varieties, then $`X` and $`Y` are isomorphic.  It is possible, however, for non-isomorphic curves to have Jacobians that are isomorphic as unpolarized abelian varieties.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "ag.kodaira_dimension"
*Kodaira dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.kodaira_dimension))

Let $`X` be a nonsingular complex algebraic variety with canonical divisor $`K`. For each $`d \in \mathbb{Z}_{\geq 0}`, the $`d^\text{th}` plurigenus of $`X` is $`P_d \colonequals \dim H^0(X, K^{\otimes d})`. The global sections of $`K^{\otimes d}` define a rational map

$$`\varphi_d: X \to \mathbb{P}(H^0(X,K^{\otimes d})) \cong \mathbb{P}^{P_d-1} \, .`

The Kodaira dimension $`\kappa(X)` is defined to be $`-1` if $`P_d = 0` for all $`d`, and

$$`\kappa(X) \colonequals \sup_d \, \dim(\varphi_d(X))`

otherwise.
:::

:::definition "ag.minimal_field" (lean := "AlgebraicGeometry.Scheme.fieldsOfDefinition, AlgebraicGeometry.Scheme.IsMinimalFieldOfDefinition, AlgebraicGeometry.Scheme.top_mem_fieldsOfDefinition, AlgebraicGeometry.Scheme.isUpperSet_fieldsOfDefinition, AlgebraicGeometry.Scheme.mem_fieldsOfDefinition_pullback")
*Minimal field of definition.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.minimal_field))

Let $`V/k` be an {bpref "ag.variety"}[algebraic variety] defined over a {bpref "ring.field"}[field] $`k` and let $`S` be the set of subfields $`k_0\subseteq k`  for which there exists an algebraic variety $`V_0/k_0` whose {bpref "ag.base_change"}[base change] to $`k` is isomorphic to $`V`.

Any field $`k_0\in S` that contains no other elements of $`S` is a *minimal field of definition* for $`V`.

In general, an algebraic variety may have more than one minimal field of definition; this does not occur for elliptic curves but it does occur for curves  of {bpref "ag.curve.genus"}[genus] 2.

Depends on: {uses "ag.base_change"}[] {uses "ag.curve.genus"}[] {uses "ag.variety"}[] {uses "ring.field"}[]
:::

:::definition "ag.modcurve.x0"
*Modular curve $`X_0(N)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.modcurve.x0))

Let $`N \ge 1`. The \*modular curve\* $`X_0(N)` is an {bpref "ag.curve"}[algebraic curve] defined over $`\Q` (or even $`\Z[1/N]`) whose points over any algebraically closed field of characteristic not dividing $`N` correspond to isomorphism classes of pairs $`(E,\phi)`, where $`E` is an {bpref "ec"}[elliptic curve] and $`\phi` is an {bpref "ec.isogeny"}[isogeny] with domain $`E` and kernel a cyclic group of order $`N`, with the exception of particular points called \*cusps\* which correspond to degenerate such pairs.

The complex manifold $`X_0(N)(\C)` is biholomorphic to the quotient $`\Gamma_0(N) \backslash \mathcal{H}^*` of the {bpref "mf.upper_half_plane"}[completed upper half plane].

Depends on: {uses "ag.curve"}[] {uses "ec"}[] {uses "ec.isogeny"}[] {uses "mf.upper_half_plane"}[]
:::

:::definition "ag.modcurve.x1"
*Modular curve $`X_1(N)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.modcurve.x1))

Let $`N \ge 1`. The \*modular curve\* $`X_1(N)` is an {bpref "ag.curve"}[algebraic curve] defined over $`\Q` (or even $`\Z[1/N]`) whose points over any algebraically closed field $`k` of characteristic not dividing $`N` correspond to isomorphism classes of pairs $`(E,P)`, where $`E` is an {bpref "ec"}[elliptic curve] over $`k` and $`P \in E(k)` is a torsion point of order exactly $`N`, with the exception of particular points called \*cusps\* which correspond to degenerate such pairs.  If $`N \ge 4`, the same description of points is valid even if $`k` is not algebraically closed.

The complex manifold $`X_1(N)(\C)` is biholomorphic to the quotient $`\Gamma_1(N) \backslash \mathcal{H}^*` of the {bpref "mf.upper_half_plane"}[completed upper half plane].

There is an action of the group $`(\Z/N\Z)^*` on $`X_1(N)`,
in which $`c \bmod N` maps $`(E,P)` to $`(E,cP)`.
The subgroup $`\{\pm 1\}` acts trivially, because $`(E,-P)` is isomorphic to $`(E,P)` via $`[-1]`.
The quotient of $`X_1(N)` by $`(\Z/N\Z)^* / \{\pm1\}` is the
{bpref "ag.modcurve.x0"}[modular curve $`X_0(N)`].

Depends on: {uses "ag.curve"}[] {uses "ag.modcurve.x0"}[] {uses "ec"}[] {uses "mf.upper_half_plane"}[]
:::

:::definition "ag.modcurve.xnsp"
*Modular curve $X\_\{\text\{ns.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.modcurve.xnsp))

Let $`N \ge 1`. The curve $`X_{\text{ns}}^{+}(N)` is the {bpref "modcurve"}[modular curve] $`X(\Gamma_{\text{ns}}^{+}(N))` where $`\Gamma_{\text{ns}}^{+}(N)` is the normalizer of the {bpref "gl2.nonsplit_cartan"}[non-split Cartan subgroup] $`\Gamma_{\text{ns}}(N)`.

Depends on: {uses "gl2.nonsplit_cartan"}[] {uses "modcurve"}[]
:::

:::definition "ag.mordell_weil" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety")
*Mordell-Weil group of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.mordell_weil))

The *Mordell-Weil group* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a {bpref "nf"}[number field] $`K` is its group of $`K`-rational points $`A(K)`.

Weil, building on Mordell's theorem for elliptic curves over $`\Q`, proved that the abelian group $`A(K)` is finitely generated.  Thus

$$`A(K)\simeq \Z^r \oplus T,`

where $`r` is a nonnegative integer called the *Mordell-Weil rank* of $`A`, and $`T` is a finite abelian group called the *torsion subgroup*.

The torsion subgroup $`T` is the product of at most $`2g` cyclic groups, where $`g` is the {bpref "ag.dimension"}[dimension] of $`A`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[]
:::

:::definition "ag.plane_model"
*Plane model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.plane_model))

A *plane model* of a smooth projective curve $`X` is a closed curve $`f(x,y,z)=0` in $`\mathbb{P}^2` that is birational to $`X`.  Such a model is *singular* if the zero locus of $`f` and its partial derivatives is non-empty, otherwise it is *smooth*.
:::

:::definition "ag.potential_good_reduction" (lean := "AlgebraicGeometry.Scheme.HasPotentialGoodReductionAt, AlgebraicGeometry.Scheme.HasGoodReductionAt, WeierstrassCurve.HasPotentialGoodReduction")
*Potential good reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.potential_good_reduction))

A smooth proper {bpref "ag.variety"}[variety] $`X` over a {bpref "nf"}[number field] $`K` is said to have *potential good reduction* at a {bpref "nf.prime"}[prime] $`\mathfrak{p}` if there is a finite extension $`L \supset K` such that the {bpref "ag.base_change"}[base change] $`X_L` has {bpref "ag.good_reduction"}[good reduction] at all primes $`\mathfrak{q}` of $`L` above $`\mathfrak{p}`.

Depends on: {uses "ag.base_change"}[] {uses "ag.good_reduction"}[] {uses "ag.variety"}[] {uses "nf"}[] {uses "nf.prime"}[]
:::

:::definition "ag.primitive" (lean := "AlgebraicGeometry.Scheme.IsBaseChangeFromSubfield, AlgebraicGeometry.Scheme.isBaseChangeFromSubfield_iff, AlgebraicGeometry.Scheme.IsMinimalFieldOfDefinition")
*Primitive algebraic variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.primitive))

An {bpref "ag.variety"}[algebraic variety] is *primitive* if it is not a {bpref "ag.base_change"}[base-change] of an algebraic variety defined over a subfield.

Depends on: {uses "ag.base_change"}[] {uses "ag.variety"}[]
:::

:::definition "ag.projective_space" (lean := "Projectivization")
*Projective space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.projective_space))

*Projective space* $`\mathbb{P}^n(K)` of {bpref "ag.dimension"}[dimension] $`n` over a {bpref "ring.field"}[field] $`K` is the set $`(K^{n+1}\setminus\{0\})/{}\sim{}`, where

$$`(x_0,x_1,\dots,x_n) \sim (y_0,y_1,\dots,y_n) \iff x_0=\lambda y_0, \dots, x_n=\lambda y_n\quad\text{for some}\ \lambda\in K^*.`

This is also known as the *projectivization* of the vector space $`K^{n+1}`.

The equivalence class of $`(x_0,x_1,\dots,x_n)` in $`\mathbb{P}^n(K)` is denoted by $`(x_0:x_1:\dots:x_n)`, and the $`x_i` are called *homogeneous coordinates*.  Thus

$$`\mathbb{P}^n(K) = \{(x_0:\dots:x_n)\mid x_0,\dots,x_n\in K,\ \text{not all zero}\}.`

Depends on: {uses "ring.field"}[]
:::

:::definition "ag.quotient_curve"
*Quotient curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.quotient_curve))

Let $`X` be an {bpref "ag.curve"}[algebraic curve] and let $`H` be a finite subgroup of its {bpref "g2c.aut_grp"}[automorphism group].

The *quotient curve* $`X/H` is the algebraic curve obtained by identifying points of $`X` that lie in the same $`H`-orbit (equations defining $`X/H` as an {bpref "ag.variety"}[algebraic variety] of dimension one can be constructed from the equations defining $`X` and the automorphisms in $`H`).

The natural projection $`X\to X/H` that sends each point on $`X` to its $`H`-orbit is a surjective morphism

Depends on: {uses "ag.curve"}[] {uses "ag.variety"}[] {uses "g2c.aut_grp"}[]
:::

:::definition "ag.real_endomorphism_algebra" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.End")
*Real endomorphism algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.real_endomorphism_algebra))

The *real endomorphism algebra* of an abelian variety $`A` is the $`\R`-algebra $`\textrm{End}(A)\otimes\R`, where $`\textrm{End}(A)` is the {bpref "ag.endomorphism_ring"}[endomorphism ring] of $`A`.

Depends on: {uses "ag.endomorphism_ring"}[]
:::

:::definition "ag.real_geom_endomorphism_algebra" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.End, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange")
*Real geometric endomorphism algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.real_geom_endomorphism_algebra))

The *real geometric endomorphism algebra* of an abelian variety $`A` over a field $`F` is the $`\R`-algebra $`\textrm{End}(A_{\overline{F}})\otimes\R`, where $`\textrm{End}(A_{\overline{F}})` is the {bpref "ag.geom_endomorphism_ring"}[geometric endomorphism ring] of $`A`.

Depends on: {uses "ag.geom_endomorphism_ring"}[]
:::

:::definition "ag.real_multiplication" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.HasRealMultiplication, TauCeti.AlgebraicGeometry.AbelianVariety.HasNontrivialRealMultiplication, TauCeti.AlgebraicGeometry.AbelianVariety.hasRealMultiplication_congr, TauCeti.AlgebraicGeometry.AbelianVariety.EndAlgebra")
*Real multiplication.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.real_multiplication))

An {bpref "ag.abelian_variety"}[abelian variety] is said to have *real multiplication* (RM) if its {bpref "ag.endomorphism_algebra"}[endomorphism algebra] is a totally real (number) field.  (In most situations, we exclude the trivial case of RM by $`\Q`.)

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_algebra"}[]
:::

:::definition "ag.regulator"
*Regulator of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.regulator))

The *regulator* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` defined over a {bpref "nf"}[number field] $`K,` denoted $`\operatorname{Reg}(A/K)`, is the volume of $`A(K)/A(K)_{tor}` with respect to the *height pairing* $`\langle -,-\rangle` associated to the {bpref "ag.canonical_height"}[canonical height] $`\hat{h}`, i.e. $`\langle P,Q\rangle = \frac{1}{2}(\hat{h}(P+Q)-\hat{h}(P)-\hat{h}(Q))`.

If the {bpref "ag.mordell_weil"}[Mordell-Weil group] $`A(K)` has rank $`r` and $`P_1, \ldots, P_r \in E(K)` generate $`A(K)/A(K)_{\text{tors}}`, then

$$`\operatorname{Reg}(A/K) = \left|\det (\langle P_i, P_j \rangle )_{1\leq i,j \leq r}\right|,`

which is independent of the choice of generators.

If $`A(K)` has rank $`0`, then $`\operatorname{Reg}(A/K)=1`.
If $`A(K)` has rank $`1`, then $`\operatorname{Reg}(A/K)` equals the {bpref "ag.canonical_height"}[canonical height] $`\hat{h}(P)` of a point $`P` generating $`A(K)/A(K)_{\text{tors}}`.

This is a generalisation of the {bpref "ec.regulator"}[regulator of an elliptic curve].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.canonical_height"}[] {uses "ag.mordell_weil"}[] {uses "ec.regulator"}[] {uses "nf"}[]
:::

:::definition "ag.riemann_surface" (lean := "IsManifold, ChartedSpace, ConnectedSpace, T2Space")
*Riemann surface.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.riemann_surface))

A *Riemann surface* is a connected complex manifold of dimension one.  Compact Riemann surfaces can be identified with smooth projective curves over $`\C`.
:::

:::definition "ag.sato_tate_group"
*Sato-Tate group (of a motive).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.sato_tate_group))

The Sato-Tate group of a motive over a number field is a compact (but often disconnected) Lie group which conjecturally governs the variation of Euler factors of the L-function associated to this motive. For example, for (the 1-motive of) a generic abelian variety of dimension $`g`, this group is $`\mathrm{USp}(2g)`.

For an elliptic curve $`E` over a number field $`K`, the Sato-Tate group equals $`\mathrm{SU}(2)` if $`E` does not have complex multiplication. Otherwise, one gets $`\mathrm{SO}(2)` if $`E` has CM defined over $`K`, and the normalizer of $`\mathrm{SO}(2)` in $`\mathrm{SU}(2)` if $`E` has CM not defined over $`K`.

For an abelian surface $`A` over a number field $`K`, there are 52 possible Sato-Tate groups as classified by Fité-Kedlaya-Rotger-Sutherland ; of these, 34 can occur for $`K = \mathbb{Q}`. The typical case $`\mathrm{USp}(4)` occurs when $`\mathrm{End}(A_{\overline{K}}) = \mathbb{Z}`.
:::

:::definition "ag.selmer_group" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.numberFieldSelmerGroup, TauCeti.AlgebraicGeometry.AbelianVariety.mem_numberFieldSelmerGroup_iff, TauCeti.AlgebraicGeometry.AbelianVariety.kummerCondition, TauCeti.AlgebraicGeometry.AbelianVariety.torsionRes, TauCeti.AlgebraicGeometry.AbelianVariety.TorsionCoeff")
*Selmer group of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.selmer_group))

Let $`A` be an {bpref "ag.abelian_variety"}[abelian variety] over a {bpref "nf"}[number field] $`K`.
Let $`n \ge 1`.
Let $`G_K` be the {bpref "group.galois.absolute"}[absolute Galois group] of $`K`.
There is a connecting homomorphism $`A(K)/nA(K) \to H^1(G_K,A[n])`, and likewise a homomorphism $`A(K_v)/nA(K_v) \to H^1(G_{K_v},A[n])` for each {bpref "nf.place"}[place] $`v` of $`K`.
The *$`n`-Selmer group* $`\operatorname{Sel}_n A` is the set of classes in $`H^1(G_K, A[n])` whose image in $`H^1(G_{K_v},A[n])` lies in the image of $`A(K_v)/nA(K_v) \to H^1(G_{K_v},A[n])` for every place $`v`, including the {bpref "nf.absolute_value"}[archimedean] places.

One may also define the Selmer group for any {bpref "av.isogeny"}[isogeny] from $`A` to another abelian variety over a global field.

Any Selmer group is finite and effectively computable. In fact, all known techniques for computing the {bpref "ag.mordell_weil"}[Mordell-Weil group] of $`A` involve computing a Selmer group.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.mordell_weil"}[] {uses "av.isogeny"}[] {uses "group.galois.absolute"}[] {uses "nf"}[] {uses "nf.absolute_value"}[] {uses "nf.place"}[]
:::

:::definition "ag.shimura_variety" (lean := "IsHermitianSymmetricDomain, biholomorphismGroup, Subgroup.IsDefinedOverRat, IsArithmeticSubgroup, IsConnectedShimuraVarietyGroup, ConnectedShimuraVariety")
*Shimura variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.shimura_variety))

There are a number of different ways to define a Shimura variety.

One definition starts with connected complex manifolds such that for every point on the manifold there is an involution fixing only that point.  If this manifold is isomorphic to a bounded open subset of $`\C^n` for some $`n`, it is called a Hermitian symmetric domain (or space).

Then, *(connected) Shimura varieties* are quotients of Hermitian symmetric domains by torsion-free subgroups of the group of automorphisms of the domain.
:::

:::definition "ag.simple" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsSimple, TauCeti.AlgebraicGeometry.AbelianVariety.isSimple_congr, TauCeti.AlgebraicGeometry.AbelianVariety.not_isSimple_trivial, TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogenous, TauCeti.AlgebraicGeometry.AbelianVariety.prod")
*Simple.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.simple))

An {bpref "ag.abelian_variety"}[abelian variety] is *simple* if it is nonzero and not isogenous to a product of abelian varieties of lower dimension.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "ag.singular_point" (lean := "AlgebraicGeometry.Scheme.Hom.smoothLocus, Algebra.smoothLocus, Algebra.smoothLocus_eq_compl_support_inter")
*Non-singular point (definition).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.singular_point))

Let $`V` be a variety over a perfect field $`F`. A point $`P` of $`V` is *non-singular* if the module of differentials of $`V` is locally free at $`P`.  According to the Jacobian criterion, if $`V` is defined in a neighborhood of $`P` by affine polynomial equations $`f_1(X_1, \ldots, X_n) = \ldots =f_r(X_1, \ldots, X_n)=0`, then $`V` is non-singular at $`P` if the Jacobian matrix $`\left( \frac{\partial f_i}{\partial X_j} \right)_{ij}` has the same rank as the codimension of $`V` in $`\mathbb{A}^n`.
:::

:::definition "ag.splitting_field" (lean := "TauCeti.torusSplittingField, TauCeti.IsTorusSplittingField, TauCeti.IsTorusSplitOver, TauCeti.IsTorusSplittingField.torusSplittingField_eq, TauCeti.torusCommHopfAlgProperty")
*Splitting field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.splitting_field))

The *splitting field* of an algebraic torus $`T` is the minimal {bpref "nf.is_galois"}[Galois] extension of its {bpref "ag.base_field"}[base field] over which $`T` becomes isomorphic to a power of the multiplicative group $`\mathbb{G}_m`.

Depends on: {uses "ag.base_field"}[] {uses "nf.is_galois"}[]
:::

:::definition "ag.tate_shafarevich" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.tateShafarevichGroup, TauCeti.AlgebraicGeometry.AbelianVariety.mem_tateShafarevichGroup_iff, TauCeti.AlgebraicGeometry.AbelianVariety.pointRes")
*Tate-Shafarevich group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.tate_shafarevich))

The *Tate-Shafarevich group* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a {bpref "nf"}[number field] $`K` is

$$`\Sha(A) = \ker\Bigl(H^1(G_K,A) \to \prod_v H^1(G_{K_v},A_{K_v})\Bigr),`

where $`G_K` is the {bpref "group.galois.absolute"}[absolute Galois group] of $`K`,
and $`v` ranges over all {bpref "nf.place"}[places] of $`K`, including the {bpref "nf.absolute_value"}[archimedean] places.

It classifies {bpref "g2c.locally_solvable"}[locally solvable] {bpref "ag.torsor"}[principal homogeneous spaces] of $`A`.

It is a {bpref "group.torsion"}[torsion abelian group] that is conjectured to be finite.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.torsor"}[] {uses "g2c.locally_solvable"}[] {uses "group.galois.absolute"}[] {uses "group.torsion"}[] {uses "nf"}[] {uses "nf.absolute_value"}[] {uses "nf.place"}[]
:::

:::definition "ag.torsor" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsPrincipalHomogeneousSpace, TauCeti.AlgebraicGeometry.AbelianVariety.orbitMap, TauCeti.AlgebraicGeometry.AbelianVariety.sepClosureOver")
*Principal homogeneous space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.torsor))

A *principal homogeneous space* (or *torsor*) of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a field $`k` is a {bpref "ag.variety"}[variety] $`X` equipped with an $`A`-action such that ($`X_{\overline{k}}` with the induced $`A_{\overline{k}}`-action) is isomorphic to ($`A_{\overline{k}}` with  $`A_{\overline{k}}`-action given by translation).

The set of isomorphism classes of principal homogeneous spaces of $`A` is in bijection with the Galois cohomology group $`H^1(k,A) = H^1(G_k,A(\overline{k}))`, where $`\overline{k}` is a separable closure of $`k`, and $`G_k` is the {bpref "group.galois.absolute"}[absolute Galois group] $`\Gal(\overline{k}/k)`, so it has the structure of an abelian group.

For a principal homogeneous space $`X`, the following are equivalent:

1. $`X` has a rational point;
2. there is an $`A`-equivariant isomorphism $`X \to A`;
3. the class of $`X` in $`H^1(k,A)` is $`0`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.variety"}[] {uses "group.galois.absolute"}[]
:::

:::definition "ag.variety" (lean := "MvPolynomial.IsAffineAlgebraicSet, MvPolynomial.IsAffineVarietyOver, MvPolynomial.IsProjectiveAlgebraicSet, MvPolynomial.IsProjectiveVarietyOver, AlgebraicGeometry.Scheme.IsVarietyOver")
*Algebraic variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.variety))

There are two main kinds of *algebraic varieties*, \*affine varieties\* and \*projective varieties\*.   Both are defined as the set of common zeros of a collection of polynomials.
Let $`K` be a {bpref "ring.field"}[field] with algebraic closure $`\overline{K}`.

An *affine algebraic set* is a subset of {bpref "ag.affine_space"}[affine space] $`\mathbb{A}^n(\overline{K})` of the form

$$`V(I) = \{P \in \mathbb{A}^n(\overline{K}) : f(P) = 0\text{ for all }f \in I\}`

where $`I \subseteq \overline{K}[x_1,\dots,x_n]` is an ideal.  Given an affine algebraic set $`V`, its *defining ideal* is

$$`I(V) = \{ f \in \overline{K}[x_1,\dots,x_n] : f(P)=0\text{ for all }P \in V\}.`

An *affine variety* over $`\overline{K}` is an affine algebraic set whose defining ideal $`I \subseteq \overline{K}[x_1,\dots,x_n]` is a {bpref "ring.prime_ideal"}[prime ideal].  An *affine variety* over $`K` is an affine variety over $`\overline{K}` whose defining ideal can be generated by polynomials in $`K[x_1,\dots,x_n]`.

We define projective notions similarly.  A *projective algebraic set* is a subset of {bpref "ag.projective_space"}[projective space] $`\mathbb{P}^n(\overline{K})` defined by a \*homogeneous\* ideal $`I \subseteq \overline{K}[x_1,\dots,x_n]`.  A *projective variety* over $`\overline{K}` is a projective algebraic set whose defining ideal is a homogeneous {bpref "ring.prime_ideal"}[prime ideal].  A *projective variety* over $`K` is a projective variety over $`\overline{K}` whose defining ideal can be generated by homogeneous polynomials in $`K[x_1,\dots,x_n]`.

Depends on: {uses "ag.affine_space"}[] {uses "ag.projective_space"}[] {uses "ring.field"}[] {uses "ring.prime_ideal"}[]
:::
