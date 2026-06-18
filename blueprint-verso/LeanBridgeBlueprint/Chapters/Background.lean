import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Background" =>

This chapter lists the LMFDB definitions relating to *background*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "af"
*Arithmetic function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af))

An *arithmetic function* is a complex-valued function whose domain is the positive integers.
:::

:::definition "af.bernoulli_numbers"
*Bernoulli numbers.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.bernoulli_numbers))

The *Bernoulli numbers* are the rational numbers $`B_n` that appear as coefficients of the formal power series

$$`\frac{T}{e^T-1}=\sum_{n\ge 0}B_n\frac{T^n}{n!},`

which has radius of convergence $`2\pi`.
:::

:::definition "af.divisor_function"
*Divisor function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.divisor_function))

A *divisor function* is a {bpref "af.multiplicative"}[multiplicative] {bpref "af"}[arithmetic function] of the form

$$`\sigma_{\tau}(n)=\sum_{d\mid n}d^\tau,`

for some fixed $`\tau\in\mathbb{C}`.

Depends on: {uses "af"}[] {uses "af.multiplicative"}[]
:::

:::definition "af.multiplicative"
*Multiplicative arithmetic function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.multiplicative))

An arithmetic function $`f:\mathbb{Z}_{>0}\to \C` is *multiplicative* if $`f(mn)=f(m)f(n)` for all coprime integers $`m,n>0`, and is not the zero-function (in particular, $`f(1)=1`).
:::

:::definition "ag.abelian_variety"
*Abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.abelian_variety))

An *abelian variety* defined over the field $`K` is a smooth connected projective {bpref "ag.variety"}[variety] equipped with the structure of an algebraic group. The group law is automatically commutative.

An abelian variety of dimension 1 is the same as an {bpref "ec"}[elliptic curve].

Depends on: {uses "ag.variety"}[] {uses "ec"}[]
:::

:::definition "ag.affine_space"
*Affine space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.affine_space))

*Affine space* $`\mathbb{A}^n(K)` of {bpref "ag.dimension"}[dimension] $`n` over a {bpref "ring.field"}[field] $`K` is the set $`K^n`.

If $`P=(x_1,\dots,x_n)` is a point in $`\mathbb{A}^n(K)`, the $`x_i` are called the \*affine coordinates\* of $`P`.  Thus

$$`\mathbb{A}^n(K) = \{(x_1,\dots,x_n)\mid x_1,\dots,x_n\in K\}.`

Depends on: {uses "ring.field"}[]
:::

:::definition "ag.base_change"
*Base change.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.base_change))

Let $`V` be an {bpref "ag.variety"}[algebraic variety] defined over a {bpref "ring.field"}[field] $`K`. If $`L/K` is a field extension, then any set of equations that define $`V` over $`K` can be used to define an algebraic variety over $`L`, the *base change* of $`V` from $`K` to $`L` (typically denoted $`V_L`).

An algebraic variety over a field $`L` is said to be a *base change* if it is the base change of an algebraic variety defined over a proper subfield of $`L`, equivalently, if its {bpref "ag.base_field"}[base field] is not a {bpref "ag.minimal_field"}[minimal field of definition].

Depends on: {uses "ag.variety"}[] {uses "ring.field"}[]
:::

:::definition "ag.base_field"
*Base field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.base_field))

The *base field*, of an {bpref "ag.abelian_variety"}[algebraic variety] is the field over which it is defined; it necessarily contains the coefficients of a set of defining equations for the variety, but it is not necessarily a {bpref "ag.minimal_field"}[minimal field of definition].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.minimal_field"}[]
:::

:::definition "ag.complex_multiplication"
*Complex multiplication.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.complex_multiplication))

A {bpref "ag.geom_simple"}[simple] {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] $`g` is said to have *complex multiplication* (CM) if its
{bpref "ag.endomorphism_algebra"}[endomorphism algebra] is a {bpref "nf.cm_field"}[CM field] of {bpref "nf.degree"}[degree] $`2g`, or equivalently, if its {bpref "ag.endomorphism_ring"}[endomorphism ring] is an {bpref "nf.order"}[order] in a CM field of degree $`2g`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "ag.endomorphism_algebra"}[] {uses "ag.endomorphism_ring"}[] {uses "ag.geom_simple"}[] {uses "nf.cm_field"}[] {uses "nf.degree"}[] {uses "nf.order"}[]
:::

:::definition "ag.curve"
*Algebraic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.curve))

An *algebraic curve* is an {bpref "ag.variety"}[algebraic variety] of dimension $`1.`

Depends on: {uses "ag.variety"}[]
:::

:::definition "ag.curve.genus"
*Genus of a smooth curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.curve.genus))

The *genus* of a smooth projective geometrically integral curve $`C` defined over a field $`k` is the dimension of the $`k`-vector space of regular differentials $`H^0(C, \omega_C)`.  When $`k=\C` this coincides with the topological genus of the corresponding {bpref "ag.riemann_surface"}[Riemann surface].

The quantity defined above is sometimes also called the *algebraic genus* or the *geometric genus* of $`C`. Because of our assumption on the smoothness of $`C`, it coincides with the *arithmetic genus* $`H^1(C,\mathcal{O}_C)`.

Depends on: {uses "ag.riemann_surface"}[]
:::

:::definition "ag.curve.smooth"
*Smoothness of an algebraic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.curve.smooth))

Let $`C` be an {bpref "ag.curve"}[algebraic curve] over a perfect field $`k`. Then $`C` is called *smooth* if the extension of $`C` to the algebraic closure of $`k` is {bpref "ag.singular_point"}[non-singular] at all of its points.

Depends on: {uses "ag.curve"}[] {uses "ag.singular_point"}[]
:::

:::definition "ag.dimension"
*Dimension of an algebraic variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.dimension))

The *dimension* of an {bpref "ag.variety"}[algebraic variety] $`V` is the maximal length $`d` of a chain

$$`V_0 \subset V_1 \subset \cdots \subset V_d`

of distinct {bpref "ag.irreducible"}[irreducible] subvarieties of $`V`.

Depends on: {uses "ag.irreducible"}[] {uses "ag.variety"}[]
:::

:::definition "ag.endomorphism_algebra"
*Endomorphism algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.endomorphism_algebra))

The *endomorphism algebra* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` is the $`\Q`-algebra $`\textrm{End}(A)\otimes\Q`, where $`\textrm{End}(A)` is the {bpref "ag.endomorphism_ring"}[endomorphism ring] of $`A`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_ring"}[]
:::

:::definition "ag.endomorphism_ring"
*Endomorphism ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.endomorphism_ring))

An *endomorphism* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a field $`k` is a homomorphism $`\varphi \colon A \to A` defined over $`k`.  The set of endomorphisms of an abelian variety $`A` can be given the structure of a ring in which addition is defined pointwise (using the group operation of $`A`) and multiplication is composition; this ring is called the *endomorphism ring* of $`A`, denoted $`\textrm{End}(A)`.

For endomorphisms defined over an extension of $`k`, we instead speak about the {bpref "ag.geom_endomorphism_ring"}[geometric endomorphism ring].

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "ag.geom_endomorphism_ring"
*Geometric endomorphism ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.geom_endomorphism_ring))

For an abelian variety $`A` over a field $`F`, the *geometric endomorphism ring* of $`A` is $`\End(A_{\overline{F}})`, the {bpref "ag.endomorphism_ring"}[endomorphism ring] of the base change of $`A` to an algebraic closure $`\overline{F}` of $`F`.

Depends on: {uses "ag.endomorphism_ring"}[]
:::

:::definition "ag.geom_simple"
*Geometrically simple.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.geom_simple))

An {bpref "ag.abelian_variety"}[abelian variety] over a field $`k` is *geometrically (or absolutely) simple* if it is {bpref "ag.simple"}[simple] when viewed as a variety over $`\bar k`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.simple"}[]
:::

:::definition "ag.hyperelliptic_curve"
*Hyperelliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.hyperelliptic_curve))

A *hyperelliptic curve* $`X` over a field $`k` is a smooth projective  {bpref "ag.curve"}[algebraic curve] of {bpref "ag.curve.genus"}[genus] $`g\ge 2` that admits a 2-to-1 map $`X\to \mathbb{P}^1` defined over the algebraic closure $`\bar k`.

If $`X` is a hyperelliptic curve over $`k`, then the canonical map $`X \to \mathbb{P}^{g-1}` is a 2-to-1 map onto a smooth genus 0 curve $`Y`.  The curve $`Y` is isomorphic to $`\mathbb{P}^1` if and only if $`Y` has a $`k`-rational point.

If $`X` admits a 2-to-1 map to $`\mathbb{P}^1` that is defined over $`k`, then $`X` has a *Weierstrass model* of the form $`y^2+h(x)y=f(x)`; when the characteristic of $`k` is not $`2` one can complete the square to put this model in the form $`y^2=f(x)`.

In general, there is always a model for $`X` in $`\mathbb{P}^3` of the form

$$`h(x,y,z)=0\qquad w^2=f(x,y,z)`

where $`h(x,y,z)` is a homogeneous polynomial of degree $`2` (a *conic*) and $`f(x,y,z)` is a homogeneous polynomial of degree $`g+1`.

Depends on: {uses "ag.curve"}[] {uses "ag.curve.genus"}[]
:::

:::definition "ag.irreducible"
*Irreducible variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.irreducible))

A {bpref "ag.variety"}[variety] defined over a field $`F` is *irreducible* if it is nonempty and cannot be decomposed as the union of two strictly smaller varieties over $`F`. It is *geometrically irreducible* if it remains irreducible when seen as a variety over the algebraic closure of $`F`.

Depends on: {uses "ag.variety"}[]
:::

:::definition "ag.jacobian"
*Jacobian of a curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.jacobian))

The *Jacobian* of a (smooth, projective, geometrically integral) curve $`X` of genus $`g` over a field $`k` is a $`g`-dimensional principally polarized {bpref "ag.abelian_variety"}[abelian variety] $`J` that is canonically associated to $`X`.

If $`X` has a $`k`-rational point, then $`J(k)` is isomorphic to the group of degree zero divisors on $`X` modulo linear equivalence.  A choice of rational point on $`X` determines a morphism $`X \to J` called an Abel-Jacobi map; it is an embedding if and only if $`g \ge 1`, and an isomorphism if and only if $`g=1`.

The Torelli theorem states that if $`X` and $`Y` are curves whose Jacobians are isomorphic as \*principally polarized\* abelian varieties, then $`X` and $`Y` are isomorphic.  It is possible, however, for non-isomorphic curves to have Jacobians that are isomorphic as unpolarized abelian varieties.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "ag.minimal_field"
*Minimal field of definition.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.minimal_field))

Let $`V/k` be an {bpref "ag.variety"}[algebraic variety] defined over a {bpref "ring.field"}[field] $`k` and let $`S` be the set of subfields $`k_0\subseteq k`  for which there exists an algebraic variety $`V_0/k_0` whose {bpref "ag.base_change"}[base change] to $`k` is isomorphic to $`V`.

Any field $`k_0\in S` that contains no other elements of $`S` is a *minimal field of definition* for $`V`.

In general, an algebraic variety may have more than one minimal field of definition; this does not occur for elliptic curves but it does occur for curves  of {bpref "ag.curve.genus"}[genus] 2.

Depends on: {uses "ag.base_change"}[] {uses "ag.curve.genus"}[] {uses "ag.variety"}[] {uses "ring.field"}[]
:::

:::definition "ag.mordell_weil"
*Mordell-Weil group of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.mordell_weil))

The *Mordell-Weil group* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a {bpref "nf"}[number field] $`K` is its group of $`K`-rational points $`A(K)`.

Weil, building on Mordell's theorem for elliptic curves over $`\Q`, proved that the abelian group $`A(K)` is finitely generated.  Thus

$$`A(K)\simeq \Z^r \oplus T,`

where $`r` is a nonnegative integer called the *Mordell-Weil rank* of $`A`, and $`T` is a finite abelian group called the *torsion subgroup*.

The torsion subgroup $`T` is the product of at most $`2g` cyclic groups, where $`g` is the {bpref "ag.dimension"}[dimension] of $`A`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[]
:::

:::definition "ag.projective_space"
*Projective space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.projective_space))

*Projective space* $`\mathbb{P}^n(K)` of {bpref "ag.dimension"}[dimension] $`n` over a {bpref "ring.field"}[field] $`K` is the set $`(K^{n+1}\setminus\{0\})/{}\sim{}`, where

$$`(x_0,x_1,\dots,x_n) \sim (y_0,y_1,\dots,y_n) \iff x_0=\lambda y_0, \dots, x_n=\lambda y_n\quad\text{for some}\ \lambda\in K^*.`

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

:::definition "ag.riemann_surface"
*Riemann surface.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.riemann_surface))

A *Riemann surface* is a connected complex manifold of dimension one.  Compact Riemann surfaces can be identified with smooth projective curves over $`\C`.
:::

:::definition "ag.simple"
*Simple.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.simple))

An {bpref "ag.abelian_variety"}[abelian variety] is *simple* if it is nonzero and not isogenous to a product of abelian varieties of lower dimension.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "ag.singular_point"
*Non-singular point (definition).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.singular_point))

Let $`V` be a variety over a perfect field $`F`. A point $`P` of $`V` is *non-singular* if the module of differentials of $`V` is locally free at $`P`.  According to the Jacobian criterion, if $`V` is defined in a neighborhood of $`P` by affine polynomial equations $`f_1(X_1, \ldots, X_n) = \ldots =f_r(X_1, \ldots, X_n)=0`, then $`V` is non-singular at $`P` if the Jacobian matrix $`\left( \frac{\partial f_i}{\partial X_j} \right)_{ij}` has the same rank as the codimension of $`V` in $`\mathbb{A}^n`.
:::

:::definition "ag.variety"
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

:::definition "alg.binary_operation"
*Binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation))

A *binary operation* on a set $`S` is a function $`S\times S\to S`.

If the operation is denoted by $`*`, then the output of this function applied to $`(s_1,s_2)` is typically denoted $`s_1*s_2`.
:::

:::definition "alg.binary_operation.associative"
*Associative binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation.associative))

If $`*` is a {bpref "alg.binary_operation"}[binary operation] on a set $`A`, then $`*` is *associative* on $`A` if for all $`a,b,c\in A`,

$$`a*(b*c)=(a*b)*c.`
/div>

Depends on: {uses "alg.binary_operation"}[]
:::

:::definition "alg.binary_operation.commutative"
*Commutative binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation.commutative))

If $`*` is a {bpref "alg.binary_operation"}[binary operation] on a set $`A`, then $`*` is *commutative* on $`A` if for all $`a,b\in A`,

$$`a*b=b*a.`

Depends on: {uses "alg.binary_operation"}[]
:::

:::definition "alg.binary_operation.identity"
*Identity for a binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation.identity))

If $`*` is a {bpref "alg.binary_operation"}[binary operation] on a set $`A`, then $`A` has an *identity* element with respect to $`*` if there exists $`e\in A` such that for all $`a\in A`,

$$`a*e = e*a = a.`

Such an identity element $`e`, if it exists, is unique and is thus called *the identity element* of $`A` with respect to $`*`.

Depends on: {uses "alg.binary_operation"}[]
:::

:::definition "alg.binary_operation.inverse"
*Inverse for a binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation.inverse))

If $`*` is a {bpref "alg.binary_operation"}[binary operation] on a set $`A` having {bpref "alg.binary_operation.identity"}[identity element] $`e\in A`, then an element $`a\in A` has an *inverse* in $`A` with respect to $`*` if there exists $`a'\in A` such that

$$`a*a' = a'*a = e.`

Depends on: {uses "alg.binary_operation"}[] {uses "alg.binary_operation.identity"}[]
:::

:::definition "alg.symplectic_isomorphism"
*Symplectic isomorphism.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.symplectic_isomorphism))

Let $`N \ge 1`.  Let $`\mu_N` be the group of $`N`th roots of unity in some algebraically closed field of characteristic not dividing $`N`.  Let $`M` be a free rank $`2` $`\Z/N\Z`-module together with an isomorphism $`\alpha \colon \bigwedge^2 M \stackrel{\sim}\to \mu_N`, or equivalently with a nondegenerate alternating pairing $`M \times M \to \mu_N`.  For example, $`M` could be $`E[N]` for an elliptic curve $`E`, together with the Weil pairing.  Or $`M` could be $`\Z/N\Z \times \mu_N` with the "determinant" pairing $`(a,\gamma),(b,\delta) \mapsto \delta^a/\gamma^b`.

A *symplectic isomorphism* from $`M` to another such structure $`M'` is a $`\Z/N\Z`-module isomorphism $`M \to M'` such that the induced isomorphism $`\bigwedge^2 M \to \bigwedge^2 M'` gets identified via $`\alpha` and $`\alpha'` with the _identity_ $`\mu_N \to \mu_N`.

The same definition makes sense in a context in which each free rank 2 $`\Z/N\Z`-module is enriched with a Galois action to make a Galois module, or replaced by a finite etale group scheme that is $`(\Z/N\Z)^2` etale locally.
:::

:::definition "artin"
*Artin representation (definition).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin))

An *Artin representation* is a continuous homomorphism
$`\rho:\mathrm{Gal}(\overline{\Q}/\Q)\to\GL(V)` from the
{bpref "group.galois.absolute"}[absolute Galois group] of $`\Q` to the automorphism group of a
finite-dimensional $`\C`-vector space $`V`.  Here continuity means that $`\rho` factors through the {bpref "nf.galois_group"}[Galois group] of some finite extension $`K/\Q`. The smallest such $`K` is called the {bpref "artin.number_field"}[Artin field] of $`\rho`.

Depends on: {uses "group.galois.absolute"}[] {uses "nf.galois_group"}[]
:::

:::definition "artin.conductor"
*Conductor of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.conductor))

The *conductor* of an {bpref "artin"}[Artin representation] is a positive integer that measures its ramification.  It can be expressed as a product of local conductors.

Let $`K/\Q` be a {bpref "nf.is_galois"}[Galois] extension and $`\rho:\Gal(K/\Q)\to\GL(V)` an Artin representation.  Then the conductor of $`\rho` is
$`\prod_p p^{f(\rho,p)}`
for non-negative integers $`f(\rho,p)`, where the product is taken over prime numbers $`p`.

To define the exponents $`f(\rho,p)`, fix a {bpref "nf.prime"}[prime] $`\mathfrak{p}` of $`K` above $`p` and consider the corresponding extension of {bpref "lf.padic_field"}[local fields] $`K_{\mathfrak{p}}/\Q_p` with {bpref "gg.galois_group"}[Galois group] $`G`.  Then $`G` has a filtration of higher ramification groups in lower numbering $`G_i`, as defined in Chapter IV of Serre's _Local Fields_ .  In particular, $`G_{-1}=G`, $`G_0` is the {bpref "lf.inertia_group"}[inertia group] of $`K_{\mathfrak{p}}/\Q_p`, and $`G_1` is the {bpref "lf.wild_inertia_group"}[wild inertia group], which is a finite $`p`-group.

Let $`g_i = |G_i|`.  Then

$$`f(\rho, p) = \sum_{i\geq 0} \frac{g_i}{g_0} (\dim(V) - \dim(V^{G_i}))`

where $`V^{G_i}` is the subspace of $`V` fixed by $`G_i`.

Note that if $`p` is {bpref "artin.unramified_primes"}[unramified] in $`K`, then $`f(\rho,p)=0` and conversely, if $`\rho` is faithful and $`p` is ramified in $`K`, then $`f(\rho,p)>0`.

Depends on: {uses "artin"}[] {uses "artin.unramified_primes"}[] {uses "gg.galois_group"}[] {uses "lf.inertia_group"}[] {uses "lf.padic_field"}[] {uses "lf.wild_inertia_group"}[] {uses "nf.is_galois"}[] {uses "nf.prime"}[]
:::

:::definition "artin.number_field"
*Number field associated to an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.number_field))

The *Artin field* is a {bpref "nf"}[number field] associated to an {bpref "artin"}[Artin representation]
$`\rho:\mathrm{Gal}(\overline{\Q}/\Q)\to\GL(V)`
by being the smallest Galois extension $`K/\mathbb{Q}` such that $`\rho` factors through
$`\mathrm{Gal}(K/\Q)`.

Depends on: {uses "artin"}[] {uses "nf"}[]
:::

:::definition "artin.parity"
*Parity of a representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.parity))

An {bpref "artin"}[Artin representation] $`\rho:\Gal(\overline{\Q}/\Q)\to \GL(V)` is *even* or *odd* if $`\det(\rho(c))` equals $`1` or $`-1`, respectively, where $`c` is a complex conjugation.

Depends on: {uses "artin"}[]
:::

:::definition "artin.ramified_primes"
*Ramified prime of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.ramified_primes))

If $`\rho:\Gal(\overline{\Q}/\Q)\to\GL_n(\C)` is an {bpref "artin"}[Artin representation] with {bpref "artin.number_field"}[Artin field] $`K`, then a prime $`p` is *ramified* if it is {bpref "nf.ramified_primes"}[ramified] in $`K/\Q`.

Equivalently, a prime is ramified if the inertia subgroup for a prime above $`p` is not contained in the kernel of $`\rho`.

Depends on: {uses "artin"}[] {uses "artin.number_field"}[] {uses "nf.ramified_primes"}[]
:::

:::definition "artin.unramified_primes"
*Unramified prime of an Artin representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/artin.unramified_primes))

If $`\rho:\Gal(\overline{\Q}/\Q)\to\GL_n(\C)` is an {bpref "artin"}[Artin representation], a prime $`p` is *unramified* if it is not {bpref "artin.ramified_primes"}[ramified].

Equivalently, a prime is unramified if the inertia subgroup for a prime above $`p` in the {bpref "artin.number_field"}[Artin field] of $`\rho` is contained in the kernel of $`\rho`.

Depends on: {uses "artin"}[] {uses "artin.number_field"}[] {uses "artin.ramified_primes"}[]
:::

:::definition "av.isogeny"
*Isogeny of abelian varieties.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.isogeny))

An *isogeny* of {bpref "ag.abelian_variety"}[abelian varieties] is a surjective algebraic group homomorphism with finite kernel.

Two abelian varieties are *isogenous* if there is an isogeny between them. This defines an equivalence relation on the set of isomorphism classes.  Equivalence classes are called isogeny classes.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.simple"
*Simple abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.simple))

An {bpref "ag.abelian_variety"}[abelian variety] is *simple* if it is nonzero and not isogenous to a product of abelian varieties of lower dimension.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "av.tate_module"
*Tate module of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.tate_module))

Let $`p \in \mathbb{Z}_{\geq 0}` be a prime and $`A` an abelian variety of dimension $`g` defined over a field $`K`. The *$`p`-adic Tate module* of $`A` is the inverse limit

$$`T_p(A) = \lim_{\xleftarrow[n \in \mathbb{N}]{}} A[p^n].`

Here for $`m\in\mathbb{Z}_{> 0}`, $`A[m]` denotes the $`m`-torsion subgroup of $`A`, which is the kernel of the multiplication-by-$`m` {bpref "av.isogeny"}[isogeny] of $`A`.

If $`K` has characteristic not equal to $`p`, then $`T_p(A)` is a free $`\Z_p`-module of rank $`2g`. It carries an action of the {bpref "group.galois.absolute"}[absolute Galois group] of $`K`, and thus has an associated Galois representation.

Depends on: {uses "av.isogeny"}[] {uses "group.galois.absolute"}[]
:::

:::definition "av.twist"
*Twist of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/av.twist))

A *twist* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` is an abelian variety $`A'` over the same field that becomes isomorphic to $`A` upon {bpref "ag.base_change"}[base change] to an algebraic closure.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_change"}[]
:::

:::definition "character.dirichlet"
*Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet))

A *Dirichlet character* is a function $`\chi: \Z\to \C` together with a positive integer $`q` called the *modulus* such that $`\chi` is completely multiplicative, i.e. $`\chi(mn)=\chi(m)\chi(n)` for all integers $`m` and $`n`, and $`\chi` is periodic modulo $`q`, i.e. $`\chi(n+q)=\chi(n)` for all $`n`. If $`(n,q)>1` then $`\chi(n)=0`, whereas if $`(n,q)=1`, then $`\chi(n)` is a root of unity. The character $`\chi` is {bpref "character.dirichlet.primitive"}[primitive] if its
{bpref "character.dirichlet.conductor"}[conductor]
is equal to its modulus.
:::

:::definition "character.dirichlet.conductor"
*Conductor of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conductor))

The *conductor* of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` modulo $`q` is the least positive integer $`q_1` dividing $`q` for which $`\chi(n+kq_1)=\chi(n)` for all $`n` and $`n+kq_1` coprime to $`q`.

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "character.dirichlet.galois_orbit"
*Galois orbit of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.galois_orbit))

The *Galois orbit* of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of {bpref "character.dirichlet.modulus"}[modulus] $`q` and {bpref "character.dirichlet.order"}[order] $`n` is the set $`[\chi]:=\{\sigma(\chi): \sigma\in \Gal(\Q(\zeta_n)/\Q)\}`, where $`\sigma(\chi)` denotes the Dirichlet character of modulus $`q` defined by  $`k \mapsto \sigma(\chi(k))`.  The map $`\chi\to \sigma(\chi)` defines a faithful action of the {bpref "nf.galois_group"}[Galois group] $`\Gal(\Q(\zeta_n)/\Q)` on the set of Dirichlet characters of modulus $`q` and order $`n`, each of which has $`\Q(\zeta_n)` as its {bpref "character.dirichlet.value_field"}[field of values].

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.value_field"}[] {uses "nf.galois_group"}[]
:::

:::definition "character.dirichlet.galois_orbit_index"
*Orbit index of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.galois_orbit_index))

The {bpref "character.dirichlet.galois_orbit"}[Galois orbits] of {bpref "character.dirichlet"}[Dirichlet characters] of {bpref "character.dirichlet.modulus"}[modulus] $`q` are ordered as follows.
Let $`\chi` be any character in the Galois orbit $`[\chi]` and define the $`N`-tuple of integers

$$`t([\chi]) := (n,t_1,t_2,\ldots,t_{q-1}) \in \Z^q,`

where $`n` is the {bpref "character.dirichlet.order"}[order] of $`\chi` and $`t_i:=\mathrm{tr}_{\Q(\chi)/\Q}(\chi(i))` is the trace of $`\chi(i)` from the {bpref "character.dirichlet.value_field"}[field of values] of $`\chi` to $`\Q`.  The $`q`-tuple $`t([\chi])` is independent of the choice of representative $`\chi` and uniquely identifies the Galois orbit $`[\chi]`.

The *orbit index* of $`\chi` is the index of $`t([\chi])` in the lexicographic ordering of all such tuples arising for Dirichlet characters of modulus $`q`; indexing begins at $`1`, which is always the index of the Galois orbit of the {bpref "character.dirichlet.principal"}[principal character] of modulus $`1`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.principal"}[] {uses "character.dirichlet.value_field"}[]
:::

:::definition "character.dirichlet.galois_orbit_label"
*Label of a Galois orbit of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.galois_orbit_label))

The *label* of a {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of modulus $`N` takes the form $`N.a`, where $`a` is a letter or string of letters representing the {bpref "character.dirichlet.galois_orbit_index"}[index] of the Galois orbit.
 The index $`1` is written as $`a`, the index  $`2` is written as $`b`, the index $`27` is written as $`ba`, and so on.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_index"}[]
:::

:::definition "character.dirichlet.induce"
*Induced Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.induce))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi_1` of {bpref "character.dirichlet.modulus"}[modulus] $`q_1` is said to be *induced* by a Dirichlet character $`\chi_2` of modulus $`q_2` dividing $`q_1` if $`\chi_1(m)=\chi_2(m)` for all $`m` coprime to $`q_1`.

A Dirichlet character is {bpref "character.dirichlet.primitive"}[primitive] if it is not induced by any character other than itself; every Dirichlet character is induced by a uniquely determined primitive Dirichlet character.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.minimal"
*Minimal Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.minimal))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of prime power {bpref "character.dirichlet.modulus"}[modulus] $`N` is *minimal* if the following conditions both hold:

1. The {bpref "character.dirichlet.conductor"}[conductor] of $`\chi` does not lie in the open interval $`(\sqrt{N},N)`, and if $`N` is a square divisible by 16 then $`{\rm cond}(\chi)\in \{\sqrt{N},N\}`.

2. Both the {bpref "character.dirichlet.order"}[order] and conductor of $`\chi` are minimal among the set of all Dirichlet character $`\chi\psi^2` for which $`{\rm cond}(\psi){\rm cond}(\chi\psi) | N`.

This includes all {bpref "character.dirichlet.primitive"}[primitive] Dirichlet characters of prime power modulus, but not every minimal Dirichlet character of prime power modulus is primitive.

For a composite modulus $`N` with prime power factorization $`N=p_1^{e_1}\cdots p_n^{e_n}`, a Dirichlet character $`\chi` of modulus $`N` is *minimal* if and only if every character in its unique factorization into Dirichlet characters of modulus $`p_1^{e_1},\cdots,p_n^{e_n}` is minimal.  The {bpref "character.dirichlet.principal"}[trivial] Dirichlet character is minimal.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.primitive"}[] {uses "character.dirichlet.principal"}[]
:::

:::definition "character.dirichlet.modulus"
*Modulus of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.modulus))

A *Dirichlet character* is a function $`\chi: \mathbb{Z}\to \mathbb{C}` together with a positive integer $`q`, called the *modulus* of the character, such that $`\chi` is completely multiplicative, i.e. $`\chi(mn)=\chi(m)\chi(n)` for all integers $`m` and $`n`, and $`\chi` is periodic modulo $`q`, i.e. $`\chi(n+q)=\chi(n)` for all $`n`. If $`(n,q)>1` then $`\chi(n)=0`, whereas if $`(n,q)=1`, then $`\chi(n)` is a root of unity.
:::

:::definition "character.dirichlet.order"
*Order of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.order))

The *order* of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` is the least positive integer $`n` such that $`\chi^n` is the {bpref "character.dirichlet.principal"}[trivial] character of the same {bpref "character.dirichlet.modulus"}[modulus] as $`\chi`. Equivalently, it is the order $`n` of the image of $`\chi` in $`\mathbb{C}^\times`, the group of $`n`th roots of unity.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.principal"}[]
:::

:::definition "character.dirichlet.primitive"
*Primitive Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.primitive))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi` is *primitive* if its
{bpref "character.dirichlet.conductor"}[conductor] is equal to its {bpref "character.dirichlet.modulus"}[modulus]; equivalently, $`\chi` is not {bpref "character.dirichlet.induce"}[induced] by a Dirichlet character of smaller modulus.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.principal"
*Principal Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.principal))

A {bpref "character.dirichlet"}[Dirichlet character] is *principal* (or *trivial*) if it has {bpref "character.dirichlet.order"}[order] $`1`, equivalently, if it is {bpref "character.dirichlet.induce"}[induced] by the unique Dirichlet character of modulus 1.

The value of the principal Dirichlet character of {bpref "character.dirichlet.modulus"}[modulus] $`q` at an integer $`n` is $`1` if $`n` is coprime to $`q` and $`0` otherwise.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.value_field"
*Field of values of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.value_field))

The *field of values* of a Dirichlet character $`\chi\colon\Z\to\C` is the field $`\Q(\chi(\Z))` generated by its values; it is equal to the cyclotomic field $`\Q(\zeta_n)`, where $`n` is the {bpref "character.dirichlet.order"}[order] of $`\chi`.

Depends on: {uses "character.dirichlet.order"}[]
:::

:::definition "g2c.aut_grp"
*Automorphism group of an algebraic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.aut_grp))

An *automorphism* of an {bpref "ag.curve"}[algebraic curve] is an isomorphism from the curve to itself.  The set of automorphisms of a curve $`X` form a group $`\mathrm{Aut}(X)` under composition; this is the *automorphism group* of the curve.

The automorphism group of a {bpref "g2c.g2curve"}[genus 2 curve] necessarily includes the *hyperelliptic involution* $`(x,y)\mapsto(x,-y)`, which is an automorphism of order 2; this means that the automorphism group of a genus 2 curve is never trivial.

The geometric automorphism group of a curve $`X/k` is the automorphism group of $`X_{\bar k}`.

Depends on: {uses "ag.curve"}[] {uses "g2c.g2curve"}[]
:::

:::definition "g2c.discriminant"
*Discriminant of a genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.discriminant))

The discriminant $`\Delta` of a Weierstrass equation $`y^2+h(x)y=f(x)` can be computed as

$$`\Delta := \begin{cases}
2^8\text{lc}(f)^2\text{disc}(f+h^2/4)&\text{if }f+h^2/4\text{ has odd degree},\\
2^8\text{disc}(f+h^2/4)&\text{if }f+h^2/4\text{ has even degree},
\end{cases}`

where $`\text{lc}(f)` denotes the leading coefficient of $`f` and $`\text{disc}(f)` its discriminant.

The *discriminant* of a genus 2 curve over $`\Q` is the discriminant of a {bpref "g2c.minimal_equation"}[minimal equation] for the curve; it is an invariant of the curve that does not depend on the choice of minimal equation.
:::

:::definition "g2c.g2curve"
*Genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.g2curve))

Every (smooth, projective, geometrically integral) curve of genus 2 can be defined by a *Weierstrass equation* of the form
$$`y^2+h(x)y=f(x)`

with nonzero {bpref "g2c.discriminant"}[discriminant] and $`\deg h \le 3` and $`\deg f \le 6`; in order to have genus 2 we must have $`\deg h = 3` or $`\deg f =5,6`.  Over a field whose characteristic is not 2 one can complete the square to make $`h(x)` zero, but this will yield a model with bad reduction at 2 that is typically not a {bpref "g2c.minimal_equation"}[minimal equation] for the curve.

This equation can be viewed as defining the function field of the curve, or as a smooth model of the curve in the weighted projective plane. Every curve of genus 2 admits a degree 2 cover of the projective line (consider the function $`x`) and is therefore a {bpref "ag.hyperelliptic_curve"}[hyperelliptic curve].

Depends on: {uses "ag.hyperelliptic_curve"}[] {uses "g2c.discriminant"}[] {uses "g2c.minimal_equation"}[]
:::

:::definition "g2c.good_reduction"
*Primes of good reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.good_reduction))

A {bpref "ag.variety"}[variety] $`X` over $`\mathbb{Q}` is said to have *good reduction* at a prime $`p` if it has an integral model whose reduction modulo $`p` defines a smooth variety of the same dimension; otherwise, $`p` is said to be a prime of *bad reduction*.

When $`X` is a curve, any prime of good reduction for $`X` is also a prime of good reduction for its {bpref "ag.jacobian"}[Jacobian], but the converse need not hold when $`X` has genus $`g>1`.

For all of the genus 2 curves currently in the LMFDB, every prime of good reduction for the curve is also a prime of good reduction for the Jacobian of the curve.

Depends on: {uses "ag.jacobian"}[] {uses "ag.variety"}[]
:::

:::definition "g2c.minimal_equation"
*Minimal equation of a hyperelliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.minimal_equation))

Every ({bpref "ag.curve.smooth"}[smooth], projective, geometrically integral) {bpref "ag.hyperelliptic_curve"}[hyperelliptic curve] $`X` over $`\Q` of {bpref "ag.curve.genus"}[genus] $`g` can be defined by an integral Weierstrass equation

$$`y^2+h(x)y=f(x),`

where $`h(x)` and $`f(x)` are integral polynomials of degree at most $`g+1` and $`2g+2`, respectively.    Each such equation has a {bpref "g2c.discriminant"}[discriminant] $`\Delta`.  A *minimal equation* is one for which $`|\Delta|` is minimal among all integral Weierstrass equations for the same curve.  Over $`\Q`, every hyperelliptic curve has a minimal equation.  The prime divisors of $`\Delta` are the primes of {bpref "g2c.good_reduction"}[bad reduction] for $`X`.

The equation $`y^2+h(x)y=f(x)` uniquely determines a homogeneous equation of weighted degree 6 in variables $`x,y,z`, where $`y` has weight $`g+1`, while $`x` and $`z` both have weight 1: one homogenizes $`h(x)` to obtain a homogeneous polynomial $`h(x,z)` of degree $`g+1` and homogenizes $`f(x)` to obtain a homogeneous polynomial $`f(x,z)` of degree $`2g+2`.  This yields a smooth projective model $`y^2+h(x,z)y=f(x,z)` for the curve $`X`.

One can always transform the minimal equation into a simplified equation $`y^2 = g(x) = 4f(x)+h(x)^2`, but this equation need not have minimal discriminant and may have bad reduction at primes that do not divide the minimal discriminant (it will always have bad reduction at the prime $`2`).

Depends on: {uses "ag.curve.genus"}[] {uses "ag.curve.smooth"}[] {uses "ag.hyperelliptic_curve"}[] {uses "g2c.discriminant"}[] {uses "g2c.good_reduction"}[]
:::

:::definition "gg.galois_group"
*Galois group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gg.galois_group))

The *Galois group* of an irreducible separable polynomial of degree $`n` can be embedded in $`S_n` through its action on the roots of the polynomial, with the image being well-defined up to labeling of the roots.  Different labelings lead to conjugate subgroups.  The subgroup acts transitively on $`\{1,\ldots,n\}`.  Conversely, for every transitive subgroup $`G` of $`S_n` with $`n\in\mathbb{Z}^+`, there is a field $`K` such that $`G` is the Galois group of some polynomial over $`K`.
:::

:::definition "gl2.borel"
*Borel subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.borel))

A *Borel subgroup* of a general linear group is a subgroup that is conjugate to the group of upper triangular matrices.

The Borel subgroups of $`\GL_2(\F_p)` are maximal subgroups that fix a one-dimensional subspace of $`\F_p^2`; every such subgroup is conjugate to the subgroup of upper triangular matrices.

Subgroup labels containing the letter *B* identify a subgroup of $`\GL_2(\F_p)` that lies in the Borel subgroup of upper triangular matrices but is not contained in the subgroup of diagonal matrices; these are precisely the subgroups of a Borel subgroup that contain an element of order $`p`.

The label *B* is used for the full Borel subgroup of upper triangular matrices

The label *B.a.b* denotes the proper subgroup of *B* generated by the matrices

$$`\begin{pmatrix}a&0\\0&1/a\end{pmatrix},\ \begin{pmatrix}b&0\\0&r/b\end{pmatrix},\ \begin{pmatrix}1&1\\0&1\end{pmatrix},`

where $`a` and $`b` are minimally chosen positive integers and $`r` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .
:::

:::definition "gl2.cartan"
*Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.cartan))

Let $`R` be a commutative ring.  Given a free rank $`2` etale $`R`-algebra $`A` equipped with a basis, any $`a \in A^\times` defines an $`R`-linear multiplication-by-$`a` map $`A \to A`, so we get an injective homomorphism $`A^\times \to \Aut_{\text{R-module}}(A) \simeq \GL_2(R)`, and the image is called a *Cartan subgroup* of $`\GL_2(R)`.  The canonical involution of the $`R`-algebra $`A` gives another element of $`\Aut_{\text{R-module}}(A)`; we call the group generated by it and the Cartan subgroup $`A^\times` the *extended Cartan subgroup*.  The Cartan subgroup has index $`2` in the extended Cartan subgroup.

If $`R=\F_p`, there are two possibilities for $`A`: the split algebra $`\F_p \times \F_p` and the nonsplit algebra $`\F_{p^2}`; the resulting Cartan subgroups are called {bpref "gl2.split_cartan"}[split] and {bpref "gl2.nonsplit_cartan"}[nonsplit].  The extended Cartan subgroup equals the normalizer of the Cartan subgroup in $`\GL_2(\F_p)` except when $`p=2` and $`A` is split.  In the split case, if we use the standard basis of $`\F_p \times \F_p`, the Cartan subgroup is the subgroup of diagonal matrices in $`\GL_2(\F_p)`, and the extended Cartan subgroup is this together with the coset of antidiagonal matrices in $`\GL_2(\F_p)`.

If $`R=\Z/p^e\Z`, again there are two possibilities for $`A`: the split algebra $`R \times R`, or the nonsplit algebra.  The nonsplit algebra can be described as $`\mathcal{O}/p^e \mathcal{O}` where $`\mathcal{O}` is either the degree $`2` unramified extension of $`\Z_p` or a quadratic order in which $`p` is inert.  The nonsplit algebra can also be described as the ring of length $`e` Witt vectors $`W_e(\F_{p^2})`.

If $`R=\Z/N\Z` for some $`N \ge 1`, then $`A` can be split or nonsplit independently at each prime dividing $`N`.
:::

:::definition "gl2.exceptional"
*Exceptional subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.exceptional))

An *exceptional subgroup* of $`\GL_2(\F_p)` does not contain $`\SL_2(\F_p)` and is not contained in a {bpref "gl2.borel"}[Borel subgroup] or in the {bpref "gl2.normalizer_cartan"}[normalizer of a Cartan subgroup].

Exceptional subgroups are classified according to their image in $`\PGL_2(\F_p)`, which must be isomorphic to one of the alternating groups $`A_4` or $`A_5`, or to the symmetric group $`S_4`.  These groups are labelled using identifiers containing one of the strings *A4*, *A5*, *S4*, as described in .

Depends on: {uses "gl2.borel"}[] {uses "gl2.normalizer_cartan"}[]
:::

:::definition "gl2.index"
*Index of an open subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.index))

The *index* of an {bpref "gl2.open"}[open subgroup] $`H` of a {bpref "gl2.profinite"}[profinite group] $`G` is the positive integer $`[G:H]`.

When $`G` is a matrix group over $`\widehat{\Z}` or $`\Z_{\ell}` and $`H` is a subgroup of {bpref "gl2.level"}[level] $`N`, this is the same as the index of $`H` in the reduction of $`G` modulo $`N`.

Depends on: {uses "gl2.level"}[] {uses "gl2.open"}[] {uses "gl2.profinite"}[]
:::

:::definition "gl2.level"
*Level of an open subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.level))

The *level* of an {bpref "gl2.open"}[open subgroup] $`H` of a matrix group $`G` over $`\widehat{\Z}` is the least positive integer $`N` for which $`H` is equal to the inverse image of its projection to the reduction of $`G` modulo $`N`.

This also applies to open subgroups of matrix groups over $`\Z_{\ell}`, in which case the level is necessarily a power of $`\ell`.

Depends on: {uses "gl2.open"}[]
:::

:::definition "gl2.nonsplit_cartan"
*Non-split Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.nonsplit_cartan))

A *non-split Cartan subgroup* of $`\GL_2(\F_p)` is a {bpref "gl2.cartan"}[Cartan subgroup] that is not diagonalizable over $`\F_p`.  Every non-split Cartan subgroup is a cyclic group isomorphic to $`\F_{p^2}^\times`.

For $`p=2` the label *Cn* identifies the unique index 2 subgroup of $`\GL_2(\F_2)`.
For $`p>2` the label *Cn* identifies the nonsplit Cartan subgroup consisting of matrices of the form

$$`\begin{pmatrix}x&\varepsilon y\\y&x\end{pmatrix},`

with $`x,y\in \F_p` not both zero and $`\varepsilon` the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`,  corresponding to $`x+y\sqrt{\varepsilon}\in\F_{p^2}^\times`.  Every non-split Cartan subgroup is conjugate to the group *Cn*.

Labels of the form *Cn.a.b* identify the proper subgroup of *Cn* generated by the matrix

$$`\begin{pmatrix}a&\varepsilon b\\b&a\end{pmatrix},`

where $`a` and $`b` are minimally chosen positive integers and $`\varepsilon` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .

Depends on: {uses "gl2.cartan"}[]
:::

:::definition "gl2.normalizer_cartan"
*Normalizer of a Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.normalizer_cartan))

For $`p>2` the *normalizer of a Cartan subgroup* of $`\GL_2(\F_p)` is a maximal subgroup of $`\GL_2(\F_p)` that contains a {bpref "gl2.cartan"}[Cartan subgroup] with index 2.  It is the normalizer in $`\GL_2(\F_p)` of the Cartan subgroup it contains.

For $`p=2` the Cartan subgroups of $`\GL_2(\F_2)` are already normal and we instead define the normalizer of a Cartan subgroup to be a group that contains a Cartan subgroup with index 2.  This means that the normalizer of a split Cartan subgroup of $`\GL_2(\F_2)` has order 2 (which makes it conjugate to the Borel subgroup), while the normalizer of a non-split Cartan subgroup of $`\GL_2(\F_2)` has order 6 (which makes it all of $`\GL_2(\F_2)`).

Depends on: {uses "gl2.cartan"}[]
:::

:::definition "gl2.normalizer_nonsplit_cartan"
*Normalizer of a non-split Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.normalizer_nonsplit_cartan))

For $`p>2` the *normalizer of a non-split Cartan subgroup* of $`\GL_2(\F_p)` is a maximal subgroup of $`\GL_2(\F_p)` that contains a {bpref "gl2.nonsplit_cartan"}[non-split Cartan subgroup] with index 2,
and it is the normalizer in $`\GL_2(\F_p)` of the non-split Cartan subgroup it contains.  For $`p=2` the normalizer of a non-split Cartan subgroup is defined to be all of $`\GL_2(\F_2)`, which contains its (already normal) non-split Cartan subgroup with index 2.

For $`p>2` the label *Nn* identifies the normalizer of the nonsplit Cartan subgroup generated by the non-split Cartan subgroup *Cn* and the matrix

$$`\begin{pmatrix}1&0\\0&-1\end{pmatrix},`

and every normalizer of a non-split Cartan subgroup is conjugate to the group *Nn*.

The label *Nn.a.b* denotes the proper subgroup of the normalizer of the nonsplit Cartan subgroup *Nn* generated by the matrices

$$`\begin{pmatrix}a&\varepsilon b\\b&a\end{pmatrix}, \begin{pmatrix}1&0\\0&-1\end{pmatrix}.`

where $`a` and $`b` are minimally chosen positive integers and $`\varepsilon` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .

Depends on: {uses "gl2.nonsplit_cartan"}[]
:::

:::definition "gl2.normalizer_split_cartan"
*Normalizer of a split Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.normalizer_split_cartan))

The *normalizer of a split Cartan subgroup* of $`\GL_2(\F_p)` is a maximal subgroup of $`\GL_2(\F_p)` that contains a {bpref "gl2.split_cartan"}[split Cartan subgroup] with index 2.  For $`p>2` such a group is in fact the normalizer in $`\GL_2(\F_p)` of the split Cartan subgroup it contains, but for $`p=2` this is not the case (the split Cartan subgroup of $`\GL_2(\F_2)` is already normal).

The label *Ns* identifies the subgroup generated by the split Cartan subgroup *Cs* of diagonal matrices and the matrix

$$`\begin{pmatrix}0&1\\1&0\end{pmatrix}.`

Every normalizer of a split Cartan subgroup is conjugate to the group *Ns*.

The label *Ns.a.b* identifies the proper subgroup of *Ns* generated by the matrices

$$`\begin{pmatrix}a&0\\0&1/a\end{pmatrix}, \begin{pmatrix}0&b\\-r/b&0\end{pmatrix},`

where $`a` and $`b` are minimally chosen positive integers and $`r` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`.

The label *Ns.a.b.c*  identifies the proper subgroup of the normalizer of the split Cartan subgroup generated by the matrices

$$`\begin{pmatrix}a&0\\0&1/a\end{pmatrix}, \begin{pmatrix}0&b\\-1/b&0\end{pmatrix}, \begin{pmatrix}0&c\\-r/c&0\end{pmatrix}`

where $`a` and $`b` are minimally chosen positive integers and $`r` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .

Depends on: {uses "gl2.split_cartan"}[]
:::

:::definition "gl2.open"
*Open subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.open))

An *open subgroup* $`H` of a {bpref "gl2.profinite"}[profinite group] $`G` is a subgroup that is open in the topology of $`G`, which implies that it is equal to the inverse image of its projection to a a finite quotient of $`G`.

Open subgroups of $`G` necessarily have finite index (since $`G` is compact), but not every finite index subgroup of $`G` is necessarily open.

When the profinite group $`G` is a matrix group over a ring $`R` that is equipped with canonical projections to finite rings of the form $`\Z/n\Z` (take $`R=\Z_{\ell}` or $`R=\widehat{\Z}`, for example), we use $`G(n)` to denote the image of $`G` under the group homomorphism induced by the projection $`R\to\Z/n\Z`.  In this situation we may identify $`H` with its projection to $`G(N)`, where $`N` is the least positive integer for which $`H` is the inverse image of its projection to $`G(N)` (this $`N` is the {bpref "gl2.level"}[level] of $`H`).

Depends on: {uses "gl2.profinite"}[]
:::

:::definition "gl2.profinite"
*Profinite group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.profinite))

A *profinite group* is a compact totally disconnected topological group.  Equivalently, it is the inverse limit of a system of finite groups equipped with the discrete topology.

For example, if we take the finite groups $`\GL_2(\Z/n\Z)` as $`n` varies over positive integers, order them by divisibility of $`n` and consider the inverse system equipped with reduction maps $`\GL_2(\Z/n\Z)\to \GL_2(\Z/m\Z)` for all positive integers $`m|n`, then the inverse limit

$$`\lim_{\overset{\longleftarrow}{n}} \GL_2(\Z/n\Z) \simeq \GL_2(\widehat{\Z})`

is a profinite group which is isomorphic to the group of invertible $`2\times 2` matrices over the topological ring $`\widehat{\Z}`, which is the inverse limit of the finite rings $`\Z/n\Z` equipped with the discrete topology.
:::

:::definition "gl2.split_cartan"
*Split Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.split_cartan))

A *split Cartan subgroup* of $`\GL_2(\F_p)` is a {bpref "gl2.cartan"}[Cartan subgroup] that is diagonalizable over $`\F_p`.  Every split Cartan subgroup is conjugate to the subgroup of diagonal matrices, which is isomorphic to $`\F_p^\times\times\F_p^\times`.

The label *Cs* identifies the split Cartan subgroup of diagonal matrices.

The label *Cs.a.b* identifies the proper subgroup of *Cs* generated by

$$`\begin{pmatrix}a&0\\0&1/a\end{pmatrix}, \begin{pmatrix}b&0\\0&r/b\end{pmatrix},`

where $`a` and $`b` are minimally chosen positive integers and $`r` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .

Depends on: {uses "gl2.cartan"}[]
:::

:::definition "group"
*Definition of group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group))

A *group* $`\langle G, *\rangle` is a set $`G` with a {bpref "alg.binary_operation"}[binary operation] $`*` such that

1. $`*` is {bpref "alg.binary_operation.associative"}[associative]
2. $`*` has an {bpref "alg.binary_operation.identity"}[identity element]
3. every element $`g\in G` has an {bpref "alg.binary_operation.inverse"}[inverse].

Depends on: {uses "alg.binary_operation"}[] {uses "alg.binary_operation.associative"}[] {uses "alg.binary_operation.identity"}[] {uses "alg.binary_operation.inverse"}[]
:::

:::definition "group.abelian"
*Abelian group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.abelian))

A {bpref "group"}[group] is *abelian* if its {bpref "alg.binary_operation"}[operation] is {bpref "alg.binary_operation.commutative"}[commutative].

Depends on: {uses "alg.binary_operation"}[] {uses "alg.binary_operation.commutative"}[] {uses "group"}[]
:::

:::definition "group.automorphism"
*Automorphisms of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.automorphism))

If $`G` is a {bpref "group"}[group], an *automorphism* of $`G` is a {bpref "group.isomorphism"}[group isomorphism] $`f:G\to G`.

The set of automorphisms of $`G`, $`\Aut(G)`, is a group under composition.

Depends on: {uses "group"}[] {uses "group.isomorphism"}[]
:::

:::definition "group.characteristic_subgroup"
*Characteristic subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.characteristic_subgroup))

A {bpref "group.subgroup"}[subgroup] $`H` of a {bpref "group"}[group] $`G`  is a *characteristic subgroup* if $`\phi(H)=H` for all {bpref "group.automorphism"}[automorphisms] $`\phi\in \Aut(G)`.

Depends on: {uses "group"}[] {uses "group.automorphism"}[] {uses "group.subgroup"}[]
:::

:::definition "group.coset"
*Coset of a subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.coset))

If $`G` is a {bpref "group"}[group] and $`H` is a {bpref "group.subgroup"}[subgroup] of $`G`, then a left *coset* of $`H` is a set

$$`gH = \{ gh \mid h \in H\}`

and similarly, a right coset of $`H` is a set

$$`Hg = \{ hg \mid h \in H\}.`

The left cosets partition $`G`, as do the right cosets.

Depends on: {uses "group"}[] {uses "group.subgroup"}[]
:::

:::definition "group.frattini_subgroup"
*Frattini subgroup of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.frattini_subgroup))

If $`G` is a group, then the *Frattini subgroup* of $`G`, denoted $`\Phi(G)`, is the intersection of all {bpref "group.maximal_subgroup"}[maximal subgroups] of $`G`.  If there are no maximal subgroups of $`G`, then $`\Phi(G)=G`.

The Frattini subgroup is always a {bpref "group.characteristic_subgroup"}[characteristic subgroup], hence a {bpref "group.subgroup.normal"}[normal] subgroup, of $`G`.

Depends on: {uses "group.characteristic_subgroup"}[] {uses "group.maximal_subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.fuchsian.cusps"
*Cusps of a subgroup of the modular group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.fuchsian.cusps))

The *cusps* of a subgroup $`\Gamma` of the {bpref "group.sl2z"}[modular group] are equivalence classes of points in $`\mathbb{Q}\cup\infty` under the action of $`\Gamma` by linear fractional transformation, where for

$$`\gamma=\left(\begin{array}{ll}a&b\\c&d \end{array}\right)\in\Gamma,`

we define $`\gamma\infty = \frac{a}{c}` when $`c\neq 0`, and $`\gamma\infty = \infty` when $`c=0`.

Depends on: {uses "group.sl2z"}[]
:::

:::definition "group.fuchsian.cusps.width"
*Width of a cusp.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.fuchsian.cusps.width))

The *width* of the {bpref "group.fuchsian.cusps"}[cusp] $`\infty`
for the group $`\Gamma` is the smallest number $`w` such that $`T^w=\left(\begin{matrix}1&w\\0&1\end{matrix}\right)\in\Gamma`. Furthermore, for a general $`x\in\mathbb{P}^1(\mathbb{Q})` and $`\gamma\in\Gamma` such that $`\gamma\infty=x`, we define the *width* of $`x` for $`\Gamma` to be the width of $`\infty` for $`\gamma^{-1}\Gamma\gamma`.

Note that $`T=\left(\begin{matrix}1&1\\0&1\end{matrix}\right)` is one of the *generators* of the {bpref "group.sl2z"}[modular group] $`\textrm{SL}_2(\mathbb{Z})`.

Depends on: {uses "group.fuchsian.cusps"}[] {uses "group.sl2z"}[]
:::

:::definition "group.fuchsian.fundamental_domain"
*Fundamental domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.fuchsian.fundamental_domain))

If $`G\subseteq\Gamma` is a subgroup of the {bpref "group.sl2z"}[modular group], then a closed set
$`F\in\mathcal{H}\cup\mathbb{Q}\cup\{\infty\}` is said
to be a *fundamental domain* for $`G` if:
<ol>
  <li> For any point $`z\in\mathcal{H}` there is a
$`g\in G` such that $`gz\in F`.</li>
  <li> If $`z\not=z'\in F` are equivalent with respect to the action of $`G`,
that is, if $`z'=gz` for some $`g\in G`, then $`z` and
$`z'` belong to $`\partial F`, the boundary of F.</li>
</ol>

Depends on: {uses "group.sl2z"}[]
:::

:::definition "group.galois.absolute"
*Absolute Galois group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.galois.absolute))

The *absolute Galois group* of a {bpref "ring.field"}[field] $`K` is the group of all automorphisms of the algebraic closure of $`K` that fix the field $`K`.

Depends on: {uses "ring.field"}[]
:::

:::definition "group.generators"
*Generators of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.generators))

If $`G` is a {bpref "group"}[group] and $`S` is a subset of $`G`, then $`S` is a set of *generators* if the smallest subgroup of $`G` containing $`S` equals $`G`.

Equivalently, $`S` generates $`G` if

$$`G=\bigcap_{S\subseteq H\leq G} H \,.`

The {bpref "group.automorphism"}[automorphism group] of $`G` acts on such $`S`, and we say $`S` and $`S'` are equivalent if they are related by this action.

Depends on: {uses "group"}[] {uses "group.automorphism"}[]
:::

:::definition "group.haar_measure"
*Haar measure of a topological group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.haar_measure))

For $`G` a locally compact topological {bpref "group"}[group], a *Haar measure* on $`G` is a nonnegative, countably additive, real-valued measure on $`G` which is invariant under left translation on $`G`. Any such measure is also invariant under right translation on $`G`.

A Haar measure always exists and is unique up to multiplication by a positive scalar. If $`G` is compact, then the *normalized Haar measure* on $`G` is the unique Haar measure on $`G` under which $`G` has total measure 1.

As a special case, if $`G` is finite of {bpref "group.order"}[order] $`n`, then the normalized Haar measure is the uniform measure that assigns to each element the measure $`1/n`.

Depends on: {uses "group"}[] {uses "group.order"}[]
:::

:::definition "group.homomorphism"
*Group homomorphism.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.homomorphism))

If $`G` and $`H` are {bpref "group"}[groups], then a *group homomorphism* from $`G` to $`H` is a function

$$`f:G\to H`

such that for all $`a,b\in G`, $`f(a*b)=f(a)*f(b)`.

Depends on: {uses "group"}[]
:::

:::definition "group.isomorphism"
*Group isomorphism.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.isomorphism))

A *group isomorphism* is a {bpref "group.homomorphism"}[group homomorphism] $`f:G\to H` which is bijective.

Depends on: {uses "group.homomorphism"}[]
:::

:::definition "group.maximal_subgroup"
*Maximal subgroup of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.maximal_subgroup))

If $`G` is a group, a subgroup $`M` is a *maximal subgroup* if for every subgroup $`H` such that $`M\subseteq H \subseteq G`, either $`H=M` or $`H=G`.
:::

:::definition "group.normal_series"
*Normal series of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.normal_series))

If $`G` is a {bpref "group"}[group], a *subnormal series* for $`G` is a chain of subgroups

$$`\langle e\rangle =H_0 \lhd H_1  \lhd \cdots \lhd H_k=G`

where each {bpref "group.subgroup"}[subgroup] $`H_i` is {bpref "group.subgroup.normal"}[normal] in $`H_{i+1}` for all $`i`.

A subnormal series where $`H_i` is normal in $`G` for all $`i` is a *normal series*.

Depends on: {uses "group"}[] {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.order"
*Order of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.order))

The *order* of a {bpref "group"}[group] is its cardinality as a set.

Depends on: {uses "group"}[]
:::

:::definition "group.presentation"
*Presentation of a finite group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.presentation))

A *presentation* of a group $`G` is a description of $`G` as the quotient $`F/R` of a free group $`F` generated by a specified set of generators, modulo the normal subgroup $`R` generated by a set of words in those generators.  When $`G` is abelian we instead express $`G` as a quotient of a free abelian group $`F` so that we can omit commutator relations.

In what follows, we denote by $`g^h` the conjugate $`h^{-1}gh` and by $`[g, h]` the commutator $`ghg^{-1}h^{-1}`.

We only give presentations for finite solvable groups, where they can take a special form.  A *polycyclic series* is a {bpref "group.normal_series"}[subnormal series] $`G = G_1 \trianglerighteq G_2 \trianglerighteq \dots \trianglerighteq G_n \trianglerighteq G_{n+1} = \{1\}` so that $`G_i/G_{i+1}` is cyclic for each $`i`.  A *polycyclic sequence* is a sequence of elements $`(g_1, \dots, g_n)` of $`G` so that $`G_i/G_{i+1} = \langle g_i G_{i+1}\rangle`.  The *relative orders* of a polycyclic series are the orders $`r_i` of the cyclic quotients $`G_i / G_{i+1}`.  The *polycyclic presentation* associated to a polycyclic sequence has generators $`g_1, \dots, g_n` and relations of the following shape.

- $`g_i^{r_i} = \prod_{k=i+1}^n g_k^{a_{i,k}}` for all $`i`;

- $`g_i^{g_j} = \prod_{k=j+1}^n g_k^{b_{i,j,k}}` for $`j < i`.

Any finite solvable group has a polycyclic presentation.  When the size of $`G` is not too large, we choose a presentation with the following properties:

- it has a minimal number of generators;

- among such, it has a maximal number of $`i` so that all $`a_{i,k} = 0`;

- among such, it has a maximal number of commuting $`g_i`;

- among such, aim for an increasing sequence of relative orders;

- among such, minimize the sum of the $`b_{i,j,k}` for noncommuting generators $`g_i` and $`g_j`.

Depends on: {uses "group.normal_series"}[]
:::

:::definition "group.rank"
*Rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.rank))

The *rank* of a finite {bpref "group"}[group] $`G` is the minimal number of elements required to {bpref "group.generators"}[generate] it, which is often smaller than the number of generators in a {bpref "group.presentation"}[polycyclic presentation].  For $`p`-groups, the rank can be computed by taking the $`\mathbb{F}_p`-dimension of the quotient by the {bpref "group.frattini_subgroup"}[Frattini subgroup].

Depends on: {uses "group"}[] {uses "group.frattini_subgroup"}[] {uses "group.generators"}[] {uses "group.presentation"}[]
:::

:::definition "group.sl2z"
The *modular group* is the group of  $`2\times2` matrices with integer coefficients and determinant $`1`; it is denoted by $`\mathrm{SL}(2,\mathbb{Z})` or $`\mathrm{SL}_2(\Z)`.

A standard set of generators for the modular group are the matrices:

$$`S:=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\quad\text{and}\quad T:=\begin{pmatrix}1&1\\0&1
\end{pmatrix}.`
:::

:::definition "group.subgroup"
*Subgroup of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup))

If $`G` is a {bpref "group"}[group], a subset $`H\subseteq G` is a *subgroup* of $`G` if the {bpref "alg.binary_operation"}[binary operation] of $`G` restricts to a {bpref "alg.binary_operation"}[binary operation] on $`H`, and $`H` is a group for this induced operation.

Equivalently, the subset $`H` must satisfy the following conditions:

1. for all $`a,b\in H`, $`a*b\in H`
2. the {bpref "alg.binary_operation.identity"}[identity] of $`G` is an element of $`H`
3. for every $`a\in H`, the {bpref "alg.binary_operation.inverse"}[inverse] of $`a` in $`G` is also in $`H`.

Depends on: {uses "alg.binary_operation"}[] {uses "alg.binary_operation.identity"}[] {uses "alg.binary_operation.inverse"}[] {uses "group"}[]
:::

:::definition "group.subgroup.index"
*Index of a subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.index))

The *index* of a subgroup $`G'` of a group $`G`, denoted $`[G:G']`, is the order of the set of {bpref "group.coset"}[left cosets] of $`G'` in $`G`.

Depends on: {uses "group.coset"}[]
:::

:::definition "group.subgroup.normal"
*Normal subgroup of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.normal))

If $`H` is a {bpref "group.subgroup"}[subgroup] of a {bpref "group"}[group] $`G`, then $`H` is *normal* if any of the following equivalent conditions hold:

1. $`gHg^{-1}=H` for all $`g\in G`
2. $`gHg^{-1}\subseteq H` for all $`g\in G`
3. $`gH=Hg` for all $`g\in G`
4. $`(aH)*(bH)=(ab)H` is a well-defined {bpref "alg.binary_operation"}[binary operation] on the set of {bpref "group.coset"}[left cosets] of $`H`

If $`H` is a normal subgroup, we write $`H \lhd G`, and the set of left cosets $`G/H` form a group under the operation given in (4) above.

Depends on: {uses "alg.binary_operation"}[] {uses "group"}[] {uses "group.coset"}[] {uses "group.subgroup"}[]
:::

:::definition "group.sylow_subgroup"
*Sylow subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sylow_subgroup))

If $`p` is a prime and $`G` is a finite {bpref "group"}[group] of {bpref "group.order"}[order] $`p^nm` where $`p\nmid m`, then a *$`p`-Sylow
subgroup*  of $`G` is any {bpref "group.subgroup"}[subgroup] of order $`p^n`.

Sylow subgroups exist for every finite group and prime $`p`.

Depends on: {uses "group"}[] {uses "group.order"}[] {uses "group.subgroup"}[]
:::

:::definition "group.torsion"
*Torsion group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.torsion))

A *torsion {bpref "group"}[group]* is a group in which every element has finite order.

The elements of finite order in an {bpref "group.abelian"}[abelian] group $`A` form a torsion group called the *torsion subgroup* of $`A`.

Depends on: {uses "group"}[] {uses "group.abelian"}[]
:::

:::definition "lf.automorphism_group"
*Automorphism group of a field extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.automorphism_group))

If $`K/F` is an extension of {bpref "ring.field"}[fields], its *automorphism group* is

$$`\textrm{Aut}(K/F) = \{\sigma:K\to K\mid  \forall a\in F, \sigma(a)=a, \text{ and } \sigma \text{ is an isomorphism}\}.`

Note, a finite extension is {bpref "nf.is_galois"}[Galois] if and only if $`|\textrm{Aut}(K/F)| = [K:F]`.

Depends on: {uses "nf.is_galois"}[] {uses "ring.field"}[]
:::

:::definition "lf.inertia_group"
*Inertia group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.inertia_group))

Let

- $`K` be a {bpref "lf.padic_field"}[$`p`-adic field].

- $`L` a finite {bpref "nf.is_galois"}[Galois] extension of $`K`.

- $`\mathcal{O}_K`, $`\mathcal{O}_L` the rings of integers for $`K`, $`L`,

- $`P_K`, $`P_L` the unique {bpref "lf.maximal_ideal"}[maximal ideals] of $`\mathcal{O}_K`, $`\mathcal{O}_L`, and

- $`\kappa=\mathcal{O}_K/P_K`, $`\lambda=\mathcal{O}_L/P_L` the

{bpref "lf.residue_field"}[residue fields] of $`K`, $`L`.

Then each $`\sigma\in \Gal(L/K)` induces a element of $`\Gal(\lambda/\kappa)`.  The kernel of the resulting homomorphism

$$`\Gal(L/K) \to \Gal(\lambda/\kappa)`

is the *inertia group* of $`L/K`.

Depends on: {uses "lf.maximal_ideal"}[] {uses "lf.padic_field"}[] {uses "lf.residue_field"}[] {uses "nf.is_galois"}[]
:::

:::definition "lf.local_field"
*Local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.local_field))

A *local field* is a {bpref "ring.field"}[field] $`K` with a non-trivial {bpref "nf.absolute_value"}[absolute value] $`|\ |` that is locally compact in the topology induced by the distance metric $`d(x,y):=|x-y|`.

An *archimedean local field* is a local field whose absolute value is {bpref "nf.absolute_value"}[archimedean]; such a field is isomorphic to $`\R` or $`\C`.

A *nonarchimedean local field* is a local field whose absolute value is {bpref "nf.absolute_value"}[nonarchimedean]. Such a field is either isomorphic to a finite extension of $`\Q_p` when $`K` has {bpref "ring.characteristic"}[characteristic] zero (in which case it is a {bpref "lf.padic_field"}[$`p`-adic field]), or to a finite extension of $`\F_p((t))` when $`K` has characteristic $`p`.  In both cases $`p` is the characteristic of the {bpref "lf.residue_field"}[residue field] of $`K`..

Depends on: {uses "nf.absolute_value"}[] {uses "ring.characteristic"}[] {uses "ring.field"}[]
:::

:::definition "lf.maximal_ideal"
*Maximal ideal of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.maximal_ideal))

The *maximal ideal* of a {bpref "lf.local_field"}[nonarchimedean local field] $`K` is the unique {bpref "ring.maximal_ideal"}[maximal ideal] of its {bpref "lf.ring_of_integers"}[ring of integers] $`\mathcal O_K`.

It consists of all elements of $`\mathcal O_K` that are not {bpref "ring.unit"}[units], equivalently, all elements of $`K` whose {bpref "nf.absolute_value"}[absolute value] is strictly less than 1.

Depends on: {uses "lf.local_field"}[] {uses "lf.ring_of_integers"}[] {uses "nf.absolute_value"}[] {uses "ring.maximal_ideal"}[] {uses "ring.unit"}[]
:::

:::definition "lf.padic_field"
*$`p`-adic field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.padic_field))

A *$`p`-adic field* (or *local number field*) is a finite extension of
$`\Q_p`, equivalently, a {bpref "lf.local_field"}[nonarchimedean local field] of {bpref "ring.characteristic"}[characteristic] zero.

Depends on: {uses "lf.local_field"}[] {uses "ring.characteristic"}[]
:::

:::definition "lf.residue_field"
*Residue field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.residue_field))

The *residue field* of a nonarchimedean local field is the quotient of its {bpref "lf.ring_of_integers"}[ring of integers] by its unique {bpref "lf.maximal_ideal"}[maximal ideal].

The residue field is finite and its characteristic $`p` is the *residue field characteristic*.  Finite extensions of $`\Q_p` have residue field characteristic $`p`.

Depends on: {uses "lf.maximal_ideal"}[] {uses "lf.ring_of_integers"}[]
:::

:::definition "lf.ring_of_integers"
*Ring of integers of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.ring_of_integers))

The *ring of integers* of a {bpref "lf.local_field"}[local field] $`K` with {bpref "nf.absolute_value"}[absolute value] $`|\ |` is the subring
$`\mathcal O_K := \{x\in K:|x|\le 1\}`; it is a discrete valuation ring.

Depends on: {uses "lf.local_field"}[] {uses "nf.absolute_value"}[]
:::

:::definition "lf.wild_inertia_group"
*Wild inertia group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.wild_inertia_group))

The *wild inertia group* of a {bpref "nf.is_galois"}[Galois] extension $`K/\Q_p` is the unique {bpref "group.sylow_subgroup"}[$`p`-Sylow subgroup] of its {bpref "lf.inertia_group"}[inertia group].

Depends on: {uses "group.sylow_subgroup"}[] {uses "lf.inertia_group"}[] {uses "nf.is_galois"}[]
:::

:::definition "lfunction"
*L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction))

An (analytic) *L-function* is a {bpref "lfunction.dirichlet_series"}[Dirichlet series] that has an {bpref "lfunction.euler_product"}[Euler product] and satisfies a certain type of {bpref "lfunction.functional_equation"}[functional equation].

It is expected that all L-functions satisfy the {bpref "lfunction.rh"}[Riemann Hypothesis,] that all of the zeros in the critical strip are on the {bpref "lfunction.critical_line"}[critical line]. Selberg has defined a class $`\mathcal S` of Dirichlet series that satisfy the Selberg axioms. It is conjectured (but far from proven) that $`\mathcal S` is precisely the set of all L-functions. Selberg's axioms have not been verified for all of the L-functions in this database but are known to hold for many of them.

It is also conjectured that a precise form of the {bpref "lfunction.functional_equation"}[functional equation] holds for every element of $`\mathcal S`. Under this assumption the functional equation is determined by a quadruple known as the Selberg data, consisting of the degree, conductor, spectral parameters, and sign.

Depends on: {uses "lfunction.dirichlet_series"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.analytic_rank"
*Analytic rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.analytic_rank))

The *analytic rank* of an {bpref "lfunction"}[L-function] $`L(s)` is its order of vanishing at its {bpref "lfunction.central_point"}[central point].

When the analytic rank $`r` is positive, the value listed in the LMFDB is typically an upper bound that is believed to be tight (in the sense that there are known to be $`r` zeroes located very near to the central point).

Depends on: {uses "lfunction.central_point"}[] {uses "lfunction"}[]
:::

:::definition "lfunction.arithmetic"
*Arithmetic L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.arithmetic))

An {bpref "lfunction"}[L-function] $`L(s) = \sum_{n=1}^{\infty} a_n n^{-s}`  is called *arithmetic* if its Dirichlet coefficients $`a_n` are algebraic numbers.

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.central_point"
*Central point of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.central_point))

The *central point* of an {bpref "lfunction"}[L-function] is the
point on the real axis of the {bpref "lfunction.critical_line"}[critical line].  Equivalently,
it is the fixed point of the {bpref "lfunction.functional_equation"}[functional equation].

In the {bpref "lfunction.normalization"}[analytic normalization], the central point is $`s=1/2`, in the arithmetic normalization, it is $`s=\frac{w+1}{2}`, where $`w` is the weight of the L-function.

Depends on: {uses "lfunction"}[] {uses "lfunction.critical_line"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.critical_line"
*Critical line of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.critical_line))

The *critical line* of an {bpref "lfunction"}[L-function]  is the line of symmetry of its {bpref "lfunction.functional_equation"}[functional equation].

In the {bpref "lfunction.normalization"}[analytic normalization], the functional equation relates $`s` to $`1-s` and the
critical line is the line $`\Re(s) = \frac12`.

In the arithmetic normalization, the functional equation relates $`s` to $`1 + w - s`,
where $`w` is the motivic weight.  In that normalization the critical line is
$`\Re(s) = \frac{1+w}2`.

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.dirichlet_series"
*Dirichlet series.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.dirichlet_series))

A *Dirichlet series* is a formal series of the form $`F(s) = {\displaystyle \sum_{n=1}^{\infty} \frac{a_n}{ n^{s}}}`, where $`a_n \in {\mathbb{C}}`.
:::

:::definition "lfunction.dual"
*Dual of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.dual))

The *dual* of an {bpref "lfunction"}[L-function] $`L(s) = \sum_{n=1}^{\infty} \frac{a_n}{n^s}` is the complex conjugate $`\bar{L}(s) = \sum_{n=1}^{\infty} \frac{\bar{a_n}}{n^s}`.

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.euler_product"
*Euler product of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.euler_product))

It is expected that the *Euler product* of an {bpref "lfunction"}[L-function] of degree $`d` and conductor $`N` can be written as

$$`L(s)=\prod_p L_p(s)`

where for  $`p\nmid N`

$$`L_p(s)=\prod_{n=1}^d  \left( 1-\frac{\alpha_{n}(p)}{p^s}\right)^{-1} \text{ with } |\alpha_{n}(p)|=1`

and
for $`p\mid N`,

$$`L_p(s)=\prod_{n=1}^{d_p}\left( 1-\frac{\beta_{n}(p)}{p^s}\right)^{-1} \text{ where } d_p < d \text{ and  } |\beta_n(p)|\le 1.`

The functions $`L_p(s)` are called *Euler factors* (or *local factors*).
:::

:::definition "lfunction.functional_equation"
*Functional equation of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.functional_equation))

All known {bpref "lfunction"}[analytic L-functions] have a *functional equation* that can be written in the form

$$`\Lambda(s) := N^{s/2}
\prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k)
\cdot L(s) = \varepsilon \overline{\Lambda}(1-s),`

where $`N` is an integer, {bpref "lfunction.gamma_factor"}[$`\Gamma_{\mathbb{R}}` and $`\Gamma_{\mathbb{C}}`] are defined in terms of the {bpref "specialfunction.gamma"}[$`\Gamma`-function,] $`\mathrm{Re}(\mu_j) = 0 \ \mathrm{or} \ 1` (assuming Selberg's eigenvalue conjecture), and $`\mathrm{Re}(\nu_k)` is a positive integer
or half-integer,

$$`\sum \mu_j + 2 \sum \nu_k \ \ \ \ \text{is real},`

and $`\varepsilon` is the {bpref "lfunction.sign"}[sign] of the functional equation.
With those restrictions on the spectral parameters, the
data in the functional equation is specified uniquely.  The integer $`d = J + 2 K`
is the degree of the L-function. The integer $`N` is  the conductor (or level)
of the L-function.  The pair $`[J,K]` is the signature of the L-function.  The parameters
in the functional equation can be used to make up the 4-tuple called the Selberg data.

The axioms of the Selberg class are less restrictive than
given above.

Note that the functional equation above has the {bpref "lfunction.central_point"}[central point] at $`s=1/2`, and relates $`s\leftrightarrow 1-s`.

For many L-functions there is another normalization which is natural. The corresponding functional equation relates $`s\leftrightarrow w+1-s` for some positive integer $`w`,
called the motivic weight of the L-function. The central point is at $`s=(w+1)/2`, and the arithmetically normalized Dirichlet coefficients $`a_n n^{w/2}` are algebraic integers.

Depends on: {uses "lfunction.gamma_factor"}[] {uses "specialfunction.gamma"}[]
:::

:::definition "lfunction.gamma_factor"
*Gamma factors.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.gamma_factor))

The complex functions

$$`\Gamma_{\R}(s) := \pi^{-s/2}\Gamma(s/2)\qquad\text{and}\qquad \Gamma_{\C}(s):= 2(2\pi)^{-s}\Gamma(s)`

that appear in the {bpref "lfunction.functional_equation"}[functional equation] of an L-function are known as *gamma factors*.  Here $`\Gamma(s):=\int_0^\infty e^{-t}t^{s-1}dt` is Euler's gamma function.

The gamma factors satisfy
$`\Gamma_{\C}(s) = \Gamma_{\R}(s) \Gamma_{\R}(s + 1)`
and can also be viewed as "missing" factors of the {bpref "lfunction.euler_product"}[Euler product] of an L-function corresponding to (real or complex) archimedean places.

Depends on: {uses "lfunction.euler_product"}[]
:::

:::definition "lfunction.leading_coeff"
*Leading coefficient.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.leading_coeff))

The *leading coefficient* of an {bpref "lfunction.arithmetic"}[arithmetic L-function] is the first nonzero coefficient of its Laurent series expansion at the {bpref "lfunction.central_point"}[central point].

Depends on: {uses "lfunction.arithmetic"}[] {uses "lfunction.central_point"}[]
:::

:::definition "lfunction.normalization"
*Normalization of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.normalization))

In its *arithmetic normalization*, an L-function $`L(s)` of weight $`w` has its central value at $`s=\frac{w+1}{2}`
and the {bpref "lfunction.functional_equation"}[functional equation] relates
$`s` to $`1 + w - s`.
For L-functions defined by an Euler product $`\prod_p L_p(s)^{-1}` where the coefficients of $`L_p` are algebraic integers, this is the usual normalization implied by the definition.

The *analytic normalization* of an L-function is defined by $`L_{an}(s):=L(s+w/2)`, where $`L(s)` is the L-function in its arithmetic normalization.  This moves the central value to $`s=1/2`, and the {bpref "lfunction.functional_equation"}[functional equation] of $`L_{an}(s)` relates $`s` to $`1-s`.

Depends on: {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.rh"
*Generalized Riemann hypothesis.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.rh))

The *Riemann hypothesis* is the assertion that if $`\rho` is a zero of an
 {bpref "lfunction"}[analytic L-function] then $`\mathrm{Re}(\rho)>0` implies
that $`\mathrm{Re}(\rho)=1/2.`

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.self-dual"
*Self-dual L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.self-dual))

An L-function $`L(s) = \sum_{n=1}^{\infty} \frac{a_n}{n^s}` is called *self-dual* if its Dirichlet coefficients $`a_n` are real.
:::

:::definition "lfunction.sign"
*Sign of the functional equation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.sign))

The *sign* of the functional equation of an analytic L-function, also called the *root number*, is the complex number $`\varepsilon` that appears in the {bpref "lfunction.functional_equation"}[functional equation] of $`\Lambda(s)=\varepsilon \overline{\Lambda}(1-s)`.  The sign appears as the 4th entry in the quadruple
known as the Selberg data.

Depends on: {uses "lfunction.functional_equation"}[]
:::

:::definition "mf.half_integral_weight.dedekind_eta"
*Dedekind eta function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.half_integral_weight.dedekind_eta))

We define the *Dedekind eta function* $`\eta(z)` by the formula

$$`\eta(z)=q^{1/24}\prod_{n\geq1}(1-q^n),`

where $`q=e^{2\pi iz}`.

It is related to the Discriminant modular form via the formula

$$`\Delta(z)=\eta^{24}(z).`
:::

:::definition "mf.upper_half_plane"
*Upper half-plane.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.upper_half_plane))

The *upper half-plane* $`\mathcal{H}` is the set of complex numbers whose imaginary part is positive, endowed with the topology induced from $`\C`.

The *completed upper* half-plane $`\mathcal{H}^*` is

$$`\mathcal{H} \cup \Q \cup \{ \infty\},`

endowed with the topology such that the disks tangent to the real line at $`r \in \Q` form a fundamental system of neighbourhoods of $`r`, and strips $`\{ z \in \mathcal{H} \mid \operatorname{Im} z > y \} \cup \{ \infty\}`, $`y>0`, form a fundamental system of neighbourhoods of $`\infty`, which should therefore be thought of as $`i \infty`.

The {bpref "group.sl2z"}[modular group] $`\SL_2(\Z)` acts properly discontinuously on $`\mathcal{H}` and $`\mathcal{H}^*` by the formula

$$`\left( \begin{matrix} a & b \\ c& d \end{matrix} \right) \cdot z = \frac{az+b}{cz+d},`

with the obvious conventions regarding $`\infty`.

Depends on: {uses "group.sl2z"}[]
:::

:::definition "modcurve"
*Modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve))

For each {bpref "gl2.open"}[open subgroup] $`H \le \GL_2(\widehat{\Z})`, there is a *modular curve* $`X_H`, defined as a quotient of the {bpref "modcurve.xn"}[full modular curve] $`X_{\text{full}}(N)`, where $`N` is the {bpref "gl2.level"}[level] of $`H`.  More precisely, $`H` is the inverse image of a subgroup $`H_N \le \GL_2(\Z/N\Z)`, which acts on $`X_{\text{full}}(N)` over $`\Q`, and $`X_H` is the {bpref "ag.quotient_curve"}[quotient curve] $`H_N \backslash X_{\text{full}}(N)`, also defined over $`\Q`.

Like $`X_{\text{full}}(N)`, the curve $`X_H` is {bpref "ag.curve.smooth"}[smooth], projective, and integral, and when $`\det(H)=\widehat{\Z}` it is also geometrically integral, but in general it may have several geometric components, as is the case for $`X_{\text{full}}(N)` when $`N>2`.

*Rational points*: When $`-1\in H` the rational points of $`X_H`  consist of  {bpref "modcurve.cusps"}[cusps] and $`\Gal_{\Q}`-stable isomorphism classes of pairs $`(E,[\iota]_H)`, where $`E` is an {bpref "ec"}[elliptic curve] over $`\Q`, and $`[\iota]_H` is an {bpref "modcurve.level_structure"}[$`H`-level structure] on $`E`.  Such points exist precisely when the image of the {bpref "ec.galois_rep"}[adelic Galois representation] $`\rho_E\colon \Gal_{\Q}\to \GL_2(\widehat{\Z})` is conjugate to a subgroup of $`H`.

*Complex points*: The {bpref "cmf.congruence_subgroup"}[congruence subgroup] $`\Gamma_H:= H\cap \SL_2(\Z)` acts on the {bpref "mf.upper_half_plane"}[completed upper half-plane] $`\overline{\mathfrak{h}}`; one connected component of $`X_H(\C)` is biholomorphic to the quotient $`\Gamma_H \backslash \overline{\mathfrak{h}}`.

The curve $`X_H` can alternatively be constructed as the coarse moduli space of the stack $`\mathcal X_H` over $`\Q` defined in Deligne-Rapoport .  Both constructions of $`X_H` can be carried out over any field of characteristic not dividing $`N`, or even over $`\Z[1/N]`.

Depends on: {uses "ag.curve.smooth"}[] {uses "ag.quotient_curve"}[] {uses "cmf.congruence_subgroup"}[] {uses "ec"}[] {uses "ec.galois_rep"}[] {uses "gl2.level"}[] {uses "gl2.open"}[] {uses "mf.upper_half_plane"}[] {uses "modcurve.cusps"}[] {uses "modcurve.level_structure"}[] {uses "modcurve.xn"}[]
:::

:::definition "modcurve.cusps"
*Cusps of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.cusps))

The *cusps* on $`X_H` are the points whose image under the canonical morphism $`j\colon X_H\to X(1)\simeq \mathbb{P}^1` is $`\infty`.  It is only the noncuspidal points that parametrize elliptic curves (with level structure).

The *cusps* of a modular curve $`X_H` correspond to the complement of $`Y_H` in $`X_H`, where $`Y_H` is the coarse moduli stack $`\mathcal M_H^0` defined in .

The *rational cusps* (also called *$`\Q`-cusps*) are the cusps fixed by $`\Gal_{\Q}`.
:::

:::definition "modcurve.level_structure"
*Level structure of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.level_structure))

Let $`H` be an {bpref "gl2.open"}[open subgroup] of $`\GL_2(\widehat{\Z})` of {bpref "gl2.level"}[level] $`N`, let $`\pi_N\colon \GL_2(\widehat{\Z})\to \GL_2(\Z/N\Z)` be the natural projection, and let $`E` be an {bpref "ec"}[elliptic curve] over a {bpref "nf"}[number field] $`K`.

An *$`H`-level structure* on $`E` is the $`H`-orbit $`[\iota]_H:=\{ h\circ \iota\colon h\in \pi_N(H)\}` of an isomorphism $`\iota\colon E[N]\overset{\sim}{\rightarrow}(\Z/N\Z)^2`.

An $`H`-level structure on $`E` is *rational* if it lies in a $`\Gal_K`-stable isomorphism class of pairs $`(E,[\iota]_H)`, where $`\sigma\in \Gal_K` acts via $`(E,[\iota]_H)\mapsto (E^\sigma,[\iota\circ\sigma^{-1}]_H)`.
Two pairs $`(E,[\iota]_H)` and $`(E',[\iota']_H)` are isomorphic if there is an isomorphism $`\phi\colon E\to E'` that induces an isomorphism $`\phi_N\colon E[N]\to E'[N]` for which $`\phi_N^*([\iota']_H) = [\iota]_H`.

If $`E` admits a rational $`H`-level structure $`[\iota]_H` then image of its {bpref "ec.galois_rep"}[adelic Galois representation] $`\rho_E\colon \Gal_K\to \GL_2(\widehat{\Z})` is conjugate to a subgroup of $`H` and the isomorphism class of $`(E,[\iota]_H)` is a non-cuspidal $`K`-rational point on the modular curve $`X_H`.

When $`-1\in H` every non-cuspidal $`K`-rational point on $`X_H` arises in this way.  When $`-1\not\in H` this is almost true, but there may be exceptions at points with $`j(E)=0,1728`.

Invariants of a rational $`H`-level structure include:

- *Cyclic $`\boldsymbol{N}`-isogeny field degree*: the minimal degree of an extension $`L/K` over which the {bpref "ec.base_change"}[base change] $`E_L` admits a rational cyclic isogeny of degree $`N`; equivalently, the index of the largest subgroup of $`H` fixing a subgroup of $`(\Z/N\Z)^2` isomorphic to $`\Z/N\Z`.

- *Cyclic $`\boldsymbol{N}`-torsion field degree*: the minimal degree of an extension $`L/K` for which $`E_L` has a rational point of order $`N`; equivalently, the index of the largest subgroup of $`H` that fixes a point of order $`N` in $`(\Z/N\Z)^2`.

- *N-torsion field degree* the minimal degree of an extension $`L/K` for which $`E[N]\subseteq E(L)`; this is simply the cardinality of the reduction of $`H` to $`\GL_2(\Z/N\Z)`.

Depends on: {uses "ec"}[] {uses "ec.base_change"}[] {uses "ec.galois_rep"}[] {uses "gl2.level"}[] {uses "gl2.open"}[] {uses "nf"}[]
:::

:::definition "modcurve.xn"
*Modular curve $`X(N)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xn))

There are three variants of the modular curve $`Y(N)`:

1. There is a functor sending each $`\Z[1/N]`-algebra $`R` to the set of (isomorphism classes of) pairs $`(E,\alpha)` such that $`E` is an {bpref "ec.ring"}[elliptic curve over $`R`] and $`\alpha \colon E[N] \to (\Z/N\Z)^2` is an isomorphism of group schemes.  Suppose that $`N \ge 3`; then this functor is represented by a smooth affine $`\mathbb{Z}[1/N]`-scheme $`Y_{\mathrm{full}}(N)`, called the *full modular curve of level $`N`*.  (If $`N<3`, it is representable only by an algebraic stack, and one must take the coarse moduli space to get a scheme.)  For any field $`k` with $`\operatorname{char} k \nmid N`, the set $`Y_{\mathrm{full}}(N)(k)` is the set of isomorphism classes of triples $`(E,P,Q)` , where $`E` is an elliptic curve over $`k` and $`P,Q \in E(k)` form a $`(\Z/N\Z)`-basis of $`E[N]`.  The curve $`Y_{\mathrm{full}}(N)_{\Q}` is integral but typically has several geometric components.

2. Let $`\zeta_N \in \overline{\Q}` be a primitive $`N`th root of unity.  There is a functor sending each $`\Z[1/N,\zeta_N]`-algebra $`R` to the set of pairs $`(E,\alpha)` such that $`E` is an elliptic curve over $`R` and $`\alpha \colon E[N] \to (\Z/N\Z)^2` is an isomorphism of group schemes such that the resulting elements $`P,Q \in E[N](R)` satisfy $`e_N(P,Q)=\zeta_N`.  For $`N \ge 3`, this functor is represented by a smooth affine $`\Z[1/N,\zeta_N]`-scheme $`Y(N)`, called the *classical modular curve of level $`N`*.  Over any {bpref "ring.a-field"}[$`\Z[1/N,\zeta_N]`-field] $`k`, the curve $`Y(N)_k` is geometrically integral.

3. There is a functor sending each $`\Z[1/N]`-algebra $`R` to the set of pairs $`(E,\alpha)` consisting of an elliptic curve $`E` over $`R` and a {bpref "alg.symplectic_isomorphism"}[symplectic isomorphism] $`\alpha \colon E[N] \to \Z/N\Z \times \mu_N`.  For $`N \ge 3`, this functor is represented by a smooth affine $`\mathbb{Z}[1/N]`-scheme $`Y_{\mathrm{arith}}(N)`.  Over any field $`k` with $`\operatorname{char} k \nmid N`, the curve $`Y_{\mathrm{arith}}(N)_k` is geometrically integral.

- Relationships\*: Over any {bpref "ring.a-field"}[$`\Z[1/N,\zeta]`-field] $`k`, the curve $`Y_{\mathrm{arith}}(N)_k` is isomorphic to $`Y(N)_k` and to a connected component of $`Y_{\mathrm{full}}(N)_k`.

- Complex points\*: The group {bpref "cmf.congruence_subgroup"}[$`\Gamma(N)`] acts on the {bpref "mf.upper_half_plane"}[upper half-plane] $`\mathfrak{h}`, and the quotient $`\Gamma(N) \backslash \mathfrak{h}` is biholomorphic to $`Y(N)(\mathbb{C}) \simeq Y_{\textup{arith}}(\C)` (choosing $`\zeta_N \in \C`).

- Compactifications\*: For each variant, there is a corresponding smooth projective model, denoted $`X_{\mathrm{full}}(N)`, $`X(N)`, or $`X_{\mathrm{arith}}(N)`.

- Quotients\*: For each {bpref "gl2.open"}[open subgroup] $`H \le \GL_2(\widehat{\Z})`, there is a quotient {bpref "modcurve"}[$`X_H`] of $`X_{\mathrm{full}}(N)`.

Depends on: {uses "alg.symplectic_isomorphism"}[] {uses "cmf.congruence_subgroup"}[] {uses "ec.ring"}[] {uses "gl2.open"}[] {uses "mf.upper_half_plane"}[] {uses "ring.a-field"}[]
:::

:::definition "ring"
*Definition of ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring))

A *ring* is a set $`R` with two {bpref "alg.binary_operation"}[binary operations] $`+` and $`\cdot` such that

1. $`R` is an {bpref "group.abelian"}[abelian group] with respect to $`+`
2. $`\cdot` is {bpref "alg.binary_operation.associative"}[associative] on $`R`
3. the distributive laws hold, i.e., for all $`a,b,c\in R`,

$$`a\cdot(b+c) = a\cdot b+a\cdot c \qquad \text{and}\qquad (b+c)\cdot a = b\cdot a+c\cdot a`

4. there is an {bpref "alg.binary_operation.identity"}[identity element] with respect to the operation $`\cdot`, typically denoted by $`1_R` or, more simply, by $`1`.

The {bpref "alg.binary_operation.identity"}[identity] element of $`R` as a group with respect to $`+` is typically denoted by $`0_R` or, more simply, by $`0`.

The ring $`R` is a *commutative ring* if $`R` is a ring such that the operation $`\cdot` is {bpref "alg.binary_operation.commutative"}[commutative] on $`R`.

We say that $`R` is a *rng* (also called *ring without identity*) if conditions 1-3 (but not necessarily 4) are satisfied.

Depends on: {uses "alg.binary_operation"}[] {uses "alg.binary_operation.associative"}[] {uses "alg.binary_operation.commutative"}[] {uses "alg.binary_operation.identity"}[] {uses "group.abelian"}[]
:::

:::definition "ring.a-field"
*$`A`-field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.a-field))

Let $`A` be a commutative ring.  An *$`A`-field* is an $`A`-algebra that is a {bpref "ring.field"}[field].

Depends on: {uses "ring.field"}[]
:::

:::definition "ring.characteristic"
*Characteristic of a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.characteristic))

The *characteristic* of a {bpref "ring"}[ring] is the least positive integer $`n` for which

$$`\underbrace{1+\cdots + 1}_n = 0,`

if such an $`n` exists, and $`0` otherwise. Equivalently, it is the exponent of the additive {bpref "group"}[group] of the ring.

The characteristic of a {bpref "ring.field"}[field] $`k` is either $`0` or a prime number $`p`, depending on whether the prime field of $`k` is isomorphic to $`\Q` or $`\F_p`.

Depends on: {uses "group"}[] {uses "ring"}[] {uses "ring.field"}[]
:::

:::definition "ring.dedekind_domain"
*Dedekind domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.dedekind_domain))

A *Dedekind domain* $`D` is a {bpref "ring.integral_domain"}[integral domain] which is not a {bpref "ring.field"}[field] such that

1. $`D` is {bpref "ring.noetherian"}[Noetherian];
2. every non-zero {bpref "ring.prime_ideal"}[prime ideal] is {bpref "ring.maximal_ideal"}[maximal];
3. $`D` is {bpref "ring.integrally_closed"}[integrally closed].

The {bpref "nf.ring_of_integers"}[ring of integers] of a {bpref "nf"}[number field] is always a Dedekind domain, as is every discrete valuation ring.

In a Dedekind domain, every non-zero {bpref "ring.ideal"}[ideal] $`I` can be written as a product of non-zero {bpref "ring.prime_ideal"}[prime ideals],

$$`I=P_1P_2\cdots P_k,`

and the product is unique up to the order of the factors.  Repeated factors are often grouped, so we write $`I=Q_1^{e_1}\cdots Q_g^{e_g}` where the $`Q_i` are non-zero prime ideals of $`D`.

In addition, every {bpref "ring.fractional_ideal"}[fractional ideal] $`I` is invertible in the sense that there exists a fractional ideal $`J` such that $`IJ=D`.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[] {uses "ring.field"}[] {uses "ring.fractional_ideal"}[] {uses "ring.ideal"}[] {uses "ring.integral_domain"}[] {uses "ring.integrally_closed"}[] {uses "ring.maximal_ideal"}[] {uses "ring.noetherian"}[] {uses "ring.prime_ideal"}[]
:::

:::definition "ring.field"
*Field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.field))

A *field* is a {bpref "ring"}[commutative ring] $`R` such that $`0_R\neq 1_R` and every nonzero element of $`R` has an {bpref "alg.binary_operation.inverse"}[inverse] in $`R` with respect to multiplication.

Depends on: {uses "alg.binary_operation.inverse"}[] {uses "ring"}[]
:::

:::definition "ring.field_of_fractions"
*Field of fractions of an integral domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.field_of_fractions))

If $`R` is an {bpref "ring.integral_domain"}[integral domain], then its *field of fractions* $`F` is the smallest {bpref "ring.field"}[field] containing $`R`.

It can be constructed by mimicking the set of fractions $`a/b` where $`a,b\in R` with $`b\neq 0` following the usual rules for fraction arithmetic.  It is unique, up to unique isomorphism.

Depends on: {uses "ring.field"}[] {uses "ring.integral_domain"}[]
:::

:::definition "ring.fractional_ideal"
*Fractional ideal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.fractional_ideal))

If $`R` is an {bpref "ring.integral_domain"}[integral domain] with {bpref "ring.field_of_fractions"}[field of fractions] $`K`, then a *fractional ideal* $`I` of $`R` is an $`R`-submodule of $`K` such that there exists $`d\in R-\{0\}` with
$$`dI=\{da\mid a\in I\} \subseteq R\,.`

Depends on: {uses "ring.field_of_fractions"}[] {uses "ring.integral_domain"}[]
:::

:::definition "ring.ideal"
*Ideal of a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.ideal))

If $`R` is a {bpref "ring"}[ring], a subset $`I\subseteq R` is an *ideal* of $`R` if $`I` is a {bpref "group.subgroup"}[subgroup] of $`R` for $`+` and for all $`a\in I` and all $`r\in R`,

$$`r\cdot a\in I \qquad\text{and}\qquad a\cdot r\in I.`

In a polynomial ring $`R[X_1,\dots,X_n]`, an ideal is *homogeneous* if it can be generated by homogeneous polynomials.

Depends on: {uses "group.subgroup"}[] {uses "ring"}[]
:::

:::definition "ring.integral"
*Integral element of a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.integral))

If $`R\subseteq S` are {bpref "ring"}[commutative rings], an element $`s\in S` is *integral* over $`R` if there exists $`n\in\Z^+` and $`a_i\in R` such that

$$`s^n+a_{n-1} s^{n-1}+\cdots + a_0 =0\,.`

The *integral closure* of $`R` in $`S` is $`\{s\in S\mid s \text{ is integral over } R\}`.

Depends on: {uses "ring"}[]
:::

:::definition "ring.integral_domain"
*Integral domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.integral_domain))

An *integral domain* is a {bpref "ring"}[commutative ring] $`R` such that $`1_R\neq 0_R` and $`R` contains no {bpref "ring.zero_divisor"}[zero divisors].

Depends on: {uses "ring"}[] {uses "ring.zero_divisor"}[]
:::

:::definition "ring.integrally_closed"
*Integrally closed.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.integrally_closed))

Let $`R` be an {bpref "ring.integral_domain"}[integral domain] and $`F` its {bpref "ring.field_of_fractions"}[field of fractions].  Then $`R` is *integrally closed* if $`R` equals the {bpref "ring.integral"}[integral closure] of $`R` in $`F`.

Depends on: {uses "ring.field_of_fractions"}[] {uses "ring.integral"}[] {uses "ring.integral_domain"}[]
:::

:::definition "ring.irreducible"
*Irreducible element.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.irreducible))

An element $`x \ne 0` of a {bpref "ring"}[commutative ring] $`R` is *irreducible* if it is not a {bpref "ring.unit"}[unit] and has the property that  whenever $`x=yz` for some $`y,z \in R`, either $`y` or $`z` is a unit.

Depends on: {uses "ring"}[] {uses "ring.unit"}[]
:::

:::definition "ring.maximal_ideal"
*Maximal ideal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.maximal_ideal))

In a {bpref "ring"}[ring] $`R`, an {bpref "ring.ideal"}[ideal] $`M` is *maximal* if $`M\neq R` and for all ideals $`I` of $`R`,

$$`M\subseteq I \subseteq R\implies M=I\quad\text{or}\quad I=R.`

Depends on: {uses "ring"}[] {uses "ring.ideal"}[]
:::

:::definition "ring.noetherian"
*Noetherian ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.noetherian))

A {bpref "ring"}[commutative ring] $`R` is *Noetherian* if for every ascending chain of {bpref "ring.ideal"}[ideals]

$$`I_1\subseteq I_2\subseteq I_3\subseteq \cdots`

there exists $`N` such that for all $`n\geq N`, $`I_n=I_N`.

Depends on: {uses "ring"}[] {uses "ring.ideal"}[]
:::

:::definition "ring.prime_ideal"
*Prime ideal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.prime_ideal))

If $`R` is a {bpref "ring"}[commutative ring] $`R`, an {bpref "ring.ideal"}[ideal] $`I` is *prime* if for all $`a,b\in R`,

$$`ab\in I \implies a\in I \quad \text{or}\quad b\in I.`

Depends on: {uses "ring"}[] {uses "ring.ideal"}[]
:::

:::definition "ring.principal_fractional_ideal"
*Principal fractional ideal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.principal_fractional_ideal))

Let $`R` be an {bpref "ring.integral_domain"}[integral domain] with {bpref "ring.field_of_fractions"}[field of fractions] $`K`.  If $`a\in K^\times`, then the *principal fractional ideal* generated by $`a` is the set

$$`\{ar\mid r\in R\}\,.`

Depends on: {uses "ring.field_of_fractions"}[] {uses "ring.integral_domain"}[]
:::

:::definition "ring.unit"
*Unit in a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.unit))

A *unit* in a {bpref "ring"}[commutative ring] $`R` is an element $`x \in R` so that there exists $`y \in R` with $`xy = 1`.  The set of units in $`R` is denoted $`R^*` or $`R^\times` and forms a {bpref "group"}[group] under multiplication.

Depends on: {uses "group"}[] {uses "ring"}[]
:::

:::definition "ring.zero_divisor"
*Zero divisor.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.zero_divisor))

An element $`a` in a {bpref "ring"}[ring] $`R` is a *zero divisor* if $`a\neq 0_R` and there exists an element $`b\in R-\{0_R\}` such that

$$`a\cdot b = 0_R \qquad \text{or}\qquad b\cdot a = 0_R.`

Depends on: {uses "ring"}[]
:::

:::definition "specialfunction.gamma"
*Euler gamma function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/specialfunction.gamma))

The *(Euler) gamma function $`\Gamma(z)`* is defined by the integral

$$`\Gamma(z) = \int_0^{ \infty } e^{-t} t^{z} \frac{dt}{t}`

for Re$`(z) > 0`. It satisfies the functional equation

$$`\Gamma(z+1) = z \Gamma(z),`

and can thus be continued into a meromorphic function on the complex plane, whose poles are at the non-positive integers $`\{0,-1,-2,\ldots\}`.
:::

:::definition "st_group.definition"
*Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.definition))

The *Sato-Tate group* of a motive $`X` is a compact Lie group $`G` containing (as a dense subset) the image of a representation that maps Frobenius elements to conjugacy classes.  When $`X` is an Artin motive, $`G` corresponds to the image of the {bpref "artin"}[Artin representation]; when $`X` is an {bpref "ag.abelian_variety"}[abelian variety] over a number field, one can define $`G` in terms of an $`\ell`-adic Galois representation attached to $`X`.

For motives of even weight $`w` and degree $`d`, the Sato-Tate group is a compact subgroup of the orthogonal group $`\mathrm{O}(d)`.  For motives of odd weight $`w` and even degree $`d`, the Sato-Tate group is a compact subgroup of the {bpref "st_group.usp"}[unitary symplectic group] $`\mathrm{USp}(d)`.  For motives $`X` arising as {bpref "ag.abelian_variety"}[abelian varieties], the weight is always $`w=1` and the the degree is $`d=2g`, where $`g` is the {bpref "ag.dimension"}[dimension] of the variety.

The simplest case is when $`X` is an {bpref "ec"}[elliptic curve] $`E/\Q`, in which case $`G` is either $`\mathrm{SU}(2)=\mathrm{USp}(2)` (the generic case), or $`G` is $`N(\mathrm{U}(1))`, the normalizer of the subgroup $`\mathrm{U}(1)` of diagonal matrices in $`\mathrm{SU}(2)`, which contains $`\mathrm{U}(1)` with index 2.

The generalized Sato-Tate conjecture states that when ordered by norm, the sequence of images of Frobenius elements under this representation is equidistributed with respect to the pushforward of the {bpref "group.haar_measure"}[Haar measure] of $`G` onto its set of conjugacy classes.
This is known for all elliptic curves over {bpref "nf.totally_real"}[totally real] number fields (including $`\mathbb{Q}`) or {bpref "nf.cm_field"}[CM fields].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "artin"}[] {uses "ec"}[] {uses "group.haar_measure"}[] {uses "nf.cm_field"}[] {uses "nf.totally_real"}[] {uses "st_group.usp"}[]
:::

:::definition "st_group.symplectic_form"
*Symplectic form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.symplectic_form))

A *symplectic form* on a vector space $`V` over a field $`k` is a non-degenerate alternating bilinear form $`\omega\colon V\times V\to k`.  This means that

- if $`\omega(u,v)=0` for all $`v\in V` then $`u=0` (non-degenerate);

- $`\omega(v,v)=0` for all $`v\in V` (alternating);

- $`\omega(\lambda u+v,w)=\lambda\omega(u,v)+\omega(v,w)` and $`\omega(u,\lambda v+w)=\omega(u)+\lambda\omega(v,w)` for all $`\lambda\in k`, $`u,v,w\in V` (bilinear).

A finite dimensional vector space admitting a symplectic form $`\omega` necessarily has even dimension $`2n`, and in this case $`\omega` can be represented by a matrix $`\Omega\in k^{2n\times 2n}` that satisfies $`u^\intercal\Omega v=\omega(u,w)` for all $`u,v\in V`.  One can always choose a basis for $`V` so that

$$`\Omega = \begin{bmatrix} 0 & I_n\\ -I_n & 0\end{bmatrix},`

where $`I_n` denotes the $`n\times n` identity matrix.
:::

:::definition "st_group.usp"
*Unitary symplectic group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.usp))

For a positive even integer $`d` the *unitary symplectic group* $`\mathrm{USp}(d)` is
the group of unitary transformations of a $`d`-dimensional $`\C`-vector space equipped with a {bpref "st_group.symplectic_form"}[symplectic form] $`\Omega`.  In other words, the subgroup of $`\GL_d(\mathbb{C})` whose elements $`A` satisfy:

- $`A^{-1} = \bar A^{\intercal}` (unitary);

- $`A^\intercal \Omega A=\Omega` (symplectic).

It is a compact real Lie group that can also be viewed as the intersection of $`\mathrm{U}(d)` and $`\mathrm{Sp}(d,\C)` in $`\GL_d(\C)`.

Depends on: {uses "st_group.symplectic_form"}[]
:::
