import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Elliptic curves" =>

This chapter lists the LMFDB definitions relating to *elliptic curves*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "ec"
*Elliptic curve over a field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec))

An *elliptic curve* $`E` over a field $`k` is a {bpref "ag.curve.smooth"}[smooth] {bpref "ag.curve"}[projective curve] of {bpref "ag.curve.genus"}[genus] $`1` together with a distinguished $`k`-rational point $`O`.

The most commonly used model for elliptic curves is a {bpref "ec.weierstrass_coeffs"}[Weierstrass model]: a smooth plane cubic with the point $`O` as the unique point at infinity.

Depends on: {uses "ag.curve"}[] {uses "ag.curve.genus"}[] {uses "ag.curve.smooth"}[]
:::

:::definition "ec.additive_reduction"
*Additive reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.additive_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *additive reduction* at a prime $`\mathfrak{p}` of $`K` if the reduction of $`E` modulo $`\mathfrak{p}` has a cuspidal singularity.

Depends on: {uses "ec"}[] {uses "nf"}[]
:::

:::definition "ec.analytic_sha_order"
*Analytic order of $`\Sha`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.analytic_sha_order))

The *Tate-Shafarevich group* $`\Sha` of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is a {bpref "group.torsion"}[torsion] {bpref "group.abelian"}[abelian group], which can be defined in terms of Galois cohomology as

$$`\Sha(E) := \ker\left(H^1(G_K,E) \to \prod_v H^1(G_{K_v},E_{K_v}) \right),`

where $`v` runs over all {bpref "nf.place"}[places] of $`K` (finite and infinite), $`K_v` is the completion of $`K` at $`v`, $`E_{K_v}` is the {bpref "ec.base_change"}[base change] of $`E` to $`K_v`, and $`G_K` and $`G_{K_v}` denote {bpref "group.galois.absolute"}[absolute Galois groups].

The group $`\Sha` is conjectured to be finite, and its {bpref "group.order"}[order] appears in the strong form of the {bpref "ec.bsdconjecture"}[Birch-Swinnerton-Dyer Conjecture] for $`E`.  The order implied by the conjecture is called the *analytic order of Sha* and can be   defined as the real number

$$`\Sha_{\text{an}} := |D_K|^{1/2}\cdot \frac{L^{(r)}(E,1)} {r!} \cdot \frac{\#E(K)_{\rm tor}^2}{\mathrm{Reg}_{\rm NT}(E/K)}  \cdot \frac{1}{ \Omega(E/K)  \cdot \prod_{\mathfrak{p}} c_{\mathfrak{p}}}.`

Here
$`D_K` is the {bpref "nf.discriminant"}[discriminant] of $`K`,
$`L(E,s)` is the $`L`-function of $`E/K`, $`r` is the analytic {bpref "ec.rank"}[rank] of $`E/K`,
$`\mathrm{Reg}_{\rm NT}(E/K)` is the Neron-Tate (un-normalised) {bpref "ec.regulator"}[regulator] of $`E/K`,  $`E(K)_{\rm tor}` is the {bpref "ec.torsion_subgroup"}[torsion subgroup] of the {bpref "ec.mordell_weil_group"}[Mordell-Weil group] $`E(K)`,
$`\Omega(E/K)` is the {bpref "ec.period"}[global period] of $`E/K`,
and $`c_{\mathfrak{p}}` is the {bpref "ec.tamagawa_number"}[Tamagawa number] of $`E` at the {bpref "nf.prime"}[prime] $`\mathfrak{p}` of $`K`.

It is known that if $`\Sha` is finite then its order is a square, so one expects the real number $`\Sha_{\text{an}}` to always be a square integer.

For elliptic curves defined over $`\Q` of rank $`0` or $`1`, it is a theorem that $`\Sha`<sub>an</sub> is a positive rational number, and this rational number can in principle be computed exactly. This exact  computation has only been carried out for the curves in the database with rank $`0`.  For curves of rank $`2` and above, there is no such theorem, and the values computed are floating point approximate values which are very close to integers.  In the LMFDB we store and display the rounded values in this case.

Depends on: {uses "ec"}[] {uses "ec.base_change"}[] {uses "ec.mordell_weil_group"}[] {uses "ec.period"}[] {uses "ec.rank"}[] {uses "ec.regulator"}[] {uses "ec.tamagawa_number"}[] {uses "ec.torsion_subgroup"}[] {uses "group.abelian"}[] {uses "group.galois.absolute"}[] {uses "group.order"}[] {uses "group.torsion"}[] {uses "nf"}[] {uses "nf.discriminant"}[] {uses "nf.place"}[] {uses "nf.prime"}[]
:::

:::definition "ec.bad_reduction"
*Bad reduction of an elliptic curve at a prime.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.bad_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *bad reduction* at a {bpref "nf.prime"}[prime] $`\mathfrak{p}` of $`K` if the reduction of $`E` modulo $`\mathfrak{p}` is singular.
There are three types of bad reduction:

- {bpref "ec.split_multiplicative_reduction"}[split multiplicative],

- {bpref "ec.nonsplit_multiplicative_reduction"}[non-split multiplicative],

- {bpref "ec.additive_reduction"}[additive].

A curve has bad reduction at $`\mathfrak{p}` if and only if $`\mathfrak{p}` divides its {bpref "ec.discriminant"}[discriminant].

Depends on: {uses "ec"}[] {uses "ec.additive_reduction"}[] {uses "ec.discriminant"}[] {uses "ec.nonsplit_multiplicative_reduction"}[] {uses "ec.split_multiplicative_reduction"}[] {uses "nf"}[] {uses "nf.prime"}[]
:::

:::definition "ec.base_change"
*Base change.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.base_change))

If $`E` is an elliptic curve defined over a field $`K`, and $`L` is an extension field of $`K`, then the same equation defining $`E` as an elliptic curve over $`K` also defines a curve over $`L` called the *base change* of $`E` from $`K` to $`L`.   Any curve defined over $`L` which is isomorphic to $`E` over $`L` is called a base-change curve from $`K` to $`L`.  A sufficient but not necessary condition for a curve to be a base change is that the coefficients of its Weierstrass equation lie in $`K`.

When $`K=\Q` and $`L` is a number field, elliptic curves over $`L` which are base-changes of curves over $`\Q` may simply be called base-change curves.  A necessary, but not sufficient, condition for this is that the {bpref "ec.j_invariant"}[$`j`-invariant] of $`E` should be in $`\Q`.

Depends on: {uses "ec.j_invariant"}[]
:::

:::definition "ec.bsdconjecture"
*Birch Swinnerton-Dyer conjecture.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.bsdconjecture))

The *Birch and Swinnerton-Dyer* conjecture (*BSD*) is one of the Millennium Prize Problems listed by the Clay Mathematics Institute. It relates the order of vanishing (or {bpref "lfunction.analytic_rank"}[analytic rank]) and the {bpref "lfunction.leading_coeff"}[leading coefficient] of  the {bpref "lfunction"}[L-function] associated to an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` at the {bpref "lfunction.central_point"}[central point] $`s=1` to certain arithmetic data, the *BSD invariants* of $`E`.

- The _weak form_ of the BSD conjecture states just that the {bpref "lfunction.analytic_rank"}[analytic rank] $`r_{an}` (that is, the order of vanishing of vanishing of $`L(E,s)` at $`s=1`), is equal to the {bpref "ec.rank"}[rank] $`r` of  $`E/K`.

- The _strong form_ of the conjecture states that $`r=r_{an}` and also that the {bpref "lfunction.leading_coeff"}[leading coefficient] of the L-function is given by the formula

$$`\frac{1}{r!} L^{(r)}(E,1) = \frac{1}{|d_K|^{1/2}}\cdot \frac{\# \Sha(E/K)\cdot \Omega(E/K) \cdot \mathrm{Reg}_{\rm NT}(E/K) \cdot \prod_{\mathfrak{p}} c_{\mathfrak{p}}}{\#E(K)_{\rm tor}^2}.`

The quantities appearing in this formula are as follows:

- $`d_K` is the {bpref "nf.discriminant"}[discriminant] of $`K`;

- $`r` is the {bpref "ec.rank"}[rank] of $`E(K)`;

- $`\Sha(E/K)` is the {bpref "ec.analytic_sha_order"}[Tate-Shafarevich] group

 of $`E/K`;

- $`\mathrm{Reg}(E/K)` is the {bpref "ec.regulator"}[regulator] of $`E/K`;

- $`\Omega(E/K)` is the {bpref "ec.period"}[global period] of $`E/K`;

- $`c_{\mathfrak{p}}` is the {bpref "ec.tamagawa_number"}[Tamagawa number] of $`E` at each {bpref "nf.prime"}[prime] $`\mathfrak{p}` of $`K`;

- $`E(K)_{\rm tor}` is the {bpref "ec.torsion_subgroup"}[torsion subgroup] of $`E(K)`.

Implicit in the strong form of the conjecture is that the Tate-Shafarevich group $`\Sha(E/K)` is finite.

There is a similar conjecture for {bpref "ag.abelian_variety"}[abelian varieties] over number fields.

Depends on: {uses "ag.abelian_variety"}[] {uses "ec"}[] {uses "ec.analytic_sha_order"}[] {uses "ec.period"}[] {uses "ec.rank"}[] {uses "ec.regulator"}[] {uses "ec.tamagawa_number"}[] {uses "ec.torsion_subgroup"}[] {uses "lfunction"}[] {uses "lfunction.analytic_rank"}[] {uses "lfunction.central_point"}[] {uses "lfunction.leading_coeff"}[] {uses "nf"}[] {uses "nf.discriminant"}[] {uses "nf.prime"}[]
:::

:::definition "ec.canonical_height"
*Canonical height on an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.canonical_height))

Let $`E` be an {bpref "ec"}[elliptic curve] defined over a {bpref "nf"}[number field] $`K`.  The *canonical height* on $`E` is a function

$$`\hat{h}: E(K) \to \R_{ {}\ge0}`

defined on the {bpref "ec.mordell_weil_group"}[Mordell-Weil group] $`E(K)`
which induces a positive definite quadratic form on $`E(K)\otimes\R`.

One definition of $`\hat{h}(P)` is

$$`\hat{h}(P)=\lim_{n\to\infty} n^{-2}h\bigl(x(nP)\bigr),`
 where $`h(x)` is the {bpref "nf.weil_height"}[Weil height] of $`x\in K`.  This definition gives the non-normalised height.  A normalised height which is invariant under base-change is given by

$$`\frac{1}{[K:\Q]} \hat{h}(P).`

Related to the canonical height is the *height pairing*

$$`\langle-,-\rangle : E(K)\times E(K) \to \R`

defined by $`\langle P,Q\rangle = \frac{1}{2}(\hat{h}(P+Q)-\hat{h}(P)-\hat{h}(Q))`, which is a positive definite quadratic form on $`E(K)\otimes\R`, used in defining the {bpref "ec.regulator"}[regulator] of $`E/K`.

Depends on: {uses "ec"}[] {uses "ec.mordell_weil_group"}[] {uses "nf"}[] {uses "nf.weil_height"}[]
:::

:::definition "ec.complex_multiplication"
*Complex multiplication.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.complex_multiplication))

An {bpref "ec"}[elliptic curve] whose {bpref "ec.endomorphism_ring"}[endomorphism ring] is larger than $`\Z` is said to have *complex multiplication* (often abbreviated to CM).  In this case, for curves defined over fields of {bpref "ring.characteristic"}[characteristic] zero, the endomorphism ring is isomorphic to an {bpref "nf.order"}[order] in an imaginary quadratic field.  The discriminant of this order is the *CM discriminant*.

An elliptic curve whose {bpref "ec.geom_endomorphism_ring"}[geometric endomorphism ring] is larger than $`\Z` is said to have *potential complex multiplication* (potential CM).  In the literature, these too are often called CM elliptic curves.

The property of having potential CM depends only on the {bpref "ec.j_invariant"}[$`j`-invariant] of the curve.  In characteristic $`0`, CM $`j`-invariants are algebraic integers, and there are only finitely many in any given number field.  There are precisely 13 CM $`j`-invariants in $`\Q` (all integers), associated to the 13 imaginary quadratic orders of {bpref "nf.class_number"}[class number] $`1`:

$$`\begin{array}{c|ccccccccccccc}
j & -12288000 & 54000 & 0 & 287496 & 1728 & 16581375 & -3375 & 8000 & -32768 & -884736 & -884736000 & -147197952000 & -262537412640768000\\
\text{CM discriminant} &-27 & -12 & -3 & -16 & -4 & -28 & -7 & -8 & -11 & -19 & -43 & -67 & -163
\end{array}`

CM elliptic curves are examples of {bpref "ag.complex_multiplication"}[CM abelian varieties].

Depends on: {uses "ag.complex_multiplication"}[] {uses "ec"}[] {uses "ec.endomorphism_ring"}[] {uses "ec.geom_endomorphism_ring"}[] {uses "ec.j_invariant"}[] {uses "nf.class_number"}[] {uses "nf.order"}[] {uses "ring.characteristic"}[]
:::

:::definition "ec.conductor"
*Conductor of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.conductor))

The *conductor* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is an ideal of the {bpref "nf.ring_of_integers"}[ring of integers] of $`K` that is divisible by the prime ideals of {bpref "ec.bad_reduction"}[bad reduction] and no others.  It is defined as

$$`\mathfrak{n} = \prod_{\mathfrak{p}}\mathfrak{p}^{e_{\mathfrak{p}}}`

where the exponent $`e_{\mathfrak{p}}` is as follows:

- $`e_{\mathfrak{p}}=0` if $`E` has {bpref "ec.good_reduction"}[good reduction] at $`\mathfrak{p}`;

- $`e_{\mathfrak{p}}=1` if $`E` has {bpref "ec.multiplicative_reduction"}[multiplicative reduction] at $`\mathfrak{p}`;

- $`e_{\mathfrak{p}}=2` if $`E` has {bpref "ec.additive_reduction"}[additive reduction] at $`\mathfrak{p}` and $`\mathfrak{p}` does not lie above either $`2` or $`3`; and

- $`2\leq e_{\mathfrak{p}}\leq 2+6v_{\mathfrak{p}}(2)+3v_{\mathfrak{p}}(3)`, where $`v_{\mathfrak{p}}` is the valuation at $`\mathfrak{p}`, if $`E` has additive reduction and $`\mathfrak{p}` lies above $`2` or $`3`.

For $`\mathfrak{p}=2` and $`3`, there is an algorithm of Tate that simultaneously creates a minimal Weierstrass equation and computes the exponent of the conductor.  See:

<UL>
<LI> J. Tate, Algorithm for determining the type of a singular fiber
in an elliptic pencil, Modular functions of one variable, IV
(Proc. Internat. Summer School, Univ. Antwerp, Antwerp, 1972),
33-52. <EM>Lecture Notes in Math.</EM>, Vol. <B>476</B>,
Springer, Berlin, 1975.

<LI> J.H. Silverman, <EM>Advanced topics in the arithmetic of elliptic
curves</EM>, GTM <B>151</B>, Springer-Verlag, New York, 1994.

</UL>

The *conductor norm* is the norm $`[\mathcal{O}_K:\mathfrak{n}]` of the ideal $`\mathfrak{n}`.

Depends on: {uses "ec"}[] {uses "ec.additive_reduction"}[] {uses "ec.bad_reduction"}[] {uses "ec.good_reduction"}[] {uses "ec.multiplicative_reduction"}[] {uses "nf"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "ec.discriminant"
*Discriminant of a Weierstrass equation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.discriminant))

The *discriminant* $`\Delta` of a {bpref "ec.weierstrass_coeffs"}[Weierstrass equation] over a {bpref "ring.field"}[field] $`K` is an element of $`K` defined in terms of the {bpref "ec.q.minimal_weierstrass_equation"}[Weierstrass coefficients].
If the {bpref "ec.weierstrass_coeffs"}[Weierstrass equation] is
$$`y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,`
 then $`\Delta` is given by a polynomial expression in $`a_1,\dots,a_6`, namely,

$$`\Delta=-b_2^2b_8 - 8 b_4^3 -27 b_6 ^2 + 9 b_2 b_4 b_6`
 where

$$`\begin{aligned}
b_2 &= a_1^2 + 4 a_2\\
b_4 &= 2a_4 + a_1 a_3\\
b_6 &= a_3^2 + 4 a_6 \\
b_8 &= a_1^2 a_6 + 4 a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2.
\end{aligned}`

Then $`\Delta\neq 0` if and only if the equation defines a {bpref "ag.curve.smooth"}[smooth] curve, in which case its projective closure gives an {bpref "ec"}[elliptic curve].

Depends on: {uses "ag.curve.smooth"}[] {uses "ec"}[] {uses "ec.weierstrass_coeffs"}[] {uses "ring.field"}[]
:::

:::definition "ec.endomorphism"
*Endomorphism of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.endomorphism))

An *endomorphism* of an {bpref "ec"}[elliptic curve] defined over a field $`K` is a homomorphism $`\varphi\colon E\to E` defined over $`K`.  The set of all endomorphisms of $`E` forms a ring called the {bpref "ec.endomorphism_ring"}[endomorphism ring] of $`E`, denoted $`\End(E)`, a special case of the {bpref "ag.endomorphism_ring"}[endomorphism ring] of an {bpref "ag.abelian_variety"}[abelian variety].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_ring"}[] {uses "ec"}[]
:::

:::definition "ec.endomorphism_ring"
*Endomorphism ring of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.endomorphism_ring))

The *endomorphism ring* $`\End(E)` of an {bpref "ec"}[elliptic curve] $`E` over a field $`K` is the ring of all {bpref "ec.endomorphism"}[endomorphisms] of $`E` defined over $`K`.  For endomorphisms defined over extensions, we speak of the {bpref "ec.geom_endomorphism_ring"}[geometric endomorphism ring] of $`E`.

For elliptic curves defined over fields of characteristic zero, this ring is isomorphic to $`\Z`, unless the curve has {bpref "ec.complex_multiplication"}[complex multiplication] (CM) defined over the ground field, in which case the endomorphism ring is an order in an imaginary quadratic field; for curves defined over $`\Q`, this order is one of the 13 orders of class number one.

$`\End(E)` always contains a subring isomorphic to $`\Z`, since for $`m\in\Z` there is the multiplication-by-$`m` map $`[m] \colon E\to E`.

This is a special case of the {bpref "ag.endomorphism_ring"}[endomorphism ring] of an {bpref "ag.abelian_variety"}[abelian variety].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_ring"}[] {uses "ec"}[] {uses "ec.endomorphism"}[]
:::

:::definition "ec.galois_rep"
*Galois representations attached to an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.galois_rep))

If $`E` is an {bpref "ec"}[elliptic curve] defined over a field $`K` and $`m` is a positive integer, then the *mod-$`m` Galois representation* attached to $`E` is the continuous homomorphism

$$`\overline{\rho}_{E,m}: \Gal(\overline{K}/K) \to \Aut(E[m])`

describing the action of the {bpref "group.galois.absolute"}[absolute Galois group] of $`K` on the $`m`-torsion subgroup $`E[m]`.

When the characteristic of $`K` does not divide $`m > 1`, we may identify the finite abelian group $`E[m]` with $`(\Z/m\Z)^2` and hence view the representation as a map

$$`\overline{\rho}_{E,m}: \Gal(\overline{K}/K) \to \GL(2,\Z/m\Z)`

defined up to conjugation. In particular, when $`m=\ell` is a prime different from the characteristic of $`K`, we have the *mod-$`\ell` Galois representation*

$$`\overline{\rho}_{E,\ell}: \Gal(\overline{K}/K) \to \GL(2,\Z/\ell\Z).`

Taking the inverse limit over prime powers $`m=\ell^n` yields the *$`\ell`-adic Galois representation* attached to $`E`,

$$`\rho_{E,\ell}: \Gal(\overline{K}/K) \to \Aut(T_{\ell}(E)) \cong \GL(2,\Z_{\ell}),`

which describes the action of the {bpref "group.galois.absolute"}[absolute Galois group] of $`K` on $`T_{\ell}(E)`, the {bpref "ec.padic_tate_module"}[$`\ell`-adic Tate module] of $`E`.

When $`K` has characteristic zero one can take the inverse limit over all positive integers $`m` (ordered by divisibility) to obtain the *adelic Galois representation*

$$`\rho_{E}: \Gal(\overline{K}/K) \to \GL(2,\hat{\Z}).`

If $`E` is an elliptic curve without {bpref "ec.complex_multiplication"}[complex multiplication] that is defined over a {bpref "nf"}[number field], then the image of $`\rho_E` is an {bpref "gl2.open"}[open subgroup] of $`\GL(2,\hat{\Z})` that has an associated {bpref "gl2.level"}[level], {bpref "gl2.index"}[index], and genus.

Depends on: {uses "ec"}[] {uses "ec.complex_multiplication"}[] {uses "ec.padic_tate_module"}[] {uses "gl2.index"}[] {uses "gl2.level"}[] {uses "gl2.open"}[] {uses "group.galois.absolute"}[] {uses "nf"}[]
:::

:::definition "ec.galois_rep_adelic_image"
*Image of the adelic Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.galois_rep_adelic_image))

The image of the {bpref "ec.galois_rep"}[adelic Galois representation] associate to an elliptic curve $`E` over a number field $`K` that does not have {bpref "ec.complex_multiplication"}[potential complex multiplication] is an {bpref "gl2.open"}[open subgroup] $`H` of $`\GL(2,\widehat{\Z})`.  The subgroup $`H` has
the following invariants:

- The *level* of $`H` is the least positive integer $`N` such that $`H` is the full inverse image of its projection to $`\GL(2,\Z/N\Z)`.

- The *index* of $`H` is the positive integer $`[\GL(2,\Z/N\Z):H]`.

- The *genus* of $`H` is the genus of the corresponding {bpref "modcurve"}[modular curve] $`X_H`.

Depends on: {uses "ec.complex_multiplication"}[] {uses "ec.galois_rep"}[] {uses "gl2.open"}[] {uses "modcurve"}[]
:::

:::definition "ec.galois_rep_modell_image"
*Image of mod-$`l` Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.galois_rep_modell_image))

Let $`\ell` be a prime and let $`E` be an {bpref "ec"}[elliptic curve] defined over a {bpref "nf"}[number field] $`K`.

Subgroups $`G` of $`\GL(2,\F_{\ell})` that can arise as the image of the mod-$`\ell` {bpref "ec.galois_rep"}[Galois representation]

$$`\bar\rho_{E,\ell}\colon {\Gal}(\overline{K}/K)\to \GL(2,\F_{\ell})`

attached to $`E` that do not contain $`\SL(2,\F_{\ell})` are identified using the labels introduced by Sutherland in .  For groups with surjective determinant map (necessarily the case when $`K=\Q`), these labels have the form

$$`\texttt{LS.a.b.c},`

where $`\texttt{L}` is the prime $`\ell`, $`\texttt{S}` is one of *G*, *B*, *Cs*, *Cn*, *Ns*, *Nn*, *A4*, *S4*, *A5*, and $`\texttt{a}`, $`\texttt{b}`, $`\texttt{c}` are optional positive integers.  When the determinant map is not surjective the label has "$`\texttt{[d]}`", where $`d` is the index of the determinant image in $`\F_{\ell}^\times`.

When $`\bar\rho_{E,\ell}` does not contain $`\SL(2,\F_{\ell})`  the possibilities for $`\texttt{S}` are: {bpref "gl2.borel"}[Borel] *B*, {bpref "gl2.split_cartan"}[split Cartan] *Cs*, {bpref "gl2.normalizer_split_cartan"}[normalizer of the split Cartan] *Ns*,
{bpref "gl2.nonsplit_cartan"}[nonsplit Cartan] *Cn*, {bpref "gl2.normalizer_nonsplit_cartan"}[normalizer of the nonsplit Cartan] *Nn*,  {bpref "gl2.exceptional"}[exceptional] *A4*, *S4*, *A5*.  The cases *A4* and *A5* cannot occur when $`K=\Q`.

Depends on: {uses "ec"}[] {uses "ec.galois_rep"}[] {uses "gl2.borel"}[] {uses "gl2.exceptional"}[] {uses "gl2.nonsplit_cartan"}[] {uses "gl2.normalizer_nonsplit_cartan"}[] {uses "gl2.normalizer_split_cartan"}[] {uses "gl2.split_cartan"}[] {uses "nf"}[]
:::

:::definition "ec.geom_endomorphism_ring"
*Geometric endomorphism ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.geom_endomorphism_ring))

The *geometric endomorphism ring* of an elliptic curve $`E` over a field $`K` is $`\End(E_{\overline{K}})`, the {bpref "ec.endomorphism_ring"}[endomorphism ring] of the base change of $`E` to an algebraic closure $`\overline{K}` of $`K`.

This is a special case of the {bpref "ag.geom_endomorphism_ring"}[geometric endomorphism ring] of an {bpref "ag.abelian_variety"}[abelian variety].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.geom_endomorphism_ring"}[] {uses "ec.endomorphism_ring"}[]
:::

:::definition "ec.global_minimal_model"
*Global minimal model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.global_minimal_model))

A *global minimal model* for an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is a {bpref "ec.weierstrass_coeffs"}[Weierstrass equation] for $`E` which is {bpref "ec.integral_model"}[integral] and is a {bpref "ec.local_minimal_model"}[local minimal model] at all primes of $`K`.

When $`K` has {bpref "nf.class_number"}[class number] $`1` all elliptic curves over $`K` have global minimal models.  In general, there is an {bpref "ec.obstruction_class"}[obstruction] to the existence of a global minimal model for each elliptic curve $`E` defined over $`K`, which is an {bpref "nf.ideal_class_group"}[ideal class] of $`K`.  In case this class is nontrivial for $`E`, there is a {bpref "ec.semi_global_minimal_model"}[semi-global minimal model] for $`E`, which is minimal at all primes except one, the ideal class of that one prime being the {bpref "ec.obstruction_class"}[obstruction class].

Depends on: {uses "ec"}[] {uses "ec.integral_model"}[] {uses "ec.local_minimal_model"}[] {uses "ec.weierstrass_coeffs"}[] {uses "nf"}[] {uses "nf.class_number"}[] {uses "nf.ideal_class_group"}[]
:::

:::definition "ec.good_ordinary_reduction"
*Good ordinary reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.good_ordinary_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *ordinary reduction* at a prime $`\mathfrak{p}` of $`K` if the reduction $`E_{\mathfrak{p}}` of $`E` modulo $`\mathfrak{p}` is smooth, and $`E_{\mathfrak{p}}` is ordinary.

An elliptic curve $`E_{\mathfrak{p}}` defined over a finite field of characteristic $`p` is *ordinary* if $`E_{\mathfrak{p}}(\overline{\F_p})` has nontrivial $`p`-torsion.

Depends on: {uses "ec"}[] {uses "nf"}[]
:::

:::definition "ec.good_reduction"
*Good reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.good_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *good reduction* at a {bpref "nf.prime"}[prime] $`\mathfrak{p}` of $`K` if the reduction of $`E` modulo $`\mathfrak{p}` is {bpref "ag.curve.smooth"}[smooth].

If $`E` has good reduction at every prime of $`K` then $`E` is said to have *everywhere good reduction*.

Depends on: {uses "ag.curve.smooth"}[] {uses "ec"}[] {uses "nf"}[] {uses "nf.prime"}[]
:::

:::definition "ec.good_supersingular_reduction"
*Good supersingular reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.good_supersingular_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *supersingular reduction* at a prime $`\mathfrak{p}` of $`K` if the reduction $`E_{\mathfrak{p}}` of $`E` modulo $`\mathfrak{p}` is smooth, and $`E_{\mathfrak{p}}` is supersingular.

An elliptic curve $`E_{\mathfrak{p}}` defined over a finite field of characteristic $`p` is *supersingular* if $`E_{\mathfrak{p}}(\overline{\F_p})` has no $`p`-torsion.

Depends on: {uses "ec"}[] {uses "nf"}[]
:::

:::definition "ec.integral_model"
*Integral model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.integral_model))

An *integral model* for an {bpref "ec"}[elliptic curve] $`E` defined over a number field $`K` is a {bpref "ec.weierstrass_coeffs"}[Weierstrass equation] for $`E` all of whose coefficients are in the {bpref "nf.ring_of_integers"}[ring of integers] of $`K`.

Depends on: {uses "ec"}[] {uses "ec.weierstrass_coeffs"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "ec.invariants"
*Elliptic curve invariants.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.invariants))

The invariants of an {bpref "ec"}[elliptic curve] $`E` over a {bpref "nf"}[number field] $`K` are its

- {bpref "ec.conductor"}[conductor], $`\mathfrak{N}`, which is an integral {bpref "ring.ideal"}[ideal] of $`K` whose norm is the *conductor norm* $`N(\mathfrak{N})`

- {bpref "ec.minimal_discriminant"}[minimal discriminant], $`\mathfrak{D}`, also an integral ideal of $`K`, whose norm is the  *minimal discriminant norm* $`N(\mathfrak{D})`

- {bpref "ec.j_invariant"}[j-invariant], $`j`

- {bpref "ec.endomorphism_ring"}[endomorphism ring], $`\text{End}(E)`

- {bpref "st_group.definition"}[Sato-Tate group], $`\text{ST}(E)`

Each {bpref "ec.weierstrass_coeffs"}[Weierstrass model] for $`E` also has a {bpref "ec.discriminant"}[discriminant], $`\Delta`, and discriminant norm, $`N(\Delta)`, which are not strictly invariants of $`E` since different models have, in general, different discriminants.

Depends on: {uses "ec"}[] {uses "ec.conductor"}[] {uses "ec.discriminant"}[] {uses "ec.endomorphism_ring"}[] {uses "ec.j_invariant"}[] {uses "ec.minimal_discriminant"}[] {uses "ec.weierstrass_coeffs"}[] {uses "nf"}[] {uses "ring.ideal"}[] {uses "st_group.definition"}[]
:::

:::definition "ec.isogeny"
*Isogeny between elliptic curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.isogeny))

Let $`E_1` and $`E_2` be two {bpref "ec"}[elliptic curves] defined over a field $`K`. An *isogeny* (over $`K`) between $`E_1` and $`E_2` is a non-constant morphism $`f\colon E_1 \to E_2` defined over $`K`, i.e., a morphism of curves given by rational functions with coefficients in $`K`, such that $`f(O_{E_1})= O_{E_2}`.  Elliptic curves $`E_1` and $`E_2` are called *isogenous* if there exists an isogeny $`f\colon E_1 \to E_2`.

An isogeny respects the group laws on $`E_1` and $`E_2`, and hence determines a {bpref "group.homomorphism"}[group homomorphism] $`E_1(L)\to E_2(L)` for any extension $`L` of $`K`.  The kernel is a finite group, defined over $`K`; in general the points in the kernel are not individually defined over $`K` but over a finite {bpref "nf.is_galois"}[Galois] extension of $`K` and are permuted by the Galois action.

The *degree* of an isogeny is its degree as a morphism of algebraic curves.  For a separable isogeny this is equal to the cardinality of the kernel.  Over a field of characteristic $`0` such as a number field, all isogenies are separable.  In finite characteristic $`p`, isogenies of degree coprime to $`p` are all separable.

An isogeny is *cyclic* if its kernel is a cyclic group.  Every isogeny is the composition of a cyclic isogeny with the multiplication-by-$`m` map for some $`m\ge1`.

Isogeny is an equivalence relation, and the equivalence classes are called {bpref "ec.isogeny_class"}[*isogeny classes*].  Over a {bpref "nf"}[number field], it is a consequence of a theorem of Shafarevich that isogeny classes are finite.  Between any two curves in an isogeny class there is a unique degree of cyclic isogeny between them, except when the curves have  additional endomorphisms defined over the {bpref "ag.base_field"}[base field] of the curves; in that case there are cyclic isogenies of infinitely many different degrees between any two isogenous curves.

Isogenies from an elliptic curve $`E` to itself are called {bpref "ec.endomorphism"}[*endomorphisms*].  The set of all endomrpshisms of $`E` forms a ring under pointwise addition and composition, the {bpref "ec.endomorphism_ring"}[endomorphism ring] of $`E`.

An isogeny of elliptic curves is a special case of an {bpref "av.isogeny"}[isogeny of abelian varieties].

Depends on: {uses "ag.base_field"}[] {uses "av.isogeny"}[] {uses "ec"}[] {uses "ec.endomorphism"}[] {uses "ec.endomorphism_ring"}[] {uses "group.homomorphism"}[] {uses "nf"}[] {uses "nf.is_galois"}[]
:::

:::definition "ec.isogeny_class"
*Isogeny class of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.isogeny_class))

The *isogeny class (over a field $`K`)* of an {bpref "ec"}[elliptic curve] $`E` defined over $`K` is the set of all isomorphism classes of elliptic curves defined over $`K` that are {bpref "ec.isogeny"}[isogenous] to $`E` over $`K`.  Over a number field $`K` this is always a finite set; over $`\Q`, it has at most 8 elements by a theorem of Kenku .

Depends on: {uses "ec"}[] {uses "ec.isogeny"}[]
:::

:::definition "ec.isogeny_class_degree"
*Isogeny class degree.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.isogeny_class_degree))

The *isogeny class degree* of an {bpref "ec.isogeny_class"}[isogeny class] of {bpref "ec"}[elliptic curves] is the least common multiple of the degrees of all rational cyclic {bpref "ec.isogeny"}[isogenies] between elliptic curves in the isogeny class.

Depends on: {uses "ec"}[] {uses "ec.isogeny"}[] {uses "ec.isogeny_class"}[]
:::

:::definition "ec.isogeny_graph"
*Isogeny graph of an isogeny class of elliptic curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.isogeny_graph))

The *isogeny graph* of an {bpref "ec.isogeny_class"}[isogeny class] of {bpref "ec"}[elliptic curves] is the graph whose vertices are the isomorphism classes (over the base field) of elliptic curves in the isogeny class and whose edges are the isogenies of prime degree between the curves representing the vertices.

The vertices of the isogeny graphs in the LMFDB are labeled by the final entry of the LMFDB label of the corresponding (isomorphism classes of) elliptic curves. Their edges, of which there may be several between any two given vertices, are labeled by the prime that is the degree of the corresponding isogeny.

Depends on: {uses "ec"}[] {uses "ec.isogeny_class"}[]
:::

:::definition "ec.isogeny_matrix"
*Isogeny matrix of an isogeny class of elliptic curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.isogeny_matrix))

The *isogeny matrix* of an {bpref "ec.isogeny_class"}[isogeny class] of {bpref "ec"}[elliptic curves] is a symmetric matrix with integral entries that records the minimum among the degrees of the cyclic isogenies between the elliptic curves in the isogeny class.

In the LMFDB, the rows and columns of the matrices are ordered by the final entry of the label of the elliptic curves in the isogeny class in question, so that the $`(i,j)`-th entry is the smallest possible degree of a cyclic isogeny between the $`i`-th and $`j`-th curve in the isogeny class.

Depends on: {uses "ec"}[] {uses "ec.isogeny_class"}[]
:::

:::definition "ec.isomorphism"
*Isomorphism of elliptic curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.isomorphism))

An *isomorphism* between two {bpref "ec"}[elliptic curves] $`E`, $`E'` defined over a field $`K` is an {bpref "ec.isogeny"}[isogeny] $`f:E\to E'` such that there exist an {bpref "ec.isogeny"}[isogeny] $`g:E'\to E` with the compositions $`g\circ f` and $`f\circ g` being the identity maps.  Equivalently, an isomorphism $`E\to E'` is an isogeny of degree $`1`.

Isomorphism is an equivalence relation, the equivalnce classes being called *isomorphism classes*.

When $`E` and $`E'` are defined by {bpref "ec.weierstrass_coeffs"}[Weierstrass models], such an isomorphism is uniquely represented as a {bpref "ec.weierstrass_isomorphism"}[Weierstrass isomorphism] between these models.

Depends on: {uses "ec"}[] {uses "ec.isogeny"}[]
:::

:::definition "ec.j_invariant"
*j-invariant of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.j_invariant))

The *$`j`-invariant* of an {bpref "ec"}[elliptic curve] $`E` defined over a field $`K` is an invariant of the {bpref "ec.isomorphism"}[isomorphism class]  of $`E` over  $`\overline{K}`.
If the {bpref "ec.weierstrass_coeffs"}[Weierstrass equation] of $`E` is

$$`y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,`

then its $`j`-invariant is given by

$$`j = \frac{c_4^3}{\Delta}`
 where

$$`\begin{aligned}
b_2 &= a_1^2 + 4 a_2\\
b_4 &= 2a_4 + a_1 a_3\\
b_6 &= a_3^2 + 4 a_6 \\
b_8 &= a_1^2 a_6 + 4 a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2\\
c_4 &= b_2^2 - 24b_4
\end{aligned}`

and

$$`\Delta=-b_2^2b_8 - 8 b_4^3 -27 b_6 ^2 + 9 b_2 b_4 b_6`

is the {bpref "ec.discriminant"}[discriminant] of $`E.`

Depends on: {uses "ec"}[] {uses "ec.discriminant"}[] {uses "ec.isomorphism"}[] {uses "ec.weierstrass_coeffs"}[]
:::

:::definition "ec.kodaira_symbol"
*Kodaira symbol.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.kodaira_symbol))

The *Kodaira symbol* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] encodes the {bpref "ec.reduction_type"}[reduction type] of $`E` at a prime $`\mathfrak{p}` of $`K`. It describes the combinatorics of the special fiber of the Ne;ron model of the elliptic curve. The Ne;ron model is obtained from the {bpref "ec.local_minimal_model"}[local minimal model] for $`E` at $`\mathfrak{p}`  using Tate's algorithm. For an exact definition and properties, consult a text on elliptic curves.

Depends on: {uses "ec"}[] {uses "ec.local_minimal_model"}[] {uses "ec.reduction_type"}[] {uses "nf"}[]
:::

:::definition "ec.local_data"
*Local data of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.local_data))

The *local data* of an  {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K`  at a prime $`\mathfrak{p}` of $`K` consists of

- the {bpref "ec.tamagawa_number"}[Tamagawa number] $`c_{\mathfrak{p}}`

- the {bpref "ec.kodaira_symbol"}[Kodaira symbol]

- the {bpref "ec.reduction_type"}[reduction type]

- the local root number

- the conductor valuation $`\text{ord}_{\mathfrak{p}}(\mathfrak{N})`

- the discriminant\_valuation $`\text{ord}_{\mathfrak{p}}(\mathfrak{D})`

- the j-invariant denominator valuation $`\text{ord}_{\mathfrak{p}}(j)_{-}`

Depends on: {uses "ec"}[] {uses "ec.kodaira_symbol"}[] {uses "ec.reduction_type"}[] {uses "ec.tamagawa_number"}[] {uses "nf"}[]
:::

:::definition "ec.local_minimal_discriminant"
*Local minimal discriminant of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.local_minimal_discriminant))

Let $`E` be an {bpref "ec"}[elliptic curve] defined over a {bpref "nf"}[number field] $`K`, and $`\mathfrak{p}` a prime of $`K`.  The *local minimal discriminant* of $`E` is the ideal $`\mathfrak{p}^e` where $`e` is is the valuation of the discriminant of a {bpref "ec.local_minimal_model"}[local minimal model] for $`E` at $`\mathfrak{p}`.

Depends on: {uses "ec"}[] {uses "ec.local_minimal_model"}[] {uses "nf"}[]
:::

:::definition "ec.local_minimal_model"
*Local minimal model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.local_minimal_model))

A *local minimal model* for an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` at a prime $`\mathfrak{p}` of $`K` is a {bpref "ec.weierstrass_coeffs"}[Weierstrass equation] for $`E` all of whose coefficients are {bpref "nf.integral"}[integral]  at $`\mathfrak{p}`, and whose {bpref "ec.discriminant"}[discriminant] has minimal valuation at $`\mathfrak{p}` among all such equations.

Depends on: {uses "ec"}[] {uses "ec.discriminant"}[] {uses "ec.weierstrass_coeffs"}[] {uses "nf"}[] {uses "nf.integral"}[]
:::

:::definition "ec.maximal_elladic_galois_rep"
*Maximal $`l`-adic Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.maximal_elladic_galois_rep))

Let $`E` be an {bpref "ec"}[elliptic curve] over a {bpref "nf"}[number field] $`K`, let $`\ell` be prime, and let

$$`\rho_{E,\ell}\colon \Gal(\overline{K}/K)\to \Aut(E[\ell^\infty]) \simeq \GL_2(\Z_{\ell})`

be the {bpref "ec.galois_rep"}[$`\ell`-adic Galois representation] associated to $`E`.

If $`E` does not have {bpref "ec.complex_multiplication"}[potential complex multiplication], then $`\rho_{E,\ell}` is *maximal* if its image contains $`\SL_2(\Z_{\ell})`.

In general, let $`\mathcal{O}` be the {bpref "ec.geom_endomorphism_ring"}[geometric endomorphism ring] of $`E`.  Then $`E[\ell^\infty]` is an $`\mathcal{O}`-module, and we view $`\Aut_{\mathcal{O}}(E[\ell^\infty])` as a subgroup of $`\Aut(E[\ell^\infty]) \simeq \GL_2(\Z_{\ell})` that contains the image of $`\rho_{E,\ell}` whenever $`K` contains $`\mathcal O`.  We say that $`\rho_{E,\ell}` is *maximal* if its image contains $`\SL_2(\Z_{\ell}) \cap \Aut_{\mathcal{O}}(E[\ell^\infty])`, in which case we call $`\ell` a *maximal prime* for $`E`.

Depends on: {uses "ec"}[] {uses "ec.complex_multiplication"}[] {uses "ec.galois_rep"}[] {uses "ec.geom_endomorphism_ring"}[] {uses "nf"}[]
:::

:::definition "ec.maximal_galois_rep"
*Maximal Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.maximal_galois_rep))

Let $`E` be an {bpref "ec"}[elliptic curve] over a {bpref "nf"}[number field] $`K`, let $`\ell` be prime, and let

$$`\bar\rho_{E,\ell}\colon \Gal(\overline{K}/K)\to \Aut(E[\ell]) \simeq \GL_2(\F_{\ell})`

be the {bpref "ec.galois_rep"}[mod-$`\ell` Galois representation] associated to $`E`.

If E does not have {bpref "ec.complex_multiplication"}[potential complex multiplication], then $`\bar\rho_{E,\ell}` is *maximal* if its image contains $`\SL_2(\F_{\ell})`.

In general, let $`\mathcal{O}` be the {bpref "ec.geom_endomorphism_ring"}[geometric endomorphism ring].  Then $`E[\ell]` is an $`\mathcal{O}`-module and we view $`\Aut_{\mathcal{O}}(E[\ell]) \leq \Aut(E[\ell]) \simeq \GL_2(\F_{\ell})`.  We say that $`\bar\rho_{E,\ell}` is *maximal* if its image contains $`\SL_2(\F_{\ell}) \cap \Aut_{\mathcal{O}}(E[\ell])`.

For $`K=\Q`, the image of a maximal $`\bar\rho_{E,\ell}` is $`\GL_2(\F_{\ell})`, a {bpref "gl2.borel"}[Borel subgroup], the {bpref "gl2.normalizer_split_cartan"}[normalizer of a split Cartan subgroup], or the {bpref "gl2.normalizer_nonsplit_cartan"}[normalizer of a non-split Cartan subgroup], depending on whether $`\mathcal{O}=\Z` or $`\mathcal{O}\ne \Z` and $`\ell` is ramified, split, or inert in $`\mathcal{O}`, respectively.

Depends on: {uses "ec"}[] {uses "ec.complex_multiplication"}[] {uses "ec.galois_rep"}[] {uses "ec.geom_endomorphism_ring"}[] {uses "gl2.borel"}[] {uses "gl2.normalizer_nonsplit_cartan"}[] {uses "gl2.normalizer_split_cartan"}[] {uses "nf"}[]
:::

:::definition "ec.minimal_discriminant"
*Minimal discriminant.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.minimal_discriminant))

The *minimal discriminant* (or minimal discriminant ideal) of an {bpref "ec"}[elliptic curve] $`E` over a {bpref "nf"}[number field] $`K` is the ideal $`\mathfrak{D}_{min}` of the {bpref "nf.ring_of_integers"}[ring of integers] of $`K` given by

$$`\mathfrak{D}_{\mathrm{min}} = \prod_{\mathfrak{p}}\mathfrak{p}^{e_{\mathfrak{p}}},`

where the product is over all {bpref "nf.prime"}[primes] $`\mathfrak{p}` of $`K`, and  $`\mathfrak{p}^{e_{\mathfrak{p}}}` is the  {bpref "ec.local_minimal_discriminant"}[local minimal discriminant] of $`E` at $`\mathfrak{p}`.

If $`E` has a {bpref "ec.weierstrass_coeffs"}[Weierstrass model] which is a {bpref "ec.global_minimal_model"}[global minimal model] then $`\mathfrak{D}_{\mathrm{min}} = (\Delta)`, the principal ideal generated by the {bpref "ec.discriminant"}[discriminant] $`\Delta` of this model.  In general, $`\mathfrak{D}_{\mathrm{min}}` differs from the ideal generated by the discriminant of any {bpref "ec.weierstrass_coeffs"}[Weierstrass model] by the 12th power of an ideal.

Depends on: {uses "ec"}[] {uses "ec.discriminant"}[] {uses "ec.global_minimal_model"}[] {uses "ec.local_minimal_discriminant"}[] {uses "ec.weierstrass_coeffs"}[] {uses "nf"}[] {uses "nf.prime"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "ec.mordell_weil_group"
*Mordell-Weil group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.mordell_weil_group))

For an {bpref "ec"}[elliptic curve] $`E` defined over a field $`K`, the *Mordell-Weil group* of $`E/K` is the group $`E(K)` of $`K`-rational points of $`E`. It is a finitely-generated Abelian group.

This is a special case of the {bpref "ag.mordell_weil"}[Mordell-Weil group of an abelian variety].

The {bpref "ec.mordell_weil_theorem"}[Mordell-Weil Theorem], first proved by Mordell for elliptic curves defined over $`\Q` and  later generalized by Weil to {bpref "ag.abelian_variety"}[abelian varieties] $`A` over general {bpref "nf"}[number fields] $`K`, states that, if $`K` is a number field, then $`A(K)` is a finitely generated abelian group. Its {bpref "ec.rank"}[rank] is called the *Mordell-Weil rank* of $`A` over $`K`.

The Mordell-Weil theorem implies in particular that the {bpref "ec.torsion_subgroup"}[torsion subgroup] $`E(K)_{\mathrm{tor}}` of $`E(K)` is finite, and thus that the {bpref "ec.torsion_order"}[torsion order] of $`E`, one of the {bpref "ec.bsdconjecture"}[BSD]  invariants, is finite.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.mordell_weil"}[] {uses "ec"}[] {uses "nf"}[]
:::

:::definition "ec.mordell_weil_theorem"
*Mordell-Weil theorem.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.mordell_weil_theorem))

For an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`F`, the *Mordell-Weil theorem* states that the set $`E(F)` of $`F`-rational points on $`E` is a finitely generated Abelian group.

This group is called the {bpref "ec.mordell_weil_group"}[Mordell-Weil] group of $`E/K`.

Depends on: {uses "ec"}[] {uses "ec.mordell_weil_group"}[] {uses "nf"}[]
:::

:::definition "ec.multiplicative_reduction"
*Multiplicative reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.multiplicative_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *multiplicative reduction* at a prime $`\mathfrak p` of $`K` if the reduction of $`E` modulo $`\mathfrak p` has a nodal singularity.

The case of multiplicative reduction is further subdivided into {bpref "ec.split_multiplicative_reduction"}[split multiplicative reduction] and {bpref "ec.nonsplit_multiplicative_reduction"}[nonsplit multiplicative reduction].

Depends on: {uses "ec"}[] {uses "ec.nonsplit_multiplicative_reduction"}[] {uses "ec.split_multiplicative_reduction"}[] {uses "nf"}[]
:::

:::definition "ec.mw_generators"
*Mordell-Weil generators.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.mw_generators))

The *{bpref "ec.mordell_weil_group"}[Mordell-Weil group]* $`E(K)` of an {bpref "ec"}[elliptic curve] $`E` over a {bpref "nf"}[number field] $`K` is a finitely generated {bpref "group.abelian"}[abelian] group, explicitly described by giving a $`\Z`-basis for the group, equivalently, a (minimal) set of *Mordell-Weil generators*, each of which is a rational point on the curve.

The generators consist of $`r` *non-torsion generators*, where $`r` is the {bpref "ec.rank"}[rank] of $`E(K)`, and up to two *torsion generators*, which generate the {bpref "ec.torsion_subgroup"}[torsion subgroup] $`E(K)_{\textrm{tor}}`.

Depends on: {uses "ec"}[] {uses "ec.mordell_weil_group"}[] {uses "ec.rank"}[] {uses "ec.torsion_subgroup"}[] {uses "group.abelian"}[] {uses "nf"}[]
:::

:::definition "ec.nonsplit_multiplicative_reduction"
*Non-split multiplicative reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.nonsplit_multiplicative_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *non-split multiplicative reduction* at a prime $`\mathfrak{p}` of $`K` if the reduction of $`E` modulo $`\mathfrak{p}` has a nodal singularity with tangent slopes _not_ defined over the residue field at $`\mathfrak{p}`.

Depends on: {uses "ec"}[] {uses "nf"}[]
:::

:::definition "ec.obstruction_class"
*Obstruction class of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.obstruction_class))

Let $`E` be an {bpref "ec"}[elliptic curve] defined over a {bpref "nf"}[number field] $`K`.  The *obstruction class* of $`E` is an {bpref "nf.ideal_class_group"}[ideal class] of $`K` which is trivial if and only if $`E` has a {bpref "ec.global_minimal_model"}[global minimal model].

Depends on: {uses "ec"}[] {uses "ec.global_minimal_model"}[] {uses "nf"}[] {uses "nf.ideal_class_group"}[]
:::

:::definition "ec.padic_tate_module"
*Tate module of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.padic_tate_module))

Let $`p \in \mathbb{Z}_{\geq 0}` be a prime and $`E` an elliptic curve defined over a field $`K`. The *$`p`-adic Tate module* of $`E` is the inverse limit

$$`T_p(E) = \lim_{\xleftarrow[n \in \mathbb{N}]{}} E[p^n].`

Here for $`m\in\mathbb{Z}_{\geq 0}`, $`E[m]` denotes the $`m`-torsion subgroup of $`E`, which is the kernel of the multiplication-by-$`m` {bpref "ec.endomorphism"}[endomorphism] of $`E`.

If $`K` has characteristic not equal to $`p`, then $`T_p(E)` is a free $`\Z_p`-module of rank $`2`. It carries an action of the {bpref "group.galois.absolute"}[absolute Galois group] of $`K`, and thus has an associated {bpref "ec.galois_rep"}[Galois representation].

This is a special case of the {bpref "av.tate_module"}[Tate module of an abelian variety].

Depends on: {uses "av.tate_module"}[] {uses "ec.endomorphism"}[] {uses "group.galois.absolute"}[]
:::

:::definition "ec.period"
*Global period of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.period))

The *global period* $`\Omega(E/K)` of an {bpref "ec"}[elliptic curve] defined over a {bpref "nf"}[number field] $`K` is a product of local factors $`\Omega_v(E_v/K_v)`, one for each infinite {bpref "nf.place"}[place] $`v` of $`K`.  Here, $`K_v` denotes the completion of $`K` at $`v` (so $`K_v=\R` for a real place and $`K_v=\C` for a complex place), and $`E_v` denotes the {bpref "ec.base_change"}[base change] of $`E` to $`K_v`.

Fixing a {bpref "ec.weierstrass_coeffs"}[Weierstrass model] for $`E` with coefficients $`a_i\in K`,  a model for $`E_v` is given by the Weierstrass equation with coefficients $`a_{i,v}`, the images of $`a_i` under $`v` in $`K_v`.  Associated to this model we have a {bpref "ec.discriminant"}[discriminant] $`\Delta(E_v)` and an invariant differential $`\omega_v=dx/(2y+a_{1,v}x+a_{3,v})`.

For a real place given by an {bpref "nf.embedding"}[embedding] $`v:K\to\R`, we define

$$`\Omega_v(E_v) = \left|\int_{E_v(\R)} \omega_E\right|.`

In terms of a basis of the {bpref "ec.q.period_lattice"}[period lattice] of $`E_v` of the form $`[x,yi]` (when $`\Delta(E_v)>0`) or $`[2x,x+yi]` (when $`\Delta(E_v)<0`), where $`x` and $`y` are positive real numbers, we have $`\Omega_v(E_v)=2x`.

For a complex place given by an embedding $`v:K\to\C`, we define

$$`\Omega_v(E_v) = \left|\int_{E_v(\C)} \omega_E\wedge\overline{\omega_E}\right|.`

In terms of a basis $`[w_1,w_2]` of the period lattice of $`E_v`, where $`\Im(w_2/w_1)>0`, we have $`\Omega_v(E_v)=2\Im(\overline{w_1}w_2)`, which is double the covolume of the period lattice.

When $`E` has a {bpref "ec.global_minimal_model"}[global minimal model], we have

$$`\Omega(E/K) = \prod_{v}\Omega_v(E_v).`

In general, given an arbitrary model for $`E` with discriminant $`\Delta(E)`, we have

$$`\Omega(E/K) = \left|\frac{N(\Delta(E))}{N(\mathfrak{d}(E))}\right|^{1/12}\prod_{v}\Omega_v(E_v),`

where $`\mathfrak{d}` is the {bpref "ec.minimal_discriminant"}[minimal discriminant ideal] of $`E` and $`N(\mathfrak{d})` denotes its norm.  This quantity is independent of the model of $`E`.

Depends on: {uses "ec"}[] {uses "ec.base_change"}[] {uses "ec.discriminant"}[] {uses "ec.global_minimal_model"}[] {uses "ec.minimal_discriminant"}[] {uses "ec.q.period_lattice"}[] {uses "ec.weierstrass_coeffs"}[] {uses "nf"}[] {uses "nf.embedding"}[] {uses "nf.place"}[]
:::

:::definition "ec.potential_good_reduction"
*Potential good reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.potential_good_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *potential good reduction* if $`E` has {bpref "ec.good_reduction"}[everywhere good reduction] over a finite extension of $`K`.

This is equivalent to the {bpref "ec.j_invariant"}[$`j`-invariant] of $`E` being {bpref "nf.integral"}[integral].

Depends on: {uses "ec"}[] {uses "ec.good_reduction"}[] {uses "ec.j_invariant"}[] {uses "nf"}[] {uses "nf.integral"}[]
:::

:::definition "ec.q"
*Elliptic curve over $`\mathbb Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q))

An *elliptic curve $`E` over $`\mathbb{Q}`* has a Weierstrass equation of the form

$$`E : y^2 = x^3 + ax + b`
 with $`a, b \in \mathbb{Z}` such that its {bpref "ec.q.discriminant"}[discriminant]

$$`\Delta := -16(4a^3 + 27b^2 ) \not = 0.`

Note that such an equation is not unique and $`E` has a unique {bpref "ec.q.minimal_weierstrass_equation"}[minimal Weierstrass equation].

Depends on: {uses "ec.q.discriminant"}[] {uses "ec.q.minimal_weierstrass_equation"}[]
:::

:::definition "ec.q.abc_quality"
*$`abc` quality.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.abc_quality))

Given a triple $`a,b,c` of nonzero coprime integers, the *quality* of the triple is defined as

$$`Q = \frac{\log \max(|a|, |b|, |c|)}{\log \operatorname{rad}(abc)},`

where $`\operatorname{rad}(abc)` is the product of the primes dividing $`abc`.  The $`abc` conjecture stipulates that for any $`\epsilon > 0` there are only finitely many relatively prime triples $`a,b,c` with quality larger than $`1+\epsilon`.

The *$`abc` quality* of an {bpref "ec"}[elliptic curve] $`E` is the quality of an $`a,b,c` triple determined by its {bpref "ec.j_invariant"}[$`j`-invariant], namely the one defined by writing $`\frac{j}{1728} = \frac{a}{c}` in lowest terms and setting $`b = c - a`.  Note that the $`abc` quality is undefined for $`j=0` and $`j=1728`.

The reason for defining the quality of $`E` in this way comes from the equivalence of the $`abc` conjecture with the {bpref "ec.q.szpiro_ratio"}[modified Szpiro conjecture]. For elliptic curves with small {bpref "ec.q.conductor"}[conductor], $`j`-invariants often have unusually large quality.

Depends on: {uses "ec"}[] {uses "ec.j_invariant"}[] {uses "ec.q.conductor"}[]
:::

:::definition "ec.q.analytic_rank"
*Analytic rank of an elliptic curve over $`\Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.analytic_rank))

The *analytic rank* of an {bpref "ec"}[elliptic curve] $`E` is the analytic rank of its {bpref "lfunction"}[L-function] $`L(E,s)`.   The weak form of the BSD conjecture implies that the analytic rank is equal to the rank of the {bpref "ec.mordell_weil_group"}[Mordell-Weil group] of $`E`.

For elliptic curves $`E` over $`\Q`, it is known that $`L(E,s)` satisfies the Hasse-Weil conjecture, and hence that the parity of the analytic rank is always compatible with the {bpref "lfunction.sign"}[sign] of the {bpref "lfunction.functional_equation"}[functional equation].

In general, analytic ranks stored in the LMFDB are only upper bounds on the true analytic rank (they could be incorrect if $`L(E,s)` had a zero very close to but not on the {bpref "lfunction.central_point"}[central point]).  For elliptic curves over $`\Q` of analytic rank less than 2 this upper bound is necessarily tight, due to parity; for analytic ranks $`2` and $`3` is also tight due to results of Kolyvagin; Murty and Murty; Bump, Friedberg and    Hoffstein;  Coates and Wiles; Gross and Zagier which together say that when the analytic rank is $`0` or $`1` then it equals the {bpref "ag.mordell_weil"}[Mordell-Weil rank].

Depends on: {uses "ag.mordell_weil"}[] {uses "ec"}[] {uses "ec.mordell_weil_group"}[] {uses "lfunction"}[] {uses "lfunction.central_point"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.sign"}[]
:::

:::definition "ec.q.analytic_sha_order"
*Analytic order of $`\Sha`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.analytic_sha_order))

The *Tate-Shafarevic group* $`\Sha` of an {bpref "ec"}[elliptic curve] $`E` defined over $`\mathbb{Q}` is a torsion group defined in terms of Galois cohomology, which is conjectured to be finite.  Its {bpref "group.order"}[order] $`\#\Sha` appears in the strong form of the Birch-Swinnerton-Dyer Conjecture for $`E`.  The value of the order which is predicted by the conjecture is called the *Analytic Order of Sha*, $`\Sha_{an}`. <!--Note that the value of $`\Sha`<sub>an</sub> predicted by the conjecture is always a square.-->

For elliptic curves of rank $`0` or $`1` it is a theorem that $`\Sha`<sub>an</sub> is a positive rational number, and this rational number can be computed exactly; this exact  computation has only been carried out for the curves in the database with rank $`0` and conductor $`N\le 500000`.  These values are always in fact integer squares in all cases computed to date.  For curves of rank $`2` and above, there is no such theorem, and the values computed are simply floating point approximate values which happen to be very close to integers.  In the LMFDB we store and display the rounded values in this case.

Depends on: {uses "ec"}[] {uses "group.order"}[]
:::

:::definition "ec.q.bsdconjecture"
*Birch and Swinnerton-Dyer conjecture.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.bsdconjecture))

The *Birch and Swinnerton-Dyer* conjecture is one of the Millennium Prize Problems listed by the Clay Mathematics Institute. It relates the order of vanishing and the first non-zero Taylor series coefficient of  the {bpref "lfunction"}[L-function] associated to an {bpref "ec"}[elliptic curve] $`E` defined over $`\Q` at the {bpref "lfunction.central_point"}[central point] $`s=1` to certain arithmetic data, the BSD invariants of $`E`.

Specifically, the BSD conjecture states that the order $`r` of vanishing of $`L(E,s)` at $`s=1` is equal to the {bpref "ec.rank"}[rank] of the {bpref "ec.mordell_weil_theorem"}[Mordell-Weil group] $`E(\Q)`,  and that

<!-- comment: if you make the following display into a normal one using
$$`..`
 or
$$`..`
 then something about the html code for Sha stops it displaying properly-->

<p align="center"> $`\displaystyle \frac{1}{r!} L^{(r)}(E,1)=  \displaystyle \frac{\# \Sha(E/\Q)\cdot \Omega_E \cdot \mathrm{Reg}(E/\Q) \cdot \prod_p c_p}{\#E(\Q)_{\rm tor}^2}.` </p>
The quantities appearing in this formula are the BSD invariants of $`E`:

- $`r` is the {bpref "ec.rank"}[rank] of $`E(\Q)` (a non-negative integer);

- $`\#\Sha(E/\Q)` is the order of the {bpref "ec.analytic_sha_order"}[Tate-Shafarevich] group

 of $`E` (which is conjectured to always  be finite, a positive integer);

- $`\mathrm{Reg}(E/\Q)` is the {bpref "ec.regulator"}[regulator] of $`E/\Q`;

- $`\Omega_E` is the {bpref "ec.q.real_period"}[real period] of $`E/\Q` (a positive real number);

- $`c_p` is the {bpref "ec.tamagawa_number"}[Tamagawa number] of $`E` at each prime $`p` (a positive integer which is $`1` for all but at most finitely many primes);

- $`E(\Q)_{\rm tor}` is the {bpref "ec.torsion_order"}[torsion order] of $`E(\Q)` (a positive integer).

There is a similar conjecture for {bpref "ag.abelian_variety"}[abelian varieties], in which the real period is replaced by the covolume of the period lattice.

Depends on: {uses "ag.abelian_variety"}[] {uses "ec"}[] {uses "ec.analytic_sha_order"}[] {uses "ec.mordell_weil_theorem"}[] {uses "ec.q.real_period"}[] {uses "ec.rank"}[] {uses "ec.regulator"}[] {uses "ec.tamagawa_number"}[] {uses "ec.torsion_order"}[] {uses "lfunction"}[] {uses "lfunction.central_point"}[]
:::

:::definition "ec.q.canonical_height"
*Canonical height.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.canonical_height))

Let $`E` be an {bpref "ec"}[elliptic curve] defined over $`\mathbb{Q}`.
The *canonical height* of a rational point $`P\in E(\mathbb{Q})` is computed by writing the $`x`-coordinate $`x(nP)=A_n(P)/D_n(P)` as a fraction in lowest terms and setting

$$`\hat{h}(P) = \lim_{n\to\infty} \frac{1}{n^2}\log \max\bigl\{|A_n(P)|,|D_n(P)|\bigr\}.`

(<EM>Note</EM>. Some sources define $`\hat{h}` to be $`\frac12` of this quantity.)

Properties of $`\hat{h}`:
<UL>
<LI>
$`\hat{h}(P)=\log \max\bigl\{|A_1(P)|,|D_1(P)|\bigr\}+O(1)` as $`P` ranges
over $`E(\mathbb{Q})`.
<LI>
$`\hat{h}(P)\ge0`; and
$`\hat{h}(P)=0` if and only if $`P` is a torsion point.
<LI>
$`\hat{h}:E(\mathbb{Q})\to\mathbb{R}` extends to a positive definite quadratic form on $`E(\mathbb{Q})\otimes\mathbb{R}`.
</UL>
The *height pairing* on $`E` is the associated bilinear form $`\langle P,Q\rangle=\frac{1}{2}\bigl(\hat{h}(P+Q)-\hat{h}(P)-\hat{h}(Q)\bigr)`, which is used to compute the {bpref "ec.regulator"}[elliptic regulator] of $`E`.  It is a symmetric positive definite bilinear form on $`E(\Q)\otimes\R`.

For a number field $`K`, the *canonical height* of $`P\in E(K)` is given by $`\hat{h}(P)=\lim_{n\to\infty} n^{-2}h\bigl(x(nP)\bigr)`, where $`h` is the {bpref "nf.weil_height"}[Weil height].

Depends on: {uses "ec"}[] {uses "ec.regulator"}[] {uses "nf.weil_height"}[]
:::

:::definition "ec.q.conductor"
*Conductor of an elliptic curve over $`\Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.conductor))

The *conductor* $`N` of an {bpref "ec"}[elliptic curve] $`E` defined over $`\Q` is a positive integer divisible by the primes of bad reduction and no others.  It has the form $`N=\prod p^{e_p}`, where the exponent $`e_p` is

- $`e_p=1` if $`E` has {bpref "ec.multiplicative_reduction"}[multiplicative reduction] at $`p`,

- $`e_p=2` if $`E` has {bpref "ec.additive_reduction"}[additive reduction] at $`p` and $`p\ge5`,

- $`2\leq e_p\leq 5` if $`E` has additive reduction and $`p=3`, and

- $`2\leq e_p\leq 8` if $`E` has additive reduction and $`p=2`.

For all primes $`p`, there is an algorithm of Tate that simultaneously creates a local minimal Weierstrass equation and computes the exponent of the conductor. See:

<UL>
<LI> J. Tate, Algorithm for determining the type of a singular fiber
in an elliptic pencil, Modular functions of one variable, IV
(Proc. Internat. Summer School, Univ. Antwerp, Antwerp, 1972),
33-52. <EM>Lecture Notes in Math.</EM>, Vol. <B>476</B>,
Springer, Berlin, 1975.

<LI> J.H. Silverman, <EM>Advanced topics in the arithmetic of elliptic
curves</EM>, GTM <B>151</B>, Springer-Verlag, New York, 1994.

</UL>

Depends on: {uses "ec"}[] {uses "ec.additive_reduction"}[] {uses "ec.multiplicative_reduction"}[]
:::

:::definition "ec.q.cremona_label"
*Cremona label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.cremona_label))

The *Cremona label* of an {bpref "ec"}[elliptic curve] over $`\mathbb{Q}` is  a way of indexing the elliptic curves over $`\mathbb{Q}.` It has the form $`11a1` or $`10050bf2.`  The first number represents the {bpref "ec.q.conductor"}[conductor], the letter or letters represent the {bpref "ec.isogeny_class"}[isogeny class] and the last number represents the {bpref "ec.isomorphism"}[isomorphism class]  within the {bpref "ec.isogeny"}[isogeny class] as it appears in [Cremona's tables.](http://johncremona.github.io/ecdata/)  In each isogeny class the curve with number 1 is the {bpref "ec.q.optimal"}[$`\Gamma_0(N)`-optimal] curve.<br>
For more details, see "The elliptic curve database for conductors to 130000" by John Cremona in ANTS-VII proceedings, Lecture Notes in Computer Science, vol. 4076, 2006, 11-29.

In the Cremona labeling, it is somewhat difficult to describe the mechanisms for ordering isogeny classes or curves within a class, since these depend on the order in which the curves were computed (though for conductors over 230,000 the isogeny class labels coincide). Cremona labels are only available for conductors up to 500,000. For these reasons, within this site we also use the {bpref "ec.q.lmfdb_label"}[LMFDB label], whose definition is somewhat simpler. Note that the lack of internal punctuation distinguishes Cremona labels from LMFDB labels.

Depends on: {uses "ec"}[] {uses "ec.isogeny"}[] {uses "ec.isogeny_class"}[] {uses "ec.isomorphism"}[] {uses "ec.q.conductor"}[] {uses "ec.q.optimal"}[]
:::

:::definition "ec.q.discriminant"
*Discriminant of an elliptic curve over $`\Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.discriminant))

The *discriminant* $`\Delta` of an {bpref "ec"}[elliptic curve] $`E` defined over $`\mathbb{Q}` is a nonzero integer divisible exactly by the primes of bad reduction.
It is the {bpref "ec.discriminant"}[discriminant] of the {bpref "ec.q.minimal_weierstrass_equation"}[minimal Weierstrass equation] of the curve.

Depends on: {uses "ec"}[] {uses "ec.discriminant"}[] {uses "ec.q.minimal_weierstrass_equation"}[]
:::

:::definition "ec.q.endomorphism_ring"
*Endomorphism ring of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.endomorphism_ring))

The *endomorphism ring* $`\End(E)` of an {bpref "ec"}[elliptic curve] $`E` is the ring of all {bpref "ec.endomorphism"}[endomorphisms] of $`E` defined over $`K`.  For endomorphisms defined over extensions, we speak of the {bpref "ec.geom_endomorphism_ring"}[geometric endomorphism ring] of $`E`.

For elliptic curves defined over $`\Q`, this ring is always isomorphic to $`\Z` consisting of the multiplication-by-$`m` maps $`[m] \colon E\to E` for $`m \in \Z`.

This is a special case of the {bpref "ag.endomorphism_ring"}[endomorphism ring] of an {bpref "ag.abelian_variety"}[abelian variety].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_ring"}[] {uses "ec"}[] {uses "ec.endomorphism"}[] {uses "ec.geom_endomorphism_ring"}[]
:::

:::definition "ec.q.faltings_height"
*Faltings height of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.faltings_height))

The *Faltings height* of an {bpref "ec"}[elliptic curve] $`E` defined over $`\Q` is the quantity

$$`h_{\mathrm{Faltings}}(E) = -\frac{1}{2}\log(A),`

where $`A` is the covolume (that is, the area of a fundamental period parallelogram) of the {bpref "ec.q.period_lattice"}[Neron lattice] of $`E`.

The *stable Faltings height* of $`E` is

$$`h_{\mathrm{stable}}(E) = \frac{1}{12}(\log\mathrm{denom}(j)-\log(|\Delta|)) - \frac{1}{2}\log(A),`

where $`j` is the {bpref "ec.j_invariant"}[$`j`-invariant] of $`E`, $`\Delta` the {bpref "ec.discriminant"}[discriminant] of any model of $`E` and $`A` the covolume of the period lattice of that model.
The stable height is independent of the model of $`E`, and the unstable and stable heights are equal for {bpref "ec.semistable"}[semistable] curves, for which $`\mathrm{denom}(j)=|\Delta|`.

Depends on: {uses "ec"}[] {uses "ec.discriminant"}[] {uses "ec.j_invariant"}[] {uses "ec.q.period_lattice"}[] {uses "ec.semistable"}[]
:::

:::definition "ec.q.faltings_ratio"
*Faltings ratio.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.faltings_ratio))

In each {bpref "ec.isogeny"}[isogeny class] of {bpref "ec"}[elliptic curves] defined over $`\Q`, there is a unique curve $`E_{\text{min}}` whose {bpref "ec.q.period_lattice"}[Neron lattice] is  a sublattice of the Ne;ron lattices of all the curves in the class (G. Stevens, );  it is the unique curve of minimal {bpref "ec.q.faltings_height"}[Faltings height] among the curves in the isogeny class.

The *Faltings ratio* of each curve $`E` is the {bpref "group.subgroup.index"}[index] of the Ne;ron lattice of $`E_{\text{min}}` in that of $`E`.

Depends on: {uses "ec"}[] {uses "ec.isogeny"}[] {uses "ec.q.faltings_height"}[] {uses "ec.q.period_lattice"}[] {uses "group.subgroup.index"}[]
:::

:::definition "ec.q.frey"
*Frey curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.frey))

Given a triple of integers $`A, B, C` with $`A + B = C`, the [*Frey curve*](https://en.wikipedia.org/wiki/Frey_curve) (or *Frey-Hellegouarch curve*) associated to this triple is the elliptic curve

$$`y^2 = x(x-A)(x+B).`
:::

:::definition "ec.q.integral_points"
*Integral points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.integral_points))

The *integral points* on a given model of an elliptic curve $`E` defined over $`\Q` are the points $`P=(x,y)` on the model that have integral coordinates $`x` and $`y`.

The number of integral points is finite, by a theorem of Siegel.
:::

:::definition "ec.q.j_invariant"
*j-invariant of a rational elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.j_invariant))

The *$`j`-invariant* of an {bpref "ec"}[elliptic curve] $`E` defined over $`\mathbb{Q}` is an invariant of the isomorphism class of $`E` over  $`\overline{\mathbb{Q}}` .
If the {bpref "ec.weierstrass_coeffs"}[Weierstrass equation] of $`E` is
$$`y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,`
 then its $`j`-invariant is given by

$$`j= \frac{c_4^3}{\Delta}`
 where

$$`\begin{aligned}
b_2 &= a_1^2 + 4 a_2\\
b_4 &= 2a_4 + a_1 a_3\\
b_6 &= a_3^2 + 4 a_6 \\
b_8 &= a_1^2 a_6 + 4 a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2\\
c_4 &= b_2^2 - 24b_4 \\
c_6 &= -b_2^3 + 36 b_2 b_4 - 216 b_6\end{aligned}`

and
$$`\Delta=-b_2^2b_8 - 8 b_4^3 -27 b_6 ^2 + 9 b_2 b_4 b_6`

is the {bpref "ec.q.discriminant"}[discriminant] of $`E.`

Depends on: {uses "ec"}[] {uses "ec.q.discriminant"}[] {uses "ec.weierstrass_coeffs"}[]
:::

:::definition "ec.q.kodaira_symbol"
*Kodaira symbol.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.kodaira_symbol))

The *Kodaira symbol* encodes the {bpref "ec.q.reduction_type"}[reduction type] of an elliptic curve at a prime $`p.` It describes the combinatorics of the special fiber of the Ne;ron model of the elliptic curve. The Ne;ron model is obtained from the {bpref "ec.q.minimal_weierstrass_equation"}[minimal Weierstrass equation] using Tate's algorithm. For an exact definition and properties, consult a text on elliptic curves.

Depends on: {uses "ec.q.minimal_weierstrass_equation"}[] {uses "ec.q.reduction_type"}[]
:::

:::definition "ec.q.lmfdb_label"
*Label for an elliptic curve over $`\mathbb Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.lmfdb_label))

The *LMFDB label* of an elliptic curve $`E` over $`\mathbb{Q}` is  a way of indexing the elliptic curves over $`\mathbb{Q}.` It has the form "11.a1" or "10050.bf2".

The label has three components: the *conductor*, the *isogeny class label*, and the *isomorphism class index*.

1.  The first component is the decimal representation of the {bpref "ec.q.conductor"}[conductor] (a positive integer).

2. The second component is the {bpref "ec.isogeny_class"}[isogeny class] label, a string which represents the *isogeny class index*,  a non-negative integer encoded
as in base 26 using the 26 symbols a,b,.., z.  The isogeny
classes of elliptic curves with the same conductor are sorted lexicographically by the $`q`-expansions of the associated modular forms, and the isogeny class index of each {bpref "ec.isogeny_class"}[isogeny class] of fixed {bpref "ec.conductor"}[conductor] is the index (starting at 0) of the class in this ordering.

3. The third component is the decimal representation of the {bpref "ec.isomorphism"}[isomorphism class] index, a positive integer giving the index of the coefficient vector $`[a_1, a_2, a_3, a_4, a_6]` of the {bpref "ec.q.minimal_weierstrass_equation"}[reduced minimal Weierstrass equation] of $`E` in a lexicographically sorted list of all the {bpref "ec"}[elliptic curves] in the {bpref "ec.isogeny_class"}[isogeny class].

The complete label is obtained by concatenating \[conductor, ".", isogeny class label, isomorphism class index\].

Note that this is not the same as the {bpref "ec.q.cremona_label"}[Cremona label], even though for certain curves they only differ in the insertion of the dot "." (for example, "37a1" and "37.a1" are the same curve). The presence of the punctuation "." distinguishes an LMFDB label from a Cremona label.  Cremona labels are only defined for curves of conductor up to 500000.

Depends on: {uses "ec"}[] {uses "ec.conductor"}[] {uses "ec.isogeny_class"}[] {uses "ec.isomorphism"}[] {uses "ec.q.conductor"}[] {uses "ec.q.minimal_weierstrass_equation"}[]
:::

:::definition "ec.q.manin_constant"
*Manin constant for elliptic curves over $`\Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.manin_constant))

Let $`E` be an {bpref "ec.q.optimal"}[optimal] {bpref "ec"}[elliptic curves] of {bpref "ec.q.conductor"}[conductor] $`N`, let $`f` be the modular form associated to $`E`, and let $`\varphi:X_0(N)\to E` be the associated {bpref "ec.q.modular_parametrization"}[modular parametrization]. Let $`\omega_E` be the Ne;ron differential on $`E`.  Then the pull-back $`\varphi^*\omega_E` of $`\omega_E` to $`X_0(N)` satisfies

$$`\varphi^*\omega_E = c \cdot 2\pi i f(z)dz`

for some non-zero rational number $`c` called the *Manin constant* of $`E`. In fact $`c\in \Z`, by a theorem of Edixhoven.

It is conjectured that $`c=1` for all optimal curves, and there are several results stating that $`c=1` if certain conditions hold: see Amod Agashe, Ken Ribet and William Stein: The Manin Constant, Pure and Applied Mathematics Quarterly, Vol. 2 no.2 (2006), pp. 617–636.  In an appendix to that paper, John Cremona gives an algorithm for verifying that $`c=1` in individual cases, and proves that $`c=1` for all optimal elliptic curves over $`\Q` in the database. Kestutis Cesnavicius proves $`c=1` for {bpref "ec.semistable"}[semistable elliptic curves] over $`\Q`, and more generally that $`v_p(c) = 0` if $`p^2 \nmid N` in \*The Manin constant in the semistable case\*, Compositio Math. *154* (2018), 1889–1920.

For non-optimal elliptic curves $`E'` over $`\Q`, the *Manin constant* is defined, in terms of the Manin constant of the unique optimal curve {bpref "ec.isogeny"}[isogenous] to $`E'`.   Let $`\varphi:X_0(N)\to E` and $`f` be as above, and $`\psi:E\to E'` an isogeny of least degree from $`E` to $`E'`.  Then we obtain a parametrization $`\psi\circ\varphi:X_0(N)\to E'` and define the Manin constant $`c'` of $`E'` to be the non-zero rational number such that

$$`(\psi\circ\varphi)^*\omega_{E'} = c' \cdot 2\pi i f(z)dz.`

This is an integer multiple of the Manin constant of $`E`, since $`\psi^*\omega_{E'}` is an integer multiple of $`\omega_E`; the multiplier divides the degree of $`\psi` but may be strictly less: it may equal $`1`.

Depends on: {uses "ec"}[] {uses "ec.isogeny"}[] {uses "ec.q.conductor"}[] {uses "ec.q.modular_parametrization"}[] {uses "ec.q.optimal"}[] {uses "ec.semistable"}[]
:::

:::definition "ec.q.minimal_twist"
The *minimal quadratic twist* of an elliptic curve $`E` defined over $`\mathbb{Q}` is defined as follows.

- First consider the finite set of all {bpref "ec.twists"}[quadratic twists]  of $`E` which have minimal {bpref "ec.q.conductor"}[conductor].  If this set contains just one curve, it is the minimal quadratic twist.

- Otherwise, sort the curves with minimal conductor into {bpref "ec.isogeny_class"}[isogeny classes], and restrict attention to the curves whose class comes first in the LMFDB labelling; equivalently, sort the curves by the sequence of coefficients $`(a_n)` of their $`L`-function and restrict to the curve or curves with the first such sequence.

- If $`E` does not have {bpref "ec.complex_multiplication"}[Complex Multiplication] (CM), then the minimal isogeny class contains a \*unique\* curve with the same {bpref "ec.j_invariant"}[$`j`-invariant] as $`E`, and this curve is the minimal quadratic twist of $`E`.

- If $`E` does have CM, then the minimal isogeny class contains exactly \*two\* curves with $`j`-invariant $`j(E)`.   In all but one case these two curves have distinct minimal discriminants, with the same sign, and we define the minimal quadratic twist to be the curve whose {bpref "ec.minimal_discriminant"}[minimal discriminant] has smallest absolute value.

- The exception is for elliptic curves with $`j=66^3`, which have CM by the imaginary quadratic {bpref "nf.order"}[order] with discriminant $`-16`.  The minimal conductor is $`32`, and curves [32.a1](https://www.lmfdb.org/EllipticCurve/Q/32/a/1) and [32.a2](https://www.lmfdb.org/EllipticCurve/Q/32/a/2) (which are quadratic twists of each other by $`-1`) both have minimal  discriminant $`2^9`.  The minimal quadratic twist for $`j=66^3` is defined to be [32.a1](https://www.lmfdb.org/EllipticCurve/Q/32/a/1).

All {bpref "ec"}[elliptic curves] $`E` over $`\mathbb{Q}` with $`j`-invariant $`1728` are {bpref "ec.twists"}[quartic twists] of each other.  The smallest
{bpref "ec.q.conductor"}[conductor] of such a curve is $`32`.   Both the curves
[32.a3](https://www.lmfdb.org/EllipticCurve/Q/32/a/3) and [32.a4](https://www.lmfdb.org/EllipticCurve/Q/32/a/4) have $`j`-invariant $`1728`, and they have minimal discriminants $`-2^{12}` and $`2^6` respectively.
We define the *minimal quartic twist* (or just *minimal twist*) of every elliptic curve with $`j=1728` to be the curve [32.a3](https://www.lmfdb.org/EllipticCurve/Q/32/a/3), which has smaller discriminant, and equation $`Y^2=X^3-X`.

All {bpref "ec"}[elliptic curves] $`E` over $`\mathbb{Q}` with $`j`-invariant $`0` are {bpref "ec.twists"}[sextic twists] of each other.  The smallest {bpref "ec.q.conductor"}[conductor] of such a curve is $`27`.   Both the curves [27.a3](https://www.lmfdb.org/EllipticCurve/Q/27/a/3) and [27.a4](https://www.lmfdb.org/EllipticCurve/Q/27/a/4) have $`j`-invariant $`0`, and they have minimal discriminants $`-3^9` and $`-3^3` respectively.
We define the *minimal sextic twist* (or just *minimal twist*) of every elliptic curve with $`j=0` to be the curve [27.a4](https://www.lmfdb.org/EllipticCurve/Q/27/a/4), which has smaller discriminant, and equation $`Y^2+Y=X^3`.

The *minimal twist* of an elliptic curve $`E` is its minimal quadratic twist, unless $`j(E)=0` or $`1728`, in which cases the minimal twist is its minimal sextic or quartic twist respectively.
The minimal quadratic twist depends only on the $`j`-invariant unless $`j=0` or $`1728`; in each of  these cases, there are infinitely many different minimal quadratic twists, though only one minimal twist.

Depends on: {uses "ec"}[] {uses "ec.complex_multiplication"}[] {uses "ec.isogeny_class"}[] {uses "ec.j_invariant"}[] {uses "ec.minimal_discriminant"}[] {uses "ec.q.conductor"}[] {uses "ec.twists"}[] {uses "nf.order"}[]
:::

:::definition "ec.q.minimal_weierstrass_equation"
*Minimal Weierstrass equation over $`\mathbb Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.minimal_weierstrass_equation))

Every elliptic curve over $`\mathbb{Q}` has an integral Weierstrass model (or equation) of the form
$$`y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,`

where $`a_1,a_2,a_3,a_4,a_6` are integers.
Each such equation has a {bpref "ec.q.discriminant"}[discriminant] $`\Delta`.  A *minimal Weierstrass equation* is one for which $`|\Delta|` is minimal among all Weierstrass models for the same curve.  For elliptic curves over $`\mathbb{Q}`, minimal models exist, and there is a unique *reduced minimal model* which satisfies the additional constraints $`a_1,a_3\in\{0,1\}`, $`a_2\in\{-1,0,1\}`.
:::

:::definition "ec.q.modular_degree"
*Modular degree of an elliptic curve over $`\mathbb Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.modular_degree))

The *modular degree* of an {bpref "ec"}[elliptic curve] over $`\Q` is the minimum degree of a {bpref "ec.q.modular_parametrization"}[modular parametrization] of the curve.

Depends on: {uses "ec"}[] {uses "ec.q.modular_parametrization"}[]
:::

:::definition "ec.q.modular_parametrization"
*Modular parametrization of an elliptic curve over $`\mathbb Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.modular_parametrization))

A *modular parametrization* of an {bpref "ec"}[elliptic curve] $`E` over $`\mathbb{Q}` is a non-constant map $`X_0(N) \to E,` where $`N` is the conductor of $`E.`

Depends on: {uses "ec"}[]
:::

:::definition "ec.q.naive_height"
*Naive height.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.naive_height))

The *naive height* of an {bpref "ec"}[elliptic curve] in short {bpref "ec.weierstrass_coeffs"}[Weierstrass form]

$$`y^2 = x^3 + a_4 x + a_6`

is the quantity $`\max(4\lvert a_4 \rvert^3, 27\lvert a_6 \rvert^2)`.

Depends on: {uses "ec"}[] {uses "ec.weierstrass_coeffs"}[]
:::

:::definition "ec.q.optimal"
*Optimal  elliptic curve over $`\mathbb Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.optimal))

An {bpref "ec.q"}[elliptic curve] over $`\Q` is *optimal* if it is an optimal quotient of the corresponding modular curve. Every isogeny class contains a unique optimal curve. For more information, see [William Stein's page on optimal quotients.](http://wstein.org/papers/ars-manin/html/node2.html)

Optimal curves have a {bpref "ec.q.cremona_label"}[Cremona label] whose last component is the number 1, with the exception of class 990h where the optimal curve is 990h3 (number 3).  This is a historical accident and has no mathematical significance.

NB It has not yet been proved in all cases that the first curve in each class is optimal; however this is true for all {bpref "ec.isogeny_class"}[isogeny classes] of {bpref "ec.q.conductor"}[conductor] $`{}\le400000`, and for many others (for example whenever the isogeny class consists of only one curve).  The current optimality status of each curve is shown on its home page.

Depends on: {uses "ec.isogeny_class"}[] {uses "ec.q"}[] {uses "ec.q.conductor"}[]
:::

:::definition "ec.q.period_lattice"
*Period lattice of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.period_lattice))

For $`E` an {bpref "ec"}[elliptic curve] defined over $`\C` by a {bpref "ec.weierstrass_coeffs"}[Weierstrass equation] with coefficients $`a_1,a_2,a_3,a_4,a_6`, the *period lattice* of $`E` is the set $`\Lambda` of periods of the invariant differential $`dx/(2y+a_1x+a_3)`, which is a discrete lattice of {bpref "group.rank"}[rank] $`2` in $`\C`.   There is an isomorphism (of complex Lie groups) $`\C/\Lambda \cong E(\C)` defined in terms of the Weierstrass $`\wp`-function.

For elliptic curves defined over $`\R` (and in particular, for those defined over $`\Q`), the period lattice has one of two possible types dependng on the sign of the {bpref "ec.q.discriminant"}[discriminant] $`\Delta` of $`E`:

- If $`\Delta>0`, then $`\Lambda` is \*rectangular\*, with a $`\Z`-basis of the form $`\left<x,yi\right>`, where $`x` and $`y` are positive real numbers; in this case, $`E(\R)` has two connected components.

- If $`\Delta<0`, then $`\Lambda` has a $`\Z`-basis of the form $`\left<2x,x+yi\right>`, where $`x` and $`y` are positive real numbers; in this case, $`E(\R)` has one connected component.

The *real period*  of $`E` is defined to be $`2x` in each case, so is equal to the smallest positive real period multiplied by the number of real components.

Note that the period lattice depends on the choice of Weierstrass model of $`E`; different models have {bpref "ec.q.real_period"}[homothetic] lattices.  For elliptic curves defined over $`\Q`, the period lattice associated to a {bpref "ec.global_minimal_model"}[global minimal model] of $`E` is called the *N\'e;ron lattice* of $`E`.  The real period of the Ne;ron lattice is denoted $`\Omega_E`, and appears in the Birch Swinnerton-Dyer conjecture for $`E`.

Depends on: {uses "ec"}[] {uses "ec.global_minimal_model"}[] {uses "ec.q.discriminant"}[] {uses "ec.q.real_period"}[] {uses "ec.weierstrass_coeffs"}[] {uses "group.rank"}[]
:::

:::definition "ec.q.real_period"
*Real period.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.real_period))

For an elliptic curve $`E` defined over $`\R` with period lattice $`\Lambda`, the *real period* $`\Omega` is the least positive element of $`\Lambda\cap\R` multiplied by the number of components of $`E(\R)`.

When an elliptic curve is defined by means of a {bpref "ec.weierstrass_coeffs"}[Weierstrass equation], the period lattice $`\Lambda` is the lattice of periods of the invariant differential $`dx/(2y+a_1x+a_3)`.  Different Weierstrass models defining {bpref "ec.weierstrass_isomorphism"}[isomorphic]  curves have period lattices which are *homothetic*, meaning that they differ by a nonzero multiplicative constant.  When we speak of *the* period lattice or *the* real period for an elliptic curve defined over $`\Q`, we always mean the lattice and period associated with a {bpref "ec.q.minimal_weierstrass_equation"}[minimal] equation.

Depends on: {uses "ec.q.minimal_weierstrass_equation"}[] {uses "ec.weierstrass_coeffs"}[] {uses "ec.weierstrass_isomorphism"}[]
:::

:::definition "ec.q.reduction_type"
*Reduction type of an elliptic curve over $`\mathbb Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.reduction_type))

The *reduction type* of an elliptic curve $`E` defined over $`\mathbb{Q}` at a prime $`p`
depends on the reduction $`\tilde E` of $`E` modulo $`p`. This reduction is constructed by taking a {bpref "ec.q.minimal_weierstrass_equation"}[minimal Weierstrass equation] for $`E` and reducing its coefficients modulo $`p` to obtain a curves over $`\mathbb{F}_p`.  The reduced curve is either smooth (non-singular) or has a unique singular point.

$`E` has *good reduction* at $`p` if $`\tilde E` is non-singular over $`\mathbb{F}_p`.   The reduction type is *ordinary* (ord) if $`\tilde E` is ordinary (equivalently, if $`\tilde E(\overline{\F_p})` has non-trivial $`p`-torsion) and *supersingular* (ss) otherwise.  The coefficient $`a(p)` of the L-function $`L(E,s)` is divisible by $`p` if the reduction is supersingular and not if it is ordinary.

$`E` has *bad reduction* at $`p` if $`\tilde E` is singular over $`\mathbb{F}_p`. In this case the reduction type is further classified according to the nature of the singularity.  In all cases the singularity is a double point.

$`E` has *multiplicative reduction* at $`p` if $`\tilde E` has a *nodal* singularity: the singular point is a node, with distinct tangents. It is called *split* if the two tangents are defined over $`\mathbb{F}_p` and *non-split* otherwise. The  coefficient $`a(p)` of $`L(E,s)` is $`1` if the reduction is split and $`-1` if it is non-split.

$`E` has *additive reduction* at $`p` if $`\tilde E` has a *cuspidal* singularity: the singular point is a cusp, with only one tangent. In this case $`a(p)=0`.

Depends on: {uses "ec.q.minimal_weierstrass_equation"}[]
:::

:::definition "ec.q.regulator"
*Regulator of elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.regulator))

The *regulator* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K,` denoted $`\operatorname{Reg}(E/K)`, is the volume of $`E(K)/E(K)_{tor}` with respect to the *height pairing* $`\langle -,-\rangle` associated to the {bpref "ec.canonical_height"}[canonical height] $`\hat{h}`, i.e. $`\langle P,Q\rangle = \frac{1}{2}(\hat{h}(P+Q)-\hat{h}(P)-\hat{h}(Q))`.

If the {bpref "ec.mordell_weil_group"}[Mordell-Weil group] $`E(K)` has rank $`r` and $`P_1, \ldots, P_r \in E(K)` generate $`E(K)/E(K)_{tor}`, then

$$`\operatorname{Reg}(E/K) = \left|\det (\langle P_i, P_j \rangle )_{1\leq i,j \leq r}\right|,`

which is independent of the choice of generators.

Special cases are when $`E(K)` has rank $`0`, in which case $`E(K)/E(K)_{tor}=0` and $`\operatorname{Reg}(E/K)=1`, and when $`E(K)` has rank $`1`, in which case $`\operatorname{Reg}(E/K)` is equal to the {bpref "ec.canonical_height"}[canonical height] $`\hat{h}(P)` of a generator $`P`.

Depends on: {uses "ec"}[] {uses "ec.canonical_height"}[] {uses "ec.mordell_weil_group"}[] {uses "nf"}[]
:::

:::definition "ec.q.semistable"
*Semistable elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.semistable))

An {bpref "ec"}[elliptic curve] is *semistable* if it has {bpref "ec.reduction_type"}[multiplicative reduction] at every {bpref "ec.bad_reduction"}[bad prime].

Depends on: {uses "ec"}[] {uses "ec.bad_reduction"}[] {uses "ec.reduction_type"}[]
:::

:::definition "ec.q.serre_invariants"
*Serre invariants.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.serre_invariants))

Let $`\bar \rho_{E,\ell}` be the mod-$`\ell` {bpref "ec.galois_rep"}[Galois representation] of an elliptic curve $`E/\Q`.

The *Serre invariants* $`(k,M)` of $`\bar \rho_{E,\ell}` consist of the *Serre weight* $`k` and the *Serre conductor* $`M` giving the {bpref "cmf.weight"}[weight] and minimal {bpref "cmf.level"}[level] of a newform $`f\in S_{k}^{\textrm new}(\Gamma_1(M))` whose associated mod-$`\ell` Galois representation is isomorphic to $`\bar \rho_{E,\ell}`.

This means that $`a_p(E)` and $`a_p(f)` reduce to the same element of the residue field of a {bpref "nf.prime"}[prime] above $`\ell` in the coefficient field of $`f` (this residue field need not have degree one, but every $`a_p(f)` must reduce to an element of $`\F_{\ell}` in order for this condition to hold).

The modular form $`f` is not uniquely determined, but the minimal level $`M` arising among all such $`f` is uniquely determined, and among those with level $`M`, the weight is uniquely determined.

For all but finitely many primes $`\ell`, including all $`\ell>7` of good reduction for $`E`, the Serre invariants are $`(2,N)`, where $`N` is the conductor of the elliptic curve. The primes $`\ell` for which this does not hold are *exceptional*.

In general, the Serre weight $`k` is divisible by $`2` and the Serre conductor $`M` divides $`N`.

Depends on: {uses "cmf.level"}[] {uses "cmf.weight"}[] {uses "ec.galois_rep"}[] {uses "nf.prime"}[]
:::

:::definition "ec.q.special_value"
*Special value of an elliptic curve L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.special_value))

The *special value* of an {bpref "ec"}[elliptic curve] $`E/\Q` is the first nonzero value of $`L^{(r)}(E,1)/r!` for $`r\in \Z_{\ge 0}`, where $`L(E,s)` is the $`L`-function of $`E` in its {bpref "lfunction.normalization"}[arithmetic normalization].

The special value appears on the LHS of the formula in the {bpref "ec.q.bsdconjecture"}[Birch and Swinnerton-Dyer conjecture].

Depends on: {uses "ec"}[] {uses "ec.q.bsdconjecture"}[] {uses "lfunction.normalization"}[]
:::

:::definition "ec.q.szpiro_ratio"
*Szpiro ratio.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.szpiro_ratio))

The (modified) *Szpiro ratio* of an {bpref "ec"}[elliptic curve] $`E` is defined as

$$`\sigma_m(E) = \frac{\log \max(|c_4|^3, |c_6|^2)}{\log N},`

where $`N` is the {bpref "ec.q.conductor"}[conductor] of $`E` and $`c_4` and $`c_6` are defined as for the {bpref "ec.q.j_invariant"}[$`j`-invariant].  The (modified) Szpiro conjecture is that, for any $`\epsilon > 0`, there are only finitely many elliptic curves with Szpiro ratio larger than $`6+\epsilon`.  In , Oesterlé proves that this conjecture is equivalent to the {bpref "ec.q.abc_quality"}[$`abc` conjecture].

In Oesterlé's paper cited above, there is another conjecture, that the ratio

$$`\frac{\log \Delta}{\log N},`

also has the property of only taking values larger than $`6+\epsilon` finitely many times (here $`\Delta` is the {bpref "ec.minimal_discriminant"}[minimal discriminant] of $`E`).  This conjecture is implied by the modified Szpiro conjecture (and thus the $`abc` conjecture), but it is not currently known to be equivalent.  All of the Szpiro ratios in the LMFDB are computed in terms of $`c_4` and $`c_6` rather than $`\Delta` for this reason.

Depends on: {uses "ec"}[] {uses "ec.minimal_discriminant"}[] {uses "ec.q.conductor"}[] {uses "ec.q.j_invariant"}[]
:::

:::definition "ec.q.torsion_growth"
*Torsion growth in number fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.torsion_growth))

Let $`E` be an {bpref "ec"}[elliptic curve] defined over $`\Q` and let $`K` be a {bpref "nf"}[number field].  We say that there is *torsion growth* from $`\Q` to $`K` if the {bpref "ec.torsion_subgroup"}[torsion subgroup] $`E(K)_{\rm tor}` of $`E(K)` is strictly larger than $`E(\Q)_{\rm tor}`.

If there is torsion growth in a field $`K` then obviously the torsion also grows in every extension of $`K`.  We say that the torsion growth in $`K` is *primitive* if $`E(K)_{\rm tor}` is strictly larger than $`E(K')_{\rm tor}` for all proper subfields $`K' \subsetneq K`.

For every elliptic curve $`E` there is torsion growth in at least one field of {bpref "nf.degree"}[degree] $`2`, $`3`, or $`4`, and torsion can only grow in fields whose degree is divisible by $`2`, $`3`, $`5` or $`7`:  see Theorem 7.2 of
.  Additionally, there is no primitive torsion growth in fields of degrees $`22` or $`26`: see  Lemma 2.11 of .  Hence the only degrees less than $`24` in which primitive torsion growth occurs are $`2,3,4,5,6,7,8,9,10,12,14,15,16,18,20,21`.

Depends on: {uses "ec"}[] {uses "ec.torsion_subgroup"}[] {uses "nf"}[] {uses "nf.degree"}[]
:::

:::definition "ec.q.torsion_subgroup"
*Torsion subgroup of an elliptic curve over $`\mathbb Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.torsion_subgroup))

If $`E` is an elliptic curve defined over $`\mathbb{Q}`, its *torsion subgroup* is the subgroup of the Mordell-Weil group $`E(\mathbb{Q})` consisting of all the rational points of finite order.  It is a finite abelian group of order at most $`16` (by a theorem of Mazur), which is a product of at most $`2` cyclic factors.  The "torsion structure" is the list of invariants of the group:

- $`[]` for the trivial group;

- $`[n]` for a cyclic group of order $`n` (only $`n=2,3,4,5,6,7,8,9,10` or $`12` occur for elliptic curves over $`\mathbb{Q}`);

- $`[n_1,n_2]` with $`n_1\mid n_2` for a product of cyclic groups of orders $`n_1` and $`n_2` (only $`[2,2m]` for $`m=2,4,6` or $`8` occur over $`\mathbb{Q}`).
:::

:::definition "ec.q_curve"
An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is a $`\mathbb{Q}`*-curve* if it is {bpref "ec.isogeny"}[isogenous] over $`\overline{K}` to each of its Galois conjugates.  Note that the isogenies need not be defined over $`K` itself.

An elliptic curve which is the {bpref "ec.base_change"}[base change] of a curve defined over $`\mathbb{Q}` is a $`\mathbb{Q}`-curve, but not all $`\mathbb{Q}`-curves are
base-change curves.

Elliptic curves with {bpref "ec.complex_multiplication"}[CM] are all $`\mathbb{Q}`-curves, as are all those whose $`j`-invariant is in $`\mathbb{Q}`.

Depends on: {uses "ec"}[] {uses "ec.base_change"}[] {uses "ec.complex_multiplication"}[] {uses "ec.isogeny"}[] {uses "nf"}[]
:::

:::definition "ec.rank"
*Rank of an elliptic curve over a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.rank))

The *rank* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is the rank of its {bpref "ec.mordell_weil_group"}[Mordell-Weil group] $`E(K)`.

The {bpref "ec.mordell_weil_theorem"}[Mordell-Weil Theorem] says that $`E(K)` is a finitely-generated abelian group, hence

$$`E(K) \cong E(K)_{\rm tor} \times \Z^r`

where $`E(K)_{\rm tor}` is the finite {bpref "ec.torsion_subgroup"}[torsion subgroup] of $`E(K)`, and $`r\geq 0` is the *rank*.

Rank is an {bpref "ec.isogeny"}[isogeny] invariant: all curves in an {bpref "ec.isogeny_class"}[isogeny class] have the same rank.

Depends on: {uses "ec"}[] {uses "ec.isogeny"}[] {uses "ec.isogeny_class"}[] {uses "ec.mordell_weil_group"}[] {uses "ec.mordell_weil_theorem"}[] {uses "ec.torsion_subgroup"}[] {uses "nf"}[]
:::

:::definition "ec.reduction"
*Reduction of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.reduction))

An {bpref "ec"}[elliptic curve] $`E` over a number field $`K` is *{bpref "ec.semistable"}[semistable]* if it has {bpref "ec.reduction_type"}[multiplicative reduction] at every {bpref "ec.bad_reduction"}[bad prime], and has *{bpref "ec.potential_good_reduction"}[potential good reduction]* if its {bpref "ec.j_invariant"}[$`j`-invariant] is {bpref "nf.integral"}[integral].

If $`E` has potential good reduction then it cannot be semistable unless it has everywhere good reduction.

Depends on: {uses "ec"}[] {uses "ec.bad_reduction"}[] {uses "ec.j_invariant"}[] {uses "ec.potential_good_reduction"}[] {uses "ec.reduction_type"}[] {uses "ec.semistable"}[] {uses "nf.integral"}[]
:::

:::definition "ec.reduction_type"
*Reduction type.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.reduction_type))

The *reduction type* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` at a prime $`\mathfrak{p}` of $`K`
depends on the reduction $`\tilde E` of $`E` modulo $`\mathfrak{p}`. Let $`\F_q` be the {bpref "nf.ring_of_integers"}[ring of integers] of $`K` modulo $`\mathfrak{p}`, a finite field of characteristic $`p`.

$`E` has {bpref "ec.good_reduction"}[good reduction] at $`\mathfrak p` if $`\tilde E` is non-singular over $`\F_q`.   The reduction type is *ordinary* if $`\tilde E` is ordinary (equivalently, $`\tilde E(\overline{\F_q})` has $`p`-torsion) and *supersingular* otherwise.

On the other hand, if the reduction of $`E` modulo $`\mathfrak{p}` is singular, then
$`E` has {bpref "ec.bad_reduction"}[bad reduction].  There are two types of bad reduction are as follows.

$`E` has *multiplicative reduction* at $`\mathfrak p` if $`\tilde E` has a nodal singularity. It is called *split multiplicative reduction* if the two tangents at the node are defined over $`\F_q` and *non-split multiplicative reduction* otherwise.

$`E` has *additive reduction* at $`\mathfrak p` if $`\tilde E` has a cuspidal singularity.

Depends on: {uses "ec"}[] {uses "ec.bad_reduction"}[] {uses "ec.good_reduction"}[] {uses "nf"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "ec.regulator"
*Regulator of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.regulator))

The *regulator* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K`, denoted $`\operatorname{Reg}(E/K)`, is the volume of $`E(K)/E(K)_{tor}` with respect to the *height pairing* $`\langle -,-\rangle` associated to the {bpref "ec.canonical_height"}[canonical height] $`\hat{h}`, i.e. $`\langle P,Q\rangle = \frac{1}{2}(\hat{h}(P+Q)-\hat{h}(P)-\hat{h}(Q))`.

If the {bpref "ec.mordell_weil_group"}[Mordell-Weil group] $`E(K)` has {bpref "ec.rank"}[rank] $`r` and $`P_1, \ldots, P_r \in E(K)` generate $`E(K)/E(K)_{\mathrm{tor}}`, then

$$`\operatorname{Reg}(E/K) = \left|\det (\langle P_i, P_j \rangle )_{1\leq i,j \leq r}\right|,`

which is independent of the choice of generators.

Special cases are when $`E(K)` has rank $`0`, in which case $`E(K)/E(K)_{\mathrm{tor}}=0` and $`\operatorname{Reg}(E/K)=1`, and when $`E(K)` has rank $`1`, in which case $`\operatorname{Reg}(E/K)` is equal to the {bpref "ec.canonical_height"}[canonical height] $`\hat{h}(P)` of a generator $`P`.

The canonical height used to define the regulator is usually \*normalised\* so that it is invariant under {bpref "ec.base_change"}[base change].   Note that the regulator which appears in the {bpref "ec.bsdconjecture"}[Birch Swinnerton-Dyer conjecture] is with respect to the non-normalised height; this is sometimes called the Neron-Tate regulator, and denoted $`\operatorname{Reg}_{\rm NT}(E/K)`.  These are related by

$$`\operatorname{Reg}_{\rm NT}(E/K) = d^r \operatorname{Reg}(E/K),`

where $`d` is the {bpref "nf.degree"}[degree] $`[K:\Q]`.

Depends on: {uses "ec"}[] {uses "ec.base_change"}[] {uses "ec.canonical_height"}[] {uses "ec.mordell_weil_group"}[] {uses "ec.rank"}[] {uses "nf"}[] {uses "nf.degree"}[]
:::

:::definition "ec.ring"
*Elliptic curve over a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.ring))

An *elliptic curve* over a {bpref "ring"}[commutative ring] $`R` is an {bpref "ec.scheme"}[elliptic scheme] $`E \to \operatorname{Spec} R`.

For example, an elliptic curve over $`\Z[1/N]` is the same as an {bpref "ec"}[elliptic curve] over $`\Q` with {bpref "ec.good_reduction"}[good reduction] at all primes not dividing $`N`.  (More precisely, the latter is the generic fiber of the former.)

Depends on: {uses "ec"}[] {uses "ec.good_reduction"}[] {uses "ec.scheme"}[] {uses "ring"}[]
:::

:::definition "ec.scheme"
*Elliptic scheme.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.scheme))

An *elliptic scheme* over a scheme $`S` is a smooth proper morphism $`E \to S` whose fibers are elliptic curves.
:::

:::definition "ec.semi_global_minimal_model"
*Semi-global minimal model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.semi_global_minimal_model))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` of {bpref "nf.class_number"}[class number] $`h(K)` greater than $`1` may not have a {bpref "ec.global_minimal_model"}[global minimal model].  In this case there still exist *semi-global minimal models* for $`E` which are {bpref "ec.local_minimal_model"}[local minimal models] at all except one prime.  At this prime, the {bpref "ec.discriminant"}[discriminant] valuation exceeds that of the {bpref "ec.minimal_discriminant"}[minimal discriminant ideal] by $`12`.

Depends on: {uses "ec"}[] {uses "ec.discriminant"}[] {uses "ec.local_minimal_model"}[] {uses "ec.minimal_discriminant"}[] {uses "nf"}[] {uses "nf.class_number"}[]
:::

:::definition "ec.semistable"
*Semistable elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.semistable))

An {bpref "ec"}[elliptic curve] is *semistable* if it has {bpref "ec.reduction_type"}[multiplicative reduction] at every {bpref "ec.bad_reduction"}[bad prime].

Depends on: {uses "ec"}[] {uses "ec.bad_reduction"}[] {uses "ec.reduction_type"}[]
:::

:::definition "ec.simple_equation"
*Simplified equation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.simple_equation))

Every {bpref "ec"}[elliptic curve] over a {bpref "ring.field"}[field] $`k` whose {bpref "ring.characteristic"}[characteristic] is not 2 or 3 has a *simplified equation* (or *short Weierstrass model*) of the form $`y^2 = x^3 + Ax + B`.  When $`k=\mathbb{Q}` is the field of rational numbers, one can choose $`A` and $`B` to be integers.

For elliptic curves over $`\Q` this model will necessarily have {bpref "ec.bad_reduction"}[bad reduction] at 2, even when $`E` has {bpref "ec.good_reduction"}[good reduction] at 2; it may also bad reduction at 3 even when the {bpref "ec.q.minimal_weierstrass_equation"}[minimal model] of $`E` does not.

Depends on: {uses "ec"}[] {uses "ec.bad_reduction"}[] {uses "ec.good_reduction"}[] {uses "ec.q.minimal_weierstrass_equation"}[] {uses "ring.characteristic"}[] {uses "ring.field"}[]
:::

:::definition "ec.special_value"
*Special value of an elliptic curve L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.special_value))

The *special value* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is the first nonzero value of $`L^{(r)}(E,1)/r!` for $`r\in \Z_{\ge 0}`, where $`L(E/K,s)` is the {bpref "lfunction"}[L-function] of $`E` in its {bpref "lfunction.normalization"}[arithmetic normalization].  It is also known as the {bpref "lfunction.leading_coeff"}[*leading coefficient*] of the L-function.

The special value appears in the {bpref "ec.bsdconjecture"}[Birch and Swinnerton-Dyer conjecture].

Depends on: {uses "ec"}[] {uses "ec.bsdconjecture"}[] {uses "lfunction"}[] {uses "lfunction.leading_coeff"}[] {uses "lfunction.normalization"}[] {uses "nf"}[]
:::

:::definition "ec.split_multiplicative_reduction"
*Split multiplicative reduction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.split_multiplicative_reduction))

An {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] $`K` is said to have *split multiplicative reduction* at a prime $`\mathfrak{p}` of $`K` if the reduction of $`E` modulo $`\mathfrak{p}` has a nodal singularity with both tangent slopes defined over the residue field at $`\mathfrak{p}`.

Depends on: {uses "ec"}[] {uses "nf"}[]
:::

:::definition "ec.tamagawa_number"
*Tamagawa number.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.tamagawa_number))

The *Tamagawa number* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "nf"}[number field] at a prime $`\mathfrak{p}` of $`K` is the index $`[E(K_{\mathfrak{p}}):E^0(K_{\mathfrak{p}})]`, where $`K_{\mathfrak{p}}` is the completion of $`K` at $`\mathfrak{p}` and $`E^0(K_{\mathfrak{p}})` is the subgroup of $`E(K_{\mathfrak{p}})` consisting of all points whose reduction modulo $`\mathfrak{p}` is smooth.

The Tamagawa number of $`E` at $`\mathfrak{p}` is usually denoted $`c_{\mathfrak{p}}(E)`.  It is a positive integer, and equal to $`1` if $`E` has {bpref "ec.good_reduction"}[good reduction] at  $`\mathfrak{p}` and may be computed in general using Tate's algorithm.

The product of the Tamagawa numbers over all primes is a positive integer known as the *Tamagawa product*.

Depends on: {uses "ec"}[] {uses "ec.good_reduction"}[] {uses "nf"}[]
:::

:::definition "ec.torsion_order"
*Torsion order of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.torsion_order))

The *torsion order* of an {bpref "ec"}[elliptic curve] $`E` over a field $`K` is the order of the {bpref "ec.torsion_subgroup"}[torsion subgroup] $`E(K)_{\text{tor}}` of its {bpref "ec.mordell_weil_group"}[Mordell-Weil group] E(K).

The torsion subgroup $`E(K)_{\text{tor}}` is the set of all points on $`E` with coordinates in $`K` having finite order in the group $`E(K)`.  When $`K` is a number field (for example, when $`K=\Q`) it is a finite set, since by the {bpref "ec.mordell_weil_theorem"}[Mordell-Weil Theorem], $`E(K)` is finitely generated.

When $`K=\Q` the torsion order $`n` satisfies $`n\le16`, by a theorem of Mazur.

Depends on: {uses "ec"}[] {uses "ec.mordell_weil_group"}[] {uses "ec.mordell_weil_theorem"}[] {uses "ec.torsion_subgroup"}[]
:::

:::definition "ec.torsion_subgroup"
*Torsion subgroup of an elliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.torsion_subgroup))

For an elliptic curve $`E` over a field $`K,` the *torsion subgroup* of $`E` over $`K` is the subgroup $`E(K)_{\text{tor}}` of the {bpref "ec.mordell_weil_group"}[Mordell-Weil group] $`E(K)` consisting of points of finite order.  For a number field $`K` this is always a finite group, since by the {bpref "ec.mordell_weil_theorem"}[Mordell-Weil Theorem] $`E(K)` is finitely generated.

The torsion subgroup is always either cyclic or a product of two cyclic groups.
The *torsion structure* is the list of invariants of the group:

- $`[]` for the trivial group;

- $`[n]` for a cyclic group of order $`n>1`;

- $`[n_1,n_2]` with $`n_1\mid n_2` for a product of non-trivial cyclic groups of orders $`n_1` and $`n_2`.

For $`K=\Q` the possible torsion structures are $`[n]` for $`n\le10` and $`n=12`, and $`[2,2n]` for $`n=1,2,3,4`.

Depends on: {uses "ec.mordell_weil_theorem"}[] {uses "ec.mordell_weil_group"}[]
:::

:::definition "ec.twists"
*Twists of elliptic curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.twists))

A *twist* of an {bpref "ec"}[elliptic curve] $`E` defined over a {bpref "ring.field"}[field] $`K` is another elliptic curve $`E'`, also defined over $`K`, which is isomorphic to $`E` over the algebraic closure of $`K`.

Two elliptic curves are twists if an only if they have the same {bpref "ec.j_invariant"}[$`j`-invariant].

For elliptic curves $`E` with $`j(E)\not=0, 1728`, the only twists of $`E` are its *quadratic twists* $`E^{(d)}`.  Provided that the {bpref "ring.characteristic"}[characteristic] of $`K` is not $`2`, the nontrivial quadratic twists of $`E` are in bijection with the nontrivial elements $`d` of $`K^*/(K^*)^2`, and  $`E^{(d)}` is isomorphic to $`E` over the quadratic extension $`K(\sqrt{d})`.

Over fields of characteristic not $`2` or $`3`, elliptic curves with $`j`-invariant $`1728` also admit *quartic twists*, parametrised by $`K^*/(K^*)^4`, and elliptic curves with $`j`-invariant $`0` also admit *sextic twists*, parametrised by $`K^*/(K^*)^6`.  Elliptic curves $`E` over fields $`K` of characteristic $`2` and $`3` with $`j(E)=0=1728` have nonabelian {bpref "g2c.aut_grp"}[automorphism] groups, and their twists are more complicated to describe, being in all cases parametrised by $`H^1(\Gal(\overline{K}/K), \Aut(E))`.

Elliptic curve twists are a special case of {bpref "av.twist"}[twists of abelian varieties].

Depends on: {uses "av.twist"}[] {uses "ec"}[] {uses "ec.j_invariant"}[] {uses "g2c.aut_grp"}[] {uses "ring.characteristic"}[] {uses "ring.field"}[]
:::

:::definition "ec.weierstrass_coeffs"
*Weierstrass equation or model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.weierstrass_coeffs))

A *Weierstrass equation* or *Weierstrass model* over a field $`k` is a plane curve $`E` of the form

$$`y^2 + a_1xy + a_3y = x^3 + a_2 x^2 + a_4 x + a_6,`

with $`a_1, a_2, a_3, a_4, a_6 \in k`.

The *Weierstrass coefficients* of this model $`E` are the five coefficients $`a_i`.  These are often displayed as a list $`[a_1, a_2, a_3, a_4, a_6]`.

It is common not to distinguish between the _affine_ curve defined by a Weierstrass equation and its _projective closure_, which contains exactly one additional _point at infinity_, $`[0:1:0]`.

A Weierstrass model is smooth if and only if its {bpref "ec.discriminant"}[discriminant] $`\Delta` is nonzero.  In this case, the plane curve $`E` together with the point at infinity as base point, define an {bpref "ec"}[elliptic curve] defined over $`k`.

Two smooth Weierstrass models define isomorphic elliptic curves if and only if they are {bpref "ec.weierstrass_isomorphism"}[isomorphic] as Weierstrass models.

Depends on: {uses "ec"}[]
:::

:::definition "ec.weierstrass_isomorphism"
*Isomorphism between Weierstrass models.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ec.weierstrass_isomorphism))

Two {bpref "ec.weierstrass_coeffs"}[Weierstrass models] $`E`, $`E'` over a field $`K` with Weierstrass coefficients $`[a_1,a_2,a_3,a_4,a_6]` and $`[a'_1,a'_2,a'_3,a'_4,a'_6]` are *isomorphic over $`K`* if there exist $`u\in K^*` and $`r,s,t\in K` such that

$$`\begin{aligned}       u  a_1' &= a_1+2s,                               \\
        u^2a_2' &= a_2-sa_1+3r-s^2,                      \\
        u^3a_3' &= a_3+ra_1+2t,                          \\
        u^4a_4' &= a_4-sa_3+2ra_2-(t+rs)a_1+3r^2-2st,    \\
        u^6a_6' &= a_6+ra_4+r^2a_2+r^3-ta_3-t^2-rta_1.   \\
\end{aligned}`

The set of transformations with parameters $`[u,r,s,t]\in K^*\times K^3` form the group of *Weierstrass isomorphisms*, which acts on both the set of all Weierstrass models over $`K` and also on the subset of smooth models, preserving the point at infinity.  The discriminants $`\Delta`, $`\Delta'` of the two models are related by

$$`u^{12}\Delta' = \Delta.`

In the smooth case such a Weierstrass isomorphism $`[u,r,s,t]` induces an {bpref "ec.isomorphism"}[isomorphism] between the two elliptic curves $`E`, $`E'` they define.  In terms of affine coordinates this is given by

$$`(x,y) \mapsto (x',y')`

where

$$`\begin{aligned}
                x &= u^2x' + r          \\
                y &= u^3y' + su^2x' + t \\
    \end{aligned}`

Depends on: {uses "ec.isomorphism"}[] {uses "ec.weierstrass_coeffs"}[]
:::
