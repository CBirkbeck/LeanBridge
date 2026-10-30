import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Local fields" =>

This section lists the LMFDB definitions in the category `lf`. Each definition links back to its LMFDB knowl.

:::definition "lf" (lean := "IsNonarchimedeanLocalField, TauCeti.FinitePadicExtension")
*$`p`-adic field (local number field).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf))

{bpref "lf.local_field"}[]

Depends on: {uses "lf.local_field"}[]
:::

:::definition "lf.associated_inertia"
*Associated inertia.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.associated_inertia))

Let $`L/K` be a finite extension, let $`L^{un}/K` be the {bpref "lf.unramified_subfield"}[maximal unramified subextension] of $`L/K`, and let $`\varphi \in L^{un}[x]` be an {bpref "lf.eisenstein_polynomial"}[Eisenstein] polynomial defining $`L/L^{un}`.  The *associated inertia* of a segment of the {bpref "lf.ramification_polygon"}[ramification polygon] of
$`\varphi` is the least common multiple of the degrees of the irreducible factors of the {bpref "lf.residual_polynomials"}[residual polynomial] of that segment.  The associated inertias are divisors of the inertia degree of $`\varphi` and are invariants of $`L/K`.

Depends on: {uses "lf.eisenstein_polynomial"}[] {uses "lf.ramification_polygon"}[] {uses "lf.residual_polynomials"}[] {uses "lf.unramified_subfield"}[]
:::

:::definition "lf.automorphism_group" (lean := "AlgEquiv, AlgEquiv.aut, IsGalois.card_aut_eq_finrank, IsGalois.of_card_aut_eq_finrank")
*Automorphism group of a field extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.automorphism_group))

If $`K/F` is an extension of {bpref "ring.field"}[fields], its *automorphism group* is

$$`\textrm{Aut}(K/F) = \{\sigma:K\to K\mid  \forall a\in F, \sigma(a)=a, \text{ and } \sigma \text{ is an isomorphism}\}.`

Note, a finite extension is {bpref "nf.is_galois"}[Galois] if and only if $`|\textrm{Aut}(K/F)| = [K:F]`.

Depends on: {uses "nf.is_galois"}[] {uses "ring.field"}[]
:::

:::definition "lf.defining_polynomial" (lean := "IsAdjoinRoot, IsAdjoinRootMonic, minpoly, IntermediateField.adjoinRootEquivAdjoin")
*Defining polynomial of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.defining_polynomial))

The *defining polynomial* of a {bpref "lf.padic_field"}[$`p`-adic field] $`K` is an irreducible polynomial $`f(x)\in\mathbb{Q}_p[x]` such that $`K\cong \mathbb{Q}_p(a)`, where $`a` is a root of $`f(x)`.

The defining polynomial can be chosen to be monic with coefficients in $`\mathbb{Z}_p`; by Krasner's lemma, we can further take $`f(x)\in \mathbb{Z}[x]`.

The LMFDB uses the following conventions for choosing defining polynomials:

 1. For {bpref "lf.unramified_degree"}[unramified] extensions, the polynomial needs to be irreducible modulo $`p`.  When it is feasible to compute, we use the {bpref "field.finite.conway_polynomial"}[Conway polynomial] for the residue prime $`p` and the given degree.
 2. For {bpref "lf.ramification_index"}[totally ramified] extensions, we pick an {bpref "lf.eisenstein_polynomial"}[Eisenstein] polynomial which is reduced in the sense of Monge.
 3. In the remaining cases, we pick a polynomial which is in {bpref "lf.eisenstein_form"}[Eisenstein form].

Depends on: {uses "field.finite.conway_polynomial"}[] {uses "lf.eisenstein_form"}[] {uses "lf.eisenstein_polynomial"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.unramified_degree"}[]
:::

:::definition "lf.degree" (lean := "Module.finrank, TauCeti.FinitePadicExtension")
*Degree of a local field extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.degree))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
The *degree* of $`L/K` is the dimension of $`L` as a vector space over $`K`.

The *base degree* $`n_0` of $`L/K` is the degree of $`K/\Q_p`.  The *absolute degree* $`n_{\mathrm{abs}}`
of $`L/K` is the degree of $`L/\Q_p`.

Depends on: {uses "lf.padic_field"}[]
:::

:::definition "lf.discriminant_exponent" (lean := "TauCeti.differentExponent, TauCeti.discriminantExponent, TauCeti.discriminantIdeal")
*Discriminant exponent of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.discriminant_exponent))

Let $`L/K` be a finite extension of {bpref "lf.padic_field"}[$`p`-adic fields], with {bpref "lf.ring_of_integers"}[rings of integers] $`\mathcal{O}_L` and $`\mathcal{O}_K` and {bpref "lf.ramification_index"}[uniformizers] $`\pi_L` and $`\pi_K`.  The *discriminant* of $`L/K` is the square of the determinant of the matrix

$$`\left( \begin{array}{ccc}
 \sigma_1(\beta_1) & \cdots & \sigma_1(\beta_n) \\
\vdots & & \vdots \\
\sigma_n(\beta_1) & \cdots & \sigma_n(\beta_n) \\
\end{array} \right)`

where $`\sigma_1,..., \sigma_n` are the embeddings of $`L` into an algebraic closure $`\overline{K}`, and $`\{\beta_1, \ldots, \beta_n\}` is a basis for $`\mathcal{O}_L` as a free $`\mathcal{O}_K`-module.

The discriminant of $`L/K` is an element of $`K^\times` which is well-defined up to the square of a unit.  Thus, it is of the form $`\pi_K^c u` where $`u \in \mathcal{O}_K^\times` is a unit.  The value $`c` is the *discriminant exponent* for $`L/K`.  Together with the {bpref "lf.discriminant_root_field"}[discriminant root field] of $`L/K`, it determines the discriminant of $`L/K` (up to the square of a unit).

The *base discriminant exponent* $`c_0` of $`L/K` is the discriminant exponent of $`K/\Q_p`.  The *absolute discriminant exponent* $`c_{\mathrm{abs}}` of $`L/K` is the discriminant exponent of $`L/\Q_p`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.ring_of_integers"}[]
:::

:::definition "lf.discriminant_root_field" (lean := "TauCeti.discrField, TauCeti.evenAutSubgroup, TauCeti.fixedField_evenAutSubgroup, Polynomial.discr")
*Discriminant root field of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.discriminant_root_field))

{bpref "nf.discriminant_root_field"}[]

Note if $`F=\mathbb{Q}_p`, there are only a small number of possibilities for quadratic extensions of $`\mathbb{Q}_p`.  If $`p` is odd, we let $`u` denote any unit in $`\mathbb{Z}_p` which is not a square modulo $`p`.  Then, the quadratic extensions of $`\mathbb{Q}_p` are $`\mathbb{Q}_p(\sqrt{u})` (which is the unramified quadratic extension), $`\mathbb{Q}_p(\sqrt{p})`, and $`\mathbb{Q}_p(\sqrt{pu})`.

For $`p=2`, there are seven quadratic extensions of $`\mathbb{Q}_2`.  Here we let $`u` denote any value in $`\mathbb{Z}_2` which is congruent to $`5` modulo $`8` (for example, $`u=5`) so again $`\mathbb{Q}_2(\sqrt{u})` is the quadratic unramified extension; the other six quadratic extensions are $`\mathbb{Q}_2(\sqrt{-1})`, $`\mathbb{Q}_2(\sqrt{-u})`, $`\mathbb{Q}_2(\sqrt{2})`, $`\mathbb{Q}_2(\sqrt{2u})`, $`\mathbb{Q}_2(\sqrt{-2})`, and $`\mathbb{Q}_2(\sqrt{-2u})`.

Depends on: {uses "nf.discriminant_root_field"}[]
:::

:::definition "lf.eisenstein_diagram" (lean := "IsNonarchimedeanLocalField.HerbrandInvariant.eisensteinDiagram, IsNonarchimedeanLocalField.HerbrandInvariant.pointType, IsNonarchimedeanLocalField.HerbrandInvariant.band, IsNonarchimedeanLocalField.HerbrandInvariant.pointIndex, IsNonarchimedeanLocalField.HerbrandInvariant.IsCritical")
*Eisenstein diagram.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.eisenstein_diagram))

Let $`K` be a {bpref "lf.padic_field"}[$`p`-adic field] whose
{bpref "lf.residue_field"}[residue field] has $`q` elements.
Let $`I/K` be a {bpref "lf.herbrand_invariant"}[Herbrand invariant] with
{bpref "lf.ramification_index"}[ramification index] $`e = \epsilon p^w`
and {bpref "lf.residue_field_degree"}[residue field degree] $`f`.  Then
$`I` can be expressed in terms of {bpref "lf.slopes"}[Swan slopes]
as $`I=[s_1, \dots, s_w]_{\epsilon}^f`, in terms of {bpref "lf.means"}[means]
as $`I=\langle m_1,\dots,m_w\rangle_{\epsilon}^f`, or in terms of
{bpref "lf.rams"}[rams] as $`I=(r_1, \dots, r_w)_{\epsilon}^f`.  The
*Eisenstein diagram of $`I/K`* gives a visual summary of the process
that produces the generic polynomial

$$`x^e + \pi \sum_{\sigma} f_{\sigma} \pi^j x^i`

associated to $`I/K`.  Here $`\sigma` and $`(i,j)` are related by
$`\sigma = je + i` with $`0 \le i < e`.  The Eisenstein diagram is drawn
in the vertical strip $`R` with horizontal coordinate $`i \in [0,e)` and
vertical coordinate $`s \in [0,s_w]`.   Notably, it only depends on the
Herbrand invariant $`I=[s_1, \dots, s_w]_{\epsilon}^f`, and not on the
ground field $`K` (with a minor exception: when $`\epsilon > 1` the diagram
depends slightly on whether $`\gcd(\epsilon, q^f-1) > 1`).

*A spiral with points representing monomials*

We think of the rectangle $`R` as a cut and unrolled cylinder, with each horizontal line segment of constant level $`s` coming from a circle.  We draw the spiral that starts at
$`(0,0)` and goes up with slope $`1/e`.   This spiral wraps every time it meets the right edge of $`R`.  The part of the spiral that goes from $`(0,j)` to $`(e,j+1)` is called the $`j^{\rm th}` ramp.

We place conditions on the term $`\pi f_{\sigma} \pi^j x^i` by referring
to the unique point $`P_{\sigma}` on ramp $`j` with horizontal
coordinate $`i`.   Equivalently $`P_{\sigma}` is the unique point
on the spiral with $`s = \sigma/e`.  Thus $`P_0 = (0,0)` is the
starting point of the spiral, and as one goes up one
encounters the points $`P_1, \dots, P_{\lfloor e s_w \rfloor}` in
order.

*Bands*

For $`k=1,\dots,w`, the *band* $`B_k` is defined to be the set of points in $`R` satisfying $`m_k \leq s < s_k`.  As $`k` increases, the $`m_k` strictly increase and so the bottom edges of bands go up.  However the $`s_k` only weakly increase.   So the top edges of the bands $`B_k` for $`k` in a segment of common $`s_k` agree, even as the widths of these bands successively decrease by a factor of $`p`.  The vertical width of $`B_k` is given by the {bpref "lf.rams"}[tiny ram] $`r_k'`.  We also make the convention that $`B_0` is the set of points with $`s=0`.

We shade bands by gray and indicate overlaps by darkening the gray.  We color bottom edges of bands green and the bounding top edges black.  In the rare cases where an upper edge agrees with a lower edge we dash this boundary using black and green.
These conventions assist in visually identifying the bands, even when they overlap.

{bpref "lf.herbrand_invariant"}[Arithmetic bands], which are the bands
for which the {bpref "lf.rams"}[small ram] $`r_k^*` is an integer, are
marked by a black segment at their right end.
{bpref "lf.herbrand_invariant"}[Geometric bands] are those that are
not arithmetic.

*Index and types of points*

We say that the *index* of an integer $`i \in [0,e)` is $`k = w-\operatorname{ord}_p(\gcd(i,p^w)) \in \{0,1,\dots,w\}`.   We partition
 the points $`P_{\sigma}` with index $`k` into five types, using colors and shapes
 to distinguish the types.

 The point $`P_0 = (0,0)` plays a special role.  We call it the *$`D`-point* and we mark it by an \*olive pentagon\*.
A $`D`-point is *critical* and
drawn solid if $`\gcd(\epsilon,q^f-1)>1`.  Otherwise
it is *negligible* and drawn hollow.  Here, like with the red diamonds below,
 the solidness indicates complications in the process
 of choosing unique distinguished polynomials for fields $`L/K` in the family.

 For $`\sigma>0`, we use the band $`B_k` to classify the points $`P_{\sigma}` of index $`k` as follows.

- *$`Z`-points* are points beneath $`B_k`.  Their

associated color is \*clear\*, meaning we don't draw them.

- *$`A`-points* are the points $`P_{\sigma}`

which are at the bottom edge of geometric bands $`B_k` for which
$`k` is final in its segment, meaning that either $`k=w` or $`s_{k+1}>s_k`.  We draw them as \*solid green squares\*.

- *$`B`-points* are points in their governing band $`B_k`

which are not $`A`-points.   They are represented by \*solid blue disks\*.

- *$`C`-points* are points above their governing band.  They are represented by \*red diamonds\*.   A $`C`-point is *critical* and drawn solid if it is on the top border of any band.  Otherwise it is *negligible* and drawn hollow.

*The generic polynomial*

Using the drawn points, we may put conditions on the generic polynomial.  Namely, we may require $`f_{\sigma} = 0` for $`Z`-points and negligible $`C`-points, $`f_{\sigma} \ne 0` for $`A`-points, and $`f_0 = 1` if the $`D`-point is negligible.  To make the structure more evident, we replace $`f_{\sigma}` in the generic polynomial by $`d_{\sigma}`, $`a_{\sigma}`, $`b_{\sigma}`, or $`c_{\sigma}` according to whether $`P_{\sigma}` is a $`D`-point, $`A`-point, $`B`-point, or $`C`-point.  Let $`K_f` be the unique
{bpref "lf.ramification_index"}[unramified] extension of $`K` of degree
$`f`.  As a consequence of Monge's reduction algorithm
, every extension in the family $`I/K` is represented by a specialization of the generic polynomial, with values for coefficients drawn from a fixed choice of lifts from the residue field $`\mathbb{F}_{q^f}` of $`K_f`.
Additional constraints can be put on the choices of $`c_{\sigma}` and $`d_0`, since
only one representative modulo a subgroup of $`\F_{q^f}` or $`\F_{q^f}^{\times}` is needed.  The {bpref "lf.family_ambiguity"}[ambiguity] of the family measures how far from bijective this association between specialization and field extensions is.

*The size of a family*

Let $`\delta \in \{0,1\}` be the number of critical $`D`-points, and let $`\alpha`, $`\beta`, and $`\gamma` be the number of $`A`-points, $`B`-points, and critical $`C`-points respectively.  The number of specializations is $`(q^f-1)^{\delta+\alpha}
q^{f\beta+f\gamma}` (if we ignore the additional constraints on $`c_{\sigma}` and
$`d_0`).  Monge reduction gives another expression for this quantity, namely $`\frac{(q^f-1)^{\delta} q^{f\gamma}}{|\Aut(L/K)|}`.  Accordingly, one gets a {bpref "lf.family_mass"}[mass] formula

$$`M(I/K) := \sum_{L/K \in I/K} \frac{1}{|\Aut(L/K)|}= (q^f-1)^\alpha q^{f\beta}.`

In the rigid case $`\delta = \gamma = 0` where $`|\Aut(L/K)|=1` is forced, this
becomes a cardinality formula.

*Slopes, means, and rams on Eisenstein diagrams*

When drawing Eisenstein diagrams we indicate the slopes, means, and rams in appropriate places.  There is no need to tick the vertical axis at the left of the diagram in the traditional way, because the left endpoint of the $`j^{\rm th}` ramp is the integer $`j`.  Instead we give decimal approximations to lower edges $`m_k` and upper edges $`s_k`.  In the leftmost column, we also give the scaled versions $`em_k` and $`es_k`.  These scaled versions make the subscripts on the marked points $`P_{\sigma}` more immediately identifiable.

The {bpref "lf.rams"}[ram] $`r_k` is printed to the immediate right of the upper boundary of the band $`B_k`.  It gives two point counts as follows.  First, keeping in mind that the band $`B_k` includes its lower boundary but not its upper boundary, the number of drawn points in $`B_k` of index at most $`k` is $`\lceil r_k \rceil`.  Second, the total number of red diamonds on or below the top edge of $`B_k` is $`\lfloor r_k \rfloor`.

Depends on: {uses "lf.family_ambiguity"}[] {uses "lf.family_mass"}[] {uses "lf.herbrand_invariant"}[] {uses "lf.means"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.rams"}[] {uses "lf.residue_field"}[] {uses "lf.residue_field_degree"}[] {uses "lf.slopes"}[]
:::

:::definition "lf.eisenstein_form" (lean := "Polynomial.IsEisensteinForm, Polynomial.IsEisensteinAt.isEisensteinForm")
*Eisenstein form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.eisenstein_form))

Let $`K` be a {bpref "lf.padic_field"}[$`p`-adic field], $`\mathcal{O}_K` its {bpref "lf.ring_of_integers"}[ring of integers], and $`\pi` a {bpref "lf.ramification_index"}[uniformizer] for $`\mathcal{O}_K`.

A monic polynomial $`f\in \mathcal{O}_K[x]`
is of *Eisenstein form* if
there exists a monic polynomial $`\nu(x)\in\mathcal{O}_K[x]`, irreducible modulo $`\pi`, and  $`e\in\Z^+` such that

$$`f(x)=\nu(x)^e+\sum_{i=1}^{e-1}g_i(x)\nu(x)^i+g_0(x)`

where for all $`0\le i\le e-1`, $`g_i\in\pi\mathcal{O}_K[x]`  with
$`\deg g_i<\deg\nu`,
and the minimum of the valuation of the coefficients of $`g_0` is one.

Note,

- a polynomial $`f` of Eisenstein form is irreducible in $`K[x]`

- every ramified extension of $`K` can be obtained by adjoining a root of a polynomial in Eisenstein form

- every {bpref "lf.eisenstein_polynomial"}[Eisenstein polynomial] is of Eisenstein form by taking $`\nu(x)=x`

Depends on: {uses "lf.eisenstein_polynomial"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.ring_of_integers"}[]
:::

:::definition "lf.eisenstein_polynomial" (lean := "Polynomial.IsEisensteinAt, Polynomial.IsEisensteinAt.irreducible, TauCeti.isTotallyRamified_iff_exists_eisenstein_generator")
*Eisenstein polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.eisenstein_polynomial))

Let $`D` be an integral domain and $`P` a prime ideal in $`D`.  A polynomial $`a_n x^n + \cdots + a_0\in D[x]` is *Eisenstein* (with respect to $`P`) if

- $`a_n \not\in P`

- $`a_i \in P` for all $`0\leq i < n`

- $`a_0 \not\in P^2`

An Eisenstein polynomial is irreducible in $`F[x]` where $`F` is the {bpref "ring.field_of_fractions"}[field of fractions] of $`D`.

If $`K` is a finite extension of $`\Q_p` with ring of integers $`\mathcal{O}_K`, then a finite extension $`L/K` is {bpref "lf.ramification_index"}[totally ramified] if and only if $`L=K(\alpha)` where $`\alpha` is a root of an Eisenstein polynomial in $`\mathcal{O}_K[x]`.

Depends on: {uses "lf.ramification_index"}[] {uses "ring.field_of_fractions"}[]
:::

:::definition "lf.family_ambiguity" (lean := "IsNonarchimedeanLocalField.HerbrandInvariant.ambiguity, IsNonarchimedeanLocalField.HerbrandInvariant")
*Ambiguity of a family.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.family_ambiguity))

Let $`K` be be a {bpref "lf.padic_field"}[$`p`-adic field]
and let $`I=(r_1,\dots,r_w)_{\epsilon}^f` be a
{bpref "lf.herbrand_invariant"}[Herbrand invariant] which
is {bpref "lf.herbrand_invariant"}[compatible] with $`K`.  Let $`f_0` be the {bpref "lf.residue_field_degree"}[residue field degree] of $`K/\Q_p`,
and set $`q=p^{f_0f}`.  Let $`r_{i_1},\dots,r_{i_k}` be the
distinct integral {bpref "lf.rams"}[rams] of $`I`, and for
$`1\le j\le k` let $`\rho_j` be the multiplicity of $`r_{i_j}` in $`I`.
The *ambiguity* of $`I` over $`K` is

$$`\text{Amb}(I/K)=f\cdot\gcd(\epsilon,q-1)\cdot\prod_{j=1}^k\gcd(p^{\rho_j},q).`

For each $`L/K` in the {bpref "lf.family_polynomial"}[family]
$`I/K`, the number of semicanonical polynomials representing $`L/K` is
a divisor of $`\frac{\operatorname{Amb}(I/K)}{\lvert\operatorname{Aut}(L/K)\rvert}`.

Depends on: {uses "lf.family_polynomial"}[] {uses "lf.herbrand_invariant"}[] {uses "lf.padic_field"}[] {uses "lf.rams"}[] {uses "lf.residue_field_degree"}[]
:::

:::definition "lf.family_base" (lean := "IsNonarchimedeanLocalField.ExtensionFamily, IsNonarchimedeanLocalField.ExtensionClass, IsNonarchimedeanLocalField.HerbrandInvariant.family")
*Base field of a family of $`p`-adic field extensions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.family_base))

A {bpref "lf.family_polynomial"}[family] of extensions of
{bpref "lf.padic_field"}[$`p`-adic fields] is a collection of
extensions $`L/K` with $`K` a fixed $`p`-adic field.  The field $`K`
is called the *base field* of the family.

Depends on: {uses "lf.family_polynomial"}[] {uses "lf.padic_field"}[]
:::

:::definition "lf.family_field_count" (lean := "IsNonarchimedeanLocalField.HerbrandInvariant.fieldCount, IsNonarchimedeanLocalField.HerbrandInvariant.family, IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf, IsNonarchimedeanLocalField.visibleSwanSlopes")
*Field count.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.family_field_count))

Let $`I/K` be a {bpref "lf.family_polynomial"}[family] of
extensions of  {bpref "lf.padic_field"}[$`p`-adic fields].  The
*field count* of $`I/K` is the number of extensions in $`I/K`.

Depends on: {uses "lf.family_polynomial"}[] {uses "lf.padic_field"}[]
:::

:::definition "lf.family_label"
*Family labels.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.family_label))

Let $`K` be a finite extension of $`\Q_p`, with $`K\ne\Q_p`.
The label associated to a relative
{bpref "lf.family_polynomial"}[family] $`I/K` has the form
$`s\text{-}f.e.c\ell`, where

- $`s` is the {bpref "lf.field_label"}[label] attached to the base

field $`K`,

- $`f` is the {bpref "lf.residue_field_degree"}[residue field degree]

of every $`L/K\in I/K`,

- $`e` is the {bpref "lf.ramification_index"}[ramification index] of

every $`L/K\in I/K`,

- $`c` is the {bpref "lf.discriminant_exponent"}[discriminant exponent]

of every $`L/K\in I/K`,

- $`\ell` is a string of one or more letters used to distinguish families

with the same basic data.  It is defined by sorting the families by their number of {bpref "lf.wild_segments"}[wild segments], then the list of lengths of the wild segments, then the {bpref "lf.rams"}[rams].

The label associated to an absolute family $`I/\Q_p` has the form
$`p.f.e.c\ell`, where $`f,e,c,\ell` are defined as above, with $`K=\Q_p`.

Depends on: {uses "lf.discriminant_exponent"}[] {uses "lf.family_polynomial"}[] {uses "lf.field_label"}[] {uses "lf.ramification_index"}[] {uses "lf.rams"}[] {uses "lf.residue_field_degree"}[] {uses "lf.wild_segments"}[]
:::

:::definition "lf.family_mass" (lean := "IsNonarchimedeanLocalField.HerbrandInvariant.mass, IsNonarchimedeanLocalField.HerbrandInvariant.absoluteMass, IsNonarchimedeanLocalField.extensionMass, IsNonarchimedeanLocalField.absoluteExtensionMass, IsNonarchimedeanLocalField.extensionMass_eq_of_algEquiv")
*Mass of a family.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.family_mass))

Let $`I/K` be a {bpref "lf.family_polynomial"}[family] of extensions of
$`p`-adic fields with {bpref "lf.family_base"}[base field] $`K`.  Let $`f` be
the {bpref "lf.residue_field_degree"}[residue field degree] of
the family, and let $`K_f` be the {bpref "lf.unramified_degree"}[unramified]
extension of $`K` of degree $`f`, which is contained in every $`L/K \in I/K`.
To each $`L/K\in I/K` we assign a *mass* $`1/|\operatorname{Aut}(L/K_f)|`.
The *mass of the family* $`I/K` is the sum of the
masses of the elements of $`I/K`.  We also assign an *absolute mass*
$`1/|\operatorname{Aut}(L/\Q_p)|` to each $`L/K\in I/K`, and define the
*absolute mass of the family* to be
the sum of the absolute masses of the elements of $`I/K`.  When
$`K = \Q_p`, the mass is the product of the absolute mass with $`f`.

For some families, not all of the fields within the family are contained within the LMFDB.  In these cases, we display the fraction of the absolute mass among those fields within the database as a percentage.

Depends on: {uses "lf.family_base"}[] {uses "lf.family_polynomial"}[] {uses "lf.residue_field_degree"}[] {uses "lf.unramified_degree"}[]
:::

:::definition "lf.family_polynomial"
*Families of extensions of local fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.family_polynomial))

Let $`K` be a {bpref "lf.padic_field"}[$`p`-adic field] whose {bpref "lf.residue_field"}[residue field] has cardinality $`q` and
let $`I=[s_1,\dots,s_w]_{\epsilon}^f` be a
{bpref "lf.herbrand_invariant"}[Herbrand invariant].
The *family* $`I/K` of extensions
associated to this data is the set of all $`K`-isomorphism
classes of extensions $`L/K` of {bpref "lf.residue_field_degree"}[residue field degree] $`f` and {bpref "lf.ramification_index"}[ramification index] $`e=\epsilon p^w`
whose {bpref "lf.slopes"}[Swan slopes] are $`s_1,\dots,s_w`
(see Monge ).
If $`K=\Q_p` we say that $`I/\Q_p` is an *absolute family*; otherwise say
$`I/K` is a *relative family*.

Associated to the family $`I/K` is a *generic polynomial*
$`f_I(x)`.  Let $`K_f` be the {bpref "lf.unramified_degree"}[unramified extension] of $`K` of degree $`f`.  Define a function $`\sigma(i,j)=ej+i` and let $`\mathcal{R}`
be a set of coset representatives for $`\lambda = \mathcal{O}_{K_f}/\mathcal{M}_{K_f}`
which includes 0 and 1.  The generic polynomial for $`I/K` has the form

$$`f_I(x)=d_0\pi_K+\sum_{(i,j)\in\mathcal{A}}a_{\sigma(i,j)}\pi_K^ix^j+
\sum_{(i,j)\in\mathcal{B}}b_{\sigma(i,j)}\pi_K^ix^j+
\sum_{(i,j)\in\mathcal{C}}c_{\sigma(i,j)}\pi_K^ix^j+x^e,`

where $`\mathcal{A}`, $`\mathcal{B}`, and $`\mathcal{C}` are finite sets.
More precisely, the elements of $`\mathcal{C}` correspond to a subset of
the set $`\{s_1,\dots,s_w\}` of Swan slopes, and the elements of
$`\mathcal{A}` correspond to certain
{bpref "lf.indices_of_inseparability"}[indices of inseparability].  The {bpref "lf.eisenstein_diagram"}[Eisenstein diagram] gives a visual description of the process for producing the generic polynomial.

One obtains Eisenstein polynomials over $`\mathcal{O}_{K_f}` known as
*semicanonical polynomials* by specializing the parameters in
$`f_I(x)`.  More precisely, we may choose
$`a_{\sigma(i,j)}\in\mathcal{R}\smallsetminus\{0\}` and
$`b_{\sigma(i,j)}\in\mathcal{R}` arbitrarily.  For each
$`(i,j)\in\mathcal{C}`, $`c_{\sigma(i,j)}` is chosen from a subset
$`S_{(i,j)}` of $`\mathcal{R}` which corresponds to coset
representatives for a certain quotient of
$`\lambda`.  We choose $`d_0` from a
subset of $`\mathcal{R}\smallsetminus\{0\}` corresponding to coset
representatives for $`\lambda^\times / (\lambda^\times)^\epsilon`; in particular if $`\gcd(\epsilon, q^f-1) = 1` then we set $`d_0=1`.

Each element of $`I/K` is represented by an
extension $`L` of $`K_f` which is generated by a root of one
of these semicanonical polynomials.  The
{bpref "lf.family_ambiguity"}[ambiguity] of the family
is an upper bound on the number of semicanonical polynomials
corresponding to each isomorphism class of extensions in
$`I/K`.

Depends on: {uses "lf.herbrand_invariant"}[] {uses "lf.indices_of_inseparability"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.residue_field"}[] {uses "lf.residue_field_degree"}[] {uses "lf.slopes"}[] {uses "lf.unramified_degree"}[]
:::

:::definition "lf.field.label"
*Label for a $`p`-adic field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.field.label))

Each {bpref "lf.family_polynomial"}[$`p`-adic family] has a label of the form "p.f.e.cA", where

- p is the {bpref "lf.residue_field"}[residue field characteristic],

- f is the {bpref "lf.residue_field_degree"}[residue field degree] of $`K` over $`\mathbb{Q}_p`,

- e is the {bpref "lf.ramification_index"}[ramification index] of $`K` over $`\mathbb{Q}_p`,

- c is the {bpref "lf.discriminant_exponent"}[discriminant exponent] of $`K` over $`\mathbb{Q}_p`,

- A is a lower case letter code, with families sorted by their number of {bpref "lf.wild_segments"}[wild segments], then the list of lengths of the wild segments, then the {bpref "lf.rams"}[rams].

Each {bpref "lf.padic_field"}[$`p`-adic field] $`K` has a label of the form "p.f.e.cAi.j", where

- p.f.e.cA is the label of the family containing the field

- i is a positive integer code, shared among fields in the same family with equivalent {bpref "lf.residual_polynomials"}[residual polynomials], sorted lexicographically by coefficients of the residual polynomial.

- j is a positive integer code, ordering fields in a given family with the same residual polynomials by their {bpref "lf.defining_polynomial"}[defining polynomial], sorted lexicographically.

Prior to 2025, local fields in the LMFDB had a different label convention, of the form p.n.c.num, where n was the {bpref "lf.degree"}[degree] and num was an integer code from an unspecified ordering.  If you have a field label in the old form, the website will translate it to the new label if you enter it in the "Find" box at the bottom of the browse page.

Depends on: {uses "lf.defining_polynomial"}[] {uses "lf.degree"}[] {uses "lf.discriminant_exponent"}[] {uses "lf.family_polynomial"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.rams"}[] {uses "lf.residual_polynomials"}[] {uses "lf.residue_field"}[] {uses "lf.residue_field_degree"}[] {uses "lf.wild_segments"}[]
:::

:::definition "lf.field_label"
*p-adic field label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.field_label))

The label associated to a {bpref "lf.padic_field"}[$`p`-adic field]
$`K` has the form $`p.f.e.c\ell m.n`, where

- $`p` is the characteristic of the

{bpref "lf.residue_field"}[residue field] of $`K`.

- $`f` is the {bpref "lf.residue_field_degree"}[residue field degree]

of $`K/\Q_p`.

- $`e` is the {bpref "lf.ramification_index"}[ramification index] of

$`K/\Q_p`,

- $`c` is the {bpref "lf.discriminant_exponent"}[discriminant exponent]

of $`K/\Q_p`,

- $`\ell` is a string of one or more letters used to identify the

{bpref "lf.family_polynomial"}[absolute family] $`I/\Q_p` that contains
$`K/\Q_p`,

- $`m` identifies the {bpref "lf.subfamily"}[subfamily] of $`I/\Q_p` that

contains $`K/\Q_p`,

- $`n` is a number used to distinguish fields in the same subfamily.

Thus if $`K` has label $`p.f.e.c\ell m.n` then $`K/\Q_p` is in the absolute
family with label $`p.f.e.c\ell`.

Depends on: {uses "lf.discriminant_exponent"}[] {uses "lf.family_polynomial"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.residue_field"}[] {uses "lf.residue_field_degree"}[] {uses "lf.subfamily"}[]
:::

:::definition "lf.galois_invariants" (lean := "IsNonarchimedeanLocalField.wildArtinSlopes, IsNonarchimedeanLocalField.swanSlopes, IsNonarchimedeanLocalField.galoisTameDegree, IsNonarchimedeanLocalField.galoisUnramifiedDegree, IsNonarchimedeanLocalField.upperRamificationGroup_eq_of_mem_Ioc")
*Galois invariants of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.galois_invariants))

Let $`K^{gal}` be the Galois closure of a {bpref "lf.padic_field"}[$`p`-adic field] $`K`. The first Galois invariant of $`K` is the {bpref "nf.galois_group"}[Galois group] $`G=\Gal(K^{gal}/\mathbb{Q}_p)`.  Most of the remaining invariants relate to the filtration on $`G` by higher ramification groups.

Let $`G^i` be the $`i`th higher ramification group in upper numbering from Serre's <i>Local Fields</i> .  They form a descending filtration of normal subgroups where $`i` is a continuous parameter, $`i\geq -1`.  Let $`G^{(j)} = G^{j-1}`, and $`G^{(j+)} = \cap_{\epsilon>0} G^{(j+\epsilon)}`.  Then

- $`G^{(0)}=G`.

- $`G^{(1)}` is the *inertia subgroup* of $`G`, i.e., the kernel of the natural map from $`G` to the {bpref "nf.galois_group"}[Galois group] of the residue field.

- the fixed field of $`G^{(1)}` is the maximum unramified subfield of $`K^{gal}/\Q_p`, which we denote by $`K^{unram}`.  The degree $`[K^{unram}:\mathbb{Q}_p]` is the *unramified degree* for $`K^{gal}/\Q_p`.  The extension $`K^{gal}/K^{unram}` is totally ramified.

- the group $`G^{(1)}/G^{(1+)}` is cyclic of order prime to $`p`.  Its order is the *tame degree* for $`K^{gal}/\Q_p` as it is the degree of the largest tamely totally ramified subextension.

- The group $`G^{(1+)}` is a $`p`-group.  Values of $`s>1` giving jumps in the filtration $`G^{(s)}\neq G^{(s+)}` are *wild Artin slopes*.  We repeat a slope $`m` times if $`p^m =[G^{(s)} : G^{(s+)}]`, and then list the wild slopes in non-decreasing order.

- The *Galois Mean Slope* is the valuation of the {bpref "nf.root_discriminant"}[root discriminant] of the Galois closure $`K^{gal}/\Q_p`.  It can also be expressed as a weighted sum of the slopes.

- A *Galois Splitting Model* of a local field $`K` is a polynomial $`f\in\Q[x]` such that $`K\cong \Q_p[x]/(f)`, and the Galois group for $`f` over $`\Q_p` equals the Galois group for $`f` over $`\Q`.  In this case, computations in the splitting field of $`f` over $`\Q_p` can be computed more easily using the splitting field of $`f` over $`\Q`.

- For each jump in the filtration $`G^{i}\neq G^{i+}` gives a *Swan slope* of $`i`.  The Swan slopes are one less than the Artin slopes.

Depends on: {uses "lf.padic_field"}[] {uses "nf.galois_group"}[] {uses "nf.root_discriminant"}[]
:::

:::definition "lf.galois_mean_slope" (lean := "TauCeti.FinitePadicExtension, TauCeti.discriminantExponent")
*Galois mean slope.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.galois_mean_slope))

Let $`K` be a finite {bpref "nf.is_galois"}[Galois] extension of $`\Q_p` for some prime $`p`.  Its *Galois mean slope* is the nonnegative rational number
$`\alpha` such that the {bpref "lf.discriminant_exponent"}[discriminant]
ideal for $`K` over $`\Q_p` is $`(p^{[K:\Q_p]\cdot \alpha})`.

The Galois mean slope can be computed as a weighted average of the {bpref "lf.slopes"}[wild Artin slopes] and {bpref "lf.tame_degree"}[tame degree] of $`K`.

Depends on: {uses "lf.discriminant_exponent"}[] {uses "lf.slopes"}[] {uses "lf.tame_degree"}[] {uses "nf.is_galois"}[]
:::

:::definition "lf.galois_splitting_model" (lean := "Polynomial.IsGaloisSplittingModel, Polynomial.Gal.restrictMap, Polynomial.Gal.nonempty_mulEquiv_iff_bijective_restrictMap, Polynomial.IsGaloisSplittingModel.finrank_eq")
*Galois splitting model of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.galois_splitting_model))

Let $`K` be a finite extension of $`\Q_p`.
A *Galois splitting model* of $`K` is an irreducible polynomial $`f\in\Q[x]` such that $`K\cong \Q_p[x]/(f)`, and the Galois group of $`f` over $`\Q` is isomorphic to the Galois group of $`f` over $`\Q_p`.

Most, but not all, local number fields have Galois splitting models.

With a Galois splitting model, the computation of various invariants related to $`K`, such as the Galois invariants, can be carried out more easily using $`f`.
:::

:::definition "lf.heights"
*Heights of an extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.heights))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
The *height* $`H(L/K)` of $`L/K` is defined by the formula $`c=f(e-1+H(L/K))`,
where $`c` is the {bpref "lf.discriminant_exponent"}[discriminant exponent],
$`f` the {bpref "lf.residue_field_degree"}[residue field degree],
and $`e` the {bpref "lf.ramification_index"}[ramification degree] of
$`L/K`.  Since $`H(L/K)` is 0 if $`L/K` is tamely ramified, and positive otherwise,
$`H(L/K)` is a measure of the wild ramification of $`L/K`.  The height $`H(L/K)`
can be expressed in terms of the {bpref "lf.means"}[mean] $`m` of $`L/K` by
$`H(L/K)=em`.  If $`L/K` is totally ramified (i.e., $`f=1`) then $`H(L/K)` is equal to the
0th {bpref "lf.indices_of_inseparability"}[index of inseparability] $`i_0`.

Now let $`K\subset L_1\subset\dots\subset L_r=L` be the sequence of subextensions
of $`L/K` which correspond to the segments of the
{bpref "lf.ramification_polygon"}[ramification polygon] of $`L/K`.  The
*set of heights* for $`L/K` is $`\{H(L_i/K):1\le i\le r\}`.

Depends on: {uses "lf.discriminant_exponent"}[] {uses "lf.indices_of_inseparability"}[] {uses "lf.means"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.ramification_polygon"}[] {uses "lf.residue_field_degree"}[]
:::

:::definition "lf.herbrand_function" (lean := "IsNonarchimedeanLocalField.HerbrandInvariant.herbrandFunction, IsNonarchimedeanLocalField.HerbrandInvariant.swanSlope, IsNonarchimedeanLocalField.HerbrandInvariant.herbrandFunction_of_mem_Icc, IsNonarchimedeanLocalField.HerbrandInvariant.herbrandFunction_of_le")
*Herbrand function of a family.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.herbrand_function))

Let $`I/K` be a {bpref "lf.family_polynomial"}[family] of extensions of
a {bpref "lf.padic_field"}[$`p`-adic field] $`K`.
We can express $`I` in terms of {bpref "lf.rams"}[rams]
as $`I=(r_1,\dots,r_w)_{\epsilon}^f`, in terms of
{bpref "lf.slopes"}[Swan slopes] as
$`I=[s_1,\dots,s_w]_{\epsilon}^f` or in terms of the {bpref "lf.means"}[means] $`\langle m_1,\dots,m_w\rangle_{\epsilon}^f`.  The *Herbrand function* of $`I/K` is
the piecewise linear function $`\phi_{I/K}:\R_{\ge0}\rightarrow\R_{\ge0}`
whose graph is obtained by joining the points
$`(0,0),(r_1,s_1),\dots,(r_w,s_w)` with
line segments; in addition, there is a ray with slope $`1/(\epsilon p^w)`
starting at $`(r_w,s_w)`.  It follows that for $`1\le i\le w` the segment
whose right endpoint is $`(r_i,s_i)` has slope $`1/(\epsilon p^{i-1})`.

The rams of $`I/K` are labeled in blue on the horizontal axis of the diagram.
The wild Swan slopes of $`I/K` are labeled in black on the vertical axis of the
diagram; to the left of each Swan slope is a rescaling by a factor
$`\epsilon p^w`.  The green numbers along the vertical axis are the means.
The rescaled green numbers on the left which correspond to
intersections of the vertical axis with extensions of segments of the graph
of $`\phi_{I/K}` give some of the
{bpref "lf.indices_of_inseparability"}[indices of inseparability] of
the extensions $`L/K` in $`I/K`.

Depends on: {uses "lf.family_polynomial"}[] {uses "lf.indices_of_inseparability"}[] {uses "lf.means"}[] {uses "lf.padic_field"}[] {uses "lf.rams"}[] {uses "lf.slopes"}[]
:::

:::definition "lf.herbrand_invariant"
*Herbrand invariant.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.herbrand_invariant))

A *Herbrand invariant* $`I` is the collection of ramification
data associated to a finite separable extension of
{bpref "lf.padic_field"}[$`p`-adic fields].  Let $`L/K` be
an extension of $`p`-adic fields with
{bpref "lf.residue_field"}[residue characteristic]
$`p`.  Let $`f` be the
{bpref "lf.residue_field_degree"}[residue field degree]
and $`\epsilon p^w` the
{bpref "lf.ramification_index"}[ramification index]
of $`L/K`, with $`p\nmid\epsilon`.
The Herbrand invariant of $`L/K` can be expressed in terms of the
{bpref "lf.slopes"}[Swan slopes]
of $`L/K` as $`I=[s_1,\dots,s_w]_{\epsilon}^f`; in terms of the
{bpref "lf.rams"}[rams] of $`L/K`
as $`I=(r_1,\dots,r_w)_{\epsilon}^f`; or in terms of the
{bpref "lf.means"}[means] of $`L/K`
as $`I=\langle m_1,\dots,m_w\rangle_{\epsilon}^f`.

As a convention, we put $`s_0=r_0=m_0=0`.   The three representations
of the Herbrand invariant of $`L/K` are related by

- $`\displaystyle s_k=\frac{p m_k-m_{k-1}}{p-1}`,

- $`\displaystyle m_k=\sum_{j=1}^k\frac{p-1}{p^{k+1-j}}s_j`,

- $`\displaystyle r_k= \epsilon p^k \frac{m_k- m_{k-1}}{p-1}`,

- $`\displaystyle m_k=\sum_{j=1}^k \frac{p-1}{\epsilon p^j}r_j`

for $`1\le k\le w`.

Alternatively, one can start with a Herbrand invariant $`I` and then
identify fields $`K` such that there exist extensions $`L/K` whose
Herbrand invariant is $`I`.  Let $`I=(r_1,\dots,r_w)_{\epsilon}^f`, with
$`r_1,\dots,r_w` a weakly increasing sequence of positive rationals and
$`\epsilon,f\in\N`.  Let $`b_1 < \dots < b_t` be the distinct elements of
$`r_1,\dots,r_w` and let $`d_i` be the multiplicity of $`b_i`.  Let $`K`
be a $`p`-adic field and let $`e_K` be the
{bpref "lf.ramification_index"}[absolute ramification index]
of $`K`.  In order for $`I` to be the Herbrand invariant of some extension
$`L/K`, for each $`1\le i\le t` we must have $`(p^{d_i}-1)b_i\in\N`, and one
of the following must hold:

- $`p\nmid(p^{d_i}-1)b_i` and

  $`b_i < \displaystyle\frac{p^{d_1+\dots+d_{i-1}+1}\epsilon e_K}{p-1}`,

- $`d_i=1` and $`b_i=\displaystyle\frac{p^{d_1+\dots+d_{i-1}+1}\epsilon e_K}{p-1}`.

In the first case we say that $`b_i` is a *geometric ram*.  In the
second case we say that $`b_i` is an *arithmetic ram*.

If the conditions above are satisfied we say that $`K` is *compatible*
with $`I`.  The compatibility of $`K` with $`I` depends only on the absolute
ramification index $`e_K` of $`K`.

Depends on: {uses "lf.means"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.rams"}[] {uses "lf.residue_field"}[] {uses "lf.residue_field_degree"}[] {uses "lf.slopes"}[]
:::

:::definition "lf.hidden_slopes"
*Hidden slopes of an extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.hidden_slopes))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields]
and let $`L^{Gal}/K` be the {bpref "nf.galois_closure"}[Galois closure]
of $`L/K`.  The *Galois Swan slopes* of $`L/K` is the multiset $`S^{Gal}` of
{bpref "lf.slopes"}[Swan slopes] of $`L^{Gal}/K` and let $`S` be
the multiset of Swan slopes of $`L/K`.  The multiset $`H` of *hidden Swan slopes* of
$`L/K` is obtained by subtracting $`S` from $`S^{Gal}`.  Thus $`S^{Gal}` is the
multiset sum of $`S` and $`H`.

The *Galois Artin slopes* and *hidden Artin slopes* are defined analogously.  In particular, they can be obtained from the corresponding Swan slopes by adding $`1` to each.

Depends on: {uses "lf.padic_field"}[] {uses "lf.slopes"}[] {uses "nf.galois_closure"}[]
:::

:::definition "lf.indices_of_inseparability" (lean := "IsNonarchimedeanLocalField.inseparabilityIndex, IsNonarchimedeanLocalField.inseparabilityIndexOf, IsNonarchimedeanLocalField.addValuation")
*Indices of inseparability.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.indices_of_inseparability))

Let $`L/K` be a finite extension of {bpref "lf.padic_field"}[$`p`-adic fields] and let
$`K'/K` be the {bpref "lf.unramified_subfield"}[maximum unramified subextension] of $`L/K`.
Set $`n=[L:K']` and write $`n=up^{\nu}` with $`p\nmid u`.
Let $`\pi_L` be a {bpref "lf.ramification_index"}[uniformizer] for $`L` and let
$`f(X)=X^n+c_{n-1}X^{n-1}\cdots+c_1X+c_0` be the minimal
polynomial of $`\pi_L` over $`K'`.  For $`k\in\Z`
define $`\overline{v}_p(k)=\min\{v_p(k),\nu\}`.  For
$`0\le j\le\nu` set

$$`i_j^{\pi_L}=\min\{nv_{K'}(c_h)+h-n:
0\le h\le n-1,\;\overline{v}_p(h)\le j\},`

or let $`i_j^{\pi_L}=\infty` if the set above is empty.
Heiermann  defines the $`j`th *index of inseparability* of $`L/K` to be

$$`i_j=\min\{i_{j'}^{\pi_L}+(j'-j)e_L:j\le j'\le\nu\},`

where $`e_L=v_L(p)` is the absolute {bpref "lf.ramification_index"}[ramification index] of
$`L`.

It follows that
$`0=i_{\nu} < i_{\nu-1}\le\dots\le i_1\le i_0`.  The value
of $`i_j^{\pi_L}` can depend on the choice of $`\pi_L`,
but $`i_j` depends only on $`L/K`.  The fact that $`i_j` is
well-defined puts constraints on the possibilities for
the valuations of the coefficients in the minimal
polynomial over $`K'` of any uniformizer for $`L`.  The
indices of inseparability determine the usual
ramification data of $`L/K` (e.g., the {bpref "lf.slopes"}[slopes]), and in
some cases give new information.

Depends on: {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.slopes"}[] {uses "lf.unramified_subfield"}[]
:::

:::definition "lf.inertia_group" (lean := "ValuationSubring.inertiaSubgroup, Ideal.inertia, Ideal.Quotient.stabilizerHom, Ideal.Quotient.map_ker_stabilizer_subtype")
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

:::definition "lf.inertia_group_search" (lean := "ValuationSubring.inertiaSubgroup, Ideal.inertia, Ideal.Quotient.stabilizerHom, Ideal.Quotient.map_ker_stabilizer_subtype")
*Inertia group searching.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.inertia_group_search))

{bpref "lf.inertia_group"}[]

When searching by inertia subgroups, it can be specified as an abstract group by either a {bpref "group.small_group_label"}[GAP id] or a group name from {bpref "gg.label"}[transitive group label].

It can also be specified by as a transitive group label.  In this case, it will only match $`p`-adic fields where the {bpref "lf.defining_polynomial"}[defining polynomial] is {bpref "ring.irreducible"}[irreducible] over the unramified extension of $`\Q_p` of degree {bpref "lf.unramified_degree"}[unramified degree] and the {bpref "gg.galois_group"}[Galois group] of the polynomial over that extension matches the specified transitive group.

Depends on: {uses "gg.galois_group"}[] {uses "gg.label"}[] {uses "group.small_group_label"}[] {uses "lf.defining_polynomial"}[] {uses "lf.inertia_group"}[] {uses "lf.unramified_degree"}[] {uses "ring.irreducible"}[]
:::

:::definition "lf.intermediate_fields" (lean := "IntermediateField")
*Intermediate fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.intermediate_fields))

For a local field $`K` which is a finite extension of $`\Q_p` for some prime $`p`, *intermediate fields* $`F` are fields with $`\Q_p\subsetneqq F \subsetneqq K`.
:::

:::definition "lf.jump_set"
*Jump set.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.jump_set))

Let $`K` be a {bpref "lf.padic_field"}[$`p`-adic field] which contains
a primitive $`p`th root of unity $`\zeta_p`.  Set $`e=v_K(p)` and
$`r=v_p(e)`.  The *jump set* associated to $`K` is an
increasing sequence of $`r+1` positive integers which
determines the structure of the 1-units of $`K` as a
filtered $`\mathbb{Z}_p`-module.  If $`K` does not contain
a primitive $`p`th root of unity then the jump set of $`K`
is not defined.

More precisely, if $`\zeta_p \in K` then Miki  showed that we can write

$$`\zeta_p=\alpha_0^{p^r}\alpha_1^{p^{r-1}}\dots
\alpha_{r-1}^p\alpha_r`

with each $`\alpha_i` satisfying one of the following
conditions:

- $`v_K(\alpha_i) < pe/(p-1)` and

$`p\nmid v_K(\alpha_i)`,

- $`v_K(\alpha_i)=pe/(p-1)` and $`\alpha_i` is not a

$`p`th power,

- $`\alpha_i=1`.

Pagano  defines the (extended) jump set associated to $`K`
by setting $`u_i=v_K(\alpha_i-1)` for all $`0\le i\le r`
such that $`\alpha_i\ne1`; these values are independent
of the choice of $`\alpha_0,\dots,\alpha_r`.  Undefined
values in the sequence $`[u_0,u_2,\dots,u_r]` are
filled in using the recursion $`u_{i+1}=\rho(u_i)`, where
$`\rho(x)=\min\{px,x+e\}`.

Depends on: {uses "lf.padic_field"}[]
:::

:::definition "lf.local_field" (lean := "IsNonarchimedeanLocalField")
*Local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.local_field))

A *local field* is a {bpref "ring.field"}[field] $`K` with a non-trivial {bpref "nf.absolute_value"}[absolute value] $`|\ |` that is locally compact in the topology induced by the distance metric $`d(x,y):=|x-y|`.

An *archimedean local field* is a local field whose absolute value is {bpref "nf.absolute_value"}[archimedean]; such a field is isomorphic to $`\R` or $`\C`.

A *nonarchimedean local field* is a local field whose absolute value is {bpref "nf.absolute_value"}[nonarchimedean]. Such a field is either isomorphic to a finite extension of $`\Q_p` when $`K` has {bpref "ring.characteristic"}[characteristic] zero (in which case it is a {bpref "lf.padic_field"}[$`p`-adic field]), or to a finite extension of $`\F_p((t))` when $`K` has characteristic $`p`.  In both cases $`p` is the characteristic of the {bpref "lf.residue_field"}[residue field] of $`K`..

Depends on: {uses "nf.absolute_value"}[] {uses "ring.characteristic"}[] {uses "ring.field"}[]
:::

:::definition "lf.local_height_function" (lean := "IsNonarchimedeanLocalField.localHeight, IsNonarchimedeanLocalField.localHeight_eq, Group.IsWeightFunction.apply_eq_of_zpowers_eq")
*Local height function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.local_height_function))

Let $`G` be a finite group and $`w` a {bpref "group.weight_function"}[weight function] on $`G`.

Let $`p` be a prime with $`p \nmid \#G` and $`\Gamma_{\Q_p}` the {bpref "group.galois.absolute"}[absolute Galois group] of $`\Q_p`. Let $`\varphi_p: \Gamma_{\Q_p} \to G` be a continuous homomorphism and $`K_{\varphi_p} = \overline{\Q}_p^{\ker \varphi_p}` the associated finite extension of $`\Q_p`. As $`p \nmid \#G` the extension $`\Q_p \subset K_{\varphi_p}` is {bpref "lf.ramification_index"}[tamely ramified], thus its {bpref "lf.inertia_group"}[inertia group] is cyclic  [tag 09EE](https://stacks.math.columbia.edu/tag/09EE). Let $`\tau_p \in \Gal(K_{\varphi_p}/\Q_p)` be a choice of generator of the inertia group.

We define the *local height* of $`\varphi_p` with respect to $`w` to be

$$`H_{w,p}(\varphi_p):=w(\varphi_p(\tau_p)).`

This yields a well-defined *local height function*
$`H_{w,p}: \Hom_{\textrm{cts}}(\Gamma_{\Q_p}, G) \to \R_{>0}`
associated to $`w`.

Depends on: {uses "group.galois.absolute"}[] {uses "group.weight_function"}[] {uses "lf.inertia_group"}[] {uses "lf.ramification_index"}[]
:::

:::definition "lf.log" (lean := "IsNonarchimedeanLocalField.iwasawaLog, IsNonarchimedeanLocalField.iwasawaLog_of_mem_unitFiltration, IsNonarchimedeanLocalField.iwasawaLog_primeUnit, IsNonarchimedeanLocalField.iwasawaLog_eq_zero_of_pow_eq_one, IsNonarchimedeanLocalField.iwasawaLog_eq_of_pow_eq")
*$`p`-adic logarithm.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.log))

Let $`K` be a finite extension of $`\Q_p` for some prime $`p`, and

$$`S=\{z \in K : |z|_p < 1\}`

where $`|\cdot|_p` is an absolute value on $`K` normalized so that $`|p|_p=1/p`.  Then the *$`p`-adic logarithm*
$`\log_p:S\to K`
is given by

$$`\log_p(1+z) = \sum_{n=1}^{\infty}(-1)^n \frac{z^n}{n}.`

One can extend $`\log_p` to $`K` by defining $`\log_p(p)=0` and $`\log_p(\zeta)=0` where $`\zeta` is any root of unity.

If $`\mathcal{O}_K` is the {bpref "lf.ring_of_integers"}[ring of integers] of $`K` and $`M` is the unique {bpref "lf.maximal_ideal"}[maximal ideal] of $`\mathcal{O}_K`, then the image of the $`p`-adic logarithm,
$`\log_p(1+M) = M` provided $`e<p-1` where $`e` is the {bpref "lf.ramification_index"}[ramification index] for $`K/\Q_p`.

Depends on: {uses "lf.maximal_ideal"}[] {uses "lf.ramification_index"}[] {uses "lf.ring_of_integers"}[]
:::

:::definition "lf.maximal_ideal" (lean := "IsLocalRing.maximalIdeal")
*Maximal ideal of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.maximal_ideal))

The *maximal ideal* of a {bpref "lf.local_field"}[nonarchimedean local field] $`K` is the unique {bpref "ring.maximal_ideal"}[maximal ideal] of its {bpref "lf.ring_of_integers"}[ring of integers] $`\mathcal O_K`.

It consists of all elements of $`\mathcal O_K` that are not {bpref "ring.unit"}[units], equivalently, all elements of $`K` whose {bpref "nf.absolute_value"}[absolute value] is strictly less than 1.

Depends on: {uses "lf.local_field"}[] {uses "lf.ring_of_integers"}[] {uses "nf.absolute_value"}[] {uses "ring.maximal_ideal"}[] {uses "ring.unit"}[]
:::

:::definition "lf.means"
*Means of an extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.means))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
The *mean* $`m` of $`L/K` is determined by the formula $`c=f(e-1+em)`, where
$`c` is the {bpref "lf.discriminant_exponent"}[discriminant exponent],
$`f` is the {bpref "lf.residue_field_degree"}[residue field degree], and
$`e` is the {bpref "lf.ramification_index"}[ramification index] of $`L/K`.
The mean of $`L/K` is related to the {bpref "lf.heights"}[height]
$`H(L/K)` by the formula $`H(L/K)=em`.

Let $`K_f/K` be the maximal unramified subextension of $`L/K`.  For each
subextension $`L'/K_f` of $`L/K_f` set $`e'=[L':K_f]` and
let $`m'` be the mean of $`L'/K_f`.  We associate to $`L'` the point
$`(e',e'm')` in the Cartesian plane.  The *slope polygon* $`S` of $`L/K` is the
lower boundary of the convex hull of these points.  Write
$`e=\epsilon p^w=[L:K_f]` and let $`h` be the function on the interval
$`[1,e]` whose graph is $`S`.  For $`1\le k\le w` set
$`m_k=h(\epsilon p^k)/(\epsilon p^k)`.  Then the *means* of $`L/K` are defined
to be $`\langle m_1,\dots,m_w\rangle`.

If we adopt the convention $`m_0=0` then the means are related to the
{bpref "lf.slopes"}[Swan slopes] $`[s_1,\dots,s_w]` by the formulas
$`(p-1)s_k=pm_k-m_{k-1}` for $`1\le k\le w`.

Depends on: {uses "lf.discriminant_exponent"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.residue_field_degree"}[] {uses "lf.slopes"}[]
:::

:::definition "lf.newton_polygon"
*Newton polygon of a polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.newton_polygon))

Let $`K` be a {bpref "lf.local_field"}[nonarchimedean local field] with discrete valuation $`v_K`, and $`f \in K[x]`, given by

$$`f(x) = a_0 + a_1 x + \cdots + a_nx^n,`

and such that $`a_0a_n \neq 0`.

Then the *Newton polygon* of $`f` is the lower convex hull of the set of points $`(i,v_K(a_i))`, if we ignore all points with $`a_i=0`.

In the context of isogeny classes of abelian varieties over finite fields, the constant term $`a_0=1` always, and therefore the Newton polygon begins at $`(0,0)`. In this context, the LMFDB accepts two methods to enter Newton polygons:

- The first is to give a list of slopes $`[s_1,s_2,s_3, \ldots]`. This denotes the Newton polygon that, starting at $`(0,0)`, is given by a line segment of width 1 with slope $`s_1`, followed by a line segment of width 1 with slope $`s_2`, etc. Note that it is possible for a slope to appear multiple times if the Newton polygon has the same slope for a width of more than 1. Note also that because the Newton polygon is a convex hull, the slopes $`s_i` will necessarily be increasing.

- The second is to give a list of points, called "breaks," $`[(x_1,y_1),(x_2,y_2), (x_3,y_3), \ldots]`, for $`0 < x_1 < x_2 < x_3 < \ldots`. This denotes the Newton polygon that, starting at $`(0,0)`, has constant slope from $`(0,0)` to $`(x_1,y_1)`, then has constant (but different) slope from $`(x_1,y_1)` to $`(x_2,y_2)`, etc. Note that by the definition of the Newton polygon, each $`x_i` is a positive integer.

Depends on: {uses "lf.local_field"}[]
:::

:::definition "lf.newton_slopes"
*Slopes of the Newton polygon of a polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.newton_slopes))

Given a polynomial $`f` defined over a {bpref "lf.local_field"}[nonarchimedean local field] $`K`, the *slopes* of its {bpref "lf.newton_polygon"}[Newton polygon] are a list of increasing numbers $`[s_1,s_2,s_3, \ldots]` such that the Newton polygon of $`f` is given by a line segment of width 1 with slope $`s_1`, followed by a line segment of width 1 with slope $`s_2`, etc. Note that it is possible for a slope to appear multiple times if the Newton polygon has the same slope for a width of more than 1.

Depends on: {uses "lf.local_field"}[] {uses "lf.newton_polygon"}[]
:::

:::definition "lf.packet"
*Packets in a family.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.packet))

Let $`I/K` be a {bpref "lf.family_polynomial"}[family] of extensions
of  {bpref "lf.padic_field"}[$`p`-adic fields].  Say the extensions
$`L_1/K,L_2/K\in I/K` are in the same *packet* if their {bpref "lf.residual_polynomials"}[residual polynomials] are equivalent and they have the same
hidden invariants.  Specifically, let $`L_1^{Gal}/K`, $`L_2^{Gal}/K` be the
{bpref "nf.galois_closure"}[Galois closures] of $`L_1/K`, $`L_2/K`.
Then $`L_1/K`, $`L_2/K` are in the same packet if

- $`\Gal(L_1^{Gal}/K)` and $`\Gal(L_2^{Gal}/K)` are isomorphic as

{bpref "group.permutation_representation"}[permutation groups],

- $`L_1^{Gal}/K` and $`L_2^{Gal}/K` have the same

{bpref "lf.residue_field_degree"}[residue field degree],

- $`L_1^{Gal}/K` and $`L_2^{Gal}/K` have the same

{bpref "lf.ramification_index"}[ramification index], and

- $`L_1/K` and $`L_2/K` have the same

{bpref "lf.hidden_slopes"}[hidden slopes].

Thus the family $`I/K` is partitioned into packets.

Depends on: {uses "group.permutation_representation"}[] {uses "lf.family_polynomial"}[] {uses "lf.hidden_slopes"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.residual_polynomials"}[] {uses "lf.residue_field_degree"}[] {uses "nf.galois_closure"}[]
:::

:::definition "lf.padic_field" (lean := "TauCeti.FinitePadicExtension, Padic, FiniteDimensional")
*$`p`-adic field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.padic_field))

A *$`p`-adic field* (or *local number field*) is a finite extension of
{bpref "lf.qp"}[$`\Q_p`], equivalently, a {bpref "lf.local_field"}[nonarchimedean local field] of {bpref "ring.characteristic"}[characteristic] zero.

Depends on: {uses "lf.local_field"}[] {uses "lf.qp"}[] {uses "ring.characteristic"}[]
:::

:::definition "lf.qp" (lean := "Padic")
*Definition of $`\Q_p`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.qp))

If $`p` is a prime number, then every rational number $`r` can be written in the form $`r=p^j \frac{a}{b}` where $`\gcd(p, ab)=1`.  We define $`|r|_p = p^{-j}`, and define a metric on $`\Q` by $`d(u,v) = |u-v|_p`; in other words, $`u` and $`v` are close to each other if they are congruent modulo a larger power of $`p`.

The completion of $`\Q` with respect to this metric is the field of *p-adic numbers*, denoted as $`\Q_p`. Any non-zero element $`x \in \Q_p` can be written uniquely as the sum of a convergent series $`x = \sum_{n=n_0}^{+\infty} a_n p^n`, where $`a_n \in \{ 0, \cdots, p-1 \}`, $`n_0 \in \Z` is such that $`|x|_p=p^{-n_0}`, and $`a_{n_0} \neq 0`.

Example: the element $`a = 3 + 7 + 2 \cdot 7^2 + 6 \cdot 7^3 + 7^4 + 2 \cdot 7^5 + \cdots` satisfies $`a^2=2`, since truncating the expansion after $`n` terms and squaring yields a number which is congruent to $`2 \bmod 7^n`.
:::

:::definition "lf.ramification_index" (lean := "Valuation.Uniformizer, TauCeti.IsTamelyRamified, TauCeti.IsTotallyRamified, TauCeti.absoluteRamificationIndex, TauCeti.ramificationIndex")
*Ramification index of an extension of $`p`-adic fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.ramification_index))

Let $`L/K` be a finite extension of {bpref "lf.padic_field"}[$`p`-adic fields].
Then $`\mathcal{O}_L` and $`\mathcal{O}_K`, the {bpref "lf.ring_of_integers"}[rings of integers] of $`L` and $`K`,
are discrete valuation domains, so they have unique maximal ideals $`P_L` and
$`P_K` which are principal.  If $`P_K=(\pi_K)`, the element $`\pi_K` is a
*uniformizer* for $`K`.

We have $`\pi_K\mathcal{O}_L=P_L^e` for some positive integer $`e`, which factors as $`e = p^w e_{\mathrm{tame}}` with $`e_{\mathrm{tame}}` coprime to $`p`.  The integer $`e`
is the *ramification index*, $`w` is the *wild ramification exponent* and $`e_{\mathrm{tame}}` is the *tame ramification index* of $`L/K`.

- If $`e=1` we say that the extension $`L/K` is *unramified*.

- If $`e=[L:K]` we say that $`L/K` is *totally ramified*.

- If $`p \nmid e` we say that $`L/K` is *tamely ramified*.

The *base ramification index* $`e_0` of $`L/K` is the ramification index of $`K/\Q_p`.
The *absolute ramification index* $`e_{\mathrm{abs}}` of $`L/K` is the ramification index of
$`L` over $`\Q_p`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.ring_of_integers"}[]
:::

:::definition "lf.ramification_polygon"
*Ramification polygon.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.ramification_polygon))

Let $`L/K` be a finite extension of {bpref "lf.padic_field"}[$`p`-adic fields]
and let $`K'/K` be the {bpref "lf.unramified_subfield"}[maximal unramified subextension] of $`L/K`.  Then $`L/K'` is totally ramified, and if
$`\alpha \in L` is a {bpref "lf.ramification_index"}[uniformizer] then
the minimal polynomial $`\varphi(x) \in K'[x]` of $`\alpha` over $`K'` will be {bpref "lf.eisenstein_polynomial"}[Eisenstein].  The
*ramification polygon* $`P` of $`L` is essentially the
{bpref "lf.newton_polygon"}[Newton polygon] of the
*ramification polynomial*

$$`\rho(x)=\alpha^{-n}\varphi(\alpha x + \alpha)\in L[x]`

of $`L/K`.  Write $`\rho(x)=x^n+\sum_{i=0}^{n-1}\rho_ix^i`.  Then the
ramification polygon of $`L/K` is the lower convex hull of the set of points
$`(-i,v_L(\rho_i))`, where we ignore all points with $`\rho_i=0`.  Thus the
ramification polygon is the reflection of the Newton polygon of $`\rho(x)`
through the vertical axis.  This is independent of the choice of uniformizer
$`\alpha` for $`L`.

If $`I/K` is a {bpref "lf.family_polynomial"}[family] of extensions then
the ramification polygon of $`I/K` is defined to be the ramification polygon
of any $`L/K\in I/K`.  The slopes of the segments of $`P` are the
{bpref "lf.rams"}[rams] of $`L/K` and $`I/K`.

Depends on: {uses "lf.eisenstein_polynomial"}[] {uses "lf.newton_polygon"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.rams"}[] {uses "lf.unramified_subfield"}[]
:::

:::definition "lf.rams"
*Rams.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.rams))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields]
with {bpref "lf.ramification_index"}[ramification index] $`e = \epsilon p^w`.
The *rams* $`r_1 \le \dots \le r_w` of $`L/K` are the same as the positive lower
ramification jumps of $`L/K`.  In the case where $`L/K` is a Galois extension the
lower jumps are defined in Chapter IV of Serre's <i>Local Fields</i>
.
For the general case where $`L/K` is separable but not necessarily
Galois see the appendix to Deligne .  When $`L/K` is Galois a
ram is any number of the form $`v_L(\sigma(\pi_L)-\pi_L)-1` for some
$`\sigma\not=1_L` in the {bpref "lf.wild_inertia_group"}[wild inertia group] of
$`\Gal(L/K)`.  Thus the rams of a Galois extension are positive integers, but in general a ram may have denominator dividing $`p^k-1` where $`k` is the multiplicity of the ram.

Two rescalings of the rams can be helpful in various contexts. The *small rams* $`r_k^*` and *tiny rams* $`r_k'` are defined by

$$`r_k^* = \frac{(p-1)r_k}{\epsilon p^k} \qquad\qquad\qquad r_k' = \frac{r_k}{\epsilon p^k}.`

With the convention that $`r_0=s_0=m_0=0`, the relationship with the {bpref "lf.means"}[means] $`\langle m_1, \dots, m_w\rangle` and {bpref "lf.slopes"}[Swan slopes] $`[s_1, \dots, s_w]` is then given by the equations

$$`r_k^* = m_k-m_{k-1} \qquad\qquad\qquad r'_k = s_k-m_k.`

Rams are helpful in enumerating the possible {bpref "lf.herbrand_invariant"}[Herbrand invariants] over $`K`.  Define first $`\mathcal{R}_k^\infty` to be the set of positive rational numbers with denominator dividing $`p^k-1` and numerator prime to $`p`.  Then set

$$`\mathcal{R}_k^{z} = \left\{\alpha \in \mathcal{R}_k^\infty : \alpha < \frac{pz}{p-1}\right\} \ \ \text{if}\ k>1\qquad\qquad\qquad \mathcal{R}_1^{z} = \left\{\alpha \in \mathcal{R}_1^\infty : \alpha \le \frac{pz}{p-1}\right\}.`

The possible rams $`r_1 = \dots = r_w` for totally wildly ramified extensions of degree $`p^w` over $`K` are then just given by $`\mathcal{R}_w^{e_K}`, where $`e_K` is the {bpref "lf.ramification_index"}[absolute ramification index] of $`K`.  In general, the possible rams $`(r_1,\dots,r_w)` over $`K` are chosen sequentially using the considerations above and the fact that if $`r_i < r_{i+1}` then $`L/K` has an intermediate field $`L_i` with $`[L_i:K] = \epsilon p^i`.  For example, to get all strictly increasing sequences, each $`r_k` is chosen from $`\mathcal{R}_1^{e_K \epsilon p^{k-1}}`.

Depends on: {uses "lf.means"}[] {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.slopes"}[] {uses "lf.wild_inertia_group"}[]
:::

:::definition "lf.residual_polynomials"
*Residual polynomials.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.residual_polynomials))

Let $`L/K` be a totally ramified extension of
{bpref "lf.padic_field"}[$`p`-adic fields], let $`\alpha` be a
{bpref "lf.ramification_index"}[uniformizer] of $`L` with minimal
polynomial $`\varphi` over $`K`
and denote by $`v_{\alpha}` the (exponential) valuation that is
normalized such that $`v_{\alpha}(\alpha)=1`. Let $`\underline{L}` be the
{bpref "lf.residue_field"}[residue field] of $`L`, and for
$`\delta \in \mathcal{O}_L` write $`\underline{\delta}` for the image of
$`\delta` in $`\underline{L}`.  Let

$$`\rho(x)=\sum_i
\rho_i x^i\in\mathcal{O}_L[x]`

be the {bpref "lf.ramification_polygon"}[ramification polynomial]
of $`L/K`.  Let $`S` be a segment of the
{bpref "lf.ramification_polygon"}[ramification polygon] of $`L/K`
with length $`l`, endpoints $`(-k-l,v_{\alpha}(\rho_{k+l}))`,
$`(-k,v_{\alpha}(\rho_k))`, and slope
$`h/m=\left(v_{\alpha}(\rho_k)-v_{\alpha}(\rho_{k+l})\right)/l`.  Then

$$`A(x)=\sum_{j=0}^{l/m}\underline{\rho_{jm+k}\alpha^{jh-v_{\alpha}(\rho_k)}}x^{j}\in\underline{L}[x]`

is called the *residual polynomial* associated to $`\rho` and $`S`.
If $`S` has positive slope then it follows from this construction that
$`x^kA(x^m)` is an additive polynomial.

Residual polynomials (originally called associated polynomials) were
introduced by Ore in 1928 .  The *residual polynomials* of $`\varphi` are the residual polynomials associated to the segments $`S_1, \dots, S_{\ell}` of the {bpref "lf.ramification_polygon"}[ramification polygon] of $`\varphi`.  Although the list of residual polynomials associated to $`\varphi` is not an invariant of $`L/K`, the definition can be modified to define an invariant.

For $`1\le i\le \ell`, let $`h_i/m_i` be the slope of $`S_i` and $`A_i(x)`
its residual polynomial.  Set

$$`\mathcal{A}= \left\{
\left(\gamma_{\delta,1}{A_1}(\underline\delta^{h_1} x),\dots,
\gamma_{\delta,\ell}{A_{\ell}}(\underline\delta^{h_{\ell}} x)\right) :
\underline\delta\in\underline{K}^\times \right\},`

where $`\gamma_{\delta,\ell}=\underline\delta^{-h_{\ell}\deg A_{\ell}},` and $`\gamma_{\delta,i}=\gamma_{\delta,i+1}\underline\delta^{-h_i\deg A_i}` for
$`1\le i\le \ell-1`.  Then $`\mathcal{A}` is an invariant of the extension
$`K[x]/(\varphi)`.  We say that $`\mathcal{A}` is the
*equivalence class of residual polynomials* associated to $`L/K`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.ramification_polygon"}[] {uses "lf.residue_field"}[]
:::

:::definition "lf.residue_field" (lean := "IsLocalRing.ResidueField")
*Residue field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.residue_field))

The *residue field* of a nonarchimedean local field is the quotient of its {bpref "lf.ring_of_integers"}[ring of integers] by its unique {bpref "lf.maximal_ideal"}[maximal ideal].

The residue field is finite and its characteristic $`p` is the *residue field characteristic*.  Finite extensions of $`\Q_p` have residue field characteristic $`p`.

Depends on: {uses "lf.maximal_ideal"}[] {uses "lf.ring_of_integers"}[]
:::

:::definition "lf.residue_field_degree" (lean := "TauCeti.inertiaDegree")
*Residue field degree of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.residue_field_degree))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
Let $`\kappa` be the {bpref "lf.residue_field"}[residue field] of $`K`
and let $`\lambda` be the residue field of $`L`.  The *residue field degree* $`f`
of $`L/K` is the degree of the field extension $`\lambda/\kappa`.

The *base residue field degree* $`f_0` of $`L/K` is the residue field degree of $`K/\Q_p`.  The *absolute residue field degree* $`f_{\mathrm{abs}}` of $`L/K` is the
residue field degree of $`L` over $`\Q_p`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.residue_field"}[]
:::

:::definition "lf.ring_of_integers" (lean := "Valuation.integer")
*Ring of integers of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.ring_of_integers))

The *ring of integers* of a {bpref "lf.local_field"}[local field] $`K` with {bpref "nf.absolute_value"}[absolute value] $`|\ |` is the subring
$`\mathcal O_K := \{x\in K:|x|\le 1\}`; it is a discrete valuation ring.

Depends on: {uses "lf.local_field"}[] {uses "nf.absolute_value"}[]
:::

:::definition "lf.root_number"
*Root number of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.root_number))

For a finite extension $`K/\mathbb{Q}_p`, we give the *local root number*, or local sign, $`\epsilon(K)  \in \{1,i,-1,-i\}`.

We start with a general description where we allow $`p=\infty`, writing
$`\Q_{\infty} = \R`.
Local root numbers, $`\epsilon(\rho) \in \C^\times`, are defined for representations
$`\rho : \mathrm{Gal}(\overline{\Q}_p/\Q_p)\rightarrow \GL_n(\C)`.  They
have absolute value $`1`,
are multiplicative in the sense that $`\epsilon(\rho_1 \oplus
\rho_2) = \epsilon(\rho_1)
\epsilon(\rho_2)`, and for $`p \neq \infty`,
any unramified representation has root number $`1`.
The root number for the trivial and sign characters of $`\mathrm{Gal}(\C/\R)` are
$`1` and $`-i` respectively.  Finally,
if $`\rho : \mathrm{Gal}(\overline{\Q}/\Q) \rightarrow \GL_n(\C)` is
a global representation whose restrictions to decomposition groups are
denoted by $`\rho_p`, the global root number
$`\epsilon(\rho)` equals the product of local root numbers
$`\prod \epsilon(\rho_p)`, and $`\epsilon(\rho)`
figures into the functional equation of the Artin $`L`-function $`L(\rho,s)`.

If $`K` is an $`n`-dimensional $`p`-adic algebra then
$`\mathrm{Gal}(\overline{\Q}_p/\Q_p)` acts on the set of its $`n`
embeddings into $`\overline{\Q}_p`.  One thus has a
representation $`\rho_K :   \mathrm{Gal}(\overline{\Q}_p/\Q_p) \rightarrow S_n \subset \GL_n(\C)`.  For a local field $`K`, we give the corresponding
root number   $`\epsilon(K) := \epsilon(\rho_K)`.  These particular root numbers
play a central role in Galois embedding problems.
Finally, we note that for a global number field $`K`, the global root number $`\epsilon(K) = \prod \epsilon(K_p)` is always $`1`.
:::

:::definition "lf.roots_of_unity" (lean := "CommGroup.torsion, Nat.card, TauCeti.exists_isPrimitiveRoot_natCard_residueField_sub_one, TauCeti.inertiaDegree")
*Roots of unity.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.roots_of_unity))

This is the order of the group of roots of unity of $`K`, written in
the form $`(p^f-1)\cdot p^r`, where $`f` is the
{bpref "lf.residue_field_degree"}[residue field degree] of $`K/\Q_p`.

Depends on: {uses "lf.residue_field_degree"}[]
:::

:::definition "lf.slope_content" (lean := "IsNonarchimedeanLocalField.artinSlopeContent, IsNonarchimedeanLocalField.wildArtinSlopes, IsNonarchimedeanLocalField.swanSlopes, IsNonarchimedeanLocalField.upperRamificationGroup_eq_of_mem_Ioc")
*Slope content of an extension of $`p`-adic fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.slope_content))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
Let $`G` be the {bpref "nf.galois_group"}[Galois group] of the
{bpref "nf.galois_closure"}[Galois closure]
$`L^{gal}/K` of $`L/K`.  Then $`G` has a filtration by {bpref "lf.galois_invariants"}[higher ramification groups], which in turn are connected to the discriminants of subfields of $`L^{gal}`.  The \*slope content\* encodes information about this filtration giving the location and sizes of the jumps.

Let $`G^i` be the $`i`th higher ramification group in upper numbering from Serre's <i>Local Fields</i> , Chapter IV.  They form a descending filtration of normal subgroups where $`i` is a continuous parameter, $`i\geq -1`.  Let $`G^{(j)} = G^{j-1}`, and $`G^{(j+)} = \cup_{\epsilon>0} G^{(j+\epsilon)}`.  Then

- $`G^{(0)}=G`.

- $`G^{(1)}` is the {bpref "lf.inertia_group"}[inertia subgroup] of $`G`, i.e., the kernel of the natural map from $`G` to the Galois group of the {bpref "lf.residue_field"}[residue field].

- the fixed field of $`G^{(1)}` is the maximum {bpref "lf.unramified_subfield"}[unramified subfield] of $`L^{gal}/K`, which we denote by $`L^{un}`.  The degree $`[L^{un}:K]` is the {bpref "lf.unramified_degree"}[unramified degree] for $`L^{gal}/K`.  The extension $`L^{gal}/L^{un}` is totally ramified.

- the group $`G^{(1)}/G^{(1+)}` is cyclic of order prime to $`p`.  Its order is the {bpref "lf.tame_degree"}[tame degree] for $`L^{gal}/K` as it is the degree of the largest tamely totally ramified subextension.

- The group $`G^{(1+)}` is a $`p`-group.  Values of $`s>1` giving jumps in the filtration $`G^{(s)}\neq G^{(s+)}` are *wild Artin slopes*.  We repeat a slope $`m` times if $`p^m =[G^{(s)} : G^{(s+)}]`, and then list the wild slopes in non-decreasing order.

The *Artin slope content* then takes the form $`[s_1,\ldots, s_k]_t^u` where $`t` is the tame degree, $`u` is the degree of the maximum unramified subfield, and the $`s_i` give the list of the wild slopes.  In particular, $`[L^{gal}:K]=tup^k`.  If $`t` or $`u` is equal to $`1`, it is not printed.

The *Swan slopes* are obtained from the Artin slopes by subtracting 1.

Depends on: {uses "lf.galois_invariants"}[] {uses "lf.inertia_group"}[] {uses "lf.padic_field"}[] {uses "lf.residue_field"}[] {uses "lf.tame_degree"}[] {uses "lf.unramified_degree"}[] {uses "lf.unramified_subfield"}[] {uses "nf.galois_closure"}[] {uses "nf.galois_group"}[]
:::

:::definition "lf.slopes"
*Slopes.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.slopes))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
For each subextension $`E/K` of $`L/K` we plot the point $`(n_E,c_E)`,
where $`n_E=[E:K]` and $`c_E` is the
{bpref "lf.discriminant_exponent"}[discriminant exponent] of $`E/K`.
Let $`B` be the boundary of the lower convex hull of these points.  The slopes
of the segments of $`B` are called the *Artin slopes* of
$`L/K`, and those which are greater than 1 are the *wild Artin slopes*.  If a segment corresponding to a wild slope runs from $`(n_1, c_1)` to $`(n_2, c_2)` then $`n_2/n_1=p^m`
for some $`m\in\N`, and the corresponding Artin slope is repeated $`m`
times.  The *Swan slopes* of $`L/K` are obtained by subtracting $`1` from each Artin slope, and the *wild Swan slopes* are precisely the positive ones.  The Artin slopes and Swan
slopes of $`L/K` are also referred to as the *visible Artin slopes* and the
*visible Swan slopes*.  This is to distinguish them from the
{bpref "lf.hidden_slopes"}[hidden slopes] of $`L/K`.

Let $`f` be the {bpref "lf.residue_field_degree"}[residue field degree], let $`\epsilon` be the {bpref "lf.tame_degree"}[tame degree] of $`L/K`, and let $`a_1\le a_2\le\dots\le a_w` be the wild Artin slopes of $`L/K`.
The *Artin slope content* of $`L/K` is the collection of data
$`[a_1,\dots,a_w]_{\epsilon}^f`.  The *Swan slope content* of $`L/K` is $`[s_1,\dots,s_w]_{\epsilon}^f`, where $`s_1,\dots,s_w` are the wild Swan slopes of
$`L/K`.

The Swan slopes are the same as the positive upper ramification jumps of
$`L/K`.  In the case where $`L/K` is a Galois extension these are defined for
instance in Chapter IV of Serre's <i>Local Fields</i>
.  For the general case where
$`L/K` is separable but not necessarily Galois see the appendix to Deligne
.

Depends on: {uses "lf.discriminant_exponent"}[] {uses "lf.padic_field"}[] {uses "lf.residue_field_degree"}[] {uses "lf.tame_degree"}[]
:::

:::definition "lf.subfamily"
*Subfamily of a family of $`p`-adic fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.subfamily))

Let $`I/K` be a {bpref "lf.family_polynomial"}[family] of
extensions of {bpref "lf.padic_field"}[$`p`-adic fields]
and let $`\mathcal{A}` be an equivalence class of
{bpref "lf.residual_polynomials"}[residual polynomials].
The *subfamily* of $`I/K` corresponding to $`\mathcal{A}` consists
of all $`L/K\in I/K` whose list of residual polynomials is in $`\mathcal{A}`.

Depends on: {uses "lf.family_polynomial"}[] {uses "lf.padic_field"}[] {uses "lf.residual_polynomials"}[]
:::

:::definition "lf.swan_slopes"
*Swan slopes.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.swan_slopes))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
The *Swan slopes* of $`L/K` are the same as the nonnegative upper ramification
breaks of $`L/K`.  In the case where $`L/K` is a Galois extension the upper breaks
are defined in Chapter IV of Serre's <i>Local Fields</i>
.
For the general case where $`L/K` is separable but not necessarily
Galois see the appendix to Deligne .  The Swan
slopes can be obtained by subtracting 1 from each of the positive {bpref "lf.galois_invariants"}[Artin
slopes] of $`L/K`.

Depends on: {uses "lf.galois_invariants"}[] {uses "lf.padic_field"}[]
:::

:::definition "lf.tame_degree" (lean := "IsNonarchimedeanLocalField.tameDegree, IsNonarchimedeanLocalField.galoisTameDegree, IsNonarchimedeanLocalField.ordProj_mul_tameDegree, IsNonarchimedeanLocalField.not_dvd_tameDegree, Algebra.galoisClosure")
*Tame degree of a local field extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.tame_degree))

Let $`K` be a {bpref "lf.padic_field"}[$`p`-adic field] and let
$`L/K` be a finite extension.  Let $`L^{un}/K` be the
{bpref "lf.unramified_subfield"}[maximal unramified subextension]
of $`L/K`.  Then the *tame degree* of $`L/K` is the integer $`t` such
that $`[L:L^{un}]=p^m t` with $`p\nmid t`.

The *Galois tame degree* of $`L/K` is the tame degree of $`L^{gal}/K`,
where $`L^{gal}/K` is the {bpref "nf.galois_closure"}[Galois closure]
of $`L/K`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.unramified_subfield"}[] {uses "nf.galois_closure"}[]
:::

:::definition "lf.top_slope" (lean := "IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois, IsNonarchimedeanLocalField.topArtinSlope, IsNonarchimedeanLocalField.upperRamificationGroup_eq_bot_iff, IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois_of_subsingleton, TauCeti.LocalFieldsRamification.upperRamificationGroup")
*Top Artin slope for an extension of local fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.top_slope))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields]
with {bpref "lf.slopes"}[Artin slope content] $`[s_1, \ldots, s_k]_t^u`.
The *top Artin slope* of $`L/K` is the largest $`s` such that the ramification
group $`G^{(s)}` is nontrivial.  Hence

- if $`k>0`, then the top slope is $`s_k`, which is always greater than $`1`

- otherwise, if $`t>1`, then the top slope is $`1`

- otherwise the top slope is $`0`

This includes the convention that the top slope of the trivial extension $`K/K`
is $`0`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.slopes"}[]
:::

:::definition "lf.unramified_degree" (lean := "TauCeti.inertiaDegree, TauCeti.finrank_unramifiedExtension_inertiaDegree, TauCeti.unramifiedExtension, IsNonarchimedeanLocalField.galoisUnramifiedDegree, TauCeti.eq_unramifiedExtension_inertiaDegree_iff")
*Unramified degree of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.unramified_degree))

Let $`L/K` be a finite extension of {bpref "lf.padic_field"}[$`p`-adic fields],
and let $`L^{un}/K` its
{bpref "lf.unramified_subfield"}[maximal unramified subextension].
The *unramified degree* of $`L/K` is the degree $`[L^{un}:K]`, which is equal to the {bpref "lf.residue_field_degree"}[residue field degree] of $`L/K`.

Since $`K` has a unique {bpref "lf.ramification_index"}[unramified] extension of degree $`n` for each positive integer $`n`, the unramified degree of an extension determines its {bpref "lf.unramified_subfield"}[unramified subfield].

The *Galois unramified degree* of $`L/K` is the unramified degree of its
{bpref "nf.galois_closure"}[Galois closure] $`L^{gal}/K`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[] {uses "lf.residue_field_degree"}[] {uses "lf.unramified_subfield"}[] {uses "nf.galois_closure"}[]
:::

:::definition "lf.unramified_subfield" (lean := "TauCeti.inertiaDegree, TauCeti.maximalUnramifiedExtension, TauCeti.unramifiedExtension")
*Unramified subfield.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.unramified_subfield))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
Then there is a unique intermediate field $`L^{ur}`  such that $`L^{ur}/K` is
{bpref "lf.ramification_index"}[unramified] and $`L/L^{ur}` is
{bpref "lf.ramification_index"}[totally ramified].  We say that
$`L^{ur}/K` is the *maximal unramified subextension* of $`L/K`.

If $`L` is a finite extension of $`\Q_p` we say that $`L^{ur}` is the
*unramified subfield* of $`L`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[]
:::

:::definition "lf.unramified_totally_ramified_tower" (lean := "TauCeti.IsTotallyRamified, TauCeti.unramifiedExtension")
*The canonical tower of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.unramified_totally_ramified_tower))

Let $`L/K` be an extension of {bpref "lf.padic_field"}[$`p`-adic fields].
Then there is a unique intermediate field $`L^{ur}`  such that $`L^{ur}/K` is
{bpref "lf.ramification_index"}[unramified] and $`L/L^{ur}` is
{bpref "lf.ramification_index"}[totally ramified].  We say that
$`L\supset L^{ur}\supset K` is the *canonical tower* associated to $`L/K`.

Depends on: {uses "lf.padic_field"}[] {uses "lf.ramification_index"}[]
:::

:::definition "lf.visible_slopes"
*Visible slopes.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.visible_slopes))

Let $`K` be a finite extension of $`\Q_p`.  If we plot points $`(n_E,c_E)` for each intermediate field $`\Q_p\subseteq E \subseteq K`, including $`K` and $`\Q_p`, where $`n_E=[E:\Q_p]` and $`c_E` its {bpref "lf.discriminant_exponent"}[discriminant] exponent. Take the lower convex hull of these points.

The *visible Artin slopes* of $`K` correspond to segments which have slopes greater than one.  For such a segment from $`(n_1, c_1)` to $`(n_2, c_2)`, $`n_2/n_1=p^k` for some $`k\in\Z^+`, and that slope is listed $`k` times.  If $`[s_1,\ldots,s_k]` are the visible Artin slopes, then the *visible Swan slopes* are $`[s_1-1,\ldots,s_k-1]`.

For a {bpref "nf.is_galois"}[Galois] extension $`K/\Q_p`, the visible Artin slopes are the same as the {bpref "lf.wild_slopes"}[wild Artin slopes] of the extension.  For a general extension, the list of visible Artin slopes is a subset of the list of wild Artin slopes of its Galois closure.  The {bpref "lf.hidden_slopes"}[hidden slopes] of $`K` are obtained by removing (as multisets) the visible slopes of $`K` from the set of all slopes of the Galois closure.

Depends on: {uses "lf.discriminant_exponent"}[] {uses "lf.hidden_slopes"}[] {uses "lf.wild_slopes"}[] {uses "nf.is_galois"}[]
:::

:::definition "lf.wild_inertia_group" (lean := "TauCeti.LocalFieldsRamification.lowerRamificationGroup, TauCeti.ramificationGroupOneSylow, TauCeti.wildInertiaSubgroup")
*Wild inertia group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.wild_inertia_group))

The *wild inertia group* of a {bpref "nf.is_galois"}[Galois] extension $`K/\Q_p` is the unique {bpref "group.sylow_subgroup"}[$`p`-Sylow subgroup] of its {bpref "lf.inertia_group"}[inertia group].

Depends on: {uses "group.sylow_subgroup"}[] {uses "lf.inertia_group"}[] {uses "nf.is_galois"}[]
:::

:::definition "lf.wild_inertia_group_search" (lean := "TauCeti.LocalFieldsRamification.lowerRamificationGroup, TauCeti.ramificationGroupOneSylow, TauCeti.wildInertiaSubgroup")
*Wild inertia group search.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.wild_inertia_group_search))

{bpref "lf.wild_inertia_group"}[]

When searching by wild inertia groups, it can be specified as an abstract group by a {bpref "group.small_group_label"}[GAP id], a group name from {bpref "gg.label"}[transitive group label], or a list of group labels.

Depends on: {uses "gg.label"}[] {uses "group.small_group_label"}[] {uses "lf.wild_inertia_group"}[]
:::

:::definition "lf.wild_segments"
*Number of wild segments of a family.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.wild_segments))

Let $`I/K` be a {bpref "lf.family_polynomial"}[family]
of extensions and let $`L/K\in I/K`.
The *number of wild segments* of $`I/K` is the number of segments
of the {bpref "lf.ramification_polygon"}[ramification polygon] of $`L/K`
with positive slope.  This is equal to the number of distinct positive
{bpref "lf.slopes"}[Swan slopes] of $`L/K`, and does not
depend on the choice of $`L/K\in I/K`.

Depends on: {uses "lf.family_polynomial"}[] {uses "lf.ramification_polygon"}[] {uses "lf.slopes"}[]
:::

:::definition "lf.wild_slopes" (lean := "IsNonarchimedeanLocalField.wildArtinSlopesOfIsGalois, IsNonarchimedeanLocalField.upperRamificationGroup_eq_of_mem_Ioc")
*Wild Artin slopes of a local field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lf.wild_slopes))

Let $`K` be a finite {bpref "nf.is_galois"}[Galois] extension of $`\Q_p` for some prime $`p`.  The *wild Artin slopes* indicate the locations and sizes of jumps in the filtration of the {bpref "nf.galois_group"}[Galois group] by higher ramification groups.  See {bpref "lf.galois_invariants"}[Galois invariants] of a local number field for more information.

Depends on: {uses "lf.galois_invariants"}[] {uses "nf.galois_group"}[] {uses "nf.is_galois"}[]
:::
