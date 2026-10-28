import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Modular curves" =>

This chapter lists the LMFDB definitions relating to *modular curves*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "modcurve.agreeable"
*Agreeable.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.agreeable))

An {bpref "gl2.open"}[open subgroup] $`H\le \GL_2(\widehat{\Z})` (and the corresponding {bpref "modcurve"}[modular curve] $`X_H`) is *agreeable* (as defined by Zywina in Section 1.4 of ) if the following hold:

- $`\det(H)=\widehat{\Z}^\times`;

- $`H` contains the subgroup of $`\GL_2(\widehat{\Z})` formed by scalar matrices;

- the {bpref "modcurve.level"}[level] of $`H\le \GL_2(\widehat{\Z})` and the level of $`H\cap \SL_2(\widehat{\Z})\le \SL_2(\widehat{\Z})` have the same odd prime divisors.

The *agreeable closure* $`\widetilde H` of $`H` is the intersection of all the agreeable open subgroups of $`\GL_2(\widehat{\Z})` that contain $`H`.

The agreeable closure $`\widetilde H` contains $`H` as a {bpref "group.subgroup.normal"}[normal subgroup] and has the same {bpref "group.commutator_subgroup"}[commutator subgroup] as $`H`; see Proposition 8.1 of .  It follows that the quotient $`\widetilde{H}/H` (called the *agreeable quotient*) is finite abelian.

Depends on: {uses "gl2.open"}[] {uses "group.commutator_subgroup"}[] {uses "group.subgroup.normal"}[] {uses "modcurve"}[] {uses "modcurve.level"}[]
:::

:::definition "modcurve.canonical_field"
*Canonical field of definition of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.canonical_field))

Let $`X_H` be the {bpref "modcurve"}[modular curve] over $`\mathbb{Q}` associated to an open subgroup $`H \le \operatorname{GL}_2(\widehat{\mathbb{Z}})`.  Let $`\pi_0((X_H)_{\overline{\Q}})` be the set of {bpref "ag.geom_component"}[geometric components].  Since $`X_H` is integral, the action of $`\Gal_{\Q}` on $`\pi_0((X_H)_{\overline{\Q}})` is transitive.  Let $`C` be one of the geometric components.  The *canonical field of definition* of $`C` is the subfield $`K` of $`\overline{\mathbb{Q}}` fixed by the stabilizer $`\operatorname{Stab}_{\Gal_{\Q}}(C)`.

Let $`N` be the {bpref "modcurve.level"}[level] of $`H`, which is the smallest $`N \ge 1` such that $`H` is the inverse image of a subgroup $`H_N \le \operatorname{GL}_2(\mathbb{Z}/N\mathbb{Z})`.  Then $`K` is a number field contained in $`\mathbb{Q}(\zeta_N)`.

Since $`K` is abelian, it is independent of the choice of $`C`, and every geometric component of $`X_H` has a canonical model over $`K`.

Equivalently, $`K` can be defined as the ring of global regular functions of the $`\mathbb{Q}`-scheme $`X_H`.

Also, $`K` is the subfield of $`\mathbb{Q}^{\textup{ab}}` fixed by $`\det(H) \le \widehat{\mathbb{Z}}^\times`, or equivalently the subfield of $`\mathbb{Q}(\zeta_N)` fixed by $`\det(H_N) \subset (\mathbb{Z}/N\mathbb{Z})^\times`.

It can happen that a geometric component of $`X_H` is definable over a field smaller than its canonical field of definition.  For example, the canonical field of definition of a geometric component of the {bpref "modcurve.xn"}[full modular curve] $`X_{\text{full}}(N)_{\mathbb{Q}}` is $`\mathbb{Q}(\zeta_N)`, but any such geometric component is the base extension of the curve $`X_{\mathrm{arith}}(N)` over $`\mathbb{Q}`.

Depends on: {uses "ag.geom_component"}[] {uses "modcurve"}[] {uses "modcurve.level"}[] {uses "modcurve.xn"}[]
:::

:::definition "modcurve.cm_discriminants"
*CM points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.cm_discriminants))

Rational points on a {bpref "modcurve"}[modular curve] $`X_H` that correspond to elliptic curves with {bpref "ec.complex_multiplication"}[complex multiplication] are called *CM points*.

Over $`\Q` these correspond to rational points in the fiber of the map $`j\colon X_H\to X(1)` above one of the $`13` $`j`-invariants of CM elliptic curves over $`\Q` corresponding to one of the *CM discriminants*

$$`\begin{itemize}
\item 3,-4,-7,-8,-11,-12,-16,-19,-27, -27, -43,-67,-163,
\end{itemize}`
 of {bpref "nf.order"}[imaginary quadratic orders] of {bpref "nf.class_number"}[class number] one.  These $`13` orders lie in $`9` distinct imaginary quadratic fields.

Depends on: {uses "ec.complex_multiplication"}[] {uses "modcurve"}[] {uses "nf.class_number"}[] {uses "nf.order"}[]
:::

:::definition "modcurve.cusp_orbits"
*Cusp orbits.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.cusp_orbits))

For an {bpref "gl2.open"}[open subgroup] $`H` of $`\GL_2(\widehat{\Z})` with $`\det(H) =\widehat{\Z}^\times`, the *cusps* of $`H` are the double cosets $`\pm H  \backslash \GL_2(\widehat{\Z}) /\langle\delta\rangle`, where $`\delta := \begin{bmatrix}1&1\\0&1\end{bmatrix}`.  These correspond to the {bpref "modcurve.cusps"}[cusps]  of the {bpref "modcurve"}[modular curve] $`X_H`.

Each $`\sigma \in \Gal_{\Q}` acts on the cusps of $`H` via $`Hg\langle \pm \delta\rangle\mapsto Hg\chi(\sigma)\langle \pm \delta\rangle`, where $`\chi(\sigma)=\begin{bmatrix}e&0\\0&1\end{bmatrix} \in \GL_2(\widehat{\Z})` is such that for all positive integers $`N` one has $`\sigma(\zeta_N)=\zeta_N^e`.

The Galois orbit of a cusp of $`H` is its orbit under the action of $`\Gal_{\Q}`.

The sizes of the Galois orbits of the cusps of $`H` form a multiset of integers that may be expressed in exponential notation, for example $`2^2\cdot 4^3` indicates that there are five *cusp orbits*, 2 of size 2 and 3 of size 4, and a total of 16 cusps.

Depends on: {uses "gl2.open"}[] {uses "modcurve"}[] {uses "modcurve.cusps"}[]
:::

:::definition "modcurve.cusp_widths"
*Cusp widths.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.cusp_widths))

For an open subgroup $`H` of $`\GL_2(\widehat{\Z})` with $`\det(H) =\widehat{\Z}^\times`, the *cusps* of $`H` are the double cosets $`\pm H  \backslash \GL_2(\widehat{\Z}) /\langle \delta\rangle`, where $`\delta := \begin{bmatrix}1&1\\0&1\end{bmatrix}`.  These correspond to the {bpref "modcurve.cusps"}[cusps]  of the modular curve $`X_H`.

The *width* of a cusp $`c \in \pm H  \backslash \GL_2(\widehat{\Z}) /\langle \delta\rangle` is the number of right cosets it contains, or equivalently the smallest integer $`h` such that $`c\delta^h = c`. The sum of the cusp widths is equal to the {bpref "modcurve.psl2index"}[$`\PSL_2`-index] of $`H`.

Depends on: {uses "modcurve.cusps"}[] {uses "modcurve.psl2index"}[]
:::

:::definition "modcurve.decomposition"
*Isogeny decomposition of the Jacobian of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.decomposition))

As with any {bpref "ag.abelian_variety"}[abelian variety], the {bpref "ag.jacobian"}[Jacobian] $`J_H` of a {bpref "modcurve"}[modular curve] $`X_H` can be {bpref "av.decomposition"}[decomposed] into {bpref "av.simple"}[simple] {bpref "av.isogeny"}[isogeny factors].  For modular curves, these simple isogeny factors are modular abelian varieties corresponding to {bpref "cmf.galois_orbit"}[Galois orbits] of {bpref "cmf.weight"}[weight] 2 {bpref "cmf.newform"}[newforms].

We list two types of information about the *isogeny decomposition* of $`J_H`:

- the multiset of dimensions of the simple isogeny factors: $`1^3\cdot 2^2` denotes $`3` factors of {bpref "ag.dimension"}[dimension] $`1` and $`2` factors of dimension $`2`;

- the multiset of newforms corresponding to the modular abelian varieties in the isogeny decomposition, listed by {bpref "cmf.label"}[label]: $`\texttt{11.2.a.a}^3\cdot \texttt{13.2.e.a}^2` denotes five simple isogeny factors, three isogenous to the modular abelian variety corresponding to the newform labelled $`\texttt{11.2.a.a}` and two isogenous to the modular abelian variety corresponding to the newform labelled $`\texttt{13.2.3.a}`.

When $`X_H` has {bpref "modcurve.genus"}[genus] zero, $`J_H` is the trivial abelian variety of dimension zero, and no isogeny decomposition information is listed.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "ag.jacobian"}[] {uses "av.decomposition"}[] {uses "av.isogeny"}[] {uses "av.simple"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.label"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[] {uses "modcurve"}[] {uses "modcurve.genus"}[]
:::

:::definition "modcurve.elliptic_points"
*Elliptic points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.elliptic_points))

An *elliptic point* on the {bpref "modcurve"}[modular curve] $`X_H` is a point whose stabilizer under the action of the {bpref "cmf.congruence_subgroup"}[congruence subgroup] $`\Gamma_H` is finite and nontrivial.

Depends on: {uses "cmf.congruence_subgroup"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.embedded_model"
*Embedded model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.embedded_model))

For hyperelliptic curves and curves of genus less than 2, the {bpref "ag.canonical_model"}[canonical map] is not an embedding.  For {bpref "modcurve"}[modular curves] $`X_G` of this form, we take the lowest even weight $`k` so that Riemann-Roch guarantees an embedding into the projectivization of the space of modular forms associated to $`G`.  We refer to the image of this embedding as the *embedded model* of $`X_G`.

Depends on: {uses "ag.canonical_model"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.entanglement_index"
*Entanglement index.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.entanglement_index))

The *entanglement index* of an {bpref "gl2.open"}[open subgroup] $`H\le \GL_2(\widehat{\Z})\simeq\prod_{\ell}\GL_2(\Z_{\ell})` is its index in the {bpref "group.direct_product"}[direct product] of its projections to $`\GL_2(\Z_{\ell})`.

When $`H` is a {bpref "group.subgroup.normal"}[normal] subgoup of the direct product $`G` of its projections to $`\GL_2(\Z_{\ell})`, the *entanglement quotient* of $`H` is the quotient $`G/H` (as an abstract group).

For an elliptic curve $`E/\Q` with {bpref "ec.galois_rep_adelic_image"}[adelic Galois image] $`H`, the entanglement index measures the extent to which its $`\ell`-power torsion fields intersect.

Depends on: {uses "ec.galois_rep_adelic_image"}[] {uses "gl2.open"}[] {uses "group.direct_product"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "modcurve.fiber_product"
*Fiber product.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.fiber_product))

If $`H` and $`H'` are open subgroups of $`\GL_2(\widehat{\Z})`, the *fiber product* $`X_H\times X_H'` of the {bpref "modcurve"}[modular curves] $`X_H` and $`X_H'` is their fiber product as [algebraic stacks](https://stacks.math.columbia.edu/tag/003O) over $`X(1)`.

Concretely, in the case that $`H` and $`H'` have coprime {bpref "gl2.level"}[levels] $`N` and $`N'`, this means that $`X_H\times X_H' = X_{H\cap H'}`, a modular curve of level $`NN'`.

Depends on: {uses "gl2.level"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.gassmann_class"
*Gassmann class.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.gassmann_class))

For an {bpref "gl2.open"}[open subgroup] $`H \leq \GL_2(\widehat{\Z})`, the *Gassmann class* of $`H` is the set of open subgroups of $`\GL_2(\widehat{\Z})` that are {bpref "group.gassmann_equivalence"}[Gassmann equivalent] to $`H`.

Let $`H,H' \leq \GL_2(\widehat{\Z})` be in the same Gassmann class.  Then $`H,H'` have the same {bpref "modcurve.level"}[level], {bpref "modcurve.index"}[index] and {bpref "modcurve.genus"}[genus].  Moreover, the {bpref "ag.jacobian"}[Jacobians] of $`X_H` and $`X_{H'}` are {bpref "av.isogeny"}[isogenous] (see Corollary 4 of Prasad-Rajan , applied to the covering curve $`X_{\mathrm{full}}(N)`), hence $`L(X_H,s)=L(X_{H'},s)`.

Depends on: {uses "ag.jacobian"}[] {uses "av.isogeny"}[] {uses "gl2.open"}[] {uses "group.gassmann_equivalence"}[] {uses "modcurve.genus"}[] {uses "modcurve.index"}[] {uses "modcurve.level"}[]
:::

:::definition "modcurve.genus"
*Genus of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.genus))

By the *genus* of a {bpref "modcurve"}[modular curve] $`X_H`, we mean the genus of any of its {bpref "ag.geom_component"}[geometric components].   This equals the {bpref "gl2.genus"}[genus] of the {bpref "gl2.open"}[open subgroup] $`H\leq \GL_2(\widehat{\Z})`.

Depends on: {uses "ag.geom_component"}[] {uses "gl2.genus"}[] {uses "gl2.open"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.genus_minus_rank"
*Genus-rank difference.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.genus_minus_rank))

The *genus-rank difference* of a {bpref "modcurve"}[modular curve] $`X_H` of positive genus is the integer obtained by subtracting the {bpref "modcurve.rank"}[analytic rank] of $`X_H` from its {bpref "modcurve.genus"}[genus].

This difference is of interest because the methods available to compute the set of rational points on $`X_H` depend critically on whether the {bpref "ag.mordell_weil"}[Mordell-Weil rank] of its {bpref "ag.jacobian"}[Jacobian] is less than, equal to, or greater than its genus (one expects the Mordell-Weil rank to equal the analytic rank of $`X_H` and the later is much more feasible to compute).

Depends on: {uses "ag.jacobian"}[] {uses "ag.mordell_weil"}[] {uses "modcurve"}[] {uses "modcurve.genus"}[] {uses "modcurve.rank"}[]
:::

:::definition "modcurve.gonality"
*$`K`-gonality of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.gonality))

The *$`K`-gonality* $`\gamma` of a {bpref "modcurve"}[modular curve] $`X_H` is the {bpref "ag.gonality"}[gonality] of any of its {bpref "ag.geom_component"}[geometric components] over its {bpref "modcurve.canonical_field"}[canonical field of definition] $`K`.  (The geometric gonality of that component might be smaller than the $`K`-gonality.)

Depends on: {uses "ag.geom_component"}[] {uses "ag.gonality"}[] {uses "modcurve"}[] {uses "modcurve.canonical_field"}[]
:::

:::definition "modcurve.index" (lean := "Subgroup.index")
*Index of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.index))

The *index* of a {bpref "modcurve"}[modular curve] $`X_H` is the {bpref "gl2.index"}[index] of the {bpref "gl2.open"}[open subgroup] $`H\leq \GL_2(\widehat{\Z})`.  The degree of the canonical morphism $`j \colon X_H\to X(1)\simeq \mathbb{P}^1` equals the index when $`-1 \in H`, and equals half the index if $`-1 \notin H`.

Depends on: {uses "gl2.index"}[] {uses "gl2.open"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.j_invariant_map"
*$`j`-invariant map.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.j_invariant_map))

The *$`\boldsymbol{j}`-invariant map* map or *$`\boldsymbol{j}`-map* of a {bpref "modcurve"}[modular curve] $`X_H` is the morphism $`X_H\to X(1)` induced by the inclusion $`H\le \GL_2(\widehat{\Z})`.

When $`X_H` is isomorphic to $`\mathbb{P}^1` this map is specified as an element of $`\mathbb{\Q}(t)`, and when $`X_H` is specified by a {bpref "ag.plane_model"}[plane model] $`f(x,y,z)=0`, it is an element of $`\mathbb{\Q}(x,z)`.

Depends on: {uses "ag.plane_model"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.label"
*Label of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.label))

The *label* of a {bpref "modcurve"}[modular curve] $`X_H` is the same as the {bpref "gl2.label"}[label] of the {bpref "gl2.open"}[open subgroup] $`H\le \GL_2(\widehat{\Z})`. When $`\det(H)=\widehat{\Z}^\times` and $`-I\in H` this label has the form $`\texttt{N.i.g.c.n}`, where

- $`N` is the {bpref "gl2.level"}[level] of $`H`

- $`i` is the {bpref "gl2.index"}[index] of $`H`

- $`g` is the {bpref "gl2.genus"}[genus] of $`H`

- $`c` is a base-26 ordinal that uniquely identifies the {bpref "modcurve.gassmann_class"}[Gassmann class] of $`H` among groups of the same level, index, and genus.

- $`n` is a positive integer that distinguishes nonconjugate subgroups of the same level, index, genus, and Gassmann class.

When $`\det(H)=\widehat{\Z}^\times` and $`-I\not \in H` this label has the form $`\texttt{N.i.g-M.c.m.n}`, where $`N`, $`i`, and $`g` are as above, and

- $`N` is the level of $`H`

- $`i` is the index of $`H`

- $`g` is the genus of $`H`

- $`M` is the level of $`H':=\langle H, -I\rangle`

- $`c` is the base-26 ordinal that identifies the Gassmann class of $`H'`

- $`m` is the positive integer in the label $`\texttt{M.j.g.c.m}` of $`H'`, where $`i=2j`.

- $`n` is a positive integer that distinguishes $`H` from nonconjugate refinements of $`H'` of the same level.

Depends on: {uses "gl2.genus"}[] {uses "gl2.index"}[] {uses "gl2.label"}[] {uses "gl2.level"}[] {uses "gl2.open"}[] {uses "modcurve"}[] {uses "modcurve.gassmann_class"}[]
:::

:::definition "modcurve.level" (lean := "Matrix.GeneralLinearGroup.adelicLevel, Matrix.GeneralLinearGroup.adelicReduction, Matrix.GeneralLinearGroup.adelicLevel_pos, Matrix.GeneralLinearGroup.inf_comap_map_adelicReduction_adelicLevel")
*Level of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.level))

The *level* of a {bpref "modcurve"}[modular curve] $`X_H` is the {bpref "gl2.level"}[level] of the {bpref "gl2.open"}[open subgroup] $`H\leq \GL_2(\widehat{\Z})`.

Depends on: {uses "gl2.level"}[] {uses "gl2.open"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.local_obstruction"
*Local obstruction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.local_obstruction))

A {bpref "modcurve"}[modular curve] $`X/\Q` has a *local obstruction* (to rational points) if it has no real points, or if it has no $`\Q_p`-points for some prime $`p`.

When $`X` has {bpref "modcurve.genus"}[genus] $`0` the absence of local obstructions guarantees the existence of rational points, but this is not true in general.

Depends on: {uses "modcurve"}[] {uses "modcurve.genus"}[]
:::

:::definition "modcurve.minimal_twist"
*Minimal Twists of modular curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.minimal_twist))

{bpref "gl2.open"}[Open subgroups] $`H_1,H_2\le \GL_2(\widehat{\Z})` for which $`H_1\cap \SL_2(\widehat{\Z}) = H_2\cap SL_2(\widehat{\Z})` are said to be *twists*. The corresponding {bpref "modcurve"}[modular curves] $`X_{H_1}` and $`X_{H_2}` become isomorphic after {bpref "ag.base_change"}[base change] to any cyclotomic field $`\Q(\zeta_n)` where $`n` is divisible by the {bpref "modcurve.level"}[level] of both $`H_1` and $`H_2`.

The *minimal twist* of a modular curve $`X_H` with $`\det(H)=\widehat{\Z}^\times` is the modular curve whose {bpref "modcurve.label"}[label] is minimal among all twists with $`\det(H)=\widehat{\Z}^\times` (in particular, it has minimal level).

Depends on: {uses "ag.base_change"}[] {uses "gl2.open"}[] {uses "modcurve"}[] {uses "modcurve.label"}[] {uses "modcurve.level"}[]
:::

:::definition "modcurve.modular_cover"
*Modular cover.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.modular_cover))

Each inclusion of {bpref "gl2.open"}[open subgroups] $`H\leq G` of $`\GL_2(\widehat{\Z})` induces a morphism of {bpref "modcurve"}[modular curves] $`X_H\to X_G`: every {bpref "ec"}[elliptic curve] with {bpref "modcurve.level_structure"}[level $`H` structure] gives rise to an elliptic curve with level $`G` structure.  We call such a morphism of modular curves a *modular cover*.

The *degree* of the morphism $`X_H\to X_G` is equal to the ratio of the {bpref "modcurve.psl2index"}[$`\PSL_2`-index] of $`H` by that of $`G`.  Note that when $`-1` is in $`G` but not $`H`, we might have $`H < G` strictly contained but the map $`X_H \to X_G` may have degree $`1` (hence be an isomorphism).

A modular cover is *minimal* if $`H < G` is a maximal (proper) subgroup.

The morphism $`X_H\to X_G` induces a surjective homomorphism $`\phi \colon \operatorname{Jac}(X_H)\to\operatorname{Jac}(X_G)`.  The *kernel* of the modular cover is the connected component of $`\ker \phi`.  This is an {bpref "ag.abelian_variety"}[abelian variety], possibly of {bpref "ag.dimension"}[dimension] zero.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "ec"}[] {uses "gl2.open"}[] {uses "modcurve"}[] {uses "modcurve.level_structure"}[] {uses "modcurve.psl2index"}[]
:::

:::definition "modcurve.name"
*Standard modular curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.name))

We use the following notation to denote some standard modular curves that appear in the literature:

- $`X(N)` denotes the {bpref "modcurve.xn"}[modular curve] that parametrizes elliptic curves with full rational $`N`-torsion.

- $`X_0(N)` denotes the modular curve that parametrizes elliptic curves with a rational cyclic isogeny of degree $`N`.

- $`X_1(N)` denotes the modular curves that parametrizes elliptic curves with a rational point of order $`N`.

- $`X_{S_4}(\ell)` parametrizes elliptic curves whose mod-$`\ell` Galois images is projectively isomorpic to $`S_4`, respectively.

- For primes $`\ell\equiv 1\bmod 4` the modular curve $`X_{A_4}(\ell)` parametrizes elliptic curves whose mod-$`\ell` Galois images is projectively isomorpic to $`A_4` and $`S_4`, respectively.

- For primes $`\ell\equiv\pm 1\bmod 5` the modular curve $`X_{A_5}(\ell)` parametrizes elliptic curves mod-$`\ell` Galois images is projectively isomorpic to $`A_5`.

- $`X_{\mathrm{sp}}(N)` denotes the *split Cartan* modular curve $`X_H` for which $`H\leq \GL_2(\widehat{\Z})` is the inverse image of the reduction to $`\GL_2(\Z/N\Z)` of the {bpref "gl2.cartan"}[Cartan subgroup] associated to an imaginary quadratic order $`\mathcal O` in which every prime divisor of $`N` splits (this definition does not depend on $`\mathcal O`, up to conjugacy $`H` is the inverse image of the diagonal subgroup of $`\GL_2(\Z/N\Z)`).

- $`X_{\mathrm{sp}}^+(N)` denotes the modular curve $`X_H` for which $`H\leq \GL_2(\widehat{\Z})` is the reduction to $`\GL_2(\Z/N\Z)` of the normalizer of the split Cartan subgroup of $`\GL_2(\widehat{\Z})` (containing the split Cartan with index 2).

- $`X_{\mathrm{ns}}(N)` denotes the *nonsplit Cartan* modular curve $`X_H` for which $`H\leq \GL_2(\widehat{\Z})` is the inverse image of the reduction to $`\GL_2(\Z/N\Z)` of the Cartan subgroup associated to an imaginary quadratic order $`\mathcal O` in which every prime divisor of $`N` is inert (this definition does not depend on $`\mathcal O`).

- $`X_{\mathrm{ns}}^+(N)` denotes the modular curve $`X_H` for which $`H\leq \GL_2(\widehat{\Z})` is the reduction to $`\GL_2(\Z/N\Z)` of the normalizer of the nonsplit Cartan subgroup of $`\GL_2(\widehat{\Z})` (containing the nonsplit Cartan with index 2).

Depends on: {uses "gl2.cartan"}[] {uses "modcurve.xn"}[]
:::

:::definition "modcurve.newform_level"
*Newform level of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.newform_level))

The *newform level* of a {bpref "modcurve"}[modular curve] $`X_H` of positive {bpref "gl2.genus"}[genus] is the least common multiple of the {bpref "cmf.level"}[level] of the {bpref "cmf.newform"}[newforms] corresponding to {bpref "av.decomposition"}[isogeny factors] of the {bpref "ag.jacobian"}[Jacobian] of $`X_H`.

Depends on: {uses "ag.jacobian"}[] {uses "av.decomposition"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "gl2.genus"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.other_labels"
*Other labels for modular curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.other_labels))

Modular curves are identified in the literature using several different labeling conventions.  In addition to the standard names for the classical modular curves $`X(N), X_0(N), X_1(N), X_{\mathrm ns}^+(N), X_{\mathrm sp}^+(N)`, etc., there are a number of labeling systems that are used in different contexts, including:

- *(CP)* Cummins and Pauli labels $`\texttt{NA}^\texttt{g}`,are used to identify congruence subgroups of $`\PSL_2(\Z)` of level $`N` and genus $`g\le 24` on [this site](https://mathstats.uncg.edu/sites/pauli/congruence/), which is based on .<br>  Note that Cummins and Pauli work up to $`\PGL_2(\Z)`-conjugacy, thus for some open $`H` in $`\GL_2(\widehat{\Z})` the group $`\pm H\cap \SL_2(\widehat{\Z})` may have more than one CP label.

- *(RZB)* Rouse and Zureick-Brown labels $`X\texttt{m}` with $`1\le m\le 727` are used for modular curves $`X_H` of $`2`-power level on [this site](https://users.wfu.edu/rouseja/2adic/), based on .<br>  Note that Rouse and Zureick-Brown put the action on the right, rather than the left (so one should transpose $`H` when comparing with their tables).

- *(RSZB)* Rouse, Sutherland, and Zureick-Brown labels $`\texttt{N.i.g.n}` identify open subgroups of $`\GL_2(\widehat{\Z})` according to their level $`N`, index $`i`, and genus $`g`, as defined in .

- *(S)* Sutherland labels $`\texttt{NS.a.b.c}` for groups of prime level $`N` were introduced in  and are used to identify {bpref "ec.galois_rep_modell_image"}[mod-$`\ell` Galois images].

- *(SZ)* Sutherland and Zywina labels $`\texttt{MA}^\texttt{g}\texttt{-Na}` are used in  to identify modular curves of prime power level with infinitely many rational points.

Depends on: {uses "ec.galois_rep_modell_image"}[]
:::

:::definition "modcurve.point_residue_field" (lean := "AlgebraicGeometry.Scheme.residueField")
*Residue field of a point on a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.point_residue_field))

The *residue field* of a point $`x` on a modular curve $`X` defined over a field $`K` is the field $`K(x)`.
:::

:::definition "modcurve.psl2index"
*$`\PSL_2`-index.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.psl2index))

The *$`\PSL_2`-index* of a {bpref "modcurve"}[modular curve] $`X_H` is the index of $`\Gamma_H := \pm H\cap \SL_2(\Z)` in $`\PSL_2(\Z)`; this index is also the degree of the map $`j : \Gamma_H \backslash \overline{\mathfrak{h}} \to X(1)`, where $`\overline{\mathfrak{h}}` is the completed {bpref "mf.upper_half_plane"}[upper half-plane]. This is equal to the {bpref "modcurve.index"}[index] of the modular curve when $`-1 \in H`, and equals half the index if $`-1 \notin H`.

Depends on: {uses "mf.upper_half_plane"}[] {uses "modcurve"}[] {uses "modcurve.index"}[]
:::

:::definition "modcurve.quadratic_refinements" (lean := "Subgroup.adjoinNegOne, Subgroup.relIndex_adjoinNegOne_eq_two")
*Index 2 refinements.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.quadratic_refinements))

An *index 2 refinement* of a {bpref "modcurve"}[modular curve] $`X_H` is a {bpref "modcurve.modular_cover"}[modular cover] $`X_{H'} \to X_H` such that $`H' < H` and $`H=\{\pm 1\}H'`, so $`(H:H')=2`.  We also refer to $`H'` as an *index 2 refinement* of $`H`.  In particular, if $`-1 \not \in H` then there are no index 2 refinements.

An index 2 refinement $`X_{H'} \to X_H` is an isomorphism of the underlying modular curves, but refines the moduli problem from $`H` to $`H'`.

Depends on: {uses "modcurve"}[] {uses "modcurve.modular_cover"}[]
:::

:::definition "modcurve.rank"
*Analytic rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.rank))

The *analytic rank* of a {bpref "modcurve"}[modular curve] is the order of vanishing of its {bpref "lfunction"}[L-function] at its {bpref "lfunction.central_point"}[central point], which is equal to the sums of the {bpref "cmf.analytic_rank"}[analytic ranks] of the L-functions of the {bpref "av.simple"}[simple] modular {bpref "ag.abelian_variety"}[abelian varieties] corresponding to {bpref "cmf.galois_orbit"}[Galois orbits] of {bpref "cmf.newform"}[modular forms] that are the {bpref "av.decomposition"}[isogeny factors] of its {bpref "ag.jacobian"}[Jacobian].

The {bpref "ec.bsdconjecture"}[Birch and Swinnerton-Dyer] conjecture for modular abelian varieties implies that the analytic rank is equal to the {bpref "ag.mordell_weil"}[Mordell-Weil rank] of the Jacobian.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "ag.mordell_weil"}[] {uses "av.decomposition"}[] {uses "av.simple"}[] {uses "cmf.analytic_rank"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "ec.bsdconjecture"}[] {uses "lfunction"}[] {uses "lfunction.central_point"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.relative_index" (lean := "Subgroup.relIndex")
*Index of a modular map.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.relative_index))

Given a map $`f : X_H \to X_G` of {bpref "modcurve"}[modular curves] induced by an inclusion of {bpref "gl2.open"}[open subgroups] $`H \le G \le \GL_2(\hat{\Z})`, the *relative index* of $`f` is the {bpref "gl2.index"}[index] $`[G : H]`.  The degree of $`f` is half the index of $`f` if $`-1 \in G` and $`-1 \not\in H`, and equal to the index otherwise.

Depends on: {uses "gl2.index"}[] {uses "gl2.open"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.simple"
*Simple modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.simple))

A {bpref "modcurve"}[modular curve] $`X_H` is *simple* if its {bpref "ag.jacobian"}[Jacobian] is a {bpref "av.simple"}[simple] {bpref "ag.abelian_variety"}[abelian variety].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "av.simple"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.sl2level"
*$`\SL_2`-level.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.sl2level))

The *$`\SL_2`-level* of a {bpref "modcurve"}[modular curve] $`X_H` is the {bpref "cmf.congruence_subgroup"}[level of the congruence subgroup] $`\Gamma_H:=H\cap\SL_2(\Z)`.  The $`\SL_2`-level divides but need not equal the {bpref "gl2.level"}[level] of $`H`.

Depends on: {uses "cmf.congruence_subgroup"}[] {uses "gl2.level"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.xns.remarks"
*Remarks on $X\_\{\mathrm\{ns.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xns.remarks))

For $`N=p` prime modular curve $`X_{\mathrm{ns}}(p)` has the following moduli interpretation.  It parameterizes $`\bar k`-isomorphism classes of pairs $`(E,\mathfrak o)` where $`E` is an elliptic curve over $`k` and $`\mathfrak o` is a $`k`-rational *oriented necklace*: a $`\Gal_k`-stable cyclic permutation of the $`p+1` cyclic subgroups of $`E[p](\bar k)` of order $`p` .
:::

:::definition "modcurve.xns_plus.remarks"
*Remarks on $X\_\{\mathrm\{ns.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xns_plus.remarks))

For $`N=p` prime the modular curve $`X_{\mathrm{ns}}^+(p)` has the following moduli interpretation.  Non-cuspidal points correspond to $`\bar k`-isomorphism classes of pairs $`(E,\mathfrak o)` where $`E` is an elliptic curve over $`k` and $`\mathfrak o` is a $`k`-rational (unoriented) *necklace*: a $`\Gal_k`-stable pair of inverse cyclic permutations of the $`p+1` cyclic subgroups of $`E[p](\bar k)` of order $`p` .
:::
