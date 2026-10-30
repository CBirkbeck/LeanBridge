import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Modular curves" =>

This section lists the LMFDB definitions in the category `modcurve`. Each definition links back to its LMFDB knowl.

:::definition "modcurve"
*Modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve))

For each {bpref "gl2.open"}[open subgroup] $`H \le \GL_2(\widehat{\Z})`, there is a *modular curve* $`X_H`, defined as a quotient of the {bpref "modcurve.xn"}[full modular curve] $`X_{\text{full}}(N)`, where $`N` is the {bpref "gl2.level"}[level] of $`H`.  More precisely, $`H` is the inverse image of a subgroup $`H_N \le \GL_2(\Z/N\Z)`, which acts on $`X_{\text{full}}(N)` over $`\Q`, and $`X_H` is the {bpref "ag.quotient_curve"}[quotient curve] $`H_N \backslash X_{\text{full}}(N)`, also defined over $`\Q`.

Like $`X_{\text{full}}(N)`, the curve $`X_H` is {bpref "ag.curve.smooth"}[smooth], projective, and integral, and when $`\det(H)=\widehat{\Z}` it is also geometrically integral, but in general it may have several {bpref "modcurve.components"}[geometric components], as is the case for $`X_{\text{full}}(N)` when $`N>2`.

*Rational points*: When $`-1\in H` the rational points of $`X_H`  consist of  {bpref "modcurve.cusps"}[cusps] and $`\Gal_{\Q}`-stable isomorphism classes of pairs $`(E,[\iota]_H)`, where $`E` is an {bpref "ec"}[elliptic curve] over $`\Q`, and $`[\iota]_H` is an {bpref "modcurve.level_structure"}[$`H`-level structure] on $`E`.  Such points exist precisely when the image of the {bpref "ec.galois_rep"}[adelic Galois representation] $`\rho_E\colon \Gal_{\Q}\to \GL_2(\widehat{\Z})` is conjugate to a subgroup of $`H`.

*Complex points*: The {bpref "cmf.congruence_subgroup"}[congruence subgroup] $`\Gamma_H:= H\cap \SL_2(\Z)` acts on the {bpref "mf.upper_half_plane"}[completed upper half-plane] $`\overline{\mathfrak{h}}`; one connected component of $`X_H(\C)` is biholomorphic to the quotient $`\Gamma_H \backslash \overline{\mathfrak{h}}`.

The curve $`X_H` can alternatively be constructed as the coarse moduli space of the stack $`\mathcal X_H` over $`\Q` defined in Deligne-Rapoport .  Both constructions of $`X_H` can be carried out over any field of characteristic not dividing $`N`, or even over $`\Z[1/N]`.

Depends on: {uses "ag.curve.smooth"}[] {uses "ag.quotient_curve"}[] {uses "cmf.congruence_subgroup"}[] {uses "ec"}[] {uses "ec.galois_rep"}[] {uses "gl2.level"}[] {uses "gl2.open"}[] {uses "mf.upper_half_plane"}[] {uses "modcurve.cusps"}[] {uses "modcurve.level_structure"}[] {uses "modcurve.xn"}[]
:::

:::definition "modcurve.agreeable" (lean := "Matrix.GeneralLinearGroup.IsAgreeable, Matrix.GeneralLinearGroup.agreeableClosure, Matrix.GeneralLinearGroup.AgreeableQuotient, Matrix.GeneralLinearGroup.adelicScalars, Matrix.GeneralLinearGroup.adelicSL")
*Agreeable.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.agreeable))

An {bpref "gl2.open"}[open subgroup] $`H\le \GL_2(\widehat{\Z})` (and the corresponding {bpref "modcurve"}[modular curve] $`X_H`) is *agreeable* (as defined by Zywina in Section 1.4 of ) if the following hold:

- $`\det(H)=\widehat{\Z}^\times`;

- $`H` contains the subgroup of $`\GL_2(\widehat{\Z})` formed by scalar matrices;

- the {bpref "modcurve.level"}[level] of $`H\le \GL_2(\widehat{\Z})` and the level of $`H\cap \SL_2(\widehat{\Z})\le \SL_2(\widehat{\Z})` have the same odd prime divisors.

The *agreeable closure* $`\widetilde H` of $`H` is the intersection of all the agreeable open subgroups of $`\GL_2(\widehat{\Z})` that contain $`H`.

The agreeable closure $`\widetilde H` contains $`H` as a {bpref "group.subgroup.normal"}[normal subgroup] and has the same {bpref "group.commutator_subgroup"}[commutator subgroup] as $`H`; see Proposition 8.1 of .  It follows that the quotient $`\widetilde{H}/H` (called the *agreeable quotient*) is finite abelian.

Depends on: {uses "gl2.open"}[] {uses "group.commutator_subgroup"}[] {uses "group.subgroup.normal"}[] {uses "modcurve"}[] {uses "modcurve.level"}[]
:::

:::definition "modcurve.canonical_field" (lean := "Matrix.GeneralLinearGroup.canonicalField, Matrix.GeneralLinearGroup.canonicalFieldOfLevel, Matrix.GeneralLinearGroup.detReduction")
*Canonical field of definition of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.canonical_field))

Let $`X_H` be the {bpref "modcurve"}[modular curve] over $`\mathbb{Q}` associated to an open subgroup $`H \le \operatorname{GL}_2(\widehat{\mathbb{Z}})`.  Let $`\pi_0((X_H)_{\overline{\Q}})` be the set of {bpref "ag.geom_component"}[geometric components].  Since $`X_H` is integral, the action of $`\Gal_{\Q}` on $`\pi_0((X_H)_{\overline{\Q}})` is transitive.  Let $`C` be one of the geometric components.  The *canonical field of definition* of $`C` is the subfield $`K` of $`\overline{\mathbb{Q}}` fixed by the stabilizer $`\operatorname{Stab}_{\Gal_{\Q}}(C)`.

Let $`N` be the {bpref "modcurve.level"}[level] of $`H`, which is the smallest $`N \ge 1` such that $`H` is the inverse image of a subgroup $`H_N \le \operatorname{GL}_2(\mathbb{Z}/N\mathbb{Z})`.  Then $`K` is a number field contained in $`\mathbb{Q}(\zeta_N)`.

Since $`K` is abelian, it is independent of the choice of $`C`, and every geometric component of $`X_H` has a canonical model over $`K`.

Equivalently, $`K` can be defined as the ring of global regular functions of the $`\mathbb{Q}`-scheme $`X_H`.

Also, $`K` is the subfield of $`\mathbb{Q}^{\textup{ab}}` fixed by $`\det(H) \le \widehat{\mathbb{Z}}^\times`, or equivalently the subfield of $`\mathbb{Q}(\zeta_N)` fixed by $`\det(H_N) \subset (\mathbb{Z}/N\mathbb{Z})^\times`.

It can happen that a geometric component of $`X_H` is definable over a field smaller than its canonical field of definition.  For example, the canonical field of definition of a geometric component of the {bpref "modcurve.xn"}[full modular curve] $`X_{\text{full}}(N)_{\mathbb{Q}}` is $`\mathbb{Q}(\zeta_N)`, but any such geometric component is the base extension of the curve {bpref "modcurve.xarith"}[$`X_{\mathrm{arith}}(N)`] over $`\mathbb{Q}`.

Depends on: {uses "ag.geom_component"}[] {uses "modcurve"}[] {uses "modcurve.level"}[] {uses "modcurve.xn"}[]
:::

:::definition "modcurve.cm_discriminants"
*CM points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.cm_discriminants))

Rational points on a {bpref "modcurve"}[modular curve] $`X_H` that correspond to elliptic curves with {bpref "ec.complex_multiplication"}[complex multiplication] are called *CM points*.

Over $`\Q` these correspond to rational points in the fiber of the map $`j\colon X_H\to X(1)` above one of the $`13` $`j`-invariants of CM elliptic curves over $`\Q` corresponding to one of the *CM discriminants*

$$`-3,-4,-7,-8,-11,-12,-16,-19,-27, -27, -43,-67,-163,`
 of {bpref "nf.order"}[imaginary quadratic orders] of {bpref "nf.class_number"}[class number] one.  These $`13` orders lie in $`9` distinct imaginary quadratic fields.

Depends on: {uses "ec.complex_multiplication"}[] {uses "modcurve"}[] {uses "nf.class_number"}[] {uses "nf.order"}[]
:::

:::definition "modcurve.components"
*Geometric components of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.components))

For the {bpref "modcurve.xn"}[full modular curve] $`X_{\mathrm{full}}(N)_{\Q}`,
the set $`\pi_0(X_{\mathrm{full}}(N)_{\overline{\Q}})` of {bpref "ag.geom_component"}[geometric components] is in bijection with the set $`\mu_N^{\text{prim}}` of primitive $`N`th roots of unity (map $`(E,P,Q)` to the Weil pairing $`e_N(P,Q)`).

For the {bpref "modcurve"}[quotient curve] $`(X_H)_{\Q}`, we have $`\pi_0((X_H)_{\overline{\Q}}) \simeq \det(H_N) \backslash \pi_0(X_{\mathrm{full}}(N)_{\overline{\Q}})\simeq \det(H_N) \backslash \mu_N^{\text{prim}}`.  Thus the number of geometric components is the index $`((\Z/N\Z)^\times : \det H_N)`.

The statements above hold also if $`\Q` and $`\overline{\Q}` are replaced by $`k` and $`\overline{k}`, for any field $`k` of characteristic not dividing $`N`.

The curve $`(X_H)_{\Q}` is integral.  It is geometrically integral if and only if $`\det H_N = (\Z/N\Z)^\times`, or equivalently $`\det H = \widehat{\Z}^\times`.

Depends on: {uses "ag.geom_component"}[] {uses "modcurve"}[] {uses "modcurve.xn"}[]
:::

:::definition "modcurve.contains_negative_one" (lean := "Subgroup.adjoinNegOne_eq_self_iff, Subgroup.adjoinNegOne")
*Contains $`-I`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.contains_negative_one))

A {bpref "modcurve"}[modular curve] $`X_H` with $`-I\in H\in \GL_2(\widehat{\Z})` has the property that if an {bpref "ec"}[elliptic curve] $`E` over a number field $`K` has $`j`-invariant $`j(E)\ne 0,1728` in the image of $`j\colon X_H\to X(1)`, then the mod-$`N` Galois image of every {bpref "av.twist"}[twist] of $`E` is conjugate to a subgroup of the projection of $`H` to $`\GL_2(\Z/N\Z)`. Modular curves $`X_H` with $`-I\not\in H` do not enjoy this property.

Depends on: {uses "av.twist"}[] {uses "ec"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.cusp_orbits" (lean := "Matrix.GeneralLinearGroup.CuspOrbit, Matrix.GeneralLinearGroup.cuspOrbitSize, Matrix.GeneralLinearGroup.numCuspOrbitsOfSize, Matrix.GeneralLinearGroup.cuspGaloisRel, Matrix.GeneralLinearGroup.adelicCyclotomicCharacter")
*Cusp orbits.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.cusp_orbits))

For an {bpref "gl2.open"}[open subgroup] $`H` of $`\GL_2(\widehat{\Z})` with $`\det(H) =\widehat{\Z}^\times`, the *cusps* of $`H` are the double cosets $`\pm H  \backslash \GL_2(\widehat{\Z}) /\langle\delta\rangle`, where $`\delta := \begin{bmatrix}1&1\\0&1\end{bmatrix}`.  These correspond to the {bpref "modcurve.cusps"}[cusps]  of the {bpref "modcurve"}[modular curve] $`X_H`.

Each $`\sigma \in \Gal_{\Q}` acts on the cusps of $`H` via $`Hg\langle \pm \delta\rangle\mapsto Hg\chi(\sigma)\langle \pm \delta\rangle`, where $`\chi(\sigma)=\begin{bmatrix}e&0\\0&1\end{bmatrix} \in \GL_2(\widehat{\Z})` is such that for all positive integers $`N` one has $`\sigma(\zeta_N)=\zeta_N^e`.

The Galois orbit of a cusp of $`H` is its orbit under the action of $`\Gal_{\Q}`.

The sizes of the Galois orbits of the cusps of $`H` form a multiset of integers that may be expressed in exponential notation, for example $`2^2\cdot 4^3` indicates that there are five *cusp orbits*, 2 of size 2 and 3 of size 4, and a total of 16 cusps.

Depends on: {uses "gl2.open"}[] {uses "modcurve"}[] {uses "modcurve.cusps"}[]
:::

:::definition "modcurve.cusp_widths" (lean := "Matrix.GeneralLinearGroup.adelicCusps, Matrix.GeneralLinearGroup.adelicCuspWidth, Subgroup.adjoinNegOne, DoubleCoset.Quotient")
*Cusp widths.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.cusp_widths))

For an open subgroup $`H` of $`\GL_2(\widehat{\Z})` with $`\det(H) =\widehat{\Z}^\times`, the *cusps* of $`H` are the double cosets $`\pm H  \backslash \GL_2(\widehat{\Z}) /\langle \delta\rangle`, where $`\delta := \begin{bmatrix}1&1\\0&1\end{bmatrix}`.  These correspond to the {bpref "modcurve.cusps"}[cusps]  of the modular curve $`X_H`.

The *width* of a cusp $`c \in \pm H  \backslash \GL_2(\widehat{\Z}) /\langle \delta\rangle` is the number of right cosets it contains, or equivalently the smallest integer $`h` such that $`c\delta^h = c`. The sum of the cusp widths is equal to the {bpref "modcurve.psl2index"}[$`\PSL_2`-index] of $`H`.

Depends on: {uses "modcurve.cusps"}[] {uses "modcurve.psl2index"}[]
:::

:::definition "modcurve.cusps"
*Cusps of a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.cusps))

The *cusps* on $`X_H` are the points whose image under the canonical morphism $`j\colon X_H\to X(1)\simeq \mathbb{P}^1` is $`\infty`.  It is only the noncuspidal points that parametrize elliptic curves (with level structure).

The *cusps* of a modular curve $`X_H` correspond to the complement of $`Y_H` in $`X_H`, where $`Y_H` is the coarse moduli stack $`\mathcal M_H^0` defined in .

The *rational cusps* (also called *$`\Q`-cusps*) are the cusps fixed by $`\Gal_{\Q}`.
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

:::definition "modcurve.elliptic_curve_of_point"
*Elliptic curve associated to a rational point.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.elliptic_curve_of_point))

Let $`X_H` be a {bpref "modcurve"}[modular curve] with $`-1\in H`.
The non-cuspidal $`K`-rational points on a modular curve $`X_H` are in one-to-one correspondence with isomorphism classes of pairs $`(E,[\iota]_H)`.  where $`E` is an {bpref "ec"}[elliptic curve] over $`K` and $`[\iota]_H` is a $`K`-rational {bpref "modcurve.level_structure"}[$`H`-level structure] on $`E`.

The isomorphism class of $`(E,[\iota]_H)` includes pairs $`(E',[\iota']_H)` for each of the infinitely many quadratic twists $`E'` of $`E` (because $`-1\in H`), but on modular curve pages and search results we list only the {bpref "ec.q.minimal_twist"}[minimal quadratic twist] of $`E`.

A quadratic twist-minimal elliptic curve $`E` may admit multiple non-isomorphic rational $`H`-level structures corresponding to multiple $`K`-rational points on $`X_H`, but in search results for low degreee points we list $`E` only once.

Depends on: {uses "ec"}[] {uses "ec.q.minimal_twist"}[] {uses "modcurve"}[] {uses "modcurve.level_structure"}[]
:::

:::definition "modcurve.elliptic_points" (lean := "Matrix.GeneralLinearGroup.ellipticPoints, Matrix.GeneralLinearGroup.modularGammaPSL, Matrix.GeneralLinearGroup.ellipticPoints_eq_ellipticOrbits, Subgroup.ellipticOrbits, Matrix.GeneralLinearGroup.modularGamma")
*Elliptic points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.elliptic_points))

An *elliptic point* on the {bpref "modcurve"}[modular curve] $`X_H` is a point whose stabilizer under the action of the {bpref "cmf.congruence_subgroup"}[congruence subgroup] $`\Gamma_H` is finite and nontrivial.

Depends on: {uses "cmf.congruence_subgroup"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.embedded_model"
*Embedded model.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.embedded_model))

For hyperelliptic curves and curves of genus less than 2, the {bpref "ag.canonical_model"}[canonical map] is not an embedding.  For {bpref "modcurve"}[modular curves] $`X_G` of this form, we take the lowest even weight $`k` so that Riemann-Roch guarantees an embedding into the projectivization of the space of modular forms associated to $`G`.  We refer to the image of this embedding as the *embedded model* of $`X_G`.

Depends on: {uses "ag.canonical_model"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.entanglement_index" (lean := "Matrix.GeneralLinearGroup.entanglementIndex, Matrix.GeneralLinearGroup.EntanglementQuotient, Matrix.GeneralLinearGroup.productOfProjections, Matrix.GeneralLinearGroup.le_productOfProjections")
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

:::definition "modcurve.gassmann_class" (lean := "Matrix.GeneralLinearGroup.gassmannClass, Matrix.GeneralLinearGroup.IsAdelicGassmannEquivalent, Subgroup.IsGassmannEquivalent, Subgroup.isGassmannEquivalent_equivalence")
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

:::definition "modcurve.level_structure" (lean := "WeierstrassCurve.levelStructure, WeierstrassCurve.IsRationalLevelStructure, WeierstrassCurve.cyclicIsogenyFieldDegree, WeierstrassCurve.cyclicTorsionFieldDegree, WeierstrassCurve.torsionFieldDegree")
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

:::definition "modcurve.local_obstruction" (lean := "AlgebraicGeometry.Scheme.HasLocalObstruction, AlgebraicGeometry.Scheme.HasPointIn, AlgebraicGeometry.Scheme.not_hasLocalObstruction")
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

:::definition "modcurve.point_degree"
*Degree of a point on a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.point_degree))

The degree of a point $`x` on a modular curve $`X` is the degree $`[\mathbb{Q}(x): \mathbb{Q}]`.
:::

:::definition "modcurve.point_residue_field" (lean := "AlgebraicGeometry.Scheme.residueField")
*Residue field of a point on a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.point_residue_field))

The *residue field* of a point $`x` on a modular curve $`X` defined over a field $`K` is the field $`K(x)`.
:::

:::definition "modcurve.psl2index" (lean := "Matrix.GeneralLinearGroup.psl2Index, Matrix.GeneralLinearGroup.modularGamma, Matrix.GeneralLinearGroup.modularGamma_adjoinNegOne, Matrix.GeneralLinearGroup.sl2zToAdelic")
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

The *analytic rank* of a {bpref "modcurve"}[modular curve] is the order of vanishing of its {bpref "lfunction"}[L-function] at its {bpref "lfunction.central_point"}[central point], which is equal to the sums of the {bpref "cmf.analytic_rank"}[analytic ranks] of the {bpref "cmf.lfunction"}[L-functions] of the {bpref "av.simple"}[simple] modular {bpref "ag.abelian_variety"}[abelian varieties] corresponding to {bpref "cmf.galois_orbit"}[Galois orbits] of {bpref "cmf.newform"}[modular forms] that are the {bpref "av.decomposition"}[isogeny factors] of its {bpref "ag.jacobian"}[Jacobian].

The {bpref "ec.bsdconjecture"}[Birch and Swinnerton-Dyer] conjecture for modular abelian varieties implies that the analytic rank is equal to the {bpref "ag.mordell_weil"}[Mordell-Weil rank] of the Jacobian.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "ag.mordell_weil"}[] {uses "av.decomposition"}[] {uses "av.simple"}[] {uses "cmf.analytic_rank"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "ec.bsdconjecture"}[] {uses "lfunction"}[] {uses "lfunction.central_point"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.rational_points"
*Rational points on a modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.rational_points))

The rational points on a {bpref "modcurve"}[modular curve] $`X_H` may be divided into three categories: {bpref "modcurve.cusps"}[cuspidal points], {bpref "modcurve.cm_discriminants"}[CM points], and non-cuspidal non-CM points.

{bpref "modcurve.genus"}[Genus] zero curves with a rational point are isomorphic to $`\mathbb{P}^1` and therefore have infinitely many rational points.  Genus one curves with a rational point whose {bpref "ag.jacobian"}[Jacobian] has positive Mordell-Weil rank are isomorphic to an {bpref "ec"}[elliptic curve] with infinitely many rational points.  In all other cases, the set of rational points is finite.

Depends on: {uses "ag.jacobian"}[] {uses "ec"}[] {uses "modcurve"}[] {uses "modcurve.cm_discriminants"}[] {uses "modcurve.cusps"}[] {uses "modcurve.genus"}[]
:::

:::definition "modcurve.relative_index" (lean := "Subgroup.relIndex")
*Index of a modular map.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.relative_index))

Given a map $`f : X_H \to X_G` of {bpref "modcurve"}[modular curves] induced by an inclusion of {bpref "gl2.open"}[open subgroups] $`H \le G \le \GL_2(\hat{\Z})`, the *relative index* of $`f` is the {bpref "gl2.index"}[index] $`[G : H]`.  The degree of $`f` is half the index of $`f` if $`-1 \in G` and $`-1 \not\in H`, and equal to the index otherwise.

Depends on: {uses "gl2.index"}[] {uses "gl2.open"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.simple" (lean := "AlgebraicGeometry.Scheme.HasSimpleJacobian, AlgebraicGeometry.Scheme.hasSimpleJacobian_iff, TauCeti.AlgebraicGeometry.AbelianVariety.IsJacobian, TauCeti.AlgebraicGeometry.AbelianVariety.IsSimple")
*Simple modular curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.simple))

A {bpref "modcurve"}[modular curve] $`X_H` is *simple* if its {bpref "ag.jacobian"}[Jacobian] is a {bpref "av.simple"}[simple] {bpref "ag.abelian_variety"}[abelian variety].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "av.simple"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.sl2level" (lean := "Matrix.GeneralLinearGroup.sl2Level, Matrix.GeneralLinearGroup.modularGamma, Matrix.GeneralLinearGroup.Gamma_adelicLevel_le_modularGamma, Matrix.GeneralLinearGroup.sl2Level_le_adelicLevel, Matrix.GeneralLinearGroup.Gamma_sl2Level_le")
*$`\SL_2`-level.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.sl2level))

The *$`\SL_2`-level* of a {bpref "modcurve"}[modular curve] $`X_H` is the {bpref "cmf.congruence_subgroup"}[level of the congruence subgroup] $`\Gamma_H:=H\cap\SL_2(\Z)`.  The $`\SL_2`-level divides but need not equal the {bpref "gl2.level"}[level] of $`H`.

Depends on: {uses "cmf.congruence_subgroup"}[] {uses "gl2.level"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.x0"
*$`X_0(N)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.x0))

$`X_0(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of $`\begin{pmatrix} \ast & \ast \\ 0 & \ast \end{pmatrix} \subset \GL_2(\Z/N\Z)`. Over a field $`k` of characteristic not dividing $`N`, its {bpref "modcurve.cusps"}[non-cuspidal] $`k`-rational points correspond to $`\bar k`-isomorphism classes of pairs $`(E,C)`, where:

- $`E` is an elliptic curve over $`k`, and

- $`C` is a $`\Gal_k`-stable cyclic subgroup of $`E[N](\overline{k})` of order $`N` (equivalently, the kernel of a $`k`-rational isogeny $`E\to E'` of degree $`N`).

Depends on: {uses "modcurve"}[] {uses "modcurve.cusps"}[]
:::

:::definition "modcurve.x1"
*$`X_1(N)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.x1))

$`X_1(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of $`\begin{pmatrix} 1 & * \\ 0 & * \end{pmatrix} < \GL_2(\Z/N\Z)`. Over a field $`k` of characteristic not dividing $`N`, its {bpref "modcurve.cusps"}[non-cuspidal] $`k`-rational points correspond to $`\bar k`-isomorphism classes of pairs $`(E,P)`, where:

- $`E` is an elliptic curve over $`k`, and

- $`P \in E[N](k)` is a point of order $`N`.

Depends on: {uses "modcurve"}[] {uses "modcurve.cusps"}[]
:::

:::definition "modcurve.x1mn"
*$`X_1(M,MN)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.x1mn))

$`X_{\mathrm{arith},1}(M,MN)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of $`\begin{pmatrix} 1 & M* \\ 0 & * \end{pmatrix} \subset \GL_2(\Z/MN\Z)`. Over a field $`k` of characteristic not dividing $`MN`, its {bpref "modcurve.cusps"}[non-cuspidal] $`k`-rational points correspond to $`\bar k`-isomorphism classes of triples $`(E,P,C)`, where:

- $`E` is an elliptic curve over $`k`,

- $`P \in E[MN](k)` is a point of order $`MN`, and

- $`C \leq E[M](\overline{k})` is a $`\Gal_k`-stable cyclic subgroup of order $`M` such that $`E[M]=\langle NP \rangle \oplus C`.

Depends on: {uses "modcurve"}[] {uses "modcurve.cusps"}[]
:::

:::definition "modcurve.xarith"
*$X\_\{\mathrm\{arith.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xarith))

$`X_{\mathrm{arith}}(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\leq \GL_2(\widehat{\Z})` the inverse image of $`\begin{pmatrix}1&0\\0&*\end{pmatrix}\leq \GL_2(\Z/N\Z)`.

As a moduli space, $`X_{\mathrm{arith}}` parametrizes isomorphism classes of triples $`(E,\phi,P)`, where:

- $`E` is a generalized elliptic curve,

- $`P` is a point of exact order $`N`,

- and $`\phi \colon E \to E'` is a cyclic $`N`-isogeny such that $`E[N]` is generated by $`P` and $`\ker\phi`.

Alternatively, it parametrizes isomorphism classes of pairs $`(E,\psi)` where $`E` is a generalized elliptic curve and $`\psi \colon \mu_N\times \Z/N\Z\xrightarrow{\sim} E[N]` is a symplectic isomorphism.

Depends on: {uses "modcurve"}[]
:::

:::definition "modcurve.xfull"
*$`X(N)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xfull))

$`X(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of the trivial subgroup of $`\GL_2(\Z/N\Z)`. Over a field $`k` of characteristic not dividing $`N`, its {bpref "modcurve.cusps"}[non-cuspidal] $`k`-rational points correspond to triples $`(E,P,Q)`, where:

- $`E` is an elliptic curve over $`k`, and

- $`P,Q \in E(k)` form a basis for $`E[N](\overline{k})`.

There are other {bpref "modcurve.xn"}[variants].

Depends on: {uses "modcurve"}[] {uses "modcurve.cusps"}[] {uses "modcurve.xn"}[]
:::

:::definition "modcurve.xn"
*Modular curve $`X(N)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xn))

There are three variants of the modular curve $`Y(N)`:

1. There is a functor sending each $`\Z[1/N]`-algebra $`R` to the set of (isomorphism classes of) pairs $`(E,\alpha)` such that $`E` is an {bpref "ec.ring"}[elliptic curve over $`R`] and $`\alpha \colon E[N] \to (\Z/N\Z)^2` is an isomorphism of group schemes.  Suppose that $`N \ge 3`; then this functor is represented by a smooth affine $`\mathbb{Z}[1/N]`-scheme $`Y_{\mathrm{full}}(N)`, called the *full modular curve of level $`N`*.  (If $`N<3`, it is representable only by an algebraic stack, and one must take the coarse moduli space to get a scheme.)  For any field $`k` with $`\operatorname{char} k \nmid N`, the set $`Y_{\mathrm{full}}(N)(k)` is the set of isomorphism classes of triples $`(E,P,Q)` , where $`E` is an elliptic curve over $`k` and $`P,Q \in E(k)` form a $`(\Z/N\Z)`-basis of $`E[N]`.  The curve $`Y_{\mathrm{full}}(N)_{\Q}` is integral but typically has several {bpref "modcurve.components"}[geometric components].

2. Let $`\zeta_N \in \overline{\Q}` be a primitive $`N`th root of unity.  There is a functor sending each $`\Z[1/N,\zeta_N]`-algebra $`R` to the set of pairs $`(E,\alpha)` such that $`E` is an elliptic curve over $`R` and $`\alpha \colon E[N] \to (\Z/N\Z)^2` is an isomorphism of group schemes such that the resulting elements $`P,Q \in E[N](R)` satisfy $`e_N(P,Q)=\zeta_N`.  For $`N \ge 3`, this functor is represented by a smooth affine $`\Z[1/N,\zeta_N]`-scheme $`Y(N)`, called the *classical modular curve of level $`N`*.  Over any {bpref "ring.a-field"}[$`\Z[1/N,\zeta_N]`-field] $`k`, the curve $`Y(N)_k` is geometrically integral.

3. There is a functor sending each $`\Z[1/N]`-algebra $`R` to the set of pairs $`(E,\alpha)` consisting of an elliptic curve $`E` over $`R` and a {bpref "alg.symplectic_isomorphism"}[symplectic isomorphism] $`\alpha \colon E[N] \to \Z/N\Z \times \mu_N`.  For $`N \ge 3`, this functor is represented by a smooth affine $`\mathbb{Z}[1/N]`-scheme $`Y_{\mathrm{arith}}(N)`.  Over any field $`k` with $`\operatorname{char} k \nmid N`, the curve $`Y_{\mathrm{arith}}(N)_k` is geometrically integral.

\*Relationships\*: Over any {bpref "ring.a-field"}[$`\Z[1/N,\zeta]`-field] $`k`, the curve $`Y_{\mathrm{arith}}(N)_k` is isomorphic to $`Y(N)_k` and to a {bpref "modcurve.components"}[connected component] of $`Y_{\mathrm{full}}(N)_k`.

\*Complex points\*: The group {bpref "cmf.congruence_subgroup"}[$`\Gamma(N)`] acts on the {bpref "mf.upper_half_plane"}[upper half-plane] $`\mathfrak{h}`, and the quotient $`\Gamma(N) \backslash \mathfrak{h}` is biholomorphic to $`Y(N)(\mathbb{C}) \simeq Y_{\textup{arith}}(\C)` (choosing $`\zeta_N \in \C`).

\*Compactifications\*: For each variant, there is a corresponding smooth projective model, denoted $`X_{\mathrm{full}}(N)`, $`X(N)`, or $`X_{\mathrm{arith}}(N)`.

\*Quotients\*: For each {bpref "gl2.open"}[open subgroup] $`H \le \GL_2(\widehat{\Z})`, there is a quotient {bpref "modcurve"}[$`X_H`] of $`X_{\mathrm{full}}(N)`.

Depends on: {uses "alg.symplectic_isomorphism"}[] {uses "cmf.congruence_subgroup"}[] {uses "ec.ring"}[] {uses "gl2.open"}[] {uses "mf.upper_half_plane"}[] {uses "ring.a-field"}[]
:::

:::definition "modcurve.xns"
*$X\_\{\text\{ns.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xns))

$`X_{\text{ns}}(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of a {bpref "gl2.cartan"}[Cartan subgroup] of $`\GL_2(\Z/N\Z)` that is nonsplit at every prime dividing $`N`.

Depends on: {uses "gl2.cartan"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.xns.remarks"
*Remarks on $X\_\{\mathrm\{ns.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xns.remarks))

For $`N=p` prime modular curve $`X_{\mathrm{ns}}(p)` has the following moduli interpretation.  It parameterizes $`\bar k`-isomorphism classes of pairs $`(E,\mathfrak o)` where $`E` is an elliptic curve over $`k` and $`\mathfrak o` is a $`k`-rational *oriented necklace*: a $`\Gal_k`-stable cyclic permutation of the $`p+1` cyclic subgroups of $`E[p](\bar k)` of order $`p` .
:::

:::definition "modcurve.xns_plus"
*$X\_\{\text\{ns.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xns_plus))

$`X_{\text{ns}}^+(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of an {bpref "gl2.cartan"}[extended Cartan subgroup] of $`\GL_2(\Z/N\Z)` that is nonsplit at every prime dividing $`N`.

Depends on: {uses "gl2.cartan"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.xns_plus.remarks"
*Remarks on $X\_\{\mathrm\{ns.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xns_plus.remarks))

For $`N=p` prime the modular curve $`X_{\mathrm{ns}}^+(p)` has the following moduli interpretation.  Non-cuspidal points correspond to $`\bar k`-isomorphism classes of pairs $`(E,\mathfrak o)` where $`E` is an elliptic curve over $`k` and $`\mathfrak o` is a $`k`-rational (unoriented) *necklace*: a $`\Gal_k`-stable pair of inverse cyclic permutations of the $`p+1` cyclic subgroups of $`E[p](\bar k)` of order $`p` .
:::

:::definition "modcurve.xpm1"
$`X_{\pm 1}(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le GL_2(\widehat{\Z})` the inverse image of $`\begin{pmatrix} \pm 1 & * \\ 0 & * \end{pmatrix} \subset \GL_2(\Z/N\Z)`. Over a field $`k` of characteristic not dividing $`N`, its {bpref "modcurve.cusps"}[non-cuspidal] $`k`-rational points correspond to $`\bar k`-isomorphism classes of pairs $`(E,\pm P)`, where:

- $`E` is an elliptic curve over $`k`, and

- $`P \in E[N]` is a point of order $`N` for which the set $`\{P,-P\}` is $`\Gal_k`-stable.

The modular curve {bpref "modcurve.x1"}[$`X_1(N)`] is a {bpref "modcurve.quadratic_refinements"}[quadratic refinement] of $`X_{\pm1}(N)`.

Depends on: {uses "modcurve"}[] {uses "modcurve.cusps"}[] {uses "modcurve.quadratic_refinements"}[] {uses "modcurve.x1"}[]
:::

:::definition "modcurve.xpm1mn"
$`X_{\mathrm{arith},\pm1}(M,MN)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of $`\begin{pmatrix} \pm 1 & M* \\ 0 & * \end{pmatrix} \subset \GL_2(\Z/MN\Z)`. The modular curve {bpref "modcurve.x1mn"}[$`X_{\mathrm{arith},1}(M,MN)`] is one of its {bpref "modcurve.quadratic_refinements"}[quadratic refinements].

Depends on: {uses "modcurve"}[] {uses "modcurve.quadratic_refinements"}[] {uses "modcurve.x1mn"}[]
:::

:::definition "modcurve.xs4"
For $`\ell` an odd prime, $`X_{S_4}(\ell)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of the subgroup of $`\PGL_2(\Z/\ell\Z)` isomorphic to $`S_4` (which is unique up to conjugacy).  It parameterizes elliptic curves whose {bpref "ec.galois_rep_modell_image"}[mod-$`\ell` Galois representation] has projective image $`S_4`, one of the three exceptional groups $`A_4`, $`A_5`, $`S_4` of $`\PGL_2(\ell)` that can arise as projective mod-$`\ell` images, and the only one that can arise for elliptic curves over $`\Q`.

Depends on: {uses "ec.galois_rep_modell_image"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.xsp"
*$X\_\{\text\{sp.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xsp))

$`X_{\text{sp}}(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of a {bpref "gl2.cartan"}[Cartan subgroup] $`\begin{pmatrix} * & 0\\ 0& * \end{pmatrix}` that is split at every prime dividing $`N`. As a moduli space it parameterizes triples $`(E,C,D)` where:

- $`E` is an elliptic curve over $`k`, and

- $`C` and $`D` are $`\Gal_k`-stable cyclic subgroups such that $`E[N](\overline{k})\simeq C \oplus D`.

Depends on: {uses "gl2.cartan"}[] {uses "modcurve"}[]
:::

:::definition "modcurve.xsp_plus"
*$X\_\{\text\{sp.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/modcurve.xsp_plus))

$`X_{\text{sp}}^+(N)` is the {bpref "modcurve"}[modular curve] $`X_H` for $`H\le \GL_2(\widehat{\Z})` the inverse image of an {bpref "gl2.cartan"}[extended Cartan subgroup] $`\begin{pmatrix} * & 0 \\ 0 & * \end{pmatrix} \cup \begin{pmatrix} 0 & * \\ * & 0 \end{pmatrix}\subseteq \GL_2(\Z/N\Z)` that is split at every prime dividing $`N`. As a moduli space it parameterizes pairs $`(E,\{C,D\})` where:

- $`E` is an elliptic curve over $`k`, and

- $`\{C,D\}` is a $`\Gal_k`-stable pair of cyclic subgroups such that $`E[N](\overline{k})\simeq C \oplus D`.  (Neither $`C` nor $`D` need be $`\Gal_k`-stable.)

Depends on: {uses "gl2.cartan"}[] {uses "modcurve"}[]
:::
