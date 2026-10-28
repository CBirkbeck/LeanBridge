import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Shimura curves" =>

This chapter lists the LMFDB definitions relating to *Shimura curves*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "shimcurve"
*Shimura curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve))

Let $`(O,\mu)` be a {bpref "shimcurve.polarized_order"}[polarized quaternion order] in an indefinite division
{bpref "shimcurve.quaternion_algebra"}[quaternion algebra]
over $`\Q` of {bpref "shimcurve.discb"}[discriminant] $`D`.
Let $`\mathcal{H}^\pm \colonequals \C \smallsetminus \R` be the union of the complex
upper and lower half planes. Since $`B` is indefinite, we may
fix an embedding $`B^\times \hookrightarrow \GL_2(\R)`, and so $`B^\times`
acts on $`\mathcal{H}^\pm` by Mobius transformations.

We define

$$`\widehat{B} \colonequals B\otimes_{\Z} \widehat{\Z},`

$$`\widehat{O} \colonequals O\otimes_{\Z} \widehat{\Z}.`

Then $`\widehat{O}^\times` is an open compact subgroup of $`\widehat{B}^\times`.  Let $`N` be a positive integer. We define

$$`\Gamma(\widehat{O},N) \colonequals \ker(\widehat{O}^\times \to
        \modstar{O}{NO}).`

We form the double coset space

$$`X(O;N)^{\text{big}}(\C) \colonequals B^\times\backslash (\mathcal{H}^\pm
        \times \widehat{B}^\times)/\Gamma(\widehat{O},N).`

Here, the group actions are as follows: for
$`\beta \in B^\times`, $`\tau \in \mathcal{H}^\pm`,
$`\widehat{b} \in \widehat{B}^\times`, and $`\widehat{\gamma}
\in \Gamma(\widehat{O},N)`, we define

$$`\beta(\tau,\widehat{b})\widehat{\gamma}
    = (\beta\cdot \tau,\beta\widehat{b}\widehat{\gamma}).`

By work of Shimura and Deligne, $`X(O;N)^{\text{big}}(\C)` is canonically
the complex points of a (possibly geometrically disconnected)
{bpref "ag.curve"}[algebraic curve]
$`X(O;N)^{\text{big}}` over $`\Q`, which we call the
*full level $`N` Shimura curve associated to $`O`*. For example,
when $`N = 1`, the *level $`1` Shimura curve associated to $`O`* can
be identified with the quotient

$$`X(O;1)^{\text{big}}(\C) = O^\times\backslash \mathcal{H}^\pm.`

Let $`H \le` {bpref "shimcurve.aut_pm_mu_o"}[$`\Aut_{\pm\mu}(O)`] $`\ltimes \widehat{O}^\times` be an open
compact subgroup of the {bpref "shimcurve.enhanced_group"}[enhanced semidirect product] of {bpref "shimcurve.level"}[level] $`N`. Then $`H` acts on $`X(O;N)^{\text{big}}` by a finite group
of automorphisms over $`\Q`. We let

$$`\mathfrak{X}_H \colonequals [H\backslash X(O;N)^{\text{big}}]`

be the corresponding stack quotient. The
*(quaternionic) Shimura curve of level $`H`* is the
associated coarse space $`X_H`.

When $`O` is maximal, we write $`X(D;1) \colonequals X(O;1)^{\text{big}}`. When $`O` is
an Eichler order of level $`N`, we write $`X_0(D;N) \colonequals X(O;1)^{\text{big}}`.

Depends on: {uses "ag.curve"}[] {uses "shimcurve.aut_pm_mu_o"}[] {uses "shimcurve.discb"}[] {uses "shimcurve.enhanced_group"}[] {uses "shimcurve.level"}[] {uses "shimcurve.polarized_order"}[] {uses "shimcurve.quaternion_algebra"}[]
:::

:::definition "shimcurve.aut_pm_mu_o" (lean := "Subalgebra.autPmMu, Subalgebra.unitsNormalizer, Subalgebra.NormalizerModScalars")
Let $`(O,\mu)` be a {bpref "shimcurve.polarized_order"}[polarized quaternion order] in an indefinite division
{bpref "shimcurve.quaternion_algebra"}[quaternion algebra]
over $`\Q`. Let $`N_{B^{\times}}(O)=\{\gamma\in B^{\times}:\gamma^{-1}O\gamma=O\}` be the normalizer of $`O` in $`B`. Then the *automorphisms of $`O` preserving the polarization $`\mu` (up to sign)* is defined by $`\Aut_{\pm\mu}(O)=\{\gamma\in N_{B^{\times}}(O)/\Q^{\times}:\gamma^{-1}\mu\gamma=\pm\mu\}`.

Depends on: {uses "shimcurve.polarized_order"}[] {uses "shimcurve.quaternion_algebra"}[]
:::

:::definition "shimcurve.decomposition"
*Isogeny decomposition of the Jacobian of a Shimura curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.decomposition))

As with any {bpref "ag.abelian_variety"}[abelian variety], the {bpref "ag.jacobian"}[Jacobian] $`J_H` of a {bpref "shimcurve"}[Shimura curve] $`X_H` can be {bpref "av.decomposition"}[decomposed] into {bpref "av.simple"}[simple] {bpref "av.isogeny"}[isogeny factors].  For Shimura curves, these simple isogeny factors are modular abelian varieties corresponding to {bpref "cmf.galois_orbit"}[Galois orbits] of {bpref "cmf.weight"}[weight] 2 {bpref "cmf.newform"}[newforms].

We list two types of information about the *isogeny decomposition* of $`J_H`:

- the multiset of dimensions of the simple isogeny factors: $`1^3\cdot 2^2` denotes $`3` factors of {bpref "ag.dimension"}[dimension] $`1` and $`2` factors of dimension $`2`;

- the multiset of newforms corresponding to the modular abelian varieties in the isogeny decomposition, listed by {bpref "cmf.label"}[label]: $`\texttt{11.2.a.a}^3\cdot \texttt{13.2.e.a}^2` denotes five simple isogeny factors, three isogenous to the modular abelian variety corresponding to the newform labelled $`\texttt{11.2.a.a}` and two isogenous to the modular abelian variety corresponding to the newform labelled $`\texttt{13.2.e.a}`.

When $`X_H` has {bpref "modcurve.genus"}[genus] zero, $`J_H` is the trivial abelian variety of dimension zero, and no isogeny decomposition information is listed.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "ag.jacobian"}[] {uses "av.decomposition"}[] {uses "av.isogeny"}[] {uses "av.simple"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.label"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[] {uses "modcurve.genus"}[] {uses "shimcurve"}[]
:::

:::definition "shimcurve.discb" (lean := "QuaternionAlgebra.discriminant, QuaternionAlgebra.IsRamifiedAt, QuaternionAlgebra.IsSplitAt")
*Discriminant of a quaternion algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.discb))

Let $`B` be a {bpref "shimcurve.quaternion_algebra"}[quaternion algebra] over $`\Q`. We say that $`B` is *ramified* at a
prime $`p` if $`B\otimes_{\Q} \Q_p` is a division algebra over
$`\Q_p`; otherwise, we say that $`B` is *split* at $`p`.

The *discriminant* $`\operatorname{disc}(B)` of $`B` is the product of primes $`p` at which $`B` is ramified.

Depends on: {uses "shimcurve.quaternion_algebra"}[]
:::

:::definition "shimcurve.disco" (lean := "Subalgebra.quaternionDisc, Subalgebra.quaternionDiscrd, Subalgebra.quaternionDiscOfBasis, QuaternionAlgebra.reducedTrace, QuaternionAlgebra.reducedTrace_quaternionAlgebra")
*Discriminant of a quaternion order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.disco))

Let $`B` be a {bpref "shimcurve.quaternion_algebra"}[quaternion algebra] over $`\Q`, and let $`O\subset B` be an
{bpref "shimcurve.order"}[order]. Let $`x_1,x_2,x_3,x_4 \in O`
be a $`\Z`-basis of $`O`. The *discriminant* of $`O` is the
integer

$$`\operatorname{disc}(O)
        \colonequals \left|\det(\operatorname{trd}(x_ix_j))_{i,j}\right|.`

where $`\operatorname{trd} : B \to \Q` is the reduced trace.

The *reduced discriminant* of $`O` is the positive integer
$`\operatorname{discrd}(O)` such that

$$`\operatorname{discrd}(O)^2 = \operatorname{disc}(O).`

Depends on: {uses "shimcurve.order"}[] {uses "shimcurve.quaternion_algebra"}[]
:::

:::definition "shimcurve.eichler" (lean := "Subalgebra.IsEichlerOrder, Subalgebra.IsEichlerOrderOfLevel, Subalgebra.IsMaximalQuaternionOrder, Subalgebra.IsQuaternionOrder")
*Eichler Orders.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.eichler))

An *Eichler {bpref "shimcurve.order"}[order]* $`O` inside a {bpref "shimcurve.quaternion_algebra"}[quaternion algebra] $`B` is the intersection of two (not necessarily distinct) maximal orders. Over $`\Q`, the {bpref "shimcurve.disco"}[reduced discriminant] of an Eichler order $`O` is of the form $`\mathrm{disc}(O)=D\cdot M` with $`\gcd(D,M)=1`, in which case we say $`O` is *Eichler of level $`M`*.

Depends on: {uses "shimcurve.disco"}[] {uses "shimcurve.order"}[] {uses "shimcurve.quaternion_algebra"}[]
:::

:::definition "shimcurve.elliptic_points"
*Elliptic point on a Shimura curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.elliptic_points))

An *elliptic point* of a {bpref "shimcurve"}[Shimura curve] $`X_H` is a point with a nontrivial stabilizer group (that can be of order $`2, 3, 4`, or $`6`).

Depends on: {uses "shimcurve"}[]
:::

:::definition "shimcurve.enhanced_group" (lean := "Subalgebra.EnhancedGroup, Subalgebra.completedUnits, Subalgebra.completedUnitsAction")
*Enhanced group associated to a polarized quaternion order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.enhanced_group))

Let $`(O,\mu)` be a {bpref "shimcurve.polarized_order"}[polarized quaternion order].
We define $`\widehat{O} \colonequals O\otimes_{\Z} \widehat{\Z}`. Then
$`\widehat{O}^\times` is a {bpref "gl2.profinite"}[profinite group] with

$$`\widehat{O}^\times = \lim_{\xleftarrow[N]{}} \modstar{O}{NO},`

where $`N` ranges over all positive integers. We define

$$`\Aut_{\pm\mu}(O) \colonequals \{\gamma \in N_{B^\times}(O)/\Q^\times :
        \gamma^{-1}\mu\gamma = \pm \mu\}.`

Then $`\Aut_{\pm\mu}(O)` acts on $`\widehat{O}^\times`.
The *enhanced group (associated to $`(O,\mu)`)* is
the semidirect product
$`\Aut_{\pm\mu}(O)\ltimes \widehat{O}^\times`.

Depends on: {uses "gl2.profinite"}[] {uses "shimcurve.polarized_order"}[]
:::

:::definition "shimcurve.genus"
*Genus of a Shimura curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.genus))

By the *genus* of a {bpref "shimcurve"}[Shimura curve] $`X_H`, we mean the genus of any of its {bpref "ag.geom_component"}[geometric components].

Depends on: {uses "ag.geom_component"}[] {uses "shimcurve"}[]
:::

:::definition "shimcurve.genus_minus_rank"
*Genus-rank difference.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.genus_minus_rank))

The *genus-rank difference* of a {bpref "shimcurve"}[Shimura curve] $`X_H` of positive genus is the integer obtained by subtracting the {bpref "shimcurve.rank"}[analytic rank] of $`X_H` from its {bpref "shimcurve.genus"}[genus].

This difference is of interest because the methods available to compute the set of rational points on $`X_H` depend critically on whether the {bpref "ag.mordell_weil"}[Mordell-Weil rank] of its {bpref "ag.jacobian"}[Jacobian] is less than, equal to, or greater than its genus (one expects the Mordell-Weil rank to equal the analytic rank of $`X_H` and the later is much more feasible to compute).

Depends on: {uses "ag.jacobian"}[] {uses "ag.mordell_weil"}[] {uses "shimcurve"}[] {uses "shimcurve.genus"}[] {uses "shimcurve.rank"}[]
:::

:::definition "shimcurve.gonality"
*$`K`-gonality of a Shimura curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.gonality))

The *$`K`-gonality* $`\gamma` of a {bpref "shimcurve"}[Shimura curve] $`X_H` is the {bpref "ag.gonality"}[gonality] of any of its {bpref "ag.geom_component"}[geometric components] over $`K`.  (The geometric gonality of that component might be smaller than the $`K`-gonality.)

Depends on: {uses "ag.geom_component"}[] {uses "ag.gonality"}[] {uses "shimcurve"}[]
:::

:::definition "shimcurve.index" (lean := "Subgroup.index, Subalgebra.EnhancedGroup")
*Index of a Shimura curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.index))

The *index* of a {bpref "shimcurve"}[Shimura curve]
$`X_H` is the index of the corresponding open compact subgroup
$`H \le \Aut_{\pm\mu}(O)\ltimes \widehat{O}^\times` in the
{bpref "shimcurve.enhanced_group"}[enhanced semidirect product].

Depends on: {uses "shimcurve"}[] {uses "shimcurve.enhanced_group"}[]
:::

:::definition "shimcurve.is_coarse" (lean := "Subalgebra.IsCoarseSubgroup, Subalgebra.EnhancedGroupMod, Subalgebra.autPmMuMul, Subalgebra.autPmMu, Subalgebra.isCoarseSubgroup_iff")
*Is coarse.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.is_coarse))

We say a subgroup $`H\leq\Aut_{\pm\mu}(O)\ltimes(O/NO)^{\times}` is *coarse* if $`H` contains the projection of the kernel of the map $`f: \Aut_{\pm\mu}(O)\ltimes O^{\times}\to N_{B^{\times}}(O)/\Q^{\times}` defined by $`(w,x)\mapsto w\cdot x`.
:::

:::definition "shimcurve.label"
*Label of a Shimura curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.label))

Let $`(O,\mu)` be a {bpref "shimcurve.polarized_order"}[polarized order] in an indefinite
division {bpref "shimcurve.quaternion_algebra"}[quaternion
algebra] $`B` over $`\Q` of {bpref "shimcurve.discb"}[discriminant] $`D`. Let $`H \le \Aut_{\pm\mu}(O)\ltimes \widehat{O}^\times` be an open
compact subgroup of the {bpref "shimcurve.enhanced_group"}[enhanced semidirect product] of {bpref "shimcurve.level"}[level] $`N`. The *label* of the {bpref "shimcurve"}[Shimura Curve] $`X_H` has the form $`\mathtt{D.d.\delta.N.i.g.c.n}`, where

- $`D` is the {bpref "shimcurve.discb"}[discriminant] of $`B`,

- $`d` is the {bpref "shimcurve.disco"}[reduced discriminant] of $`O`, which is omitted when $`O` is maximal,

- $`\delta` is the {bpref "shimcurve.nrdmu"}[degree] of the polarized element $`\mu`,

- $`N` is the {bpref "shimcurve.level"}[level] of $`H`,

- $`i` is the {bpref "shimcurve.index"}[index] of $`H`,

- $`g` is the {bpref "shimcurve.genus"}[genus] of $`X_H`,

- $`c` is a base-26 ordinal that uniquely identifies the Gassman class of $`H` among groups of the same level, index, and genus, and

- $`n` is a positive integer that distinguishes nonconjugate subgroups of the same level, index, genus, and Gassmann class.

Depends on: {uses "shimcurve"}[] {uses "shimcurve.discb"}[] {uses "shimcurve.disco"}[] {uses "shimcurve.enhanced_group"}[] {uses "shimcurve.genus"}[] {uses "shimcurve.index"}[] {uses "shimcurve.level"}[] {uses "shimcurve.nrdmu"}[] {uses "shimcurve.polarized_order"}[] {uses "shimcurve.quaternion_algebra"}[]
:::

:::definition "shimcurve.level" (lean := "Subalgebra.enhancedGroupLevel, Subalgebra.enhancedGroupKernel, Subalgebra.enhancedGroupKernel_le_of_level_pos")
*Level of a Shimura curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.level))

Let $`(O,\mu)` be a {bpref "shimcurve.polarized_order"}[polarized quaternion order], and let
$`G \colonequals \Aut_{\pm\mu}(O)\ltimes \widehat{O}^\times` be the corresponding
{bpref "shimcurve.enhanced_group"}[enhanced semidirect product].
Let $`H \le G` be an open compact subgroup. The *level* of
$`H` is the least positive integer $`N` such that $`H` contains

$$`\ker(\widehat{O}^\times \to \modstar{O}{NO}).`

The *level* of a {bpref "shimcurve"}[Shimura curve]
$`X_H` is the level of the corresponding open compact subgroup
$`H`.

Depends on: {uses "shimcurve.enhanced_group"}[] {uses "shimcurve.polarized_order"}[]
:::

:::definition "shimcurve.local_obstruction"
*Local obstruction.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.local_obstruction))

A {bpref "shimcurve"}[Shimura curve] $`X_H/\Q` has a *local obstruction* (to rational points) if it has no real points, or if it has no $`\Q_p`-points for some prime $`p`.

When $`X` has {bpref "shimcurve.genus"}[genus] $`0` the absence of local obstructions guarantees the existence of rational points, but this is not true in general.

Depends on: {uses "shimcurve"}[] {uses "shimcurve.genus"}[]
:::

:::definition "shimcurve.nrdmu" (lean := "PolarizedQuaternionOrder.degree, QuaternionAlgebra.reducedNorm, QuaternionAlgebra.reducedNorm_quaternionAlgebra")
*Polarization degree of a polarized order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.nrdmu))

Let $`(O,\mu)` be a {bpref "shimcurve.polarized_order"}[polarized quaternion order]. The *polarization degree*
$`\deg(\mu)` is the square-free part of the integer
$`\operatorname{nrd}(\mu)/\operatorname{discrd}(O)`.
Here, $`\operatorname{nrd} : B \to \Q` is the reduced norm,
and $`\operatorname{discrd}(O)` is the {bpref "shimcurve.disco"}[reduced discriminant] of $`O`.

Depends on: {uses "shimcurve.disco"}[] {uses "shimcurve.polarized_order"}[]
:::

:::definition "shimcurve.order" (lean := "Subalgebra, Subalgebra.toSubmodule, Submodule.IsLattice")
*Quaternion order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.order))

Let $`B` be a {bpref "shimcurve.quaternion_algebra"}[quaternion algebra] over $`\Q`. An *order* $`O\subset B` is a
$`\Z`-lattice in $`B` that is also a subring of $`B` (where we
require $`1 \in O`). We say that $`O` is *maximal* if it is
not properly contained in another order of $`B`.

Unlike {bpref "nf.order"}[orders in number fields], there
is never a unique maximal order in a rational quaternion
algebra; however, the number of $`B^\times`-conjugacy classes is finite (and in many cases, there is exactly one $`B^\times`-conjugacy class).

Depends on: {uses "nf.order"}[] {uses "shimcurve.quaternion_algebra"}[]
:::

:::definition "shimcurve.polarized_order" (lean := "PolarizedQuaternionOrder, Subalgebra.IsPolarization, QuaternionAlgebra.IsIndefinite, QuaternionAlgebra.IsDivision")
*Polarized quaternion order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.polarized_order))

Let $`O` be an {bpref "shimcurve.order"}[order] in an indefinite
division {bpref "shimcurve.quaternion_algebra"}[quaternion
algebra] $`B` over $`\Q`. Let $`\operatorname{trd} : B \to \Q`
be the reduced trace. A *polarization* of $`O` is an element
$`\mu \in B^\times` such that $`\mu^2 \in \Z_{<0}` and for all
$`x \in O`, we have $`\operatorname{trd}(\mu x) \in \Z`.

A *polarized order* is a pair $`(O,\mu)` where $`O` is an
order in an indefinite division quaternion algebra $`B` over
$`\Q` and $`\mu \in B^\times` is a polarization of $`O`.

Depends on: {uses "shimcurve.order"}[] {uses "shimcurve.quaternion_algebra"}[]
:::

:::definition "shimcurve.quaternion_algebra" (lean := "QuaternionAlgebra, CSA, Algebra.IsCentral, IsSimpleRing, TauCeti.Algebra.IsSplittingField, TauCeti.QuaternionAlgebra.nonempty_algEquiv_matrix_tfae")
*Quaternion algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.quaternion_algebra))

Let $`F` be a {bpref "ring.field"}[field]. A *quaternion algebra* over $`F` is a central simple algebra of dimension 4 over $`F`.

A quaternion algebra
$`B` over a field $`F` of
{bpref "ring.characteristic"}[characteristic] not equal
to 2 has elements $`i,j \in B` such that $`\{1,i,j,ij\}` is an
$`F`-basis for $`B`, and such that there exists $`a,b \in F^\times`
with $`i^2 = a`, $`j^2 = b`, and $`ji = -ij`. In this case, we
write

$$`B = \left(\frac{a,b}{F}\right).`

We set $`k = ij`.

We say that a quaternion algebra $`B` over $`F` is *split* if $`B` is isomorphic to the matrix algebra $`\operatorname{M}_2(F)`, and we say $`B` is *nonsplit* otherwise.

If $`B` is a quaternion algebra over $`\Q`, we say that $`B` is *indefinite* if $`B\otimes_{\Q} \R` is a split quaternion algebra over $`\R`, and we say $`B` is *definite* otherwise.

Depends on: {uses "ring.characteristic"}[] {uses "ring.field"}[]
:::

:::definition "shimcurve.rank"
*Analytic rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.rank))

The *analytic rank* of a {bpref "shimcurve"}[Shimura curve] is the order of vanishing of its {bpref "lfunction"}[L-function] at its {bpref "lfunction.central_point"}[central point], which is equal to the sums of the {bpref "cmf.analytic_rank"}[analytic ranks] of the L-functions of the {bpref "av.simple"}[simple] modular {bpref "ag.abelian_variety"}[abelian varieties] corresponding to {bpref "cmf.galois_orbit"}[Galois orbits] of {bpref "cmf.newform"}[modular forms] that are the {bpref "av.decomposition"}[isogeny factors] of its {bpref "ag.jacobian"}[Jacobian].

The {bpref "ec.bsdconjecture"}[Birch and Swinnerton-Dyer] conjecture for modular abelian varieties implies that the analytic rank is equal to the {bpref "ag.mordell_weil"}[Mordell-Weil rank] of the Jacobian.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "ag.mordell_weil"}[] {uses "av.decomposition"}[] {uses "av.simple"}[] {uses "cmf.analytic_rank"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "ec.bsdconjecture"}[] {uses "lfunction"}[] {uses "lfunction.central_point"}[] {uses "shimcurve"}[]
:::

:::definition "shimcurve.simple"
*Simple Shimura curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/shimcurve.simple))

A {bpref "shimcurve"}[Shimura curve] $`X_H` is *simple* if its {bpref "ag.jacobian"}[Jacobian] is a {bpref "av.simple"}[simple] {bpref "ag.abelian_variety"}[abelian variety].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "av.simple"}[] {uses "shimcurve"}[]
:::
