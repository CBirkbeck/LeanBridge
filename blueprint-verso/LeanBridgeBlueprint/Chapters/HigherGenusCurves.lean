import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Higher genus curves" =>

This chapter lists the LMFDB definitions relating to *higher genus curves*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "curve.highergenus.aut.braid_equivalence" (lean := "Hurwitz.braidOperation, Hurwitz.braidOperationGroup, Hurwitz.braidEquivalence, Hurwitz.braidMove")
*Braid Equivalence.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.braid_equivalence))

Given a group $`G`, the *braid operations* on an $`n`-tuples of elements in $`G` are the maps

$$`Q_i: (g_1, \ldots, g_{i-1}, g_i, g_{i+1}, \ldots, g_n) \to (g_1, \ldots g_{i-1}, g_i+1, g_{i+1}^{-1}g_ig_{i+1}, \ldots, g_n)`

and their inverses, for $`1 \leq i \leq n-1`.  These operations generate an action on {bpref "curve.highergenus.aut.generatingvector"}[generating vectors] of one {bpref "curve.highergenus.aut.refinedpassport"}[refined passport].

Two generating vectors from the same refined passport are considered  *braid equivalent* if they are in the same orbit under this action.

Depends on: {uses "curve.highergenus.aut.generatingvector"}[] {uses "curve.highergenus.aut.refinedpassport"}[]
:::

:::definition "curve.highergenus.aut.branchpoints" (lean := "MulAction.branchPoints, MulAction.mk_mem_branchPoints_iff, MulAction.finite_branchPoints, MulAction.finite_branchPoints_of_subgroup, TauCeti.Diff")
*Branch Points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.branchpoints))

If $`G` is a finite group of automorphisms acting on a {bpref "ag.riemann_surface"}[Riemann surface] $`X`, and $`\phi\colon X\to X/G` is the natural projection to the quotient $`X/G` (the compact Riemann surface whose points are the $`G`-orbits of $`X`), then all but finitely many fibers of the map $`\phi` have cardinality $`d:=|G|`.

The points $`P` of $`X/G` whose fibers $`\phi^{-1}(P)` have cardinality strictly less than $`d` are called *branch points*.

Depends on: {uses "ag.riemann_surface"}[]
:::

:::definition "curve.highergenus.aut.dimension" (lean := "MulAction.signatureDimension, MulAction.signatureDimension_signature, MulAction.signature")
*Dimension of a family of curves.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.dimension))

Given a group of automorphisms $`G` acting on a curve $`X/\C` of genus $`g`, with {bpref "curve.highergenus.aut.signature"}[signature] $`[g_0;m_1, \ldots, m_r]`, the *dimension* of the family of curves with this signature is $`3g_0+r-3`, where $`r` is the number of {bpref "curve.highergenus.aut.branchpoints"}[branch points] of the map $`X \to X/G` and $`g_0` is the {bpref "curve.highergenus.aut.quotientgenus"}[quotient genus].

Depends on: {uses "curve.highergenus.aut.branchpoints"}[] {uses "curve.highergenus.aut.quotientgenus"}[] {uses "curve.highergenus.aut.signature"}[]
:::

:::definition "curve.highergenus.aut.full" (lean := "TauCeti.Diff")
*Full group of automorphisms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.full))

A group of automorphisms $`G` acting on a curve $`X` is necessarily a subgroup of the {bpref "g2c.aut_grp"}[automorphism group] $`\Aut(X)`, but need not equal $`\Aut(X)`.  When $`G=\Aut(X)` we say that $`G` is the *full group of automorphisms*.

Depends on: {uses "g2c.aut_grp"}[]
:::

:::definition "curve.highergenus.aut.generatingvector"
*Generating Vector.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.generatingvector))

The *generating vector* of a group of automorphisms $`G` acting on a compact {bpref "ag.riemann_surface"}[Riemann surface] $`X` is a list of generators for the {bpref "curve.highergenus.aut.monodromy"}[monodromy group] of $`G` obtained by taking the image of the {bpref "curve.highergenus.aut.generators"}[standard generators] for $`\pi_1(Y-B,y_0)` under the image of the map $`\rho\colon \pi_1(Y-B,y_0)\to S_d` used to define the monodromy group, where $`B` is the set of {bpref "curve.highergenus.aut.branchpoints"}[branch points] of the projection $`\phi\colon X\to Y=X/G`, and $`y_0` is any point on $`Y` that is not in $`B`.

Depends on: {uses "ag.riemann_surface"}[] {uses "curve.highergenus.aut.branchpoints"}[] {uses "curve.highergenus.aut.generators"}[] {uses "curve.highergenus.aut.monodromy"}[]
:::

:::definition "curve.highergenus.aut.generators" (lean := "TauCeti.RiemannSurface.IsStandardGeneratingSystem, TauCeti.RiemannSurface.IsStandardGenerator, TauCeti.RiemannSurface.IsolatingDisc, TauCeti.RiemannSurface.IsolatingDisc.loop, TauCeti.RiemannSurface.exists_isStandardGenerator")
*Standard generators.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.generators))

Let $`Y` be a compact {bpref "ag.riemann_surface"}[Riemann surface] of genus $`0`, let $`B` be a finite set of points in $`Y`, and let $`y_0` be a point in $`Y` that is not in $`B`.

*Standard generators* for the fundamental group $`\pi_1(Y - B, y_0)` are obtained by taking the homotopy classes of loops indexed by $`b\in B` that  start at $`y_0` and
make a counterclockwise loop about $`b` containing no other elements of
$`B`.  This construction associates a generator to each element of $`B` (there will typically be relations among these generators).

Depends on: {uses "ag.riemann_surface"}[]
:::

:::definition "curve.highergenus.aut.group_action" (lean := "TauCeti.Diff")
*A group acting on a compact Riemann Surface.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.group_action))

A *group $`G` acts on a compact Riemann surface $`X`* if there is an injective homomorphism from $`G` to the {bpref "g2c.aut_grp"}[group of automorphisms] of $`X`, i.e. a homomorphism $`\phi: G \hookrightarrow \mathrm{Aut}(X)`.

Equivalently, a group $`G` acts on $`X` if there is a {bpref "group.fuchsian"}[Fuchsian group] $`\Gamma` and a surjective homomorphism $`\eta: \Gamma \to G` with $`\ker( \eta)` isomorphic to the fundamental group of $`X`.

Depends on: {uses "g2c.aut_grp"}[] {uses "group.fuchsian"}[]
:::

:::definition "curve.highergenus.aut.groupalgebradecomp"
*Group algebra decomposition of Jacobian varieties.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.groupalgebradecomp))

Given a curve $`X`, the group action of the {bpref "g2c.aut_grp"}[automorphism group]  $`G=`Aut$`(X)` on $`X` may allow one to decompose its {bpref "ag.jacobian"}[Jacobian] $`J` as a product of abelian varieties of lower dimension. Idempotent relations in the group ring $`\mathbb{Q}[G]` correspond, via  a  natural map of  $`\mathbb{Q}`-algebras $`\rho:  \mathbb{Q}[G] \to \text{End}(J) \otimes_{\mathbb{Z}} \mathbb{Q}`, to
factorizations of the Jacobian variety into abelian varieties that are the images of the Jacobian under the {bpref "ag.endomorphism_ring"}[endomorphisms] determined by those idempotents. The dimensions of the factors in this *group algebra decomposition* are computed as inner products of certain characters of $`G` (and are thus canonical).

Note: factors in the group algebra decomposition need not be simple (it may be possible to decompose them further), and factors of the same dimension may be {bpref "av.isogeny"}[isogenous].

For further details see [the source of the automorphisms of curves data](http://www.lmfdb.org//HigherGenus/C/Aut/Source).

Depends on: {uses "ag.endomorphism_ring"}[] {uses "av.isogeny"}[] {uses "ag.jacobian"}[] {uses "g2c.aut_grp"}[]
:::

:::definition "curve.highergenus.aut.monodromy" (lean := "MulAction.monodromyGroup, MulAction.unbranchedProjection, MulAction.isCoveringMap_unbranchedProjection, MulAction.card_fiber_unbranchedProjection, MulAction.branchPoints")
*Monodromy Group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.monodromy))

Let $`G` be a group of automorphisms acting on a compact {bpref "ag.riemann_surface"}[Riemann surface] $`X` of genus $`g\ge 2`, let $`\phi` be the natural projection from $`X` to the quotient $`Y:=X/G`, let $`\mathcal B=\{y_1,\ldots,y_r\}` be the {bpref "curve.highergenus.aut.branchpoints"}[branch points] of $`\phi`, and let us fix a base point $`y_0 \in Y-\mathcal{B}`. The fiber $`\phi^{-1}(y_0)` consists of $`d:=|G|` points, say
$`\phi^{-1}(y_0)=:\{x_1, \ldots, x_d\} \subset X`.

Consider an element $`\gamma` of the fundamental group $`\pi_1(Y-\mathcal{B},y_0)` (homotopy classes of loops in $`Y-\mathcal{B}` with base point $`y_0`).
For each $`x_i\in \phi^{-1}(y_0),` the loop $`\gamma` lifts to a path in $`X`  which starts at $`x_i` and ends at some $`x_j \in \phi^{-1}(y_0)` uniquely determined by $`\gamma`.
This defines a permutation $`\sigma_{\gamma}` of the set $`\{x_1,\ldots,x_d\}` corresponding to a transitive right action of $`\pi_1(Y-\mathcal{B},y_0)`, and the map $`\gamma\mapsto \sigma_{\gamma}` defines a group homomorphism $`\rho\colon\pi_1(Y-\mathcal{B},y_0) \to S_d`.

The image of $`\rho` is the *(geometric) monodromy group* of $`G`; it is a transitive permutation group of degree $`d` and does not depend on the choice of the base point $`y_0`.

Depends on: {uses "ag.riemann_surface"}[] {uses "curve.highergenus.aut.branchpoints"}[]
:::

:::definition "curve.highergenus.aut.quotientgenus" (lean := "TauCeti.genus")
*Quotient genus.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.quotientgenus))

For a group of automorphisms $`G` acting on a curve $`X`, the {bpref "ag.curve.genus"}[genus] of the quotient curve $`X/G` is the *quotient genus* of $`G`.

Depends on: {uses "ag.curve.genus"}[]
:::

:::definition "curve.highergenus.aut.refinedpassport" (lean := "RefinedPassport, RefinedPassport.ofGeneratingVector, RefinedPassport.ofGeneratingVector_eq_ofGeneratingVector_iff")
*Refined passport.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.refinedpassport))

Let $`G` be a group of automorphisms acting on a compact {bpref "ag.riemann_surface"}[Riemann surface] $`X` of genus $`g`,  let  $`(s_1, \ldots, s_n)` be a {bpref "curve.highergenus.aut.generatingvector"}[generating vector] for the action of $`G` on $`X`, and let $`\mathcal{C}=(C_1, \ldots, C_n)` be the corresponding vector of conjugacy classes of $`G`.

The tuple $`(g,G,\mathcal{C})` is called a *refined passport* (some authors say that $`X` is of ramification type $`(g,G,\mathcal{C})`).

Depends on: {uses "ag.riemann_surface"}[] {uses "curve.highergenus.aut.generatingvector"}[]
:::

:::definition "curve.highergenus.aut.signature"
*Signature of a group action on a curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.signature))

Let $`G` be a group of automorphisms acting on a curve $`X/\C` of genus at least $`2`, let $`g_0` be the {bpref "curve.highergenus.aut.quotientgenus"}[genus of the quotient] $`Y:=X/G`, and let $`B` be the set of {bpref "curve.highergenus.aut.branchpoints"}[branch points] of the projection $`\phi\colon X\to Y`. For each {bpref "curve.highergenus.aut.generators"}[standard generator] for $`\pi_1(Y-B,y_0)` corresponding to the elements of $`B=\{y_1,\ldots,y_r\}` and a fixed pre-image of $`y_0`, there is a lift of that loop to a path in $`X - \phi^{-1}(B)` starting at the particular pre-image of $`y_0`. The lifted path ends at some (possibly different) pre-image of $`y_0`. Varying the particular pre-images of $`y_0` and then recording the end point corresponding to that starting point induces a permutation on those pre-images.

We define $`m_1 \leq m_2 \leq \ldots \leq m_r` to be the orders of the permutations described above, one for each of the $`r` standard generators.

The sequence of integers $`[g_0; m_1, \ldots, m_r]` is the *signature* of the group action.

Depends on: {uses "curve.highergenus.aut.branchpoints"}[] {uses "curve.highergenus.aut.generators"}[] {uses "curve.highergenus.aut.quotientgenus"}[]
:::

:::definition "curve.highergenus.aut.topological_equivalence"
*Topological Equivalence.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/curve.highergenus.aut.topological_equivalence))

Given a group $`G` {bpref "curve.highergenus.aut.group_action"}[acting] on a compact Riemann surface $`X` by the maps $`\phi_1: G \hookrightarrow \mathrm{Aut}(X)` and $`\phi_2: G \hookrightarrow \mathrm{Aut}(X)`, then $`\phi_1` and $`\phi_2` are *topologically equivalent* if there is an automorphism $`\omega` of $`G` and an orientation preserving homeomorphism $`h: X \to X` so that

$$`\phi_2(g)=h \phi_1(\omega(g)) h^{-1} \text{ for all } g \in G.`

Equivalently, if the actions are described as surjective homomorphisms $`\eta_1: \Gamma \to G` and $`\eta_2: \Gamma \to G` from a  {bpref "group.fuchsian"}[Fuchsian group] $`\Gamma` with kernel isomorphic to the fundamental group of $`X`, these actions are *topologically equivalent* if there is an automorphism $`\omega` of $`G`	and a homeomorphism $`h` of the upper half plane $`\mathbb{H}` normalizing $`\Gamma` such that the following diagram commutes.

$$`\begin{matrix}\Gamma & \xrightarrow{\mathit{\eta_1}}& G \\ \Big\downarrow h & & \Big\downarrow \omega  \\ \Gamma & \xrightarrow{\mathit{\eta_2}}& G  \end{matrix}`

Depends on: {uses "curve.highergenus.aut.group_action"}[] {uses "group.fuchsian"}[]
:::
