import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Varieties" =>

This chapter lists the LMFDB definitions relating to *varieties*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "ag.abelian_surface" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety, TauCeti.AlgebraicGeometry.AbelianVariety.dim, TauCeti.AlgebraicGeometry.AbelianVariety.prod")
*Abelian surface.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.abelian_surface))

An *abelian surface* is an {bpref "ag.abelian_variety"}[abelian variety] of {bpref "ag.dimension"}[dimension] 2.

Examples are given by the product of two {bpref "ec"}[elliptic curves], or the {bpref "ag.jacobian"}[Jacobian] of a curve of {bpref "ag.curve.genus"}[genus] 2.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.curve.genus"}[] {uses "ag.dimension"}[] {uses "ag.jacobian"}[] {uses "ec"}[]
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

:::definition "ag.conductor"
*Conductor of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.conductor))

The *conductor* of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over $`\Q` is a positive integer $`N` whose prime factors are the primes $`p` where $`A` has bad reduction. The power to which $`p` divides $`N` depends on the type of bad reduction; it can be expressed in terms of ramification in the $`\ell`-adic representation associated to $`A` for any prime $`\ell \ne p`.

The conductor of an abelian variety over a number field is defined similarly; it is an ideal that is a product of positive powers of the prime ideals where $`A` has bad reduction.  The conductor of a curve $`C` over a number field is defined to be the conductor of the {bpref "ag.jacobian"}[Jacobian] of $`C`.

Isogenous abelian varieties have the same conductor.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[]
:::

:::definition "ag.cyclic_trigonal" (lean := "AlgebraicGeometry.Scheme.IsCyclicTrigonalCurveOver, TauCeti.IsCyclicTrigonalFunctionField, TauCeti.IsTrigonalAutomorphism, TauCeti.isCyclicTrigonalFunctionField_iff_exists_isTrigonalAutomorphism")
*Cyclic trigonal curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.cyclic_trigonal))

An {bpref "ag.curve"}[algebraic curve] $`X` is a *cyclic trigonal curve* if there is an order $`3` subgroup $`H` of its {bpref "g2c.aut_grp"}[automorphism group] such that the {bpref "ag.quotient_curve"}[quotient curve] $`X/H` is isomorphic to $`\mathbb{P}^1`.

A generator of such a subgroup $`H` is called a *trigonal automorphism*.

Depends on: {uses "ag.curve"}[] {uses "ag.quotient_curve"}[] {uses "g2c.aut_grp"}[]
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

:::definition "ag.isolated_point"
*Isolated point.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.isolated_point))

A closed point $`x` on a curve $`C` is isolated if it is not contained in a family of effective degree $`d` divisors parametrized by $`\mathbb{P}^1` or a positive rank abelian variety.
:::

:::definition "ag.kodaira_dimension"
*Kodaira dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.kodaira_dimension))

Let $`X` be a nonsingular complex algebraic variety with canonical divisor $`K`. For each $`d \in \mathbb{Z}_{\geq 0}`, the $`d^\text{th}` plurigenus of $`X` is $`P_d \colonequals \dim H^0(X, K^{\otimes d})`. The global sections of $`K^{\otimes d}` define a rational map

$$`\varphi_d: X \to \mathbb{P}(H^0(X,K^{\otimes d})) \cong \mathbb{P}^{P_d-1} \, .`

The Kodaira dimension $`\kappa(X)` is defined to be $`-1` if $`P_d = 0` for all $`d`, and

$$`\kappa(X) \colonequals \sup_d \, \dim(\varphi_d(X))`

otherwise.
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

:::definition "ag.shimura_variety"
*Shimura variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.shimura_variety))

There are a number of different ways to define a Shimura variety.

One definition starts with connected complex manifolds such that for every point on the manifold there is an involution fixing only that point.  If this manifold is isomorphic to a bounded open subset of $`\C^n` for some $`n`, it is called a Hermitian symmetric domain (or space).

Then, *(connected) Shimura varieties* are quotients of Hermitian symmetric domains by torsion-free subgroups of the group of automorphisms of the domain.
:::

:::definition "ag.splitting_field" (lean := "TauCeti.torusSplittingField, TauCeti.IsTorusSplittingField, TauCeti.IsTorusSplitOver, TauCeti.IsTorusSplittingField.torusSplittingField_eq, TauCeti.torusCommHopfAlgProperty")
*Splitting field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ag.splitting_field))

The *splitting field* of an algebraic torus $`T` is the minimal {bpref "nf.is_galois"}[Galois] extension of its {bpref "ag.base_field"}[base field] over which $`T` becomes isomorphic to a power of the multiplicative group $`\mathbb{G}_m`.

Depends on: {uses "ag.base_field"}[] {uses "nf.is_galois"}[]
:::

:::definition "ag.tate_shafarevich"
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
