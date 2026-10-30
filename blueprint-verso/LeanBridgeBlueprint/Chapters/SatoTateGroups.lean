import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Sato-Tate groups" =>

This chapter lists the LMFDB definitions relating to *Sato-Tate groups*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "st_group.ambient" (lean := "SatoTateGroup.ambient, SatoTateGroup.ambientGroup, Matrix.satoTateForm, Matrix.reindex_J_eq_satoTateForm, SatoTateGroup.mem_ambientGroup_iff_of_even")
*Ambient group of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.ambient))

A {bpref "st_group.definition"}[Sato-Tate group] of {bpref "st_group.weight"}[weight] $`w` and {bpref "st_group.degree"}[degree] $`d` is a subgroup of either:

- $`\mathrm{USp}(d)`, if $`w` is odd (in which case $`d` must be even);

- $`\mathrm{O}(d)`, if $`w` is even (in which case $`d` may be even or odd).

Here $`\mathrm{USp}(d)\subseteq \mathrm{GL}_d(\mathbb{C})` denotes the group of $`d\times d` complex matrices that are both unitary ($`\bar A A^{\rm t}=I`) and symplectic ($`A^{\rm t}\Omega A = \Omega` for some fixed symplectic form $`\Omega`), while $`\mathrm{O}(d)\subseteq\mathrm{GL}_d(\mathbb{C})` is the group of $`d\times d` orthogonal matrices ($`AA^{\rm t}=I`).  Both are classical real Lie groups.

In either case, the group $`\mathrm{USp}(d)` or $`\mathrm{O}(d)` is called the *ambient group* of the Sato-Tate group.

Depends on: {uses "st_group.definition"}[] {uses "st_group.degree"}[] {uses "st_group.weight"}[]
:::

:::definition "st_group.component_group" (lean := "Subgroup.connectedComponentOfOne, Subgroup.normal_connectedComponentOfOne, QuotientGroup.totallyDisconnectedSpace_connectedComponentOfOne")
*Component group of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.component_group))

The *component group* of a {bpref "st_group.definition"}[Sato-Tate group] $`G` is the quotient $`G/G^0` of $`G` by its {bpref "st_group.identity_component"}[identity component] $`G^0`, which is a normal subgroup of finite index.

If $`G` is the Sato-Tate group of a motive defined over a {bpref "nf"}[number field] $`K`, then the component group $`G/G^0` is canonically isomorphic to the {bpref "nf.galois_group"}[Galois group] of a finite extension $`L/K`. For the motive attached to an {bpref "ag.abelian_variety"}[abelian variety] $`A` of {bpref "ag.dimension"}[dimension] at most 3, $`L` is the smallest field over which all endomorphisms of $`A_{\overline{K}}` (the {bpref "ag.base_change"}[base change] of $`A` to an algebraic closure of $`K`) are defined.

Component groups are named according to their isomorphism type.  This does not determine them uniquely; one can obtain a more explicit description by examining the list of generators.  Common notations used in component group names include:

- $`C_n`, the {bpref "group.cyclic"}[cyclic group] of order $`n`;

- $`D_n`, the {bpref "group.dihedral"}[dihedral group] of order $`2n`;

- $`A_n`, the {bpref "group.alternating"}[alternating group] on $`n` letters;

- $`S_n`, the {bpref "group.symmetric"}[symmetric group] on $`n` letters.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_change"}[] {uses "ag.dimension"}[] {uses "group.alternating"}[] {uses "group.cyclic"}[] {uses "group.dihedral"}[] {uses "group.symmetric"}[] {uses "nf"}[] {uses "nf.galois_group"}[] {uses "st_group.definition"}[] {uses "st_group.identity_component"}[]
:::

:::definition "st_group.components" (lean := "Subgroup.connectedComponentOfOne, connectedComponent, smul_connectedComponent, Subgroup.normal_connectedComponentOfOne, ConnectedComponents")
*Components of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.components))

As a compact Lie group, a {bpref "st_group.definition"}[Sato-Tate group] $`G` need not be {bpref "st_group.connected"}[connected], but it necessarily consists of a finite set of components, each of which is a coset of the {bpref "st_group.identity_component"}[identity component] $`G^0`, a normal subgroup.  The number of components is equal to the cardinality of the {bpref "st_group.component_group"}[component group] $`G/G^0`.

Depends on: {uses "st_group.component_group"}[] {uses "st_group.connected"}[] {uses "st_group.definition"}[] {uses "st_group.identity_component"}[]
:::

:::definition "st_group.connected" (lean := "ConnectedSpace, Subgroup.connectedComponentOfOne_eq_top")
*Connected Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.connected))

A {bpref "st_group.definition"}[Sato-Tate group] $`G` is *connected* if it is connected as a topological group.  In this case it is equal to its {bpref "st_group.identity_component"}[identity component] $`G^0` and the {bpref "st_group.component_group"}[component group] $`G/G^0` is trivial.

Depends on: {uses "st_group.component_group"}[] {uses "st_group.definition"}[] {uses "st_group.identity_component"}[]
:::

:::definition "st_group.degree" (lean := "SatoTateGroup, SatoTateGroup.degree, SatoTateGroup.natDegree_charpoly")
*Degree of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.degree))

The *degree* $`d` of a {bpref "st_group.definition"}[Sato-Tate group] is the degree of the characteristic polynomials of its elements, equivalently, the {bpref "ag.dimension"}[dimension] of the $`d\times d` matrices it contains.

For an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a {bpref "nf"}[number field], the degree $`d` of its Sato-Tate group is twice its dimension $`g` as an abelian variety (if $`A=\mathrm{Jac}(C)` is the {bpref "ag.jacobian"}[Jacobian] of a curve $`C`, then $`g` is also the genus of $`C`).  The degree $`d=2g` is then also the degree of the characteristic polynomials of the Frobenius endomorphism of the reductions of $`A` modulo good primes.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.dimension"}[] {uses "ag.jacobian"}[] {uses "nf"}[] {uses "st_group.definition"}[]
:::

:::definition "st_group.first_a2_moment" (lean := "SatoTateGroup.firstA2Moment, SatoTateGroup.charpolyCoeff")
*First $`a_2` moment.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.first_a2_moment))

The *first $`a_2` moment* of a {bpref "st_group.definition"}[Sato-Tate group] $`G` is the expected value of the quadratic coefficient of the characteristic polynomial of a random element of $`G` (under its {bpref "group.haar_measure"}[Haar measure]).

When $`G` is the Sato-Tate group of an {bpref "ag.abelian_variety"}[abelian variety], the first $`a_2` moment is equal to the rank of its Néron–Severi group .

Depends on: {uses "ag.abelian_variety"}[] {uses "group.haar_measure"}[] {uses "st_group.definition"}[]
:::

:::definition "st_group.fourth_trace_moment" (lean := "SatoTateGroup.fourthTraceMoment, SatoTateGroup.traceMoment")
*Fourth trace moment.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.fourth_trace_moment))

The *fourth trace moment* of a {bpref "st_group.definition"}[Sato-Tate group] $`G` is the expected value of the fourth power of the trace of a random element of $`G` (under the {bpref "group.haar_measure"}[Haar measure]).

By a result known as "Larsen's alternative" , if the fourth trace moment is less than or equal to 5 then $`G` is irreducible, and for $`G` of odd {bpref "st_group.weight"}[weight], the fourth trace moment is 3 when $`G=\mathrm{USp}(2g)` and greater than 3 otherwise.

Depends on: {uses "group.haar_measure"}[] {uses "st_group.definition"}[] {uses "st_group.weight"}[]
:::

:::definition "st_group.generators" (lean := "SatoTateGroup.IsGeneratingSet, SatoTateGroup.isGeneratingSet_iff_closure_image_eq_top, SatoTateGroup.IsGeneratingSet.exists_mem_closure_mk_eq, SatoTateGroup.IsGeneratingSet.closure_eq_top, Subgroup.connectedComponentOfOne")
*Generators of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.generators))

The generators of a {bpref "st_group.definition"}[Sato-Tate group] $`G` are a set $`S` of matrices $`g` that together with the identity component $`G^0` generate $`G`.

The group $`\langle S\rangle` generated by $`S` necessarily contains representatives of every element of the {bpref "st_group.component_group"}[component group] but it will typically be larger (but not when $`G^0` is the trivial group, as in {bpref "st_group.weight"}[weight] $`0`).

Depends on: {uses "st_group.component_group"}[] {uses "st_group.definition"}[] {uses "st_group.weight"}[]
:::

:::definition "st_group.hodge_circle" (lean := "SatoTateGroup.IsHodgeCircle, SatoTateGroup.HasHodgeEigenvalues")
*Hodge circle.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.hodge_circle))

For a {bpref "st_group.definition"}[Sato-Tate group] $`G` of {bpref "st_group.degree"}[degree] $`d` and {bpref "st_group.weight"}[weight] $`w` a *Hodge circle* is a continuous homomorphism

$$`h\colon \mathrm{U}(1)\to G^0`

for which there exist nonnegative integers $`h^{p,q}` satisfying $`\sum h^{p,q}=d` with $`p,q` varying over integers in $`[0,w]` such that

- $`h(u)` has eigenvalues $`u^{p-q}` with multiplicity $`h^{p,q}` for all $`u\in \mathrm{U}(1)`;

- the conjugates of the image of $`h` generate a dense subgroup of $`G^0`.

When $`G` is the Sato-Tate group of a motive $`X` of weight $`w`, the $`h^{p,q}` are the Hodge numbers of $`X`.  For a $`d`-dimensional abelian variety $`X` we necessarily have $`h^{0,1}=h^{1,0}=d`.

Depends on: {uses "st_group.definition"}[] {uses "st_group.degree"}[] {uses "st_group.weight"}[]
:::

:::definition "st_group.identity_component" (lean := "Subgroup.connectedComponentOfOne, Subgroup.normal_connectedComponentOfOne")
*Identity component of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.identity_component))

The *identity component* of a {bpref "st_group.definition"}[Sato-Tate group] $`G` is the connected component $`G^0` of the identity element.  As a compact Lie group, the identity component $`G^0` is a normal subgroup of finite index.  The quotient $`G/G^0` is the {bpref "st_group.component_group"}[component group] of $`G`.

Depends on: {uses "st_group.definition"}[]
:::

:::definition "st_group.index" (lean := "Subgroup.index, Subgroup.connectedComponentOfOne, Subgroup.normal_connectedComponentOfOne")
*Index of the identity component.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.index))

The identity component $`G^0` of a compact Lie group $`G` is a normal subgroup of finite index; this index is equal to the cardinality of the {bpref "st_group.component_group"}[component group] $`G/G^0`.

Depends on: {uses "st_group.component_group"}[]
:::

:::definition "st_group.label"
*Sato-Tate group labels.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.label))

In general {bpref "st_group.definition"}[Sato-Tate group] labels have the form $`w.d.A.c.ns`, where

- $`w` is the {bpref "st_group.weight"}[weight] (nonnegative integer);

- $`d` is the {bpref "st_group.degree"}[degree] (positive integer, even if $`w` is odd);

- $`A` is an uppercase letter that identifies the {bpref "st_group.identity_component"}[identity component] among those of weight $`w` and degree $`d` (ordered by {bpref "st_group.moment_simplex"}[moment simplex]);

- $`c` is the number of {bpref "st_group.components"}[components] (positive integer);

- $`n` is the second digit of the GAP id $`[c,n]` of the {bpref "st_group.component_group"}[component group] (positive integer);

- $`s` is a lowercase letter used to distinguish groups for which all the preceding invariants coincide (ordered by moment simplex).

When $`w=0` we the identity component is necessarily trivial and the $`A` is omitted.  When $`w=0` and $`d=1` there is exactly one Sato-Tate group for each value of $`c` and we may omit $`n` and $`s`.

Depends on: {uses "st_group.component_group"}[] {uses "st_group.components"}[] {uses "st_group.definition"}[] {uses "st_group.degree"}[] {uses "st_group.identity_component"}[] {uses "st_group.moment_simplex"}[] {uses "st_group.weight"}[]
:::

:::definition "st_group.moment_matrix"
*Moment matrix.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.moment_matrix))

The *moment matrix* of a {bpref "st_group.definition"}[Sato-Tate group] $`G` is the matrix of moments $`\mathrm{E}[\chi_i\chi_j]` with $`\chi_i` and $`\chi_j` ranging over the irreducible characters of the {bpref "st_group.ambient"}[ambient group] that contains $`G`;  The irreducible characters are ordered according to their highest weight, which can be written as a monomial in the elementary symmetric functions; these are ordered by (unweighted) degree and then by reverse lexicographic order of exponent vectors.  The *diagonal* of the moment matrix is the vector $`(\mathrm{E}[\chi_i^2])`.

In the symplectic case the irreducible characters of $`\mathrm{USp}(2g)` can be explicitly computed via the Brauer-Klimyk formula using the algorithm of Shieh .  Each character $`\chi` is then an integer polynomial in $`a_1,\ldots a_g` and the moments $`\mathrm{E}[\chi_i\chi_j]` can be computed as integer linear combinations of entries of the {bpref "st_group.moment_simplex"}[moment simplex] corresponding to the terms of $`\chi_i\chi_j`.

Depends on: {uses "st_group.ambient"}[] {uses "st_group.definition"}[] {uses "st_group.moment_simplex"}[]
:::

:::definition "st_group.moment_simplex" (lean := "SatoTateGroup.momentSimplexRow, SatoTateGroup.mixedMoment, SatoTateGroup.weightedDegree")
*Moment simplex.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.moment_simplex))

For a {bpref "st_group.definition"}[Sato-Tate group] $`G` of odd {bpref "st_group.weight"}[weight] and {bpref "st_group.degree"}[degree] $`2g` with $`g>1` it is natural to organize the mixed moments

$$`\mathrm{E}[a_1^{e_1}\cdots a_g^{e_g}]`

by weighted degree $`\sum ie_i`; here $`a_i` denotes the $`i`th symmetric function of the eigenvalues of a random element of $`G` (equivalently, the $`i`th coefficient of a random characteristic polynomial). We may restrict to cases where every term in the weighted degree sum is even, since symmetry constraints will force the expectation to be zero otherwise.  Moments of the same weighted degree are ordered by exponent vector $`(e_1,\ldots,e_g)` in reverse lexicographic order; for example, the weight-2 row is $`(\mathrm{E}[a_2^1],\mathrm{E}[a_1^2])`, corresponding to the list of exponent vectors $`(1,0)`, $`(0,2)`.

The *moment simplex* of a Sato-Tate group is the triangular table of nonzero mixed moments with rows indexed by even weighted degree and the entries in each row sorted lexicographically by exponent vector.

Depends on: {uses "st_group.definition"}[] {uses "st_group.degree"}[] {uses "st_group.weight"}[]
:::

:::definition "st_group.moments" (lean := "SatoTateGroup.moment, SatoTateGroup.charpolyCoeff, SatoTateGroup.esymmEigen, SatoTateGroup.powerSum, SatoTateGroup.moment_zero")
*Moment statistics.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.moments))

*Moment statistics* refers to moments of random variables associated to a {bpref "st_group.definition"}[Sato-Tate group] $`G`, where the distribution of the random variable is defined using the pushforward of the Haar measure of $`G`.

Standard random variables one can associated to $`G` include the coefficients $`a_i` of the characteristic polynomial $`\sum a_ix^i` of a random matrix $`g\in G`, the $`i`th symmetric function $`e_i` of the eigenvalues $`\lambda_j` of $`g`, and the powers sums $`s_i:=\sum \lambda_j^i` which can be expressed as polynomials in the $`a_i` or $`e_i` via the Newton identities.

The *moment sequence* of $`a_i` (or any random variable) is the integer sequence $`(\mathrm{E}[a_i^0], \mathrm{E}[a_i^1],\mathrm{E}[a_i^2]\ldots)`; the convention of including the zeroth moment $`\mathrm{E}[a_i^0]=1` facilitates the computation of moment sequences of products of independent random variables by taking binomial convolutions.

Depends on: {uses "st_group.definition"}[]
:::

:::definition "st_group.probabilities" (lean := "SatoTateGroup.probability")
*Event probabilities.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.probabilities))

If $`a_i:=a_i(g)` denotes the $`i`th coefficient of the characteristic polynomial $`\sum a_ix^i` of a random matrix $`g` in a {bpref "st_group.definition"}[Sato-Tate group] $`G` with {bpref "group.haar_measure"}[Haar measure] $`\mu`, then

$$`\mathrm{Pr}[a_i=n] := \mu(\{g\in G|a_i(g)=n\})`

can be viewed as the *probability* that a random $`g\in G` satisfies $`a_i(g)=n`. This is a rational number equal to the proportion of connected components of G on which $`a_i` is identically equal to $`n`, by Proposition 8.4.3.3 of Serre's \*Lecture's on $`N_X(p)`\* .  This probability is necessarily zero unless $`n` is one of a finite set of integers.

Note that while $`\mathrm{Pr}[a_i=n]=0` implies that $`\{g\in G:a_i(g) = n\}` has measure zero, this set need not be empty (unless $`G` is finite).

Depends on: {uses "group.haar_measure"}[] {uses "st_group.definition"}[]
:::

:::definition "st_group.rational" (lean := "SatoTateGroup.IsRational, SatoTateGroup.IsRationalSubgroup, TauCeti.rationalWeylRep")
*Rational Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.rational))

A {bpref "st_group.definition"}[Sato-Tate group] $`G` of {bpref "st_group.degree"}[degree] $`d` is said to be *rational* if for every irreducible character $`\chi` of $`\GL_d(\C)` and every component $`H` of $`G` we have

$$`\int_H \chi(g)\mu_H \in \Z,`

where $`\mu_H` denotes the restriction to $`H` of the Haar measure $`\mu` on $`G`, normalized so that $`\mu_H(H)=1`.  If $`G` is the Sato-Tate group of an {bpref "lfunction.arithmetic"}[arithmetic L-function]

$$`L(s)=\prod_{\mathfrak p}L_{\mathfrak{p}}(N(\mathfrak{p})^{-s})^{-1},`

this means that the polynomials $`L_{\mathfrak p}(T)` have integer coefficients, equivalently, the $`L`-function $`L(s)` is {bpref "lfunction.rational"}[rational].

Depends on: {uses "lfunction.arithmetic"}[] {uses "lfunction.rational"}[] {uses "st_group.definition"}[] {uses "st_group.degree"}[]
:::

:::definition "st_group.real_dimension" (lean := "SatoTateGroup.realDimension")
*Real dimension of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.real_dimension))

The *real dimension* of a {bpref "st_group.definition"}[Sato-Tate group] is its dimension as a real Lie group.

Depends on: {uses "st_group.definition"}[]
:::

:::definition "st_group.second_trace_moment" (lean := "SatoTateGroup.secondTraceMoment, SatoTateGroup.traceMoment")
*Second trace moment.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.second_trace_moment))

The *second trace moment* of a {bpref "st_group.definition"}[Sato-Tate group] $`G` is the expected value of the square of the trace of a random element of $`G` (under its {bpref "group.haar_measure"}[Haar measure]).

When $`G` is the Sato-Tate group of an abelian variety, this is equal to the dimension of its {bpref "ag.endomorphism_algebra"}[endomorphism algebra] .

Depends on: {uses "ag.endomorphism_algebra"}[] {uses "group.haar_measure"}[] {uses "st_group.definition"}[]
:::

:::definition "st_group.subgroups" (lean := "IsCoatom, Subgroup.FiniteIndex")
*Maximal subgroups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.subgroups))

For a {bpref "st_group.definition"}[Sato-Tate group] $`G`, its *maximal subgroups* are the proper subgroups $`H` of $`G` of finite index that are not contained in any other proper subgroup of $`G`; such groups necessarily have the same {bpref "st_group.identity_component"}[identity component] $`H^0=G^0` as $`G`.

Depends on: {uses "st_group.definition"}[] {uses "st_group.identity_component"}[]
:::

:::definition "st_group.supgroups" (lean := "SatoTateGroup.IsMinimalSupergroup, SatoTateGroup.IsMinimalRationalSupergroup, SatoTateGroup.IsMaximal, SatoTateGroup.IsFiniteIndexSupergroup")
*Minimal supergroups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.supgroups))

The *minimal supergroups* of a {bpref "st_group.definition"}[Sato-Tate group] $`G` are the groups $`H` that properly contain $`G` with finite index and do not properly contain any other proper supergroup of $`G`; they necessarily have the same {bpref "st_group.identity_component"}[identity component] $`H^0=G^0` as $`G`.

For {bpref "st_group.rational"}[rational] Sato-Tate groups in the LMFDB we list only rational minimal supergroups.

A rational Sato-Tate group is *maximal* if it has no supergroups.

Depends on: {uses "st_group.definition"}[] {uses "st_group.identity_component"}[] {uses "st_group.rational"}[]
:::

:::definition "st_group.trace_moments" (lean := "SatoTateGroup.traceMoment, SatoTateGroup.trace, SatoTateGroup.charpolyCoeff_one")
*Trace moments of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.trace_moments))

The trace $`t` of a random element of a {bpref "st_group.definition"}[Sato-Tate group] $`G` can be viewed as a random variable whose distribution is given by the pushforward of the Haar measure on $`G` under the trace map.

The $`n`th *moment* $`\mathrm{M}_n[t]:= \mathrm{E}[t^n]` of $`t` is the expected value of the $`n`th power of the trace, which is always an integer.

For Sato-Tate groups of odd {bpref "st_group.weight"}[weight] we have $`t=-a_1` and the moment sequences of $`t` and $`a_1` coincide because their distributions are symmetric about zero.

Depends on: {uses "st_group.definition"}[] {uses "st_group.weight"}[]
:::

:::definition "st_group.trace_zero_density" (lean := "SatoTateGroup.traceZeroDensity")
*Trace zero density of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.trace_zero_density))

The *trace zero density* of a {bpref "st_group.definition"}[Sato-Tate group] is the probability that a randomly sampled element (chosen according to the {bpref "group.haar_measure"}[Haar measure]) has trace zero.

On each component of a Sato-Tate group, the trace is either constant and equal to zero, or varies continuously taking each particular value with probability zero; so this probability is simply the ratio of the number of components on which the trace is identically zero to the total number of components.

Depends on: {uses "group.haar_measure"}[] {uses "st_group.definition"}[]
:::

:::definition "st_group.weight"
*Weight of a Sato-Tate group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/st_group.weight))

The *weight* $`w` of the {bpref "st_group.definition"}[Sato-Tate group] $`G` of a motive $`X` is determined by the cohomology group $`H^w(X,\mathbb{Q}_{\ell})` used to define $`G`. For a {bpref "nf.prime"}[prime] of norm $`q`, the characteristic polynomial of Frobenius is a {bpref "av.fq.weil_polynomial"}[Weil $`q^w`-polynomial].

Depends on: {uses "av.fq.weil_polynomial"}[] {uses "nf.prime"}[] {uses "st_group.definition"}[]
:::
