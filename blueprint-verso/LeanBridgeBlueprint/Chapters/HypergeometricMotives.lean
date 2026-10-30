import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Hypergeometric motives" =>

This chapter lists the LMFDB definitions relating to *hypergeometric motives*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "hgm.bezout_determinant" (lean := "Hypergeometric.Parameters.bezoutDeterminant, Hypergeometric.Parameters.bezoutDeterminant_eq")
*Bézout determinant.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.bezout_determinant))

The *Bézout determinant* of a hypergeometric motive $`H` is the determinant of its {bpref "hgm.bezout_matrix"}[Bézout matrix].

Depends on: {uses "hgm.bezout_matrix"}[]
:::

:::definition "hgm.bezout_matrix" (lean := "Hypergeometric.Parameters.bezoutMatrix, Hypergeometric.CuspIndex.cyclotomicProd, Hypergeometric.CuspIndex.natDegree_cyclotomicProd, Polynomial.bezoutMatrix")
*Bézout matrix of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.bezout_matrix))

For a list of integers $`C=[c_1,\ldots, c_n]` we associate the polynomial

$$`\Phi_C(x) = \prod_{j=1}^n \Phi_{c_j}(x)`

where $`\Phi_n(x)` is the $`n`th cyclotomic polynomial.

Given a hypergeometric motive with {bpref "hgm.defining_parameters"}[defining parameters] $`A` and $`B`, its *Bézout matrix* is the {bpref "alg.bezout_matrix"}[Bézout matrix] of $`\Phi_A(x)` and $`\Phi_B(x)` of degree $`\max(\deg \Phi_A(x), \deg \Phi_B(x))`.

Depends on: {uses "alg.bezout_matrix"}[] {uses "hgm.defining_parameters"}[]
:::

:::definition "hgm.bezout_module" (lean := "Hypergeometric.Parameters.BezoutModule")
*Bézout module of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.bezout_module))

The *Bezout module* of a hypergeometric motive $`M` is the finite $`\mathbb{Z}`-module whose relations matrix is the {bpref "hgm.bezout_matrix"}[Bézout matrix] $`B` of $`M`. In other words, it is the quotient $`\mathbb{Z}^d/B \mathbb{Z}^d`, where $`d` is the {bpref "hgm.degree"}[degree] of $`M`.

Depends on: {uses "hgm.bezout_matrix"}[] {uses "hgm.degree"}[]
:::

:::definition "hgm.conductor"
*Conductor of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.conductor))

The exponents $`c_p` in the *conductor* $`N = \prod_p p^{c_p}` of a {bpref "hgm.motive"}[hypergeometric motive] $`H(A,B,t)` can be positive only if $`p` is {bpref "hgm.tame"}[tame] or {bpref "hgm.wild"}[wild] for $`H(A,B,t)`.

Depends on: {uses "hgm.motive"}[] {uses "hgm.tame"}[] {uses "hgm.wild"}[]
:::

:::definition "hgm.cusp_index" (lean := "Hypergeometric.CuspIndex, Hypergeometric.Parameters, Nat.totient")
*Cusp index.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.cusp_index))

A *cusp-index* of degree $`d` is a weakly increasing
list of positive integers $`[u_1,\dots,u_k]` with $`\sum_{i=1}^k \phi(u_i) = d`.

Hypergeometric families $`H(A,B)` are indexed by pairs
$`(A,B)` of cusp-indices of a common degree having no common entries.
:::

:::definition "hgm.defining_parameter_ppart" (lean := "Hypergeometric.Parameters.pPart, Hypergeometric.Parameters.pPartCommon, Hypergeometric.CuspIndex.pPartMultiset, Hypergeometric.Parameters.pPart_A_add_pPartCommon, Hypergeometric.Parameters.pPartDegree_add_sum_totient_pPartCommon")
*p-part of defining parameters of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.defining_parameter_ppart))

For a hypergeometric motive with {bpref "hgm.defining_parameters"}[defining parameters] $`[A, B]` and a prime number $`p`, we define the $`p`-part $`[A_p, B_p]` as follows.

For each $`u=a_i` or $`b_j` in $`A=(a_1,\ldots, a_m)` and $`B=(b_1,\ldots, b_n)` we write $`u=p^s v` where $`p \nmid v`.  We replace $`u` with $`\phi(v)` copies of $`p^s`, to get $`[A', B']`, and then remove equal numbers of any overlapping elements between the multisets $`A'` and $`B'` to get $`A_p` and $`B_p`. We denote the list of these removed overlapping elements by $`C_p`.

Depends on: {uses "hgm.defining_parameters"}[]
:::

:::definition "hgm.defining_parameter_primetoppart" (lean := "Hypergeometric.Parameters.primeToPPart, Hypergeometric.CuspIndex.primeToPPartMultiset, Hypergeometric.Parameters.coe_primeToPPart_A, Hypergeometric.Parameters.ofMultisets")
*prime to $`p`-part of defining parameters of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.defining_parameter_primetoppart))

For a hypergeometric motive with {bpref "hgm.defining_parameters"}[defining parameters] $`[A, B]` and a prime number $`p`, we define the prime-to-$`p`-part $`[A^p, B^p]` as follows.

For each $`u=a_i` or $`b_j` in $`A=(a_1,\ldots, a_m)` and $`B=(b_1,\ldots, b_n)` we write $`u=p^s v` where $`p \nmid v`.  We replace $`u` with $`\phi(p^s)` copies of $`v`, to get $`[A', B']`, and then remove equal numbers of any overlapping elements between the multisets $`A'` and $`B'` to get $`A^p` and $`B^p`.

Depends on: {uses "hgm.defining_parameters"}[]
:::

:::definition "hgm.defining_parameters" (lean := "Hypergeometric.Parameters, Hypergeometric.CuspIndex.fractions, Hypergeometric.Parameters.gammaVector, Hypergeometric.Parameters.algebraMap_div_eq_prod_gammaExponent")
*Defining parameters of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.defining_parameters))

A hypergeometric motive $`H(A,B,t)` in $`M(\Q,\Q)` is described by a {bpref "hgm.familes"}[hypergeometric family] $`H(A,B)` in $`M(\Q(t),t)` along with a specialization point $`t \in \Q^\times`. Here, $`A` and $`B` are disjoint multisets of positive integers and are the *defining parameters* of the hypergeometric family; they are subject to a constraint that

$$`\sum_{a \in A} \phi(a) = \sum_{b \in B} \phi(b);`

this common value is the {bpref "hgm.degree"}[degree] of the family.  The value $`t` along with $`A` and $`B` are the *defining parameters* of the hypergeometric motive $`H(A,B,t)`.

The list $`\alpha` is obtained from $`A` by replacing each $`a \in A` with the list of all elements of $`\Q \cap (0,1]` with denominator $`a`, then sorting into ascending order; the list $`\beta` is obtained from $`B` by the same procedure. Both $`\alpha` and $`\beta` have length equal to the degree.

The list $`\gamma` of nonzero integers in ascending order is characterized by the property

$$`\frac{\prod_{g \in \gamma, g>0} (x^g-1)}{\prod_{g \in \gamma,g<0} (x^{-g}-1)} = \frac{\prod_{a \in \alpha} (x - e^{2 \pi i a})}{\prod_{b \in \beta} (x - e^{2\pi i b})} = \frac{\prod_{a \in A} \Phi_a(x)}{\prod_{b \in B} \Phi_b(x)}`

where $`\Phi_n(x)` denotes the $`n`-th cyclotomic polynomial.

Depends on: {uses "hgm.familes"}[]
:::

:::definition "hgm.degree" (lean := "Hypergeometric.Parameters.degree, Hypergeometric.Parameters.degree_eq_sum_totient_B")
*Degree of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.degree))

Associated to a motive are vector spaces coming from cohomology of an algebraic variety.  The dimension of these vector spaces is the *degree* of the motive.

For a hypergeometric motive with {bpref "hgm.defining_parameters"}[defining parameters] $`A=[a_1,\ldots,a_m]`, $`B=[b_1,\ldots,b_n]`, the degree is the common value

$$`\sum_{j=1}^m \phi(a_j) = \sum_{j=1}^n \phi(b_j)`

where $`\phi` is the Euler totient function.

Depends on: {uses "hgm.defining_parameters"}[]
:::

:::definition "hgm.familes"
*Hypergeometric family over $`\Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.familes))

A *hypergeometric family* over $`\Q` is a motive over the field $`\Q(t)` with coefficients in $`\Q`.  The families are indexed by non-overlapping ordered pairs of multisets of positive integers $`(A,B)` (called {bpref "hgm.cusp_index"}[cusp-indices]) with $`\sum_{a \in A} \phi(a) = \sum_{b \in B} \phi(b) = d \in \Z_{\geq 1}`, where $`d` is the {bpref "hgm.degree"}[degree] and $`\phi` is Euler's totient function.

This motive has periods which satisfy the hypergeometric differential equation

$$`\left(t \prod_{i=1}^d \left(t \frac{\mathrm d}{\mathrm dt} - \alpha_i\right) - \prod_{j=1}^d \left(t \frac{\mathrm d}{\mathrm dt} + \beta_j - 1\right) \right)(y) = 0`

where $`\alpha_1,\dots,\alpha_d` and $`\beta_1,\dots,\beta_d` are lists obtained from $`A,B` by replacing each integer $`n` with the set of all elements of $`\Q \cap (0,1]` with denominator $`n`. For $`k=1,\dots,d`, one solution of this equation is the hypergeometric series

$$`z^{1-\beta_k} \sum_{n=0}^\infty \frac{\prod_{i=1}^d (\alpha_i - \beta_k + 1)_n}{\prod_{j=1}^d (\beta_j - \beta_k + 1)_n} z^n`

where $`(x)_n = x(x+1)\cdots(x+n-1)` is the Pochhammer symbol.

Depends on: {uses "hgm.cusp_index"}[]
:::

:::definition "hgm.families"
*Hypergeometric family over $`\Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.families))

A *hypergeometric family* over $`\Q` is a motive over the field $`\Q(t)` with coefficients in $`\Q`.  The families are indexed by non-overlapping ordered pairs of multisets of positive integers $`(A,B)` (called {bpref "hgm.cusp_index"}[cusp-indices]) with $`\sum_{a \in A} \phi(a) = \sum_{b \in B} \phi(b) = d \in \Z_{\geq 1}`, where $`d` is the {bpref "hgm.degree"}[degree] and $`\phi` is Euler's totient function.

This motive has periods which satisfy the hypergeometric differential equation

$$`\left(t \prod_{i=1}^d \left(t \frac{\mathrm d}{\mathrm dt} - \alpha_i\right) - \prod_{j=1}^d \left(t \frac{\mathrm d}{\mathrm dt} + \beta_j - 1\right) \right)(y) = 0`

where $`\alpha_1,\dots,\alpha_d` and $`\beta_1,\dots,\beta_d` are lists obtained from $`A,B` by replacing each integer $`n` with the set of all elements of $`\Q \cap (0,1]` with denominator $`n`. For $`k=1,\dots,d`, one solution of this equation is the hypergeometric series

$$`z^{1-\beta_k} \sum_{n=0}^\infty \frac{\prod_{i=1}^d (\alpha_i - \beta_k + 1)_n}{\prod_{j=1}^d (\beta_j - \beta_k + 1)_n} z^n`

where $`(x)_n = x(x+1)\cdots(x+n-1)` is the Pochhammer symbol.

Depends on: {uses "hgm.cusp_index"}[] {uses "hgm.degree"}[]
:::

:::definition "hgm.field.label" (lean := "Hypergeometric.Parameters.motiveLabel, Hypergeometric.Parameters.label, Hypergeometric.CuspIndex.labelEntries")
*Label of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.field.label))

{bpref "hgm.motive"}[Hypergeometric motives] $`H(A,B,t) \in M(\Q,\Q)` are labeled following the pattern of $`H([3,3],[2,2,4],-1/3)` having label A3.3\_B2.2.4\_t-1.3  and the corresponding {bpref "hgm.familes"}[family] having label A3.3\_B2.2.4 .

Depends on: {uses "hgm.familes"}[] {uses "hgm.motive"}[]
:::

:::definition "hgm.good_prime"
*Primes of good and bad reduction of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.good_prime))

A *prime of bad reduction* or *bad prime* of a {bpref "hgm.motive"}[hypergeometric motive] $`M` is a prime dividing the {bpref "hgm.conductor"}[conductor] of $`M`. A bad prime is either {bpref "hgm.tame"}[tame] or {bpref "hgm.wild"}[wild].

A *prime of good reduction* or *good prime* is a prime that is not a bad prime, i.e., a prime that does not divide the conductor.

Depends on: {uses "hgm.conductor"}[] {uses "hgm.motive"}[] {uses "hgm.tame"}[] {uses "hgm.wild"}[]
:::

:::definition "hgm.hodge_vector" (lean := "Hypergeometric.Parameters.hodgeVector, Hypergeometric.Parameters.sum_hodgeVector, Hypergeometric.Parameters.hodgeVectorAtOne")
*Hodge vector of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.hodge_vector))

Let $`H(A,B)` be a {bpref "hgm.familes"}[hypergeometric family] of {bpref "hgm.degree"}[degree] $`d` and {bpref "hgm.weight"}[weight] $`w` with {bpref "hgm.defining_parameters"}[defining parameters] $`A=[a_1,\ldots,a_m]` and $`B=[b_1,\ldots,b_n]`. The *Hodge vector* $`(h^{0,w},\dots,h^{w,0})` of $`H(A,B)` records the dimensions $`h^{p,q}` (with $`p+q=w`) of the Hodge subspaces associated to the family.

The Hodge vector depends on how the indices $`a_j` and  $`b_k` intertwine on the circle $`\R/\Z`, and we have $`d = \sum_{p=0}^{w} h^{p,w-p}`.   At the extreme of complete intertwining, the Hodge vector is $`(h^{0,0}) = (d)`.  At the extreme of complete separation, $`d = w+1` and
the Hodge vector is $`(h^{0,w},\dots,h^{w,0}) = (1,\dots,1)`.

For $`t \in \Q` with $`t \neq 0,1`, the {bpref "hgm.motive"}[motive] $`H(A,B,t)` has the same Hodge vector as the family.  For $`t=1`, the motive $`H(A,B,t)` has degree $`d-1` or $`d-2`, according to whether $`w` is even or odd: if $`w` is even, then the middle Hodge number $`h^{w/2,w/2}` drops by $`1`, whereas if $`w` is odd, then the two middle Hodge numbers drop by $`1`.

Depends on: {uses "hgm.defining_parameters"}[] {uses "hgm.degree"}[] {uses "hgm.familes"}[] {uses "hgm.motive"}[] {uses "hgm.weight"}[]
:::

:::definition "hgm.imprimitivity_index" (lean := "Hypergeometric.Parameters.rotationNumber, Hypergeometric.Parameters.rotationGroup")
*Imprimitivity index of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.imprimitivity_index))

If a hypergeometric family has {bpref "hgm.defining_parameters"}[defining parameters] $`A=(a_1,\ldots,a_n)` and $`B=(b_1,\ldots,b_m)`, then we can view the parameters as giving two multisets of roots of unity, namely for $`A`, the primitive $`a_i`-th roots of unity repeated according to their multiplicities in $`A`, and similarly for $`B`.  These sets has a rotational symmetry group $`R`, which may be trivial.  The *rotation number* is the order of $`R`.

Depends on: {uses "hgm.defining_parameters"}[]
:::

:::definition "hgm.levelt_matrices" (lean := "Hypergeometric.Parameters.leveltInfty, Hypergeometric.Parameters.leveltZero, Hypergeometric.Parameters.IsLeveltPair, Hypergeometric.Parameters.IsLeveltPair.exists_conj, Hypergeometric.CuspIndex.map_cyclotomicProd_eq_prod_exp")
*Levelt matrices of a hypergeometric family.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.levelt_matrices))

The {bpref "hgm.monodromy"}[monodromy representation] associated to a {bpref "hgm.familes"}[hypergeometric family] is generated by two matrices $`h_{\infty}` and $`h_0` describing the local monodromy around $`\infty` and $`0`, respectively.  The characteristic polynomial of $`h_{\infty}` is $`\prod_j (T - e^{2\pi i \alpha_j})` and of $`h_0` is $`\prod_j (T - e^{2\pi i \beta_j})`, where $`(\alpha_j)` and $`(\beta_j)` are from the {bpref "hgm.defining_parameters"}[defining parameters] of the family.  The choice of matrices satisfying this condition is determined up to simultaneous conjugacy.

The presentation used here is due to Levelt .

Depends on: {uses "hgm.defining_parameters"}[] {uses "hgm.familes"}[] {uses "hgm.monodromy"}[]
:::

:::definition "hgm.local_discriminant"
*The local discriminant of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.local_discriminant))

Given a {bpref "hgm.motive"}[hypergeometric motive] $`M` and a prime $`p`, the *local discriminant* of $`M` at $`p` is the {bpref "nf.discriminant"}[discriminant] of the number field defined by the {bpref "modlgal.frobenius_charpoly"}[characteristic polynomial of Frobenius] of $`M` at $`p`.

Depends on: {uses "hgm.motive"}[] {uses "modlgal.frobenius_charpoly"}[] {uses "nf.discriminant"}[]
:::

:::definition "hgm.monodromy" (lean := "Hypergeometric.Parameters.monodromyGroup, Hypergeometric.Parameters.IsLeveltPair.exists_map_closure_eq, Hypergeometric.Parameters.monodromyGroup_eq_closure_companionMatrix, Hypergeometric.Parameters.leveltInfty, Hypergeometric.Parameters.leveltZero")
*Monodromy group of a hypergeometric family.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.monodromy))

The monodromy representation associated to a hypergeometric family is generated by two matrices $`A` and $`B` describing the local monodromy around $`\infty` and $`0`, respectively. The presentation used here is due to Levelt .

The monodromy groups of hypergeometric families of weight 0 were computed by Beukers and Heckman .
:::

:::definition "hgm.motive"
*Hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.motive))

*Hypergeometric motives* $`H(A,B,t)` in a {bpref "hgm.familes"}[family] $`H(A,B)` are
indexed by rational numbers $`t \not \in \{0,1\}`, with the case $`t=1` allowed if special attention is given.

For example $`H([3],[1,1],t)` is the
motive $`H^1(E_{1728t},{\Bbb Q})` where
$`E_{j}` is an elliptic curve with $`j`-invariant $`1728j`.
Also special hypergeometric motives $`H(A,B,1)` are defined, having degree
$`1` or $`2` less than the other $`H(A,B,t)`.

Depends on: {uses "hgm.familes"}[]
:::

:::definition "hgm.rotation_number" (lean := "Hypergeometric.Parameters.rotationNumber, Hypergeometric.Parameters.rotationGroup, Hypergeometric.Parameters.finite_rotationGroup")
*Imprimitivity index of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.rotation_number))

If a hypergeometric family has {bpref "hgm.defining_parameters"}[defining parameters] $`A=(a_1,\ldots,a_n)` and $`B=(b_1,\ldots,b_m)`, then we can view the parameters as giving two multisets of roots of unity, namely for $`A`, the primitive $`a_i`-th roots of unity repeated according to their multiplicities in $`A`, and similarly for $`B`.  These sets has a rotational symmetry group $`R`, which may be trivial.  The *rotation number* is the order of $`R`.

Depends on: {uses "hgm.defining_parameters"}[]
:::

:::definition "hgm.signature"
Complex conjugation acts on the vector space corresponding to the middle entry in the {bpref "hgm.hodge_vector"}[Hodge vector].  The *signature* of a hypergeometric motive is the difference between the number of $`+1` eigenvalues and the number of $`-1` eigenvalues for this operator.

When there is no middle entry (because the Hodge width is odd), the signature is $`0`.

The archimedean root number can be recovered from the signature $`s` and the Hodge vector $`(h_n)`.

Depends on: {uses "hgm.hodge_vector"}[]
:::

:::definition "hgm.tame" (lean := "Hypergeometric.Parameters.IsTamePrime, Hypergeometric.Parameters.isTamePrime_iff_padicValRat")
*Tame primes for hypergeometric families.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.tame))

A prime $`p` is called *tame* for a {bpref "hgm.motive"}[hypergeometric motive] $`H(A,B,t)` if $`p` is not {bpref "hgm.wild"}[wild] and either $`v_p(t) \ne 0` or $`v_p(t-1) \ne 0`.  The {bpref "hgm.conductor"}[conductor] of $`H(A,B,t)` is supported at a subset of the tame and wild primes.

Depends on: {uses "hgm.motive"}[] {uses "hgm.wild"}[]
:::

:::definition "hgm.type" (lean := "Hypergeometric.Parameters.IsOrthogonalType, Hypergeometric.Parameters.IsSymplecticType, Hypergeometric.Parameters.isSymplecticType_iff_not_isOrthogonalType")
*The type of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.type))

A {bpref "hgm.motive"}[hypergeometric motive] $`M` of {bpref "hgm.weight"}[weight] $`w` is of *orthogonal* or *symplectic* *type* according as $`w` is even or odd. This corresponds to the fact that the motivic Galois group of $`M` is either a subgroup of the conformal orthogonal group or conformal symplectic group depending on the parity of $`w`.

Depends on: {uses "hgm.motive"}[] {uses "hgm.weight"}[]
:::

:::definition "hgm.weight"
*weight.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.weight))

Associated to a motive are vector spaces coming from cohomology $`H^*(X)` of an algebraic variety $`X`.  If these vector spaces arise in $`H^w(X)`, then $`w` is the *(motivic) weight* of the motive.  The weight is the number of commas in the {bpref "mot.hodgevector"}[Hodge vector], i.e., the Hodge vector is of the form $`(h^{0,w},\dots,h^{w,0})`.
:::

:::definition "hgm.wild" (lean := "Hypergeometric.Parameters.IsWildPrime")
*Wild primes for hypergeometric families.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.wild))

A prime $`p` is called *wild* for a {bpref "hgm.familes"}[hypergeometric family] $`H(A,B)` if it divides an element of the {bpref "hgm.defining_parameters"}[defining parameters] $`A` and $`B`.  The name is appropriate since if $`p` is such a prime, then for most $`t \in \Q^\times` the motive $`H(A,B,t)` is wildly ramified at $`p`.

Depends on: {uses "hgm.defining_parameters"}[] {uses "hgm.familes"}[]
:::

:::definition "hgm.zigzagplot" (lean := "Hypergeometric.Parameters.zigzagHeights, Hypergeometric.Parameters.hodgeVector")
*Zigzag plot.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hgm.zigzagplot))

The *zigzag plot*, or *zigzag procedure*, is a graphical representation of the {bpref "hgm.defining_parameters"}[defining parameters of a hypergeometric family] $`\alpha` and $`\beta`. For improved readability, we color the $`\alpha` parameters with red, and the $`\beta` parameters with blue. It is constructed by ordering the parameters $`\alpha_i` and $`\beta_j`. One draws a point at $`(0,0)` corresponding to the lowest parameter. One then proceeds in uniform steps from left to right, drawing a point for each parameter and then moving diagonally upwards after red points and diagonally downwards after blue points.

The {bpref "hgm.hodge_vector"}[hodge vector] of the corresponding hypergeometric family can be read from the Zigzag plot by counting the number of points of the same color lying on each horizontal line.

Depends on: {uses "hgm.defining_parameters"}[] {uses "hgm.hodge_vector"}[]
:::

:::definition "mot.hodgevector" (lean := "Hypergeometric.Parameters.hodgeVector, Hypergeometric.Parameters.sum_hodgeVector, Hypergeometric.Parameters.hodgeVectorAtOne")
*Hodge vector of a hypergeometric motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mot.hodgevector))

Let $`H(A,B)` be a {bpref "hgm.familes"}[hypergeometric family] of {bpref "hgm.degree"}[degree] $`d` and {bpref "hgm.weight"}[weight] $`w` with {bpref "hgm.defining_parameters"}[defining parameters] $`A=[a_1,\ldots,a_m]` and $`B=[b_1,\ldots,b_n]`. The *Hodge vector* $`(h^{0,w},\dots,h^{w,0})` of $`H(A,B)` records the dimensions $`h^{p,q}` (with $`p+q=w`) of the Hodge subspaces associated to the family.

The Hodge vector depends on how the indices $`a_j` and  $`b_k` intertwine on the circle $`\R/\Z`, and we have $`d = \sum_{p=0}^{w} h^{p,w-p}`.   At the extreme of complete intertwining, the Hodge vector is $`(h^{0,0}) = (d)`.  At the extreme of complete separation, $`d = w+1` and
the Hodge vector is $`(h^{0,w},\dots,h^{w,0}) = (1,\dots,1)`.

For $`t \in \Q` with $`t \neq 0,1`, the {bpref "hgm.motive"}[motive] $`H(A,B,t)` has the same Hodge vector as the family.  For $`t=1`, the motive $`H(A,B,t)` has degree $`d-1` or $`d-2`, according to whether $`w` is even or odd: if $`w` is even, then the middle Hodge number $`h^{w/2,w/2}` drops by $`1`, whereas if $`w` is odd, then the two middle Hodge numbers drop by $`1`.

Depends on: {uses "hgm.defining_parameters"}[] {uses "hgm.degree"}[] {uses "hgm.familes"}[] {uses "hgm.motive"}[] {uses "hgm.weight"}[]
:::

:::definition "mot.width" (lean := "TauCeti.Hodge.HodgeType.width, Hypergeometric.hodgeVectorWidth, TauCeti.Hodge.HodgeType.hodgeVectorWidth_hodgeVector, TauCeti.Hodge.HodgeType.width_eq_two_mul_sub_weight, Hypergeometric.hodgeVectorWidth_zero_two_three_one_three_two_zero")
*Width of a motive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mot.width))

The width of a weight $`w` motive $`M` in $`M(F,\Q)` is the number of steps from the first nonzero entry in the Hodge vector to the last nonzero entry.  Thus if $`M` has weight $`7` and Hodge vector $`(0,2,3,1,3,2,0)`, then its width is $`4`.
:::
