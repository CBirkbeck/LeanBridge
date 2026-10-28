import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Further background" =>

This chapter lists the LMFDB definitions relating to *further background*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "alg.bezout_matrix" (lean := "Polynomial.bezoutMatrix, Polynomial.sub_mul_sum_bezoutMatrix, Polynomial.det_bezoutMatrix, Polynomial.resultant, Polynomial.sylvester")
*Bézout matrix.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.bezout_matrix))

Given two polynomials $`f` and $`g` of degree at most $`n`, their *degree $`n` Bézout matrix* is the $`n\times n` matrix $`(c_{ij})` where

$$`\frac{f(x)g(y)-f(y)g(x)}{x-y} = \sum_{i,j=1}^n c_{ij} x^i y^{j}.`

The determinant of this matrix is the resultant of the two polynomials.
:::

:::definition "alg.symmetric_bilinear_form" (lean := "LinearMap.BilinForm, LinearMap.BilinForm.IsSymm")
*Symmetric bilinear form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.symmetric_bilinear_form))

For a vector space $`V` over a field $`F`, a *symmetric bilinear form* is a function $`B \colon V^2 \to F` satisfying

1. $`B(x+w,y) = B(x,y) + B(w,y)` for all $`x,y,w \in V`;
2. $`B(\alpha x, y) = \alpha B(x,y)` for all $`x \in V`, and all $`\alpha \in F`;
3. $`B(x,y) = B(y,x)` for all $`x,y \in V`.

Conditions (1) and (2) imply that $`B(\cdot,y)` is a linear map in the first variable when $`y` is fixed. Including condition (3) then implies that $`B(x,\cdot)` is also a linear map in the second variable when $`x` is fixed.
:::

:::definition "combin.hasse_diagram" (lean := "SimpleGraph.hasse, SimpleGraph.hasse_adj, CovBy")
*Hasse diagram.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/combin.hasse_diagram))

If $`(S, \leq)` is a finite partially ordered set, then a *Hasse diagram* for $`S` is a representation of $`S` in the plane where

- there is one node for each element of $`S`

- there is an edge connecting $`s_1` and $`s_2` if $`s_1` is maximal in $`\leq` for $`\{s\in S \mid s < s_2\}`, or vice versa

- if $`s_1` is connected to $`s_2` by an edge and $`s_1 < s_2`, then $`s_2` is higher in the plane in the sense of having a larger "$`y`-coordinate"
:::

:::definition "crystals.crystal"
*Crystal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/crystals.crystal))

A *($`U_q(\mathfrak{g})`-)crystal* is a nonempty set $`B` together with maps

$$`\begin{aligned}
   &\mathrm{wt}: B \to P\\
   &e_i, f_i : B \to B \cup \{0\} \quad \text{for all } i\in I.
\end{aligned}`

Here $`\mathfrak{g}` is a Lie or Kac-Moody algebra of a particular type with index set $`I`.

The map $`\mathrm{wt}` is called the weight function which maps a crystal element to a weight in the weight lattice $`P`. The maps $`e_i` and $`f_i` are called Kashiwara raising and lowering operators.
:::

:::definition "field.finite.conway_polynomial" (lean := "FiniteField.conwayPolynomial, FiniteField.conwayKey, FiniteField.conwayKey_lt_conwayKey_iff, FiniteField.IsConwayCompatible, FiniteField.minimalFor_conwayPolynomial")
*Conway polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/field.finite.conway_polynomial))

*Conway polynomials* give a standardized defining polynomial for defining finite fields.

For the finite field of order $`p^n` where $`p` is prime, we first set an ordering for the elements of $`\F_p=\Z/p\Z`, namely $`0<1<\cdots< p-1` where we represent classes modulo $`p` by an integer in $`\{0,\ldots, p-1\}`.

For two degree $`n` polynomials over $`\F_p`, $`f=a_n x^n + \cdots a_0` and $`g=b_n x^n+\cdots b_0`, we say $`f<g` if there exists $`j` such that $`a_i=b_i` for $`i>j` and $`(-1)^{n-j} a_j < (-1)^{n-j} b_j`.

Then, the Conway polynomial is the first polynomial $`f_{p,n}` of degree $`n` under this ordering such that

  1. a root of $`f_{p,n}` is primitive, i.e., it has order $`p^n-1` in $`\overline{\F}_p`
  2. for every positive divisor $`m` of $`n`,

$$`f_{p,m}(x^{(p^n-1)/(p^m-1)}) \equiv 0 \pmod{f_{p,n}},`

i.e., the $`(p^n-1)/(p^m-1)`th power of a root of $`f_{p,n}` is a root of $`f_{p,m}`.
:::

:::definition "ring.associate" (lean := "Associated, Associated.setoid")
*Associate of an element.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.associate))

If $`R` is a {bpref "ring"}[commutative ring], two elements $`x, y \in R` are *associates* if there is a {bpref "ring.unit"}[unit] $`u \in R` with $`y = ux`.  This defines an equivalence relation on the elements of $`R`.

Depends on: {uses "ring"}[] {uses "ring.unit"}[]
:::

:::definition "ring.euclidean_domain"
*Euclidean domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.euclidean_domain))

An *Euclidean domain* is an {bpref "ring.integral_domain"}[integral domain] $`R` with a function

$$`\nu: R-\{0\}\to \Z_{\geq 0}`

such that for all $`a\in R` and all $`b\in R-\{0\}`, there exists $`q,r\in R` such that $`a=bq+r` and $`r=0` or $`\nu(r)<\nu(b)`.

Euclidean domains are {bpref "ring.principal_ideal_domain"}[principal ideal domains], and hence, {bpref "ring.unique_factorization_domain"}[unique factorization domains].

Depends on: {uses "ring.integral_domain"}[] {uses "ring.principal_ideal_domain"}[] {uses "ring.unique_factorization_domain"}[]
:::

:::definition "ring.principal_ideal_domain" (lean := "IsPrincipalIdealRing, IsDomain, PrincipalIdealRing.to_uniqueFactorizationMonoid")
*Principal ideal domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.principal_ideal_domain))

A *principal ideal domain*, or PID, is an {bpref "ring.integral_domain"}[integral domain] $`R` such that every ideal of $`R` is of the form $`\langle a\rangle` for some $`a\in R`.

Every such ring is a {bpref "ring.unique_factorization_domain"}[unique factorization domain].

Depends on: {uses "ring.integral_domain"}[] {uses "ring.unique_factorization_domain"}[]
:::

:::definition "ring.unique_factorization_domain" (lean := "UniqueFactorizationMonoid, IsDomain, UniqueFactorizationMonoid.of_existsUnique_irreducible_factors, UniqueFactorizationMonoid.factors_unique")
*Unique factorization domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.unique_factorization_domain))

A *unique factorization domain*, or UFD, is an {bpref "ring.integral_domain"}[integral domain] $`R` such that for every non-zero non-unit $`a\in R` there exist {bpref "ring.irreducible"}[irreducibles] $`p_1, \ldots, p_n` such that

$$`a = p_1\cdots p_n,`

and this representation is unique up to the order of the factors and up to {bpref "ring.associate"}[associates].

Depends on: {uses "ring.associate"}[] {uses "ring.integral_domain"}[] {uses "ring.irreducible"}[]
:::

:::definition "specialfunction.k_bessel" (lean := "Complex.besselK, Complex.besselKIntegrand, Complex.integrableOn_besselKIntegrand, Complex.besselK_neg, Complex.conj_besselK_I_mul")
*$`K`-Bessel functions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/specialfunction.k_bessel))

For $`x\in\mathbb{R}_{>0}` and $`\nu\in\mathbb{C}` we define the *$`K`-Bessel functions*

$$`K_{\nu}(x)=\frac{1}{2}\int_0^\infty t^{\nu-1}e^{-(x/2)(t+1/t)}dt.`
:::

:::definition "specialfunction.poincare"
*Poincar&eacute; series.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/specialfunction.poincare))

Let $`G` be a subgroup of {bpref "group.sl2z"}[$`\Gamma`] of finite {bpref "group.subgroup.index"}[index] $`m`, $`v` a {bpref "mf.multipliersystem"}[multiplier system] on $`G` and $`k\geq3\in\mathbb{N}` such that $`v(-I)=(-1)^k`. Let $`s` be a {bpref "group.fuchsian.cusps"}[cusp] representative of $`G` with {bpref "group.fuchsian.cusps.width"}[width] $`w` such that $`s=\gamma_s(\infty)` for some $`\gamma_s\in\Gamma` and let $`G_s=G\cap\gamma_s\Gamma_{\infty}\gamma_s^{-1}` be the \*stabilizer\* of the cusp $`s`. Assume that $`v` is trivial on $`G_s`. The *$`n`th Poincar\'e; series* for the cusp that $`s` represents is defined as

$$`P_k^n(G,v;z;\overline{s})=\sum_{g\in G_s\setminus G}\overline{v(g)}e^{2\pi
i(n/w)\gamma_s^{-1}gz}j(\gamma_s^{-1}g,z)^{-k},`

where $`j(\gamma,z)=cz+d` for $`\gamma=\left(\begin{matrix}a&b\\c&d\end{matrix}\right)`.

Poincare; series are \*holomorphic\* on the {bpref "mf.upper_half_plane"}[upper half-plane]. Further more, for a fixed cusp $`\overline{S}`, they generate the corresponding space of {bpref "cmf.cusp_form"}[cusp forms]. The series depends on the choice of $`\gamma_s` up to a factor of $`e^{2\pi in/w}`, therefore, if $`w\mid n`, it does not depend on the cusp representative.

Depends on: {uses "cmf.cusp_form"}[] {uses "group.fuchsian.cusps"}[] {uses "group.fuchsian.cusps.width"}[] {uses "group.sl2z"}[] {uses "group.subgroup.index"}[] {uses "mf.multipliersystem"}[] {uses "mf.upper_half_plane"}[]
:::
