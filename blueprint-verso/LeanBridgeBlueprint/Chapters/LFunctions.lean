import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "L-functions" =>

This chapter lists the LMFDB definitions in the category `lfunction`. Each definition links back to its LMFDB knowl. `af`, `af.bernoulli_numbers`, `af.divisor_function`, `af.multiplicative` and `specialfunction.gamma` also belong here, although their ids put them in another LMFDB category.

:::definition "af" (lean := "ArithmeticFunction")
*Arithmetic function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af))

An *arithmetic function* is a complex-valued function whose domain is the positive integers.
:::

:::definition "af.bernoulli_numbers" (lean := "bernoulli")
*Bernoulli numbers.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.bernoulli_numbers))

The *Bernoulli numbers* are the rational numbers $`B_n` that appear as coefficients of the formal power series

$$`\frac{T}{e^T-1}=\sum_{n\ge 0}B_n\frac{T^n}{n!},`

which has radius of convergence $`2\pi`.
:::

:::definition "af.divisor_function" (lean := "ArithmeticFunction.divisorFunction, ArithmeticFunction.isMultiplicative_divisorFunction, ArithmeticFunction.divisorFunction_natCast, ArithmeticFunction.sigma")
*Divisor function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.divisor_function))

A *divisor function* is a {bpref "af.multiplicative"}[multiplicative] {bpref "af"}[arithmetic function] of the form

$$`\sigma_{\tau}(n)=\sum_{d\mid n}d^\tau,`

for some fixed $`\tau\in\mathbb{C}`.

Depends on: {uses "af"}[] {uses "af.multiplicative"}[]
:::

:::definition "af.multiplicative" (lean := "ArithmeticFunction.IsMultiplicative")
*Multiplicative arithmetic function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.multiplicative))

An arithmetic function $`f:\mathbb{Z}_{>0}\to \C` is *multiplicative* if $`f(mn)=f(m)f(n)` for all coprime integers $`m,n>0`, and is not the zero-function (in particular, $`f(1)=1`).
:::

:::definition "lfunction" (lean := "AnalyticLFunction, AnalyticLFunction.SelbergData, AnalyticLFunction.eqOn_toFun_of_coeff_eq, AnalyticLFunction.zeta, LSeries")
*L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction))

An (analytic) *L-function* is a {bpref "lfunction.dirichlet_series"}[Dirichlet series] that has an {bpref "lfunction.euler_product"}[Euler product] and satisfies a certain type of {bpref "lfunction.functional_equation"}[functional equation].

It is expected that all L-functions satisfy the {bpref "lfunction.rh"}[Riemann Hypothesis,] that all of the {bpref "lfunction.zeros"}[zeros] in the {bpref "lfunction.critical_strip"}[critical strip] are on the {bpref "lfunction.critical_line"}[critical line]. Selberg has defined a class $`\mathcal S` of Dirichlet series that satisfy the {bpref "lfunction.selberg_class.axioms"}[Selberg axioms.] It is conjectured (but far from proven) that $`\mathcal S` is precisely the set of all L-functions. Selberg's axioms have not been verified for all of the L-functions in this database but are known to hold for many of them.

It is also conjectured that a precise form of the {bpref "lfunction.functional_equation"}[functional equation] holds for every element of $`\mathcal S`. Under this assumption the functional equation is determined by a quadruple known as the {bpref "lfunction.selbergdata"}[Selberg data], consisting of the {bpref "lfunction.degree"}[degree], {bpref "lfunction.conductor"}[conductor], {bpref "lfunction.spectral_parameters"}[spectral parameters], and {bpref "lfunction.root_number"}[sign].

Depends on: {uses "lfunction.dirichlet_series"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.analytic_conductor" (lean := "AnalyticLFunction.analyticConductor, AnalyticLFunction.SelbergData.analyticConductor, AnalyticLFunction.SelbergData.analyticConductor_eq_analyticConductorLMFDB")
*Analytic conductor.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.analytic_conductor))

The *analytic conductor* of an {bpref "lfunction"}[L-function] $`L(s)` with {bpref "lfunction.infinity_factor"}[infinity factor] $`L_{\infty}(s)` and {bpref "lfunction.conductor"}[conductor] $`N` is the real number

$$`A := \mathrm{exp}\left(2\mathrm{Re}\left(\frac{L_{\infty}'(1/2)}{L_{\infty}(1/2)}\right)\right)N.`

Depends on: {uses "lfunction"}[] {uses "lfunction.conductor"}[] {uses "lfunction.infinity_factor"}[]
:::

:::definition "lfunction.analytic_rank" (lean := "AnalyticLFunction.analyticRank, AnalyticLFunction.natCast_analyticRank, AnalyticLFunction.iteratedDeriv_analyticRank_ne_zero, AnalyticLFunction.analyticOrderNatAt_arithmeticNormalization, AnalyticLFunction.analyticRank_congr")
*Analytic rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.analytic_rank))

The *analytic rank* of an {bpref "lfunction"}[L-function] $`L(s)` is its order of vanishing at its {bpref "lfunction.central_point"}[central point].

When the analytic rank $`r` is positive, the value listed in the LMFDB is typically an upper bound that is believed to be tight (in the sense that there are known to be $`r` zeroes located very near to the central point).

Depends on: {uses "lfunction.central_point"}[] {uses "lfunction"}[]
:::

:::definition "lfunction.arithmetic" (lean := "IsAlgebraic, LSeries")
*Arithmetic L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.arithmetic))

An {bpref "lfunction"}[L-function] $`L(s) = \sum_{n=1}^{\infty} a_n n^{-s}`  is called *arithmetic* if its Dirichlet coefficients $`a_n` are algebraic numbers.

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.bad_prime" (lean := "AnalyticLFunction.conductor, Nat.primeFactors, AnalyticLFunction.exists_eulerFactor")
*Bad prime.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.bad_prime))

The *bad primes* of an {bpref "lfunction"}[L-function] are the primes that divided its {bpref "lfunction.conductor"}[conductor].

Depends on: {uses "lfunction"}[] {uses "lfunction.conductor"}[]
:::

:::definition "lfunction.central_character" (lean := "AnalyticLFunction.IsCentralCharacter, AnalyticLFunction.eulerFactor, AnalyticLFunction.IsCentralCharacter.eq")
*Central character of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.central_character))

An L-function has an {bpref "lfunction.euler_product"}[Euler product] of the form
$`L(s) = \prod_p L_p(p^{-s})^{-1}`
where $`L_p(x) = 1 + a_p x + \ldots + (-1)^d \chi(p) x^d`. The character $`\chi` is a {bpref "character.dirichlet"}[Dirichlet character] mod $`N` and is called *central character* of the L-function.
Here, $`N` is the {bpref "lfunction.conductor"}[conductor] of $`L`.

Depends on: {uses "character.dirichlet"}[] {uses "lfunction.conductor"}[] {uses "lfunction.euler_product"}[]
:::

:::definition "lfunction.central_point" (lean := "AnalyticLFunction.centralPoint, AnalyticLFunction.arithmeticCentralPoint, AnalyticLFunction.criticalLine_inter_im_eq_zero, AnalyticLFunction.one_sub_eq_self_iff")
*Central point of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.central_point))

The *central point* of an {bpref "lfunction"}[L-function] is the
point on the real axis of the {bpref "lfunction.critical_line"}[critical line].  Equivalently,
it is the fixed point of the {bpref "lfunction.functional_equation"}[functional equation].

In the {bpref "lfunction.normalization"}[analytic normalization], the central point is $`s=1/2`, in the arithmetic normalization, it is $`s=\frac{w+1}{2}`, where $`w` is the {bpref "lfunction.motivic_weight"}[weight] of the L-function.

Depends on: {uses "lfunction"}[] {uses "lfunction.critical_line"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.central_value" (lean := "AnalyticLFunction.toFun, AnalyticLFunction.analyticRank_eq_zero_iff, AnalyticLFunction.arithmeticNormalization_add")
*Central value of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.central_value))

The *central value* of an {bpref "lfunction"}[L-function] is its value at the {bpref "lfunction.central_point"}[central point] of the {bpref "lfunction.critical_strip"}[critical strip].

Depends on: {uses "lfunction"}[] {uses "lfunction.central_point"}[] {uses "lfunction.critical_strip"}[]
:::

:::definition "lfunction.coefficient_field" (lean := "AnalyticLFunction.arithmeticCoeff, AnalyticLFunction.motivicWeight, IntermediateField.adjoin")
*Coefficient field of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.coefficient_field))

The *coefficient field* of an {bpref "lfunction.arithmetic"}[arithmetic] {bpref "lfunction"}[L-function] $`L(s)=\sum a_nn^{-s}` is the {bpref "nf"}[number field] generated by the algebraic integers $`a_nn^{w/2}`, where $`w` is the {bpref "lfunction.motivic_weight"}[motivic weight].

Depends on: {uses "lfunction"}[] {uses "lfunction.arithmetic"}[] {uses "lfunction.motivic_weight"}[] {uses "nf"}[]
:::

:::definition "lfunction.completed" (lean := "AnalyticLFunction.completed, AnalyticLFunction.completed_eq, AnalyticLFunction.completed_eq_sign_mul_conj")
*Completed L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.completed))

If the {bpref "lfunction"}[L-function] $`L(s)` satisfies the {bpref "lfunction.functional_equation"}[functional equation]

$$`\Lambda(s) := N^{s/2}
\prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k)
\cdot L(s) = \varepsilon \overline{\Lambda}(1-s),`

then $`\Lambda(s)` is called the *completed L-function*.

The completed L-function is the product of the L-function and its {bpref "lfunction.gamma_factor"}[gamma factors].

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[]
:::

:::definition "lfunction.conductor" (lean := "AnalyticLFunction.conductor, AnalyticLFunction.SelbergData.conductor")
*Conductor of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.conductor))

The *conductor* of an {bpref "lfunction"}[L-function] is the integer $`N`  occurring in its {bpref "lfunction.functional_equation"}[functional equation]

$$`\Lambda(s) := N^{s/2}
\prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k)
\cdot L(s) = \varepsilon \overline{\Lambda}(1-s).`

The conductor of an analytic {bpref "lfunction"}[L-function] is the second component in the {bpref "lfunction.selbergdata"}[Selberg data]. For a {bpref "lfunction.dirichlet"}[Dirichlet L-function]
 associated with a primitive {bpref "character.dirichlet"}[Dirichlet character], the conductor of the L-function is the same as the {bpref "character.dirichlet.conductor"}[conductor] of the character. For a primitive L-function associated with a {bpref "cmf.cusp_form"}[cusp form] $`\phi` on $`GL(2)/\mathbb{Q}`, the conductor of the L-function is the same as the level of $`\phi`.

In the literature, the word _level_ is sometimes used instead of _conductor_.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "cmf.cusp_form"}[] {uses "lfunction"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.critical_line" (lean := "AnalyticLFunction.criticalLine, AnalyticLFunction.arithmeticCriticalLine, AnalyticLFunction.mem_criticalLine_iff_one_sub_conj_eq, AnalyticLFunction.mem_arithmeticCriticalLine_iff_add_sub_conj_eq, AnalyticLFunction.riemannHypothesis_iff_mem_criticalLine")
*Critical line of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.critical_line))

The *critical line* of an {bpref "lfunction"}[L-function]  is the line of symmetry of its {bpref "lfunction.functional_equation"}[functional equation].

In the {bpref "lfunction.normalization"}[analytic normalization], the functional equation relates $`s` to $`1-s` and the
critical line is the line $`\Re(s) = \frac12`.

In the arithmetic normalization, the functional equation relates $`s` to $`1 + w - s`,
where $`w` is the motivic weight.  In that normalization the critical line is
$`\Re(s) = \frac{1+w}2`.

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.critical_strip" (lean := "AnalyticLFunction.criticalStrip, AnalyticLFunction.arithmeticCriticalStrip, AnalyticLFunction.summable_norm_tsum_term_prime_pow_sub_one, AnalyticLFunction.toFun_ne_zero, AnalyticLFunction.mem_closure_criticalStrip_of_completed_eq_zero")
*Critical strip.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.critical_strip))

In the {bpref "lfunction.normalization"}[analytic normalization], the {bpref "lfunction.functional_equation"}[functional equation] relates $`s` to $`1-s` and the
*critical strip* is the open strip $`\{ s \in {\mathbb{C}}: 0 < \Re(s) < 1 \}`.

In the arithmetic normalization, the functional equation relates $`s` to $`1 + w - s`,
where $`w` is the {bpref "lfunction.motivic_weight"}[motivic weight] of the L-function,
and the
*critical strip* is the open strip $`\{ s \in {\mathbb{C}}: w/2 < \Re(s) < w/2 + 1 \}`.

In either normalization, the {bpref "lfunction.dirichlet_series"}[Dirichlet series] and {bpref "lfunction.euler_product"}[Euler product] converge
absolutely to the right of the critical strip, and so the L-function
does not vanish there.  Therefore all nontrivial zeros
of the L-function lie in (the closure of) the critical strip.

Depends on: {uses "lfunction.dirichlet_series"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.motivic_weight"}[] {uses "lfunction.normalization"}[]
:::

:::definition "lfunction.degree" (lean := "AnalyticLFunction.degree, AnalyticLFunction.SelbergData.degree, AnalyticLFunction.exists_eulerFactor")
*Degree of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.degree))

The *degree* of an {bpref "lfunction"}[L-function] is the number $`J + 2K` of {bpref "lfunction.gamma_factor"}[Gamma factors] occurring in its {bpref "lfunction.functional_equation"}[functional equation]

$$`\Lambda(s) := N^{s/2}
\prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k)
\cdot L(s) = \varepsilon \overline{\Lambda}(1-s).`

The degree appears as the first component of the {bpref "lfunction.selbergdata"}[Selberg data] of $`L(s).` In all known cases it is the degree of the polynomial of the inverse of the Euler factor at any prime not dividing the {bpref "lfunction.conductor"}[conductor].

Depends on: {uses "lfunction"}[] {uses "lfunction.conductor"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[]
:::

:::definition "lfunction.dirichlet" (lean := "DirichletCharacter.LFunction, DirichletCharacter.LFunction_eq_LSeries, DirichletCharacter.LSeries_eulerProduct_tprod, DirichletCharacter.IsPrimitive.completedLFunction_one_sub, DirichletCharacter.rootNumber")
*Dirichlet L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.dirichlet))

A *Dirichlet L-function* is an {bpref "lfunction"}[L-function] defined by a {bpref "lfunction.dirichlet_series"}[Dirichlet series] of the form $`{\displaystyle L(s, \chi)=\sum_{n=1}^\infty \frac {\chi(n)}{n^s}}`, where $`\chi` is a {bpref "character.dirichlet"}[Dirichlet character].

Dirichlet L-functions can be meromorphically continued to the complex plane, have an {bpref "lfunction.euler_product"}[Euler product] $`{\displaystyle L(s, \chi)= \prod_p (1 - \chi(p) p^{-s} )^{-1}}`, and satisfy a {bpref "lfunction.functional_equation"}[functional equation] of the form

$$`\Lambda(s,\chi) = q^{s/2} \Gamma_{\mathbb{R}} (s) L(s,\chi) = \varepsilon_{\chi} \overline{\Lambda}(1-s),`

where $`q` is the {bpref "character.dirichlet.conductor"}[conductor] of $`\chi`.

These L-functions were introduced by [Peter Gustav Lejeune Dirichlet](https://en.wikipedia.org/wiki/Peter_Gustav_Lejeune_Dirichlet) in the mid-1800s as a tool to study prime numbers in arithmetic progressions.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "lfunction"}[] {uses "lfunction.dirichlet_series"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.dirichlet_series" (lean := "LSeries, LSeries.term, ArithmeticFunction")
*Dirichlet series.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.dirichlet_series))

A *Dirichlet series* is a formal series of the form $`F(s) = {\displaystyle \sum_{n=1}^{\infty} \frac{a_n}{ n^{s}}}`, where $`a_n \in {\mathbb{C}}`.
:::

:::definition "lfunction.dual" (lean := "LSeries, starRingEnd")
*Dual of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.dual))

The *dual* of an {bpref "lfunction"}[L-function] $`L(s) = \sum_{n=1}^{\infty} \frac{a_n}{n^s}` is the complex conjugate $`\bar{L}(s) = \sum_{n=1}^{\infty} \frac{\bar{a_n}}{n^s}`.

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.euler_product" (lean := "ArithmeticFunction.eulerProduct, ArithmeticFunction.ofPowerSeries, EulerProduct.eulerProduct_tprod")
*Euler product of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.euler_product))

It is expected that the *Euler product* of an {bpref "lfunction"}[L-function] of {bpref "lfunction.degree"}[degree] $`d` and {bpref "lfunction.conductor"}[conductor] $`N` can be written as

$$`L(s)=\prod_p L_p(s)`

where for  $`p\nmid N`

$$`L_p(s)=\prod_{n=1}^d  \left( 1-\frac{\alpha_{n}(p)}{p^s}\right)^{-1} \text{ with } |\alpha_{n}(p)|=1`

and
for $`p\mid N`,

$$`L_p(s)=\prod_{n=1}^{d_p}\left( 1-\frac{\beta_{n}(p)}{p^s}\right)^{-1} \text{ where } d_p < d \text{ and  } |\beta_n(p)|\le 1.`

The functions $`L_p(s)` are called *Euler factors* (or *local factors*).
:::

:::definition "lfunction.functional_equation" (lean := "AnalyticLFunction.SelbergData, AnalyticLFunction.SelbergData.gammaFactor, AnalyticLFunction.SelbergData.degree, AnalyticLFunction.completed_eq, AnalyticLFunction.completed_eq_sign_mul_conj")
*Functional equation of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.functional_equation))

All known {bpref "lfunction"}[analytic L-functions] have a *functional equation* that can be written in the form

$$`\Lambda(s) := N^{s/2}
\prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k)
\cdot L(s) = \varepsilon \overline{\Lambda}(1-s),`

where $`N` is an integer, {bpref "lfunction.gamma_factor"}[$`\Gamma_{\mathbb{R}}` and $`\Gamma_{\mathbb{C}}`] are defined in terms of the {bpref "specialfunction.gamma"}[$`\Gamma`-function,] $`\mathrm{Re}(\mu_j) = 0 \ \mathrm{or} \ 1` (assuming Selberg's eigenvalue conjecture), and $`\mathrm{Re}(\nu_k)` is a positive integer
or half-integer,

$$`\sum \mu_j + 2 \sum \nu_k \ \ \ \ \text{is real},`

and $`\varepsilon` is the {bpref "lfunction.sign"}[sign] of the functional equation.
With those restrictions on the {bpref "lfunction.spectral_parameters"}[spectral parameters], the
data in the functional equation is specified uniquely.  The integer $`d = J + 2 K`
is the {bpref "lfunction.degree"}[degree] of the L-function. The integer $`N` is  the {bpref "lfunction.conductor"}[conductor] (or level)
of the L-function.  The pair $`[J,K]` is the {bpref "lfunction.signature"}[signature] of the L-function.  The parameters
in the functional equation can be used to make up the 4-tuple called the {bpref "lfunction.selbergdata"}[Selberg data].

The {bpref "lfunction.selberg_class.axioms"}[axioms] of the {bpref "lfunction.selberg_class"}[Selberg class] are less restrictive than
given above.

Note that the functional equation above has the {bpref "lfunction.central_point"}[central point] at $`s=1/2`, and relates $`s\leftrightarrow 1-s`.

For many L-functions there is another normalization which is natural. The corresponding functional equation relates $`s\leftrightarrow w+1-s` for some positive integer $`w`,
called the {bpref "lfunction.motivic_weight"}[motivic weight] of the L-function. The central point is at $`s=(w+1)/2`, and the arithmetically normalized Dirichlet coefficients $`a_n n^{w/2}` are algebraic integers.

Depends on: {uses "lfunction.gamma_factor"}[] {uses "specialfunction.gamma"}[]
:::

:::definition "lfunction.gamma_factor" (lean := "Complex.Gammaℝ, Complex.Gammaℂ, Complex.Gammaℝ_mul_Gammaℝ_add_one")
*Gamma factors.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.gamma_factor))

The complex functions

$$`\Gamma_{\R}(s) := \pi^{-s/2}\Gamma(s/2)\qquad\text{and}\qquad \Gamma_{\C}(s):= 2(2\pi)^{-s}\Gamma(s)`

that appear in the {bpref "lfunction.functional_equation"}[functional equation] of an L-function are known as *gamma factors*.  Here $`\Gamma(s):=\int_0^\infty e^{-t}t^{s-1}dt` is Euler's gamma function.

The gamma factors satisfy
$`\Gamma_{\C}(s) = \Gamma_{\R}(s) \Gamma_{\R}(s + 1)`
and can also be viewed as "missing" factors of the {bpref "lfunction.euler_product"}[Euler product] of an L-function corresponding to (real or complex) archimedean places.

Depends on: {uses "lfunction.euler_product"}[]
:::

:::definition "lfunction.infinity_factor" (lean := "AnalyticLFunction.SelbergData.gammaFactor, AnalyticLFunction.completed_eq")
*Infinity factor of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.infinity_factor))

The *infinity factor* $`L_{\infty}(s)` of an {bpref "lfunction"}[L-function] $`L(s)` is the product of its {bpref "lfunction.gamma_factor"}[Gamma factors]:

$$`L_{\infty}(s) := \prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k).`

Here the $`\mu_j` and $`\nu_k` are the {bpref "lfunction.spectral_parameters"}[spectral parameters] of the L-function.

That is, the {bpref "lfunction.functional_equation"}[functional equation] has the form

$$`\Lambda(s) := L_{\infty}(s) L(s) = \varepsilon \overline{\Lambda}(1-s).`

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[] {uses "lfunction.spectral_parameters"}[]
:::

:::definition "lfunction.label"
*Label of L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.label))

Each {bpref "lfunction"}[L-function] $`L` has a label of the form d-N-q.k-x-y-i, where

- $`d` is the {bpref "lfunction.degree"}[degree] of $`L`.

- $`N` is the {bpref "lfunction.conductor"}[conductor] of $`L`.  When $`N` is a perfect power $`m^n` we write $`N` as $`m`e$`n`, since $`N` can be very large for some imprimitive L-functions.

- q.k is the {bpref "character.dirichlet.conrey"}[label] of the {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet"}[Dirichlet character] from which the {bpref "lfunction.central_character"}[central character] is {bpref "character.dirichlet.induce"}[induced].

- x-y is the {bpref "lfunction.spectral_label"}[spectral label] encoding the $`\mu_j` and $`\nu_j` in the {bpref "lfunction.normalization"}[analytically normalized] {bpref "lfunction.functional_equation"}[functional equation].

- i is a non-negative integer disambiguating between L-functions that would otherwise have the same label.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conrey"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.primitive"}[] {uses "lfunction"}[] {uses "lfunction.central_character"}[] {uses "lfunction.conductor"}[] {uses "lfunction.degree"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.normalization"}[] {uses "lfunction.spectral_label"}[]
:::

:::definition "lfunction.leading_coeff" (lean := "AnalyticLFunction.leadingCoeff, AnalyticLFunction.leadingCoeff_eq_iteratedDeriv, AnalyticLFunction.meromorphicTrailingCoeffAt_arithmeticNormalization, AnalyticAt.meromorphicTrailingCoeffAt_eq_iteratedDeriv_div_factorial, meromorphicTrailingCoeffAt")
*Leading coefficient.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.leading_coeff))

The *leading coefficient* of an {bpref "lfunction.arithmetic"}[arithmetic L-function] is the first nonzero coefficient of its Laurent series expansion at the {bpref "lfunction.central_point"}[central point].

Depends on: {uses "lfunction.arithmetic"}[] {uses "lfunction.central_point"}[]
:::

:::definition "lfunction.motivic_weight" (lean := "AnalyticLFunction.motivicWeight, AnalyticLFunction.arithmeticCoeff, AnalyticLFunction.isIntegral_arithmeticCoeff_motivicWeight")
*Motivic weight.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.motivic_weight))

The *motivic weight* (or *arithmetic weight*) of an {bpref "lfunction.arithmetic"}[arithmetic] {bpref "lfunction"}[L-function] with {bpref "lfunction.normalization"}[analytic normalization] $`L_{an}(s)=\sum_{n=1}^\infty a_nn^{-s}` is the least nonnegative integer $`w` for which $`a_nn^{w/2}` is an algebraic integer for all $`n\ge 1`.

If the L-function arises from a motive, then the weight of the motive has the
same parity as the motivic weight of the L-function, but the weight of the motive
could be larger.  This apparent discrepancy comes from the fact that a Tate twist
increases the weight of the motive.  This corresponds to the change of variables
$`s \mapsto s + j` in the L-function of the motive.

Depends on: {uses "lfunction"}[] {uses "lfunction.arithmetic"}[] {uses "lfunction.normalization"}[]
:::

:::definition "lfunction.normalization" (lean := "AnalyticLFunction.arithmeticNormalization, AnalyticLFunction.arithmeticCoeff, AnalyticLFunction.arithmeticNormalization_eq_LSeries, AnalyticLFunction.completed_sub_eq_sign_mul_conj, AnalyticLFunction.motivicWeight")
*Normalization of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.normalization))

In its *arithmetic normalization*, an L-function $`L(s)` of weight $`w` has its {bpref "lfunction.central_value"}[central value] at $`s=\frac{w+1}{2}`
and the {bpref "lfunction.functional_equation"}[functional equation] relates
$`s` to $`1 + w - s`.
For L-functions defined by an Euler product $`\prod_p L_p(s)^{-1}` where the coefficients of $`L_p` are algebraic integers, this is the usual normalization implied by the definition.

The *analytic normalization* of an L-function is defined by $`L_{an}(s):=L(s+w/2)`, where $`L(s)` is the L-function in its arithmetic normalization.  This moves the central value to $`s=1/2`, and the {bpref "lfunction.functional_equation"}[functional equation] of $`L_{an}(s)` relates $`s` to $`1-s`.

Depends on: {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.primitive" (lean := "AnalyticLFunction.IsPrimitive, AnalyticLFunction.IsTrivial, AnalyticLFunction.one, AnalyticLFunction.mul, AnalyticLFunction.isPrimitive_zeta")
*Primitive L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.primitive))

An L-function is <b>primitive</b> if it cannot be written as a product of nontrivial L-functions.  The "trivial L-function" is the constant function $`1`.
:::

:::definition "lfunction.rational" (lean := "AnalyticLFunction.arithmeticCoeff, AnalyticLFunction.motivicWeight, IntermediateField.adjoin")
*Rational L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.rational))

A *rational* L-function $`L(s)` is an {bpref "lfunction.arithmetic"}[arithmetic] L-function with {bpref "lfunction.coefficient_field"}[coefficient field] $`\Q`; equivalently, its {bpref "lfunction.euler_product"}[Euler product] in the {bpref "lfunction.normalization"}[arithmetic normalization] can be written as a product over rational primes

$$`L(s)=\prod_pL_p(p^{-s})^{-1}`

with $`L_p\in \Z[T]`.

Depends on: {uses "lfunction.arithmetic"}[] {uses "lfunction.coefficient_field"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.normalization"}[]
:::

:::definition "lfunction.rh" (lean := "AnalyticLFunction.RiemannHypothesis, GeneralizedRiemannHypothesis, AnalyticLFunction.zeros, riemannHypothesis_iff_zeta, RiemannHypothesis")
*Generalized Riemann hypothesis.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.rh))

The *Riemann hypothesis* is the assertion that if $`\rho` is a zero of an
 {bpref "lfunction"}[analytic L-function] then $`\mathrm{Re}(\rho)>0` implies
that $`\mathrm{Re}(\rho)=1/2.`

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.riemann" (lean := "riemannZeta, AnalyticLFunction.zeta, zeta_eq_tsum_one_div_nat_cpow, completedRiemannZeta_one_sub, riemannZeta_residue_one")
*Riemann zeta-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.riemann))

The *Riemann zeta-function* is defined by the {bpref "lfunction.dirichlet_series"}[Dirichlet series]

$$`\zeta(s)=\sum_{n=1}^\infty \frac 1{n^s},`

which converges for $`s=\sigma+it` with $`\sigma>1`. Euler showed that

$$`\zeta(s)=\prod_p (1-p^{-s})^{-1},`

known today as the {bpref "lfunction.euler_product"}[Euler product], for $`s` a real number with $`s>1`, a fact that connects the study of $`\zeta(s)` with the prime numbers.
 Riemann, in 1859,  was the first to consider $`\zeta(s)`  as a function of a complex variable.  He proved that $`\zeta(s)` has an analytic continuation to the whole complex plane apart from a simple pole at $`s=1` with residue 1. Riemann proved a remarkable {bpref "lfunction.functional_equation"}[functional equation]. He showed that

$$`\xi(s):=\frac 12 s (s-1) \pi^{-s/2} \Gamma(s/2) \zeta(s)`

is an entire function of order 1 which satisfies

$$`\xi(s)=\xi(1-s).`

Riemann showed that the distribution of prime numbers depends on the location of the {bpref "lfunction.zeros"}[zeros] of the Riemann zeta-function which, by the Euler product and functional equation, are all in the {bpref "lfunction.critical_strip"}[critical strip] $`0\le \sigma \le 1`. Riemann showed that the number $`N(T)` of zeros of
$`\zeta(s)` in the critical strip with ordinates at most $`T` satisfies

$$`N(T)=\frac{T}{2\pi} \log\frac{T}{2\pi e} +O(\log T).`

He calculated the first few zeros and verified that they are on the {bpref "lfunction.critical_line"}[critical line] $`\sigma=1/2` and then made his famous conjecture, today known as the {bpref "lfunction.rh"}[Riemann Hypothesis], that all of the zeros are on the critical line. In 1896 Hadamard and de la Vallee Poussin independently proved that $`\zeta(s)` has no zeros on the boundary of the critical strip, i.e. all of the zeros are in the open strip $`0< \sigma < 1`,
and in doing so proved the Prime Number Theorem, that the number of primes less than a large number $`x` is asymptotic to $`\frac{x}{\log x}`.

Today we know that the first 10 trillion zeros of $`\zeta(s)` are all on the critical line and that at least 41% of all of the complex zeros are on the critical line.

Depends on: {uses "lfunction.critical_line"}[] {uses "lfunction.critical_strip"}[] {uses "lfunction.dirichlet_series"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.rh"}[] {uses "lfunction.zeros"}[]
:::

:::definition "lfunction.riemann.euler_product" (lean := "riemannZeta_eulerProduct_tprod, riemannZeta_eulerProduct_hasProd")
*Euler product for the Riemann zeta function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.riemann.euler_product))

The *Euler product* for the Riemann zeta function is its expansion as the infinite product

$$`\zeta(s) = \prod_{p \textrm{ prime}} \frac{1}{1-p^{-s}}.`

This expansion holds in the region $`\Re(s)>1,` where the product is absolutely convergent. The first proof of this expansion, due to Euler (1737), is based on the fact that every positive integer $`n` can be written uniquely as a product of primes. Namely, for $`\Re(s) >1,`

$$`\prod_{p } \frac{1}{1-p^{-s}} = \prod_p \left(\sum_{k=0}^\infty p^{-ks} \right) = \sum_{n=1}^\infty n^{-s} = \zeta(s).`
:::

:::definition "lfunction.root_analytic_conductor" (lean := "AnalyticLFunction.rootAnalyticConductor, AnalyticLFunction.rootAnalyticConductor_pow_degree")
*Root analytic conductor.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.root_analytic_conductor))

If $`d` is the {bpref "lfunction.degree"}[degree] of the {bpref "lfunction"}[L-function] $`L(s)`, the *root analytic conductor* $`\alpha` of $`L` is the $`d`th root of the {bpref "lfunction.analytic_conductor"}[analytic conductor] of $`L`.  It plays a role analogous to the {bpref "nf.root_discriminant"}[root discriminant] for {bpref "nf"}[number fields].

Depends on: {uses "lfunction"}[] {uses "lfunction.analytic_conductor"}[] {uses "lfunction.degree"}[] {uses "nf"}[] {uses "nf.root_discriminant"}[]
:::

:::definition "lfunction.root_angle" (lean := "AnalyticLFunction.sign, Complex.arg, AnalyticLFunction.norm_sign")
*Root angle of L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.root_angle))

The *root angle* of an L-function is the argument of its {bpref "lfunction.sign"}[root number], as a real number $`\alpha` with $`-0.5 < \alpha \le 0.5`.

Depends on: {uses "lfunction.sign"}[]
:::

:::definition "lfunction.root_number" (lean := "AnalyticLFunction.sign, AnalyticLFunction.SelbergData.sign, AnalyticLFunction.norm_sign")
*Sign of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.root_number))

The *sign* of an {bpref "lfunction"}[L-function] is the complex number $`\varepsilon` occurring in its {bpref "lfunction.functional_equation"}[functional equation]

$$`\Lambda(s) := N^{s/2}
\prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k)
\cdot L(s) = \varepsilon \overline{\Lambda}(1-s).`

It appears as the fourth component of the {bpref "lfunction.selbergdata"}[Selberg data] of L.

If all of the coefficients of the Dirichlet series defining $`L(s)` are real, then necessarily
$`\varepsilon = \pm 1`.  If the coefficients are real and $`\varepsilon = - 1`,
then $`L(1/2)=0`.

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.selberg_class" (lean := "LSeries.selbergClass, LSeries.delta_mem_selbergClass")
*Selberg class of L-functions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.selberg_class))

The *Selberg class* $`\mathcal{S}` is the set of
all {bpref "lfunction.dirichlet_series"}[Dirichlet series]
that satisfy the four {bpref "lfunction.selberg_class.axioms"}[Selberg class axioms].  The set $`\mathcal{S}` was defined by [Atle Selberg](https://en.wikipedia.org/wiki/Atle_Selberg), who conjectured that its elements all satisfy the {bpref "lfunction.rh"}[Riemann hypothesis.]

Depends on: {uses "lfunction.dirichlet_series"}[] {uses "lfunction.rh"}[] {uses "lfunction.selberg_class.axioms"}[]
:::

:::definition "lfunction.selberg_class.axioms" (lean := "LSeries.SelbergAxioms, LSeries.SelbergAnalyticity, LSeries.RamanujanHypothesis, LSeries.SelbergFunctionalEquation, LSeries.SelbergEulerProduct")
*Selberg class axioms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.selberg_class.axioms))

The *Selberg axioms* for $`F(s)=\sum_{n=1}^\infty \frac{a_n}{n^s}` in the {bpref "lfunction.selberg_class"}[Selberg class] are:
<ol>
<li>   Analyticity: $`(s-1)^mF(s)` is an entire function of
finite order for some non-negative integer $`m`
<li> Ramanujan Hypothesis: $`a_n = O_{\epsilon}(n^\epsilon)` for any fixed $`\epsilon>0`
<li>  {bpref "lfunction.functional_equation"}[Functional equation]: there is a function $`\gamma_F(s)` of the
form

$$`\gamma_F(s)=\epsilon Q^s \prod_{i=1}^k\Gamma(\lambda_is+\mu_i)`

where $`|\epsilon|=1`, $`Q>0`, $`\lambda_i>0`, and Re$`(\mu_i)\ge 0`
such that
$$`\Lambda(s)=\gamma_F(s)F(s)`

satisfies

$$`\Lambda(s)=\overline{\Lambda}(1-s)`

where $`\overline{\Lambda}(s)=\overline{\Lambda(\overline{s})}`.</li>
<li>  {bpref "lfunction.euler_product"}[Euler product]: $`a_1=1`,
 and
$$`\log F(s)=\sum_{n=1}^\infty \frac{b_n}{n^s}`

where $`b_n=0` unless $`n` is a positive power of a prime
and $`b_n\ll n^\theta` for some $`\theta<1/2`.</li>
</ol>

Depends on: {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.selbergdata" (lean := "AnalyticLFunction.SelbergData, AnalyticLFunction.selbergData, AnalyticLFunction.SelbergData.degree")
*Selberg data for the functional equation of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.selbergdata))

The *Selberg data* for an {bpref "lfunction"}[L-function] is the quadruple
$`(d, N,(\mu_1,\ldots,\mu_J:\nu_1,\ldots,\nu_K),\varepsilon)` obtained from the parameters in the {bpref "lfunction.normalization"}[analytically normalized] {bpref "lfunction.functional_equation"}[functional equation].

Here $`d=J+2K` is the {bpref "lfunction.degree"}[degree] of the
L-function, $`N` is the  {bpref "lfunction.conductor"}[conductor] of the
L-function, the set of $`\mu_j` and $`\nu_k`
arising from the {bpref "lfunction.gamma_factor"}[$`\Gamma_{\mathbb{R}}` and $`\Gamma_{\mathbb{C}}`] factors, respectively,
are the {bpref "lfunction.spectral_parameters"}[spectral parameters], and $`\varepsilon` is the {bpref "lfunction.root_number"}[sign] of the L-function.

Depends on: {uses "lfunction"}[] {uses "lfunction.conductor"}[] {uses "lfunction.degree"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[] {uses "lfunction.normalization"}[] {uses "lfunction.root_number"}[] {uses "lfunction.spectral_parameters"}[]
:::

:::definition "lfunction.self-dual" (lean := "LSeries, starRingEnd, Complex.conj_eq_iff_real")
*Self-dual L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.self-dual))

An L-function $`L(s) = \sum_{n=1}^{\infty} \frac{a_n}{n^s}` is called *self-dual* if its Dirichlet coefficients $`a_n` are real.
:::

:::definition "lfunction.sign" (lean := "AnalyticLFunction.sign, AnalyticLFunction.SelbergData.sign, AnalyticLFunction.norm_sign, AnalyticLFunction.completed_eq_sign_mul_conj")
*Sign of the functional equation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.sign))

The *sign* of the functional equation of an analytic L-function, also called the *root number*, is the complex number $`\varepsilon` that appears in the {bpref "lfunction.functional_equation"}[functional equation] of $`\Lambda(s)=\varepsilon \overline{\Lambda}(1-s)`.  The sign appears as the 4th entry in the quadruple
known as the {bpref "lfunction.selbergdata"}[Selberg data.]

Depends on: {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.signature" (lean := "AnalyticLFunction.SelbergData.μ, AnalyticLFunction.SelbergData.ν, AnalyticLFunction.SelbergData.re_eq_zero_or_one_of_mem_μ, AnalyticLFunction.SelbergData.exists_two_mul_re_eq_of_mem_ν")
*Signature of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.signature))

The *signature* either refers to the pair $`[J,K]` where $`J` is the number of {bpref "lfunction.gamma_factor"}[$`\Gamma_{\mathbb{R}}`] and $`K` is the number of {bpref "lfunction.gamma_factor"}[$`\Gamma_{\mathbb{C}}`] in the {bpref "lfunction.selbergdata"}[Selberg data], or else it refers to the tuple

$$`(\Re(\mu_1),\ldots,\Re(\mu_J); 2\Re(\nu_1),\ldots,2\Re(\nu_K)).`

Note that the entries in that tuple are non-negative integers.

Depends on: {uses "lfunction.gamma_factor"}[] {uses "lfunction.selbergdata"}[]
:::

:::definition "lfunction.spectral_label" (lean := "AnalyticLFunction.SelbergData.spectralLabel, AnalyticLFunction.spectralLabel, AnalyticLFunction.spectralLabelRe, AnalyticLFunction.spectralLabelIm, AnalyticLFunction.SelbergData.prod_labelμ_mul_prod_labelν")
*Spectral label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.spectral_label))

The {bpref "lfunction.spectral_parameters"}[spectral parameters] are encoded as a string "x-y".  Here x is the concatenation of expressions of the form r$`u` and c$`v`.  The first indicates that $`\Gamma_{\R}(s + \mu)` appears in the {bpref "lfunction.functional_equation"}[functional equation] with $`\Re(\mu) = u`, and the second that $`\Gamma_{\C}(s + \nu)` appears with $`2\Re(\nu) = v`.  The factor of $`2` is included so that the $`u` and $`v`s are integral.  In the multiset of $`u` and $`v`s, if the multiplicities are all a multiple of an integer $`n > 1` then we use e$`n` to shorten x.  For example, r0r0c0c0 is encoded r0c0e2.  The $`\Gamma_{\R}` terms and $`\Gamma_{\C}` terms are separately sorted, and we use the identity $`\Gamma_{\C}(s) = \Gamma_{\R}(s)\Gamma_{\R}(s + 1)` as much as possible to combine pairs $`\Gamma_{\R}(s + \mu)\Gamma_{\R}(s + \mu + 1)` into $`\Gamma_{\C}(s + \mu)` in the interest of brevity.

Similarly, y is either 0 (indicating that all $`\mu_j` and $`\nu_j` are real), or the concatenation of expressions of the form p$`t`, m$`t` or c$`t` indicating complex numbers with imaginary part either $`t` or $`-t` or both (respectively).  These imaginary parts are listed in the same order as the real parts and are sorted by increasing absolute value within parameters with the same real part.  We round imaginary parts to two digits after the decimal point.  We write p0 when the imaginary part is zero to the known precision, and p0.00 and m0.00 for imaginary parts with an absolute value smaller than $`0.5 \cdot 10^{-2}`.

Depends on: {uses "lfunction.functional_equation"}[] {uses "lfunction.spectral_parameters"}[]
:::

:::definition "lfunction.spectral_parameters" (lean := "AnalyticLFunction.SelbergData.μ, AnalyticLFunction.SelbergData.ν, AnalyticLFunction.SelbergData.gammaFactor")
*L-function spectral parameters.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.spectral_parameters))

The *spectral parameters* are the numbers $`\mu_j` and $`\nu_k` that appear as shifts in the {bpref "lfunction.gamma_factor"}[gamma factors] ($`\Gamma_{\mathbb{R}}` and $`\Gamma_{\mathbb{C}}`, respectively) in the {bpref "lfunction.functional_equation"}[functional equation] of an {bpref "lfunction"}[L-function].

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[]
:::

:::definition "lfunction.symm"
*Symmetric power of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.symm))

Let $`L(s)` be an L-function given by an Euler product

$$`L(s)= \prod_{p\not\in S} \prod_{j=1}^r \left (1-
\frac{\alpha_j}{p^s}\right)^{-1} \times \prod_{p \in S} L_p(s),`

where $`S` is a finite set of primes.  The  symmetric $`n`-th power of $`L(s)` is an L-function given by an Euler product

$$`L(s,\mathrm{sym}^n) = \prod_{p\not\in S}\prod_{ { \mathrm{degree}-n} \atop  \mathrm{monomials}\,m} \left( 1-
\frac{m(\alpha_1,\dotsc,\alpha_r)}{p^s} \right)^{-1} \times
\prod_{p\in S} L_p(s,\mathrm{sym}^n).`

The Euler factors at the primes $`p\in S` (the  "bad" primes) are computed via a more complicated recipe which involves a non-trivial amount of information about the underlying object.   The degree of an Euler factor at one of the bad primes will be smaller than the degree of the Euler factors outside the set $`S`.
:::

:::definition "lfunction.trivial_zero" (lean := "AnalyticLFunction.trivialZeros, AnalyticLFunction.SelbergData.gammaPoles, AnalyticLFunction.zeros")
*Trivial zeros of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.trivial_zero))

The {bpref "lfunction.zeros"}[zeros] of an L-function $`L(s)` that occur at
poles of its  {bpref "lfunction.gamma_factor"}[gamma factors] are *trivial zeros*.

The presence of trivial zeros is required by the {bpref "lfunction.functional_equation"}[functional equation].  In its {bpref "lfunction.normalization"}[analytic normalization], the L-function $`L(s)` has no zeros or poles in the right half-plane $`\Re(s)>1`, but the {bpref "lfunction.gamma_factor"}[gamma factors] that appear in the functional equation have poles.  Since the {bpref "lfunction.completed"}[completed L-function] has no poles (except possibly from Riemann zeta-function factors),
the L-function must have zeros at poles of the gamma factors.

For {bpref "lfunction.arithmetic"}[arithmetic] L-functions, the poles are at certain negative integers.

Depends on: {uses "lfunction.arithmetic"}[] {uses "lfunction.completed"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[] {uses "lfunction.normalization"}[] {uses "lfunction.zeros"}[]
:::

:::definition "lfunction.zeros" (lean := "AnalyticLFunction.zeros, AnalyticLFunction.lowestZero, AnalyticLFunction.centralPoint_add_lowestZero_mul_I_mem_zeros, AnalyticLFunction.lowestZero_le")
*Zeros of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.zeros))

The *zeros* of an {bpref "lfunction"}[L-function] $`L(s)` are the complex numbers $`\rho` for which $`L(\rho)=0`.

Under the {bpref "lfunction.rh"}[Riemann Hypothesis], every {bpref "lfunction.trivial_zero"}[non-trivial zero] $`\rho` lies on the {bpref "lfunction.critical_line"}[critical line] $`\Re(s)=1/2` (in the {bpref "lfunction.normalization"}[analytic normalization]).

The *lowest zero* of an L-function $`L(s)` is the least $`\gamma>0` for which $`L(1/2+i\gamma)=0`. Note that even when $`L(1/2)=0`, the lowest zero is by definition a positive real number.

Depends on: {uses "lfunction"}[] {uses "lfunction.critical_line"}[] {uses "lfunction.normalization"}[] {uses "lfunction.rh"}[]
:::

:::definition "lfunction.zfunction" (lean := "AnalyticLFunction.zFunction, riemannSiegelTheta, exp_riemannSiegelTheta_mul_I, ofReal_hardyZ_eq_exp_mul_riemannZeta, AnalyticLFunction.ofReal_zFunction")
*Z-function of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.zfunction))

The (Hardy or Riemann-Siegel) *Z-function* for the Riemann zeta-function is  a real-valued function defined in terms of the values of $`\zeta(s)` on the {bpref "lfunction.critical_line"}[ critical line] via the formula

$$`Z(t) := e^{i \theta(t)} \zeta\left( \frac{1}{2} + it \right),`

where $`\theta(t)` is the *Riemann-Siegel theta function*

$$`\theta(t) := \arg \left(\Gamma\left(\frac{2it+1}{4}\right)\right) -\frac{\log\pi}{2}t.`

There is a bijection between zeros $`t_0` of $`Z(t)` and zeros $`\frac{1}{2}+it_0` of $`\zeta(s)`.

The  *Z-function* of a general L-function is a smooth real-valued function of a real variable $`t` such that

$$`|Z(t)|=|L(1/2+it)|.`

Specifically, if we write the completed L-function as $`\Lambda(s)=\gamma(s)L(s),` where $`\Lambda(s)` satisfies the {bpref "lfunction.functional_equation"}[functional equation]

$$`\Lambda(s)=\varepsilon \overline{\Lambda}(1-s),`

then $`Z(t)` is defined by

$$`Z(t)=\overline{\varepsilon}^{1/2} \frac{\gamma(1/2+it)}{|\gamma(1/2+it)|} L(1/2+it).`

The square root is chosen so that $`Z(t)>0` for sufficiently small $`t>0`.

The multiset of zeros of $`Z(t)` matches that of $`L(1/2+it)` and $`Z(t)` changes sign at the zeros of $`L(1/2+it)` of odd multiplicity.

Depends on: {uses "lfunction.critical_line"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "specialfunction.gamma" (lean := "Complex.Gamma")
*Euler gamma function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/specialfunction.gamma))

The *(Euler) gamma function $`\Gamma(z)`* is defined by the integral

$$`\Gamma(z) = \int_0^{ \infty } e^{-t} t^{z} \frac{dt}{t}`

for Re$`(z) > 0`. It satisfies the functional equation

$$`\Gamma(z+1) = z \Gamma(z),`

and can thus be continued into a meromorphic function on the complex plane, whose poles are at the non-positive integers $`\{0,-1,-2,\ldots\}`.
:::
