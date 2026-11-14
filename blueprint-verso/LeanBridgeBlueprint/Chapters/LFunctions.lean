import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "L-functions" =>

This chapter lists the LMFDB definitions in the category `lfunction`. Each definition links back to its LMFDB knowl. `af`, `af.bernoulli_numbers`, `af.divisor_function`, `af.multiplicative` and `specialfunction.gamma` also belong here, although their ids put them in another LMFDB category. It also lists the knowls about the LMFDB's data on this subject that have mathematical content, from the categories `intro` and `rcs`.

:::definition "af" (lean := "ArithmeticFunction")
*Arithmetic function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af))

An *arithmetic function* is a complex-valued function whose domain is the positive integers.

Tau Ceti Review: [`ArithmeticFunction`](https://taucetiproject.org/review/#/d/ArithmeticFunction).
:::

:::definition "af.bernoulli_numbers" (lean := "bernoulli, bernoulliPowerSeries, bernoulliPowerSeries_mul_exp_sub_one, bernoulliSeries, radius_bernoulliSeries")
*Bernoulli numbers.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.bernoulli_numbers))

The *Bernoulli numbers* are the rational numbers $`B_n` that appear as coefficients of the formal power series

$$`\frac{T}{e^T-1}=\sum_{n\ge 0}B_n\frac{T^n}{n!},`

which has radius of convergence $`2\pi`.

Tau Ceti Review: [`bernoulli`](https://taucetiproject.org/review/#/d/bernoulli), [`bernoulliPowerSeries`](https://taucetiproject.org/review/#/d/bernoulliPowerSeries), [`bernoulliPowerSeries_mul_exp_sub_one`](https://taucetiproject.org/review/#/d/bernoulliPowerSeries_mul_exp_sub_one).
:::

:::definition "af.divisor_function" (lean := "ArithmeticFunction.divisorFunction, ArithmeticFunction.isMultiplicative_divisorFunction, ArithmeticFunction.divisorFunction_natCast, ArithmeticFunction.sigma")
*Divisor function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.divisor_function))

A *divisor function* is a {bpref "af.multiplicative"}[multiplicative] {bpref "af"}[arithmetic function] of the form

$$`\sigma_{\tau}(n)=\sum_{d\mid n}d^\tau,`

for some fixed $`\tau\in\mathbb{C}`.

Tau Ceti Review: [`ArithmeticFunction.sigma`](https://taucetiproject.org/review/#/d/ArithmeticFunction.sigma).

Depends on: {uses "af"}[] {uses "af.multiplicative"}[]
:::

:::definition "af.multiplicative" (lean := "ArithmeticFunction.IsMultiplicative")
*Multiplicative arithmetic function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/af.multiplicative))

An arithmetic function $`f:\mathbb{Z}_{>0}\to \C` is *multiplicative* if $`f(mn)=f(m)f(n)` for all coprime integers $`m,n>0`, and is not the zero-function (in particular, $`f(1)=1`).

Tau Ceti Review: [`ArithmeticFunction.IsMultiplicative`](https://taucetiproject.org/review/#/d/ArithmeticFunction.IsMultiplicative).
:::

:::definition "intro.features"
*Introduction/Features.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/intro.features))

In the LMFDB, we aim for every object to have its own homepage.  Note
the following features:

*Knowls:*  Interspersed throughout the LMFDB are underlined words.
These words represent knowls, which are bits of context free
information.  A knowl is identified by a word or phrase underlined
with a dotted line.  Clicking on a knowl brings up a box of text containing information about the object.
Clicking on the knowl a second time will retract the box of text.

*Navigating:*

- \**Browsing:*\* One way to investigate information on the database is

through browsing.  For each type of object in the database, you can
browse by distinguishing features.  For example, to look for
information about L-functions, you can browse by {bpref "lfunction.degree"}[degree] or {bpref "lfunction.underlying_object"}[underlying object].

- \**Searching:*\*  Another way to investigate is through searching.  You

can search either by using a label to find a specific object or by
specifying certain characteristics an object may have.  For each of
these types of searching, there is an example in grey text, and a
description of possible inputs.  Some fields may be left blank (or
with grey text) in a search.

- \**Navigation Bars:*\* On a given page, additional headings may appear in

the navigation bar.  For example Learn More About, which contains additional
information, and Downloads or Data, for files.

- \**Breadcrumbs:*\*  On the top left of the header of a given page there is

a description of your current path of navigation.  Clicking on an item
in the path will take you back to that page.

*Properties:*  On the upper right hand side of a homepage for an object
there is often a box containing specific properties of the object.
This box can be closed and opened by clicking on the vertical arrow.

*Related Objects:*  Often below the properties box in the upper right hand side of a homepage for an object is a box containing links to the homepages of directly related objects.

*Zeros of L-functions Search:*  For each L-function in the database we
have identified the lowest {bpref "lfunction.zeros"}[zero] above the real axis.  It is believed
that the value of this zero uniquely identifies an L-function.  This
gives an interesting and useful way of identifying an L-function.

*Downloading:*  You may download available data, for example moment polynomials of the zeta function.  Some data is available to download within a page, while other data may be obtained through a link in the navigation bar.

*Feedback:*  If you encounter any issues or problems while using the LMFDB, please click on Feedback in the upper right hand corner of the header to file a report.

Depends on: {uses "lfunction.degree"}[] {uses "lfunction.zeros"}[]
:::

:::definition "intro.tutorial"
*A tour of the Riemann zeta function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/intro.tutorial))

The simplest of all {bpref "lfunction"}[L-functions] is the {bpref "lfunction.riemann"}[Riemann zeta function], a
function whose analytic properties were first discovered by [Bernhard Riemann](https://en.wikipedia.org/wiki/Bernhard_Riemann) in
1859 in his attempts to find a formula for the number of primes
smaller than a given number $`x`. It gives us a model for how to think
about other L-functions.

Let's begin by  taking a look at this prototype:
[the Riemann zeta function homepage](https://beta.lmfdb.org/L/Riemann/).

The first thing we see is that the Riemann zeta function can be
defined as a special type of infinite series, called a {bpref "lfunction.dirichlet_series"}[Dirichlet
series]:

$`\zeta(s):=1+\frac1{2^s}+\frac1{3^s}+\frac1{4^s}+\cdots.`

This is the classical definition of $`\zeta(s)` and holds in the half
plane $`Re(s)>1`.

All L-functions can be expressed as Dirichlet series. On this website
we {bpref "lfunction.normalization"}[normalize] each Dirichlet series so
that it converges absolutely for  $`Re (s)>1`.

The page then exhibits the {bpref "lfunction.functional_equation"}[functional equation], an equation that
relates the values of this L-function on the left and on the right of
the line $`Re (s)= 1/2`. A key component of the functional equation is that it
involves {bpref "specialfunction.gamma"}[Euler's Gamma function], which is well known as a function
that interpolates factorials.
Again, this is typical of all L-functions: there is a functional
equation involving the product of the L-function and some
Gamma functions and relates the values at $`s` and $`1-s`.  The {bpref "lfunction.selbergdata"}[Selberg data] is a way of encoding the functional equation; details at the bottom of this page.

The page then goes on by showing the {bpref "lfunction.euler_product"}[Euler product] formula of the
L-function. In the case of $`\zeta(s)`, this was discovered by [Leonhard Euler](https://en.wikipedia.org/wiki/Leonhard_Euler)
and later used by Riemann as a starting point for investigating
prime numbers. In particular, Riemann showed that the distribution of
prime numbers is determined by the location of the {bpref "lfunction.zeros"}[zeros] of
$`\zeta(s)`.  All L-functions have an Euler product, i.e. they have an
expression as an infinite product over primes where the factor for
each prime is the inverse of a polynomial in $`p^{-s}`.

Next we find the imaginary parts of the first few zeros of the Riemann
zeta function.
Riemann's Hypothesis is that any {bpref "lfunction.trivial_zero"}[non-trivial zero] of the zeta function
has real part 1/2.  Moreover, it's hypothesized that any non-trivial zero of any L-function has real part 1/2.  This is true, so far, for
every zero ever found. Consequently on these pages we only display the
imaginary parts of the zeros. The first non-trivial zero of the
Riemann zeta function
is at $`1/2+ i 14.1347...` and was actually computed by Riemann himself.
It has been checked that the first 10 trillion zeros of the Riemann zeta
function all have real part 1/2, where the zeros are written in increasing
order of their imaginary part.
On these pages we have high precision rendering of the first 36
billion zeros; see [http://www.lmfdb.org/zeros/zeta/](http://www.lmfdb.org/zeros/zeta/).

Further information found on the Riemann zeta function page is the
list of values the function takes at some special points.  Again, this
is typical of L-functions. The special values of L-functions form a
remarkable area of modern research. The {bpref "ec.q.bsdconjecture"}[Birch and Swinnerton-Dyer
Conjecture], mentioned
above as one of the Clay Millennium problems, has to do with the
special values of L-functions
associated with {bpref "ec.q"}[elliptic curves].

Finally the page concludes by displaying the graph of the {bpref "lfunction.zfunction"}[Hardy
Z-function]. This function has the same modulus as $`\zeta(s)` on the {bpref "lfunction.critical_line"}[critical line], so its graph helps to provide a visual picture of the Riemann
zeta function. In particular, the Z-function has the same zeros as the
L-function and so for this one we can see the first zero at 14.1347...

In order to successfully navigate the L-functions pages you need to
know a little bit about how we classify L-functions. As we mentioned,
each L-function has a Dirichlet series, a functional equation, and an
Euler product.
We sort our L-functions first by {bpref "lfunction.degree"}[degree], then by {bpref "lfunction.conductor"}[conductor].

There is a certain amount of compatibility between these expressions.
For example, it is believed that the Euler product can always be
written as a product over  primes
of the inverse of a  polynomial in $`p^{-s}`. In all known cases, at almost all
primes the
degree of this polynomial is the same as the number of
{bpref "lfunction.gamma_factor"}[Gamma factors] in the functional equation!

We specify a functional equation  by providing its {bpref "lfunction.selbergdata"}[Selberg data];
this is a 4-tuple which has the shape
({bpref "lfunction.degree"}[degree],
{bpref "lfunction.conductor"}[conductor], {bpref "lfunction.spectral_parameters"}[Gamma-shifts],
{bpref "lfunction.root_number"}[sign]),
or:

$`(d,N,(\mu_1,\dots , \mu_{J}:\nu_{1},\dots ,\nu_{K}),\varepsilon).`

Here the degree $`d=J+2K` is a positive integer, the {bpref "lfunction.conductor"}[conductor] $`N` is a
positive integer, the $`\mu` are complex numbers with non-negative real parts and
imaginary parts which sum to 0, and the sign $`\epsilon` is a
complex number with absolute value $`1`.

For example, the LMFDB page for the Riemann zeta function identifies
its Selberg data using the notation $`(1,1,(0:),1)`, where the first value $`1` is the
{bpref "lfunction.degree"}[degree], the second is the {bpref "lfunction.conductor"}[conductor], $`(0:)` indicates the {bpref "lfunction.spectral_parameters"}[spectral
parameters] and the last $`1` is the {bpref "lfunction.sign"}[sign] of the functional equation.

Depends on: {uses "ec.q"}[] {uses "ec.q.bsdconjecture"}[] {uses "lfunction"}[] {uses "lfunction.conductor"}[] {uses "lfunction.critical_line"}[] {uses "lfunction.degree"}[] {uses "lfunction.dirichlet_series"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[] {uses "lfunction.normalization"}[] {uses "lfunction.riemann"}[] {uses "lfunction.root_number"}[] {uses "lfunction.selbergdata"}[] {uses "lfunction.sign"}[] {uses "lfunction.spectral_parameters"}[] {uses "lfunction.trivial_zero"}[] {uses "lfunction.zeros"}[] {uses "lfunction.zfunction"}[] {uses "specialfunction.gamma"}[]
:::

:::definition "lfunction" (lean := "AnalyticLFunction, AnalyticLFunction.SelbergData, AnalyticLFunction.selbergData, AnalyticLFunction.eqOn_toFun_of_coeff_eq, AnalyticLFunction.zeta, LSeries")
*L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction))

An (analytic) *L-function* is a {bpref "lfunction.dirichlet_series"}[Dirichlet series] that has an {bpref "lfunction.euler_product"}[Euler product] and satisfies a certain type of {bpref "lfunction.functional_equation"}[functional equation].

It is expected that all L-functions satisfy the {bpref "lfunction.rh"}[Riemann Hypothesis,] that all of the {bpref "lfunction.zeros"}[zeros] in the {bpref "lfunction.critical_strip"}[critical strip] are on the {bpref "lfunction.critical_line"}[critical line]. Selberg has defined a class $`\mathcal S` of Dirichlet series that satisfy the {bpref "lfunction.selberg_class.axioms"}[Selberg axioms.] It is conjectured (but far from proven) that $`\mathcal S` is precisely the set of all L-functions. Selberg's axioms have not been verified for all of the L-functions in this database but are known to hold for many of them.

It is also conjectured that a precise form of the {bpref "lfunction.functional_equation"}[functional equation] holds for every element of $`\mathcal S`. Under this assumption the functional equation is determined by a quadruple known as the {bpref "lfunction.selbergdata"}[Selberg data], consisting of the {bpref "lfunction.degree"}[degree], {bpref "lfunction.conductor"}[conductor], {bpref "lfunction.spectral_parameters"}[spectral parameters], and {bpref "lfunction.root_number"}[sign].

Tau Ceti Review: [`LSeries`](https://taucetiproject.org/review/#/d/LSeries).

Depends on: {uses "lfunction.dirichlet_series"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.analytic_conductor" (lean := "AnalyticLFunction.analyticConductor, AnalyticLFunction.SelbergData.analyticConductor, AnalyticLFunction.SelbergData.gammaFactor, AnalyticLFunction.conductor, AnalyticLFunction.SelbergData.analyticConductor_pos, AnalyticLFunction.SelbergData.analyticConductor_eq_analyticConductorLMFDB")
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

Tau Ceti Review: [`IsAlgebraic`](https://taucetiproject.org/review/#/d/IsAlgebraic), [`LSeries`](https://taucetiproject.org/review/#/d/LSeries).

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.bad_prime" (lean := "AnalyticLFunction.conductor, Nat.primeFactors, AnalyticLFunction.exists_eulerFactor, AnalyticLFunction.badPrimes, AnalyticLFunction.dvd_conductor_iff, AnalyticLFunction.badPrimes_eq_of_coeff_eq, AnalyticLFunction.badPrimes_eq_of_toFun_eq")
*Bad prime.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.bad_prime))

The *bad primes* of an {bpref "lfunction"}[L-function] are the primes that divided its {bpref "lfunction.conductor"}[conductor].

Tau Ceti Review: [`Nat.primeFactors`](https://taucetiproject.org/review/#/d/Nat.primeFactors).

Depends on: {uses "lfunction"}[] {uses "lfunction.conductor"}[]
:::

:::definition "lfunction.central_character"
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

:::definition "lfunction.coefficient_field"
*Coefficient field of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.coefficient_field))

The *coefficient field* of an {bpref "lfunction.arithmetic"}[arithmetic] {bpref "lfunction"}[L-function] $`L(s)=\sum a_nn^{-s}` is the {bpref "nf"}[number field] generated by the algebraic integers $`a_nn^{w/2}`, where $`w` is the {bpref "lfunction.motivic_weight"}[motivic weight].

Depends on: {uses "lfunction"}[] {uses "lfunction.arithmetic"}[] {uses "lfunction.motivic_weight"}[] {uses "nf"}[]
:::

:::definition "lfunction.completed" (lean := "AnalyticLFunction.completed, AnalyticLFunction.completed_eq, AnalyticLFunction.completed_eq_of_notMem_gammaPoles, AnalyticLFunction.completed_eq_sign_mul_conj, AnalyticLFunction.SelbergData.gammaFactor, AnalyticLFunction.SelbergData.gammaPoles")
*Completed L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.completed))

If the {bpref "lfunction"}[L-function] $`L(s)` satisfies the {bpref "lfunction.functional_equation"}[functional equation]

$$`\Lambda(s) := N^{s/2}
\prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k)
\cdot L(s) = \varepsilon \overline{\Lambda}(1-s),`

then $`\Lambda(s)` is called the *completed L-function*.

The completed L-function is the product of the L-function and its {bpref "lfunction.gamma_factor"}[gamma factors].

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[]
:::

:::definition "lfunction.conductor"
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

:::definition "lfunction.critical_strip" (lean := "AnalyticLFunction.criticalStrip, AnalyticLFunction.arithmeticCriticalStrip, AnalyticLFunction.summable_norm_tsum_term_prime_pow_sub_one, AnalyticLFunction.toFun_ne_zero, AnalyticLFunction.mem_closure_criticalStrip_of_completed_eq_zero, AnalyticLFunction.summable_norm_tsum_term_arithmeticCoeff_prime_pow_sub_one, AnalyticLFunction.zeros_diff_trivialZeros_subset_closure_criticalStrip, AnalyticLFunction.mem_closure_arithmeticCriticalStrip")
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

:::definition "lfunction.dirichlet" (lean := "DirichletCharacter.LFunction, DirichletCharacter.LFunction_eq_LSeries, DirichletCharacter.LSeries_eulerProduct_tprod, DirichletCharacter.IsPrimitive.completedLFunction_one_sub, DirichletCharacter.rootNumber, AnalyticLFunction, AnalyticLFunction.dirichlet, AnalyticLFunction.SelbergData.dirichlet, AnalyticLFunction.SelbergData.gammaFactor_dirichlet, AnalyticLFunction.eulerPolynomial_dirichlet, AnalyticLFunction.dirichlet_eq_zeta, DirichletCharacter.completedLFunction_conj, DirichletCharacter.IsPrimitive.norm_rootNumber")
*Dirichlet L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.dirichlet))

A *Dirichlet L-function* is an {bpref "lfunction"}[L-function] defined by a {bpref "lfunction.dirichlet_series"}[Dirichlet series] of the form $`{\displaystyle L(s, \chi)=\sum_{n=1}^\infty \frac {\chi(n)}{n^s}}`, where $`\chi` is a {bpref "character.dirichlet"}[Dirichlet character].

Dirichlet L-functions can be meromorphically continued to the complex plane, have an {bpref "lfunction.euler_product"}[Euler product] $`{\displaystyle L(s, \chi)= \prod_p (1 - \chi(p) p^{-s} )^{-1}}`, and satisfy a {bpref "lfunction.functional_equation"}[functional equation] of the form

$$`\Lambda(s,\chi) = q^{s/2} \Gamma_{\mathbb{R}} (s) L(s,\chi) = \varepsilon_{\chi} \overline{\Lambda}(1-s),`

where $`q` is the {bpref "character.dirichlet.conductor"}[conductor] of $`\chi`.

These L-functions were introduced by [Peter Gustav Lejeune Dirichlet](https://en.wikipedia.org/wiki/Peter_Gustav_Lejeune_Dirichlet) in the mid-1800s as a tool to study prime numbers in arithmetic progressions.

Tau Ceti Review: [`DirichletCharacter.LFunction`](https://taucetiproject.org/review/#/d/DirichletCharacter.LFunction), [`DirichletCharacter.LFunction_eq_LSeries`](https://taucetiproject.org/review/#/d/DirichletCharacter.LFunction_eq_LSeries), [`DirichletCharacter.IsPrimitive.completedLFunction_one_sub`](https://taucetiproject.org/review/#/d/DirichletCharacter.IsPrimitive.completedLFunction_one_sub), [`DirichletCharacter.rootNumber`](https://taucetiproject.org/review/#/d/DirichletCharacter.rootNumber).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "lfunction"}[] {uses "lfunction.dirichlet_series"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.dirichlet_series" (lean := "LSeries, LSeries.term, ArithmeticFunction")
*Dirichlet series.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.dirichlet_series))

A *Dirichlet series* is a formal series of the form $`F(s) = {\displaystyle \sum_{n=1}^{\infty} \frac{a_n}{ n^{s}}}`, where $`a_n \in {\mathbb{C}}`.

Tau Ceti Review: [`LSeries`](https://taucetiproject.org/review/#/d/LSeries), [`LSeries.term`](https://taucetiproject.org/review/#/d/LSeries.term), [`ArithmeticFunction`](https://taucetiproject.org/review/#/d/ArithmeticFunction).
:::

:::definition "lfunction.dual" (lean := "LSeries, starRingEnd")
*Dual of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.dual))

The *dual* of an {bpref "lfunction"}[L-function] $`L(s) = \sum_{n=1}^{\infty} \frac{a_n}{n^s}` is the complex conjugate $`\bar{L}(s) = \sum_{n=1}^{\infty} \frac{\bar{a_n}}{n^s}`.

Tau Ceti Review: [`LSeries`](https://taucetiproject.org/review/#/d/LSeries), [`starRingEnd`](https://taucetiproject.org/review/#/d/starRingEnd).

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.euler_product"
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

:::definition "lfunction.functional_equation" (lean := "AnalyticLFunction.SelbergData, AnalyticLFunction.SelbergData.gammaFactor, AnalyticLFunction.completed_eq, AnalyticLFunction.completed_eq_sign_mul_conj, AnalyticLFunction.SelbergData.degree, AnalyticLFunction.completed_sub_eq_sign_mul_conj, AnalyticLFunction.selbergFunctionalEquation_coeff, AnalyticLFunction.SelbergData.not_eqOn_gammaDivThree")
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

Tau Ceti Review: [`Complex.Gammaℝ`](https://taucetiproject.org/review/#/d/Complex.Gamma%E2%84%9D), [`Complex.Gammaℂ`](https://taucetiproject.org/review/#/d/Complex.Gamma%E2%84%82), [`Complex.Gammaℝ_mul_Gammaℝ_add_one`](https://taucetiproject.org/review/#/d/Complex.Gamma%E2%84%9D_mul_Gamma%E2%84%9D_add_one).

Depends on: {uses "lfunction.euler_product"}[]
:::

:::definition "lfunction.history"
*A history of L-functions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history))

{bpref "lfunction.history.euler"}[]

<h2>Riemann's memoir</h2>
{bpref "lfunction.history.riemanns_memoir"}[]

<h2>Dirichlet L-functions</h2>
{bpref "lfunction.history.dirichlet"}[]

<h2>Dedekind zeta functions</h2>
[lfunction.history.dedekind](https://beta.lmfdb.org/knowledge/show/lfunction.history.dedekind)

The automorphy properties of
Hilbert modular forms  for real quadratic fields were considered in the
1901 Gottingen
University Habilitationssschrift of Otto Blumenthal. Therein he refers to
unpublished  work of 1893-1894 of his advisor David Hilbert. Hilbert modular forms
 were significantly
developed by Hecke in his 1910 dissertation.

<h2>The L-function of $`\Delta`</h2>
{bpref "lfunction.history.ramanujan_tau"}[]

<h2>Hecke L-functions</h2>
{bpref "lfunction.history.hecke_characters"}[]

{bpref "lfunction.history.hecke_operators"}[]

<h2> Artin L-functions </h2>
{bpref "lfunction.history.artin"}[]

<h2> Siegel Modular forms </h2>
[lfunction.history.siegel](https://beta.lmfdb.org/knowledge/show/lfunction.history.siegel)

<h2> Rankin-Selberg convolution </h2>
{bpref "lfunction.history.rankin_selberg"}[]

<h2>L-functions of nonholomorphic modular forms</h2>
{bpref "lfunction.history.maass"}[]

<h2> Tate's thesis </h2>
[lfunction.history.tates\_thesis](https://beta.lmfdb.org/knowledge/show/lfunction.history.tates_thesis)

<h2> Hasse-Weil L-functions </h2>
{bpref "lfunction.history.hasse_weil"}[]

<h2> Langlands Program </h2>

{bpref "lfunction.history.langlands_program"}[]

Depends on: {uses "lfunction.history.artin"}[] {uses "lfunction.history.dirichlet"}[] {uses "lfunction.history.euler"}[] {uses "lfunction.history.hasse_weil"}[] {uses "lfunction.history.hecke_characters"}[] {uses "lfunction.history.hecke_operators"}[] {uses "lfunction.history.langlands_program"}[] {uses "lfunction.history.maass"}[] {uses "lfunction.history.ramanujan_tau"}[] {uses "lfunction.history.rankin_selberg"}[] {uses "lfunction.history.riemanns_memoir"}[]
:::

:::definition "lfunction.history.artin"
*Artin L-functions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.artin))

Artin L-functions were introduced in 1924 . Artin's conjecture that these L-functions are
entire remains unsolved, though many instances are known.
:::

:::definition "lfunction.history.dirichlet" (lean := "DirichletCharacter.χ₃, DirichletCharacter.χ₃_intCast, DirichletCharacter.LFunction_eulerProduct_hasProd, DirichletCharacter.completedLFunctionModThree_one_sub, DirichletCharacter.completedLFunctionModThree_eq, DirichletCharacter.LFunction_χ₃_apply_one, Nat.infinite_setOfPred_prime_and_modEq, DirichletCharacter.LFunction_apply_one_ne_zero")
*Dirichlet's work on L-functions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.dirichlet))

The first use of the letter L to denote  these functions was by Dirichlet in 1837 (see <i>Werke I</i>  pages 313-342)
who
used L-functions to prove that there are infinitely many primes in any (primitive) arithmetic progression.
He considered
series of the form

$$`L(s,\chi)=\sum_{n=1}^\infty \frac{\chi(n)}{n^s}`

where $`\chi` is a {bpref "character.dirichlet"}[(Dirichlet) character], which is the extension to the integers of a character of the
group $`(\mathbb{Z}/q\mathbb{Z})^*`. For example the arithmetic function $`\chi` defined by

$$`\chi(n)=\begin{cases} 1 & \textrm{ if } n\equiv 1 \bmod 3\\
-1 & \textrm{ if } n\equiv 2\bmod 3\\
0 & \textrm{ if  }n\equiv 0\bmod 3\end{cases}`

is a Dirichlet character modulo 3. The above L-function has an Euler product

$$`L(s,\chi)=\prod_{p }\left(1-\frac{\chi(p)}{p^s}\right)^{-1}`

and satisfies a functional equation that

$$`\left(\frac{3}{\pi}\right)^{\frac{s}{2}}\Gamma\left(\frac{s+1}{2}\right) L(s,\chi)`

is invariant under $`s\to 1-s`. Also, note the special value

$$`L(1,\chi)= \frac{\pi}{3\sqrt{3}};`

Dirichlet needed to know that his L-functions did not vanish at 1 and he
used special values to prove this fact.
Dirichlet's original proof was for prime moduli; for composite moduli he required
his class number formula which was proven in 1839 - 1840 (see his _Werke I_, pp. 411-496).

Tau Ceti Review: [`Nat.infinite_setOfPred_prime_and_modEq`](https://taucetiproject.org/review/#/d/Nat.infinite_setOfPred_prime_and_modEq), [`DirichletCharacter.LFunction_apply_one_ne_zero`](https://taucetiproject.org/review/#/d/DirichletCharacter.LFunction_apply_one_ne_zero).

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "lfunction.history.euler"
*Euler's work on the zeta function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.euler))

The prototype of L-functions is the Riemann zeta-function defined by

$$`\zeta(s)=\sum_{n=1}^\infty \frac {1}{n^s}`

for $`\Re s>1`. Euler discovered that $`\zeta(2)=\frac{\pi^2}{6}`,
and he also found the fundamental identity

$$`\zeta(s)=\prod_p \left(1-\frac{1}{p^s}\right)^{-1},`

which he used to prove that the series $`\sum_p \frac{1}{p}` diverges. Euler considered other divergent series
and noticed a connection between  values of $`\zeta` at $`s` and $`1-s`, linked by powers of $`\pi` and {bpref "af.bernoulli_numbers"}[Bernoulli numbers],
such as the interpretations

$$`1+2+3+\dots =-\frac{1}{12}`

and

$$`1+4+9+16+\dots =0.`

Euler found hints of many of the remarkable features of L-functions that
make them such worthy objects of study: the Euler product, special values, and the functional equation.
It was left to Riemann to discover perhaps the most remarkable property of all, one that
hasn't been proven yet: the Riemann Hypothesis that each  non-real zero of $`\zeta(s)` has real part
equal to $`\frac 12`.

Depends on: {uses "af.bernoulli_numbers"}[]
:::

:::definition "lfunction.history.hasse_weil"
*Hasse-Weil L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.hasse_weil))

In 1955 Hasse  introduced the zeta-function associated with a curve, today called the
Hasse-Weil zeta function. For a Fermat curve $`x^m+y^m=1` he obtains an expression
for his zeta-function in terms of L-functions with a Hecke character.
:::

:::definition "lfunction.history.hecke_characters"
*Hecke L-functions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.hecke_characters))

The  L-functions  associated with finite characters of number fields (often called {bpref "character.dirichlet"}[Dirichlet charaters]
or finite {bpref "character.hecke"}[Hecke characters])
were considered by Hecke in a series of papers beginning in 1917.
In the first paper of this series, _&Uuml;ber die Zetafunktion_
\_beliebiger algebraischer Zahlkorper\_ [G\"ott. Nachr. 1917 77-89 (1917)](https://eudml.org/doc/58974),  he refers to $`\zeta_k(s)` as the "Dirichlet-Dedekindsche Zetafunktion".
Here he gives the functional equation for the Dedekind zeta-function of any number field.
In the second
paper <i>&Uuml;ber eine neue anwendung der Zetafunktionnen
auf die arithmetik der Zahlkorper</i> also in 1917, he refers to it as
"der Dedekindschen Funktion $`\zeta_k(s)`." This paper ends with the remark that
for abelian extensions $`\zeta_k(s)` can be factored as a product of Dirichlet L-functions.
In the third paper in the series, he refers again to
"Dirichlet-Dedekindsche Funktion $`\zeta_k(s)`".
Here he proves the functional equation for L-functions of finite Hecke characters.

The L-functions associated with Hecke's Gro&beta;encharaktere, i.e. characters of infinite order,
and their functional equations
appear in a two-paper series beginning in 1918 . It is only in the second of these
papers (1920) that Hecke uses the  term "Gro&beta;encharaktere".

Depends on: {uses "character.dirichlet"}[] {uses "character.hecke"}[]
:::

:::definition "lfunction.history.hecke_operators" (lean := "HeckeRing.GL2.Eigenform, HeckeRing.GL2.heckeTNat, HeckeRing.GL2.Eigenform.qExpansion_coeff_mul, HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd, CuspForm.frickeCompletedL_eq_mul_LSeries, CuspForm.frickeCompletedL_functional_equation_gamma1, CuspForm.frickeCompletedL_sub_eq_of_level_one, HeckeRing.GL2.Newform.analyticCompletedL_eq_rootNumber_mul")
*Hecke operators, history.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.hecke_operators))

Hecke , building on Mordell, introduced operators acting on
vector spaces of modular forms.  The forms which were simultaneous eigenvalues
of these operators have multiplicative Fourier coefficients so that their
associated Dirichlet series have Euler products and functional equations.
Hecke mainly worked with level 1 modular forms.
The more subtle theory of Hecke operators for spaces of higher level and
with character was developed by Atkin and Lehner, and Li .

Tau Ceti Review: [`HeckeRing.GL2.Eigenform`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Eigenform), [`HeckeRing.GL2.heckeTNat`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.heckeTNat), [`HeckeRing.GL2.Eigenform.qExpansion_coeff_mul`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Eigenform.qExpansion_coeff_mul), [`HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd), [`CuspForm.frickeCompletedL_functional_equation_gamma1`](https://taucetiproject.org/review/#/d/CuspForm.frickeCompletedL_functional_equation_gamma1).
:::

:::definition "lfunction.history.langlands_program"
*Langlands program.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.langlands_program))

Langlands theory of automorphic forms ushered in an age of a new understanding
of the profundity of L-functions. His small book _Euler Products_ of 1967 contains
the beginnings of a general theory.

In 1969 Ogg  proved the holomorphy and functional equation for the Rankin-Selberg convolution
of two inequivalent cusp forms of the same level. This is a degree 4 L-function.
In 1972 Jacquet  considered the Rankin-Selberg convolution
of two GL(2)
cusp forms and obtained the analytic continuation and functional equation of the associated L-function.
In 1979 Winnie Li  completed the Rankin-Selberg story for two arbitrary GL(2)
 cusp forms. Her techniques really require the use
of Tate's thesis and the theory of automorphic forms as it is virtually impossible
to figure out the Euler factors at bad primes without these.

In 1971 Andrianov  explicitly constructed the L-function for a genus 2 Siegel modular form
and gave its analytic continuation and functional equation.

In 1972 Godement and Jacquet  defined the L-function of a general automorphic form
on a reductive group and obtained the analytic continuation and functional equation.

It wasn't until the mid 1970's  that Shimura  and, shortly later
but independently, Zagier
proved that the L-function associated with the symmetric
square of a cusp form is entire. See also the footnote in Selberg's paper
 that suggests that
Selberg had discovered  this many years earlier.

In 1977 Asai  obtained the holomorphy and functional equation of certain
degree 4 L-functions associated with Hilbert modular forms over quadratic fields.
These are known as Asai L-functions.

Beginning in 1978 Shahidi  and completed
in 1999 with Kim  proved that the symmetric cube
of a GL(2) L-function is entire and has
functional equation.

In 1980 Langlands proved Artin's conjecture for 2-dimensional representations of
tetrahedral type (and also for certain octahedral
representations) .
In 1981 Tunnell proved Artin's conjecture for octahedral representations .

In  work  beginning in 1981 with ,  Shahidi
proved the holomorphy and functional equation for many automorphic L-functions.

In 1983 Jacquet,  Piatetskii-Shapiro, and  Shalika obtained the meromorphicity and
functional equation for the L-function that is a general Rankin-Selberg convolution
of automorphic L-functions.

In 1995 Andrew Wiles  proved the holomorphy and functional equation of the Hasse-Weil zeta-function
of most elliptic curves. In 2001 this work was extended by Breuil, Conrad, Diamond, and Taylor
to include all elliptic curves .
:::

:::definition "lfunction.history.maass"
*L-functions of Maass forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.maass))

In 1949 Hans Maass made his profound discovery that there are L-functions associated with
non-holomorphic automorphic forms. In his Math Review of
Maass' article
J. Lehner writes

<i>In Hecke's theory of Dirichlet series with Euler products we associate, roughly speaking,
a Dirichlet series with an automorphic function; the invariance of the latter under linear
substitutions is used, together with the Mellin transform, to derive a functional equation
for the Dirichlet series. This suffices for the discussion of the $`\zeta`-function of an imaginary
quadratic field, for example, but not of a real quadratic field. In order to handle the latter case,
the author defines a class of functions
 ("automorphic wave functions") to take the place of the analytic
automorphic functions of Hecke's theory. </i>

Maass' work prompted Andre; Weil to remark "Il a fallu Maass pour nous sortir du ghetto des fonctions holomorphes."
:::

:::definition "lfunction.history.ramanujan_tau"
*Ramanujan tau L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.ramanujan_tau))

In 1916 Ramanujan  made the startling observation that the coefficients of the $`\Delta` function
are multiplicative! Ramanujan defined $`\tau(n)` by

$$`q\prod_{n=1}^\infty (1-q^n)^{24}=\sum_{n=1}^\infty \tau(n)q^n`

and conjectured that $`\tau(mn)=\tau(m)\tau(n)` whenever $`m` and $`n` are relatively prime.
Moreover that
$$`\sum_{r=0}^\infty \tau(p^r)X^r = (1-\tau(p)X +p^{11}X^2)^{-1}`

and that $`|\tau(p)|< 2p^{11/2}`. The first two of these astounding conjectures were  verified
by Mordell in 1917 (see
"On Mr. Ramanujan's Empirical Expansions
of Modular Functions."
Proc. Cambridge Phil. Soc.19, (1917))
 and the last by Deligne in 1974 in work for which he won a Fields
Medal. It was already known   that

$$`\Delta(z)=\sum_{n=1}^\infty \tau(n)e(nz)`

is a modular form of weight 12. Thus $`L(s)=\sum_{n=1}^\infty \tau(n)n^{-s}`
has  a functional equation and (by Mordell)
an Euler product.  Ramanujan's discovery was the ushering in of a new age of arithmetic L-functions.
:::

:::definition "lfunction.history.rankin_selberg"
*Ranking-Selberg convolution, history.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.rankin_selberg))

In 1939 R. A. Rankin  studied Ramanujan's conjecture about the size of $`\tau(n)`
and was led to consider the analytic properties of $`g(s)=\sum_{n=1}^\infty \tau(n)^2 n^{-s}`.
He proved that $`\zeta(2s-22) g(s)` is analytic everywhere except for a simple
pole at $`s=12`  and satisfies a functional equation. This was the beginning
of the Rankin - Selberg convolution which we now realize was a hugely important event in the theory of L-functions. Selberg  did the same calculation
around the
same time.
:::

:::definition "lfunction.history.riemanns_memoir"
*Riemann's memoir.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.history.riemanns_memoir))

In 1859, in an 8 page paper "Uber die Anzahl der Primzahlen unter einer
gegebenen Grosse" [Transcript](http://www.claymath.org/sites/default/files/zeta.pdf) read to the Berlin Academy of Sciences by Gauss' former student Encke,
 Riemann first considered $`\zeta(s)` as a function of a complex variable $`s`.
He proved that $`\zeta(s)`
is a meromorphic function in the complex $`s`-plane whose only singularity is a simple pole at $`s=1` with
residue 1. He went on to prove that

$$`\xi(s)=\frac{1}{2} s(s-1)\pi^{-s/2}\Gamma(s/2) \zeta(s)`

is entire of order 1 and satisfies the functional equation

$$`\xi(s)=\xi(1-s).`

He proved that $`\xi(s)` has infinitely many zeros, all of which are in the critical strip $`0\le \sigma\le 1`, where $`\sigma` denotes the real part of $`s`.
Riemann calculated the first few of these zeros (this was discovered later when Siegel studied Riemann's
notes left to the Gottingen library) and found them to lie on the critical line
$`\sigma=1/2`. He conjectured that all of the zeros are on this line.
And the analytic theory of L-functions was born!
:::

:::definition "lfunction.infinity_factor" (lean := "AnalyticLFunction.SelbergData.gammaFactor, AnalyticLFunction.SelbergData.μ, AnalyticLFunction.SelbergData.ν, AnalyticLFunction.completed_eq, AnalyticLFunction.completed_eq_of_notMem_gammaPoles, AnalyticLFunction.completed_eq_sign_mul_conj")
*Infinity factor of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.infinity_factor))

The *infinity factor* $`L_{\infty}(s)` of an {bpref "lfunction"}[L-function] $`L(s)` is the product of its {bpref "lfunction.gamma_factor"}[Gamma factors]:

$$`L_{\infty}(s) := \prod_{j=1}^J \Gamma_{\mathbb{R}}(s+\mu_j) \prod_{k=1}^K \Gamma_{\mathbb{C}}(s+\nu_k).`

Here the $`\mu_j` and $`\nu_k` are the {bpref "lfunction.spectral_parameters"}[spectral parameters] of the L-function.

That is, the {bpref "lfunction.functional_equation"}[functional equation] has the form

$$`\Lambda(s) := L_{\infty}(s) L(s) = \varepsilon \overline{\Lambda}(1-s).`

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[] {uses "lfunction.spectral_parameters"}[]
:::

:::definition "lfunction.known_degree1"
*Degree 1 L-functions, all.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.known_degree1))

The {bpref "lfunction.degree"}[degree] 1 {bpref "lfunction"}[L-functions] are:

- $`\zeta(s)`: the Riemann zeta function

- $`L(s, \chi)`: the Dirichlet L-function of a primitive Dirichlet character

Note that these L-functions also arise as {bpref "artin.lfunction"}[Artin L-functions].

Depends on: {uses "artin.lfunction"}[] {uses "lfunction"}[] {uses "lfunction.degree"}[]
:::

:::definition "lfunction.known_degree2"
*Degree 2 L-functions, examples.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.known_degree2))

Examples of primitive {bpref "lfunction.degree"}[degree] 2 {bpref "lfunction"}[L-functions] are:

- $`L(s, f)`: the L-function of a holomorphic {bpref "cmf.newform"}[newform] in $`S_k(\Gamma_0(N))`

- $`L(s, f)`: the L-function of a Maass cusp form on  {bpref "mf.sl2.subgroup.gamma0n"}[$`\Gamma_0(N)`]

- $`L(s, E)`: the L-function of an {bpref "ec.q"}[elliptic curve $`E` over $`\mathbb{Q}`]

Depends on: {uses "cmf.newform"}[] {uses "ec.q"}[] {uses "lfunction"}[] {uses "lfunction.degree"}[] {uses "mf.sl2.subgroup.gamma0n"}[]
:::

:::definition "lfunction.known_degree3"
*Degree 3 L-functions, examples.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.known_degree3))

Examples of primitive {bpref "lfunction.degree"}[degree] 3 {bpref "lfunction"}[L-functions] are:

- $`L(s, f, \mathrm{sym}^2)`: the symmetric square of a degree 2 L-function

- $`L(s,f)`: standard L-function of a cusp form on GL(3)

Depends on: {uses "lfunction"}[] {uses "lfunction.degree"}[]
:::

:::definition "lfunction.known_degree4"
*Degree 4 L-functions, examples.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.known_degree4))

Examples of {bpref "lfunction.primitive"}[primitive] {bpref "lfunction.degree"}[degree] 4 {bpref "lfunction"}[L-functions] are:

- $`L(s, f, \mathrm{sym}^3)`: the symmetric cube L-function of a {bpref "cmf.cusp_form"}[cusp form] on GL(2)

- $`L(s, F, \mathrm{spin})`: spin L-function of a Siegel modular form on GSp(4) (genus 2)

- $`L(s,f)`: standard L-function of a cusp form on the Picard group SL(2,Z\[i\])

- $`L(s,f)`: standard L-function of a cusp form on Sp(4)

- $`L(s,f)`: standard L-function of a cusp form on GL(4)

- $`L(s,E)`: L-function of an elliptic curve over a quadratic field

- $`L(s,f)`: standard L-function of a Hilbert modular form on GL(2) over a real quadratic field

Depends on: {uses "cmf.cusp_form"}[] {uses "lfunction"}[] {uses "lfunction.degree"}[] {uses "lfunction.primitive"}[]
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

Tau Ceti Review: [`meromorphicTrailingCoeffAt`](https://taucetiproject.org/review/#/d/meromorphicTrailingCoeffAt).

Depends on: {uses "lfunction.arithmetic"}[] {uses "lfunction.central_point"}[]
:::

:::definition "lfunction.motivic_weight"
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

:::definition "lfunction.rational" (lean := "AnalyticLFunction.IsRational, AnalyticLFunction.arithmeticEulerPolynomial, AnalyticLFunction.motivicWeight, AnalyticLFunction.arithmeticCoeff, AnalyticLFunction.IsRational.isAlgebraic_coeff, AnalyticLFunction.arithmeticEulerPolynomial_mul_mk, AnalyticLFunction.isRational_iff, AnalyticLFunction.isRational_zeta")
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

Tau Ceti Review: [`RiemannHypothesis`](https://taucetiproject.org/review/#/d/RiemannHypothesis).

Depends on: {uses "lfunction"}[]
:::

:::definition "lfunction.riemann"
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

:::definition "lfunction.root_analytic_conductor" (lean := "AnalyticLFunction.rootAnalyticConductor, AnalyticLFunction.rootAnalyticConductor_pow_degree, AnalyticLFunction.rootAnalyticConductor_pos, AnalyticLFunction.analyticConductor, AnalyticLFunction.degree")
*Root analytic conductor.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.root_analytic_conductor))

If $`d` is the {bpref "lfunction.degree"}[degree] of the {bpref "lfunction"}[L-function] $`L(s)`, the *root analytic conductor* $`\alpha` of $`L` is the $`d`th root of the {bpref "lfunction.analytic_conductor"}[analytic conductor] of $`L`.  It plays a role analogous to the {bpref "nf.root_discriminant"}[root discriminant] for {bpref "nf"}[number fields].

Depends on: {uses "lfunction"}[] {uses "lfunction.analytic_conductor"}[] {uses "lfunction.degree"}[] {uses "nf"}[] {uses "nf.root_discriminant"}[]
:::

:::definition "lfunction.root_angle" (lean := "AnalyticLFunction.sign, Complex.arg, Complex.neg_pi_lt_arg, Complex.arg_le_pi, AnalyticLFunction.norm_sign")
*Root angle of L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.root_angle))

The *root angle* of an L-function is the argument of its {bpref "lfunction.sign"}[root number], as a real number $`\alpha` with $`-0.5 < \alpha \le 0.5`.

Tau Ceti Review: [`Complex.arg`](https://taucetiproject.org/review/#/d/Complex.arg), [`Complex.neg_pi_lt_arg`](https://taucetiproject.org/review/#/d/Complex.neg_pi_lt_arg), [`Complex.arg_le_pi`](https://taucetiproject.org/review/#/d/Complex.arg_le_pi).

Depends on: {uses "lfunction.sign"}[]
:::

:::definition "lfunction.root_number" (lean := "AnalyticLFunction.sign, AnalyticLFunction.SelbergData.sign, AnalyticLFunction.completed_eq, AnalyticLFunction.completed_eq_sign_mul_conj, AnalyticLFunction.sign_eq_one_or_eq_neg_one, AnalyticLFunction.toFun_one_half_eq_zero_of_sign_eq_neg_one")
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

:::definition "lfunction.selbergdata" (lean := "AnalyticLFunction.SelbergData, AnalyticLFunction.selbergData, AnalyticLFunction.SelbergData.degree, AnalyticLFunction.SelbergData.μ, AnalyticLFunction.SelbergData.ν, AnalyticLFunction.SelbergData.sign")
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

Tau Ceti Review: [`LSeries`](https://taucetiproject.org/review/#/d/LSeries), [`starRingEnd`](https://taucetiproject.org/review/#/d/starRingEnd), [`Complex.conj_eq_iff_real`](https://taucetiproject.org/review/#/d/Complex.conj_eq_iff_real).
:::

:::definition "lfunction.sign" (lean := "AnalyticLFunction.sign, AnalyticLFunction.SelbergData.sign, AnalyticLFunction.completed_eq_sign_mul_conj, AnalyticLFunction.norm_sign, AnalyticLFunction.SelbergData")
*Sign of the functional equation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.sign))

The *sign* of the functional equation of an analytic L-function, also called the *root number*, is the complex number $`\varepsilon` that appears in the {bpref "lfunction.functional_equation"}[functional equation] of $`\Lambda(s)=\varepsilon \overline{\Lambda}(1-s)`.  The sign appears as the 4th entry in the quadruple
known as the {bpref "lfunction.selbergdata"}[Selberg data.]

Depends on: {uses "lfunction.functional_equation"}[]
:::

:::definition "lfunction.signature" (lean := "AnalyticLFunction.SelbergData.μ, AnalyticLFunction.SelbergData.ν, AnalyticLFunction.SelbergData.re_eq_zero_or_one_of_mem_μ, AnalyticLFunction.SelbergData.exists_two_mul_re_eq_of_mem_ν, AnalyticLFunction.SelbergData.degree, Multiset.card")
*Signature of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.signature))

The *signature* either refers to the pair $`[J,K]` where $`J` is the number of {bpref "lfunction.gamma_factor"}[$`\Gamma_{\mathbb{R}}`] and $`K` is the number of {bpref "lfunction.gamma_factor"}[$`\Gamma_{\mathbb{C}}`] in the {bpref "lfunction.selbergdata"}[Selberg data], or else it refers to the tuple

$$`(\Re(\mu_1),\ldots,\Re(\mu_J); 2\Re(\nu_1),\ldots,2\Re(\nu_K)).`

Note that the entries in that tuple are non-negative integers.

Tau Ceti Review: [`Multiset.card`](https://taucetiproject.org/review/#/d/Multiset.card).

Depends on: {uses "lfunction.gamma_factor"}[] {uses "lfunction.selbergdata"}[]
:::

:::definition "lfunction.spectral_label"
*Spectral label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.spectral_label))

The {bpref "lfunction.spectral_parameters"}[spectral parameters] are encoded as a string "x-y".  Here x is the concatenation of expressions of the form r$`u` and c$`v`.  The first indicates that $`\Gamma_{\R}(s + \mu)` appears in the {bpref "lfunction.functional_equation"}[functional equation] with $`\Re(\mu) = u`, and the second that $`\Gamma_{\C}(s + \nu)` appears with $`2\Re(\nu) = v`.  The factor of $`2` is included so that the $`u` and $`v`s are integral.  In the multiset of $`u` and $`v`s, if the multiplicities are all a multiple of an integer $`n > 1` then we use e$`n` to shorten x.  For example, r0r0c0c0 is encoded r0c0e2.  The $`\Gamma_{\R}` terms and $`\Gamma_{\C}` terms are separately sorted, and we use the identity $`\Gamma_{\C}(s) = \Gamma_{\R}(s)\Gamma_{\R}(s + 1)` as much as possible to combine pairs $`\Gamma_{\R}(s + \mu)\Gamma_{\R}(s + \mu + 1)` into $`\Gamma_{\C}(s + \mu)` in the interest of brevity.

Similarly, y is either 0 (indicating that all $`\mu_j` and $`\nu_j` are real), or the concatenation of expressions of the form p$`t`, m$`t` or c$`t` indicating complex numbers with imaginary part either $`t` or $`-t` or both (respectively).  These imaginary parts are listed in the same order as the real parts and are sorted by increasing absolute value within parameters with the same real part.  We round imaginary parts to two digits after the decimal point.  We write p0 when the imaginary part is zero to the known precision, and p0.00 and m0.00 for imaginary parts with an absolute value smaller than $`0.5 \cdot 10^{-2}`.

Depends on: {uses "lfunction.functional_equation"}[] {uses "lfunction.spectral_parameters"}[]
:::

:::definition "lfunction.spectral_parameters" (lean := "AnalyticLFunction.SelbergData.μ, AnalyticLFunction.SelbergData.ν, AnalyticLFunction.SelbergData.gammaFactor, AnalyticLFunction.selbergData, AnalyticLFunction.completed_eq")
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

:::definition "lfunction.taxonomy"
*Taxonomy of L-functions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.taxonomy))

Taxonomy of L-functions
=======================

One can consider $`L`-functions as autonomous objects, not necessarily
arising from another more basic object.  From that point of view it
is natural to develop a taxonomy of $`L`-functions, where
only the properties of the $`L`-function are used for the classification.

The most obvious invariant of an $`L`-function is its <em>degree</em>.
After the degree, it is not immediately obvious which properties
of the $`L`-function should be considered next, but we propose the
following as a reasonable scheme:

Note: some of the names could be better.  And the order is not
canonical.

0) Degree.

The non-negative integer $`d=J+2K`, where $`J` and $`K`
refer respectively to the number of $`\Gamma_{\R}` and
$`\Gamma_{\C}` factors in the functional equation.
Recall that the $`L`-function axioms determine $`J` and $`K`
uniquely.

1) Signature.

The pair $`(J,K)`.

1.5) $`\Gamma`-data

The pair $`(\{\mu_1,...,\mu_J\}, \{\nu_1,...,\nu_K\})`, where at this
point we may wish to think of the $`\mu_j` and $`\nu_k` as depending on
a parameter.  For example, the two main classes of degree 2
$`L`-functions have:

$$`(\{i\lambda,-i\lambda\},\{\})
\ \ \ \ \ \ \ \ \
or
\ \ \ \ \ \ \ \ \
(\{\},\{\frac{k-1}{2}\}),`

where $`\lambda` is a positive real number and $`k` is an integer.

2) Is the $`L`-function algebraic?

We call an $`L`-function <em>algebraic</em> if its Dirichlet
coefficients are algebraic numbers.  This, conjecturally,
is equivalent to each of:

a) $`\mu_j` and $`\nu_k` are real

b) The $`L`-function is the $`L`-function of a Galois representation.

c) The $`L`-function is motivic

d) There exists a number field $`K/\Q`,
called the <em>field of coefficients</em>,
and a integer $`w`, called the <em>motivic weight</em> of the $`L`-function,
such that $`a_n n^{w/2}` is in integer of $`K` for all $`n`.
(Note that $`w` is chosen to be the minimal integer with this property.)
(Note also that, conjecturally, $`w=\min\{0,\max\{\nu_k\}\}`.
In the arithmetic normalization, the functional equation relates $`s`
to $`w+1-s`.)
(Note that for holomorphic $`GL(2)` cusp forms, motivic weight
is one less than the "classical" weight.
For Siegel modular forms, the "classical" weight has yet
another relationship to the motivic weight.)

2') The motivic weight

2") The field of coefficients

3) Level.

The non-negative integer $`N` appearing in the functional equation.

Note: Once the level and the specific numbers in the $`\Gamma`-factors
have been specified, then (conjecturally) there are only finitely many
$`L`-functions possible.

4) Central character.

The Euler product has the form

$$`L(s) = \prod_p F_p(p^{-s})`

where

$$`F_p(x) = 1+a_p x + \cdots + (-1)^d \chi(p)  x^d.`

The character $`\chi`, which is a Dirichlet character mod~$`N`,
is called the <em>central character</em>
of the $`L`-function.

If $`p` is a good prime, then the roots of $`F_p` are
called the <em>Satake paramaters at $`p`</em> for the
$`L`-funciton.

Note: if $`L(s)=L(s,f)` for some object $`f`, then $`f` may have
its own Satake parameters, which in general are different from the
Satake parameters of the $`L`-function.  (This has to be the case,
because $`f` probably has infinitely many $`L`-functions associated
to it, and each $`L`-function has different Satake parameters.)

5) Sign.

The parameter $`\varepsilon` appearing in the functional equation.
Also known as the "root number."

The above classification exhausts the parameters in the functional
equation
and the Euler product,
but there are further refinements based on the distribution
of Dirichlet coefficients.

6) Self-dual?

Are the Dirichlet coefficients real?

7) Sato-Tate group

The Sato-Tate group of an $`L`-function is a compact subgroup
of a classical matrix group whose eigenvalues under Haar measure have the
same distribution as the distribution of Satake parameters
of the $`L`-function.  Further discussion below.

The Dirichlet coefficients $`a_p`,...,$`a_{p^{[d/2]}}` have
a limiting distribution.  The first few moments of those
coefficients uniquely determine the distributions.
For example, for L-functions of degree $`d=2` and weight $`w\ge 1` with rational coefficients there are three possibilities:

$$`\langle |a_p|^2 \rangle = 1,
\ \ \ \ \
\langle |a_p|^4 \rangle = 2;`

and

$$`\langle |a_p|^2 \rangle = 1,
\ \ \ \ \
\langle |a_p|^4 \rangle = 3;`

and

$$`\langle |a_p|^2 \rangle = 2,
\ \ \ \ \
\langle |a_p|^4 \rangle = 6.`

The first possibility corresponds to what was classically known as "Sato-Tate", while
the second two are commonly called "CM".
For $`d=2` and $`w=0` there are several more options.

Serre uses "Sato-Tate group" for the general case. See his
excellent book "Lectures on $`N_X(p)`" .

As the degree grows there are more possibilities: 55 for L-functions of degree $`d=4` and weight $`w=1` with rational coefficients, of which 52 arise for abelian surfaces (in fact, for Jacobians of hyperelliptic curves); this follows from the classification of Fite-Kedlaya-Rotger-Sutherland .

Note:  The first few coefficient moments determine the distribution
because there is a compact matrix group whose eigenvalues have
the same distribution as the Satake parameters.  That group is
the <em>Sato-Tate group</em> of the $`L`-function.  All of this
is conjectural for $`d>2`.

Note: The Sato-Tate group determines which operations on the $`L`-function
($`sym^n`, for example) have poles.
:::

:::definition "lfunction.trivial_zero"
*Trivial zeros of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.trivial_zero))

The {bpref "lfunction.zeros"}[zeros] of an L-function $`L(s)` that occur at
poles of its  {bpref "lfunction.gamma_factor"}[gamma factors] are *trivial zeros*.

The presence of trivial zeros is required by the {bpref "lfunction.functional_equation"}[functional equation].  In its {bpref "lfunction.normalization"}[analytic normalization], the L-function $`L(s)` has no zeros or poles in the right half-plane $`\Re(s)>1`, but the {bpref "lfunction.gamma_factor"}[gamma factors] that appear in the functional equation have poles.  Since the {bpref "lfunction.completed"}[completed L-function] has no poles (except possibly from Riemann zeta-function factors),
the L-function must have zeros at poles of the gamma factors.

For {bpref "lfunction.arithmetic"}[arithmetic] L-functions, the poles are at certain negative integers.

Depends on: {uses "lfunction.arithmetic"}[] {uses "lfunction.completed"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[] {uses "lfunction.normalization"}[] {uses "lfunction.zeros"}[]
:::

:::definition "lfunction.underlying_object"
*Underlying object of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.underlying_object))

L-functions arise from many different sources. Already in {bpref "lfunction.degree"}[degree] 2 we have examples of
L-functions associated with {bpref "cmf"}[holomorphic cusp forms], with {bpref "mf.maass.mwf"}[Maass forms,] with {bpref "ec.q"}[elliptic curves,] with characters of {bpref "nf"}[number fields] ({bpref "character.hecke"}[Hecke characters]), and with 2-dimensional representations of the {bpref "nf.galois_group"}[Galois group of a number field] (Artin L-functions).

Sometimes an L-function may arise from more than one source. For example, the L-functions associated with elliptic curves are also associated with weight 2 cusp forms. A goal of the Langlands program ostensibly is to prove that any degree $`d` L-function is associated with an automorphic form on $`\mathrm{GL}(d)`. Because of this representation theoretic genesis, one can associate an L-function not only to an automorphic representation but also to symmetric powers, or exterior powers of that representation, or to the tensor product of two representations (the Rankin-Selberg product of two L-functions).

Depends on: {uses "character.hecke"}[] {uses "cmf"}[] {uses "ec.q"}[] {uses "lfunction.degree"}[] {uses "mf.maass.mwf"}[] {uses "nf"}[] {uses "nf.galois_group"}[]
:::

:::definition "lfunction.zeros"
*Zeros of an L-function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lfunction.zeros))

The *zeros* of an {bpref "lfunction"}[L-function] $`L(s)` are the complex numbers $`\rho` for which $`L(\rho)=0`.

Under the {bpref "lfunction.rh"}[Riemann Hypothesis], every {bpref "lfunction.trivial_zero"}[non-trivial zero] $`\rho` lies on the {bpref "lfunction.critical_line"}[critical line] $`\Re(s)=1/2` (in the {bpref "lfunction.normalization"}[analytic normalization]).

The *lowest zero* of an L-function $`L(s)` is the least $`\gamma>0` for which $`L(1/2+i\gamma)=0`. Note that even when $`L(1/2)=0`, the lowest zero is by definition a positive real number.

Depends on: {uses "lfunction"}[] {uses "lfunction.critical_line"}[] {uses "lfunction.normalization"}[] {uses "lfunction.rh"}[]
:::

:::definition "lfunction.zfunction" (lean := "AnalyticLFunction.zFunction, riemannSiegelTheta, ofReal_hardyZ_eq_exp_mul_riemannZeta, AnalyticLFunction.ofReal_zFunction, AnalyticLFunction.eventually_zFunction_pos, AnalyticLFunction.contDiff_zFunction, AnalyticLFunction.analyticOrderAt_zFunction, AnalyticLFunction.eventually_zFunction_mul_zFunction_neg")
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

:::definition "rcs.cande.lfunction"
*Completeness of L-function Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.cande.lfunction))

The database currently contains more than $`20` million {bpref "lfunction"}[L-functions].  Most of these are stored in the database along with related information such as {bpref "lfunction.zeros"}[zeros] and {bpref "lfunction.analytic_rank"}[analytic rank] that have been precomputed using explicit precision bounds (see the "reliability" link on each L-function's home page for further details).  A small number of dynamically computed L-functions are also available, as noted in the summary below.  The pages for dynamically computed L-functions may be missing information that cannot be computed quickly, and the data displayed on them may be less accurate than the displayed precision suggests.

Below is a summary of available L-functions by {bpref "lfunction.degree"}[degree].  Note that the counts are not mutually exclusive, as different types of mathematical objects may have the same L-function.  For precomputed L-functions, objects in the database that are believed to give rise to this L-function are listed in the "origins" box on the L-functions home page.

*{bpref "lfunction.known_degree1"}[Degree 1]*

- The {bpref "lfunction.riemann"}[Riemann zeta-function] $`\zeta(s)`.

- $`7\,655\,469` Dirichlet L-functions associated to {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet"}[Dirichlet characters], including all $`1\,448\,484` of {bpref "lfunction.conductor"}[conductor] $`N\le 2800` (this includes the Riemann zeta-function).

*{bpref "lfunction.known_degree2"}[Degree 2]*

- $`14\,398\,359` L-functions of {bpref "cmf"}[classical modular forms] (more precisely, {bpref "cmf.embedding"}[embedded] {bpref "cmf.newform"}[newforms]); this includes the L-functions of all {bpref "rcs.cande.cmf"}[newforms in the database]  that have {bpref "cmf.weight"}[weight] $`k\le 200`  ({bpref "lfunction.motivic_weight"}[motivic weight] $`w=k-1\le 199`), including $`152\,268` {bpref "artin.lfunction"}[Artin L-functions] corresponding to weight $`1` newforms ($`6470` of the corresponding {bpref "artin"}[Artin representations] are in the database).

- $`1\,741\,002` L-functions of {bpref "ec"}[elliptic curves] over $`\Q` corresponding to the $`1\,741\,002` {bpref "ec.isogeny_class"}[isogeny classes] of {bpref "ec.q.conductor"}[conductor] $`N\le 400\,000`; of these, $`38\,042` have conductor $`N\le 10\,000` and correspond to L-functions of newforms in the database (those of {bpref "cmf.weight"}[weight] $`2`, trivial {bpref "cmf.character"}[character], and {bpref "cmf.dimension"}[dimension] $`1`).

- $`15\,659` dynamically computed L-functions of $`\GL(2)` {bpref "mf.maass.mwf"}[Maass forms].

- $`4296` dynamically computed Dedekind zeta-functions of the quadratic fields with {bpref "nf.abs_discriminant"}[absolute discriminant] $`|D|\le 7071` are available.

- $`55\,810` Artin L-functions arising from $`2`-dimensional Artin representations of conductor $`N\le 27\,000\,000`, of which all but $`6470` are dynamically computed.

*{bpref "lfunction.known_degree3"}[Degree 3]*

- $`1552` L-functions of $`\GL(3)` Maass forms.

- $`51` dynamically computed Dedekind zeta functions of the cubic fields with absolute discriminant $`|D|\le 368`.

- $`7925` dynamically computed Artin L-functions arising from $`3`-dimensional Artin representations of conductor $`N\le 90\,000` are available.

*{bpref "lfunction.known_degree4"}[Degree 4]*

- $`41\,653` {bpref "lfunction.primitive"}[imprimitive] {bpref "lfunction.rational"}[rational] L-functions corresponding to (Galois orbits of) newforms of dimension $`2`.

- $`253\,190` L-functions of elliptic curve isogeny classes over quadratic fields (all but $`9` isogeny classes of elliptic curves over quadratic fields in the database).

- $`66\,684` L-functions of {bpref "mf.hilbert"}[Hilbert modular forms] of {bpref "mf.hilbert.dimension"}[dimension] $`1` over real quadratic fields (each is also the L-function of an isogeny class of elliptic curves over a quadratic field).

- $`2913` dynamically computed L-functions of Hilbert modular forms of dimension $`d>1` over real quadratic fields.

- $`185\,541` L-functions of {bpref "mf.bianchi.newform"}[Bianchi newforms] of dimension $`1` over imaginary quadratic fields (all but the $`40` that do not correspond to elliptic curves).

- $`65\,534` L-functions of {bpref "g2c.isogeny_class"}[isogeny classes] of genus $`2` curves over $`\Q` (some of which also arise as L-functions of classical/Hilbert/Bianchi newforms, elliptic curves over quadratic fields, or products of L-functions of elliptic curves over $`\Q`).

- $`35` dynamically computed Artin L-functions arising from $`4`-dimensional Artin representations of conductor $`N\le 5196` are available.

*Degrees 5 to 40*

- $`115\,645` imprimitive rational L-functions corresponding to newforms of dimensions $`3` to $`20` and weight $`k\le 200` (there are at least $`2000` in each even degree from $`6` to $`40`).

Depends on: {uses "artin"}[] {uses "character.dirichlet"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.dimension"}[] {uses "cmf.embedding"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[] {uses "ec"}[] {uses "ec.isogeny_class"}[] {uses "ec.q.conductor"}[] {uses "g2c.isogeny_class"}[] {uses "lfunction"}[] {uses "lfunction.analytic_rank"}[] {uses "lfunction.conductor"}[] {uses "lfunction.degree"}[] {uses "lfunction.motivic_weight"}[] {uses "lfunction.rational"}[] {uses "lfunction.riemann"}[] {uses "lfunction.zeros"}[] {uses "mf.bianchi.newform"}[] {uses "mf.hilbert"}[] {uses "mf.hilbert.dimension"}[] {uses "mf.maass.mwf"}[] {uses "nf.abs_discriminant"}[]
:::

:::definition "rcs.cande.zeros.zeta"
*Completeness of Riemann Zeta Zeros Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.cande.zeros.zeta))

This database contains the $`103{,}800{,}788{,}359` zeros of the Riemann zeta function $`\zeta(s)` with imaginary part in the interval $`(0,30\,610\,046\,000]`, all of which have real part $`\frac{1}{2}`.
:::

:::definition "rcs.rigor.lfunction.curve"
*Reliability of Curve L-function Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.rigor.lfunction.curve))

L-functions of {bpref "g2c.g2curve"}[genus 2 curves] over $`\Q` in the database have been precomputed using heuristic precision bounds that should (but are not guaranteed to) ensure that all {bpref "lfunction.zeros"}[zeros] and special values are accurate to the displayed precision (up to an error in the last digit), and that the list of zeros is complete (within the region covered by the list, which includes the {bpref "lfunction.zeros"}[lowest zero]).

All L-function computations for genus 2 curves are conditional on the assumption that the L-function lies in the {bpref "lfunction.selberg_class"}[Selberg class], and in particular, has an analytic continuation that satisfies the {bpref "lfunction.functional_equation"}[functional equation].  For genus 2 curves with {bpref "g2c.good_reduction"}[bad reduction] at 2, this includes the 2-part of the {bpref "lfunction.conductor"}[conductor] and the {bpref "lfunction.euler_product"}[Euler factor] at 2, which was computed using the functional equation as described in Section 5 of .

In cases where a genus 2 L-function is {bpref "lfunction.primitive"}[imprimitive], the computation is also conditional on knowing its factorization into primitive L-functions.

The displayed analytic rank $`r` is an upper bound on the true {bpref "lfunction.analytic_rank"}[analytic rank] that is believed to be tight; it is known that there are $`r` (but not $`r+1`) zeros within a region of $`s=1/2` (in the {bpref "lfunction.normalization"}[analytic normalization]) of radius equal to the error implied by the displayed precision of the zeros (assuming the heuristic precision bounds are sufficient to achieve this error bound).

For L-functions of genus 2 curves over $`\Q` the parity of the analytic rank is determined by the {bpref "lfunction.sign"}[sign] $`\varepsilon=\pm 1` of the functional equation.  The parity of the displayed analytic rank is always consistent with the sign, thus any displayed analytic rank $`r\le 1` is correct provided that the heuristic precision bounds are sufficient to identify all zeros near $`s=1/2`.

Depends on: {uses "g2c.g2curve"}[] {uses "g2c.good_reduction"}[] {uses "lfunction.analytic_rank"}[] {uses "lfunction.conductor"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.normalization"}[] {uses "lfunction.primitive"}[] {uses "lfunction.selberg_class"}[] {uses "lfunction.sign"}[] {uses "lfunction.zeros"}[]
:::

:::definition "rcs.rigor.lfunction.dirichlet"
*Reliability of Dirichlet L-function Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.rigor.lfunction.dirichlet))

All {bpref "character.dirichlet"}[Dirichlet] L-functions in the database have been precomputed using rigorous precision bounds and interval arithmetic ensure that {bpref "lfunction.zeros"}[zeros] and special values are accurate to the displayed precision (up to an error in the last digit displayed), and that the list of zeros is complete (within the region covered by the list, including the {bpref "lfunction.zeros"}[lowest zero]).

For Dirichlet L-functions in the database, all listed zeros are known to lie on the {bpref "lfunction.critical_line"}[critcial line], and the {bpref "lfunction.analytic_rank"}[analytic rank] is known to be zero.

Depends on: {uses "character.dirichlet"}[] {uses "lfunction.analytic_rank"}[] {uses "lfunction.critical_line"}[] {uses "lfunction.zeros"}[]
:::

:::definition "rcs.rigor.lfunction.ec"
*Reliability of Elliptic Curve L-function Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.rigor.lfunction.ec))

L-functions of {bpref "ec"}[elliptic curves] over $`\Q` in the database have been precomputed using heuristic precision bounds that should (but are not guaranteed to) ensure that all {bpref "lfunction.zeros"}[zeros] and special values are accurate to the displayed precision (up to an error in the last digit), and that the list of zeros is complete (within the region covered by the list, including the {bpref "lfunction.zeros"}[lowest zero]).

For L-functions of elliptic curves over $`\Q` the displayed {bpref "lfunction.analytic_rank"}[analytic rank] is known to be correct in all but one case, the L-function of the elliptic curve $`\texttt{234446.a1}`, which is the unique curve of  {bpref "ec.rank"}[Mordell-Weil rank] 4 in the database.  For this L-function the analytic rank is known to be either 2 or 4.

Depends on: {uses "ec"}[] {uses "ec.rank"}[] {uses "lfunction.analytic_rank"}[] {uses "lfunction.zeros"}[]
:::

:::definition "rcs.rigor.lfunction.modular"
*Reliability of Modular L-function Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.rigor.lfunction.modular))

L-functions of {bpref "cmf.newform"}[classical], {bpref "mf.hilbert"}[Hilbert], and {bpref "mf.bianchi.newform"}[Bianchi] modular forms in the database have been precomputed using rigorous precision bounds and interval arithmetic ensure that {bpref "lfunction.zeros"}[zeros] and special values are accurate to the displayed precision (up to an error in the last digit displayed), and that the list of zeros is complete (within the region covered by the list, including the {bpref "lfunction.zeros"}[lowest zero]).  Each zero is known to lie within a disc whose radius is determined by the displayed precision, but note that this is not sufficient to prove that the lie on the {bpref "lfunction.critical_line"}[critical line].

The displayed analytic rank $`r` is an upper bound on the true {bpref "lfunction.analytic_rank"}[analytic] rank that is believed to be tight; it is known that there are $`r` (but not $`r+1`) zeros within a region of $`s=1/2` (in the {bpref "lfunction.normalization"}[analytic normalization]) of radius equal to the error implied by the displayed precision of the zeros).  In particular, any displayed analytic rank $`r=0` must be correct.

For {bpref "lfunction.self-dual"}[self-dual] L-functions the parity of the analytic rank is determined by the {bpref "lfunction.sign"}[sign] $`\varepsilon=\pm 1` of the functional equation that all modular L-functions are known to satisfy.  The parity of the displayed analytic rank is always consistent with the sign, thus for self-dual modular L-functions any displayed analytic rank $`r\le 1` must be correct.

For {bpref "cmf.newform"}[classical modular form] L-functions the displayed analytic rank has been rigorously verified in all cases (even when it is greater than one or the L-function is not self-dual).

For {bpref "mf.bianchi.newform"}[Bianchi modular form] L-functions, all results are  conditional on the assumption that the elliptic curve whose isogeny class has the same label as the Bianchi modular form actually has the same L-function; this is known if the elliptic curve is modular, but the modularity of the elliptic curves over imaginary quadratic fields is not known in general and has been explicitly verified for only a subset of the elliptic curves in the database.

Depends on: {uses "cmf.newform"}[] {uses "lfunction.analytic_rank"}[] {uses "lfunction.critical_line"}[] {uses "lfunction.normalization"}[] {uses "lfunction.self-dual"}[] {uses "lfunction.sign"}[] {uses "lfunction.zeros"}[] {uses "mf.bianchi.newform"}[] {uses "mf.hilbert"}[]
:::

:::definition "specialfunction.gamma" (lean := "Complex.Gamma, Complex.Gamma_eq_integral, Complex.Gamma_add_one, Complex.differentiableAt_Gamma, Complex.not_continuousAt_Gamma_neg_nat")
*Euler gamma function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/specialfunction.gamma))

The *(Euler) gamma function $`\Gamma(z)`* is defined by the integral

$$`\Gamma(z) = \int_0^{ \infty } e^{-t} t^{z} \frac{dt}{t}`

for Re$`(z) > 0`. It satisfies the functional equation

$$`\Gamma(z+1) = z \Gamma(z),`

and can thus be continued into a meromorphic function on the complex plane, whose poles are at the non-positive integers $`\{0,-1,-2,\ldots\}`.

Tau Ceti Review: [`Complex.Gamma`](https://taucetiproject.org/review/#/d/Complex.Gamma), [`Complex.Gamma_eq_integral`](https://taucetiproject.org/review/#/d/Complex.Gamma_eq_integral), [`Complex.Gamma_add_one`](https://taucetiproject.org/review/#/d/Complex.Gamma_add_one), [`Complex.differentiableAt_Gamma`](https://taucetiproject.org/review/#/d/Complex.differentiableAt_Gamma).
:::
