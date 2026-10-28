import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Automorphic forms" =>

This chapter lists the LMFDB definitions relating to *automorphic forms*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "mf"
*Modular form (general).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf))

The term *modular form* is used to describe several types
of complex functions which have a certain type of functional equation and growth condition.  Examples include:

- {bpref "cmf"}[classical modular forms]

- {bpref "mf.maass"}[Maass waveforms]

- {bpref "mf.hilbert"}[Hilbert modular forms]

- {bpref "mf.bianchi"}[Bianchi modular forms]

- {bpref "mf.siegel"}[Siegel modular forms]

Modular forms of the same {bpref "cmf.weight"}[weight] and {bpref "mf.multipliersystem"}[multiplier system] that are defined over the same group form a $`\mathbb{C}`-vector space.

Depends on: {uses "cmf"}[] {uses "cmf.weight"}[] {uses "mf.bianchi"}[] {uses "mf.hilbert"}[] {uses "mf.maass"}[] {uses "mf.multipliersystem"}[] {uses "mf.siegel"}[]
:::

:::definition "mf.base_change"
*Base change of a GL(2) modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.base_change))

Let $`K \supseteq F` be a finite extension of {bpref "nf"}[number fields], not necessarily Galois.  Let $`f` be a {bpref "mf"}[modular form] on $`\GL(2)` over $`F` of level $`\mathfrak{N}`.

For a (nonzero) prime $`\mathfrak{p} \nmid \mathfrak{N}` of $`F`, let $`L_{\mathfrak{p}}(f,T)` be the (good, degree 2) Euler factor at $`\mathfrak{p}`.  For $`r \in \Z_{\geq 1}` and a polynomial $`h(T) \in \C[T]`, let $`h^{(r)}(T)` be the polynomial whose roots are the $`r`-th powers of the roots of $`h(T)` (with $`\deg h^{(r)}(T)=\deg h(T)`).

We say that a modular form $`g` for $`\GL(2)` over $`K` is a *base change* of $`f` to $`K` if

$$`L_{\mathfrak{q}}(g,T) = L_{\mathfrak{p}}^{(r)}(f,T)`

for all but finitely many primes $`\mathfrak{q}` of $`K`, where $`\mathfrak{q}` lies over $`\mathfrak{p} \nmid \mathfrak{N}` and $`r` is the degree of $`\mathfrak{q}` over $`\mathfrak{p}`.

In general, we say that a form $`g` for $`\GL(2)` over $`K` is a *base change* if there exists a proper subfield $`K_0 \subsetneq K` and a modular form $`g_0` on $`\GL(2)` over $`K_0` such that $`g` is the base change of $`g_0` to $`K`.

In particular, if $`g` is a base change from $`\Q` to $`K`, then $`a_{\mathfrak{q}}(g) = a_{\sigma(\mathfrak{q})}(g)` for all $`\sigma \in \mathrm{Aut}(K)`.

Depends on: {uses "mf"}[] {uses "nf"}[]
:::

:::definition "mf.bianchi"
*Bianchi modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi))

Let $`K` be an imaginary quadratic {bpref "nf"}[number field] of {bpref "nf.class_number"}[class number] $`1`, and $`\mathcal{O}_K` be its {bpref "nf.ring_of_integers"}[ring of integers]. Let $`\Gamma` be a congruence subgroup of the
{bpref "mf.bianchi.bianchigroup"}[Bianchi group] $`\textrm{PSL}_2(\mathcal{O}_K)`.
Let $`\mathcal{H}_3` be {bpref "mf.bianchi.hyperbolic3space"}[hyperbolic 3-space]. A *Bianchi modular form* for $`\Gamma` with weight $`k\ge0` is a real analytic vector-valued function
$`F: \mathcal{H}_3 \rightarrow \mathbb{C}^{k+1}` with the properties

1. $`F|_k\gamma = F` for every $`\gamma \in \Gamma`;
2. $`F` is harmonic;
3. $`F` has at worst polynomial growth at each cusp of $`\Gamma`.

The set $`M(\Gamma,k)` of Bianchi modular forms for $`\Gamma` with weight $`k` is a finite dimensional complex vector space. Bianchi modular forms have a {bpref "mf.bianchi.fourierbessell"}[Fourier-Bessel expansion]., with coefficients indexed by elements of $`\mathcal{O}_K`.  Bianchi modular forms which vanish at all the cusps are called Bianchi cusp forms; their $`0`th coefficient is $`0`.

In condition 1, the weight $`k` "slash operator" is defined by

$$`(F |_k\gamma)(z):=\mathrm{Sym}^k(J(\gamma, z)^{-1}) \ F(\gamma z),`

where $`\mathrm{Sym}^k` is the symmetric $`k^{th}` power of the standard representation of $`\textrm{PSL}_2(\mathbb{C})` on $`\mathbb{C}^2`, and for $`\gamma=\begin{pmatrix} a & b \\ c&d \end{pmatrix} \in \textrm{PSL}_2(\mathbb{C})` we define

$$`J(\gamma, z):= \begin{pmatrix} cx+d & -cy \\ \bar{c}y & \overline{cx+d}\end{pmatrix}.`

Condition 2, harmonicity, is the analogue of the usual condition of being holomorphic for classical and Hilbert modular forms.  It means that $`\Psi F=0` and $`\Psi' F=0`, where the differential operators $`\Psi`, $`\Psi'` are the Casismir operators which generate the center of the universal enveloping algebra of the Lie algebra associated to the real Lie group $`\textrm{PSL}_2(\mathbb{C})`.

Depends on: {uses "mf.bianchi.bianchigroup"}[] {uses "mf.bianchi.hyperbolic3space"}[] {uses "nf"}[] {uses "nf.class_number"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "mf.bianchi.anr"
*Analytic rank of a Bianchi newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.anr))

Let $`F` be a {bpref "mf.bianchi.newform"}[Bianchi newform] over the imaginary quadratic field $`K`.   The *analytic rank* of $`F` is the order of vanishing of the L-function attached to $`F` at the centre of its critical strip.  The parity of the analytic rank is determined by the {bpref "mf.bianchi.sign"}[sign] of $`F`.

Depends on: {uses "mf.bianchi.newform"}[] {uses "mf.bianchi.sign"}[]
:::

:::definition "mf.bianchi.base_change"
*Base-change Bianchi modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.base_change))

For every {bpref "cmf.newform"}[classical elliptic newform] $`f` and every imaginary quadratic field $`K` one can define the *base-change* $`F` of $`f` to $`K`.

Usually the base-change of an elliptic newform $`f` is a cuspidal Bianchi newform, but there is one exceptional situation, when $`f` is a {bpref "cmf.cm_form"}[CM form] whose character is that of the extension $`K/\Q`.  In this case the base-change still exists but is not cuspidal.   One explanation for this is that the automorphic representation attached to $`f` is always irreducible, but after base-change to $`K` the representation splits as a sum of two Hecke characters over $`K`, whereas the representations attached to Bianchi (cuspidal) newforms are irreducible.

The {bpref "mf.bianchi.hecke_algebra"}[Hecke eigenvalues] of the base-change $`F` of $`f` to $`K` may be determined easily from those of the original elliptic newform $`f`.  For every prime $`p` not dividing the level of $`f`, if the eigenvalue of $`T_p` on $`f` is $`a_p` then the eigenvalue(s) $`a_{\frak{p}}` for $`{\frak{p}}\mid p` of its base-change are given by the following (where $`k` is the weight of $`f`):

- if $`p` splits in $`K` as $`p\mathcal{O}_K=\frak{p}\overline{\frak{p}}` then $`a_{\frak{p}}=a_{\overline{\frak{p}}}=a_p`;

- if $`p` ramifies in $`K` as $`p\mathcal{O}_K=\frak{p}^2` then $`a_{\frak{p}}=a_p`;

- if $`p` is inert in $`K` with $`p\mathcal{O}_K=\frak{p}` then $`a_{\frak{p}}=a_p^2-2p^{k-1}`.

For an explanation of the last formula, note that $`a_p=\alpha+\beta` where $`\alpha,\beta` are the associated eigenvalues of Frobenius, so that $`\alpha\beta=p^{k-1}`, while $`a_{\frak{p}}=\alpha^2+\beta^2`.

One consequence of this formula is the following fact: it is possible for the Hecke field of the base-change of $`f` to be of smaller degree than that of $`f` itself.  For example, it is possible to have a classical newform with quadratic Hecke field whose base-change has $`\Q` as its Hecke field.

Base-change as defined here is a special case of a more general definition of {bpref "mf.base_change"}[base change] for GL(2) modular forms.

Depends on: {uses "cmf.cm_form"}[] {uses "cmf.newform"}[] {uses "mf.base_change"}[] {uses "mf.bianchi.hecke_algebra"}[]
:::

:::definition "mf.bianchi.bianchigroup" (lean := "Matrix.ProjectiveSpecialLinearGroup, NumberField.RingOfIntegers, NumberField.IsTotallyComplex")
*Bianchi Groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.bianchigroup))

Let $`K` be an imaginary quadratic field and $`\mathcal{O}` be its ring of integers. Then the group

$$`\textrm{PSL}_2(\mathcal{O})`

is called the *Bianchi group associated to* $`K`.

Bianchi groups are discrete subgroups of $`\textrm{PSL}_2(\mathbb{C})`. The latter can be
identified with the group of orientation-preserving isometries of the
{bpref "mf.bianchi.hyperbolic3space"}[hyperbolic 3-space] $`\mathcal{H}_3` and as a result, every Bianchi group $`G` acts properly discontinuously on $`\mathcal{H}_3`. The quotient space $`G \backslash \mathcal{H}_3` is a non-compact hyperbolic 3-fold with finite volume.

Depends on: {uses "mf.bianchi.hyperbolic3space"}[]
:::

:::definition "mf.bianchi.cm"
*CM Bianchi newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.cm))

A {bpref "mf.bianchi.newform"}[Bianchi newform] $`F` of {bpref "mf.bianchi.level"}[level] $`\mathcal{N}` over an imaginary quadratic field $`K` is said to have *Complex Multiplication* or *CM* if it is equal to its own twist by a non-trivial Hecke character $`\chi`.  Such a character $`\chi` is necessarily quadratic.  The CM property is characterised in terms of the Hecke eigenvalues $`a_{\frak{p}}`of $`F` by the property that
$$`a_{\frak{p}} = \chi(\frak{p}) a_{\frak{p}}`

for all primes $`\frak{p}` not dividing the level.  In particular, $`a_{\frak{p}}=0` for all primes $`\frak{p}` for which $`\chi(\frak{p})=-1`.

Depends on: {uses "mf.bianchi.level"}[] {uses "mf.bianchi.newform"}[]
:::

:::definition "mf.bianchi.fourierbessell"
*Fourier-Bessel expansion.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.fourierbessell))

Let $`F` be a  {bpref "mf.bianchi"}[Bianchi modular form] of {bpref "mf.bianchi.weight"}[weight] $`2` with respect to the congruence subgroup $`\Gamma` of a {bpref "mf.bianchi.bianchigroup"}[Bianchi group]. As a function on {bpref "mf.bianchi.hyperbolic3space"}[hyperbolic 3-space] $`\mathcal{H}_3 = \{ (x,y) \in \C \times \R \mid y>0 \}`,  $`F` is a periodic function in the variable $`x\in\C`, and  has a *Fourier-Bessel expansion* of the form

$$`F(x,y)=\sum_{0 \not =\alpha \in \mathcal{O}_K}c(\alpha) y^2 \mathbb{K}\left ( \dfrac{4\pi|\alpha|y}{\sqrt{|\triangle|}} \right )
                        \psi\left (\dfrac{\alpha x}{\sqrt{\triangle}} \right ),`

where

$$`\psi(x)=e^{2\pi(x+\bar{x})}`

and

$$`\mathbb{K}(t)=\left ( -\dfrac{i}{2}K_1(y),K_0(y),\dfrac{i}{2}K_1(y) \right)`

with $`K_0,K_1` are the hyperbolic *K-Bessel functions* satisfying the differential equation

$$`\dfrac{dK_j}{dy^2}+\dfrac{1}{y}\dfrac{dK_j}{dy}-\left ( 1+\dfrac{1}{y^{2j}}\right )K_j = 0, \ \ \ \ j=0,1`

and decreasing rapidly at infinity.

Depends on: {uses "mf.bianchi"}[] {uses "mf.bianchi.bianchigroup"}[] {uses "mf.bianchi.hyperbolic3space"}[] {uses "mf.bianchi.weight"}[]
:::

:::definition "mf.bianchi.hecke_algebra"
*Hecke algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.hecke_algebra))

Let $`K` be an imaginary quadratic field and  $`\mathcal{M}_k(\Gamma)` the space of {bpref "mf.bianchi"}[Bianchi modular forms] of {bpref "mf.bianchi.weight"}[weight] $`k` and {bpref "mf.bianchi.level"}[level] $`\Gamma=\Gamma_0(\mathcal{N})`  for some integral ideal $`\mathcal{N}` of $`\mathcal{O}_K`.

The (level $`\mathcal{N}`) *Hecke algebra* $`\mathbb{T}` is a commutative algebra of linear *Hecke operators* acting on $`\mathcal{M}_k(\Gamma)`.  It preserves the {bpref "mf.bianchi.spaces"}[cuspidal subspace] $`\mathcal{S}_k(\mathcal{N})` of Bianchi cusp forms and the {bpref "mf.bianchi.spaces"}[new subspace] $`\mathcal{S}_k(\mathcal{N})^{\text{new}}`, and also preserves the rational and integral structures on these.

The Hecke algebra is generated by operators $`T_{\frak{p}}` for primes $`\frak{p}` of $`K`.   Each $`T_{\frak{p}}` is self-adjoint on $`\mathcal{S}_k(\mathcal{N})` and hence has eigenvalues which are totally real algebraic integers.  The new space $`\mathcal{S}_k(\mathcal{N})^{\text{new}}` has a basis consisting of forms which are eigenforms for all Hecke operators.

Depends on: {uses "mf.bianchi"}[] {uses "mf.bianchi.level"}[] {uses "mf.bianchi.weight"}[]
:::

:::definition "mf.bianchi.hyperbolic3space" (lean := "TauCeti.HyperbolicMetric, TauCeti.UpperHalfSpace, TauCeti.UpperHalfSpace.hyperbolicMetric")
*Hyperbolic 3-space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.hyperbolic3space))

*Hyperbolic 3-space* $`\mathcal{H}_3` is the unique connected, simply connected Riemannian manifold of dimension 3 with constant sectional curvature $`-1`.  A standard model for $`\mathcal{H}_3` is the upper half space model

$$`\{ (x,y) \in \C \times \R \mid y>0 \} = \{ (x_1,x_2,y) \in \R^3 \mid y>0 \}`

with the metric coming from the line element

$$`ds^2 = \dfrac{dx_1^2+dx_2^2+dy^2}{y^2}`

under which the distance $`d(P,P')` between two points $`P=(x_1,x_2,y)`,$`P'=(x'_1,x'_2,y')` is given by

$$`\cosh d(P,P')=1+ \dfrac{(x_1-x'_1)^2+(x_2-x'_2)^2+(y-y')^2}{2yy'}.`

The orientation-preserving isometries of $`\mathcal{H}_3` can be identified with the group $`\textrm{PSL}_2(\mathbb{C}) \simeq \textrm{PGL}_2(\mathbb{C})`. The action on $`\mathcal{H}_3` is given as

$$`\begin{pmatrix} a & b \\ c&d \end{pmatrix} \cdot z =
\Biggl ( \frac{(ax+b)\overline{(cx+d)}+a\bar{c}y^2}{|cx+d|^2+|c|^2y^2},\frac{y}{|cx+d|^2+|c|^2y^2} \Biggr )`

where $`z=(x,y) \in \mathcal{H}_3`.

It is computationally convenient to regard $`\mathcal{H}_3` inside the Hamiltonians $`\mathbb{H}`. We embed $`\mathcal{H}_3` into $`\mathbb{H}` via $`(x_1,x_2,y) \mapsto (x_1,x_2,y,0).` In other words, $`(x,y) \mapsto x+y j`. In particular, the element $`j \in \mathbb{H}` corresponds to $`(0,0,1) \in \mathbb{R}^3`. Then the action of
$`\textrm{PSL}_2(\mathbb{C})` on $`\mathcal{H}_3` takes the familiar form

$$`\begin{pmatrix} a & b \\ c&d \end{pmatrix} \cdot z = (az+b)(cz+d)^{-1}`

where the inverse of $`cz+d` is taken inside the skew-field $`\mathbb{H}`.

To see this transition, consider $`\mathbb{H}`  as a subalgebra of $`\mathbb{H} \otimes_{\mathbb{R}} \mathbb{C} \simeq M_2(\mathbb{C})` as follows

$$`\mathbb{H} \hookrightarrow M_2(\mathbb{C}), \ \ \ x+yj \mapsto \begin{pmatrix} x & -y \\ \bar{y} & \bar{x}\end{pmatrix}.`

In particular,  if $`x \in \C`, we have $`x \mapsto \begin{pmatrix} x & 0 \\ 0 & \bar{x}\end{pmatrix}`. This embedding respects the ring operations of $`\mathbb{H}`. It is now trivial to verify the equivalence between the two descriptions of the action of $`\textrm{PSL}_2(\mathbb{C})` on $`\mathcal{H}_3` that we gave above when we consider this matrix representation of
$`\mathcal{H}_3 \subset \mathbb{H}`.
:::

:::definition "mf.bianchi.level"
*Level of a Bianchi modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.level))

The <b>level</b> of a {bpref "mf.bianchi"}[Bianchi modular form] $`F` is the discrete subgroup $`\Gamma` of $`\PSL(2,\C)` such that $`F|_k\gamma = F` for every $`\gamma \in \Gamma`, where $`k` is the {bpref "mf.bianchi.weight"}[weight] of $`F`.

More precisely, let $`K` be an imaginary quadratic field; we suppose that $`K` has class number $`1` for simplicity.  For a Bianchi modular form over $`K`, the level $`\Gamma` is a congruence subgroup of the {bpref "mf.bianchi.bianchigroup"}[Bianchi group] $`\GL_2(\mathcal{O}_K)`.  The most common levels are those of the form

$$`\Gamma_0(\mathcal{N}) = \left\{\begin{pmatrix} a &b \\ c&d \end{pmatrix}\in\GL_2(\mathcal{O}_K)\mid c\in\mathcal{N}\right\}`

where $`\mathcal{N}` is an integral ideal of $`\mathcal{O}_K`.  In this case one says that $`F` has "level $`\mathcal{N}`" as an abbreviation for "level $`\Gamma_0(\mathcal{N})`".  The *level label* is the {bpref "nf.ideal_labels"}[ideal label] of $`\mathcal N` and the *level norm* is its norm (a positive integer).

Note these levels are *$`\mathbf{GL}_2`-levels*.  It is also possible to consider *$`\mathbf{SL}_2`-levels*, which are subgroups of $`\SL_2(\mathcal{O}_K)`: for example, $`\Gamma_0(\mathcal{N})\cap\SL_2(\mathcal{O}_K)`.  Since such groups are smaller, the corresponding spaces of Bianchi forms are larger, containing as a subspace the forms on $`\Gamma_0(\mathcal{N})`.

Depends on: {uses "mf.bianchi"}[] {uses "mf.bianchi.bianchigroup"}[] {uses "mf.bianchi.weight"}[] {uses "nf.ideal_labels"}[]
:::

:::definition "mf.bianchi.newform"
*Bianchi newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.newform))

A *Bianchi newform* $`F` is  a {bpref "mf.bianchi"}[Bianchi modular form] lying in the {bpref "mf.bianchi.spaces"}[new subspace] $`\mathcal{S}_k(\Gamma_0(\mathcal{N}))^{\text{new}}` of the space $`\mathcal{S}_k(\Gamma_0(\mathcal{N}))`  of Bianchi cusp forms of {bpref "mf.bianchi.weight"}[weight] $`k` and {bpref "mf.bianchi.level"}[level] $`\Gamma_0(\mathcal{N})` which is an normalised eigenform for the {bpref "mf.bianchi.hecke_algebra"}[Hecke algebra] $`\mathbb{T}`.

For each prime $`\frak{p}` of $`K` not dividing the level $`\mathcal{N}`, the eigenvalue $`a_{\frak{p}}` of $`T_{\frak{p}}` on $`F` is an algebraic integer lying in the *Hecke field* of $`F`.  This is a totally real Galois extension of $`\Q` whose degree $`d` is the dimension of the irreducible component of the rational newspace $`\mathcal{S}_k(\Gamma_0(\mathcal{N}))^{\text{new}}_{\Q}` containing $`F`.  The integer $`d` is the *dimension* of the newform $`F`.  The Hecke eigenvalue $`a_{\frak{p}}` is also the coefficient of index $`\frak{p}` in the Fourier expansion of $`F`.

Depends on: {uses "mf.bianchi"}[] {uses "mf.bianchi.hecke_algebra"}[] {uses "mf.bianchi.level"}[] {uses "mf.bianchi.spaces"}[] {uses "mf.bianchi.weight"}[]
:::

:::definition "mf.bianchi.sign"
*Sign of a Bianchi newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.sign))

Let $`F` be a {bpref "mf.bianchi.newform"}[Bianchi newform] of {bpref "mf.bianchi.level"}[level] $`\mathcal{N}`.  When $`\mathcal{N}=(N)` is principal, $`F` is an eigenform for the *Fricke involution* $`W_N` defined by the matrix $`\left(\begin{matrix}0&-1\\N&0\end{matrix}\right)`.

The *sign* of $`F` is \*minus\* the eigenvalue of $`W_N` on $`F`.  This is equal to the sign of the {bpref "lfunction.functional_equation"}[functional equation] satisfied by the {bpref "lfunction"}[L-function] attached to $`F`.  It follows that the {bpref "mf.bianchi.anr"}[analytic rank] of $`F` is even when $`F` has sign $`+1` and odd otherwise.

Depends on: {uses "lfunction"}[] {uses "lfunction.functional_equation"}[] {uses "mf.bianchi.level"}[] {uses "mf.bianchi.newform"}[]
:::

:::definition "mf.bianchi.spaces"
*Spaces of Bianchi modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.spaces))

The {bpref "mf.bianchi"}[Bianchi modular forms] of fixed {bpref "mf.bianchi.weight"}[weight] $`k` and {bpref "mf.bianchi.level"}[level] $`\Gamma` form a finite-dimensional vector space $`\mathcal{M}_k(\Gamma)` over the complex numbers $`\C`.
The forms $`F` which are {bpref "mf.bianchi"}[cuspidal] comprise  the *cuspidal subspace* $`\mathcal{S}_k(\Gamma)` of $`\mathcal{M}_k(\Gamma)`.
The algebra $`\mathbb{T}` of {bpref "mf.bianchi.hecke_algebra"}[Hecke operators] acts on the space $`\mathcal{M}_k(\Gamma)`, and preserves the cuspidal subspace $`\mathcal{S}_k(\Gamma)`.

$`\mathcal{S}_k(\Gamma)` is an inner product spaces with respect to an inner product analogous to the classical {bpref "cmf.petersson_scalar_product"}[Peterssen inner product] on spaces of {bpref "cmf"}[elliptic modular forms] over $`\Q`.   For level $`\Gamma_0(\mathcal{N})` the Hecke operators are all self-adjoint, so have totally real eigenvalues.

The *newspace*  $`\mathcal{S}_k(\mathcal{N})^{\text{new}}` at level $`\mathcal{N}` and weight $`k` is the orthogonal complement in $`\mathcal{S}_k(\mathcal{N})`, with respect to this inner product, of all *oldforms*: these are forms coming from lower levels $`\mathcal{M}\mid\mathcal{N}` with $`N(\mathcal{M})<N(\mathcal{N})`.  The Hecke algebra preserves the newspace and acts semisimply on it, so that the newspace has a basis of simultaneous eigenforms for the Hecke algebra.  A *newform* is an eigenform normalised so that the coefficient of $`(1)` in its Fourier expansion is $`1`.

The complex vector space $`\mathcal{S}_k(\mathcal{N})` has a rational structure: the subset $`\mathcal{S}_k(\mathcal{N})_{\Q}` of forms with rational Fourier coefficients is a vector space over $`\Q` such that $`\mathcal{S}_k(\mathcal{N}) = \mathcal{S}_k(\mathcal{N})_{\Q}\otimes\C`.  There is also an integral structure, and the Hecke algebra $`\mathbb{T}`  preserves both, so that the Hecke eigenvalues are all algebraic integers.

The irreducible components of $`\mathcal{S}_k(\mathcal{N})_{\Q}` under the action of $`\mathbb{T}` have *dimension* $`d\ge1`, with a basis consisting of $`d` conjugate newforms whose Fourier coefficients are Galois conjugate elements of the associated *Hecke field*, a Galois extension of $`\Q` of degree $`d`.  The *dimension* of a newform is therefore the dimension of the $`\Q`-irreducible component it lies in, and also the degree of its Hecke field.

Depends on: {uses "cmf"}[] {uses "cmf.petersson_scalar_product"}[] {uses "mf.bianchi"}[] {uses "mf.bianchi.hecke_algebra"}[] {uses "mf.bianchi.level"}[] {uses "mf.bianchi.weight"}[]
:::

:::definition "mf.bianchi.weight"
*Weight of a Bianchi modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.weight))

The *weight* of a {bpref "mf.bianchi"}[Bianchi modular form] is the positive integer $`k` occurring in the transformation formula.  In addition, Bianchi modular forms are vector-valued functions $`F: \mathcal{H}_3 \rightarrow \C^{k+1}` where $`\mathcal{H}_3` is {bpref "mf.bianchi.hyperbolic3space"}[Hyperbolic 3-space], and $`k` is the weight.  For example a Bianchi modular form of weight $`2` takes values in $`\C^3`.

Depends on: {uses "mf.bianchi"}[] {uses "mf.bianchi.hyperbolic3space"}[]
:::

:::definition "mf.bianchi.weight2"
*Weight 2 Bianchi modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.weight2))

Weight 2 Bianchi modular forms are particularly important in regard to their conjectural connections with abelian varieties of $`\textrm{GL}_2`-type. In the weight 2  case, we have $`F: \mathcal{H}_3 \rightarrow \mathbb{C}^3` and

$$`(F |_k\gamma)(z)=\dfrac{1}{|r|^2+|s|^2}
\begin{pmatrix}  \bar{r}^2 & 2\bar{r}s & s^2 \\
                          -\bar{r}\bar{s} & |r|^2-|s|^2 & rs \\
                          \bar{s}^2 & -2r\bar{s} & r^2 \end{pmatrix} F(\gamma z)`

where $`\gamma=\begin{pmatrix} a &b \\ c&d \end{pmatrix}` and $`r=cx+d` and $`s=cy`.

Let $`\beta_1:=-\frac{dx}{y}, \beta_2:= \frac{dy}{y}, \beta_3:=\frac{d\bar{x}}{y}` be a basis of differential 1-forms on $`\mathcal{H}_3`.
A differential form $`\omega` is _harmonic_ if $`\Delta \omega =0` where $`\Delta=d \circ \delta + \delta \circ d`
is the usual Laplacian with $`d` being the exterior derivative and $`\delta` the codifferential operator.
Then $`\textrm{PSL}_2(\mathbb{C})` acts on the space of differential 1-forms as

$$`\gamma \cdot {}^t(\beta_1,\beta_2,\beta_3)_{(z)} = Sym^2(J(\gamma,z)){}^t(\beta_1,\beta_2,\beta_3)_{(z)}.`

A weight $`2` Bianchi modular form for $`\Gamma` can be _alternatively_ described as
a real analytic function $`F=(F_1,F_2,F_3) : \mathcal{H}_3 \rightarrow \mathbb{C}^3`
such that

$$`F_1\beta_1 + F_2 \beta_2+F_3\beta_3`

is a harmonic differential 1-form on $`\mathcal{H}_3` that is $`\Gamma`-invariant.
It is called *cuspidal* if it satisfies the extra property

$$`\int_{\mathbb{C} / \mathcal{O}_K} (F| \gamma )(x,y) dx = 0`

for every $`\gamma \in \textrm{PSL}_2(\mathcal{O}_K).`

This condition is equivalent to saying that the constant coefficient in the Fourier-Bessel expansion of $`F|\gamma` is equal to zero for every $`\gamma \in \textrm{PSL}_2(\mathcal{O}_K)`.
:::

:::definition "mf.cm"
*Complex multiplication.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.cm))

A {bpref "mf"}[modular form] $`f` for $`\GL(2)` over a {bpref "nf"}[number field] $`F` has *complex multiplication (CM)* if it is equal to its twist by a nontrivial {bpref "character.hecke"}[Hecke character] $`\chi` over $`F`, or equivalently

$$`a_{\frak{p}} = \chi(\frak{p}) a_{\frak{p}}`

for all good primes $`\frak{p} \nmid \frak{N}`.  Such a character $`\chi` is necessarily quadratic, and $`a_{\frak{p}} = 0` for all good primes  $`\frak{p}` such that $`\chi(\frak{p}) = -1`.

Depends on: {uses "character.hecke"}[] {uses "mf"}[] {uses "nf"}[]
:::

:::definition "mf.ellitpic.self_twist" (lean := "HeckeRing.GL2.Newform.HasSelfTwist, HeckeRing.GL2.Newform.HasCMBy, HeckeRing.GL2.Newform.HasRMBy")
*Self twist of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.ellitpic.self_twist))

A {bpref "cmf.newform"}[newform] $`f=\sum a_n q^n` admits a *self twist* by a nontrivial {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet"}[Dirichlet character] $`\chi` if we have $`a_p=\chi(p)a_p` for all but finitely many primes $`p`.

This can occur only when $`\chi` has {bpref "character.dirichlet.order"}[order] $`2` and $`a_p=0` for all primes $`p` not dividing the {bpref "cmf.level"}[level] of $`f` for which $`\chi(p)=-1`.
The character $`\chi` is then the Kronecker character of a quadratic field $`K` and may be identified by the {bpref "nf.discriminant"}[discriminant] $`D` of $`K`.

If $`D` is negative, the modular form $`f` is said to have {bpref "cmf.cm_form"}[complex multiplication] (CM) by $`K`, and if $`D` is positive, $`f` is said to have {bpref "cmf.rm_form"}[real multiplication] (RM) by $`K`.  The latter can occur only when $`f` is a modular form of {bpref "cmf.weight"}[weight] $`1` whose {bpref "cmf.projective_image"}[projective image] is dihedral.

It is possible for a modular form to have more than one self twist; this occurs precisely when $`f` is a modular form of weight one whose projective image is isomorphic to $`D_2:=C_2\times C_2`; in this case $`f` admits three self twists, two of which are CM and one of which is RM.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.projective_image"}[] {uses "cmf.rm_form"}[] {uses "cmf.weight"}[] {uses "nf.discriminant"}[]
:::

:::definition "mf.half_integral_weight"
*Half-integral weight modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.half_integral_weight))

Let $`k` be an odd integer, and let $`N` a positive integer divisible by $`4`. Let $`\chi` be a {bpref "character.dirichlet"}[character] modulo $`N`. A *modular form of half-integral {bpref "cmf.weight"}[weight]* $`k/2` , {bpref "cmf.level"}[level] $`N` and character $`\chi` is an holomorphic function defined on the upper half plane $`\mathcal{H}`, satisfying the transformation formula

$$`f(\gamma z) = \chi(d) j(\gamma, z)^k f(z)`

for every $`\gamma=\left(\begin{matrix} a & b \\ c & d \end{matrix}\right)\in\Gamma_0(N)` and $`z\in \mathcal{H}`, and being holomorphic at the {bpref "group.fuchsian.cusps"}[cusps]. Here the automorphy factor $`j(\gamma, z)` is given by

$$`j(\gamma, z) = \theta(\gamma z)/\theta(z),`

where $`\theta` denotes the classical {bpref "mf.half_integral_weight.theta"}[theta function]. This space is denoted by $`M_{k/2}(N)`, and the subspace of {bpref "cmf.cusp_form"}[cusp forms] is denoted by $`S_{k/2}(N)`.

These modular forms are related with integral weight modular forms through the {bpref "cmf.shimura_correspondence"}[Shimura correspondence]. In terms of this correspondence, the space of cusp forms can be decomposed according to the Shimura decomposition.

Depends on: {uses "character.dirichlet"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.shimura_correspondence"}[] {uses "cmf.weight"}[] {uses "group.fuchsian.cusps"}[] {uses "mf.half_integral_weight.theta"}[]
:::

:::definition "mf.half_integral_weight.theta" (lean := "jacobiTheta")
*Theta function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.half_integral_weight.theta))

The (classical) *theta function* $`\theta(z)` is a holomorphic modular form of {bpref "mf.half_integral_weight"}[half-integral weight] $`1/2` and {bpref "cmf.level"}[level] 4, defined by the formula

$$`\theta(z)=\sum_{n=-\infty}^\infty e^{\pi iz n^2}.`

It has the following <em>product expansion</em>:

$$`\theta(z)=\prod_{n\geq1}(1+q^{n-1/2})^2(1-q^n),`

where $`q=e^{2\pi iz}`.

The (classical) theta function is related to the {bpref "mf.half_integral_weight.dedekind_eta"}[Dedekind eta function] via the formula:

$$`\theta(z)=\frac{\eta^5(z)}{\eta^2(z/2)\eta^2(2z)}=\frac{\eta^2((z+1)/2)}{\eta(z+1)}.`

Depends on: {uses "cmf.level"}[] {uses "mf.half_integral_weight.dedekind_eta"}[]
:::

:::definition "mf.hilbert"
*Hilbert modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.hilbert))

Let $`F` be a {bpref "nf.totally_real"}[totally real] {bpref "nf"}[number field] $`F` of {bpref "nf.degree"}[degree] $`n>1`.  Let $`v_1,\ldots,v_n \colon F \hookrightarrow \R` be the real embeddings of $`F`, and for $`a \in F` abbreviate $`a_i \colonequals v_i(a)` and extend this elementwise to matrices.  Write $`\alpha \in F_{>0}^\times` if $`\alpha` is {bpref "nf.totally_positive"}[totally positive] and $`\Z_{F,>0}^\times \colonequals \Z_F^\times \cap F_{>0}^\times`.

Let $`k_1,\dots,k_n \geq 2` be positive integers of the same parity, and let $`\mathfrak{N}` be a nonzero ideal of the {bpref "nf.ring_of_integers"}[ring of integers] $`\Z_F` of $`F`.

For an ideal $`\mathfrak{b} \subseteq \Z_F`, let

$$`\gamma\in\Gamma_0(\mathfrak{N})_{\mathfrak{b}} \colonequals \left\{\gamma=\begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \GL_2(F) : c \in \mathfrak{Nb}, \ b \in \mathfrak{b}^{-1},\ \text{ and } \det(\gamma) \in \Z_{F,>0}^\times \right\}.`

A *Hilbert modular form* of weight $`(k_1\ldots,k_n)` and level $`\mathfrak{N}` is a tuple $`(f_{\mathfrak{b}})_{\mathfrak{b}}` of holomorphic functions $`f \colon \mathcal{H}^n\rightarrow \C`, indexed by ideals $`\mathfrak{b}` representing the {bpref "nf.narrow_class_group"}[narrow class group] of $`\Z_F`, such that for all $`z=(z_1\ldots,z_n)\in\mathcal{H}^n` and all $`\gamma=\begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(\mathfrak{N})_{\mathfrak{b}}` we have

$$`f_{\mathfrak{b}}(\gamma z)=f_{\mathfrak{b}}\left(\frac{a_1z_1+b_1}{c_1z_1+d_1}, \ldots, \frac{a_nz_n+b_n}{c_nz_n+d_n}\right)=\prod_{i=1}^n\left( \frac{(c_iz_i+d_i)^{k_i}}{(a_id_i-b_ic_i)^{k_i/2}}\right)f_{\mathfrak{b}}(z).`

A *Hilbert cusp form* is a Hilbert modular form that vanishes at the cusps.

Depends on: {uses "nf"}[] {uses "nf.degree"}[] {uses "nf.narrow_class_group"}[] {uses "nf.ring_of_integers"}[] {uses "nf.totally_positive"}[] {uses "nf.totally_real"}[]
:::

:::definition "mf.hilbert.dimension"
*Dimension of a Hecke orbit.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.hilbert.dimension))

The *dimension* of a Hecke orbit is its $`\Q`-vector space dimension.  The dimension of the Hecke orbit of a form $`f` is also equal to the degree over $`\Q` of the field generated by the Hecke eigenvalues of $`f`.
:::

:::definition "mf.hilbert.level_norm"
*Level of a Hilbert modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.hilbert.level_norm))

Given a Hilbert modular form $`f` that is defined in terms of the {bpref "nf.totally_real"}[totally real] {bpref "nf"}[number field] $`F`, the *level* of $`f` is a nonzero ideal $`\mathfrak{N}` of the {bpref "nf.ring_of_integers"}[ring of integers] $`\Z_F` of $`F` that determines the group $`\Gamma_0(\mathfrak{N})` under which $`f` transforms. In the LMFDB, such an ideal $`\mathfrak{N}` is identified by a label.

The *level norm* is the absolute norm of the level of the form.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[] {uses "nf.totally_real"}[]
:::

:::definition "mf.hilbert.weight_vector"
*Weight of a Hilbert modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.hilbert.weight_vector))

The *weight* of a {bpref "mf.hilbert"}[Hilbert modular form] $`f` is the vector of positive integers $`(k_1\ldots,k_n)` occurring in the transformation formula for $`f`. When the $`k_i` are all equal to $`k \in \Z_{>0}`, we say $`f` has *parallel weight* $`k`.

Depends on: {uses "mf.hilbert"}[]
:::

:::definition "mf.maass"
*Maass forms on GL(n).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass))

The term *Maass form* is used for automorphic forms on $`GL_{n}` (for some positive integer n), which are not holomorphic.
Instead of satisfying the  Cauchy-Riemann equations (as holomorphic functions do), these functions are eigenfunctions of the Casimir element in the universal enveloping algebra of the Lie algebra of $`GL_{n}`.
:::

:::definition "mf.maass.exceptional_eigenvalue"
*Exceptional eigenvalues of Maass forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.exceptional_eigenvalue))

Each {bpref "mf.maass.mwf.eigenvalue"}[eigenvalue] $`\lambda` of a {bpref "mf.maass.mwf"}[Maass form] can be written as $`\lambda = \frac{1}{4} + R^2`, where $`R` is the {bpref "mf.maass.mwf.spectralparameter"}[spectral parameter].
Each eigenvalue is real and nonnegative, and the spectral parameter is either purely real or purely imaginary.

If $`R` is purely real (so $`0 < \lambda < \frac{1}{4}`), then $`\lambda` is called *exceptional*. No exceptional eigenvalues are known. Selberg conjectured that they don't exist \[Sel65\].

\[Sel65\]: Selberg, Atle (1965), "On the estimation of Fourier coefficients of modular forms", in Whiteman, Albert Leon (ed.), Theory of Numbers, Proceedings of Symposia in Pure Mathematics, vol. VIII, Providence, R.I.: American Mathematical Society, pp. 1–15.

Depends on: {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.eigenvalue"}[] {uses "mf.maass.mwf.spectralparameter"}[]
:::

:::definition "mf.maass.label"
*Label of a Maass newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.label))

The *label* of a {bpref "mf.maass.mwf"}[Maass newform] $`f \in M_k(\Gamma_0(N), \chi)` either has the format $`N.k.a.m.d` or $`N.m`, where

- $`N` is the {bpref "mf.maass.mwf.level"}[level];

- $`k` is the {bpref "mf.maass.mwf.weight"}[weight];

- $`N.a` is the Conrey label of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi`;

- $`m` is the {bpref "mf.maass.spectral_index"}[spectral index], which uniquely identifies the {bpref "mf.maass.mwf.eigenvalue"}[eigenvalue] $`\lambda` of $`f`;

- $`d` indicates which form among those of level $`N`, Dirichlet character $`N.a`, and eigenvalue $`\lambda` this is.

The shorter form is used when $`k=0` and $`a=1` and $`d=1`.

For squarefree level, it is conjectured that there is only one Maass form per eigenvalue $`\lambda`, hence $`d` is (currently) always $`1`. Generally, there are only finitely many Maass newforms in $`M_k(\Gamma_0(N), \chi)` with the same eigenvalue $`\lambda`. Then $`d` denotes the index among these finitely many forms, where the ordering is lexicographical in the sequence $`\{ \bigl(\mathrm{Re}(a(n)), \mathrm{Im}(a(n))\bigr) \}_{n \geq 1}`.

Depends on: {uses "character.dirichlet"}[] {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.eigenvalue"}[] {uses "mf.maass.mwf.level"}[] {uses "mf.maass.mwf.weight"}[] {uses "mf.maass.spectral_index"}[]
:::

:::definition "mf.maass.mwf"
*Maass form on GL2(R) with trivial character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf))

Maass forms
------------------
A *Maass form* (of weight 0) on a subgroup $`\Gamma` of $`\GL_{2}(\R)`
is a smooth, square-integrable, automorphic eigenfunction of the {bpref "mf.maass.mwf.laplacian"}[Laplace-Beltrami operator] $`\Delta`. In other words,

$$`f\in C^\infty(\mathcal{H}),\quad f\in L^2(\Gamma\backslash{\mathcal H}),\quad f(\gamma z)=f(z)\ \forall\gamma\in\Gamma,\quad (\Delta+\lambda)f(z)=0 \textrm{ for some } \lambda \in \C.`

Maass forms of weight $`k`
------------------

A Maass form $`f` of {bpref "mf.maass.mwf.weight"}[weight]  $`k` and {bpref "mf.multipliersystem"}[multiplier system] $`v` on a group $`\Gamma` is a smooth function $`f:\mathcal{H} \rightarrow\C` with the following properties:

1. $`f` transforms according to a unitary weight $`k` {bpref "mf.slash_action"}[slash-action]:
 $`f|[\gamma,k]( z) = v(\gamma) f(z)` for all $`\gamma \in \Gamma` where
$`f|[\gamma,k]( z) = \exp(-ik\mathrm{Arg}(c z+d)) f(\gamma z)` for $`\gamma=\begin{pmatrix}a & b \\ c & d \end{pmatrix}`

2. $`f` is an eigenfunction of the corresponding weight $`k` Laplacian
$`\Delta_k = y^2\left( \frac{\partial^2}{\partial x^2}+\frac{\partial^2}{\partial y^2}\right) - iky\frac{\partial}{\partial x}`

If the level is equal to 1, the only possible multiplier systems are given by the Dedekind eta function. A compatible multiplier system for weight $`k\in \R` is given by

$$`v(A) = v_{\eta}^{2k}:=\eta(Az)^{2k}/\eta(z)^{2k}`

or one of its 6 conjugates. One can show that $`v(A)` is well-defined and independent of the point $`z` in the upper half-plane.

Remark:
-------
 One can also consider Maass forms transforming with the usual "holomorphic" weight $`k` slash-action. In this case the corresponding weight $`k` Laplacian will look slightly different: $`\Delta_k = y^2\left( \frac{\partial^2}{\partial x^2}+\frac{\partial^2}{\partial y^2}\right) - iky\left(\frac{\partial}{\partial x}+i\frac{\partial}{\partial y}\right).`
This convention is usually used in the context of Harmonic weak Maass forms.

Depends on: {uses "mf.maass.mwf.laplacian"}[] {uses "mf.multipliersystem"}[] {uses "mf.slash_action"}[]
:::

:::definition "mf.maass.mwf.coefficients"
*Maass form coefficients.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.coefficients))

Let $`f` be a {bpref "mf.maass.mwf"}[Maass newform] of {bpref "mf.maass.mwf.weight"}[weight] 0 on $`\Gamma_0(N)` with {bpref "mf.maass.mwf.spectralparameter"}[spectral parameter] $`R`.  If $`f` has even {bpref "mf.maass.mwf.symmetry"}[symmetry] then as a function on the complex upper half plane it can be uniquely expressed in the form

$$`f(x+iy) = \sum_{n=1}^\infty a_n\sqrt{y}K_{iR}(2\pi ny)\cos(2\pi nx),`

where $`K_{iR}(\cdot)` denotes the {bpref "specialfunction.k_bessel"}[$`K`-Bessel function] with parameter $`\nu=iR` and the $`a_n` are real numbers.

If $`f` has odd symmetry it can instead be written as

$$`f(x+iy) = \sum_{n=1}^\infty a_n\sqrt{y}K_{iR}(2\pi ny)\sin(2\pi nx).`

In both cases the real numbers $`a_n` are the *coefficients* of $`f` and are used to define its {bpref "lfunction"}[L-function] $`L(f,s)=\sum_{n=1}^\infty a_nn^{-s}`.

Depends on: {uses "lfunction"}[] {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.spectralparameter"}[] {uses "mf.maass.mwf.symmetry"}[] {uses "mf.maass.mwf.weight"}[] {uses "specialfunction.k_bessel"}[]
:::

:::definition "mf.maass.mwf.dimension"
*Multiplicity of an eigenvalue.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.dimension))

The *multiplicity* of an {bpref "mf.maass.mwf.eigenvalue"}[eigenvalue] $`\lambda` of the {bpref "mf.maass.mwf.laplacian"}[Laplace-Beltrami operator] refers to the dimension of the eigenspace $`\mathcal{M}(\Gamma,\chi,\lambda)` of {bpref "mf.maass.mwf"}[Maass newforms] on the group $`\Gamma` of {bpref "cmf.character"}[character] $`\chi` with the same Laplace eigenvalue $`\lambda`.

It is generally believed that these eigenspaces are one-dimensional unless there is a symmetry present. There are essentially three known cases where the dimension is greater than 1:

1. If the eigenvalue corresponds to an oldspace in the sense of Atkin and Lehner.

2. If the character $`\chi` has quadratic characters as factors.

3. If $`\Gamma=\Gamma_{0}(N)` with $`9|N`

The above three cases are proven and the generalization of 3. to other square factors greater than 9 is conjectured.

Depends on: {uses "cmf.character"}[] {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.eigenvalue"}[] {uses "mf.maass.mwf.laplacian"}[]
:::

:::definition "mf.maass.mwf.eigenvalue"
*The eigenvalue of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.eigenvalue))

The *eigenvalue* $`\lambda` of a {bpref "mf.maass.mwf"}[Maass newform] on GL(2) refers to the eigenvalue of the eigenspace of the {bpref "mf.maass.mwf.laplacian"}[Laplace-Baltrami operator] in which it lies.

This eigenvalue is a real number that is typically written in the form $`\lambda=\frac{1}{4}+R^2`, where $`R` is the {bpref "mf.maass.mwf.spectralparameter"}[spectral parameter].

Depends on: {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.laplacian"}[] {uses "mf.maass.mwf.spectralparameter"}[]
:::

:::definition "mf.maass.mwf.fourierexpansion"
*Fourier expansion of Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.fourierexpansion))

The *Fourier expansion* (at infinity) of a {bpref "mf.maass.mwf"}[Maass form] of a non-cocompact subgroup of PSL$`(2,\R)` reads

$$`f(z)=\sum_{n\in\Z}a(n)\sqrt{y}K_{ir}(2\pi|n|y)e^{2\pi inx},`

where $`K_{ir}(x)` is a {bpref "specialfunction.k_bessel"}[$`K`-Bessel function] and the expansion coefficients $`a(n)` are related to Hecke eigenvalues.

If the Maass form is {bpref "mf.maass.mwf.symmetry"}[even], then the expansion simplifies to

$$`f(z)=\sum_{n=1}^{\infty}c(n)\sqrt{y}K_{ir}(2\pi ny)\cos(2\pi nx),`

and if the form is {bpref "mf.maass.mwf.symmetry"}[odd]

$$`f(z)=\sum_{n=1}^{\infty}c(n)\sqrt{y}K_{ir}(2\pi ny)\sin(2\pi nx).`

For a prime $`p` the coefficient $`c(p)` equals the corresponding Hecke eigenvalue.

Depends on: {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.symmetry"}[] {uses "specialfunction.k_bessel"}[]
:::

:::definition "mf.maass.mwf.laplacian"
*Laplace-Beltrami operator (hyperbolic).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.laplacian))

The *Laplace-Beltrami operator* on the {bpref "mf.upper_half_plane"}[hyperbolic upper half-plane] is given by

$$`\Delta = -y^{2} \left(\frac{\partial^{2}}{\partial x^{2}}+\frac{\partial^{2}}{\partial y^{2}}\right).`

Note that it is sometimes defined without the minus sign in front.

Depends on: {uses "mf.upper_half_plane"}[]
:::

:::definition "mf.maass.mwf.level"
*The level of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.level))

A {bpref "mf.maass.mwf"}[Maass form] $`f` is said to have *level* $`N` if $`f` is invariant under the principal congruence subgroup $`\Gamma(N)`.

Depends on: {uses "mf.maass.mwf"}[]
:::

:::definition "mf.maass.mwf.spectralparameter"
*The spectral parameter of a Maass waveform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.spectralparameter))

If $`f` is a {bpref "mf.maass.mwf"}[Maass form] with {bpref "mf.maass.mwf.laplacian"}[Laplace] eigenvalue $`\lambda = \frac{1}{4}+R^{2}`, the number $`R` is said to be the *spectral parameter* of $`f`.

Depends on: {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.laplacian"}[]
:::

:::definition "mf.maass.mwf.symmetry"
*The symmetry of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.symmetry))

The {bpref "group.sl2z"}[modular group] and its congruence subgroups has an outer automorphism of order two, which is given by the reflection in the imaginary axis: $`z=x+iy \mapsto -\bar{z}=-x+iy`.
This map belongs to $`\mathrm{PGL}(2,\mathbb{Z})` and can be represented by the matrix
$`\begin{pmatrix} -1 & 0 \\ 0 & 1 \end{pmatrix}`.

A {bpref "mf.maass.mwf"}[Maass form] $`f` is said to be *even* if $`f(-\bar{z})=f(z)` and *odd* if $`f(-\bar{z})=-f(z)`.

Depends on: {uses "group.sl2z"}[] {uses "mf.maass.mwf"}[]
:::

:::definition "mf.maass.mwf.weight"
*The weight of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.weight))

A {bpref "mf.maass.mwf"}[Maass form] is of *weight* $`k` if it is an eigenfunction of the weight $`k` {bpref "mf.maass.mwf.laplacian"}[Laplacian]
$`\Delta_k = y^2\left( \frac{\partial^2}{\partial x^2}+\frac{\partial^2}{\partial y^2}\right) - iky\frac{\partial}{\partial x}`.

Depends on: {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.laplacian"}[]
:::

:::definition "mf.maass.mwf.weight0"
*Maass forms of weight 0.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.weight0))

A *Maass form* of {bpref "mf.maass.mwf.weight"}[weight] 0 on a subgroup $`\Gamma` of $`\GL_{2}(\R)`
is a smooth, square-integrable, automorphic eigenfunction of the {bpref "mf.maass.mwf.laplacian"}[Laplace-Beltrami operator] $`\Delta`. In other words,

$$`f\in C^\infty(\mathcal{H}),\quad f\in L^2(\Gamma\backslash{\mathcal H}),\quad f(\gamma z)=f(z)\ \forall\gamma\in\Gamma,\quad (\Delta+\lambda)f(z)=0 \textrm{ for some } \lambda \in \C.`

Depends on: {uses "mf.maass.mwf.laplacian"}[] {uses "mf.maass.mwf.weight"}[]
:::

:::definition "mf.maass.picard" (lean := "HyperbolicThreeSpace.IsPicardMaassForm, HyperbolicThreeSpace.PicardGroup, HyperbolicThreeSpace.laplacian, HyperbolicThreeSpace.moebius, HyperbolicThreeSpace.hyperbolicVolume")
*Maass forms on PSL(2,Z\[i\]).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.picard))

A *Maass form* is a smooth, square-integrable, automorphic eigenfunction of the Laplacian,
$$`f\in C^\infty({\mathcal H}),\quad f\in L^2(\Gamma\backslash{\mathcal H}),\quad f(\gamma z)=f(z)\ \forall\gamma\in\Gamma,\quad (\Delta+\lambda)f(z)=0.`

Maass forms on PSL$`(2,{\mathbb{Z}}[i])` live in the upper half-space $`{\mathcal H}=\{z=x+iy \mid x\in{\mathbb{C}},\ y>0\}`, equipped with the hyperbolic metric $`ds=|dz|/y`.

The *Picard group* $`\Gamma=`PSL$`(2,{\mathbb{Z}}[i])` is a discrete, cofinite, but non-cocompact subgroup of the group of isometries PSL$`(2,{\mathbb{C}})` ,where the isometries are given by linear fractional transformations $`z\to(az+b)(cz+d)^{-1}` with $`a,b,c,d\in {\mathbb{C}}`, $`ad-bc\not=0`.
:::

:::definition "mf.maass.picard.eigenvalue" (lean := "HyperbolicThreeSpace.picardTrueEigenvalue, HyperbolicThreeSpace.HasPicardSpectralParameter, HyperbolicThreeSpace.IsPicardMaassForm.eigenvalue_eq, HyperbolicThreeSpace.HasPicardSpectralParameter.eq_or_eq_neg, HyperbolicThreeSpace.IsPicardMaassForm")
*Spectral parameter of Maass forms on PSL(2,Z\[i\]).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.picard.eigenvalue))

Each {bpref "mf.maass.picard"}[Maass form] is associated to an *eigenvalue* via the eigenvalue equation $`(\Delta+\lambda)f(z)=0` where $`\Delta` is the Laplacian.  It is convenient to introduce the *spectral parameter* $`r` which is also called the eigenvalue.  Only if one speaks about the *true eigenvalue* one refers to $`\lambda`, since by convention *eigenvalue* refers to $`r`.  In {bpref "mf.bianchi.hyperbolic3space"}[hyperbolic 3-space], the eigenvalue is connected to the true eigenvalue via $`\lambda=r^2+1`.

Depends on: {uses "mf.bianchi.hyperbolic3space"}[] {uses "mf.maass.picard"}[]
:::

:::definition "mf.maass.picard.fourierexpansion" (lean := "HyperbolicThreeSpace.picardFourierTerm, HyperbolicThreeSpace.HasPicardFourierExpansion, Complex.besselK")
*Fourier expansion of a Maass form on PSL(2,Z\[i\]).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.picard.fourierexpansion))

The *Fourier expansion* of a Maass forrm on PSL$`(2,\Z[i])` reads

$$`f(z)=\sum_{n\in\Z[i]}a(n)yK_{ir}(2\pi|n|y)e^{2\pi i\,\textrm{Re}(nx)},`

where $`K_{ir}(x)` is a {bpref "specialfunction.k_bessel"}[$`K`-Bessel function] and the expansion coefficients $`a(n)` are related to Hecke eigenvalues.

Depends on: {uses "specialfunction.k_bessel"}[]
:::

:::definition "mf.maass.spectral_index"
*Spectral index of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.spectral_index))

The {bpref "mf.maass.mwf.eigenvalue"}[eigenvalues] $`\lambda = \frac{1}{4} + R^2` (written in terms of the {bpref "mf.maass.mwf.spectralparameter"}[spectral parameter] $`R`) are discrete, real, and nonnegative. We order them, and the index of a particular eigenvalue $`\lambda` in this order is called the *spectral index*.

The index $`0` is reserved for when the eigenvalue $`\lambda = \frac{1}{4}`, or equivalently for when the spectral parameter $`R = 0`.
For other eigenvalues, we notate the index differently based on whether the eigenvalue is {bpref "mf.maass.exceptional_eigenvalue"}[exceptional] or not.

- For standard eigenvalues, when $`R` is purely imaginary, we order the eigenvalues by the absolute value of the spectral parameter $`R`. The first such eigenvalue with $`R \neq 0` is assigned *spectral index* $`1`, and so on.

- For exceptional eigenvalues, when $`R` is purely real, we again order the eigenvalues by the absolute value of the spectral parameter $`R`. But the index is encoded in base $`26` using the $`26` symbols $`a, b, \ldots, z`. The first such eigenvalue with $`R \neq 0` is assigned the *spectral index* $`b`.

Exceptional eigenvalues are conjectured to not exist. In practice, the latter indexing system is not necessary.

Depends on: {uses "mf.maass.mwf.eigenvalue"}[] {uses "mf.maass.mwf.spectralparameter"}[] {uses "mf.maass.exceptional_eigenvalue"}[]
:::

:::definition "mf.multipliersystem" (lean := "MonoidHom.IsMultiplierSystem, MonoidHom.isMultiplierSystem_of_slash_eq_smul, CongruenceSubgroup.nebentypusMultiplier, CongruenceSubgroup.isMultiplierSystem_nebentypusMultiplier_iff, CongruenceSubgroup.mem_modFormCharSpace_iff_slash_eq_smul")
*Multiplier system.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.multipliersystem))

A *multiplier system* of weight $`k\in\mathbb{Z}` for a group $`G` is a group homomorphism from $`G` to the group $`S^1` of complex numbers of modulus $`1`, with the added condition that, if $`-I\in G`, then $`v(-I)=(-1)^k`.
:::

:::definition "mf.quasi_modular"
*Quasi-modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.quasi_modular))

A *quasi-modular form* of {bpref "cmf.weight"}[weight] $`k` and {bpref "mf.multipliersystem"}[multiplier system] $`v` for a {bpref "group.fuchsian"}[fuchsian group] $`G` is a function $`f` from {bpref "mf.upper_half_plane"}[$`\mathfrak{H}`] to $`\mathbb{C}` which is
holomorphic and satisfies a certain growth condition and, for any $`\gamma=\left(\begin{matrix}a&b\\c&d\end{matrix}\right)\in G` and
$`z\in\mathfrak{H}`, we have:

$$`(f|_k\gamma)(z)=v(\gamma)P\left(z,\frac{c}{cz+d}\right),`

where $`P` is a polynomial in two variables whose coefficients depend only on $`f`
and not on $`\gamma` and $`f|_k\gamma` is the {bpref "mf.slash_action"}[weight $`k` slash-action]. The \*degree\* of $`P` is called the \*depth\* of $`f`.

An example of a quasi-modular form is the Eisenstein series $`E_2(z)=1-24\sum_{n\geq1}\sigma_1(n)q^n`, where $`q=e^{2\pi iz}` and $`\sigma_1` is a {bpref "af.divisor_function"}[divisor function]. It has weight $`2` and depth $`1` on {bpref "group.sl2z"}[$`\Gamma`] and it has the following transformation property:

$$`E_2(\gamma z)=(cz+d)^2E_2(z)-\frac{6i}{\pi}c(cz+d).`

Depends on: {uses "af.divisor_function"}[] {uses "cmf.weight"}[] {uses "group.fuchsian"}[] {uses "group.sl2z"}[] {uses "mf.multipliersystem"}[] {uses "mf.slash_action"}[] {uses "mf.upper_half_plane"}[]
:::

:::definition "mf.siegel"
*Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel))

Let $`g\ge 2` be an integer, let
$`\rho\colon \GL(g,\mathbb{C})\to \GL(V)` be a finite-dimensional complex representation, and let
$`\Gamma \leq \GSp(2g,\Q)` be an arithmetic subgroup.

A holomorphic map $`f` on the
Siegel upper half space $`\mathcal{H}_g`
taking values in $`V` is called a *Siegel modular form* of weight $`\rho` on $`\Gamma` if

$$`f((a\tau+b)(c\tau+d)^{-1})=\rho(c\tau+d)f(\tau)`

for all $`\begin{pmatrix} a&b\\c&d\end{pmatrix}\in \Gamma` (with $`a,b,c,d \in \mathrm{M}(g,\mathbb{Q})`) and all $`\tau\in\mathcal{H}_g`.

The arithmetic subgroups of $`\GSp(2g,\Q)` that we focus on are the following ones:
<ul><li>
{bpref "group.sp2gr"}[integral symplectic group:  $`\Sp(2g,\Z)`]
 </li><li>
Congruence subgroups of $`\Sp(2g,\Z)`
 </li><li>
paramodular group:  $`\Gamma^{\mathrm{para}}(d)\subset \Sp(2g,\Q)`
 </li>
</ul>
Note in the case of {bpref "cmf"}[(classical) modular forms], a
holomorphicity condition at all the cusps of $`\Gamma` is required in the definition.
Due to the so-called {bpref "mf.siegel.koecher.principle"}[Koecher principle] such a condition is superfluous for Siegel modular form of degree $`g>1`.

For each fixed choice of $`\rho` and $`\Gamma`, the set of modular forms of weight $`\rho` on $`\Gamma` is a finite-dimensional complex-vector space denoted by $`M_{\rho}(\Gamma)`.
Moreover if the representation $`\rho` is the direct sum of two representations
$`\rho=\rho_1\oplus \rho_2` then the space $`M_{\rho}(\Gamma)` is isomorphic to
$`M_{\rho_1}(\Gamma)\oplus M_{\rho_2}(\Gamma)` and we can restrict ourselves to
irreducible representations of $`\GL(g,\C)`.

If the {bpref "repn.highest.weight"}[highest weight] of the representation $`\rho`
is $`(k,\ldots,k)` i.e. $`\rho=\det^{\otimes k}` (note that $`V` is one-dimensional in this case) then the previous functional equation takes the form

$$`f((a\tau+b)(c\tau+d)^{-1})=\det(c\tau+d)^kf(\tau)`

and $`f` is called a *scalar-valued Siegel modular form*. The space of such forms is simply denoted by $`M_k(\Gamma)`. When $`\dim(V)>1`, we usually talk about
*vector-valued Siegel modular forms*.

Depends on: {uses "cmf"}[] {uses "group.sp2gr"}[] {uses "repn.highest.weight"}[]
:::

:::definition "mf.siegel.automorphic_type"
*Automorphic type.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.automorphic_type))

The *automorphic type* of a {bpref "mf.siegel.newform"}[Siegel newform] $`f \in S_{k,j}(\Gamma)` of {bpref "mf.siegel.degree"}[degree] 2 is a letter indicating the type of the Arthur parameters of the automorphic representation $`\pi` associated to $`f`.
These fall into six classes of (packets of ) representations:

(F) - Finite type: (in fact, one-dimensional) representations.

(P) - Saito-Kurokawa type: Their $`L`-functions are of the form $`L(s,\mu)L(s+1/2,\sigma)L(s-1/2,\sigma)`, where $`\mu` is a cusp form on $`\GL(2)` and $`\sigma` is a Hecke character. Saito-Kurokawa lifts are of type (P).

(Q) - Soudry type (also known as Klingen packets): Their $`L`-functions are of the form $`L(s+1/2,\mu)L(s-1/2,\mu)`, where $`\mu` is a cusp form on $`\GL(2)`.

(B) - Howe-Piatetski-Shapiro type (also known as Borel packets): Their $`L`-functions are of the form $`L(s+1/2,\sigma_1)L(s-1/2,\sigma_1)L(s+1/2,\sigma_2)L(s-1/2,\sigma_2)`, where $`\sigma_1,\sigma_2` are Hecke characters.

(Y) - Yoshida type: These are functorial (endoscopic) lifts of pairs of automorphic representations $`\mu_1,\mu_2` of $`\GL(2)`. Their $`L`-functions are of the form $`L(s,\mu_1)L(s,\mu_2)`.

(G) - General type: (which contains the remaining representations) These are characterized by admitting a functorial transfer to a cuspidal automorphic representation of $`\GL_4`.Their $`L`-functions are primitive.

Depends on: {uses "mf.siegel.degree"}[] {uses "mf.siegel.newform"}[]
:::

:::definition "mf.siegel.character" (lean := "SiegelUpperHalfSpace.modularForms, SiegelUpperHalfSpace.mem_modularForms_iff_slash, SiegelUpperHalfSpace.slash, SiegelUpperHalfSpace.IsHolomorphic, SiegelUpperHalfSpace")
*Siegel modular form with character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.character))

Let $`g\ge 2` be an integer, let
$`\rho\colon \GL(g,\mathbb{C})\to \GL(V)` be a finite-dimensional complex representation, $`\Gamma \leq \GSp(2g,\Q)` be an arithmetic subgroup and $`\psi` a character of $`\Gamma`.

A holomorphic map $`f` on the
Siegel upper half space $`\mathcal{H}_g`
taking values in $`V` is called a *Siegel modular form with character $`\psi`* and
weight $`\rho` on $`\Gamma` if

$$`f((a\tau+b)(c\tau+d)^{-1})=\psi(\gamma)\rho(c\tau+d)f(\tau)`

for all $`\gamma=\begin{pmatrix} a&b\\c&d\end{pmatrix}\in \Gamma` (with $`a,b,c,d \in \mathrm{M}(g,\mathbb{Q})`) and all $`\tau\in\mathcal{H}_g`.

The space of Siegel modular forms with character $`\psi` and weight $`\rho` on $`\Gamma`
is denoted by $`M_{\rho}(\Gamma,\psi)` and its subspace of
cusp forms  by $`S_{\rho}(\Gamma,\psi)`.
:::

:::definition "mf.siegel.coefficient_field"
*Coefficient field for Siegel newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.coefficient_field))

The *coefficient field* of a Siegel modular form is the subfield of $`\C` generated by the coefficients $`a_n` of its $`q`-expansion $`\sum a_nq^n`.  The space of cusp forms $`S_{k,j}^\mathrm{new}(\Gamma_F(N),\chi)` has a basis of modular forms that are simultaneous eigenforms for all {bpref "mf.siegel.hecke_operator"}[Hecke operators] and with algebraic Fourier coefficients.  For such eigenforms the coefficient field will be a number field, and Galois conjugate eigenforms will share the same coefficient field.  Moreover, if $`m` is the smallest positive integer such that the values of the character $`\chi` are contained in the cyclotomic field $`\Q(\zeta_m)`, the coefficient field will contain $`\Q(\zeta_m)`
For eigenforms, the coefficient field is also known as the *Hecke field*.

Depends on: {uses "mf.siegel.hecke_operator"}[]
:::

:::definition "mf.siegel.coefficient_ring"
*Coefficient ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.coefficient_ring))

The *coefficient ring* of a Siegel modular form is the subring $`\Z[{a_n}]` of $`\C` generated by the coefficients $`a_n` of its $`q`-expansion $`\sum a_nq^n`.  In the case of a {bpref "mf.siegel.newform"}[newform] the coefficients $`a_n` are algebraic integers and the coefficient ring is a finite index subring of the ring of integers of the {bpref "mf.siegel.coefficient_field"}[coefficient field] of the newform.
It is also known as the *Hecke ring*, since the $`a_n` generate the same ring as the eigenvalues of the Hecke operators.

Depends on: {uses "mf.siegel.coefficient_field"}[] {uses "mf.siegel.newform"}[]
:::

:::definition "mf.siegel.cusp_form_degree2" (lean := "SiegelUpperHalfSpace.cuspFormsKJ, SiegelUpperHalfSpace.IsCuspForm, SiegelUpperHalfSpace.SiegelOperatorVanishes, SiegelUpperHalfSpace.rhoKJ, SiegelUpperHalfSpace.slash")
*Siegel cusp form of degree 2.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.cusp_form_degree2))

Let $`f` be a vector-valued Siegel modular form on
an arithmetic subsgroup $`\Gamma` of $`\GSp(4,\Q)` then $`f` is called a *cusp form* if for any $`\gamma\in \Sp(4,\Q)`, we have

$$`\Phi(f\vert_{k,j}\gamma)=0`

where $`\Phi` denotes the Siegel operator while $`\vert_{k,j}` denotes the slash operator.
:::

:::definition "mf.siegel.defining_polynomial"
*Defining polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.defining_polynomial))

The {bpref "mf.siegel.coefficient_field"}[coefficient field of a Siegel modular form] is a {bpref "nf"}[number field]. A *defining polynomial* for this number field is explicitly recorded, because some of the data associated to the modular form will be expressed in terms of roots of this polynomial.

Depends on: {uses "mf.siegel.coefficient_field"}[] {uses "nf"}[]
:::

:::definition "mf.siegel.degree"
*Degree of a Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.degree))

A {bpref "mf.siegel"}[Siegel modular form] on an arithmetic subgroup of
$`\Sp(2g,\Q)` is said to be of *degree* $`g`.

Depends on: {uses "mf.siegel"}[]
:::

:::definition "mf.siegel.dimension"
*Dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.dimension))

The *dimension* of a space of Siegel modular forms is its dimension as a complex vector space; for spaces of newforms $`S_{k,j}^{\rm new}(K(N),\chi)` this is the same as the dimension of the $`\Q`-vector space spanned by its eigenforms.

The *dimension* of a {bpref "mf.siegel.newform"}[newform] refers to the dimension of its newform subspace, equivalently, the cardinality of its newform orbit.  This is equal to the degree of its coefficient field (as an extension of $`\Q`).

The *relative dimension* of $`S_{k,j}^{\rm new}(K(N),\chi)`  is its dimension as a $`\Q(\chi)`-vector space, where $`\Q(\chi)` is the field generated by the values of $`\chi`, and similarly for newform subspaces.

Depends on: {uses "mf.siegel.newform"}[]
:::

:::definition "mf.siegel.family" (lean := "SymplecticGroup.Gamma, SymplecticGroup.Gamma0, SymplecticGroup.paramodular, SymplecticGroup.paramodularGL, SymplecticGroup.paramodularDelta_mul_mul_mem")
*Family of Siegel groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family))

Siegel modular forms of degree $`g` transform under the action of a discrete subgroup $`\Gamma` of $`\Sp(2g,\Q)`.  We focus on certain discrete subgroups.

- *Principal congruence subgroup*: $`\Gamma(N)`.

- *Siegel parabolic subgroup*: $`\Gamma_0(N)`.

- *Paramodular subgroup*: $`\Gamma^{\mathrm{para}}(d)`.
:::

:::definition "mf.siegel.hecke_operator"
*Hecke operators.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.hecke_operator))

For a positive integer $`g`, let
$`\GSp(2g,\Q)^+=\{\gamma\in\GL(2g,\Q)\, \mid \, \exists\, r(g)\in\Q_{>0}: \gamma^t J\gamma=r(g)J\}`.

Define the semigroup $`S=\GSp(2g,\Q)^+\cap M(2g,\Z)`. For a discrete subgroup $`\Gamma` of $`\Sp(2g,\Q)`, let $`L(\Gamma,S)` be the free $`\C`-module generated by the right cosets $`\Gamma\alpha`, where $`\alpha\in S`. Note that $`\Gamma` acts on $`L(\Gamma,S)` by right multiplication. The $`\C`-algebra $`\mathcal{H}(\Gamma)=L(\Gamma,S)^\Gamma`, called the *Hecke algebra* of $`\Gamma`, has the following multiplication:

If $`T,T'\in\mathcal{H}(\Gamma)` with $`T=\sum_i c_i\Gamma\alpha_i` and $`T'=\sum_j c_j'\Gamma\alpha'_j`, then $`TT'=\sum_{i,j} c_ic_j'\Gamma\alpha_i\alpha_j'`.

For a prime $`p`, let $`S_p` be the subsemigroup of $`S` consisting of elements $`g` for which $`r(g)` is a power of $`p`. Analogously define $`\mathcal{H}_p(\Gamma)=L(\Gamma,S_p)^\Gamma`, the *local Hecke algebra* at $`p`.
If $`\Gamma=\Sp(2g,\Z)`, then it is known that $`\mathcal{H}(\Gamma)\cong\bigotimes_p\mathcal{H}(\Gamma,S_p)`.

We define the following elements of $`\mathcal{H}_p(\Gamma)`. Let $`1_j` be the identity  matrix of size $`j`. We set

- $`T(p)=\Gamma\,\mathrm{diag}(1_g,p1_g)\Gamma`

- $`T_i(p^2)=\Gamma\,\mathrm{diag}(1_i,p1_{g-i},p^21_i,p1_{g-i})\Gamma`

 for $`0\leqslant i\leqslant g`

where we identify a double coset with the sum of its single cosets in the Hecke algebra. Also, let $`T(p^2)=\sum_{i=0}^gT_i(p^2)`.

Suppose that $`\Gamma` contains $`B(N)`, the Borel congruence subgroup of level $`N`. Then it is known that $`\mathcal{H}_p(\Gamma)` is generated by $`T(p)` and by $`T_i(p^2)` for $`1\leqslant i\leqslant g-1`.

If $`g=2`, then $`\mathcal{H}_p(\Gamma)` is generated by $`T(p)` and $`T_1(p)`, or alternatively by $`T(p)` and $`T(p^2)`.

The Hecke algebra $`\mathcal{H}(\Gamma)` acts on the space $`M_{\rho}(\Gamma)` of {bpref "mf.siegel"}[Siegel modular forms] by

$$`F\vert_{\rho}(\sum c_i\Gamma\alpha_i)=\sum_ic_iF\vert_{\rho}\alpha_i.`

Note that the slash operator can be normalized in various ways. A common normalization is

$$`(F\vert_{\rho}\alpha)(\tau)=r(\alpha)^{\lambda_1+\ldots+\lambda_g-\frac{g(g+1)}{2}}\rho(c\tau+d)^{-1}F(\alpha\cdot\tau)`

for $`\alpha=\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \GSp(2g,\Q)^+` and $`\rho` irreducible finite-dimensional representations of $`\GL(g,\C)` of {bpref "repn.highest.weight"}[highest weight]
$`\lambda_1\geqslant \lambda_2\geqslant\ldots\geqslant \lambda_g`.

For scalar-valued forms $`F\in M_k(\Gamma)`, i.e., $`\rho=\det^{\otimes}`, we get

$$`(F\vert_{k}\alpha)(\tau)=r(\alpha)^{gk-\frac{g(g+1)}{2}}\det(c\tau+d)^{-k}F(\alpha\cdot\tau)`

for $`\alpha=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in \GSp(2g,\Q)^+`.

  The subspace $`S_{\rho}(\Gamma)` of cusp forms is preserved under this action.

A *Hecke eigenform* is a form in $`M_{\rho}(\Gamma)` which is a simultaneous eigenform for all the Hecke operators.

Depends on: {uses "mf.siegel"}[] {uses "repn.highest.weight"}[]
:::

:::definition "mf.siegel.koecher.principle"
*Koecher principle.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.koecher.principle))

Let $`f(\tau)=\sum_{n\in L_{\Gamma}^{\vee}} a(n) e^{2 \pi i \text{tr}(n\tau)}` be the q-expansion of $`f\in M_{\rho}(\Gamma)`.
The *Koecher principle* says that, for {bpref "mf.siegel.degree"}[degree] $`g\geqslant 2`, if $`a(n)\neq 0` then
$`n` is positive semidefinite.

Depends on: {uses "mf.siegel.degree"}[]
:::

:::definition "mf.siegel.label"
*Label of a Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.label))

The *label* of a {bpref "mf.siegel.newform"}[newform] $`f\in S_{\underline{k}}^{\rm new}(\Gamma_F(N),\chi)` has the format $`g.F.N.k1...kd.a.x`, where

- $`g` is the {bpref "mf.siegel.degree"}[degree];

- $`F` is the {bpref "mf.siegel.family"}[family];

- $`N` is the {bpref "mf.siegel.level"}[level];

- $`\underline{k}=(k_1,\dots,k_d)` is the {bpref "mf.siegel.weight"}[weight];

- $`N.a` is the {bpref "character.dirichlet.galois_orbit_label"}[label] of the {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi`;

- $`x` is the label of the Galois orbit of the newform $`f`.

For each embedding of the {bpref "mf.siegel.coefficient_field"}[coefficient field] of $`f` into the complex numbers, the corresponding modular form over $`\C` has a label of the form $`g.F.N.k1...kd.a.x.n.i`, where

- $`n` determines the Conrey label $`N.n` of the Dirichlet character $`\chi`;

- $`i` is an integer ranging from 1 to the relative dimension of the newform that distinguishes embeddings with the same character $`\chi`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_label"}[] {uses "mf.siegel.coefficient_field"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.family"}[] {uses "mf.siegel.level"}[] {uses "mf.siegel.newform"}[] {uses "mf.siegel.weight"}[]
:::

:::definition "mf.siegel.level"
*Level of a Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.level))

A {bpref "mf.siegel"}[Siegel modular form] on a discrete subgroup $`\Gamma` of $`\Sp(2g,\Q)`  is said to be of *level* $`N` if $`\Gamma` is a
congruence subgroup of level $`N`.

A Siegel modular form on a discrete subgroup $`\Gamma` of $`\Sp(2g,\Q)` is said to be of *level* $`N` if $`\Gamma` is a congruence subgroup of level $`N`.

Families of congruence subgroups are typically indexed by the
minimal level $`N` of the subgroup. For example, in degree $`2`, we have the paramodular groups
$`K(N)`,
the congruence subgroups
$`\Gamma_0(N)`,
and the principal congruence subgroups
$`\Gamma(N)`.

Depends on: {uses "mf.siegel"}[]
:::

:::definition "mf.siegel.newform"
*Siegel newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.newform))

Let $`M_{\rho}(K(N))` be the space of {bpref "mf.siegel"}[Siegel modular forms] of {bpref "mf.siegel.weight"}[weight] $`\rho` and paramodular level $`N`.

If $`M` is a proper divisor of $`N`, then for every divisor $`D \mid (N/M)`, there are maps from $`M_{\rho}(K(M))` to $`M_{\rho}(K(N))`.  Such modular forms are said to be *old*, and together they span a subspace $`M_{\rho}^{\rm old}(K(N)) \subseteq M_{\rho}(K(N))`.

The orthogonal complement of the $`S_{\rho}^{\rm old}(K(N))` in $`S_{\rho}(K(N))` with respect to the Petersson scalar product is denoted $`S_{\rho}^{\rm new}(K(N))`, and we have the decomposition

$$`S_{\rho}(K(N))=S_{\rho}^{\rm old}(K(N))\oplus S_{\rho}^{\rm new}(K(N)).`

into the *old subspace* and *new subspace*.

A *newform* is a cusp form $`f\in S_{\rho}^{\rm new}(K(N))` that is also an eigenform of all {bpref "mf.siegel.hecke_operator"}[Hecke operators], normalized so that the $`q`-expansion  $`f(\tau)=\sum a_{T} q^T`, where $`q=e^{2\pi i {\rm tr}(T \tau) }`, begins with the coefficient $`a_1=1`.  The newforms are a basis for the vector space $`S_{\rho}^{\rm new}(K(N))`.

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.hecke_operator"}[] {uses "mf.siegel.weight"}[]
:::

:::definition "mf.siegel.newspace"
*Space of paramodular newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.newspace))

For each {bpref "mf.siegel.level"}[level] $`N`, {bpref "mf.siegel.weight_k_j"}[weight] $`k`, and {bpref "mf.siegel.character"}[character] $`\chi` the space $`S_{k,j}(K(N),\chi)` of cuspidal modular forms can be decomposed as an internal direct sum

$$`S_{k,j}(K(N),\chi) = S_{k,j}^{\rm old}(K(N),\chi) \oplus S_{k,j}^{\rm new}(K(N),\chi).`

The *old subspace* $`S_{k,j}^{\rm old}(K(N),\chi)` is generated by all elements of
$`S_{k,j}(K(N),\chi)` which are in the image of the level-raising operators $`\eta, \theta, \theta'`.

The *new subspace* $`S_{k,j}^{\rm new}(K(N),\chi)` is the orthogonal complement of $`S_{k,j}^{\rm old}(K(N),\chi)` with respect to the Petersson inner product on $`S_{k,j}(K(N),\chi)`.  The {bpref "mf.siegel.newform"}[newforms] in $`S_{k,j}(K(N),\chi)` are a canonical basis for this subspace.

Depends on: {uses "mf.siegel.character"}[] {uses "mf.siegel.level"}[] {uses "mf.siegel.newform"}[] {uses "mf.siegel.weight_k_j"}[]
:::

:::definition "mf.siegel.phi"
*Siegel $`\Phi` operator.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.phi))

The *Siegel $`\Phi` operator* is a linear map that sends {bpref "mf.siegel.degree"}[degree] $`g` Siegel modular forms to degree $`g-1` ones; it is defined by

$$`\Phi(f)(\tau) = \lim_{t\to +\infty}
f\begin{pmatrix}\tau&0\\0&it\end{pmatrix} \quad \text{for any } \tau \in \mathfrak{H}_{g-1}.`

Depends on: {uses "mf.siegel.degree"}[]
:::

:::definition "mf.siegel.slash.op"
*Siegel slash operator.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.slash.op))

For a positive integer $`g`, let
$`\GSp(2g,\Q)^+=\{\gamma\in\GL(2g,\Q)\, \mid \, \exists\, r(g)\in\Q_{>0}: \gamma^t J\gamma=r(g)J\}` and $`f \colon \mathcal{H}_g \to V`, the *slash operator* (of weight $`\rho`) is defined by

$$`(f\vert_{\rho}\alpha)(\tau)=r(\alpha)^{\lambda_1+\ldots+\lambda_g-\frac{g(g+1)}{2}}\rho(c\tau+d)^{-1}f((a\tau+b)(c\tau+d)^{-1})`

for $`\alpha=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\GSp(2g,\Q)^+` and
$`\rho\colon \GL(g,\C) \to \GL(V)` an irreducible finite-dimensional
representations of $`\GL(g,\C)` of {bpref "repn.highest.weight"}[highest weight]
$`\lambda_1\geqslant \lambda_2\geqslant\ldots\geqslant \lambda_g`.

Depends on: {uses "repn.highest.weight"}[]
:::

:::definition "mf.siegel.weight"
*Weight of a Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.weight))

The *weight* of a {bpref "mf.siegel"}[Siegel modular form] $`f` of {bpref "mf.siegel.degree"}[degree] $`g` is the
finite-dimensional complex representation $`\rho` of $`\GL(g,\mathbb{C})`
that occurs in the modular transformation property of $`f` under the action of $`\gamma = \left( \begin{array}{ll}  a & b \\ c & d \end{array}\right)` on the Siegel upper half space $`\mathcal{H}_g`.  That is, the weight is the representation $`\rho`
in the transformation law

$$`f\left( (a \tau + b)(c \tau + d)^{-1} \right) = \rho(c \tau + d) f(\tau) .`

Irreducible representations of $`\GL(g,\mathbb{C})` are indexed by their highest weight.

In degree $`2`, to a pair of non-negative integers $`(k,j)`, one associates the irreducible representation
$`\rm det^{k}(\rm St) \otimes {\rm Sym}^j(\rm St),`
where $`\rm St` denotes the standard $`2`-dimensional representation of $`\rm \GL(2,\C)`.
The pair $`(k,j)` is called its weight, and when $`j = 0`, the integer $`k` is called the weight. Note that the highest weight of this representation is $`(j+k,k)`.

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[]
:::

:::definition "mf.siegel.weight_k_j"
*Weight.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.weight_k_j))

The *weight* of a {bpref "mf.siegel"}[Siegel modular form] $`f` of {bpref "mf.siegel.degree"}[degree] 2 is the pair of non-negative integers
that occurs in the modular transformation property of $`f` under the action of $`\gamma = \left( \begin{array}{ll}  a & b \\ c & d \end{array}\right)` on the Siegel upper half space $`\mathcal{H}_2`.  That is, the weight is the numbers $`(k,j)` in the transformation law

$$`f\left( (a \tau + b)(c \tau + d)^{-1} \right) = \det(c \tau + d)^k {\rm Sym}^j(c \tau + d) f(\tau) .`

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[]
:::

:::definition "mf.slash_action" (lean := "SlashAction, ModularForm.slash_def")
*Weight $`k` slash-action.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.slash_action))

Let $`f` be a function from {bpref "mf.upper_half_plane"}[$`\mathcal{H}`] to $`\mathbb{C}`. We define the *weight $`k` slash-action*  $`f|_k\gamma` to be the action of $`\gamma=\left(\begin{matrix}a&b\\c&d\end{matrix}\right)\in\textrm{SL}_2(\mathbb{R})` given by

$$`f|_k\gamma(z)=\det(\gamma)^{k/2}(cz+d)^{-k}f(\gamma z).`

Note that, if $`f` is a {bpref "mf"}[modular form] with {bpref "mf.multipliersystem"}[multiplier system] $`v`, the modularity condition is equivalent to

$$`f|_k\gamma(z)=v(\gamma)f(z).`

Depends on: {uses "mf"}[] {uses "mf.multipliersystem"}[] {uses "mf.upper_half_plane"}[]
:::
