import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Bianchi" =>
%%%
tag := "bianchi-modular-forms"
file := "Bianchi-modular-forms"
%%%

This section lists the LMFDB definitions in the subcategory `mf.bianchi`. Each definition links back to its LMFDB knowl.

:::definition "mf.bianchi" (lean := "HyperbolicThreeSpace.IsBianchiModularForm, HyperbolicThreeSpace.bianchiSlash, HyperbolicThreeSpace.IsBianchiHarmonic, HyperbolicThreeSpace.casimirOne, HyperbolicThreeSpace.IsBianchiCuspidal")
*Bianchi modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi))

Let $`K` be an imaginary quadratic {bpref "nf"}[number field] of {bpref "nf.class_number"}[class number] $`1`, and $`\mathcal{O}_K` be its {bpref "nf.ring_of_integers"}[ring of integers]. Let $`\Gamma` be a {bpref "mf.bianchi.bianchicongruencesubgroup"}[congruence subgroup] of the
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

:::definition "mf.bianchi.bianchicongruencesubgroup" (lean := "Ideal.gammaPSL, Ideal.mk_mem_gammaPSL_iff, Subgroup.IsPSLCongruenceSubgroup, Ideal.gammaSL, Ideal.gammaPSL_normal, Subgroup.IsPSLCongruenceSubgroup.finiteIndex")
*Congruence subgroup of a Bianchi group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.bianchicongruencesubgroup))

Let $`K` be an imaginary quadratic field with {bpref "nf.ring_of_integers"}[ring of integers] $`\mathcal{O}_K`.  For a nonzero ideal $`\mathfrak{N}` of $`\mathcal{O}_K`, the <b>principal congruence subgroup of level $`\mathfrak{N}`</b> is

$$`\Gamma(\mathfrak{N}) = \{\gamma \in \textrm{PSL}_2(\mathcal{O}_K) : \gamma\equiv \pm 1 \!\! \pmod{\mathfrak{N}} \}.`
  A subgroup of $`\textrm{PSL}_2(\mathcal{O}_K)` is called a <b>congruence subgroup</b> if it contains a principal congruence subgroup.

Depends on: {uses "nf.ring_of_integers"}[]
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

:::definition "mf.bianchi.fourierbessell" (lean := "HyperbolicThreeSpace.HasBianchiFourierBesselExpansion, HyperbolicThreeSpace.bianchiFourierBesselTerm, HyperbolicThreeSpace.bianchiBesselVector, Complex.besselK")
*Fourier-Bessel expansion.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.fourierbessell))

Let $`F` be a  {bpref "mf.bianchi"}[Bianchi modular form] of {bpref "mf.bianchi.weight"}[weight] $`2` with respect to the {bpref "mf.bianchi.bianchicongruencesubgroup"}[congruence subgroup] $`\Gamma` of a {bpref "mf.bianchi.bianchigroup"}[Bianchi group]. As a function on {bpref "mf.bianchi.hyperbolic3space"}[hyperbolic 3-space] $`\mathcal{H}_3 = \{ (x,y) \in \C \times \R \mid y>0 \}`,  $`F` is a periodic function in the variable $`x\in\C`, and  has a *Fourier-Bessel expansion* of the form

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

:::definition "mf.bianchi.hecke_algebra" (lean := "HyperbolicThreeSpace.bianchiHeckeAlgebra, HyperbolicThreeSpace.bianchiHeckeTPrime, HyperbolicThreeSpace.bianchiHeckeOperatorModularForms, HyperbolicThreeSpace.isBianchiModularForm_bianchiHeckeOperator, HyperbolicThreeSpace.bianchiHeckeOperator")
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

:::definition "mf.bianchi.labels"
*Labels of Bianchi modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.labels))

The label of a Bianchi newform has the form _field_-\_level\_-\_suffix\_.
Here _field_ is the base number field $`K`, and is denoted by its {bpref "nf.label"}[standard label]; _level_ is an integral ideal of $`K`, denoted by its {bpref "nf.ideal_labels"}[standard label]; and  _suffix_ is a sequence of one or more letters representing the index of the form in a sorted list of newforms of the same level.  Forms at the same level are sorted first by dimension, then by lexicographical order of the Fourier coefficients, which are themselves sorted according to the standard ordering of integral ideals.

For example, the Bianchi newform with label _2.0.4.1-61650.6-a_ has base field $`\mathbb{Q}(\sqrt{-1})` (with label 2.0.4.1), level $`(219-117i)` (with norm 61650 and label 61650.6) and suffix $`a` (being the first of three newforms of dimension $`1` at that level).

Depends on: {uses "nf.ideal_labels"}[] {uses "nf.label"}[]
:::

:::definition "mf.bianchi.level" (lean := "Ideal.gamma0GL, Ideal.gamma0SL, Ideal.mem_gamma0SL, Ideal.absNorm")
*Level of a Bianchi modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.bianchi.level))

The <b>level</b> of a {bpref "mf.bianchi"}[Bianchi modular form] $`F` is the discrete subgroup $`\Gamma` of $`\PSL(2,\C)` such that $`F|_k\gamma = F` for every $`\gamma \in \Gamma`, where $`k` is the {bpref "mf.bianchi.weight"}[weight] of $`F`.

More precisely, let $`K` be an imaginary quadratic field; we suppose that $`K` has class number $`1` for simplicity.  For a Bianchi modular form over $`K`, the level $`\Gamma` is a {bpref "mf.bianchi.bianchicongruencesubgroup"}[congruence subgroup] of the {bpref "mf.bianchi.bianchigroup"}[Bianchi group] $`\GL_2(\mathcal{O}_K)`.  The most common levels are those of the form

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

:::definition "mf.bianchi.weight" (lean := "HyperbolicThreeSpace.IsBianchiModularForm, HyperbolicThreeSpace.bianchiSlash")
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
