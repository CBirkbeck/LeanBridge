import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Maass" =>
%%%
tag := "maass-forms"
file := "Maass-forms"
%%%

This section lists the LMFDB definitions in the subcategory `mf.maass`. Each definition links back to its LMFDB knowl. `specialfunction.k_bessel` also belongs here, although its id puts it in another LMFDB category.

:::definition "mf.maass"
*Maass forms on GL(n).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass))

The term *Maass form* is used for automorphic forms on $`GL_{n}` (for some positive integer n), which are not holomorphic.
Instead of satisfying the  Cauchy-Riemann equations (as holomorphic functions do), these functions are eigenfunctions of the Casimir element in the universal enveloping algebra of the Lie algebra of $`GL_{n}`.
:::

:::definition "mf.maass.exceptional_eigenvalue" (lean := "UpperHalfPlane.IsExceptionalMaassEigenvalue, UpperHalfPlane.isExceptionalMaassEigenvalue_iff, UpperHalfPlane.SelbergEigenvalueConjecture")
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

- $`N.a` is the {bpref "character.dirichlet.conrey"}[Conrey label] of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi`;

- $`m` is the {bpref "mf.maass.spectral_index"}[spectral index], which uniquely identifies the {bpref "mf.maass.mwf.eigenvalue"}[eigenvalue] $`\lambda` of $`f`;

- $`d` indicates which form among those of level $`N`, Dirichlet character $`N.a`, and eigenvalue $`\lambda` this is.

The shorter form is used when $`k=0` and $`a=1` and $`d=1`.

For squarefree level, it is conjectured that there is only one Maass form per eigenvalue $`\lambda`, hence $`d` is (currently) always $`1`. Generally, there are only finitely many Maass newforms in $`M_k(\Gamma_0(N), \chi)` with the same eigenvalue $`\lambda`. Then $`d` denotes the index among these finitely many forms, where the ordering is lexicographical in the sequence $`\{ \bigl(\mathrm{Re}(a(n)), \mathrm{Im}(a(n))\bigr) \}_{n \geq 1}`.

Depends on: {uses "character.dirichlet"}[] {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.eigenvalue"}[] {uses "mf.maass.mwf.level"}[] {uses "mf.maass.mwf.weight"}[] {uses "mf.maass.spectral_index"}[]
:::

:::definition "mf.maass.mwf" (lean := "UpperHalfPlane.IsMaassForm, UpperHalfPlane.IsMaassFormOfWeight, UpperHalfPlane.maassSlash, UpperHalfPlane.maassLaplacian, UpperHalfPlane.isMaassFormOfWeight_zero_iff")
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

:::definition "mf.maass.mwf.eigenvalue" (lean := "UpperHalfPlane.IsMaassForm, UpperHalfPlane.maassEigenvalue, UpperHalfPlane.IsMaassForm.eigenvalue_eq, UpperHalfPlane.hyperbolicLaplacian")
*The eigenvalue of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.eigenvalue))

The *eigenvalue* $`\lambda` of a {bpref "mf.maass.mwf"}[Maass newform] on GL(2) refers to the eigenvalue of the eigenspace of the {bpref "mf.maass.mwf.laplacian"}[Laplace-Baltrami operator] in which it lies.

This eigenvalue is a real number that is typically written in the form $`\lambda=\frac{1}{4}+R^2`, where $`R` is the {bpref "mf.maass.mwf.spectralparameter"}[spectral parameter].

Depends on: {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.laplacian"}[] {uses "mf.maass.mwf.spectralparameter"}[]
:::

:::definition "mf.maass.mwf.fourierexpansion" (lean := "UpperHalfPlane.HasMaassFourierExpansion, UpperHalfPlane.HasMaassCosineExpansion, UpperHalfPlane.HasMaassSineExpansion, UpperHalfPlane.maassHeckeOperator, UpperHalfPlane.IsMaassHeckeEigenform.coeff_prime_eq")
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

:::definition "mf.maass.mwf.laplacian" (lean := "UpperHalfPlane.hyperbolicLaplacian")
*Laplace-Beltrami operator (hyperbolic).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.laplacian))

The *Laplace-Beltrami operator* on the {bpref "mf.upper_half_plane"}[hyperbolic upper half-plane] is given by

$$`\Delta = -y^{2} \left(\frac{\partial^{2}}{\partial x^{2}}+\frac{\partial^{2}}{\partial y^{2}}\right).`

Note that it is sometimes defined without the minus sign in front.

Depends on: {uses "mf.upper_half_plane"}[]
:::

:::definition "mf.maass.mwf.level" (lean := "UpperHalfPlane.IsMaassFormOfLevel")
*The level of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.level))

A {bpref "mf.maass.mwf"}[Maass form] $`f` is said to have *level* $`N` if $`f` is invariant under the principal congruence subgroup {bpref "group.sl2z.subgroup.gamman"}[$`\Gamma(N)`].

Depends on: {uses "mf.maass.mwf"}[]
:::

:::definition "mf.maass.mwf.spectralparameter" (lean := "UpperHalfPlane.HasMaassSpectralParameter, UpperHalfPlane.HasMaassSpectralParameter.eq_or_eq_neg")
*The spectral parameter of a Maass waveform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.spectralparameter))

If $`f` is a {bpref "mf.maass.mwf"}[Maass form] with {bpref "mf.maass.mwf.laplacian"}[Laplace] eigenvalue $`\lambda = \frac{1}{4}+R^{2}`, the number $`R` is said to be the *spectral parameter* of $`f`.

Depends on: {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.laplacian"}[]
:::

:::definition "mf.maass.mwf.symmetry" (lean := "UpperHalfPlane.maassReflection, UpperHalfPlane.coe_maassReflection_smul, UpperHalfPlane.IsEvenMaassForm, UpperHalfPlane.IsOddMaassForm")
*The symmetry of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.symmetry))

The {bpref "group.sl2z"}[modular group] and its congruence subgroups has an outer automorphism of order two, which is given by the reflection in the imaginary axis: $`z=x+iy \mapsto -\bar{z}=-x+iy`.
This map belongs to $`\mathrm{PGL}(2,\mathbb{Z})` and can be represented by the matrix
$`\begin{pmatrix} -1 & 0 \\ 0 & 1 \end{pmatrix}`.

A {bpref "mf.maass.mwf"}[Maass form] $`f` is said to be *even* if $`f(-\bar{z})=f(z)` and *odd* if $`f(-\bar{z})=-f(z)`.

Depends on: {uses "group.sl2z"}[] {uses "mf.maass.mwf"}[]
:::

:::definition "mf.maass.mwf.weight" (lean := "UpperHalfPlane.maassLaplacian, UpperHalfPlane.IsMaassFormOfWeight")
*The weight of a Maass form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.mwf.weight))

A {bpref "mf.maass.mwf"}[Maass form] is of *weight* $`k` if it is an eigenfunction of the weight $`k` {bpref "mf.maass.mwf.laplacian"}[Laplacian]
$`\Delta_k = y^2\left( \frac{\partial^2}{\partial x^2}+\frac{\partial^2}{\partial y^2}\right) - iky\frac{\partial}{\partial x}`.

Depends on: {uses "mf.maass.mwf"}[] {uses "mf.maass.mwf.laplacian"}[]
:::

:::definition "mf.maass.mwf.weight0" (lean := "UpperHalfPlane.IsMaassForm, UpperHalfPlane.hyperbolicLaplacian")
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

Each {bpref "mf.maass.picard"}[Maass form] is associated to an *eigenvalue* via the eigenvalue equation $`(\Delta+\lambda)f(z)=0` where $`\Delta` is the {bpref "mf.maass.picard.laplacian"}[Laplacian].  It is convenient to introduce the *spectral parameter* $`r` which is also called the eigenvalue.  Only if one speaks about the *true eigenvalue* one refers to $`\lambda`, since by convention *eigenvalue* refers to $`r`.  In {bpref "mf.bianchi.hyperbolic3space"}[hyperbolic 3-space], the eigenvalue is connected to the true eigenvalue via $`\lambda=r^2+1`.

Depends on: {uses "mf.bianchi.hyperbolic3space"}[] {uses "mf.maass.picard"}[]
:::

:::definition "mf.maass.picard.fourierexpansion" (lean := "HyperbolicThreeSpace.picardFourierTerm, HyperbolicThreeSpace.HasPicardFourierExpansion, Complex.besselK")
*Fourier expansion of a Maass form on PSL(2,Z\[i\]).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.picard.fourierexpansion))

The *Fourier expansion* of a Maass forrm on PSL$`(2,\Z[i])` reads

$$`f(z)=\sum_{n\in\Z[i]}a(n)yK_{ir}(2\pi|n|y)e^{2\pi i\,\textrm{Re}(nx)},`

where $`K_{ir}(x)` is a {bpref "specialfunction.k_bessel"}[$`K`-Bessel function] and the expansion coefficients $`a(n)` are related to Hecke eigenvalues.

Depends on: {uses "specialfunction.k_bessel"}[]
:::

:::definition "mf.maass.picard.laplacian" (lean := "HyperbolicThreeSpace.laplacian")
*Laplacian in 3d hyperbolic upper half-space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.maass.picard.laplacian))

$`\Delta=y^2(\frac{d^2}{d\Re(x)^2}+\frac{d^2}{d\Im(x)^2}+\frac{d^2}{dy^2})-y\frac{d}{dy}`.
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

:::definition "specialfunction.k_bessel" (lean := "Complex.besselK, Complex.besselKIntegrand, Complex.integrableOn_besselKIntegrand, Complex.besselK_neg, Complex.conj_besselK_I_mul")
*$`K`-Bessel functions.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/specialfunction.k_bessel))

For $`x\in\mathbb{R}_{>0}` and $`\nu\in\mathbb{C}` we define the *$`K`-Bessel functions*

$$`K_{\nu}(x)=\frac{1}{2}\int_0^\infty t^{\nu-1}e^{-(x/2)(t+1/t)}dt.`
:::
