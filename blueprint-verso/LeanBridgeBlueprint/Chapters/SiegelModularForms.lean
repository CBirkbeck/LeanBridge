import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Siegel" =>
%%%
tag := "siegel-modular-forms"
file := "Siegel-modular-forms"
%%%

This section lists the LMFDB definitions in the subcategory `mf.siegel`. Each definition links back to its LMFDB knowl. `paramodulargroup.sp2gr`, `repn.highest.weight` and `repn.irrep.gl` also belong here, although their ids put them in another LMFDB category.

:::definition "mf.siegel" (lean := "SiegelUpperHalfSpace.modularForms, SiegelUpperHalfSpace.scalarModularForms, SiegelUpperHalfSpace.mem_scalarModularForms_iff, SymplecticGroup.IsArithmetic, SiegelUpperHalfSpace.IsHolomorphic")
*Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel))

Let $`g\ge 2` be an integer, let
$`\rho\colon \GL(g,\mathbb{C})\to \GL(V)` be a finite-dimensional complex representation, and let
$`\Gamma \leq \GSp(2g,\Q)` be an arithmetic subgroup.

A holomorphic map $`f` on the
{bpref "mf.siegel.halfspace"}[Siegel upper half space $`\mathcal{H}_g`]
taking values in $`V` is called a *Siegel modular form* of weight $`\rho` on $`\Gamma` if

$$`f((a\tau+b)(c\tau+d)^{-1})=\rho(c\tau+d)f(\tau)`

for all $`\begin{pmatrix} a&b\\c&d\end{pmatrix}\in \Gamma` (with $`a,b,c,d \in \mathrm{M}(g,\mathbb{Q})`) and all $`\tau\in\mathcal{H}_g`.

The arithmetic subgroups of $`\GSp(2g,\Q)` that we focus on are the following ones:
<ul><li>
{bpref "group.sp2gr"}[integral symplectic group:  $`\Sp(2g,\Z)`]
 </li><li>
{bpref "group.sp2gr.subgroup.congn"}[Congruence subgroups of $`\Sp(2g,\Z)`]
 </li><li>
{bpref "paramodulargroup.sp2gr"}[paramodular group:  $`\Gamma^{\mathrm{para}}(d)\subset \Sp(2g,\Q)`]
 </li>
</ul>
Note in the case of {bpref "cmf"}[(classical) modular forms], a
holomorphicity condition at all the cusps of $`\Gamma` is required in the definition.
Due to the so-called {bpref "mf.siegel.koecher.principle"}[Koecher principle] such a condition is superfluous for Siegel modular form of degree $`g>1`.

For each fixed choice of $`\rho` and $`\Gamma`, the set of modular forms of weight $`\rho` on $`\Gamma` is a finite-dimensional complex-vector space denoted by $`M_{\rho}(\Gamma)`.
Moreover if the representation $`\rho` is the direct sum of two representations
$`\rho=\rho_1\oplus \rho_2` then the space $`M_{\rho}(\Gamma)` is isomorphic to
$`M_{\rho_1}(\Gamma)\oplus M_{\rho_2}(\Gamma)` and we can restrict ourselves to
{bpref "repn.irrep.gl"}[irreducible representations] of $`\GL(g,\C)`.

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

(P) - Saito-Kurokawa type: Their $`L`-functions are of the form $`L(s,\mu)L(s+1/2,\sigma)L(s-1/2,\sigma)`, where $`\mu` is a cusp form on $`\GL(2)` and $`\sigma` is a Hecke character. {bpref "mf.siegel.lift.saito_kurokawa"}[Saito-Kurokawa lifts] are of type (P).

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
{bpref "mf.siegel.halfspace"}[Siegel upper half space $`\mathcal{H}_g`]
taking values in $`V` is called a *Siegel modular form with character $`\psi`* and
weight $`\rho` on $`\Gamma` if

$$`f((a\tau+b)(c\tau+d)^{-1})=\psi(\gamma)\rho(c\tau+d)f(\tau)`

for all $`\gamma=\begin{pmatrix} a&b\\c&d\end{pmatrix}\in \Gamma` (with $`a,b,c,d \in \mathrm{M}(g,\mathbb{Q})`) and all $`\tau\in\mathcal{H}_g`.

The space of Siegel modular forms with character $`\psi` and weight $`\rho` on $`\Gamma`
is denoted by $`M_{\rho}(\Gamma,\psi)` and its subspace of
{bpref "mf.siegel.cusp_form"}[cusp forms ] by $`S_{\rho}(\Gamma,\psi)`.
:::

:::definition "mf.siegel.coefficient_field" (lean := "SiegelUpperHalfSpace.coefficientField, SiegelUpperHalfSpace.vectorCoefficientField, SiegelUpperHalfSpace.heckeField, SiegelUpperHalfSpace.fourierCoeffs_eq_range, SiegelUpperHalfSpace.vectorFourierCoeffs_eq_range")
*Coefficient field for Siegel newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.coefficient_field))

The *coefficient field* of a Siegel modular form is the subfield of $`\C` generated by the coefficients $`a_n` of its $`q`-expansion $`\sum a_nq^n`.  The space of {bpref "mf.siegel.cusp_form"}[cusp forms] $`S_{k,j}^\mathrm{new}(\Gamma_F(N),\chi)` has a basis of modular forms that are simultaneous eigenforms for all {bpref "mf.siegel.hecke_operator"}[Hecke operators] and with algebraic Fourier coefficients.  For such eigenforms the coefficient field will be a number field, and Galois conjugate eigenforms will share the same coefficient field.  Moreover, if $`m` is the smallest positive integer such that the values of the character $`\chi` are contained in the cyclotomic field $`\Q(\zeta_m)`, the coefficient field will contain $`\Q(\zeta_m)`
For eigenforms, the coefficient field is also known as the *Hecke field*.

Depends on: {uses "mf.siegel.hecke_operator"}[]
:::

:::definition "mf.siegel.coefficient_ring" (lean := "SiegelUpperHalfSpace.coefficientRing, SiegelUpperHalfSpace.vectorCoefficientRing, SiegelUpperHalfSpace.heckeRing, SiegelUpperHalfSpace.heckeEigenvalues_eq_range")
*Coefficient ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.coefficient_ring))

The *coefficient ring* of a Siegel modular form is the subring $`\Z[{a_n}]` of $`\C` generated by the coefficients $`a_n` of its $`q`-expansion $`\sum a_nq^n`.  In the case of a {bpref "mf.siegel.newform"}[newform] the coefficients $`a_n` are algebraic integers and the coefficient ring is a finite index subring of the ring of integers of the {bpref "mf.siegel.coefficient_field"}[coefficient field] of the newform.
It is also known as the *Hecke ring*, since the $`a_n` generate the same ring as the eigenvalues of the Hecke operators.

Depends on: {uses "mf.siegel.coefficient_field"}[] {uses "mf.siegel.newform"}[]
:::

:::definition "mf.siegel.cusp_form"
*Siegel cusp form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.cusp_form))

A {bpref "mf.siegel"}[Siegel modular form]
Siegel modular form $`f`
{bpref "mf.siegel.character"}[with character]
$`\psi` and weight $`\rho` on an arithmetic subgroup $`\Gamma \leq \GSp(2g,\Q)`
is called a cusp form if for any $`\gamma\in \Sp(2g,\Q)`, we have

$$`\Phi(f|_{\rho}\gamma)=0`

where $`|` is the {bpref "mf.siegel.slash.op"}[slash operator].

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.character"}[] {uses "mf.siegel.slash.op"}[]
:::

:::definition "mf.siegel.cusp_form_degree2" (lean := "SiegelUpperHalfSpace.cuspFormsKJ, SiegelUpperHalfSpace.IsCuspForm, SiegelUpperHalfSpace.SiegelOperatorVanishes, SiegelUpperHalfSpace.rhoKJ, SiegelUpperHalfSpace.slash")
*Siegel cusp form of degree 2.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.cusp_form_degree2))

Let $`f` be a {bpref "mf.siegel.vector_valued_degree_two"}[vector-valued Siegel modular form] on
an arithmetic subsgroup $`\Gamma` of $`\GSp(4,\Q)` then $`f` is called a *cusp form* if for any $`\gamma\in \Sp(4,\Q)`, we have

$$`\Phi(f\vert_{k,j}\gamma)=0`

where $`\Phi` denotes the Siegel operator while $`\vert_{k,j}` denotes the slash operator.
:::

:::definition "mf.siegel.defining_polynomial"
*Defining polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.defining_polynomial))

The {bpref "mf.siegel.coefficient_field"}[coefficient field of a Siegel modular form] is a {bpref "nf"}[number field]. A *defining polynomial* for this number field is explicitly recorded, because some of the data associated to the modular form will be expressed in terms of roots of this polynomial.

Depends on: {uses "mf.siegel.coefficient_field"}[] {uses "nf"}[]
:::

:::definition "mf.siegel.degree" (lean := "SiegelUpperHalfSpace, SiegelUpperHalfSpace.modularForms")
*Degree of a Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.degree))

A {bpref "mf.siegel"}[Siegel modular form] on an arithmetic subgroup of
$`\Sp(2g,\Q)` is said to be of *degree* $`g`.

Depends on: {uses "mf.siegel"}[]
:::

:::definition "mf.siegel.dimension"
*Dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.dimension))

The *dimension* of a space of Siegel modular forms is its dimension as a complex vector space; for spaces of newforms $`S_{k,j}^{\rm new}(K(N),\chi)` this is the same as the dimension of the $`\Q`-vector space spanned by its eigenforms.

The *dimension* of a {bpref "mf.siegel.newform"}[newform] refers to the dimension of its {bpref "mf.siegel.newform_subspace"}[newform subspace], equivalently, the cardinality of its {bpref "mf.siegel.galois_orbit"}[newform orbit].  This is equal to the degree of its coefficient field (as an extension of $`\Q`).

The *relative dimension* of $`S_{k,j}^{\rm new}(K(N),\chi)`  is its dimension as a $`\Q(\chi)`-vector space, where $`\Q(\chi)` is the field generated by the values of $`\chi`, and similarly for newform subspaces.

Depends on: {uses "mf.siegel.newform"}[]
:::

:::definition "mf.siegel.eisenstein_series" (lean := "SiegelUpperHalfSpace.siegelEisensteinSeries, SiegelUpperHalfSpace.siegelEisensteinTerm, SiegelUpperHalfSpace.siegelEisensteinTerm_mul, SymplecticGroup.SiegelParabolicCosets")
*Siegel Eisenstein series.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.eisenstein_series))

The (Siegel) Eisenstein series in degree $`n`
 of even weight $`k>n+1` is defined by the formula

$$`\psi_k(Z)=\sum_{(C,D)}\det(CZ+D)^{-k},`

where the summation extends over all inequivalent bottom rows $`(C,D)`
of elements of the {bpref "group.sp2gr"}[integral
symplectic group] $`{\rm Sp}(2n,\mathbb{Z})`
 with respect to left multiplication by elements of $`{\rm GL}(n,\mathbb{Z})`.

Siegel Eisenstein series are also defined for some subgroups of the full integral symplectic group as well.
:::

:::definition "mf.siegel.family" (lean := "SymplecticGroup.Gamma, SymplecticGroup.Gamma0, SymplecticGroup.paramodular, SymplecticGroup.paramodularGL, SymplecticGroup.paramodularDelta_mul_mul_mem")
*Family of Siegel groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family))

Siegel modular forms of degree $`g` transform under the action of a discrete subgroup $`\Gamma` of $`\Sp(2g,\Q)`.  We focus on certain discrete subgroups.

- *Principal congruence subgroup*: {bpref "group.sp2gr.ppal.congruence"}[$`\Gamma(N)`].

- *Siegel parabolic subgroup*: {bpref "group.sp2gr.gamma0"}[$`\Gamma_0(N)`].

- *Paramodular subgroup*: {bpref "paramodulargroup.sp2gr"}[$`\Gamma^{\mathrm{para}}(d)`].
:::

:::definition "mf.siegel.family.gamma0_2"
*The ring of Siegel modular forms of degree 2 for $`\Gamma_0(2)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family.gamma0_2))

By a result of Tomoyoshi Ibukiyama , the ring $`M_{*}(\Gamma_0(2))` of {bpref "mf.siegel"}[Siegel modular forms] of {bpref "mf.siegel.degree"}[degree] 2  with respect to the group
$`\Gamma_0(2)`
is generated by the following five generators, which are specified in terms of
{bpref "mf.siegel.theta_constant"}[theta constants].

- $`X`, a form of weight 2, with formula $`X = ((\theta_{0000})^4+(\theta_{0001})^4+(\theta_{0010})^4+(\theta_{0011})^4)/4.`

- $`Y`, a form  of weight 4, with formula $`Y = (\theta_{0000}\theta_{0001}\theta_{0010}\theta_{0011})^2.`

- $`Z`, a form  of weight 4, with formula $`Z = ((\theta_{0100})^4-(\theta_{0110})^4)^2)/16384.`

- $`K`, a form  of weight 6, with formula $`K = (\theta_{0100}\theta_{0110}\theta_{1000}\theta_{1001}\theta_{1100}\theta_{1111})^2/4096.`

- $`\chi_{19}`, a cusp form of weight 19, with formula

$`\chi_{19} = \theta \theta'(8YZ-X^2T +YT +1024ZT+96T^2 - 8XK)/32,`
where
$$`\theta=\theta_{0000}\theta_{0001}\theta_{0010}\theta_{0011}\theta_{0100}\theta_{0110}\theta_{1000}\theta_{1001}\theta_{1100}\theta_{1111},\qquad
\theta' = ((\theta_{1000})^{12}+(\theta_{1001})^{12}+(\theta_{1100})^{12}+(\theta_{1111})^{12})/1536,\qquad T = (\theta_{0100}\theta_{0110})^{4}/256.`

The generators $`X, Y, Z, K` are algebraically independent.
The ring of modular forms is

$$`M(\Gamma_0(2)) = \C[X,Y,Z,K] + \chi_{19}\,\C[X,Y,Z,K].`

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.theta_constant"}[]
:::

:::definition "mf.siegel.family.gamma0_3" (lean := "SiegelUpperHalfSpace.IbukiyamaThree.Gamma0ThreeStructure, SiegelUpperHalfSpace.IbukiyamaThree.Gamma0ThreeGenerators, SiegelUpperHalfSpace.IbukiyamaThree.chi14, SiegelUpperHalfSpace.IbukiyamaThree.gamma4, SymplecticGroup.psi3")
*The ring of Siegel modular forms of degree 2 with respect to  $`\Gamma_0(3)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family.gamma0_3))

By a result of Tomoyoshi Ibukiyama , the ring $`M_{*}(\Gamma_0(3))` of {bpref "mf.siegel"}[Siegel modular forms] of {bpref "mf.siegel.degree"}[degree] 2 with respect to the group
$`\Gamma_0(3)` is generated by functions that may be specified in terms of {bpref "mf.siegel.theta_series"}[theta series].

Let

$$`A_2\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad E_6\begin{pmatrix}
2&-1&0&0&0&0\\
-1&2&-1&0&0&0\\
0&-1&2&-1&0&-1\\
0&0&-1&2&-1&0\\
0&0&0&-1&2&0\\
0&0&-1&0&0&2
\end{pmatrix},\qquad
E_6^* = 3E6^{-1},\qquad
S\begin{pmatrix}
1&0&3/2&0\\
0&1&0&3/2\\
3/2&0&3&0\\
0&3/2&0&3
\end{pmatrix},`

and let $`P:{\Bbb C}^4\times{\Bbb C}^4\to{\Bbb C}`
be a pluriharmonic polynomial defined by

$$`P(x,y)=(x_1y_3-x_3y_1)+(x_2y_4-x_4y_2)^2-(x_1y_4-x_4y_1 + x_3y_2-x_2y_3 + x_1y_2-x_2y_1 )^2.`

We now define the generators

- $`\alpha_1`, a form of weight 1 in $`S_1(\Gamma_0(3),\psi_3)`, with formula $`\alpha_1 = \theta_{A_2}.`

- $`\beta_3`, a form  of weight 3 in $`S_3(\Gamma_0(3),\psi_3)`, with formula $`\beta_3 = \theta_{E_6}-10 \theta_{A_2}^3 + 9 \theta_{E_6^*}.`

- $`\delta_3`, a form  of weight 3 in $`S_3(\Gamma_0(3),\psi_3)`, with formula $`\delta_3 = \theta_{E_6}- 9 \theta_{E_6^*}.`

- $`\gamma_4`, a form  of weight 4 in $`S_4(\Gamma_0(3))`, with formula $`\gamma_4 = \theta_{S,P}.`

- $`\chi_{14}`, a cusp form of weight 14 in $`S_{14}(\Gamma_0(3),\psi_3)`, with formula

$$`\chi_{14} = \frac1{2^9 3^{10}} \cdot \frac1{(2\pi i)^3}
\begin{vmatrix}
\alpha_1&3\beta_3&4\gamma_4/2&3\delta_4\\
\frac{\partial\alpha_1}{\partial\tau}& \frac{\partial\beta_3}{\partial\tau}&
\frac{\partial\gamma_4}{\partial\tau}& \frac{\partial\delta_3}{\partial\tau}\\
\frac{\partial\alpha_1}{\partial z}& \frac{\partial\beta_3}{\partial z}&
\frac{\partial\gamma_4}{\partial z}& \frac{\partial\delta_3}{\partial z}\\
\frac{\partial\alpha_1}{\partial\omega}& \frac{\partial\beta_3}{\partial\omega}&
\frac{\partial\gamma_4}{\partial\omega}& \frac{\partial\delta_3}{\partial\omega}
\end{vmatrix}
,`

where the character $`\psi_3:\Gamma_0(3)\to\{\pm1\}` is defined by

$$`\psi_3\left(\begin{pmatrix}A&B\\C&D\end{pmatrix}\right)
=\left(\frac{-3}{\det D}\right).`

The generators $`\alpha_1, \beta_3, \gamma_4, \delta_3` are algebraically independent.
Let

$$`B = {\Bbb C}[\alpha_1, \beta_3, \gamma_4, \delta_3],\qquad
C = {\Bbb C}[\alpha_1^2, \beta_3^2, \gamma_4, \delta_3^2].`

We then have the ring

$$`M_*(\Gamma_0(3)) = B^{\rm{even}} \oplus C\alpha_1\chi_{14}\oplus C\beta_3\chi_{14}
\oplus C\delta_3\chi_{14}\oplus C\alpha_1\beta_3\delta3\chi_{14}.`

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.theta_series"}[]
:::

:::definition "mf.siegel.family.gamma0_3_psi_3" (lean := "SiegelUpperHalfSpace.IbukiyamaThree.Gamma0ThreePsi3Structure, SymplecticGroup.psi3, SymplecticGroup.psi3Rat, SiegelUpperHalfSpace.gradedModularFormsChar, SiegelUpperHalfSpace.IbukiyamaThree.Gamma0ThreeGenerators")
*The ring of Siegel modular forms of degree 2 with respect to  $`\Gamma_0(3)` with character $`\psi_3`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family.gamma0_3_psi_3))

The character $`\psi_3:\Gamma_0(3)\to\{\pm1\}` is defined by

$$`\psi_3\left(\begin{pmatrix}A&B\\C&D\end{pmatrix}\right)
=\left(\frac{-3}{\det D}\right).`

By a result of Tomoyoshi Ibukiyama , the module $`\oplus_k M_{k}(\Gamma_0(3),\psi_3)` of {bpref "mf.siegel"}[Siegel modular forms] of {bpref "mf.siegel.degree"}[degree] 2 with respect to the group
$`\Gamma_0(3)` and the character $`\psi_3`
is generated by five functions that can be specified in terms of
{bpref "mf.siegel.theta_series"}[theta series].

Let

$$`A_2\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad E_6\begin{pmatrix}
2&-1&0&0&0&0\\
-1&2&-1&0&0&0\\
0&-1&2&-1&0&-1\\
0&0&-1&2&-1&0\\
0&0&0&-1&2&0\\
0&0&-1&0&0&2
\end{pmatrix},\qquad
E_6^* = 3E6^{-1},\qquad
S\begin{pmatrix}
1&0&3/2&0\\
0&1&0&3/2\\
3/2&0&3&0\\
0&3/2&0&3
\end{pmatrix},`

and let $`P:{\Bbb C}^4\times{\Bbb C}^4\to{\Bbb C}`
be a pluriharmonic polynomial defined by

$$`P(x,y)=(x_1y_3-x_3y_1)+x(_2y_4-x_4y_2)^2-(x_1y_4-x_4y_1 + x_3y_2-x_2y_3 + x_1y_2-x_2y_1 )^2.`

The five generators are

- $`\alpha_1`, a form of weight 1 in $`S_1(\Gamma_0(3),\psi_3)`, with formula $`\alpha_1 = \theta_{A_2}.`

- $`\beta_3`, a form  of weight 3 in $`S_3(\Gamma_0(3),\psi_3)`, with formula $`\beta_3 = \theta_{E_6}-10 \theta_{A_2}^3 + 9 \theta_{E_6^*}.`

- $`\delta_3`, a form  of weight 3 in $`S_3(\Gamma_0(3),\psi_3)`, with formula $`\delta_3 = \theta_{E_6}- 9 \theta_{E_6^*}.`

- $`\gamma_4`, a form  of weight 4 in $`S_4(\Gamma_0(3))`, with formula $`\gamma_4 = \theta_{S,P}.`

- $`\chi_{14}`, a cusp form of weight 14 in $`S_{14}(\Gamma_0(3),\psi_3)`, with formula

$$`\chi_{14} = \frac1{2^9 3^{10}} \cdot \frac1{(2\pi i)^3}
\begin{vmatrix}
\alpha_1&3\beta_3&4\gamma_4/2&3\delta_4\\
\frac{\partial\alpha_1}{\partial\tau}& \frac{\partial\beta_3}{\partial\tau}&
\frac{\partial\gamma_4}{\partial\tau}& \frac{\partial\delta_3}{\partial\tau}\\
\frac{\partial\alpha_1}{\partial z}& \frac{\partial\beta_3}{\partial z}&
\frac{\partial\gamma_4}{\partial z}& \frac{\partial\delta_3}{\partial z}\\
\frac{\partial\alpha_1}{\partial\omega}& \frac{\partial\beta_3}{\partial\omega}&
\frac{\partial\gamma_4}{\partial\omega}& \frac{\partial\delta_3}{\partial\omega}
\end{vmatrix}
.`

The generators $`\alpha_1, \beta_3, \gamma_4, \delta_3` are algebraically independent.
Let

$$`B = {\Bbb C}[\alpha_1, \beta_3, \gamma_4, \delta_3],\qquad
C = {\Bbb C}[\alpha_1^2, \beta_3^2, \gamma_4, \delta_3^2].`

We then have

$$`\oplus_k M_k(\Gamma_0(3),\psi_3) = B^{\rm{odd}} \oplus B^{\rm{even}}\chi_{14}.`

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.theta_series"}[]
:::

:::definition "mf.siegel.family.gamma0_4" (lean := "SiegelUpperHalfSpace.Ibukiyama.Gamma0FourStructure, SiegelUpperHalfSpace.Ibukiyama.f11, SiegelUpperHalfSpace.Ibukiyama.f2, SiegelUpperHalfSpace.double, SiegelUpperHalfSpace.IsFreeOverAdjoin")
*The ring of Siegel modular forms of degree 2 with respect to  $`\Gamma_0(4)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family.gamma0_4))

By results of Aoki and Ibukiyama , and of Hayashida and Ibukiyama , the ring $`M_{*}(\Gamma_0(4))` of {bpref "mf.siegel"}[Siegel modular forms] of {bpref "mf.siegel.degree"}[degree] 2 with respect to the group $`\Gamma_0(4)` is generated by the following functions, which are specified in terms of {bpref "mf.siegel.theta_constant"}[theta constants]:

- $`X`, a form of weight 2, with formula $`X = ((\theta_{0000})^4+(\theta_{0001})^4+(\theta_{0010})^4+(\theta_{0011})^4)/4.`

- $`X(2\Omega)`, a form of weight 2.

- $`f_2(2\Omega)`, a form  of weight 4, with formula $`f_2 = (\theta_{0000})^4.`

- $`K(2\Omega)`, a form  of of weight 6, with formula

$$`K = \theta_{0100}\theta_{0110}\theta_{1000}\theta_{1001}\theta_{1100}\theta_{1111})^2/4096.`

- $`f_{11}(2\Omega)`, a cusp form of weight 11, with formula $`f_{11} = f_6\chi_5,`

where

$$`\chi_5=\theta_{0000}\theta_{0001}\theta_{0010}\theta_{0011}\theta_{0100}\theta_{0110}\theta_{1000}\theta_{1001}\theta_{1100}\theta_{1111},\qquad
f_6 = ((\theta_{0001})^{4}-(\theta_{0010})^{4})
((\theta_{0001})^{4}-(\theta_{0011})^{4})((\theta_{0010})^{4}-(\theta_{0011})^{4}).`

Note that we write $`F(2\Omega)` to mean "apply $`F` after doubling the input".

The generators $`X, X(2\Omega),f_2(2\Omega), K(2\Omega)` are algebraically independent.
Let $`B={\Bbb C}[X, X(2\Omega),f_2(2\Omega), K(2\Omega)]`.  The ring of modular forms is

$$`M(\Gamma_0(4)) = B + Y(2\Omega) B + f_{11}(2\Omega)(B + Y(2\Omega) B),`

where
$`Y = (\theta_{0000}\theta_{0001}\theta_{0010}\theta_{0011})^2`.

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.theta_constant"}[]
:::

:::definition "mf.siegel.family.gamma0_4_psi_4"
*The ring of Siegel modular forms of degree 2 with respect to  $`\Gamma_0(4)` with character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family.gamma0_4_psi_4))

By results of Aoki and Ibukiyama , and of Hayashida and Ibukiyama , the  module $`\oplus_k M_{k}(\Gamma_0(4),\psi_4)` of {bpref "mf.siegel"}[Siegel modular forms] of {bpref "mf.siegel.degree"}[degree] 2 with respect to the group  $`\Gamma_0(4)` and {bpref "mf.siegel.character"}[character] $`\psi_4` is generated by the following functions, which are defined in terms of {bpref "mf.siegel.theta_constant"}[theta constants]:

- $`X`, a form of weight 2, with formula $`X = ((\theta_{0000})^4+(\theta_{0001})^4+(\theta_{0010})^4+(\theta_{0011})^4)/4.`

- $`X(2\Omega)`, a form of weight 2.

- $`f_2(2\Omega)`, a form  of weight 4, with formula $`f_2 = (\theta_{0000})^4.`

- $`K(2\Omega)`, a form  of of weight 6, with formula

$$`K = \theta_{0100}\theta_{0110}\theta_{1000}\theta_{1001}\theta_{1100}\theta_{1111})^2/4096.`

- $`f_{11}(2\Omega)`, a cusp form of weight 11, with formula $`f_{11} = f_6\chi_5,`

where

$$`\chi_5=\theta_{0000}\theta_{0001}\theta_{0010}\theta_{0011}\theta_{0100}\theta_{0110}\theta_{1000}\theta_{1001}\theta_{1100}\theta_{1111},\qquad
f_6 = ((\theta_{0001})^{4}-(\theta_{0010})^{4})
((\theta_{0001})^{4}-(\theta_{0011})^{4})((\theta_{0010})^{4}-(\theta_{0011})^{4}).`

Note that we write $`F(2\Omega)` to mean "apply $`F` after doubling the input".

The generators $`X, X(2\Omega),f_2(2\Omega), K(2\Omega)` are algebraically independent.
Let $`B={\Bbb C}[X, X(2\Omega),f_2(2\Omega), K(2\Omega)]`.  The module of modular forms with character of even weights only is then give by

$$`\oplus_{k=0}^\infty M_{2k}(\Gamma_0(4),\psi_4) =
f_{11}(2\Omega)f_{1}(2\Omega)B + Y(2\Omega) B + f_{11}(2\Omega)f_{3}(2\Omega)B,`

where $`f_1=\theta_{0000}^2` and $`f_3=(\theta_{0000}\theta_{0001}\theta_{0011})^2`.

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.character"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.theta_constant"}[]
:::

:::definition "mf.siegel.family.gamma_2"
*The ring of Siegel modular forms of degree 2 for $`\Gamma(2)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family.gamma_2))

We define the following subgroups of the symplectic group $`\Sp(4,\Z)`:

$$`\Gamma[2]=\{
  M\in \Sp(4,\Z):  M\equiv 1_4   \bmod 2 \} \, ,
  \qquad
  \Gamma_1[2]= \{ M\in \Sp(4,\Z):
  M\equiv \left(\begin{matrix} 1_2 & * \\ 0 & 1_2\end{matrix} \right) \bmod 2\} \, ,
  \qquad
  \Gamma_0[2]= \{
  M\in \Sp(4,\Z): M\equiv \left(\begin{matrix} * & * \\ 0 & *
  \end{matrix} \right) \bmod 2
  \}.`

  The successive quotients can be identified   as follows

$$`\Gamma_1[2]/ \Gamma[2]  \simeq (\Z/2\Z)^3, \quad
  \Gamma_0[2]/ \Gamma[2]  \simeq \Z/2\Z \times S_4, \quad
  \Gamma_0[2]/ \Gamma_1[2]  \simeq S_3, \quad
  \Gamma/ \Gamma[2]  \simeq S_6\,`

  where $`S_n` is the symmetric group on $`n` letters.

Recall that the irreducible representations of the symmetric group $`S_n` correspond bijectively to the partitions $`(\lambda)` of $`n`; the representation corresponding to the partition $`\lambda` will be denoted $`s[\lambda]`. Repetions of a digit in a partition will be abreviated by a power, e.g. $`[a,a,b,\ldots]=[a^2,b,\ldots]`. For convenience, we give the following:

$$`\text{Irreducible representations of }S_6\\
\begin{matrix}\lambda\colon & [6] & [5,1] & [4,2] & [4,1^2] & [3^2] & [3,2,1] & [3,1^3] & [2^3] & [2^2,1^2] & [2,1^4] & [1^6]\\
\dim\colon & 1 & 5 & 9 & 10 & 5 & 16 & 10 & 5 & 9 & 5 & 1\end{matrix}`

$$`\text{Irreducible representations of }S_3\\
\begin{matrix}\lambda\colon & [3] & [2,1] & [1^3]\\
\dim\colon & 1 & 2 & 1\end{matrix}`

It turns out that the vector space of vector-valued modular forms (resp. cusp forms) of weight $`(k,j)` on $`\Gamma[2]`, denoted $`M_{k,j}(\Gamma[2])` (resp. $`S_{k,j}(\Gamma[2])`), is a $`S_6`-representation space. We have the following splitting:

$$`M_{k,j}(\Gamma[2])=S_{k,j}(\Gamma[2])\oplus E_{k,j}(\Gamma[2]),`

where $`E_{k,j}(\Gamma[2])` denotes the space of Eisenstein series of weight $`(k,j)`.    We give the isotypic decomposition of these spaces as follows.  For fixed $`(k,j)`, the isotypic decompositions

- $`M_{k,j}(\Gamma[2])=m_{s[6]}s[6]+m_{s[5,1]}s[5,1]+\ldots +m_{s[1^6]}s[1^6]`,

- $`E_{k,j}(\Gamma[2])=n_{s[6]}s[6]+n_{s[5,1]}s[5,1]+\ldots +n_{s[1^6]}s[1^6]`,

- $`S_{k,j}(\Gamma[2])=l_{s[6]}s[6]+l_{s[5,1]}s[5,1]+\ldots +l_{s[1^6]}s[1^6]`,

will be denoted by

$$`\begin{matrix}
\lambda\colon & [6] & \ldots & [1^6]\\
[M_{k,j}(\Gamma[2]),E_{k,j}(\Gamma[2]),S_{k,j}(\Gamma[2])] & [m_{s[6]},n_{s[6]},l_{s[6]}] & \ldots & [m_{s[1^6]},n_{s[1^6]},l_{s[1^6]}]
\end{matrix}`

Since $`\Gamma_0[2]/ \Gamma_1[2]  \simeq S_3`, the space of vector-valued modular forms on $`\Gamma_1[2]` is a $`S_3`-representation space.

An $`S_6`-representation $`m_{s[6]}s[6]+m_{s[5,1]}s[5,1]+\ldots +m_{s[1^6]}s[1^6]`
contributes a $`S_3`-representation

$$`(m_{s[6]}+m_{s[4,2]}+m_{s[2^3]}s[3]+(m_{s[5,1]}+m_{s[4,2]}+m_{s[3,2,1]})s[2,1]+(m_{s[4,1^2]}+m_{s[3^2]})s[1^3]`

to $`M_{k,j}(\Gamma_1[2])` and a contribution $`m_{s[6]}+m_{s[4,2]}+m_{s[2^3]}` to the dimension of $`M_{k,j}(\Gamma_0[2])`. We use the same notations as for $`\Gamma[2]` for the isotypic decomposition (under $`S_3`) of the spaces $`M_{k,j}(\Gamma_1[2])`.

The structures of the graded rings $`R= \oplus_k M_{k,0}(\Gamma_[2])` and  $`R^{\rm ev}=\oplus_k M_{2k,0}(\Gamma[2])`   of scalar-valued modular forms on $`\Gamma[2]` has been determined by Jun-Ichi Igusa .  In order to describe these structures, we need to introduce theta series with characteristics.

We use the following (lexicographic) notation for the ten even theta characteristics

$$`\begin{aligned}
  & n_1=\left[\begin{matrix} 0 & 0 \cr 0 & 0 \cr\end{matrix}\right],
  n_2=\left[\begin{matrix} 0 & 0 \cr 0 & 1 \cr\end{matrix}\right],
  n_3=\left[\begin{matrix} 0 & 0 \cr 1 & 0 \cr\end{matrix}\right],
  n_4=\left[\begin{matrix} 0 & 0 \cr 1 & 1 \cr\end{matrix}\right],
  n_5=\left[\begin{matrix} 0 & 1 \cr 0 & 0 \cr\end{matrix}\right], \\
  & n_6=\left[\begin{matrix} 0 & 1 \cr 1 & 0 \cr\end{matrix}\right],
  n_7=\left[\begin{matrix} 1 & 0 \cr 0 & 0 \cr\end{matrix}\right],
  n_8=\left[\begin{matrix} 1 & 0 \cr 0 & 1 \cr\end{matrix}\right],
  n_9=\left[\begin{matrix} 1 & 1 \cr 0 & 0 \cr\end{matrix}\right],
  n_{10}=\left[\begin{matrix} 1 & 1 \cr 1 & 1 \cr\end{matrix}\right] \\
  \end{aligned}`

and define, for
$`\tau \in \mathbb{H}_2` and
$$`\begin{bmatrix} \mu \\ \nu \\ \end{bmatrix} = \begin{bmatrix} \mu_1 & \mu_2 \\ \nu_1 & \nu_2 \\ \end{bmatrix}`

with $`\mu =(\mu_1,\mu_2)` and $`\nu =(\nu_1,\nu_2)` in $`{\Z}^2`, the standard theta constants with characteristics

$$`\vartheta_{\begin{bmatrix}\mu  \\ \nu
  \end{bmatrix}}(\tau)=
  \sum_{n=(n_1,n_2) \in \Z^2}
  e^{\pi i
  \left((n+\mu /2)\left(\tau(n+\mu/2)^t+\nu^t\right)\right)}.`

We denote $`\vartheta_{n_i}=\vartheta_i` and $`\vartheta_i^4=x_i`. The results of Jun-Ichi Igusa can be read as follows:

$$`R^{\rm ev} \cong {\C}[x_1,\ldots,x_5]/(f)`

with $`f` a homogeneous polynomial of degree $`4` in the $`x_i`, the so-called Igusa quartic. The full ring   $`R` is a degree $`2` extension $`R^{\rm ev}[\chi_5]/(\chi_5^2+2^{14}\chi_{10})`  generated by the modular form $`\chi_5` of weight $`5`

$$`\chi_5= \prod_{i=1}^{10} \vartheta_{i}\, .`

Also see F. Cle;ry, G. van der Geer, S. Grushevsky,  and J. Bergstrom, C. Faber, G. van der Geer .
:::

:::definition "mf.siegel.family.sp4z" (lean := "SiegelUpperHalfSpace.Igusa.IgusaStructure, SiegelUpperHalfSpace.Igusa.psi, SiegelUpperHalfSpace.Igusa.chi10, SiegelUpperHalfSpace.Igusa.chi12, SiegelUpperHalfSpace.Igusa.chi35")
*The ring of Siegel modular forms of degree 2 with respect to the full modular group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family.sp4z))

By a classical result of Jun-Ichi Igusa , the ring $`M_{2}({\rm Sp}(4,\mathbb{Z}))` of {bpref "mf.siegel"}[Siegel modular forms] of {bpref "mf.siegel.degree"}[degree] 2 with \*even weights\* with respect to
the {bpref "group.sp2gr"}[full modular group] $`\mathrm{Sp}(4,{\Bbb Z})` is generated by the four algebraically independent {bpref "mf.siegel.eisenstein_series"}[Eisenstein series]: $`\psi_4`</a>,  $`\psi_6`</a>, $`\psi_{10}`</a>, $`\psi_{12}`</a>.

Alternatively, $`\psi_{10}` can be replaced by the cusp form

$$`\chi_{10} =-43867\cdot 2^{-12}3^{-5}5^{-2}7^{-1}53^{-1}(\psi_4\psi_6-\psi_{10})`

and $`\psi_{12}` can be replaced by the cusp form

$$`\chi_{12}=131\cdot593\cdot2^{-13}3^{-7}5^{-3}7^{-2}337^{-1}(441\psi_4^3+250\psi_6^2-691\psi_{12}).`

Note that $`\chi_{10}` is a Saito-Kurokawa lifting coming from the cuspform of weight 18 for $`{\rm SL}(2,\mathbb{Z})`, and $`\chi_{12}` is a Saito-Kurokawa lifting coming from the cuspform of weight 22.

The even weight forms are:

$$`{\Bbb C}[\psi_4,\psi_6,\chi_{10},\chi_{12}],`

with the cusp forms being the ideal generated by $`\chi_{10}, \chi_{12}`.

To generate the odd weight forms, there is one more generator, namely
$`\chi_{35}`

The odd weight forms are:

$$`\chi_{35}\,{\Bbb C}[\psi_4,\psi_6,\chi_{10},\chi_{12}],`

where $`\chi_{35}` is a weight 35 cusp form.

We write

- $`A=\psi_4`,

- $`B=\psi_6`,

- $`C=-4\chi_{10}`,

- $`D=12\chi_{12}`,

for short in the modular form pages.

Depends on: {uses "group.sp2gr"}[] {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.eisenstein_series"}[]
:::

:::definition "mf.siegel.family.sp4z_2" (lean := "SiegelUpperHalfSpace.Satoh.SatohStructure, SiegelUpperHalfSpace.satohBracket, SiegelUpperHalfSpace.Satoh.V, SiegelUpperHalfSpace.Satoh.W, SiegelUpperHalfSpace.Satoh.summand")
*Vector valued Siegel modular forms of degree 2 taking values in three-dimensional space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.family.sp4z_2))

The module of {bpref "mf.siegel.vector_valued"}[vector-valued Siegel modular forms] of {bpref "mf.siegel.degree"}[degree] 2, taking values in a three-dimensional space, with respect to the {bpref "group.sp2gr"}[full modular group].

Let $`\psi_4`, $`\psi_6`, $`\chi_{10}`, $`\chi_{12}` be generators of $`M(\Sp(4,\Z))`,
the Siegel modular forms of degree 2 with respect to the full modular group. We will write $`\Gamma_2=\Sp(4,\Z)` for short.  For $`f\in M_k(\Gamma_2)` and $`g\in M_j(\Gamma_2)`, define the Satoh bracket

$$`[f,g] = \frac 1{2\pi i}\left(\frac1k g\frac{d}{dZ}f-\frac1j f\frac{d}{dZ}g\right).`

Then $`[f,g]\in M_{k,2}(\Gamma_2)`, and for even integers $`k`,

$$`\begin{aligned}
M_{k,2}(\Gamma_2)
=& M_{k-10}(\Gamma_2) [\psi_4,\psi_6] \oplus M_{k-14}(\Gamma_2) [\psi_4,\chi_{10}] \\
 &\oplus M_{k-16}(\Gamma_2) [\psi_4,\chi_{12}]  \oplus V_{k-16}(\Gamma_2) [\psi_6,\chi_{10}]\\
&\oplus V_{k-18}(\Gamma_2) [\psi_6,\chi_{12}]\oplus V_{k-22}(\Gamma_2) [\chi_{10},\chi_{12}],
\end{aligned}`

where

$$`V_k(\Gamma_2)=M_k(\Gamma_2)\cap \C[\psi_6,\chi_{10},\chi_{12}],`

$$`W_k(\Gamma_2)=M_k(\Gamma_2)\cap \C[\chi_{10},\chi_{12}].`

We write

- $`A=\psi_4`,

- $`B=\psi_6`,

- $`C=\chi_{10}`,

- $`D=\chi_{12}`,

for short in the modular form sample pages.

Dimension tables are taken from Tsushima .

Depends on: {uses "group.sp2gr"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.vector_valued"}[]
:::

:::definition "mf.siegel.galois_orbit" (lean := "SiegelUpperHalfSpace.galoisOrbit, SiegelUpperHalfSpace.IsGaloisConjugate, SiegelUpperHalfSpace.IsGaloisConjugateBy, SiegelUpperHalfSpace.galoisOrbit_eq_iff, SiegelUpperHalfSpace.disjoint_galoisOrbit")
*Galois orbit.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.galois_orbit))

{bpref "mf.siegel.hecke_operator"}[Hecke operators]
operate on Siegel modular forms.
The Hecke eigenforms break into Galois orbits which are conjugate
over $`\Bbb Q`.
:::

:::definition "mf.siegel.halfspace" (lean := "SiegelUpperHalfSpace, SiegelUpperHalfSpace.val_smul, SiegelUpperHalfSpace.num, SiegelUpperHalfSpace.denom")
*Siegel upper half-space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.halfspace))

The Siegel upper half-space of degree $`g` is denoted by $`\mathcal{H}_g` and defined as

$$`\mathcal{H}_g=
\left\{
\tau \in \text{Mat}(g\times g): \tau=\tau^t, \, \text{Im}(\tau)>0
\right\}.`

It is the set of $`g\times g` complex symmetric matrices which have positive definite imaginary part. It is acted on by the {bpref "group.sp2gr"}[real symplectic group] via

$$`\left(
\begin{matrix}
\Sp(2g,\R)\times \mathcal{H}_g
& \to
& \mathcal{H}_g\\
(M=\left(\begin{matrix}a & b\\ c & d\end{matrix}\right), \tau)
&\mapsto
& (a\tau+b)(c\tau+d)^{-1}
\end{matrix}
\right).`

The action of any discrete subgroup of $`\Sp(2g,\R)` on $`\mathcal{H}_g`
is properly discontinuous. Note that the integral symplectic group $`\Gamma_g`
does not act freely on $`\mathcal{H}_g`.

Depends on: {uses "group.sp2gr"}[]
:::

:::definition "mf.siegel.hecke_operator" (lean := "SiegelUpperHalfSpace.siegelHeckeRingOf, SiegelUpperHalfSpace.localSiegelHeckeRingOf, SiegelUpperHalfSpace.heckeTSqOf, SiegelUpperHalfSpace.heckeOperator, SiegelUpperHalfSpace.IsHeckeEigenform")
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

:::definition "mf.siegel.klingen_eisenstein_series" (lean := "SiegelUpperHalfSpace.klingenEisensteinSeries, SymplecticGroup.klingenParabolic, SiegelUpperHalfSpace.klingenTerm, SiegelUpperHalfSpace.klingenTerm_mul, SiegelUpperHalfSpace.upperLeft_smul")
*Siegel Klingen-Eisenstein series.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.klingen_eisenstein_series))

Given a modular form $`f` of degree $`n_1 \le n` and  weight $`k > n + n_1 + 1` the
Klingen-Eisenstein series of $`f` is a modular
form $`E_{n, n_1}(f)` of degree $`n` and weight $`k` such that the {bpref "mf.siegel.phi"}[Siegel $`\Phi`
operator] maps $`E_{n, n_1}(f)` to $`f`.
:::

:::definition "mf.siegel.koecher.principle"
*Koecher principle.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.koecher.principle))

Let $`f(\tau)=\sum_{n\in L_{\Gamma}^{\vee}} a(n) e^{2 \pi i \text{tr}(n\tau)}` be the {bpref "mf.siegel.q-expansion"}[q-expansion] of $`f\in M_{\rho}(\Gamma)`.
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

- $`x` is the label of the {bpref "mf.siegel.galois_orbit"}[Galois orbit] of the newform $`f`.

For each embedding of the {bpref "mf.siegel.coefficient_field"}[coefficient field] of $`f` into the complex numbers, the corresponding modular form over $`\C` has a label of the form $`g.F.N.k1...kd.a.x.n.i`, where

- $`n` determines the {bpref "character.dirichlet.conrey"}[Conrey label] $`N.n` of the Dirichlet character $`\chi`;

- $`i` is an integer ranging from 1 to the relative dimension of the newform that distinguishes embeddings with the same character $`\chi`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_label"}[] {uses "mf.siegel.coefficient_field"}[] {uses "mf.siegel.degree"}[] {uses "mf.siegel.family"}[] {uses "mf.siegel.level"}[] {uses "mf.siegel.newform"}[] {uses "mf.siegel.weight"}[]
:::

:::definition "mf.siegel.level" (lean := "SymplecticGroup.IsCongruenceOfLevel, SymplecticGroup.isCongruenceOfLevel_Gamma0, SymplecticGroup.IsCongruenceOfLevel.mul, SiegelUpperHalfSpace.modularForms")
*Level of a Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.level))

A {bpref "mf.siegel"}[Siegel modular form] on a discrete subgroup $`\Gamma` of $`\Sp(2g,\Q)`  is said to be of *level* $`N` if $`\Gamma` is a
{bpref "group.sp2gr.subgroup.congn"}[congruence subgroup of level] $`N`.

A Siegel modular form on a discrete subgroup $`\Gamma` of $`\Sp(2g,\Q)` is said to be of *level* $`N` if $`\Gamma` is a {bpref "group.sp2gr.subgroup.congn"}[congruence subgroup of level] $`N`.

Families of congruence subgroups are typically indexed by the
minimal level $`N` of the subgroup. For example, in degree $`2`, we have the paramodular groups
{bpref "group.paramodular"}[$`K(N)`],
the congruence subgroups
{bpref "group.sp2gr.gamma0"}[$`\Gamma_0(N)`],
and the principal congruence subgroups
{bpref "group.sp2gr.ppal.congruence"}[$`\Gamma(N)`].

Depends on: {uses "mf.siegel"}[]
:::

:::definition "mf.siegel.lift"
*Lift Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.lift))

A Siegel eigenform is a lift if its Euler factors are products of Euler factors that arise from Siegel modular forms of lower genus.
:::

:::definition "mf.siegel.lift.gritsenko" (lean := "SiegelUpperHalfSpace.gritsenkoLift, SiegelUpperHalfSpace.gritsenkoCoeff, SiegelUpperHalfSpace.GritsenkoLiftTheorem, ModularForm.jacobiCoeff, ModularForm.HasJacobiFourierExpansion.unique")
*Gritsenko lift.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.lift.gritsenko))

Given a Jacobi cusp form
$`\phi(\tau,z)\in J_{k,N}^{\text{cusp}}`,
the Gritsenko lift of $`\phi`,

$$`Grit(\phi)\in S_k(K(N)),`

is a paramodular form
defined by the formula on its Fourier coefficients

$$`a(Grit(\phi); n,r,m) =
\sum_{d|(n,r,m)} d^{k-1} c(\phi; mn/d^2, r/d).`

If $`\phi` is a Jacobi cusp form,
then $`Grit(\phi)` is a paramodular cusp form.

The L-function of the Gritsenko lift is related to the L-function
of an elliptic modular form that is related to the Jacobi form.
:::

:::definition "mf.siegel.lift.ikeda"
*Duke-Imamoglu-Ikeda lift.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.lift.ikeda))

A Duke-Imamoglu-Ikeda lift is a lift from
elliptic modular forms</a>
 to
{bpref "mf.siegel"}[Siegel modular forms]
of even degree
with respect to the
integral {bpref "group.sp2gr"}[symplectic group].
An elliptic cusp eigenform of weight $`k` may be lifted to
a cusp eigenform of even degree $`n` of even weight $`(k+n)/2`.

The Ikeda lifting, also known as Duke-Imamoglu-Ikeda lifting, is a generalization of the {bpref "mf.siegel.lift.saito_kurokawa"}[Saito-Kurokawa lifting]. Given $`n\geq1`, it associates to an {bpref "cmf"}[elliptic modular eigenform] $`f\in S_{2k}({\rm SL}(2,\mathbb{Z}))`, where $`k\equiv n` mod $`2`, a {bpref "mf.siegel"}[Siegel modular form] $`F` of degree $`2n` and weight $`k+n` with respect to the integral {bpref "group.sp2gr"}[symplectic group]. The $`L`-function of $`f` and the standard $`L`-function of $`F` are related by

$$`L(s,F)=\zeta(s)\prod_{i=1}^{2n}L(s+k+n-i,f),`

where $`\zeta` is the {bpref "lfunction.riemann"}[Riemann zeta function].

Depends on: {uses "cmf"}[] {uses "group.sp2gr"}[] {uses "lfunction.riemann"}[] {uses "mf.siegel"}[] {uses "mf.siegel.lift.saito_kurokawa"}[]
:::

:::definition "mf.siegel.lift.maass"
*Maass lift from Jacobi form to Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.lift.maass))

A Maass lift is a lift from {bpref "mf.jacobi"}[Jacobi forms] to {bpref "mf.siegel"}[Siegel modular forms] of degree 2 with respect to the {bpref "group.sp2gr"}[Siegel modular group].

Depends on: {uses "group.sp2gr"}[] {uses "mf.jacobi"}[] {uses "mf.siegel"}[]
:::

:::definition "mf.siegel.lift.miyawaki"
*Miyawaki lift.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.lift.miyawaki))

A <b>Miyawaki Lift</b> is a {bpref "mf.siegel.lift"}[lift]
from {bpref "cmf"}[elliptic modular forms]
to {bpref "mf.siegel"}[Siegel modular forms] of degree 3
over the full {bpref "group.sp2gr"}[symplectic group].

Miyawaki conjectured two types of lift.
{bpref "mf.siegel.lift.miyawaki1"}[Type I],
also called the Ikeda–Miyawaki lift,
was established by Ikeda using a Duke-Imamoglu-Ikeda lift
provided that the construction does not produce 0.
Ikeda's construction is valid for degrees other than 3.
{bpref "mf.siegel.lift.miyawaki2"}[Type II] remains conjectural.

On the right sides of the Miyawaki lift Euler factor and $`L`-function descriptions,
the elliptic Euler factor is

$$`Q_p(f,X)=1-a_p(f)X+p^{k-1}X^2`

with $`a_p(f)` the $`p`-th Fourier coefficient of the normalized weight $`k` eigenform $`f`.
Let $`Q_p(f,X)` factor as $`(1-\gamma_+X)(1-\gamma_-X)`;
the standard elliptic Euler factor of $`f` is
$`Q_p^{\rm st}(f,X)=(1-X)(1-(\gamma_+/\gamma_-)X)(1-(\gamma_-/\gamma_+)X)`,
and this is

$$`Q_p^{\rm st}(f,X)=(1-X)(1-(a_p(f)^2/p^{k-1}-2)X+X^2).`

Also, if $`g` has weight $`\ell` and $`Q_p(g,X)=(1-\delta_+X)(1-\delta_-X)`
then $`Q_p(f\otimes g,X)=(1-\gamma_+\delta_+X)(1-\gamma_+\delta_-X)(1-\gamma_-\delta_+X)(1-\gamma_-\delta_-X)`,
and this is

$$`Q_p(f\otimes g,X)=1-a_p(f)a_p(g)X+(a_p(f)^2p^{\ell-1}+a_p(g)^2p^{k-1}-2p^{k+\ell-2})X^2-a_p(f)a_p(g)p^{k+\ell-2}X^3+p^{2k+2\ell-4}X^4.`

Depends on: {uses "cmf"}[] {uses "group.sp2gr"}[] {uses "mf.siegel"}[] {uses "mf.siegel.lift"}[] {uses "mf.siegel.lift.miyawaki1"}[] {uses "mf.siegel.lift.miyawaki2"}[]
:::

:::definition "mf.siegel.lift.miyawaki1"
*Miyawaki lift of type I, Ikeda-Miyawaki lift.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.lift.miyawaki1))

<b>Genus 3 Miyawaki Lift, Type I:</b>  Let $`k` be an even weight. Each pair of elliptic Hecke cusp eigenforms

$$`f\in{\mathcal S}_{2k-4}(\SL(2,{\mathbb{Z}}))
\quad\text{and}\quad
g\in{\mathcal S}_k(\SL(2,{\mathbb{Z}}))`

has an Ikeda-Miyawaki lift, or Miyawaki lift of type I, a Siegel Hecke cusp eigenform

$$`F\in{\mathcal S}_k(\Sp(6,{\mathbb{Z}}))`

If $`F` is nonzero then its standard Euler factors and standard $`L`-function factor as

$$`Q_p^{\rm st}(F,X)=Q_p(f,p^{2-k}X)Q_p(f,p^{3-k}X)Q_p^{\rm st}(g,X)`

and

$$`L^{\rm st}(F,s)=L(f,s+k-2)L(f,s+k-3)L^{\rm st}(g,s)`

and its spinor Euler factors and spinor $`L`-function factor as

$$`Q_p^{\rm spin}(F,X)=Q_p(g,p^{k-2}X)Q_p(g,p^{k-3}X)Q_p(f\otimes g,X)`

and
$$`L^{\rm spin}(F,s)=L(g,s-k+2)L(g,s-k+3)L(f\otimes g,s).`

More generally, Ikeda proved the following.

<p><b>Theorem (Ikeda-Miyawaki Lift, Type I)</b>
Let $`k`, $`n+r`, and $`m=(n+r+k)/2` be all even integers with $`r\le n`.
Given: an elliptic cusp eigenforms, $`f` of weight $`k` and
a cusp eigenform $`g` in degree $`r` of weight $`2m`,
there exists an eigenform in degree $`n` of weight $`m`
such that if nonzero it has an
$`L`-function that is a product of $`L`-functions related to those of $`f` and $`g`.
</p>
:::

:::definition "mf.siegel.lift.miyawaki2"
*Miyawaki lift of type II.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.lift.miyawaki2))

<b>Miyawaki Lift, Type II (conjectural):</b>  Let $`k` be an even weight.
For each pair of elliptic Hecke cusp eigenforms

$$`f\in{\mathcal S}_{2k-2}(\SL(2,{\mathbb{Z}}))
\quad\text{quad}\quad
g\in{\mathcal S}_{k-2}(\SL(2,{\mathbb{Z}}))`

their Miyawaki lift of type II is a Siegel Hecke cusp eigenform

$$`F\in{\mathcal S}_k(\Sp(6,{\mathbb{Z}}))`

whose standard Euler factors and standard $`L`-function factor as

$$`Q_p^{\rm st}(F,X)=Q_p(f,p^{1-k}X)Q_p(f,p^{2-k}X)Q_p^{\rm st}(g,X)`

and
$$`L^{\rm st}(F,s)=L(f,s+k-1)L(f,s+k-2)L^{\rm st}(g,s)`

and whose spinor Euler factors and spinor L-function factor as

$$`Q_p^{\rm spin}(F,X)=Q_p(g,p^{k-1}X)Q_p(g,p^{k-2}X)Q_p(f\otimes g,X)`

and
$$`L^{\rm spin}(F,s)=L(g,s-k+1)L(g,s-k+2)L(f\otimes g,s).`
:::

:::definition "mf.siegel.lift.saito_kurokawa"
*Saito-Kurokawa lift.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.lift.saito_kurokawa))

The Saito-Kurokawa lifting associates to an {bpref "cmf"}[elliptic modular eigenform] $`f\in S_{2k}({\rm SL}(2,\mathbb{Z}))`, where $`k` is odd, a {bpref "mf.siegel"}[Siegel modular form] $`F` of degree $`2` and weight $`k+1` with respect to the full
{bpref "group.sp2gr"}[symplectic group]. The $`L`-function of $`f` and the spin $`L`-function of $`F` are related by

$$`L(s,F)=L(s,f)\zeta(s+1/2)\zeta(s-1/2),`

where $`\zeta` is the {bpref "lfunction.riemann"}[Riemann zeta function]. The space spanned by all Saito-Kurokawa lifts is the same as the space spanned by all Maass lifts.
:::

:::definition "mf.siegel.newform"
*Siegel newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.newform))

Let $`M_{\rho}(K(N))` be the space of {bpref "mf.siegel"}[Siegel modular forms] of {bpref "mf.siegel.weight"}[weight] $`\rho` and {bpref "group.paramodular"}[paramodular level] $`N`.

If $`M` is a proper divisor of $`N`, then for every divisor $`D \mid (N/M)`, there are maps from $`M_{\rho}(K(M))` to $`M_{\rho}(K(N))`.  Such modular forms are said to be *old*, and together they span a subspace $`M_{\rho}^{\rm old}(K(N)) \subseteq M_{\rho}(K(N))`.

The orthogonal complement of the $`S_{\rho}^{\rm old}(K(N))` in $`S_{\rho}(K(N))` with respect to the Petersson scalar product is denoted $`S_{\rho}^{\rm new}(K(N))`, and we have the decomposition

$$`S_{\rho}(K(N))=S_{\rho}^{\rm old}(K(N))\oplus S_{\rho}^{\rm new}(K(N)).`

into the *old subspace* and *new subspace*.

A *newform* is a cusp form $`f\in S_{\rho}^{\rm new}(K(N))` that is also an eigenform of all {bpref "mf.siegel.hecke_operator"}[Hecke operators], normalized so that the $`q`-expansion  $`f(\tau)=\sum a_{T} q^T`, where $`q=e^{2\pi i {\rm tr}(T \tau) }`, begins with the coefficient $`a_1=1`.  The newforms are a basis for the vector space $`S_{\rho}^{\rm new}(K(N))`.

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.hecke_operator"}[] {uses "mf.siegel.weight"}[]
:::

:::definition "mf.siegel.newform.paramodular"
*Paramodular newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.newform.paramodular))

A paramodular form on $`K(N)`
that is a Hecke eigenform
is a newform if it is not a
{bpref "mf.siegel.lift.gritsenko"}[Gritsenko Lift]
and it is not
the result of applying
a level raising Hecke operator to a paramodular form
of a lower level.
There are three level raising operators
(see \*Local newforms for GSp(4)\*
 by Brooks Roberts and Ralf Schmidt ):

$$`\begin{aligned}
V_m^+:& S_k(K(N)) \to S_k(K(mN))\\
V_m^-:& S_k(K(N)) \to S_k(K(mN))\\
U_m:& S_k(K(N)) \to S_k(K(m^2 N)).
\end{aligned}`

Depends on: {uses "mf.siegel.lift.gritsenko"}[]
:::

:::definition "mf.siegel.newform_subspace" (lean := "SiegelUpperHalfSpace.newformSubspace, SiegelUpperHalfSpace.self_mem_newformSubspace, SiegelUpperHalfSpace.IsParamodularNewform, SiegelUpperHalfSpace.IsGaloisConjugate")
*Newform subspace.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.newform_subspace))

The newform subspace of a newform $`f` in $`S_{k,j}^{\rm new}(K(N),\chi)` is the subspace generated by $`T_{(1,1,p,p)}(f)` and $`T_{(1,p,p,p^2)}(f)` for all Hecke operators $`T_{(1,1,p,p)}, T_{(1,p,p,p^2)}` for $`p` coprime to the level, equivalently, the subspace generated by the Galois conjugates of $`f`.
Every newspace has a canonical decomposition into newform subspaces.
:::

:::definition "mf.siegel.newspace"
*Space of paramodular newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.newspace))

For each {bpref "mf.siegel.level"}[level] $`N`, {bpref "mf.siegel.weight_k_j"}[weight] $`k`, and {bpref "mf.siegel.character"}[character] $`\chi` the space $`S_{k,j}(K(N),\chi)` of {bpref "mf.siegel.cusp_form"}[cuspidal modular forms] can be decomposed as an internal direct sum

$$`S_{k,j}(K(N),\chi) = S_{k,j}^{\rm old}(K(N),\chi) \oplus S_{k,j}^{\rm new}(K(N),\chi).`

The *old subspace* $`S_{k,j}^{\rm old}(K(N),\chi)` is generated by all elements of
$`S_{k,j}(K(N),\chi)` which are in the image of the level-raising operators $`\eta, \theta, \theta'`.

The *new subspace* $`S_{k,j}^{\rm new}(K(N),\chi)` is the orthogonal complement of $`S_{k,j}^{\rm old}(K(N),\chi)` with respect to the Petersson inner product on $`S_{k,j}(K(N),\chi)`.  The {bpref "mf.siegel.newform"}[newforms] in $`S_{k,j}(K(N),\chi)` are a canonical basis for this subspace.

Depends on: {uses "mf.siegel.character"}[] {uses "mf.siegel.level"}[] {uses "mf.siegel.newform"}[] {uses "mf.siegel.weight_k_j"}[]
:::

:::definition "mf.siegel.phi" (lean := "SiegelUpperHalfSpace.siegelPhi, SiegelUpperHalfSpace.HasSiegelPhi, SiegelUpperHalfSpace.phiPoint, SiegelUpperHalfSpace.siegelPhi_eq, SiegelUpperHalfSpace.HasSiegelPhi.add")
*Siegel $`\Phi` operator.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.phi))

The *Siegel $`\Phi` operator* is a linear map that sends {bpref "mf.siegel.degree"}[degree] $`g` Siegel modular forms to degree $`g-1` ones; it is defined by

$$`\Phi(f)(\tau) = \lim_{t\to +\infty}
f\begin{pmatrix}\tau&0\\0&it\end{pmatrix} \quad \text{for any } \tau \in \mathfrak{H}_{g-1}.`

Depends on: {uses "mf.siegel.degree"}[]
:::

:::definition "mf.siegel.q-expansion" (lean := "SiegelUpperHalfSpace.HasSiegelFourierExpansion, SiegelUpperHalfSpace.translationLattice, SiegelUpperHalfSpace.dualLattice, SiegelUpperHalfSpace.fourierExp, SiegelUpperHalfSpace.HasSiegelFourierExpansion.unique")
*Fourier expansion smf.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.q-expansion))

Let $`f` be a {bpref "mf.siegel"}[Siegel modular form] of
{bpref "mf.siegel.weight"}[weight] $`\rho` on a discrete subgroup $`\Gamma` of $`\Sp(2g,\Q)` that is {bpref "commensurable.group"}[commensurable] with $`\Sp(2g,\Z)`.
Let $`V_g(\Q)` be the vector space of rational symmetric $`g\times g` matrices and

$$`L_{\Gamma}=
\left\{
s \in V_g(\Q)\, : \, \left( \begin{array}{ll}  1_g & s \\ 0 & 1_g \end{array}\right)\in \Gamma
\right\}`

be the translation lattice, which is commensurable with $`V_g(\Z)`. Its dual lattice is

$$`L_{\Gamma}^{\vee}=
\left\{
n\in V_{g}(\Q)\, : \, \text{ for any } s \in L_{\Gamma}, \text{tr}(sn) \in \Z
\right\}.`

For $`\tau \in \mathcal{H}_g`, there is a Fourier expansion

$$`f(\tau)=\sum_{n\in L_{\Gamma}^{\vee}} a(n) e^{2 \pi i \text{tr}(n\tau)}.`

Depends on: {uses "commensurable.group"}[] {uses "mf.siegel"}[] {uses "mf.siegel.weight"}[]
:::

:::definition "mf.siegel.slash.op" (lean := "SiegelUpperHalfSpace.gspSlash, SiegelUpperHalfSpace.gspPlus, SiegelUpperHalfSpace.multiplier, SiegelUpperHalfSpace.gspSmul_val, SiegelUpperHalfSpace.gspSlash_ofSp")
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

:::definition "mf.siegel.subspace.degree.two"
*Subspaces of degree 2 Siegel modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.subspace.degree.two))

The space {bpref "mf.siegel.vector_valued_degree_two"}[vector-valued Siegel modular forms] $`M_{j,k}(\Gamma_2)` can be decomposed as

$$`M_{j,k}(\Gamma_2)=S_{j,k}(\Gamma_2)\oplus N_{j,k}(\Gamma_2)`

where $`S_{j,k}(\Gamma_2)` denotes the subspace of
{bpref "mf.siegel.cusp_form_degree2"}[cusp forms] on $`\Gamma_2`
and $`N_{j,k}(\Gamma_2)` denotes its orthogonal complement with respect to the
Petersson inner product.
The previous decomposition is stable under the
{bpref "mf.siegel.hecke_operator"}[Hecke operators].
The subspace $`N_{j,k}(\Gamma_2)` can be in turn decomposed into a direct sum, again stable under the
{bpref "mf.siegel.hecke_operator"}[Hecke operators]. :

$$`N_{j,k}(\Gamma_2)=E_{j,k}(\Gamma_2)\oplus KE_{j,k}(\Gamma_2)`

where $`E_{j,k}(\Gamma_2)` denotes the subspace of
{bpref "mf.siegel.eisenstein_series"}[Eisenstein series.]
while $`KE_{j,k}(\Gamma_2)` denotes the subspace of {bpref "mf.siegel.klingen_eisenstein_series"}[Klingen-Eisenstein series.]
For $`k>4` and $`j>0`, the subspace $`KE_{j,k}(\Gamma_2)` is isomorphic
to the space of cusp forms of weight $`k+j` on $`\SL(2,\Z)`.

Depends on: {uses "mf.siegel.cusp_form_degree2"}[] {uses "mf.siegel.eisenstein_series"}[] {uses "mf.siegel.hecke_operator"}[] {uses "mf.siegel.klingen_eisenstein_series"}[] {uses "mf.siegel.vector_valued_degree_two"}[]
:::

:::definition "mf.siegel.theta_constant" (lean := "SiegelUpperHalfSpace.thetaConstant, SiegelUpperHalfSpace.thetaConstant_zero_zero")
*Theta constant.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.theta_constant))

Given a degree $`g` and a vector
$`m = (\mu,\nu)\in {\Bbb Z}^{g}\times {\Bbb Z}^{g}`,
define the theta constant of characteristic $`m`
by

$$`\theta_m(\Omega) = \sum_{n\in{\Bbb Z}^{g}}
\exp\left( \frac12(n+\frac\mu2)'\Omega(n+\frac\mu2)
+(n+\frac\mu2)\frac\nu2\right).`

Then $`\theta_m` is a
{bpref "mf.siegel"}[Siegel modular form]
of weight $`\frac12` with respect
to some subgroup of the integral
{bpref "group.sp2gr"}[symplectic group]
with some character.
:::

:::definition "mf.siegel.theta_series" (lean := "SiegelUpperHalfSpace.latticeTheta, SiegelUpperHalfSpace.IsPluriharmonic, SiegelUpperHalfSpace.IbukiyamaThree.isPluriharmonic_P")
*Siegel theta series and theta series with pluriharmonics.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.theta_series))

Given a positive definite quadratic $`m\times m`
positive definite even quadratic form $`Q`,
and given a degree $`g`,
define

$$`\vartheta_Q^{(g)}(\Omega)
=
\sum_{N\in\Bbb Z^{m \times g}}
\exp(\pi i N' Q N \Omega )`

If $`m` is a multiple of 4,
this is a Siegel modular form of degree $`g`
of weight $`m/2`
with respect to the subgroup $`\Gamma_0(\ell)`
where $`\ell` is such that $`\ell Q^{-1}` is an even quadratic form.

We say $`P` is pluriharmonic (spherical function) in the matrix variable
$`X=(x_{r,s})` for $`1\le r\le m`, $`1\le s\le g`,
 if
<ul>
<li>for each $`1\le i,j\le n`, we have $`\displaystyle{\sum_{t=1}^g\frac{\partial^2 P}{\partial_{i,t}\partial_{j,t}}=0}`</li>
</ul>
Define the theta series with pluriharmonic polynomial $`P` homogeneous of degree $`\nu`
to be

$$`\vartheta_{Q,P}^{(g)}(\Omega)=
\sum_{N\in\Bbb Z^{m \times g}}
P(N) \exp(\pi i N' Q N \Omega )`

If $`m` is a multiple of 4,
this is a Siegel cusp form of weight $`m/2+\nu` in degree $`g`
with respect to the subgroup $`\Gamma_0(\ell)`.

When $`m` is not a multiple of $`4`, one gets a Siegel modular form with a character.
:::

:::definition "mf.siegel.vector_valued"
*Vector-valued Siegel modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.vector_valued))

Let $`\rho: \GL_g(\mathbb{C})\to \GL(V),` where $`V` is a finite-dimensional complex vector space, be an irreducible representation.  A (vector valued) Siegel modular form of degree $`g`, weight $`\rho`, with respect to a subgroup
$`\Gamma\subset \GSp(2g,\Q)` is a complex analytic function $`F:\Bbb{H}_g\to V`
such that for any $`\gamma=\begin{pmatrix} A&B\\C&D\end{pmatrix}` we have
$`F((AZ+B)(CZ+D)^{-1})=\left(\rho(C Z+D)\right)F(Z)`.  If $`g=1`, one must also impose the following condition: there exists $`\epsilon>0` such that

$$`|F(x+iy)|\ll y^\epsilon\quad\text{for }y\geq 1.`

Consider the case $`g=2`.  Let $`std` denote the standard representation of $`\GL_2(\C)`, i.e. $`std` is the identity map from $`\GL_2(\C)` to $`\GL(\C^2)`.  To any pair of integers $`(k,j)` one associates the representation $`\rho_{k,j}:=Sym^{j}(std)\otimes\det(std)^{k}` of $`\GL_2(\C)`.  This enumerates all the irreducible representations of $`\GL_2(\C)`.
:::

:::definition "mf.siegel.vector_valued_degree_two" (lean := "SiegelUpperHalfSpace.rhoKJ, SiegelUpperHalfSpace.modularFormsKJ")
*Vector-valued Siegel modular forms of degree 2.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.vector_valued_degree_two))

The {bpref "repn.irrep.gl"}[irreducible representations] of $`\GL(2,\C)`
are given by $`\rho_{k,j}:=\det(St)^{\otimes k}\otimes \text{Sym}^{j}(St)`
where $`St` stands for the standard representation of $`\GL(2,\C)` and
$`(k,j)\in \Z\times\Z_{\geqslant 0}`. The space of
{bpref "mf.siegel"}[Siegel modualr forms ]
of weight $`\rho_{k,j}` on any arithmetic subsgroup $`\Gamma` of $`\GSp(4,\Q)` will be denoted by $`M_{k,j}(\Gamma)`.

Depends on: {uses "mf.siegel"}[] {uses "repn.irrep.gl"}[]
:::

:::definition "mf.siegel.weight" (lean := "SiegelUpperHalfSpace.modularForms, SiegelUpperHalfSpace.rhoKJ, SiegelUpperHalfSpace.modularFormsKJ, Representation.highestWeight")
*Weight of a Siegel modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.weight))

The *weight* of a {bpref "mf.siegel"}[Siegel modular form] $`f` of {bpref "mf.siegel.degree"}[degree] $`g` is the
finite-dimensional complex representation $`\rho` of $`\GL(g,\mathbb{C})`
that occurs in the modular transformation property of $`f` under the action of $`\gamma = \left( \begin{array}{ll}  a & b \\ c & d \end{array}\right)` on the {bpref "mf.siegel.halfspace"}[Siegel upper half space $`\mathcal{H}_g`].  That is, the weight is the representation $`\rho`
in the transformation law

$$`f\left( (a \tau + b)(c \tau + d)^{-1} \right) = \rho(c \tau + d) f(\tau) .`

Irreducible representations of $`\GL(g,\mathbb{C})` are indexed by their {bpref "repn.irrep.gl"}[highest weight].

In degree $`2`, to a pair of non-negative integers $`(k,j)`, one associates the irreducible representation
$`\rm det^{k}(\rm St) \otimes {\rm Sym}^j(\rm St),`
where $`\rm St` denotes the standard $`2`-dimensional representation of $`\rm \GL(2,\C)`.
The pair $`(k,j)` is called its weight, and when $`j = 0`, the integer $`k` is called the weight. Note that the highest weight of this representation is $`(j+k,k)`.

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[]
:::

:::definition "mf.siegel.weight_k_j" (lean := "SiegelUpperHalfSpace.rhoKJ, SiegelUpperHalfSpace.modularFormsKJ")
*Weight.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/mf.siegel.weight_k_j))

The *weight* of a {bpref "mf.siegel"}[Siegel modular form] $`f` of {bpref "mf.siegel.degree"}[degree] 2 is the pair of non-negative integers
that occurs in the modular transformation property of $`f` under the action of $`\gamma = \left( \begin{array}{ll}  a & b \\ c & d \end{array}\right)` on the {bpref "mf.siegel.halfspace"}[Siegel upper half space $`\mathcal{H}_2`].  That is, the weight is the numbers $`(k,j)` in the transformation law

$$`f\left( (a \tau + b)(c \tau + d)^{-1} \right) = \det(c \tau + d)^k {\rm Sym}^j(c \tau + d) f(\tau) .`

Depends on: {uses "mf.siegel"}[] {uses "mf.siegel.degree"}[]
:::

:::definition "paramodulargroup.sp2gr" (lean := "SymplecticGroup.paramodularGL, SymplecticGroup.paramodular, SymplecticGroup.paramodularForm, SymplecticGroup.paramodularDelta")
*Paramodular group in degree g.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/paramodulargroup.sp2gr))

A paramodular group $`\Gamma` of degree $`g` preserves
an integral alternating $`2g \times 2g` matrix
$`T=\left( \begin{array}{ll}  0 & d \\ -d & 0 \end{array}\right)`
for $`d=\mathrm{diag}(d_1,d_2,\dots,d_g)` with $`d_j\mid d_{j+1}` for $`1\leqslant j \leqslant g-1`:
$`\Gamma=\left\{\gamma \in \GL(2g,\mathbb{Z})\, : \, \gamma^t T \gamma=T\right\}.`
For $`\delta= \left( \begin{array}{ll}  1_g & 0 \\ 0 & d \end{array}\right)`, the conjugate $`\Gamma^{\mathrm{para}}(d)=\delta\Gamma\delta^{-1}\subseteq \mathrm{Sp}(2g,\Q)` is also referred to as a paramodular group.

In degree $`2`,
{bpref "group.paramodular"}[$`K(N)`]$`= \Gamma^{\mathrm{para}}(1,N)`.

Depends on: {uses "group.paramodular"}[]
:::

:::definition "repn.highest.weight"
*Highest weight of an irreducible representation of $`\GL(g,\C)`..* ([LMFDB](https://beta.lmfdb.org/knowledge/show/repn.highest.weight))

Let $`\rho\colon \GL(g,\C)\to \GL(V)` be a finite-dimensional irreducible representation  Then there exists a unique $`1`-dimensional subspace $`\langle v_0 \rangle` of $`V`
and a unique $`g`-tuple of integers $`(\lambda_1 \geqslant\lambda_2 \geqslant \ldots \geqslant \lambda_g)` such that
$`\rho(\mathrm{diag}(a_1,\ldots,a_g))\,v_0=\prod_{i=1}^{g}a_i^{\lambda_i}\, v_0`.
The $`g`-tuple of integers $`(\lambda_1,\lambda_2, \ldots, \lambda_g)` is called *the highest weight* of $`\rho`.

For example the $`1`-dimensional representation of $`\GL(g,\C)` given by the determinant has highest weight $`(1,\ldots,1)` while the standard $`g`-dimensional representation
has highest weight $`(1,0,\ldots,0)`.
:::

:::definition "repn.irrep.gl"
*Irreducible representations of $`\GL(g,\C)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/repn.irrep.gl))

The irreducible finite-dimensional representations of $`\GL(g,\C)` correspond bijectively to the $`g`-tuples of integers $`(\lambda_1,\ldots,\lambda_g)` with
$`\lambda_1\geqslant \lambda_2\geqslant\ldots\geqslant \lambda_g` called
{bpref "repn.highest.weight"}[highest weight of the representation].

Depends on: {uses "repn.highest.weight"}[]
:::
