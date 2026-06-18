import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Modular forms" =>

This chapter lists the LMFDB definitions relating to *modular forms*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "cmf"
*Classical modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf))

Let $`k` be a positive integer and let $`\Gamma` be a finite index subgroup of the {bpref "group.sl2z"}[modular group] $`\SL(2,\Z)`.

A (classical) *modular form* $`f` of  {bpref "cmf.weight"}[weight] $`k` on $`\Gamma`,  is a holomorphic function defined on the {bpref "mf.upper_half_plane"}[upper half plane] $`\mathcal{H}`, which satisfies the transformation property

$$`f(\gamma z) = (cz+d)^k f(z)`

for all $`z\in\mathcal{H}` and $`\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in \Gamma` and is holomorphic  at all the {bpref "group.fuchsian.cusps"}[cusps] of $`\Gamma`.

If $`\Gamma` contains the principal congruence subgroup $`\Gamma(N)` then $`f` is said to be a modular form of {bpref "cmf.level"}[level] $`N`.

For each fixed choice of $`k` and $`\Gamma` the set of modular forms of weight $`k` on $`G` form a finite-dimensional $`\mathbb{C}`-vector space denoted $`M_k(\Gamma)`.

For the congruence subgroup $`\Gamma_1(N)` the space $`M_k(\Gamma_1(N))` decomposes as a direct sum of subspaces $`M_k(N,\chi)` over the group of {bpref "character.dirichlet"}[Dirichlet characters] $`\chi` of modulus $`N`, where $`M_k(N,\chi)` is the subspace of forms $`f\in M_k(N)` that satisfy

$$`f(\gamma z) = \chi(d)(cz+d)^k f(z)`

for all $`\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}` in $`\Gamma_0(N)`.

Elements of $`M_k(N,\chi)` are said to be modular forms of weight $`k`, level $`N`, and character $`\chi`.

For trivial character $`\chi` of modulus $`N` we have $`M_k(N,\chi)=M_k(\Gamma_0(N))`.

Depends on: {uses "character.dirichlet"}[] {uses "group.fuchsian.cusps"}[] {uses "group.sl2z"}[] {uses "mf.upper_half_plane"}[]
:::

:::definition "cmf.analytic_conductor"
*Analytic conductor of a classical newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.analytic_conductor))

The *analytic conductor* of a {bpref "cmf.newform"}[newform] $`f \in S_k^{\mathrm{new}}(N,\chi)` is the positive real number

$$`N\left(\frac{\exp(\psi(k/2))}{2\pi}\right)^2,`

where $`\psi(x):=\Gamma'(x)/\Gamma(x)` is the logarithmic derivative of the Gamma function.

Depends on: {uses "cmf.newform"}[]
:::

:::definition "cmf.analytic_rank"
*Analytic rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.analytic_rank))

The *analytic rank* of a {bpref "cmf.cusp_form"}[cuspidal modular form] $`f` is the {bpref "lfunction.analytic_rank"}[analytic rank] of the L-function

$$`L(f,s) = \sum_{n\ge 1} a_nn^{-s}`

where the $`a_n` are the complex coefficients that appear in the {bpref "cmf.q-expansion"}[$`q`-expansion] of the modular form: $`f(z)=\sum_{n\ge 1}a_nq^n`, where $`q=e^{2\pi i z}`.

The complex coefficients $`a_n` depend on a choice of embedding of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f` into the complex numbers.  It is conjectured that the analytic rank does not depend on this choice, and this conjecture has been verified for all classical modular forms stored in the LMFDB.

In general, analytic ranks of L-functions listed in the LMFDB are upper bounds that are believed (but not proven) to be tight.

For modular forms, the analytic ranks listed in the LMFDB are provably correct whenever the listed analytic rank is 0, or the listed analytic rank is 1 and the modular form is {bpref "cmf.selfdual"}[self dual] (in the self dual case the sign of the functional equation determines the parity of the analytic rank).

Depends on: {uses "cmf.coefficient_field"}[] {uses "cmf.cusp_form"}[] {uses "cmf.q-expansion"}[] {uses "cmf.selfdual"}[] {uses "lfunction.analytic_rank"}[]
:::

:::definition "cmf.artin_field"
*Artin field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.artin_field))

The *Artin field* of a {bpref "cmf.weight"}[weight] one {bpref "cmf.newform"}[newform] is the number field fixed by the kernel of its associated {bpref "cmf.galois_representation"}[Galois representation] $`\rho\colon \Gal(\overline{\Q}/\Q)\to \GL_2(\C)`.

This number field is typically identified as the Galois closure of a {bpref "nf.sibling"}[sibling subfield] with minimal degree and absolute discriminant.

Depends on: {uses "cmf.galois_representation"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[] {uses "nf.sibling"}[]
:::

:::definition "cmf.artin_image"
*Artin image.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.artin_image))

The *Artin image* of a {bpref "cmf.weight"}[weight] one {bpref "cmf.newform"}[newform] is the image of its associated {bpref "cmf.galois_representation"}[Galois representation] $`\rho\colon \Gal(\overline{\Q}/\Q)\to \GL_2(\C)`.

The Artin image is a finite subgroup of $`\GL_2(\C)` whose cardinality is equal to the degree of the {bpref "cmf.artin_field"}[Artin field].

Depends on: {uses "cmf.artin_field"}[] {uses "cmf.galois_representation"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.atkin-lehner"
*Atkin-Lehner involution $`w_Q`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.atkin-lehner))

Let $`N` be a positive integer, and let $`Q` be a positive divisor of $`N` satisfying $`\gcd(Q,N/Q)=1`.  Then there exist $`x,y,z,t \in \Z` for which the matrix

$$`W_Q=\left( \begin{matrix} Qx & y \\ Nz & Qt\end{matrix} \right)`

has determinant $`Q`. The matrix $`W_Q` normalizes the group $`\Gamma_0(N)`, and for any {bpref "cmf.weight"}[weight] $`k` it induces a linear operator $`w_Q` on the space of {bpref "cmf.cusp_form"}[cusp forms]  $`S_k(\Gamma_0(N))` that commutes with the {bpref "cmf.hecke_operator"}[Hecke operators] $`T_p` for all $`p \nmid Q` and acts as its own inverse.

The linear operator $`w_Q` does not depend on the choice of $`x,y,z,t` and is called the *Atkin-Lehner involution* of $`S_k(\Gamma_0(N))`.  Any cusp form $`f` in $`S_k(\Gamma_0(N))` which is an eigenform for all $`T_p` with $`p \nmid N` is also an eigenform for $`w_Q`, with eigenvalue $`\pm 1`.

The matrix $`W_Q` induces an automorphism of the modular curve $`X_0(N)` that is also denoted $`w_Q`.

In the case $`Q=N`, the Atkin-Lehner involution $`w_N` is also called the {bpref "cmf.fricke"}[Fricke involution].

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.bad_prime"
*Bad prime.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.bad_prime))

A *bad prime* for a {bpref "cmf"}[modular form] $`f` is a prime dividing the {bpref "cmf.level"}[level] of $`f`.

A *good prime* is a prime that is not a bad prime.  In other words, a prime that
does not divide the level.

Depends on: {uses "cmf"}[] {uses "cmf.level"}[]
:::

:::definition "cmf.character"
*Character of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.character))

The *character* of an {bpref "cmf"}[elliptic modular form] $`f`
of weight $`k` for the group $`\Gamma`  is the {bpref "character.dirichlet"}[Dirichlet character] $`\chi` that appears in its transformation under the action of the defining group $`\Gamma`.  Namely,

$$`f(\gamma z) = \chi(d)(cz+d)^k f(z)`

for any $`z\in\mathcal{H}` and $`\gamma = \begin{pmatrix} * & * \\ c & d  \end{pmatrix}\in\Gamma`.  Here $`\Gamma` is a subgroup of $`\rm{SL}_2(\mathbb{Z})` containing the principal congruence subgroup $`\Gamma(N)`, and $`\chi` is a character mod $`N`.

Depends on: {uses "character.dirichlet"}[] {uses "cmf"}[]
:::

:::definition "cmf.cm_form"
*CM form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.cm_form))

A {bpref "cmf"}[classical modular form] is said to have *complex multiplication* if it admits a {bpref "cmf.self_twist"}[self twist] by the Kronecker character of an imaginary quadratic field.

Depends on: {uses "cmf"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.coefficient_field"
*Coefficient field for newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.coefficient_field))

The *coefficient field* of a modular form is the subfield of $`\C` generated by the coefficients $`a_n` of its $`q`-expansion $`\sum a_nq^n`.  The space of {bpref "cmf.cusp_form"}[cusp forms] $`S_k^\mathrm{new}(N,\chi)` has a basis of modular forms that are simultaneous eigenforms for all {bpref "cmf.hecke_operator"}[Hecke operators] and with algebraic {bpref "cmf.fouriercoefficients"}[Fourier coefficients].  For such eigenforms the coefficient field will be a number field, and Galois conjugate eigenforms will share the same coefficient field.  Moreover, if $`m` is the smallest positive integer such that the values of the character $`\chi` are contained in the cyclotomic field $`\Q(\zeta_m)`, the coefficient field will contain $`\Q(\zeta_m)`
For eigenforms, the coefficient field is also known as the *Hecke field*.

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.hecke_operator"}[]
:::

:::definition "cmf.coefficient_ring"
*Coefficient ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.coefficient_ring))

The *coefficient ring* of a modular form is the subring $`\Z[a_1,a_2,a_3,\ldots]` of $`\C` generated by the coefficients $`a_n` of its $`q`-expansion $`\sum a_nq^n`.  In the case of a {bpref "cmf.newform"}[newform] the coefficients $`a_n` are algebraic integers and the coefficient ring is a finite index subring of the ring of integers of the {bpref "cmf.coefficient_field"}[coefficient field] of the newform.
It is also known as the *Hecke ring*, since the $`a_n` are eigenvalues of Hecke operators.

Depends on: {uses "cmf.coefficient_field"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.congruence_subgroup"
*Congruence subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.congruence_subgroup))

A *congruence subgroup* $`\Gamma` of $`\SL_2(\Z)` is a subgroup that contains a *principal congruence subgroup* $`\Gamma(N) := \ker \left( \operatorname{SL}_2(\mathbb{Z}) \to \operatorname{SL}_2(\mathbb{Z}/N\mathbb{Z}) \right)` for some $`N\ge 1`.  The least such $`N` is the *level* of $`\Gamma`.
:::

:::definition "cmf.cusp_form"
*Cuspidal modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.cusp_form))

Let $`k` be a positive integer and let $`\Gamma` be a finite index subgroup of the {bpref "group.sl2z"}[modular group] $`\SL(2,\Z)`.

A *cusp form* of {bpref "cmf.weight"}[weight] $`k` on $`\Gamma` is a {bpref "cmf"}[modular form] $`f\in M_k(\Gamma)` that vanishes at all {bpref "group.fuchsian.cusps"}[cusps] of $`\Gamma`.  In particular, the constant term in the {bpref "cmf.fouriercoefficients"}[Fourier expansion] of $`f` about any cusp is zero.

The cusp forms in $`M_k(\Gamma)` form a subspace $`S_k(\Gamma)`.  For each {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of modulus $`N` the cusp forms in {bpref "cmf"}[$`M_k(N,\chi)`] form a subspace $`S_k(N,\chi)`; these are the cusp forms of weight $`k`, level $`N`, and character $`\chi`.

Depends on: {uses "character.dirichlet"}[] {uses "cmf"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.weight"}[] {uses "group.fuchsian.cusps"}[] {uses "group.sl2z"}[]
:::

:::definition "cmf.decomposition.new.gamma0chi"
*Decomposition into newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.decomposition.new.gamma0chi))

The {bpref "cmf.hecke_operator"}[Hecke algebra] acts on $`S_k^{\mathrm{new}}(N, \chi)`, breaking it up into irreducible pieces.  Each piece is spanned by a set of conjugate eigenforms with Fourier coefficients in a number field of degree equal to the dimension of the subspace.  We refer to an irreducible orbit as a *{bpref "cmf.newform"}[newform]*.

Depends on: {uses "cmf.hecke_operator"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.defining_polynomial"
*Defining polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.defining_polynomial))

The {bpref "cmf.coefficient_field"}[coefficient field of a modular form] is a {bpref "nf"}[number field]. A *defining polynomial* for this number field is explicitly recorded, because some of the data associated to the modular form will be expressed in terms of roots of this polynomial.

Depends on: {uses "cmf.coefficient_field"}[] {uses "nf"}[]
:::

:::definition "cmf.dimension"
*Dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.dimension))

The *dimension* of a space of modular forms is its dimension as a complex vector space; for spaces of newforms $`S_k^{\rm new}(N,\chi)` this is the same as the dimension of the $`\Q`-vector space spanned by its eigenforms.

The *dimension* of a {bpref "cmf.newform"}[newform] refers to the dimension of its {bpref "cmf.newform_subspace"}[newform subspace], equivalently, the cardinality of its {bpref "cmf.galois_orbit"}[newform orbit].  This is equal to the degree of its coefficient field (as an extension of $`\Q`).

The *relative dimension* of $`S_k^{\rm new}(N,\chi)`  is its dimension as a $`\Q(\chi)`-vector space, where $`\Q(\chi)` is the field generated by the values of $`\chi`, and similarly for newform subspaces.

Depends on: {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "cmf.newform_subspace"}[]
:::

:::definition "cmf.distinguishing_primes"
*Distinguishing Hecke operators.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.distinguishing_primes))

For a {bpref "cmf.newspace"}[newspace] $`S^\mathrm{new}_k(N,\chi)` we say that a set of {bpref "cmf.hecke_operator"}[Hecke operators] $`\mathcal T:=\{T_{p_1},\ldots,T_{p_r}\}` *distinguishes* the {bpref "cmf.newform"}[newforms] in the space if the sets $`X_f(\mathcal T)` of characteristic polynomials of the $`T_p\in \mathcal T` acting on the subspace $`V_f` spanned by the {bpref "cmf.galois_orbit"}[Galois orbit] of $`f` in $`S_k^\mathrm{new}(N,\chi)` are distinct as $`f` ranges over (non-conjugate) newforms in $`S_k^\mathrm{new}(N,\chi)`.

The set $`\mathcal T` can be identified by a list of primes $`p`.  For convenience we restrict to primes $`p` that do not divide the level $`N` and list the unique ordered sequence of primes $`p_1,\ldots,p_n` for which the sequence of integers $`c_1,\ldots,c_n` defined by

$$`c_m := \#\bigl\{X_f(\{T_{p_i}:i < m\}): \mathrm{newforms}\ f\in S_k^\mathrm{new}(N,\chi)\bigr\}`

is strictly increasing.  The length of the sequence $`p_1,\ldots p_n` is always less then the number of newforms in $`S_k^\mathrm{new}(N,\chi)` and we obtain the empty sequence when $`S_k^\mathrm{new}(N,\chi)` contains just one newform.

Depends on: {uses "cmf.galois_orbit"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.dualform"
*Dual cuspform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.dualform))

The *dual* of a {bpref "cmf.cusp_form"}[cuspidal modular form] $`f` is the form whose coefficients $`a_n` in its {bpref "cmf.q-expansion"}[$`q`-expansion] are the complex conjugates of those of $`f`.  The L-function of the dual form is the {bpref "lfunction.dual"}[dual] of the L-function of $`f`.

The {bpref "cmf.coefficient_field"}[coefficient field] of a {bpref "cmf.selfdual"}[non-self-dual] {bpref "cmf.newform"}[newform] is a {bpref "nf.cm_field"}[CM field].

Depends on: {uses "cmf.coefficient_field"}[] {uses "cmf.cusp_form"}[] {uses "cmf.newform"}[] {uses "cmf.q-expansion"}[] {uses "cmf.selfdual"}[] {uses "lfunction.dual"}[] {uses "nf.cm_field"}[]
:::

:::definition "cmf.eisenstein"
*Holomorphic Eisenstein series of level 1.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.eisenstein))

For an even integer $`k\geq4`, we define the (normalized) holomorphic *Eisenstein series* of level 1

$$`E_k(z)=\frac{1}{2\zeta(k)}\sum_{(c,d)\ne(0,0)}(cz+d)^{-k}=\sum_{\left(\begin{matrix} a&b\\c&d \end{matrix}\right)\in\ \Gamma_{\infty}\setminus \SL(2,\Z)
}(cz+d)^{-k},`

 where $`\Gamma_z=\{\gamma\in\Gamma: \gamma z=z\}` is the
*isotropy group* of the cusp $`z`.

The Eisenstein series $`E_k` are {bpref "cmf"}[modular forms] of {bpref "cmf.weight"}[weight] $`k` and {bpref "cmf.level"}[level] $`1` on the {bpref "group.sl2z"}[modular group].

They have the following {bpref "cmf.q-expansion"}[$`q`-expansion]:

$$`E_k(z)=1-\frac{2k}{B_k}\sum_{n\geq1}\sigma_{k-1}(n)q^n,`

where the $`B_k` are the {bpref "af.bernoulli_numbers"}[Bernoulli numbers],  $`\sigma_{k-1}(n)` is a {bpref "af.divisor_function"}[divisor function],
and $`q=e^{2 \pi i z}`.

Depends on: {uses "af.bernoulli_numbers"}[] {uses "af.divisor_function"}[] {uses "cmf"}[] {uses "cmf.level"}[] {uses "cmf.q-expansion"}[] {uses "cmf.weight"}[] {uses "group.sl2z"}[]
:::

:::definition "cmf.eisenstein_form"
*Holomorphic Eisenstein modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.eisenstein_form))

Let $`k` be a positive integer and let $`\Gamma` be a finite index subgroup of the {bpref "group.sl2z"}[modular group] $`\SL(2,\Z)`.

the *Eisenstein subspace* $`E_k(\Gamma)` is the orthogonal complement in {bpref "cmf"}[$`M_k(\Gamma)`] to the subspace {bpref "cmf.cusp_form"}[$`S_k(\Gamma)`] under the {bpref "cmf.petersson_scalar_product"}[Petersson inner product].

An *Eisenstein form* of {bpref "cmf.weight"}[weight] $`k` on $`\Gamma` is a {bpref "cmf"}[modular form] $`f\in E_k(\Gamma)`. For each {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of modulus $`N` the Eisenstein forms in {bpref "cmf"}[$`M_k(N,\chi)`] form a subspace $`E_k(N,\chi)`; these are the Eisenstein forms of weight $`k`, level $`N`, and character $`\chi`.

The space $`E_k(N, \chi)` is spanned by the {bpref "cmf.eisenstein_series"}[$`E_k^{\chi_1, \chi_2}(d \\tau)`] where $`\chi_1 \chi_2 = \chi` and $`d N_1 N_2 \mid N`, unless $`k = 2` and $`\chi = 1`, in which case $`E_2^{1,1}(d \tau)` is not holomorphic, and is replaced by $`E_2^{1,1}(\tau) - d E_2^{1,1}(d \tau)`.

Depends on: {uses "character.dirichlet"}[] {uses "cmf"}[] {uses "cmf.cusp_form"}[] {uses "cmf.eisenstein_series"}[] {uses "cmf.petersson_scalar_product"}[] {uses "cmf.weight"}[] {uses "group.sl2z"}[]
:::

:::definition "cmf.eisenstein_label"
*Label of a classical Eisenstein modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.eisenstein_label))

The *label* of an {bpref "cmf.eisenstein_newform"}[Eisenstein newform] $`f\in E_k^{\rm new}(N,\chi)` has the format $`N.k.E.a.x`, where

- $`N` is the {bpref "cmf.level"}[level];

- $`k` is the {bpref "cmf.weight"}[weight];

- $`N.a` is the {bpref "character.dirichlet.galois_orbit_label"}[label] of the {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi`;

- $`x` is the label of the {bpref "cmf.galois_orbit"}[Galois orbit] of the newform $`f`.

For each {bpref "cmf.embedding"}[embedding] of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f` into the complex numbers, the corresponding modular form over $`\C` has a label of the form $`N.k.E.a.x.n.i`, where

- $`n` determines the Conrey label $`N.n` of the Dirichlet character $`\chi`;

- $`i` is an integer ranging from 1 to the {bpref "cmf.relative_dimension"}[relative dimension] of the newform that distinguishes embeddings with the same character $`\chi`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_label"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.eisenstein_newform"}[] {uses "cmf.embedding"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.level"}[] {uses "cmf.relative_dimension"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.eisenstein_newform"
*Eisenstein newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.eisenstein_newform))

An *Eisenstein newform* is an Eisenstein form $`f\in E_k^{\rm new}(N,\chi)` in the {bpref "cmf.eisenstein_newspace"}[Eisenstein new subspace] that is also an eigenform of all {bpref "cmf.hecke_operator"}[Hecke operators], normalized so that the {bpref "cmf.fouriercoefficients"}[$`q`-expansion]  $`f(z)=\sum a_n q^n`, where $`q=e^{2\pi i z}`, has coefficient $`a_1=1`.  The Eisenstein newforms are a basis for the Eisenstein new subspace.

Depends on: {uses "cmf.eisenstein_newspace"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.hecke_operator"}[]
:::

:::definition "cmf.eisenstein_newspace"
*New Eisenstein subspace.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.eisenstein_newspace))

The space $`E_k(N,\chi)` of {bpref "cmf.eisenstein_form"}[Eisenstein] {bpref "cmf"}[modular forms] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k`, and {bpref "cmf.character"}[character] $`\chi` can be decomposed

$$`E_k(N,\chi) = E_k^{\rm old}(N,\chi) \oplus E_k^{\rm new}(N,\chi)`

into old and new subspaces, defined as follows.

If $`M` is a proper divisor of $`N` and $`\chi_M` is a {bpref "character.dirichlet"}[Dirichlet character] of {bpref "character.dirichlet.modulus"}[modulus] $`M` that {bpref "character.dirichlet.induce"}[induces] $`\chi`, then for all $`d \mid (N/M)`, there is a map from $`E_k(M,\chi_M) \to E_k(N,\chi)` via $`f(z) \mapsto f(dz)`.  The span of the images of all of these maps is the *old subspace* $`E_k^{\rm old}(N,\chi) \subseteq E_k(N,\chi)`.

The *new subspace* $`E_k^{\rm new}(N,\chi)` is the subspace spanned by the {bpref "cmf.eisenstein_newform"}[newforms] {bpref "cmf.eisenstein_series"}[$`E_k^{\chi_1, \chi_2}(\\tau)`] such that $`\chi_1 \chi_2 = \chi` and $`N_1 N_2 = N`, unless $`k = 2` and $`\chi = 1`, in which case $`E_2^{\rm new}(N) = 0` when $`N` is not a prime, and when $`N = p` is prime it is spanned by $`E_2^{1,1}(\tau) - p E_2^{1,1}(p \tau)`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[] {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.eisenstein_form"}[] {uses "cmf.eisenstein_series"}[] {uses "cmf.level"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.eisenstein_series"
*Holomorphic Eisenstein series.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.eisenstein_series))

Let $`k, N_1, N_2` be positive integers, and let $`\chi_1, \chi_2` be {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet"}[Dirichlet characters] modulo $`N_1` and $`N_2` respectively.

The *Eisenstein series* of {bpref "cmf.weight"}[weight] $`k` associated to $`\chi_1` and $`\chi_2` is

$$`E_{k}^{\chi_1, \chi_2}(\tau) = \frac{1}{2} \left ( \delta_{\chi_1=1} L(1-k, \chi_2) + \delta_{k=1} \delta_{\chi_2=1} L(0,\chi_1) \right) + \sum_{n=1}^{\infty} \sigma_{k-1}^{\chi_1, \chi_2}(n) q^n,`

where $`q = e^{2 \pi i \tau}`, $`L(s,\chi_i)` is the Dirichlet $`L`-function associated to $`\chi_i`, and

$$`\sigma_{k-1}^{\chi_1, \chi_2}(n) = \sum_{m \mid n} \chi_1(n/m) \chi_2(m) m^{k-1}.`

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.embedding"
*Embedding of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.embedding))

The coefficients in the {bpref "cmf.q-expansion"}[$`q`-expansion] $`\sum a_nq^n` of a {bpref "cmf.q-expansion"}[newform] $`f` are algebraic integers that generate the {bpref "cmf.coefficient_field"}[coefficient field] $`\Q(f)` of $`f`.

Each {bpref "nf.embedding"}[embedding] $`\iota\colon \Q(f)\to \C` gives rise to a modular form $`\iota(f)` with $`q`-expansion $`\sum \iota(a_n)q^n`; the modular form $`\iota(f)` is an *embedding* of the newform $`f`.

Distinct embeddings give rise to modular forms  that lie in the same {bpref "cmf.galois_orbit"}[galois orbit] but have distinct {bpref "lfunction"}[$`L`-functions] $`L(s):=\sum \iota(a_n)n^{-s}`.

If $`f` is a newform of {bpref "cmf.character"}[character] $`\chi`, each embedding $`\Q(f)\to \C` induces an embedding $`\Q(\chi)\to \C` of the {bpref "character.dirichlet.value_field"}[value field] of $`\chi`.  The embeddings of $`f` may be grouped into blocks with the same {bpref "character.dirichlet"}[Dirichlet character]; distinct blocks correspond to modular forms with distinct (but Galois conjugate) Dirichlet characters.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.value_field"}[] {uses "cmf.character"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.q-expansion"}[] {uses "lfunction"}[] {uses "nf.embedding"}[]
:::

:::definition "cmf.embedding_label"
*Complex embedding label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.embedding_label))

The *label* complex embedded holomorphic {bpref "cmf.cusp_form"}[cusp form] $`f` is $`N.k.a.x.c.j` (sometimes shortened as $`a.j` ), where

- $`N` is the {bpref "cmf.level"}[level],

- $`k` is the {bpref "cmf.weight"}[weight],

- $`N.a` is the {bpref "character.dirichlet.galois_orbit_label"}[label] of the Galois orbit of the Dirichlet character,

- $`x` is the Hecke Galois orbit label,

- $`N.c` is the Conrey label for the character corresponding to the {bpref "cmf.embedding"}[embedding], and

- $`j` is the index for the embedding within those with the same Dirichlet character, these are ordered by the vector $`\iota(a_n)`, where we order the complex numbers first by their real part and then by their imaginary part.

Depends on: {uses "character.dirichlet.galois_orbit_label"}[] {uses "cmf.cusp_form"}[] {uses "cmf.embedding"}[] {uses "cmf.level"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.eta_quotient"
*Eta quotient.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.eta_quotient))

An *eta quotient* is any function $`f` of the form

$$`f(z)=\prod_{1\leq i\leq s}\eta^{r_i}(m_iz),`

where $`m_i\in\mathbb{N}` and $`r_i\in\mathbb{Z}` and $`\eta(z)` is the {bpref "mf.half_integral_weight.dedekind_eta"}[Dedekind eta function].

An *eta product* is an eta quotient in which all the $`r_i` are non-negative.

Depends on: {uses "mf.half_integral_weight.dedekind_eta"}[]
:::

:::definition "cmf.fouriercoefficients"
*Fourier coefficients of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.fouriercoefficients))

Let $`f` be a {bpref "cmf"}[modular form] on a finite index subgroup $`\Gamma` of $`\SL_2(\Z)`,
and suppose $`\Gamma` contains the matrix $`T:=\left(\begin{matrix}1&1\\0&1\end{matrix}\right)`.
Then $`f` is periodic with period 1, so it has a Fourier expansion of the form

$$`f(z)=\sum_{n\ge 0}a_n q^n ,`

where $`q=e^{2 \pi i z}`.  That is the *Fourier expansion* of $`f` around the cusp $`\infty`, with *Fourier coefficients* $`a_n`.  If one says "the Fourier expansion of $`f`", is it understood to refer to
the expansion at $`\infty`.

For other cusps of $`\Gamma`, suppose $`w` is the {bpref "group.fuchsian.cusps.width"}[width] of the cusp $`\gamma\infty`, for some {bpref "group.fuchsian.cusps"}[cusp] representative $`\gamma`.
Then we can write $`f` as $`f(z)=g_{\gamma}(e^{2\pi iz/w})` for some holomorphic function $`g_{\gamma}` on the punctured unit disk. We can expand $`g` as a Laurent series:

$$`g_{\gamma}(q^{1/w})=\sum_{n\geq0}a_{\gamma}(n)q^{n/w}\quad\text{for}\quad0<|q|<1.`

We then define the *Fourier expansion* of $`f` around the cusp $`\gamma\infty` to be

$$`f(z)=\sum_{n \geq0}a_{\gamma}(n)q^{n/w},`

where $`q=e^{2\pi iz}`.

The $`a_{\gamma}(n)` are called the *Fourier coefficients* of $`f` with respect to the cusp $`\gamma\infty`.

Depends on: {uses "cmf"}[] {uses "group.fuchsian.cusps"}[] {uses "group.fuchsian.cusps.width"}[]
:::

:::definition "cmf.fricke"
*Fricke involution.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.fricke))

The *Fricke involution* is the {bpref "cmf.atkin-lehner"}[Atkin-Lehner involution] $`w_N` on the space $`S_k(\Gamma_0(N))` (induced by the corresponding involution on the modular curve $`X_0(N)`).

For a newform $`f \in S_k^{\textup{new}}(\Gamma_0(N))`, the sign of the {bpref "lfunction.functional_equation"}[functional equation] satisfied by the {bpref "lfunction"}[L-function] attached to $`f` is $`i^{-k}` times the eigenvalue of $`\omega_N` on $`f`.  So, for example when $`k=2`, the signs swap, and the {bpref "cmf.analytic_rank"}[analytic rank] of $`f` is even when $`w_N f = -f` and odd when $`w_N f = +f`.

Depends on: {uses "cmf.analytic_rank"}[] {uses "cmf.atkin-lehner"}[] {uses "lfunction"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "cmf.galois_conjugate"
*Galois conjugate newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.galois_conjugate))

Two {bpref "cmf.newform"}[newforms] $`f=\sum a_nq^n` and $`g=\sum b_nq^n`  are *Galois conjugate* if there is an automorphism $`\sigma\in \Gal(\overline{\Q}/\Q)` such that $`b_n=\sigma(a_n)` for all $`n\ge 1`, in which case we write $`g=\sigma(f)`.

The set $`\{\sigma(f):\sigma\in\Gal(\overline{\Q}/\Q)\}` of all Galois conjugates of $`f` is the {bpref "cmf.galois_orbit"}[Galois orbit] of $`f`; it has cardinality equal to the {bpref "cmf.dimension"}[dimension] of $`f`, equivalently, the {bpref "nf.degree"}[degree] of its {bpref "cmf.coefficient_field"}[coefficient field]

Depends on: {uses "cmf.newform"}[] {uses "nf.degree"}[]
:::

:::definition "cmf.galois_orbit"
*Galois orbit of a newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.galois_orbit))

The *Galois orbit* of a {bpref "cmf.newform"}[newform] $`f\in S_k^{\rm new}(N,\chi)` is the finite set

$$`[f]:=\{\sigma(f):\sigma\in \mathrm{Gal}(\overline{\Q}/\Q)\}`

of its {bpref "cmf.galois_conjugate"}[Galois conjugates], which forms a canonical $`\Q`-basis for the corresponding {bpref "cmf.newform_subspace"}[newform subspace].

Galois orbits of newforms are also called *newform orbits*.

Depends on: {uses "cmf.galois_conjugate"}[] {uses "cmf.newform"}[] {uses "cmf.newform_subspace"}[]
:::

:::definition "cmf.galois_representation"
*Galois representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.galois_representation))

As shown by Deligne and Serre , every  {bpref "cmf.newform"}[newform] of {bpref "cmf.weight"}[weight] one has an associated *Galois representation* $`\rho\colon \Gal(\overline{\Q}/\Q)\to \GL_2(\C)`.

This representation corresponds to an {bpref "artin"}[Artin representation] of dimension two whose {bpref "artin.conductor"}[conductor] is the level $`N` of the modular form.

Conversely, every {bpref "artin.parity"}[odd] irreducible two-dimensional Artin representation of conductor $`N` gives rise to a modular form of weight one and level $`N`.

Composing the representation $`\rho` with the natural map $`\GL_2(\C)\to \PGL_2(\C)` yields the *projective Galois representation* $`\bar\rho\colon \Gal(\overline{\Q}/\Q)\to \PGL_2(\C)`.

Depends on: {uses "artin"}[] {uses "artin.conductor"}[] {uses "artin.parity"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.hecke_operator"
*Hecke operator.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.hecke_operator))

Let $`f` be a {bpref "cmf"}[modular form] of {bpref "cmf.weight"}[weight] $`k`, {bpref "cmf.level"}[level] $`N`, and {bpref "character.dirichlet"}[character] $`\chi`.

For each positive integer $`n` the *Hecke operator* $`T_n` is a linear operator on the vector space $`M_k(N,\chi)` whose action on $`f\in M_k(N,\chi)` can be defined as follows. If  $`f(z)=\sum a_n (f)q^n` is the {bpref "cmf.q-expansion"}[$`q`-expansion] of $`f\in M_k(N,\chi)`, where $`q=e^{2\pi i z}`, then the $`q`-expansion of $`T_nf\in M_k(N,\chi)` has coefficients

$$`a_m(T_nf) := \sum_{d|\gcd(m,n)}\chi(d)d^{k-1}a_{mn/d^2}(f).`

The Hecke operators pairwise commute, and when restricted to the subspace $`S_k(N,\chi)` of {bpref "cmf.cusp_form"}[cusp forms], they commute with their adjoints with respect to the {bpref "cmf.petersson_scalar_product"}[Petersson scalar product].  This implies that $`S_k(N,\chi)` has a canonical basis whose elements are eigenforms for all the Hecke operators.  If we normalize such an eigenform $`f(z)=\sum a_n q^n` so that $`a_1=1`, then for all $`n\ge 1` we have

$$`T_n f = a_nf.`

The {bpref "cmf.newspace"}[newspace] $`S_k^{\rm new}(N,\chi)\subseteq S_k(N,\chi)` is invariant under the action of the Hecke operators, so the canonical basis of normalized eigenforms for $`S_k(N,\chi)` includes a basis of {bpref "cmf.newform"}[newforms] for $`S_k^{\rm new}(N,\chi)`.

Depends on: {uses "character.dirichlet"}[] {uses "cmf"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.petersson_scalar_product"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.hecke_orbit"
*Hecke orbit.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.hecke_orbit))

The *Hecke orbit* of a {bpref "cmf.cusp_form"}[cusp form] $`f` in $`S_k(N,\chi)` is defined as the
space generated by $`T_p(f)` for all {bpref "cmf.hecke_operator"}[Hecke operators] $`T_p` for $`p` coprime to the {bpref "cmf.level"}[level].

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.level"}[]
:::

:::definition "cmf.hecke_ring_generators"
*Coefficient ring generator bound.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.hecke_ring_generators))

The *coefficient ring generator bound* of a {bpref "cmf.newform"}[newform] with {bpref "cmf.q-expansion"}[$`q`-expansion] $`\sum a_nq^n` is the least positive integer $`n` such that $`\Z[a_1,\ldots,a_n]` is the entire {bpref "cmf.coefficient_ring"}[coefficient ring] $`\Z[a_1,a_2,a_3,\ldots]`.

Depends on: {uses "cmf.coefficient_ring"}[] {uses "cmf.newform"}[] {uses "cmf.q-expansion"}[]
:::

:::definition "cmf.heckecharpolys"
*Hecke characteristic polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.heckecharpolys))

The *Hecke characteristic polynomial* of a {bpref "cmf.newform"}[newform] $`f` at a prime $`p` is the characteristic polynomial of the {bpref "cmf.hecke_operator"}[Hecke operator] $`T_p` acting on the {bpref "cmf.newform_subspace"}[newform subspace] $`V_f`.

Depends on: {uses "cmf.hecke_operator"}[] {uses "cmf.newform"}[] {uses "cmf.newform_subspace"}[]
:::

:::definition "cmf.inner_twist"
*Inner twist.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.inner_twist))

{bpref "cmf.galois_conjugate"}[Galois conjugate] {bpref "cmf.newform"}[newforms] $`f` and $`g` are *inner twists* if there is a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` such that

$$`a_p(g) = \chi(p)a_p(f)`

for all but finitely many primes $`p`.  Without loss of generality, we may assume that $`\chi` is a {bpref "character.dirichlet.primitive"}[primitive] Dirichlet character, and by a theorem of Ribet , the newform $`g` is conjugate to $`f` via a $`\Q`-automorphism $`\sigma` of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f`.  The set of pairs $`(\chi,\sigma)` form the group of inner twists of $`f`.

Each pair $`(\chi,\sigma)` corresponding to an inner twist of $`f` is uniquely determined by the the primitive character $`\chi`, and we say that $`f` admits an inner twist by $`\chi`.  When $`\sigma=1` is is the trivial automorphism, we have $`g=f` and say that $`f` admits a {bpref "cmf.self_twist"}[self twist] by $`\chi`; in this case $`\chi` is either the trivial character or the Kronecker character of a quadratic field.

The {bpref "cmf.inner_twist_count"}[number] of inner twists of $`f` is an invariant of its {bpref "cmf.galois_orbit"}[Galois orbit], as is the number of inner twists by characters in any particular {bpref "character.dirichlet.galois_orbit"}[Galois orbit of Dirichlet characters].

The home page of each newform in the LMFDB includes a list of inner twists, in which non-trivial self twists are distinguished by listing the associated quadratic field (the {bpref "cmf.cm_form"}[CM] or {bpref "cmf.rm_form"}[RM] field), while inner twists that are not self twists are simply marked as "inner".

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.cm_form"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.galois_conjugate"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "cmf.rm_form"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.inner_twist_count"
*Inner twist count.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.inner_twist_count))

The *inner twist count* of a {bpref "cmf.newform"}[newform] $`f` is the number of distinct {bpref "cmf.inner_twist"}[inner twists] of $`f`.

Associated to each inner twist is a pair $`(\chi,\sigma)`, where $`\chi` is a primitive {bpref "character.dirichlet"}[Dirichlet character] and $`\sigma` is a $`\Q`-automorphism of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f`.

Pairs with $`\sigma=1` are {bpref "cmf.self_twist"}[self twists] $`(\chi,1)`, including the pair $`(1,1)` corresponding to the twist of $`f` by the trivial character; self twists are included in the count of inner twists.

The set of pairs $`(\chi,\sigma)` forms the group of inner twists; the inner twist count is the cardinality of this group.

Not all of the inner twists included in the inner twist count have necessarily been proved; those that have are explicitly identified in the table of inner twists on the newforms home page.  In cases where not every inner twist has been proved the inner twist should be viewed as a rigorous upper bound that is believed to be tight.

Inner twist data is available only for newforms for which exact eigenvalue data has been computed; this includes all newforms of {bpref "cmf.dimension"}[dimension] up to $`20` and all newforms of {bpref "cmf.weight"}[weight] 1; when the inner twist count is specified in a search the results include only newforms for which inner twists have been computed.

Depends on: {uses "character.dirichlet"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.dimension"}[] {uses "cmf.inner_twist"}[] {uses "cmf.newform"}[] {uses "cmf.self_twist"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.inner_twist_multiplicity"
*Inner twist multiplicity.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.inner_twist_multiplicity))

It is possible for a {bpref "cmf.newform"}[newform] $`f` to admit an {bpref "cmf.inner_twist"}[inner twist] by more than one {bpref "character.dirichlet"}[Dirichlet character] $`\varphi` in the same {bpref "character.dirichlet.galois_orbit"}[Galois orbit].  Different {bpref "cmf.embedding"}[embeddings] of $`f` into $`\C` will yield different $`\varphi`, but the number of such $`\varphi` is the same for every embedding; this number is the *multiplicity*.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "cmf.embedding"}[] {uses "cmf.inner_twist"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.label"
*Label of a classical modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.label))

The *label* of a {bpref "cmf.newform"}[newform] $`f\in S_k^{\rm new}(N,\chi)` has the format $`N.k.a.x`, where

- $`N` is the {bpref "cmf.level"}[level];

- $`k` is the {bpref "cmf.weight"}[weight];

- $`N.a` is the {bpref "character.dirichlet.galois_orbit_label"}[label] of the {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi`;

- $`x` is the label of the {bpref "cmf.galois_orbit"}[Galois orbit] of the newform $`f`.

For each {bpref "cmf.embedding"}[embedding] of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f` into the complex numbers, the corresponding modular form over $`\C` has a label of the form $`N.k.a.x.n.i`, where

- $`n` determines the Conrey label $`N.n` of the Dirichlet character $`\chi`;

- $`i` is an integer ranging from 1 to the {bpref "cmf.relative_dimension"}[relative dimension] of the newform that distinguishes embeddings with the same character $`\chi`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_label"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.embedding"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.relative_dimension"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.labels"
*Label of a classical modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.labels))

The *label* of a $`f\in M_k^{\\rm new}(N,\chi)` has the format $`N.k.A.a.x`, where

- $`N` is the {bpref "cmf.level"}[level];

- $`k` is the {bpref "cmf.weight"}[weight];

- $`N.a` is the {bpref "character.dirichlet.galois_orbit_label"}[label] of the {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi`;

- $`A` is a character signifying the automorphic type of the modular form - $`E` for Eisenstein or $`C` for cuspidal.

- $`x` is the label of the {bpref "cmf.galois_orbit"}[Galois orbit] of the newform $`f`.

For each {bpref "cmf.embedding"}[embedding] of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f` into the complex numbers, the corresponding modular form over $`\C` has a label of the form $`N.k.A.a.x.n.i`, where

- $`n` determines the Conrey label $`N.n` of the Dirichlet character $`\chi`;

- $`i` is an integer ranging from 1 to the {bpref "cmf.relative_dimension"}[relative dimension] of the newform that distinguishes embeddings with the same character $`\chi`.

If $`f \in S_k^{\rm new}(N, \chi)` is cuspidal, the automorphic type may be omitted from both labels.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_label"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.embedding"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.level"}[] {uses "cmf.relative_dimension"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.level"
*Level of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.level))

A *level* of a {bpref "cmf"}[modular form] $`f` is a positive integer $`N` such that $`f` is a modular form on a subgroup $`\Gamma` of {bpref "group.sl2z"}[$`\operatorname{SL}_2(\mathbb{Z})`] that contains the principal congruence subgroup $`\Gamma(N)`.

The *level* of a {bpref "cmf"}[newform] is the least such integer $`N`.

Depends on: {uses "cmf"}[] {uses "group.sl2z"}[]
:::

:::definition "cmf.maximal"
*Maximal newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.maximal))

A {bpref "cmf.newform"}[newform] is *maximal* if its {bpref "cmf.galois_orbit"}[Galois orbit] spans the ambient subspace that contains it (its Atkin-Lehner subspace when the {bpref "cmf.character"}[character] is trivial, the entire newspace otherwise).

A newform is the *largest* newform in its ambient subspace if its {bpref "cmf.dimension"}[dimension] is strictly larger than that of any other newform in the same subspace (this includes newforms that are maximal).

Depends on: {uses "cmf.character"}[] {uses "cmf.dimension"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.minimal"
*Minimal modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.minimal))

A modular form is *minimal* if it is not a twist of a form of lower level.
:::

:::definition "cmf.minimal_twist"
*Minimal twist.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.minimal_twist))

The *minimal twist* of a {bpref "cmf.newform"}[newform] $`f` is the {bpref "cmf.twist"}[twist] $`g` of $`f` whose {bpref "cmf.label"}[label] is lexicographically minimal among all twists of $`f` that are both {bpref "cmf.twist_minimal"}[twist minimal] and have {bpref "character.dirichlet.minimal"}[minimal] {bpref "cmf.character"}[character] $`\chi`.

A key feature of the minimal twist $`g` (and more generally, of any twist minimal $`g` of {bpref "cmf.level"}[level] $`N` and minimal character $`\chi`) is that for any character $`\psi`, the level $`M` of the twist $`g\otimes\psi` can be computed as $`M={\rm lcm}(N,{\rm cond}(\psi){\rm cond}(\chi\psi))`.

Depends on: {uses "character.dirichlet.minimal"}[] {uses "cmf.character"}[] {uses "cmf.label"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.twist"}[] {uses "cmf.twist_minimal"}[]
:::

:::definition "cmf.minus_space"
*Minus space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.minus_space))

The *minus subspace* of $`S_k(\Gamma_0(N))` is the eigenspace of the {bpref "cmf.fricke"}[Fricke involution] $`w_N` with eigenvalue $`-1`.

Depends on: {uses "cmf.fricke"}[]
:::

:::definition "cmf.newform"
*Newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.newform))

A *newform* is a cusp form $`f\in S_k^{\rm new}(N,\chi)` in the {bpref "cmf.newspace"}[new subspace] that is also an eigenform of all {bpref "cmf.hecke_operator"}[Hecke operators], normalized so that the {bpref "cmf.fouriercoefficients"}[$`q`-expansion]  $`f(z)=\sum a_n q^n`, where $`q=e^{2\pi i z}`, begins with the coefficient $`a_1=1`.  The newforms are a basis for the new subspace.

Depends on: {uses "cmf.fouriercoefficients"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.newform_subspace"
*Newform subspace.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.newform_subspace))

The *newform subspace* of a {bpref "cmf.newform"}[newform] $`f` in $`S_k^{\rm new}(N,\chi)` is the subspace generated by $`T_p(f)` for all {bpref "cmf.hecke_operator"}[Hecke operators] $`T_p` for $`p` coprime to the {bpref "cmf.level"}[level], equivalently, the subspace generated by the Galois conjugates of $`f`.

Every {bpref "cmf.newspace"}[newspace] has a canonical decomposition into newform subspaces.

Depends on: {uses "cmf.hecke_operator"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.newspace"
*New subspace.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.newspace))

The space $`S_k(N,\chi)` of {bpref "cmf.cusp_form"}[cuspidal] {bpref "cmf"}[modular forms] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k`, and {bpref "cmf.character"}[character] $`\chi` can be decomposed

$$`S_k(N,\chi) = S_k^{\rm old}(N,\chi) \oplus S_k^{\rm new}(N,\chi)`

into old and new subspaces, defined as follows.

If $`M` is a proper divisor of $`N` and $`\chi_M` is a {bpref "character.dirichlet"}[Dirichlet character] of {bpref "character.dirichlet.modulus"}[modulus] $`M` that {bpref "character.dirichlet.induce"}[induces] $`\chi`, then for all $`d \mid (N/M)`, there is a map from $`S_k(M,\chi_M) \to S_k(N,\chi)` via $`f(z) \mapsto f(dz)`.  The span of the images of all of these maps is the *old subspace* $`S_k^{\rm old}(N,\chi) \subseteq S_k(N,\chi)`.

The *new subspace* $`S_k^{\rm new}(N,\chi)` is the orthogonal complement of $`S_k^{\rm old}(N,\chi)` with respect to the {bpref "cmf.petersson_scalar_product"}[Petersson inner product].

A basis for the new subspace is given by {bpref "cmf.newform"}[newforms].

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[] {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.petersson_scalar_product"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.nontrivial_twist"
*Nontrivial inner twist.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.nontrivial_twist))

An {bpref "cmf.inner_twist"}[inner twist] is *nontrivial* if it is not the {bpref "cmf.self_twist"}[self twist] by the trivial character.

Depends on: {uses "cmf.inner_twist"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.oldspace"
*Old subspace of modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.oldspace))

Each space of $`S_k(N,\chi)` of {bpref "cmf.cusp_form"}[cuspidal] {bpref "cmf"}[modular forms] of {bpref "cmf.weight"}[weight] $`k`, {bpref "cmf.level"}[level] $`N`, and {bpref "cmf.character"}[character] $`\chi` contains an *old* subspace $`S_k^{\rm old}(N,\chi)` that can be expressed as a direct sum of {bpref "cmf.newspace"}[spaces of newforms] $`S_k^{\rm new}(N_i,\chi_i)`, where each $`N_i` is a proper divisor of $`N` divisible by the {bpref "character.dirichlet.conductor"}[conductor] of $`\chi`, and each $`\chi_i` is the unique character of modulus $`N_i` {bpref "character.dirichlet.induce"}[induced] by the {bpref "character.dirichlet.primitive"}[primitive character] that induces $`\chi`.

This decomposition arises from the injective maps

$$`\begin{aligned}
\iota_d\colon S_k(N_i,\chi_i)&\to S_k(N,\chi)\\
f\ &\mapsto f(d\tau)
\end{aligned}`

that exist for each divisor $`d` of $`N/N_i`.  The image of each $`\iota_d` is isomorphic to $`S_k(N_i,\chi_i)`, and we have the decomposition

$$`S_k(N,\chi)\simeq\!\!\!\! \bigoplus_{\mathrm{cond}(\chi)|N_i|N}\!\!\!\! S_k^{\rm new}(N_i,\chi_i)^{\oplus m_i},`

where $`m_i` is the number of divisors of $`N/N_i`.  Restricting the direct sum to proper divisors $`N_i` of $`N` yields a decomposition for $`S_k^{\rm old}(N,\chi)`.

Depends on: {uses "character.dirichlet.conductor"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.newspace"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.petersson_scalar_product"
*Petersson scalar product.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.petersson_scalar_product))

Let $`f` and $`g` be two modular forms with respect to a {bpref "group.subgroup.index"}[finite index] subgroup $`G` of $`\Gamma`. When it exists, we define the
*Petersson scalar product* of $`f` and $`g` with respect to the group $`G`
by

$$`\langle
f,g\rangle_G=\frac{1}{[\Gamma:G]}\int_{\mathfrak{F}}f(z)\overline{
g(z)}y^kd\mu,`

where $`\mathfrak{F}` is a {bpref "group.fuchsian.fundamental_domain"}[fundamental domain] for $`G` and $`d\mu=dxdy/y^2` is the measure associated to the hyperbolic metric.

Note that the Petersson scalar product exists if at least one of $`f`, $`g` is a {bpref "cmf.cusp_form"}[cusp form].

Depends on: {uses "cmf.cusp_form"}[] {uses "group.fuchsian.fundamental_domain"}[] {uses "group.subgroup.index"}[]
:::

:::definition "cmf.plus_space"
*Plus space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.plus_space))

The *plus subspace* of $`S_k(\Gamma_0(N)` is the eigenspace of the {bpref "cmf.fricke"}[Fricke involution] $`\omega_N` with eigenvalue $`1`.

Depends on: {uses "cmf.fricke"}[]
:::

:::definition "cmf.projective_field"
*Projective field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.projective_field))

The *projective field* of a {bpref "cmf.weight"}[weight] one {bpref "cmf.newform"}[newform] is the {bpref "nf"}[number field] fixed by the kernel of its associated {bpref "cmf.galois_representation"}[projective Galois representation] $`\bar\rho\colon \Gal(\overline{\Q}/\Q)\to \PGL_2(\C)`.

This number field is typically identified as the Galois closure of a {bpref "nf.sibling"}[sibling subfield] with minimal degree and absolute discriminant.

Depends on: {uses "cmf.galois_representation"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[] {uses "nf"}[] {uses "nf.sibling"}[]
:::

:::definition "cmf.projective_image"
*Projective image.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.projective_image))

The *projective image* of a {bpref "cmf.weight"}[weight] one {bpref "cmf.newform"}[newform] is the image of its associated {bpref "cmf.galois_representation"}[projective Galois representation] $`\rho\colon \Gal(\overline{\Q}/\Q)\to \PGL_2(\C)`.  It is a finite subgroup of $`\PGL_2(\C)` that can be classified as one of four *types*: It is either isomorphic to a dihedral group $`D_n` for some integer $`n\ge 2` (where $`D_2:=C_2\times C_2` is the Klein group), or to one of $`A_4, S_4, A_5`, where $`A_n` and $`S_n` respectively denote the alternating and symmetric groups on $`n` letters.

Depends on: {uses "cmf.galois_representation"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.q-expansion"
*q-expansion of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.q-expansion))

The *$`q`-expansion* of a modular form $`f(z)` is its {bpref "cmf.fouriercoefficients"}[Fourier expansion] at the {bpref "group.fuchsian.cusps"}[cusp] $`z=i\infty`, expressed as a power series $`\sum_{n=0}^{\infty} a_n q^n` in the variable $`q=e^{2\pi iz}`.

For {bpref "cmf.cusp_form"}[cusp forms], the constant coefficient $`a_0` of the $`q`-expansion is zero.

For {bpref "cmf.newform"}[newforms], we have $`a_1=1` and the coefficients $`a_n` are algebraic integers in a {bpref "nf"}[number field] $`K \subseteq \C`.

Accordingly, we define the *$`q`-expansion* of a {bpref "cmf.galois_orbit"}[newform orbit] $`[f]` to be the $`q`-expansion of any newform $`f` in the orbit, but with coefficients $`a_n \in K` (without an embedding into $`\C`).  Each {bpref "nf.embedding"}[embedding] $`K \hookrightarrow \C` then gives rise to an {bpref "cmf.embedding"}[embedded newform] whose $`q`-expansion has $`a_n \in \C`, as above.

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "group.fuchsian.cusps"}[] {uses "nf"}[] {uses "nf.embedding"}[]
:::

:::definition "cmf.relative_dimension"
*Relative dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.relative_dimension))

The *relative dimension* of a {bpref "cmf.newform"}[newform] in a space of modular forms $`S_k^{\mathrm{new}}(\Gamma_0(N),\chi)` is the dimension of its coefficient field as an extension of the character field $`\Q(\chi)` (the number field generated by the values of $`\chi`).

Depends on: {uses "cmf.newform"}[]
:::

:::definition "cmf.rm_form"
*Real multiplication.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.rm_form))

A {bpref "cmf"}[modular form] is said to have *real multiplication* if it admits a {bpref "cmf.self_twist"}[self twist] by the Kronecker character of a real quadratic field.

Only modular forms of weight one can have real multiplication.

Depends on: {uses "cmf"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.satake_angles"
*Satake Angles.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.satake_angles))

The *Satake angles* $`\theta_p = \arg \alpha_p \in [-\pi, \pi]` are the arguments of a complex embedding of the {bpref "cmf.satake_parameters"}[Satake parameters] $`\alpha_p`.

Depends on: {uses "cmf.satake_parameters"}[]
:::

:::definition "cmf.satake_parameters"
*Satake parameters.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.satake_parameters))

Let $`f` be {bpref "cmf.newform"}[newform] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k` and {bpref "cmf.character"}[character] $`\chi`.
Let $`p` be a {bpref "cmf.bad_prime"}[good prime], i.e., $`p \nmid N`.

The *Satake parameters* $`\alpha_p` are the reciprocal roots of $`L_p\left(p^{-(k-1)/2} t \right)`, where

$$`L_p\left( t \right) =  1 -a_p t + \chi(p)  p^{k-1} t^2 = \det(1 - t \, T_p)
= (1 - \alpha_p p^{\frac{k-1}{2}}t )(1 - \alpha_p^{-1} \chi(p) p^{\frac{k-1}{2}} t),`

$`T_p` is {bpref "cmf.hecke_operator"}[Hecke operator], and $`a_p` its trace.

Depends on: {uses "cmf.bad_prime"}[] {uses "cmf.character"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.sato_tate"
*Sato-Tate group of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.sato_tate))

The *Sato-Tate group* of a {bpref "cmf.newform"}[newform] is a compact Lie group that one can attach to the Galois representation associated to the newform.

For newforms of {bpref "cmf.weight"}[weight] $`k=1`, the Sato-Tate group is simply the image of the corresponding 2-dimensional Artin representation, a finite subgroup of $`\SL_2(\C)`.

For newforms of weight $`k>1` the Sato-Tate group is a subgroup of $`\mathrm{U}(2)` whose identity component is either $`\mathrm{SU(2)}` (for newforms without {bpref "cmf.cm_form"}[CM]) or $`\mathrm{U}(1)` (for CM newforms) diagonally embedded in $`\mathrm{U}(2)`.

The Sato-Tate conjecture implies that as $`p\to\infty` the limiting distribution of normalized Hecke eigenvalues $`a_p/p^{(k-1)/2}` converges to the trace distribution induced by the Haar measure of the Sato-Tate group.

The Sato-Tate conjecture for classical modular forms has been proved .

Depends on: {uses "cmf.cm_form"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.self_twist"
*Self-twist.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.self_twist))

A {bpref "cmf.newform"}[newform] $`f` admits a *self-twist* by a {bpref "character.dirichlet.primitive"}[primitive]
 {bpref "character.dirichlet"}[Dirichlet character] $`\chi` if the equality

$$`a_p(f) = \chi(p)a_p(f)`

holds for all but finitely many primes $`p`.

For non-trivial $`\chi` this can hold only when $`\chi` has {bpref "character.dirichlet.order"}[order] $`2` and $`a_p=0` for all primes $`p` not dividing the {bpref "cmf.level"}[level] of $`f` for which $`\chi(p)=-1`.
The character $`\chi` is then the Kronecker character of a quadratic field $`K` and may be identified by the {bpref "nf.discriminant"}[discriminant] $`D` of $`K`.

If $`D` is negative, the modular form $`f` is said to have {bpref "cmf.cm_form"}[complex multiplication] (CM) by $`K`, and if $`D` is positive, $`f` is said to have {bpref "cmf.rm_form"}[real multiplication] (RM) by $`K`.  The latter can occur only when $`f` is a modular form of {bpref "cmf.weight"}[weight] $`1` whose {bpref "cmf.projective_image"}[projective image] is dihedral.

It is possible for a modular form to have multiple non-trivial self twists; this occurs precisely when $`f` is a modular form of weight one whose projective image is isomorphic to $`D_2:=C_2\times C_2`; in this case $`f` admits three non-trivial self twists, two of which are CM and one of which is RM.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.projective_image"}[] {uses "cmf.weight"}[] {uses "nf.discriminant"}[]
:::

:::definition "cmf.selfdual"
*Self dual modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.selfdual))

A {bpref "cmf.cusp_form"}[cuspidal modular form] $`f` is said to be *self dual* if the coefficients $`a_n` that appear in its {bpref "cmf.q-expansion"}[$`q`-expansion] are real numbers; equivalently, the L-function of the modular form is {bpref "lfunction.self-dual"}[self dual].

The {bpref "cmf.coefficient_field"}[coefficient field] of a {bpref "cmf.newform"}[newform] is either a {bpref "nf.totally_real"}[totally real] number field or a {bpref "nf.cm_field"}[CM field], depending on whether the newform is self dual or not.

Depends on: {uses "cmf.coefficient_field"}[] {uses "cmf.cusp_form"}[] {uses "cmf.newform"}[] {uses "cmf.q-expansion"}[] {uses "lfunction.self-dual"}[] {uses "nf.cm_field"}[] {uses "nf.totally_real"}[]
:::

:::definition "cmf.shimura_correspondence"
*Shimura correspondence.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.shimura_correspondence))

Let $`k` be an odd integer, and let $`N` a positive integer divisible by $`4`. Let $`\chi` be a {bpref "character.dirichlet"}[character] modulo $`N`. Let $`t` be a square-free integer. The *Shimura correspondence* is the linear map $`Sh_t:S_{k/2}(N, \chi)\to S_{k-1}(N/2, \chi^2)` defined by the equation

$$`L(s, Sh_t(g)) = L(\chi_t, s+1-\lambda) \cdot \sum_{n\geq1} a_{tn^2} n^{-s},`

where

- $`\lambda=(k-1)/2`.

- $`\chi_t` is the character given by $`\chi_t(m) = \chi(m) \left(\frac{-1}{m}\right) \left(\frac{t}{m}\right)`.

- $`g(z) = \sum_{n\geq1} a_n q^n` is the $`q`-expansion of $`g`.

This map is Hecke linear. If $`k\geq5`, it takes cusp forms to cusp forms.

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "cmf.space"
*Spaces of modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.space))

The *space* of {bpref "cmf"}[modular forms] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k`, and {bpref "cmf.character"}[character] $`\chi` is denoted $`M_k(N,\chi)`.

The space $`M_k(N,\chi)` is a finite-dimensional complex vector space which further decmoposes into {bpref "cmf.subspaces"}[subspaces].  In particular, we have a subspace of {bpref "cmf.cusp_form"}[cusp forms] $`S_k(N,\chi) \subseteq M_k(N,\chi)`.

Depends on: {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.space_trace_form"
*Trace form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.space_trace_form))

The *trace form* of a {bpref "cmf.newspace"}[newspace] $`S_k(N,\chi)` is the modular form obtained by summing its canonical basis of {bpref "cmf.newform"}[newforms].

Depends on: {uses "cmf.newform"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.stark_unit"
*Stark unit of a newform of weight one.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.stark_unit))

Stark's conjecture applied to the associated {bpref "cmf.galois_representation"}[Galois representation] of a {bpref "cmf.newform"}[newform] $`f(z)=\sum a_n q^n` of {bpref "cmf.weight"}[weight] one  states the following. Let $`E=\mathbb{Q}((a_n)_{n \in \mathbb{N}})`, $`\Delta=\text{Gal}(E/\mathbb{Q})` and $`f^\alpha(z)=\sum \alpha(a_n) q^n` for $`\alpha \in \Delta`. Let $`L(s, f)` be the L-function of $`f`. Then, for all $`b \in E^*` there exists an integer $`m \geq 1` and a unit $`\varepsilon` in the {bpref "cmf.artin_field"}[Artin field] of $`f`, called the *Stark unit*, such that

$$`e^{m \sum_{\alpha \in \Delta} \alpha(b)L'(0, f^\alpha)} = \varepsilon`

In the case where the coefficients of $`\text{Tr}(bf)` are in $`\mathbb{Z}`, Chinburg further conjectured that there exists a Stark unit for $`m=1` . Notice that if we choose $`b = 1`, the preceding condition always holds. Here, we compute the Stark unit of the newform for $`b=1` and $`m=1`.

Depends on: {uses "cmf.artin_field"}[] {uses "cmf.galois_representation"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.sturm_bound"
*Sturm bound.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.sturm_bound))

The *Sturm bound* is an upper bound on the least index where the coefficients of the {bpref "cmf.fouriercoefficients"}[Fourier expansions] of distinct modular forms in the same space $`M_k(N,\chi)` must differ.

More precisely, for any space $`M_k(N,\chi)` of modular forms of {bpref "cmf.weight"}[weight] $`k`, {bpref "cmf.level"}[level] $`N`, and {bpref "cmf.character"}[character] $`\chi`, the Sturm bound is the integer

$$`B(M_k(N,\chi)) := \left\lfloor \frac{km}{12}\right\rfloor,`

where

$$`m:=[\SL_2(\Z):\Gamma_0(N)]=N\prod_{p|N}\left(1+\frac{1}{p}\right).`

If $`f=\sum_{n\ge 0}a_n q^n` and $`g=\sum_{n\ge 0}b_n q^n` are elements of $`M_k(N,\chi)`  with $`a_n=b_n` for all $`n\le B(M_k(N,\chi))` then $`f=g`; see Corollary 9.20 in [stein-modforms.pdf](https://wstein.org/books/modform/stein-modform.pdf) for $`k>1` and Lemma 5 in  for $`k=1`.

The Sturm bound applies, in particular, to {bpref "cmf.newform"}[newforms] of the same level, weight, and character.  Better bounds for newforms are known in certain cases (see Corollary 9.19 and Theorem 9.21 in [stein-modforms.pdf](https://wstein.org/books/modform/stein-modform.pdf), for example), but for consistency we always take the Sturm bound to be the integer $`B(M_k(N,\chi))` defined above.

Note that the Sturm bound for $`S_k^{\mathrm{new}}(N,\chi)` does not apply (in general) to the space

$$`S_k^{\mathrm{new}}(N,[\chi]):= \bigoplus_{\chi'\in [\chi]}S_k^{\rm new}(N,\chi')`

associated to the Galois orbit $`[\chi]`; rather, it applies to each direct summand $`S_k^{\rm new}(N,\chi')`.

Depends on: {uses "cmf.character"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.sturm_bound_gamma1"
*Sturm bound for Gamma1(N).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.sturm_bound_gamma1))

The *Sturm bound* is an upper bound on the least index where the coefficients of the {bpref "cmf.fouriercoefficients"}[Fourier expansions] of distinct modular forms in the same space must differ.

More precisely, for any space $`M_k(\Gamma_1(N))` of modular forms of {bpref "cmf.weight"}[weight] $`k` and {bpref "cmf.level"}[level] $`N`, the Sturm bound is the integer

$$`B(M_k(\Gamma_1(N))) := \left\lfloor \frac{km}{12}\right\rfloor,`

where

$$`m:=[\SL_2(\Z):\Gamma_1(N)]=N^2\prod_{p|N}\left(1-\frac{1}{p^2}\right).`

If $`f=\sum_{n\ge 0}a_n q^n` and $`g=\sum_{n\ge 0}b_n q^n` are elements of $`M_k(\Gamma_1(N))`  with $`a_n=b_n` for all $`n\le B(M_k(\Gamma_1(N)))` then $`f=g`; see Corollary 9.19 in [stein-modforms.pdf](https://wstein.org/books/modform/stein-modform.pdf) for $`k>1`.

The Sturm bound applies, in particular, to {bpref "cmf.newform"}[newforms] of the same level and weight.  Better bounds for newforms are known in certain cases (see Corollary 9.19 and Theorem 9.21 in [stein-modforms.pdf](https://wstein.org/books/modform/stein-modform.pdf), for example), but for consistency we always take the Sturm bound to be the integer $`B(M_k(\Gamma_1(N)))` defined above.

Depends on: {uses "cmf.fouriercoefficients"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.subspaces"
*Subspaces of modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.subspaces))

The {bpref "cmf.space"}[space] $`M_k(N,\chi)` of {bpref "cmf"}[modular forms] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k`, and {bpref "cmf.character"}[character] $`\chi` can be decomposed as

$$`M_k(N,\chi) = E_k(N,\chi) \oplus S_k(N,\chi)`

where $`E_k(N,\chi)` is the Eisenstein subspace (the span of Eisenstein series) and $`S_k(N,\chi)` the subspace of {bpref "cmf.cusp_form"}[cusp forms].

These spaces further decompose into old and new subspaces as follows.  If $`M` is a proper divisor of $`N` and $`\chi_M` is a {bpref "character.dirichlet"}[Dirichlet character] of {bpref "character.dirichlet.modulus"}[modulus] $`M` that {bpref "character.dirichlet.induce"}[induces] $`\chi`, then for every divisor $`d \mid (N/M)`, there is a map from $`M_k(M,\chi_M) \to M_k(N,\chi)` via $`f(z) \mapsto f(dz)`.  The span of the images of all of these maps is the *old subspace* $`M_k^{\rm old}(N,\chi) \subseteq M_k(N,\chi)`.

The cuspidal subspace decomposes as

$$`S_k(N,\chi) = S_k^{\rm new}(N,\chi) \oplus S_k^{\rm old}(N,\chi)`

where the *new subspace* $`S_k^{\rm new}(N,\chi)` is the orthogonal complement of $`S_k^{\rm old}(N,\chi)` with respect to the {bpref "cmf.petersson_scalar_product"}[Petersson inner product].

The Eisenstein subspace similarly decomposes as

$$`E_k(N,\chi) = E_k^{\rm new}(N,\chi) \oplus E_k^{\rm old}(N,\chi)`

where $`E_k^{\rm new}(N,\chi)` is the span of those Eisenstein series attached to a pair $`(\chi_1,\chi_2)` of (primitive) characters of {bpref "character.dirichlet.conductor"}[conductor] $`N`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[] {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.petersson_scalar_product"}[] {uses "cmf.space"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.trace_bound"
*Trace bound.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.trace_bound))

The *trace bound* for a {bpref "cmf.newspace"}[space of newforms] $`S_k^{new}(N, \chi)` is the least positive integer $`m` such that taking traces down to $`\Q` of the coefficients $`a_n` for $`n \le m` suffices to distinguish all the
{bpref "cmf.galois_orbit"}[Galois orbits] of
{bpref "cmf.newform"}[newforms] in the space; here $`a_n` denotes the $`n`th coefficient of the {bpref "cmf.q-expansion"}[$`q`-expansion] $`\sum a_n q^n` of a newform.

If the newforms in the space all have distinct {bpref "cmf.dimension"}[dimensions] then the trace bound is 1, because the trace of $`a_1=1` from the {bpref "cmf.coefficient_field"}[coefficient field] of the newform down to $`\Q` is equal to the dimension of its {bpref "cmf.galois_orbit"}[Galois orbit].

Depends on: {uses "cmf.coefficient_field"}[] {uses "cmf.dimension"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[] {uses "cmf.q-expansion"}[]
:::

:::definition "cmf.trace_form"
*Trace form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.trace_form))

For a {bpref "cmf.newform"}[newform] $`f \in S_k^{\rm new}(\Gamma_1(N))`, its *trace form* $`\mathrm{Tr}(f)` is the sum of its distinct conjugates under $`\mathrm{Aut}(\C)` (equivalently, the sum under all embeddings of the {bpref "cmf.coefficient_field"}[coefficient field] into $`\C`).  The trace form is a modular form $`\mathrm{Tr}(f) \in S_k^{\rm new}(\Gamma_1(N))` whose $`q`-expansion has integral coefficients $`a_n(\mathrm{Tr}(f)) \in \Z`.

The coefficient $`a_1` is equal to the {bpref "cmf.dimension"}[dimension] of the newform.

For $`p` prime, the coefficient $`a_p` is the trace of Frobenius in the direct sum of the $`\ell`-adic Galois representations attached to the conjugates of $`f` (for any prime $`\ell`).  When $`f` has weight $`k=2`, the coefficient $`a_p(f)` is the trace of Frobenius acting on the modular abelian variety associated to $`f`.

For a {bpref "cmf.newspace"}[newspace] $`S_k^{\rm new}(N,\chi)`, its trace form is the sum of the trace forms $`\mathrm{Tr}(f)` over all newforms $`f\in S_k^{\rm new}(N,k)`; it is also a modular form in $`S_k^{\rm new}(\Gamma_1(N))`.

The graphical plot displayed in the properties box on the home page of each newform or newspace is computed using the trace form.

Depends on: {uses "cmf.coefficient_field"}[] {uses "cmf.dimension"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.twist"
*Twist.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.twist))

Associated to each {bpref "cmf.newform"}[newform] $`f` and {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet"}[Dirichlet character] $`\psi`, there is a unique newform $`g:=f\otimes\psi`, the *twist* of $`f` by $`\psi`, that satisfies

$$`a_n(g)=\psi(n)a_n(f)`

for all integers $`n\ge 1` coprime to $`N` and the {bpref "character.dirichlet.conductor"}[conductor] of $`\psi`.  The newforms $`f` and $`g` are then *twist equivalent*.  When $`g` is a {bpref "cmf.galois_conjugate"}[Galois conjugate] of $`f`, it is said to be an {bpref "cmf.inner_twist"}[inner twist].

The {bpref "cmf.galois_orbit"}[newform orbit] $`[g]` is a *twist* of the newform orbit $`[f]` by the {bpref "character.dirichlet.galois_orbit"}[character orbit] $`[\psi]` if some $`g\in [g]` is a twist of $`f` by some $`\psi` in $`[\psi]`.  This may occur with {bpref "cmf.twist_multiplicity"}[multiplicity].

Twist equivalence is an equivalence relation.  The *twist class* of a newform or newform orbit is its equivalence class under this relation.

In the LMFDB each twist class is identified by the label of its {bpref "cmf.minimal_twist"}[minimal twist].

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.galois_conjugate"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.inner_twist"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.twist_minimal"
*Twist minimal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.twist_minimal))

A {bpref "cmf.newform"}[newform] $`f` is *twist minimal* if its {bpref "cmf.level"}[level] achieves the minimum within its {bpref "cmf.twist"}[twist class].

A twist minimal newform $`f` need not have {bpref "character.dirichlet.minimal"}[minimal character], but if this is not the case there will be a twist of $`f` that is both twist minimal and has minimal {bpref "cmf.character"}[character].

In the LMFDB, the designated representative of each twist class is the twist minimal newform $`g` of minimal character whose {bpref "cmf.label"}[label] is lexicographically minimal among all such newforms.  This newform $`g` is called the *minimal twist* of the newforms in its twist equivalence class and is identified by a checkmark (\checkmark) in tables of twists.

These conventions also apply to {bpref "cmf.galois_orbit"}[newform orbits].

Depends on: {uses "character.dirichlet.minimal"}[] {uses "cmf.character"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.label"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.twist"}[]
:::

:::definition "cmf.twist_multiplicity"
*Twist multiplicity.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.twist_multiplicity))

The *multiplicity* of a {bpref "cmf.galois_orbit"}[newform orbit] $`[g]` as a {bpref "cmf.twist"}[twist] of a newform orbit $`[f]` by a {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet.galois_orbit"}[character orbit] $`[\psi]` is the number of distinct $`\psi\in[\psi]` for which $`f\otimes\psi\in[g]`.  This number is the same for every $`f\in [f]` and depends only on the Galois orbits $`[g]`, $`[f]`, and $`[\psi]`.

When $`g` is an {bpref "cmf.inner_twist"}[inner twist] of $`f`, this multiplicity is equal to the {bpref "cmf.inner_twist_count"}[inner twist count] of $`f`.

Depends on: {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.inner_twist"}[] {uses "cmf.inner_twist_count"}[] {uses "cmf.twist"}[]
:::

:::definition "cmf.weight"
*Weight of an elliptic modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.weight))

The *weight* of an elliptic {bpref "cmf"}[modular form] $`f` is the integer or half-integer power of $`(cz+d)` that occurs in the modular transformation property of $`f` under the action of $`\gamma = \left( \begin{array}{ll}  a & b \\ c & d \end{array}\right)` on the upper half plane.  That is, the weight is the number $`k`
in the transformation law

$$`f\left( \frac{a z + b}{c z + d} \right) = \chi(d)(c z + d)^k f(z) .`

Depends on: {uses "cmf"}[]
:::
