import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Ring theory" =>

This section lists the LMFDB definitions in the categories `ring`, `gl2` and `alg`. Each definition links back to its LMFDB knowl.

:::definition "alg.bezout_matrix" (lean := "Polynomial.bezoutMatrix, Polynomial.sub_mul_sum_bezoutMatrix, Polynomial.det_bezoutMatrix, Polynomial.resultant, Polynomial.sylvester")
*Bézout matrix.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.bezout_matrix))

Given two polynomials $`f` and $`g` of degree at most $`n`, their *degree $`n` Bézout matrix* is the $`n\times n` matrix $`(c_{ij})` where

$$`\frac{f(x)g(y)-f(y)g(x)}{x-y} = \sum_{i,j=1}^n c_{ij} x^i y^{j}.`

The determinant of this matrix is the resultant of the two polynomials.
:::

:::definition "alg.binary_operation" (lean := "Mul")
*Binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation))

A *binary operation*,  on a set $`S` is a function $`S\times S\to S`.

If the operation is denoted by $`*`, then the output of this function applied to $`(s_1,s_2)` is typically denoted $`s_1*s_2`.
:::

:::definition "alg.binary_operation.associative" (lean := "Std.Associative, Semigroup")
*Associative binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation.associative))

If $`*` is a {bpref "alg.binary_operation"}[binary operation] on a set $`A`, then $`*` is *associative* on $`A` if for all $`a,b,c\in A`,

$$`a*(b*c)=(a*b)*c.`
/div>

Depends on: {uses "alg.binary_operation"}[]
:::

:::definition "alg.binary_operation.commutative" (lean := "Std.Commutative, CommMagma")
*Commutative binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation.commutative))

If $`*` is a {bpref "alg.binary_operation"}[binary operation] on a set $`A`, then $`*` is *commutative* on $`A` if for all $`a,b\in A`,

$$`a*b=b*a.`

Depends on: {uses "alg.binary_operation"}[]
:::

:::definition "alg.binary_operation.identity" (lean := "Std.LawfulIdentity, MulOneClass, MulOneClass.ext")
*Identity for a binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation.identity))

If $`*` is a {bpref "alg.binary_operation"}[binary operation] on a set $`A`, then $`A` has an *identity* element with respect to $`*` if there exists $`e\in A` such that for all $`a\in A`,

$$`a*e = e*a = a.`

Such an identity element $`e`, if it exists, is unique and is thus called *the identity element* of $`A` with respect to $`*`.

Depends on: {uses "alg.binary_operation"}[]
:::

:::definition "alg.binary_operation.inverse" (lean := "Invertible")
*Inverse for a binary operation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.binary_operation.inverse))

If $`*` is a {bpref "alg.binary_operation"}[binary operation] on a set $`A` having {bpref "alg.binary_operation.identity"}[identity element] $`e\in A`, then an element $`a\in A` has an *inverse* in $`A` with respect to $`*` if there exists $`a'\in A` such that

$$`a*a' = a'*a = e.`

Depends on: {uses "alg.binary_operation"}[] {uses "alg.binary_operation.identity"}[]
:::

:::definition "alg.matrix.skew_symmetric" (lean := "LieAlgebra.Orthogonal.so, LieAlgebra.Orthogonal.mem_so, Matrix.IsSkewAdjoint")
*Skew-symmetric matrix.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.matrix.skew_symmetric))

A matrix $`M` is skew-symmetric if its transpose equals its negation, i.e. if $`M^T = -M`. In particular, a skew-symmetric matrix must be square.
:::

:::definition "alg.symmetric_bilinear_form" (lean := "LinearMap.BilinForm, LinearMap.BilinForm.IsSymm")
*Symmetric bilinear form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.symmetric_bilinear_form))

For a vector space $`V` over a field $`F`, a *symmetric bilinear form* is a function $`B \colon V^2 \to F` satisfying

1. $`B(x+w,y) = B(x,y) + B(w,y)` for all $`x,y,w \in V`;
2. $`B(\alpha x, y) = \alpha B(x,y)` for all $`x \in V`, and all $`\alpha \in F`;
3. $`B(x,y) = B(y,x)` for all $`x,y \in V`.

Conditions (1) and (2) imply that $`B(\cdot,y)` is a linear map in the first variable when $`y` is fixed. Including condition (3) then implies that $`B(x,\cdot)` is also a linear map in the second variable when $`x` is fixed.
:::

:::definition "alg.symplectic_isomorphism" (lean := "LinearEquiv.IsSymplectic, LinearEquiv.isSymplectic_iff, exteriorPower.map")
*Symplectic isomorphism.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/alg.symplectic_isomorphism))

Let $`N \ge 1`.  Let $`\mu_N` be the group of $`N`th roots of unity in some algebraically closed field of characteristic not dividing $`N`.  Let $`M` be a free rank $`2` $`\Z/N\Z`-module together with an isomorphism $`\alpha \colon \bigwedge^2 M \stackrel{\sim}\to \mu_N`, or equivalently with a nondegenerate alternating pairing $`M \times M \to \mu_N`.  For example, $`M` could be $`E[N]` for an elliptic curve $`E`, together with the Weil pairing.  Or $`M` could be $`\Z/N\Z \times \mu_N` with the "determinant" pairing $`(a,\gamma),(b,\delta) \mapsto \delta^a/\gamma^b`.

A *symplectic isomorphism* from $`M` to another such structure $`M'` is a $`\Z/N\Z`-module isomorphism $`M \to M'` such that the induced isomorphism $`\bigwedge^2 M \to \bigwedge^2 M'` gets identified via $`\alpha` and $`\alpha'` with the _identity_ $`\mu_N \to \mu_N`.

The same definition makes sense in a context in which each free rank 2 $`\Z/N\Z`-module is enriched with a Galois action to make a Galois module, or replaced by a finite etale group scheme that is $`(\Z/N\Z)^2` etale locally.
:::

:::definition "gl2.borel" (lean := "Matrix.GeneralLinearGroup.IsBorelSubgroup, TauCeti.GL2Borel, Matrix.GeneralLinearGroup.labelBAB, Matrix.GeneralLinearGroup.isBorelSubgroup_iff_exists_lineStabilizer, ZMod.leastPrimitiveRoot")
*Borel subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.borel))

A *Borel subgroup* of a general linear group is a subgroup that is conjugate to the group of upper triangular matrices.

The Borel subgroups of $`\GL_2(\F_p)` are maximal subgroups that fix a one-dimensional subspace of $`\F_p^2`; every such subgroup is conjugate to the subgroup of upper triangular matrices.

Subgroup labels containing the letter *B* identify a subgroup of $`\GL_2(\F_p)` that lies in the Borel subgroup of upper triangular matrices but is not contained in the subgroup of diagonal matrices; these are precisely the subgroups of a Borel subgroup that contain an element of order $`p`.

The label *B* is used for the full Borel subgroup of upper triangular matrices

The label *B.a.b* denotes the proper subgroup of *B* generated by the matrices

$$`\begin{pmatrix}a&0\\0&1/a\end{pmatrix},\ \begin{pmatrix}b&0\\0&r/b\end{pmatrix},\ \begin{pmatrix}1&1\\0&1\end{pmatrix},`

where $`a` and $`b` are minimally chosen positive integers and $`r` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .
:::

:::definition "gl2.cartan" (lean := "Matrix.GeneralLinearGroup.cartanSubgroup, Matrix.GeneralLinearGroup.canonicalInvolution, Matrix.GeneralLinearGroup.extendedCartanSubgroup, Matrix.GeneralLinearGroup.IsCartanSubgroup, Matrix.GeneralLinearGroup.IsExtendedCartanSubgroup")
*Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.cartan))

Let $`R` be a commutative ring.  Given a free rank $`2` etale $`R`-algebra $`A` equipped with a basis, any $`a \in A^\times` defines an $`R`-linear multiplication-by-$`a` map $`A \to A`, so we get an injective homomorphism $`A^\times \to \Aut_{\text{R-module}}(A) \simeq \GL_2(R)`, and the image is called a *Cartan subgroup* of $`\GL_2(R)`.  The canonical involution of the $`R`-algebra $`A` gives another element of $`\Aut_{\text{R-module}}(A)`; we call the group generated by it and the Cartan subgroup $`A^\times` the *extended Cartan subgroup*.  The Cartan subgroup has index $`2` in the extended Cartan subgroup.

If $`R=\F_p`, there are two possibilities for $`A`: the split algebra $`\F_p \times \F_p` and the nonsplit algebra $`\F_{p^2}`; the resulting Cartan subgroups are called {bpref "gl2.split_cartan"}[split] and {bpref "gl2.nonsplit_cartan"}[nonsplit].  The extended Cartan subgroup equals the normalizer of the Cartan subgroup in $`\GL_2(\F_p)` except when $`p=2` and $`A` is split.  In the split case, if we use the standard basis of $`\F_p \times \F_p`, the Cartan subgroup is the subgroup of diagonal matrices in $`\GL_2(\F_p)`, and the extended Cartan subgroup is this together with the coset of antidiagonal matrices in $`\GL_2(\F_p)`.

If $`R=\Z/p^e\Z`, again there are two possibilities for $`A`: the split algebra $`R \times R`, or the nonsplit algebra.  The nonsplit algebra can be described as $`\mathcal{O}/p^e \mathcal{O}` where $`\mathcal{O}` is either the degree $`2` unramified extension of $`\Z_p` or a quadratic order in which $`p` is inert.  The nonsplit algebra can also be described as the ring of length $`e` Witt vectors $`W_e(\F_{p^2})`.

If $`R=\Z/N\Z` for some $`N \ge 1`, then $`A` can be split or nonsplit independently at each prime dividing $`N`.
:::

:::definition "gl2.exceptional" (lean := "Matrix.GeneralLinearGroup.IsExceptionalSubgroup, Matrix.GeneralLinearGroup.projectiveImage, Matrix.GeneralLinearGroup.ExceptionalType, Matrix.GeneralLinearGroup.HasExceptionalType, Matrix.ProjGenLinGroup")
*Exceptional subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.exceptional))

An *exceptional subgroup* of $`\GL_2(\F_p)` does not contain $`\SL_2(\F_p)` and is not contained in a {bpref "gl2.borel"}[Borel subgroup] or in the {bpref "gl2.normalizer_cartan"}[normalizer of a Cartan subgroup].

Exceptional subgroups are classified according to their image in $`\PGL_2(\F_p)`, which must be isomorphic to one of the alternating groups $`A_4` or $`A_5`, or to the symmetric group $`S_4`.  These groups are labelled using identifiers containing one of the strings *A4*, *A5*, *S4*, as described in .

Depends on: {uses "gl2.borel"}[] {uses "gl2.normalizer_cartan"}[]
:::

:::definition "gl2.genus" (lean := "Matrix.GeneralLinearGroup.adelicGenus, Matrix.GeneralLinearGroup.padicGenus, Matrix.GeneralLinearGroup.reductionGenus, Subgroup.modularGenusFormula, Subgroup.numFixedRightCosets")
*Genus of a subgroup of $`\GL_2`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.genus))

The *genus* of an {bpref "gl2.open"}[open subgroup] $`H` of $`\GL_2(\widehat{\Z})` or $`\GL_2(\widehat{\Z}_{\ell})` of level $`N` is defined by the formula

$$`g(H) := g(\Gamma_H) := 1+\frac{i(\Gamma_H)}{12} - \frac{\nu_2(\Gamma_H)}{4} - \frac{\nu_3(\Gamma_H)}{3} - \frac{\nu_{\infty}(\Gamma_H)}{2},`

where $`\Gamma_H:=\pm H_N \cap \SL_2(\Z/N\Z)`, $`H_N` denotes the projection of $`H` onto $`\GL_2(\Z/N\Z)`, and

- $`i(\Gamma_H)=[\SL_2(\Z/N\Z):\Gamma_H]`,

- $`\nu_2` is the number of right cosets of $`\Gamma_H` in $`\SL_2(\Z/N\Z)` fixed by the right action of <small>$`\begin{bmatrix}0&1\\-1&0\end{bmatrix}`</small>,

- $`\nu_3` is the number of right cosets of $`\Gamma_H` in $`\SL_2(\Z/N\Z)` fixed by the right action of  matrix <small>$`\begin{bmatrix}0&1\\-1&-1\end{bmatrix}`</small>,

- $`\nu_{\infty}(\Gamma_H)` is the number of orbits of the right coset space $`\Gamma_H\backslash \SL_2(\Z/N\Z)` under the right action of <small>$`\begin{bmatrix}1&1\\0&1\end{bmatrix}`</small>.

The genus $`g(H)` is a nonnegative integer that equals the genus of each {bpref "ag.geom_component"}[geometric component] of the {bpref "modcurve"}[modular curve] $`X_H`.

This coincides with the genus of the Riemann surface $`\mathcal H^*/\Gamma`, where   $`\mathcal H^*` is the {bpref "mf.upper_half_plane"}[completed upper half-plane] and $`\Gamma` is the inverse image of $`\Gamma_H` in $`\SL_2(\Z)`.

Depends on: {uses "ag.geom_component"}[] {uses "gl2.open"}[] {uses "mf.upper_half_plane"}[] {uses "modcurve"}[]
:::

:::definition "gl2.index" (lean := "Subgroup.index, Subgroup.quotient_finite_of_isOpen, Subgroup.index_ne_zero_of_finite")
*Index of an open subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.index))

The *index* of an {bpref "gl2.open"}[open subgroup] $`H` of a {bpref "gl2.profinite"}[profinite group] $`G` is the positive integer $`[G:H]`.

When $`G` is a matrix group over $`\widehat{\Z}` or $`\Z_{\ell}` and $`H` is a subgroup of {bpref "gl2.level"}[level] $`N`, this is the same as the index of $`H` in the reduction of $`G` modulo $`N`.

Depends on: {uses "gl2.level"}[] {uses "gl2.open"}[] {uses "gl2.profinite"}[]
:::

:::definition "gl2.label"
Let $`H` be an {bpref "gl2.open"}[open subgroup] of $`\GL_2(\widehat{\Z})` for which $`\det(H)=\widehat{\Z}^\times`.  The *RSZB label* of $`H` has the form $`\texttt{N.i.g.n}`, where

- $`N` is the {bpref "gl2.level"}[level] of $`H`,

- $`i` is the {bpref "gl2.index"}[index] of $`H`,

- $`g` is the {bpref "gl2.genus"}[genus] of $`H`, and

- $`n` is a positive integer that distinguishes nonconjugate subgroups of the same level, index, and genus.

The positive integer $`n` is defined by ordering the subgroups of $`\GL_2(\Z/n\Z)` as described in Section 2.4 of .

When $`\det(H)\ne \widehat{\Z}^\times` the *RSZB label* of $`H` has the form $`\texttt{M.d.m-N.i.g.n}`, where $`\texttt{M.d.m}` identifies the open subgroup $`\det(H)\le \GL_1(\widehat{\Z})` in terms of its level $`M`, index $`d`, and a positive integer $`m` that is defined by ordering the open subgroups of $`\GL_1(\widehat{\Z})` via the lexicographic ordering of the Conrey labels in the corresponding group of Dirichlet characters of modulus $`M`.  In this case the index $`i` is taken relative to the inverse image of $`\det(H)` in $`\GL_2(\widehat{\Z})`.

This convention is also used to label open subgroups of $`\GL_2(\Z_{\ell})` and arbitrary subgroups of $`\GL_2(\Z/n\Z)` by using the label of the inverse image of $`H` in $`\GL_2(\widehat{\Z})`.

Depends on: {uses "gl2.genus"}[] {uses "gl2.index"}[] {uses "gl2.level"}[] {uses "gl2.open"}[]
:::

:::definition "gl2.level" (lean := "Matrix.GeneralLinearGroup.adelicLevel, Matrix.GeneralLinearGroup.adelicReduction, Matrix.GeneralLinearGroup.adelicLevel_pos, Matrix.GeneralLinearGroup.padicLevel, Matrix.GeneralLinearGroup.exists_padicLevel_eq_pow_of_isOpen")
*Level of an open subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.level))

The *level* of an {bpref "gl2.open"}[open subgroup] $`H` of a matrix group $`G` over $`\widehat{\Z}` is the least positive integer $`N` for which $`H` is equal to the inverse image of its projection to the reduction of $`G` modulo $`N`.

This also applies to open subgroups of matrix groups over $`\Z_{\ell}`, in which case the level is necessarily a power of $`\ell`.

Depends on: {uses "gl2.open"}[]
:::

:::definition "gl2.nonsplit_cartan" (lean := "Matrix.GeneralLinearGroup.IsNonsplitCartanSubgroup, Matrix.GeneralLinearGroup.labelCn, Matrix.GeneralLinearGroup.mem_labelCn_iff, Matrix.GeneralLinearGroup.labelCn_two_eq_of_index_eq_two, Matrix.GeneralLinearGroup.labelCnAB")
*Non-split Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.nonsplit_cartan))

A *non-split Cartan subgroup* of $`\GL_2(\F_p)` is a {bpref "gl2.cartan"}[Cartan subgroup] that is not diagonalizable over $`\F_p`.  Every non-split Cartan subgroup is a cyclic group isomorphic to $`\F_{p^2}^\times`.

For $`p=2` the label *Cn* identifies the unique index 2 subgroup of $`\GL_2(\F_2)`.
For $`p>2` the label *Cn* identifies the nonsplit Cartan subgroup consisting of matrices of the form

$$`\begin{pmatrix}x&\varepsilon y\\y&x\end{pmatrix},`

with $`x,y\in \F_p` not both zero and $`\varepsilon` the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`,  corresponding to $`x+y\sqrt{\varepsilon}\in\F_{p^2}^\times`.  Every non-split Cartan subgroup is conjugate to the group *Cn*.

Labels of the form *Cn.a.b* identify the proper subgroup of *Cn* generated by the matrix

$$`\begin{pmatrix}a&\varepsilon b\\b&a\end{pmatrix},`

where $`a` and $`b` are minimally chosen positive integers and $`\varepsilon` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .

Depends on: {uses "gl2.cartan"}[]
:::

:::definition "gl2.normalizer_cartan" (lean := "Matrix.GeneralLinearGroup.IsCartanNormalizer, Subgroup.normalizer, Matrix.GeneralLinearGroup.extendedCartanSubgroup_le_normalizer")
*Normalizer of a Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.normalizer_cartan))

For $`p>2` the *normalizer of a Cartan subgroup* of $`\GL_2(\F_p)` is a maximal subgroup of $`\GL_2(\F_p)` that contains a {bpref "gl2.cartan"}[Cartan subgroup] with index 2.  It is the normalizer in $`\GL_2(\F_p)` of the Cartan subgroup it contains.

For $`p=2` the Cartan subgroups of $`\GL_2(\F_2)` are already normal and we instead define the normalizer of a Cartan subgroup to be a group that contains a Cartan subgroup with index 2.  This means that the normalizer of a split Cartan subgroup of $`\GL_2(\F_2)` has order 2 (which makes it conjugate to the Borel subgroup), while the normalizer of a non-split Cartan subgroup of $`\GL_2(\F_2)` has order 6 (which makes it all of $`\GL_2(\F_2)`).

Depends on: {uses "gl2.cartan"}[]
:::

:::definition "gl2.normalizer_nonsplit_cartan" (lean := "Matrix.GeneralLinearGroup.IsNonsplitCartanNormalizer, Matrix.GeneralLinearGroup.labelNn, Matrix.GeneralLinearGroup.labelNn_eq_sup, Matrix.GeneralLinearGroup.labelNn_two, Matrix.GeneralLinearGroup.labelNnAB")
*Normalizer of a non-split Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.normalizer_nonsplit_cartan))

For $`p>2` the *normalizer of a non-split Cartan subgroup* of $`\GL_2(\F_p)` is a maximal subgroup of $`\GL_2(\F_p)` that contains a {bpref "gl2.nonsplit_cartan"}[non-split Cartan subgroup] with index 2,
and it is the normalizer in $`\GL_2(\F_p)` of the non-split Cartan subgroup it contains.  For $`p=2` the normalizer of a non-split Cartan subgroup is defined to be all of $`\GL_2(\F_2)`, which contains its (already normal) non-split Cartan subgroup with index 2.

For $`p>2` the label *Nn* identifies the normalizer of the nonsplit Cartan subgroup generated by the non-split Cartan subgroup *Cn* and the matrix

$$`\begin{pmatrix}1&0\\0&-1\end{pmatrix},`

and every normalizer of a non-split Cartan subgroup is conjugate to the group *Nn*.

The label *Nn.a.b* denotes the proper subgroup of the normalizer of the nonsplit Cartan subgroup *Nn* generated by the matrices

$$`\begin{pmatrix}a&\varepsilon b\\b&a\end{pmatrix}, \begin{pmatrix}1&0\\0&-1\end{pmatrix}.`

where $`a` and $`b` are minimally chosen positive integers and $`\varepsilon` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .

Depends on: {uses "gl2.nonsplit_cartan"}[]
:::

:::definition "gl2.normalizer_split_cartan" (lean := "Matrix.GeneralLinearGroup.IsSplitCartanNormalizer, Matrix.GeneralLinearGroup.labelNs, Matrix.GeneralLinearGroup.isSplitCartanNormalizer_labelNs, Matrix.GeneralLinearGroup.labelNsAB, Matrix.GeneralLinearGroup.labelNsABC")
*Normalizer of a split Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.normalizer_split_cartan))

The *normalizer of a split Cartan subgroup* of $`\GL_2(\F_p)` is a maximal subgroup of $`\GL_2(\F_p)` that contains a {bpref "gl2.split_cartan"}[split Cartan subgroup] with index 2.  For $`p>2` such a group is in fact the normalizer in $`\GL_2(\F_p)` of the split Cartan subgroup it contains, but for $`p=2` this is not the case (the split Cartan subgroup of $`\GL_2(\F_2)` is already normal).

The label *Ns* identifies the subgroup generated by the split Cartan subgroup *Cs* of diagonal matrices and the matrix

$$`\begin{pmatrix}0&1\\1&0\end{pmatrix}.`

Every normalizer of a split Cartan subgroup is conjugate to the group *Ns*.

The label *Ns.a.b* identifies the proper subgroup of *Ns* generated by the matrices

$$`\begin{pmatrix}a&0\\0&1/a\end{pmatrix}, \begin{pmatrix}0&b\\-r/b&0\end{pmatrix},`

where $`a` and $`b` are minimally chosen positive integers and $`r` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`.

The label *Ns.a.b.c*  identifies the proper subgroup of the normalizer of the split Cartan subgroup generated by the matrices

$$`\begin{pmatrix}a&0\\0&1/a\end{pmatrix}, \begin{pmatrix}0&b\\-1/b&0\end{pmatrix}, \begin{pmatrix}0&c\\-r/c&0\end{pmatrix}`

where $`a` and $`b` are minimally chosen positive integers and $`r` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .

Depends on: {uses "gl2.split_cartan"}[]
:::

:::definition "gl2.open" (lean := "OpenSubgroup")
*Open subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.open))

An *open subgroup* $`H` of a {bpref "gl2.profinite"}[profinite group] $`G` is a subgroup that is open in the topology of $`G`, which implies that it is equal to the inverse image of its projection to a a finite quotient of $`G`.

Open subgroups of $`G` necessarily have finite index (since $`G` is compact), but not every finite index subgroup of $`G` is necessarily open.

When the profinite group $`G` is a matrix group over a ring $`R` that is equipped with canonical projections to finite rings of the form $`\Z/n\Z` (take $`R=\Z_{\ell}` or $`R=\widehat{\Z}`, for example), we use $`G(n)` to denote the image of $`G` under the group homomorphism induced by the projection $`R\to\Z/n\Z`.  In this situation we may identify $`H` with its projection to $`G(N)`, where $`N` is the least positive integer for which $`H` is the inverse image of its projection to $`G(N)` (this $`N` is the {bpref "gl2.level"}[level] of $`H`).

Depends on: {uses "gl2.profinite"}[]
:::

:::definition "gl2.profinite" (lean := "ProfiniteGrp")
*Profinite group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.profinite))

A *profinite group* is a compact totally disconnected topological group.  Equivalently, it is the inverse limit of a system of finite groups equipped with the discrete topology.

For example, if we take the finite groups $`\GL_2(\Z/n\Z)` as $`n` varies over positive integers, order them by divisibility of $`n` and consider the inverse system equipped with reduction maps $`\GL_2(\Z/n\Z)\to \GL_2(\Z/m\Z)` for all positive integers $`m|n`, then the inverse limit

$$`\lim_{\overset{\longleftarrow}{n}} \GL_2(\Z/n\Z) \simeq \GL_2(\widehat{\Z})`

is a profinite group which is isomorphic to the group of invertible $`2\times 2` matrices over the topological ring $`\widehat{\Z}`, which is the inverse limit of the finite rings $`\Z/n\Z` equipped with the discrete topology.
:::

:::definition "gl2.split_cartan" (lean := "Matrix.GeneralLinearGroup.IsSplitCartanSubgroup, TauCeti.diagonalTorus, Matrix.GeneralLinearGroup.cartanSubgroup_piBasisFun, Matrix.GeneralLinearGroup.isSplitCartanSubgroup_diagonalTorus, Matrix.GeneralLinearGroup.labelCsAB")
*Split Cartan subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/gl2.split_cartan))

A *split Cartan subgroup* of $`\GL_2(\F_p)` is a {bpref "gl2.cartan"}[Cartan subgroup] that is diagonalizable over $`\F_p`.  Every split Cartan subgroup is conjugate to the subgroup of diagonal matrices, which is isomorphic to $`\F_p^\times\times\F_p^\times`.

The label *Cs* identifies the split Cartan subgroup of diagonal matrices.

The label *Cs.a.b* identifies the proper subgroup of *Cs* generated by

$$`\begin{pmatrix}a&0\\0&1/a\end{pmatrix}, \begin{pmatrix}b&0\\0&r/b\end{pmatrix},`

where $`a` and $`b` are minimally chosen positive integers and $`r` is the least positive integer generating $`(\Z/p\Z)^\times\simeq \F_p^\times`, as defined in .

Depends on: {uses "gl2.cartan"}[]
:::

:::definition "ring" (lean := "Ring, CommRing, NonUnitalRing")
*Definition of ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring))

A *ring* is a set $`R` with two {bpref "alg.binary_operation"}[binary operations] $`+` and $`\cdot` such that

1. $`R` is an {bpref "group.abelian"}[abelian group] with respect to $`+`
2. $`\cdot` is {bpref "alg.binary_operation.associative"}[associative] on $`R`
3. the distributive laws hold, i.e., for all $`a,b,c\in R`,

$$`a\cdot(b+c) = a\cdot b+a\cdot c \qquad \text{and}\qquad (b+c)\cdot a = b\cdot a+c\cdot a`

4. there is an {bpref "alg.binary_operation.identity"}[identity element] with respect to the operation $`\cdot`, typically denoted by $`1_R` or, more simply, by $`1`.

The {bpref "alg.binary_operation.identity"}[identity] element of $`R` as a group with respect to $`+` is typically denoted by $`0_R` or, more simply, by $`0`.

The ring $`R` is a *commutative ring* if $`R` is a ring such that the operation $`\cdot` is {bpref "alg.binary_operation.commutative"}[commutative] on $`R`.

We say that $`R` is a *rng* (also called *ring without identity* or *non-unital ring*) if conditions 1-3 (but not necessarily 4) are satisfied.

Depends on: {uses "alg.binary_operation"}[] {uses "alg.binary_operation.associative"}[] {uses "alg.binary_operation.commutative"}[] {uses "alg.binary_operation.identity"}[] {uses "group.abelian"}[]
:::

:::definition "ring.a-field" (lean := "Algebra, Field")
*$`A`-field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.a-field))

Let $`A` be a commutative ring.  An *$`A`-field* is an $`A`-algebra that is a {bpref "ring.field"}[field].

Depends on: {uses "ring.field"}[]
:::

:::definition "ring.associate" (lean := "Associated, Associated.setoid")
*Associate of an element.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.associate))

If $`R` is a {bpref "ring"}[commutative ring], two elements $`x, y \in R` are *associates* if there is a {bpref "ring.unit"}[unit] $`u \in R` with $`y = ux`.  This defines an equivalence relation on the elements of $`R`.

Depends on: {uses "ring"}[] {uses "ring.unit"}[]
:::

:::definition "ring.characteristic" (lean := "ringChar, CharP, CharP.addOrderOf_one, CharP.char_is_prime_or_zero")
*Characteristic of a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.characteristic))

The *characteristic* of a {bpref "ring"}[ring] is the least positive integer $`n` for which

$$`\underbrace{1+\cdots + 1}_n = 0,`

if such an $`n` exists, and $`0` otherwise. Equivalently, it is the exponent of the additive {bpref "group"}[group] of the ring.

The characteristic of a {bpref "ring.field"}[field] $`k` is either $`0` or a prime number $`p`, depending on whether the prime field of $`k` is isomorphic to $`\Q` or $`\F_p`.

Depends on: {uses "group"}[] {uses "ring"}[] {uses "ring.field"}[]
:::

:::definition "ring.dedekind_domain" (lean := "IsDedekindDomain")
*Dedekind domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.dedekind_domain))

A *Dedekind domain* $`D` is a {bpref "ring.integral_domain"}[integral domain] which is not a {bpref "ring.field"}[field] such that

1. $`D` is {bpref "ring.noetherian"}[Noetherian];
2. every non-zero {bpref "ring.prime_ideal"}[prime ideal] is {bpref "ring.maximal_ideal"}[maximal];
3. $`D` is {bpref "ring.integrally_closed"}[integrally closed].

The {bpref "nf.ring_of_integers"}[ring of integers] of a {bpref "nf"}[number field] is always a Dedekind domain, as is every discrete valuation ring.

In a Dedekind domain, every non-zero {bpref "ring.ideal"}[ideal] $`I` can be written as a product of non-zero {bpref "ring.prime_ideal"}[prime ideals],

$$`I=P_1P_2\cdots P_k,`

and the product is unique up to the order of the factors.  Repeated factors are often grouped, so we write $`I=Q_1^{e_1}\cdots Q_g^{e_g}` where the $`Q_i` are non-zero prime ideals of $`D`.

In addition, every {bpref "ring.fractional_ideal"}[fractional ideal] $`I` is invertible in the sense that there exists a fractional ideal $`J` such that $`IJ=D`.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[] {uses "ring.field"}[] {uses "ring.fractional_ideal"}[] {uses "ring.ideal"}[] {uses "ring.integral_domain"}[] {uses "ring.integrally_closed"}[] {uses "ring.maximal_ideal"}[] {uses "ring.noetherian"}[] {uses "ring.prime_ideal"}[]
:::

:::definition "ring.euclidean_domain" (lean := "IsNatEuclidean, IsNatEuclidean.toEuclideanDomain, IsNatEuclidean.isPrincipalIdealRing, EuclideanDomain")
*Euclidean domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.euclidean_domain))

An *Euclidean domain* is an {bpref "ring.integral_domain"}[integral domain] $`R` with a function

$$`\nu: R-\{0\}\to \Z_{\geq 0}`

such that for all $`a\in R` and all $`b\in R-\{0\}`, there exists $`q,r\in R` such that $`a=bq+r` and $`r=0` or $`\nu(r)<\nu(b)`.

Euclidean domains are {bpref "ring.principal_ideal_domain"}[principal ideal domains], and hence, {bpref "ring.unique_factorization_domain"}[unique factorization domains].

Depends on: {uses "ring.integral_domain"}[] {uses "ring.principal_ideal_domain"}[] {uses "ring.unique_factorization_domain"}[]
:::

:::definition "ring.field" (lean := "Field")
*Field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.field))

A *field* is a {bpref "ring"}[commutative ring] $`R` such that $`0_R\neq 1_R` and every nonzero element of $`R` has an {bpref "alg.binary_operation.inverse"}[inverse] in $`R` with respect to multiplication.

Depends on: {uses "alg.binary_operation.inverse"}[] {uses "ring"}[]
:::

:::definition "ring.field_of_fractions" (lean := "FractionRing, IsFractionRing, FractionRing.field, IsFractionRing.lift, FractionRing.algEquiv")
*Field of fractions of an integral domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.field_of_fractions))

If $`R` is an {bpref "ring.integral_domain"}[integral domain], then its *field of fractions* $`F` is the smallest {bpref "ring.field"}[field] containing $`R`.

It can be constructed by mimicking the set of fractions $`a/b` where $`a,b\in R` with $`b\neq 0` following the usual rules for fraction arithmetic.  It is unique, up to unique isomorphism.

Depends on: {uses "ring.field"}[] {uses "ring.field_of_fractions_mathlib"}[] {uses "ring.integral_domain"}[]
:::

:::definition "ring.field_of_fractions_mathlib" (lean := "FractionRing")
*Field of fractions (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.field_of_fractions_mathlib))

This is also defined in mathlib as *Fraction Ring*, which is the localisation at the non-zero divisors of your ring. When your ring $`R` is a {bpref "ring"}[commutative ring] and an {bpref "ring"}[integral domain] then gets the fact that this is a field.

Depends on: {uses "ring"}[]
:::

:::definition "ring.fractional_ideal" (lean := "FractionalIdeal")
*Fractional ideal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.fractional_ideal))

If $`R` is an {bpref "ring.integral_domain"}[integral domain] with {bpref "ring.field_of_fractions"}[field of fractions] $`K`, then a *fractional ideal* $`I` of $`R` is an $`R`-submodule of $`K` such that there exists $`d\in R-\{0\}` with
$$`dI=\{da\mid a\in I\} \subseteq R\,.`

Depends on: {uses "ring.field_of_fractions"}[] {uses "ring.integral_domain"}[]
:::

:::definition "ring.ideal" (lean := "TwoSidedIdeal, Ideal, Ideal.IsHomogeneous, MvPolynomial.gradedAlgebra, Ideal.IsHomogeneous.iff_exists")
*Ideal of a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.ideal))

If $`R` is a {bpref "ring"}[ring], a subset $`I\subseteq R` is an *ideal* of $`R` if $`I` is a {bpref "group.subgroup"}[subgroup] of $`R` for $`+` and for all $`a\in I` and all $`r\in R`,

$$`r\cdot a\in I \qquad\text{and}\qquad a\cdot r\in I.`

In a polynomial ring $`R[X_1,\dots,X_n]`, an ideal is *homogeneous* if it can be generated by homogeneous polynomials.

Depends on: {uses "group.subgroup"}[] {uses "ring"}[]
:::

:::definition "ring.integral" (lean := "IsIntegral, integralClosure")
*Integral element of a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.integral))

If $`R\subseteq S` are {bpref "ring"}[commutative rings], an element $`s\in S` is *integral* over $`R` if there exists $`n\in\Z^+` and $`a_i\in R` such that

$$`s^n+a_{n-1} s^{n-1}+\cdots + a_0 =0\,.`

The *integral closure* of $`R` in $`S` is $`\{s\in S\mid s \text{ is integral over } R\}`.

Depends on: {uses "ring"}[]
:::

:::definition "ring.integral_domain" (lean := "IsDomain")
*Integral domain.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.integral_domain))

An *integral domain* is a {bpref "ring"}[commutative ring] $`R` such that $`1_R\neq 0_R` and $`R` contains no {bpref "ring.zero_divisor"}[zero divisors].

Depends on: {uses "ring"}[] {uses "ring.zero_divisor"}[]
:::

:::definition "ring.integrally_closed" (lean := "IsIntegrallyClosed")
*Integrally closed.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.integrally_closed))

Let $`R` be an {bpref "ring.integral_domain"}[integral domain] and $`F` its {bpref "ring.field_of_fractions"}[field of fractions].  Then $`R` is *integrally closed* if $`R` equals the {bpref "ring.integral"}[integral closure] of $`R` in $`F`.

Depends on: {uses "ring.field_of_fractions"}[] {uses "ring.integral"}[] {uses "ring.integral_domain"}[]
:::

:::definition "ring.irreducible" (lean := "Irreducible")
*Irreducible element.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.irreducible))

An element $`x \ne 0` of a {bpref "ring"}[commutative ring] $`R` is *irreducible* if it is not a {bpref "ring.unit"}[unit] and has the property that  whenever $`x=yz` for some $`y,z \in R`, either $`y` or $`z` is a unit.

Depends on: {uses "ring"}[] {uses "ring.unit"}[]
:::

:::definition "ring.maximal_ideal" (lean := "Ideal.IsMaximal")
*Maximal ideal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.maximal_ideal))

In a {bpref "ring"}[ring] $`R`, an {bpref "ring.ideal"}[ideal] $`M` is *maximal* if $`M\neq R` and for all ideals $`I` of $`R`,

$$`M\subseteq I \subseteq R\implies M=I\quad\text{or}\quad I=R.`

Depends on: {uses "ring"}[] {uses "ring.ideal"}[]
:::

:::definition "ring.noetherian" (lean := "IsNoetherianRing")
*Noetherian ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.noetherian))

A {bpref "ring"}[commutative ring] $`R` is *Noetherian* if for every ascending chain of {bpref "ring.ideal"}[ideals]

$$`I_1\subseteq I_2\subseteq I_3\subseteq \cdots`

there exists $`N` such that for all $`n\geq N`, $`I_n=I_N`.

Depends on: {uses "ring"}[] {uses "ring.ideal"}[]
:::

:::definition "ring.prime_ideal" (lean := "Ideal.IsPrime")
*Prime ideal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.prime_ideal))

If $`R` is a {bpref "ring"}[commutative ring] $`R`, an {bpref "ring.ideal"}[ideal] $`I \ne R` is *prime* if for all $`a,b\in R`,

$$`ab\in I \implies a\in I \quad \text{or}\quad b\in I.`

Depends on: {uses "ring"}[] {uses "ring.ideal"}[]
:::

:::definition "ring.principal_fractional_ideal" (lean := "FractionalIdeal.spanSingleton, toPrincipalIdeal, FractionalIdeal.mem_spanSingleton")
*Principal fractional ideal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.principal_fractional_ideal))

Let $`R` be an {bpref "ring.integral_domain"}[integral domain] with {bpref "ring.field_of_fractions"}[field of fractions] $`K`.  If $`a\in K^\times`, then the *principal fractional ideal* generated by $`a` is the set

$$`\{ar\mid r\in R\}\,.`

Depends on: {uses "ring.field_of_fractions"}[] {uses "ring.integral_domain"}[]
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

:::definition "ring.unit" (lean := "IsUnit")
*Unit in a ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.unit))

A *unit* in a {bpref "ring"}[commutative ring] $`R` is an element $`x \in R` so that there exists $`y \in R` with $`xy = 1`.  The set of units in $`R` is denoted $`R^*` or $`R^\times` and forms a {bpref "group"}[group] under multiplication.

Depends on: {uses "group"}[] {uses "ring"}[]
:::

:::definition "ring.zero_divisor" (lean := "nonZeroDivisors, notMem_nonZeroDivisors_iff")
*Zero divisor.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/ring.zero_divisor))

An element $`a` in a {bpref "ring"}[ring] $`R` is a *zero divisor* if $`a\neq 0_R` and there exists an element $`b\in R-\{0_R\}` such that

$$`a\cdot b = 0_R \qquad \text{or}\qquad b\cdot a = 0_R.`

Depends on: {uses "ring"}[]
:::
