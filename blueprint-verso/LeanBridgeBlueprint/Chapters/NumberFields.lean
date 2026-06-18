import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Number fields" =>

This chapter lists the LMFDB definitions relating to *number fields*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "nf"
*Number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf))

\leanok
A *number field* is a finite degree field extension of the field $`\Q` of rational numbers. In LMFDB, number fields are identified by a label.

Depends on: {uses "nf.degree"}[]
:::

:::definition "nf.abelian"
*Abelian number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.abelian))

A {bpref "nf"}[number field] $`K` is *abelian* if it is Galois over $`\Q` and its {bpref "nf.galois_group"}[Galois group] $`\Gal(K/\Q)` is abelian.

Depends on: {uses "nf"}[] {uses "nf.galois_group"}[]
:::

:::definition "nf.abs_discriminant"
*Absolute discriminant of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.abs_discriminant))

The *absolute discriminant* of a {bpref "nf"}[number field] is the absolute value of its {bpref "nf.discriminant"}[discriminant].

Depends on: {uses "nf"}[] {uses "nf.discriminant"}[]
:::

:::definition "nf.absolute_value"
*Absolute value of a field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.absolute_value))

An *absolute value* of a field $`k` is a function $`|\ |:k\to \R_{\ge 0}` that satisfies:

- $`|x|=0` if and only if $`x=0`;

- $`|xy| = |x||y|`;

- $`|x+y| \le |x|+|y|`.

Absolute values that satisfy the stronger condition $`|x+y|\le \max(|x|,|y|)` are *nonarchimedean*, while those that do not are *archimedean*; the latter arise only in fields of characteristic zero.  The *trivial absolute value* assigns 1 to every nonzero element of $`k`; it is a nonarchimedean absolute value.

Absolute values $`|\ |_1` and $`|\ |_2` are *equivalent* if there exists a positive real number $`c` such that $`|x|_1 = |x|_2^c` for all $`x\in k`; this defines an equivalence relation on the set of absolute values of $`k`.
:::

:::definition "nf.arithmetically_equivalent"
*Arithmetically equivalent fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.arithmetically_equivalent))

Two {bpref "nf"}[number fields] are *arithmetically equivalent* if they have the same Dedekind $`\zeta`-functions. Arithmetically equivalent fields share many invariants, such as their {bpref "nf.degree"}[degrees], {bpref "nf.signature"}[signatures], {bpref "nf.discriminant"}[discriminants], and {bpref "nf.galois_group"}[Galois groups].  For a given field, the existence of an arithmetically equivalent {bpref "nf.sibling"}[sibling] depends only on the Galois group.

Depends on: {uses "nf"}[] {uses "nf.degree"}[] {uses "nf.discriminant"}[] {uses "nf.galois_group"}[] {uses "nf.sibling"}[] {uses "nf.signature"}[]
:::

:::definition "nf.class_number"
*Class number of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.class_number))

The *class number* of a {bpref "nf"}[number field] $`K` is the order of the {bpref "nf.ideal_class_group"}[ideal class group] of $`K`.

Depends on: {uses "nf"}[] {uses "nf.ideal_class_group"}[]
:::

:::definition "nf.class_number_formula"
*Analytic class number formula.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.class_number_formula))

If $`K` is a {bpref "nf"}[number field] with {bpref "nf.signature"}[signature] $`(r_1, r_2)`, {bpref "nf.discriminant"}[discriminant] $`D`, {bpref "nf.regulator"}[regulator] $`R`, {bpref "nf.class_number"}[class number] $`h`, containing $`w` roots of unity, and Dedekind $`\zeta`-function $`\zeta_K`, then $`\zeta_K` has a meromorphic continuation to the whole complex plane with a single pole at $`s=1`, which is of order $`1`.  The *analytic class number formula* gives the residue at this pole:

$$`\lim_{s\to 1}\ (s-1)\zeta_K(s) = \frac{2^{r_1}\cdot (2\pi)^{r_2}\cdot R\cdot  h}{w\cdot\sqrt{|D|}} .`

Depends on: {uses "nf"}[] {uses "nf.class_number"}[] {uses "nf.discriminant"}[] {uses "nf.regulator"}[] {uses "nf.signature"}[]
:::

:::definition "nf.cm_field"
*CM number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.cm_field))

A *CM field* is a {bpref "nf.totally_imaginary"}[totally complex] quadratic extension of a {bpref "nf.totally_real"}[totally real] {bpref "nf"}[number field].

Depends on: {uses "nf"}[] {uses "nf.totally_imaginary"}[] {uses "nf.totally_real"}[]
:::

:::definition "nf.complex_embedding"
*Complex embedding.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.complex_embedding))

A *complex embedding* of a {bpref "nf"}[number field] $`K` is a nonzero field homomorphism $`K\to \C` whose image is not contained in $`\R`.

A single number field may have several distinct complex embeddings.

For $`K=\Q(a)` where $`a` is an algebraic number with {bpref "nf.minimal_polynomial"}[minimal polynomial] $`f(X)`, the embeddings $`\iota:K\to\C` are determined by the value $`z=\iota(a)` which is one of the complex roots of $`f(X)`, and the embedding is complex when $`z\notin\R`.  The complex embeddings come in conjugate pairs.

Depends on: {uses "nf"}[] {uses "nf.minimal_polynomial"}[]
:::

:::definition "nf.conductor"
*Conductor of an abelian number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.conductor))

If a {bpref "nf"}[number field] $`K` is {bpref "nf.abelian"}[abelian], then $`K\subseteq \Q(\zeta_n)` for some positive integer $`n`.  The minimum such $`n` is the *conductor* of $`K`.

Depends on: {uses "nf"}[] {uses "nf.abelian"}[]
:::

:::definition "nf.defining_polynomial"
*Defining Polynomial of a Number Field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.defining_polynomial))

A *defining polynomial* of a {bpref "nf"}[number field] $`K` is an irreducible polynomial $`f\in\Q[x]` such that $`K\cong \mathbb{Q}(a)`, where $`a` is a root of $`f(x)`. Equivalently, it is a polynomial $`f\in \Q[x]` such that $`K \cong \Q[x]/(f)`.

A root $`a \in K` of the defining polynomial is a {bpref "nf.generator"}[generator] of $`K`.

Depends on: {uses "nf"}[]
:::

:::definition "nf.degree"
*Degree of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.degree))

The *degree* of a {bpref "nf"}[number field] $`K` is its degree as an extension of the rational field $`\mathbb{Q}`, i.e., the dimension of $`K` as a $`\mathbb{Q}`-vector space.  The degree of $`K/\Q` is written $`[K:\mathbb{Q}]`.
:::

:::definition "nf.dirichlet_group"
*Dirichlet group of an Abelian number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.dirichlet_group))

If $`K` is an {bpref "nf.abelian"}[abelian number field], then $`K\subseteq \Q(\zeta_n)` for some positive integer $`n`.  Take the minimal such $`n`, i.e., the {bpref "nf.conductor"}[conductor] of $`K`.

The Galois group $`\Gal(\Q(\zeta_n)/\Q)` is canonically isomorphic to $`\Z_n^\times`.  The {bpref "character.dirichlet"}[Dirichlet characters] modulo $`n` form the dual group of homomorphisms $`\chi:\Z_n^\times\to\C^\times`.  Since $`\Gal(K/\Q)` is a quotient group of $`\Gal(\Q(\zeta_n)/\Q)`, its dual group is a subgroup of the group of Dirichlet characters modulo $`n`, called the *Dirichlet character group* of $`K`.

Depends on: {uses "character.dirichlet"}[] {uses "nf.abelian"}[] {uses "nf.conductor"}[]
:::

:::definition "nf.discriminant"
*Discriminant of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.discriminant))

The *discriminant* of a {bpref "nf"}[number field] $`K` is the square of the determinant of the matrix

$$`\left( \begin{array}{ccc}
 \sigma_1(\beta_1) & \cdots & \sigma_1(\beta_n) \\
\vdots & & \vdots \\
\sigma_n(\beta_1) & \cdots & \sigma_n(\beta_n) \\
\end{array} \right)`

where $`\sigma_1,..., \sigma_n` are the embeddings of $`K` into the complex numbers $`\mathbb{C}`, and $`\{\beta_1, \ldots, \beta_n\}` is an {bpref "nf.integral_basis"}[integral basis] for the ring of integers of $`K`.

The discriminant of $`K` is a non-zero integer divisible exactly by the primes which {bpref "nf.ramified_primes"}[ramify] in $`K`.

Depends on: {uses "nf"}[] {uses "nf.integral_basis"}[]
:::

:::definition "nf.discriminant_root_field"
*Discriminant root field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.discriminant_root_field))

If $`K/F` is a finite algebraic extension, it can be defined by a polynomial $`f(x)\in F[x]`.  The polynomial discriminant, $`\mathrm{disc}(f)`, is well-defined up a factor of a non-zero square.  The *discriminant root field* of the extension is $`F(\sqrt{\mathrm{disc}(f)})`, which is well-defined.

If $`n=[K:F]`, then the Galois group $`G` for $`K/F` is a subgroup of $`S_n`, well-defined up to conjugation.  The discriminant root field can alternatively be described as the fixed field of $`G\cap A_n`.
:::

:::definition "nf.embedding"
*Embedding of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.embedding))

An *embedding* of a {bpref "nf"}[number field] $`K` is a field homomorphism $`K\to \C`.  A number field of {bpref "nf.degree"}[degree] $`n` has $`n` distinct embeddings, which may be distinguished as {bpref "nf.real_embedding"}[real] or {bpref "nf.complex_embedding"}[complex] depending on whether the image of the embedding is contained in $`\R` or not.

Complex embeddings necessarily come in conjugate pairs.  The {bpref "nf.signature"}[signature] of a number field is determined by the number of real embeddings and the number of pairs of conjugate complex embeddings.

For $`K=\Q(a)`, where $`a` is an algebraic number with {bpref "nf.minimal_polynomial"}[minimal polynomial] $`f(X)`, each embedding $`\iota` is uniquely determined by the value $`z=\iota(a)`, which is one of the complex roots of $`f(X)`. The embedding is real if $`z\in\R` and complex if $`z\notin\R`.

Depends on: {uses "nf"}[] {uses "nf.complex_embedding"}[] {uses "nf.degree"}[] {uses "nf.minimal_polynomial"}[] {uses "nf.real_embedding"}[] {uses "nf.signature"}[]
:::

:::definition "nf.frobenius_cycle_types"
*Frobenius cycle types.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.frobenius_cycle_types))

If $`K` is a degree $`n` extension of $`\mathbb{Q}`, $`\hat{K}` its normal closure and $`G=\text{Gal}(\hat{K}/\mathbb{Q})`, then $`G` acts on the set of $`n` embeddings of $`K\to \hat{K}` giving an embedding $`G\to S_n`.  Let $`\mathcal{O}_K` be the ring of integers of $`K` and $`p` a prime number.  Then

$$`p\mathcal{O}_K = P_1^{e_1}\cdots P_g^{e_g}`

where the $`P_i` are distinct prime ideals of $`\mathcal{O}_K`.  The prime $`p` is *unramified* if $`e_i=1` for all $`i`.

Suppose hereafter that $`p` is unramified. For each $`P_i`, there is a unique element
of $`G` that fixes $`P_i` and acts on the quotient $`\mathcal{O}_K/P_i` via the Frobenius automorphism $`x \mapsto x^p`; this element is the *Frobenius element* associated to $`P_i`. The Frobenius elements associated to the different $`P_i` are conjugate to each other, so their images in $`S_n` all have the same lengths of cycles in their disjoint cycle decompositions. This is the *Frobenius cycle type* of $`p`.

Alternatively, for each prime $`P_i`, its *residue degree* $`f_i` is defined by $`|\mathcal{O}_K/P_i| = p^{f_i}`.  The list of $`f_i` is the same partition of $`n` as the cycle decomposition described above.
:::

:::definition "nf.fundamental_units"
*Fundamental units of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.fundamental_units))

A minimal set of generators of a maximal torsion-free subgroup of the {bpref "nf.unit_group"}[unit group] of a {bpref "nf"}[number field] $`K` is called a set of *fundamental units* for $`K`.

Depends on: {uses "nf"}[] {uses "nf.unit_group"}[]
:::

:::definition "nf.galois_closure"
*Galois closure of an extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.galois_closure))

If $`K` is a {bpref "nf.separable"}[separable] algebraic extension of a field $`F`, then its *Galois closure* is the smallest extension field, in terms of inclusion, which contains $`K` and is Galois over $`F`.  If $`K=F(\alpha)` where $`\alpha` has irreducible polynomial $`f` over $`F`, then the Galois closure of $`K` is the splitting field of $`f` over $`F`.

Depends on: {uses "nf.separable"}[]
:::

:::definition "nf.galois_group"
*Galois group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.galois_group))

Let $`K` be a finite {bpref "nf.degree"}[degree] $`n` {bpref "nf.separable"}[separable extension] of a {bpref "ring.field"}[field] $`F`, and $`K^{gal}` be its
{bpref "nf.galois_closure"}[Galois (or normal) closure].
The *Galois group* for $`K/F` is the {bpref "lf.automorphism_group"}[automorphism group] $`\Aut(K^{gal}/F)`.

This automorphism group acts on the $`n` embeddings $`K\hookrightarrow K^{gal}` via composition.  As a result, we get an injection $`\Aut(K^{gal}/F)\hookrightarrow S_n`, which is well-defined up to the labelling of the $`n` embeddings, which corresponds to being well-defined up to conjugation in $`S_n`.

We use the notation $`\Gal(K/F)` for $`\Aut(K/F)` when $`K=K^{gal}`.

There is a naming convention for Galois groups up to degree $`47`.

Depends on: {uses "lf.automorphism_group"}[] {uses "nf.degree"}[] {uses "nf.galois_closure"}[] {uses "nf.separable"}[] {uses "ring.field"}[]
:::

:::definition "nf.galois_root_discriminant"
*Galois root discriminant.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.galois_root_discriminant))

The *Galois root discriminant* of a {bpref "nf"}[number field] is the {bpref "nf.root_discriminant"}[root discriminant] of its {bpref "nf.galois_closure"}[Galois closure].

Depends on: {uses "nf"}[] {uses "nf.galois_closure"}[] {uses "nf.root_discriminant"}[]
:::

:::definition "nf.generator"
*Generator of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.generator))

A *generator* of a {bpref "nf"}[number field] $`K` is an element $`a\in K` such that $`K=\Q(a)`.
The {bpref "nf.minimal_polynomial"}[minimal polynomial] of a generator is a {bpref "nf.defining_polynomial"}[defining polynomial] for $`K`.

Depends on: {uses "nf"}[] {uses "nf.defining_polynomial"}[] {uses "nf.minimal_polynomial"}[]
:::

:::definition "nf.ideal_class_group"
*Ideal class group of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.ideal_class_group))

The *ideal class group* of a {bpref "nf"}[number field] $`K` with {bpref "nf.ring_of_integers"}[ring of integers] $`O_K` is the group of equivalence classes of ideals, given by the quotient of the multiplicative group of all {bpref "ring.fractional_ideal"}[fractional ideals] of $`O_K` by the subgroup of {bpref "ring.principal_fractional_ideal"}[principal fractional ideals].

Since $`K` is a {bpref "nf"}[number field], the ideal class group of $`K` is a finite abelian group, and so has the structure of a product of cyclic groups encoded by a finite list $`[a_1,\dots,a_n]`, where the $`a_i` are positive integers with $`a_i\mid a_{i+1}` for $`1\leq i < n`.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[] {uses "ring.fractional_ideal"}[] {uses "ring.principal_fractional_ideal"}[]
:::

:::definition "nf.ideal_labels"
*Ideal labels.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.ideal_labels))

In the LMFDB ideals in rings of integers of number fields are identified using the labeling system developed by John Cremona, Aurel Page and Andrew Sutherland .

In a number field $`K`, each nonzero ideal $`I` of its ring of integers $`\mathcal{O}_K` is assigned an *ideal label* of the form $`\texttt{N.i}`, where $`N` and $`i` are positive integers, in which $`N:=[\mathcal{O}_K:I]` is the norm of the ideal and $`i` is the index of the ideal in a sorted list of all ideals of norm $`N`.  Once an integral primitive element $`\alpha` for the field $`K` is fixed, the ordering of ideals of the same norm is defined in a deterministic fashion (involving no arbitrary choices).

In the LMFDB we always represent number fields as $`K = \mathbb{Q}[X]/(g(X))` where $`g` is the unique monic integral polynomial which satisfies the {bpref "nf.polredabs"}[polredabs] condition. In this representation the image of $`X` under the quotient map $`\mathbb{Q}[X]\rightarrow\mathbb{Q}[X]/(g(X))` is a canonical integral primitive element $`\alpha` for $`K`.  Fixing this element determines a unique ordering of all $`\mathcal{O}_K`-ideals of the same norm.

Depends on: {uses "nf.polredabs"}[]
:::

:::definition "nf.inessential_prime"
*Inessential prime.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.inessential_prime))

An *inessential prime* of a {bpref "nf"}[number field] is a prime divisor of its {bpref "nf.zk_index"}[index].

Depends on: {uses "nf"}[] {uses "nf.zk_index"}[]
:::

:::definition "nf.integral"
*Integral elements.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.integral))

An element of a {bpref "nf"}[number field] $`K` is *integral* if it is {bpref "ring.integral"}[integral] over $`\Z`.

Depends on: {uses "nf"}[] {uses "ring.integral"}[]
:::

:::definition "nf.integral_basis"
*Integral basis of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.integral_basis))

An *integral basis* of a {bpref "nf"}[number field] $`K` is a $`\mathbb{Z}`-basis for the {bpref "nf.ring_of_integers"}[ring of integers] of $`K`.  This is also a $`\mathbb{Q}`-basis for $`K`.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "nf.intermediate_fields"
*Intermediate fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.intermediate_fields))

For a number field $`K`, *intermediate fields* $`F` are fields with $`\Q\subsetneqq F \subsetneqq K`.
:::

:::definition "nf.is_galois"
*Is a Galois extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.is_galois))

Let $`F` be a subfield of $`K`,

$$`\Aut(K/F)=\{ \sigma:K\to K\mid \sigma(a)=a \text{ for all } a\in F \text{ and } \sigma \text{ is a ring homomorphism}\},`

and

$$`K^{\Aut(K/F)} = \{ a\in K \mid \sigma(a)=a\}.`

Then $`K` is *Galois* over $`F` if $`K^{\Aut(K/F)} = F`.
:::

:::definition "nf.local_algebra"
*Local algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.local_algebra))

Given a global {bpref "nf"}[number field] $`K` and a prime $`p`, the *local algebra* for $`K` is $`K\otimes \Q_p`.  This is a finite {bpref "nf.separable_algebra"}[separable algebra] over $`\Q_p` which is isomorphic to a finite direct product of finite extension fields of $`\Q_p`.

Depends on: {uses "nf"}[] {uses "nf.separable_algebra"}[]
:::

:::definition "nf.maximal_cm_subfield"
*Maximal CM subfield.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.maximal_cm_subfield))

The *maximal CM subfield* of a {bpref "nf"}[number field] is the largest subfield by {bpref "nf.degree"}[degree] which is a {bpref "nf.cm_field"}[CM field].

Depends on: {uses "nf"}[] {uses "nf.cm_field"}[] {uses "nf.degree"}[]
:::

:::definition "nf.minimal_polynomial"
*Minimal polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.minimal_polynomial))

The *minimal polynomial* of an element $`a` in a {bpref "nf"}[number field] $`K` is the unique monic polynomial $`f(X)\in\Q[X]` of minimal degree such that $`f(a)=0`. It is necessarily irreducible over $`\Q.`

Depends on: {uses "nf"}[]
:::

:::definition "nf.minimal_sibling"
*Minimal sibling.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.minimal_sibling))

The *minimal sibling* of a {bpref "nf"}[number field] is a {bpref "nf.sibling"}[sibling] that is minimal with respect to the following quantities considered in order:

- its {bpref "nf.degree"}[degree]

- the T-number of its {bpref "nf.galois_group"}[Galois group]

- the absolute value of its {bpref "nf.discriminant"}[discriminant]

- the vector $`(a_0, a_1, \ldots, a_{n-1})` of coefficients of its normalized defining polynomial

$`x^n+a_{n-1} x^{n-1}+\cdots +a_0`

Depends on: {uses "nf"}[] {uses "nf.degree"}[] {uses "nf.discriminant"}[] {uses "nf.galois_group"}[] {uses "nf.sibling"}[]
:::

:::definition "nf.monogenic"
*Monogenic field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.monogenic))

A {bpref "nf"}[number field] $`K` is *monogenic* if its {bpref "nf.ring_of_integers"}[ring of integers] $`\mathcal{O}_K` equals $`\Z[\alpha]` for some $`\alpha \in \mathcal{O}_K`.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "nf.monomial_order"
*Monomial order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.monomial_order))

A *monomial order* in a {bpref "nf"}[number field] $`K` is an {bpref "nf.order"}[order] of the form $`\Z[\alpha]`, where $`\alpha` is an element of $`K`. The element $`\alpha` is necessarily both an {bpref "nf.ring_of_integers"}[algebraic integer] and a primitive element for $`K`.

Depends on: {uses "nf"}[] {uses "nf.order"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "nf.narrow_class_group"
*Narrow class group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.narrow_class_group))

The *narrow class group* (also called the *strict class group*) of a {bpref "nf"}[number field] $`K` is the group of equivalence classes of ideals, given by the quotient of the multiplicative group of all fractional ideals of $`K` by the subgroup of principal fractional ideals which have a {bpref "nf.totally_positive"}[totally positive] generator.  It is a
finite abelian group whose order is the {bpref "nf.narrow_class_number"}[narrow class number].

Depends on: {uses "nf"}[] {uses "nf.totally_positive"}[]
:::

:::definition "nf.narrow_class_number"
*Narrow class number.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.narrow_class_number))

The *narrow class number* (also called the *strict class number*) of an {bpref "nf"}[algebraic number field] is the order of its {bpref "nf.narrow_class_group"}[narrow class group].
Since the ordinary {bpref "nf.ideal_class_group"}[ideal class group] is a quotient of the {bpref "nf.narrow_class_group"}[narrow class group], the narrow class number is a multiple of the {bpref "nf.class_number"}[class number].  Moreover, the ratio is a power of $`2`. The two class numbers are the same in many cases, for example when the number field is {bpref "nf.totally_imaginary"}[totally complex].

Depends on: {uses "nf"}[] {uses "nf.class_number"}[] {uses "nf.ideal_class_group"}[] {uses "nf.narrow_class_group"}[] {uses "nf.totally_imaginary"}[]
:::

:::definition "nf.nickname"
*Number field nicknames.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.nickname))

The LMFDB supports *nicknames*, short human-readable names for
various fields.  Examples include:

- Q, for the rationals $`\mathbb{Q}`

- Qi, for $`\mathbb{Q}(i)`

- QsqrtN, for $`\mathbb{Q}(\sqrt{N})`, as in Qsqrt-5 for $`\mathbb{Q}(\sqrt{-5})`

- QzetaN, for $`\mathbb{Q}(\zeta_N)`, where $`\zeta_N` is a primitive $`N`th root of unity.
:::

:::definition "nf.order"
*Order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.order))

An *order* in a {bpref "nf"}[number field] $`K` is a subring of $`K` which is also a lattice in $`K`. Every order in $`K` is contained in the ring of integers of $`K`, which is itself an order in $`K`; for this reason, the ring of integers is sometimes called the _maximal order_.

Example: $`\Z[\sqrt{5}]` is an order in $`K=\Q(\sqrt{5})`. However, it is not maximal, since the maximal order (i.e. ring of integers) of $`K` is $`\Z\left[\frac{1+\sqrt{5}}2\right]`.

Depends on: {uses "nf"}[]
:::

:::definition "nf.padic_completion"
*$`p`-adic completion of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.padic_completion))

Let $`K` be a {bpref "nf"}[number field], $`\mathcal{O}_K` its {bpref "lf.ring_of_integers"}[ring of integers], $`\mathfrak{P}` a non-zero {bpref "nf.prime"}[prime ideal] of $`\mathcal{O}_K`, and $`p\in \Z\cap \mathfrak{P}`.
There are a couple of ways to construct $`K_{\mathfrak{P}}`, the *$`p`-adic completion of $`K` at $`\mathfrak{P}`*.

First, we can take the inverse limit

$$`\lim_{\leftarrow} \mathcal{O}_K/\mathfrak{P}^n`

which is an {bpref "ring.integral_domain"}[integral domain].  Its {bpref "ring.field_of_fractions"}[field of fractions] is $`K_{\mathfrak{P}}`.

Second, since $`\mathcal{O}_K` is a {bpref "ring.dedekind_domain"}[Dedekind domain], if $`\alpha\in K^*` the {bpref "ring.fractional_ideal"}[fractional ideal]

$$`\langle \alpha\rangle = \prod_{\mathfrak{Q}} \mathfrak{Q}^{e_{\mathfrak{Q}}}`

where the product is over all non-zero prime ideals $`\mathfrak{Q}`, all $`e_{\mathfrak{Q}}\in\Z`, and all but finitely many $`e_{\mathfrak{Q}}=0`.  Then we define
$`v_{\mathfrak{P}}(\alpha)=e_{\mathfrak{P}}`, and then the metric $`d` on $`K` by
$`d(\alpha, \beta) = p^{-v_{\mathfrak{P}}(\alpha-\beta)}` if $`\alpha\neq \beta` and $`d(\alpha,\alpha)=0`.  Then the completion of $`K` with respect to this metric is $`K_{\mathfrak{P}}`.

If $`K=\Q(a)`, and $`f\in\Q[x]` is the monic {bpref "ring.irreducible"}[irreducible] polynomial for $`a` over $`\Q`, then adjoining the roots of $`f` to $`\Q_p` provide another means of constructing the completions.

Finally, the {bpref "nf.local_algebra"}[local algebra] of $`K`, $`\prod_{j=1}^g K_j` is a product of the $`p`-adic completions of $`K`.  The $`p`-adic completions of $`K` correspond to the nonarchimedian {bpref "nf.place"}[places] of $`K`.

Depends on: {uses "lf.ring_of_integers"}[] {uses "nf"}[] {uses "nf.local_algebra"}[] {uses "nf.prime"}[] {uses "ring.dedekind_domain"}[] {uses "ring.field_of_fractions"}[] {uses "ring.fractional_ideal"}[] {uses "ring.integral_domain"}[] {uses "ring.irreducible"}[]
:::

:::definition "nf.place"
*Place of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.place))

A *place* $`v` of a field $`K` is an equivalence class of non-trivial {bpref "nf.absolute_value"}[absolute values] on $`K`.  As with absolute values, places may be classified as archimedean or nonarchimedean, since these properties are preserved under equivalence.

Each place induces a distance metric that gives $`K` a metric topology.  The {bpref "nf.padic_completion"}[*completion*] $`K_v` of $`K` at $`v` is the completion of this metric space, which is also a topological field.

When $`K` is a {bpref "nf"}[number field] each nonarchimedean place arises from the valuation associated to each {bpref "ring.prime_ideal"}[prime ideal] in the {bpref "nf.ring_of_integers"}[ring of integers] of $`K`, while archimedean places arise from embeddings of $`K` into the complex numbers: each {bpref "nf.real_embedding"}[real embedding] determines a *real place*, and each conjugate pair of {bpref "nf.complex_embedding"}[complex embeddings] determines a *complex place*. The archimedean places of a number field are also called *infinite places*.

Depends on: {uses "nf"}[] {uses "nf.absolute_value"}[] {uses "nf.complex_embedding"}[] {uses "nf.real_embedding"}[] {uses "nf.ring_of_integers"}[] {uses "ring.prime_ideal"}[]
:::

:::definition "nf.polredabs"
*Canonical defining polynomial for number fields.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.polredabs))

Every {bpref "nf"}[number field] $`K` can be represented as $`K = \Q[X]/P(x)` for some monic $`P\in\Z[X]`, called a *defining polynomial* for $`K`.  Among all such defining polynomials, we define the *reduced defining polynomial* as follows.

Recall that for a monic polynomial $`P(x) = \prod_i(x-\alpha_i)`, the $`T_2` norm of $`P` is $`T_2(P) = \sum_i |\alpha_i|^2`.

- Let $`L_0` be the list of (monic integral) defining polynomials for $`K` that are minimal with respect to the $`T_2` norm.

- Let $`L_1` be the sublist of $`L_0` of polynomials whose {bpref "nf.poly_discriminant"}[discriminant] has minimal absolute value.

- For a polynomial $`P = x^n + a_1x^{n-1} + \dots + a_n`, let $`S(P) = (|a_1|,a_1,\dots,|a_n|,a_n)`, and order the polynomials in $`L_1` by the lexicographic order of the vectors $`S(P)`.

Then the reduced defining polynomial of $`K` is the first polynomial in $`L_1` with respect to this order.

The pari/gp function <code>polredabs()</code> computes reduced defining polynomials, which are also commonly called <code>polredabs</code> polynomials.

Depends on: {uses "nf"}[] {uses "nf.poly_discriminant"}[]
:::

:::definition "nf.poly_discriminant"
*Discriminant of polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.poly_discriminant))

The *discriminant* of a monic polynomial $`f(x) = \prod_{i=1}^d (x - \alpha_i)` is the quantity

$$`\Delta = \prod_{i < j} (\alpha_i - \alpha_j)^2.`

If $`f` has integral coefficients, $`K` is the {bpref "nf"}[number field] defined by $`f` and $`\alpha` is a root of $`f` in $`K`, then the {bpref "nf.discriminant"}[discriminant] $`D` of $`K` divides $`\Delta` and the ratio $`\Delta/D` is the square of the index of $`\Z[\alpha]` in the {bpref "nf.ring_of_integers"}[ring of integers] of $`K`.

Depends on: {uses "nf"}[] {uses "nf.discriminant"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "nf.prime"
*Prime of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.prime))

A *prime* $`\mathfrak p` of a {bpref "nf"}[number field] $`K` is a nonzero {bpref "ring.prime_ideal"}[prime ideal] of its {bpref "nf.ring_of_integers"}[ring of integers] $`\mathcal O_K`.

The ideal $`\mathfrak p \cap\mathcal O_K` is a nonzero prime ideal of $`\Z` (a prime of $`\Q`), which is necessarily a principal ideal $`(p)` for some prime number $`p`.  The prime $`\mathfrak p` is then said to be a *prime above* $`p`.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[] {uses "ring.prime_ideal"}[]
:::

:::definition "nf.ramified_primes"
*Ramified (rational) prime of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.ramified_primes))

A prime integer $`p` is a *ramified prime* of a number field $`K` if, when the ideal generated by $`p` is factored into prime ideals in the ring of integers
$`\mathcal{O}_K` of $`K`,

$$`p\mathcal{O}_K= \mathcal{P_1}^{e_1}\cdots \mathcal{P_k}^{e_k},`

there is an $`i` such that $`e_i\geq 2`.

The ramified primes of $`K` are the primes dividing the {bpref "nf.discriminant"}[discriminant] of $`K`.
:::

:::definition "nf.rank"
*Rank of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.rank))

The *rank* of a {bpref "nf"}[number field] $`K` is the size of any set of  {bpref "nf.fundamental_units"}[fundamental units] of $`K`. It is equal to $`r = r_1 + r_2 -1` where $`r_1` is the number of real embeddings of $`K` into $`\C` and $`2r_2` is the number of complex embeddings of $`K` into $`\C.`

Depends on: {uses "nf"}[] {uses "nf.fundamental_units"}[]
:::

:::definition "nf.real_embedding"
*Real embedding.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.real_embedding))

A *real embedding* of a number field $`K` is a field homomorphism $`K\to \R`.  A single number field may have several distinct real embeddings.
:::

:::definition "nf.reflex_field"
*Reflex field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.reflex_field))

Let $`K` be a {bpref "nf.cm_field"}[CM number field] and let $`\overline{\mathbb{Q}}` be the algebraic closure of $`\Q` in $`\C`. A subset $`\Phi \subset \mathrm{Hom}(K, \overline{\mathbb{Q}})` is called a *CM type* if for every {bpref "nf.embedding"}[embedding] $`\iota \in \mathrm{Hom}(K, \overline{\mathbb{Q}})` either $`\iota \in \Phi` or $`\overline{\iota} \in \Phi`, but not both, where $`\overline{\iota}` is the complex conjugate of $`\iota`.

Given a {bpref "nf.cm_field"}[CM field] $`K` and a CM type $`\Phi`, the *reflex field* is the fixed field inside $`\overline{\Q}` corresponding to the {bpref "group.subgroup"}[subgroup] $`\{ \rho \in \Gal(\overline{\Q}/\Q) : \rho \Phi = \Phi \}` of $`\Gal(\overline{\Q}/\Q)`. A CM type $`\Phi` and its complement $`\overline{\Phi}`, which is the same as the set of complex conjugate embeddings, have the same reflex field. The number of complex conjugate pairs of CM types is $`2^{g-1}`, where $`2g=[K:\Q]`, the {bpref "nf.degree"}[degree] of $`K` over $`\Q`.

To specify a CM type $`\Phi` for the CM field $`K=\Q(a)`:
<ol>
<li>fix an order
$`(\iota_1,\overline{\iota_1}), \dots,  (\iota_g,\overline{\iota_g})`
of the pairs of {bpref "nf.complex_embedding"}[complex embeddings] of $`K`;
<li> then $`\Phi=(\varphi_1,\dots,\varphi_g)` where $`\varphi_j\in\{\iota_j,\overline{\iota_j}\}` for $`1\le j\le g`;
<li> now $`\Phi` can be encoded by the list $`(\text{sign}(\text{im}(\varphi_1(a))),\dots,\text{sign}(\text{im}(\varphi_g(a))))`.
</ol>

The CM types in the LMFDB are grouped in Galois orbits under the action of $`\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})` described above.

<!--- (commented out by John Cremona: this information should be in the completeness knowl for number fields)
In the LMFDB, there is a potentially incomplete list of reflex fields for each CM field $`K` of {bpref "nf.degree"}[degree] at most 12.  For each reflex field, it is indicated for how many of the $`2^{[K:\mathbb{Q}]/2 - 1}` pairs of complementary CM types this particular field is the reflex field. The only reflex fields listed are those of degree at most 36.

- -->

Depends on: {uses "group.subgroup"}[] {uses "nf.cm_field"}[] {uses "nf.complex_embedding"}[] {uses "nf.degree"}[] {uses "nf.embedding"}[]
:::

:::definition "nf.reflex_reflex_field"
*Reflex field of the reflex field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.reflex_reflex_field))

Let $`K` be a {bpref "nf.cm_field"}[CM number field] and let $`N` a normal closure of $`K`, let $`\Phi \subset \mathrm{Hom}(K, \overline{\mathbb{Q}})` be a {bpref "nf.reflex_field"}[CM type] and $`L` its associated {bpref "nf.reflex_field"}[reflex field]. Then $`\Phi` induces a CM type $`\Phi_N \subset \mathrm{Hom}(N, \mathbb{C})` by taking the maps that restrict to a map inside $`\Phi` on $`K`. The maps in $`\Phi_N` are isomorphisms on the image $`F` of $`N` inside $`\overline{\mathbb{Q}}` and by inverting them, we obtain a CM type on $`F` with values in $`N`. The *reflex field of the reflex field* is the reflex field of this CM type.

It can also be computed as follows. Consider the right action of $`\mathrm{Gal}(N/K)` on the set of CM types on $`K`. Then the reflex field of the reflex field is the subfield corresponding to the subgroup stabilising $`\Phi`.

The reflex field of the reflex field is also the smallest field of definition of the CM type $`\Phi`, i.e. it is the largest subfield $`M` of $`K` such that $`\Phi` is induced from a CM type on $`M`.

Depends on: {uses "nf.cm_field"}[] {uses "nf.reflex_field"}[]
:::

:::definition "nf.regulator"
*Regulator of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.regulator))

Let $`\sigma_1,\ldots,\sigma_{r_1}` be the real embeddings of a {bpref "nf"}[number field] $`K` into the complex numbers $`\mathbb{C}`, and $`\sigma_{r_1+ 1},\ldots,\sigma_{r_1+r_2}` be complex embeddings of $`K` into $`\C` such that no two are complex conjugate. Let $`u_1,\ldots,u_r` be a set of {bpref "nf.fundamental_units"}[fundamental units] of $`K`. Then $`r = r_1 + r_2 -1`.

Let $`M` be the $`(r_1+ r_2-1)\times (r_1+r_2)` matrix
$`(d_j\log{ \sigma_j(u_i)})`, where $`d_j=1` if $`j\leq r_1`, i.e, if $`\sigma_j` is a real embedding, and $`d_j=2` otherwise, i.e., if $`\sigma_j` is a complex embedding.  The sum of the columns of $`M` is the zero vector.

The *regulator* of $`K` is the absolute value of the determinant of the sub-matrix of $`M` where one column is removed.  Its value is independent of the choice of column which is removed.

Depends on: {uses "nf"}[] {uses "nf.fundamental_units"}[]
:::

:::definition "nf.relative_class_number"
*Relative class number of a CM field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.relative_class_number))

If $`K` is a {bpref "nf"}[number field] with {bpref "nf.cm_field"}[CM] with {bpref "nf.class_number"}[class number] $`h`, and $`K^+` is its maximal {bpref "nf.totally_real"}[totally real] subfield with class number $`h^+`, then $`h^+` divides $`h` and the *relative class number* is
$`h/h^+`.

Depends on: {uses "nf"}[] {uses "nf.class_number"}[] {uses "nf.cm_field"}[] {uses "nf.totally_real"}[]
:::

:::definition "nf.ring_of_integers"
*Ring of integers of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.ring_of_integers))

The *ring of integers* of a {bpref "nf"}[number field] $`K` is the {bpref "ring.integral"}[integral closure] of $`\Z` in $`K`.

Depends on: {uses "nf"}[] {uses "ring.integral"}[]
:::

:::definition "nf.root_discriminant"
*Root discriminant of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.root_discriminant))

If $`K` is a {bpref "nf"}[number field] of {bpref "nf.degree"}[degree] $`n` and {bpref "nf.discriminant"}[discriminant] $`D`, then the *root discriminant* of $`K` is

$$`\textrm{rd}(K) = |D|^{1/n}.`

It gives a measure of the discriminant of a number field which is normalized for the degree.  For example, if $`K\subseteq L` are number fields and $`L/K` is unramified, then $`\textrm{rd}(K)=\textrm{rd}(L)`.

Depends on: {uses "nf"}[] {uses "nf.degree"}[] {uses "nf.discriminant"}[]
:::

:::definition "nf.separable"
*Separable extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.separable))

If $`K/F` is a finite {bpref "nf.degree"}[degree] field extension, $`\alpha\in K` is *separable* over $`F` if its monic irreducible polynomial has distinct roots in the algebraic closure $`\overline{F}`.

The extension $`K/F` is *separable* if every $`\alpha\in K` is separable over $`F`.

All algebraic extensions of local and global number fields are separable.

Depends on: {uses "nf.degree"}[]
:::

:::definition "nf.separable_algebra"
*Separable algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.separable_algebra))

A (finite) *separable algebra* $`A` over a field $`F`, also called an *\'etale $`F`-algebra*, is an  $`F`-algebra of finite dimension that is isomorphic to a product of {bpref "nf.separable"}[separable] field extensions of $`F`.

If $`L/K` is a field extension and $`A` is a separable $`K`-algebra then $`A\otimes_K L` is a separable $`L`-algebra (which is typically not a field, even when $`A` is).

Depends on: {uses "nf.separable"}[]
:::

:::definition "nf.serre_odlyzko_bound"
*Serre Odlyzko bound.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.serre_odlyzko_bound))

For each positive integer $`n`, let $`C_n` for the minimum {bpref "nf.root_discriminant"}[root discriminant] for all {bpref "nf"}[number fields] of {bpref "nf.degree"}[degree] $`n`.  Assuming the {bpref "lfunction.rh"}[Generalized Riemann Hypothesis], $`\limsup C_n \geq \Omega` where

$$`\Omega = 8\pi e^\gamma\approx 44.7632\ldots`

and $`\gamma` is the Euler–Mascheroni constant.  Lower bounds for the $`C_n` were deduced by analytic methods through the work of Odlyzko and others.  In particular, Serre introduced the constant $`\Omega` which  we refer to as the *Serre Odlyzko bound*,

Consequently, any number field whose root discriminant lies below $`\Omega` can be considered to have small discriminant.

Depends on: {uses "lfunction.rh"}[] {uses "nf"}[] {uses "nf.degree"}[] {uses "nf.root_discriminant"}[]
:::

:::definition "nf.sibling"
*Sibling fields and algebras.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.sibling))

Two finite {bpref "nf.separable"}[separable extension fields] $`K_1` and $`K_2` of a ground field $`F` are called *siblings* if they are not isomorphic, but have isomorphic {bpref "nf.galois_closure"}[Galois closures].

A finite dimensional separable $`\Q`-algebra is isomorphic to a product of number fields.  By its Galois closure, we mean the compositum of the Galois closures of the constituent fields.  Then two algebras are *siblings* if they have isomorphic Galois closures, but are not isomorphic as $`\Q`-algebras.

Depends on: {uses "nf.galois_closure"}[] {uses "nf.separable"}[]
:::

:::definition "nf.signature"
*Signature of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.signature))

The *signature* of a {bpref "nf"}[number field] $`K` is the pair $`[r_1,r_2]` where $`r_1` is the number of {bpref "nf.real_embedding"}[real embeddings] of $`K` and $`r_2` is the number of conjugate pairs of {bpref "nf.complex_embedding"}[complex embeddings].

The {bpref "nf.degree"}[degree] of $`K` is $`r_1+2r_2`.

Depends on: {uses "nf"}[] {uses "nf.complex_embedding"}[] {uses "nf.degree"}[] {uses "nf.real_embedding"}[]
:::

:::definition "nf.stem_field"
*Stem field for a Galois extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.stem_field))

If $`K/F` is a {bpref "nf.is_galois"}[Galois] extension of fields, a *stem field* for $`K/F` is a field $`E` such that $`F\subseteq E\subseteq K` and $`K` is the {bpref "nf.galois_closure"}[Galois closure] of $`E/F`.

This is connected to the notion of the stem field of a polynomial.
If $`f\in F[x]` is a separable irreducible polynomial of degree $`n` with roots $`\alpha_1, \ldots, \alpha_n` (in some extension field), then the fields $`F(\alpha_i)` are the *stem fields of the polynomial* $`f`.  The splitting field of $`f` is $`K=F(\alpha_1,\ldots,\alpha_n)`, which is a Galois extension of $`F`, and the fields $`F(\alpha_i)` are stem fields for $`K/F` as defined above.

Depends on: {uses "nf.galois_closure"}[] {uses "nf.is_galois"}[]
:::

:::definition "nf.torsion"
*Unit group torsion.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.torsion))

A *torsion generator* of a {bpref "nf"}[number field] is a primitive root of unity that generates the torsion subgroup of the {bpref "nf.unit_group"}[unit group] (which is necessarily cyclic).

Depends on: {uses "nf"}[] {uses "nf.unit_group"}[]
:::

:::definition "nf.totally_imaginary"
*Totally imaginary.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.totally_imaginary))

A {bpref "nf"}[number field] $`K` is *totally imaginary* (or *totally complex*) if it cannot be embedded in the real numbers $`\R`; equivalently, $`\R` does not contain the image of any of the homomorphisms from $`K` to $`\C`.

Depends on: {uses "nf"}[]
:::

:::definition "nf.totally_positive"
*Totally positive.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.totally_positive))

An element $`\alpha` in a {bpref "nf"}[number field] $`K` is *totally positive* if $`\sigma(\alpha)>0` for all real embeddings $`\sigma` of $`K` into $`\R`.

Depends on: {uses "nf"}[]
:::

:::definition "nf.totally_real"
*Totally real.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.totally_real))

A {bpref "nf"}[global number field] $`K` is always of the form $`K=\Q(\alpha)` where $`\alpha` has monic irreducible polynomial $`f(x)\in\Q[x]`.  The field is *totally real* if all of the roots of $`f(x)` in $`\C` lie in the real numbers $`\R`.

Equivalently, $`K` is totally real if all the embeddings of $`K` into $`\C` have image contained in $`\R`.

Depends on: {uses "nf"}[]
:::

:::definition "nf.unit_group"
*Unit group of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.unit_group))

The *unit group* of a {bpref "nf"}[number field] $`K` is the group of units of the {bpref "nf.ring_of_integers"}[ring of integers] of $`K`.  It is a finitely generated abelian group with cyclic torsion subgroup.  A set of generators of a maximal torsion-free subgroup is called a set of {bpref "nf.fundamental_units"}[fundamental units] for $`K`.

The unit group of $`K` has as invariants the {bpref "nf.rank"}[rank]
 and the {bpref "nf.regulator"}[regulator] of $`K`.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "nf.unramified_prime"
*Unramified (rational) prime of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.unramified_prime))

A *unramified (rational) prime* of a {bpref "nf"}[number field ] $`K` is a prime integer $`p` such that the ideal generated by $`p` is factored into distinct prime ideals in the ring of integers $`\mathcal{O}_K` of $`K`
$$`p\mathcal{O}_K = \mathcal{P}_1\cdots \mathcal{P}_k.`

The unramified primes of $`K` are the primes which do not divide the {bpref "nf.discriminant"}[discriminant] of $`K`.

Depends on: {uses "nf"}[] {uses "nf.discriminant"}[]
:::

:::definition "nf.weil_height"
*Weil height.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.weil_height))

The (*logarithmic*) *Weil height* of a nonzero rational number $`a/b\in\mathbb{Q}` in lowest terms is the quantity

$$`h(a/b) = \log\max\bigl\{|a|,|b|\bigr\}.`
 The height of $`0` is taken to be $`0.`

The (*absolute logarithmic*) *Weil height* of an element $`\alpha` in a {bpref "nf"}[number field] $`K` is the quantity

$$`h(\alpha) = \frac{1}{[K:\mathbb{Q}]} \sum_{v\in M_K} [K_v:\mathbb{Q}_v]\log\max\bigl\{\|\alpha\|_v,1\bigr\},`

where $`M_K` is an appropriately normalized set of inequivalent absolute values on $`K`. More generally, the height of a point $`P=[\alpha_0,\alpha_1,\ldots,\alpha_n]` in projective space $`\mathbb{P}^n(K)` is given by

$$`h(P) = \frac{1}{[K:\mathbb{Q}]} \sum_{v\in M_K} [K_v:\mathbb{Q}_v]\log\max_{0\le i\le n}\bigl\{\|\alpha_i\|_v\bigr\}.`

If $`\mathcal{L}` is a very amply line bundle on a {bpref "ag.variety"}[projective variety] $`V` inducing an embedding $`\iota \colon V \hookrightarrow \mathbb{P}^n`, then the Weil height associated on $`X` associated to $`\mathcal{L}` is given by

$$`h_{\mathcal{L}}(P) = h(\iota(P)).`

This definition can be extended to all line bundles by using the following linearity:

$$`h_{\mathcal{L}_1 \otimes \mathcal{L}_2}(P) = h_{\mathcal{L}_1}(P) + h_{\mathcal{L}_2}(P).`

Depends on: {uses "ag.variety"}[] {uses "nf"}[]
:::

:::definition "nf.weil_polynomial"
*Weil polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.weil_polynomial))

For a prime power $`q`, a *Weil $`q`-polynomial* is a monic polynomial with integer coefficients whose complex roots are of absolute value $`\sqrt{q}`.

Given $`q` and a nonnegative integer $`d`, there are only finitely many Weil $`q`-polynomials of degree $`d`.

The characteristic polynomial of an {bpref "ag.abelian_variety"}[abelian variety] over $`\F_q` is a Weil $`q`-polynomial, but it is not quite true that every Weil $`q`-polynomial arises in this way.  Every irreducible Weil $`q`-polynomial has a unique power that is the characteristic polynomial of a {bpref "av.simple"}[simple abelian variety] over $`\F_q`; it is the products of these powers that arise from abelian varieties.

Depends on: {uses "ag.abelian_variety"}[] {uses "av.simple"}[]
:::

:::definition "nf.zk_index"
*Index of a number field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/nf.zk_index))

If $`K` is a {bpref "nf"}[number field] with {bpref "nf.ring_of_integers"}[ring of integers] $`\mathcal{O}_K`, then for all $`\alpha\in\mathcal{O}_K` such that $`K=\Q(\alpha)`, the index of $`\alpha`, $`i(\alpha)` is the index of the {bpref "nf.order"}[order] $`\Z[\alpha]`.

The *index of the number field* is the greatest common divisor of all $`i(\alpha)` with $`\alpha` as above.

Depends on: {uses "nf"}[] {uses "nf.order"}[] {uses "nf.ring_of_integers"}[]
:::
