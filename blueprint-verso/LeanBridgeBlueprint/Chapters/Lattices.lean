import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Lattices" =>

This chapter lists the LMFDB definitions relating to *lattices*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "lattice.additively_indecomposable"
*Additively indecomposable lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.additively_indecomposable))

A {bpref "lattice.positive_definite"}[positive definite] {bpref "lattice.definition"}[integral lattice] $`L` is *additively indecomposable* if it cannot be written as a sum of two nonzero {bpref "lattice.nondegenerate"}[positive semi-definite] integral lattices.

Every additively indecomposable lattice is (orthogonally) {bpref "lattice.orthogonal_decomposition"}[indecomposable], though the converse is not true in general.  However, every {bpref "lattice.unimodular"}[unimodular] (orthogonally) indecomposable lattice is additively indecomposable.

The only additively indecomposable integral lattices of {bpref "lattice.dimension"}[rank] up to $`8` are $`\Z`, $`E_6`, $`E_7`, and $`E_8`, proven by Mordell and Ko.

Depends on: {uses "lattice.definition"}[] {uses "lattice.dimension"}[] {uses "lattice.nondegenerate"}[] {uses "lattice.orthogonal_decomposition"}[] {uses "lattice.positive_definite"}[] {uses "lattice.unimodular"}[]
:::

:::definition "lattice.algebraic"
*Algebraic lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.algebraic))

A lattice is called *algebraic* if it can be realized as a free $`\mathbb{Z}`-module in an algebraic number field.
:::

:::definition "lattice.arithmetic"
*Arithmetic lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.arithmetic))

A lattice is called *arithmetic* if it is {bpref "lattice.similarity"}[similar] to an {bpref "lattice.definition"}[integral lattice].

Depends on: {uses "lattice.definition"}[] {uses "lattice.similarity"}[]
:::

:::definition "lattice.automorphism_group" (lean := "TauCeti.BilinForm.isometryGroup, TauCeti.IntegralLattice.Isometry, TauCeti.IntegralLattice.specialOrthogonalGroup")
*Automorphism group of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.automorphism_group))

The *automorphism group* of an {bpref "lattice.definition"}[integral lattice] $`L` is the group of {bpref "lattice.isometry"}[isometries] from $`L` to itself. For a {bpref "lattice.positive_definite"}[positive definite] lattice, this is a finite group.

Depends on: {uses "lattice.definition"}[] {uses "lattice.isometry"}[] {uses "lattice.positive_definite"}[]
:::

:::definition "lattice.class_number"
*Class number of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.class_number))

For an {bpref "lattice.definition"}[integral lattice], $`L`, the number of {bpref "lattice.isometry"}[isometry] classes in the {bpref "lattice.genus"}[genus] of $`L` is the *class number* of $`L`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.genus"}[] {uses "lattice.isometry"}[]
:::

:::definition "lattice.conway_genus_symbol"
*Conway symbol.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.conway_genus_symbol))

The *Conway genus symbol* of an {bpref "lattice.definition"}[integral lattice] $`L` is an invariant of the {bpref "lattice.genus"}[genus] of $`L`.  It is given in the form $`\text{I}_{r,s}(\cdots)` or $`\text{II}_{r,s}(\cdots)` where the Roman numeral $`\text{I}` or $`\text{II}` indicates the type of $`L`, and $`(r,s)` is the {bpref "lattice.signature"}[signature] of $`L`.

For a complete description of the Conway symbol, see Conway-Sloane, Chapter 15.

Depends on: {uses "lattice.definition"}[] {uses "lattice.genus"}[] {uses "lattice.signature"}[]
:::

:::definition "lattice.covering_radius"
*Covering radius.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.covering_radius))

*Covering radius* (also known as *inhomogeneous minimum*) of a convex $`\boldsymbol 0`-symmetric set $`K` in $`\mathbb{R}^n` with respect to a full-rank lattice $`L \subset \mathbb{R}^n` is $`\mu = \min \{ t > 0 : \bigcup_{\boldsymbol x \in L} (\boldsymbol x + tK) = \mathbb{R}^n \}`. Covering radius satisfies Jarnik's inequality:

$$`\frac{1}{2} \lambda_n \leq \mu \leq \frac{1}{2} \sum_{i=1}^n \lambda_i \leq \frac{n}{2} \lambda_n,`

where $`\lambda_1,\dots,\lambda_n` are the {bpref "lattice.successive_minima"}[successive minima] of $`K` with respect to $`L`. The covering radius of the unit ball with respect to $`L` is called the covering radius of $`L`.

Depends on: {uses "lattice.successive_minima"}[]
:::

:::definition "lattice.definition" (lean := "TauCeti.IntegralLattice")
*Integral Lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.definition))

Let $`V` be an $`n`-dimensional vector space over a topological field $`F` (with $`\text{char}(F) \neq 2`) equipped with a nonsingular symmetric bilinear map $`B:V\times V\rightarrow F` and associated quadratic map $`Q(v):=B(v,v).`  The pair $`(V,Q)` is a *quadratic space*.  Fixing a basis, $`\{v_1,...,v_n\}` for $`V`, the space $`(V,Q)` has an associated quadratic form, that is, a homogeneous degree 2 polynomial, given by

$$`f(x_1,...,x_n)=\sum_{i,j}B(v_i,v_j)x_ix_j,`

where $`B(v_i,v_j)=B(v_j,v_i)` since $`B` is symmetric. It is often helpful to think of a quadratic space in terms of its {bpref "lattice.gram"}[Gram matrix] representation.

Let $`R` denote a subring of $`F`.  An $`R`-lattice is a finitely generated $`R`-module which is a discrete subset of $`V` endowed with the same bilinear map $`B`. In the special case when $`F=\mathbb{R}`, a *lattice* is simply a $`\mathbb{Z}`-lattice, $`L`, which is called *integral* if $`B(L,L)\subseteq \mathbb{Z}`.

For example, letting $`B(v,w)=v\cdot w`, the standard inner product, Euclidean $`n`-space can be thought of as the quadratic space $`(\mathbb{R}^n, \cdot)`.  In this case, the space $`(\mathbb{R}^n, \cdot)` contains the integral lattice $`\mathbb{Z}^n` as a discrete subset endowed with the standard inner product.

Currently, all the lattices in the database are {bpref "lattice.nondegenerate"}[nondegenerate], integral, and have {bpref "lattice.signature"}[signature] $`(n_+, n_-)` with $`n_+ \ge n_-`.

Depends on: {uses "lattice.gram"}[]
:::

:::definition "lattice.density"
*Density of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.density))

The density of a {bpref "lattice.positive_definite"}[positive definite] {bpref "lattice.definition"}[integral lattice] $`L` of {bpref "lattice.dimension"}[rank] $`n` is the density of the lattice-centered sphere packing in $`\mathbb{R}^n`.

The volume of a sphere in dimension $`n` is

$$`V_n = \frac{\pi^{n/2}}{(n/2)!} = \frac{2^n \pi^{(n-1)/2}((n-1)/2)!}{n!},`

where the first form is most useful when $`n` is even and the second form most useful when $`n` is odd.  Suppose that $`L` has {bpref "lattice.gram"}[Gram matrix] $`G` and {bpref "lattice.minimum"}[minimum] $`2\rho`.  Then the *density* of $`L` is

$$`\Delta = \frac{V_n \rho^n}{\sqrt{\det G}}`

while the *center density* of $`L` is

$$`\delta = \frac{\Delta}{V_n} = \frac{\rho^n}{\sqrt{\det G}}.`

The *lattice packing problem* of dimension $`n` is to find the {bpref "lattice.positive_definite"}[positive definite] lattices of rank $`n` which maximize the density. In general, these may not be solutions of the *sphere packing problem*, which asks for the maximum density of a sphere packing in which the centers of the spheres need not form an integral lattice.

Depends on: {uses "lattice.definition"}[] {uses "lattice.dimension"}[] {uses "lattice.gram"}[] {uses "lattice.minimum"}[] {uses "lattice.positive_definite"}[]
:::

:::definition "lattice.determinant" (lean := "TauCeti.IntegralLattice.determinant, TauCeti.IntegralLattice.gramDet")
*Determinant of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.determinant))

For an {bpref "lattice.definition"}[integral lattice] $`L`, the *determinant* of $`L` is defined as the determinant of the {bpref "lattice.gram"}[Gram matrix] associated to any basis of $`L`.

If $`L` is {bpref "lattice.positive_definite"}[positive definite] of {bpref "lattice.dimension"}[rank] $`n`, then the determinant of $`L` is also the square of the volume of the fundamental parallelotope of the Euclidean embedding of $`L` in $`\R^n`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.dimension"}[] {uses "lattice.gram"}[] {uses "lattice.positive_definite"}[]
:::

:::definition "lattice.dimension" (lean := "Module.finrank, TauCeti.IntegralLattice.finrank_carrier")
*Rank of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.dimension))

The *rank* of an {bpref "lattice.definition"}[integral lattice] is the rank of its underlying free $`\Z`-module.

Depends on: {uses "lattice.definition"}[]
:::

:::definition "lattice.discriminant"
*Discriminant of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.discriminant))

For an {bpref "lattice.definition"}[integral lattice] $`L`, the *discriminant* $`D` of $`L` is defined as the determinant of the {bpref "lattice.gram"}[Gram matrix] associated to any basis of $`L`.

There are several different conventions for the term "discriminant" in the literature; we give them different names here for clarity.  The definition we take above is used in Cassels' \*Rational Quadratic Forms\* and Conway-Sloane's \*Sphere Packings, Lattices and Groups\*.

- The *Witt discriminant* of $`L` is the quantity $`(-1)^{\binom{n}{2}} D`.  This choice makes the Witt discriminant of the {bpref "lattice.hyperbolic_plane"}[hyperbolic plane] $`U` equal to $`1` so that the Witt discriminant is stable under adding copies of $`U`.  It also simplifies the connection with Clifford algebras: using this definition, the center of the even Clifford algebra associated to the lattice will be the quadratic étale algebra generated by the square root of the Witt discriminant.  This convention is used in Milnor–Husemoller's \*Symmetric Bilinear Forms\* and Lam's \*Introduction to Quadratic Forms over Fields\*.

- The *absolute discriminant* of $`L` is the quantity $`\lvert D \rvert`.  This removes the sign ambiguity completely, and is used in Minkowski's \*Geometrie der Zahlen\* and Schmidt's \*Diophantine Approximations\*.

- The *geometric discriminant* of $`L` is the quantity $`\sqrt{\lvert D \rvert}`. For {bpref "lattice.postive_definite"}[positive definite] lattices of {bpref "lattice.dimension"}[rank] $`n`, the geometric discriminant is the covolume of any embedding of the lattice as a subgroup of $`\mathbb{R}^n`, ie the volume of a fundamental parallelotope.  Borevich and Shafarevich's \*Number Theory\* uses this definition.

- The *quadratic discriminant* of $`L` is the quantity $`2^{-n}D`.  While we define the {bpref "lattice.quadratic_form"}[quadratic form] associated to $`L` to be $`Q(\mathbf{v}) = \langle \mathbf{v}, \mathbf{v} \rangle`, some authors scale by $`\frac{1}{2}` so that integer valued quadratic forms can be obtained from integer matrices.  Doing so leads to the extra factor of $`2^{-n}`.  This convention is used in Dickson's \*History of the Theory of Numbers, Vol. II\* and Serre's \*Course in Arithmetic\*.

- The *half discriminant* of $`L` is $`2^{-n}D` when $`n` is even and $`2^{-n-1}D` when $`n` is odd.  This gives better behavior upon reduction to characteristic $`2`.  See Voight's \*Quaternion Algebras\* and Milnor–Husemoller's \*Symmetric Bilinear Forms\*.

- The *2-adic unit discriminant* of $`L` is the the quantity $`2^{-v_2(D)} D \pmod{8}`.  This is used in the $`2`-adic classification of quadratic spaces, and gives the $`2`-adic square class of the odd part of the discriminant.  It is defined in O'Meara's \*Introduction to Quadratic Forms\* and Earnest–Hsia's \*$`2`-adic Quadratic Forms\*.

Depends on: {uses "lattice.definition"}[] {uses "lattice.dimension"}[] {uses "lattice.gram"}[] {uses "lattice.hyperbolic_plane"}[] {uses "lattice.postive_definite"}[] {uses "lattice.quadratic_form"}[]
:::

:::definition "lattice.discriminant_group"
*Discriminant group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.discriminant_group))

For an {bpref "lattice.definition"}[integral lattice] $`L` with associated bilinear form $`B`, the *discriminant group* is the finite {bpref "group.abelian"}[abelian group] $`L^\vee / L`, where $`L^\vee` is the {bpref "lattice.dual"}[dual lattice] of $`L`.

The discriminant group is trivial if and only if $`L` is self-dual (i.e. unimodular).

The discriminant group $`L^\vee/L` is equipped with a *torsion bilinear form*:

$$`B_L\colon L^\vee/L\times L^\vee/L\to \mathbb{Q}/\mathbb{Z},\, (u+L, v+L)\mapsto B(u,v)+\mathbb{Z}.`

If the integral lattice $`L` is {bpref "lattice.parity"}[even], the group $`L^\vee/L` is moreover equipped with a *torsion quadratic form*:

$$`Q_L\colon L^\vee/L\to\mathbb{Q}/2\mathbb{Z},\, u+L\mapsto B(u,u)+2\mathbb{Z}.`

For a set of generators $`\{u_1+L,\ldots, u_r+L\}` of $`L^\vee/L`, one can represent the form $`Q_L` (resp. $`B_L` if $`L` is  {bpref "lattice.parity"}[odd]) by a *Gram matrix* $`M`: The diagonal entries of $`M` are given by rational representatives of $`Q_L(u_i+L)\in\mathbb{Q}/2\mathbb{Z}` (resp. of $`B_L(u_i+L, u_i+L)\in\mathbb{Q}/\mathbb{Z}`) for all $`1\leq i\leq r`, and the off-diagonal entries are given by rational representatives of $`B_L(u_i+L, u_j+L)\in\mathbb{Q}/\mathbb{Z}` for all $`i\neq j`.

The isometry class of the pair $`(L^\vee/L, Q_L)` as a finite abelian group equipped with a torsion quadratic form (resp. of the pair $`(L^\vee/L, B_L)` as a finite abelian group equipped with a torsion bilinear form, if $`L` is odd) is uniquely determined by the {bpref "lattice.genus"}[genus] of $`L`. Its isometry class is thus an intrinsic invariant of the genus, and together with the {bpref "lattice.signature"}[signature] they uniquely determine the genus of $`L`.

Depends on: {uses "group.abelian"}[] {uses "lattice.definition"}[] {uses "lattice.dual"}[] {uses "lattice.genus"}[] {uses "lattice.parity"}[] {uses "lattice.signature"}[]
:::

:::definition "lattice.dual"
*Dual lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.dual))

For an {bpref "lattice.definition"}[integral lattice], $`L`, its *dual* is the set $`L^\#=\{\vec{v}\in \Q L:B(\vec{v},L)\subseteq \mathbb{Z}\}`. There is a unique rescaling of the bilinear map $`B` for which $`L^\#` is a {bpref "lattice.primitive"}[primitive] integral lattice; we will refer to the resulting integral lattice as the *rescaled dual* of $`L`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.primitive"}[]
:::

:::definition "lattice.euclidean_basis" (lean := "Matrix.gram, TauCeti.IntegralLattice.gramMatrix, TauCeti.IntegralLattice.IsPosDef.exists_realization")
*Euclidean basis of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.euclidean_basis))

Let $`L` be a {bpref "lattice.positive_definite"}[positive definite] {bpref "lattice.definition"}[integral lattice] of {bpref "lattice.dimension"}[rank] $`n` with {bpref "lattice.gram"}[Gram matrix] $`G = (g_{ij})`.  A *Euclidean basis* for $`L` is a collection of vectors $`v_1, \dots, v_n \in \R^n` such that

$$`\langle v_i, v_j \rangle = g_{ij},`

for all $`i, j`.  Equivalently, if $`B` denotes the matrix whose rows are $`v_i`, then $`G = BB^T`.  This gives an explicit realization of the lattice $`L \hookrightarrow \R^n` as a discrete lattice in $`\R^n`, with respect to the usual dot product norm.

Depends on: {uses "lattice.definition"}[] {uses "lattice.dimension"}[] {uses "lattice.gram"}[] {uses "lattice.positive_definite"}[]
:::

:::definition "lattice.eutactic"
*Eutactic lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.eutactic))

A lattice $`L` in $`\mathbb{R}^n` is called *eutactic* if there exist positive real numbers $`c_1,\dots,c_m` such that for every $`v \in \mathbb{R}^n`, the inner product

$$`(v,v) = \sum_{j=1}^n c_j (v,x_j)^2,`

where the sum is over all the {bpref "lattice.minimal_vector"}[minimal vectors] of $`L`. A eutactic lattice is {bpref "lattice.well_rounded"}[well-rounded], and there are only finitely many {bpref "lattice.similarity"}[similarity classes] of eutactic lattices in each dimension $`n \geq 2`. A lattice is called *strongly eutactic* if the eutaxy coefficients $`c_1 = \dots = c_m`. Strongly eutactic lattices are {bpref "lattice.arithmetic"}[arithmetic].

Depends on: {uses "lattice.arithmetic"}[] {uses "lattice.minimal_vector"}[] {uses "lattice.similarity"}[] {uses "lattice.well_rounded"}[]
:::

:::definition "lattice.even_sublattice" (lean := "TauCeti.IntegralLattice.evenSublattice, TauCeti.IntegralLattice.evenSubmodule")
*Even sublattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.even_sublattice))

The *even sublattice* of an {bpref "lattice.definition"}[integral lattice] $`L` is the sublattice of $`L` spanned by vectors of even length.

An integral lattice $`L` is {bpref "lattice.parity"}[even] exactly when it is equal to its even sublattice.

In general, the even sublattice $`L_0` of an integral lattice $`L` has index at most equal to 2.

Depends on: {uses "lattice.definition"}[] {uses "lattice.parity"}[]
:::

:::definition "lattice.extreme"
*Extreme lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.extreme))

A lattice $`L` in $`\mathbb{R}^n` is called *extreme* if it is a local maximum of the {bpref "lattice.density"}[packing density] function in $`\mathbb{R}^n`. A theorem of Voronoi asserts that a lattice is extreme if and only if it is {bpref "lattice.perfect"}[perfect] and {bpref "lattice.eutactic"}[eutactic].

Depends on: {uses "lattice.density"}[] {uses "lattice.eutactic"}[] {uses "lattice.perfect"}[]
:::

:::definition "lattice.festi_veniani_index"
*Festi-Veniani index of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.festi_veniani_index))

For an {bpref "lattice.definition"}[integral lattice] $`L`, the *Festi--Veniani index* of $`L` is the index of the {bpref "lattice.automorphism_group"}[automorphism group] of $`L` in the automorphism group of the {bpref "lattice.discriminant_group"}[discriminant group] $`L^\vee/L`.

Depends on: {uses "lattice.automorphism_group"}[] {uses "lattice.definition"}[] {uses "lattice.discriminant_group"}[]
:::

:::definition "lattice.genus" (lean := "TauCeti.IntegralLattice.SameGenus, TauCeti.IntegralLattice.localIntegralForm")
*Genus of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.genus))

For an {bpref "lattice.definition"}[integral lattice], $`L` with underlying quadratic space $`V`, the *genus* of $`L` is the set of all lattices $`M` on $`V`, such that $`M_p\cong L_p` for all primes $`p`.

Depends on: {uses "lattice.definition"}[]
:::

:::definition "lattice.gram" (lean := "TauCeti.IntegralLattice.IsMinkowskiReduced, TauCeti.IntegralLattice.gramMatrix")
*Gram matrix.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.gram))

Fixing a basis $`\{v_1,...,v_n\}` for a space $`V`, the *Gram matrix* is the $`n\times n` symmetric matrix given by $`[B(v_i,v_j)]`.  Similarly, if we fix a basis $`\{w_1,...,w_n\}` for a lattice $`L`, then it is also a basis for $`V`, and the Gram matrix for $`L` is given by $`[B(w_i,w_j)]`.

For example, given the integral lattice $`\mathbb{Z}^3` on the Euclidean space $`\mathbb{R}^3`, in the standard basis $`\{e_1,e_2,e_3\}` the lattice (and hence the space) has a Gram matrix

$$`\begin{bmatrix}
1 & 0 & 0\\
0 & 1 & 0 \\
0 & 0 & 1
\end{bmatrix}.`

Although Gram matrices are only unique up to a choice of basis, each lattice in the database is identified by a single Gram matrix.  By entering a Gram matrix, $`G`, into the search field, the database will return an isometric lattice whose Gram matrix, $`A`, is equivalent to $`G` via conjugation by some transition matrix, $`T` (that is, $`A=T^tGT`), provided the lattice is in the database.

\{% if BETA %\}

Lattices in the database are presented in *Minkowski reduced form*.  That is, for an $`n`-dimensional lattice, $`L`, the gram matrix, $`A`, is given in a basis $`\{v_1,...,v_n\}` such that for each $`j\leq n`

$$`{v_j}^{*t}\cdot A\cdot {v_j}^*\geq v_j^t \cdot A\cdot v_j`

where $`v_j^*` runs through all vectors with which $`v_1,...v_{j-1}` can be extended to a basis. Minkowski reduction is not unique, but when $`n\leq 4`, the diagonal entries of a Minkowski reduced Gram matrix are precisely the successive minima of the lattice $`L` \[[MR1096467](https://mathscinet.ams.org/mathscinet/search/publdoc.html?arg3=1991&co4=AND&co5=AND&co6=AND&co7=AND&dr=pubyear&pg4=AUCN&pg5=TI&pg6=PC&pg7=ALLF&pg8=ET&r=1&review_format=html&s4=schulze-pillot&s5=&s6=&s7=&s8=All&sort=Newest&vfpref=html&yearRangeFirst=&yearRangeSecond=&yrop=eq)\].

\{% endif %\}
:::

:::definition "lattice.group_order" (lean := "TauCeti.IntegralLattice.Isometry")
*Group order of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.group_order))

The *group order* of an {bpref "lattice.definition"}[integral lattice] is the size of its {bpref "lattice.automorphism_group"}[automorphism group].

Depends on: {uses "lattice.automorphism_group"}[] {uses "lattice.definition"}[]
:::

:::definition "lattice.hermite_number" (lean := "TauCeti.IntegralLattice.discriminant, TauCeti.IntegralLattice.minimum")
*Hermite number.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.hermite_number))

The *Hermite number* of a {bpref "lattice.positive_definite"}[positive definite] {bpref "lattice.definition"}[integral lattice] $`L`, with absolute {bpref "lattice.determinant"}[determinant] $`d`, is given by

$$`\frac{m(L)}{d^{\frac{1}{n}}},`

where $`n` is the {bpref "lattice.dimension"}[rank] of $`L`, and $`m(L)` denotes the {bpref "lattice.minimal_vector"}[minimum] of $`L`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.determinant"}[] {uses "lattice.dimension"}[] {uses "lattice.minimal_vector"}[] {uses "lattice.positive_definite"}[]
:::

:::definition "lattice.hyperbolic_plane" (lean := "TauCeti.IntegralLattice.hyperbolicPlane")
*Hyperbolic plane.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.hyperbolic_plane))

The *hyperbolic plane* $`U` is the {bpref "lattice.definition"}[integral lattice] with {bpref "lattice.gram"}[Gram matrix]

$$`\begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}.`

Over a {bpref "ring.field"}[field] with {bpref "ring.characteristic"}[characteristic] not $`2`, every {bpref "lattice.nondegenerate"}[nondegenerate] {bpref "lattice.signature"}[indefinite] quadratic space is {bpref "lattice.isometry"}[isometric] to a direct sum of a definite quadratic space and some number of copies of the hyperbolic plane.  A version also holds for {bpref "lattice.parity"}[even] {bpref "lattice.unimodular"}[unimodular] lattices, which can be written as $`U^{\oplus r} \oplus E_8^{\oplus s}` or $`U^{\oplus r} \oplus E_8(-1)^{\oplus s}`.  But this direct sum decomposition does not hold for lattices.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[] {uses "lattice.isometry"}[] {uses "lattice.nondegenerate"}[] {uses "lattice.parity"}[] {uses "lattice.signature"}[] {uses "lattice.unimodular"}[] {uses "ring.characteristic"}[] {uses "ring.field"}[]
:::

:::definition "lattice.isometry" (lean := "TauCeti.IntegralLattice.Isometry, QuadraticMap.IsometryEquiv, QuadraticMap.Equivalent, TauCeti.IntegralLattice.Isometry.ofGramMatrixEq")
*Isometries between integral lattices.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.isometry))

Two {bpref "lattice.definition"}[integral lattices], $`L` and $`L'`, are *isometric* if there exists a map $`\sigma:L\rightarrow L'` such that $`Q(\vec{v})=Q(\sigma(\vec{v}))` for all $`\vec{v}\in L`. If this is the case, we say $`L\cong L'`. The set of all lattices $`M` such that $`M\cong L` is called the *isometry class* (or simply the *class*) of $`L`.

If $`L` and $`L'` have associated {bpref "lattice.gram"}[Gram matrices] $`G` and $`G'`, then $`L\cong L'` implies that $`G=T\cdot G'\cdot T^t` for some $`T\in GL_n(\mathbb{Z})`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[]
:::

:::definition "lattice.kissing"
*Kissing number.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.kissing))

The *kissing number* of a lattice, $`L`, is the number of vectors of {bpref "lattice.minimal_vector"}[minimal length].  The vectors in the list of {bpref "lattice.minimal_vector"}[minimal length] vectors are normalized, so the kissing number will always be twice as large as the number of vectors in this list.

The *lattice kissing number problem* in {bpref "lattice.dimension"}[dimension] $`n` is to find the lattices of dimension $`n` which maximize the kissing number. In general, these may not be solutions of the *general kissing number problem*, which asks for the maximum number of spheres with non-overlapping interiors in dimension $`n` which are all tangent to a single sphere.

Depends on: {uses "lattice.dimension"}[] {uses "lattice.minimal_vector"}[]
:::

:::definition "lattice.level" (lean := "TauCeti.IntegralLattice.level")
*Level of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.level))

For an {bpref "lattice.definition"}[integral lattice], $`L`, the *level* is the smallest integer, $`N`, such that $`N\cdot B(\vec{v},\vec{v})\in 2\mathbb{Z}` for all $`\vec{v}` in the {bpref "lattice.dual"}[dual] of $`L`.

This is related to the {bpref "group.exponent"}[exponent] $`e` of the {bpref "lattice.discriminant_group"}[discriminant group]: either $`N = e` or $`N = 2e`.  You can determine when the second case occurs using the {bpref "lattice.conway_genus_symbol"}[Conway genus symbol]: the level will be $`2e` when the highest $`2`-adic block is of type I, and it will be $`e` when the highest $`2`-adic block is of type II (or if $`2` does not divide the {bpref "lattice.discriminant"}[discriminant]).

Depends on: {uses "group.exponent"}[] {uses "lattice.conway_genus_symbol"}[] {uses "lattice.definition"}[] {uses "lattice.discriminant"}[] {uses "lattice.discriminant_group"}[] {uses "lattice.dual"}[]
:::

:::definition "lattice.mass"
*Mass of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.mass))

For an {bpref "lattice.definition"}[integral lattice] $`L`, the *mass* of $`L` is the weighted sum

$$`\sum_{\Lambda} \frac{1}{\# \text{Aut} (\Lambda)}`

where the sum runs over all isometry classes of lattices $`\Lambda` in the same {bpref "lattice.genus"}[genus] as $`L`.  Here $`\text{Aut}(\Lambda)` denotes the {bpref "lattice.automorphism_group"}[automorphism group] of $`\Lambda`.

Depends on: {uses "lattice.automorphism_group"}[] {uses "lattice.definition"}[] {uses "lattice.genus"}[]
:::

:::definition "lattice.minimal_vector" (lean := "TauCeti.IntegralLattice.minimum, TauCeti.IntegralLattice.vectorsOfNorm")
*Minimum.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.minimal_vector))

For an {bpref "lattice.definition"}[integral lattice], $`L`, the *minimum*, denoted $`m(L)`, is the length of the shortest non-zero vector in $`L`.  A *minimal vector* in $`L` is a vector $`\vec{v}` such that $`Q(\vec{v})=m(L)`.

Depends on: {uses "lattice.definition"}[]
:::

:::definition "lattice.minimum" (lean := "TauCeti.IntegralLattice.minimum, TauCeti.IntegralLattice.vectorsOfNorm")
*Minimum.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.minimum))

For an {bpref "lattice.definition"}[integral lattice], $`L`, the *minimum*, denoted $`m(L)`, is the length of the shortest non-zero vector in $`L`.  A *minimal vector* in $`L` is a vector $`\vec{v}` such that $`Q(\vec{v})=m(L)`.

Depends on: {uses "lattice.definition"}[]
:::

:::definition "lattice.nondegenerate" (lean := "TauCeti.IntegralLattice.IsNondegenerate, LinearMap.BilinForm.Nondegenerate, TauCeti.IntegralLattice.signature, TauCeti.IntegralLattice.IsPosSemidef")
*Nondegenerate lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.nondegenerate))

An {bpref "lattice.definition"}[integral lattice] $`L` with bilinear form $`B` is *nondegenerate* if

$$`\{w \in L : B(v, w) = 0 \text{ for all } v \in L\} = 0.`

Otherwise, we call $`L` degenerate.  All lattices in the database are nondegenerate, but some definitions require degenerate lattices.  In particular, the *signature* of a (possibly degenerate) lattice is a triple $`(n_+, n_0, n_-)` where $`n_+` and $`n_-` are as in the standard {bpref "lattice.signature"}[signature] and $`n_0` is the number of $`0` eigenvalues for a {bpref "lattice.gram"}[Gram matrix].  A lattice is degenerate if and only if $`n_0 > 0`.  We say $`L` is *positive semidefinite* if $`n_-=0`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[]
:::

:::definition "lattice.norm" (lean := "TauCeti.IntegralLattice.norm, TauCeti.IntegralLattice.integralNorm")
*Norm of a vector.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.norm))

Given an {bpref "lattice.definition"}[integral lattice] $`L` with associated bilinear map $`B`, the *norm* of a vector $`v \in L` is $`B(v, v)`. If $`L` has {bpref "lattice.gram"}[Gram matrix] $`A`, then the norm of $`v` is $`v^T A v`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[]
:::

:::definition "lattice.norm1_sublattice"
*Norm 1 sublattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.norm1_sublattice))

Given an {bpref "lattice.definition"}[integral lattice] $`L`, the *norm 1 sublattice* is the {bpref "lattice.sublattice"}[sublattice] of $`L` generated by all vectors of {bpref "lattice.norm"}[norm] 1 in $`L`.

If $`L` is {bpref "lattice.parity"}[even], then the norm 1 sublattice is trivial.  If $`L =I_n`, then the norm 1 sublattice is the lattice $`I_n` itself.

Depends on: {uses "lattice.definition"}[] {uses "lattice.norm"}[] {uses "lattice.parity"}[] {uses "lattice.sublattice"}[]
:::

:::definition "lattice.normalized_minimal_vector"
*Normalized minimal vector of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.normalized_minimal_vector))

For an {bpref "lattice.definition"}[integral lattice] $`L`, the {bpref "lattice.minimal_vector"}[minimal vectors] of $`L` come in pairs: if $`\vec{v}` is a minimal vector, then so is $`-\vec{v}`. A minimal vector is *normalized* if its first nonzero component is positive.

Depends on: {uses "lattice.definition"}[] {uses "lattice.minimal_vector"}[]
:::

:::definition "lattice.orthogonal_decomposition"
*Orthogonal decomposition of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.orthogonal_decomposition))

Let $`L` be an integral lattice, with bilinear form $`B : L \times L \to \Z`. An *orthogonal decomposition* of $`L` is a direct sum decomposition

$$`L = L_1 \oplus L_2 \oplus \dots \oplus L_r`

such that $`B(x_i, x_j) = 0` for all $`x_i \in L_i`, $`x_j \in L_j`, where $`i \not = j`.  Equivalently, if $`G` is the Gram matrix of $`L`, then after a suitable change of basis, it has the block diagonal form

$$`G = \begin{pmatrix}  G_1 & & & \\ & G_2 & & \\ & & \ddots & \\ & & & G_r  \end{pmatrix}`

where each $`G_i` is a Gram matrix for $`L_i`.

 A lattice is (orthogonally) *indecomposable* if it does not admit a non-trivial orthogonal decomposition.

A theorem of Kneser states that every lattice admits a unique orthogonal decomposition into indecomposable summands.  This decomposition is unique up to ordering and isometry of the summands.
:::

:::definition "lattice.parity" (lean := "TauCeti.IntegralLattice.IsEven")
*Parity of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.parity))

If an {bpref "lattice.definition"}[integral lattice] $`L` has {bpref "lattice.gram"}[Gram matrix] $`M`, we say that $`L` is *even* if all of the diagonal entries of $`M` are even, and *odd* otherwise.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[]
:::

:::definition "lattice.perfect"
*Perfect lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.perfect))

A lattice $`L` in $`\mathbb{R}^n` is called *perfect* if the space of $`n \times n` real symmetric matrices is spanned by the set of $`n \times n` symmetric matrices

$$`\{ x x^{\top} : x \in S(L) \},`

where $`S(L)` is the set of {bpref "lattice.minimal_vector"}[minimal vectors] of $`L`. A perfect lattice is {bpref "lattice.well_rounded"}[well-rounded], {bpref "lattice.arithmetic"}[arithmetic], and is uniquely determined by its minimal vectors. Further, there are only finitely many {bpref "lattice.similarity"}[similarity classes] of perfect lattices in each dimension $`n \geq 2`.

Depends on: {uses "lattice.arithmetic"}[] {uses "lattice.minimal_vector"}[] {uses "lattice.similarity"}[] {uses "lattice.well_rounded"}[]
:::

:::definition "lattice.pneighbor"
*p-Neighbor of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.pneighbor))

Given an integral lattice $`L` and a prime $`p`, a *$`p`-neighbor* of $`L` is an integral lattice $`M` such that

$$`[L : L \cap M ] = [M : L \cap M ] = p.`

We denote the $`p`-neighborhood relation as $`L \sim_p M`.  This is a symmetric relation, but in general is not  reflexive nor transitive.  If two lattices are $`p`-neighbors, then they lie in the same genus.
:::

:::definition "lattice.pneighbor_adjacency"
*p-Neighbor adjacency matrix of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.pneighbor_adjacency))

Let $`\mathcal{G}` be a {bpref "lattice.genus"}[genus]  of {bpref "lattice.definition"}[integral lattices], with {bpref "lattice.class_number"}[class number] $`h` and with representatives $`\{L_1, L_2, \dots, L_h\}`.  The *p-neighbor adjacency graph* of $`\mathcal{G}` is the weighted directed graph with $`h` vertices  $`\{L_1, L_2, \dots, L_h\}`, and with a directed edge from $`L_i` to $`L_j`, where the edge weight is the number of {bpref "lattice.pneighbor"}[$`p`-neighbors] of $`L_i` which are {bpref "lattice.isometry"}[isometric] to $`L_j`.

The *$`p`-neighbor adjacency matrix* is the adjacency matrix of the $`p`-neighbor adjacency graph.  In general, the $`p`-neighbor adjacency matrix does not need to be symmetric, and can contain self-edges.

Depends on: {uses "lattice.class_number"}[] {uses "lattice.definition"}[] {uses "lattice.genus"}[] {uses "lattice.isometry"}[] {uses "lattice.pneighbor"}[]
:::

:::definition "lattice.positive_definite" (lean := "TauCeti.IntegralLattice.IsPosDef, QuadraticMap.PosDef, Matrix.PosDef")
*Positive definite lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.positive_definite))

An {bpref "lattice.definition"}[integral lattice] $`L` is *positive definite* if the {bpref "lattice.gram"}[Gram matrix] of the bilinear form $`B` on $`L` is a positive definite matrix. This is equivalent to the condition that $`B(u,u)>0` for all $`u \in L \setminus\{0\}`.

The {bpref "lattice.signature"}[signature] of a rank $`n` positive definite integral lattice is $`(n, 0)`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[]
:::

:::definition "lattice.postive_definite" (lean := "TauCeti.IntegralLattice.IsPosDef, QuadraticMap.PosDef, Matrix.PosDef")
*Positive definite lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.postive_definite))

An {bpref "lattice.definition"}[integral lattice] $`L` is *positive definite* if the {bpref "lattice.gram"}[Gram matrix] of the bilinear form $`B` on $`L` is a positive definite matrix. This is equivalent to the condition that $`B(u,u)>0` for all $`u \in L \setminus\{0\}`.

The {bpref "lattice.signature"}[signature] of a rank $`n` positive definite integral lattice is $`(n, 0)`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[] {uses "lattice.signature"}[]
:::

:::definition "lattice.primitive" (lean := "LinearMap.BilinForm.scaleIdeal, TauCeti.IntegralLattice.scaleIdeal")
*Primitive integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.primitive))

An {bpref "lattice.definition"}[integral lattice], $`L`, with an associated {bpref "lattice.gram"}[Gram matrix], $`G=[g_{ij}]`, is called *primitive* if
$`\gcd(\{g_{ij}:1\leq i\leq n,i\leq j\leq n\})=1`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[]
:::

:::definition "lattice.quadratic_form"
*Quadratic form of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.quadratic_form))

Given an {bpref "lattice.definition"}[integral lattice] $`L` with {bpref "lattice.gram"}[Gram matrix] $`G`, the *quadratic form* of $`L` is the function on $`L \otimes \mathbb{Q}` defined by

$$`Q(\mathbf{v}) = \langle \mathbf{v},\mathbf{v}\rangle = \mathbf{v}^{\mathrm{T}}G\mathbf{v}.`

We will refer to the value $`Q(v)` as the *norm* of $`v`.  By construction, $`Q(L) \subseteq \mathbb{Z}`, and we say that $`Q` or $`L` is *universal* if $`Q(L) = \mathbb{Z}`.  An {bpref "lattice.parity"}[even] lattice can never be universal since $`Q(L) \subseteq 2\mathbb{Z}`; we say that $`L` is *even universal* if $`Q(L) \supseteq 2\mathbb{Z}`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[] {uses "lattice.parity"}[]
:::

:::definition "lattice.root_lattice" (lean := "RootPairing, RootPairing.IsRootSystem, RootPairing.IsCrystallographic, RootPairing.IsReduced, RootPairing.rootSpan, RootPairing.weylGroup")
*Root lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.root_lattice))

A *root system* is a finite set $`\Phi` of nonzero vectors (called *roots*) in a Euclidean space $`E` satisfying the following conditions.

- The roots span $`E`.

- For $`\alpha \in \Phi`, the only scalar multiples of $`\alpha` in $`E` are $`\pm \alpha`.

- For $`\alpha, \beta \in \Phi`, the quantity $`2 \frac{\alpha \cdot \beta}{\alpha \cdot \alpha}` is an integer.

- For $`\alpha,\beta \in \Phi`, we have $`\beta - 2 \frac{\alpha \cdot \beta}{\alpha \cdot \alpha} \alpha \in \Phi`. That is, $`\Phi` is stable under the reflection through the hyperplane perpendicular to $`\alpha`.

The lattice generated by $`\Phi` is a *root lattice*.

The product of two root systems is again a root system. Root systems which are irreducible for this product are classified by Dynkin diagrams, which have standard names (where the subscript is always the dimension of the lattice):

$$`A_n \,(n \geq 1), \,B_n \,(n \geq 2), \,C_n\, (n \geq 3), \,D_n \,(n \geq 4), \,E_6,\, E_7, \,E_8, \,F_4,\, G_2.`

Some small indices are omitted due to exceptional equalities:

$$`B_1 = A_1, \,C_2 = B_2, \,D_3 = A_3.`

In addition, in some cases multiple root systems generate the same lattice. The names used for root lattices are:

$$`A_n \,(n \geq 1), \,D_n \,(n \geq 4), \,E_6, \,E_7, \,E_8.`

For any root system, the reflections in the hyperplanes orthogonal to the roots generate a finite group, called the *Weyl group*. The Weyl group is a subgroup of the {bpref "lattice.automorphism_group"}[automorphism group] of the root lattice.

Depends on: {uses "lattice.automorphism_group"}[]
:::

:::definition "lattice.root_sublattice"
*Root sublattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.root_sublattice))

The *root sublattice* of a {bpref "lattice.positive_definite"}[positive definite] {bpref "lattice.definition"}[integral lattice] $`L` is the sublattice of $`L` spanned by vectors of length at most equal to 2.

A positive definite integral lattice $`L` is called a *root lattice* if it is equal to its root sublattice.

Depends on: {uses "lattice.definition"}[] {uses "lattice.positive_definite"}[]
:::

:::definition "lattice.signature" (lean := "sigPos, sigNeg, TauCeti.IntegralLattice.signature, TauCeti.IntegralLattice.IsNegDef, TauCeti.IntegralLattice.IsIndefinite")
*Signature of an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.signature))

For a {bpref "lattice.nondegenerate"}[nondegenerate] {bpref "lattice.definition"}[integral lattice] $`L`, the *signature* of $`L` is a pair $`(n_+, n_-)`, where $`n_+` (resp. $`n_-`) is the number of positive (resp. negative) eigenvalues of a {bpref "lattice.gram"}[Gram matrix] for $`L`.  Note that the {bpref "lattice.nondegenerate"}[signature] of a degenerate lattice has an extra component $`n_0` for the number of $`0` eigenvalues.  The signature classifies lattices up to isometry over the real numbers.

If $`L` has signature $`(n,0)` we say it is {bpref "lattice.positive_definite"}[positive definite]; if it has signature $`(0,n)` we say it is *negative definite*; otherwise we say it is *indefinite*.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[] {uses "lattice.nondegenerate"}[] {uses "lattice.positive_definite"}[]
:::

:::definition "lattice.similarity"
*Similarity of lattices.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.similarity))

Lattices $`L` and $`M` are called *similar* if there exists a real constant $`\alpha` so that $`L` is {bpref "lattice.isometry"}[isometric] to $`\alpha M`. Key properties of lattices, such as {bpref "lattice.well_rounded"}[well-roundedness], {bpref "lattice.eutactic"}[eutaxy], {bpref "lattice.perfect"}[perfection], {bpref "lattice.density"}[packing density] are preserved on similarity classes.  Each similarity class that contains an integer lattice contains a unique {bpref "lattice.primitive"}[primitive] integer lattice.

Depends on: {uses "lattice.density"}[] {uses "lattice.isometry"}[] {uses "lattice.primitive"}[] {uses "lattice.well_rounded"}[]
:::

:::definition "lattice.spherical_design"
*Spherical design lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.spherical_design))

A collection of $`m \geq 1` points $`\{ v_1,\dots,v_m \}` on a sphere $`S_n(r)` of radius $`r >0` in $`\mathbb{R}^n` centered at the origin is a called a *spherical $`t`-design* if for every polynomial $`f(x) = f(x_1,\dots,x_n)` in $`n` variables with real coefficients of degree no bigger than $`t`, $`t \geq 1`,

$$`\int_{S_n(r)} f(x) dx = \frac{1}{m} \sum_{i=1}^m f(v_i),`

where the measure $`dx` is normalized so that the measure of $`S_n(r)` is $`1`. A lattice $`L` is called a *spherical $`t`-design lattice* if its set of {bpref "lattice.minimal_vector"}[minimal vectors] $`S(L)` is a spherical $`t`-design.

A lattice is a spherical $`2`-design if and only if it is {bpref "lattice.eutactic"}[strongly eutactic]. A lattice $`L` is called *strongly perfect* if it is a spherical $`4`-design; this last condition implies that it is {bpref "lattice.perfect"}[perfect] and is a strictly stronger condition.

Depends on: {uses "lattice.eutactic"}[] {uses "lattice.minimal_vector"}[] {uses "lattice.perfect"}[]
:::

:::definition "lattice.sublattice"
*Sublattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.sublattice))

Given an {bpref "lattice.definition"}[integral lattice] $`L`, a *sublattice* of $`L` is a subgroup $`M \subseteq L` which is itself a lattice.

There are several special named sublattices of $`L`:

- *Norm 1 sublattice* - the sublattice generated by vecotrs of {bpref "lattice.norm"}[norm] $`1`.

- *Root sublattice* - the sublattice generated by all vectors of norm $`2`.

- *Min vector sublattice* - the sublattice generated by all {bpref "lattice.minimal_vector"}[minimal vectors].

- *Even sublattice* - the sublattice generated by vectors of even norm.

- *Max diag sublattice* - the maximal sublattice whose {bpref "lattice.gram"}[Gram matrix] is diagonal.

Depends on: {uses "lattice.definition"}[] {uses "lattice.gram"}[] {uses "lattice.minimal_vector"}[] {uses "lattice.norm"}[]
:::

:::definition "lattice.successive_minima"
*Successive minima.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.successive_minima))

*Successive minima* $`\lambda_1,\dots,\lambda_n` of a $`\boldsymbol 0`-symmetric convex body $`K \subset \mathbb{R}^n` with respect to a full-rank lattice $`L \subset \mathbb{R}^n` is defined as $`\lambda_i = \min \{ t > 0 : \text{dim}_{\mathbb{R}} \text{span}_{\mathbb{R}}(tK \cap L) \geq i \}`. Then $`0 < \lambda_1 \leq \dots \leq \lambda_n`, and

$$`\frac{2^n \text{det}(L)}{n! \text{Vol}(K)} \leq \lambda_1 \cdots \lambda_n \leq \frac{2^n \text{det}(L)}{\text{Vol}(K)},`

by Minkowski's Successive Minima Theorem. Successive minima of $`L` are the successive minima of the unit ball with respect to $`L`.
:::

:::definition "lattice.tensor_decomposition"
*Tensor decomposition of a lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.tensor_decomposition))

Given {bpref "lattice.definition"}[integral lattices] $`L_1` and $`L_2`, we define the *tensor product* of $`L_1` and $`L_2` as the lattice $`L = L_1 \otimes_{\Z} L_2`, where the associated bilinear form is defined as

$$`B( v_1 \otimes w_1, v_2 \otimes w_2 ) = B_{L_1} ( v_1, v_2) B_{L_2} (w_1,  w_2),`

extended bilinearly. The {bpref "lattice.dimension"}[rank] of $`L` is the product of the ranks of $`L_1` and $`L_2`, and the determinant of $`L` is $`\det(L_1)^{\operatorname{rank}(L_2)} \cdot \det(L_2)^{\operatorname{rank}(L_1)}`.

We say that $`L` is *tensor decomposable* if it can be written as $`L = L_1 \otimes L_2` for some integral lattices $`L_1` and $`L_2`.  If not, we say $`L` is *tensor indecomposable*.

A *tensor decomposition* of $`L` is a decomposition of the form $`L = L_1 \otimes L_2 \otimes \dots \otimes L_r`.

Depends on: {uses "lattice.definition"}[] {uses "lattice.dimension"}[]
:::

:::definition "lattice.theta"
*Theta series for an integral lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.theta))

The *theta series* $`\Theta_L` of an {bpref "lattice.definition"}[integral lattice] $`L` is a generating function for the number of vectors $`v\in L` of {bpref "lattice.quadratic_form"}[norm] $`n`.  Specifically, we define

$$`\Theta_L(q) = \sum_{v \in L} q^{\frac{1}{2}\langle v,v \rangle}`

If $`L` has {bpref "lattice.dimension"}[rank] $`n` and {bpref "lattice.level"}[level] $`N` and we take $`q = e^{2\pi i z}` as usual, this will be a modular form of {bpref "cmf.weight"}[weight] $`k = \frac{n}{2}` and {bpref "cmf.level"}[level] $`N`.  In the case that $`n` is odd, to get a {bpref "cmf"}[classical modular form] with integer weight one may apply the Shimura lift, which will produce a modular form of weight $`n-1`.

In order to express the theta series in terms of a power series with integral exponents, we will usually record

$$`\Theta_L(q^2) = \sum_{v \in L} q^{\langle v,v \rangle},`

which allows a more direct recovery of the number of vectors of each possible norm.

Depends on: {uses "cmf"}[] {uses "cmf.level"}[] {uses "cmf.weight"}[] {uses "lattice.definition"}[] {uses "lattice.dimension"}[] {uses "lattice.level"}[] {uses "lattice.quadratic_form"}[]
:::

:::definition "lattice.unimodular" (lean := "TauCeti.IntegralLattice.IsUnimodular")
*Unimodular lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.unimodular))

An {bpref "lattice.definition"}[integral lattice] is *unimodular* if its {bpref "lattice.determinant"}[determinant] is equal to 1.

Depends on: {uses "lattice.definition"}[] {uses "lattice.determinant"}[]
:::

:::definition "lattice.well_rounded"
*Well-rounded lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/lattice.well_rounded))

A lattice $`L` is called *well-rounded* if its set of {bpref "lattice.minimal_vector"}[minimal vectors] $`S(L)` spans a sublattice $`M` of finite index, and $`L` is said to be *generated by minimal vectors* if $`M = L`. The lattice $`L` is *strongly well-rounded* if the set $`S(L)` contains a basis for $`L`. Being generated by minimal vectors is a strictly stronger condition than well-rounded for lattices of rank $`\geq 5`, and a strictly weaker condition than strongly well-rounded for lattices of rank $`\geq 10`.

Depends on: {uses "lattice.minimal_vector"}[]
:::
