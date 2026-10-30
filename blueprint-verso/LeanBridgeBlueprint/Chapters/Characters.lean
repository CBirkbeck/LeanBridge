import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dirichlet characters" =>

This chapter lists the LMFDB definitions relating to *Dirichlet characters*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "character.dirichlet.conrey"
*Conrey label of Dirichlet characters.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conrey))

We use the notation $`\chi_{q}(n,\cdot)` to identify {bpref "character.dirichlet"}[Dirichlet characters] $`\Z\to \C`, where $`q` is the
{bpref "character.dirichlet"}[modulus], and $`n` is the {bpref "character.dirichlet.conrey.index"}[index], a positive integer coprime to $`q` that identifies a Dirichlet character of modulus $`q` as described below.  The LMFDB label $`\texttt{q.n}`, with $`1\le n < \max(q,2)` uniquely identifies $`\chi_{q}(n,\cdot)`.

Introduced by Brian Conrey, this labeling system is based on an explicit isomorphism between the multiplicative group $`(\Z/q\Z)^\times` and the {bpref "character.dirichlet.group"}[group of Dirichlet characters] of modulus $`q` that makes it easy to recover the
{bpref "character.dirichlet.conrey.order"}[order], the
{bpref "character.dirichlet.conrey.conductor"}[conductor], and the
{bpref "character.dirichlet.conrey.parity"}[parity]
of a Dirichlet character from its label, or to {bpref "character.dirichlet.induce"}[induce] characters.

As an example,
$`\chi_q(1, \cdot)` is always trivial, $`\chi_q(m,\cdot)` is real if $`m^2=1\bmod q`, and for all $`m,n` coprime to $`q` we have $`\chi_q(m,n)=\chi_q(n,m)`.

For prime powers $`q=p^e` we define $`\chi_q(n,\cdot)` as follows:

- For each odd prime $`p` we choose the least positive integer $`g_p` which

 {bpref "character.dirichlet.conrey.primitive_generator"}[is a
  primitive root for all $`p^e`], and then for $`n \equiv g_p^a` mod $`p^{e}` and $`m
  \equiv g_p^{b}` mod $`p^{e}` coprime to $`p` we define

$$`\chi_{p^e}(n, m) = \exp\left(2\pi i \frac{a b}{\phi(p^{e})} \right).`

- $`\chi_2(1, \cdot)` is trivial, $`\chi_4(3, \cdot)` is the

  unique nontrivial character of modulus $`4`, and for larger powers of $`2` we choose
  $`-1` and $`5` as generators of the multiplicative group. For $`e > 2`, if

$$`n \equiv \epsilon_a 5^a \pmod{2^e}`

  and

$$`m \equiv \epsilon_b 5^b \pmod{2^e}`

  with $`\epsilon_a, \epsilon_b \in \{\pm 1\}`, then

$$`\chi_{2^e}(n, m) = \exp\left(2 \pi i \left(\frac{(1 - \epsilon_a)(1 - \epsilon_b)}{8}
        + \frac{ab}{2^{e-2}}\right)\right).`

For general $`q`, the function $`\chi_q(n, m)` is defined multiplicatively: $`\chi_{q_1 q_2}(n, m) := \chi_{q_1}(n, m)\chi_{q_2}(n, m)`  for all coprime positive integers $`q_1` and $`q_2`.  The Chinese remainder theorem implies that this definition is well founded and that every Dirichlet character can be defined in this way.  In particular, every Dirichlet character $`\chi` of modulus $`q` can be written uniquely as a product of Dirichlet characters of prime power modulus.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conrey.conductor"}[] {uses "character.dirichlet.conrey.index"}[] {uses "character.dirichlet.conrey.parity"}[] {uses "character.dirichlet.conrey.primitive_generator"}[] {uses "character.dirichlet.group"}[] {uses "character.dirichlet.induce"}[]
:::

:::definition "character.dirichlet.conrey.conductor"
*Conductor of a Dirichlet character from its Conrey label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conrey.conductor))

Let
$$`\chi_q(n,\cdot)=\prod_{p|q}\chi_{p^e}(n,\cdot)`
 be the unique factorization of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi_q(n,\cdot)` into characters of prime power modulus $`p^e` under the {bpref "character.dirichlet.conrey"}[Conrey labeling system].  The {bpref "character.dirichlet.conductor"}[conductor] of $`\chi_q(n,\cdot)` is the product of the conductors of the $`\chi_{p^e}(n,\cdot)`.

For odd primes $`p` and $`1\leq f\leq e`, the isomorphism between $`(\Z/p^f\Z)^\times`
and the image of $`x\mapsto x^{p^{e-f}}` in $`(\Z/p^e\Z)^\times` is compatible with
the Conrey labeling system.

Thus for odd primes $`p`, the conductor of $`\chi_{p^e}(n,\cdot)` is

- $`1` if $`n\equiv 1\bmod p^e`;

- $`p^f` if $`n^{p-1}` has order $`p^{f-1}` modulo $`p^e`.

For $`p=2` the conductor of $`\chi_{p^e}(n,\cdot)` is

- 1 if $`n\equiv 1\bmod 2^e`;

- $`4` if $`e=2` and $`n\equiv 3\bmod 4`;

- $`2^{f+2}` if $`e\geq3` and $`\varepsilon n` has order $`2^f` modulo $`2^e`, where $`\varepsilon\in\{-1,1\}` satisfies $`n\equiv \epsilon\bmod 4`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[]
:::

:::definition "character.dirichlet.conrey.index"
*Conrey index of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conrey.index))

The *Conrey index* (or *index*) of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of {bpref "character.dirichlet.modulus"}[modulus] $`q` is the unique positive integer $`n < \max(q,2)` for which $`\chi = \chi_q(n,\cdot)` in the {bpref "character.dirichlet.conrey"}[Conrey labeling system].

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.conrey.orbit_label" (lean := "DirichletCharacter.galoisOrbitLabel, DirichletCharacter.galoisOrbitIndex, DirichletCharacter.galoisOrbitTraceVector, DirichletCharacter.letterCode")
*Labels for Galois orbits of Dirichlet Characters.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conrey.orbit_label))

A {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of {bpref "character.dirichlet"}[Dirichlet characters] is labelled as $`\texttt{q.A}`, where $`\texttt{q}` is the modulus of the characters in the orbit, and $`\texttt{A}` is a lower-case letter which corresponds to the lexicographic ordering of the Galois-invariant vector $`\left( \textup{Order}(\chi), \mathrm{Tr}(\chi(2)), \cdots, \mathrm{Tr}(\chi(\texttt{q} - 1) \right)`, for $`\chi` any Dirichlet character in the orbit. See Section 3.3 of  for more details.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[]
:::

:::definition "character.dirichlet.conrey.order"
*Order of a Dirichlet character from its label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conrey.order))

Since $`\chi_q(m^r,n)=\chi_q(m,n)^r,` a {bpref "character.dirichlet"}[Dirichlet character] of {bpref "character.dirichlet.conrey"}[Conrey index] $`m`
has {bpref "character.dirichlet.order"}[order] $`r`, where $`r` is the multiplicative order of $`m` in $`(\Z/q\Z)^\times`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conrey"}[] {uses "character.dirichlet.order"}[]
:::

:::definition "character.dirichlet.conrey.parity"
*Parity of a Dirichlet character from its Conrey label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conrey.parity))

Let
$$`\chi_q(n,\cdot)=\prod_{p|q}\chi_{p^e}(n,\cdot)`
 be the unique factorization of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi_q(n,\cdot)` into characters of prime power modulus $`p^e` under the {bpref "character.dirichlet.conrey"}[Conrey labeling system]. The {bpref "character.dirichlet.parity"}[parity] of $`\chi_q(n,\cdot)` is the sum of the parities of the Dirichlet characters $`\chi_{p^e}(n,\cdot)`, which can be computed as follows:

- for $`p>2`, the character $`\chi_{p^e}(n,\cdot)` is even if and only if $`n` is a square modulo $`p`;

- for $`p=2` and $`e>1` the character $`\chi_{p^e}(n,\cdot)` is even if and only if $`n` is a square modulo $`4`.

- for $`p=2` and $`e=1` the character $`\chi_{p^e}(n,\cdot)=\chi_2(1,\cdot)` is even.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.parity"}[]
:::

:::definition "character.dirichlet.conrey.primitive_generator"
*Conrey primitive generator modulo $`p`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conrey.primitive_generator))

For an odd prime $`p` and an exponent $`e\geq1`, the group $`(\Z/p^e\Z)^\times` is cyclic. It happens that any integer $`a` which generates $`(\Z/p^2\Z)^\times` will also be a generator of $`(\Z/p^e\Z)^\times` for all $`e\geq 1`. We call the least such $`a` the *Conrey (primitive) generator* modulo p.

Interestingly, the Conrey generator is also the smallest generator of $`(\Z/p\Z)^\times`
for all primes $`p<10^{12}` except two cases:

- for $`p=40487`, the Conrey generator is $`10` instead of $`5`.

- for $`p=6692367337`, the Conrey generator is $`7` instead of $`5`.
:::

:::definition "character.dirichlet.degree" (lean := "Module.finrank, IntermediateField.adjoin, TauCeti.CharacterField")
*Degree of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.degree))

The *degree* of a Dirichlet character $`\chi` is the {bpref "nf.degree"}[degree] of its {bpref "character.dirichlet.value_field"}[field of values] $`\Q(\chi(\Z))`.

If $`\chi` has {bpref "character.dirichlet.order"}[order] $`n` then its degree is $`\phi(n):=\#(\Z/n\Z)^\times`.

Depends on: {uses "character.dirichlet.order"}[] {uses "character.dirichlet.value_field"}[] {uses "nf.degree"}[]
:::

:::definition "character.dirichlet.field_cut_out" (lean := "IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar, IsCyclotomicExtension.Rat.galEquivZMod, IntermediateField.fixedField, IsCyclotomicExtension.Rat.card_intermediateFieldEquivSubgroupChar")
*Fixed field of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.field_cut_out))

Let $`\chi:\mathbb{Z}\to \mathbb{C}` be a {bpref "character.dirichlet"}[Dirichlet character with modulus $`q`]. The *fixed field* of $`\chi` is $`\mathbb{Q}(\zeta_q)^{\ker(\chi)}`. By definition, this is the subfield of elements fixed
under Galois morphisms $`\zeta_q\mapsto \zeta_q^k` for all $`k` such that $`\chi(k)=1`.

In fact $`\chi` determines a homomorphism $`\chi:(\mathbb{Z}/q\mathbb{Z})^\times\to \mathbb{C}^\times`.  Identifying $`(\mathbb{Z}/q\mathbb{Z})^\times` with $`\textrm{Gal}(\mathbb{Q}(\zeta_q)/\mathbb{Q})` by $`a\mapsto \sigma_a` with $`\sigma_a(\zeta_q)=\zeta_q^a`, we then identify $`\ker(\chi)` with a subgroup of $`\textrm{Gal}(\mathbb{Q}(\zeta_q)/\mathbb{Q})`.
By the Galois correspondence, the fixed field $`\mathbb{Q}(\zeta_q)^{\ker(\chi)}` of this subgroup is a subfield of $`\mathbb{Q}(\zeta_q)` whose Galois group is isomorphic to $`\textrm{Im}(\chi)`, which is cyclic of order $`n` where $`n` is the {bpref "character.dirichlet.order"}[order] of $`\chi`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.order"}[]
:::

:::definition "character.dirichlet.gauss_sum" (lean := "gaussSum, ZMod.stdAddChar, AddChar.mulShift")
*Gauss sum.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.gauss_sum))

Let $`\chi` be a {bpref "character.dirichlet"}[Dirichlet character] with modulus $`q`. For $`a \in \mathbb{Z}`, the *Gauss sum* associated to $`\chi` and $`a` is given by

$$`\large \tau_{a}(\chi) = \sum_{r \,\in\, \mathbb{Z}/q\mathbb{Z}} \chi(r)\, e^{2\pi iar/q}.`

The Gauss sum $`\tau_1(\chi)` is often called "the Gauss sum" of $`\chi`.

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "character.dirichlet.group" (lean := "MulChar.commGroup, MulChar.coeToFun_mul, DirichletCharacter.mulEquiv_units")
*Dirichlet character group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.group))

The {bpref "character.dirichlet"}[Dirichlet characters] $`\chi\colon\Z\to\C` of {bpref "character.dirichlet.modulus"}[modulus] $`q` form a group under pointwise multiplication.

In the {bpref "character.dirichlet.conrey"}[Conrey labeling system] we simply have $`\chi_q(n_1,\cdot)\chi_q(n_2,\cdot) = \chi_q(n_1n_2,\cdot)`.

This group is (non-canonically) isomorphic to the multiplicative group $`(\Z/q\Z)^\times`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.group.generators"
*Generators of a Dirichlet character group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.group.generators))

A set of *generators* of the {bpref "character.dirichlet.group"}[Dirichlet character group] $`G` of {bpref "character.dirichlet.modulus"}[modulus] $`q` is a set of {bpref "character.dirichlet"}[Dirichlet characters] $`\chi_q(n_i,\cdot)` that generate $`G` under multiplication.  These may be chosen so that $`G` is the direct product of the cyclic groups generated by each of the $`\chi_q(n_i,\cdot)`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.group.order" (lean := "DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, DirichletCharacter.mulEquiv_units")
*Order of a Dirichlet character group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.group.order))

The set of {bpref "character.dirichlet"}[Dirichlet characters] $`\chi\colon\Z\to\C` of {bpref "character.dirichlet.modulus"}[modulus] $`q` form a {bpref "character.dirichlet.group"}[group] isomorphic (though not canonically) to $`(\Z/q\Z)^\times`, which has *order* $`\varphi(q)`, where $`\varphi` is the Euler function.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.group.structure" (lean := "DirichletCharacter.groupStructure, DirichletCharacter.groupStructure_eq_iff, DirichletCharacter.groupStructure_eq, AddCommGroup.smithAbelianInvariants")
*Structure of a Dirichlet group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.group.structure))

The *structure* of a {bpref "character.dirichlet.group"}[Dirichlet character group] of Dirichlet characters of {bpref "character.dirichlet.modulus"}[modulus] $`q` refers to its isomorphism type as a finite abelian group, which can be uniquely expressed as a product of cyclic groups $`C_{n_1}\times C_{n_2}\cdots\times C_{n_r}` with $`n_1|n_2|\cdots |n_r`.  This is the same as the structure of the group $`(\Z/q\Z)^\times`.

Depends on: {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.jacobi_sum" (lean := "jacobiSum")
*Jacobi sum.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.jacobi_sum))

Given two {bpref "character.dirichlet"}[Dirichlet characters] $`\chi` and $`\psi` modulo $`q`, the *Jacobi sum* associated to these characters is given by
$$`J(\chi,\psi) = \sum_{r \,\in\, \mathbb{Z}/q\mathbb{Z}} \chi(r)\, \psi(1-r).`

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "character.dirichlet.jacobi_symbol" (lean := "jacobiSym, jacobiSym.quadratic_reciprocity, jacobiSym.at_neg_one, jacobiSym.at_two")
*Jacobi symbol.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.jacobi_symbol))

The *Jacobi symbol* $`\displaystyle\left(\frac{a}{b}\right)` is an extension of the {bpref "character.dirichlet.legendre_symbol"}[Legendre symbol] to all positive odd integers $`b` as follows.

We set
$`\displaystyle\left(\frac{a}{1}\right) =1` for all $`a.`

If $`b>1,` then it has a decomposition into distinct \*odd\* primes of the form $`b = p_1^{e_1} p_2^{e_2}\cdots p_r^{e_r}` and the Jacobi symbol is defined as the product of Legendre symbols

$$`\displaystyle\left(\frac{a}{b}\right) = \left(\frac{a}{p_1}\right)^{e_1} \left(\frac{a}{p_2}\right)^{e_2}\cdots \left(\frac{a}{p_r}\right)^{e_r}.`

The Jacobi symbol is multiplicative in the sense that $`\displaystyle\left(\frac{a_1 a_2}{b}\right) = \displaystyle\left(\frac{a_1}{b}\right)\displaystyle\left(\frac{a_2}{b}\right)` and  $`\displaystyle\left(\frac{a}{b_1b_2}\right) = \displaystyle\left(\frac{a}{b_1}\right)\displaystyle\left(\frac{a}{b_2}\right)` for all integers $`a, a_1, a_2` and all positive odd integers $`b, b_1, b_2.`

It has the same special formulas for $`a=-1` and $`a = 2` as the Legendre symbol, namely

$`\left(\displaystyle \frac{-1}{b}\right)= (-1)^{\frac{b-1}{2}} =  \left\{ \begin{array}{cl} 1 & \text{if } b \equiv 1 \bmod 4 \\ -1 & \text{if } b \equiv -1 \bmod 4 \end{array} \right.`  and $`\left(\displaystyle \frac{2}{b}\right) = (-1)^{\frac{b^2-1}{8}}=\left\{ \begin{array}{cl} 1 & \text{if } b \equiv \pm1 \bmod 8 \\ -1 & \text{if } b \equiv \pm3 \bmod 8 \end{array} \right.`.

The *law of quadratic reciprocity states* that for $`m,n` odd positive coprime integers we have

$$`\left(\displaystyle\frac{n}{m}\right) = (-1)^{\frac{m-1}2 \frac{n-1}2} \left(\displaystyle \frac{m}{n}\right).`

Depends on: {uses "character.dirichlet.legendre_symbol"}[]
:::

:::definition "character.dirichlet.kloosterman_sum" (lean := "kloostermanSum, DirichletCharacter.kloostermanSum_stdAddChar, kloostermanSum_zero_right, ZMod.stdAddChar, gaussSum")
*Kloosterman sum.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.kloosterman_sum))

Let $`\chi` be a {bpref "character.dirichlet"}[Dirichlet character] with modulus $`q`. The *Kloosterman sum* $`K(a,b,\chi)` is defined by

$$`K(a,b,\chi) = \sum_{r \in (\mathbb{Z}/q\mathbb{Z})^\times} \chi(r)\zeta^{ar+br^{-1}},`

where $`\zeta = e^{2\pi i/q}`. This reduces to the {bpref "character.dirichlet.gauss_sum"}[Gauss sum] if $`b=0`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.gauss_sum"}[]
:::

:::definition "character.dirichlet.kronecker_symbol"
*Kronecker symbol.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.kronecker_symbol))

The *Kronecker symbol* $`\displaystyle\left(\frac{a}{n}\right)` is the multiplicative extension of the {bpref "character.dirichlet.jacobi_symbol"}[Jacobi symbol] $`\displaystyle\left(\frac{a}{m}\right)`, which is defined on all positive odd integers $`m`, to all integers $`n\in\mathbb{Z}` as follows.

We set

$$`\displaystyle\left(\frac{a}{-1}\right) = \left\{ \begin{array}{cl} 1 & \text{if }  a\geq 0\\
-1 & \text{if } a < 0; \end{array} \right.`

$$`\displaystyle\left(\frac{a}{2}\right) = \left\{ \begin{array}{cl} 0 & \text{if }  a\equiv 0 \bmod 2\\
 1 & \text{if }  a\equiv \pm 1 \bmod 8\\
-1 & \text{if } a \equiv \pm 3 \bmod 8; \end{array} \right.`

and

$$`\displaystyle\left(\frac{a}{0}\right) = \left\{ \begin{array}{cl} 1 & \text{if }  a= \pm 1\\
0 & \text{otherwise }. \end{array} \right.`

Then for each nonzero integer $`n = \sgn(n) p_1^{e_1} p_2^{e_2} \cdots p_r^{e_r}` the Kronecker symbol is defined as the product of  symbols above and the {bpref "character.dirichlet.legendre_symbol"}[Legendre symbols] for odd primes

$$`\displaystyle\left(\frac{a}{n}\right) = \displaystyle\left(\frac{a}{\sgn(n)}\right) \displaystyle\left(\frac{a}{p_1}\right)^{e_1} \displaystyle\left(\frac{a}{p_2}\right)^{e_2}\cdots \displaystyle\left(\frac{a}{p_r}\right)^{e_r}.`

A Dirichlet character can be written as a Kronecker symbol $`\displaystyle\left(\frac{a}{\cdot}\right)` if and only if it is
{bpref "character.dirichlet.real"}[real].

Depends on: {uses "character.dirichlet.jacobi_symbol"}[] {uses "character.dirichlet.legendre_symbol"}[] {uses "character.dirichlet.real"}[]
:::

:::definition "character.dirichlet.legendre_symbol" (lean := "legendreSym, quadraticChar, legendreSym.quadratic_reciprocity, legendreSym.at_neg_one, legendreSym.at_two")
*Legendre symbol.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.legendre_symbol))

Let $`x` be an integer and $`p` be an odd prime. The *Legendre symbol* $`\displaystyle\left(\frac{x}{p}\right)` is defined to be

$$`\left( \frac{x}{p} \right) = \left\{ \begin{array}{cl} 0 & \text{if } p \mid x, \\ 1 & \text{if } x \bmod p \text{ is a non-zero square in } \Z/p\Z, \\ -1 & \text{if } x \bmod p \text{ is not a square in } \Z/p\Z. \end{array} \right.`

It can be computed efficiently by using the following formulae inductively:

- (Multiplicativity) $`\left(\frac{ab}{p}\right) = \left(\frac{a}{p}\right) \left(\frac{b}{p}\right)`.

- (Special cases) $`\left(\frac{-1}{p}\right)= \left\{ \begin{array}{cl} 1 & \text{if } p \equiv 1 \bmod 4 \\ -1 & \text{if } p \equiv -1 \bmod 4 \end{array} \right.`  and $`\left(\frac{2}{p}\right)=\left\{ \begin{array}{cl} 1 & \text{if } p \equiv \pm1 \bmod 8 \\ -1 & \text{if } p \equiv \pm3 \bmod 8 \end{array} \right.`.

- (Quadratic reciprocity) If $`p` and $`q` are distinct odd primes, then $`\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}2 \frac{q-1}2} \left(\frac{p}{q}\right)`.

In particular, for a fixed odd prime $`p`, $`x \mapsto \left(\frac{x}{p}\right)` is a {bpref "character.dirichlet"}[Dirichlet character] modulo $`p`.

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "character.dirichlet.parity" (lean := "DirichletCharacter.Even, DirichletCharacter.Odd, DirichletCharacter.even_or_odd")
*Parity of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.parity))

A character has odd/even *parity* if it is odd/even as a function. A {bpref "character.dirichlet"}[Dirichlet character] $`\chi\colon\Z\to\C` is odd if $`\chi(-1) = -1` and even if $`\chi(-1)=1.`

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "character.dirichlet.real" (lean := "MulChar.IsQuadratic, Complex.conj_eq_iff_real")
*Real Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.real))

A character is *real* if its image is contained in $`\mathbb{R}.`
:::

:::definition "character.dirichlet.related_fields" (lean := "TauCeti.CharacterField, IntermediateField.fixedField, IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar, IntermediateField.adjoin")
*Number fields related to a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.related_fields))

There are two number fields naturally associated to a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of {bpref "character.dirichlet.modulus"}[modulus] $`q`:

- the {bpref "character.dirichlet.value_field"}[field of values]: $`\Q(\chi(1),\ldots,\chi(q-1))`;

- the {bpref "character.dirichlet.field_cut_out"}[fixed field]: $`\mathbb{Q}(\zeta_q)^{\ker(\chi)}`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.field_cut_out"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.value_field"}[]
:::

:::definition "character.hecke"
*Hecke character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.hecke))

Let $`K` be a {bpref "nf"}[number field] with {bpref "nf.ring_of_integers"}[ring of integers] $`\Z_K` and let $`\mathfrak{m}` be an integral {bpref "ring.ideal"}[ideal] of $`\Z_K`. Let $`I(\mathfrak{m})` be the group of {bpref "ring.fractional_ideal"}[fractional ideals] of $`\Z_K` coprime to $`\mathfrak{m}`. A *Hecke character* modulo $`\mathfrak{m}` is a group homomorphism $`\chi:I(\mathfrak{m})\to\mathbb{C}^\times` with the property there exists another group homomorphism $`\chi_{\infty}:K^\times/\mathbb{Q}^\times\to\mathbb{C}^\times` such that

$$`\chi(\alpha\mathbb{Z}_K)=\chi_{\infty}(\alpha) \text{ for all }\alpha\in
K^\times\text{ such that }\alpha\equiv1 \mod ^*\mathfrak{m},`

where by $`\alpha\equiv1\mod^*{\mathfrak{m}}` we mean that $`v_{\mathfrak{p}}((\alpha-1))\geq v_{\mathfrak{p}}(\mathfrak{m})` for all prime ideals $`\mathfrak{p}\mid\mathfrak{m}`.

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[] {uses "ring.fractional_ideal"}[] {uses "ring.ideal"}[]
:::

:::definition "character.unit_group" (lean := "Units, ZMod, MulChar.equivToUnitHom")
*Underlying unit group for a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.unit_group))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi: \Z\to \C` has a {bpref "character.dirichlet.modulus"}[modulus] $`n` such that $`\chi` is induced from a function $`\chi:\Z/n\Z\to \C`.  It gives a homomorphism $`(\Z/n\Z)^\times\to \C^\times`.  The *underlying unit group* is $`(\Z/n\Z)^\times`, the group of units of the ring $`\Z/n\Z`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::
