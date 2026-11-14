import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dirichlet characters" =>

This section lists the LMFDB definitions in the category `character`. Each definition links back to its LMFDB knowl. It also lists the knowl about the LMFDB's data on this subject that has mathematical content, from the category `portrait`.

:::definition "character.dirichlet" (lean := "DirichletCharacter, MulChar, DirichletCharacter.apply_eq_zero_iff, MulChar.apply_mem_rootsOfUnity")
*Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet))

A *Dirichlet character* is a function $`\chi: \Z\to \C` together with a positive integer $`q` called the *modulus* such that $`\chi` is completely multiplicative, i.e. $`\chi(mn)=\chi(m)\chi(n)` for all integers $`m` and $`n`, and $`\chi` is periodic modulo $`q`, i.e. $`\chi(n+q)=\chi(n)` for all $`n`. If $`(n,q)>1` then $`\chi(n)=0`, whereas if $`(n,q)=1`, then $`\chi(n)` is a root of unity. The character $`\chi` is {bpref "character.dirichlet.primitive"}[primitive] if its
{bpref "character.dirichlet.conductor"}[conductor]
is equal to its modulus.

Tau Ceti Review: [`DirichletCharacter`](https://taucetiproject.org/review/#/d/DirichletCharacter), [`MulChar`](https://taucetiproject.org/review/#/d/MulChar), [`DirichletCharacter.apply_eq_zero_iff`](https://taucetiproject.org/review/#/d/DirichletCharacter.apply_eq_zero_iff).
:::

:::definition "character.dirichlet.conductor" (lean := "DirichletCharacter.conductor")
*Conductor of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.conductor))

The *conductor* of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` modulo $`q` is the least positive integer $`q_1` dividing $`q` for which $`\chi(n+kq_1)=\chi(n)` for all $`n` and $`n+kq_1` coprime to $`q`.

Tau Ceti Review: [`DirichletCharacter.conductor`](https://taucetiproject.org/review/#/d/DirichletCharacter.conductor).

Depends on: {uses "character.dirichlet"}[]
:::

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

:::definition "character.dirichlet.conrey.orbit_label" (lean := "DirichletCharacter.galoisOrbitLabel, DirichletCharacter.orbitLabelVector, DirichletCharacter.letterCode, DirichletCharacter.galoisOrbitLabel_eq, DirichletCharacter.galoisOrbitIndex_eq_ncard_orbitLabelVector, DirichletCharacter.orbitLabelVector_lt_orbitLabelVector_iff, DirichletCharacter.orbitLabelVector_eq_iff, DirichletCharacter.valueTrace_one, DirichletCharacter.galoisOrbitIndex, DirichletCharacter.galoisOrbitTraceVector")
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

:::definition "character.dirichlet.degree" (lean := "MulChar.degree, MulChar.degree_eq_totient, Nat.totient, ZMod.card_units_eq_totient")
*Degree of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.degree))

The *degree* of a Dirichlet character $`\chi` is the {bpref "nf.degree"}[degree] of its {bpref "character.dirichlet.value_field"}[field of values] $`\Q(\chi(\Z))`.

If $`\chi` has {bpref "character.dirichlet.order"}[order] $`n` then its degree is $`\phi(n):=\#(\Z/n\Z)^\times`.

Tau Ceti Review: [`Nat.totient`](https://taucetiproject.org/review/#/d/Nat.totient), [`ZMod.card_units_eq_totient`](https://taucetiproject.org/review/#/d/ZMod.card_units_eq_totient).

Depends on: {uses "character.dirichlet.order"}[] {uses "character.dirichlet.value_field"}[] {uses "nf.degree"}[]
:::

:::definition "character.dirichlet.field_cut_out" (lean := "DirichletCharacter.fixedField, DirichletCharacter.mem_fixedField_iff, IsCyclotomicExtension.Rat.galEquivZMod, DirichletCharacter.galEquivRange, MulChar.isCyclic_range_toUnitHom, MulChar.card_range_toUnitHom")
*Fixed field of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.field_cut_out))

Let $`\chi:\mathbb{Z}\to \mathbb{C}` be a {bpref "character.dirichlet"}[Dirichlet character with modulus $`q`]. The *fixed field* of $`\chi` is $`\mathbb{Q}(\zeta_q)^{\ker(\chi)}`. By definition, this is the subfield of elements fixed
under Galois morphisms $`\zeta_q\mapsto \zeta_q^k` for all $`k` such that $`\chi(k)=1`.

In fact $`\chi` determines a homomorphism $`\chi:(\mathbb{Z}/q\mathbb{Z})^\times\to \mathbb{C}^\times`.  Identifying $`(\mathbb{Z}/q\mathbb{Z})^\times` with $`\textrm{Gal}(\mathbb{Q}(\zeta_q)/\mathbb{Q})` by $`a\mapsto \sigma_a` with $`\sigma_a(\zeta_q)=\zeta_q^a`, we then identify $`\ker(\chi)` with a subgroup of $`\textrm{Gal}(\mathbb{Q}(\zeta_q)/\mathbb{Q})`.
By the Galois correspondence, the fixed field $`\mathbb{Q}(\zeta_q)^{\ker(\chi)}` of this subgroup is a subfield of $`\mathbb{Q}(\zeta_q)` whose Galois group is isomorphic to $`\textrm{Im}(\chi)`, which is cyclic of order $`n` where $`n` is the {bpref "character.dirichlet.order"}[order] of $`\chi`.

Tau Ceti Review: [`IsCyclotomicExtension.Rat.galEquivZMod`](https://taucetiproject.org/review/#/d/IsCyclotomicExtension.Rat.galEquivZMod).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.order"}[]
:::

:::definition "character.dirichlet.galois_orbit" (lean := "MulChar.galoisOrbit, MulChar.galoisConj, MulChar.image_val_orbit, MulChar.faithfulSMul_galois, MulChar.adjoin_range_eq_adjoin_nth_roots, IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots")
*Galois orbit of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.galois_orbit))

The *Galois orbit* of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of {bpref "character.dirichlet.modulus"}[modulus] $`q` and {bpref "character.dirichlet.order"}[order] $`n` is the set $`[\chi]:=\{\sigma(\chi): \sigma\in \Gal(\Q(\zeta_n)/\Q)\}`, where $`\sigma(\chi)` denotes the Dirichlet character of modulus $`q` defined by  $`k \mapsto \sigma(\chi(k))`.  The map $`\chi\to \sigma(\chi)` defines a faithful action of the {bpref "nf.galois_group"}[Galois group] $`\Gal(\Q(\zeta_n)/\Q)` on the set of Dirichlet characters of modulus $`q` and order $`n`, each of which has $`\Q(\zeta_n)` as its {bpref "character.dirichlet.value_field"}[field of values].

Tau Ceti Review: [`MulChar.galoisOrbit`](https://taucetiproject.org/review/#/d/MulChar.galoisOrbit), [`IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots`](https://taucetiproject.org/review/#/d/IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.value_field"}[] {uses "nf.galois_group"}[]
:::

:::definition "character.dirichlet.galois_orbit_index" (lean := "DirichletCharacter.galoisOrbitIndex, DirichletCharacter.intTraceVector, DirichletCharacter.galoisOrbitTraceVector, DirichletCharacter.intCast_num_valueTrace, DirichletCharacter.length_intTraceVector, DirichletCharacter.intTraceVector_eq_iff, DirichletCharacter.galoisOrbitIndex_eq_ncard_intTraceVector, DirichletCharacter.galoisOrbitIndex_one, DirichletCharacter.galoisOrbitIndex_eq_iff, DirichletCharacter.galoisOrbitTraceVector_eq_iff")
*Orbit index of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.galois_orbit_index))

The {bpref "character.dirichlet.galois_orbit"}[Galois orbits] of {bpref "character.dirichlet"}[Dirichlet characters] of {bpref "character.dirichlet.modulus"}[modulus] $`q` are ordered as follows.
Let $`\chi` be any character in the Galois orbit $`[\chi]` and define the $`N`-tuple of integers

$$`t([\chi]) := (n,t_1,t_2,\ldots,t_{q-1}) \in \Z^q,`

where $`n` is the {bpref "character.dirichlet.order"}[order] of $`\chi` and $`t_i:=\mathrm{tr}_{\Q(\chi)/\Q}(\chi(i))` is the trace of $`\chi(i)` from the {bpref "character.dirichlet.value_field"}[field of values] of $`\chi` to $`\Q`.  The $`q`-tuple $`t([\chi])` is independent of the choice of representative $`\chi` and uniquely identifies the Galois orbit $`[\chi]`.

The *orbit index* of $`\chi` is the index of $`t([\chi])` in the lexicographic ordering of all such tuples arising for Dirichlet characters of modulus $`q`; indexing begins at $`1`, which is always the index of the Galois orbit of the {bpref "character.dirichlet.principal"}[principal character] of modulus $`1`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.principal"}[] {uses "character.dirichlet.value_field"}[]
:::

:::definition "character.dirichlet.galois_orbit_label" (lean := "DirichletCharacter.galoisOrbitLabel, DirichletCharacter.letterCode, DirichletCharacter.letterCode_zero, DirichletCharacter.letterCode_one, DirichletCharacter.letterCode_twentySix")
*Label of a Galois orbit of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.galois_orbit_label))

The *label* of a {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of modulus $`N` takes the form $`N.a`, where $`a` is a letter or string of letters representing the {bpref "character.dirichlet.galois_orbit_index"}[index] of the Galois orbit.
 The index $`1` is written as $`a`, the index  $`2` is written as $`b`, the index $`27` is written as $`ba`, and so on.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_index"}[]
:::

:::definition "character.dirichlet.gauss_sum" (lean := "gaussSum, ZMod.stdAddChar, AddChar.mulShift")
*Gauss sum.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.gauss_sum))

Let $`\chi` be a {bpref "character.dirichlet"}[Dirichlet character] with modulus $`q`. For $`a \in \mathbb{Z}`, the *Gauss sum* associated to $`\chi` and $`a` is given by

$$`\large \tau_{a}(\chi) = \sum_{r \,\in\, \mathbb{Z}/q\mathbb{Z}} \chi(r)\, e^{2\pi iar/q}.`

The Gauss sum $`\tau_1(\chi)` is often called "the Gauss sum" of $`\chi`.

Tau Ceti Review: [`gaussSum`](https://taucetiproject.org/review/#/d/gaussSum), [`ZMod.stdAddChar`](https://taucetiproject.org/review/#/d/ZMod.stdAddChar), [`AddChar.mulShift`](https://taucetiproject.org/review/#/d/AddChar.mulShift).

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "character.dirichlet.group" (lean := "MulChar.commGroup, MulChar.coeToFun_mul, DirichletCharacter.mulEquiv_units")
*Dirichlet character group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.group))

The {bpref "character.dirichlet"}[Dirichlet characters] $`\chi\colon\Z\to\C` of {bpref "character.dirichlet.modulus"}[modulus] $`q` form a group under pointwise multiplication.

In the {bpref "character.dirichlet.conrey"}[Conrey labeling system] we simply have $`\chi_q(n_1,\cdot)\chi_q(n_2,\cdot) = \chi_q(n_1n_2,\cdot)`.

This group is (non-canonically) isomorphic to the multiplicative group $`(\Z/q\Z)^\times`.

Tau Ceti Review: [`MulChar.commGroup`](https://taucetiproject.org/review/#/d/MulChar.commGroup), [`MulChar.coeToFun_mul`](https://taucetiproject.org/review/#/d/MulChar.coeToFun_mul).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.group.generators" (lean := "Subgroup.closure, Subgroup.zpowers, DirichletCharacter.exists_generators_bijective_prod_zpowers, CommGroup.exists_bijective_prod_zpowers, CommGroup.closure_range_eq_top_of_surjective_prod_zpowers")
*Generators of a Dirichlet character group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.group.generators))

A set of *generators* of the {bpref "character.dirichlet.group"}[Dirichlet character group] $`G` of {bpref "character.dirichlet.modulus"}[modulus] $`q` is a set of {bpref "character.dirichlet"}[Dirichlet characters] $`\chi_q(n_i,\cdot)` that generate $`G` under multiplication.  These may be chosen so that $`G` is the direct product of the cyclic groups generated by each of the $`\chi_q(n_i,\cdot)`.

Tau Ceti Review: [`Subgroup.closure`](https://taucetiproject.org/review/#/d/Subgroup.closure), [`Subgroup.zpowers`](https://taucetiproject.org/review/#/d/Subgroup.zpowers).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.group.order" (lean := "DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, DirichletCharacter.mulEquiv_units")
*Order of a Dirichlet character group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.group.order))

The set of {bpref "character.dirichlet"}[Dirichlet characters] $`\chi\colon\Z\to\C` of {bpref "character.dirichlet.modulus"}[modulus] $`q` form a {bpref "character.dirichlet.group"}[group] isomorphic (though not canonically) to $`(\Z/q\Z)^\times`, which has *order* $`\varphi(q)`, where $`\varphi` is the Euler function.

Tau Ceti Review: [`DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`](https://taucetiproject.org/review/#/d/DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.group.structure" (lean := "DirichletCharacter.groupStructure, DirichletCharacter.groupStructure_eq_iff, DirichletCharacter.groupStructure_eq, AddCommGroup.smithAbelianInvariants")
*Structure of a Dirichlet group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.group.structure))

The *structure* of a {bpref "character.dirichlet.group"}[Dirichlet character group] of Dirichlet characters of {bpref "character.dirichlet.modulus"}[modulus] $`q` refers to its isomorphism type as a finite abelian group, which can be uniquely expressed as a product of cyclic groups $`C_{n_1}\times C_{n_2}\cdots\times C_{n_r}` with $`n_1|n_2|\cdots |n_r`.  This is the same as the structure of the group $`(\Z/q\Z)^\times`.

Depends on: {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.induce" (lean := "DirichletCharacter.changeLevel, DirichletCharacter.IsInducedBy, DirichletCharacter.isInducedBy_iff, DirichletCharacter.isPrimitive_iff_forall_isInducedBy, DirichletCharacter.isPrimitive_and_isInducedBy_iff, DirichletCharacter.primitiveCharacter")
*Induced Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.induce))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi_1` of {bpref "character.dirichlet.modulus"}[modulus] $`q_1` is said to be *induced* by a Dirichlet character $`\chi_2` of modulus $`q_2` dividing $`q_1` if $`\chi_1(m)=\chi_2(m)` for all $`m` coprime to $`q_1`.

A Dirichlet character is {bpref "character.dirichlet.primitive"}[primitive] if it is not induced by any character other than itself; every Dirichlet character is induced by a uniquely determined primitive Dirichlet character.

Tau Ceti Review: [`DirichletCharacter.changeLevel`](https://taucetiproject.org/review/#/d/DirichletCharacter.changeLevel), [`DirichletCharacter.primitiveCharacter`](https://taucetiproject.org/review/#/d/DirichletCharacter.primitiveCharacter).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.jacobi_sum" (lean := "jacobiSum")
*Jacobi sum.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.jacobi_sum))

Given two {bpref "character.dirichlet"}[Dirichlet characters] $`\chi` and $`\psi` modulo $`q`, the *Jacobi sum* associated to these characters is given by
$$`J(\chi,\psi) = \sum_{r \,\in\, \mathbb{Z}/q\mathbb{Z}} \chi(r)\, \psi(1-r).`

Tau Ceti Review: [`jacobiSum`](https://taucetiproject.org/review/#/d/jacobiSum).

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

Tau Ceti Review: [`jacobiSym`](https://taucetiproject.org/review/#/d/jacobiSym), [`jacobiSym.quadratic_reciprocity`](https://taucetiproject.org/review/#/d/jacobiSym.quadratic_reciprocity), [`jacobiSym.at_neg_one`](https://taucetiproject.org/review/#/d/jacobiSym.at_neg_one), [`jacobiSym.at_two`](https://taucetiproject.org/review/#/d/jacobiSym.at_two).

Depends on: {uses "character.dirichlet.legendre_symbol"}[]
:::

:::definition "character.dirichlet.kloosterman_sum" (lean := "kloostermanSum, DirichletCharacter.kloostermanSum_stdAddChar, kloostermanSum_zero_right, ZMod.stdAddChar, gaussSum")
*Kloosterman sum.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.kloosterman_sum))

Let $`\chi` be a {bpref "character.dirichlet"}[Dirichlet character] with modulus $`q`. The *Kloosterman sum* $`K(a,b,\chi)` is defined by

$$`K(a,b,\chi) = \sum_{r \in (\mathbb{Z}/q\mathbb{Z})^\times} \chi(r)\zeta^{ar+br^{-1}},`

where $`\zeta = e^{2\pi i/q}`. This reduces to the {bpref "character.dirichlet.gauss_sum"}[Gauss sum] if $`b=0`.

Tau Ceti Review: [`ZMod.stdAddChar`](https://taucetiproject.org/review/#/d/ZMod.stdAddChar), [`gaussSum`](https://taucetiproject.org/review/#/d/gaussSum).

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

Tau Ceti Review: [`legendreSym`](https://taucetiproject.org/review/#/d/legendreSym), [`quadraticChar`](https://taucetiproject.org/review/#/d/quadraticChar), [`legendreSym.at_neg_one`](https://taucetiproject.org/review/#/d/legendreSym.at_neg_one), [`legendreSym.at_two`](https://taucetiproject.org/review/#/d/legendreSym.at_two).

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "character.dirichlet.minimal" (lean := "DirichletCharacter.IsMinimalOfPrimePowerModulus, DirichletCharacter.IsMinimal, DirichletCharacter.primePowerPart, DirichletCharacter.IsPrimitive.isMinimalOfPrimePowerModulus, DirichletCharacter.not_forall_isPrimitive_of_isMinimalOfPrimePowerModulus, DirichletCharacter.isMinimal_one_iff, DirichletCharacter.isMinimalOfPrimePowerModulus_one_iff, TauCeti.Nat.IsExactDivisor.eq_mul_comp_unitsMap")
*Minimal Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.minimal))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of prime power {bpref "character.dirichlet.modulus"}[modulus] $`N` is *minimal* if the following conditions both hold:

1. The {bpref "character.dirichlet.conductor"}[conductor] of $`\chi` does not lie in the open interval $`(\sqrt{N},N)`, and if $`N` is a square divisible by 16 then $`{\rm cond}(\chi)\in \{\sqrt{N},N\}`.

2. Both the {bpref "character.dirichlet.order"}[order] and conductor of $`\chi` are minimal among the set of all Dirichlet character $`\chi\psi^2` for which $`{\rm cond}(\psi){\rm cond}(\chi\psi) | N`.

This includes all {bpref "character.dirichlet.primitive"}[primitive] Dirichlet characters of prime power modulus, but not every minimal Dirichlet character of prime power modulus is primitive.

For a composite modulus $`N` with prime power factorization $`N=p_1^{e_1}\cdots p_n^{e_n}`, a Dirichlet character $`\chi` of modulus $`N` is *minimal* if and only if every character in its unique factorization into Dirichlet characters of modulus $`p_1^{e_1},\cdots,p_n^{e_n}` is minimal.  The {bpref "character.dirichlet.principal"}[trivial] Dirichlet character is minimal.

Tau Ceti Review: [`TauCeti.Nat.IsExactDivisor.eq_mul_comp_unitsMap`](https://taucetiproject.org/review/#/d/TauCeti.Nat.IsExactDivisor.eq_mul_comp_unitsMap).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.primitive"}[] {uses "character.dirichlet.principal"}[]
:::

:::definition "character.dirichlet.modulus" (lean := "DirichletCharacter, MulChar, DirichletCharacter.apply_eq_zero_iff, MulChar.apply_mem_rootsOfUnity")
*Modulus of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.modulus))

A *Dirichlet character* is a function $`\chi: \mathbb{Z}\to \mathbb{C}` together with a positive integer $`q`, called the *modulus* of the character, such that $`\chi` is completely multiplicative, i.e. $`\chi(mn)=\chi(m)\chi(n)` for all integers $`m` and $`n`, and $`\chi` is periodic modulo $`q`, i.e. $`\chi(n+q)=\chi(n)` for all $`n`. If $`(n,q)>1` then $`\chi(n)=0`, whereas if $`(n,q)=1`, then $`\chi(n)` is a root of unity.

Tau Ceti Review: [`DirichletCharacter`](https://taucetiproject.org/review/#/d/DirichletCharacter), [`MulChar`](https://taucetiproject.org/review/#/d/MulChar), [`DirichletCharacter.apply_eq_zero_iff`](https://taucetiproject.org/review/#/d/DirichletCharacter.apply_eq_zero_iff).
:::

:::definition "character.dirichlet.order" (lean := "orderOf, MulChar.isLeast_orderOf, MulChar.toUnitHom, MulChar.range_toUnitHom_eq_rootsOfUnity, MulChar.card_range_toUnitHom, rootsOfUnity")
*Order of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.order))

The *order* of a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` is the least positive integer $`n` such that $`\chi^n` is the {bpref "character.dirichlet.principal"}[trivial] character of the same {bpref "character.dirichlet.modulus"}[modulus] as $`\chi`. Equivalently, it is the order $`n` of the image of $`\chi` in $`\mathbb{C}^\times`, the group of $`n`th roots of unity.

Tau Ceti Review: [`orderOf`](https://taucetiproject.org/review/#/d/orderOf), [`MulChar.toUnitHom`](https://taucetiproject.org/review/#/d/MulChar.toUnitHom), [`rootsOfUnity`](https://taucetiproject.org/review/#/d/rootsOfUnity).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.principal"}[]
:::

:::definition "character.dirichlet.parity" (lean := "DirichletCharacter.Even, DirichletCharacter.Odd, DirichletCharacter.even_or_odd")
*Parity of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.parity))

A character has odd/even *parity* if it is odd/even as a function. A {bpref "character.dirichlet"}[Dirichlet character] $`\chi\colon\Z\to\C` is odd if $`\chi(-1) = -1` and even if $`\chi(-1)=1.`

Tau Ceti Review: [`DirichletCharacter.Even`](https://taucetiproject.org/review/#/d/DirichletCharacter.Even), [`DirichletCharacter.Odd`](https://taucetiproject.org/review/#/d/DirichletCharacter.Odd), [`DirichletCharacter.even_or_odd`](https://taucetiproject.org/review/#/d/DirichletCharacter.even_or_odd).

Depends on: {uses "character.dirichlet"}[]
:::

:::definition "character.dirichlet.primitive" (lean := "DirichletCharacter.IsPrimitive")
*Primitive Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.primitive))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi` is *primitive* if its
{bpref "character.dirichlet.conductor"}[conductor] is equal to its {bpref "character.dirichlet.modulus"}[modulus]; equivalently, $`\chi` is not {bpref "character.dirichlet.induce"}[induced] by a Dirichlet character of smaller modulus.

Tau Ceti Review: [`DirichletCharacter.IsPrimitive`](https://taucetiproject.org/review/#/d/DirichletCharacter.IsPrimitive).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.principal" (lean := "MulChar.trivial, MulChar.trivial_apply, DirichletCharacter.factorsThrough_one_iff")
*Principal Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.principal))

A {bpref "character.dirichlet"}[Dirichlet character] is *principal* (or *trivial*) if it has {bpref "character.dirichlet.order"}[order] $`1`, equivalently, if it is {bpref "character.dirichlet.induce"}[induced] by the unique Dirichlet character of modulus 1.

The value of the principal Dirichlet character of {bpref "character.dirichlet.modulus"}[modulus] $`q` at an integer $`n` is $`1` if $`n` is coprime to $`q` and $`0` otherwise.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.real" (lean := "MulChar.IsQuadratic, Complex.conj_eq_iff_real")
*Real Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.real))

A character is *real* if its image is contained in $`\mathbb{R}.`

Tau Ceti Review: [`MulChar.IsQuadratic`](https://taucetiproject.org/review/#/d/MulChar.IsQuadratic), [`Complex.conj_eq_iff_real`](https://taucetiproject.org/review/#/d/Complex.conj_eq_iff_real).
:::

:::definition "character.dirichlet.related_fields" (lean := "TauCeti.CharacterField, IntermediateField.fixedField, IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar, IntermediateField.adjoin")
*Number fields related to a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.related_fields))

There are two number fields naturally associated to a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of {bpref "character.dirichlet.modulus"}[modulus] $`q`:

- the {bpref "character.dirichlet.value_field"}[field of values]: $`\Q(\chi(1),\ldots,\chi(q-1))`;

- the {bpref "character.dirichlet.field_cut_out"}[fixed field]: $`\mathbb{Q}(\zeta_q)^{\ker(\chi)}`.

Tau Ceti Review: [`TauCeti.CharacterField`](https://taucetiproject.org/review/#/d/TauCeti.CharacterField), [`IntermediateField.fixedField`](https://taucetiproject.org/review/#/d/IntermediateField.fixedField), [`IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar`](https://taucetiproject.org/review/#/d/IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar), [`IntermediateField.adjoin`](https://taucetiproject.org/review/#/d/IntermediateField.adjoin).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.field_cut_out"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.value_field"}[]
:::

:::definition "character.dirichlet.value_field" (lean := "TauCeti.CharacterField, IntermediateField.adjoin, MulChar.adjoin_range_eq_adjoin_nth_roots")
*Field of values of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.value_field))

The *field of values* of a Dirichlet character $`\chi\colon\Z\to\C` is the field $`\Q(\chi(\Z))` generated by its values; it is equal to the cyclotomic field $`\Q(\zeta_n)`, where $`n` is the {bpref "character.dirichlet.order"}[order] of $`\chi`.

Tau Ceti Review: [`TauCeti.CharacterField`](https://taucetiproject.org/review/#/d/TauCeti.CharacterField), [`IntermediateField.adjoin`](https://taucetiproject.org/review/#/d/IntermediateField.adjoin).

Depends on: {uses "character.dirichlet.order"}[]
:::

:::definition "character.dirichlet.values" (lean := "DirichletCharacter, DirichletCharacter.eq_iff_forall_mem_Icc, MulChar.map_one, DirichletCharacter.apply_modulus, DirichletCharacter.apply_eq_zero_or_exists_rat_apply_eq_exp, DirichletCharacter.exists_rat_apply_eq_exp, MulChar.map_nonunit")
*Values of a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.values))

Complete information about a {bpref "character.dirichlet"}[Dirichlet character] $`\chi\colon \Z\to\C` of {bpref "character.dirichlet.modulus"}[modulus] $`q > 1` is contained in the list of values $`(\chi(1)=1,\ \chi(2),\ \chi(3),\ \dots,\ \chi(q-1),\  \chi(q)=0)`, each of which is a root of unity $`e(r) := \exp({2 \pi i r}`), for some rational number $`r`.

Tau Ceti Review: [`DirichletCharacter`](https://taucetiproject.org/review/#/d/DirichletCharacter), [`MulChar.map_one`](https://taucetiproject.org/review/#/d/MulChar.map_one), [`MulChar.map_nonunit`](https://taucetiproject.org/review/#/d/MulChar.map_nonunit).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.dirichlet.values_on_gens" (lean := "DirichletCharacter, DirichletCharacter.eq_iff_forall_apply_eq_of_closure_eq_top, DirichletCharacter.exists_rat_apply_eq_exp, ZMod.val_mem_Icc_of_isUnit, ZMod.natCast_zmod_val, MulChar.apply_mem_rootsOfUnity")
*Values of a Dirichlet character on generators.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.dirichlet.values_on_gens))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi\colon \Z\to \C` of {bpref "character.dirichlet.modulus"}[modulus] $`q` is determined (via multiplicativity) by the values $`\chi(g_1), \ldots, \chi(g_r)` it takes on any list of generators $`g_1,\ldots,g_r` for the {bpref "character.dirichlet.group.structure"}[group $`(\mathbb{Z}/q\mathbb{Z})^\times`].  The generators $`g_i` can each be specified as integers in the interval $`[1,q-1]`, and the values $`\chi(g_i)` are roots of unity $`e(r):=\exp(2\pi i r)`, where $`r` is a rational number.

Tau Ceti Review: [`DirichletCharacter`](https://taucetiproject.org/review/#/d/DirichletCharacter), [`ZMod.natCast_zmod_val`](https://taucetiproject.org/review/#/d/ZMod.natCast_zmod_val).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.group.structure"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "character.hecke" (lean := "TauCeti.GlobalNumberFields.IsIdealHeckeCharacter, TauCeti.GlobalNumberFields.isIdealHeckeCharacter_iff, TauCeti.GlobalNumberFields.IsIdealHeckeCharacter.heckeCharacter, TauCeti.GlobalNumberFields.IsIdealHeckeCharacter.idealCharacter_comp_heckeCharacter, TauCeti.GlobalNumberFields.HeckeCharacter.isIdealHeckeCharacter_idealCharacter, TauCeti.GlobalNumberFields.HeckeCharacter")
*Hecke character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.hecke))

Let $`K` be a {bpref "nf"}[number field] with {bpref "nf.ring_of_integers"}[ring of integers] $`\Z_K` and let $`\mathfrak{m}` be an integral {bpref "ring.ideal"}[ideal] of $`\Z_K`. Let $`I(\mathfrak{m})` be the group of {bpref "ring.fractional_ideal"}[fractional ideals] of $`\Z_K` coprime to $`\mathfrak{m}`. A *Hecke character* modulo $`\mathfrak{m}` is a group homomorphism $`\chi:I(\mathfrak{m})\to\mathbb{C}^\times` with the property there exists another group homomorphism $`\chi_{\infty}:K^\times/\mathbb{Q}^\times\to\mathbb{C}^\times` such that

$$`\chi(\alpha\mathbb{Z}_K)=\chi_{\infty}(\alpha) \text{ for all }\alpha\in
K^\times\text{ such that }\alpha\equiv1 \mod ^*\mathfrak{m},`

where by $`\alpha\equiv1\mod^*{\mathfrak{m}}` we mean that $`v_{\mathfrak{p}}((\alpha-1))\geq v_{\mathfrak{p}}(\mathfrak{m})` for all prime ideals $`\mathfrak{p}\mid\mathfrak{m}`.

Tau Ceti Review: [`TauCeti.GlobalNumberFields.HeckeCharacter`](https://taucetiproject.org/review/#/d/TauCeti.GlobalNumberFields.HeckeCharacter).

Depends on: {uses "nf"}[] {uses "nf.ring_of_integers"}[] {uses "ring.fractional_ideal"}[] {uses "ring.ideal"}[]
:::

:::definition "character.unit_group" (lean := "Units, ZMod, MulChar.equivToUnitHom")
*Underlying unit group for a Dirichlet character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/character.unit_group))

A {bpref "character.dirichlet"}[Dirichlet character] $`\chi: \Z\to \C` has a {bpref "character.dirichlet.modulus"}[modulus] $`n` such that $`\chi` is induced from a function $`\chi:\Z/n\Z\to \C`.  It gives a homomorphism $`(\Z/n\Z)^\times\to \C^\times`.  The *underlying unit group* is $`(\Z/n\Z)^\times`, the group of units of the ring $`\Z/n\Z`.

Tau Ceti Review: [`Units`](https://taucetiproject.org/review/#/d/Units), [`ZMod`](https://taucetiproject.org/review/#/d/ZMod), [`MulChar.equivToUnitHom`](https://taucetiproject.org/review/#/d/MulChar.equivToUnitHom).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.modulus"}[]
:::

:::definition "portrait.character.dirichlet" (lean := "DirichletCharacter.partialGaussSum, DirichletCharacter.partialGaussSum_modulus_sub_one, DirichletCharacter.partialGaussSum_succ_of_not_coprime, DirichletCharacter.norm_gaussSum_mulShift_of_isPrimitive, DirichletCharacter.isPrimitive_iff_forall_norm_gaussSum_mulShift_eq_sqrt, DirichletCharacter.image_setOf_norm_gaussSum_mulShift_eq_sqrt_of_isPrimitive, DirichletCharacter.partialGaussSum_neg, DirichletCharacter.partialGaussSum_one_zero")
*Pictures for Dirichlet characters.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/portrait.character.dirichlet))

For each {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of {bpref "character.dirichlet.modulus"}[modulus] $`N` and each residue $`a` modulo $`N`, we draw the partial {bpref "character.dirichlet.gauss_sum"}[Gauss sums]

$$`S_a(k) = \sum_{n = 1}^{k} \chi(n) e^{2\pi i a n/N}`

as segments from the origin of the complex plane to $`S_a(k)`. All the segments belonging to a given $`a` share a hue, running through the spectrum from red at $`a = 0` to violet at $`a = N-1`; within one hue the segments for small $`k` are darkened and those for large $`k` are drawn at full brightness, so the eye can follow the partial sums as they accumulate. A large dot marks the last of them, the complete Gauss sum $`\tau_a(\chi) = S_a(N-1)`.

Only the stages $`k` coprime to $`N` are drawn: $`\chi(n) = 0` whenever $`\gcd(n, N) > 1`, so each omitted stage would simply repeat the segment before it.

The grey circle has radius $`\sqrt N`. If $`\chi` is {bpref "character.dirichlet.primitive"}[primitive], then $`|\tau_a(\chi)| = \sqrt N` for every $`a` coprime to $`N`, and $`\tau_a(\chi) = 0` for every other $`a`: the picture of a primitive character is $`\phi(N)` dots on the circle together with a cluster of dots at the origin, and a character is primitive exactly when its coprime dots reach the circle.

Several other properties of $`\chi` can be read off the picture.

- Since $`\tau_a(\chi) = \overline{\chi(a)}\,\tau_1(\chi)` for primitive $`\chi` and $`a` coprime to $`N`, the dots on the circle are the vertices of a regular $`n`-gon, where $`n` is the {bpref "character.dirichlet.order"}[order] of $`\chi`.

- $`S_{N-a}(k) = \overline{S_a(k)}` when $`\chi` is real, so the picture of a real character is symmetric about the real axis.

- The {bpref "character.dirichlet.principal"}[principal character] shows a single long red spike along the positive real axis, of length $`\phi(N)`, since then $`S_0(k)` just counts the units up to $`k`.

The pictures are drawn when the page is requested rather than stored in the database, so they are only shown when there is little work to do: the number of segments is $`N\phi(N)`, and we draw the picture only when that is at most $`25000`. This is why a character of modulus $`300` has a picture while one of modulus $`293` does not.

The design follows [Alex Best's demo](https://alexjbest.github.io/dirich/).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.gauss_sum"}[] {uses "character.dirichlet.modulus"}[] {uses "character.dirichlet.order"}[] {uses "character.dirichlet.primitive"}[] {uses "character.dirichlet.principal"}[]
:::
