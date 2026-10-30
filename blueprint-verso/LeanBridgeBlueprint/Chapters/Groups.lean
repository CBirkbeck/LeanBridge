import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Groups" =>

This chapter lists the LMFDB definitions relating to *groups*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "commensurable.group" (lean := "Subgroup.Commensurable, Subgroup.IsFiniteRelIndex")
*commensurable group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/commensurable.group))

Two groups $`G` and $`H` are commensurable if their intersection $`G \cap H` has finite index in $`G` and in $`H`.
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

:::definition "group.a_group" (lean := "IsAGroup, IsZGroup.isAGroup")
*A-group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.a_group))

An *A-group* is a group all of whose Sylow subgroups are {bpref "group.abelian"}[abelian].

Every {bpref "group.z_group"}[Z-group] is an A-group, but the converse does not hold, as shown by [these examples](https://beta.lmfdb.org/Groups/Abstract/?Agroup=yes&Zgroup=no).  Every {bpref "group.solvable"}[solvable] A-group is {bpref "group.monomial"}[monomial].

Depends on: {uses "group.abelian"}[] {uses "group.monomial"}[] {uses "group.solvable"}[] {uses "group.z_group"}[]
:::

:::definition "group.abelian_invariants" (lean := "AddCommGroup.smithAbelianInvariants, AddCommGroup.smithAbelianInvariants_eq_iff, AddCommGroup.primaryAbelianInvariants, AddCommGroup.primaryAbelianInvariants_eq_iff, CommGroup.smithAbelianInvariants_additive_eq_iff")
*Abelian invariants.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.abelian_invariants))

There are two canonical forms for an abelian group $`A`:

1. The *Smith abelian invariants* of $`A` are the unique sequence of integers $`[m_1, \dots, m_k]`, all larger than $`1`, so that $`A \cong C_{m_1} \times \dots \times C_{m_k}`, $`m_i \mid m_{i+1}` for all $`i`.
2. The *primary abelian invariants* of $`A` are the unique sequence of integers $`[q_1, \dots, q_k]`, all larger than $`1`, so that $`A \cong C_{q_1} \times \dots \times C_{q_k}`, each $`q_i = p_i^{e_i}` for a prime $`p_i` and the $`q_i` are sorted first by $`p_i` and then in increasing order for fixed $`p_i`.
:::

:::definition "group.abelianization" (lean := "Abelianization, Abelianization.lift")
*Abelianization.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.abelianization))

The *abelianization* of a group $`G` is $`G/G'`, the quotient by its {bpref "group.commutator_subgroup"}[commutator subgroup]. The abelianization of $`G` is the largest {bpref "group.abelian"}[abelian] {bpref "group.quotient"}[quotient] of $`G` in the sense that any homomorphism $`G\to A` where $`A` is an abelian group factors as a composition of homomorphisms $`G\to G/G'\to A`.

Depends on: {uses "group.abelian"}[] {uses "group.commutator_subgroup"}[] {uses "group.quotient"}[]
:::

:::definition "group.action" (lean := "MulAction, MulAction.IsPretransitive")
*Group action.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.action))

A (left) *group action* of a {bpref "group"}[group] $`G` on a set $`A` is a function
$`\cdot : G\times A \to A`
such that
<ul>
<li> for all $`a\in A`, $`e\cdot a = a` where $`e` is the {bpref "alg.binary_operation.identity"}[identity] element of $`G`
  <li> for all $`g,h\in G` and all $`a\in A`, $`g\cdot (h\cdot a) = (gh)\cdot a`.
</ul>

The action is *transitive* if for all $`a,b\in A`, there exists $`g\in G` such that $`g\cdot a = b`.

Depends on: {uses "alg.binary_operation.identity"}[] {uses "group"}[]
:::

:::definition "group.affine_general_linear" (lean := "AffineEquiv.group, AffineEquiv.linearHom, AffineEquiv.constVAddHom, GaloisField")
*Affine general linear group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.affine_general_linear))

The {bpref "group.general_linear"}[general linear group] $`\GL(n,q)` acts on the vector space $`\F_q^n` by matrix multiplication. The affine general linear group is the group $`\AGL(n,q) = \F_q^n \rtimes \GL(n,q)`. It is the group of all invertible affine transformations of $`\F_q^n`.

Depends on: {uses "group.general_linear"}[]
:::

:::definition "group.affine_linear_automorphism" (lean := "AffineEquiv.AffineGeneralSemilinearGroup, AffineEquiv.AffineSpecialSemilinearGroup, AffineEquiv.conjAlgEquivHom, AffineEquiv.conjAlgEquiv_apply_eq_mulVec_add, AffineEquiv.conjAlgEquiv_mem_affineSpecialLinearGroup")
*Affine linear group twisted by automorphisms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.affine_linear_automorphism))

The group $`\AGammaL(n,q)` is the semi-direct product of $`\AGL(n,q)`, the {bpref "group.affine_general_linear"}[affine general linear group], with the group $`A` of field automorphisms of $`\F_q/\F_p`.

Similarly, the group $`\ASigmaL(n,q)` is the semi-direct product of $`\ASL(n,q)`, the {bpref "group.affine_special_linear"}[affine special linear group], with $`A`.

Depends on: {uses "group.affine_general_linear"}[] {uses "group.affine_special_linear"}[]
:::

:::definition "group.affine_special_linear" (lean := "AffineEquiv.affineSpecialLinearGroup, AffineEquiv.mem_affineSpecialLinearGroup_iff_det, AffineEquiv.apply_eq_mulVec_add, AffineEquiv.group, AffineEquiv.linearHom")
*Affine special linear group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.affine_special_linear))

The affine special linear group $`\ASL(n,q)` is the subgroup of the {bpref "group.affine_general_linear"}[affine general linear group] $`\AGL(n,q) = \F_q^n \rtimes \GL(n,q)` of all affine transformations $`x \mapsto Mx + v` such that $`\det(M)=1`. It is the affine analogue of the {bpref "group.special_linear"}[special linear group].

Depends on: {uses "group.affine_general_linear"}[] {uses "group.special_linear"}[]
:::

:::definition "group.affine_symplectic" (lean := "AffineEquiv.affineSymplecticGroup, AffineEquiv.mem_affineSymplecticGroup_iff, AffineEquiv.linearMatrixHom, Matrix.symplecticGroup, TauCeti.GLSymplectic")
*Affine symplectic group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.affine_symplectic))

The affine symplectic group $`\ASp(n,q)` is the subgroup of the {bpref "group.affine_general_linear"}[affine general linear group] $`\AGL(n,q) = \F_q^n \rtimes \GL(n,q)` of all affine transformations $`x \mapsto Mx + v` such that $`M` is an element of the {bpref "group.symplectic"}[symplectic group] $`\Sp(n,q)`.

Depends on: {uses "group.affine_general_linear"}[] {uses "group.symplectic"}[]
:::

:::definition "group.almost_simple" (lean := "IsAlmostSimple, IsSimpleGroup.isAlmostSimple")
*Almost simple group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.almost_simple))

An *almost simple group* is a group $`G` that lies between a non-abelian {bpref "group.simple"}[simple] group $`S` and its {bpref "group.automorphism"}[automorphism] group Aut$`(S)`, i.e. $`S \subseteq G \subseteq`Aut$`(S).`

Every non-abelian simple group is almost simple, but it is not implied by $`G` being {bpref "group.quasisimple"}[quasisimple], as shown by [these examples](https://beta.lmfdb.org/Groups/Abstract/?almost_simple=yes&quasisimple=no).

Depends on: {uses "group.automorphism"}[] {uses "group.simple"}[]
:::

:::definition "group.alternating" (lean := "alternatingGroup")
*Alternating group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.alternating))

The *alternating group*, denoted $`A_n` is the {bpref "group.subgroup"}[subgroup] of the {bpref "group.symmetric"}[symmetric group]  consisting of the \*even\* permutations. For $`n\ge2` it is of {bpref "group.order"}[order] $`\frac{n!}{2}`, and is {bpref "group.subgroup.index"}[index] $`2` in $`S_n`. The group is {bpref "group.solvable"}[solvable] for $`n\leq 4` and {bpref "group.simple"}[simple] for $`n\geq 5`.

Depends on: {uses "group.order"}[] {uses "group.simple"}[] {uses "group.solvable"}[] {uses "group.subgroup"}[] {uses "group.subgroup.index"}[] {uses "group.symmetric"}[]
:::

:::definition "group.ambient" (lean := "Subgroup")
*Ambient group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.ambient))

If $`H \subseteq G` is a {bpref "group.subgroup"}[subgroup], we refer to $`G` as the *ambient group* of $`H`.

Depends on: {uses "group.subgroup"}[]
:::

:::definition "group.aut_phi_ratio" (lean := "Group.autPhiRatio, IsCyclic.autPhiRatio_eq_one, IsCyclic.card_mulAut, MulAut, Nat.totient")
*$`\phi`-ratio.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.aut_phi_ratio))

Given a {bpref "group"}[group] $`G` and its {bpref "group.automorphism"}[automorphism] group $`A`, the $`\phi`-ratio is the size of the automorphism group divided by $`\phi(G)` where $`\phi` represents Euler's totient function, that is
$$`|A|/\phi(G).`

For {bpref "group.cyclic"}[cyclic] groups, the size of their automorphism group is always $`\phi(G)` and hence this ratio is $`1`.

Depends on: {uses "group"}[] {uses "group.automorphism"}[] {uses "group.cyclic"}[]
:::

:::definition "group.autjugacy_class" (lean := "MulAction.orbit, MulAut, MulAut.applyMulAction")
*Autjugacy class.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.autjugacy_class))

If $`G` is a group and $`x \in G`, the *autjugacy class* of $`x` is the orbit of $`x` under the action of the {bpref "group.automorphism"}[automorphism group], namely $`\{\varphi(x) : \varphi \in \operatorname{Aut}(G)\}`.  Any autjugacy class is a disjoint union of {bpref "group.conjugacy_class"}[conjugacy classes], each of the same size and {bpref "group.element_order"}[order].

Depends on: {uses "group.automorphism"}[] {uses "group.conjugacy_class"}[] {uses "group.element_order"}[]
:::

:::definition "group.autjugate_subgroup" (lean := "Subgroup.pointwiseMulAction, MulAut.applyMulDistribMulAction, MulAction.orbit")
*Autjugate subgroups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.autjugate_subgroup))

In analogy with conjugate subgroups, we say that two {bpref "group.subgroup"}[subgroups] $`H_1` and $`H_2` of a {bpref "group"}[group] $`G` are *autjugate* if there is an {bpref "group.automorphism"}[automorphism] $`\phi` of $`G` so that $`\phi(H_1) = \phi(H_2)`.

Depends on: {uses "group"}[] {uses "group.automorphism"}[] {uses "group.subgroup"}[]
:::

:::definition "group.center" (lean := "Subgroup.center, Subgroup.mem_center_iff")
*Center of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.center))

If $`G` is a {bpref "group"}[group], the *center* of $`G` is the set

$$`Z(G) = \{g\in G\mid gh=hg \text{ for all } h\in G\}.`

It is a {bpref "group.subgroup.normal"}[normal subgroup] of $`G`.

Depends on: {uses "group"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.central" (lean := "Subgroup.center, Subgroup.centralizer_eq_top_iff_subset")
*Central subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.central))

A subset, or {bpref "group.subgroup"}[subgroup], $`H` of a {bpref "group"}[group] $`G` is *central* if
$`gh=hg` for all $`g\in G` and all $`h\in H`.  Equivalently, it is central if and only if it is a subset of the {bpref "group.center"}[center] of the group.

Depends on: {uses "group"}[] {uses "group.center"}[] {uses "group.subgroup"}[]
:::

:::definition "group.central_quotient" (lean := "Subgroup.center, QuotientGroup.Quotient.group, MulAut.conj, MulAut.ker_conj, QuotientGroup.quotientKerEquivRange")
*Central quotient.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.central_quotient))

The central quotient of a {bpref "group"}[group] $`G` is $`G/Z(G)`, where $`Z(G)` is the {bpref "group.center"}[center] of $`G`. The central quotient is isomorphic to the group of {bpref "group.inner_automorphism"}[inner automorphisms] of $`G`.

Depends on: {uses "group"}[] {uses "group.center"}[] {uses "group.inner_automorphism"}[]
:::

:::definition "group.centralizer" (lean := "Subgroup.centralizer, Subgroup.mem_centralizer_iff")
*Centralizer of a subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.centralizer))

If $`G` is a {bpref "group"}[group] and $`H` is a subgroup of $`G`, then the *centralizer* of $`H` in $`G` is

$$`C_G(H) = \{g\in G\mid gh=hg \text{ for all } h\in H\}.`

Depends on: {uses "group"}[]
:::

:::definition "group.chevalley"
*Chevalley group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.chevalley))

The *Chevalley groups* are examples of groups of Lie type over finite {bpref "ring.field"}[fields].  They generalise the classical {bpref "group.general_linear"}[linear], {bpref "group.symplectic"}[symplectic], {bpref "group.orthogonal"}[orthogonal], and {bpref "group.unitary"}[unitary] matrix groups. In many cases, these are examples of finite {bpref "group.simple"}[simple] groups.

- $`A(n, q)` is the {bpref "group.special_linear"}[special linear] group $`\SL(n+1, q)`.

- $`B(n, q)` is the {bpref "group.orthogonal"}[orthogonal] group $`\Omega(2n + 1, q)`.

- $`C(n,q)` is the {bpref "group.symplectic"}[symplectic] group  $`\Sp(2n,q)`.

- $`D(n, q)` is the {bpref "group.orthogonal"}[orthogonal] group $`\OmegaPlus(2n,q)`.

Depends on: {uses "group.general_linear"}[] {uses "group.orthogonal"}[] {uses "group.simple"}[] {uses "group.special_linear"}[] {uses "group.symplectic"}[] {uses "group.unitary"}[] {uses "ring.field"}[]
:::

:::definition "group.chief_series"
*Chief series of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.chief_series))

If $`G` is a {bpref "group"}[group], the *chief series* of $`G` is a {bpref "group.normal_series"}[normal series]

$$`\langle e\rangle=N_0 \lhd N_1 \lhd \cdots \lhd N_k=G`

where each $`N_{i+1}/N_i` is a minimal {bpref "group.subgroup.normal"}[normal subgroup] of $`G/N_i`.

The factor groups $`N_{i+1}/N_i` are each isomorphic to a product of some number of copies of a single {bpref "group.simple"}[simple group] (which depends on $`i`).  These simple groups (together with their multiplicities) are the *composition factors* of $`G`.  While there may be many chief series for $`G`, the set of composition factors is a well defined invariant.

Depends on: {uses "group"}[] {uses "group.normal_series"}[] {uses "group.simple"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.commutator_length" (lean := "commutatorLength, exists_list_length_le_commutatorLength, exists_list_commutatorSet_of_mem_commutator")
*Commutator length.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.commutator_length))

The {bpref "group.commutator_subgroup"}[commutator subgroup] is generated by commutators, but it's not necessarily the case that every element is a commutator.  The *commutator length* of $`G` is the minimal integer $`k` so that every element of $`G'` can be written as the product of $`k` commutators.

Depends on: {uses "group.commutator_subgroup"}[]
:::

:::definition "group.commutator_subgroup" (lean := "commutator, commutatorSet, commutatorElement, commutator_eq_closure")
*Commutator subgroup of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.commutator_subgroup))

Given a {bpref "group"}[group] $`G`, the *commutators* of $`G` are the elements $`a^{-1}b^{-1}ab` where $`a,b\in G`.

The {bpref "group.subgroup"}[subgroup] generated by all commutators of $`G` is the *commutator subgroup* or *derived subgroup* of $`G`, and is denoted by $`[G,G]` or $`G'`.

The commutator subgroup is always a {bpref "group.subgroup.normal"}[normal] subgroup, and the quotient group $`G/G'`, called the {bpref "group.abelianization"}[abelianization] of $`G`, is the largest {bpref "group.abelian"}[abelian] {bpref "group.quotient"}[quotient] of $`G` in the sense that any homomorphism $`G\to A` where $`A` is an abelian group factors as a composition of homomorphisms $`G\to G/G'\to A`.

Depends on: {uses "group"}[] {uses "group.abelian"}[] {uses "group.quotient"}[] {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.complete" (lean := "Group.IsComplete, Group.isComplete_iff, Subgroup.isComplement'_centralizer, Group.surjective_conj_of_isComplement', MulAut.conj")
*Complete group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.complete))

A group $`G` is *complete* if one of the following equivalent conditions holds:

- it has trivial center and every automorphism is inner,

- the natural map from $`G` to its inner automorphism group is an isomorphism,

- whenever it is embedded as a normal subgroup of a larger group, it is a direct factor.

For $`n \ne 2, 6`, the symmetric group $`S_n` is complete.
:::

:::definition "group.complex_character_table" (lean := "TauCeti.characterTable, TauCeti.irreducibleCharacters")
*Complex character table of a finite group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.complex_character_table))

The *complex character table* of a finite {bpref "group"}[group] $`G` is a square tabulation of the value of its irreducible {bpref "group.representation.character"}[complex characters], which encodes useful information about the group $`G` in a compact way. Each row of the table is labeled by an irreducible character (given by its  {bpref "group.label_complex_group_char"}[label]) and the entries in the row are the values of that character on some representative of the corresponding conjugacy class of $`G` given by its {bpref "group.label_conjugacy_class"}[label] on the columns.

Depends on: {uses "group"}[] {uses "group.label_complex_group_char"}[] {uses "group.label_conjugacy_class"}[] {uses "group.representation.character"}[]
:::

:::definition "group.conjugacy_class" (lean := "conjugatesOf, ConjClasses, ConjClasses.carrier, IsConj")
*Conjugacy class.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.conjugacy_class))

If $`G` is a {bpref "group"}[group] and $`x\in G`, the *conjugacy class* of $`x` is the set $`\{gxg^{-1}\mid g\in G\}`.  These sets partition $`G`, and the set of conjugacy classes is denoted by $`\mathrm{conj}(G)`.

Since conjugation by fixed $`g\in G` is an {bpref "group.automorphism"}[automorphism] of $`G`, all conjugate elements have the same {bpref "group.element_order"}[order] in the group.

Depends on: {uses "group"}[] {uses "group.automorphism"}[] {uses "group.element_order"}[]
:::

:::definition "group.conjugacy_class.power_classes" (lean := "ConjClasses.pow, ConjClasses.mk_pow")
*Power classes.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.conjugacy_class.power_classes))

If $`G` is a {bpref "group"}[group], $`g\in G` is an element of a {bpref "group.conjugacy_class"}[conjugacy class] $`P`, and $`n` is a positive integer, then $`nP` denotes the conjugacy class of the element $`g^n`.

Depends on: {uses "group"}[] {uses "group.conjugacy_class"}[]
:::

:::definition "group.core" (lean := "Subgroup.normalCore, Subgroup.normalCore_eq_iSup")
*Core of a subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.core))

If $`H` is a {bpref "group.subgroup"}[subgroup] of a {bpref "group"}[group] $`G`, then the *core* of $`H` is

$$`\bigcap_{g\in G} g^{-1} H g .`

It is the largest normal subgroup of $`G` contained in $`H`.

Depends on: {uses "group"}[] {uses "group.subgroup"}[]
:::

:::definition "group.coxeter" (lean := "CoxeterMatrix.coxeterGraph, CoxeterMatrix.IsIrreducible, IsIrreducibleCoxeterGroup, IsCoxeterGroup, CoxeterMatrix.coxeterGraph_adj_iff")
*Coxeter group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.coxeter))

A finite *Coxeter group* is a finite group $`G` which has a group presentation of the form

$$`G = \langle s_1, s_2, \dots, s_n \mid (s_i s_j)^{m_{ij}} = 1 \rangle,`

where $`m_{ii} = 1` for all $`i = 1, \dots, n`, and where $`m_{ij} = m_{ji} \geq 2` for all $`i \not = j`. Examples of Coxeter groups include all Euclidean reflection groups (e.g. the {bpref "group.triangle_group"}[triangle group]).

Given a Coxeter group $`G` with the above group presentation, one can define the *Coxeter graph* of $`G` to be a graph with $`n` vertices, labelled $`1` to $`n`, with an edge between vertex $`i` and vertex $`j` if and only if $`m_{ij} \geq 3`.  If $`m_{ij} \geq 4`, then the edge between $`i` and $`j` is furthermore given a value of $`m_{ij}`.

A finite *irreducible Coxeter group* is a Coxeter group whose Coxeter graph is connected.

All finite irreducible Coxeter groups have been classified - every such group lies in either one of the four families $`W(A_n)`, $`W(B_n)`, $`W(D_n)`, $`I_2(n)`, or is one of the six exceptional groups $`W(E_6)`, $`W(E_7)`, $`W(E_8)`, $`W(F_4)`, $`H_3`, or $`H_4`.

- $`W(A_n)` is isomorphic to the {bpref "group.symmetric"}[symmetric group] $`S_{n+1}` of order $`(n+1)!`.

- $`W(B_n)` is a group of {bpref "group.order"}[order] $`2^n n!`, whose group structure can be written as a {bpref "group.wreath_product"}[wreath product] $`C_2 \wr S_n`.

- $`W(D_n)` is a group of order $`2^{n-1} n!`, whose group structure can be written as $`C_2^{n-1} . S_n`.

- $`I_2(n)` is isomorphic to the {bpref "group.dihedral"}[dihedral group] $`D_n` of order $`2n`.

Every finite Coxeter group is a {bpref "group.direct_product"}[direct product] of finite irreducible Coxeter groups.  In the LMFDB, we use the notation $`W( \_ )` to denote irreducible Coxeter groups which are also Weyl groups.  This avoids a clash of notation with the {bpref "group.alternating"}[alternating group] $`A_n`, the dihedral group $`D_n`, and the {bpref "group.frobenius"}[Frobenius group] $`F_n`.

Depends on: {uses "group.alternating"}[] {uses "group.dihedral"}[] {uses "group.direct_product"}[] {uses "group.frobenius"}[] {uses "group.order"}[] {uses "group.symmetric"}[] {uses "group.triangle_group"}[] {uses "group.wreath_product"}[]
:::

:::definition "group.cyclic" (lean := "IsCyclic")
*Cyclic group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.cyclic))

A {bpref "group"}[group] $`G` is *cyclic* if it can be {bpref "group.generators"}[generated] by one element.

Depends on: {uses "group"}[] {uses "group.generators"}[]
:::

:::definition "group.derived_series" (lean := "derivedSeries, derivedLength, derivedSeries_succ_derivedLength, derivedLength_eq_sInf_eq_bot")
*Derived series of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.derived_series))

The *derived series* of a finite {bpref "group"}[group] $`G` is the chain of subgroups

$$`G =G^{(0)}\rhd G^{(1)} \rhd G^{(2)} \rhd \cdots \rhd G^{(k)}`

where $`G^{(i+1)}` is the {bpref "group.commutator_subgroup"}[commutator subgroup] of $`G^{(i)}` for all $`i`, each inclusion is {bpref "group.proper_subgroup"}[proper], and $`G^{(k+1)}=G^{(k)}`.  The final index $`k` is the *derived length* of $`G`.

A group is {bpref "group.solvable"}[solvable] if and only if $`G^{(k)}=\langle e\rangle`.

Depends on: {uses "group"}[] {uses "group.commutator_subgroup"}[] {uses "group.proper_subgroup"}[] {uses "group.solvable"}[]
:::

:::definition "group.dicyclic" (lean := "DihedralGroup")
*Dicyclic group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.dicyclic))

A *dicyclic group* of {bpref "group.order"}[order] $`4n`, denoted $`\mathrm{Dic}_n` or $`Q_{4n}`, is a non-split extension of a {bpref "group.cyclic"}[cyclic] {bpref "group"}[group] of order $`2n` by a cyclic group of order $`2`.  That is, $`\mathrm{Dic}_n` has a subgroup of index $`2` which is cyclic, but it is not a {bpref "group.semidirect_product"}[semidirect product] of that subgroup and a subgroup of order $`2`.

The dicyclic group of order $`4n` can be given by generators and relations:
$`\langle a,b \mid a^{2n}, a^n b^{-2}, bab^{-1}a\rangle`.

The group $`\textrm{Dic}_2` is isomorphic to the quaternion group of order $`8`.

Depends on: {uses "group"}[] {uses "group.cyclic"}[] {uses "group.order"}[] {uses "group.semidirect_product"}[]
:::

:::definition "group.dihedral" (lean := "DihedralGroup")
*Dihedral group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.dihedral))

The *dihedral group* is the set of symmetries of a regular $`n`-gon under the operation of composition.  It consists of $`n` rotations and $`n` reflections, has {bpref "group.order"}[order] $`2n`, and can be generated by one rotation of order $`n` and one reflection of order $`2`.

$$`D_n = \langle g,h \mid g^n=h^2=1, hg=g^{-1}h \rangle = \{e,g,g_2,...,g_{n-1},h,gh,...,g_{n-1}h\}.`

It is the split extension $`C_n\rtimes C_2` with $`C_2` acting by $`-1`. The non-split extension in this case is the {bpref "group.dicyclic"}[dicyclic]  group.

Depends on: {uses "group.dicyclic"}[] {uses "group.order"}[]
:::

:::definition "group.direct_product" (lean := "Prod.instGroup, Subgroup.IsComplement', Subgroup.isComplement'_of_disjoint_and_mul_eq_univ, SemidirectProduct.mulEquivSubgroup")
*Direct product of groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.direct_product))

Given two groups $`G_1` and $`G_2` with operations $`*_1` and $`*_2`, the *direct product* of sets $`G_1\times G_2` is a {bpref "group"}[group] under the operation

$$`(a_1, a_2)*(b_1, b_2) = (a_1*_1 b_1, a_2 *_2 b_2).`

This has {bpref "group.subgroup.normal"}[normal] subgroups

$$`H_1=\{(a,e_2) \mid a \in G_1\}\cong G_1`

and

$$`H_2=\{(e_1,a) \mid a \in G_2\}\cong G_2`

such that $`H_1\cap H_2 = \{(e_1,e_2)\}` and $`H_1H_2=G_1\times G_2`.

Conversely, if a group $`G` has normal subgroups $`H` and $`K` such that $`H\cap K=\{e\}` and $`HK=G`, then $`G\cong H\times K`.  We call $`H` and $`K` a *direct factors* of $`G` in this case.

Depends on: {uses "group"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.division" (lean := "IsRationallyConj, IsRationallyConj.equivalence, IsRationallyConj.setoid, RatConjClasses, IsConj.isRationallyConj")
*Divisions of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.division))

A *division* (or *rational conjugacy classes*) of a finite {bpref "group"}[group] $`G` is an equivalence class under the following relation: $`x \sim y` if there exist $`g \in G` and $`n \in \Z` relatively prime to the {bpref "group.element_order"}[order] of $`x` with $`y = g^{-1} x^n g`.  It is a coarsening of conjugacy: any division is a union of {bpref "group.conjugacy_class"}[conjugacy classes].

Just as values of {bpref "group.representation.character"}[characters] are constant on conjugacy classes, values of {bpref "group.representation.rational_character"}[rational characters] are constant on rational conjugacy classes.

Depends on: {uses "group"}[] {uses "group.conjugacy_class"}[] {uses "group.element_order"}[] {uses "group.representation.character"}[]
:::

:::definition "group.division_maximal" (lean := "RatConjClasses.IsMaximal, Subgroup.IsMaximalCyclic, RatConjClasses.isMaximal_mk_iff")
*Maximal division of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.division_maximal))

A {bpref "group.division"}[division] (or rational conjugacy classes) of a finite {bpref "group"}[group] $`G` is *maximal* if if a representative generates a maximal cyclic subgroup of $`G`.

Depends on: {uses "group"}[] {uses "group.division"}[]
:::

:::definition "group.division_small_large"
*Small and large divisions of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.division_small_large))

A {bpref "group.division_maximal"}[maximal division] of a group is either *small* or *large* (and not both), according to the following process.

Consider a division consisting of $`n` conjugacy classes, each of size $`m` with elements of order $`r`.  If $`n  \ge |G| / 2000` and either $`n \ge 20000` or $`n^2 \ge |G|`, then the division is considered large.  Otherwise, for divisions that don't meet these criteria, we compute the intersections down chains of maximal subgroups (i.e., with maximal subgroups, their maximal subgroups, etc.), greedily minimizing the intersection.  If we are able to decrease the size of the intersection below a threshold then we consider the division small; if the process terminates in a step where the remaining elements do not intersect nontrivially with any of the next steps in the subgroup tree, and we're still above the threshold, then we also consider the original division large.

Depends on: {uses "group.division_maximal"}[]
:::

:::definition "group.element_order" (lean := "orderOf, addOrderOf, orderOf_eq_zero_iff, Nat.card_zpowers")
*Order of a group element.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.element_order))

The *order* of an element $`g` in a multiplicative {bpref "group"}[group] $`G` is the least positive integer $`n` such that $`g^n` is the {bpref "alg.binary_operation.identity"}[identity element] of $`G`, if such an integer exist, and is $`\infty` otherwise.  In an additive group, the order of $`g` is the least positive integer $`n` such that $`ng=0`.  In both cases, the order of $`g` is also equal to the cardinality of the {bpref "group.cyclic"}[cyclic] {bpref "group.subgroup"}[subgroup] it generates.

Depends on: {uses "alg.binary_operation.identity"}[] {uses "group"}[] {uses "group.cyclic"}[] {uses "group.subgroup"}[]
:::

:::definition "group.elementary" (lean := "TauCeti.IsElementary, TauCeti.IsPElementary")
*Elementary group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.elementary))

A finite {bpref "group"}[group] is $`p`-*elementary* if it is the {bpref "group.direct_product"}[direct product] of a {bpref "group.cyclic"}[cyclic] group of order relatively prime to $`p` and a {bpref "group.pgroup"}[$`p`-group].  Brauer's induction theorem states that any {bpref "group.representation.character"}[character] of a finite group $`G` is an integer linear combination of inductions of linear characters from elementary subgroups of $`G` (for different primes $`p` dividing the order of $`G`).

Depends on: {uses "group"}[] {uses "group.cyclic"}[] {uses "group.direct_product"}[] {uses "group.pgroup"}[] {uses "group.representation.character"}[]
:::

:::definition "group.exponent" (lean := "Monoid.exponent, Monoid.exponent_eq_zero_iff")
*Exponent of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.exponent))

The *exponent of a {bpref "group"}[group]* $`G` is the smallest positive integer $`n` such that $`g^n=e` for all $`g\in G`.  If no such positive integer exists, then the exponent of the group is infinite.

Depends on: {uses "group"}[]
:::

:::definition "group.fitting_subgroup" (lean := "Subgroup.fittingSubgroup, Subgroup.isNilpotent_fittingSubgroup, Subgroup.le_fittingSubgroup, Subgroup.isNilpotent_sup")
*Fitting subgroup of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.fitting_subgroup))

The *Fitting subgroup* of a {bpref "group"}[group] $`G`, denoted $`\mathrm{Fit}(G)`, is the largest {bpref "group.subgroup.normal"}[normal] {bpref "group.subgroup"}[subgroup] of $`G` which is {bpref "group.nilpotent"}[nilpotent].  Since the product of a collection of normal nilpotent subgroups of a group is nilpotent, the Fitting subgroup is unique.

Depends on: {uses "group"}[] {uses "group.nilpotent"}[] {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.frobenius" (lean := "AffineEquiv.group, GaloisField, TauCeti.AffineGroup, TauCeti.AffineGroup.smul_def")
*Frobenius group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.frobenius))

Given a prime power $`q`, the *Frobenius group* $`F_q` is the group of invertible affine transformations ($`x \mapsto ax + b`) on $`\F_q`.  Explicitly, it is the group

$$`F_q := \{ \varphi : \F_q \to \F_q \mid \exists a, b \in \F_q \text{ such that } a \neq 0 \text{ and } \varphi(x) = ax + b \text{ for all } x \in \F_q \}`

where the usual composition of maps is the group operation. It has {bpref "group.order"}[order] $`q(q-1)` and is a {bpref "group.z_group"}[Z-group] (and hence is {bpref "group.metacyclic"}[metacyclic] and {bpref "group.solvable"}[solvable]).

Depends on: {uses "group.order"}[] {uses "group.solvable"}[] {uses "group.z_group"}[]
:::

:::definition "group.fuchsian" (lean := "Subgroup.IsCofinite")
*Fuchsian group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.fuchsian))

A *Fuchsian group* is a discrete subgroup of $`\mathrm{PSL}(2,\mathbb{R})`  for the natural topology induced by the topology of $`2\times
2` real matrices.

We say that a Fuchsian group is of
the *first kind* if it has finite covolume for the hyperbolic metric {bpref "mf.upper_half_plane"}[$`d\mu=dxdy/y^2`], i.e.

$$`\text{covol}(G)=\int_{\mathfrak{F}(G)}d\mu<\infty,`

where $`\mathfrak{F}(G)` is the {bpref "group.fuchsian.fundamental_domain"}[fundamental domain] of $`G`.

Depends on: {uses "group.fuchsian.fundamental_domain"}[] {uses "mf.upper_half_plane"}[]
:::

:::definition "group.fuchsian.action" (lean := "UpperHalfPlane.SLAction, UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.specialLinearGroup_apply")
*Action of $`\SL(2,\R)` in the upper half-plane.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.fuchsian.action))

The group $`\SL(2,\R)` acts on the {bpref "mf.upper_half_plane"}[upper half-plane] via
<b>linear fractional transformation</b>, given by

$$`\begin{pmatrix}a&b\\c&d \end{pmatrix}(z)
 =
\frac{a z + b}{c z + d} .`

Depends on: {uses "mf.upper_half_plane"}[]
:::

:::definition "group.gassmann_equivalence"
*Gassmann equivalence.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.gassmann_equivalence))

Two {bpref "group.subgroup"}[subgroups] $`H_1` and $`H_2` of a finite {bpref "group"}[group] $`G` are *Gassmann equivalent* if, for every {bpref "group.conjugacy_class"}[conjugacy class] $`C` of $`G`, the sets $`C \cap H_1` and $`C \cap H_2` have the same size.  An ordering of the conjugacy classes of $`G` then induces an ordering of the Gassmann equivalence classes of subgroups of $`G`, just by lexicographically ordering the vectors of intersection counts.

An equivalent condition is that the permutation modules $`\Q[H_1\backslash G]` and $`\Q[H_2\backslash G]` are isomorphic as $`\Q[G]`-modules, which also applies to finite index subgroups $`H_1,H_2` of an infinite group $`G`; see Proposition 2.6 of  for other equivalent definitions.

Gassmann equivalent subgroups of {bpref "gg.galois_group"}[Galois groups] of number fields give rise to {bpref "nf.arithmetically_equivalent"}[arithmetically equivalent] number fields.

Depends on: {uses "gg.galois_group"}[] {uses "group"}[] {uses "group.conjugacy_class"}[] {uses "group.subgroup"}[] {uses "nf.arithmetically_equivalent"}[]
:::

:::definition "group.general_linear" (lean := "Matrix.GeneralLinearGroup, Matrix.ProjGenLinGroup, GaloisField")
*General linear group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.general_linear))

The *general linear group* $`\GL(n,q)` is the group of $`n \times n` invertible matrices with entries in the {bpref "ring.field"}[field] $`\F_q` (the finite field with $`q` elements). It has order $`\prod_{k=0}^{n-1} (q^n - q^k)`.
If $`p` is prime, then $`\GL(n,p)` is the {bpref "group.automorphism"}[automorphism group] of the abelian group $`C_p^n`.

The *projective general linear group* $`\PGL(n, q)` is the {bpref "group.quotient"}[quotient] of $`\GL(n, q)` by its subgroup of scalar matrices.

Depends on: {uses "group.automorphism"}[] {uses "group.quotient"}[] {uses "ring.field"}[]
:::

:::definition "group.generalized_quaternion" (lean := "QuaternionGroup")
*Generalized quaternion.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.generalized_quaternion))

The *(generalized) quaternion group* $`Q_n` is a special case of a {bpref "group.dicyclic"}[dicyclic] group $`\text{Dic}_m` when $`n=4m\geq 8` is a power of $`2`.

Depends on: {uses "group.dicyclic"}[]
:::

:::definition "group.group_mathlib_defn" (lean := "Monoid")
*Group (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.group_mathlib_defn))

A group in mathlib is defined as a *monoid* (which has the data of a binary operation, an identity element $`1` and is associative) with an operation $`{}^{-1}` such that $`a^ {-1} * a = 1`.
:::

:::definition "group.group_ring" (lean := "MonoidAlgebra")
*group ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.group_ring))

If $`G` is a {bpref "group"}[group] and $`R` is a {bpref "ring"}[ring], the *group ring* is the free $`R`-module with basis $`G` in which multiplication is defined via the distributive law.  It consists of all formal finite sums of the form $`\sum r_g g` with $`g\in G` and $`r_g\in R`.

Depends on: {uses "group"}[] {uses "ring"}[]
:::

:::definition "group.heisenberg" (lean := "TauCeti.HeisenbergGroup")
*Heisenberg group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.heisenberg))

Given a prime $`p`, the *Heisenberg group* $`\He_p` is the group of $`3 \times 3` unitriangular matrices over the finite field $`\F_p`.  Explicitly, it is given by

$$`\He_p := \left\{ \begin{pmatrix} 1 & a & b \\ 0 & 1 & c \\ 0 & 0 & 1 \\ \end{pmatrix} \mid a, b, c \in \F_p \right\}`

with the usual matrix multiplication as the group operation. It has order $`p^3`, and is one of only two non-abelian groups of order $`p^3`.  In particular, for an odd prime $`p`, it is the unique non-abelian group of order $`p^3` and exponent $`p`.
:::

:::definition "group.hyperelementary" (lean := "TauCeti.IsHyperelementary, TauCeti.IsPHyperelementary")
*Hyperelementary group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.hyperelementary))

A finite {bpref "group"}[group] $`G` is *hyperelementary* if it is an {bpref "group.nonsplit_product"}[extension] $`G \simeq C \rtimes P` of a {bpref "group.pgroup"}[$`p`-group] $`P` by a {bpref "group.cyclic"}[cyclic] group $`C` of order prime to $`p`.  Solomon's induction theorem states that the trivial {bpref "group.representation.character"}[character] is an integer linear combination of inductions of trivial characters from hyperelementary subgroups of $`G` (for various primes dividing the {bpref "group.order"}[order] of $`G`).

Depends on: {uses "group"}[] {uses "group.cyclic"}[] {uses "group.nonsplit_product"}[] {uses "group.order"}[] {uses "group.pgroup"}[] {uses "group.representation.character"}[]
:::

:::definition "group.inner_automorphism" (lean := "MulAut.conj, MulAut.conj_apply")
*Inner automorphism of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.inner_automorphism))

If $`G` is a {bpref "group"}[group] and $`g\in G`, then the function $`\phi_g:G\to G` given by conjugation by $`g`

$$`\phi_g(x) = gxg^{-1}`

is an {bpref "group.automorphism"}[automorphism] of $`G` called an *inner automorphism*.

The set of inner automorphisms $`\mathrm{Inn}(G)` is a
{bpref "group.subgroup"}[subgroup] of $`\Aut(G)`, and

$$`\mathrm{Inn}(G) \cong G/Z(G)`

where $`Z(G)` is the {bpref "group.center"}[center] of $`G`.

Depends on: {uses "group"}[] {uses "group.automorphism"}[] {uses "group.center"}[] {uses "group.subgroup"}[]
:::

:::definition "group.isoclinism" (lean := "Group.Isoclinism, Group.IsIsoclinic, Group.centralCommutatorMap, Group.IsIsoclinic.symm, Group.IsIsoclinic.trans")
*Isoclinism.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.isoclinism))

For a group $`G` and its {bpref "group.commutator_subgroup"}[commutator] $`G'`, write $`\omega_G` for the map $`G \times G \to G'` defined by $`\omega_G(x, y) = x^{-1}y^{-1}xy`, and note that $`\omega_G` descends to a map on $`G / Z(G) \times G / Z(G)`.
An *isoclinism* between two groups $`G_1` and $`G_2` is a pair of isomorphisms between their {bpref "group.inner_automorphism"}[inner automorphism groups] and their {bpref "group.commutator_subgroup"}[commutator subgroups]

$$`\phi : G_1 / Z(G_1) \to G_2 / Z(G_2)`

$$`\sigma : G_1' \to G_2'`

 so that

$$`\sigma \circ \omega_{G_1} = \omega_{G_2} \circ (\phi \times \phi).`

This is an equivalence relation on groups, and each equivalence class contains at least one {bpref "group.stem_group"}[stem group].  Note that order is not an isoclinism invariant, but {bpref "group.nilpotent"}[nilpotency class] and {bpref "group.derived_series"}[solvable length] are (except for the trivial group).

Depends on: {uses "group.commutator_subgroup"}[] {uses "group.derived_series"}[] {uses "group.inner_automorphism"}[] {uses "group.nilpotent"}[]
:::

:::definition "group.label"
*Label of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.label))

The *label* for a {bpref "group"}[group] $`G` has the form $`\mathtt{N.i}`, where $`\mathtt{N}` is the {bpref "group.order"}[order] of the group and $`\mathtt{i}` is the small group id that distinguishes groups of the same order (as determined in GAP). If a group is not in GAP Small Groups database, we replace $`\mathtt{i}` with an incrementing letter code, assigning labels to groups as they are added to our database.

Subgroups are {bpref "group.subgroup_label"}[labeled] using the ambient group, index, and an ordering of subgroups up to automorphism and then up to conjugacy with the same  invariants.

Depends on: {uses "group"}[] {uses "group.order"}[]
:::

:::definition "group.label_complex_group_char"
*Label of irreducible complex characters of groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.label_complex_group_char))

The *label* of an irreducible complex character of a {bpref "group"}[group] has the format $`N.i.dcj` where $`N.i` is the label for the group, $`d` is the dimension, $`c` is a lower-case letter code for the rational class of this character, and $`j` is an enumeration of characters within that rational class ($`j` is omitted if the rational class is a singleton).

Depends on: {uses "group"}[]
:::

:::definition "group.label_conjugacy_class"
*Label of a conjugacy class.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.label_conjugacy_class))

The *label* of a rational {bpref "group.conjugacy_class"}[conjugacy class] of a group $`G` has the format $`NA` where $`N` is the order of elements in the conjugacy class, $`A` is a sequence of capital letters.

The *label* of a complex {bpref "group.conjugacy_class"}[conjugacy class] of a group $`G` has the format $`NAj` where $`NA` is the label of the division containing it, (so $`N` is the order of elements in the conjugacy class), and $`j` is an enumeration of class within that rational conjugacy class ($`j` is omitted if there is a single class within rational conjugacy classes).

Depends on: {uses "group.conjugacy_class"}[]
:::

:::definition "group.label_rational_group_char"
*Label of rational character of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.label_rational_group_char))

The *label of a rational character* of a {bpref "group"}[group] has the form $`N.i.oj` where $`N.i` is the label for the group, $`o` is the order of elements in this class and $`j` is a lower-case letter code.

Depends on: {uses "group"}[]
:::

:::definition "group.linear" (lean := "TauCeti.GeneralLinear.hopfIdealPointsSubgroup, TauCeti.HopfIdeal, TauCeti.GeneralLinear.coordinateHopfAlgebra, TauCeti.ProjectiveGeneralLinear.coordinateHopfAlgebra, Matrix.ProjGenLinGroup")
*Linear and Projective Linear Groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.linear))

Over any field $`K`, linear group usually refers to an algebraic group which is a (Zariski closed) subgroup of the general linear group GL$`(n,K)` of invertible $`n\times n` matrices with coefficients in $`K`. Similarly, projective linear group refers to a closed subgroup of $`\text{PGL}(n,K)=\text{GL}(n,K)/\{\text{scalar matrices}\}`, the group of linear automorphisms of the projective $`n`-space. When $`K=\mathbb{F}_q` is a finite field, these groups are finite, and often simple or almost simple, and so they play an important role in the classification of finite simple groups.
:::

:::definition "group.linear_automorphism" (lean := "Matrix.GeneralSemilinearGroup, Matrix.SpecialSemilinearGroup, Matrix.ProjectiveGeneralSemilinearGroup, Matrix.ProjectiveSpecialSemilinearGroup, Matrix.GeneralLinearGroup.entrywiseAut")
*Linear group twisted by automorphisms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.linear_automorphism))

The group $`\Gamma\mathrm{L} (n,q)` is the semi-direct product of $`\GL(n,q)` with the group of field automorphisms $`A = \Aut(\F_q / \F_p)`, acting $`\GL(n,q)` entry-wise. Similarly, $`\Sigma \mathrm{L}(n,q)` is the semi-direct product of $`\SL(n,q)` with $`A`.

The projective linear groups twisted by automorphisms are $`\PGammaL(n,q)` and $`\PSigmaL(n,q)`, the quotients of $`\Gamma \mathrm{L}(n,q)` and $`\Sigma \mathrm{L}(n,q)`, respectively, by their subgroups of scalar matrices.
:::

:::definition "group.lower_central_series" (lean := "Subgroup.lowerCentralSeries, Subgroup.nilpotent_iff_lowerCentralSeries")
*Lower central series of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.lower_central_series))

If $`G` is a {bpref "group"}[group], for subsets $`A` and $`B` let $`[A,B]` be the {bpref "group.subgroup"}[subgroup] generated by commutators of $`A` and $`B`, i.e.,

$$`[A,B] = \langle a^{-1}b^{-1}ab\mid a\in A \text{ and } b\in B\rangle.`

Further, let $`G^0=G` and for $`i>0`, $`G^i = [G,G^{i-1}]`.  Then, the *lower central series* of $`G` is a {bpref "group.normal_series"}[normal series] of subgroups

$$`G \unrhd G^1 \unrhd G^2 \unrhd \cdots .`

Then, $`G` is {bpref "group.nilpotent"}[nilpotent] if and only if $`G^k =\langle e\rangle` for some $`k>0`.

Depends on: {uses "group"}[] {uses "group.nilpotent"}[] {uses "group.normal_series"}[] {uses "group.subgroup"}[]
:::

:::definition "group.matrix_group" (lean := "Matrix.GeneralLinearGroup, Subgroup")
*Matrix group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.matrix_group))

A matrix group is a subgroup of $`\GL_n(R)` for some commutative ring $`R`.

A given abstract group may have more than one presentation as a matrix group over different rings $`R`.

The value $`z_k` in a given matrix represents a primitive element of the finite field $`\F_{p^k}` for some prime $`p`.
:::

:::definition "group.maximal_quotient" (lean := "MonoidHom.IsMaximalQuotient, QuotientGroup.isMaximalQuotient_mk'")
*Maximal quotient of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.maximal_quotient))

A *maximal quotient* $`M = G/K` of a {bpref "group"}[group] $`G` is a {bpref "group.quotient"}[quotient] of $`G` with the property that if $`H \le K` is normal in $`G` then either $`H=K` or $`H=1`.  Equivalently, $`K` is a {bpref "group.minimal_normal"}[minimal normal subgroup] of $`G`.

Depends on: {uses "group"}[] {uses "group.minimal_normal"}[] {uses "group.quotient"}[]
:::

:::definition "group.metabelian" (lean := "IsMetabelian, isMetabelian_iff_exists_normal, isMetabelian_iff_derivedSeries_two")
*Metabelian group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.metabelian))

A finite group $`G` is *metabelian* if its commutator subgroup is abelian. Equivalently, $`G` is an extension of an abelian group by an abelian group. Metabelian groups are {bpref "group.solvable"}[solvable], and they include all {bpref "group.abelian"}[abelian], {bpref "group.dihedral"}[dihedral], {bpref "group.generalized_quaternion"}[quaternion], {bpref "group.metacyclic"}[metacyclic], extra​special groups and groups of $`p`-rank one.

Every {bpref "group.metacyclic"}[metacylic] group is metabelian, but the converse does not hold, as shown by [these examples](https://beta.lmfdb.org/Groups/Abstract/?metacyclic=no&metabelian=yes).

Depends on: {uses "group.abelian"}[] {uses "group.dihedral"}[] {uses "group.generalized_quaternion"}[] {uses "group.solvable"}[]
:::

:::definition "group.metacyclic" (lean := "IsMetacyclic, IsMetacyclic.isSupersolvable, IsZGroup.isMetacyclic, IsKleinFour.isMetacyclic, IsKleinFour.not_isZGroup")
*Metacyclic group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.metacyclic))

A metacyclic group is an {bpref "group.nonsplit_product"}[extension] of a cyclic group by a cyclic group.  All metacyclic groups are {bpref "group.supersolvable"}[supersolvable] and in particular {bpref "group.monomial"}[monomial].

Every {bpref "group.z_group"}[Z-group] is metacyclic, but the converse does not hold, as shown by [these examples](https://beta.lmfdb.org/Groups/Abstract/?metacyclic=yes&Zgroup=no).

Depends on: {uses "group.monomial"}[] {uses "group.nonsplit_product"}[] {uses "group.supersolvable"}[] {uses "group.z_group"}[]
:::

:::definition "group.min_complex_irrep_deg" (lean := "irreducibleDegree, Matrix.GeneralLinearGroup.representation")
*Minimal degree of a complex irrep.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.min_complex_irrep_deg))

The smallest positive integer $`d` such that the group $`G` admits a {bpref "group.representation.faithful"}[faithful] {bpref "group.representation.irrep"}[irreducible] complex representation of degree $`d`.

Depends on: {uses "group.representation.faithful"}[] {uses "group.representation.irrep"}[]
:::

:::definition "group.min_complex_rep_deg" (lean := "linearDegree")
*Minimal degree of a complex representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.min_complex_rep_deg))

The smallest positive integer $`d` such that the group $`G` admits a {bpref "group.representation.faithful"}[faithful] complex representation of degree $`d`.

Depends on: {uses "group.representation.faithful"}[]
:::

:::definition "group.min_faithful_linear" (lean := "linearDegree, irreducibleDegree, Matrix.GeneralLinearGroup.representation")
*Minimal faithful linear representations.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.min_faithful_linear))

A {bpref "group"}[group] $`G` can always be represented as a {bpref "group.matrix_group"}[matrix group], but the degree of the matrix group is constrained both by $`G` and the {bpref "ring"}[ring] $`R` from which the matrix entries are drawn.  The *linear degree* $`\operatorname{lin}_R(G)` is the minimal degree $`n` of a {bpref "group.representation.faithful"}[faithful] {bpref "group.representation.irrep"}[linear representation] $`\rho : G \hookrightarrow \GL_n(R)`, and the *irreducible degree* $`\operatorname{irr}_R(G)` is the minimal degree $`n` of a faithful {bpref "group.representation.irrep"}[irreducible] representation $`\rho: G \hookrightarrow \GL_n(R)`.  Note that, while a faithful linear representation always exists, there may be no faithful irreducible representations of $`G` (in which case we conventionally set $`\operatorname{irr}_R(G) = -1`).

For fields $`R` of {bpref "ring.characteristic"}[characteristic] 0, these values can be characterized in terms of the {bpref "group.complex_character_table"}[character table] of $`G`.  A {bpref "group.representation.character"}[character] $`\chi` of degree $`n` is faithful if the only $`g \in G` with $`\chi(g) = n` is $`g=1`.  The value $`\operatorname{irr}_{\mathbb{C}}(G)` can thus be read off of the character table, but computing $`\operatorname{lin}_{\mathbb{C}}(G)` requires finding linear combinations of characters that are faithful.

For fields $`k` that are not algebraically closed, summing over Galois orbits of complex characters yields {bpref "group.representation.rational_character"}[characters with values in $`k`], and the resulting characters will be faithful if and only if each of the summands is.  However, the {bpref "group.representation.schur_index"}[Schur index] now plays a role, since multiple copies of the given $`k`-values character may be needed in order to produce an actual representation with matrix entries in $`k`.  Both $`\operatorname{lin}_R(G)` and $`\operatorname{irr}_R(G)` are defined in terms of the matrix degree of a representation, which may be larger than the degree of a minimal faithful $`k`-valued character.

Depends on: {uses "group"}[] {uses "group.complex_character_table"}[] {uses "group.representation.character"}[] {uses "group.representation.faithful"}[] {uses "group.representation.irrep"}[] {uses "group.representation.rational_character"}[] {uses "group.representation.schur_index"}[] {uses "ring"}[] {uses "ring.characteristic"}[]
:::

:::definition "group.min_rational_irrep_deg" (lean := "irreducibleDegree, Matrix.GeneralLinearGroup.representation")
*Minimal degree of a rational irrep.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.min_rational_irrep_deg))

The smallest positive integer $`d` such that the group $`G` admits a {bpref "group.representation.faithful"}[faithful] {bpref "group.representation.irrep"}[irreducible] rational representation of degree $`d`.

Depends on: {uses "group.representation.faithful"}[] {uses "group.representation.irrep"}[]
:::

:::definition "group.min_rational_rep_deg" (lean := "linearDegree")
*Minimal degree of a rational representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.min_rational_rep_deg))

The smallest positive integer $`d` such that the group $`G` admits a {bpref "group.representation.faithful"}[faithful] rational representation of degree $`d`.

Depends on: {uses "group.representation.faithful"}[]
:::

:::definition "group.minimal_normal" (lean := "Subgroup.IsMinimalNormal, Subgroup.isMinimalNormal_iff")
*Minimal normal subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.minimal_normal))

A *minimal normal subgroup* $`K` of a {bpref "group"}[group] $`G` is a {bpref "group.subgroup.normal"}[normal subgroup] of $`G` with the property that if $`H \le K` is normal in $`G` then either $`H=K` or $`H=1`.  Equivalently, $`G / K` is a {bpref "group.maximal_quotient"}[maximal quotient] of $`G`.

Depends on: {uses "group"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.mobius_function" (lean := "Subgroup.mobius, Subgroup.normalMobius, Subgroup.mobius_eq_neg_finsum, Subgroup.normalMobius_eq_neg_finsum")
*Möbius function of subgroup lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.mobius_function))

Given a finite group $`G`, we define the *möbius subgroup function* $`\mu_G(H)` on the lattice of subgroups of $`G` by setting $`\mu_G(G) = 1` and then inductively using the relation

$$`\mu_G(H) = -\sum_{H' > H} \mu_G(H').`

Similarly, we define the *möbius quotient function* $`\nu_G(N)` on the lattice of normal subgroups of $`G` by setting $`\nu_G(1) = 1` and inductively using the relation

$$`\nu_G(N) = -\sum_{N' < N} \nu_G(N').`

The möbius subgroup function is used in computing the {bpref "group.rank"}[rank] of $`G`, while the möbius quotient function is used in computing the number of faithful representations of $`G`.

Depends on: {uses "group.rank"}[]
:::

:::definition "group.monomial" (lean := "IsMGroup, IsMGroup.of_isNilpotent")
*Monomial group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.monomial))

A group $`G` is *monomial* or an *M-group* if every complex irreducible representation of $`G` is induced from a $`1`-dimensional representation of some subgroup. Such a group is always {bpref "group.solvable"}[solvable], and monomial groups include all {bpref "group.supersolvable"}[supersolvable] groups and solvable A-groups. A purely group-theoretic description of monomial groups is not known.

While every supersolvable group is monomial, the converse does not hold, as shown by [these examples](https://beta.lmfdb.org/Groups/Abstract/?monomial=yes&supersolvable=no).  Similarly, [these examples](https://beta.lmfdb.org/Groups/Abstract/?solvable=yes&Agroup=yes&supersolvable=no) show that not every solvable A-group is supersolvable.  There are also [examples](https://beta.lmfdb.org/Groups/Abstract/?solvable=yes&monomial=no) of solvable groups that are not monomial.

Depends on: {uses "group.solvable"}[] {uses "group.supersolvable"}[]
:::

:::definition "group.nilpotent" (lean := "Group.IsNilpotent, Group.nilpotencyClass, Subgroup.IsAscendingCentralSeries, Group.isNilpotent_of_finite_tfae, Subgroup.least_ascending_central_series_length_eq_nilpotencyClass")
*Nilpotent group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.nilpotent))

A finite {bpref "group"}[group] $`G` is *nilpotent* if it is a direct product of $`p`-groups. Equivalently, all Sylow subgroups of $`G` are normal. Equivalently, $`G` has a central series

$$`\{1\}=G_0 \lhd G_1 \lhd G_2 \lhd \ldots \lhd G_k = G,`

a nested sequence of normal subgroups with $`[G,G_{i+1}] \leq G_i`.

The smallest such $`k` is the *nilpotency class* of $`G`. It is $`0` for $`C_1`, $`1` for non-trivial {bpref "group.abelian"}[abelian] groups, and $`\geq 2` for all other nilpotent groups. By convention, one can define the nilpotency class of a non-nilpotent group to be $`-1`.

Nilpotent groups are closed under subgroups and quotients (but not extensions), and are {bpref "group.solvable"}[solvable], {bpref "group.supersolvable"}[supersolvable] and {bpref "group.monomial"}[monomial].

Depends on: {uses "group"}[] {uses "group.abelian"}[] {uses "group.solvable"}[]
:::

:::definition "group.nonsplit_product" (lean := "GroupExtension, GroupExtension.Splitting, GroupExtension.Splitting.semidirectProductMulEquiv, Subgroup.IsComplement'")
*Split and non-split extension of groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.nonsplit_product))

If $`G` is a {bpref "group"}[group] with {bpref "group.subgroup.normal"}[normal subgroup] $`N` and {bpref "group.quotient"}[quotient] $`Q\cong G/N`, then $`G` is a *extension* of $`Q` by $`N`, denoted $`N.Q`. Equivalently there is a short exact sequence

$$`1 \to N \to G \to Q \to 1.`

If $`G` has a subgroup $`\tilde Q\leq G` such that $`\tilde Q\cap N=\langle e\rangle`, and $`\tilde QN=G`, then $`\tilde Q\cong Q` and $`G` is a {bpref "group.semidirect_product"}[semidirect product] of $`N` and $`\tilde Q`.  This is equivalent to the existence of a section of the quotient map $`G \to Q`. In this case we say $`G` is a *split extension* of $`Q` by $`N`.

If no such subgroup $`\tilde Q` exists, then $`G` is a *non-split extension* of $`Q` by $`N`.

Depends on: {uses "group"}[] {uses "group.quotient"}[] {uses "group.semidirect_product"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.omega"
*Omega (Lie group).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.omega))

The groups $`\Omega(n,q)` and $`\Omega^{\pm}(n,q)` are subgroups of the {bpref "group.orthogonal"}[special orthogonal groups] $`\SO(n,q)` and $`\SO^{\pm}(n,q)`. Their specific definitions depend on the properties of $`n` and $`q`.

When $`n` is odd, $`\Omega(n,q)` is a subgroup of $`\SO(n,q)`. If $`q` is odd, $`\Omega(n,q)` is the kernel of the {bpref "group.spinor_norm"}[spinor norm map] $`\SO(n,q) \to (\F_q^\times)/(\F_q^\times)^2`, and is an index $`2` subgroup of $`\SO(n,q)`. When $`q` is even, we define $`\Omega(n,q) = \SO(n,q)`.

When $`n` is even, $`\Omega^{\pm}(n,q)` is a subgroup of $`\SO^{\pm}(n,q)`. To define it, we use the _quasideterminant_ map, sending $`g \in \SO(n,q)` to $`(-1)^d`, where $`d` is the dimension of the subspace of $`V = \F_q^n` fixed by $`g`. Then $`\Omega^{\pm}(n,q)` is the kernel of this map, i.e. all those $`g` fixing an even-dimensional subspace of $`V`.

The groups $`\POmega(n,q)` are $`\POmega^{\pm}(n,q)` are the quotients of $`\Omega(n,q)` and $`\Omega^{\pm}(n,q)`, respectively, by their subgroups of scalar matrices.

(see , pages xi-xii)

Depends on: {uses "group.orthogonal"}[] {uses "group.spinor_norm"}[]
:::

:::definition "group.order_conjugacy_class" (lean := "IsConj.orderOf_eq, SemiconjBy.orderOf_eq, ConjClasses")
*Order of elements in a conjugacy class.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.order_conjugacy_class))

All elements in a particular {bpref "group.conjugacy_class"}[conjugacy class] are of the same {bpref "group.element_order"}[order] in the group.

Depends on: {uses "group.conjugacy_class"}[] {uses "group.element_order"}[]
:::

:::definition "group.order_stats" (lean := "Monoid.orderStatistics, Monoid.count_orderStatistics")
*Order statistics of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.order_stats))

The *order statistics* of a group $`G` is the multiset of {bpref "group.element_order"}[orders of elements] of $`G`, with multiplicities given by the number of elements in $`G` of that order.

For example, the Quaternion group of order 8 has order statistics $`\{1,2,4,4,4,4,4,4\}` which we denote in searches as 1^1, 2^1, 4^6.

Depends on: {uses "group.element_order"}[]
:::

:::definition "group.orthogonal" (lean := "TauCeti.QuadraticMap.orthogonalGroup, TauCeti.QuadraticMap.specialOrthogonalGroup, QuadraticForm.projectiveOrthogonalGroup, QuadraticForm.projectiveSpecialOrthogonalGroup, QuadraticForm.ellipticForm")
*Orthogonal group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.orthogonal))

An *orthogonal group* over a vector space $`V` of dimension $`n` over a field $`F` is a subgroup of $`\GL_n(F)` that fixes a quadratic form $`Q`, i.e. all those $`m` such that $`Q(mx) = Q(x)` for all $`x \in V`.

Over a finite field, the orthogonal groups behave differently depending on the dimension $`n` of $`V`. When $`n` is odd, there is one equivalence class of quadratic forms, and so there is a unique orthogonal group (up to isomorphism), denoted $`\GO(n,q)`. When $`n` is even there are two equivalence classes of quadratic forms, called the $`+` and $`-` forms. These give rise to the orthogonal groups $`\GO^{+}(n,q)` and $`\GO^{-}(n,q)`.

The *special orthogonal groups* $`\SO(n,q)` and $`\SO^{\pm}(n,q)` are the subgroups of $`\GO(n,q)` and $`\GO^{\pm}(n,q)`, respectively, consisting of all matrices of determinant $`1`.

The *projective orthogonal groups* are given by the quotient of an orthogonal group by its subgroup of scalar matrices. In particular,  we have

$$`\begin{matrix} \PGO(n,q) = \GO(n,q)/\{ \pm I_n \}, & \PGO^{\pm}(n,q) = \begin{cases}\GO^{\pm}(n,q) & q \text{ even}, \\ \GO^{\pm}(n,q)/\{ \pm I_n \} & q \text{ odd}.\end{cases} \\ \\ \PSO(n,q) = \SO(n,q), & \PSO^{\pm}(n,q) = \begin{cases}\SO^{\pm}(n,q) & q \text{ even}, \\ \SO^{\pm}(n,q)/\{ \pm I_n \} & q \text{ odd}.\end{cases} \end{matrix}`

(see , pages xi-xii)
:::

:::definition "group.other_dihedral" (lean := "OtherDihedralGroup, OtherDihedralGroup.card, ZMod.involutionMulAut")
*Other-dihedral group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.other_dihedral))

The *other-dihedral group* $`\OD_{2^k}` is one of the four non-abelian groups of {bpref "group.order"}[order] $`2^k` containing a cyclic subgroup of index 2 (the other three being the {bpref "group.dihedral"}[dihedral group], the {bpref "group.generalized_quaternion"}[(generalized) quaternion group], and the {bpref "group.semi_dihedral"}[semi-dihedral group]).  It has the group presentation:

$$`\OD_{2^k} = \langle r,s \mid r^{2^{k-1}} = s^2 = 1,\ srs=r^{2^{k-2}+1}\rangle.`

It can also be given as the {bpref "group.semidirect_product"}[semidirect product] $`C_{2^{k-1}} \rtimes C_2` where the action of $`C_2` on $`C_{2^{k-1}}` is given by $`x \mapsto x^{2^{k-2}+1}`.

Depends on: {uses "group.dihedral"}[] {uses "group.generalized_quaternion"}[] {uses "group.order"}[] {uses "group.semi_dihedral"}[] {uses "group.semidirect_product"}[]
:::

:::definition "group.outer_aut" (lean := "MulAut.Out, MulAut.IsOuter, MulAut.isOuter_iff_ne_one, MulAut.conj")
*Outer automorphism group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.outer_aut))

If $`G` is a {bpref "group"}[group], its {bpref "group.inner_automorphism"}[inner automorphism] group is a {bpref "group.subgroup.normal"}[normal subgroup] of the full {bpref "group.automorphism"}[automorphism group].  Then, the *outer automorphism group* of $`G` is

$$`\mathrm{Out}(G) = \Aut(G)/\mathrm{Inn}(G).`

Note that the term *outer automorphism* is often used to mean any automorphism of a group $`G` which is not an inner automorphism. In this case, the nontrivial elements of the outer automorphism group are cosets of outer automorphisms.

Depends on: {uses "group"}[] {uses "group.automorphism"}[] {uses "group.inner_automorphism"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.over_subgroup" (lean := "Subgroup, CovBy")
*Over-subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.over_subgroup))

If $`H \subseteq G` is a {bpref "group.subgroup"}[subgroup], an *over-subgroup* is a subgroup $`K \subseteq G` with $`H \subseteq K`.  A *minimal over-subgroup* is an over-subgroup $`K \ne H` that is minimal with respect to inclusion.

Depends on: {uses "group.subgroup"}[]
:::

:::definition "group.paramodular" (lean := "SymplecticGroup.paramodular, SymplecticGroup.mem_paramodular_iff, SymplecticGroup.paramodularGL")
*Paramodular group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.paramodular))

The paramodular group $`K(N)` of level $`N` is defined as

$$`K(N)=\left\{
\left(\begin{matrix}
 * & N* & * &*\\
* & * & * & */N\\
* & N* &*&*\\
N*&N*&N*&*
\end{matrix}\right)
:
*\in{\Bbb Z}\right\}\cap \mathrm{Sp}(4, {\Bbb Q})`

where  $`\mathrm{Sp}(4, {\Bbb Q})`
is the {bpref "group.sp2gr"}[symplectic group]
with rational entries.

The paramodular group is defined more intrinsically as the stabilizer in $`\Sp(4,\Q)`
of $`\Z\oplus\Z\oplus\Z\oplus N\Z` (column vectors).
Thus it comprises the $`\Sp(4,\Q)` matrices

$$`\left(\begin{matrix}
 * & * & * &*/N\\
* & * & * & */N\\
* & * &*&*/N\\
N*&N*&N*&*\end{matrix}\right)`

but the symplectic conditions imply that such matrices satisfy the stronger entrywise conditions shown above.

Depends on: {uses "group.sp2gr"}[]
:::

:::definition "group.perfect" (lean := "Group.IsPerfect")
*Perfect groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.perfect))

A {bpref "group"}[group] $`G` is *perfect* if it is equal to its own {bpref "group.commutator_subgroup"}[commutator subgroup] $`G'`. Equivalently, $`G` has no non-trivial cyclic (equivalently abelian, equivalently soluble) quotients. All non-abelian simple and quasisimple groups are perfect.

A perfect group may have cyclic composition factors, for example, $`\mathrm{SL}(2,5)=C_2.A_5` is perfect.

Depends on: {uses "group"}[] {uses "group.commutator_subgroup"}[]
:::

:::definition "group.permutation_degree" (lean := "Group.minPermDegree, Group.exists_injective_minPermDegree, Group.minPermDegree_le")
*Permutation degree.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.permutation_degree))

Given a finite {bpref "group"}[group] $`G`, the *minimal permutation degree* of $`G` is the minimal degree of a faithful {bpref "group.permutation_representation"}[permutation representation] of $`G`. Equivalently, it is the smallest positive integer $`n` such that $`S_n` has a subgroup isomorphic to $`G` which may or may not be transitive.

Depends on: {uses "group"}[] {uses "group.permutation_representation"}[]
:::

:::definition "group.permutation_module" (lean := "Representation.ofMulAction, MulAction.toPermHom")
*permutation module.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.permutation_module))

If $`H` is a finite index subgroup of $`G`, then $`G` acts on the right cosets of $`H` via $`Hg\overset{g'}{\mapsto}Hgg'`, yielding a *permutation representation* that sends each $`g\in G` to the permutation of $`H\backslash G` given by its action.  This defines a homomorphism from $`G` to the symmetric group on $`n=[G:H]` letters.

For a commutative ring $`R`, the action of $`G` of $`H\backslash G` can be extended $`R`-linearly to an action of $`G` on  $`R[H\backslash G]`, the free $`R`-module with basis $`G\backslash H`, which is then a module over the {bpref "group.group_ring"}[group ring] $`R[G`\].  The $`R[G]`-module $`R[H\backslash G]` is a *permutation module* over $`R`.

Depends on: {uses "group.group_ring"}[]
:::

:::definition "group.permutation_representation" (lean := "Equiv.Perm, MulAction.IsPretransitive, Equiv.permutationRepresentation, Equiv.isPretransitive_range_permutationRepresentation_iff")
*Permutation representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.permutation_representation))

A *permutation representation* of a finite group $`G` is a homomorphism $`\rho : G \to S_n` for some $`n`.  The integer $`n` is the *degree* of $`\rho`, and a representation is *faithful* if $`\rho` is injective.  The representation is *transitive* if the set $`\{1, \dots, n\}` cannot be broken up into smaller orbits under the action of $`G`, i.e. for all $`1 \le i \le j \le n` there is some $`g \in G` with $`\rho(g)(i) = j`.
:::

:::definition "group.pgroup" (lean := "IsPGroup, IsPGroup.iff_card")
*$`p`-group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.pgroup))

A *$`p`-group* is a {bpref "group"}[group] whose {bpref "group.order"}[order] is a power of a prime $`p`.  A result of Higman and Sims shows that the number of groups of order $`p^k` is $`p^{(2/27 + o(1))k^3}`, and this can be combined with a result of Pyber to show that, asymptotically, 100% of groups are $`p`-groups.

Depends on: {uses "group"}[] {uses "group.order"}[]
:::

:::definition "group.primary_decomposition" (lean := "AddCommGroup.exists_addEquiv_pi_zmod_isPrimePow, AddCommGroup.exists_equiv_of_addEquiv_pi_zmod, AddCommGroup.primaryAbelianInvariants, AddCommGroup.primaryAbelianInvariants_eq_iff, AddCommGroup.equiv_directSum_zmod_of_finite")
*Primary decomposition of abelian group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.primary_decomposition))

Every finite abelian group $`G` is isomorphic to a direct product of cyclic groups of prime power order, and this decomposition is unique up to reordering.  It is referred to as the *primary decomposition* of $`G`.
:::

:::definition "group.proper_subgroup" (lean := "Subgroup")
*Proper subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.proper_subgroup))

A {bpref "group.subgroup"}[subgroup] of a {bpref "group"}[group] $`G` is *proper* if it is not equal to $`G`.

Depends on: {uses "group"}[] {uses "group.subgroup"}[]
:::

:::definition "group.psl2r" (lean := "Matrix.ProjectiveSpecialLinearGroup, Matrix.SpecialLinearGroup.mem_center_iff")
The *projective special linear group* $`\text{PSL}_2(\mathbb{R})` is defined as the quotient $`\text{PSL}_2(\mathbb{R})=\text{SL}_2(\mathbb{R})/\{\pm I\}`.
:::

:::definition "group.quasisimple" (lean := "IsQuasisimple, isQuasisimple_iff_isSimpleGroup_quotient_center, IsSimpleGroup.isQuasisimple, Group.IsPerfect, IsSimpleGroup")
*Quasisimple group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.quasisimple))

A quasisimple group is a {bpref "group.perfect"}[perfect] group that is a central extension of a {bpref "group.simple"}[simple] group.

Every {bpref "group.abelian"}[nonabelian] simple group is quasisimple, but it is not implied by $`G` being {bpref "group.almost_simple"}[almost simple], as shown by [these examples](https://beta.lmfdb.org/Groups/Abstract/?almost_simple=no&quasisimple=yes).

Depends on: {uses "group.abelian"}[] {uses "group.almost_simple"}[] {uses "group.perfect"}[] {uses "group.simple"}[]
:::

:::definition "group.quotient" (lean := "QuotientGroup.Quotient.group, QuotientGroup.mk'")
*Quotient group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.quotient))

If $`G` is a {bpref "group"}[group] and $`N` is a {bpref "group.subgroup.normal"}[normal subgroup] of $`G`, then the operation on the set of left {bpref "group.coset"}[cosets] of $`N`

$$`(aN)*(bN) = (ab)N`

is well-defined.  The result is a group, called a *quotient group* of $`G` by $`N`.

Depends on: {uses "group"}[] {uses "group.coset"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.quotient_size" (lean := "Subgroup.index, Subgroup.index_eq_card, QuotientGroup.Quotient.group")
*Size of a quotient.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.quotient_size))

The size of the quotient of a finite group by a subgroup is the number of corresponding {bpref "group.coset"}[cosets].  When the subgroup is normal, this number is the order of the {bpref "group.quotient"}[quotient group].

Depends on: {uses "group.coset"}[] {uses "group.quotient"}[]
:::

:::definition "group.radical" (lean := "Subgroup.solvableRadical, Subgroup.isSolvable_solvableRadical, Subgroup.le_solvableRadical, Subgroup.isSolvable_sup")
*Radical of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.radical))

If $`G` is a {bpref "group"}[group], then the *radical* of $`G` is the largest {bpref "group.subgroup.normal"}[normal] {bpref "group.subgroup"}[subgroup] of $`G` which is {bpref "group.solvable"}[solvable].  It is the subgroup generated by all normal subgroups which are solvable.

Depends on: {uses "group"}[] {uses "group.solvable"}[] {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.rational_character_table"
*Rational character table of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.rational_character_table))

The *rational character table* of a finite {bpref "group"}[group] $`G` is a square tabulation of the values of {bpref "group.representation.rational_character"}[irreducible rational characters] on the {bpref "group.division"}[rational conjugacy classes] of $`G`.

The row corresponding to each rational character is marked by its {bpref "group.label_rational_group_char"}[label] and the columns by the {bpref "group.label_conjugacy_class"}[labels] of the corresponding rational conjugacy class.

Depends on: {uses "group"}[] {uses "group.division"}[] {uses "group.label_conjugacy_class"}[] {uses "group.label_rational_group_char"}[] {uses "group.representation.rational_character"}[]
:::

:::definition "group.rational_group" (lean := "Group.IsRational, FDRep.IsRationalCharacter")
*Rational group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.rational_group))

A group $`G` is *rational* if all of its {bpref "group.representation.character"}[characters] are rational valued. (Equivalently every $`g` and $`g^k` are conjugate for $`k` coprime to $`|G|`.) It is an unsolved problem to determine what {bpref "group.cyclic"}[cyclic] groups of order $`p` can be composition factors of rational groups.

Rational groups are sometimes also known as Q-groups, though some authors reserve that term for a stronger property that every representation of G can be realized over $`\mathbb{Q}`. (According to this terminology, $`Q_8` is rational but not a Q-group.)

Depends on: {uses "group.cyclic"}[] {uses "group.representation.character"}[]
:::

:::definition "group.representation.center" (lean := "FDRep.characterCenter, FDRep.mem_characterCenter_iff, FDRep.norm_character_eq_finrank_iff")
*Center of a character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.center))

The *center* of the {bpref "group.representation.character"}[character] $`\chi` of a group $`G` is the subgroup of $`G` given by the set:
$$`\{g \in G : |\chi(g)|=\chi(1)\}.`

Depends on: {uses "group.representation.character"}[]
:::

:::definition "group.representation.character" (lean := "FDRep.character, Representation.character")
*Character of a group representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.character))

If $`G` is a {bpref "group"}[group] and $`\rho:G\to \GL_n(\C)` is a {bpref "group.representation.irrep"}[representation] of $`G`, then the *character* of $`\rho` is the function $`\operatorname{Tr}\circ \rho` where $`\operatorname{Tr}` is the function which takes the trace of a square matrix.  Since $`\operatorname{Tr}(AB) = \operatorname{Tr}(BA)`, the character of $`\rho` is well defined on {bpref "group.conjugacy_class"}[conjugacy classes]; the values $`\rho(g)` for $`g` ranging over the conjugacy classees of $`G` and $`\rho` ranging over all {bpref "group.representation.irrep"}[irreducible] characters of $`G` constitute the {bpref "group.complex_character_table"}[character table] of $`G`.

Depends on: {uses "group"}[] {uses "group.conjugacy_class"}[] {uses "group.representation.irrep"}[]
:::

:::definition "group.representation.complex_char_deg" (lean := "FDRep.character, FDRep.char_one, TauCeti.characterDegree")
*Degree of a character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.complex_char_deg))

The *degree* of a {bpref "group.representation.character"}[character] $`\chi` of a group $`G` is the value given by $`\chi(1)` where $`1` is the trivial element of $`G`.

Depends on: {uses "group.representation.character"}[]
:::

:::definition "group.representation.cyclotomic_n" (lean := "FDRep.characterConductor, FDRep.characterConductor_pos, NumberField.abelianConductor, FDRep.characterField")
*Conductor of the field generated by the character values.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.cyclotomic_n))

Given a complex {bpref "group.representation.character"}[character] $`\chi` of a group $`G`, define $`\Q(\chi)` to be the smallest field containing $`\Q` and the character values of $`\chi`.  This field is abelian and hence has a *conductor*, a positive integer giving the minimum $`n` so that $`\Q(\chi) \subseteq  \Q(\zeta_n)`.

Depends on: {uses "group.representation.character"}[]
:::

:::definition "group.representation.faithful" (lean := "MonoidHom.ker, MonoidHom.ker_eq_bot_iff, FDRep.ker_eq_bot_iff")
*Faithful representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.faithful))

A {bpref "group.representation.irrep"}[representation] $`\rho` is *faithful* if it is injective as a homomorphism to $`\GL(V)`.  In terms of the {bpref "group.representation.character"}[character] $`\chi` of $`\rho`, for representations of finite groups in characteristic $`0`, this will hold precisely when $`\chi(g) = \chi(1)` implies $`g = 1`.

Depends on: {uses "group.representation.character"}[] {uses "group.representation.irrep"}[]
:::

:::definition "group.representation.image" (lean := "MonoidHom.range, Representation.asGroupHom")
*Image of a representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.image))

The *image* of a {bpref "group.representation.irrep"}[representation] of a finite group $`G` is the image of the defining homomorphism $`\rho : G \to \GL(V)` for some vector  space $`V`.

Depends on: {uses "group.representation.irrep"}[]
:::

:::definition "group.representation.irrep" (lean := "Representation, Representation.IsIrreducible, FDRep, TauCeti.SimpleFDRepClasses")
*Complex irreducible representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.irrep))

A *representation* of a finite {bpref "group"}[group] $`G` is a homomorphism $`\rho : G \to \GL(V)` for some vector space $`V`.  A representation is *reducible* if there is some nontrivial subspace $`W \subset V` with $`\rho(g)(W) = W` for all $`g \in G`; otherwise it is *irreducible*.  We say two representations $`\rho : G \to \GL(V)` and $`\rho' : G \to \GL(V')` are equivalent if there is an isomorphism $`\sigma : V \to V'` so that $`\rho'(g) = \sigma^{-1} \rho(g) \sigma` for all $`g \in G`.  Up to equivalence, the complex irreducible representations of a finite group $`G` (also known as *irreps*) are determined by their {bpref "group.representation.character"}[characters], which are recorded in the {bpref "group.complex_character_table"}[character table] of $`G`.

Depends on: {uses "group"}[]
:::

:::definition "group.representation.kernel" (lean := "MonoidHom.ker, FDRep.coe_ker, FDRep.mem_ker_iff_char_eq")
*Kernel of a character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.kernel))

The *kernel* of the {bpref "group.representation.character"}[character] $`\chi` of a group $`G` is the subgroup of $`G` given by the set:
$$`\ker(\chi)=\{g \in G : \chi(g)=\chi(1)\}.`

Depends on: {uses "group.representation.character"}[]
:::

:::definition "group.representation.min_perm_rep"
*Minimum permutation representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.min_perm_rep))

The smallest permutation representation containing the given {bpref "group.representation.character"}[character] $`\chi`, as a {bpref "gg.tnumber"}[transitive group].

Depends on: {uses "gg.tnumber"}[] {uses "group.representation.character"}[]
:::

:::definition "group.representation.rational_character"
*Rational character.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.rational_character))

A *rational character* of a finite {bpref "group"}[group] $`G` is {bpref "group.representation.character"}[complex character] taking values in $`\Q`. Such a character can be obtained by taking the sum of Galois conjugates of an irreducible complex character, and we will refer to these as *irreducible rational characters* even though they are not irreducible as complex characters.  The irreducible rational characters form a $`\Q`-basis for the $`\Q`-vector space of rational characters.

Note that the representation corresponding to a rational character may not take values in $`\GL_n(\Q)` even though the character takes values in $`\Q` (the difference between the field of character values and the field in which matrix entries lie is measured by the Schur index).

The value taken by a rational character is constant on each {bpref "group.division"}[rational conjugacy classes].

Depends on: {uses "group"}[] {uses "group.division"}[] {uses "group.representation.character"}[]
:::

:::definition "group.representation.schur_index" (lean := "FDRep.schurIndex, FDRep.IsRealizedOver, FDRep.characterField, FDRep.schurIndex_pos, FDRep.exists_relfinrank_eq_schurIndex")
*Schur index.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.schur_index))

Given a group $`G`, a field $`K \subseteq \mathbb{C}` with $`F` a subfield of $`K`, and  a character $`\chi` of an irreducible $`KG`-module $`V`, define the field extension $`F(\chi)` of $`F` formed by adjoining to $`F` all the values the character takes on:

$$`F(\chi)=F\left(\chi(g) :  g \in G\right).`

The *Schur index* of $`\chi` is the minimum of all indices $`[E:F(\chi)]` where E varies over all field $`F(\chi) \subseteq E \subseteq K` so that there is an $`EG`-module $`W` with $`V\cong K \otimes_E W`.
:::

:::definition "group.representation.type" (lean := "Representation.IsQuaternionicStructure, Representation.IsRealizableOverReal, TauCeti.Representation.frobeniusSchurIndicator")
*Type of a complex group representation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.representation.type))

Let $`\rho:G\to\GL_n(\C)` be an irreducible complex {bpref "group"}[group] representation.  Then $`\rho` is one of three *types*:

1. *Real* if $`\rho` is conjugate to a representation $`G\to \GL_n(\R)`
1. *Complex* if some {bpref "group.representation.character"}[character] value $`\textrm{Tr}(\rho(g))` is not contained in $`\R`
1. *Quaternionic (or Symplectic)* if the character values are all real but the representation is not conjugate to a real representation.

The type of the representation can be computed via its {bpref "artin.frobenius_schur_indicator"}[Frobenius-Schur indicator].

Depends on: {uses "group"}[] {uses "group.representation.character"}[]
:::

:::definition "group.schur_multiplier" (lean := "groupHomology, Rep.trivial, TauCeti.schurMultiplier")
*Schur multiplier.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.schur_multiplier))

If $`G` is a finite group then the *Schur multiplier* of $`G` is the homology group $`H_2(G, \Z)`.  It is the maximal kernel of a {bpref "group.stem_extension"}[stem extension] of $`G`. In the data, the Schur multiplier is represented as a list of invariant factors; e.g., '\[2,4,12\]' corresponds to the abelian group $`C_2 \times C_4 \times C_{12}`.
:::

:::definition "group.semi_dihedral" (lean := "SemiDihedralGroup, SemiDihedralGroup.card, ZMod.involutionMulAut")
*Semi-dihedral group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.semi_dihedral))

The *semi-dihedral group* $`\SD_{2^k}` is one of the four non-abelian groups of {bpref "group.order"}[order] $`2^k` containing a cyclic subgroup of index 2 (the other three being the {bpref "group.dihedral"}[dihedral group], the {bpref "group.generalized_quaternion"}[(generalized) quaternion group], and the {bpref "group.other_dihedral"}[other-dihedral group]).  It has the group presentation:

$$`\SD_{2^k} = \langle r,s\mid r^{2^{k-1}}=s^{2}=1,\ srs=r^{2^{k-2}-1} \rangle.`

It can also be given as the {bpref "group.semidirect_product"}[semidirect product] $`C_{2^{k-1}} \rtimes C_2` where the action of $`C_2` on $`C_{2^{k-1}}` is given by $`x \mapsto x^{2^{k-2}-1}`.

Depends on: {uses "group.dihedral"}[] {uses "group.generalized_quaternion"}[] {uses "group.order"}[] {uses "group.semidirect_product"}[]
:::

:::definition "group.semidirect_product" (lean := "SemidirectProduct, SemidirectProduct.mulEquivProd, SemidirectProduct.mulEquivSubgroup, GroupExtension.Splitting, Subgroup.IsComplement'")
*Semidirect product of groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.semidirect_product))

Suppose $`H` and $`N` are {bpref "group"}[groups] with operations $`*_H` and $`*_N` and $`\phi:H\to \Aut(N)` is a {bpref "group.homomorphism"}[homomorphism] to the {bpref "group.automorphism"}[automorphism] group of $`N`. Then the set $`N\times H` with the operation

$$`(n_1, h_1)*(n_2, h_2) = (n_1*_N \phi(h_1)(n_2),  h_1 *_H h_2)`

is a group called a *semidirect product* of $`H` and $`N` denoted $`N:H` or $`N\rtimes H`.  If $`\phi` is the trivial homomorphism, then the resulting group is the {bpref "group.direct_product"}[direct product] $`N\times H`, so it is a *trivial semidirect product*.

The group $`N:H` has subgroups

$$`N' = \{(n,e)\mid n\in N\} \cong N`

and

$$`H' = \{(e,h) \mid h\in H\} \cong H`

satisfying $`N'\cap H'=\{(e,e)\}`, $`N'H'=N:H`, and $`N'` is a {bpref "group.subgroup.normal"}[normal] {bpref "group.subgroup"}[subgroup] of $`N:H`.

Conversely, if a group $`G` has a normal subgroup $`N` and a subgroup $`H` such that $`N\cap H=\{e\}` such that $`N\cap H=\{e\}` and $`NH=G`, then $`G\cong N:H` for some function $`\phi`.  We call $`N` a *semidirect factor* of $`G` in this case.

The semidirect product of $`N` and $`H` fits into a sequence

$$`1 \to N \to N \rtimes H \to H \to 1,`

and is distinguished by the existence of a homomorphism $`H \to N \rtimes H` with image $`H'` that splits the projection $`N \rtimes H \to H`.  We refer to such an {bpref "group.nonsplit_product"}[extension] as *split*, in contrast to other  *non-split* extensions.

Depends on: {uses "group"}[] {uses "group.automorphism"}[] {uses "group.direct_product"}[] {uses "group.homomorphism"}[] {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.simple" (lean := "IsSimpleGroup")
*Simple groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.simple))

A non-trivial {bpref "group"}[group] $`G` is *simple* if its only {bpref "group.subgroup.normal"}[normal] subgroups are the trivial group and $`G` itself.

Finite simple groups are building blocks for all finite groups, via extensions, and they are divided into {bpref "group.cyclic"}[cyclic] groups of prime {bpref "group.order"}[order] and the {bpref "group.abelian"}[nonabelian] simple groups. For small orders, nonabelian simple groups they are all alternating or linear.

Depends on: {uses "group"}[] {uses "group.abelian"}[] {uses "group.cyclic"}[] {uses "group.order"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.size_conjugacy_class" (lean := "ConjClasses.carrier, ConjClasses.card_carrier")
*Size of a conjugacy class..* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.size_conjugacy_class))

The *size* of a {bpref "group.conjugacy_class"}[conjugacy class] of a finite group is the cardinality of the set of elements conjugate to each other.

By the Orbit-Stabilizer Theorem, the size of a conjugacy class divides the {bpref "group.order"}[order] of the group. Since conjugacy classes partition a group, the sum of the sizes of the conjugacy classes equals the size of the group.

A conjugacy class is of size $`1` if and only if the element is in the {bpref "group.center"}[center] of the group.

Depends on: {uses "group.center"}[] {uses "group.conjugacy_class"}[] {uses "group.order"}[]
:::

:::definition "group.sl2z.fundamental_domain" (lean := "ModularGroup.isFundamentalDomain_fd, ModularGroup.fd, ModularGroup.IsFundamentalDomain, UpperHalfPlane.Completed")
*Fundamental domain of $`\SL(2,\Z)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sl2z.fundamental_domain))

Let $`\mathfrak{F}` be the following set:

$$`\mathfrak{F}=\{z\in\mathcal{H} : |z|\geq1 \text{ and
} |\Re(z)|\leq1/2\}\cup\{\infty\}.`

Then $`\mathfrak{F}` is a {bpref "group.fuchsian.fundamental_domain"}[fundamental domain] for the action of $`\Gamma` on $`\mathcal{H}`.

Depends on: {uses "group.fuchsian.fundamental_domain"}[]
:::

:::definition "group.sl2z.genus_subgroup"
*Genus of a subgroup of the modular group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sl2z.genus_subgroup))

The *genus* of a finite index subgroup $`G` of the {bpref "group.sl2z"}[modular group] is the genus of the corresponding compact {bpref "ag.riemann_surface"}[Riemann surface] arising from the compactification of $`G\backslash\mathcal{H},` which is obtained by adjoining the {bpref "group.fuchsian.cusps"}[cusps] of $`G`.

Here $`\mathcal{H}` denotes the complex upper halfplane  on which $`G` acts by linear fractional transformations, and $`G\backslash \mathcal{H}` denotes the quotient of $`\mathcal{H}` by this action (points of $`G\backslash\mathcal{H}` correspond to $`G`-orbits in $`\mathcal{H}`).

Depends on: {uses "ag.riemann_surface"}[] {uses "group.fuchsian.cusps"}[] {uses "group.sl2z"}[]
:::

:::definition "group.sl2z.subgroup.gamma0n" (lean := "CongruenceSubgroup.Gamma0, CongruenceSubgroup.Gamma0_mem")
The group $`\Gamma_0(N)` is the subgroup of $`\textrm{SL}(2,\mathbb{Z})` that consists of matrices whose lower-left entry is 0 modulo $`N`.  That is,

$$`\Gamma_0(N) = \left\lbrace \left .\begin{pmatrix} a & b \\ c & d \end{pmatrix}\in \textrm{SL}(2,\mathbb{Z})\ \right|\  c\equiv 0 \bmod N \right\rbrace.`
:::

:::definition "group.sl2z.subgroup.gamma1n" (lean := "CongruenceSubgroup.Gamma1, CongruenceSubgroup.Gamma1_mem")
The group $`\Gamma_1(N)` is the subgroup of $`\textrm{SL}(2,\mathbb{Z})` defined
by the congruences:

$$`\Gamma_1(N) = \left\lbrace \left .\begin{pmatrix} a & b \\ c & d \end{pmatrix}\in \textrm{SL}(2,\mathbb{Z})\ \right| \ c\equiv 0,\ a \equiv d\equiv 1 \bmod N \right\rbrace.`
:::

:::definition "group.sl2z.subgroup.gamman" (lean := "CongruenceSubgroup.Gamma, CongruenceSubgroup.Gamma_mem")
The group $`\Gamma(N)` is the subgroup of {bpref "group.sl2z"}[$`\SL(2,\mathbb{Z})`]  that consists of matrices congruent to the identity matrix modulo $`N`.  That is,

$$`\Gamma(N)=\left\{ \begin{pmatrix} a&b\\ c&d \end{pmatrix}\in\textrm{SL}(2,\mathbb{Z})\ \Bigg|\  \begin{pmatrix} a & b \\ c & d \end{pmatrix}\equiv \begin{pmatrix} 1&0\\ 0&1 \end{pmatrix} \bmod N \right\} .`

Depends on: {uses "group.sl2z"}[]
:::

:::definition "group.small_group_label"
*Labels for the small group database in GAP and Magma.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.small_group_label))

The computer algebra systems GAP and Magma both include a database of small groups that includes all groups of order up to 2000, except for groups of order 1024. Groups in this database are identified by an ordered pair $`[n,d]` where $`n` is the order of the group and $`d` is a positive integer that distinguishes the group from others of the same order (the value of $`d` is the same in both GAP and Magma).

In both systems, the command "SmallGroup($`n`,$`d`)" will return an explicit representation of the group in terms of generators and relations.

Magma also associates a descriptive name to each small group.  For example, the command "GroupName(SmallGroup(24,3))" returns the string "SL(2,3)".
:::

:::definition "group.socle" (lean := "Subgroup.socle, Subgroup.le_socle")
*Socle of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.socle))

If $`G` is a {bpref "group"}[group], the *socle* of $`G`, denoted $`\mathrm{soc}(G)`, is the subgroup generated by all of the minimal {bpref "group.subgroup.normal"}[normal] subgroups of $`G`.

That is, it is the join of subgroups $`N` which are normal in $`G` such that $`N\neq \langle e \rangle` and if $`H` is a normal {bpref "group.subgroup"}[subgroup] of $`G` with $`H\subseteq N`, then $`H=N` or $`H=\langle e \rangle`.  If there are no such subgroups $`N`, then the socle of $`G` is defined to be $`\langle e\rangle`.

If $`G` is a finite {bpref "group.solvable"}[solvable] group, then $`\mathrm{soc}(G)` is isomorphic to a product of some number of {bpref "group.cyclic"}[cyclic] groups of prime {bpref "group.order"}[order].

Depends on: {uses "group"}[] {uses "group.cyclic"}[] {uses "group.order"}[] {uses "group.solvable"}[] {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.solvable" (lean := "Group.IsSolvable, derivedSeries")
*Solvable group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.solvable))

A {bpref "group"}[group] $`G` is *solvable* if there exists a chain of subgroups

$$`\langle e\rangle =H_0\leq H_1 \leq H_2 \leq \cdots \leq H_n=G`

such that for all $`i< n`, $`H_i` is a normal subgroup of $`H_{i+1}` (i.e., it is a {bpref "group.normal_series"}[subnormal series]) and each quotient $`H_{i+1}/H_i` is {bpref "group.abelian"}[abelian].

Depends on: {uses "group"}[] {uses "group.abelian"}[] {uses "group.normal_series"}[]
:::

:::definition "group.sp2gr" (lean := "Matrix.symplecticGroup, Matrix.J, SymplecticGroup.mem_iff', SymplecticGroup.det_eq_one")
*Symplectic group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sp2gr))

The real symplectic group of degree $`g` denoted by $`\Sp(2g,\R)` is defined as

$$`\Sp(2g,\R)
=\left\{
\gamma=\left(\begin{matrix} a & b\\ c & d\end{matrix}\right)\in\GL(2g,\R):
\, \gamma^t J \gamma=J\right\},`

where
$`J=\left(\begin{matrix}0 & 1_g\\ -1_g & 0\end{matrix}\right)`
with $`1_g` is the identity matrix of size $`g`.

By using the following two properties of the Pfaffian:
$`\text{Pf}(\gamma^t J \gamma)=\text{Pf}(J)` and
$`\text{Pf}(\gamma^t J \gamma)=\det(\gamma)\text{Pf}(J)`, we see that
$`\Sp(2g,\R)` is a subgroup of $`\SL(2g,\R)`.

The *integral symplectic group* $`\Gamma_g=\Sp(2g,\Z)`, also called the Siegel modular group,
is defined as  $`\Gamma_g=\Sp(2g,\R)\cap{\rm M}(2g,\Z)`. Clearly $`\Gamma_1=\SL(2,\Z)`.
:::

:::definition "group.sp2gr.gamma0" (lean := "SymplecticGroup.Gamma0, SymplecticGroup.mem_Gamma0_iff")
*Subgroup $`\Gamma_0(N)` of $`\Sp(2g,\Z)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sp2gr.gamma0))

The group $`\Gamma_0(N)` in degree $`g` is the subgroup of the integral
{bpref "group.sp2gr"}[symplectic group]
$`\Sp(2g,\Z)`, defined by

$$`\Gamma_0(N)=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in \Sp(2g,\Z)
:
c \equiv 0 \bmod N
\right\}.`

The group $`\Gamma_0(N)` is sometimes called the Hecke
congruence subgroup of level $`N`.

For $`g=1`, it is the subgroup
{bpref "group.sl2z.subgroup.gamma0n"}[$`\Gamma_0(N)`] of
$`\SL(2,\Z)`.

Depends on: {uses "group.sl2z.subgroup.gamma0n"}[] {uses "group.sp2gr"}[]
:::

:::definition "group.sp2gr.gamma1"
*Subgroup Gamma1(N) of $`\Sp(2g,\Z)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sp2gr.gamma1))

The subgroup $`\Gamma_1(N)` of the integral
{bpref "group.sp2gr"}[symplectic group]
$`\Sp(2g,\Z)`
is defined by:

$$`\Gamma_1(N)=
\left\{
\begin{pmatrix} a & b \\ c & d \end{pmatrix}\in \Sp(2g,\Z)\ \vert
\begin{pmatrix} a & b \\ c & d \end{pmatrix}\equiv
\begin{pmatrix} 1_g & * \\ 0 & 1_g \end{pmatrix}
 \bmod N
\right\}.`

For $`g=1`, it is the subgroup
{bpref "group.sl2z.subgroup.gamma1n"}[$`\Gamma_1(N)`] of
$`\SL(2,\Z)`.

Depends on: {uses "group.sl2z.subgroup.gamma1n"}[] {uses "group.sp2gr"}[]
:::

:::definition "group.sp2gr.ppal.congruence" (lean := "SymplecticGroup.Gamma, SymplecticGroup.mem_Gamma_iff")
*Subgroup $`\Gamma(N)` of $`\Sp(2g,\Z)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sp2gr.ppal.congruence))

The principal congruence subgroup of level $`N`, $`\Gamma(N)`,
of the integral {bpref "group.sp2gr"}[symplectic group]
$`\Sp(2g,\Z)`
is the subgroup of $`\Sp(2g,\Z)` that consists of matrices congruent to the identity matrix modulo $`N`:

$$`\Gamma(N)=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in \Sp(2g,{\Z})
:
\begin{pmatrix}a&b\\c&d\end{pmatrix} \equiv
\begin{pmatrix}1_g&0\\0&1_g\end{pmatrix}
 \bmod N
\right\}`

where $`1_g` stands for the identity matrix of size $`g`.
For $`g=1`, it is the subgroup
{bpref "group.sl2z.subgroup.gamman"}[$`\Gamma(N)`] of
$`\SL(2,\Z)`.

Depends on: {uses "group.sl2z.subgroup.gamman"}[] {uses "group.sp2gr"}[]
:::

:::definition "group.sp2gr.subgroup.congn" (lean := "SymplecticGroup.IsCongruenceOfLevel, SymplecticGroup.isCongruenceOfLevel_Gamma, SymplecticGroup.isCongruenceOfLevel_Gamma0")
*Congruence subgroup of level $`N` of $`\Sp(2g,\Z)`.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sp2gr.subgroup.congn))

A subgroup of $`\Sp(2g,\Q)`
is called a congruence subgroup of level $`N`
if it contains the {bpref "group.sp2gr.ppal.congruence"}[principal congruence subgroup] $`\Gamma(N)`.

Examples of such subgroups are:
<ul>
<li>
the principal congruence subgroup
{bpref "group.sp2gr.ppal.congruence"}[$`\Gamma(N)`];
</li>
<li>
Hecke (or Siegel parabolic) subgroup
{bpref "group.sp2gr.gamma0"}[$`\Gamma_0(N)`];
</li>
<li>
the subgroup
{bpref "group.sp2gr.gamma1"}[$`\Gamma_1(N)`].
</li>
</ul>

Depends on: {uses "group.sp2gr.gamma0"}[] {uses "group.sp2gr.gamma1"}[] {uses "group.sp2gr.ppal.congruence"}[]
:::

:::definition "group.special_linear" (lean := "Matrix.SpecialLinearGroup, Matrix.ProjectiveSpecialLinearGroup, Matrix.SpecialLinearGroup.mem_center_iff, GaloisField")
*Special linear group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.special_linear))

The *special linear group* $`\SL(n,q)` is the group of $`n \times n` matrices with determinant 1 with entries in the {bpref "ring.field"}[field] $`\F_q` (the finite field with $`q` elements). It has {bpref "group.order"}[order] $`|\GL(n, q)|/(q-1) =  \frac{1}{q-1} \prod_{k=0}^{n-1} (q^n - q^k)`.

The *projective special linear group* $`\PSL(n, q)` is the {bpref "group.quotient"}[quotient] of $`\SL(n, q)` with the group of $`n \times n` scalar matrices over $`\F_q` with determinant 1.  If either $`n > 2` or $`q > 3`, then $`\PSL(n, q)` is a {bpref "group.simple"}[simple] group.

Depends on: {uses "group.order"}[] {uses "group.quotient"}[] {uses "group.simple"}[] {uses "ring.field"}[]
:::

:::definition "group.spinor_norm" (lean := "CliffordAlgebra.orthogonalSpinorNorm, CliffordAlgebra.spinorNorm, TauCeti.QuadraticMap.specialOrthogonalGroup")
*Spinor norm.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.spinor_norm))

The {bpref "group.orthogonal"}[orthogonal group] $`\GO(n,q)` is the subgroup of $`\GL(n,q)` fixing a particular quadratic form $`Q`, and has the subgroup $`\SO(n,q)` of all matrices with determinant $`1`. One can associate to $`Q` a {bpref "alg.symmetric_bilinear_form"}[symmetric bilinear form] $`f \colon V^2 \to \F_q` (for $`V = \F_q^n`) by writing $`f(x,y) = Q(x+y) -Q(x) - Q(y)`. Then the reflection in a vector $`v \in V` such that $`Q(v) \neq 0` is the element of $`\SO(n,q)` that acts on $`V` by

$$`x \mapsto x - \frac{f(x,v)}{Q(v)} v.`

We can write any $`g \in \SO(n,q)` as a product of reflections: $`g = r_1 \cdot \ldots \cdot r_n`.

The *spinor norm* is the map $`\SO(n,q) \to (\F_q^\times) / (\F_q^\times)^2` that sends $`g` to the image of $`Q(r_1) \cdot \ldots \cdot Q(r_n)` in the quotient.

Depends on: {uses "alg.symmetric_bilinear_form"}[] {uses "group.orthogonal"}[]
:::

:::definition "group.sporadic" (lean := "TauCeti.ClassificationStatement, TauCeti.SporadicName, TauCeti.SporadicName.Group, TauCeti.SporadicName.presentation")
*Sporadic groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.sporadic))

By the classification of finite {bpref "group.simple"}[simple] groups, we know that every finite simple group is either {bpref "group.cyclic"}[cyclic] of prime {bpref "group.order"}[order], an {bpref "group.alternating"}[alternating] group, a member of one of 16 infinite families of simple groups of Lie type, or one of 26 exceptions called *sporadic groups*.

The 26 sporadic groups are:

- The Mathieu groups $`M_{11}`, $`M_{12}`, $`M_{22}`, $`M_{23}`, and $`M_{24}`.

- The Janko groups $`J_1`, $`J_2`, $`J_3`, and $`J_4`.

- The Conway groups $`\Co_1`, $`\Co_2`, and $`\Co_3`.

- The Fischer groups $`\text{Fi}_{22}`, $`\text{Fi}_{23}`, and $`\text{Fi}_{24}'`.

- The Higman-Sims groups $`\HS`.

- The McLaughlin group $`\McL`.

- The Held group $`\He`.

- The Rudvalis group $`\Ru`.

- The Suzuki group $`\text{Suz}`.

- The O'Nan group $`\text{O'N}`.

- The Harada-Norton group $`\text{HN}`.

- The Lyons group $`\text{Ly}`.

- The Thompson group $`\text{Th}`.

- The Baby Monster group $`\text{B}`.

- The Fischer-Griess Monster group $`\text{M}`.

The smallest sporadic group is the Mathieu group $`M_{11}` of order $`7920 = 2^4 \cdot 3^2 \cdot 5 \cdot 11`, and the largest sporadic group is the Fischer–Griess Monster group $`M` of order $`808 017 424 794 512 875 886 459 904 961 710 757 005 754 368 000 000 000 = 2^{46} \cdot 3^{20} \cdot 5^9 \cdot 7^6 \cdot 11^2 \cdot 13^3 \cdot 17 \cdot 19 \cdot 23 \cdot 29 \cdot 31 \cdot 41 \cdot 47 \cdot 59 \cdot 71`.

Depends on: {uses "group.alternating"}[] {uses "group.cyclic"}[] {uses "group.order"}[] {uses "group.simple"}[]
:::

:::definition "group.stem_extension" (lean := "GroupExtension.IsStem, Subgroup.IsStem")
*Stem extension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.stem_extension))

A short exact sequence of groups

$$`1 \to K \to C \to G \to 1`

is a *stem extension* if $`K` is contained in both the {bpref "group.center"}[center] and the {bpref "group.commutator_subgroup"}[commutator] of $`G` (we also refer to $`K` as a *stem subgroup* of $`C`).  For fixed $`G`, the size of $`C` is bounded.  For any extension with $`C` of maximal size, the kernel $`K` is isomorphic to the {bpref "group.schur_multiplier"}[Schur multiplier] of $`G`.  In general, $`C` is only determined up to {bpref "group.isoclinism"}[isoclinism] in such an extension, but if $`G` is {bpref "group.perfect"}[perfect] then $`C` is determined up to isomorphism.

Depends on: {uses "group.center"}[] {uses "group.commutator_subgroup"}[] {uses "group.isoclinism"}[] {uses "group.perfect"}[] {uses "group.schur_multiplier"}[]
:::

:::definition "group.stem_group" (lean := "Group.IsStemGroup")
*Stem group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.stem_group))

A *stem group* is a {bpref "group"}[group] $`G` whose {bpref "group.center"}[center] is contained in its {bpref "group.commutator_subgroup"}[commutator subgroup].  Any group is {bpref "group.isoclinism"}[isoclinic] to a stem group (not necessarily unique), and the order of a stem group divides the order of every other group in its isoclinism class.

Depends on: {uses "group"}[] {uses "group.center"}[] {uses "group.commutator_subgroup"}[] {uses "group.isoclinism"}[]
:::

:::definition "group.subgroup.centralizer" (lean := "Subgroup.centralizer")
*Centralizer of a subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.centralizer))

If $`H` is a {bpref "group.subgroup"}[subgroup] of a {bpref "group"}[group] $`G`, then the *centralizer* of $`H` is the subgroup

$$`C_G(H) = \{ g\in G\mid gh=hg \text{ for all } h\in H\}.`

Depends on: {uses "group"}[] {uses "group.subgroup"}[]
:::

:::definition "group.subgroup.complement" (lean := "Subgroup.IsComplement', Subgroup.isComplement'_of_disjoint_and_mul_eq_univ, SemidirectProduct.mulEquivSubgroup, GroupExtension.Splitting")
*Complement.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.complement))

If $`H \trianglelefteq G` is a {bpref "group.subgroup.normal"}[normal] {bpref "group.subgroup"}[subgroup], a *complement* of $`H` is a subgroup $`K \subseteq G` with $`\lvert H \cap K \rvert = 1` and $`HK=G` where

$$`HK = \{ hk \mid h\in H \text{ and } k\in K\}.`

In order for a complement to exist, the sequence

$$`1 \to H \to G \to G/H \to 1`

must {bpref "group.nonsplit_product"}[split], in which case the complements are precisely the images of the possible splittings $`G/H \to G`.  All complements are isomorphic to $`G/H`, and if $`K` is any complement then $`G` can be described as the internal {bpref "group.semidirect_product"}[semidirect product] $`H \rtimes K`.

Depends on: {uses "group.nonsplit_product"}[] {uses "group.semidirect_product"}[] {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.subgroup.diagram" (lean := "SimpleGraph.hasse, CovBy")
*Subgroup diagram.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.diagram))

If $`G` is a {bpref "group"}[group], its *subgroup diagram* is the {bpref "combin.hasse_diagram"}[Hasse diagram] for the set of subgroups of $`G` under inclusion.  Generally, subgroups of the same {bpref "group.order"}[order] are drawn at the same height in the diagram.

Depends on: {uses "combin.hasse_diagram"}[] {uses "group"}[] {uses "group.order"}[]
:::

:::definition "group.subgroup.hall" (lean := "Subgroup.index, Sylow.card_coprime_index")
*Hall subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.hall))

If $`H` is a {bpref "group.subgroup"}[subgroup] of a finite {bpref "group"}[group] $`G`, then $`H` is a *Hall subgroup* if the {bpref "group.order"}[order] of $`H` is relatively prime to its {bpref "group.subgroup.index"}[index].

Depends on: {uses "group"}[] {uses "group.order"}[] {uses "group.subgroup"}[] {uses "group.subgroup.index"}[]
:::

:::definition "group.subgroup.normal_closure" (lean := "Subgroup.normalClosure")
*Normal closure of a subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.normal_closure))

If $`H` is a {bpref "group.subgroup"}[subgroup] of a group $`G`, the *normal closure* of $`H` is the smallest {bpref "group.subgroup.normal"}[normal subgroup] of $`G` containing $`H`.  Alternatively, it is the subgroup generated by the set

$$`\bigcup_{g\in G} gHg^{-1}.`

Depends on: {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.subgroup.normalizer" (lean := "Subgroup.normalizer")
*Normalizer of a subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.normalizer))

If $`H` is a {bpref "group.subgroup"}[subgroup] of a {bpref "group"}[group] $`G`, then the *normalizer* of $`H` is the subgroup

$$`N_G(H) = \{ g\in G\mid gHg^{-1} = H\}.`

Equivalently, $`N_G(H)` is the largest subgroup of $`G` containing $`H` in which $`H` is {bpref "group.subgroup.normal"}[normal].

Depends on: {uses "group"}[] {uses "group.subgroup"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.subgroup.projective_image" (lean := "Subgroup.map, QuotientGroup.mk', Subgroup.center")
*Projective image of a subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup.projective_image))

If $`H \subset G` is a subgroup, the *projective image* of $`H` is the image of $`H` in the {bpref "group.center"}[central] {bpref "group.quotient"}[quotient] $`G / Z(G)`.

Depends on: {uses "group.center"}[] {uses "group.quotient"}[]
:::

:::definition "group.subgroup_label"
*Subgroup labels.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.subgroup_label))

The full label of a {bpref "group.subgroup"}[subgroup] is of the form $`\mathtt{N.i.m.a}` or $`\mathtt{N.i.m.a.j}`.  In either case, $`\mathtt{N.i}` is the {bpref "group.label"}[label] of the {bpref "group.ambient"}[ambient group], $`\mathtt{m}` is the {bpref "group.subgroup.index"}[index] of the subgroup in the ambient group, $`\mathtt{a}` distinguishes subgroups up to {bpref "group.automorphism"}[automorphism] and $`\mathtt{j}` distinguishes subgroups up to conjugacy.  Both $`\mathtt{a}` and $`\mathtt{j}` take the form of a sequence of letters followed by an ordinal. The letters are a base 26 (a=0, z=25) encoding of the ordering up to {bpref "group.gassmann_equivalence"}[Gassmann-equivalence], and the integer following distinguishes groups in the same Gassmann class.  (For details on how we label Gassmann classes and order subgroups within a Gassmann class, see Computing labels of subgroups.) For some ambient groups, we only compute subgroups up to automorphism (in which case the first form is used, omitting the $`\mathtt{j}`.

When the ambient group is clear from context, sometimes the short label $`\mathtt{m.a}` or $`\mathtt{m.a.j}` is used instead.

Depends on: {uses "group.ambient"}[] {uses "group.automorphism"}[] {uses "group.gassmann_equivalence"}[] {uses "group.label"}[] {uses "group.subgroup"}[] {uses "group.subgroup.index"}[]
:::

:::definition "group.supersolvable" (lean := "Group.IsSupersolvable, Subgroup.NormalSeries, Subgroup.SubnormalSeries.IsPolycyclic")
*Supersolvable group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.supersolvable))

A group is *supersolvable* if there are nested {bpref "group.subgroup.normal"}[normal] subgroups $`N_i\lhd G`

$$`{1}=N_0 < N_1 < N_2 < \ldots < N_k = G`

with all successive quotients $`N_{i+1}/N_i` cyclic. It is stronger than requiring $`N_{i+1}/N_i` to be abelian (because $`N_i \lhd G`), so not all {bpref "group.solvable"}[solvable] groups are supersolvable. The smallest solvable groups that are not supersolvable are $`A_4`, $`S_4`, SL$`_2(\mathbb{F}_3)` and $`C_2\times A_4`. All supersolvable groups are {bpref "group.monomial"}[monomial], and all {bpref "group.abelian"}[abelian], {bpref "group.nilpotent"}[nilpotent], {bpref "group.metacyclic"}[metacyclic] groups, Z-groups and groups of square-free order are supersolvable. Supersolvable groups are closed under subgroups and quotients (but not extensions), and a group is supersolvable if and only if each of its maximal subgroups has prime index.

While every nilpotent group is supersolvable, the converse does not hold as shown by [these examples](https://beta.lmfdb.org/Groups/Abstract/?nilpotent=no&supersolvable=yes).  Similarly, [these examples](https://beta.lmfdb.org/Groups/Abstract/?metacyclic=no&supersolvable=yes) show that not every supersolvable group is metacyclic.

Depends on: {uses "group.abelian"}[] {uses "group.nilpotent"}[] {uses "group.solvable"}[] {uses "group.subgroup.normal"}[]
:::

:::definition "group.symmetric" (lean := "Equiv.Perm, Fintype.card_perm")
*Symmetric group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.symmetric))

The *symmetric group* is the group $`S_n` of bijections from $`n` element sets to themselves (called permutations), which is of order $`n!`. This group is {bpref "group.solvable"}[solvable] for $`n\leq 4` and {bpref "group.almost_simple"}[almost simple] since $`S_n=A_n\rtimes C_2` for $`n\geq 5`.

Depends on: {uses "group.almost_simple"}[] {uses "group.solvable"}[]
:::

:::definition "group.symplectic" (lean := "Matrix.symplecticGroup, Matrix.J, Subgroup.center")
*Symplectic group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.symplectic))

The *symplectic group* $`\Sp(2n, q)` is the group of invertible $`2n \times 2n` matrices $`M` with entries in $`\F_q`, which satisfy the condition that $`M^T \Omega M = \Omega`, for $`\Omega` is any fixed invertible {bpref "alg.matrix.skew_symmetric"}[skew-symmetric matrix] over $`\F_q`.   For example, $`\Omega` can be taken to be the block matrix

$$`\Omega = \begin{pmatrix} 0 & I_n \\ -I_n & 0 \end{pmatrix},`

where $`I_n` is the $`n \times n` identity matrix.

The *projective symplectic group* $`\PSp(2n, q)` is the {bpref "group.quotient"}[quotient] of $`\Sp(2n, q)` by the scalar matrices in $`\Sp(2n, q)` (equivalently, $`\PSp(2n, q)` is the quotient of $`\Sp(2n, q)` by its {bpref "group.center"}[center]).

(see , pages x-xi)

Depends on: {uses "group.center"}[] {uses "group.quotient"}[]
:::

:::definition "group.transitive_degree" (lean := "Group.minTransitiveDegree, Group.exists_injective_isTransitive_minTransitiveDegree, Group.minTransitiveDegree_le, Group.minPermDegree_le_minTransitiveDegree")
*Transitive degree.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.transitive_degree))

Given a finite {bpref "group"}[group] $`G`, we call the minimal degree of a faithful transitive {bpref "group.permutation_representation"}[permutation representation] of $`G` the *minimal transitive degree* of $`G`.

Equivalently, it is the smallest positive integer $`n` such that $`S_n` has a transitive subgroup isomorphic to $`G`.

This can be computed as the minimal {bpref "group.subgroup.index"}[index] of a {bpref "group.subgroup"}[subgroup] with trivial {bpref "group.core"}[core].

Depends on: {uses "group"}[] {uses "group.core"}[] {uses "group.permutation_representation"}[] {uses "group.subgroup"}[] {uses "group.subgroup.index"}[]
:::

:::definition "group.triangle_group" (lean := "TauCeti.TriangleGroup")
*Triangle group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.triangle_group))

Given positive integers $`l, m, n \ge 2`, the *triangle group* $`\Delta(l, m, n)` is given by the presentation $`\langle a, b, c | a^2 = b^2 = c^2 = (ab)^l = (bc)^m = (ca)^n \rangle`.  It is a Coxeter group, and forms the symmetry group of a tiling of either the sphere (if $`\frac1l + \frac1m + \frac1n > 1`), the Euclidean plane (if $`\frac1l + \frac1m + \frac1n = 1`) or the hyperbolic plane (if $`\frac1l + \frac1m + \frac1n < 1`) by triangles with angles $`\frac{\pi}l, \frac{\pi}m` and $`\frac{\pi}n`.

The *Von Dyck group* $`D(l, m, n)` is the subgroup of index $`2` generated by $`x = ab, y = bc` and $`z = ca`.  It has presentation $`\langle x, y | x^l = y^m = (xy)^n \rangle` and can be interpreted as the orientation preserving elements of the triangle group.
:::

:::definition "group.trivial_subgroup" (lean := "Subgroup.mem_bot")
*Trivial subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.trivial_subgroup))

If $`G` is a {bpref "group"}[group] with {bpref "alg.binary_operation.identity"}[identity] element $`e`, then $`\{e\}` is a {bpref "group.subgroup"}[subgroup] isomorphic to the trivial group.  It is the *trivial subgroup* of $`G`, and all other subgroups are *non-trivial*.

Depends on: {uses "alg.binary_operation.identity"}[] {uses "group"}[] {uses "group.subgroup"}[]
:::

:::definition "group.type" (lean := "Group.typeLength, Group.TypeLength, Group.compositionLength, derivedLength, Group.nilpotencyClass")
*Type of groups.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.type))

For a finite {bpref "group"}[group] $`G`, we write *Type - length* as follows

<ul>
<li> If $`G` is {bpref "group.cyclic"}[cyclic] we write "Cyclic".  For {bpref "group.abelian"}[abelian] groups that are not cyclic we write "Abelian - $`n`", where $`n` is the number of cyclic groups in the unique cyclic decomposition of $`G` as $`C_{d_1} \times C_{d_2}\times \cdots \times C_{d_n}` with $`d_i\mid d_{i+1}` and $`d_i>0`.</li>

<li> If $`G` is {bpref "group.nilpotent"}[nilpotent] but not abelian then we write  "Nilpotent - $`n`", where $`n` is the nilpotency class of $`G`.</li>

<li> If $`G` is {bpref "group.solvable"}[solvable] but not nilpotent then we write  "Solvable - $`n`", where $`n` is the {bpref "group.derived_series"}[derived length] of $`G`.</li>

<li> If $`G` is simple we write "Simple".

 <li> For non-simple, non-solvable groups we write "Non-solvable - $`n`", where $`n` is the number of Jordan factors of $`G`.</li>
</ul>

Depends on: {uses "group"}[] {uses "group.abelian"}[] {uses "group.cyclic"}[] {uses "group.derived_series"}[] {uses "group.nilpotent"}[] {uses "group.solvable"}[]
:::

:::definition "group.under_subgroup" (lean := "Subgroup, CovBy")
*Under-subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.under_subgroup))

If $`H \subseteq G` is a {bpref "group.subgroup"}[subgroup], an *under-subgroup* is a subgroup $`K \subseteq G` with $`K \subseteq H`.  A *maximal under-subgroup* is an under-subgroup $`K \ne H` that is maximal with respect to inclusion.

Depends on: {uses "group.subgroup"}[]
:::

:::definition "group.unitary" (lean := "Matrix.generalUnitaryGroup, Matrix.specialUnitaryGroupFq, Matrix.projectiveGeneralUnitaryGroup, Matrix.projectiveSpecialUnitaryGroup, Matrix.sesquiUnitaryGroup")
*Unitary group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.unitary))

The *(general) unitary group* $`\GU(n, q)` is the group of $`n \times n` unitary matrices with entries in the {bpref "ring.field"}[field] $`\F_{q^2}` (the finite field with $`q^2` elements).  Here, a matrix is \*unitary\* if the inverse of $`M` equals the conjugate transpose of $`M`.

For matrices $`M` over the finite field $`\F_{q^2}`, the \*conjugate\* of $`M` is defined as the matrix obtained by applying the map $`x \mapsto x^q` (i.e. the $`r`-th power of the Frobenius automorphism, where $`q = p^r`) to each entry of $`M`.

The *projective (general) unitary group* $`\PGU(n, q)` is the {bpref "group.quotient"}[quotient] of $`\GU(n, q)` by the scalar matrices in $`\GU(n, q)` (equivalently, $`\PGU(n, q)` is the quotient of $`\GU(n, q)` by its {bpref "group.center"}[center]).

The *special unitary group* $`\SU(n, q)` is the {bpref "group.subgroup"}[subgroup] of $`\GU(n, q)` consisting of those matrices with determinant 1.

The *projective special unitary group* $`\PSU(n, q)` is the quotient of $`\SU(n, q)` by the scalar matrices in $`\SU(n, q)` (equivalently, $`\PSU(n, q)` is the quotient of $`\SU(n, q)` by its center).

(see , page x)

Depends on: {uses "group.center"}[] {uses "group.quotient"}[] {uses "group.subgroup"}[] {uses "ring.field"}[]
:::

:::definition "group.upper_central_series" (lean := "Subgroup.upperCentralSeries, Subgroup.upperCentralSeriesStep, Group.IsNilpotent")
*Upper central series of a group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.upper_central_series))

If $`G` is a {bpref "group"}[group], then its *upper central series* is a {bpref "group.normal_series"}[normal series] of subgroups

$$`\langle e\rangle = Z_0(G) \unlhd Z_1(G) \unlhd Z_2(G) \unlhd \cdots`

where $`Z_0(G)=\langle e\rangle` and $`Z_i(G)/Z_{i-1}(G)` is the {bpref "group.center"}[center] of $`G/Z_{i-1}(G)`, i.e., $`Z_i(G)` is the inverse image of the center of $`G/Z_{i-1}(G)`.

Each of the subgroups $`Z_i(G)` is characteristic.  The group is {bpref "group.nilpotent"}[nilpotent] if and only if $`Z_i(G)=G` for some $`i`.

Depends on: {uses "group"}[] {uses "group.center"}[] {uses "group.nilpotent"}[] {uses "group.normal_series"}[]
:::

:::definition "group.weight_function" (lean := "Group.IsWeightFunction, Group.IsWeightFunction.apply_conj_pow")
*Weight function.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.weight_function))

Let $`G` be a finite group. A *weight function* on $`G` is a function $`w:G \to \R_{\geq 0}` such that:

1. $`w(g) = 0` if and only if $`g` equals the identity element of $`G`.
2. $`w(h g h^{-1}) = w(g)` for all $`g,h \in G`, i.e. $`w` is invariant under conjugacy.
3. $`w(g^n) = w(g)` for all $`g \in G` and all natural numbers $`n` with $`n \nmid \#G`, i.e. $`w` is invariant under invertible powering.

Any weight function takes constant value on each {bpref "group.division"}[rational conjugacy class] of $`G`.

Depends on: {uses "group.division"}[]
:::

:::definition "group.weyl_group" (lean := "Subgroup.normalizer, Subgroup.centralizer, Subgroup.normalizerMonoidHom, Subgroup.normalizerMonoidHom_ker")
*Weyl group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.weyl_group))

The *Weyl group* associated to a {bpref "group.subgroup"}[subgroup] $`H \subseteq G` is the quotient $`W = N_G(H) / Z_G(H)` of the {bpref "group.subgroup.normalizer"}[normalizer] of $`H` by the {bpref "group.centralizer"}[centralizer] of $`H`.  The terminology is taken from the theory of Lie groups, where there is a unique conjugacy class of maximal tori in a Lie group $`G` and if $`T` is any such maximal torus then $`Z_G(T) = T` has finite {bpref "group.subgroup.index"}[index] in $`N_G(T)`.  In that context we may thus speak of the Weyl group of $`G`.

When $`G` is an abstract group, we must specify $`H` as well, and the Weyl group naturally embeds into the {bpref "group.automorphism"}[automorphism] group $`\Aut(H)` and gives the subset of automorphisms of $`H` that are induced by conjugation within $`G`.

Depends on: {uses "group.automorphism"}[] {uses "group.centralizer"}[] {uses "group.subgroup"}[] {uses "group.subgroup.index"}[] {uses "group.subgroup.normalizer"}[]
:::

:::definition "group.wreath_product" (lean := "TauCeti.PermSubgroupWreathProduct, TauCeti.PermutationWreathProduct, SemidirectProduct, mulAutArrow, MulAction.IsPretransitive")
*Wreath product.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.wreath_product))

If $`S\leq S_n` and $`H` are {bpref "group"}[groups], the *wreath product* of $`H` and $`S` is the {bpref "group.semidirect_product"}[semidirect product]
$$`H \wr S = H^n \rtimes S`

where $`S` acts on $`H^n` via $`S\subseteq S_n`, permuting the $`n` copies of $`H`.

If $`S` is a transitive subgroup of $`S_n`, we say that the wreath product is *transitive*.

Depends on: {uses "group"}[] {uses "group.semidirect_product"}[]
:::

:::definition "group.z_group" (lean := "IsZGroup")
*Z-group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/group.z_group))

A *Z-group* is a (finite) group all of whose Sylow subgroups are {bpref "group.cyclic"}[cyclic]. Such groups are {bpref "group.metacyclic"}[metacyclic], {bpref "group.supersolvable"}[supersolvable] and {bpref "group.monomial"}[monomial].

Every cyclic group is a Z-group, but the converse does not hold, as shown by [these examples](https://beta.lmfdb.org/Groups/Abstract/?Zgroup=yes&cyclic=no).

Depends on: {uses "group.cyclic"}[] {uses "group.monomial"}[] {uses "group.supersolvable"}[]
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
