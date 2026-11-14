import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Classical" =>
%%%
tag := "classical-modular-forms"
file := "Classical-modular-forms"
%%%

This section lists the LMFDB definitions in the category `cmf`. Each definition links back to its LMFDB knowl. `specialfunction.poincare` also belongs here, although its id puts it in another LMFDB category. It also lists the knowls about the LMFDB's data on this subject that have mathematical content, from the categories `portrait` and `rcs`.

:::definition "cmf" (lean := "ModularForm, SlashInvariantForm.slash_action_eqn'")
*Classical modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf))

Let $`k` be a positive integer and let $`\Gamma` be a finite index subgroup of the {bpref "group.sl2z"}[modular group] $`\SL(2,\Z)`.

A (classical) *modular form* $`f` of  {bpref "cmf.weight"}[weight] $`k` on $`\Gamma`,  is a holomorphic function defined on the {bpref "mf.upper_half_plane"}[upper half plane] $`\mathcal{H}`, which satisfies the transformation property

$$`f(\gamma z) = (cz+d)^k f(z)`

for all $`z\in\mathcal{H}` and $`\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in \Gamma` and is holomorphic  at all the {bpref "group.fuchsian.cusps"}[cusps] of $`\Gamma`.

If $`\Gamma` contains the principal congruence subgroup {bpref "group.sl2z.subgroup.gamman"}[$`\Gamma(N)`] then $`f` is said to be a modular form of {bpref "cmf.level"}[level] $`N`.

For each fixed choice of $`k` and $`\Gamma` the set of modular forms of weight $`k` on $`G` form a finite-dimensional $`\mathbb{C}`-vector space denoted $`M_k(\Gamma)`.

For the congruence subgroup {bpref "group.sl2z.subgroup.gamma1n"}[$`\Gamma_1(N)`] the space $`M_k(\Gamma_1(N))` decomposes as a direct sum of subspaces $`M_k(N,\chi)` over the group of {bpref "character.dirichlet"}[Dirichlet characters] $`\chi` of modulus $`N`, where $`M_k(N,\chi)` is the subspace of forms $`f\in M_k(N)` that satisfy

$$`f(\gamma z) = \chi(d)(cz+d)^k f(z)`

for all $`\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}` in {bpref "group.sl2z.subgroup.gamma0n"}[$`\Gamma_0(N)`].

Elements of $`M_k(N,\chi)` are said to be modular forms of weight $`k`, level $`N`, and character $`\chi`.

For trivial character $`\chi` of modulus $`N` we have $`M_k(N,\chi)=M_k(\Gamma_0(N))`.

Tau Ceti Review: [`ModularForm`](https://taucetiproject.org/review/#/d/ModularForm), [`SlashInvariantForm.slash_action_eqn'`](https://taucetiproject.org/review/#/d/SlashInvariantForm.slash_action_eqn%27).

Depends on: {uses "character.dirichlet"}[] {uses "cmf.space_mathlib_def"}[] {uses "group.fuchsian.cusps"}[] {uses "group.sl2z"}[] {uses "mf.upper_half_plane"}[]
:::

:::definition "cmf.analytic_conductor" (lean := "HeckeRing.GL2.Newform.analyticConductorLMFDB, HeckeRing.GL2.Newform.ofReal_analyticConductorLMFDB, HeckeRing.GL2.Newform.analyticConductorLMFDB_pos, Complex.digamma_ofReal_im")
*Analytic conductor of a classical newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.analytic_conductor))

The *analytic conductor* of a {bpref "cmf.newform"}[newform] $`f \in S_k^{\mathrm{new}}(N,\chi)` is the positive real number

$$`N\left(\frac{\exp(\psi(k/2))}{2\pi}\right)^2,`

where $`\psi(x):=\Gamma'(x)/\Gamma(x)` is the logarithmic derivative of the Gamma function.

Depends on: {uses "cmf.newform"}[]
:::

:::definition "cmf.analytic_rank" (lean := "HeckeRing.GL2.Newform.analyticRank, ModularForm.L, HeckeRing.GL2.Newform.analyticLFunction, AnalyticLFunction.analyticRank, HeckeRing.GL2.Newform.analyticRank_analyticLFunction, HeckeRing.GL2.Newform.IsSelfDual, HeckeRing.GL2.Newform.rootNumber, HeckeRing.GL2.Newform.IsSelfDual.rootNumber_eq_neg_one_pow_analyticRank")
*Analytic rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.analytic_rank))

The *analytic rank* of a {bpref "cmf.cusp_form"}[cuspidal modular form] $`f` is the {bpref "lfunction.analytic_rank"}[analytic rank] of the L-function

$$`L(f,s) = \sum_{n\ge 1} a_nn^{-s}`

where the $`a_n` are the complex coefficients that appear in the {bpref "cmf.q-expansion"}[$`q`-expansion] of the modular form: $`f(z)=\sum_{n\ge 1}a_nq^n`, where $`q=e^{2\pi i z}`.

The complex coefficients $`a_n` depend on a choice of embedding of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f` into the complex numbers.  It is conjectured that the analytic rank does not depend on this choice, and this conjecture has been verified for all classical modular forms stored in the LMFDB.

In general, analytic ranks of L-functions listed in the LMFDB are upper bounds that are believed (but not proven) to be tight.

For modular forms, the analytic ranks listed in the LMFDB are provably correct whenever the listed analytic rank is 0, or the listed analytic rank is 1 and the modular form is {bpref "cmf.selfdual"}[self dual] (in the self dual case the sign of the functional equation determines the parity of the analytic rank).

Tau Ceti Review: [`HeckeRing.GL2.Newform.analyticRank`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.analyticRank), [`ModularForm.L`](https://taucetiproject.org/review/#/d/ModularForm.L), [`HeckeRing.GL2.Newform.IsSelfDual`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.IsSelfDual).

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

has determinant $`Q`. The matrix $`W_Q` normalizes the group {bpref "group.sl2z.subgroup.gamma0n"}[$`\Gamma_0(N)`], and for any {bpref "cmf.weight"}[weight] $`k` it induces a linear operator $`w_Q` on the space of {bpref "cmf.cusp_form"}[cusp forms]  $`S_k(\Gamma_0(N))` that commutes with the {bpref "cmf.hecke_operator"}[Hecke operators] $`T_p` for all $`p \nmid Q` and acts as its own inverse.

The linear operator $`w_Q` does not depend on the choice of $`x,y,z,t` and is called the *Atkin-Lehner involution* of $`S_k(\Gamma_0(N))`.  Any cusp form $`f` in $`S_k(\Gamma_0(N))` which is an eigenform for all $`T_p` with $`p \nmid N` is also an eigenform for $`w_Q`, with eigenvalue $`\pm 1`.

The matrix $`W_Q` induces an automorphism of the {bpref "ag.modcurve.x0"}[modular curve $`X_0(N)`] that is also denoted $`w_Q`.

In the case $`Q=N`, the Atkin-Lehner involution $`w_N` is also called the {bpref "cmf.fricke"}[Fricke involution].

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.atkin_lehner_dims" (lean := "TauCeti.atkinLehnerSubspace, TauCeti.atkinLehnerDim, TauCeti.atkinLehnerDims, TauCeti.sum_atkinLehnerDim, HeckeRing.GL2.Newform.toCuspFormGamma0_mem_atkinLehnerSubspace")
*Dimensions of Atkin-Lehner subspaces.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.atkin_lehner_dims))

For each prime dividing the {bpref "cmf.level"}[level] $`N`, the {bpref "cmf.atkin-lehner"}[Atkin-Lehner operator] scales each {bpref "cmf.newform"}[newform] by either $`1` or $`-1`.  Let $`j` be the number of primes dividing $`N`.  Ordering the $`2^j` vectors of $`\pm 1` lexicographically (with $`1` before $`-1`), we show the dimensions of the subspaces of $`S_k^{\mathrm{new}}(\Gamma_0(N),\chi)` with prescribed Atkin-Lehner eigenvalues.

Depends on: {uses "cmf.atkin-lehner"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.bad_prime" (lean := "Nat.primeFactors, Nat.mem_primeFactors, CongruenceSubgroup.Gamma")
*Bad prime.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.bad_prime))

A *bad prime* for a {bpref "cmf"}[modular form] $`f` is a prime dividing the {bpref "cmf.level"}[level] of $`f`.

A *good prime* is a prime that is not a bad prime.  In other words, a prime that
does not divide the level.

Tau Ceti Review: [`Nat.primeFactors`](https://taucetiproject.org/review/#/d/Nat.primeFactors), [`Nat.mem_primeFactors`](https://taucetiproject.org/review/#/d/Nat.mem_primeFactors), [`CongruenceSubgroup.Gamma`](https://taucetiproject.org/review/#/d/CongruenceSubgroup.Gamma).

Depends on: {uses "cmf"}[] {uses "cmf.level"}[]
:::

:::definition "cmf.character" (lean := "HeckeRing.GL2.Newform.dirichletLift, modFormCharSpace")
*Character of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.character))

The *character* of an {bpref "cmf"}[elliptic modular form] $`f`
of weight $`k` for the group $`\Gamma`  is the {bpref "character.dirichlet"}[Dirichlet character] $`\chi` that appears in its transformation under the action of the defining group $`\Gamma`.  Namely,

$$`f(\gamma z) = \chi(d)(cz+d)^k f(z)`

for any $`z\in\mathcal{H}` and $`\gamma = \begin{pmatrix} * & * \\ c & d  \end{pmatrix}\in\Gamma`.  Here $`\Gamma` is a subgroup of $`\rm{SL}_2(\mathbb{Z})` containing the principal congruence subgroup $`\Gamma(N)`, and $`\chi` is a character mod $`N`.

Tau Ceti Review: [`HeckeRing.GL2.Newform.dirichletLift`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.dirichletLift).

Depends on: {uses "character.dirichlet"}[] {uses "cmf"}[]
:::

:::definition "cmf.cm_form" (lean := "HeckeRing.GL2.Newform.HasCM, HeckeRing.GL2.Newform.HasCMBy, Int.IsFundamentalDiscr.kroneckerChar, HeckeRing.GL2.Newform.HasCM.exists_hasSelfTwist, HeckeRing.GL2.Newform.IsGaloisConjugate.hasCMBy_iff")
*CM form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.cm_form))

A {bpref "cmf"}[classical modular form] is said to have *complex multiplication* if it admits a {bpref "cmf.self_twist"}[self twist] by the Kronecker character of an imaginary quadratic field.

Depends on: {uses "cmf"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.coefficient_field" (lean := "TauCeti.CoefficientField, HeckeRing.GL2.Newform.numberField_coefficientField, HeckeRing.GL2.Newform.isIntegral_coeff, TauCeti.CharacterField_le_CoefficientField, HeckeRing.GL2.Newform.IsGaloisConjugateBy.coefficientFieldEquiv, TauCeti.CharacterField, TauCeti.cyclotomicLevel, TauCeti.isLeast_cyclotomicLevel, TauCeti.adjoin_nth_roots_cyclotomicLevel, HeckeRing.GL2.Newform.adjoin_nth_roots_cyclotomicLevel_le_coefficientField, Complex.isLeast_adjoin_nth_roots_le, HeckeRing.GL2.Newform.span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace, HeckeRing.GL2.Newform.linearIndependent_toCuspForm, HeckeRing.GL2.Newform.toEigenform")
*Coefficient field for newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.coefficient_field))

The *coefficient field* of a modular form is the subfield of $`\C` generated by the coefficients $`a_n` of its $`q`-expansion $`\sum a_nq^n`.  The space of {bpref "cmf.cusp_form"}[cusp forms] $`S_k^\mathrm{new}(N,\chi)` has a basis of modular forms that are simultaneous eigenforms for all {bpref "cmf.hecke_operator"}[Hecke operators] and with algebraic {bpref "cmf.fouriercoefficients"}[Fourier coefficients].  For such eigenforms the coefficient field will be a number field, and Galois conjugate eigenforms will share the same coefficient field.  Moreover, if $`m` is the smallest positive integer such that the values of the character $`\chi` are contained in the cyclotomic field $`\Q(\zeta_m)`, the coefficient field will contain $`\Q(\zeta_m)`
For eigenforms, the coefficient field is also known as the *Hecke field*.

Tau Ceti Review: [`TauCeti.CoefficientField`](https://taucetiproject.org/review/#/d/TauCeti.CoefficientField), [`TauCeti.CharacterField_le_CoefficientField`](https://taucetiproject.org/review/#/d/TauCeti.CharacterField_le_CoefficientField), [`TauCeti.CharacterField`](https://taucetiproject.org/review/#/d/TauCeti.CharacterField), [`HeckeRing.GL2.Newform.span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace), [`HeckeRing.GL2.Newform.linearIndependent_toCuspForm`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.linearIndependent_toCuspForm), [`HeckeRing.GL2.Newform.toEigenform`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.toEigenform).

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.hecke_operator"}[]
:::

:::definition "cmf.coefficient_ring" (lean := "UpperHalfPlane.qExpansionCoeffRing, HeckeRing.GL2.Newform.coefficientRing, HeckeRing.GL2.Newform.coefficientOrder, HeckeRing.GL2.Newform.finiteIndex_coefficientOrder, HeckeRing.GL2.Newform.isIntegral_qExpansion_coeff")
*Coefficient ring.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.coefficient_ring))

The *coefficient ring* of a {bpref "cmf"}[modular form] is the subring $`\Z[a_1,a_2,a_3,\ldots]` of $`\C` generated by the coefficients $`a_n` of its $`q`-expansion $`\sum a_nq^n`.  In the case of a {bpref "cmf.newform"}[newform] the coefficients $`a_n` are algebraic integers and the coefficient ring is a finite index subring of the {bpref "nf.ring_of_integers"}[ring of integers] of the {bpref "cmf.coefficient_field"}[coefficient field] of the newform.
It is also known as the *Hecke ring*, since the $`a_n` are eigenvalues of {bpref "cmf.hecke_operator"}[Hecke operators].

Tau Ceti Review: [`HeckeRing.GL2.Newform.isIntegral_qExpansion_coeff`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.isIntegral_qExpansion_coeff).

Depends on: {uses "cmf"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.newform"}[] {uses "nf.ring_of_integers"}[]
:::

:::definition "cmf.congruence_subgroup" (lean := "CongruenceSubgroup.IsCongruenceSubgroup, CongruenceSubgroup.Gamma")
*Congruence subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.congruence_subgroup))

A *congruence subgroup* $`\Gamma` of $`\SL_2(\Z)` is a subgroup that contains a *principal congruence subgroup* $`\Gamma(N) := \ker \left( \operatorname{SL}_2(\mathbb{Z}) \to \operatorname{SL}_2(\mathbb{Z}/N\mathbb{Z}) \right)` for some $`N\ge 1`.  The least such $`N` is the *level* of $`\Gamma`.

Tau Ceti Review: [`CongruenceSubgroup.Gamma`](https://taucetiproject.org/review/#/d/CongruenceSubgroup.Gamma).
:::

:::definition "cmf.cusp_form" (lean := "CuspForm, ModularForm.cuspFormSubmodule, CuspFormClass.qExpansion_coeff_zero")
*Cuspidal modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.cusp_form))

Let $`k` be a positive integer and let $`\Gamma` be a finite index subgroup of the {bpref "group.sl2z"}[modular group] $`\SL(2,\Z)`.

A *cusp form* of {bpref "cmf.weight"}[weight] $`k` on $`\Gamma` is a {bpref "cmf"}[modular form] $`f\in M_k(\Gamma)` that vanishes at all {bpref "group.fuchsian.cusps"}[cusps] of $`\Gamma`.  In particular, the constant term in the {bpref "cmf.fouriercoefficients"}[Fourier expansion] of $`f` about any cusp is zero.

The cusp forms in $`M_k(\Gamma)` form a subspace $`S_k(\Gamma)`.  For each {bpref "character.dirichlet"}[Dirichlet character] $`\chi` of modulus $`N` the cusp forms in {bpref "cmf"}[$`M_k(N,\chi)`] form a subspace $`S_k(N,\chi)`; these are the cusp forms of weight $`k`, level $`N`, and character $`\chi`.

Tau Ceti Review: [`CuspForm`](https://taucetiproject.org/review/#/d/CuspForm), [`ModularForm.cuspFormSubmodule`](https://taucetiproject.org/review/#/d/ModularForm.cuspFormSubmodule), [`CuspFormClass.qExpansion_coeff_zero`](https://taucetiproject.org/review/#/d/CuspFormClass.qExpansion_coeff_zero).

Depends on: {uses "character.dirichlet"}[] {uses "cmf"}[] {uses "cmf.cusp_form_mathlib_def"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.weight"}[] {uses "group.fuchsian.cusps"}[] {uses "group.sl2z"}[]
:::

:::definition "cmf.cusp_form_mathlib_def" (lean := "CuspForm")
*Cuspidal modular form (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.cusp_form_mathlib_def))

This is *CuspForm $`\Gamma` $`k`* in mathlib. In the LMFDB definition, $`k` is a positive integer and $`\Gamma` is a finite-index subgroup of $`\SL_2(\mathbb{Z})`. Mathlib is more general: $`k` is an integer
and $`\Gamma` is a subgroup of $`\GL_2(\mathbb{R})`.

Tau Ceti Review: [`CuspForm`](https://taucetiproject.org/review/#/d/CuspForm).
:::

:::definition "cmf.cusp_form_subspace_mathlib_def" (lean := "ModularForm.cuspFormSubmodule")
*Cuspidal subspace (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.cusp_form_subspace_mathlib_def))

This is *cuspFormSubmodule $`\Gamma` $`k`* in mathlib. It is the submodule of the {bpref "cmf.space_mathlib_def"}[ModularForm $`\Gamma` $`k`] consisting of {bpref "cmf.cusp_form"}[cusp forms].

Tau Ceti Review: [`ModularForm.cuspFormSubmodule`](https://taucetiproject.org/review/#/d/ModularForm.cuspFormSubmodule).

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.space_mathlib_def"}[]
:::

:::definition "cmf.decomposition.new.gamma0chi" (lean := "HeckeRing.GL2.Newform.rationalPiece, HeckeRing.GL2.Newform.exists_apply_eq_of_mem_rationalPiece, HeckeRing.GL2.Newform.span_rationalPiece, HeckeRing.GL2.Newform.finrank_newformSubspaceOver, HeckeRing.GL2.NewformOrbit.iSup_newformSubspace_inf_cuspFormCharSpace, HeckeRing.GL2.Newform.numberField_coefficientField")
*Decomposition into newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.decomposition.new.gamma0chi))

The {bpref "cmf.hecke_operator"}[Hecke algebra] acts on $`S_k^{\mathrm{new}}(N, \chi)`, breaking it up into irreducible pieces.  Each piece is spanned by a set of conjugate eigenforms with Fourier coefficients in a number field of degree equal to the dimension of the subspace.  We refer to an irreducible orbit as a *{bpref "cmf.newform"}[newform]*.

Depends on: {uses "cmf.hecke_operator"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.decomposition.new.gamma1" (lean := "TauCeti.iSup_inf_cuspFormsNew_cuspFormCharSpace, iSupIndep_cuspFormCharSpace, TauCeti.GaloisAction.conjCusp, TauCeti.GaloisAction.conjCusp_mem_cuspFormsNew_inf_cuspFormCharSpace_iff, HeckeRing.GL2.Newform.exists_conjCusp_mem_iff_of_mem_galoisOrbit, HeckeRing.GL2.Newform.finrank_cuspFormsNew_inf_cuspFormCharSpace_comp")
*Decomposition into newforms for Gamma1(N).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.decomposition.new.gamma1))

The space of newforms of weight $`k` on $`\Gamma_1(N)` decomposes as

$$`S_k^{\mathrm{new}}(\Gamma_1(N)) \cong \bigoplus_{\chi \bmod N} S_k^{\mathrm{new}}(N, \chi),`

where the direct sum is over all {bpref "character.dirichlet"}[Dirichlet characters] modulo $`N`. If $`\chi` and $`\chi'` are in the same {bpref "character.dirichlet.galois_orbit"}[Galois orbit], then $`S_k^{\mathrm{new}}(N, \chi)` and $`S_k^{\mathrm{new}}(N, \chi')` are Galois conjugate and we identify them since we define {bpref "cmf.newform"}[newforms] as Galois orbits.

Tau Ceti Review: [`TauCeti.iSup_inf_cuspFormsNew_cuspFormCharSpace`](https://taucetiproject.org/review/#/d/TauCeti.iSup_inf_cuspFormsNew_cuspFormCharSpace), [`iSupIndep_cuspFormCharSpace`](https://taucetiproject.org/review/#/d/iSupIndep_cuspFormCharSpace).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.decomposition.old.gamma0chi"
*Oldspace decomposition for newform space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.decomposition.old.gamma0chi))

There are natural inclusion maps from lower level; the old subspace is the span of their images.  For $`M` dividing the level $`N` and divisible by $`\operatorname{cond}(\chi)`, for $`\chi_M` of modulus $`M` inducing $`\chi`, and for $`d \mid (N/M)`, the maps

$$`\begin{aligned}
  \alpha_{M, d} : S_k(\Gamma_0(M), \chi_M) & \to S_k(\Gamma_0(N), \chi) \\\\
  f(q) & \mapsto f(q^d)
  \end{aligned}`

  induce an isomorphism

$$`S_k(\Gamma_0(N), \chi) \cong \bigoplus_{M,d} \alpha_{M,d}\left(S_k^{\mathrm{new}}(\Gamma_0(M), \chi_M)\right).`
:::

:::definition "cmf.decomposition.old.gamma1"
*Oldspace decomposition for Gamma1(N).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.decomposition.old.gamma1))

There are natural inclusion maps from lower level; the old subspace is the span of their images.  For $`M` dividing the level $`N`, and for $`t` dividing $`\frac{N}{M}`, the maps

$$`\begin{aligned}
  \alpha_{M, t} : S_k(\Gamma_1(M)) & \to S_k(\Gamma_1(N)) \\\\
  f(q) & \mapsto f(q^t)
  \end{aligned}`

  induce an isomorphism

$$`S_k(\Gamma_1(N)) \cong \bigoplus_{M,t} \alpha_{M,t}\left(S_k^{\mathrm{new}}(\Gamma_1(M))\right).`
:::

:::definition "cmf.defining_polynomial" (lean := "TauCeti.CoefficientField, HeckeRing.GL2.Newform.numberField_coefficientField")
*Defining polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.defining_polynomial))

The {bpref "cmf.coefficient_field"}[coefficient field of a modular form] is a {bpref "nf"}[number field]. A *defining polynomial* for this number field is explicitly recorded, because some of the data associated to the modular form will be expressed in terms of roots of this polynomial.

Tau Ceti Review: [`TauCeti.CoefficientField`](https://taucetiproject.org/review/#/d/TauCeti.CoefficientField).

Depends on: {uses "cmf.coefficient_field"}[] {uses "nf"}[]
:::

:::definition "cmf.dimension" (lean := "HeckeRing.GL2.Newform.dimension, HeckeRing.GL2.Newform.relativeDimension, HeckeRing.GL2.Newform.finrank_span_toCuspForm_eq_finrank, Module.finrank, HeckeRing.GL2.Newform.dimension_eq_finrank, HeckeRing.GL2.Newform.relativeDimension_eq_finrank, HeckeRing.GL2.Newform.dimension_eq_ncard_galoisOrbit, HeckeRing.GL2.Newform.finrank_rationalPiece")
*Dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.dimension))

The *dimension* of a space of modular forms is its dimension as a complex vector space; for spaces of newforms $`S_k^{\rm new}(N,\chi)` this is the same as the dimension of the $`\Q`-vector space spanned by its eigenforms.

The *dimension* of a {bpref "cmf.newform"}[newform] refers to the dimension of its {bpref "cmf.newform_subspace"}[newform subspace], equivalently, the cardinality of its {bpref "cmf.galois_orbit"}[newform orbit].  This is equal to the degree of its coefficient field (as an extension of $`\Q`).

The *relative dimension* of $`S_k^{\rm new}(N,\chi)`  is its dimension as a $`\Q(\chi)`-vector space, where $`\Q(\chi)` is the field generated by the values of $`\chi`, and similarly for newform subspaces.

Tau Ceti Review: [`Module.finrank`](https://taucetiproject.org/review/#/d/Module.finrank).

Depends on: {uses "cmf.dimension_mathlib_def"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "cmf.newform_subspace"}[]
:::

:::definition "cmf.dimension_galois_orbit" (lean := "HeckeRing.GL2.Newform.dimension, HeckeRing.GL2.Newform.newformSubspace, HeckeRing.GL2.Newform.dimension_eq_ncard_galoisOrbit")
*Dimension of a Hecke orbit.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.dimension_galois_orbit))

The dimension of an (irreducible) {bpref "cmf.hecke_orbit"}[Hecke orbit] of a newform $`f`.

Depends on: {uses "cmf.hecke_orbit"}[]
:::

:::definition "cmf.dimension_mathlib_def" (lean := "Module.finrank")
*Dimension (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.dimension_mathlib_def))

This is defined as 'finrank ℂ (ModularForm Γ k)' in mathlib, where {bpref "cmf.space_mathlib_def"}[ModularForm $`\Gamma` $`k`] is the {bpref "cmf.space"}[space of modular forms] and finrank ℂ gives its  *module rank* over $`\mathbb{C}`.

Tau Ceti Review: [`Module.finrank`](https://taucetiproject.org/review/#/d/Module.finrank).

Depends on: {uses "cmf.space"}[] {uses "cmf.space_mathlib_def"}[]
:::

:::definition "cmf.display_dim" (lean := "TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp, TauCeti.cuspFormsNewGamma0, TauCeti.Nat.IsExactDivisor.finrank_inf_eigenspace_add_finrank_inf_eigenspace, TauCeti.Nat.IsExactDivisor.finrank_eigenspace_add_finrank_eigenspace, TauCeti.Nat.IsExactDivisor.isCompl_eigenspace_normalizedAtkinLehnerOperatorCusp, TauCeti.Nat.IsExactDivisor.restrict_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew, Module.finrank")
*Dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.display_dim))

If the {bpref "cmf.character"}[character] of the space is trivial, the {bpref "cmf.dimension"}[dimension] is the sum of the dimensions of the {bpref "cmf.plus_space"}[plus subspace] and the {bpref "cmf.minus_space"}[minus subspace].

Tau Ceti Review: [`TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp`](https://taucetiproject.org/review/#/d/TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp), [`TauCeti.Nat.IsExactDivisor.isCompl_eigenspace_normalizedAtkinLehnerOperatorCusp`](https://taucetiproject.org/review/#/d/TauCeti.Nat.IsExactDivisor.isCompl_eigenspace_normalizedAtkinLehnerOperatorCusp), [`TauCeti.Nat.IsExactDivisor.restrict_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew`](https://taucetiproject.org/review/#/d/TauCeti.Nat.IsExactDivisor.restrict_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew), [`Module.finrank`](https://taucetiproject.org/review/#/d/Module.finrank).

Depends on: {uses "cmf.character"}[] {uses "cmf.dimension"}[] {uses "cmf.minus_space"}[] {uses "cmf.plus_space"}[]
:::

:::definition "cmf.distinguishing_primes"
*Distinguishing Hecke operators.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.distinguishing_primes))

For a {bpref "cmf.newspace"}[newspace] $`S^\mathrm{new}_k(N,\chi)` we say that a set of {bpref "cmf.hecke_operator"}[Hecke operators] $`\mathcal T:=\{T_{p_1},\ldots,T_{p_r}\}` *distinguishes* the {bpref "cmf.newform"}[newforms] in the space if the sets $`X_f(\mathcal T)` of characteristic polynomials of the $`T_p\in \mathcal T` acting on the subspace $`V_f` spanned by the {bpref "cmf.galois_orbit"}[Galois orbit] of $`f` in $`S_k^\mathrm{new}(N,\chi)` are distinct as $`f` ranges over (non-conjugate) newforms in $`S_k^\mathrm{new}(N,\chi)`.

The set $`\mathcal T` can be identified by a list of primes $`p`.  For convenience we restrict to primes $`p` that do not divide the level $`N` and list the unique ordered sequence of primes $`p_1,\ldots,p_n` for which the sequence of integers $`c_1,\ldots,c_n` defined by

$$`c_m := \#\bigl\{X_f(\{T_{p_i}:i < m\}): \mathrm{newforms}\ f\in S_k^\mathrm{new}(N,\chi)\bigr\}`

is strictly increasing.  The length of the sequence $`p_1,\ldots p_n` is always less then the number of newforms in $`S_k^\mathrm{new}(N,\chi)` and we obtain the empty sequence when $`S_k^\mathrm{new}(N,\chi)` contains just one newform.

Depends on: {uses "cmf.galois_orbit"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.dualform" (lean := "CuspForm.conj, CuspForm.qExpansion_conj, CuspForm.coeff_conj_div_cpow, HeckeRing.GL2.Newform.analyticCoeff_conj, HeckeRing.GL2.Newform.isCMField_coefficientField_iff, HeckeRing.GL2.Newform.numberField_coefficientField")
*Dual cuspform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.dualform))

The *dual* of a {bpref "cmf.cusp_form"}[cuspidal modular form] $`f` is the form whose coefficients $`a_n` in its {bpref "cmf.q-expansion"}[$`q`-expansion] are the complex conjugates of those of $`f`.  The {bpref "cmf.lfunction"}[L-function] of the dual form is the {bpref "lfunction.dual"}[dual] of the L-function of $`f`.

The {bpref "cmf.coefficient_field"}[coefficient field] of a {bpref "cmf.selfdual"}[non-self-dual] {bpref "cmf.newform"}[newform] is a {bpref "nf.cm_field"}[CM field].

Tau Ceti Review: [`CuspForm.conj`](https://taucetiproject.org/review/#/d/CuspForm.conj), [`CuspForm.qExpansion_conj`](https://taucetiproject.org/review/#/d/CuspForm.qExpansion_conj).

Depends on: {uses "cmf.coefficient_field"}[] {uses "cmf.cusp_form"}[] {uses "cmf.newform"}[] {uses "cmf.q-expansion"}[] {uses "cmf.selfdual"}[] {uses "lfunction.dual"}[] {uses "nf.cm_field"}[]
:::

:::definition "cmf.eisenstein" (lean := "ModularForm.E")
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

Tau Ceti Review: [`ModularForm.E`](https://taucetiproject.org/review/#/d/ModularForm.E).

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

- $`x` is the {bpref "cmf.hecke_galois_orbit"}[label] of the {bpref "cmf.galois_orbit"}[Galois orbit] of the newform $`f`.

For each {bpref "cmf.embedding"}[embedding] of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f` into the complex numbers, the corresponding modular form over $`\C` has a label of the form $`N.k.E.a.x.n.i`, where

- $`n` determines the {bpref "character.dirichlet.conrey"}[Conrey label] $`N.n` of the Dirichlet character $`\chi`;

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

:::definition "cmf.embedding" (lean := "HeckeRing.GL2.Newform.isIntegral_coeff, HeckeRing.GL2.Newform.IsEmbedding, HeckeRing.GL2.Newform.exists_isEmbedding, HeckeRing.GL2.Newform.IsEmbedding.LSeries_ne, HeckeRing.GL2.Newform.IsEmbedding.χ_eq_iff, HeckeRing.GL2.Newform.IsEmbedding.dirichletLift_mem_galoisOrbit")
*Embedding of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.embedding))

The coefficients in the {bpref "cmf.q-expansion"}[$`q`-expansion] $`\sum a_nq^n` of a {bpref "cmf.q-expansion"}[newform] $`f` are algebraic integers that generate the {bpref "cmf.coefficient_field"}[coefficient field] $`\Q(f)` of $`f`.

Each {bpref "nf.embedding"}[embedding] $`\iota\colon \Q(f)\to \C` gives rise to a modular form $`\iota(f)` with $`q`-expansion $`\sum \iota(a_n)q^n`; the modular form $`\iota(f)` is an *embedding* of the newform $`f`.

Distinct embeddings give rise to modular forms  that lie in the same {bpref "cmf.galois_orbit"}[galois orbit] but have distinct {bpref "lfunction"}[$`L`-functions] $`L(s):=\sum \iota(a_n)n^{-s}`.

If $`f` is a newform of {bpref "cmf.character"}[character] $`\chi`, each embedding $`\Q(f)\to \C` induces an embedding $`\Q(\chi)\to \C` of the {bpref "character.dirichlet.value_field"}[value field] of $`\chi`.  The embeddings of $`f` may be grouped into blocks with the same {bpref "character.dirichlet"}[Dirichlet character]; distinct blocks correspond to modular forms with distinct (but Galois conjugate) Dirichlet characters.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.value_field"}[] {uses "cmf.character"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.q-expansion"}[] {uses "lfunction"}[] {uses "nf.embedding"}[]
:::

:::definition "cmf.embedding_format" (lean := "HeckeRing.GL2.Newform.IsEmbedding, HeckeRing.GL2.Newform.analyticCoeff, HeckeRing.GL2.Newform.normalizedSatakeParameters, HeckeRing.GL2.Newform.satakeAngles, HeckeRing.GL2.Newform.satakeAngles_eq_map_arg_satakeParameters")
*Embedding Format.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.embedding_format))

Let $`f` be {bpref "cmf.newform"}[newform] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k` and {bpref "cmf.character"}[character] $`\chi`.

Further, let $`a_n` denote the trace  of the {bpref "cmf.hecke_operator"}[Hecke operator] $`T_n`.

For each {bpref "nf.embedding"}[embedding] $`\iota` of the coefficient field, we may consider the embedded modular form $`\iota(f)`.
We present these embeddings sorted numerically according to the two values that define their {bpref "cmf.embedding_label"}[label].

We may present $`\iota(f)` in four formats:

- Complex embeddings: For each embedding $`\iota`, we present the real and imaginary values $`\iota(a_n)` with the desired number of significant digits of the stored values.

The stored values are the approximations to 53 bits of $`\iota(a_n)` initially computed up to 200 bits of precision.

- Normalized embeddings: the same as above, but now we present $`a_n` analytically normalized, i.e., $`\iota(a_n) / n^{(k-1)/2}`

- {bpref "cmf.satake_parameters"}[Satake Parameters]: we use $`\iota(a_p)`, these are deduced from the {bpref "cmf.satake_angles"}[Satake angles].

- {bpref "cmf.satake_angles"}[Satake Angles]: $`\theta_p` where $`\theta_p \in [-\pi, \pi]`, the arguments of the {bpref "cmf.satake_parameters"}[Satake parameters].

Depends on: {uses "cmf.character"}[] {uses "cmf.embedding_label"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.satake_angles"}[] {uses "cmf.satake_parameters"}[] {uses "cmf.weight"}[] {uses "nf.embedding"}[]
:::

:::definition "cmf.embedding_label"
*Complex embedding label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.embedding_label))

The *label* complex embedded holomorphic {bpref "cmf.cusp_form"}[cusp form] $`f` is $`N.k.a.x.c.j` (sometimes shortened as $`a.j` ), where

- $`N` is the {bpref "cmf.level"}[level],

- $`k` is the {bpref "cmf.weight"}[weight],

- $`N.a` is the {bpref "character.dirichlet.galois_orbit_label"}[label] of the Galois orbit of the Dirichlet character,

- $`x` is the {bpref "cmf.hecke_galois_orbit"}[Hecke Galois orbit label],

- $`N.c` is the {bpref "character.dirichlet.conrey"}[Conrey label] for the character corresponding to the {bpref "cmf.embedding"}[embedding], and

- $`j` is the index for the embedding within those with the same Dirichlet character, these are ordered by the vector $`\iota(a_n)`, where we order the complex numbers first by their real part and then by their imaginary part.

Depends on: {uses "character.dirichlet.galois_orbit_label"}[] {uses "cmf.cusp_form"}[] {uses "cmf.embedding"}[] {uses "cmf.level"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.eta_quotient" (lean := "ModularForm.eta, ModularForm.eta_ne_zero")
*Eta quotient.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.eta_quotient))

An *eta quotient* is any function $`f` of the form

$$`f(z)=\prod_{1\leq i\leq s}\eta^{r_i}(m_iz),`

where $`m_i\in\mathbb{N}` and $`r_i\in\mathbb{Z}` and $`\eta(z)` is the {bpref "mf.half_integral_weight.dedekind_eta"}[Dedekind eta function].

An *eta product* is an eta quotient in which all the $`r_i` are non-negative.

Tau Ceti Review: [`ModularForm.eta`](https://taucetiproject.org/review/#/d/ModularForm.eta), [`ModularForm.eta_ne_zero`](https://taucetiproject.org/review/#/d/ModularForm.eta_ne_zero).

Depends on: {uses "mf.half_integral_weight.dedekind_eta"}[]
:::

:::definition "cmf.fouriercoefficients" (lean := "UpperHalfPlane.qExpansion, PowerSeries.coeff, UpperHalfPlane.hasSum_qExpansion, UpperHalfPlane.cuspFunction, Subgroup.strictWidthInfty")
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

Tau Ceti Review: [`UpperHalfPlane.qExpansion`](https://taucetiproject.org/review/#/d/UpperHalfPlane.qExpansion), [`PowerSeries.coeff`](https://taucetiproject.org/review/#/d/PowerSeries.coeff), [`UpperHalfPlane.hasSum_qExpansion`](https://taucetiproject.org/review/#/d/UpperHalfPlane.hasSum_qExpansion), [`UpperHalfPlane.cuspFunction`](https://taucetiproject.org/review/#/d/UpperHalfPlane.cuspFunction), [`Subgroup.strictWidthInfty`](https://taucetiproject.org/review/#/d/Subgroup.strictWidthInfty).

Depends on: {uses "cmf"}[] {uses "group.fuchsian.cusps"}[] {uses "group.fuchsian.cusps.width"}[]
:::

:::definition "cmf.fouriercoefficients_mathlib_def" (lean := "PowerSeries.coeff")
*Fourier coefficients of a modular form (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.fouriercoefficients_mathlib_def))

This is '(qExpansion h f).coeff n' in mathlib, where $`f:\mathcal H\to\mathbb{C}` is the {bpref "cmf"}[modular form], $`h` is the period parameter used to define the {bpref "cmf.q-expansion"}[q-expansion] of $`f`, and 'coeff n' extracts its *$`n`-th coefficient*.

Tau Ceti Review: [`PowerSeries.coeff`](https://taucetiproject.org/review/#/d/PowerSeries.coeff).

Depends on: {uses "cmf"}[] {uses "cmf.q-expansion"}[]
:::

:::definition "cmf.fricke"
*Fricke involution.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.fricke))

The *Fricke involution* is the {bpref "cmf.atkin-lehner"}[Atkin-Lehner involution] $`w_N` on the space $`S_k(\Gamma_0(N))` (induced by the corresponding involution on the modular curve $`X_0(N)`).

For a newform $`f \in S_k^{\textup{new}}(\Gamma_0(N))`, the sign of the {bpref "lfunction.functional_equation"}[functional equation] satisfied by the {bpref "lfunction"}[L-function] attached to $`f` is $`i^{-k}` times the eigenvalue of $`\omega_N` on $`f`.  So, for example when $`k=2`, the signs swap, and the {bpref "cmf.analytic_rank"}[analytic rank] of $`f` is even when $`w_N f = -f` and odd when $`w_N f = +f`.

Depends on: {uses "cmf.analytic_rank"}[] {uses "cmf.atkin-lehner"}[] {uses "lfunction"}[] {uses "lfunction.functional_equation"}[]
:::

:::definition "cmf.galois_conjugate" (lean := "HeckeRing.GL2.Newform.IsGaloisConjugate, HeckeRing.GL2.Newform.IsGaloisConjugateBy, HeckeRing.GL2.Newform.isGaloisConjugateBy_iff_forall_pnat, HeckeRing.GL2.Newform.isGaloisConjugate_iff_exists_isEmbedding, HeckeRing.GL2.Newform.exists_isGaloisConjugateBy, HeckeRing.GL2.Newform.ncard_galoisOrbit_eq")
*Galois conjugate newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.galois_conjugate))

Two {bpref "cmf.newform"}[newforms] $`f=\sum a_nq^n` and $`g=\sum b_nq^n`  are *Galois conjugate* if there is an automorphism $`\sigma\in \Gal(\overline{\Q}/\Q)` such that $`b_n=\sigma(a_n)` for all $`n\ge 1`, in which case we write $`g=\sigma(f)`.

The set $`\{\sigma(f):\sigma\in\Gal(\overline{\Q}/\Q)\}` of all Galois conjugates of $`f` is the {bpref "cmf.galois_orbit"}[Galois orbit] of $`f`; it has cardinality equal to the {bpref "cmf.dimension"}[dimension] of $`f`, equivalently, the {bpref "nf.degree"}[degree] of its {bpref "cmf.coefficient_field"}[coefficient field]

Depends on: {uses "cmf.newform"}[] {uses "nf.degree"}[]
:::

:::definition "cmf.galois_orbit" (lean := "HeckeRing.GL2.Newform.galoisOrbit, HeckeRing.GL2.NewformOrbit, HeckeRing.GL2.Newform.galoisOrbitRel, HeckeRing.GL2.Newform.finite_galoisOrbit, HeckeRing.GL2.Newform.galoisOrbitBasis, HeckeRing.GL2.Newform.orbit_algebraicClosure_eq_galoisOrbit, HeckeRing.GL2.Newform.orbit_eq_galoisOrbit")
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

:::definition "cmf.hecke_galois_orbit" (lean := "HeckeRing.GL2.NewformOrbit.traceSeq, HeckeRing.GL2.NewformOrbit.letterLabel, HeckeRing.GL2.Newform.exists_int_coeffTrace, HeckeRing.GL2.NewformOrbit.traceSeq_injective, HeckeRing.GL2.NewformOrbit.letterLabel_eq_iff, HeckeRing.GL2.NewformOrbit.image_labelIndex")
*Galois orbit label.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.hecke_galois_orbit))

The {bpref "cmf.galois_orbit"}[Galois orbits] within each {bpref "cmf.newspace"}[space of newforms] $`S^{\rm new}_k(N,[\chi])` are labeled using small roman letters: $`a, b, c, \ldots, z, aa, ba, \ldots`, with orbits ordered according to the lexicographical ordering of their integer trace sequences

$$`({\rm tr}_{K/\Q}(a_1),\ {\rm tr}_{K/\Q}(a_2), {\rm tr}_{K\Q}(a_3),\ \ldots)`

obtained by taking traces of Hecke eigenvalues $`a_1,a_2,\ldots` from the coefficient field $`K` down to $`\Q`.

Depends on: {uses "cmf.galois_orbit"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.hecke_kernels" (lean := "HeckeRing.GL2.Newform.heckeKernel, HeckeRing.GL2.Newform.mem_heckeKernel, HeckeRing.GL2.Newform.map_iInf_heckeKernel, HeckeRing.GL2.Newform.map_iInf_heckeKernel_eq_newformSubspace_inf, HeckeRing.GL2.Newform.coeffMinpoly")
*Hecke kernel.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.hecke_kernels))

Each {bpref "cmf.newform"}[newform] $`f=\sum a_n^n` necessarily lies in the kernel of the linear operator $`g_n(T_n)`, where $`g_n\in \Z[X]` is the minimal polynomial of $`a_n` and $`T_n` is the $`n`th {bpref "cmf.hecke_operator"}[Hecke operator] acting on the {bpref "cmf.newspace"}[newspace] $`S_k^{\rm new}(N,\chi)` in which $`f` lies.

If $`X` is a set of {bpref "cmf.distinguishing_primes"}[distinguishing primes] for $`S^{\rm new}_k(N,\chi)`, then the {bpref "cmf.galois_orbit"}[Galois orbit] of $`f` can be uniquely identified as the intersection of the kernels of the linear operators $`\{g_p(T_p):p \in X\}`.

This characterization allows one to reconstruct the newform $`f` without computing a basis of newforms for $`S_k^{\rm new}(N,\chi)`, which may be computationally useful when the {bpref "cmf.dimension"}[dimension] of $`f` is much smaller than that of $`S_k^{\rm new}(N,\chi)`.

Depends on: {uses "cmf.dimension"}[] {uses "cmf.distinguishing_primes"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.hecke_operator" (lean := "HeckeRing.GL2.heckeRingHomCharSpace, HeckeRing.GL2.heckeTCompositeGamma0, HeckeRing.GL2.heckeTNat")
*Hecke operator.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.hecke_operator))

Let $`f` be a {bpref "cmf"}[modular form] of {bpref "cmf.weight"}[weight] $`k`, {bpref "cmf.level"}[level] $`N`, and {bpref "character.dirichlet"}[character] $`\chi`.

For each positive integer $`n` the *Hecke operator* $`T_n` is a linear operator on the vector space $`M_k(N,\chi)` whose action on $`f\in M_k(N,\chi)` can be defined as follows. If  $`f(z)=\sum a_n (f)q^n` is the {bpref "cmf.q-expansion"}[$`q`-expansion] of $`f\in M_k(N,\chi)`, where $`q=e^{2\pi i z}`, then the $`q`-expansion of $`T_nf\in M_k(N,\chi)` has coefficients

$$`a_m(T_nf) := \sum_{d|\gcd(m,n)}\chi(d)d^{k-1}a_{mn/d^2}(f).`

The Hecke operators pairwise commute, and when restricted to the subspace $`S_k(N,\chi)` of {bpref "cmf.cusp_form"}[cusp forms], they commute with their adjoints with respect to the {bpref "cmf.petersson_scalar_product"}[Petersson scalar product].  This implies that $`S_k(N,\chi)` has a canonical basis whose elements are eigenforms for all the Hecke operators.  If we normalize such an eigenform $`f(z)=\sum a_n q^n` so that $`a_1=1`, then for all $`n\ge 1` we have

$$`T_n f = a_nf.`

The {bpref "cmf.newspace"}[newspace] $`S_k^{\rm new}(N,\chi)\subseteq S_k(N,\chi)` is invariant under the action of the Hecke operators, so the canonical basis of normalized eigenforms for $`S_k(N,\chi)` includes a basis of {bpref "cmf.newform"}[newforms] for $`S_k^{\rm new}(N,\chi)`.

Tau Ceti Review: [`HeckeRing.GL2.heckeRingHomCharSpace`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.heckeRingHomCharSpace), [`HeckeRing.GL2.heckeTCompositeGamma0`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.heckeTCompositeGamma0), [`HeckeRing.GL2.heckeTNat`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.heckeTNat).

Depends on: {uses "character.dirichlet"}[] {uses "cmf"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.petersson_scalar_product"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.hecke_orbit" (lean := "HeckeRing.GL2.heckeRingHomCuspCharSpace, HeckeRing.GL2.heckeTCuspNat, HeckeRing.GL2.Newform.newformSubspace, HeckeRing.GL2.Newform.heckeTCuspNat_mem_newformSubspace")
*Hecke orbit.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.hecke_orbit))

The *Hecke orbit* of a {bpref "cmf.cusp_form"}[cusp form] $`f` in $`S_k(N,\chi)` is defined as the
space generated by $`T_p(f)` for all {bpref "cmf.hecke_operator"}[Hecke operators] $`T_p` for $`p` coprime to the {bpref "cmf.level"}[level].

Tau Ceti Review: [`HeckeRing.GL2.heckeRingHomCuspCharSpace`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.heckeRingHomCuspCharSpace), [`HeckeRing.GL2.heckeTCuspNat`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.heckeTCuspNat).

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.level"}[]
:::

:::definition "cmf.hecke_ring_generators" (lean := "HeckeRing.GL2.Newform.coefficientRingGeneratorBound, HeckeRing.GL2.Newform.truncCoefficientRing, HeckeRing.GL2.Newform.truncCoefficientRing_coefficientRingGeneratorBound, HeckeRing.GL2.Newform.coefficientRingGeneratorBound_le, HeckeRing.GL2.Newform.nonempty_truncCoefficientRing_eq")
*Coefficient ring generator bound.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.hecke_ring_generators))

The *coefficient ring generator bound* of a {bpref "cmf.newform"}[newform] with {bpref "cmf.q-expansion"}[$`q`-expansion] $`\sum a_nq^n` is the least positive integer $`n` such that $`\Z[a_1,\ldots,a_n]` is the entire {bpref "cmf.coefficient_ring"}[coefficient ring] $`\Z[a_1,a_2,a_3,\ldots]`.

Depends on: {uses "cmf.coefficient_ring"}[] {uses "cmf.newform"}[] {uses "cmf.q-expansion"}[]
:::

:::definition "cmf.heckecharpolys" (lean := "HeckeRing.GL2.Newform.heckeCharpoly, HeckeRing.GL2.Newform.heckeCharpoly_eq_prod, HeckeRing.GL2.Newform.IsGaloisConjugate.heckeCharpoly_eq, HeckeRing.GL2.heckeTCuspNat")
*Hecke characteristic polynomial.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.heckecharpolys))

The *Hecke characteristic polynomial* of a {bpref "cmf.newform"}[newform] $`f` at a prime $`p` is the characteristic polynomial of the {bpref "cmf.hecke_operator"}[Hecke operator] $`T_p` acting on the {bpref "cmf.newform_subspace"}[newform subspace] $`V_f`.

Tau Ceti Review: [`HeckeRing.GL2.heckeTCuspNat`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.heckeTCuspNat).

Depends on: {uses "cmf.hecke_operator"}[] {uses "cmf.newform"}[] {uses "cmf.newform_subspace"}[]
:::

:::definition "cmf.inner_twist" (lean := "HeckeRing.GL2.Newform.IsInnerTwist, HeckeRing.GL2.Newform.HasInnerTwist, HeckeRing.GL2.Newform.innerTwists, HeckeRing.GL2.Newform.mk_self_mem_innerTwists_iff, HeckeRing.GL2.Newform.mk_ringHomComp_mem_innerTwists, HeckeRing.GL2.Newform.mk_mem_innerTwists_iff_exists_mem_innerTwistGroup, HeckeRing.GL2.Newform.eq_of_mk_mem_innerTwists")
*Inner twist.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.inner_twist))

{bpref "cmf.galois_conjugate"}[Galois conjugate] {bpref "cmf.newform"}[newforms] $`f` and $`g` are *inner twists* if there is a {bpref "character.dirichlet"}[Dirichlet character] $`\chi` such that

$$`a_p(g) = \chi(p)a_p(f)`

for all but finitely many primes $`p`.  Without loss of generality, we may assume that $`\chi` is a {bpref "character.dirichlet.primitive"}[primitive] Dirichlet character, and by a theorem of Ribet , the newform $`g` is conjugate to $`f` via a $`\Q`-automorphism $`\sigma` of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f`.  The set of pairs $`(\chi,\sigma)` form the {bpref "cmf.inner_twist_group"}[group of inner twists] of $`f`.

Each pair $`(\chi,\sigma)` corresponding to an inner twist of $`f` is uniquely determined by the the primitive character $`\chi`, and we say that $`f` admits an inner twist by $`\chi`.  When $`\sigma=1` is is the trivial automorphism, we have $`g=f` and say that $`f` admits a {bpref "cmf.self_twist"}[self twist] by $`\chi`; in this case $`\chi` is either the trivial character or the Kronecker character of a quadratic field.

The {bpref "cmf.inner_twist_count"}[number] of inner twists of $`f` is an invariant of its {bpref "cmf.galois_orbit"}[Galois orbit], as is the number of inner twists by characters in any particular {bpref "character.dirichlet.galois_orbit"}[Galois orbit of Dirichlet characters].

The home page of each newform in the LMFDB includes a list of inner twists, in which non-trivial self twists are distinguished by listing the associated quadratic field (the {bpref "cmf.cm_form"}[CM] or {bpref "cmf.rm_form"}[RM] field), while inner twists that are not self twists are simply marked as "inner".

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.cm_form"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.galois_conjugate"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "cmf.rm_form"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.inner_twist_count" (lean := "HeckeRing.GL2.Newform.innerTwistCount, HeckeRing.GL2.Newform.innerTwists, HeckeRing.GL2.Newform.IsGaloisConjugateBy.innerTwistCount_eq, HeckeRing.GL2.Newform.innerTwistCount_eq_natCard, HeckeRing.GL2.Newform.finite_innerTwists, HeckeRing.GL2.Newform.innerTwistGroup")
*Inner twist count.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.inner_twist_count))

The *inner twist count* of a {bpref "cmf.newform"}[newform] $`f` is the number of distinct {bpref "cmf.inner_twist"}[inner twists] of $`f`.

Associated to each inner twist is a pair $`(\chi,\sigma)`, where $`\chi` is a primitive {bpref "character.dirichlet"}[Dirichlet character] and $`\sigma` is a $`\Q`-automorphism of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f`.

Pairs with $`\sigma=1` are {bpref "cmf.self_twist"}[self twists] $`(\chi,1)`, including the pair $`(1,1)` corresponding to the twist of $`f` by the trivial character; self twists are included in the count of inner twists.

The set of pairs $`(\chi,\sigma)` forms the {bpref "cmf.inner_twist_group"}[group of inner twists]; the inner twist count is the cardinality of this group.

Not all of the inner twists included in the inner twist count have necessarily been {bpref "cmf.inner_twist_proved"}[proved]; those that have are explicitly identified in the table of inner twists on the newforms home page.  In cases where not every inner twist has been proved the inner twist should be viewed as a rigorous upper bound that is believed to be tight.

Inner twist data is available only for newforms for which exact eigenvalue data has been computed; this includes all newforms of {bpref "cmf.dimension"}[dimension] up to $`20` and all newforms of {bpref "cmf.weight"}[weight] 1; when the inner twist count is specified in a search the results include only newforms for which inner twists have been computed.

Depends on: {uses "character.dirichlet"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.dimension"}[] {uses "cmf.inner_twist"}[] {uses "cmf.newform"}[] {uses "cmf.self_twist"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.inner_twist_group" (lean := "HeckeRing.GL2.Newform.innerTwistGroup, HeckeRing.GL2.Newform.innerTwistGroup_mul_fst, HeckeRing.GL2.Newform.innerTwistGroupToAut, HeckeRing.GL2.Newform.mem_ker_innerTwistGroupToAut_iff, HeckeRing.GL2.Newform.isMulCommutative_range_innerTwistGroupToAut, HeckeRing.GL2.Newform.innerTwistGroup_fst_injective")
*Inner twist group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.inner_twist_group))

For a given {bpref "cmf.newform"}[newform] $`f`, the set of pairs $`(\chi,\sigma)` giving rise to an {bpref "cmf.inner_twist"}[inner twist] of $`f` form a group $`G`; here $`\chi` is a {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet"}[Dirichlet character] and $`\sigma`, is a $`\Q`-automorphism of the {bpref "cmf.coefficient_field"}[coefficient field] $`K` of $`f`.

The group operation is given by

$$`(\chi,\sigma)\cdot (\chi',\sigma') = (\chi\sigma(\chi'),\sigma\sigma').`

The projection map $`(\chi,\sigma)\mapsto \sigma` is a group homomorphism $`G\to \Aut_{\Q}(K)` with kernel equal to the subgroup of {bpref "cmf.self_twist"}[self\_twists] and abelian image.

The projection map $`(\chi,\sigma)\mapsto \chi` is injective, but it is not a group homomorphism, in general, although its restriction to the subgroup of self twists is.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.inner_twist"}[] {uses "cmf.newform"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.inner_twist_multiplicity" (lean := "HeckeRing.GL2.Newform.innerTwistMultiplicity, HeckeRing.GL2.Newform.HasInnerTwist, HeckeRing.GL2.Newform.IsGaloisConjugateBy.innerTwistMultiplicity_eq, MulChar.galoisOrbit")
*Inner twist multiplicity.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.inner_twist_multiplicity))

It is possible for a {bpref "cmf.newform"}[newform] $`f` to admit an {bpref "cmf.inner_twist"}[inner twist] by more than one {bpref "character.dirichlet"}[Dirichlet character] $`\varphi` in the same {bpref "character.dirichlet.galois_orbit"}[Galois orbit].  Different {bpref "cmf.embedding"}[embeddings] of $`f` into $`\C` will yield different $`\varphi`, but the number of such $`\varphi` is the same for every embedding; this number is the *multiplicity*.

Tau Ceti Review: [`MulChar.galoisOrbit`](https://taucetiproject.org/review/#/d/MulChar.galoisOrbit).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "cmf.embedding"}[] {uses "cmf.inner_twist"}[] {uses "cmf.newform"}[]
:::

:::definition "cmf.inner_twist_proved"
*Inner twist proved.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.inner_twist_proved))

In order to prove that a {bpref "cmf.newform"}[newform] $`f\in S_k(N,\chi)` admits an {bpref "cmf.inner_twist"}[Inner twist] by a {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet"}[Dirichlet character] $`\phi` it is sufficient to verify that for some Galois conjugate newform $`g\ne f` the equality

$$`a_p(g)=\varphi(p)a_p(f)`

holds for all primes $`p\le B` not dividing the level of $`f` or the conductor of $`\varphi`, where $`B` is the {bpref "cmf.sturm_bound"}[Sturm bound] for the level

$$`\mathrm{lcm}(N,\mathrm{cond}(\varphi)^2,\mathrm{cond}(\varphi)\mathrm{cond}(\chi)).`

In cases where it is not feasible to test this equality, it is still checked at least up to the Sturm bound for level $`N`, and for all primes $`p\le 1000`.

The set of inner twists listed for a newform in the LMFDB is always guaranteed to contain all possible inner twists, regardless of whether or not all the listed inner twists have been proved (false positives are, in principle, possible, but not false negatives).  In particular, if no inner twists are listed then the newform provably does not admit any inner twists.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.inner_twist"}[] {uses "cmf.newform"}[] {uses "cmf.sturm_bound"}[]
:::

:::definition "cmf.label"
*Label of a classical modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.label))

The *label* of a {bpref "cmf.newform"}[newform] $`f\in S_k^{\rm new}(N,\chi)` has the format $`N.k.a.x`, where

- $`N` is the {bpref "cmf.level"}[level];

- $`k` is the {bpref "cmf.weight"}[weight];

- $`N.a` is the {bpref "character.dirichlet.galois_orbit_label"}[label] of the {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi`;

- $`x` is the {bpref "cmf.hecke_galois_orbit"}[label] of the {bpref "cmf.galois_orbit"}[Galois orbit] of the newform $`f`.

For each {bpref "cmf.embedding"}[embedding] of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f` into the complex numbers, the corresponding modular form over $`\C` has a label of the form $`N.k.a.x.n.i`, where

- $`n` determines the {bpref "character.dirichlet.conrey"}[Conrey label] $`N.n` of the Dirichlet character $`\chi`;

- $`i` is an integer ranging from 1 to the {bpref "cmf.relative_dimension"}[relative dimension] of the newform that distinguishes embeddings with the same character $`\chi`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_label"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.embedding"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.relative_dimension"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.labels"
*Label of a classical modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.labels))

The *label* of a {bpref "cmf.new_subspaces"}[$`f\in M_k^{\\rm new}(N,\chi)`] has the format $`N.k.A.a.x`, where

- $`N` is the {bpref "cmf.level"}[level];

- $`k` is the {bpref "cmf.weight"}[weight];

- $`N.a` is the {bpref "character.dirichlet.galois_orbit_label"}[label] of the {bpref "character.dirichlet.galois_orbit"}[Galois orbit] of the {bpref "character.dirichlet"}[Dirichlet character] $`\chi`;

- $`A` is a character signifying the automorphic type of the modular form - $`E` for Eisenstein or $`C` for cuspidal.

- $`x` is the {bpref "cmf.hecke_galois_orbit"}[label] of the {bpref "cmf.galois_orbit"}[Galois orbit] of the newform $`f`.

For each {bpref "cmf.embedding"}[embedding] of the {bpref "cmf.coefficient_field"}[coefficient field] of $`f` into the complex numbers, the corresponding modular form over $`\C` has a label of the form $`N.k.A.a.x.n.i`, where

- $`n` determines the {bpref "character.dirichlet.conrey"}[Conrey label] $`N.n` of the Dirichlet character $`\chi`;

- $`i` is an integer ranging from 1 to the {bpref "cmf.relative_dimension"}[relative dimension] of the newform that distinguishes embeddings with the same character $`\chi`.

If $`f \in S_k^{\rm new}(N, \chi)` is cuspidal, the automorphic type may be omitted from both labels.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.galois_orbit_label"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.embedding"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.level"}[] {uses "cmf.relative_dimension"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.level" (lean := "ModularForm.IsLevel, ModularForm.isLevel_iff, HeckeRing.GL2.Newform.level, HeckeRing.GL2.Newform.level_le, CongruenceSubgroup.Gamma")
*Level of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.level))

A *level* of a {bpref "cmf"}[modular form] $`f` is a positive integer $`N` such that $`f` is a modular form on a subgroup $`\Gamma` of {bpref "group.sl2z"}[$`\operatorname{SL}_2(\mathbb{Z})`] that contains the principal congruence subgroup {bpref "group.sl2z.subgroup.gamman"}[$`\Gamma(N)`].

The *level* of a {bpref "cmf"}[newform] is the least such integer $`N`.

Tau Ceti Review: [`CongruenceSubgroup.Gamma`](https://taucetiproject.org/review/#/d/CongruenceSubgroup.Gamma).

Depends on: {uses "cmf"}[] {uses "group.sl2z"}[]
:::

:::definition "cmf.lfunction" (lean := "HeckeRing.GL2.Newform.analyticL, HeckeRing.GL2.Newform.hasSum_analyticL, HeckeRing.GL2.Newform.analyticL_eulerProduct, HeckeRing.GL2.Newform.analyticCompletedL, HeckeRing.GL2.Newform.rootNumber, HeckeRing.GL2.Newform.analyticCompletedL_eq_rootNumber_mul")
*L-function of a classical modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.lfunction))

For a {bpref "cmf.newform"}[newform] $`f\in S_k^{\rm new}(N,\chi)` with {bpref "cmf.q-expansion"}[q-expansion] $`f(z)=\sum a_n n^{(k-1)/2}q^n`, where $`q=\exp(2\pi i z)`, the {bpref "lfunction"}[L-function] $`L(s,f) = \sum a_n n^{-s}` has an {bpref "lfunction.euler_product"}[Euler product] of the form

$$`L(s,f)= \prod_{p\mid N} \left(1 - a_p p^{-s}
\right)^{-1}\prod_{p\nmid N} \left(1 - a_p p^{-s} + \chi(p) \cdot p^{-2s}
\right)^{-1}`

and satisfies the {bpref "lfunction.functional_equation"}[functional equation]

$$`\Lambda(s,f) = N^{s/2} \Gamma_{\mathbb{C}
} \left(s + \frac{k-1}{2} \right)\cdot L(s, f) = \varepsilon
\overline{\Lambda}(1-s,f),`

where $`\varepsilon` is the {bpref "lfunction.sign"}[sign] of the
functional equation and $`\Gamma_{\C}(s+(k-1)/2)` is its {bpref "lfunction.gamma_factor"}[gamma factor].  When $`\chi` is the trivial character, $`\varepsilon=\pm 1`, and in general it is a root of unity.

Depends on: {uses "cmf.newform"}[] {uses "cmf.q-expansion"}[] {uses "lfunction"}[] {uses "lfunction.euler_product"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.gamma_factor"}[] {uses "lfunction.sign"}[]
:::

:::definition "cmf.maximal" (lean := "HeckeRing.GL2.Newform.IsMaximal, HeckeRing.GL2.Newform.IsLargest, HeckeRing.GL2.Newform.ambientSubspace, HeckeRing.GL2.Newform.ambientNewforms, HeckeRing.GL2.Newform.isMaximal_iff")
*Maximal newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.maximal))

A {bpref "cmf.newform"}[newform] is *maximal* if its {bpref "cmf.galois_orbit"}[Galois orbit] spans the ambient subspace that contains it (its {bpref "cmf.atkin_lehner_dims"}[Atkin-Lehner subspace] when the {bpref "cmf.character"}[character] is trivial, the entire newspace otherwise).

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

:::definition "cmf.minus_space" (lean := "TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp")
*Minus space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.minus_space))

The *minus subspace* of $`S_k(\Gamma_0(N))` is the eigenspace of the {bpref "cmf.fricke"}[Fricke involution] $`w_N` with eigenvalue $`-1`.

Tau Ceti Review: [`TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp`](https://taucetiproject.org/review/#/d/TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp).

Depends on: {uses "cmf.fricke"}[]
:::

:::definition "cmf.new_subspaces"
*New subspaces of modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.new_subspaces))

The space $`M_k(N,\chi)` of {bpref "cmf"}[modular forms] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k`, and {bpref "cmf.character"}[character] $`\chi` can be decomposed

$$`M_k(N,\chi) = M_k^{\rm old}(N,\chi) \oplus M_k^{\rm new}(N,\chi)`

into old and new subspaces, defined using the corresponding decompositions of {bpref "cmf.eisenstein_newspace"}[$`E_k(N,\chi)`] and {bpref "cmf.newspace"}[$`S_k(N,\chi)`] as $`M_k^{\rm old}(N,\chi) = E_k^{\rm old}(N,\chi) \oplus S_k^{\rm old}(N, \chi)` and $`M_k^{\rm new}(N,\chi) = E_k^{\rm new}(N,\chi) \oplus S_k^{\rm new}(N, \chi)`.

Depends on: {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.eisenstein_newspace"}[] {uses "cmf.level"}[] {uses "cmf.newspace"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.newform" (lean := "HeckeRing.GL2.Newform, HeckeRing.GL2.Newform.basis, HeckeRing.GL2.Newform.toEigenform, TauCeti.cuspFormsNew")
*Newform.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.newform))

A *newform* is a cusp form $`f\in S_k^{\rm new}(N,\chi)` in the {bpref "cmf.newspace"}[new subspace] that is also an eigenform of all {bpref "cmf.hecke_operator"}[Hecke operators], normalized so that the {bpref "cmf.fouriercoefficients"}[$`q`-expansion]  $`f(z)=\sum a_n q^n`, where $`q=e^{2\pi i z}`, begins with the coefficient $`a_1=1`.  The newforms are a basis for the new subspace.

Tau Ceti Review: [`HeckeRing.GL2.Newform`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform), [`HeckeRing.GL2.Newform.basis`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.basis), [`HeckeRing.GL2.Newform.toEigenform`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.toEigenform), [`TauCeti.cuspFormsNew`](https://taucetiproject.org/review/#/d/TauCeti.cuspFormsNew).

Depends on: {uses "cmf.fouriercoefficients"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.newform_subspace" (lean := "HeckeRing.GL2.Newform.newformSubspace, HeckeRing.GL2.NewformOrbit.newformSubspace, HeckeRing.GL2.cuspFormsNewGaloisOrbit, HeckeRing.GL2.NewformOrbit.characterOrbit, HeckeRing.GL2.Newform.newformSubspace_le_cuspFormsNewGaloisOrbit, HeckeRing.GL2.NewformOrbit.iSupIndep_newformSubspace_characterOrbit, HeckeRing.GL2.NewformOrbit.iSup_newformSubspace_characterOrbit, HeckeRing.GL2.NewformOrbit.iSupIndep_newformSubspace, HeckeRing.GL2.NewformOrbit.iSup_newformSubspace, HeckeRing.GL2.Newform.heckeTCuspNat_mem_newformSubspace")
*Newform subspace.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.newform_subspace))

The *newform subspace* of a {bpref "cmf.newform"}[newform] $`f` in $`S_k^{\rm new}(N,\chi)` is the subspace generated by the Galois conjugates of $`f`.

Every {bpref "cmf.newspace"}[newspace] has a canonical decomposition into newform subspaces.

Depends on: {uses "cmf.newform"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.newspace" (lean := "TauCeti.cuspFormsNew, TauCeti.cuspFormsOld, cuspFormCharSpace")
*New subspace.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.newspace))

The space $`S_k(N,\chi)` of {bpref "cmf.cusp_form"}[cuspidal] {bpref "cmf"}[modular forms] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k`, and {bpref "cmf.character"}[character] $`\chi` can be decomposed

$$`S_k(N,\chi) = S_k^{\rm old}(N,\chi) \oplus S_k^{\rm new}(N,\chi)`

into old and new subspaces, defined as follows.

If $`M` is a proper divisor of $`N` and $`\chi_M` is a {bpref "character.dirichlet"}[Dirichlet character] of {bpref "character.dirichlet.modulus"}[modulus] $`M` that {bpref "character.dirichlet.induce"}[induces] $`\chi`, then for all $`d \mid (N/M)`, there is a map from $`S_k(M,\chi_M) \to S_k(N,\chi)` via $`f(z) \mapsto f(dz)`.  The span of the images of all of these maps is the *old subspace* $`S_k^{\rm old}(N,\chi) \subseteq S_k(N,\chi)`.

The *new subspace* $`S_k^{\rm new}(N,\chi)` is the orthogonal complement of $`S_k^{\rm old}(N,\chi)` with respect to the {bpref "cmf.petersson_scalar_product"}[Petersson inner product].

A basis for the new subspace is given by {bpref "cmf.newform"}[newforms].

Tau Ceti Review: [`TauCeti.cuspFormsNew`](https://taucetiproject.org/review/#/d/TauCeti.cuspFormsNew), [`TauCeti.cuspFormsOld`](https://taucetiproject.org/review/#/d/TauCeti.cuspFormsOld).

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[] {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.petersson_scalar_product"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.newspaces" (lean := "TauCeti.cuspFormsNew, HeckeRing.GL2.Newform.coeff_smul_algebraicClosure, HeckeRing.GL2.Newform.orbit_algebraicClosure_eq_galoisOrbit, HeckeRing.GL2.Newform.rationalPiece, HeckeRing.GL2.Newform.eq_bot_or_eq_rationalPiece, HeckeRing.GL2.NewformOrbit.iSup_newformSubspace_inf_cuspFormCharSpace")
*Space of newforms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.newspaces))

The {bpref "cmf.newform"}[new part] of the space $`S_k(N,\chi)` of {bpref "cmf.cusp_form"}[cusp forms] of {bpref "cmf.weight"}[weight] $`k`, {bpref "cmf.level"}[level] $`N`, and {bpref "character.dirichlet"}[character] $`\chi` is the space of $`S_k^{\rm new}(N,\chi)` of {bpref "cmf.newform"}[newforms].

It can be decomposed into irreducible subspaces under the action of the {bpref "cmf.hecke_operator"}[Hecke operators], each of which corresponds to a Galois orbit of newforms (the absolute Galois group of $`\Q` acts the set of newforms in $`S_k^{\rm new}(N,\chi)` via its action on the coefficients of {bpref "cmf.fouriercoefficients"}[$`q`-expansions]).

Tau Ceti Review: [`TauCeti.cuspFormsNew`](https://taucetiproject.org/review/#/d/TauCeti.cuspFormsNew).

Depends on: {uses "character.dirichlet"}[] {uses "cmf.cusp_form"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.hecke_operator"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.nk2" (lean := "HeckeRing.GL2.Newform.levelMulWeightSq, HeckeRing.GL2.Newform.tendsto_analyticConductorLMFDB_div_levelMulWeightSq, HeckeRing.GL2.Newform.analyticConductorLMFDB")
*Nk^2.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.nk2))

The integer $`Nk^2` is the product of the {bpref "cmf.level"}[level] and the square of the {bpref "cmf.weight"}[weight] of a {bpref "cmf"}[modular form] or space of modular forms.

Asymptotically (as $`k\to\infty`) this quantity is proportional to the {bpref "cmf.analytic_conductor"}[analytic conductor].

Depends on: {uses "cmf"}[] {uses "cmf.analytic_conductor"}[] {uses "cmf.level"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.nontrivial_twist" (lean := "HeckeRing.GL2.Newform.nontrivialInnerTwists, HeckeRing.GL2.Newform.ncard_nontrivialInnerTwists")
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

:::definition "cmf.petersson_scalar_product" (lean := "ModularForm.peterssonScalarProduct, ModularForm.peterssonScalarProduct_eq_integral, ModularForm.integrableOn_of_isCuspForm, ModularForm.peterssonScalarProduct_coe_coe, UpperHalfPlane.petersson")
*Petersson scalar product.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.petersson_scalar_product))

Let $`f` and $`g` be two modular forms with respect to a {bpref "group.subgroup.index"}[finite index] subgroup $`G` of $`\Gamma`. When it exists, we define the
*Petersson scalar product* of $`f` and $`g` with respect to the group $`G`
by

$$`\langle
f,g\rangle_G=\frac{1}{[\Gamma:G]}\int_{\mathfrak{F}}f(z)\overline{
g(z)}y^kd\mu,`

where $`\mathfrak{F}` is a {bpref "group.fuchsian.fundamental_domain"}[fundamental domain] for $`G` and $`d\mu=dxdy/y^2` is the measure associated to the hyperbolic metric.

Note that the Petersson scalar product exists if at least one of $`f`, $`g` is a {bpref "cmf.cusp_form"}[cusp form].

Tau Ceti Review: [`UpperHalfPlane.petersson`](https://taucetiproject.org/review/#/d/UpperHalfPlane.petersson).

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.petersson_scalar_product_mathlib_def"}[] {uses "group.fuchsian.fundamental_domain"}[] {uses "group.subgroup.index"}[]
:::

:::definition "cmf.petersson_scalar_product_mathlib_def" (lean := "UpperHalfPlane.petersson")
*Petersson scalar product (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.petersson_scalar_product_mathlib_def))

The mathlib definition *petersson* defines only the integrand of the Petersson scalar product. Mathlib uses the conjugate of the first argument, whereas the LMFDB definition uses the conjugate of the second argument.

Tau Ceti Review: [`UpperHalfPlane.petersson`](https://taucetiproject.org/review/#/d/UpperHalfPlane.petersson).
:::

:::definition "cmf.picture_description" (lean := "UpperHalfPlane.portraitMoebius, UpperHalfPlane.bijOn_portraitMoebius, UpperHalfPlane.portraitMoebiusMatrix, UpperHalfPlane.portraitMoebiusMatrix_smul_coe, HeckeRing.GL2.Newform.traceForm, HeckeRing.GL2.Newform.newspaceTraceForm, Complex.arg_eq_pi_iff")
*Pictures for classical modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.picture_description))

For each {bpref "cmf.newform"}[newform] or {bpref "cmf.trace_form"}[trace form], we use domain coloring to plot the associated trace form $`\mathrm{Tr}(f)`.

At each point $`z` in the unit disk $`\mathcal{D}`, we assign a color based on the value of $`\mathrm{Tr}(f)(\mu(z))`, where $`\mu` is the Möbius transform $`\mu: \mathcal{D} \longrightarrow \mathcal{H}` given by $`\mu(z) = \frac{1 - iz}{z - i}`. Writing $`\mathrm{Tr}(f)(\mu(z)) = r e^{i \theta}`, the color is determined entirely by the argument $`\theta`.

The color starts as a dull mustard yellow at $`\theta = 0` and becomes brighter and more yellow as $`\theta` increases towards $`\pi`. There is a sharp change at $`\theta = \pi` from bright yellow to slate blue. As $`\theta` increases from $`\pi` to $`2 \pi`, the slate blue dulls back towards mustard yellow. This coloration has the effect of sharply changing when the trace form takes on negative real values. These strong patterns highlight the matrix periodicity of the form.

*Implementation ##*

The pictures of modular forms were implemented by David Lowry-Duda following the "pure phase plots" described in \*Visualizing Modular Forms\* by Lowry-Duda .

Tau Ceti Review: [`Complex.arg_eq_pi_iff`](https://taucetiproject.org/review/#/d/Complex.arg_eq_pi_iff).

Depends on: {uses "cmf.newform"}[] {uses "cmf.trace_form"}[]
:::

:::definition "cmf.plus_space" (lean := "TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp")
*Plus space.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.plus_space))

The *plus subspace* of $`S_k(\Gamma_0(N)` is the eigenspace of the {bpref "cmf.fricke"}[Fricke involution] $`\omega_N` with eigenvalue $`1`.

Tau Ceti Review: [`TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp`](https://taucetiproject.org/review/#/d/TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp).

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

:::definition "cmf.q-expansion" (lean := "UpperHalfPlane.qExpansion, CuspFormClass.qExpansion_coeff_zero, HeckeRing.GL2.Newform.orbitQExpansion, HeckeRing.GL2.Newform.map_orbitQExpansion, HeckeRing.GL2.Newform.IsGaloisConjugateBy.map_orbitQExpansion, HeckeRing.GL2.Newform.isIntegral_coeff, HeckeRing.GL2.Newform.numberField_coefficientField")
*q-expansion of a modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.q-expansion))

The *$`q`-expansion* of a modular form $`f(z)` is its {bpref "cmf.fouriercoefficients"}[Fourier expansion] at the {bpref "group.fuchsian.cusps"}[cusp] $`z=i\infty`, expressed as a power series $`\sum_{n=0}^{\infty} a_n q^n` in the variable $`q=e^{2\pi iz}`.

For {bpref "cmf.cusp_form"}[cusp forms], the constant coefficient $`a_0` of the $`q`-expansion is zero.

For {bpref "cmf.newform"}[newforms], we have $`a_1=1` and the coefficients $`a_n` are algebraic integers in a {bpref "nf"}[number field] $`K \subseteq \C`.

Accordingly, we define the *$`q`-expansion* of a {bpref "cmf.galois_orbit"}[newform orbit] $`[f]` to be the $`q`-expansion of any newform $`f` in the orbit, but with coefficients $`a_n \in K` (without an embedding into $`\C`).  Each {bpref "nf.embedding"}[embedding] $`K \hookrightarrow \C` then gives rise to an {bpref "cmf.embedding"}[embedded newform] whose $`q`-expansion has $`a_n \in \C`, as above.

Tau Ceti Review: [`UpperHalfPlane.qExpansion`](https://taucetiproject.org/review/#/d/UpperHalfPlane.qExpansion), [`CuspFormClass.qExpansion_coeff_zero`](https://taucetiproject.org/review/#/d/CuspFormClass.qExpansion_coeff_zero).

Depends on: {uses "cmf.cusp_form"}[] {uses "cmf.fouriercoefficients"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.newform"}[] {uses "cmf.q-expansion_mathlib_def"}[] {uses "group.fuchsian.cusps"}[] {uses "nf"}[] {uses "nf.embedding"}[]
:::

:::definition "cmf.q-expansion_mathlib_def" (lean := "UpperHalfPlane.qExpansion")
*q-expansion of a modular form (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.q-expansion_mathlib_def))

This is *qExpansion* in mathlib. In the LMFDB definition, $`f` is a {bpref "cmf"}[modular form], and its period is assumed to be $`1`. Mathlib is more general: $`f` may be any function from $`\mathcal{H}\to\mathbb{C}` and the period $`h` is an explicit parameter.

Tau Ceti Review: [`UpperHalfPlane.qExpansion`](https://taucetiproject.org/review/#/d/UpperHalfPlane.qExpansion).

Depends on: {uses "cmf"}[]
:::

:::definition "cmf.relative_dimension" (lean := "TauCeti.CharacterField, TauCeti.CoefficientField, HeckeRing.GL2.Newform.relativeDimension, HeckeRing.GL2.Newform.relativeDimension_eq_finrank, TauCeti.CharacterField_le_CoefficientField")
*Relative dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.relative_dimension))

The *relative dimension* of a {bpref "cmf.newform"}[newform] in a space of modular forms $`S_k^{\mathrm{new}}(\Gamma_0(N),\chi)` is the dimension of its coefficient field as an extension of the character field $`\Q(\chi)` (the number field generated by the values of $`\chi`).

Tau Ceti Review: [`TauCeti.CharacterField`](https://taucetiproject.org/review/#/d/TauCeti.CharacterField), [`TauCeti.CoefficientField`](https://taucetiproject.org/review/#/d/TauCeti.CoefficientField), [`TauCeti.CharacterField_le_CoefficientField`](https://taucetiproject.org/review/#/d/TauCeti.CharacterField_le_CoefficientField).

Depends on: {uses "cmf.newform"}[]
:::

:::definition "cmf.rm_form"
*Real multiplication.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.rm_form))

A {bpref "cmf"}[modular form] is said to have *real multiplication* if it admits a {bpref "cmf.self_twist"}[self twist] by the Kronecker character of a real quadratic field.

Only modular forms of weight one can have real multiplication.

Depends on: {uses "cmf"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.satake_angles" (lean := "HeckeRing.GL2.Newform.satakeAngles, HeckeRing.GL2.Newform.normalizedSatakeParameters_eq_map_exp_satakeAngles, HeckeRing.GL2.Newform.satakeAngles_eq_map_arg_satakeParameters, HeckeRing.GL2.Newform.satakeAngles_eq_pair_satakeAngle")
*Satake Angles.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.satake_angles))

The *Satake angles* $`\theta_p = \arg \alpha_p \in [-\pi, \pi]` are the arguments of a complex embedding of the {bpref "cmf.satake_parameters"}[Satake parameters] $`\alpha_p`.

Depends on: {uses "cmf.satake_parameters"}[]
:::

:::definition "cmf.satake_parameters" (lean := "HeckeRing.GL2.Newform.normalizedSatakeParameters, HeckeRing.GL2.Newform.prod_map_one_sub_mul_normalizedSatakeParameters, HeckeRing.GL2.Newform.normalizedSatakeParameters_eq_pair_inv_mul, HeckeRing.GL2.Newform.pOldSpaceHeckeT, HeckeRing.GL2.Newform.det_one_sub_smul_pOldSpaceHeckeT, HeckeRing.GL2.Newform.trace_pOldSpaceHeckeT, HeckeRing.GL2.Newform.prod_map_one_sub_mul_normalizedSatakeParameters_eq_det, HeckeRing.GL2.Newform.finrank_pOldSpace")
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

:::definition "cmf.self_twist_field" (lean := "HeckeRing.GL2.Newform.comp_unitsMap_eq_of_eventually_coeff_eq, HeckeRing.GL2.Newform.HasSelfTwist.isQuadratic_character, HeckeRing.GL2.Newform.HasSelfTwist.exists_kroneckerChar_of_ne_one, HeckeRing.GL2.Newform.eq_one_or_exists_kroneckerChar_of_mk_self_mem_innerTwists, HeckeRing.GL2.Newform.HasSelfTwist.discr, HeckeRing.GL2.Newform.HasSelfTwist.hasCMBy_or_hasRMBy_discr")
*Self twist field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.self_twist_field))

{bpref "cmf.inner_twist"}[Inner twists] that are {bpref "cmf.self_twist"}[self-twists] arise either from the {bpref "character.dirichlet.principal"}[trivial character], or from the {bpref "character.dirichlet.kronecker_symbol"}[Kronecker character] of a quadratic field $`K`.

When $`K` is an imaginary quadratic field the {bpref "cmf.newform"}[newform] is said to have {bpref "cmf.cm_form"}[complex multiplication] (CM) by $`K`, and when $`K` is a real quadratic field the newform is said to have {bpref "cmf.rm_form"}[real multiplication] (RM) by $`K`.

Depends on: {uses "character.dirichlet.kronecker_symbol"}[] {uses "character.dirichlet.principal"}[] {uses "cmf.cm_form"}[] {uses "cmf.inner_twist"}[] {uses "cmf.newform"}[] {uses "cmf.rm_form"}[] {uses "cmf.self_twist"}[]
:::

:::definition "cmf.selfdual" (lean := "CuspForm.IsSelfDual, CuspForm.isSelfDual_iff_forall_conj_div_cpow, HeckeRing.GL2.Newform.IsSelfDual, HeckeRing.GL2.Newform.isTotallyReal_coefficientField_iff, HeckeRing.GL2.Newform.isCMField_coefficientField_iff, HeckeRing.GL2.Newform.numberField_coefficientField")
*Self dual modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.selfdual))

A {bpref "cmf.cusp_form"}[cuspidal modular form] $`f` is said to be *self dual* if the coefficients $`a_n` that appear in its {bpref "cmf.q-expansion"}[$`q`-expansion] are real numbers; equivalently, the {bpref "cmf.lfunction"}[L-function] of the modular form is {bpref "lfunction.self-dual"}[self dual].

The {bpref "cmf.coefficient_field"}[coefficient field] of a {bpref "cmf.newform"}[newform] is either a {bpref "nf.totally_real"}[totally real] number field or a {bpref "nf.cm_field"}[CM field], depending on whether the newform is self dual or not.

Tau Ceti Review: [`HeckeRing.GL2.Newform.IsSelfDual`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.IsSelfDual).

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

:::definition "cmf.sort_order" (lean := "HeckeRing.GL2.AllNewformOrbits, HeckeRing.GL2.AllNewformOrbits.sortKey, HeckeRing.GL2.AllNewformOrbits.sortOrder, HeckeRing.GL2.AllNewformOrbits.sortKey_injective, HeckeRing.GL2.AllNewformOrbits.sortOrderBy, HeckeRing.GL2.AllNewformOrbits.injective_toLex_sortKey, HeckeRing.GL2.NewformOrbit.characterOrbitIndex, HeckeRing.GL2.NewformOrbit.traceSeq")
*Sort order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.sort_order))

By default {bpref "cmf.newform"}[newform] search results are sorted by {bpref "cmf.level"}[level],
{bpref "cmf.weight"}[weight],
{bpref "character.dirichlet.galois_orbit_label"}[character], and
{bpref "cmf.hecke_galois_orbit"}[trace sequence], which defines a complete ordering on the set of all newforms.

If a specific sort key is chosen, results will be sorted first on that key and then by level, weight, character, and trace sequence, so that the sort order is always uniquely determined.

Depends on: {uses "character.dirichlet.galois_orbit_label"}[] {uses "cmf.hecke_galois_orbit"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.space" (lean := "cuspFormCharSpace, modFormCharSpace")
*Spaces of modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.space))

The *space* of {bpref "cmf"}[modular forms] of {bpref "cmf.level"}[level] $`N`, {bpref "cmf.weight"}[weight] $`k`, and {bpref "cmf.character"}[character] $`\chi` is denoted $`M_k(N,\chi)`.

The space $`M_k(N,\chi)` is a finite-dimensional complex vector space which further decmoposes into {bpref "cmf.subspaces"}[subspaces].  In particular, we have a subspace of {bpref "cmf.cusp_form"}[cusp forms] $`S_k(N,\chi) \subseteq M_k(N,\chi)`.

Depends on: {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.cusp_form"}[] {uses "cmf.level"}[] {uses "cmf.space_mathlib_def"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.space_mathlib_def" (lean := "ModularForm")
*Spaces of modular forms (mathlib).* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.space_mathlib_def))

This is *ModularForm $`\Gamma` $`k`* in mathlib. The LMFDB definition is specified by a level $`N`, weight $`k`, and character $`\chi`, whereas the mathlib definition is specified by a subgroup $`\Gamma` and weight $`k`, with no character.

For $`\Gamma=\Gamma_0(N)`, the mathlib space corresponds to $`M_k(N,1)`, the space of modular forms with trivial character.

For $`\Gamma=\Gamma_1(N)`, recall the decomposition $`M_k(\Gamma_1(N))=\bigoplus_{\chi\bmod N} M_k(N,\chi)` where only characters satisfying $`\chi(-1)=(-1)^k` can contribute to nonzero summands. Hence the mathlib space for $`M_k(\Gamma_1(N))` is the direct sum of the corresponding character spaces from the LMFDB.

Tau Ceti Review: [`ModularForm`](https://taucetiproject.org/review/#/d/ModularForm).
:::

:::definition "cmf.space_trace_form" (lean := "HeckeRing.GL2.Newform, HeckeRing.GL2.Newform.basis, HeckeRing.GL2.Newform.newspaceTraceForm")
*Trace form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.space_trace_form))

The *trace form* of a {bpref "cmf.newspace"}[newspace] $`S_k(N,\chi)` is the modular form obtained by summing its canonical basis of {bpref "cmf.newform"}[newforms].

Tau Ceti Review: [`HeckeRing.GL2.Newform`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform), [`HeckeRing.GL2.Newform.basis`](https://taucetiproject.org/review/#/d/HeckeRing.GL2.Newform.basis).

Depends on: {uses "cmf.newform"}[] {uses "cmf.newspace"}[]
:::

:::definition "cmf.stark_unit"
*Stark unit of a newform of weight one.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.stark_unit))

Stark's conjecture applied to the associated {bpref "cmf.galois_representation"}[Galois representation] of a {bpref "cmf.newform"}[newform] $`f(z)=\sum a_n q^n` of {bpref "cmf.weight"}[weight] one  states the following. Let $`E=\mathbb{Q}((a_n)_{n \in \mathbb{N}})`, $`\Delta=\text{Gal}(E/\mathbb{Q})` and $`f^\alpha(z)=\sum \alpha(a_n) q^n` for $`\alpha \in \Delta`. Let $`L(s, f)` be the {bpref "cmf.lfunction"}[L-function] of $`f`. Then, for all $`b \in E^*` there exists an integer $`m \geq 1` and a unit $`\varepsilon` in the {bpref "cmf.artin_field"}[Artin field] of $`f`, called the *Stark unit*, such that

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

The *cuspidal subspace* decomposes as

$$`S_k(N,\chi) = S_k^{\rm new}(N,\chi) \oplus S_k^{\rm old}(N,\chi)`

where the *new subspace* $`S_k^{\rm new}(N,\chi)` is the orthogonal complement of $`S_k^{\rm old}(N,\chi)` with respect to the {bpref "cmf.petersson_scalar_product"}[Petersson inner product].

The Eisenstein subspace similarly decomposes as

$$`E_k(N,\chi) = E_k^{\rm new}(N,\chi) \oplus E_k^{\rm old}(N,\chi)`

where $`E_k^{\rm new}(N,\chi)` is the span of those Eisenstein series attached to a pair $`(\chi_1,\chi_2)` of (primitive) characters of {bpref "character.dirichlet.conductor"}[conductor] $`N`.

Depends on: {uses "character.dirichlet"}[] {uses "character.dirichlet.conductor"}[] {uses "character.dirichlet.induce"}[] {uses "character.dirichlet.modulus"}[] {uses "cmf"}[] {uses "cmf.character"}[] {uses "cmf.cusp_form"}[] {uses "cmf.cusp_form_subspace_mathlib_def"}[] {uses "cmf.level"}[] {uses "cmf.petersson_scalar_product"}[] {uses "cmf.space"}[] {uses "cmf.weight"}[]
:::

:::definition "cmf.trace_bound" (lean := "HeckeRing.GL2.Newform.traceBound, HeckeRing.GL2.Newform.TracesDistinguishNewforms, HeckeRing.GL2.Newform.exists_tracesDistinguishNewforms, HeckeRing.GL2.Newform.tracesDistinguishNewforms_traceBound, HeckeRing.GL2.Newform.coeffTrace_one_eq_dimension, HeckeRing.GL2.Newform.traceBound_eq_one_of_dimension")
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

:::definition "cmf.twist_multiplicity" (lean := "HeckeRing.GL2.Newform.twistMultiplicity, HeckeRing.GL2.Newform.IsGaloisConjugateBy.twistMultiplicity_eq, HeckeRing.GL2.Newform.IsGaloisConjugate.twistMultiplicity_eq, MulChar.galoisOrbit, HeckeRing.GL2.Newform.twistMultiplicity_self_eq_innerTwistMultiplicity")
*Twist multiplicity.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.twist_multiplicity))

The *multiplicity* of a {bpref "cmf.galois_orbit"}[newform orbit] $`[g]` as a {bpref "cmf.twist"}[twist] of a newform orbit $`[f]` by a {bpref "character.dirichlet.primitive"}[primitive] {bpref "character.dirichlet.galois_orbit"}[character orbit] $`[\psi]` is the number of distinct $`\psi\in[\psi]` for which $`f\otimes\psi\in[g]`.  This number is the same for every $`f\in [f]` and depends only on the Galois orbits $`[g]`, $`[f]`, and $`[\psi]`.

When $`g` is an {bpref "cmf.inner_twist"}[inner twist] of $`f`, this multiplicity is equal to the {bpref "cmf.inner_twist_count"}[inner twist count] of $`f`.

Tau Ceti Review: [`MulChar.galoisOrbit`](https://taucetiproject.org/review/#/d/MulChar.galoisOrbit).

Depends on: {uses "character.dirichlet.galois_orbit"}[] {uses "character.dirichlet.primitive"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.inner_twist"}[] {uses "cmf.inner_twist_count"}[] {uses "cmf.twist"}[]
:::

:::definition "cmf.weight" (lean := "ModularForm.HasWeight, ModularForm.HasWeight.unique, ModularForm.mem_modFormCharSpace_iff_hasWeight, ModularForm.thetaFactor, ModularForm.weightFactor")
*Weight of an elliptic modular form.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/cmf.weight))

The *weight* of an elliptic {bpref "cmf"}[modular form] $`f` is the integer or half-integer power of $`(cz+d)` that occurs in the modular transformation property of $`f` under the action of $`\gamma = \left( \begin{array}{ll}  a & b \\ c & d \end{array}\right)` on the upper half plane.  That is, the weight is the number $`k`
in the transformation law

$$`f\left( \frac{a z + b}{c z + d} \right) = \chi(d)(c z + d)^k f(z) .`

Depends on: {uses "cmf"}[]
:::

:::definition "portrait.cmf" (lean := "UpperHalfPlane.portraitMoebius, UpperHalfPlane.bijOn_portraitMoebius, UpperHalfPlane.portraitMoebiusMatrix, UpperHalfPlane.portraitMoebiusMatrix_smul_coe, HeckeRing.GL2.Newform.traceForm, HeckeRing.GL2.Newform.newspaceTraceForm, Complex.arg_eq_pi_iff")
*Pictures for classical modular forms.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/portrait.cmf))

For each {bpref "cmf.newform"}[newform] or {bpref "cmf.trace_form"}[trace form], we use domain coloring to plot the associated trace form $`\mathrm{Tr}(f)`.

At each point $`z` in the unit disk $`\mathcal{D}`, we assign a color based on the value of $`\mathrm{Tr}(f)(\mu(z))`, where $`\mu` is the Möbius transform $`\mu: \mathcal{D} \longrightarrow \mathcal{H}` given by $`\mu(z) = \frac{1 - iz}{z - i}`. Writing $`\mathrm{Tr}(f)(\mu(z)) = r e^{i \theta}`, the color is determined entirely by the argument $`\theta`.

The color starts as a dull mustard yellow at $`\theta = 0` and becomes brighter and more yellow as $`\theta` increases towards $`\pi`. There is a sharp change at $`\theta = \pi` from bright yellow to slate blue. As $`\theta` increases from $`\pi` to $`2 \pi`, the slate blue dulls back towards mustard yellow. This coloration has the effect of sharply changing when the trace form takes on negative real values. These strong patterns highlight the matrix periodicity of the form.

*Implementation ##*

The pictures of modular forms were implemented by David Lowry-Duda following the "pure phase plots" described in \*Visualizing Modular Forms\* by Lowry-Duda .

Tau Ceti Review: [`Complex.arg_eq_pi_iff`](https://taucetiproject.org/review/#/d/Complex.arg_eq_pi_iff).

Depends on: {uses "cmf.newform"}[] {uses "cmf.trace_form"}[]
:::

:::definition "rcs.cande.cmf"
*Completeness of Classical Modular Form Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.cande.cmf))

The classical modular form database currently contains information for all {bpref "cmf.newform"}[newforms] $`f\in S_k^\mathrm{new}(N,\chi)` of {bpref "cmf.level"}[level] $`N\ge 1`, {bpref "cmf.weight"}[weight] $`k\ge 1`, {bpref "cmf.character"}[character] $`\chi\colon (\Z/N\Z)^\times\to \C`,
for which any of the following hold:

- $`Nk^2\le 4000`;

- $`\chi` trivial and $`Nk^2\le 40\,000`;

- $`N \le 24` and $`Nk^2 \le 40\,000`;

- $`N \le 10` and $`Nk^2 \le 100\,000`;

- $`N \le 100` and $`k \le 12`;

- $`k > 1` and $`\dim S_k^{\rm new}(N,\chi) \le 100` and $`Nk^2 \le 40\,000`.

- $`k = 2`, $`\chi` is trivial, and $`N\le 50\,000` or $`N \le 10^6` is prime.

In addition to the {bpref "cmf.newspace"}[newspaces] identified above, there are 131 newspaces that are present because they contain the {bpref "cmf.minimal_twist"}[minimal twist] of a newform in one of the newspaces above.

For each newform with {bpref "cmf.q-expansion"}[q-expansion] $`f=\sum a_nq^n` the database contains the integers $`\mathrm{tr}(a_n)` for $`1\le n \le 1000`, and when the level is at most $`10\,000` and the {bpref "cmf.dimension"}[dimension] of $`f` is at most $`20`, the algebraic integers $`a_n` for $`1\le n \le 1000` expressed in terms of an explicit basis for the {bpref "cmf.coefficient_ring"}[coefficient ring] $`\Q(f)`.  For $`1000 < N \le 4000` this data is available for all $`n\le 2000`, and for $`4000 < N\le 10\,000`, for all $`n\le 3000`  (these values exceed both the {bpref "cmf.sturm_bound"}[Sturm bound] and $`30\sqrt{N}` in every case). When the level is at most $`10\,000` and the dimension of $`f` is at most $`20` {bpref "cmf.heckecharpolys"}[Hecke characteristic polynomials] for primes $`p\le 100` are also available.

For each newform $`f` of level $`N\le 10\,000` and each {bpref "cmf.embedding"}[embedding] $`\rho\colon \Q(f)\to \C` the complex numbers $`\rho(a_n)` are available as floating point numbers with a precision of at least $`52` bits (separately, for both real and imaginary parts); this information is available for all newforms, regardless of their dimension, even when algebraic $`a_n` are not available (for the same ranges of $`n` as above).

Dimension tables are available for all newspaces $`S_k^\mathrm{new}(N,\chi)` with $`Nk^2 \le 4000`, and also for those with $`k>1` and $`Nk^2\le 40\,000`, and those with $`N\le 10` and $`Nk^2\le 100\,000`.  For newspaces in these ranges with $`N\le 4000` we have also computed the first $`1000` coefficients of the {bpref "cmf.trace_form"}[trace form] of the newspace.

Not every invariant of every newform has been computed (this is computationally infeasible).  Below is completeness information for some specific invariants:

- The following information is available for every newform of level $`N\le 10\,000`: {bpref "cmf.level"}[level], {bpref "cmf.weight"}[weight], {bpref "cmf.character"}[character], {bpref "cmf.dimension"}[dimension], {bpref "cmf.analytic_conductor"}[analytic conductor], {bpref "cmf.sato_tate"}[Sato-Tate group], {bpref "cmf.trace_form"}[trace form], {bpref "cmf.embedding"}[complex embedding] data, all {bpref "cmf.self_twist"}[self twists], all {bpref "cmf.inner_twist"}[inner twists], all {bpref "cmf.twist"}[twists] to other newforms in the database, the {bpref "cmf.minimal_twist"}[minimal twist], and an upper bound on the {bpref "cmf.analytic_rank"}[analytic rank].

- The following information is available for every newform of dimension at most $`20` and level $`N\le 10000`, and also for every weight one newform: {bpref "cmf.coefficient_field"}[coefficient field], exact algebraic coefficient data, generators for the {bpref "cmf.coefficient_ring"}[coefficient ring], and a lower bound on the index of the coefficient ring in the ring of integers of the coefficient field.

- The following information is available for every weight one newform: {bpref "cmf.projective_image"}[projective image] and {bpref "cmf.projective_image"}[projective field].

- In cases where the odd 2-dimensional {bpref "artin"}[Artin representation] corresponding to a weight one newform is present in the LMFDB, it is listed as a related object and the {bpref "cmf.artin_image"}[Artin image] and {bpref "cmf.artin_field"}[Artin field] of the weight one newform are available, and this information is also available in some cases where a twist of a weight one newform has a corresponding Artin representation in the LMFDB, even though the twisted Artin representation is not in the LMFDB.  As of January 2020 this applies to about 30% of the weight one newforms in the database.

- The database includes all of the 43 newforms that can be expressed as {bpref "cmf.eta_quotient"}[eta quotients] .

- {bpref "cmf.stark_unit"}[Stark units] for $`b=1` are available for weight 1 newforms of dimension 1.

Depends on: {uses "artin"}[] {uses "cmf.analytic_conductor"}[] {uses "cmf.analytic_rank"}[] {uses "cmf.artin_field"}[] {uses "cmf.artin_image"}[] {uses "cmf.character"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.coefficient_ring"}[] {uses "cmf.dimension"}[] {uses "cmf.embedding"}[] {uses "cmf.eta_quotient"}[] {uses "cmf.heckecharpolys"}[] {uses "cmf.inner_twist"}[] {uses "cmf.level"}[] {uses "cmf.minimal_twist"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[] {uses "cmf.projective_image"}[] {uses "cmf.q-expansion"}[] {uses "cmf.sato_tate"}[] {uses "cmf.self_twist"}[] {uses "cmf.stark_unit"}[] {uses "cmf.sturm_bound"}[] {uses "cmf.trace_form"}[] {uses "cmf.twist"}[] {uses "cmf.weight"}[]
:::

:::definition "rcs.cande.cmf_eisenstein"
*Completeness of classical modular form data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.cande.cmf_eisenstein))

The classical modular form database currently contains information for all {bpref "cmf.newform"}[newforms] $`f\in S_k^\mathrm{new}(N,\chi)` of {bpref "cmf.level"}[level] $`N\ge 1`, {bpref "cmf.weight"}[weight] $`k\ge 1`, {bpref "cmf.character"}[character] $`\chi\colon (\Z/N\Z)^\times\to \C`,
for which any of the following hold:

- $`Nk^2\le 4000`;

- $`\chi` trivial and $`Nk^2\le 40\,000`;

- $`N \le 24` and $`Nk^2 \le 40\,000`;

- $`N \le 10` and $`Nk^2 \le 100\,000`;

- $`N \le 100` and $`k \le 12`;

- $`k > 1` and $`\dim S_k^{\rm new}(N,\chi) \le 100` and $`Nk^2 \le 40\,000`.

- $`k = 2`, $`\chi` is trivial, and $`N\le 50\,000` or $`N \le 10^6` is prime.

In addition to the {bpref "cmf.newspace"}[newspaces] identified above, there are 131 newspaces that are present because they contain the {bpref "cmf.minimal_twist"}[minimal twist] of a newform in one of the newspaces above.

The database also contains information for all {bpref "cmf.eisenstein_newform"}[Eisenstein newforms] $`f\in E_k^\mathrm{new}(N,\chi)` of {bpref "cmf.level"}[level] $`N\ge 1`, {bpref "cmf.weight"}[weight] $`k\ge 2`, {bpref "cmf.character"}[character] $`\chi\colon (\Z/N\Z)^\times\to \C`,
for which any of the following hold:

- $`Nk^2\le 4000`;

For each newform with {bpref "cmf.q-expansion"}[q-expansion] $`f=\sum a_nq^n` the database contains the integers $`\mathrm{tr}(a_n)` for $`1\le n \le 1000`, and when the level is at most $`10\,000` and the {bpref "cmf.dimension"}[dimension] of $`f` is at most $`20`, the algebraic integers $`a_n` for $`1\le n \le 1000` expressed in terms of an explicit basis for the {bpref "cmf.coefficient_ring"}[coefficient ring] $`\Q(f)`.  For $`1000 < N \le 4000` this data is available for all $`n\le 2000`, and for $`4000 < N\le 10\,000`, for all $`n\le 3000`  (these values exceed both the {bpref "cmf.sturm_bound"}[Sturm bound] and $`30\sqrt{N}` in every case). When the level is at most $`10\,000` and the dimension of $`f` is at most $`20` {bpref "cmf.heckecharpolys"}[Hecke characteristic polynomials] for primes $`p\le 100` are also available.

For each newform $`f` of level $`N\le 10\,000` and each {bpref "cmf.embedding"}[embedding] $`\rho\colon \Q(f)\to \C` the complex numbers $`\rho(a_n)` are available as floating point numbers with a precision of at least $`52` bits (separately, for both real and imaginary parts); this information is available for all newforms, regardless of their dimension, even when algebraic $`a_n` are not available (for the same ranges of $`n` as above).

Dimension tables are available for all newspaces $`S_k^\mathrm{new}(N,\chi)` with $`Nk^2 \le 4000`, and also for those with $`k>1` and $`Nk^2\le 40\,000`, and those with $`N\le 10` and $`Nk^2\le 100\,000`.  For newspaces in these ranges with $`N\le 4000` we have also computed the first $`1000` coefficients of the {bpref "cmf.trace_form"}[trace form] of the newspace.

Not every invariant of every newform has been computed (this is computationally infeasible).  Below is completeness information for some specific invariants:

- The following information is available for every newform of level $`N\le 10\,000`: {bpref "cmf.level"}[level], {bpref "cmf.weight"}[weight], {bpref "cmf.character"}[character], {bpref "cmf.dimension"}[dimension], {bpref "cmf.analytic_conductor"}[analytic conductor], {bpref "cmf.sato_tate"}[Sato-Tate group], {bpref "cmf.trace_form"}[trace form], {bpref "cmf.embedding"}[complex embedding] data, all {bpref "cmf.self_twist"}[self twists], all {bpref "cmf.inner_twist"}[inner twists], all {bpref "cmf.twist"}[twists] to other newforms in the database, the {bpref "cmf.minimal_twist"}[minimal twist], and an upper bound on the {bpref "cmf.analytic_rank"}[analytic rank].

- The following information is available for every newform of dimension at most $`20` and level $`N\le 10000`, and also for every weight one newform: {bpref "cmf.coefficient_field"}[coefficient field], exact algebraic coefficient data, generators for the {bpref "cmf.coefficient_ring"}[coefficient ring], and a lower bound on the index of the coefficient ring in the ring of integers of the coefficient field.

- The following information is available for every weight one newform: {bpref "cmf.projective_image"}[projective image] and {bpref "cmf.projective_image"}[projective field].

- In cases where the odd 2-dimensional {bpref "artin"}[Artin representation] corresponding to a weight one newform is present in the LMFDB, it is listed as a related object and the {bpref "cmf.artin_image"}[Artin image] and {bpref "cmf.artin_field"}[Artin field] of the weight one newform are available, and this information is also available in some cases where a twist of a weight one newform has a corresponding Artin representation in the LMFDB, even though the twisted Artin representation is not in the LMFDB.  As of January 2020 this applies to about 30% of the weight one newforms in the database.

- The database includes all of the 43 newforms that can be expressed as {bpref "cmf.eta_quotient"}[eta quotients] .

- {bpref "cmf.stark_unit"}[Stark units] for $`b=1` are available for weight 1 newforms of dimension 1.

Depends on: {uses "artin"}[] {uses "cmf.analytic_conductor"}[] {uses "cmf.analytic_rank"}[] {uses "cmf.artin_field"}[] {uses "cmf.artin_image"}[] {uses "cmf.character"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.coefficient_ring"}[] {uses "cmf.dimension"}[] {uses "cmf.eisenstein_newform"}[] {uses "cmf.embedding"}[] {uses "cmf.eta_quotient"}[] {uses "cmf.heckecharpolys"}[] {uses "cmf.inner_twist"}[] {uses "cmf.level"}[] {uses "cmf.minimal_twist"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[] {uses "cmf.projective_image"}[] {uses "cmf.q-expansion"}[] {uses "cmf.sato_tate"}[] {uses "cmf.self_twist"}[] {uses "cmf.stark_unit"}[] {uses "cmf.sturm_bound"}[] {uses "cmf.trace_form"}[] {uses "cmf.twist"}[] {uses "cmf.weight"}[]
:::

:::definition "rcs.rigor.cmf"
*Reliability of the Classical Modular Form Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.rigor.cmf))

All {bpref "cmf"}[modular form] data currently in the database has been computed using rigorous algorithms that do not depend on any unproved assumptions or conjectures.  In particular

- All {bpref "cmf.self_twist"}[self twists] and {bpref "cmf.inner_twist"}[inner twists] have been rigorously verified either by checking exact algebraic coefficients or complex analytic coefficients computed to sufficient precision to uniquely identify every such twist (as of February 2020).

- The {bpref "cmf.analytic_rank"}[analytic ranks] have all been rigorously verified by computing winding elements on spaces of modular symbols (and using the {bpref "lfunction.sign"}[sign] of the functional equation in the case of {bpref "cmf.selfdual"}[self dual] {bpref "cmf.newform"}[newforms]).

- For {bpref "cmf.weight"}[weight] 1 newforms, the  classification of the {bpref "cmf.projective_image"}[projective image] as $`D_n`, $`A_4`, $`S_4`, $`A_5` has been rigorously verified by explicitly computing the {bpref "cmf.projective_field"}[projective field] (as of August 2019).

In addition to using mathematically rigorous algorithms whenever possible, we have performed a variety of consistency checks intended to catch any errors in the software packages used to compute modular forms data, or any errors that might have been introduced during post-processing.  The following checks have been performed:

- All newforms of weight $`k > 1` and {bpref "cmf.level"}[level] $`N` satisfying $`Nk^2 \le 2000` have been independently computed using [Magma](http://magma.maths.usyd.edu.au/magma/) and [Pari/GP](https//pari.math.u-bordeaux.fr/).  By comparing the results of these computations we have verified that the decompositions of each {bpref "cmf.newspace"}[newspace] $`S_k^{\rm new}(N,\chi)` into  {bpref "cmf.galois_orbit"}[Galois orbits] agree (with matching {bpref "cmf.coefficient_field"}[coefficient fields]), that the first 1000 coefficients of the {bpref "cmf.trace_form"}[trace forms] for each Galois orbit agree, and for newforms of {bpref "cmf.dimension"}[dimension] $`d\le 20`, that there is an automorphism of the coefficient field that relates the sequences of algebraic eigenvalues $`(a_1,\ldots,a_{1000})` computed by Pari and Magma.

- For all newforms of weight $`k>1` and level $`N` satisfying $`Nk^2 \le 4000` we have verified that the trace forms computed by Magma (using modular symbols) agree with the trace forms obtained from complex analytic data computed using the explicit trace formula.  This also verifies the dimensions of the coefficient fields.

- For newforms of weight $`k=1` and level $`N\le 1000` we have matched the data computed using Pari/GP with the tables computed by Buzzard and Lauder .

- For dihedral newforms of weight $`k=1` and level $`N\le 4000` we have matched trace forms with data computed using the explicit trace formula in Pari/GP with data computed independently in both Pari/GP and Magma using class field theoretic methods.

See  for further details.

Depends on: {uses "cmf"}[] {uses "cmf.analytic_rank"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.dimension"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.inner_twist"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[] {uses "cmf.projective_field"}[] {uses "cmf.projective_image"}[] {uses "cmf.self_twist"}[] {uses "cmf.selfdual"}[] {uses "cmf.trace_form"}[] {uses "cmf.weight"}[] {uses "lfunction.sign"}[]
:::

:::definition "rcs.rigor.cmf_eisenstein"
*Reliability of the Classical Modular Form Data.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/rcs.rigor.cmf_eisenstein))

All {bpref "cmf"}[modular form] data currently in the database has been computed using rigorous algorithms that do not depend on any unproved assumptions or conjectures.  In particular

- All {bpref "cmf.self_twist"}[self twists] and {bpref "cmf.inner_twist"}[inner twists] have been rigorously verified either by checking exact algebraic coefficients or complex analytic coefficients computed to sufficient precision to uniquely identify every such twist (as of February 2020).

- The {bpref "cmf.analytic_rank"}[analytic ranks] have all been rigorously verified by computing winding elements on spaces of modular symbols (and using the {bpref "lfunction.sign"}[sign] of the functional equation in the case of {bpref "cmf.selfdual"}[self dual] {bpref "cmf.newform"}[newforms]).

- For {bpref "cmf.weight"}[weight] 1 newforms, the  classification of the {bpref "cmf.projective_image"}[projective image] as $`D_n`, $`A_4`, $`S_4`, $`A_5` has been rigorously verified by explicitly computing the {bpref "cmf.projective_field"}[projective field] (as of August 2019).

In addition to using mathematically rigorous algorithms whenever possible, we have performed a variety of consistency checks intended to catch any errors in the software packages used to compute modular forms data, or any errors that might have been introduced during post-processing.  The following checks have been performed:

- All newforms and Eisenstein newforms of weight $`k > 1` and {bpref "cmf.level"}[level] $`N` satisfying $`Nk^2 \le 2000` have been independently computed using [Magma](http://magma.maths.usyd.edu.au/magma/) and [Pari/GP](https//pari.math.u-bordeaux.fr/).  By comparing the results of these computations we have verified that the decompositions of each {bpref "cmf.newspace"}[newspace] $`S_k^{\rm new}(N,\chi)` into  {bpref "cmf.galois_orbit"}[Galois orbits] agree (with matching {bpref "cmf.coefficient_field"}[coefficient fields]), that the first 1000 coefficients of the {bpref "cmf.trace_form"}[trace forms] for each Galois orbit agree, and for newforms of {bpref "cmf.dimension"}[dimension] $`d\le 20`, that there is an automorphism of the coefficient field that relates the sequences of algebraic eigenvalues $`(a_1,\ldots,a_{1000})` computed by Pari and Magma.

- For all newforms and Eisenstein newforms of weight $`k>1` and level $`N` satisfying $`Nk^2 \le 4000` we have verified that the trace forms computed by Magma (using modular symbols) agree with the trace forms obtained from complex analytic data computed using the explicit trace formula.  This also verifies the dimensions of the coefficient fields.

- For newforms of weight $`k=1` and level $`N\le 1000` we have matched the data computed using Pari/GP with the tables computed by Buzzard and Lauder .

- For dihedral newforms of weight $`k=1` and level $`N\le 4000` we have matched trace forms with data computed using the explicit trace formula in Pari/GP with data computed independently in both Pari/GP and Magma using class field theoretic methods.

See  for further details.

Depends on: {uses "cmf"}[] {uses "cmf.analytic_rank"}[] {uses "cmf.coefficient_field"}[] {uses "cmf.dimension"}[] {uses "cmf.galois_orbit"}[] {uses "cmf.inner_twist"}[] {uses "cmf.level"}[] {uses "cmf.newform"}[] {uses "cmf.newspace"}[] {uses "cmf.projective_field"}[] {uses "cmf.projective_image"}[] {uses "cmf.self_twist"}[] {uses "cmf.selfdual"}[] {uses "cmf.trace_form"}[] {uses "cmf.weight"}[] {uses "lfunction.sign"}[]
:::

:::definition "specialfunction.poincare" (lean := "ModularForm.poincareSeries, ModularForm.poincareSeries_eq_tsum_of_section, ModularForm.hasSum_poincareSeries_of_three_le, ModularForm.mdifferentiable_poincareSeries_of_three_le, ModularForm.poincareSeries_mem_multiplierCuspSpace, ModularForm.span_poincareSeries_eq_multiplierCuspSpace_of_finiteIndex, ModularForm.exists_poincareSeries_eq_of_smul_infty_eq, ModularForm.poincareSeries_coe_mul")
*Poincar&eacute; series.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/specialfunction.poincare))

Let $`G` be a subgroup of {bpref "group.sl2z"}[$`\Gamma`] of finite {bpref "group.subgroup.index"}[index] $`m`, $`v` a {bpref "mf.multipliersystem"}[multiplier system] on $`G` and $`k\geq3\in\mathbb{N}` such that $`v(-I)=(-1)^k`. Let $`s` be a {bpref "group.fuchsian.cusps"}[cusp] representative of $`G` with {bpref "group.fuchsian.cusps.width"}[width] $`w` such that $`s=\gamma_s(\infty)` for some $`\gamma_s\in\Gamma` and let $`G_s=G\cap\gamma_s\Gamma_{\infty}\gamma_s^{-1}` be the \*stabilizer\* of the cusp $`s`. Assume that $`v` is trivial on $`G_s`. The *$`n`th Poincar\'e; series* for the cusp that $`s` represents is defined as

$$`P_k^n(G,v;z;\overline{s})=\sum_{g\in G_s\setminus G}\overline{v(g)}e^{2\pi
i(n/w)\gamma_s^{-1}gz}j(\gamma_s^{-1}g,z)^{-k},`

where $`j(\gamma,z)=cz+d` for $`\gamma=\left(\begin{matrix}a&b\\c&d\end{matrix}\right)`.

Poincare; series are \*holomorphic\* on the {bpref "mf.upper_half_plane"}[upper half-plane]. Further more, for a fixed cusp $`\overline{S}`, they generate the corresponding space of {bpref "cmf.cusp_form"}[cusp forms]. The series depends on the choice of $`\gamma_s` up to a factor of $`e^{2\pi in/w}`, therefore, if $`w\mid n`, it does not depend on the cusp representative.

Depends on: {uses "cmf.cusp_form"}[] {uses "group.fuchsian.cusps"}[] {uses "group.fuchsian.cusps.width"}[] {uses "group.sl2z"}[] {uses "group.subgroup.index"}[] {uses "mf.multipliersystem"}[] {uses "mf.upper_half_plane"}[]
:::
