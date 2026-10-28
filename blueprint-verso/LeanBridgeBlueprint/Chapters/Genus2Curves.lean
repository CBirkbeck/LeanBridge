import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Genus 2 curves" =>

This chapter lists the LMFDB definitions relating to *genus 2 curves*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl. The definitions from this area that the number field, elliptic curve and modular form chapters depend on are in the Background chapter instead.

:::definition "g2c.abs_discriminant" (lean := "HyperellipticEquation.discriminant, HyperellipticEquation.IsMinimal, HyperellipticEquation.IsMinimal.abs_discriminant_eq")
*Absolute discriminant.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.abs_discriminant))

The *absolute discriminant* of a {bpref "g2c.g2curve"}[genus 2 curve] over $`\Q` is the absolute value of its {bpref "g2c.discriminant"}[discriminant].

Depends on: {uses "g2c.discriminant"}[] {uses "g2c.g2curve"}[]
:::

:::definition "g2c.all_rational_points" (lean := "HyperellipticEquation.RationalPoint, HyperellipticEquation.IsWeightedSolution, HyperellipticEquation.weightedScale, AlgebraicGeometry.Scheme.PointOver")
*Rational points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.all_rational_points))

For a curve $`X` of {bpref "ag.curve.genus"}[genus] $`g\ge 2` over $`\Q` (or any number fields) the set of *rational points* $`X(\Q)` is finite, by a theorem of Faltings. At present no algorithm is known that explicitly computes a provably complete list of the points in $`X(\Q)`, for any given curve $`X`, but in specific cases, including when the rank of the {bpref "ag.jacobian"}[Jacobian] of $`X` is less than $`g`, this can often be accomplished.

Rational points on {bpref "ag.hyperelliptic_curve"}[hyperelliptic curves] are written in projective coordinates with respect to the weighted homogeneous equation $`y^2+h(x,z)y=f(x,z)` of degree $`2g+2` that is a smooth projective model for the curve $`X`, where $`y` has weight $`g+1`, while $`x` and $`z` both have weight 1.  This homogeneous equation is uniquely determined by the affine equation $`y^2+h(x)y=f(x)` that listed as the {bpref "g2c.minimal_equation"}[minimal equation] for the curve.

Depends on: {uses "ag.curve.genus"}[] {uses "ag.hyperelliptic_curve"}[] {uses "ag.jacobian"}[] {uses "g2c.minimal_equation"}[]
:::

:::definition "g2c.analytic_rank"
*Analytic rank of a curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.analytic_rank))

The *analytic rank* of an {bpref "ag.abelian_variety"}[abelian variety] is the {bpref "lfunction.analytic_rank"}[analytic rank] of its {bpref "lfunction"}[L-function] $`L(A,s)`.  The analytic rank of a {bpref "ag.curve"}[curve] is the analytic rank of its {bpref "ag.jacobian"}[Jacobian].  The weak form of the {bpref "g2c.bsd_invariants"}[BSD conjecture] implies that the analytic rank is equal to the rank of the {bpref "ag.mordell_weil"}[Mordell-Weil group] of the abelian variety.

Analytic ranks are always computed under the assumption that $`L(A,s)` satisfies the {bpref "g2c.hasse_weil_conjecture"}[Hasse-Weil conjecture] (they are not necessarily well-defined otherwise).  When $`A` is defined over $`\Q`, the parity of the analytic rank is always compatible with the {bpref "lfunction.sign"}[sign] of the {bpref "lfunction.functional_equation"}[functional equation].

In general, analytic ranks stored in the LMFDB are only upper bounds on the true analytic rank (they could be incorrect if $`L(A,s)` has a zero very close to but not on the {bpref "lfunction.central_point"}[central point]).  For abelian varieties over $`\Q` of analytic rank less than 2 this upper bound is necessarily tight, due to parity.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.curve"}[] {uses "ag.jacobian"}[] {uses "ag.mordell_weil"}[] {uses "g2c.hasse_weil_conjecture"}[] {uses "lfunction"}[] {uses "lfunction.analytic_rank"}[] {uses "lfunction.central_point"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.sign"}[]
:::

:::definition "g2c.analytic_sha"
*Analytic order of Sha.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.analytic_sha))

For an {bpref "ag.abelian_variety"}[abelian variety] $`A/\Q` the *analytic order of Sha* is the real number

$$`\Sha_{an}(A) := \frac{L^{(r)}(A,1)}{r!}\frac{(\#A(\Q)_{\rm tor})^2}{\Omega_AR_AT_A}`

where

- $`r` is the {bpref "g2c.analytic_rank"}[analytic rank] of $`A`;

- $`L(A,s)` is the {bpref "lfunction"}[L-function] of $`A`, with {bpref "lfunction.leading_coeff"}[leading coefficient] $`L^{(r)}(A,1)/r!`;

- $`A(\Q)_{\rm tor}` is the {bpref "g2c.torsion"}[torsion subgroup] of the {bpref "ag.mordell_weil"}[Mordell-Weil group] $`A(\Q)`;

- $`\Omega` is the {bpref "g2c.real_period"}[real period] of $`A`;

- $`R` is the {bpref "ag.regulator"}[regulator] of $`A`;

- $`T = \prod_p c_p` is the {bpref "g2c.tamagawa"}[Tamagawa product] of $`A`.

The Birch and Swinnerton-Dyer for abelian varieties implies that the analytic rank of $`A` is equal to its {bpref "g2c.mordell_weil_rank"}[Mordell-Weil rank], and that its analytic order of Sha is equal to the order of its {bpref "ag.tate_shafarevich"}[Tate-Shafarevich group].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.mordell_weil"}[] {uses "ag.regulator"}[] {uses "g2c.analytic_rank"}[] {uses "g2c.mordell_weil_rank"}[] {uses "g2c.real_period"}[] {uses "g2c.tamagawa"}[] {uses "ag.tate_shafarevich"}[] {uses "g2c.torsion"}[] {uses "lfunction"}[] {uses "lfunction.leading_coeff"}[]
:::

:::definition "g2c.bsd_invariants"
*BSD invariants.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.bsd_invariants))

The *BSD invariants* of an {bpref "ag.abelian_variety"}[abelian variety] $`A/\Q` include:

- the {bpref "g2c.analytic_rank"}[analytic rank] of $`A`;

- the {bpref "g2c.mordell_weil_rank"}[Mordell-Weil rank] of $`A`;

- the {bpref "lfunction.leading_coeff"}[leading coefficient] $`L^{(r)}(A,1)/r!` of the {bpref "lfunction"}[L-function] of $`A`;

- the order of the {bpref "g2c.torsion"}[torsion subgroup] $`A(\Q)_{\rm tor}` of the {bpref "ag.mordell_weil"}[Mordell-Weil group] $`A`;

- the {bpref "g2c.real_period"}[real period] $`\Omega_A` of $`A`;

- the {bpref "ag.regulator"}[regulator] $`R_A` of $`A`;

- the {bpref "g2c.tamagawa"}[Tamagawa product] $`T_A:=\prod_p c_p` of $`A`;

- the order of the {bpref "ag.tate_shafarevich"}[Tate-Shafarevich] group $`\Sha(A)` of $`A`.

The weak form of the Birch and Swinnerton-Dyer conjecture predicts that the first two invariants are equal, while the strong form of their conjecture relates the last six invariants via the *BSD formula*

$$`\frac{L^{(r)}(A,1)}{r!} = \frac{\#\Sha(A)\Omega_AR_AT_A}{(\#A(\Q)_{\rm tor})^2}.`

No effective method to compute $`\Sha(A)` is currently known (indeed, it is not even known that $`\Sha(A)` is finitely generated, although the BSD conjecture requires this).  However, one can compute (approximations of) the the five remaining quantities and use this to compute the {bpref "g2c.analytic_sha"}[analytic order of Sha], and under the assumption that  $`\Sha(A)` is finite, one can determine whether its order is a square or not.  One can also compute the {bpref "g2c.two_selmer_rank"}[rank of the 2-Selmer group] of $`A`, which constrains the 2-part of $`\Sha(A)`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.mordell_weil"}[] {uses "ag.regulator"}[] {uses "g2c.analytic_rank"}[] {uses "g2c.analytic_sha"}[] {uses "g2c.mordell_weil_rank"}[] {uses "g2c.real_period"}[] {uses "g2c.tamagawa"}[] {uses "ag.tate_shafarevich"}[] {uses "g2c.torsion"}[] {uses "g2c.two_selmer_rank"}[] {uses "lfunction"}[] {uses "lfunction.leading_coeff"}[]
:::

:::definition "g2c.conductor"
*Conductor of a genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.conductor))

The *conductor* $`N` of a {bpref "g2c.g2curve"}[genus 2 curve] $`X/\Q` is the conductor of its {bpref "ag.jacobian"}[Jacobian] $`\mathrm{Jac}(X)`.  This is a positive integer that divides the {bpref "g2c.discriminant"}[discriminant] of $`X` and is divisible by every {bpref "ag.bad_prime"}[prime of bad reduction] for $`\mathrm{Jac}(X)` (but not necessarily by every prime of bad reduction for $`X`).

The valuation of $`N` at a prime $`p` satisfies the following bounds.
<table>
<tr><td>$`p`:</td><td>$`2`</td><td>$`3`</td><td>$`5`</td><td>$`\ge 7`</td</tr>
<tr><td>$`v_p(N)`:</td><td>$`20`</td><td>$`10`</td><td>$`9`</td><td>$`4`</td</tr>
</table>

Depends on: {uses "ag.bad_prime"}[] {uses "ag.jacobian"}[] {uses "g2c.discriminant"}[] {uses "g2c.g2curve"}[]
:::

:::definition "g2c.decomposition" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange, TauCeti.AlgebraicGeometry.AbelianVariety.dim, TauCeti.AlgebraicGeometry.AbelianVariety.prod")
*Decomposition of the Jacobian of a genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.decomposition))

An {bpref "ag.abelian_variety"}[abelian variety] $`A` defined over a field $`K` is said to *split* or *decompose* (over $`K`) if it is {bpref "av.isogeny"}[isogenous] to a product of abelian varieties $`B_1\times B_2` of lower positive dimension; the abelian varieties $`B_1` and $`B_2` are also defined over $`K`, as is the isogeny from $`A` to $`B_1\times B_2`.  An abelian variety that does not decompose is said to be {bpref "ag.simple"}[simple].  A simple abelian variety may decompose over a finite extension $`L/K` (meaning that its base change to $`L` decomposes), unless it is {bpref "ag.geom_simple"}[geometrically simple].

When $`A` is the Jacobian of a genus 2 curve, the abelian varieties $`B_1` and $`B_2` are necessarily {bpref "ec"}[elliptic curves].  If $`B_1` and $`B_2` are isogenous elliptic curves, then $`A` is isogenous to the square of $`B_1` (the abelian variety $`B_1\times B_1`).

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.geom_simple"}[] {uses "av.isogeny"}[] {uses "ag.simple"}[] {uses "ec"}[]
:::

:::definition "g2c.end_alg" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.End, TauCeti.AlgebraicGeometry.AbelianVariety.dim")
*Endomorphism algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.end_alg))

The *endomorphism algebra* of an {bpref "ag.abelian_surface"}[abelian surface] $`A` over a {bpref "ring.field"}[field] $`K` is the $`\Q`-algebra $`\End(A) \otimes \Q`.  This is a special case of the {bpref "ag.endomorphism_algebra"}[endomorphism algebra] of an {bpref "ag.abelian_variety"}[abelian variety].

When $`A` is an abelian surface over $`\Q`, there are five possibilities for $`\End(A)\otimes\Q`:

1. $`\Q`;
2. a real quadratic field (in which case $`A` has *real multiplication*, denoted RM);
3. an imaginary quadratic field (in which case $`A` has *complex multiplication*, denoted CM);
4. $`\Q\times \Q`;
5. $`\mathrm{M}_2(\Q)`;

The first three cases occur when $`A` is {bpref "ag.simple"}[simple], while the last two cases occur when $`A` is {bpref "av.isogeny"}[isogenous] to a product of {bpref "ec"}[elliptic curves] $`E_1\times E_2` over $`\overline{K}`. Which of the last two cases occurs depends on whether $`E_1` and/or $`E_2` are isogenous or not.

Depends on: {uses "ag.abelian_surface"}[] {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_algebra"}[] {uses "ag.simple"}[] {uses "av.isogeny"}[] {uses "ec"}[] {uses "ring.field"}[]
:::

:::definition "g2c.g2_invariants" (lean := "Polynomial.g2Invariants, HyperellipticEquation.g2Invariants")
*G2-invariants of a genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.g2_invariants))

The *G2-invariants* of a {bpref "g2c.g2curve"}[genus 2 curve] are absolute invariants associated to the {bpref "g2c.geom_iso_class"}[geometric isomorphism class] of the curve.  They are denoted $`g_1,g_2,g_3`.

These invariants were defined by Cardona, Quer, Nart and Pujolàs. Like the {bpref "g2c.igusa_invariants"}[Igusa invariants], they reflect the behavior of the curve in question at a prime; for example, if one of the invariants contains a prime in its denominator, then the curve will have bad reduction at that prime over any extension of the base field. However, the G2-invariants give less information than the {bpref "g2c.igusa_invariants"}[Igusa invariants] do about the particular type of reduction at a given prime.

The exact definition of the G2-invariants is as follows. Let $`X` be a curve of genus $`2` with Igusa invariants $`J_2, J_4, J_6, J_8, J_{10}`. Then

$$`(g_1,g_2,g_3) = (J_2^5 / J_{10},\, J_2^3 J_4 / J_{10},\, J_2^2 J_6 / J_{10}),`

so long as $`J_2` is nonzero ($`J_{10}` is always nonzero because it is a multiple of the discriminant of $`f`). When $`J_2` is zero we instead have

$$`(g_1,g_2,g_3) = (0,\, J_4^5 / J_{10}^2,\, J_4 J_6 / J_{10}),\qquad\ \`

except when $`J_4` is also zero, in which case

$$`(g_1,g_2,g_3) = (0,\,0,\,J_6^5 / J_{10}^3).\qquad\qquad\quad`

Depends on: {uses "g2c.g2curve"}[] {uses "g2c.geom_iso_class"}[] {uses "g2c.igusa_invariants"}[]
:::

:::definition "g2c.galois_rep.non_maximal_primes"
*Nonmaximal primes associated to genus $`2` curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.galois_rep.non_maximal_primes))

The *nonmaximal primes* associated to a {bpref "g2c.g2curve"}[genus $`2` curve] are the finitely many primes $`\ell` for which the image of the mod-$`\ell` Galois representation is not as large as possible, subject to constraints imposed by the {bpref "ag.geom_endomorphism_ring"}[geometric endomorphism ring] of the {bpref "ag.jacobian"}[Jacobian] of $`C`.

This information is currently available only for genus 2 curves whose Jacobian has geometric endomorphism ring $`\Z`, equivalently, curves with {bpref "g2c.st_group"}[Sato-Tate group] $`\mathrm{USp}(4)`.  In this case the nonmaximal primes are simply the primes $`\ell` for which the mod-$`\ell` Galois representation is not surjective.

Depends on: {uses "ag.geom_endomorphism_ring"}[] {uses "ag.jacobian"}[] {uses "g2c.g2curve"}[] {uses "g2c.st_group"}[]
:::

:::definition "g2c.galois_rep_image"
*Image of mod p Galois Representation of Jacobian of genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.galois_rep_image))

WARNING: The image types of nonmaximal primes is still in development, and subject to change.

Let $`p` be a prime and let $`C` be a {bpref "g2c.g2curve"}[genus 2 curve] defined over $`\mathbb{Q}`.

Subgroups $`G` of $`\GSp(4,\F_{\ell})` that can arise as the image of the mod-$`\ell` {bpref "ec.galois_rep"}[Galois representation]

$$`\rho_{J,p}\colon {\Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to \GSp(4,\F_{\ell})`

attached to the jacobian $`J` of $`C` that do not contain $`\Sp(4,\F_{\ell})` are identified via the types arising from Mitchell's 1914 classification.

There are six types: Irreducible *irred*, Cuspidal *cusp*, One-plus-Three *1p3*,
Two-plus-Two *2p2*, Non-Semistable *nss*, and last but very much not least, the super duper mysterious and esoteric unknown type *?*. Can you catch 'em all?

Depends on: {uses "ec.galois_rep"}[] {uses "g2c.g2curve"}[]
:::

:::definition "g2c.geom_aut_grp" (lean := "CategoryTheory.Aut, AlgebraicGeometry.Scheme.geometricBaseChange")
*Geometric automorphism group.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.geom_aut_grp))

The *geometric automorphism group* of a curve is the {bpref "g2c.aut_grp"}[automorphism group] of its {bpref "ag.base_change"}[base change] to the algebraic closure of its base field.

If $`X` is a curve over a field $`k`, its geometric automorphism group is denoted $`\mathrm{Aut}(X_{\bar{k}})`.

Depends on: {uses "ag.base_change"}[] {uses "g2c.aut_grp"}[]
:::

:::definition "g2c.geom_end_alg" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.End, TauCeti.AlgebraicGeometry.AbelianVariety.End.baseChange, TauCeti.AlgebraicGeometry.AbelianVariety.baseChange")
*Geometric endomorphism algebra.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.geom_end_alg))

The *geometric endomorphism algebra* of an {bpref "ag.abelian_surface"}[abelian surface] $`A` over a {bpref "ring.field"}[field] $`K` is the $`\Q`-algebra $`\End(A_{\overline{K}}) \otimes \Q`, the endomorphism algebra of the base change $`A_{\overline{K}}` of $`A` to an algebraic closure $`\overline{K}` of $`K`.  This is a special case of the {bpref "ag.geom_endomorphism_algebra"}[geometric endomorphism algebra] of an {bpref "ag.abelian_variety"}[abelian variety].

When $`A` is an abelian surface over a number field $`K`, there are nine possibilities for $`\End(A_{\overline{K}})\otimes\Q`:

1. $`\Q`;
2. a real quadratic field (in which case $`A` has *real multiplication*, denoted RM);
3. a quartic {bpref "nf.cm_field"}[CM field] (in which case $`A` has *complex multiplication*, denoted CM);
4. a non-split quaternion algebra over $`\Q` (in which case $`A` has *quaternionic multiplication*, denoted QM);
5. $`\Q\times \Q`;
6. $`F\times \Q`, where $`F` is a quadratic CM field (denoted $`\mathrm{CM} \times \Q`);
7. $`F_1\times F_2`, where $`F_1` and $`F_2` are distinct quadratic CM fields (denoted $`\mathrm{CM} \times \mathrm{CM}`);
8. $`\mathrm{M}_2(\Q)`;
9. $`\mathrm{M}_2(F)`, where $`F` is a quadratic CM field (denoted $`\mathrm{M}_2(\mathrm{CM})`).

The first four cases occur when $`A` is {bpref "ag.geom_simple"}[geometrically simple], while the last five cases occur when $`A_{\overline{K}}` is {bpref "av.isogeny"}[isogenous] to a product of {bpref "ec"}[elliptic curves] $`E_1\times E_2` over $`\overline{K}`. Which of the last five cases occurs depends on whether $`E_1` and/or $`E_2` have {bpref "ec.complex_multiplication"}[complex multiplication], and whether $`E_1` and $`E_2` are isogenous or not.

Depends on: {uses "ag.abelian_surface"}[] {uses "ag.abelian_variety"}[] {uses "ag.geom_endomorphism_algebra"}[] {uses "ag.geom_simple"}[] {uses "av.isogeny"}[] {uses "ec"}[] {uses "ec.complex_multiplication"}[] {uses "nf.cm_field"}[] {uses "ring.field"}[]
:::

:::definition "g2c.geom_iso_class" (lean := "AlgebraicGeometry.Scheme.geometricBaseChange, CategoryTheory.IsIsomorphic, CategoryTheory.isIsomorphicSetoid")
*Geometric isomorphism class of a curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.geom_iso_class))

The *geometric isomorphism class* of a {bpref "ag.curve"}[curve] $`C` {bpref "ag.base_field"}[over a field] $`K` is the isomorphism class of the {bpref "ag.base_change"}[base change] of $`C` to the algebraic closure of $`K`.

Depends on: {uses "ag.base_change"}[] {uses "ag.base_field"}[] {uses "ag.curve"}[]
:::

:::definition "g2c.gl2type" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety.IsSimpleGL2Type, TauCeti.AlgebraicGeometry.AbelianVariety.IsGL2Type, TauCeti.AlgebraicGeometry.AbelianVariety.IsCurveGL2Type")
*$`\GL_2`-type.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.gl2type))

A {bpref "ag.simple"}[simple] {bpref "ag.abelian_variety"}[abelian variety] $`A` over a field $`K` is said to be of *$`\textbf{GL}_2`-type* if its {bpref "ag.endomorphism_algebra"}[endomorphism algebra] $`\mathrm{End}(A)\otimes\Q` is commutative and has dimension (as a $`\Q`-vector space) equal to the dimension of $`A` (as an abelian variety).  More generally, an abelian variety is said to be of *$`\textbf{GL}_2`-type* if it is isogenous (over the ground field) to a product of pairwise non-isogenous simple abelian varieties of $`\textrm{GL}_2`-type.

Let $`\ell \in \mathbb{Z}_{> 0}` be a prime, and let $`V_{\ell}(A) = T_{\ell}(A) \otimes_{\mathbb{Z}_{\ell}} \mathbb{Q}_{\ell}`, where $`T_{\ell}(A)` is the $`\ell`-adic {bpref "av.tate_module"}[Tate module] of $`A`. If $`K` has characteristic different from $`\ell`, then $`V_{\ell}(A)` is free of rank $`2` as a $`(E \otimes_{\mathbb{Q}} \mathbb{Q}_{\ell})`-module. Consequently, the image of the $`\ell`-adic {bpref "av.galois_rep"}[Galois representation] of $`A` is a subgroup of $`\operatorname{GL}_2(E \otimes_{\mathbb{Q}} \mathbb{Q}_{\ell})`.

A curve is said to be of $`\text{GL}_2`-type if its {bpref "ag.jacobian"}[Jacobian] is of $`\text{GL}_2`-type.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_algebra"}[] {uses "ag.jacobian"}[] {uses "ag.simple"}[] {uses "av.galois_rep"}[] {uses "av.tate_module"}[]
:::

:::definition "g2c.hasse_weil_conjecture"
*Hasse-Weil conjecture.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.hasse_weil_conjecture))

The *Hasse-Weil conjecture* predicts that the {bpref "lfunction"}[L-function] $`L(A,s)` of a (positive-dimensional) {bpref "ag.abelian_variety"}[abelian variety] $`A` over a {bpref "nf"}[number field] $`K` has an analytic continuation to $`\C` with no poles in the {bpref "lfunction.critical_strip"}[critical strip] and that it satisfies its {bpref "lfunction.functional_equation"}[functional equation]; equivalently, $`L(A,s)` lies in the {bpref "lfunction.selberg_class"}[Selberg class].

The Hasse-Weil conjecture is implied by modularity and is thus known to hold, for example, when $`K=\Q` and $`A` is an {bpref "ec"}[elliptic curve] or an abelian variety of {bpref "g2c.gl2type"}[$`\GL_2`-type].

Depends on: {uses "ag.abelian_variety"}[] {uses "ec"}[] {uses "g2c.gl2type"}[] {uses "lfunction"}[] {uses "lfunction.critical_strip"}[] {uses "lfunction.functional_equation"}[] {uses "lfunction.selberg_class"}[] {uses "nf"}[]
:::

:::definition "g2c.igusa_clebsch_invariants" (lean := "Polynomial.igusaClebsch, HyperellipticEquation.igusaClebsch, Polynomial.sexticOrbitSum, Polynomial.sexticOrbitSum_comp, Polynomial.normalizeWeighted")
*Igusa-Clebsch invariants of a genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.igusa_clebsch_invariants))

The *Igusa-Clebsch invariants* of a {bpref "g2c.g2curve"}[genus 2 curve] are weighted projective invariants associated to the {bpref "g2c.geom_iso_class"}[geometric isomorphism class] of the curve.  They are denoted $`I_2, I_4, I_6, I_{10}`, where the subscript indicates the weight.

For genus 2 curves over $`\Q` we may assume that the Igusa-Clebsch invariants are integral. We can then normalize them by removing a factor of $`d^k` from $`I_{2k}`, where $`d` is the largest positive integer for which the invariants remain integral after this normalization.  We can also make the first nonzero $`I_{2k}` with $`k` odd positive by multiplying each $`I_{2k}` by $`(-i)^k`.

In the LMFDB, Igusa-Clebsch invariants for genus 2 curves over $`\Q` are always normalized in this way, which means that their values may differ from those returned by the corresponding functions in Sage or Magma; however, they are equivalent as $`\overline{\mathbb}{Q}`-points in weighted projective space and identify the same geometric isomorphism class.

The exact definition of the Igusa-Clebsch invariants is as follows. Let $`X` be a curve of genus $`2`, which we may assume to be defined by an equation $`y^2 = f(x)` with $`f` a sextic in $`x`. Let $`c` be the leading coefficient of $`f`, fix an ordering of the roots $`x_1,\ldots,x_6` of $`f` in its splitting field, and let $`(i j)` denote the difference $`x_i-x_j`.  Then

$$`I_2 = c^2 \sum (1 2)^2 (3 4)^2 (5 6)^2,\qquad\qquad\qquad\qquad\qquad\quad \\
I_4 = c^4 \sum (1 2)^2 (2 3)^2 (3 1)^2 (4 5)^2 (5 6)^2 (6 4)^2,\qquad\qquad\quad\ \ \\
I_6 = c^6 \sum (1 2)^2 (2 3)^2 (3 1)^2 (4 5)^2 (5 6)^2 (6 4)^2 (1 4)^2 (2 5)^2 (3 6)^2, \\
I_{10} = c^{10} \prod (1 2)^2.\qquad\qquad\qquad\qquad\qquad\qquad\qquad\quad \\`

Here each sum and product runs over the distinct expressions obtained by applying a permutation to the index set $`\{1, \ldots, 6\}`. More precisely, it is obtained by averaging over the $`S_6`-Galois orbit of the given expression. Note that $`I_{10}` is simply the discriminant of the sextic polynomial $`f`.

Depends on: {uses "g2c.g2curve"}[] {uses "g2c.geom_iso_class"}[]
:::

:::definition "g2c.igusa_invariants" (lean := "Polynomial.igusa, HyperellipticEquation.igusa, Polynomial.normalizeWeighted")
*Igusa invariants of a genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.igusa_invariants))

The *Igusa invariants* of a {bpref "g2c.g2curve"}[genus 2 curve] are weighted projective invariants associated to the {bpref "g2c.geom_iso_class"}[geometric isomorphism class] of the curve.  They are denoted $`J_2, J_4, J_6, J_8, J_{10}`, where the subscript indicates the weight.

For genus 2 curves over $`\Q` we may assume that the Igusa invariants are integral. We can then normalize them by removing a factor of $`d^k` from $`I_{2k}`, where $`d` is the largest positive integer for which the invariants remain integral after this normalization. We can also make the first nonzero $`I_{2k}` with $`k` odd nonnegative by multiplying each $`I_{2k}` by $`(-i)^k`.

In the LMFDB, Igusa invariants for genus 2 curves over $`\Q` are always normalized in this way, which means that their values may differ from those returned by the corresponding functions in Sage or Magma; however, they are equivalent as $`\overline{\mathbb}{Q}`-points in weighted projective space and identify the same geometric isomorphism class.

These invariants were first defined by Igusa to enable him to study the moduli space of genus 2 curves over $`\Z`. In particular, they reflect the behavior of the corresponding curve when reducing modulo a prime. For instance, if in our normalized representation of the Igusa invariants a prime divides $`I_{10}`, then the curve does not have good reduction at that prime, though it may still have potentially good reduction.

The exact definition of the Igusa  invariants is as follows. Let $`X` be a curve of genus $`2`, which we may assume to be defined by an equation $`y^2 = f(x)` with $`f` a sextic in $`x`. Let $`I_2, I_4, I_6, I_{10}` be obtained from $`f` as in the definition of the {bpref "g2c.igusa_clebsch_invariants"}[Igusa-Clebsch invariants] of $`f`. Then the Igusa invariants are given by

$$`J_2 = I_2 / 8,\qquad\qquad\qquad\quad\ \ \ \\
J_4 = (4 J_2^2 - I_4) / 96,\qquad\qquad\ \\
J_6 = (8 J_2^3 - 160 J_2 J_4 - I_6) / 576, \\
J_8 = (J_2 J_6 - J_4^2) / 4,\qquad\qquad\ \\
J_{10} = I_{10} / 4096.\qquad\qquad\qquad\ \,`

These invariants will be integral whenever $`f` is integral. The invariant $`J_8` may appear redundant, but is crucial when reducing to a field of even characteristic.

Depends on: {uses "g2c.g2curve"}[] {uses "g2c.geom_iso_class"}[] {uses "g2c.igusa_clebsch_invariants"}[]
:::

:::definition "g2c.isogeny_class" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety, TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny")
*Isogeny class of an abelian variety.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.isogeny_class))

The *isogeny class* (over a field $`K`) of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a field $`K` is the set of isomorphism classes of abelian varieties over $`K` that are {bpref "av.isogeny"}[isogenous] to $`A` (over $`K`).

LMFDB entries for isogeny classes typically list only those elements of the isogeny class that are present in the LMFDB; for abelian varieties of dimension greater than 1 this means that the list of elements of the isogeny class will often be incomplete.

Isogeny class information listed on LMFDB pages for curves refer to the isogeny class of its {bpref "ag.jacobian"}[Jacobian].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "av.isogeny"}[]
:::

:::definition "g2c.jac_end_lattice"
*Endomorphism lattice.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.jac_end_lattice))

Let $`A` be an {bpref "ag.abelian_variety"}[abelian variety] over a field $`F`.  Given a field extension $`F' \supseteq F`, there is a natural inclusion of {bpref "ag.endomorphism_ring"}[endomorphism rings] $`\End(A)\subseteq\mathrm{End}(A_{F'})`, where $`A_{F'}` denotes the base change of $`A` to $`F'`.

Let $`K` be the {bpref "av.endomorphism_field"}[endomorphism field] of $`A`.  The set of endomorphism rings $`\mathrm{End}(A_{F'})` over subextensions $`K \supseteq F' \supseteq F` forms a lattice under inclusion, called the *endomorphism lattice* of $`A` over $`F`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.endomorphism_ring"}[] {uses "av.endomorphism_field"}[]
:::

:::definition "g2c.known_rational_points"
*Known rational points.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.known_rational_points))

For a curve $`X` of genus $`g\ge 2` over $`\Q` (or any {bpref "nf"}[number field]) the set of rational points $`X(\Q)` is finite, by a theorem of Faltings. At present no algorithm is known that explicitly computes a provably complete list of the points in $`X(\Q)`, but one can conduct a search among points of bounded height to obtain a list of *known rational points*.

Rational points on hyperelliptic curves are written in projective coordinates with respect to the weighted homogeneous equation $`y^2+h(x,z)y=f(x,z)` of degree $`2g+2` that is a smooth projective model for the curve $`X`, where $`y` has weight $`g+1`, while $`x` and $`z` both have weight 1.  This homogeneous equation is uniquely determined by the affine equation $`y^2+h(x)y=f(x)` listed as the {bpref "g2c.minimal_equation"}[minimal equation] for the curve.

Depends on: {uses "g2c.minimal_equation"}[] {uses "nf"}[]
:::

:::definition "g2c.lfunction"
The *L-function* of an {bpref "ag.abelian_variety"}[Abelian variety] $`A` over $`\Q` is defined as an {bpref "lfunction.euler_product"}[Euler product] $`\prod_p L_p(p^{-s})` over primes $`p`, where the *L-polynomial* $`L_p(T)` is an integer polynomial of degree at most $`2g`, where $`g` is the dimension of $`A`; the L-function of a curve is then defined as the L-function of its {bpref "ag.jacobian"}[Jacobian].  The $`L`-function is an invariant of the {bpref "g2c.isogeny_class"}[isogeny class] of $`A`.

For primes $`p` where $`A` has {bpref "g2c.good_reduction"}[good reduction] (all but finitely many), the polynomial $`L_p(T)=T^{2g}\chi(T^{-1})` is determined by the characteristic polynomial $`\chi(T)` of the Frobenius endomomrphism of the reduction of $`A` modulo $`p`.

The Euler factors at bad primes $`p` depend on the type of bad reduction $`A` has at $`p`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "g2c.good_reduction"}[] {uses "g2c.isogeny_class"}[] {uses "lfunction.euler_product"}[]
:::

:::definition "g2c.local_invariants"
*Local invariants.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.local_invariants))

The *local invariants* of a {bpref "g2c.g2curve"}[genus 2 curve] over $`\Q` include, for each prime $`p`:

- The $`p`-adic valuation $`\mathrm{ord}_p(\Delta)` of its {bpref "g2c.discriminant"}[discriminant];

- The $`p`-adic valuation $`\mathrm{ord}_p(N)` of the {bpref "ag.conductor"}[conductor] of its {bpref "ag.jacobian"}[Jacobian];

- The {bpref "g2c.tamagawa"}[Tamagawa number] $`c_p` ;

- The local root number;

- The L-factor at $`p`.

For primes of {bpref "g2c.good_reduction"}[good reduction] the valuations of both discriminant and conductor are $`0`, and the Tamagawa number is $`1`.

Depends on: {uses "ag.conductor"}[] {uses "ag.jacobian"}[] {uses "g2c.discriminant"}[] {uses "g2c.g2curve"}[] {uses "g2c.good_reduction"}[] {uses "g2c.tamagawa"}[]
:::

:::definition "g2c.locally_solvable" (lean := "AlgebraicGeometry.Scheme.IsLocallySolvable, AlgebraicGeometry.Scheme.PointOver, AlgebraicGeometry.Scheme.isLocallySolvable_of_nonempty, AlgebraicGeometry.Scheme.HasPointIn")
*Locally solvable.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.locally_solvable))

A {bpref "ag.curve"}[curve] defined over the rational numbers is said to be *locally solvable* if the equation(s) defining the curve have a solution over $`\R` and over {bpref "lf.qp"}[$`\Q_p`] for every prime $`p`.  For curves over {bpref "nf"}[number fields] we require solutions over every completion of the number field.

If the curve is {bpref "ag.singular_point"}[non-singular] (or even merely {bpref "ag.irreducible"}[geometrically irreducible]), then there are always at most finitely many primes $`p` such that the curve has no point over {bpref "lf.qp"}[$`\Q_p`].

Curves with a rational point are obviously always locally solvable, but the converse need not hold (unless the curve has {bpref "ag.curve.genus"}[genus] zero).  For example, the genus 1 curve $`3x^3+4y^3+5z^3=0` over $`\Q` is locally solvable but has no rational points (this example is due to Selmer).

Depends on: {uses "ag.curve"}[] {uses "ag.curve.genus"}[] {uses "ag.irreducible"}[] {uses "ag.singular_point"}[] {uses "lf.qp"}[] {uses "nf"}[]
:::

:::definition "g2c.maximal_galois_rep"
*Maximal image.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.maximal_galois_rep))

The image of the mod-$`\ell`  Galois representation associated to a genus 2 curve is *maximal* if it is as large as possible given constraints imposed by the Weil pairing and endomorphisms of the {bpref "ag.jacobian"}[Jacobian].

For *generic* curves the {bpref "ag.geom_endomorphism_ring"}[geometric endomorphism ring] of the Jacobian is $`\Z` and the maximal image is $`\GSp(4,\Z/\ell\Z)`. In all other cases it is a proper subgroup of $`\GSp(4,\Z/\ell\Z)`.

Depends on: {uses "ag.geom_endomorphism_ring"}[] {uses "ag.jacobian"}[]
:::

:::definition "g2c.mordell_weil_rank" (lean := "Module.finrank, TauCeti.AlgebraicGeometry.AbelianVariety, TauCeti.AlgebraicGeometry.AbelianVariety.isCommMonObj, CategoryTheory.Hom.commGroup")
*Mordell-Weil rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.mordell_weil_rank))

The Mordell-Weil theorem states that the set of rational points on an {bpref "ag.abelian_variety"}[abelian variety] over a number field forms a finitely generated abelian group, hence isomorphic to a group of the form $`T \oplus \Z^r`, where $`T` is a finite torsion group.  The integer $`r\ge 0` is the *Mordell-Weil rank* of the abelian variety.

Depends on: {uses "ag.abelian_variety"}[]
:::

:::definition "g2c.mw_generator"
*Mordell-Weil generator.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.mw_generator))

The {bpref "ag.mordell_weil"}[Mordell-Weil group] of an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a {bpref "nf"}[number field] $`K` is a finitely generated group, explicitly described by giving a $`\Z`-basis for the group, or equivalently a (minimal) set of *Mordell-Weil generators*.

When $`A` is the {bpref "ag.jacobian"}[Jacobian] of a {bpref "g2c.g2curve"}[genus 2 curve] $`X` over $`\Q`, elements of $`A(\Q)` can be specified as the linear equivalence class of a rational divisor $`D` on $`X` of degree zero.  If $`X` is defined by the (homogeneous) {bpref "g2c.minimal_equation"}[minimal equation]

$$`y^2 + h(x,z)y = f(x,z),`

we may express $`D` in the form $`D_0-nD_{\infty}`, where $`D_0` is a rational effective divisor of degree at most $`g=2` and $`D_{\infty}` is the sum of the points in the intersection of the curve with the line $`z=0` at infinity, with $`n=\deg(D_0)/\deg(D_{\infty})\in \{0,1,2\}`.

The divisor $`D_0` can be described by a pair of homogeneous polynomials $`a,b\in \Q[x,z]`, with $`a(x,z)` of degree at most $`2` and $`b(x,z)` of degree $`3`: the divisor $`D_0` is the intersection of $`X` with the locus of $`a(x,z)=0` and $`y=b(x,z)`.  When $`h=0` and $`\deg(f)=5` this is equivalent to the *Mumford representation* of $`D_0` as $`(u,v)` with $`u(x)=a(x,1)` and $`v(x)=b(x,1)`.

For example, on the curve $`X \colon y^2 - y = x^5` with homogenization $`y^2-yz^3=x^5z`, the Mordell-Weil generator $`x=0,\ y=z^3` specifies the class of the divisor $`(0:1:1)-(0:1:0)`.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.jacobian"}[] {uses "ag.mordell_weil"}[] {uses "g2c.g2curve"}[] {uses "g2c.minimal_equation"}[] {uses "nf"}[]
:::

:::definition "g2c.mw_generator_order" (lean := "orderOf, addOrderOf, Nat.card_zpowers")
*Order of a Mordell-Weil generator.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.mw_generator_order))

The *order* of a {bpref "g2c.mw_generator"}[generator] of the {bpref "ag.mordell_weil"}[Mordell-Weil group] is the cardinality of the cyclic subgroup it generates.

Depends on: {uses "ag.mordell_weil"}[] {uses "g2c.mw_generator"}[]
:::

:::definition "g2c.num_rat_wpts" (lean := "TauCeti.Place.weierstrassWeight, TauCeti.branchPlaces")
*Weierstrass points of a hyperelliptic curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.num_rat_wpts))

Every {bpref "ag.hyperelliptic_curve"}[hyperelliptic curve] is a
degree-2 cover of the projective line.  The *Weierstrass points* of the curve are the ramification points of this cover, of which there are $`2g+2`, where $`g` is the {bpref "ag.curve.genus"}[genus] of the curve.

Over a {bpref "ring.field"}[field] of characteristic not 2, a hyperelliptic curve of genus $`g`  always has a model of the form $`y^2=f(x)`, where $`\deg f = 2g+2`, in which case the Weierstrass points are simply the points $`(\alpha, 0)` where $`\alpha` is a root of $`f(x)`, of which any number between $`0` and $`2g+2` may be rational (defined over the field of definition of the curve).

For curves with a rational Weierstrass point, by moving this point to infinity one can put the curve in the form $`y^2=f(x)` with $`\deg f =2g+1`, but otherwise not.

Depends on: {uses "ag.curve.genus"}[] {uses "ag.hyperelliptic_curve"}[] {uses "ring.field"}[]
:::

:::definition "g2c.paramodular_conjecture"
*Paramodular conjecture.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.paramodular_conjecture))

The *paramodular conjecture* of Brumer and Kramer  makes precise an earlier conjecture of Yoshida [eudml.org/doc/142747](https://eudml.org/doc/142747).  The conjecture states that for every {bpref "ag.abelian_surface"}[abelian surface] $`A/\Q` of paramodular type (meaning $`\End(A)=\Z`) there exists a corresponding paramodular newform of level $`N` equal to the {bpref "ag.conductor"}[conductor] of $`A`.

For squarefree integers $`N` it is further conjectured that this correspondence gives a bijection between {bpref "av.isogeny_class"}[isogeny classes] of paramodular type abelian surfaces of conductor $`N` and paramodular newforms of level $`N`.

Depends on: {uses "ag.abelian_surface"}[] {uses "ag.conductor"}[] {uses "av.isogeny_class"}[]
:::

:::definition "g2c.real_period"
*Real period.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.real_period))

For an {bpref "ag.abelian_variety"}[abelian variety] $`A` of {bpref "ag.dimension"}[dimension] $`g` defined over $`\R` with period lattice $`\Lambda \subset \C^g`, the *real period* $`\Omega` is the covolume of $`\Lambda\cap\R^g` inside $`\R^g` multiplied by the number of components of $`A(\R)`.

Let $`A` be an abelian variety of dimension $`g` defined over $`\Q`. Let $`(\omega_1, \ldots, \omega_g)` be a basis of regular differentials on $`A(\R)` such that $`\omega_1 \wedge \ldots \wedge \omega_g` is a Néron differential of $`A`. Let $`(\gamma_1, \ldots, \gamma_g)` be a basis of conjugation invariant elements in the abelianised fundamental group of $`A(\C)`, i.e. a basis of  $`H_1(A(\C), \Z)^{\Gal(\C/\R)}`. Then the *real period* of $`A` is the real period of $`A(\R)` with associated period lattice generated by the vectors $`(\int_{\gamma_i} \omega_j)_{j=1}^g \in \C^g` for $`i = 1, \ldots, g`.

In case $`A` is the {bpref "ag.jacobian"}[Jacobian] of a curve $`C` over $`\Q` of {bpref "ag.curve.genus"}[genus] $`g`, the real period can be defined alternatively as follows. Let $`(\omega_1, \ldots, \omega_g)` be a basis of differentials in $`\omega_{\mathcal{C}/\Z}(\mathcal{C})`, the global sections of the canonical sheaf on a regular model $`\mathcal{C}` of $`C` over $`\Z`. Let $`(\gamma_1, \ldots, \gamma_{2g})` be a symplectic basis of the homology group $`H^1(C, \Z)`. Then the vectors $`(\int_{\gamma_i} \omega_i)_{j=1}^g \in \C^g` for $`i = 1, \ldots, 2g` generate the period lattice for $`A(\R)` and the real period is defined accordingly.

This generalises the {bpref "ec.q.real_period"}[real period] for an {bpref "ec"}[elliptic curve].

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.curve.genus"}[] {uses "ag.dimension"}[] {uses "ag.jacobian"}[] {uses "ec"}[] {uses "ec.q.real_period"}[]
:::

:::definition "g2c.regulator"
*Regulator of a genus 2 curve.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.regulator))

The *regulator* of a {bpref "g2c.g2curve"}[genus 2 curve] is the {bpref "ag.regulator"}[regulator] of its  Jacobian.

Depends on: {uses "ag.regulator"}[] {uses "g2c.g2curve"}[]
:::

:::definition "g2c.simple_equation" (lean := "HyperellipticEquation.simplifiedPolynomial, HyperellipticEquation.w, HyperellipticEquation.w_sq")
*Simplified equation.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.simple_equation))

A {bpref "ag.hyperelliptic_curve"}[hyperelliptic curve] over $`\Q` with a {bpref "g2c.minimal_equation"}[minimal equation] of the form

$$`y^2 + h(x)y = f(x),`

with $`h,f\in \Z[x]` can always be defined by a *simplified equation* of the form

$$`y^2 = g(x),`

with $`g\in \Z[x]` defined by $`g:=4f+h^2`.

In the LMFDB, invariants of hyperelliptic curves such as rational points and generators of the {bpref "ag.mordell_weil"}[Mordell-Weil group] of its {bpref "ag.jacobian"}[Jacobian] are always expressed in terms of the minimal equation, not the corresponding simplified equation (except in cases where the minimal equation has $`h=0` and the two coincide).

Depends on: {uses "ag.hyperelliptic_curve"}[] {uses "ag.jacobian"}[] {uses "ag.mordell_weil"}[] {uses "g2c.minimal_equation"}[]
:::

:::definition "g2c.st_group"
*Sato-Tate group of a genus 2 curve over Q.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.st_group))

The *Sato-Tate group* of a curve refers to the Sato-Tate group of its {bpref "ag.jacobian"}[Jacobian], which is a special case of the {bpref "st_group.definition"}[Sato-Tate group of a motive].

For {bpref "g2c.g2curve"}[genus 2 curves] over $`\mathbb{Q}` there are 6 possibilities for the {bpref "g2c.st_group_identity_component"}[identity component of the Sato-Tate group] and 34 possibilities for the full Sato-Tate group; these are labelled according to the classification in Fité-Kedlaya-Rotger-Sutherland, _Sato-Tate distributions and Galois endomorphism modules in genus 2_ . The generic case is $`\mathrm{USp}(4)`, which occurs if and only if the Jacobian of the curve has trivial endomorphism ring.

Depends on: {uses "ag.jacobian"}[] {uses "g2c.g2curve"}[] {uses "st_group.definition"}[]
:::

:::definition "g2c.st_group_identity_component"
*Sato-Tate group identity component.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.st_group_identity_component))

The {bpref "g2c.st_group"}[Sato-Tate group] of an {bpref "ag.abelian_variety"}[abelian variety] $`A` is a compact Lie group that is not necessarily connected; it may have a finite number of distinct components.  The component containing the identity element of the Sato-Tate group $`\mathrm{ST}(A)` is the *identity component*, denoted $`\mathrm{ST}^0(A)`; it acts as the identity of the *component group* $`\mathrm{ST}(A)/\mathrm{ST}^0(A)`.

For an abelian variety $`A` of dimension 2, including the {bpref "ag.jacobian"}[Jacobian] of a genus 2 curve, there are six possibilities for the identity component $`\mathrm{ST}^0(A)` (up to conjugacy), corresponding to the six possibilities for its {bpref "ag.real_geom_endomorphism_algebra"}[real geometric endomorphism algebra] $`\mathrm{End}(A_{\overline{\Q}})\otimes\R` (up to isomorphism).  These are listed below:

- $`\mathrm{U}(1)`, corresponding to $`\mathrm{End}(A_{\overline{\Q}})\otimes\R\simeq \mathrm{M}_2(\C)`, with real dimension 1; this occurs when $`A_{\overline{\Q}}` is isogenous to the square of a CM elliptic curve.

- $`\mathrm{SU}(2)`, corresponding to $`\mathrm{End}(A_{\overline{\Q}})\otimes\R\simeq \mathrm{M}_2(\R)`, with real dimension 3; this occurs when $`A_{\overline{\Q}}` is isogenous to the square of a non-CM elliptic curve.

- $`\mathrm{U}(1)\times\mathrm{U}(1)`, corresponding to $`\mathrm{End}(A_{\overline{\Q}})\otimes\R\simeq \C\times \C`, with real dimension 2; this occurs both when $`A_{\overline{\Q}}` is isogenous to a product of non-isogenous CM elliptic curves and when $`A_{\overline{\Q}}` is a simple abelian surface with CM.

- $`\mathrm{U}(1)\times\mathrm{SU}(2)`, corresponding to $`\mathrm{End}(A_{\overline{\Q}})\otimes\R\simeq \R\times\C`, with real dimension 4; this occurs when $`A_{\overline{\Q}}` is isogenous to the product of a CM elliptic curve with a non-CM ellliptic curve.

- $`\mathrm{SU}(2)\times\mathrm{SU}(2)`, corresponding to $`\mathrm{End}(A_{\overline{\Q}})\otimes\R\simeq \R\times\R`, with real dimension 6; this occurs both when $`A_{\overline{\Q}}` is isogenous to a product of non-isogenous non-CM elliptic curves and when $`A_{\overline{\Q}}` is a simple abelian surface with RM.

- $`\mathrm{USp}(4)`, corresponding to $`\mathrm{End}(A_{\overline{\Q}})\otimes\R\simeq \R`, with real dimension 10; this is the generic case.

Here CM denotes {bpref "ag.complex_multiplication"}[complex multiplication], and RM denotes {bpref "ag.real_multiplication"}[real multiplication].

For arbitrary $`A`, there is a canonical surjective homomorphism from the component group $`\mathrm{ST}(A)/\mathrm{ST}^0(A)` to the group $`\mathrm{Gal}(K/\Q)`, where $`K` is the minimal field over which all endomorphisms of $`A_{\overline{\Q}}` can be defined. For $`A` of dimension $`\leq 3`, this homomorphism is an isomorphism.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.complex_multiplication"}[] {uses "ag.jacobian"}[] {uses "ag.real_geom_endomorphism_algebra"}[] {uses "ag.real_multiplication"}[] {uses "g2c.st_group"}[]
:::

:::definition "g2c.tamagawa"
*Tamagawa numbers.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.tamagawa))

For an {bpref "ag.abelian_variety"}[abelian variety] $`A` over a {bpref "lf.padic_field"}[$`p`-adic field], the *Tamagawa number* of $`A` is the number of connected components of its Neron model.

For a smooth projective curve $`X/\Q` the Tamagawa number of $`X` at at a prime $`p` is the Tamagawa number of the {bpref "ag.base_change"}[base change] of its {bpref "ag.jacobian"}[Jacobian] to the field $`\Q_p`.

It is a positive integer that is equal to 1 at all primes of {bpref "g2c.good_reduction"}[good reduction] for the Jacobian; it may also be 1 at primes of bad reduction.

The product of the Tamagawa numbers over all primes is a positive integer known as the *Tamagawa product*.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.base_change"}[] {uses "ag.jacobian"}[] {uses "g2c.good_reduction"}[] {uses "lf.padic_field"}[]
:::

:::definition "g2c.torsion" (lean := "TauCeti.AlgebraicGeometry.AbelianVariety, TauCeti.GroupScheme.torsion")
*Torsion subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.torsion))

The *torsion subgroup* of an {bpref "ag.abelian_variety"}[abelian variety] over a {bpref "nf"}[number field]  is the subgroup of elements of finite order; it is a finite group that is isomorphic to the direct sum of at most $`2g` cyclic groups, where $`g` is the dimension of the abelian variety.

The structure of the torsion subgroup can be compactly described by listing its sequence of elementary divisors $`[d_1,\ldots,d_n]`, where each $`d_i` divides $`d_{i+1}`, indicating a finite abelian group that is isomorphic to $`\Z/d_1\Z\oplus \cdots \oplus\Z/d_n\Z`.

Depends on: {uses "ag.abelian_variety"}[] {uses "nf"}[]
:::

:::definition "g2c.torsion_order" (lean := "AddCommGroup.torsion, CommGroup.torsion, Nat.card, Nat.primeFactors")
*Torsion order.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.torsion_order))

The *torsion order* of a finitely-generated abelian group such as the Mordell-Weil group of the {bpref "ag.jacobian"}[Jacobian] of a curve over a {bpref "nf"}[number field] is the cardinality of its {bpref "g2c.torsion"}[torsion subgroup]. The *torsion primes* are the primes that divide the torsion order, equivalently, the primes $`\ell` for which the Jacobian has a rational point of order $`\ell`.

Depends on: {uses "ag.jacobian"}[] {uses "g2c.torsion"}[] {uses "nf"}[]
:::

:::definition "g2c.two_selmer_rank"
*2-Selmer rank.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.two_selmer_rank))

The *2-Selmer rank* of an {bpref "ag.abelian_variety"}[abelian variety] is the rank of its {bpref "ag.selmer_group"}[2-Selmer group].

The difference between the 2-Selmer rank and the 2-rank of the {bpref "g2c.torsion"}[torsion subgroup] is an upper bound on the rank of the {bpref "ag.mordell_weil"}[Mordell-Weil group].  This bound is tight if and only if the 2-part of the {bpref "ag.tate_shafarevich"}[Tate-Shafarevich group] is trivial

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.mordell_weil"}[] {uses "ag.selmer_group"}[] {uses "ag.tate_shafarevich"}[] {uses "g2c.torsion"}[]
:::

:::definition "g2c.two_torsion_field"
*2-torsion field.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/g2c.two_torsion_field))

The *2-torsion field* of an {bpref "ag.abelian_variety"}[abelian variety] is the minimal field extension over which the 2-torsion subgroup of its {bpref "ag.mordell_weil"}[Mordell-Weil group] is rational; it is a Galois extension of the field over which the abelian variety is defined.

The 2-torsion field of the Jacobian of a {bpref "ag.hyperelliptic_curve"}[hyperelliptic curve] of the form $`y^2=f(x)` is the same as the splitting field of the polynomial $`f(x)`.

For abelian varieties over number fields, the 2-torsion field is specified by giving a number field of minimal degree and absolute discriminant whose Galois closure is equal to the 2-torsion field.

Depends on: {uses "ag.abelian_variety"}[] {uses "ag.hyperelliptic_curve"}[] {uses "ag.mordell_weil"}[]
:::
