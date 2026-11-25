import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "GitHub issues" =>

45 entries. The project's GitHub issues, with what remains to be done for each.

# Issues (1–30 of 45)

* [#13](https://github.com/CBirkbeck/LeanBridge/issues/13) (open) — General: Conrey labels and Galois orbits of Dirichlet characters. Remaining: Conrey labelling and the orbit labels N.a: Conrey labels are on Tau Ceti main ('TauCeti.conreyCharacter') and can be linked after the pin bump. Knowls: `character.dirichlet.conrey`, `character.dirichlet.conrey.conductor`, `character.dirichlet.conrey.parity`, `character.dirichlet.conrey.primitive_generator`.
* [#14](https://github.com/CBirkbeck/LeanBridge/issues/14) (open) — Number fields: torsion generator, monogenicity, ramified primes. Remaining: A canonical torsion generator; a decision procedure for monogenicity; LMFDB-facing wrappers.
* [#15](https://github.com/CBirkbeck/LeanBridge/issues/15) (open) — Number fields: computable polynomial irreducibility and roots over UFDs.
* [#16](https://github.com/CBirkbeck/LeanBridge/issues/16) (open) — Elliptic curves: conductor, root number, Kodaira types & Tate's algorithm. Remaining: Local and global root numbers: stuck on the Langlands–Deligne local constants (ε-factors), which Tau Ceti main lacks too. Knowls: `ec.local_data`, `ec.local_root_number`.
* [#17](https://github.com/CBirkbeck/LeanBridge/issues/17) (closed) — Hasse-Weil bound and finite-field point counting for elliptic curves. Remaining: Closed in June. Counts over 𝔽\_\{p\^n\} via Conway polynomials (the Conway polynomials themselves, with existence for every n, are formalised); a reusable point-counting procedure; the converse 'a\_q² ≤ 4q ⇒ roots of modulus √q'.
* [#18](https://github.com/CBirkbeck/LeanBridge/issues/18) (closed) — Atkin-Lehner operators and Fricke signs for modular forms. Remaining: Closed in June. Test cases at levels 11, 37 and pq (no concrete newforms of level \> 1); normalised W\_Q and pseudo-eigenvalues with nebentypus.
* [#19](https://github.com/CBirkbeck/LeanBridge/issues/19) (open) — Modular forms: eta quotients and the Ligozat modularity criterion. Remaining: The Ligozat criterion.
* [#22](https://github.com/CBirkbeck/LeanBridge/issues/22) (open) — Elliptic curves: mod-m / adelic images of Galois, and level/index/genus. Remaining: The mod-m image for general m; the genus shown to be the genus of X\_H (no X\_H yet); the genus formula shown to be a nonnegative integer independent of N; LMFDB labels. Knowls: `ec.galois_rep_elladic_image`, `ec.rouse_label`, `gl2.label`, `modcurve`, `modcurve.genus`, `modcurve.label`, `modcurve.other_labels`.
* [#25](https://github.com/CBirkbeck/LeanBridge/issues/25) (closed) — Elliptic curves: Néron–Tate canonical height and elliptic regulator. Remaining: Closed. Verifying regulators by interval arithmetic: needs explicit naive/canonical height bounds (Tau Ceti's are existential) and certified logarithms.
* [#26](https://github.com/CBirkbeck/LeanBridge/issues/26) (open) — Elliptic curves: real/complex periods, complex Néron lattice, AGM, Faltings height. Remaining: The period lattice (uniformisation of E(ℂ)); the AGM. Knowls: `ec.q.faltings_ratio`, `ec.q.period_lattice`.
* [#27](https://github.com/CBirkbeck/LeanBridge/issues/27) (open) — Elliptic curves: special values of L-functions and modularity coefficients. Remaining: a\_p(E) = the coefficients of the attached newform; anything beyond the BSD statements. Knowls: `ec.q.manin_constant`, `ec.q.modular_degree`, `ec.q.modular_form`, `ec.q.modular_parametrization`.
* [#28](https://github.com/CBirkbeck/LeanBridge/issues/28) (open) — Elliptic curves: the Sato–Tate group. Remaining: The Sato–Tate group of a motive or elliptic curve (SU(2) for non-CM E/ℚ); the Sato–Tate measure on normalised traces; equidistribution. Knowls: `ag.sato_tate_group`, `g2c.st_group`, `g2c.st_group_identity_component`, `st_group.definition`.
* [#29](https://github.com/CBirkbeck/LeanBridge/issues/29) (open) — Elliptic curves: the Lutz–Nagell theorem.
* [#32](https://github.com/CBirkbeck/LeanBridge/issues/32) (closed) — Modular forms: Satake parameters and Satake angles. Remaining: Closed. Deligne's theorem itself; it is the named hypothesis 'RamanujanDeligne'.
* [#33](https://github.com/CBirkbeck/LeanBridge/issues/33) (open) — Modular forms: LMFDB labels (level.weight.char\_orbit.hecke\_orbit). Knowls: `cmf.embedding_label`, `cmf.label`, `cmf.labels`.
* [#34](https://github.com/CBirkbeck/LeanBridge/issues/34) (open) — Modular forms: coefficient field of a newform. Remaining: Nothing on the formal side: degree = dimension is now proved with no hypothesis (issue \#38), and the coefficient field is a number field in every weight ('numberField\_coefficientField'). To recheck under the ruling of 11-04: the LMFDB error in cmf.coefficient\_field (conjugate newforms have isomorphic, not equal, coefficient fields in ℂ).
* [#35](https://github.com/CBirkbeck/LeanBridge/issues/35) (open) — Modular forms: Hecke characteristic polynomials. Remaining: cmf.distinguishing\_primes is partial (the LMFDB's canonical primes); the characteristic polynomial of T\_n on all of S\_k(N,χ). Knowls: `cmf.distinguishing_primes`.
* [#36](https://github.com/CBirkbeck/LeanBridge/issues/36) (open) — Modular forms: spaces of modular symbols.
* [#37](https://github.com/CBirkbeck/LeanBridge/issues/37) (open) — Modular forms: Eisenstein series with Dirichlet characters. Remaining: Weights 1 and 2 with character; a basis of Eisenstein newforms; cmf.eisenstein\_label. Knowls: `cmf.eisenstein_label`, `cmf.eisenstein_newform`, `cmf.eisenstein_newspace`, `cmf.labels`, `cmf.new_subspaces`, `cmf.subspaces`.
* [#38](https://github.com/CBirkbeck/LeanBridge/issues/38) (open) — Modular forms: Galois-conjugate forms and Galois orbits. Remaining: Formalised with no hypothesis: σ(f) for every σ ('exists\_isGaloisConjugateBy'), the Galois orbit, and its size \[K\_f : ℚ\] = the dimension ('ncard\_galoisOrbit\_eq', 'dimension\_eq\_ncard\_galoisOrbit'). Partial by the ruling of 11-04, because their LMFDB texts are wrong: cmf.galois\_orbit (the orbit is a basis over ℂ, not over ℚ) and cmf.hecke\_orbit (the span of the T\_p(f) is ℂf for an eigenform).
* [#39](https://github.com/CBirkbeck/LeanBridge/issues/39) (open) — Modular forms: the Galois representation attached to a form (and Artin field/image). Remaining: ρ\_\{f,ℓ\} in weight ≥ 2; Deligne–Serre existence in weight 1. Knowls: `cmf.galois_representation`, `cmf.projective_image`, `cmf.sato_tate`, `ec.q.serre_invariants`.
* [#40](https://github.com/CBirkbeck/LeanBridge/issues/40) (open) — Modular forms: Shimura correspondence (half-integral weight). Remaining: The Shimura correspondence map from weight k/2 to weight k − 1 itself. Knowls: `cmf.shimura_correspondence`, `mf.half_integral_weight.shimura_decomposition`.
* [#41](https://github.com/CBirkbeck/LeanBridge/issues/41) (open) — Modular forms: Stark units. Knowls: `cmf.stark_unit`.
* [#43](https://github.com/CBirkbeck/LeanBridge/issues/43) (open) — General: Artin representations. Remaining: Artin L-functions; the link to Frobenius classes; the Artin representation of a Dirichlet character. Knowls: `artin.dimensionone`, `artin.lfunction`, `artin.root_number`.
* [#44](https://github.com/CBirkbeck/LeanBridge/issues/44) (open) — General: local invariants of ℓ-adic Galois representations (Artin conductor, ε-factors, L-factors). Knowls: `ag.conductor`, `artin.lfunction`, `artin.root_number`, `ec.local_data`, `ec.local_root_number`, `g2c.bad_lfactors`, `g2c.conductor`, `g2c.lfunction`, `g2c.local_root_number`, `lf.root_number`.
* [#45](https://github.com/CBirkbeck/LeanBridge/issues/45) (open) — General: prime number certificates (Pocklington, ECPP).
* [#46](https://github.com/CBirkbeck/LeanBridge/issues/46) (open) — Number fields: Kronecker–Weber theorem. Knowls: `artin.dimensionone`.
* [#47](https://github.com/CBirkbeck/LeanBridge/issues/47) (open) — General: Lubin–Tate theory.
* [#49](https://github.com/CBirkbeck/LeanBridge/issues/49) (open) — General: transitive (T-number) Galois group labels. Knowls: `belyi.label`, `gg.label`, `gg.resolvents`, `gg.tnumber`, `modlgal.min_sib_splitting_field`, `modlgal.projective_kernel_polynomial`, `nf.minimal_sibling`.
* [#50](https://github.com/CBirkbeck/LeanBridge/issues/50) (open) — General: abc quality of a coprime triple (and the radical).

# Issues (31–45 of 45)

* [#53](https://github.com/CBirkbeck/LeanBridge/issues/53) (open) — Elliptic curves: basic API for torsion subgroups. Remaining: Named torsion-order definitions; test cases (11a: order 5).
* [#54](https://github.com/CBirkbeck/LeanBridge/issues/54) (open) — Modular forms: bad primes. Remaining: A named bad-primes definition and lemma; test cases.
* [#55](https://github.com/CBirkbeck/LeanBridge/issues/55) (open) — Modular forms: dual and self-dual cusp forms (predicate).
* [#56](https://github.com/CBirkbeck/LeanBridge/issues/56) (open) — Number fields: totally positive elements (predicate). Remaining: Rated 'mostly done' on 2026-10-19; recheck its items and test cases.
* [#57](https://github.com/CBirkbeck/LeanBridge/issues/57) (open) — Lattices: theta series of an integral lattice. Remaining: 'thetaSeries' and its modularity. Knowls: `lattice.theta`.
* [#58](https://github.com/CBirkbeck/LeanBridge/issues/58) (open) — Lattices: kissing number and Hermite invariant. Remaining: 'hermiteNumber'; the kissing numbers of ℤ², A₂ and ℤⁿ.
* [#59](https://github.com/CBirkbeck/LeanBridge/issues/59) (open) — Lattices: genus and class number of an integral lattice. Remaining: A lattice 'classNumber', its finiteness, and the computations in dimensions 8, 16 and 24.
* [#60](https://github.com/CBirkbeck/LeanBridge/issues/60) (open) — Groups: complex and rational character tables of a finite group. Remaining: The rational character table shown well defined (constant on rational classes) and square; row and column orthogonality as matrix identities; the table of a general C\_n. Knowls: `group.label_complex_group_char`, `group.label_rational_group_char`.
* [#61](https://github.com/CBirkbeck/LeanBridge/issues/61) (open) — Groups: LMFDB finite-group label (small-group identification). Knowls: `group.label`, `group.label_complex_group_char`, `group.label_rational_group_char`, `group.small_group_label`.
* [#62](https://github.com/CBirkbeck/LeanBridge/issues/62) (open) — Groups: Gassmann equivalence (and arithmetically equivalent fields). Remaining: The equivalence with ℚ\[H₁\\G\] ≅ ℚ\[H₂\\G\]; arithmetic equivalence of fields (equal Dedekind zeta functions); the order-32 / GL(3,2) test case. Knowls: `gg.arithmetically_equivalent`, `group.gassmann_equivalence`.
* [#64](https://github.com/CBirkbeck/LeanBridge/issues/64) (open) — Local fields: ramification polygon and higher-ramification (Herbrand) data. Remaining: The ramification polygon; Herbrand functions of non-Galois extensions in the LMFDB normalisation; test cases (ℚ₂(√2), ℚ\_p(ζ\_\{p²\})).
* [#65](https://github.com/CBirkbeck/LeanBridge/issues/65) (open) — Abelian varieties over F\_q: Weil polynomial, L-polynomial, and Honda-Tate. Remaining: 'weilPolynomial A' of an abelian variety; the L-polynomial; the functional equation; Honda–Tate; the g = 1 and E₁ × E₂ test cases. Knowls: `av.fq.honda_tate`, `av.fq.l-polynomial`, `av.fq.weil_polynomial`, `g2c.good_lfactors`, `g2c.lfunction`.
* [#66](https://github.com/CBirkbeck/LeanBridge/issues/66) (open) — Abelian varieties over F\_q: p-rank, ordinary and supersingular. Remaining: 'IsSupersingular' for abelian varieties; 0 ≤ pRank ≤ g; for g = 1, ordinary ⇔ p ∤ a\_p; the bridge to 'WeierstrassCurve.IsSupersingular'; pRank A = the p-rank of its Weil polynomial. Knowls: `av.fq.supersingular`.
* [#74](https://github.com/CBirkbeck/LeanBridge/issues/74) (open) — Number fields: certifying class groups and regulators.
* [#75](https://github.com/CBirkbeck/LeanBridge/issues/75) (open) — Hecke ring definition. Remaining: Modular forms of all levels in a commensurability class (an IsModularForm predicate or a direct limit); eigenforms and newforms on that space.
