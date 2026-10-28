import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Hilbert modular surfaces" =>

This chapter lists the LMFDB definitions relating to *Hilbert modular surfaces*, migrated from the LaTeX blueprint. Each definition links back to its LMFDB knowl.

:::definition "hmsurface.arithmetic_genus" (lean := "AlgebraicGeometry.Scheme.Modules.eulerCharBelow, AlgebraicGeometry.Scheme.genus, TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology")
*Arithmetic genus.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.arithmetic_genus))

The *arithmetic genus* of a projective scheme $`X` is the alternating sum
$`\chi(\mathcal{O}_X) = \sum_{i=0}^{\dim X} (-1)^i \dim H^i(X, \mathcal{O}_X)`.
Note that some authors call this quantity the holomorphic Euler characteristic.
Additionally, some authors refer to the quantity $`p_a(X) = (-1)^{\dim X} (\chi(\mathcal{O}_X) - 1)` as the arithmetic genus.
:::

:::definition "hmsurface.congruence_subgroup" (lean := "HilbertModularGroup.principalCongruenceSubgroup, HilbertModularGroup.IsCongruenceSubgroup, HilbertModularGroup.IsLevel, HilbertModularGroup.level, HilbertModularGroup.glPlus")
*Congruence Subgroup.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.congruence_subgroup))

Let $`F` be a real quadratic field with ring of integers $`\Z_F`. Let
$`\frak{b}` be a fractional ideal in $`F` (the component ideal ).

A *principal congruence subgroup* $`\Gamma_{\frak{b}}(\frak{N})` is the kernel
of reduction-modulo-$`\frak{N}` within $`\GL^+(\Z_F \oplus \frak{b})` or $`\SL(\Z_F \oplus \frak{b})`.
A *congruence subgroup* $`\Gamma` is a subgroup of either $`\GL^+(\Z_F \oplus \frak{b})` or $`\SL(\Z_F \oplus \frak{b})` which contains
a principal congruence subgroup $`\Gamma_{\frak{b}}(\frak{N})`. The minimal such $`\frak{N}` is called the *level*.
:::

:::definition "hmsurface.elliptic_point" (lean := "Matrix.GeneralLinearGroup.IsEllipticTuple, Matrix.GeneralLinearGroup.ellipticPoint, Matrix.GeneralLinearGroup.IsTotallyElliptic, Matrix.GeneralLinearGroup.IsEllipticPoint, Matrix.GeneralLinearGroup.smul_eq_self_iff_eq_ellipticPoint")
*Elliptic point.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.elliptic_point))

A transformation $`(\alpha_1, \ldots, \alpha_n) \in \GL_2^+(\R)^n` is called *elliptic* if each

$$`\operatorname{tr}(\alpha_i)^2 - 4\det(\alpha_i) < 0.`

If $`F` is a real quadratic field, an element $`\alpha \in \GL_2^+(F)` is called *elliptic* if the above condition holds for each real embedding of $`F`. An *elliptic point* is the (necessarily unique) fixed point in $`\frak{h}^2` of an elliptic element.
:::

:::definition "hmsurface.euler_number" (lean := "AlgebraicGeometry.Scheme.topologicalEulerNumber, AlgebraicGeometry.Scheme.bettiNumber, AlgebraicGeometry.Scheme.ComplexPoint, AlgebraicGeometry.Scheme.ComplexPoint.continuous_eval, TopCat.singularCohomology")
*Topological Euler number.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.euler_number))

The *(topological) Euler number* of a smooth projective variety $`X` over a field of characteristic zero is the quantity

$$`\chi = \sum_{i=0}^{2\dim X} (-1)^i \cdot H^i(X(\mathbb{C}), \mathbb{Z})`

where the cohomology is singular cohomology on the topological space $`X(\mathbb{C})`.
:::

:::definition "hmsurface.hmsurface"
*Hilbert modular surface.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.hmsurface))

A *Hilbert modular surface* is a nice algebraic surface that parametrizes abelian surfaces with real multiplication and equipped with level structure.

More precisely, let $`F` be a real quadratic field.  Let $`\Gamma < \GL_2^+(F)` be a {bpref "hmsurface.congruence_subgroup"}[congruence subgroup].  Then $`\Gamma` is a discrete group acting properly by isometries on the product $`\overline{\mathfrak{h}}^2` of {bpref "mf.upper_half_plane"}[completed upper half-planes].

The quotient $`\overline{Y}(\Gamma)(\C) := \Gamma \backslash \mathfrak{h}^2` is the set of complex points of a projective surface $`Y(\Gamma)`, canonically defined over a number field $`E` (its reflex field).  A *Hilbert modular surface* is the minimal desingularization $`X(\Gamma)` of $`Y(\Gamma)`.  In particular, $`X(\Gamma)` is smooth, projective, and geometrically integral.

Depends on: {uses "hmsurface.congruence_subgroup"}[] {uses "mf.upper_half_plane"}[]
:::

:::definition "hmsurface.hodge_numbers" (lean := "AlgebraicGeometry.Scheme.relativeDifferentials, SheafOfModules.exteriorPower, TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology")
*Hodge numbers.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.hodge_numbers))

The *Hodge numbers* $`h^{p,q}` of a smooth projective variety $`X` over $`\mathbb{C}` are the dimensions of the complex vector spaces $`H^{p,q}(X) := H^q(X,\Omega^p)` appearing in the Hodge decomposition of the cohomology group $`H^n(X,\mathbb{C}) \cong \bigoplus_{p+q=n} H^{p,q}(X)`.
:::

:::definition "hmsurface.kodaira_dimension" (lean := "AlgebraicGeometry.Scheme.kodairaDimension, AlgebraicGeometry.Scheme.PlurigenusIsBigO, AlgebraicGeometry.Scheme.plurigenus, AlgebraicGeometry.Scheme.canonicalSheaf, AlgebraicGeometry.Scheme.kodairaDimension_eq_of_tendsto")
*Kodaira dimension.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.kodaira_dimension))

The *Kodaira dimension* of a projective variety $`X` with canonical bundle $`K`
is the smallest integer $`d` such that the limit

$$`\lim_{m \to \infty} \frac{H^0(X, K^{\otimes m})}{m^d}`

exists and is non-zero. In the case no such integer exists, our convention is
to take $`d=-1`.
:::

:::definition "hmsurface.level" (lean := "HilbertModularGroup.gammaZero, HilbertModularGroup.isCongruenceSubgroup_gammaZero, HilbertModularGroup.principalCongruenceSubgroup_le_gammaZero, HilbertModularGroup.gammaZeroLattice")
*Definition of the level.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.level))

The *level* is a nonzero ideal $`\mathfrak{N}` which determines the {bpref "hmsurface.congruence_subgroup"}[congruence subgroup] $`\Gamma_0(\mathfrak{N})_{\mathfrak{b}}`. In the LMFDB, such an ideal $`\mathfrak{N}` is identified by a label.

Depends on: {uses "hmsurface.congruence_subgroup"}[]
:::

:::definition "hmsurface.polarization_module"
*polarization module.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/hmsurface.polarization_module))

Let $`(A, \iota)` be an abelian variety with RM by $`\iota : \Z_F \to \End(A_{\overline{\Q}})`. The *polarization module* of $`A` is the $`\Z_F`-module

$$`\mathcal{PM}(A) = \{ \lambda \in \Hom_{\Z_F}(A, A^{\vee}) : \lambda = \lambda^{\vee}   \} \subseteq NS(A).`

The *polarization cone* is the cone of polarizations $`\mathcal{PM}^+(A) \subseteq \mathcal{PM}(A)`, which equips the polarization module with a notion of positivity as a $`\Z_F`-module. We say that a polarization module is \*isomorphic\* to a fractional ideal $`J` of $`\Z_F` if there is an orientation preserving $`\Z_F`-module isomorphism $`\phi : \mathcal{PM}(A) \to J`, i.e. such that $`\phi(\mathcal{PM}^+(A)) = J^+`.
:::
