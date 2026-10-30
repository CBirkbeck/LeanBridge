import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.KodairaDimension
import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic

/-!
# The self-intersection of the canonical divisor of a surface

Let `X` be a smooth projective surface over a field `k`, such as a Hilbert modular surface. The
**intersection number** of two line bundles `L` and `M` on `X` is
`(L · M) = χ(𝒪_X) - χ(L⁻¹) - χ(M⁻¹) + χ(L⁻¹ ⊗ M⁻¹)` (Beauville, *Complex algebraic surfaces*,
I.4; Hartshorne, *Algebraic geometry*, V, Exercise 1.1), where `χ(G) = ∑ᵢ (-1)ⁱ dim_k Hⁱ(X, G)` is
the Euler characteristic of a coherent sheaf `G`, a sum over `i ≤ 2` since the cohomology of a
coherent sheaf on a surface vanishes in degrees `i > 2`. By Beauville's theorem it is a symmetric
bilinear form on the Picard group, and `(𝒪(C) · 𝒪(D))` is the number of intersection points of two
curves `C` and `D` meeting transversally; only the symmetry is formalised here
(`AlgebraicGeometry.Scheme.surfaceIntersectionNumber_comm`). The **self-intersection of the
canonical divisor** `K` (LMFDB `hmsurface.k2`) is `K² = (ω_X · ω_X)` for the canonical line bundle
`ω_X = ⋀² Ω_{X/k}`. The knowl notes that it is also the first Chern number `c₁²` of `X`, as
`c₁(X) = -K`; Chern classes are not available, so this is not formalised.

The inverse `L⁻¹` of a line bundle is its dual `𝓗om(L, 𝒪_X)`, the internal Hom of Tau Ceti's closed
monoidal category of `𝒪_X`-modules, whose tensor product is used: by definition this is Tau Ceti's
`SheafOfModules.dual L`, which gives the inverse in its Picard group
`TauCeti.AlgebraicGeometry.LineBundleClass X`. The Euler characteristic `χ` is Tau Ceti's truncated
Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerCharBelow` in degrees `< 3`. The
definitions make sense for any scheme `X` over `k` and any `𝒪_X`-modules `L` and `M`; they give
the intersection numbers when `X` is a smooth projective surface and `L` and `M` are line bundles.
The canonical sheaf is `AlgebraicGeometry.Scheme.canonicalSheaf`, `⋀ⁿ Ω_{X/k}` for the dimension
`n` of `X`, which is `2` for a surface. The knowl's `K²` is that of a Hilbert modular surface,
which is not available.

## Main definitions

* `AlgebraicGeometry.Scheme.surfaceIntersectionNumber`: the intersection number `(L · M)`.
* `AlgebraicGeometry.Scheme.canonicalSelfIntersection` (LMFDB `hmsurface.k2`): the
  self-intersection `K²` of the canonical divisor.

## Main results

* `AlgebraicGeometry.Scheme.surfaceIntersectionNumber_comm`: the intersection number is symmetric.
-/

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

open Modules

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] (L M : X.Modules)

/-- The **intersection number** `(L · M) = χ(𝒪_X) - χ(L⁻¹) - χ(M⁻¹) + χ(L⁻¹ ⊗ M⁻¹)` of two line
bundles `L` and `M` on a smooth projective surface `X` over `k` (Beauville, I.4), where
`L⁻¹ = 𝓗om(L, 𝒪_X)` and `χ(G) = ∑_{i ≤ 2} (-1)ⁱ dim_k Hⁱ(X, G)`. It is defined for any scheme over
`k` and any `𝒪_X`-modules `L` and `M`. -/
noncomputable def surfaceIntersectionNumber : ℤ :=
  eulerCharBelow k X (𝟙_ X.Modules) 3 - eulerCharBelow k X ((ihom L).obj (𝟙_ X.Modules)) 3 -
    eulerCharBelow k X ((ihom M).obj (𝟙_ X.Modules)) 3 +
    eulerCharBelow k X ((ihom L).obj (𝟙_ X.Modules) ⊗ (ihom M).obj (𝟙_ X.Modules)) 3

/-- The **self-intersection `K²` of the canonical divisor** (LMFDB `hmsurface.k2`) of a smooth
projective surface `X` over `k`, such as a Hilbert modular surface: the intersection number
`(ω_X · ω_X) = χ(𝒪_X) - 2 χ(ω_X⁻¹) + χ(ω_X⁻²)` of its canonical line bundle `ω_X = ⋀² Ω_{X/k}`
with itself. It is also the first Chern number `c₁²` of `X`. -/
noncomputable def canonicalSelfIntersection : ℤ :=
  X.surfaceIntersectionNumber k (X.canonicalSheaf k) (X.canonicalSheaf k)

/-- **The intersection number is symmetric**: `(L · M) = (M · L)`, by the symmetry of the tensor
product of `𝒪_X`-modules. -/
lemma surfaceIntersectionNumber_comm :
    X.surfaceIntersectionNumber k L M = X.surfaceIntersectionNumber k M L := by
  rw [surfaceIntersectionNumber, surfaceIntersectionNumber, eulerCharBelow_congr k (β_ _ _) 3]
  ring1

end AlgebraicGeometry.Scheme
