import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
import LeanBridge.ForMathlib.AlgebraicGeometry.Scheme.FiniteFieldPoints
import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Frobenius

/-!
# Mod-`ℓ` Galois representations with values in the `𝔽_ℓ`-points of an algebraic group

A mod-`ℓ` Galois representation of a number field `K` is a continuous homomorphism
`ρ : Gal(K̄/K) → G(𝔽_ℓ)` to the `𝔽_ℓ`-points of an algebraic group `G` over `𝔽_ℓ` (LMFDB `modlgal`).
An algebraic group over a field `k` is a group scheme of finite type over `k` (Milne, *Algebraic
groups*, Definition 1.1): a group object `G` of the category of schemes over `Spec k`, whose
structure morphism is quasi-compact and locally of finite type. Its `k`-points are the sections
`Spec k → G` over `Spec k`, the morphisms `𝟙 ⟶ G` from the terminal object of `Over (Spec k)`,
which form a group (Mathlib's `CategoryTheory.Hom.group`). This is the most general of the usual
definitions: it contains the affine (linear) algebraic groups, as Tau Ceti's group schemes of
finite-type Hopf algebras, and the smooth ones, so it restricts no LMFDB codomain.

The codomain `G(𝔽_ℓ)` is a finite group (LMFDB `modlgal.codomain`): a scheme `X` of finite type
over a finite field `k` has finitely many `k`-points
(`AlgebraicGeometry.finite_points_of_finiteType`), the case `L = k` of LeanBridge's
`AlgebraicGeometry.Scheme.finite_pointOver`, by which `X` has finitely many points over every finite
extension `L` of `k`. Continuity for the discrete topology on `G(𝔽_ℓ)` means that the kernel of `ρ`
is open.

The Frobenius class and the Frobenius order (LMFDB `modlgal.frobenius_order`) make sense for a
homomorphism with open kernel into any group, and are defined in that generality in
`LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Frobenius` (`MonoidHom.frobeniusConjClass` and
`MonoidHom.frobeniusElementOrder`). The trivial representation into the `𝔽_ℓ`-points of any
algebraic group is a mod-`ℓ` Galois representation (`MonoidHom.isModEllGaloisRepIn_one`). The
general linear group `GL_n` over `𝔽_ℓ` is Tau Ceti's group scheme
`TauCeti.GeneralLinear.groupScheme`, an algebraic group in this sense, whose `𝔽_ℓ`-points form the
group `GL_n(𝔽_ℓ)` (`AlgebraicGeometry.rationalPointsGLMulEquiv`, through Tau Ceti's
`TauCeti.GeneralLinear.schemePointsMulEquiv` for the object `Spec 𝔽_ℓ` of `Over (Spec 𝔽_ℓ)`,
isomorphic to the terminal one).

## Main definitions

* `AlgebraicGeometry.rationalPoints` (LMFDB `modlgal.codomain`): the group `G(k)` of `k`-points
  of a group scheme over `k`.
* `MonoidHom.IsModEllGaloisRepIn` (LMFDB `modlgal`): mod-`ℓ` Galois representations into the
  `𝔽_ℓ`-points of an algebraic group over `𝔽_ℓ`.

## Main results

* `AlgebraicGeometry.finite_points_of_finiteType`: a scheme of finite type over a finite field `k`
  has finitely many `k`-points.
* `MonoidHom.IsModEllGaloisRepIn.finite_points` (LMFDB `modlgal.codomain`): the codomain `G(𝔽_ℓ)`
  of a mod-`ℓ` Galois representation is a finite group.
* `MonoidHom.IsModEllGaloisRepIn.frobeniusElementOrder_pos` (LMFDB `modlgal.frobenius_order`): the
  Frobenius order is positive, as an order in the finite group `G(𝔽_ℓ)`.
* `MonoidHom.isModEllGaloisRepIn_one` (LMFDB `modlgal`): the trivial representation into the
  `𝔽_ℓ`-points of an algebraic group, such as `GL_n`, is a mod-`ℓ` Galois representation.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory NumberField

open scoped MonObj

universe u

namespace AlgebraicGeometry

/-- The group `G(k)` of **`k`-points** of a group scheme `G` over a commutative ring `k` (LMFDB
`modlgal.codomain` for `k = 𝔽_ℓ`): the sections `Spec k → G` of its structure morphism, that is,
the morphisms from the terminal object of `Over (Spec k)` to `G`, with the group law of `G`. -/
abbrev rationalPoints {R : Type u} [CommRing R] (G : Grp (Over (Spec (.of R)))) : Type u :=
  𝟙_ (Over (Spec (.of R))) ⟶ G.X

noncomputable instance {R : Type u} [CommRing R] (G : Grp (Over (Spec (.of R)))) :
    Group (rationalPoints G) :=
  inferInstance

variable {k : Type u} [Field k] [Finite k]

/-- **A scheme of finite type over a finite field `k` has finitely many `k`-points**: the case
`L = k` of `AlgebraicGeometry.Scheme.finite_pointOver`, a `k`-point being a morphism `Spec k ⟶ X`
over `Spec k`. -/
lemma finite_points_of_finiteType (X : Over (Spec (.of k))) [QuasiCompact X.hom]
    [LocallyOfFiniteType X.hom] : Finite (𝟙_ (Over (Spec (.of k))) ⟶ X) :=
  have : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  have : Finite (X.left.PointOver k k) := X.left.finite_pointOver k
  Finite.of_injective (β := X.left.PointOver k k) (fun s ↦ ⟨s.left, by simp⟩) fun _ _ h ↦
    Over.OverMorphism.ext (congrArg Subtype.val h)

end AlgebraicGeometry

namespace MonoidHom

variable {K : Type*} [Field K] {ℓ : ℕ} {G : Grp (Over (Spec (.of (ZMod ℓ))))}

/-- A homomorphism `ρ : Gal(K̄/K) → G(𝔽_ℓ)` from the absolute Galois group of a number field `K` to
the `𝔽_ℓ`-points of a group scheme `G` over `𝔽_ℓ` is a **mod-`ℓ` Galois representation** (LMFDB
`modlgal`) if `ℓ` is prime, `G` is an algebraic group, that is, of finite type over `𝔽_ℓ`, and `ρ`
is continuous for the discrete topology on `G(𝔽_ℓ)`: its kernel is open. The `𝔽_ℓ`-points of `G`
are the sections of `G → Spec 𝔽_ℓ` (`AlgebraicGeometry.rationalPoints`), with the group structure
of the group object `G`. -/
structure IsModEllGaloisRepIn (ρ : Gal(AlgebraicClosure K/K) →* rationalPoints G) : Prop where
  /-- The characteristic `ℓ` is prime. -/
  prime : ℓ.Prime
  /-- The algebraic group `G` is locally of finite type over `𝔽_ℓ`. -/
  locallyOfFiniteType : LocallyOfFiniteType G.X.hom
  /-- The algebraic group `G` is quasi-compact over `𝔽_ℓ`. -/
  quasiCompact : QuasiCompact G.X.hom
  /-- A mod-`ℓ` Galois representation is continuous: its kernel is open. -/
  isOpen_ker : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))

namespace IsModEllGaloisRepIn

variable {ρ : Gal(AlgebraicClosure K/K) →* rationalPoints G}

/-- **The codomain `G(𝔽_ℓ)` of a mod-`ℓ` Galois representation is a finite group** (LMFDB
`modlgal.codomain`). -/
lemma finite_points (hρ : ρ.IsModEllGaloisRepIn) : Finite (rationalPoints G) := by
  have : Fact ℓ.Prime := ⟨hρ.prime⟩
  have : LocallyOfFiniteType G.X.hom := hρ.locallyOfFiniteType
  have : QuasiCompact G.X.hom := hρ.quasiCompact
  exact finite_points_of_finiteType G.X

variable [NumberField K] in
/-- **The Frobenius order of a mod-`ℓ` Galois representation is positive** (LMFDB
`modlgal.frobenius_order`): it is the order of `ρ(Frob_𝔭)` in the finite group `G(𝔽_ℓ)`. -/
lemma frobeniusElementOrder_pos (hρ : ρ.IsModEllGaloisRepIn) (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 (kerSplittingField ρ hρ.isOpen_ker))) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    0 < frobeniusElementOrder hρ.isOpen_ker 𝔭 hur := by
  have : Finite (rationalPoints G) := hρ.finite_points
  rcases ConjClasses.exists_rep (frobeniusConjClass hρ.isOpen_ker 𝔭 hur) with ⟨A, hA⟩
  rw [frobeniusElementOrder_eq hρ.isOpen_ker 𝔭 hur hA]
  exact orderOf_pos A

end IsModEllGaloisRepIn

/-- **The trivial representation into the `𝔽_ℓ`-points of an algebraic group is a mod-`ℓ` Galois
representation**, for `ℓ` prime and `G` of finite type over `𝔽_ℓ`, such as Tau Ceti's general
linear group scheme `GL_n` (`TauCeti.GeneralLinear.groupScheme`), affine and of finite type, its
special linear group scheme `SL_n` and the diagonal torus of `GL_n`: the hypotheses of
`MonoidHom.IsModEllGaloisRepIn` are satisfied by a concrete representation for every algebraic
group. -/
lemma isModEllGaloisRepIn_one (hℓ : ℓ.Prime) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    (1 : Gal(AlgebraicClosure K/K) →* rationalPoints G).IsModEllGaloisRepIn where
  prime := hℓ
  locallyOfFiniteType := ‹_›
  quasiCompact := ‹_›
  isOpen_ker := by
    rw [ker_one, Subgroup.coe_top]
    exact isOpen_univ

end MonoidHom
