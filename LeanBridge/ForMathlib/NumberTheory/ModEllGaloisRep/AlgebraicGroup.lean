import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
import TauCeti.AlgebraicGeometry.RationalPoint.Affine
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

The codomain `G(𝔽_ℓ)` is a finite group (LMFDB `modlgal.codomain`): a scheme of finite type over a
finite field `k` has finitely many `k`-points
(`AlgebraicGeometry.finite_points_of_finiteType`), since every `k`-point factors through one of
finitely many affine opens `Spec A`, `A` a finitely generated `k`-algebra, where it is a
`k`-algebra map `A → k` (Tau Ceti's `AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom`); the file
adds the instance `Finite (A →ₐ[R] B)` for `A` of finite type over `R` and `B` finite. Continuity
for the discrete topology on `G(𝔽_ℓ)` means that the kernel of `ρ` is open.

The Frobenius class and the Frobenius order (LMFDB `modlgal.frobenius_order`) make sense for a
homomorphism with open kernel into any group, and are defined here in that generality, as in
`LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Frobenius` for `GL_n(𝔽_ℓ)`. The general linear
group `GL_n` over `𝔽_ℓ` is Tau Ceti's group scheme `TauCeti.GeneralLinear.groupScheme`, an
algebraic group in this sense (`MonoidHom.isModEllGaloisRepIn_one`), whose points over `Spec 𝔽_ℓ`
Tau Ceti identifies with `GL_n(𝔽_ℓ)` (`TauCeti.GeneralLinear.schemePointsMulEquiv`, for the object
`Spec 𝔽_ℓ` of `Over (Spec 𝔽_ℓ)`, isomorphic to the terminal one).

## Main definitions

* `AlgebraicGeometry.rationalPoints` (LMFDB `modlgal.codomain`): the group `G(k)` of `k`-points
  of a group scheme over `k`.
* `MonoidHom.IsModEllGaloisRepIn` (LMFDB `modlgal`): mod-`ℓ` Galois representations into the
  `𝔽_ℓ`-points of an algebraic group over `𝔽_ℓ`.
* `MonoidHom.kerSplittingField`: the fixed field of the open kernel of a representation, a finite
  Galois extension of `K`.
* `MonoidHom.kerGaloisFactor`: the homomorphism from its Galois group through which `ρ` factors.
* `MonoidHom.frobeniusConjClass`: the conjugacy class of the images of the Frobenius elements at an
  unramified prime.
* `MonoidHom.frobeniusElementOrder` (LMFDB `modlgal.frobenius_order`): the Frobenius order.

## Main results

* `AlgebraicGeometry.finite_points_of_finiteType`: a scheme of finite type over a finite field `k`
  has finitely many `k`-points.
* `MonoidHom.IsModEllGaloisRepIn.finite_points` (LMFDB `modlgal.codomain`): the codomain `G(𝔽_ℓ)`
  of a mod-`ℓ` Galois representation is a finite group.
* `MonoidHom.frobeniusElementOrder_eq` (LMFDB `modlgal.frobenius_order`): the Frobenius order is the
  order of any element of the Frobenius class.
* `MonoidHom.IsModEllGaloisRepIn.frobeniusElementOrder_pos` (LMFDB `modlgal.frobenius_order`): the
  Frobenius order is positive, as an order in the finite group `G(𝔽_ℓ)`.
* `MonoidHom.isModEllGaloisRepIn_one` (LMFDB `modlgal`): the trivial representation into the
  `𝔽_ℓ`-points of the algebraic group `GL_n` is a mod-`ℓ` Galois representation.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory IntermediateField NumberField

open scoped MonObj

universe u

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Algebra.FiniteType R A]
    [Semiring B] [Algebra R B] [Finite B] : Finite (A →ₐ[R] B) := by
  rcases ‹Algebra.FiniteType R A›.out with ⟨s, hs⟩
  exact Finite.of_injective (fun φ : A →ₐ[R] B ↦ fun x : s ↦ φ x) fun φ ψ h ↦
    AlgHom.ext_of_adjoin_eq_top hs fun x hx ↦ congrFun h ⟨x, hx⟩

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

lemma finite_points_of_isAffine {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType g] : Finite (𝟙_ (Over (Spec (.of k))) ⟶ Over.mk g) := by
  let _ : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hg : g.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  have : Algebra.FiniteType k Γ(Y, ⊤) := hg.comp <| .of_surjective _
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact Finite.of_equiv _ (g.pointsEquivAlgHom rfl).symm

/-- **A scheme of finite type over a finite field `k` has finitely many `k`-points**: every point
factors through one of finitely many affine opens `Spec A`, where it is a `k`-algebra map `A → k`
for a finitely generated `k`-algebra `A`. -/
lemma finite_points_of_finiteType (X : Over (Spec (.of k))) [QuasiCompact X.hom]
    [LocallyOfFiniteType X.hom] : Finite (𝟙_ (Over (Spec (.of k))) ⟶ X) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let 𝒰 : X.left.OpenCover := X.left.affineCover.finiteSubcover
  have hfin (i : 𝒰.I₀) : Finite (𝟙_ (Over (Spec (.of k))) ⟶ Over.mk (𝒰.f i ≫ X.hom)) :=
    have : IsAffine (𝒰.X i) := Scheme.isAffine_affineCover _ _
    finite_points_of_isAffine _
  refine Finite.of_surjective (fun p : Σ i, (𝟙_ (Over (Spec (.of k))) ⟶ Over.mk (𝒰.f i ≫ X.hom)) ↦
    p.2 ≫ Over.homMk (𝒰.f p.1)) fun s ↦ ?_
  have : Unique (𝟙_ (Over (Spec (.of k)))).left := inferInstanceAs (Unique (PrimeSpectrum k))
  let i : 𝒰.I₀ := 𝒰.idx (s.left default)
  have H : Set.range s.left ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    exact 𝒰.covers _
  refine ⟨⟨i, Over.homMk (IsOpenImmersion.lift (𝒰.f i) s.left H) ?_⟩, ?_⟩
  · simp
  · ext1
    simp

end AlgebraicGeometry

namespace MonoidHom

section Frobenius

variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H]
  {ρ : Gal(AlgebraicClosure K/K) →* H} (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K)))

variable (ρ) in
/-- The **splitting field** of a homomorphism `ρ : Gal(K̄/K) → H` with open kernel (LMFDB
`modlgal.splitting_field`): the fixed field of its kernel, a finite Galois extension of `K`. -/
noncomputable def kerSplittingField : FiniteGaloisIntermediateField K (AlgebraicClosure K) where
  toIntermediateField := fixedField ρ.ker
  finiteDimensional := ρ.finiteDimensional_fixedField_ker hρ
  isGalois := ρ.isGalois_fixedField_ker hρ

/-- The homomorphism `Gal(L/K) → H` through which a homomorphism `ρ : Gal(K̄/K) → H` with open
kernel factors, `L` being its splitting field. -/
noncomputable def kerGaloisFactor : Gal(kerSplittingField ρ hρ/K) →* H :=
  (QuotientGroup.kerLift ρ).comp
    (InfiniteGalois.normalAutEquivQuotient ⟨ρ.ker, ρ.ker.isClosed_of_isOpen hρ⟩).symm.toMonoidHom

variable (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] (hur : ∀ (Q : Ideal (𝓞 (kerSplittingField ρ hρ)))
  [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- The **Frobenius class** of a homomorphism `ρ : Gal(K̄/K) → H` with open kernel at a prime `𝔭`
of `K` unramified in its splitting field `L`: the image under `ρ` of the conjugacy class of the
Frobenius elements of `Gal(L/K)` at the primes above `𝔭`, Tau Ceti's `NumberField.artinSymbol`. -/
noncomputable def frobeniusConjClass : ConjClasses H :=
  (artinSymbol 𝔭 hur).map (kerGaloisFactor hρ)

/-- The **Frobenius order** (LMFDB `modlgal.frobenius_order`) of a homomorphism `ρ : Gal(K̄/K) → H`
with open kernel at a prime `𝔭` of `K` at which `ρ` is unramified: the order of `ρ(Frob_𝔭)` in `H`,
which does not depend on the choice of `Frob_𝔭` in its conjugacy class
(`MonoidHom.frobeniusElementOrder_eq`). -/
noncomputable def frobeniusElementOrder : ℕ :=
  Quotient.lift (s := IsConj.setoid _) (fun A : H ↦ orderOf A)
    (fun _ _ h ↦ by
      rcases isConj_iff.mp h with ⟨c, rfl⟩
      exact ((MulAut.conj c).orderOf_eq _).symm) (frobeniusConjClass hρ 𝔭 hur)

/-- **The Frobenius order is the order of any element of the Frobenius class.** -/
lemma frobeniusElementOrder_eq {A : H} (hA : ConjClasses.mk A = frobeniusConjClass hρ 𝔭 hur) :
    frobeniusElementOrder hρ 𝔭 hur = orderOf A := by
  rw [frobeniusElementOrder, ← hA]
  rfl

end Frobenius

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

open TauCeti in
/-- **The trivial representation into the `𝔽_ℓ`-points of `GL_n` is a mod-`ℓ` Galois
representation**: the general linear group scheme over `𝔽_ℓ` (Tau Ceti's
`TauCeti.GeneralLinear.groupScheme`), affine and of finite type, is an algebraic group, so that the
hypotheses of `MonoidHom.IsModEllGaloisRepIn` are satisfied by a concrete representation. -/
lemma isModEllGaloisRepIn_one (hℓ : ℓ.Prime) (n : ℕ) : (1 : Gal(AlgebraicClosure K/K) →*
    rationalPoints (GeneralLinear.groupScheme (ZMod ℓ) n)).IsModEllGaloisRepIn where
  prime := hℓ
  locallyOfFiniteType := inferInstance
  quasiCompact := inferInstance
  isOpen_ker := by
    rw [ker_one, Subgroup.coe_top]
    exact isOpen_univ

end MonoidHom
