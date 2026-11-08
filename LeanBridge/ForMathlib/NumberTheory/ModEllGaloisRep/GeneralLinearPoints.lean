import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Scheme
import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.AlgebraicGroup

/-!
# The rational points of the general linear group scheme and of its subgroups

For a commutative ring `R`, the group `G(R)` of `R`-points of a group scheme `G` over `R` is the
group of sections `𝟙_ ⟶ G` of `G → Spec R` (`AlgebraicGeometry.rationalPoints`). Tau Ceti describes
the points of its group schemes with values in an `R`-algebra `A` as the morphisms `Spec A ⟶ G` over
`Spec R`. For `A = R`, the structure morphism of `Spec R` over itself is the identity, so the unique
morphism `Spec R ⟶ 𝟙_` is an isomorphism, and precomposition with it identifies the two groups of
points. In particular, the `R`-points of Tau Ceti's general linear group scheme `GL_n` form the
group `GL_n(R)`.

A morphism of group schemes `ι : G ⟶ GL_n` over `R`, a linear representation of `G`, thus induces a
homomorphism `G(R) → GL_n(R)`, injective when `ι` is a monomorphism, for instance an embedding (a
closed immersion). For Tau Ceti's closed immersion of the special linear group scheme `SL_n` into
`GL_n`, the image consists of matrices of determinant `1`; for that of the diagonal split torus, the
image contains the scalar matrices. The instance `IsAffine (SpecialLinear.groupScheme R n).X.left`,
missing from Tau Ceti, makes `SL_n` quasi-compact over `R`, like `GL_n`.

The isomorphism `Spec R ⟶ 𝟙_` is obtained for an arbitrary base scheme and only then specialised to
`Spec R`: identifying the terminal object of `Over (Spec R)` with `Spec R` by unfolding definitions
makes the kernel unfold `Spec`, which takes about a minute already for a general ring `R`, and
several minutes for `R = ZMod ℓ`.

## Main definitions

* `CategoryTheory.Hom.mulEquivCongrLeft`: the isomorphism `(X ⟶ M) ≃* (Y ⟶ M)` of monoids of
  morphisms into a monoid object induced by an isomorphism `X ≅ Y`.
* `AlgebraicGeometry.rationalPointsMulEquivSchemePoints`: the `R`-points of a group scheme `G` over
  `R` are its `Spec R`-valued points over `Spec R`, the scheme-valued points of Tau Ceti.
* `AlgebraicGeometry.rationalPointsGLMulEquiv`: the `R`-points of `GL_n` form the group `GL_n(R)`.
* `AlgebraicGeometry.rationalPointsToGL`: the homomorphism `G(R) → GL_n(R)` induced by a morphism of
  group schemes `G ⟶ GL_n`.

## Main results

* `AlgebraicGeometry.rationalPointsToGL_injective`: an embedding `G ⟶ GL_n` is injective on
  `R`-points.
* `AlgebraicGeometry.rationalPointsToGL_id`: for `GL_n` itself, the identity induces the
  identification of its `R`-points with `GL_n(R)`.
* `AlgebraicGeometry.range_rationalPointsToGL_id`: so its image is all of `GL_n(R)`.
* `AlgebraicGeometry.det_rationalPointsToGL_specialLinear`: the `R`-points of `SL_n` are matrices of
  determinant `1`.
* `AlgebraicGeometry.center_le_range_rationalPointsToGL_diagonalTorus`: the diagonal torus of `GL_n`
  contains the scalar matrices.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Matrix TauCeti

universe u

namespace CategoryTheory

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y : C}

open scoped MonObj in
/-- An isomorphism `e : X ≅ Y` induces an isomorphism `(X ⟶ M) ≃* (Y ⟶ M)` between the monoids of
morphisms into a monoid object `M`, by precomposition with `e.inv`. -/
@[simps]
def Hom.mulEquivCongrLeft (e : X ≅ Y) (M : C) [MonObj M] : (X ⟶ M) ≃* (Y ⟶ M) where
  toFun f := e.inv ≫ f
  invFun g := e.hom ≫ g
  left_inv := e.hom_inv_id_assoc
  right_inv := e.inv_hom_id_assoc
  map_mul' := MonObj.comp_mul e.inv

end CategoryTheory

namespace TauCeti.SpecialLinear

instance {R : Type u} [CommRing R] {n : ℕ} : IsAffine (groupScheme R n).X.left := by
  rw [groupScheme_X_left]
  infer_instance

end TauCeti.SpecialLinear

namespace AlgebraicGeometry

instance {S : Scheme.{u}} (X : Over S) [IsIso X.hom] : IsIso (toUnit X) :=
  have : IsIso ((Over.forget S).map (toUnit X)) := ‹IsIso X.hom›
  isIso_of_reflects_iso _ (Over.forget S)

variable {R : Type u} [CommRing R] {n : ℕ} {G : Grp (Over (Spec (.of R)))}

instance : IsIso ((Spec (.of R)).asOver (Spec (.of R))).hom := by
  simp only [OverClass.asOver_hom, specOverSpec_over, Algebra.algebraMap_self, CommRingCat.ofHom_id,
    Spec.map_id]
  exact IsIso.id _

variable (G) in
open scoped MonObj in
/-- The `R`-points `𝟙_ ⟶ G` of a group scheme `G` over a commutative ring `R` are its
`Spec R`-valued points `Spec R ⟶ G` over `Spec R`, the scheme-valued points of Tau Ceti for the
`R`-algebra `R`, by precomposition with the unique morphism `Spec R ⟶ 𝟙_`, an isomorphism. -/
noncomputable def rationalPointsMulEquivSchemePoints :
    rationalPoints G ≃* ((Spec (.of R)).asOver (Spec (.of R)) ⟶ G.X) :=
  Hom.mulEquivCongrLeft (asIso (toUnit _)).symm G.X

lemma rationalPointsMulEquivSchemePoints_apply (x : rationalPoints G) :
    rationalPointsMulEquivSchemePoints G x = toUnit _ ≫ x :=
  rfl

variable (R n) in
open scoped MonObj in
/-- **The `R`-points of the general linear group scheme form the group `GL_n(R)`**: the `R`-points
of Tau Ceti's group scheme `GL_n` over `R` are its `Spec R`-valued points
(`AlgebraicGeometry.rationalPointsMulEquivSchemePoints`), which are the invertible matrices over `R`
(Tau Ceti's `TauCeti.GeneralLinear.schemePointsMulEquiv`). -/
noncomputable def rationalPointsGLMulEquiv :
    rationalPoints (GeneralLinear.groupScheme R n) ≃* GL (Fin n) R :=
  (rationalPointsMulEquivSchemePoints _).trans (GeneralLinear.schemePointsMulEquiv n R)

open scoped MonObj in
lemma rationalPointsGLMulEquiv_apply (x : rationalPoints (GeneralLinear.groupScheme R n)) :
    rationalPointsGLMulEquiv R n x = GeneralLinear.schemePointsMulEquiv n R (toUnit _ ≫ x) := by
  rw [rationalPointsGLMulEquiv, MulEquiv.trans_apply, rationalPointsMulEquivSchemePoints_apply]

variable (ι : G ⟶ GeneralLinear.groupScheme R n)

/-- The homomorphism `G(R) → GL_n(R)` on `R`-points induced by a morphism of group schemes
`ι : G ⟶ GL_n` over `R`, a linear representation of `G`: an `R`-point `x` of `G` is sent to the
`R`-point `ι ∘ x` of `GL_n`, an invertible matrix over `R`. It is injective when `ι` is an
embedding (`AlgebraicGeometry.rationalPointsToGL_injective`). -/
noncomputable def rationalPointsToGL : rationalPoints G →* GL (Fin n) R :=
  (rationalPointsGLMulEquiv R n).toMonoidHom.comp (IsMonHom.monoidHom ι.hom.hom _)

lemma rationalPointsToGL_apply (x : rationalPoints G) :
    rationalPointsToGL ι x = GeneralLinear.schemePointsMulEquiv n R (toUnit _ ≫ x ≫ ι.hom.hom) := by
  rw [rationalPointsToGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, IsMonHom.monoidHom_apply,
    rationalPointsGLMulEquiv_apply]

/-- **An embedding of group schemes into `GL_n` is injective on `R`-points**: if the morphism of
schemes underlying `ι : G ⟶ GL_n` is a monomorphism, as a closed immersion is, then so is the
induced homomorphism `G(R) → GL_n(R)`. -/
lemma rationalPointsToGL_injective [Mono ι.hom.hom.left] :
    Function.Injective (rationalPointsToGL ι) :=
  have : Mono ι.hom.hom := Over.mono_of_mono_left _
  (rationalPointsGLMulEquiv R n).injective.comp fun _ _ h ↦ (cancel_mono ι.hom.hom).mp h

/-- **For `GL_n` itself, the identity induces the identification of its `R`-points with
`GL_n(R)`.** -/
lemma rationalPointsToGL_id : rationalPointsToGL (𝟙 (GeneralLinear.groupScheme R n)) =
    (rationalPointsGLMulEquiv R n).toMonoidHom :=
  MonoidHom.ext fun x ↦ by
    rw [rationalPointsToGL, MonoidHom.comp_apply, IsMonHom.monoidHom_apply, Grp.id_hom_hom,
      Category.comp_id]

/-- **The image of `GL_n` under the identity is all of `GL_n(R)`**: in particular, `GL_n` with the
identity contains the scalar matrices. -/
lemma range_rationalPointsToGL_id :
    (rationalPointsToGL (𝟙 (GeneralLinear.groupScheme R n))).range = ⊤ := by
  rw [rationalPointsToGL_id, MonoidHom.range_eq_top]
  exact (rationalPointsGLMulEquiv R n).surjective

/-- **The `R`-points of the special linear group scheme are matrices of determinant `1`**: their
images in `GL_n(R)` under Tau Ceti's closed immersion `SL_n ⟶ GL_n` have determinant `1`. -/
lemma det_rationalPointsToGL_specialLinear (x : rationalPoints (SpecialLinear.groupScheme R n)) :
    GeneralLinearGroup.det (rationalPointsToGL (SpecialLinear.groupSchemeι R n) x) = 1 := by
  rw [rationalPointsToGL_apply, ← Category.assoc,
    SpecialLinear.schemePointsMulEquiv_comp_groupSchemeι]
  exact SpecialLinearGroup.coeToGL_det _

open scoped MonObj in
/-- **The diagonal torus of `GL_n` contains the scalars**: every scalar matrix in `GL_n(R)`, that
is, every element of its centre, is the image of an `R`-point of the diagonal split torus under Tau
Ceti's closed immersion `TauCeti.GeneralLinear.diagonalTorus`. -/
lemma center_le_range_rationalPointsToGL_diagonalTorus :
    Subgroup.center (GL (Fin n) R) ≤ (rationalPointsToGL GeneralLinear.diagonalTorus).range := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  rintro _ ⟨u, rfl⟩
  refine ⟨(rationalPointsMulEquivSchemePoints _).symm <|
    SplitTorus.schemePointsMulEquiv.symm fun _ ↦ u, ?_⟩
  rw [rationalPointsToGL_apply, ← Category.assoc, ← rationalPointsMulEquivSchemePoints_apply,
    MulEquiv.apply_symm_apply, GeneralLinear.schemePointsMulEquiv_diagonalTorus,
    MulEquiv.apply_symm_apply]
  exact diagGL_const u

end AlgebraicGeometry
