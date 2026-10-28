import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Elliptic elements and elliptic points of Hilbert modular groups

A tuple `(α₁, …, αₙ)` of elements of `GL₂⁺(ℝ)` is **elliptic** if every `αᵢ` is elliptic, that is,
`tr(αᵢ)² - 4 det(αᵢ) < 0`: Mathlib's `Matrix.IsElliptic`, the discriminant being negative. An
elliptic element of `GL₂⁺(ℝ)` fixes exactly one point of the upper half-plane `ℍ`, Mathlib's
`UpperHalfPlane.fixedPt`, so an elliptic tuple, acting componentwise on `ℍⁿ`, fixes exactly one
point of `ℍⁿ`, its **elliptic point**. An element `g` of `GL₂(F)`, for a field `F`, real quadratic
for the LMFDB, is **elliptic** if its images `φ(g)` under all the real embeddings `φ : F →+* ℝ` are.
It acts on `ℍ^{Hom(F, ℝ)}`, which is `ℍ²` for a real quadratic field, through the tuple of these
images, and the elliptic point of `g` is that of this tuple. The elliptic points of a subgroup of
`GL₂(F)`, such as a Hilbert modular group, are the fixed points of its elliptic elements.

Ellipticity forces a positive determinant, so the definitions are stated on `GL₂(ℝ)` and `GL₂(F)`
rather than on `GL₂⁺`: an elliptic tuple lies in `GL₂⁺(ℝ)ⁿ`, and an elliptic element of `GL₂(F)`
has a totally positive determinant, so lies in `GL₂⁺(F)`.

## Main definitions

* `Matrix.GeneralLinearGroup.IsEllipticTuple` (LMFDB `hmsurface.elliptic_point`): an elliptic
  tuple of elements of `GL₂(ℝ)`.
* `Matrix.GeneralLinearGroup.ellipticPoint` (LMFDB `hmsurface.elliptic_point`): its elliptic point.
* `Matrix.GeneralLinearGroup.realEmbeddingsHom`: the homomorphism `GL₂(F) → GL₂(ℝ)^{Hom(F, ℝ)}`.
* `Matrix.GeneralLinearGroup.IsTotallyElliptic` (LMFDB `hmsurface.elliptic_point`): an elliptic
  element of `GL₂(F)`.
* `Matrix.GeneralLinearGroup.IsEllipticPoint` (LMFDB `hmsurface.elliptic_point`): an elliptic
  point of a subgroup of `GL₂(F)`.

## Main results

* `Matrix.GeneralLinearGroup.smul_eq_self_iff_eq_ellipticPoint`: the elliptic point of an elliptic
  tuple is its unique fixed point in `ℍⁿ`.
* `Matrix.GeneralLinearGroup.IsTotallyElliptic.isTotallyPositive_det`: an elliptic element of
  `GL₂(F)` has a totally positive determinant.
* `Matrix.GeneralLinearGroup.isEllipticPoint_iff`: the elliptic points of a subgroup of `GL₂(F)`
  are the points of `ℍ^{Hom(F, ℝ)}` fixed by one of its elliptic elements.
-/

open NumberField InfinitePlace UpperHalfPlane

namespace Matrix

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {m : Matrix (Fin 2) (Fin 2) R}

lemma IsElliptic.det_pos (hm : m.IsElliptic) : 0 < m.det := by
  have h : m.trace ^ 2 - 4 * m.det < 0 := discr_fin_two m ▸ hm
  nlinarith [sq_nonneg m.trace]

namespace GeneralLinearGroup

variable {ι F : Type*} [Field F] (α : ι → GL (Fin 2) ℝ) {z : ι → ℍ} (g : GL (Fin 2) F)
  (Γ : Subgroup (GL (Fin 2) F)) (w : (F →+* ℝ) → ℍ)

/-- A tuple `(αᵢ)` of elements of `GL₂(ℝ)` is **elliptic** (LMFDB `hmsurface.elliptic_point`) if
every `αᵢ` is elliptic, that is, `tr(αᵢ)² - 4 det(αᵢ) < 0`. Every `αᵢ` then has a positive
determinant, so the tuple lies in `GL₂⁺(ℝ)ⁿ`, where the LMFDB takes it. -/
def IsEllipticTuple : Prop :=
  ∀ i, (α i).IsElliptic

/-- The **elliptic point** (LMFDB `hmsurface.elliptic_point`) of an elliptic tuple `(αᵢ)`: the
point of `ℍⁿ` whose `i`-th coordinate is the fixed point of `αᵢ` in `ℍ`. It is the unique fixed
point of the tuple acting componentwise on `ℍⁿ` (`smul_eq_self_iff_eq_ellipticPoint`). -/
noncomputable def ellipticPoint (h : IsEllipticTuple α) : ι → ℍ :=
  fun i ↦ fixedPt (α i) (h i)

/-- **The elliptic point of an elliptic tuple is its unique fixed point** in `ℍⁿ`, for the
componentwise action. -/
lemma smul_eq_self_iff_eq_ellipticPoint (h : IsEllipticTuple α) :
    α • z = z ↔ z = ellipticPoint α h :=
  (funext_iff.trans <| forall_congr' fun i ↦
    gl_smul_eq_self_iff_eq_fixedPt (h i).det_pos (h i)).trans funext_iff.symm

variable (F) in
/-- The images `(φ(α))_φ` of an element `α` of `GL₂(F)` under all the real embeddings
`φ : F →+* ℝ` of a field `F`, as a homomorphism `GL₂(F) → GL₂(ℝ)^{Hom(F, ℝ)}`. Through it `GL₂(F)`
acts componentwise on `ℍ^{Hom(F, ℝ)}`, which is `ℍ²` for a real quadratic field. -/
noncomputable def realEmbeddingsHom : GL (Fin 2) F →* (F →+* ℝ) → GL (Fin 2) ℝ :=
  MonoidHom.pi fun φ ↦ map φ

@[simp]
lemma realEmbeddingsHom_apply (φ : F →+* ℝ) : realEmbeddingsHom F g φ = map φ g :=
  rfl

/-- An element `g` of `GL₂(F)` is **elliptic** (LMFDB `hmsurface.elliptic_point`) if its image
under every real embedding `φ : F →+* ℝ` is elliptic; we say **totally elliptic**, as for totally
positive elements, to tell it apart from `Matrix.GeneralLinearGroup.IsElliptic` over an ordered
ring. The LMFDB takes `F` real quadratic and `g ∈ GL₂⁺(F)`; ellipticity forces the determinant of
`g` to be totally positive (`IsTotallyElliptic.isTotallyPositive_det`). The elliptic point of `g`
is the elliptic point `ellipticPoint (realEmbeddingsHom F g) h` of the tuple of its images. -/
def IsTotallyElliptic : Prop :=
  IsEllipticTuple (realEmbeddingsHom F g)

variable {g} in
/-- **An elliptic element of `GL₂(F)` has a totally positive determinant**, so it lies in
`GL₂⁺(F)`. -/
lemma IsTotallyElliptic.isTotallyPositive_det (h : g.IsTotallyElliptic) :
    IsTotallyPositive g.val.det :=
  fun _ hw ↦ by simpa [RingHom.map_det] using (h (embedding_of_isReal hw)).det_pos

/-- A point `w` of `ℍ^{Hom(F, ℝ)}`, which is `ℍ²` for a real quadratic field `F`, is an
**elliptic point** (LMFDB `hmsurface.elliptic_point`) of a subgroup `Γ` of `GL₂(F)`, such as a
Hilbert modular group, if it is the elliptic point of an elliptic element of `Γ`, that is, the
fixed point of an elliptic element of `Γ` (`isEllipticPoint_iff`). -/
def IsEllipticPoint : Prop :=
  ∃ γ ∈ Γ, ∃ h : γ.IsTotallyElliptic, w = ellipticPoint (realEmbeddingsHom F γ) h

variable {Γ w} in
/-- **The elliptic points of a subgroup `Γ` of `GL₂(F)` are the points of `ℍ^{Hom(F, ℝ)}` fixed
by an elliptic element of `Γ`.** -/
lemma isEllipticPoint_iff :
    IsEllipticPoint Γ w ↔ ∃ γ ∈ Γ, γ.IsTotallyElliptic ∧ realEmbeddingsHom F γ • w = w :=
  exists_congr fun _ ↦ and_congr_right fun _ ↦
    (exists_congr fun h ↦ (smul_eq_self_iff_eq_ellipticPoint _ h).symm).trans exists_prop

end GeneralLinearGroup

end Matrix
