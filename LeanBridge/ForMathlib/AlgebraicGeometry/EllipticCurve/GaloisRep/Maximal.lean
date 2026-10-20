import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.LinearAlgebra.Determinant
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Torsion

/-!
# Maximal Galois representations of an elliptic curve

Let `W` be an elliptic curve over a field `F`, with separable closure `F^s`, and let `O` be its
geometric endomorphism ring `WeierstrassCurve.GeometricEnd W`, the endomorphisms over `F^s`. Then
`O` acts on `E[ℓ]` and on the Tate module `T_ℓ E`, and `Aut_O` denotes the automorphisms commuting
with this action. The mod-`ℓ` (respectively `ℓ`-adic) Galois representation is maximal if its
image contains the automorphisms of determinant `1` in `Aut_O(E[ℓ])` (respectively
`Aut_O(T_ℓ E)`). Without potential complex multiplication `O = ℤ` acts by scalars, `Aut_O` is all of
`Aut(E[ℓ])`, and maximality says that the image contains `SL₂(𝔽_ℓ)`. The LMFDB states this for
number fields `F`; the definitions make sense over any field.

## Main definitions

* `WeierstrassCurve.torsionGeometricEndCentralizer`: `Aut_O(E[ℓ])`.
* `WeierstrassCurve.IsMaximalModGaloisRepresentation` (LMFDB `ec.maximal_galois_rep`).
* `WeierstrassCurve.tateModuleGeometricEndCentralizer`: `Aut_O(T_ℓ E)`.
* `WeierstrassCurve.IsMaximalTateModuleGaloisRepresentation` (LMFDB
  `ec.maximal_elladic_galois_rep`): the `ℓ`-adic representation is maximal, that is, `ℓ` is a
  maximal prime for `W`.

## Main results

* `WeierstrassCurve.torsionGeometricEndCentralizer_eq_top`: without potential complex
  multiplication, `Aut_O(E[ℓ])` is all of `Aut(E[ℓ])`.
* `WeierstrassCurve.isMaximalModGaloisRepresentation_iff_of_not_hasGeometricCM`: without potential
  complex multiplication, the mod-`ℓ` representation is maximal exactly when its image contains
  every automorphism of determinant `1`.
-/

open Matrix TauCeti TauCeti.Isogeny
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq (SeparableClosure F)] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) (h : ¬W.HasGeometricCM)

/-- `Aut_O(E[ℓ])`: the `𝔽_ℓ`-linear automorphisms of the `ℓ`-torsion of `W` over a separable
closure that commute with the action of the geometric endomorphism ring `O`. -/
noncomputable def torsionGeometricEndCentralizer : Subgroup (LinearMap.GeneralLinearGroup (ZMod ℓ)
    (AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (ℓ : ℤ))) :=
  (Submonoid.centralizer
    (Set.range (Hom.torsionRepresentation (W⁄(SeparableClosure F)).toAffine ℓ))).units

/-- The mod-`ℓ` Galois representation of `W` is **maximal** (LMFDB `ec.maximal_galois_rep`) if its
image contains `SL₂(𝔽_ℓ) ∩ Aut_O(E[ℓ])`, the automorphisms of `E[ℓ]` of determinant `1` commuting
with the geometric endomorphisms. Without potential complex multiplication this says that the image
contains `SL₂(𝔽_ℓ)` (`isMaximalModGaloisRepresentation_iff_of_not_hasGeometricCM`). -/
def IsMaximalModGaloisRepresentation : Prop :=
  (Units.map LinearMap.det).ker ⊓ W.torsionGeometricEndCentralizer ℓ ≤
    (W.modGaloisRepresentation (K := SeparableClosure F) ℓ).range

include h in
/-- **Without potential complex multiplication, `Aut_O(E[ℓ])` is all of `Aut(E[ℓ])`**: the
geometric endomorphisms are integers, which act on `E[ℓ]` by scalars. -/
lemma torsionGeometricEndCentralizer_eq_top : W.torsionGeometricEndCentralizer ℓ = ⊤ := by
  have hS : Submonoid.centralizer
      (Set.range (Hom.torsionRepresentation (W⁄(SeparableClosure F)).toAffine ℓ)) = ⊤ := by
    refine eq_top_iff.mpr fun g _ ↦ ?_
    rintro - ⟨f, rfl⟩
    rcases not_exists_not.mp (by simpa [hasGeometricCM_iff] using h) f with ⟨n, rfl⟩
    rw [map_intCast]
    exact (Int.cast_commute n g).eq
  rw [torsionGeometricEndCentralizer, hS, Submonoid.units_top]

include h in
/-- **Without potential complex multiplication, the mod-`ℓ` representation is maximal exactly when
its image contains `SL₂(𝔽_ℓ)`**, that is, every automorphism of `E[ℓ]` of determinant `1`. -/
lemma isMaximalModGaloisRepresentation_iff_of_not_hasGeometricCM :
    W.IsMaximalModGaloisRepresentation ℓ ↔ (Units.map LinearMap.det).ker ≤
    (W.modGaloisRepresentation (K := SeparableClosure F) ℓ).range := by
  rw [IsMaximalModGaloisRepresentation, W.torsionGeometricEndCentralizer_eq_top ℓ h, inf_top_eq]

variable [Fact ℓ.Prime]

/-- `Aut_O(T_ℓ E)`: the `ℤ_ℓ`-linear automorphisms of the Tate module of `W` over a separable
closure that commute with the action of the geometric endomorphism ring `O`. -/
noncomputable def tateModuleGeometricEndCentralizer : Subgroup (LinearMap.GeneralLinearGroup ℤ_[ℓ]
    (TateModule ℓ (W⁄(SeparableClosure F)).toAffine.Point)) :=
  (Submonoid.centralizer (Set.range fun f : W.GeometricEnd ↦
    TateModule.mapLinearMap (p := ℓ) f.pointMapHom)).units

/-- The `ℓ`-adic Galois representation of `W` is **maximal**, and `ℓ` is a **maximal prime** for `W`
(LMFDB `ec.maximal_elladic_galois_rep`), if its image contains `SL₂(ℤ_ℓ) ∩ Aut_O(T_ℓ E)`, the
automorphisms of the Tate module of determinant `1` commuting with the geometric endomorphisms.
The LMFDB phrases it on `E[ℓ^∞]`, whose automorphisms are those of `T_ℓ E`. -/
def IsMaximalTateModuleGaloisRepresentation : Prop :=
  (Units.map LinearMap.det).ker ⊓ W.tateModuleGeometricEndCentralizer ℓ ≤
    (W.tateModuleGaloisRepresentation (K := SeparableClosure F) ℓ).asGroupHom.range

end WeierstrassCurve
