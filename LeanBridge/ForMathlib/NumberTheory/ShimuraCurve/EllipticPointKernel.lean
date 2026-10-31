import Mathlib.Algebra.Central.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.RingTheory.SimpleRing.Basic
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EllipticPoint

/-!
# The kernel of the action of `Γ_H^+` on the upper half-plane

An elliptic point of the Shimura curve `X_H` (LMFDB `shimcurve.elliptic_points`) is a point with
nontrivial stabilizer. On the geometric component `Γ_H^+ \ ℍ`, the stabilizer of the image of `τ`
is that of `τ` in the group by which `Γ_H^+` acts on `ℍ`, the quotient of `Γ_H^+` by the kernel of
the action. The elliptic points `Subalgebra.shimuraEllipticPoints` are defined as the orbits of the
points fixed by an element of `Γ_H^+` that is not a rational scalar; this file proves that, when `B`
is a central simple `ℚ`-algebra (such as a quaternion algebra), the rational scalars are exactly the
elements of `Γ_H^+` acting trivially on `ℍ`, so that the definition is the nontriviality of the
stabilizers in the group acting on `ℍ`. A matrix fixing every point of `ℍ` is central in `GL₂(ℝ)`
(Mathlib's `UpperHalfPlane.forall_smul_eq_self_iff_mem_center`), hence scalar, and an element of `B`
sent by `ι` to a scalar matrix is central, `ι` being injective, hence rational.

## Main results

* `Subalgebra.forall_smul_eq_self_iff_mem_normalizerRatUnits`: an element of `Γ_H^+` acts trivially
  on `ℍ` exactly when it is a rational scalar.
* `Subalgebra.quotientMk_mem_shimuraEllipticPoints_iff_exists_smul_ne`
  (LMFDB `shimcurve.elliptic_points`): the orbit of `τ` is an elliptic point exactly when some
  element of `Γ_H^+` fixing `τ` acts nontrivially on `ℍ`.
-/

open Algebra Matrix MulAction UpperHalfPlane

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] [Algebra.IsCentral ℚ B] [IsSimpleRing B]
  {O : Subalgebra ℤ B} {μ : B} {H : Subgroup (O.EnhancedGroup μ)}
  {ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ} {γ : O.shimuraGammaPlus μ H ι}

lemma mem_normalizerRatUnits_of_forall_smul_eq (h : ∀ τ : ℍ, γ • τ = τ) :
    (γ : O.unitsNormalizer) ∈ O.normalizerRatUnits := by
  rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
    (forall_smul_eq_self_iff_mem_center.mp h) with ⟨r, hr⟩
  have hscal : ι ((γ : O.unitsNormalizer) : Bˣ) = scalar (Fin 2) r := hr.symm
  have hcomm (b : B) : b * ((γ : O.unitsNormalizer) : Bˣ) = ((γ : O.unitsNormalizer) : Bˣ) * b :=
    ι.toRingHom.injective <| by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_mul, hscal]
      exact (scalar_commute r (Commute.all r) (ι b)).eq.symm
  have hmem : (((γ : O.unitsNormalizer) : Bˣ) : B) ∈ (⊥ : Subalgebra ℚ B) :=
    IsCentral.center_eq_bot ℚ B ▸ mem_center_iff.mpr hcomm
  rcases Algebra.mem_bot.mp hmem with ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact Units.ne_zero _ (hq.symm.trans (map_zero _))
  exact Subgroup.mem_subgroupOf.mpr ⟨Units.mk0 q hq0, Units.ext hq⟩

/-- **The elements of `Γ_H^+` acting trivially on the upper half-plane are the rational scalars**,
for `B` central simple over `ℚ` and any `ℚ`-algebra map `ι : B → M₂(ℝ)`: a matrix fixing every
point of `ℍ` is a scalar matrix, and an element sent by the injective map `ι` to a scalar matrix is
central, hence rational. -/
lemma forall_smul_eq_self_iff_mem_normalizerRatUnits :
    (∀ τ : ℍ, γ • τ = τ) ↔ (γ : O.unitsNormalizer) ∈ O.normalizerRatUnits :=
  ⟨mem_normalizerRatUnits_of_forall_smul_eq, fun hγ τ ↦ smul_eq_self_of_mem_normalizerRatUnits τ hγ⟩

/-- **The elliptic points are the points with nontrivial stabilizer** (LMFDB
`shimcurve.elliptic_points`) on the geometric component `Γ_H^+ \ ℍ` of the Shimura curve `X_H`,
for `B` central simple over `ℚ`: the orbit of `τ` is an elliptic point exactly when some element of
`Γ_H^+` fixing `τ` acts nontrivially on `ℍ`, that is, when the stabilizer of `τ` in the group by
which `Γ_H^+` acts on `ℍ` is nontrivial. -/
lemma quotientMk_mem_shimuraEllipticPoints_iff_exists_smul_ne (τ : ℍ) :
    (Quotient.mk _ τ : orbitRel.Quotient (O.shimuraGammaPlus μ H ι) ℍ) ∈
    O.shimuraEllipticPoints μ H ι ↔ ∃ γ : O.shimuraGammaPlus μ H ι, γ • τ = τ ∧
    ∃ τ' : ℍ, γ • τ' ≠ τ' := by
  rw [quotientMk_mem_shimuraEllipticPoints_iff]
  simp only [← forall_smul_eq_self_iff_mem_normalizerRatUnits, not_forall]

end Subalgebra
