import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum

/-!
# Densities of lattice packings

The density (LMFDB `lattice.density`) of a positive definite integral lattice `L` of rank `n` is
the density of the sphere packing of `ℝⁿ` centred at the points of `L`. Its spheres have radius
`ρ`, half the length `√(min L)` of a shortest nonzero vector, so that the minimum of `L`, the least
norm `min L` of a nonzero vector, is `(2ρ)²`. With `G` a Gram matrix of `L` and
`V_n = π^{n/2} / (n/2)!` the volume of the unit ball of `ℝⁿ`, the density is
`Δ = V_n ρⁿ / √(det G)`, and the centre density is `δ = Δ / V_n = ρⁿ / √(det G)`. The knowl writes
that the minimum is `2ρ`, which is the length of a shortest vector, not the minimum `min L` of LMFDB
`lattice.minimum`.

The density is the volume of a ball of radius `ρ` divided by the covolume of `L` realized in
`ℝⁿ` (`density_eq_volume_div_covolume`), the proportion of space that the packing fills. That this
is the limit of the proportion of large balls covered by the packing is not formalised.

The lattice packing problem in dimension `n` asks for the positive definite lattices of rank `n`
of largest density, `TauCeti.IntegralLattice.IsDensestLattice`, and their density is
`TauCeti.IntegralLattice.latticePackingDensity n`. As in the LMFDB, lattices are integral; since
the largest density of a lattice of `ℝⁿ` is attained by a perfect lattice, which is similar to an
integral one (Voronoi), this is the classical lattice packing problem of `ℝⁿ`, but that is not
formalised. The sphere packing problem asks for the largest density
`EuclideanSpace.spherePackingDensity n` of a packing of balls of the same radius, whose centres
need not form a lattice, the density of a packing being the upper limit of the proportion of large
balls that it covers.

## Main definitions

* `EuclideanSpace.unitBallVolume`: the volume `V_n` of the unit ball of `ℝⁿ`.
* `TauCeti.IntegralLattice.packingRadius`: the radius `ρ` of the spheres of the packing.
* `TauCeti.IntegralLattice.density` (LMFDB `lattice.density`).
* `TauCeti.IntegralLattice.centerDensity` (LMFDB `lattice.density`).
* `TauCeti.IntegralLattice.latticePackingDensity` (LMFDB `lattice.density`).
* `TauCeti.IntegralLattice.IsDensestLattice` (LMFDB `lattice.density`).
* `EuclideanSpace.packingDensity`: the density of a packing of balls of the same radius.
* `EuclideanSpace.spherePackingDensity` (LMFDB `lattice.density`).

## Main results

* `EuclideanSpace.unitBallVolume_eq`: `V_n` is the volume of the unit ball of `ℝⁿ`.
* `TauCeti.IntegralLattice.density_eq_volume_div_covolume`: the density is the volume of a ball of
  radius `ρ` divided by the covolume of a realization of `L` in Euclidean space.
* `TauCeti.IntegralLattice.Isometry.density_eq`: the density is an isometry invariant.
* `TauCeti.IntegralLattice.density_le_latticePackingDensity` and
  `TauCeti.IntegralLattice.IsDensestLattice.density_le`: the lattice packing density bounds the
  density of every positive definite lattice of rank `n`, and a densest lattice attains it.
-/

open Module MeasureTheory
open scoped ENNReal InnerProductSpace Real

namespace EuclideanSpace

variable (n : ℕ)

/-- The volume `V_n = π^{n/2} / (n/2)!` (LMFDB `lattice.density`) of the unit ball of `ℝⁿ`, with
`(n/2)! = Γ(n/2 + 1)`. -/
noncomputable def unitBallVolume : ℝ :=
  √π ^ n / Real.Gamma (n / 2 + 1)

/-- **`V_n` is the volume of the unit ball of `ℝⁿ`.** -/
lemma unitBallVolume_eq [NeZero n] :
    unitBallVolume n = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  rw [volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity), unitBallVolume]

lemma unitBallVolume_pos : 0 < unitBallVolume n :=
  div_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))

variable {n} in
/-- The **density** of the packing of the balls of radius `r` centred at the points of `X ⊆ ℝⁿ`:
the upper limit, as `R → ∞`, of the proportion of the ball of radius `R` centred at `0` that the
balls cover. -/
noncomputable def packingDensity (X : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun R : ℝ ↦ volume ((⋃ x ∈ X, Metric.ball x r) ∩ Metric.ball 0 R) /
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)) Filter.atTop

/-- The **sphere packing density** of `ℝⁿ` (LMFDB `lattice.density`, the sphere packing problem):
the largest density of a packing of balls of the same radius `r` with pairwise disjoint interiors,
that is centred at points at distance at least `2r` from each other, which need not form a lattice;
a supremum in `ℝ≥0∞`. -/
noncomputable def spherePackingDensity : ℝ≥0∞ :=
  ⨆ (X : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) (_ : X.Pairwise fun x y ↦ 2 * r ≤ dist x y),
    packingDensity X r

end EuclideanSpace

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  (L : IntegralLattice V) {M : IntegralLattice W}

/-- The **packing radius** `ρ` of a positive definite integral lattice `L`: half the length
`√(min L)` of its shortest nonzero vectors, the radius of the spheres of the packing centred at the
points of `L`. -/
noncomputable def packingRadius : ℝ :=
  √(L.minimum : ℝ) / 2

/-- The **centre density** `δ = ρⁿ / √(det G)` (LMFDB `lattice.density`) of a positive definite
integral lattice `L` of rank `n`, with packing radius `ρ` and Gram matrix `G`. -/
noncomputable def centerDensity : ℝ :=
  L.packingRadius ^ finrank ℤ L / √(L.determinant : ℝ)

/-- The **density** `Δ = V_n ρⁿ / √(det G)` (LMFDB `lattice.density`) of a positive definite
integral lattice `L` of rank `n`, with packing radius `ρ` and Gram matrix `G`, `V_n` being the
volume of the unit ball of `ℝⁿ`: the volume of a ball of radius `ρ` divided by the covolume of `L`
(`density_eq_volume_div_covolume`). -/
noncomputable def density : ℝ :=
  EuclideanSpace.unitBallVolume (finrank ℤ L) * L.packingRadius ^ finrank ℤ L /
    √(L.determinant : ℝ)

/-- The **lattice packing density** in dimension `n` (LMFDB `lattice.density`, the lattice packing
problem): the largest density of a positive definite integral lattice of rank `n`, a supremum in
`ℝ≥0∞`. It is taken over the lattices of `ℚⁿ`, which is no restriction
(`density_le_latticePackingDensity`). -/
noncomputable def latticePackingDensity (n : ℕ) : ℝ≥0∞ :=
  ⨆ (M : IntegralLattice (Fin n → ℚ)) (_ : M.IsPosDef), ENNReal.ofReal M.density

/-- A positive definite integral lattice `L` **solves the lattice packing problem** (LMFDB
`lattice.density`) in its dimension `n` if its density is the largest density of a positive
definite lattice of rank `n`. -/
def IsDensestLattice : Prop :=
  L.IsPosDef ∧ latticePackingDensity (finrank ℤ L) ≤ ENNReal.ofReal L.density

lemma density_eq_mul_centerDensity :
    L.density = EuclideanSpace.unitBallVolume (finrank ℤ L) * L.centerDensity :=
  mul_div_assoc _ _ _

lemma packingRadius_nonneg : 0 ≤ L.packingRadius :=
  div_nonneg (Real.sqrt_nonneg _) zero_le_two

lemma density_nonneg : 0 ≤ L.density :=
  div_nonneg (mul_nonneg (EuclideanSpace.unitBallVolume_pos _).le
    (pow_nonneg L.packingRadius_nonneg _)) (Real.sqrt_nonneg _)

variable {L}

/-- **The density of a positive definite lattice is the volume of a ball of radius `ρ` divided by
the covolume of a realization of the lattice in Euclidean space.** -/
lemma density_eq_volume_div_covolume (hL : L.IsPosDef) [Nontrivial L] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {φ : L →ₗ[ℤ] E} (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y)
    (hspan : Submodule.span ℝ (Set.range φ) = ⊤) : L.density =
      (volume (Metric.ball (0 : E) L.packingRadius)).toReal /
        ZLattice.covolume (LinearMap.range φ) := by
  have : L.IsNondegenerate := ⟨(L.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hL).2⟩
  have : DiscreteTopology (LinearMap.range φ) := discreteTopology_range hφ
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  have hrank : finrank ℝ E = finrank ℤ L := by
    rw [← ZLattice.rank ℝ (LinearMap.range φ),
      LinearMap.finrank_range_of_inj (injective_of_inner_eq hφ)]
  have hpos : 0 < finrank ℝ E := hrank ▸ finrank_pos
  have : Nontrivial E := nontrivial_of_finrank_pos hpos
  rw [covolume_range_eq_sqrt_discriminant hφ hspan, InnerProductSpace.volume_ball,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal L.packingRadius_nonneg,
    ENNReal.toReal_ofReal (by positivity), hrank, discriminant_def, Nat.cast_natAbs, Int.cast_abs,
    abs_of_pos (by exact_mod_cast hL.determinant_pos), density, EuclideanSpace.unitBallVolume]
  ring1

/-- **The density is an isometry invariant.** -/
lemma Isometry.density_eq (e : Isometry L M) : L.density = M.density := by
  rw [density, density, packingRadius, packingRadius, e.finrank_carrier_eq, e.minimum_eq,
    e.determinant_eq]

/-- **The density of a positive definite lattice of rank `n` is at most the lattice packing density
in dimension `n`**, whatever rational space the lattice lies in. -/
lemma density_le_latticePackingDensity (hL : L.IsPosDef) :
    ENNReal.ofReal L.density ≤ latticePackingDensity (finrank ℤ L) := by
  have : FiniteDimensional ℚ V := L.finiteDimensional
  let e : Isometry L (L.transport (finBasisOfFinrankEq ℚ V L.finrank_carrier.symm).equivFun) :=
    L.transportIsometry _
  exact e.density_eq ▸ le_iSup₂_of_le (L.transport _) (e.isPosDef_iff.mp hL) le_rfl

/-- **A lattice solving the lattice packing problem has a density at least that of every positive
definite lattice of the same rank.** -/
lemma IsDensestLattice.density_le (hL : L.IsDensestLattice) (hM : M.IsPosDef)
    (hrank : finrank ℤ M = finrank ℤ L) : M.density ≤ L.density :=
  (ENNReal.ofReal_le_ofReal_iff L.density_nonneg).mp <|
    (density_le_latticePackingDensity hM).trans (hrank ▸ hL.2)

end TauCeti.IntegralLattice
