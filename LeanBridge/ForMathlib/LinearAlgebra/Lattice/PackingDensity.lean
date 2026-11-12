import LeanBridge.ForMathlib.LinearAlgebra.Lattice.Density
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# The density of a lattice packing

The density of a positive definite integral lattice `L` of rank `n` (LMFDB `lattice.density`) is
the density of the lattice-centred sphere packing in `ℝⁿ`: realize `L` in `ℝⁿ` and place a ball of
radius `ρ`, half the length of a shortest nonzero vector, at each lattice point. The density of the
packing is the limit, as `R → ∞`, of the proportion of the ball `B(0, R)` covered by the balls
`B(v, ρ)`, `v ∈ L`. This file proves that the limit exists and is the density
`Δ = V_n ρⁿ / √(det G)` of `TauCeti.IntegralLattice.density`, which is the volume of a ball of
radius `ρ` divided by the covolume of `L`
(`TauCeti.IntegralLattice.density_eq_volume_div_covolume`). Hence the density of `L` is also the
density `EuclideanSpace.packingDensity` of its packing, an upper limit by definition. A positive
definite lattice has a realization in `ℝⁿ` (Tau Ceti's
`TauCeti.IntegralLattice.IsPosDef.exists_realization`), so this applies to every positive definite
lattice of positive rank. As its packing is a sphere packing, the density of a lattice is at most
the sphere packing density, and so is the lattice packing density. The file also proves the two
formulas of the knowl for the volume `V_n` of the unit ball, `π^{n/2} / (n/2)!` for even `n` and
`2ⁿ π^{(n-1)/2} ((n-1)/2)! / n!` for odd `n`.

The proof holds for any lattice `Λ` of a Euclidean space `E` of dimension `n ≥ 1` and any radius
`r` for which the balls `B(v, r)`, `v ∈ Λ`, are disjoint. The balls centred at the `N(R - r)`
points of `Λ` in `B̄(0, R - r)` lie in `B(0, R)`, and the part of the packing inside `B(0, R)` lies
in the balls centred at the `N(R + r)` points of `Λ` in `B̄(0, R + r)`. Mathlib counts the points of
a lattice in large balls: `N(R) / Rⁿ` tends to `vol(B(0, 1)) / covol(Λ)`
(`ZLattice.covolume.tendsto_card_le_div'`). As `vol(B(0, R)) = Rⁿ vol(B(0, 1))`, both bounds of the
proportion tend to `vol(B(0, r)) / covol(Λ)`.

## Main results

* `EuclideanSpace.unitBallVolume_two_mul` (LMFDB `lattice.density`): `V_{2k} = π^k / k!`.
* `EuclideanSpace.unitBallVolume_two_mul_add_one` (LMFDB `lattice.density`):
  `V_{2k+1} = 2^{2k+1} π^k k! / (2k+1)!`.
* `ZLattice.tendsto_card_closedBall_inter_div_pow`: the number of points of a lattice `Λ` in the
  ball `B̄(0, R)`, divided by `Rⁿ`, tends to `vol(B(0, 1)) / covol(Λ)`.
* `ZLattice.tendsto_volume_iUnion_ball_inter_ball_div`: the proportion of `B(0, R)` covered by
  disjoint balls of radius `r` centred at the points of `Λ` tends to `vol(B(0, r)) / covol(Λ)`.
* `TauCeti.IntegralLattice.tendsto_volume_iUnion_ball_inter_ball_div` (LMFDB `lattice.density`):
  the proportion of `B(0, R)` covered by the packing of a positive definite lattice tends to its
  density.
* `TauCeti.IntegralLattice.packingDensity_range_eq_density` (LMFDB `lattice.density`): the density
  of a positive definite lattice is the density of its sphere packing.
* `TauCeti.IntegralLattice.density_le_spherePackingDensity` (LMFDB `lattice.density`): it is at most
  the sphere packing density.
* `TauCeti.IntegralLattice.latticePackingDensity_le_spherePackingDensity` (LMFDB
  `lattice.density`): the lattice packing density is at most the sphere packing density.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §1.2.
-/

open Filter Metric MeasureTheory Module Set Topology

open scoped ENNReal InnerProductSpace Real

namespace EuclideanSpace

variable (k : ℕ)

/-- **`V_{2k} = π^k / k!`** (LMFDB `lattice.density`): the knowl's formula for the volume of the
unit ball in even dimension. -/
lemma unitBallVolume_two_mul : unitBallVolume (2 * k) = π ^ k / k.factorial := by
  have h : ((2 * k : ℕ) : ℝ) / 2 + 1 = k + 1 := by
    push_cast
    ring1
  rw [unitBallVolume, h, Real.Gamma_nat_eq_factorial, pow_mul, Real.sq_sqrt Real.pi_pos.le]

/-- **`V_{2k+1} = 2^{2k+1} π^k k! / (2k+1)!`** (LMFDB `lattice.density`): the knowl's formula for
the volume of the unit ball in odd dimension. -/
lemma unitBallVolume_two_mul_add_one : unitBallVolume (2 * k + 1) =
    2 ^ (2 * k + 1) * π ^ k * k.factorial / (2 * k + 1).factorial := by
  have h₁ : ((2 * k + 1 : ℕ) : ℝ) / 2 + 1 = k + 1 + 1 / 2 := by
    push_cast
    ring1
  have h₂ : ((2 * k + 1).factorial : ℝ) = (2 * k + 1).doubleFactorial * (2 ^ k * k.factorial) := by
    rw [Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [unitBallVolume, h₁, Real.Gamma_nat_add_one_add_half, h₂, pow_succ, pow_mul,
    Real.sq_sqrt Real.pi_pos.le]
  field_simp
  ring1

end EuclideanSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Λ : Submodule ℤ E} [DiscreteTopology Λ] {r t : ℝ} (R : ℝ)

variable (Λ t) in
lemma finite_closedBall_inter : (closedBall (0 : E) t ∩ Λ).Finite := by
  refine finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discreteTopology

variable [Nontrivial E] in
lemma setOf_norm_pow_le_pow (ht : 0 ≤ t) :
    {x ∈ (univ : Set E) | ‖x‖ ^ finrank ℝ E ≤ t ^ finrank ℝ E} = closedBall 0 t := by
  ext x
  rw [mem_closedBall_zero_iff, mem_ofPred_eq,
    pow_le_pow_iff_left₀ (norm_nonneg x) ht finrank_pos.ne']
  exact and_iff_right (mem_univ x)

variable [MeasurableSpace E] [BorelSpace E]

lemma volume_iUnion_ball_inter_ball_le :
    volume ((⋃ x ∈ (Λ : Set E), ball x r) ∩ ball 0 R) ≤
      Nat.card (closedBall (0 : E) (R + r) ∩ Λ : Set E) * volume (ball (0 : E) r) := by
  have hfin := finite_closedBall_inter Λ (R + r)
  refine (measure_mono fun y hy ↦ ?_).trans
    ((measure_biUnion_finset_le hfin.toFinset fun x ↦ ball x r).trans ?_)
  · rcases hy with ⟨hy, hyR⟩
    rcases mem_iUnion₂.mp hy with ⟨x, hx, hxy⟩
    refine mem_iUnion₂.mpr ⟨x, hfin.mem_toFinset.mpr ⟨?_, hx⟩, hxy⟩
    rw [mem_ball_zero_iff] at hyR
    rw [mem_ball, dist_eq_norm] at hxy
    rw [mem_closedBall_zero_iff]
    linarith [norm_le_norm_add_norm_sub' x y, norm_sub_rev x y]
  · rw [Finset.sum_congr rfl fun x _ ↦ Measure.addHaar_ball_center volume x r, Finset.sum_const,
      nsmul_eq_mul, Nat.card_coe_set_eq, ncard_eq_toFinset_card _ hfin]

lemma card_mul_volume_ball_le (hΛ : (Λ : Set E).Pairwise fun x y ↦ 2 * r ≤ dist x y) :
    Nat.card (closedBall (0 : E) (R - r) ∩ Λ : Set E) * volume (ball (0 : E) r) ≤
      volume ((⋃ x ∈ (Λ : Set E), ball x r) ∩ ball 0 R) := by
  have hfin := finite_closedBall_inter Λ (R - r)
  rw [Nat.card_coe_set_eq, ncard_eq_toFinset_card _ hfin, ← nsmul_eq_mul, ← Finset.sum_const,
    ← Finset.sum_congr rfl fun x _ ↦ Measure.addHaar_ball_center volume x r,
    ← measure_biUnion_finset (fun x hx y hy hxy ↦ ball_disjoint_ball (by
      linarith [hΛ (hfin.mem_toFinset.mp hx).2 (hfin.mem_toFinset.mp hy).2 hxy]))
      fun _ _ ↦ measurableSet_ball]
  refine measure_mono fun y hy ↦ ?_
  rcases mem_iUnion₂.mp hy with ⟨x, hx, hxy⟩
  rcases hfin.mem_toFinset.mp hx with ⟨hxR, hx⟩
  refine ⟨mem_iUnion₂.mpr ⟨x, hx, hxy⟩, ?_⟩
  rw [mem_closedBall_zero_iff] at hxR
  rw [mem_ball, dist_eq_norm] at hxy
  rw [mem_ball_zero_iff]
  linarith [norm_le_norm_add_norm_sub' y x]

lemma measureReal_ball_pos (ht : 0 < t) : 0 < volume.real (ball (0 : E) t) :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 ht).ne' measure_ball_lt_top.ne

variable [Nontrivial E]

lemma measureReal_ball_zero (ht : 0 ≤ t) :
    volume.real (ball (0 : E) t) = t ^ finrank ℝ E * volume.real (ball (0 : E) 1) := by
  rw [measureReal_def, Measure.addHaar_ball volume 0 ht, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ht _), measureReal_def]

variable [IsZLattice ℝ Λ]

variable (Λ) in
/-- **The number of points of a lattice `Λ` in the ball `B̄(0, R)`, divided by `Rⁿ`, tends to
`vol(B(0, 1)) / covol(Λ)`.** -/
lemma tendsto_card_closedBall_inter_div_pow :
    Tendsto (fun t : ℝ ↦ (Nat.card (closedBall (0 : E) t ∩ Λ : Set E) : ℝ) / t ^ finrank ℝ E)
      atTop (𝓝 (volume.real (ball (0 : E) 1) / covolume Λ)) := by
  have h₁ := setOf_norm_pow_le_pow (E := E) zero_le_one
  rw [one_pow] at h₁
  have h := (covolume.tendsto_card_le_div' Λ (X := univ) (F := fun x ↦ ‖x‖ ^ finrank ℝ E)
    (fun _ _ _ _ ↦ mem_univ _) (fun x c hc ↦ by rw [norm_smul, Real.norm_of_nonneg hc, mul_pow])
    (h₁ ▸ isBounded_closedBall) (h₁ ▸ measurableSet_closedBall)
    (by rw [h₁, frontier_closedBall _ one_ne_zero, Measure.addHaar_sphere])).comp
      (tendsto_pow_atTop (finrank_pos (R := ℝ) (M := E)).ne')
  rw [h₁, Measure.addHaar_real_closedBall_eq_addHaar_real_ball] at h
  refine h.congr' ((eventually_ge_atTop 0).mono fun t ht ↦ ?_)
  rw [Function.comp_apply, setOf_norm_pow_le_pow ht]

lemma tendsto_card_mul_measureReal_ball_div {s : ℝ → ℝ} (hs : Tendsto s atTop atTop)
    (hsR : Tendsto (fun R ↦ s R / R) atTop (𝓝 1)) :
    Tendsto (fun R ↦ Nat.card (closedBall (0 : E) (s R) ∩ Λ : Set E) *
      volume.real (ball (0 : E) r) / volume.real (ball (0 : E) R)) atTop
        (𝓝 (volume.real (ball (0 : E) r) / covolume Λ)) := by
  have h₁ : (0 : ℝ) < volume.real (ball (0 : E) 1) := measureReal_ball_pos one_pos
  have h₂ : volume.real (ball (0 : E) 1) / covolume Λ *
      (volume.real (ball (0 : E) r) / volume.real (ball (0 : E) 1)) =
        volume.real (ball (0 : E) r) / covolume Λ := by
    field_simp
  have h := (((tendsto_card_closedBall_inter_div_pow Λ).comp hs).mul (hsR.pow (finrank ℝ E))).mul
    (tendsto_const_nhds (x := volume.real (ball (0 : E) r) / volume.real (ball (0 : E) 1)))
  rw [one_pow, mul_one, h₂] at h
  refine h.congr' ((hs.eventually_gt_atTop 0).mp ((eventually_gt_atTop 0).mono fun R hR hs₀ ↦ ?_))
  dsimp only [Function.comp_apply]
  rw [measureReal_ball_zero hR.le, div_pow]
  field_simp

lemma tendsto_add_div_self (c : ℝ) : Tendsto (fun R ↦ (R + c) / R) atTop (𝓝 1) := by
  have h := tendsto_const_nhds (x := (1 : ℝ)).add (tendsto_const_nhds (x := c).div_atTop tendsto_id)
  rw [add_zero] at h
  refine h.congr' ((eventually_gt_atTop 0).mono fun R hR ↦ ?_)
  dsimp only [id]
  rw [add_div, div_self hR.ne']

/-- **The proportion of the ball `B(0, R)` covered by disjoint balls of radius `r` centred at the
points of a lattice `Λ` tends to `vol(B(0, r)) / covol(Λ)`**, as `R → ∞`. -/
lemma tendsto_volume_iUnion_ball_inter_ball_div
    (hΛ : (Λ : Set E).Pairwise fun x y ↦ 2 * r ≤ dist x y) :
    Tendsto (fun R ↦ volume ((⋃ x ∈ (Λ : Set E), ball x r) ∩ ball 0 R) / volume (ball (0 : E) R))
      atTop (𝓝 (ENNReal.ofReal (volume.real (ball (0 : E) r) / covolume Λ))) := by
  have hU (R : ℝ) : volume ((⋃ x ∈ (Λ : Set E), ball x r) ∩ ball 0 R) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hlow := tendsto_card_mul_measureReal_ball_div (Λ := Λ) (r := r) (s := fun R ↦ R - r)
    (by simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-r) tendsto_id)
    (by simpa [sub_eq_add_neg] using tendsto_add_div_self (-r))
  have hup := tendsto_card_mul_measureReal_ball_div (Λ := Λ) (r := r) (s := fun R ↦ R + r)
    (tendsto_atTop_add_const_right _ r tendsto_id) (tendsto_add_div_self r)
  have h : Tendsto (fun R ↦ volume.real ((⋃ x ∈ (Λ : Set E), ball x r) ∩ ball 0 R) /
      volume.real (ball (0 : E) R)) atTop (𝓝 (volume.real (ball (0 : E) r) / covolume Λ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
      (.of_forall fun R ↦ div_le_div_of_nonneg_right ?_ measureReal_nonneg)
      (.of_forall fun R ↦ div_le_div_of_nonneg_right ?_ measureReal_nonneg)
    · have h := ENNReal.toReal_mono (hU R) (card_mul_volume_ball_le R hΛ)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
    · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        measure_ball_lt_top.ne) (volume_iUnion_ball_inter_ball_le (Λ := Λ) (r := r) R)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  refine (ENNReal.tendsto_ofReal h).congr' ((eventually_gt_atTop 0).mono fun R hR ↦ ?_)
  rw [ENNReal.ofReal_div_of_pos (measureReal_ball_pos hR), ofReal_measureReal (hU R),
    ofReal_measureReal measure_ball_lt_top.ne]

end ZLattice

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

variable [Nontrivial L] in
lemma packingRadius_pos (hL : L.IsPosDef) : 0 < L.packingRadius :=
  div_pos (Real.sqrt_pos.mpr (by exact_mod_cast hL.minimum_pos)) two_pos

section Realization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {φ : L →ₗ[ℤ] E}

lemma pairwise_two_mul_packingRadius_le_dist (hL : L.IsPosDef)
    (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y) :
    (range φ).Pairwise fun x y ↦ 2 * L.packingRadius ≤ dist x y := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  have h : (L.minimum : ℝ) ≤ ‖φ (a - b)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hφ, ← integralNorm_apply]
    exact_mod_cast hL.isPosSemidef.minimum_le_integralNorm
      (sub_ne_zero.mpr fun h ↦ hab (congrArg φ h))
  rw [dist_eq_norm, ← map_sub, packingRadius, mul_div_cancel₀ _ two_ne_zero]
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (norm_nonneg _))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable [Nontrivial L] in
/-- **The proportion of the ball `B(0, R)` covered by the sphere packing of a positive definite
lattice `L` tends to the density of `L`** (LMFDB `lattice.density`), as `R → ∞`: the packing of the
balls of radius `ρ`, half the length of a shortest nonzero vector, centred at the points of a
realization of `L` in Euclidean space. -/
lemma tendsto_volume_iUnion_ball_inter_ball_div (hL : L.IsPosDef)
    (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y) (hspan : Submodule.span ℝ (range φ) = ⊤) :
    Tendsto (fun R ↦ volume ((⋃ x ∈ range φ, ball x L.packingRadius) ∩ ball 0 R) /
      volume (ball (0 : E) R)) atTop (𝓝 (ENNReal.ofReal L.density)) := by
  have : L.IsNondegenerate := ⟨(L.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hL).2⟩
  have : DiscreteTopology (LinearMap.range φ) := discreteTopology_range hφ
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  rcases exists_ne (0 : L) with ⟨x, hx⟩
  have : Nontrivial E := nontrivial_of_ne (φ x) 0 (by simpa using (injective_of_inner_eq hφ).ne hx)
  rw [density_eq_volume_div_covolume hL hφ hspan, ← LinearMap.coe_range]
  refine ZLattice.tendsto_volume_iUnion_ball_inter_ball_div ?_
  rw [LinearMap.coe_range]
  exact pairwise_two_mul_packingRadius_le_dist hL hφ

end Realization

variable [Nontrivial L] in
/-- **The density of a positive definite lattice `L` is the density of its sphere packing** (LMFDB
`lattice.density`): the upper limit, here a limit, of the proportion of large balls covered by the
balls of radius `ρ` centred at the points of a realization of `L` in `ℝⁿ`. -/
lemma packingDensity_range_eq_density (hL : L.IsPosDef) {n : ℕ}
    {φ : L →ₗ[ℤ] EuclideanSpace ℝ (Fin n)} (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y)
    (hspan : Submodule.span ℝ (range φ) = ⊤) :
    EuclideanSpace.packingDensity (range φ) L.packingRadius = ENNReal.ofReal L.density :=
  (tendsto_volume_iUnion_ball_inter_ball_div hL hφ hspan).limsup_eq

variable [Nontrivial L] in
/-- **The density of a positive definite lattice is at most the sphere packing density in its
dimension** (LMFDB `lattice.density`): its packing is a sphere packing. -/
lemma density_le_spherePackingDensity (hL : L.IsPosDef) :
    ENNReal.ofReal L.density ≤ EuclideanSpace.spherePackingDensity (finrank ℤ L) := by
  rcases hL.exists_realization with ⟨φ, hφ, hspan⟩
  rw [← packingDensity_range_eq_density hL hφ hspan]
  exact le_iSup₂_of_le (range φ) L.packingRadius
    (le_iSup_of_le (pairwise_two_mul_packingRadius_le_dist hL hφ) le_rfl)

/-- **The lattice packing density is at most the sphere packing density** in positive dimension
(LMFDB `lattice.density`): lattice packings are sphere packings. -/
lemma latticePackingDensity_le_spherePackingDensity {n : ℕ} (hn : n ≠ 0) :
    latticePackingDensity n ≤ EuclideanSpace.spherePackingDensity n := by
  refine iSup₂_le fun M hM ↦ ?_
  have h : finrank ℤ M = n := M.finrank_carrier.trans (finrank_fin_fun ℚ)
  have : Nontrivial M := nontrivial_of_finrank_pos ((Nat.pos_of_ne_zero hn).trans_eq h.symm)
  exact (density_le_spherePackingDensity hM).trans_eq
    (congrArg EuclideanSpace.spherePackingDensity h)

end TauCeti.IntegralLattice
