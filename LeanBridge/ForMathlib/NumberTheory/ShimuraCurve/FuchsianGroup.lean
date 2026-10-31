import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EllipticPointStabilizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action

/-!
# The Fuchsian group of the Shimura curve `X_H`

Let `B` be a quaternion algebra over `ℚ` with a `ℚ`-algebra map `ι : B → M₂(ℝ)`, `O` an order of
`B` and `Γ_H^+ ⊆ N_{B^×}(O)` the group of the geometric component `Γ_H^+ \ ℍ` of the Shimura curve
`X_H` through the points `[τ, 1]` (`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EllipticPoint`).
Normalizing `ι(γ)` by `√det ι(γ)` sends `Γ_H^+` to `SL₂(ℝ)`, hence to `PSL₂(ℝ)`, with kernel the
rational scalars: its image is the group `Γ_H^+ / ℚ^×` acting on `ℍ`, the Fuchsian group of this
component of `X_H`. This file proves that it is discrete in `PSL₂(ℝ)`, and that the elliptic points
of `X_H` (LMFDB `shimcurve.elliptic_points`, `Subalgebra.shimuraEllipticPoints`) are the elliptic
orbits of this Fuchsian group in the sense of Tau Ceti (`Subgroup.ellipticOrbits`).

Discreteness: a `ℤ`-basis `x₁, …, x₄` of `O` gives an `ℝ`-basis `ι(x₁), …, ι(x₄)` of `M₂(ℝ)`
(`Subalgebra.realBasis`), in which conjugation by `ι(γ)`, `γ ∈ Γ_H^+`, has an integral matrix since
it preserves `O`. The matrix of conjugation by `s ∈ SL₂(ℝ)` in this basis depends continuously on
`s` and only on the class of `s` in `PSL₂(ℝ)`, and it is the identity matrix at `s = 1`. In the
open neighbourhood of `1` where its entries are within `1/2` of those of the identity, an element of
the image of `Γ_H^+` has an integral matrix, hence the identity matrix, hence is central, that is,
trivial in `PSL₂(ℝ)`.

## Main definitions

* `Subalgebra.shimuraGammaPlusToGLPos`: the homomorphism `Γ_H^+ → GL₂(ℝ)^+` given by `ι`.
* `Subalgebra.shimuraGammaPlusToPSL`: the homomorphism `Γ_H^+ → PSL₂(ℝ)`, `γ ↦ ι(γ) / √det ι(γ)`.
* `Subalgebra.shimuraFuchsianGroup`: its image, the Fuchsian group `Γ_H^+ / ℚ^×` of `X_H`.
* `Subalgebra.shimuraGammaPlusModScalarsEquiv`: the isomorphism of `Γ_H^+ / ℚ^×` with it.

## Main results

* `Subalgebra.shimuraGammaPlusToPSL_smul`: `Γ_H^+` acts on `ℍ` through its image in `PSL₂(ℝ)`.
* `Subalgebra.ker_shimuraGammaPlusToPSL`: the kernel is the group of the rational scalars.
* `Subalgebra.discreteTopology_shimuraFuchsianGroup`: the image of `Γ_H^+` in `PSL₂(ℝ)` is
  discrete, for an order `O` of a quaternion algebra `B` over `ℚ`.
* `Subalgebra.quotientMk_mem_ellipticOrbits_shimuraFuchsianGroup_iff` (LMFDB
  `shimcurve.elliptic_points`): the elliptic orbits of the Fuchsian group are the elliptic points
  of `X_H`.
* `Subalgebra.natCard_stabilizer_shimuraFuchsianGroup_mem` (LMFDB `shimcurve.elliptic_points`): the
  point stabilizers of the Fuchsian group have order `1`, `2`, `3`, `4` or `6`.
-/

open Algebra Matrix Module MulAction TauCeti UpperHalfPlane

open scoped MatrixGroups

lemma glPosToSL2R_mul_mul_inv (g : GL(2, ℝ)⁺) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ((glPosToSL2R g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * M * ((glPosToSL2R g)⁻¹ : SL(2, ℝ)) =
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * M * ((g⁻¹ : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) := by
  have hdet : ((g⁻¹ : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val * (g : GL (Fin 2) ℝ).det.val = 1 := by
    rw [← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, map_one,
      Units.val_one]
  have hc :
      (√((g⁻¹ : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val)⁻¹ * (√(g : GL (Fin 2) ℝ).det.val)⁻¹ = 1 := by
    rw [← mul_inv, ← Real.sqrt_mul (g⁻¹).2.le, hdet, Real.sqrt_one, inv_one]
  rw [← map_inv, glPosToSL2R_coe_matrix, glPosToSL2R_coe_matrix]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hc, one_smul]

namespace Matrix.SpecialLinearGroup

variable {s v z : SL(2, ℝ)}

lemma mem_center_of_forall_basis_mul_mul_inv_eq {κ : Type*}
    (bR : Basis κ ℝ (Matrix (Fin 2) (Fin 2) ℝ)) (h : ∀ j, (s : Matrix (Fin 2) (Fin 2) ℝ) * bR j *
      (↑s⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) = bR j) : s ∈ Subgroup.center SL(2, ℝ) := by
  have hconj : LinearMap.mulLeftRight ℝ
      ((s : Matrix (Fin 2) (Fin 2) ℝ), (↑s⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) = LinearMap.id :=
    bR.ext h
  refine Subgroup.mem_center_iff.mpr fun t ↦ Subtype.ext ?_
  have ht : (s : Matrix (Fin 2) (Fin 2) ℝ) * t * (↑s⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) = t :=
    LinearMap.congr_fun hconj t
  rw [coe_mul, coe_mul]
  conv_lhs => rw [← ht]
  rw [mul_assoc, ← coe_mul s⁻¹, inv_mul_cancel, coe_one, mul_one]

lemma mul_mul_inv_of_mem_center (hz : z ∈ Subgroup.center SL(2, ℝ)) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ((v * z : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * M * (↑(v * z)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) =
      (v : Matrix (Fin 2) (Fin 2) ℝ) * M * (↑v⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hcomm : (z : Matrix (Fin 2) (Fin 2) ℝ) * M = M * z := by
    rw [← scalar_eq_self_of_mem_center hz 0]
    exact scalar_commute _ (Commute.all _) M
  rw [DivisionMonoid.mul_inv_rev, coe_mul, coe_mul, mul_assoc (v : Matrix (Fin 2) (Fin 2) ℝ), hcomm,
    mul_assoc, mul_assoc, ← mul_assoc (z : Matrix (Fin 2) (Fin 2) ℝ), ← coe_mul z, mul_inv_cancel,
    coe_one, one_mul, ← mul_assoc]

end Matrix.SpecialLinearGroup

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] {O : Subalgebra ℤ B} {μ : B}
  {H : Subgroup (O.EnhancedGroup μ)} {ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
  (γ : O.shimuraGammaPlus μ H ι) (τ : ℍ)

variable (μ H ι) in
/-- The homomorphism `Γ_H^+ → GL₂(ℝ)^+` given by the `ℚ`-algebra map `ι : B → M₂(ℝ)`, the
elements of `Γ_H^+` having positive norm. -/
noncomputable def shimuraGammaPlusToGLPos : O.shimuraGammaPlus μ H ι →* GL(2, ℝ)⁺ :=
  ((O.normalizerToGL ι).comp (O.shimuraGammaPlus μ H ι).subtype).codRestrict _
    fun γ ↦ (Subgroup.mem_inf.mp γ.2).2

variable (μ H ι) in
/-- The homomorphism `Γ_H^+ → PSL₂(ℝ)`, `γ ↦ ι(γ) / √det ι(γ)`, through which `Γ_H^+` acts on the
upper half-plane. -/
noncomputable def shimuraGammaPlusToPSL : O.shimuraGammaPlus μ H ι →* PSL(2, ℝ) :=
  glPosToPSL2R.comp (O.shimuraGammaPlusToGLPos μ H ι)

variable (μ H ι) in
/-- The **Fuchsian group** of the geometric component `Γ_H^+ \ ℍ` of the Shimura curve `X_H`: the
image of `Γ_H^+` in `PSL₂(ℝ)`, isomorphic to `Γ_H^+ / ℚ^×` for `B` central simple
(`Subalgebra.ker_shimuraGammaPlusToPSL`) and discrete for an order `O` of a quaternion algebra `B`
over `ℚ` (`Subalgebra.discreteTopology_shimuraFuchsianGroup`). -/
noncomputable def shimuraFuchsianGroup : Subgroup PSL(2, ℝ) :=
  (O.shimuraGammaPlusToPSL μ H ι).range

/-- **`Γ_H^+` acts on the upper half-plane through its image in `PSL₂(ℝ)`.** -/
lemma shimuraGammaPlusToPSL_smul : O.shimuraGammaPlusToPSL μ H ι γ • τ = γ • τ :=
  glPosToPSL2R_smul _ τ

variable [IsCentral ℚ B] [IsSimpleRing B]

lemma shimuraGammaPlusToPSL_eq_one_iff :
    O.shimuraGammaPlusToPSL μ H ι γ = 1 ↔ (γ : O.unitsNormalizer) ∈ O.normalizerRatUnits := by
  rw [← forall_smul_eq_self_iff_mem_normalizerRatUnits]
  simp only [← shimuraGammaPlusToPSL_smul]
  exact ⟨fun h τ ↦ by rw [h, one_smul], fun h ↦ eq_of_smul_eq_smul fun τ ↦ by rw [h, one_smul]⟩

/-- **The kernel of `Γ_H^+ → PSL₂(ℝ)` is the group of the rational scalars**, for `B` central
simple over `ℚ`, so that the Fuchsian group of `X_H` is `Γ_H^+ / ℚ^×`. -/
lemma ker_shimuraGammaPlusToPSL : (O.shimuraGammaPlusToPSL μ H ι).ker =
    O.normalizerRatUnits.subgroupOf (O.shimuraGammaPlus μ H ι) := by
  ext γ
  rw [MonoidHom.mem_ker, shimuraGammaPlusToPSL_eq_one_iff, Subgroup.mem_subgroupOf]

/-- **The Fuchsian group of the Shimura curve `X_H` is discrete**: the image of `Γ_H^+` in
`PSL₂(ℝ)` is a discrete subgroup, for an order `O` of a quaternion algebra `B` over `ℚ` and any
`ℚ`-algebra map `ι : B → M₂(ℝ)`. -/
lemma discreteTopology_shimuraFuchsianGroup (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    DiscreteTopology (O.shimuraFuchsianGroup μ H ι) := by
  have : Submodule.IsLattice ℚ (toSubmodule O) := hO
  let b : Basis (Free.ChooseBasisIndex ℤ (toSubmodule O)) ℤ (toSubmodule O) :=
    Free.chooseBasis ℤ (toSubmodule O)
  let bR : Basis (Free.ChooseBasisIndex ℤ (toSubmodule O)) ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
    O.realBasis ι hB hO b
  let Φ : SL(2, ℝ) → Free.ChooseBasisIndex ℤ (toSubmodule O) →
      Free.ChooseBasisIndex ℤ (toSubmodule O) → ℝ :=
    fun s i j ↦
      bR.coord i ((s : Matrix (Fin 2) (Fin 2) ℝ) * bR j * (↑s⁻¹ : Matrix (Fin 2) (Fin 2) ℝ))
  have hinv : Continuous fun s : SL(2, ℝ) ↦ ((s⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) :=
    continuous_subtype_val.comp continuous_inv
  have hΦ : Continuous Φ :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ (bR.coord i).continuous_of_finiteDimensional.comp
      ((continuous_subtype_val.mul continuous_const).mul hinv)
  let V : Set SL(2, ℝ) := Φ ⁻¹' Metric.ball (Φ 1) (1 / 2)
  refine discreteTopology_of_isOpen_singleton_one <| isOpen_induced_iff.mpr
    ⟨(QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) '' V,
      QuotientGroup.isOpenMap_coe V (Metric.isOpen_ball.preimage hΦ), ?_⟩
  ext ⟨x, hx⟩
  refine ⟨fun ⟨v, hv, hvx⟩ ↦ ?_, fun h ↦ ?_⟩
  · rcases hx with ⟨γ, rfl⟩
    let s : SL(2, ℝ) := glPosToSL2R (O.shimuraGammaPlusToGLPos μ H ι γ)
    have hvs : v⁻¹ * s ∈ Subgroup.center SL(2, ℝ) := QuotientGroup.eq.mp hvx
    have hΦs : Φ s = Φ v := by
      ext i j
      simp only [Φ]
      rw [← mul_inv_cancel_left v s, SpecialLinearGroup.mul_mul_inv_of_mem_center hvs]
    have hint (i j) : ∃ n : ℤ, Φ s i j = n := by
      refine ⟨b.repr ⟨_, conj_mem_of_mem_unitsNormalizer (γ : O.unitsNormalizer).2 (b j).2⟩ i, ?_⟩
      rw [← realBasis_repr_mulLeftRight ι hB hO b i (γ : O.unitsNormalizer).2]
      simp only [Φ, s, glPosToSL2R_mul_mul_inv]
      rfl
    have hΦone (i j) : Φ 1 i j = bR.repr (bR j) i := by
      have h1 : ((1 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := rfl
      simp only [Φ, inv_one, h1, one_mul, mul_one, Basis.coord_apply]
    have hone (i j) : ∃ n : ℤ, Φ 1 i j = n := by
      refine ⟨if j = i then 1 else 0, ?_⟩
      rw [hΦone, Basis.repr_self, Finsupp.single_apply]
      push_cast
      rfl
    have hΦ1 : Φ s = Φ 1 := by
      ext i j
      rcases hint i j with ⟨m, hm⟩
      rcases hone i j with ⟨n, hn⟩
      have hd : dist (Φ s i j) (Φ 1 i j) < 1 / 2 := by
        rw [hΦs]
        exact (dist_pi_lt_iff one_half_pos).mp ((dist_pi_lt_iff one_half_pos).mp hv i) j
      rw [hm, hn, Real.dist_eq] at hd
      rw [hm, hn]
      have hmn : |m - n| < 1 := by
        have h1 : |(m : ℝ) - n| < 1 := hd.trans (by norm_num)
        exact_mod_cast h1
      exact_mod_cast sub_eq_zero.mp (Int.abs_lt_one_iff.mp hmn)
    refine Subtype.ext <| (QuotientGroup.eq_one_iff _).mpr <|
      SpecialLinearGroup.mem_center_of_forall_basis_mul_mul_inv_eq bR fun j ↦ bR.ext_elem fun i ↦ ?_
    exact (congrFun (congrFun hΦ1 i) j).trans (hΦone i j)
  · exact ⟨1, Metric.mem_ball_self (by norm_num),
      (QuotientGroup.mk_one _).trans (congrArg Subtype.val h).symm⟩

/-- **The elliptic points of the Shimura curve `X_H` are the elliptic orbits of its Fuchsian group**
(LMFDB `shimcurve.elliptic_points`), in the sense of Tau Ceti's `Subgroup.ellipticOrbits`, for `B`
central simple over `ℚ`: the orbit of `τ` under the group `Γ_H^+ / ℚ^×` of `PSL₂(ℝ)`, discrete for
an order `O` of a quaternion algebra `B` (`Subalgebra.discreteTopology_shimuraFuchsianGroup`), is
elliptic exactly when the orbit of `τ` under `Γ_H^+` is an elliptic point of `X_H`. -/
lemma quotientMk_mem_ellipticOrbits_shimuraFuchsianGroup_iff :
    (Quotient.mk _ τ : orbitRel.Quotient (O.shimuraFuchsianGroup μ H ι) ℍ) ∈
      (O.shimuraFuchsianGroup μ H ι).ellipticOrbits ↔
      (Quotient.mk _ τ : orbitRel.Quotient (O.shimuraGammaPlus μ H ι) ℍ) ∈
        O.shimuraEllipticPoints μ H ι := by
  rw [Subgroup.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus,
    quotientMk_mem_shimuraEllipticPoints_iff, ← Ne, Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨fun ⟨⟨⟨_, γ, hγ⟩, hq⟩, hq1⟩ ↦ ⟨γ, ?_, fun h ↦ hq1 ?_⟩, fun ⟨γ, hγ, h⟩ ↦ ?_⟩
  · rw [← shimuraGammaPlusToPSL_smul, hγ]
    exact hq
  · ext
    exact hγ.symm.trans ((shimuraGammaPlusToPSL_eq_one_iff γ).mpr h)
  · refine ⟨⟨⟨_, γ, rfl⟩, ?_⟩, fun h1 ↦ h ((shimuraGammaPlusToPSL_eq_one_iff γ).mp ?_)⟩
    · rw [mem_stabilizer_iff, Subgroup.smul_def, shimuraGammaPlusToPSL_smul, hγ]
    · exact congrArg Subtype.val (congrArg Subtype.val h1)

variable (μ H ι) in
/-- The isomorphism of `Γ_H^+ / ℚ^×` with the Fuchsian group of the Shimura curve `X_H`, for `B`
central simple over `ℚ`: the kernel of `Γ_H^+ → PSL₂(ℝ)` is the group of the rational scalars. -/
noncomputable def shimuraGammaPlusModScalarsEquiv : O.shimuraGammaPlus μ H ι ⧸
    O.normalizerRatUnits.subgroupOf (O.shimuraGammaPlus μ H ι) ≃* O.shimuraFuchsianGroup μ H ι :=
  (QuotientGroup.quotientMulEquivOfEq ker_shimuraGammaPlusToPSL.symm).trans
    (QuotientGroup.quotientKerEquivRange _)

lemma map_shimuraStabilizer_shimuraGammaPlusModScalarsEquiv :
    (O.shimuraStabilizer μ H ι τ).map (O.shimuraGammaPlusModScalarsEquiv μ H ι).toMonoidHom =
      stabilizer (O.shimuraFuchsianGroup μ H ι) τ := by
  ext ⟨_, γ, rfl⟩
  rw [shimuraStabilizer_eq_map, Subgroup.map_map, mem_stabilizer_iff, Subgroup.smul_def]
  refine ⟨fun ⟨δ, hδ, h⟩ ↦ ?_, fun h ↦ ⟨γ, (shimuraGammaPlusToPSL_smul γ τ).symm.trans h, rfl⟩⟩
  exact (congrArg (· • τ) (congrArg Subtype.val h)).symm.trans
    ((shimuraGammaPlusToPSL_smul δ τ).trans hδ)

lemma natCard_stabilizer_shimuraFuchsianGroup :
    Nat.card (stabilizer (O.shimuraFuchsianGroup μ H ι) τ) =
      Nat.card (O.shimuraStabilizer μ H ι τ) := by
  rw [← map_shimuraStabilizer_shimuraGammaPlusModScalarsEquiv]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

/-- **The point stabilizers of the Fuchsian group of the Shimura curve `X_H` have order `1`, `2`,
`3`, `4` or `6`** (LMFDB `shimcurve.elliptic_points`), for an order `O` of a quaternion algebra `B`
over `ℚ`: the stabilizer of `τ` in `Γ_H^+ / ℚ^× ⊆ PSL₂(ℝ)` is the stabilizer group of the point of
`X_H` given by `τ`. -/
lemma natCard_stabilizer_shimuraFuchsianGroup_mem (hB : finrank ℚ B = 4)
    (hO : O.IsQuaternionOrder) :
    Nat.card (stabilizer (O.shimuraFuchsianGroup μ H ι) τ) ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rw [natCard_stabilizer_shimuraFuchsianGroup]
  exact natCard_shimuraStabilizer_mem hB hO

end Subalgebra
