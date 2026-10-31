import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EllipticPointKernel
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrder
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.Basic
import TauCeti.Algebra.CentralSimple.TensorProduct
import TauCeti.Analysis.Complex.UpperHalfPlane.DiscCoordinate

/-!
# The stabilizers of the points of the Shimura curve `X_H`

Let `B` be a quaternion algebra over `ℚ`, a central simple `ℚ`-algebra of dimension `4`, with a
`ℚ`-algebra map `ι : B → M₂(ℝ)`, let `O` be an order of `B` and let `Γ_H^+ ⊆ N_{B^×}(O)` be the
group of the geometric component `Γ_H^+ \ ℍ` of the Shimura curve `X_H` through the points `[τ, 1]`
(`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EllipticPoint`). An elliptic point of `X_H` (LMFDB
`shimcurve.elliptic_points`) is a point with a nontrivial stabilizer group, which can be of order
`2`, `3`, `4` or `6`. The group by which `Γ_H^+` acts on `ℍ` is `Γ_H^+ / ℚ^×`, the rational scalars
being the elements acting trivially (`Subalgebra.forall_smul_eq_self_iff_mem_normalizerRatUnits`),
and the stabilizer group of the point given by `τ ∈ ℍ` is the image `Γ_τ` in `Γ_H^+ / ℚ^×` of the
stabilizer of `τ` in `Γ_H^+`. This file proves that `Γ_τ` is cyclic of order `1`, `2`, `3`, `4` or
`6`, so that the elliptic points `Subalgebra.shimuraEllipticPoints` are exactly the points whose
stabilizer group has order `2`, `3`, `4` or `6`.

The proof is arithmetic (the discreteness of `Γ_H^+ / ℚ^×` in `PSL₂(ℝ)` is proved, from the same
lattice argument, in `LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.FuchsianGroup`):

* `ι` extends to an injective `ℝ`-algebra map from the simple ring `ℝ ⊗ B`, so a `ℤ`-basis of the
  lattice `O`, which is a `ℚ`-basis of `B`, is sent by `ι` to an `ℝ`-basis of `M₂(ℝ)`.
* For `γ` in the normalizer of `O`, conjugation by `γ` preserves `O`, so its trace on `M₂(ℝ)`,
  which is `tr(ι γ) tr(ι γ⁻¹) = tr(ι γ)² / det(ι γ)`, is an integer `t`.
* If `γ` fixes `τ`, the automorphy factor `j = c τ + d` of `ι(γ) = (a b; c d)` and its conjugate
  are the eigenvalues of `ι(γ)`, so `ζ = j / conj j` satisfies `(ζ + 1)² = t ζ`, and
  `0 ≤ t ≤ 4` since `tr(ι γ)² - 4 det(ι γ) = -4 (im j)²`. Hence `ζ⁴ = 1` or `ζ⁶ = 1`.
* `γ ↦ ζ` is a character of the stabilizer of `τ` whose kernel is the group of the rational
  scalars, so `Γ_τ` is isomorphic to a finite subgroup of `ℂ^×` all of whose elements satisfy
  `ζ⁴ = 1` or `ζ⁶ = 1`, a cyclic group of order `1`, `2`, `3`, `4` or `6`.

This is the bound on the torsion of `K^× / ℚ^×` for the imaginary quadratic field `K = ℚ(γ)`:
`ζ` is the image of the root of unity `γ / γ̄` of `K` under the embedding `K → ℂ` sending `γ` to the
eigenvalue `j`. The other geometric components of `X_H`, which need the finite adelic points `B̂^×`,
are not covered; their groups `B^×_+ ∩ b K_H b⁻¹` consist of positive-norm elements of the
normalizers of the orders `B ∩ b Ô b⁻¹`, to which the arithmetic part of the argument applies.

## Main definitions

* `Subalgebra.realBasis`: the `ℝ`-basis of `M₂(ℝ)` given by a `ℤ`-basis of an order.
* `Subalgebra.shimuraStabilizerRotation`: the character `γ ↦ j(γ, τ) / conj j(γ, τ)` of the
  stabilizer of `τ` in `Γ_H^+`.
* `Subalgebra.shimuraStabilizer` (LMFDB `shimcurve.elliptic_points`): the stabilizer group `Γ_τ`
  of the point of `X_H` given by `τ`.
* `Subalgebra.shimuraStabilizerOrder` (LMFDB `shimcurve.elliptic_points`): the order of the
  stabilizer group of a point of `Γ_H^+ \ ℍ`, independent of the representative.
* `Subalgebra.shimuraStabilizerEquivRange`: the isomorphism of `Γ_τ` with the image of the
  character.

## Main results

* `AlgHom.linearIndependent_real_comp_basis`: a `ℚ`-algebra map `ι : B → M₂(ℝ)` from a central
  simple `ℚ`-algebra sends a `ℚ`-basis of `B` to `ℝ`-linearly independent matrices.
* `Subalgebra.exists_trace_sq_eq_intCast_mul_det`: `tr(ι γ)² / det(ι γ)` is an integer for every
  `γ` in the normalizer of an order.
* `Subalgebra.denom_div_conj_pow_four_eq_one_or_pow_six_eq_one`: for every positive-norm element of
  the normalizer of an order fixing `τ`, `j / conj j` is a root of unity of order dividing `4` or
  `6`.
* `Subalgebra.shimuraStabilizerRotation_pow_four_eq_one_or_pow_six_eq_one`: the character takes
  values in the roots of unity of order dividing `4` or `6`.
* `Subalgebra.shimuraStabilizerRotation_eq_one_iff`: its kernel is the group of the rational
  scalars.
* `Subalgebra.isCyclic_shimuraStabilizer`: the stabilizer group is cyclic.
* `Subalgebra.natCard_shimuraStabilizer_mem` (LMFDB `shimcurve.elliptic_points`): it has order `1`,
  `2`, `3`, `4` or `6`, in particular it is finite.
* `Subalgebra.shimuraStabilizerOrder_mem` (LMFDB `shimcurve.elliptic_points`): the same for the
  points of `Γ_H^+ \ ℍ`.
* `Subalgebra.mem_shimuraEllipticPoints_iff_shimuraStabilizerOrder_mem` (LMFDB
  `shimcurve.elliptic_points`): the elliptic points are the points whose stabilizer group has order
  `2`, `3`, `4` or `6`.
-/

open Algebra ComplexConjugate Matrix Module MulAction TensorProduct UpperHalfPlane

namespace Matrix

variable {R : Type*} [CommRing R]

lemma stdBasis_repr_apply {m n : Type*} [Fintype m] [Finite n] (M : Matrix m n R) (i : m) (j : n) :
    (stdBasis R m n).repr M (i, j) = M i j := by
  simp [stdBasis]

lemma trace_mulLeftRight_fin_two (A C : Matrix (Fin 2) (Fin 2) R) :
    LinearMap.trace R _ (LinearMap.mulLeftRight R (A, C)) = A.trace * C.trace := by
  rw [LinearMap.trace_eq_matrix_trace R (stdBasis R (Fin 2) (Fin 2))]
  simp only [Matrix.trace, diag, Fintype.sum_prod_type, LinearMap.toMatrix_apply,
    stdBasis_eq_single, LinearMap.mulLeftRight_apply, stdBasis_repr_apply]
  simp only [single, mul_apply, of_apply, Fin.sum_univ_two, true_and, zero_ne_one, false_and,
    ↓reduceIte, one_ne_zero]
  ring1

lemma trace_mul_det_fin_two_of_mul_eq_one {K : Type*} [Field K] {A C : Matrix (Fin 2) (Fin 2) K}
    (h : A * C = 1) : C.trace * A.det = A.trace := by
  rw [← inv_eq_right_inv h, inv_def, trace_smul, adjugate_fin_two, trace_fin_two, trace_fin_two]
  simp only [Ring.inverse_eq_inv', of_apply, cons_val_zero, cons_val_one, smul_eq_mul]
  field_simp [(isUnit_det_of_right_inverse h).ne_zero]
  ring1

end Matrix

namespace UpperHalfPlane

variable {g : GL (Fin 2) ℝ} {τ : ℍ}

variable (g τ) in
lemma conj_denom_ne_zero : conj (denom g τ) ≠ 0 :=
  (map_ne_zero _).mpr (denom_ne_zero g τ)

lemma gl_smul_eq_self_quadratic_conj (hg : 0 < g.val.det) (h : g • τ = τ) :
    (g 1 0 * (conj ↑τ * conj ↑τ) + (g 1 1 - g 0 0) * conj ↑τ + -g 0 1 : ℂ) = 0 := by
  simpa using congrArg conj ((gl_smul_eq_self_iff_quadratic hg).mp h)

lemma gl_c_mul_add_conj_of_smul_eq_self (hg : 0 < g.val.det) (h : g • τ = τ) :
    (g 1 0 : ℂ) * (τ + conj ↑τ) = g 0 0 - g 1 1 :=
  mul_left_cancel₀ (coe_sub_conj_ne_zero τ τ) <| by
    linear_combination (gl_smul_eq_self_iff_quadratic hg).mp h - gl_smul_eq_self_quadratic_conj hg h

lemma gl_c_mul_mul_conj_of_smul_eq_self (hg : 0 < g.val.det) (h : g • τ = τ) :
    (g 1 0 : ℂ) * (τ * conj ↑τ) = -g 0 1 :=
  mul_left_cancel₀ (coe_sub_conj_ne_zero τ τ) <| by
    linear_combination conj ↑τ * (gl_smul_eq_self_iff_quadratic hg).mp h -
      ↑τ * gl_smul_eq_self_quadratic_conj hg h

lemma denom_add_conj_of_smul_eq_self (hg : 0 < g.val.det) (h : g • τ = τ) :
    denom g τ + conj (denom g τ) = g.val.trace := by
  simp only [denom, trace_fin_two, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_add]
  linear_combination gl_c_mul_add_conj_of_smul_eq_self hg h

lemma denom_mul_conj_of_smul_eq_self (hg : 0 < g.val.det) (h : g • τ = τ) :
    denom g τ * conj (denom g τ) = g.val.det := by
  simp only [denom, det_fin_two, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_sub,
    Complex.ofReal_mul]
  linear_combination (g 1 0 : ℂ) * gl_c_mul_mul_conj_of_smul_eq_self hg h +
    (g 1 1 : ℂ) * gl_c_mul_add_conj_of_smul_eq_self hg h

lemma trace_sq_sub_four_mul_det_of_smul_eq_self (hg : 0 < g.val.det) (h : g • τ = τ) :
    g.val.trace ^ 2 - 4 * g.val.det = -4 * (denom g τ).im ^ 2 := by
  have hs : denom g τ - conj (denom g τ) = 2 * (denom g τ).im * Complex.I := by
    rw [Complex.sub_conj]
    push_cast
    ring1
  have hc : ((g.val.trace ^ 2 - 4 * g.val.det : ℝ) : ℂ) = ((-4 * (denom g τ).im ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [← denom_add_conj_of_smul_eq_self hg h, ← denom_mul_conj_of_smul_eq_self hg h]
    linear_combination (denom g τ - conj (denom g τ) + 2 * (denom g τ).im * Complex.I) * hs +
      4 * (denom g τ).im ^ 2 * Complex.I_sq
  exact_mod_cast hc

lemma gl_mem_center_iff_of_smul_eq_self (hg : 0 < g.val.det) (h : g • τ = τ) :
    g ∈ Subgroup.center (GL (Fin 2) ℝ) ↔ g 1 0 = 0 := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ by_contra fun hgc ↦
    (isElliptic_of_exists_smul_eq_self hg hgc ⟨τ, h⟩).c_ne_zero hc⟩
  rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc with ⟨r, hr⟩
  rw [← hr]
  simp

end UpperHalfPlane

lemma Complex.pow_four_eq_one_or_pow_six_eq_one_of_add_one_sq_eq {ζ : ℂ} {n : ℤ} (h0 : 0 ≤ n)
    (h4 : n ≤ 4) (h : (ζ + 1) ^ 2 = n * ζ) : ζ ^ 4 = 1 ∨ ζ ^ 6 = 1 := by
  interval_cases n
  · have hζ : ζ + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| by simpa using h
    exact Or.inl <| by linear_combination (ζ - 1) * (ζ ^ 2 + 1) * hζ
  · exact Or.inr <| by linear_combination (ζ - 1) * (ζ ^ 3 + 1) * h
  · exact Or.inl <| by linear_combination (ζ ^ 2 - 1) * h
  · exact Or.inr <| by linear_combination (ζ + 1) * (ζ ^ 3 - 1) * h
  · have hζ : ζ - 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| by linear_combination h
    exact Or.inl <| by linear_combination (ζ ^ 3 + ζ ^ 2 + ζ + 1) * hζ

lemma IsCyclic.natCard_mem_of_forall_pow_four_eq_one_or_pow_six_eq_one {G : Type*} [Group G]
    [IsCyclic G] [Finite G] (h : ∀ g : G, g ^ 4 = 1 ∨ g ^ 6 = 1) :
    Nat.card G ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rcases exists_ofOrder_eq_natCard (α := G) with ⟨g, hg⟩
  have hdvd : Nat.card G ∣ 4 ∨ Nat.card G ∣ 6 :=
    hg ▸ (h g).imp orderOf_dvd_of_pow_eq_one orderOf_dvd_of_pow_eq_one
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hle : Nat.card G ≤ 6 :=
    hdvd.elim (fun h ↦ (Nat.le_of_dvd (by norm_num) h).trans (by norm_num))
      (Nat.le_of_dvd (by norm_num))
  interval_cases Nat.card G <;> simp_all

namespace AlgHom

variable {B : Type*} [Ring B] [Algebra ℚ B] [IsCentral ℚ B] [IsSimpleRing B]

/-- **A `ℚ`-algebra map `ι : B → M₂(ℝ)` from a central simple `ℚ`-algebra `B` sends a `ℚ`-basis of
`B` to `ℝ`-linearly independent matrices**: `ι` extends to an `ℝ`-algebra map from `ℝ ⊗ B`, which
is a simple ring (Tau Ceti's `IsSimpleRing.tensorProduct_of_isCentral_right`), so it is injective
on `ℝ ⊗ B`, of which the elements `1 ⊗ bₖ` form an `ℝ`-basis. -/
lemma linearIndependent_real_comp_basis (ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) {κ : Type*}
    (b : Basis κ ℚ B) : LinearIndependent ℝ fun k ↦ ι (b k) := by
  let ιR : ℝ ⊗[ℚ] B →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := lift (ofId ℝ _) ι fun r x ↦ by
    rw [ofId_apply]
    exact commute_algebraMap_left r (ι x)
  have h : ιR.toLinearMap ∘ basis ℝ b = fun k ↦ ι (b k) := funext fun k ↦ by
    simp [ιR]
  exact h ▸ (basis ℝ b).linearIndependent.map' ιR.toLinearMap
    (LinearMap.ker_eq_bot.mpr ιR.toRingHom.injective)

end AlgHom

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] {O : Subalgebra ℤ B} {μ : B}
  {H : Subgroup (O.EnhancedGroup μ)} {ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ} {τ : ℍ} {u : Bˣ}
  (γ : O.shimuraGammaPlus μ H ι) (δ : stabilizer (O.shimuraGammaPlus μ H ι) τ)
  (x : orbitRel.Quotient (O.shimuraGammaPlus μ H ι) ℍ)

lemma zero_lt_det_normalizerToGL : 0 < (O.normalizerToGL ι γ).val.det :=
  (mem_glpos _).mp (Subgroup.mem_inf.mp γ.2).2

lemma normalizerToGL_smul : O.normalizerToGL ι γ • τ = γ • τ :=
  rfl

variable (μ H ι τ) in
/-- The **rotation character** of the stabilizer of a point `τ` of `ℍ` in `Γ_H^+`: an element `γ`
fixing `τ`, with `ι(γ) = (a b; c d)`, is sent to `j / conj j` for its automorphy factor
`j = j(ι γ, τ) = c τ + d`. The eigenvalues of `ι(γ)` are `j` and `conj j`, and the value is the
inverse `j / conj j = j² / det ι(γ)` of the derivative of `z ↦ γ • z` at its fixed point `τ`. -/
noncomputable def shimuraStabilizerRotation : stabilizer (O.shimuraGammaPlus μ H ι) τ →* ℂˣ where
  toFun γ := Units.mk0 (denom (O.normalizerToGL ι γ) τ / conj (denom (O.normalizerToGL ι γ) τ))
    (div_ne_zero (denom_ne_zero _ τ) (conj_denom_ne_zero _ τ))
  map_one' := Units.ext <| by
    simp
  map_mul' γ δ := Units.ext <| by
    have hδ : O.normalizerToGL ι δ • τ = τ := δ.2
    have hσ : σ (O.normalizerToGL ι δ) = ContinuousAlgEquiv.refl ℝ ℂ :=
      ite_eq_left (zero_lt_det_normalizerToGL _)
    simp only [Subgroup.coe_mul, map_mul, denom_cocycle_σ, hδ, hσ]
    simp [mul_div_mul_comm]

variable (μ H ι τ) in
/-- The **stabilizer group** (LMFDB `shimcurve.elliptic_points`) `Γ_τ` of the point of the Shimura
curve `X_H` given by `τ ∈ ℍ`, on its geometric component `Γ_H^+ \ ℍ`: the image of the stabilizer of
`τ` in `Γ_H^+` under the quotient map `Γ_H^+ → Γ_H^+ / ℚ^×`. It is the stabilizer of `τ` in the
group `Γ_H^+ / ℚ^×` by which `Γ_H^+` acts on `ℍ`, the rational scalars being, for `B` central
simple, the elements of `Γ_H^+` acting trivially. -/
noncomputable def shimuraStabilizer : Subgroup (O.shimuraGammaPlus μ H ι ⧸
    O.normalizerRatUnits.subgroupOf (O.shimuraGammaPlus μ H ι)) :=
  ((QuotientGroup.mk' _).comp (stabilizer (O.shimuraGammaPlus μ H ι) τ).subtype).range

lemma shimuraStabilizer_ne_bot_iff : O.shimuraStabilizer μ H ι τ ≠ ⊥ ↔
    ∃ γ : O.shimuraGammaPlus μ H ι, γ • τ = τ ∧ (γ : O.unitsNormalizer) ∉ O.normalizerRatUnits := by
  rw [Ne, shimuraStabilizer, MonoidHom.range_eq_bot_iff]
  simp [DFunLike.ext_iff, Subgroup.mem_subgroupOf]

lemma shimuraStabilizer_eq_map : O.shimuraStabilizer μ H ι τ =
    (stabilizer (O.shimuraGammaPlus μ H ι) τ).map (QuotientGroup.mk' _) := by
  rw [shimuraStabilizer, MonoidHom.range_comp, Subgroup.range_subtype]

lemma natCard_shimuraStabilizer_smul :
    Nat.card (O.shimuraStabilizer μ H ι (γ • τ)) = Nat.card (O.shimuraStabilizer μ H ι τ) := by
  rw [shimuraStabilizer_eq_map, shimuraStabilizer_eq_map, stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.map_map]
  have h : (QuotientGroup.mk' (O.normalizerRatUnits.subgroupOf (O.shimuraGammaPlus μ H ι))).comp
      (MulAut.conj γ).toMonoidHom = (MulAut.conj (QuotientGroup.mk' _ γ)).toMonoidHom.comp
      (QuotientGroup.mk' _) := by
    ext x
    simp
  rw [h, ← Subgroup.map_map]
  exact Subgroup.card_map_of_injective (MulAut.conj _).injective

variable (μ H ι) in
/-- The **order of the stabilizer group** (LMFDB `shimcurve.elliptic_points`) of a point of the
geometric component `Γ_H^+ \ ℍ` of the Shimura curve `X_H`: the order `Nat.card` of the stabilizer
group `Γ_τ` of any representative `τ` of the orbit, which does not depend on the representative,
the stabilizer groups of the points of an orbit being conjugate. It would be `0` for an infinite
stabilizer, which does not happen for an order of a quaternion algebra over `ℚ`
(`Subalgebra.shimuraStabilizerOrder_mem`). -/
noncomputable def shimuraStabilizerOrder : orbitRel.Quotient (O.shimuraGammaPlus μ H ι) ℍ → ℕ :=
  Quotient.lift (fun τ ↦ Nat.card (O.shimuraStabilizer μ H ι τ)) fun _ _ ⟨γ, hγ⟩ ↦
    hγ ▸ natCard_shimuraStabilizer_smul γ

variable [IsCentral ℚ B] [IsSimpleRing B]

section RealBasis

variable {κ : Type*} [Fintype κ] (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder)
  (b : Basis κ ℤ (toSubmodule O)) (k : κ)

variable (ι) in
/-- The **`ℝ`-basis `ι(x₁), …, ι(x₄)` of `M₂(ℝ)`** given by a `ℤ`-basis `x₁, …, x₄` of an order `O`
of a quaternion algebra `B` over `ℚ`, for a `ℚ`-algebra map `ι : B → M₂(ℝ)`: the `ℤ`-basis is a
`ℚ`-basis of `B` (`Module.Basis.extendOfIsLattice`), sent by `ι` to `ℝ`-linearly independent
matrices (`AlgHom.linearIndependent_real_comp_basis`), so that `O` is a lattice in
`B ⊗ ℝ ≅ M₂(ℝ)`. -/
noncomputable def realBasis : Basis κ ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  haveI : Submodule.IsLattice ℚ (toSubmodule O) := hO
  basisOfLinearIndependentOfCardEqFinrank' _
    (ι.linearIndependent_real_comp_basis (b.extendOfIsLattice ℚ)) <| by
      rw [← finrank_eq_card_basis (b.extendOfIsLattice ℚ), hB, finrank_matrix]
      simp

lemma realBasis_apply : O.realBasis ι hB hO b k = ι (b k) := by
  have : Submodule.IsLattice ℚ (toSubmodule O) := hO
  simp only [realBasis, coe_basisOfLinearIndependentOfCardEqFinrank']
  exact congrArg ι (b.extendOfIsLattice_apply ℚ k)

variable (ι) in
lemma realBasis_repr_apply (m : toSubmodule O) :
    (O.realBasis ι hB hO b).repr (ι m) k = b.repr m k := by
  have h : ι m = ∑ j, (b.repr m j : ℝ) • O.realBasis ι hB hO b j := by
    conv_lhs => rw [← b.sum_repr m]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Submodule.coe_smul, map_zsmul, realBasis_apply, Int.cast_smul_eq_zsmul]
  rw [h, Basis.repr_sum_self]

variable (ι) in
lemma realBasis_repr_mulLeftRight (hu : u ∈ O.unitsNormalizer) (j : κ) :
    (O.realBasis ι hB hO b).repr (ι u * O.realBasis ι hB hO b j * ι ↑u⁻¹) k =
      b.repr ⟨u * b j * ↑u⁻¹, conj_mem_of_mem_unitsNormalizer hu (b j).2⟩ k := by
  rw [← realBasis_repr_apply ι hB hO b, realBasis_apply]
  simp

end RealBasis

variable (ι) in
lemma exists_trace_mulLeftRight_eq_intCast (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder)
    (hu : u ∈ O.unitsNormalizer) :
    ∃ n : ℤ, LinearMap.trace ℝ _ (LinearMap.mulLeftRight ℝ (ι u, ι ↑u⁻¹)) = n := by
  have : Submodule.IsLattice ℚ (toSubmodule O) := hO
  let b : Basis (Free.ChooseBasisIndex ℤ (toSubmodule O)) ℤ (toSubmodule O) :=
    Free.chooseBasis ℤ (toSubmodule O)
  refine ⟨∑ k, b.repr ⟨u * b k * ↑u⁻¹, conj_mem_of_mem_unitsNormalizer hu (b k).2⟩ k, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℝ (O.realBasis ι hB hO b), Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [diag_apply, LinearMap.toMatrix_apply, LinearMap.mulLeftRight_apply,
    realBasis_repr_mulLeftRight ι hB hO b k hu]

variable (ι) in
/-- **`tr(ι γ)² / det(ι γ)` is an integer** for every element `γ` of the normalizer `N_{B^×}(O)` of
an order `O` of a quaternion algebra `B` over `ℚ` and every `ℚ`-algebra map `ι : B → M₂(ℝ)`: it is
the trace `tr(ι γ) tr(ι γ⁻¹)` of the conjugation by `ι(γ)` on `M₂(ℝ)`, whose matrix in the basis
`ι(x₁), …, ι(x₄)` given by a `ℤ`-basis `x₁, …, x₄` of `O` is integral, since conjugation by `γ`
preserves `O`. -/
lemma exists_trace_sq_eq_intCast_mul_det (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder)
    (hu : u ∈ O.unitsNormalizer) : ∃ n : ℤ, (ι u).trace ^ 2 = n * (ι u).det := by
  rcases exists_trace_mulLeftRight_eq_intCast ι hB hO hu with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [← hn, trace_mulLeftRight_fin_two, mul_assoc, trace_mul_det_fin_two_of_mul_eq_one, sq]
  rw [← map_mul, Units.mul_inv, map_one]

/-- **The automorphy factor of a positive-norm element of the normalizer of an order fixing `τ`
gives a root of unity of order dividing `4` or `6`**, for an order `O` of a quaternion algebra `B`
over `ℚ`: if `g = ι(v)`, for `v` in the normalizer `N_{B^×}(O)`, has positive determinant and
fixes `τ`, then for `ζ = j / conj j`, `j = j(g, τ)`, the integer `t = tr(g)² / det(g)` satisfies
`(ζ + 1)² = t ζ` and `0 ≤ t ≤ 4`. This applies to the elements of any subgroup of positive-norm
elements of `N_{B^×}(O)`, such as `Γ_H^+`. -/
lemma denom_div_conj_pow_four_eq_one_or_pow_six_eq_one (hB : finrank ℚ B = 4)
    (hO : O.IsQuaternionOrder) {v : O.unitsNormalizer} (hg : 0 < (O.normalizerToGL ι v).val.det)
    (hfix : O.normalizerToGL ι v • τ = τ) :
    (denom (O.normalizerToGL ι v) τ / conj (denom (O.normalizerToGL ι v) τ)) ^ 4 = 1 ∨
      (denom (O.normalizerToGL ι v) τ / conj (denom (O.normalizerToGL ι v) τ)) ^ 6 = 1 := by
  rcases exists_trace_sq_eq_intCast_mul_det ι hB hO v.2 with ⟨n, hn⟩
  have hn' : (O.normalizerToGL ι v).val.trace ^ 2 = n * (O.normalizerToGL ι v).val.det := hn
  generalize O.normalizerToGL ι v = g at hn' hg hfix ⊢
  have h0 : 0 ≤ n := by
    have h : (0 : ℝ) ≤ n * g.val.det := hn' ▸ sq_nonneg _
    exact_mod_cast nonneg_of_mul_nonneg_left h hg
  have h4 : n ≤ 4 := by
    have h : (n : ℝ) * g.val.det ≤ 4 * g.val.det := by
      nlinarith [trace_sq_sub_four_mul_det_of_smul_eq_self hg hfix]
    exact_mod_cast le_of_mul_le_mul_right h hg
  have hζ : (denom g τ / conj (denom g τ) + 1) ^ 2 = n * (denom g τ / conj (denom g τ)) := by
    have h : ((g.val.trace ^ 2 : ℝ) : ℂ) = ((n * g.val.det : ℝ) : ℂ) := congrArg _ hn'
    push_cast at h
    rw [← denom_add_conj_of_smul_eq_self hg hfix, ← denom_mul_conj_of_smul_eq_self hg hfix] at h
    field_simp
    linear_combination h
  exact Complex.pow_four_eq_one_or_pow_six_eq_one_of_add_one_sq_eq h0 h4 hζ

/-- **The rotation character takes values in the roots of unity of order dividing `4` or `6`**, for
an order `O` of a quaternion algebra `B` over `ℚ`. -/
lemma shimuraStabilizerRotation_pow_four_eq_one_or_pow_six_eq_one (hB : finrank ℚ B = 4)
    (hO : O.IsQuaternionOrder) : O.shimuraStabilizerRotation μ H ι τ δ ^ 4 = 1 ∨
    O.shimuraStabilizerRotation μ H ι τ δ ^ 6 = 1 := by
  refine (denom_div_conj_pow_four_eq_one_or_pow_six_eq_one hB hO (zero_lt_det_normalizerToGL _)
    δ.2).imp (fun h ↦ Units.ext ?_) (fun h ↦ Units.ext ?_) <;>
  simpa [shimuraStabilizerRotation] using h

/-- **The kernel of the rotation character is the group of the rational scalars** of the stabilizer
of `τ`: `j / conj j = 1` exactly when `c = 0`, which for a matrix fixing `τ` means that it is
scalar. -/
lemma shimuraStabilizerRotation_eq_one_iff : O.shimuraStabilizerRotation μ H ι τ δ = 1 ↔
    ((δ : O.shimuraGammaPlus μ H ι) : O.unitsNormalizer) ∈ O.normalizerRatUnits := by
  rw [← forall_smul_eq_self_iff_mem_normalizerRatUnits]
  simp only [← normalizerToGL_smul]
  rw [forall_smul_eq_self_iff_mem_center,
    gl_mem_center_iff_of_smul_eq_self (zero_lt_det_normalizerToGL _) δ.2, Units.ext_iff]
  simp only [shimuraStabilizerRotation, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0,
    Units.val_one]
  rw [div_eq_one_iff_eq (conj_denom_ne_zero _ τ), eq_comm, Complex.conj_eq_iff_im]
  simp [denom, τ.im_ne_zero]

lemma ker_mk'_comp_subtype_stabilizer :
    ((QuotientGroup.mk' (O.normalizerRatUnits.subgroupOf (O.shimuraGammaPlus μ H ι))).comp
      (stabilizer (O.shimuraGammaPlus μ H ι) τ).subtype).ker =
      (O.shimuraStabilizerRotation μ H ι τ).ker := by
  ext γ
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, shimuraStabilizerRotation_eq_one_iff]
  simp [Subgroup.mem_subgroupOf]

variable (μ H ι τ) in
/-- The isomorphism of the stabilizer group `Γ_τ` of `τ` with the image of the rotation character,
for `B` central simple: both are the quotient of the stabilizer of `τ` in `Γ_H^+` by its rational
scalars, the kernel of the character. -/
noncomputable def shimuraStabilizerEquivRange :
    O.shimuraStabilizer μ H ι τ ≃* (O.shimuraStabilizerRotation μ H ι τ).range :=
  (QuotientGroup.quotientKerEquivRange _).symm.trans <|
    (QuotientGroup.quotientMulEquivOfEq ker_mk'_comp_subtype_stabilizer).trans <|
      QuotientGroup.quotientKerEquivRange _

lemma range_shimuraStabilizerRotation_le (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    (O.shimuraStabilizerRotation μ H ι τ).range ≤ rootsOfUnity 12 ℂ := by
  rintro _ ⟨γ, rfl⟩
  rw [mem_rootsOfUnity]
  rcases shimuraStabilizerRotation_pow_four_eq_one_or_pow_six_eq_one γ hB hO with h | h <;>
  exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one h).trans (by norm_num))

lemma finite_range_shimuraStabilizerRotation (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    Finite (O.shimuraStabilizerRotation μ H ι τ).range :=
  Finite.of_injective _ (Subgroup.inclusion_injective (range_shimuraStabilizerRotation_le hB hO))

lemma isCyclic_range_shimuraStabilizerRotation (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    IsCyclic (O.shimuraStabilizerRotation μ H ι τ).range :=
  have : Finite (O.shimuraStabilizerRotation μ H ι τ).range :=
    finite_range_shimuraStabilizerRotation hB hO
  isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp (Subgroup.subtype _))
    (Units.val_injective.comp Subtype.val_injective)

/-- **The stabilizer group of a point of the Shimura curve `X_H` is cyclic**, for an order `O` of a
quaternion algebra `B` over `ℚ`: it is isomorphic to a finite subgroup of `ℂ^×`. -/
lemma isCyclic_shimuraStabilizer (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    IsCyclic (O.shimuraStabilizer μ H ι τ) :=
  have : IsCyclic (O.shimuraStabilizerRotation μ H ι τ).range :=
    isCyclic_range_shimuraStabilizerRotation hB hO
  isCyclic_of_surjective (O.shimuraStabilizerEquivRange μ H ι τ).symm.toMonoidHom
    (O.shimuraStabilizerEquivRange μ H ι τ).symm.surjective

/-- **The stabilizer group of a point of the Shimura curve `X_H` has order `1`, `2`, `3`, `4` or
`6`** (LMFDB `shimcurve.elliptic_points`), for an order `O` of a quaternion algebra `B` over `ℚ`
and any `ℚ`-algebra map `ι : B → M₂(ℝ)`; in particular it is finite. -/
lemma natCard_shimuraStabilizer_mem (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    Nat.card (O.shimuraStabilizer μ H ι τ) ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  have : Finite (O.shimuraStabilizerRotation μ H ι τ).range :=
    finite_range_shimuraStabilizerRotation hB hO
  have : IsCyclic (O.shimuraStabilizerRotation μ H ι τ).range :=
    isCyclic_range_shimuraStabilizerRotation hB hO
  rw [Nat.card_congr (O.shimuraStabilizerEquivRange μ H ι τ).toEquiv]
  refine IsCyclic.natCard_mem_of_forall_pow_four_eq_one_or_pow_six_eq_one ?_
  rintro ⟨_, γ, rfl⟩
  exact (shimuraStabilizerRotation_pow_four_eq_one_or_pow_six_eq_one γ hB hO).imp Subtype.ext
    Subtype.ext

variable (τ) in
lemma quotientMk_mem_shimuraEllipticPoints_iff_natCard_mem (hB : finrank ℚ B = 4)
    (hO : O.IsQuaternionOrder) :
    (Quotient.mk _ τ : orbitRel.Quotient (O.shimuraGammaPlus μ H ι) ℍ) ∈
    O.shimuraEllipticPoints μ H ι ↔ Nat.card (O.shimuraStabilizer μ H ι τ) ∈
    ({2, 3, 4, 6} : Finset ℕ) := by
  have h : Nat.card (O.shimuraStabilizer μ H ι τ) ∈ ({1, 2, 3, 4, 6} : Finset ℕ) :=
    natCard_shimuraStabilizer_mem hB hO
  rw [quotientMk_mem_shimuraEllipticPoints_iff, ← shimuraStabilizer_ne_bot_iff, Ne,
    ← Subgroup.card_eq_one]
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  omega

/-- **The stabilizer group of a point of the Shimura curve `X_H` has order `1`, `2`, `3`, `4` or
`6`** (LMFDB `shimcurve.elliptic_points`), for a point `x` of the geometric component
`Γ_H^+ \ ℍ`, an order `O` of a quaternion algebra `B` over `ℚ` and any `ℚ`-algebra map
`ι : B → M₂(ℝ)`. -/
lemma shimuraStabilizerOrder_mem (hB : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    O.shimuraStabilizerOrder μ H ι x ∈ ({1, 2, 3, 4, 6} : Finset ℕ) :=
  Quotient.inductionOn x fun _ ↦ natCard_shimuraStabilizer_mem hB hO

/-- **The elliptic points of the Shimura curve `X_H` are the points whose stabilizer group has order
`2`, `3`, `4` or `6`** (LMFDB `shimcurve.elliptic_points`), on its geometric component
`Γ_H^+ \ ℍ`, for an order `O` of a quaternion algebra `B` over `ℚ`: a point is elliptic exactly
when its stabilizer group is nontrivial, and the stabilizer group has order `1`, `2`, `3`, `4` or
`6`. -/
lemma mem_shimuraEllipticPoints_iff_shimuraStabilizerOrder_mem (hB : finrank ℚ B = 4)
    (hO : O.IsQuaternionOrder) : x ∈ O.shimuraEllipticPoints μ H ι ↔
    O.shimuraStabilizerOrder μ H ι x ∈ ({2, 3, 4, 6} : Finset ℕ) :=
  Quotient.inductionOn x fun τ ↦ quotientMk_mem_shimuraEllipticPoints_iff_natCard_mem τ hB hO

end Subalgebra
