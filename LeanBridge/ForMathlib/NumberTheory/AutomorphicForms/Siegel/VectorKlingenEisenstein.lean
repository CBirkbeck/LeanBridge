import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.EisensteinSubspace
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.VectorKlingenBound
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Vector-valued Klingen–Eisenstein series of degree 2

The LMFDB knowl `mf.siegel.subspace.degree.two` decomposes the space `M_{j,k}(Γ₂)` of Siegel modular
forms of degree `2` and weight `ρ_{k,j} = det^k ⊗ Sym^j` on `Γ₂ = Sp(4, ℤ)` as
`S_{j,k}(Γ₂) ⊕ E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`, the last space being that of the Klingen–Eisenstein
series, and says that for `k > 4` and `j > 0` it is isomorphic to the space of cusp forms of weight
`k + j` on `SL(2, ℤ)`. This file constructs these series,
`E(f)(Z) = ∑_{δ ∈ P \ Sp(4, ℤ)} f((δZ)₀₀) ρ_{k,j}(CZ + D)⁻¹ e₁^j`, for a cusp form `f` of weight
`k + j` on `SL(2, ℤ)`, and proves that for even `k > 4` they converge absolutely to Siegel modular
forms of weight `ρ_{k,j}` on `Γ₂`, with `E(f)(diag(τ', it)) → f(τ') e₁^j` as `t → ∞`. So for `j`
even, `f ↦ E(f)` is an isomorphism onto `KE_{j,k}(Γ₂)`, which meets the cusp forms trivially.

The series is summed coordinatewise, through every linear form on the finite-dimensional space
`Sym^j(ℂ²)`, as in `SiegelUpperHalfSpace.IsVectorSiegelEisensteinSeries`. Holomorphy in the three
variables of `Z` follows from Mathlib's term-by-term differentiation theorem
`hasFDerivAt_tsum_of_isPreconnected`, with bounds on the derivatives coming from the Schwarz lemma
`Complex.norm_fderiv_le_div_of_mapsTo_ball`; the limit follows from dominated convergence.

The knowl's isomorphism needs `j` even: for `j` odd, `M_{j,k}(Γ₂) = 0`, the element `-1` of
`Sp(4, ℤ)` acting by `(-1)^j`, while the space of cusp forms of weight `k + j` need not vanish, for
instance for `(k, j) = (5, 7)`. For `k` odd and `j` even both spaces vanish. For `k` odd the terms
of the series depend on the representatives of the cosets, up to a sign, which is why
`KE_{j,k}(Γ₂)` is taken inside `M_{j,k}(Γ₂)`.

Not proved here: that `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`, which needs the
Fourier expansions of Siegel modular forms (not available) to define the Siegel operator on all of
`M_{j,k}(Γ₂)`, and, for `j = 0`, the convergence of the Siegel Eisenstein series (for `j > 0`,
`E_{j,k}(Γ₂) = 0` by `SiegelUpperHalfSpace.siegelEisensteinSubspaceKJ_eq_bot`); that `KE_{j,k}(Γ₂)`
is orthogonal to the cusp forms for the Petersson product (the unfolding of the integral over a
fundamental domain); and the stability of `E_{j,k}(Γ₂)`, `KE_{j,k}(Γ₂)` and `N_{j,k}(Γ₂)` under the
Hecke operators (for `M_{j,k}(Γ₂)` and `S_{j,k}(Γ₂)` it is
`SiegelUpperHalfSpace.heckeOperator_mem_modularFormsKJ` and
`SiegelUpperHalfSpace.heckeOperator_mem_cuspFormsKJ`).

## Main definitions

* `SiegelUpperHalfSpace.dualTsum`: the sum of a family in a finite-dimensional complex vector space.
* `SiegelUpperHalfSpace.vectorKlingenEisenstein` (LMFDB `mf.siegel.klingen_eisenstein_series`,
  `mf.siegel.subspace.degree.two`): the vector-valued Klingen–Eisenstein series `E(f)`.
* `SiegelUpperHalfSpace.vectorKlingenEisensteinLinear`: the linear map `f ↦ E(f)`.
* `SiegelUpperHalfSpace.klingenEisensteinSubspaceKJ` (LMFDB `mf.siegel.subspace.degree.two`): the
  space `KE_{j,k}(Γ₂)`.
* `SiegelUpperHalfSpace.klingenEisensteinEquiv` (LMFDB `mf.siegel.subspace.degree.two`): the
  isomorphism `S_{k+j}(SL(2, ℤ)) ≃ KE_{j,k}(Γ₂)`, for `k > 4` and `j` even.

## Main results

* `SiegelUpperHalfSpace.hasSum_dualTsum`: the sum of a family summable through every linear form.
* `SiegelUpperHalfSpace.differentiableAt_tsum_of_bound`: term-by-term differentiation in several
  complex variables.
* `SiegelUpperHalfSpace.exists_nonneg_bound`: the bound `|f(τ)| ≤ C (Im τ)^(-w / 2)` of a cusp form.
* `SiegelUpperHalfSpace.hasSum_dual_vectorKlingenEisenstein`: `E(f)` converges for `k > 4`.
* `SiegelUpperHalfSpace.slash_vectorKlingenEisenstein`: it is invariant under `Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.isHolomorphic_vectorKlingenEisenstein`: it is holomorphic.
* `SiegelUpperHalfSpace.vectorKlingenEisenstein_mem_modularFormsKJ`: it is a Siegel modular form.
* `SiegelUpperHalfSpace.tendsto_dual_vectorKlingenEisenstein_diagPoint`: its Siegel operator is
  `f e₁^j`.
* `SiegelUpperHalfSpace.vectorKlingenEisensteinLinear_injective`: `f ↦ E(f)` is injective.
* `SiegelUpperHalfSpace.modularFormsKJ_eq_bot_of_odd`: `M_{j,k}(Γ₂) = 0` for `j` odd.
* `SiegelUpperHalfSpace.disjoint_klingenEisensteinSubspaceKJ_cuspFormsKJ`:
  `KE_{j,k}(Γ₂) ∩ S_{j,k}(Γ₂) = 0` for `k > 4`.
-/

open Complex Filter Metric Module TauCeti Topology

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open scoped Manifold MatrixGroups TensorProduct UpperHalfPlane

namespace SiegelUpperHalfSpace

open SymplecticGroup

section DualSum

variable {ι V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] (t : ι → V)

/-- The sum of a family `(tₓ)` in a finite-dimensional complex vector space, coordinatewise in a
basis: the value is the sum as soon as the family is summable through every linear form
(`SiegelUpperHalfSpace.hasSum_dualTsum`). -/
noncomputable def dualTsum : V :=
  ∑ i, (∑' x, (finBasis ℂ V).coord i (t x)) • finBasis ℂ V i

variable {t}

/-- **The sum of a family summable through every linear form**: for every linear form `φ`,
`∑ₓ φ(tₓ) = φ(∑ₓ tₓ)`. -/
lemma hasSum_dualTsum (ht : ∀ φ : Dual ℂ V, Summable fun x ↦ φ (t x)) (φ : Dual ℂ V) :
    HasSum (fun x ↦ φ (t x)) (φ (dualTsum t)) := by
  have h₁ (i : Fin (finrank ℂ V)) :
      HasSum (fun x ↦ (finBasis ℂ V).coord i (t x) * φ (finBasis ℂ V i))
        ((∑' x, (finBasis ℂ V).coord i (t x)) * φ (finBasis ℂ V i)) :=
    (ht _).hasSum.mul_right _
  have h₂ : HasSum (fun x ↦ ∑ i, (finBasis ℂ V).coord i (t x) * φ (finBasis ℂ V i))
      (∑ i, (∑' x, (finBasis ℂ V).coord i (t x)) * φ (finBasis ℂ V i)) :=
    hasSum_sum fun i (_ : i ∈ Finset.univ) ↦ h₁ i
  have e₁ (x : ι) : ∑ i, (finBasis ℂ V).coord i (t x) * φ (finBasis ℂ V i) = φ (t x) := by
    conv_rhs => rw [← (finBasis ℂ V).sum_repr (t x)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp
  have e₂ : ∑ i, (∑' x, (finBasis ℂ V).coord i (t x)) * φ (finBasis ℂ V i) = φ (dualTsum t) := by
    rw [dualTsum, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
  rw [e₂] at h₂
  exact h₂.congr_fun fun x ↦ (e₁ x).symm

end DualSum

/-- **The term-by-term differentiation in several complex variables**: if the holomorphic functions
`Fᵢ` are bounded on the ball of radius `3ε` around `z₀` by a summable family, their sum is complex
differentiable at `z₀`, the bounds on the derivatives on the ball of radius `ε` coming from the
Schwarz lemma. -/
lemma differentiableAt_tsum_of_bound {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ι → E → ℂ} {u : ι → ℝ} (hu : Summable u) {z₀ : E} {ε : ℝ} (hε : 0 < ε)
    (hd : ∀ i, DifferentiableOn ℂ (F i) (ball z₀ (3 * ε)))
    (hb : ∀ i, ∀ z ∈ ball z₀ (3 * ε), ‖F i z‖ ≤ u i) :
    DifferentiableAt ℂ (fun z ↦ ∑' i, F i z) z₀ := by
  have hsub : ball z₀ ε ⊆ ball z₀ (3 * ε) :=
    ball_subset_ball (by linarith)
  have hderiv (i : ι) (z : E) (hz : z ∈ ball z₀ ε) : ‖fderiv ℂ (F i) z‖ ≤ ε⁻¹ * u i := by
    have hball : ball z (2 * ε) ⊆ ball z₀ (3 * ε) := by
      refine ball_subset_ball' ?_
      have h₀ : dist z z₀ < ε := hz
      linarith
    have hu₀ : 0 ≤ u i :=
      (norm_nonneg _).trans (hb i z₀ (mem_ball_self (by linarith)))
    have hm : Set.MapsTo (F i) (ball z (2 * ε)) (closedBall (F i z) (2 * u i)) := fun w hw ↦ by
      rw [mem_closedBall, dist_eq_norm]
      refine (norm_sub_le _ _).trans ?_
      linarith [hb i w (hball hw), hb i z (hball (mem_ball_self (by linarith)))]
    refine (Complex.norm_fderiv_le_div_of_mapsTo_ball ((hd i).mono hball) hm
      (by linarith)).trans_eq ?_
    field_simp
  have hF (i : ι) (z : E) (hz : z ∈ ball z₀ ε) : HasFDerivAt (F i) (fderiv ℂ (F i) z) z :=
    ((hd i).differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasFDerivAt
  have hz₀ : z₀ ∈ ball z₀ ε :=
    mem_ball_self hε
  exact (hasFDerivAt_tsum_of_isPreconnected (hu.mul_left ε⁻¹) isOpen_ball
    (convex_ball z₀ ε).isPreconnected hF hderiv hz₀ (hu.of_norm_bounded fun i ↦ hb i z₀ (hsub hz₀))
    hz₀).differentiableAt

variable {k : ℤ} {j : ℕ} (f : CuspForm 𝒮ℒ (k + j))

lemma cuspForm_apply_smul (g : SL(2, ℤ)) (w : ℍ) :
    f (g • w) = ((g 1 0 : ℂ) * w + (g 1 1 : ℂ)) ^ (k + j) * f w := by
  have h : f (SpecialLinearGroup.mapGL ℝ g • w) =
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) w ^ (k + j) * f w :=
    SlashInvariantForm.slash_action_eqn'' f (MonoidHom.mem_range.mpr ⟨g, rfl⟩) w
  have e : g • w = SpecialLinearGroup.mapGL ℝ g • w :=
    rfl
  rw [e, h]
  simp [UpperHalfPlane.denom]

/-- **A cusp form of weight `w` on `SL(2, ℤ)` is bounded by a multiple of `(Im τ)^(-w / 2)`**, with
a nonnegative constant. -/
lemma exists_nonneg_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((k + j : ℤ) : ℝ) / 2) := by
  rcases CuspFormClass.exists_bound f with ⟨C, hC⟩
  refine ⟨C, ?_, hC⟩
  have h : ‖f UpperHalfPlane.I‖ ≤ C / UpperHalfPlane.I.im ^ (((k + j : ℤ) : ℝ) / 2) :=
    hC UpperHalfPlane.I
  simp only [UpperHalfPlane.I_im, Real.one_rpow, div_one] at h
  exact (norm_nonneg _).trans h

lemma summable_norm_bottomRow_zpow (hk : 4 < k) :
    Summable fun x : KlingenCosetsTwo ↦ ‖bottomRow x.out‖ ^ (-k) := by
  have h₁ : Summable fun x : Fin 2 ⊕ Fin 2 → ℤ ↦ ‖x‖ ^ (((-k : ℤ) : ℝ)) :=
    summable_norm_rpow_int (by
      have hk' : (4 : ℝ) < k := by
        exact_mod_cast hk
      simpa using hk')
  have h₂ : Summable fun x : Fin 2 ⊕ Fin 2 → ℤ ↦ ‖x‖ ^ (-k) :=
    h₁.congr fun x ↦ Real.rpow_intCast _ _
  exact h₂.comp_injective bottomRow_out_injective

variable (Z : SiegelUpperHalfSpace (Fin 2)) (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ)))

lemma summable_dual_vectorKlingenTerm (hk : 4 < k) :
    Summable fun x : KlingenCosetsTwo ↦ φ (vectorKlingenTerm Z k j f x.out) := by
  rcases exists_nonneg_bound f with ⟨C, hC, hf⟩
  refine Summable.of_norm_bounded ((summable_norm_bottomRow_zpow hk).mul_left
    (C * dualBound φ * klingenConst j k Z.val)) fun x ↦ ?_
  exact norm_dual_vectorKlingenTerm_le Z φ x.out hC hf (by linarith)

variable (k j) in
/-- The **vector-valued Klingen–Eisenstein series** of degree `2` and weight `ρ_{k,j}`
(LMFDB `mf.siegel.klingen_eisenstein_series`, `mf.siegel.subspace.degree.two`) of `u : ℍ → ℂ`:
`E(u)(Z) = ∑_{δ ∈ P \ Sp(4, ℤ)} u((δZ)₀₀) ρ_{k,j}(CZ + D)⁻¹ e₁^j`, the sum over the right cosets of
the Klingen parabolic subgroup `P`, with chosen representatives (for `u` of weight `k + j` on
`SL(2, ℤ)` and even `k`, the terms do not depend on them). The sum is taken coordinatewise; it
converges for a cusp form `u` and `k > 4`. -/
noncomputable def vectorKlingenEisenstein (u : ℍ → ℂ) :
    SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ) :=
  fun Z ↦ dualTsum fun x : KlingenCosetsTwo ↦ vectorKlingenTerm Z k j u x.out

/-- **The vector-valued Klingen–Eisenstein series converges** absolutely, for `k > 4`, through every
linear form on `Sym^j(ℂ²)`, by comparison with the lattice sum `∑_{ℓ ∈ ℤ⁴} ‖ℓ‖^(-k)`. -/
lemma hasSum_dual_vectorKlingenEisenstein (hk : 4 < k) : HasSum
    (fun x : KlingenCosetsTwo ↦ φ (vectorKlingenTerm Z k j f x.out))
    (φ (vectorKlingenEisenstein k j f Z)) :=
  hasSum_dualTsum (fun ψ ↦ summable_dual_vectorKlingenTerm f Z ψ hk) φ

/-- **The vector-valued Klingen–Eisenstein series is invariant under `Sp(4, ℤ)`**, for even `k > 4`:
the terms at `βZ` are `ρ_{k,j}(C_β Z + D_β)` times the terms at `Z` of the cosets translated by
`β`. -/
lemma slash_vectorKlingenEisenstein (hk : 4 < k) (hk' : Even k) (β : symplecticGroup (Fin 2) ℤ) :
    slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) β) (vectorKlingenEisenstein k j f) =
      vectorKlingenEisenstein k j f := by
  funext Z
  rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  rw [map_sub, sub_eq_zero, slash_apply]
  let ψ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ)) :=
    φ ∘ₗ rhoKJ k j (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) β) Z)⁻¹
  have h₁ : HasSum _ (ψ (vectorKlingenEisenstein k j f
      (SymplecticGroup.map (Int.castRingHom ℝ) β • Z))) :=
    hasSum_dual_vectorKlingenEisenstein f _ ψ hk
  have h₂ : HasSum _ (φ (vectorKlingenEisenstein k j f Z)) :=
    hasSum_dual_vectorKlingenEisenstein f Z φ hk
  have e (x : KlingenCosetsTwo) :
      ψ (vectorKlingenTerm (SymplecticGroup.map (Int.castRingHom ℝ) β • Z) k j f x.out) =
        φ (vectorKlingenTerm Z k j f (klingenCosetsMul β x).out) := by
    rw [vectorKlingenTerm_smul]
    have e₁ : ψ (rhoKJ k j (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) β) Z)
        (vectorKlingenTerm Z k j f (x.out * β))) =
          φ (vectorKlingenTerm Z k j f (x.out * β)) := by
      simp only [ψ, LinearMap.comp_apply]
      rw [← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply]
    rw [e₁, vectorKlingenTerm_out_mul Z hk' (cuspForm_apply_smul f)]
  exact (h₁.congr_fun fun x ↦ (e x).symm).unique ((Equiv.hasSum_iff (klingenCosetsMul β)).mpr h₂)

variable {u : ℍ → ℂ}

lemma isHolomorphic_topLeft (hu : MDiff u) :
    IsHolomorphic fun τ : SiegelUpperHalfSpace (Fin 2) ↦ u (topLeft τ) := by
  rw [isHolomorphic_iff_differentiableOn]
  have h₀ : DifferentiableOn ℂ (u ∘ UpperHalfPlane.ofComplex) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hu
  have hmaps : Set.MapsTo (fun Z : Fin 2 → Fin 2 → ℂ ↦ symmetrize Z 0 0)
      (symmetrizePreimage (Fin 2)) {z | 0 < z.im} := fun Z hZ ↦
    (topLeft ⟨symmetrize Z, transpose_symmetrize Z, hZ⟩).im_pos
  refine (h₀.comp (differentiableOn_symmetrize_apply 0 0) hmaps).congr fun Z hZ ↦ ?_
  rw [extend_of_mem _ hZ, Function.comp_apply, Function.comp_apply,
    UpperHalfPlane.ofComplex_apply_of_im_pos (hmaps hZ)]
  rfl

lemma rhoKJ_denomGL_inv_apply (g : symplecticGroup (Fin 2) ℝ) (v : Sym[ℂ]^j (Fin 2 → ℂ)) :
    rhoKJ k j (denomGL g Z)⁻¹ v =
      (denom g Z.val).det ^ (-k) • symPowerRep ℂ 2 j (denomGL g Z)⁻¹ v := by
  have e : rhoKJ k j (denomGL g Z)⁻¹ v = ((((denomGL g Z)⁻¹).det ^ k : ℂˣ) : ℂ) •
      symPowerRep ℂ 2 j (denomGL g Z)⁻¹ v :=
    rfl
  rw [e, map_inv, inv_zpow', Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply,
    coe_denomGL]

lemma isHolomorphic_dual_vectorKlingenTerm (hu : MDiff u) (δ : symplecticGroup (Fin 2) ℤ) :
    IsHolomorphic fun τ ↦ φ (vectorKlingenTerm τ k j u δ) := by
  have e : (fun τ ↦ φ (vectorKlingenTerm τ k j u δ)) =
      (fun τ ↦ u (topLeft (SymplecticGroup.map (Int.castRingHom ℝ) δ • τ))) *
        ((fun τ ↦ (denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) τ.val).det ^ (-k)) *
          fun τ ↦ φ (symPowerRep ℂ 2 j
            (denomGL (SymplecticGroup.map (Int.castRingHom ℝ) δ) τ)⁻¹
              (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) := by
    funext τ
    rw [Pi.mul_apply, Pi.mul_apply, vectorKlingenTerm, rhoKJ_denomGL_inv_apply, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
  rw [e]
  exact ((isHolomorphic_topLeft hu).comp_smul _).mul ((isHolomorphic_det_denom_zpow _ (-k)).mul
    (isHolomorphic_symPowerRep_denomGL_inv φ _ _))

private lemma continuousAt_klingenConst {Z₀ : Fin 2 → Fin 2 → ℂ}
    (hZ₀ : Z₀ ∈ symmetrizePreimage (Fin 2)) :
    ContinuousAt (fun Z : Fin 2 → Fin 2 → ℂ ↦ klingenConst j k (symmetrize Z)) Z₀ := by
  have hE (a b : Fin 2) : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ symmetrize Z a b := by
    have e : (fun Z : Fin 2 → Fin 2 → ℂ ↦ symmetrize Z a b) =
        fun Z ↦ (2⁻¹ : ℂ) * (Z a b + Z b a) := by
      funext Z
      rw [symmetrize, Matrix.smul_apply, Matrix.add_apply, transpose_apply, of_apply, of_apply,
        smul_eq_mul]
    rw [e]
    fun_prop
  have hy (a b : Fin 2) : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ (symmetrize Z a b).im :=
    continuous_im.comp (hE a b)
  have hx (a b : Fin 2) : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ (symmetrize Z a b).re :=
    continuous_re.comp (hE a b)
  let Z₁ : SiegelUpperHalfSpace (Fin 2) := ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩
  have hdet : 0 < (symmetrize Z₀ 0 0).im * (symmetrize Z₀ 1 1).im -
      (symmetrize Z₀ 0 1).im * (symmetrize Z₀ 1 0).im :=
    det_im_pos Z₁
  have htr : 0 < (symmetrize Z₀ 0 0).im + (symmetrize Z₀ 1 1).im :=
    add_pos (im_zero_zero_pos Z₁) (im_one_one_pos Z₁)
  have cdet : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ (symmetrize Z 0 0).im * (symmetrize Z 1 1).im -
      (symmetrize Z 0 1).im * (symmetrize Z 1 0).im :=
    ((hy 0 0).mul (hy 1 1)).sub ((hy 0 1).mul (hy 1 0))
  have ctr : Continuous fun Z : Fin 2 → Fin 2 → ℂ ↦ (symmetrize Z 0 0).im + (symmetrize Z 1 1).im :=
    (hy 0 0).add (hy 1 1)
  have hL : ContinuousAt (fun Z : Fin 2 → Fin 2 → ℂ ↦ imLam (symmetrize Z)) Z₀ :=
    (cdet.continuousAt.div ctr.continuousAt htr.ne').sqrt
  have hK : ContinuousAt (fun Z : Fin 2 → Fin 2 → ℂ ↦ imK (symmetrize Z)) Z₀ := by
    refine continuousAt_const.add (ContinuousAt.mul (continuousAt_const.add ?_)
      (ContinuousAt.div ?_ cdet.continuousAt hdet.ne'))
    · exact (((hx 0 0).abs.add (hx 0 1).abs).add (hx 1 1).abs).continuousAt
    · exact (((hy 0 0).abs.add (hy 0 1).abs).add (hy 1 1).abs).continuousAt
  have hL₀ : imLam (symmetrize Z₀) ≠ 0 :=
    (imLam_pos Z₁).ne'
  have hK₀ : imK (symmetrize Z₀) / imLam (symmetrize Z₀) ≠ 0 :=
    (div_pos (imK_pos Z₁) (imLam_pos Z₁)).ne'
  exact (hL.zpow₀ _ (Or.inl hL₀)).mul ((hK.div hL hL₀).zpow₀ _ (Or.inl hK₀))

/-- **The vector-valued Klingen–Eisenstein series is holomorphic**, for a cusp form `f` and `k > 4`:
around each point the terms are bounded by a summable family, locally uniformly. -/
lemma isHolomorphic_vectorKlingenEisenstein (hk : 4 < k) :
    IsHolomorphic (vectorKlingenEisenstein k j f) := by
  intro φ Z₀ hZ₀
  rcases exists_nonneg_bound f with ⟨C, hC, hf⟩
  have hU : ∀ᶠ Z in 𝓝 Z₀, Z ∈ symmetrizePreimage (Fin 2) ∧
      klingenConst j k (symmetrize Z) < klingenConst j k (symmetrize Z₀) + 1 :=
    (isOpen_symmetrizePreimage.eventually_mem hZ₀).and <|
      (continuousAt_klingenConst hZ₀).eventually_lt continuousAt_const (by linarith)
  rcases eventually_nhds_iff_ball.mp hU with ⟨r, hr, hball⟩
  have hd (x : KlingenCosetsTwo) : DifferentiableOn ℂ
      (extend fun τ ↦ φ (vectorKlingenTerm τ k j f x.out)) (ball Z₀ (3 * (r / 3))) := by
    refine (isHolomorphic_iff_differentiableOn.mp
      (isHolomorphic_dual_vectorKlingenTerm φ f.holo' x.out)).mono fun Z hZ ↦ (hball Z ?_).1
    rwa [mul_div_cancel₀ _ three_ne_zero] at hZ
  have hb (x : KlingenCosetsTwo) (Z : Fin 2 → Fin 2 → ℂ) (hZ : Z ∈ ball Z₀ (3 * (r / 3))) :
      ‖extend (fun τ ↦ φ (vectorKlingenTerm τ k j f x.out)) Z‖ ≤
        C * dualBound φ * (klingenConst j k (symmetrize Z₀) + 1) * ‖bottomRow x.out‖ ^ (-k) := by
    have hZ' : Z ∈ ball Z₀ r := by
      rwa [mul_div_cancel₀ _ three_ne_zero] at hZ
    rw [extend_of_mem _ (hball Z hZ').1]
    refine (norm_dual_vectorKlingenTerm_le _ φ x.out hC hf (by linarith)).trans ?_
    gcongr
    · exact mul_nonneg hC (dualBound_nonneg φ)
    · exact (hball Z hZ').2.le
  refine ((differentiableAt_tsum_of_bound ((summable_norm_bottomRow_zpow hk).mul_left _)
    (div_pos hr three_pos) hd hb).congr_of_eventuallyEq ?_).differentiableWithinAt
  refine (isOpen_symmetrizePreimage.eventually_mem hZ₀).mono fun Z hZ ↦ ?_
  rw [extend_of_mem _ hZ, Function.comp_apply]
  rw [← (hasSum_dual_vectorKlingenEisenstein f _ φ hk).tsum_eq]
  exact tsum_congr fun x ↦
    (extend_of_mem (fun τ ↦ φ (vectorKlingenTerm τ k j f x.out)) hZ).symm

/-- **The vector-valued Klingen–Eisenstein series is a Siegel modular form** of weight `ρ_{k,j}` on
`Sp(4, ℤ)`, for a cusp form `f` of weight `k + j` on `SL(2, ℤ)` and even `k > 4`. -/
lemma vectorKlingenEisenstein_mem_modularFormsKJ (hk : 4 < k) (hk' : Even k) :
    vectorKlingenEisenstein k j f ∈ modularFormsKJ k j (SymplecticGroup.integral (Fin 2)) :=
  mem_modularFormsKJ_of_slash_eq k (H := ⊤) (isHolomorphic_vectorKlingenEisenstein f hk)
    fun β _ ↦ slash_vectorKlingenEisenstein f hk hk' β

private lemma zpow_neg_le_zpow_neg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {n : ℤ} (hn : 0 ≤ n) :
    b ^ (-n) ≤ a ^ (-n) := by
  rw [zpow_neg, zpow_neg]
  exact inv_anti₀ (zpow_pos ha n) (zpow_le_zpow_left₀ hn ha.le hab)

variable (τ' : ℍ) (t : Set.Ioi (0 : ℝ)) (δ : symplecticGroup (Fin 2) ℤ)

lemma topLeft_diagPoint : topLeft (diagPoint τ' t) = τ' :=
  UpperHalfPlane.ext rfl

private lemma denom_diagPoint_one_zero :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) (diagPoint τ' t).val 1 0 =
      (δ.1 (.inr 1) (.inl 0) : ℂ) * τ' + (δ.1 (.inr 1) (.inr 0) : ℂ) := by
  simp [denom, diagPoint, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]

private lemma denom_diagPoint_one_one :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) (diagPoint τ' t).val 1 1 =
      (δ.1 (.inr 1) (.inl 1) : ℂ) * ((t : ℝ) * I) + (δ.1 (.inr 1) (.inr 1) : ℂ) := by
  simp [denom, diagPoint, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]

private lemma hermForm_diagPoint : hermForm ((diagPoint τ' t).val.map im)
    (klingenVec (diagPoint τ' t) (SymplecticGroup.map (Int.castRingHom ℝ) δ)) =
      τ'.im * ((δ.1 (.inr 1) (.inl 1) : ℝ) ^ 2 * (t : ℝ) ^ 2 + (δ.1 (.inr 1) (.inr 1) : ℝ) ^ 2) +
        (t : ℝ) * normSq ((δ.1 (.inr 1) (.inl 0) : ℂ) * τ' + (δ.1 (.inr 1) (.inr 0) : ℂ)) := by
  simp only [hermForm, klingenVec, denom_diagPoint_one_zero, denom_diagPoint_one_one]
  simp [diagPoint, normSq_apply]
  ring1

private lemma imLam_diagPoint : imLam (diagPoint τ' t).val =
    √(τ'.im * (t : ℝ) / (τ'.im + (t : ℝ))) := by
  simp [imLam, diagPoint]

/-- The parameter `t = 1` of the points `diag(τ', it)`. -/
private def tOne : Set.Ioi (0 : ℝ) :=
  ⟨1, Set.mem_Ioi.mpr one_pos⟩

private lemma imLam_diagPoint_le (ht : tOne ≤ t) :
    imLam (diagPoint τ' tOne).val ≤ imLam (diagPoint τ' t).val := by
  have ht₁ : (1 : ℝ) ≤ t := ht
  have hy : 0 < τ'.im := τ'.im_pos
  have ht₀ : (0 : ℝ) < t := t.2
  rw [imLam_diagPoint, imLam_diagPoint]
  refine Real.sqrt_le_sqrt ?_
  have e : ((tOne : Set.Ioi (0 : ℝ)) : ℝ) = 1 :=
    rfl
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hy ht₀, mul_nonneg hy.le (sub_nonneg.mpr ht₁)]

private lemma klingenRadius_diagPoint_le (ht : tOne ≤ t) :
    klingenRadius (diagPoint τ' tOne) δ ≤ klingenRadius (diagPoint τ' t) δ := by
  have ht₁ : (1 : ℝ) ≤ t := ht
  have hy : 0 < τ'.im := τ'.im_pos
  refine Real.sqrt_le_sqrt ?_
  rw [hermForm_diagPoint, hermForm_diagPoint]
  have e : ((tOne : Set.Ioi (0 : ℝ)) : ℝ) = 1 :=
    rfl
  rw [e]
  have hN : 0 ≤ normSq ((δ.1 (.inr 1) (.inl 0) : ℂ) * τ' + (δ.1 (.inr 1) (.inr 0) : ℂ)) :=
    normSq_nonneg _
  have h₂ : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by
    nlinarith
  nlinarith [mul_nonneg hy.le (mul_nonneg (sq_nonneg (δ.1 (.inr 1) (.inl 1) : ℝ))
    (sub_nonneg.mpr h₂)), mul_nonneg (sub_nonneg.mpr ht₁) hN]

private lemma le_klingenRadius_diagPoint (ht : tOne ≤ t) :
    √((t : ℝ) * (τ'.im * (δ.1 (.inr 1) (.inl 1) : ℝ) ^ 2 +
      normSq ((δ.1 (.inr 1) (.inl 0) : ℂ) * τ' + (δ.1 (.inr 1) (.inr 0) : ℂ)))) ≤
        klingenRadius (diagPoint τ' t) δ := by
  have ht₁ : (1 : ℝ) ≤ t := ht
  have hy : 0 < τ'.im := τ'.im_pos
  refine Real.sqrt_le_sqrt ?_
  rw [hermForm_diagPoint]
  have h₂ : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
    nlinarith
  nlinarith [mul_nonneg hy.le (mul_nonneg (sq_nonneg (δ.1 (.inr 1) (.inl 1) : ℝ))
    (sub_nonneg.mpr h₂)), mul_nonneg hy.le (sq_nonneg (δ.1 (.inr 1) (.inr 1) : ℝ))]

variable {C : ℝ}

private lemma norm_dual_vectorKlingenTerm_diagPoint_le (hC : 0 ≤ C)
    (hu : ∀ τ : ℍ, ‖u τ‖ ≤ C / τ.im ^ (((k + j : ℤ) : ℝ) / 2)) (ht : tOne ≤ t) :
    ‖φ (vectorKlingenTerm (diagPoint τ' t) k j u δ)‖ ≤
      C * dualBound φ * imLam (diagPoint τ' tOne).val ^ (-(j : ℤ)) *
        klingenRadius (diagPoint τ' t) δ ^ (-k) := by
  refine (norm_dual_vectorKlingenTerm_le_radius _ φ δ hC hu).trans ?_
  have h₁ : imLam (diagPoint τ' t).val ^ (-(j : ℤ)) ≤
      imLam (diagPoint τ' tOne).val ^ (-(j : ℤ)) :=
    zpow_neg_le_zpow_neg (imLam_pos _) (imLam_diagPoint_le τ' t ht) (Int.natCast_nonneg j)
  have h₃ : 0 ≤ klingenRadius (diagPoint τ' t) δ ^ (-k) :=
    zpow_nonneg (klingenRadius_pos _ δ).le _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁
    (mul_nonneg hC (dualBound_nonneg φ))) h₃

private lemma tendsto_dual_vectorKlingenTerm_diagPoint (hk : 4 < k) (hC : 0 ≤ C)
    (hu : ∀ τ : ℍ, ‖u τ‖ ≤ C / τ.im ^ (((k + j : ℤ) : ℝ) / 2))
    (hκ : 0 < τ'.im * (δ.1 (.inr 1) (.inl 1) : ℝ) ^ 2 +
      normSq ((δ.1 (.inr 1) (.inl 0) : ℂ) * τ' + (δ.1 (.inr 1) (.inr 0) : ℂ))) : Tendsto
    (fun t : Set.Ioi (0 : ℝ) ↦ φ (vectorKlingenTerm (diagPoint τ' t) k j u δ)) atTop (𝓝 0) := by
  generalize hκ' : τ'.im * (δ.1 (.inr 1) (.inl 1) : ℝ) ^ 2 +
    normSq ((δ.1 (.inr 1) (.inl 0) : ℂ) * τ' + (δ.1 (.inr 1) (.inr 0) : ℂ)) = κ at hκ
  have hk₀ : 0 < k := by
    linarith
  have ht : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ (t : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have h₁ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ √((t : ℝ) * κ) ^ (-k)) atTop (𝓝 0) :=
    (tendsto_zpow_atTop_zero (by linarith)).comp
      (Real.tendsto_sqrt_atTop.comp (ht.atTop_mul_const hκ))
  have h₂ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ C * dualBound φ *
      imLam (diagPoint τ' tOne).val ^ (-(j : ℤ)) * √((t : ℝ) * κ) ^ (-k)) atTop
      (𝓝 (C * dualBound φ * imLam (diagPoint τ' tOne).val ^ (-(j : ℤ)) * 0)) :=
    h₁.const_mul _
  rw [mul_zero] at h₂
  refine squeeze_zero_norm' ?_ h₂
  filter_upwards [eventually_ge_atTop tOne] with t ht₁
  refine (norm_dual_vectorKlingenTerm_diagPoint_le φ τ' t δ hC hu ht₁).trans ?_
  have hc : 0 ≤ C * dualBound φ * imLam (diagPoint τ' tOne).val ^ (-(j : ℤ)) :=
    mul_nonneg (mul_nonneg hC (dualBound_nonneg φ)) (zpow_nonneg (imLam_pos _).le _)
  have ht₀ : (0 : ℝ) < t := t.2
  refine mul_le_mul_of_nonneg_left (zpow_neg_le_zpow_neg (Real.sqrt_pos.mpr (mul_pos ht₀ hκ)) ?_
    hk₀.le) hc
  rw [← hκ']
  exact le_klingenRadius_diagPoint τ' t δ ht₁

private lemma kappa_pos_of_ne {x : KlingenCosetsTwo} (hx : x ≠ ⟦1⟧) : 0 <
    τ'.im * (x.out.1 (.inr 1) (.inl 1) : ℝ) ^ 2 +
      normSq ((x.out.1 (.inr 1) (.inl 0) : ℂ) * τ' + (x.out.1 (.inr 1) (.inr 0) : ℂ)) := by
  have hy : 0 < τ'.im := τ'.im_pos
  by_contra hκ
  have h₁ : (x.out.1 (.inr 1) (.inl 1) : ℝ) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x.out.1 (.inr 1) (.inl 1) : ℝ),
      normSq_nonneg ((x.out.1 (.inr 1) (.inl 0) : ℂ) * τ' + (x.out.1 (.inr 1) (.inr 0) : ℂ)),
      mul_nonneg hy.le (sq_nonneg (x.out.1 (.inr 1) (.inl 1) : ℝ))]
  have h₂ :
      normSq ((x.out.1 (.inr 1) (.inl 0) : ℂ) * τ' + (x.out.1 (.inr 1) (.inr 0) : ℂ)) = 0 := by
    rw [h₁, mul_zero, zero_add] at hκ
    exact le_antisymm (not_lt.mp hκ) (normSq_nonneg _)
  have h₃ : (x.out.1 (.inr 1) (.inl 0) : ℂ) * τ' + (x.out.1 (.inr 1) (.inr 0) : ℂ) = 0 :=
    normSq_eq_zero.mp h₂
  have h₄ : (x.out.1 (.inr 1) (.inl 0) : ℝ) * τ'.im = 0 := by
    simpa using congrArg im h₃
  have h₅ : x.out.1 (.inr 1) (.inl 0) = 0 := by
    exact_mod_cast (mul_eq_zero.mp h₄).resolve_right hy.ne'
  have h₆ : x.out.1 (.inr 1) (.inr 0) = 0 := by
    rw [h₅] at h₃
    simpa using h₃
  have h₇ : x.out.1 (.inr 1) (.inl 1) = 0 := by
    exact_mod_cast pow_eq_zero_iff (two_ne_zero) |>.mp h₁
  refine hx ?_
  have hmem : x.out ∈ klingenParabolicTwo := by
    refine mem_klingenParabolicTwo_of_row (d := x.out.1 (.inr 1) (.inr 1)) fun a ↦ ?_
    rcases a with a | a <;> fin_cases a <;> simp [h₅, h₆, h₇]
  rw [← Quotient.out_eq x]
  refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
  simpa using inv_mem hmem

/-- **The Siegel operator of the vector-valued Klingen–Eisenstein series**: for a cusp form `f` of
weight `k + j` on `SL(2, ℤ)` and even `k > 4`, `E(f)(diag(τ', it)) → f(τ') e₁^j` as `t → ∞`,
coordinatewise, by dominated convergence: the term of the trivial coset is constant, equal to
`f(τ') e₁^j`, and the other terms tend to `0`. -/
lemma tendsto_dual_vectorKlingenEisenstein_diagPoint (hk : 4 < k) (hk' : Even k) : Tendsto
    (fun t : Set.Ioi (0 : ℝ) ↦ φ (vectorKlingenEisenstein k j f (diagPoint τ' t))) atTop
    (𝓝 (f τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) := by
  classical
  rcases exists_nonneg_bound f with ⟨C, hC, hf⟩
  have hk₀ : 0 < k := by
    linarith
  have hsum : Summable fun x : KlingenCosetsTwo ↦ C * dualBound φ * klingenConst j k
      (diagPoint τ' tOne).val * ‖bottomRow x.out‖ ^ (-k) :=
    (summable_norm_bottomRow_zpow hk).mul_left _
  have hbound : ∀ᶠ t : Set.Ioi (0 : ℝ) in atTop, ∀ x : KlingenCosetsTwo,
      ‖φ (vectorKlingenTerm (diagPoint τ' t) k j f x.out)‖ ≤
        C * dualBound φ * klingenConst j k (diagPoint τ' tOne).val * ‖bottomRow x.out‖ ^ (-k) := by
    filter_upwards [eventually_ge_atTop tOne] with t ht x
    refine (norm_dual_vectorKlingenTerm_diagPoint_le φ τ' t x.out hC hf ht).trans ?_
    have hc : 0 ≤ C * dualBound φ * imLam (diagPoint τ' tOne).val ^ (-(j : ℤ)) :=
      mul_nonneg (mul_nonneg hC (dualBound_nonneg φ)) (zpow_nonneg (imLam_pos _).le _)
    have h₁ : klingenRadius (diagPoint τ' t) x.out ^ (-k) ≤
        klingenRadius (diagPoint τ' tOne) x.out ^ (-k) :=
      zpow_neg_le_zpow_neg (klingenRadius_pos _ x.out)
        (klingenRadius_diagPoint_le τ' t x.out ht) hk₀.le
    refine (mul_le_mul_of_nonneg_left
      (h₁.trans (klingenRadius_zpow_le (diagPoint τ' tOne) x.out hk₀)) hc).trans_eq ?_
    rw [klingenConst]
    ring1
  have hlim (x : KlingenCosetsTwo) : Tendsto
      (fun t : Set.Ioi (0 : ℝ) ↦ φ (vectorKlingenTerm (diagPoint τ' t) k j f x.out)) atTop
      (𝓝 (if x = ⟦1⟧ then f τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) else 0)) := by
    split_ifs with hx
    · subst hx
      refine tendsto_const_nhds.congr fun t ↦ ?_
      rw [vectorKlingenTerm_out _ hk' (cuspForm_apply_smul f), vectorKlingenTerm_one,
        topLeft_diagPoint, map_smul, smul_eq_mul]
    · exact tendsto_dual_vectorKlingenTerm_diagPoint φ τ' x.out hk hC hf (kappa_pos_of_ne τ' hx)
  have key : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ ∑' x : KlingenCosetsTwo,
      φ (vectorKlingenTerm (diagPoint τ' t) k j f x.out)) atTop (𝓝 (∑' x : KlingenCosetsTwo,
        if x = ⟦1⟧ then f τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) else 0)) :=
    tendsto_tsum_of_dominated_convergence hsum hlim hbound
  rw [tsum_ite_eq] at key
  exact key.congr fun t ↦ (hasSum_dual_vectorKlingenEisenstein f (diagPoint τ' t) φ hk).tsum_eq

lemma tprod_single_ne_zero : (⨂ₛ[ℂ] _ : Fin j, (Pi.single 0 1 : Fin 2 → ℂ)) ≠ 0 := by
  have e : (⨂ₛ[ℂ] _ : Fin j, (Pi.single 0 1 : Fin 2 → ℂ)) =
      (Pi.basisFun ℂ (Fin 2)).symmetricPower j (Sym.ofFn fun _ : Fin j ↦ (0 : Fin 2)) := by
    rw [Basis.symmetricPower_apply, SymmetricPower.tprodOfSym_ofFn]
    simp
  rw [e]
  exact Basis.ne_zero _ _

variable (k j) in
/-- The vector-valued Klingen–Eisenstein series, as a linear map on the cusp forms of weight `k + j`
on `SL(2, ℤ)`, for `k > 4`. -/
noncomputable def vectorKlingenEisensteinLinear (hk : 4 < k) :
    CuspForm 𝒮ℒ (k + j) →ₗ[ℂ] SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ) where
  toFun f := vectorKlingenEisenstein k j f
  map_add' f g := by
    funext Z
    rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have e (x : KlingenCosetsTwo) :
        φ (vectorKlingenTerm Z k j (f + g : CuspForm 𝒮ℒ (k + j)) x.out) =
          φ (vectorKlingenTerm Z k j f x.out) + φ (vectorKlingenTerm Z k j g x.out) := by
      simp [vectorKlingenTerm, add_smul]
    rw [map_sub, Pi.add_apply, map_add, sub_eq_zero]
    exact ((hasSum_dual_vectorKlingenEisenstein (f + g) Z φ hk).congr_fun fun x ↦ (e x).symm).unique
      ((hasSum_dual_vectorKlingenEisenstein f Z φ hk).add
        (hasSum_dual_vectorKlingenEisenstein g Z φ hk))
  map_smul' c f := by
    funext Z
    rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have e (x : KlingenCosetsTwo) :
        φ (vectorKlingenTerm Z k j (c • f : CuspForm 𝒮ℒ (k + j)) x.out) =
          c * φ (vectorKlingenTerm Z k j f x.out) := by
      simp [vectorKlingenTerm, mul_smul]
    rw [map_sub, RingHom.id_apply, Pi.smul_apply, map_smul, smul_eq_mul, sub_eq_zero]
    exact ((hasSum_dual_vectorKlingenEisenstein (c • f) Z φ hk).congr_fun fun x ↦ (e x).symm).unique
      ((hasSum_dual_vectorKlingenEisenstein f Z φ hk).mul_left c)

private lemma cuspForm_eq_zero_of_odd (hk : Odd k) (hj : Even j) : f = 0 :=
  DFunLike.ext _ _ fun w ↦ DFunLike.congr_fun (ModularForm.levelOne_odd_weight_eq_zero
    (hk.add_even (by exact_mod_cast hj)) (ModularFormClass.modularForm f)) w

/-- **The Klingen–Eisenstein series determine the cusp form**: `f ↦ E(f)` is injective for `k > 4`
and `j` even, as `E(f)(diag(τ', it)) → f(τ') e₁^j` and `e₁^j ≠ 0` when `k` is even, while there are
no nonzero cusp forms of odd weight `k + j` on `SL(2, ℤ)`. -/
lemma vectorKlingenEisensteinLinear_injective (hk : 4 < k) (hj : Even j) :
    Function.Injective (vectorKlingenEisensteinLinear k j hk) := by
  intro f g h
  rcases Int.even_or_odd k with hk' | hk'
  · rcases Projective.exists_dual_ne_zero ℂ (tprod_single_ne_zero (j := j)) with ⟨φ, hφ⟩
    refine DFunLike.ext _ _ fun τ' ↦ ?_
    have h₃ : vectorKlingenEisenstein k j f = vectorKlingenEisenstein k j g :=
      h
    have h₁ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (vectorKlingenEisenstein k j g (diagPoint τ' t)))
        atTop (𝓝 (f τ' * φ (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1))) :=
      h₃ ▸ tendsto_dual_vectorKlingenEisenstein_diagPoint f φ τ' hk hk'
    exact mul_right_cancel₀ hφ (tendsto_nhds_unique h₁
      (tendsto_dual_vectorKlingenEisenstein_diagPoint g φ τ' hk hk'))
  · rw [cuspForm_eq_zero_of_odd f hk' hj, cuspForm_eq_zero_of_odd g hk' hj]

/-- The element `-1` of `Sp(4, ℤ)`. -/
private def negOneSp : symplecticGroup (Fin 2) ℤ :=
  ⟨-1, by rw [SymplecticGroup.mem_iff']; simp⟩

private lemma denom_negOneSp (W : SiegelUpperHalfSpace (Fin 2)) :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) negOneSp) W.val = -1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [negOneSp, denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]

private lemma negOneSp_smul (W : SiegelUpperHalfSpace (Fin 2)) :
    SymplecticGroup.map (Int.castRingHom ℝ) negOneSp • W = W := by
  refine SiegelUpperHalfSpace.ext ?_
  have hn : num (SymplecticGroup.map (Int.castRingHom ℝ) negOneSp) W.val = -W.val := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [negOneSp, num, toBlocks₁₁, toBlocks₁₂, Matrix.mul_apply]
  have hi : (-1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = -1 :=
    inv_eq_left_inv (by simp)
  rw [val_smul, hn, denom_negOneSp, hi, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_one]

private lemma rhoKJ_neg_one_apply (hj : Odd j) (g : GL (Fin 2) ℂ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = -1) (v : Sym[ℂ]^j (Fin 2 → ℂ)) : rhoKJ k j g v = -v := by
  have hv : v ∈ Submodule.span ℂ (Set.range (SymmetricPower.tprod ℂ)) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  have hdet : ((g.det ^ k : ℂˣ) : ℂ) = 1 := by
    rw [Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, hg]
    simp [det_neg]
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨m, rfl⟩
    have e : TauCeti.symPowerRep ℂ 2 j g (SymmetricPower.tprod ℂ m) =
        SymmetricPower.tprod ℂ fun i ↦ (-1 : ℂ) • m i := by
      refine (Representation.symmetricPower_apply_tprod _ _ _ _).trans
        (congrArg _ (funext fun i ↦ ?_))
      simp [hg]
    have e₁ : (SymmetricPower.tprod ℂ fun i ↦ (-1 : ℂ) • m i) =
        (∏ _ : Fin j, (-1 : ℂ)) • SymmetricPower.tprod ℂ m :=
      (SymmetricPower.tprod ℂ).map_smul_univ (fun _ : Fin j ↦ (-1 : ℂ)) m
    have e₂ : rhoKJ k j g (SymmetricPower.tprod ℂ m) =
        ((g.det ^ k : ℂˣ) : ℂ) • TauCeti.symPowerRep ℂ 2 j g (SymmetricPower.tprod ℂ m) :=
      rfl
    rw [e₂, e, hdet, one_smul, e₁]
    simp [hj.neg_one_pow]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy, neg_add]
  | smul a x _ hx =>
    rw [map_smul, hx, smul_neg]

/-- **There are no nonzero Siegel modular forms of weight `ρ_{k,j}` on `Sp(4, ℤ)` for `j` odd**: the
element `-1` of `Sp(4, ℤ)` acts trivially on `ℋ₂`, with automorphy factor `-1`, and
`ρ_{k,j}(-1) = (-1)^j`. -/
lemma modularFormsKJ_eq_bot_of_odd (hj : Odd j) :
    modularFormsKJ k j (SymplecticGroup.integral (Fin 2)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro F ⟨-, hF⟩
  funext W
  have h : F (SymplecticGroup.map (algebraMap ℚ ℝ)
      (SymplecticGroup.map (Int.castRingHom ℚ) negOneSp) • W) = _ :=
    hF ⟨_, negOneSp, trivial, rfl⟩ W
  rw [map_algebraMap_map_intCast negOneSp, negOneSp_smul] at h
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h
  rw [rhoKJ_neg_one_apply hj _ (denom_negOneSp W)] at h
  have h₂ : (2 : ℂ) • F W = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  simpa using h₂

variable (k j) in
/-- The space `KE_{j,k}(Γ₂)` of **vector-valued Klingen–Eisenstein series of degree `2`** (LMFDB
`mf.siegel.subspace.degree.two`, `mf.siegel.klingen_eisenstein_series`) and weight
`ρ_{k,j} = det^k ⊗ Sym^j`: the Siegel modular forms on `Γ₂` in the span of the series `E(f)` of the
cusp forms `f` of weight `k + j` on `SL(2, ℤ)`. For `k > 4` and `k` even or `j` even it is that span
(`SiegelUpperHalfSpace.klingenEisensteinSubspaceKJ_eq_range` for `j` even), the series being Siegel
modular forms for `k` even, and zero for `k` odd. For `k` and `j` both odd, the terms of `E(f)` only
make sense up to a sign, and the space is `0`, there being no nonzero modular forms
(`SiegelUpperHalfSpace.modularFormsKJ_eq_bot_of_odd`). -/
noncomputable def klingenEisensteinSubspaceKJ :
    Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) :=
  Submodule.span ℂ (Set.range fun f : CuspForm 𝒮ℒ (k + j) ↦ vectorKlingenEisenstein k j f) ⊓
    modularFormsKJ k j (SymplecticGroup.integral (Fin 2))

variable (k j) in
lemma klingenEisensteinSubspaceKJ_le_modularFormsKJ :
    klingenEisensteinSubspaceKJ k j ≤ modularFormsKJ k j (SymplecticGroup.integral (Fin 2)) :=
  inf_le_right

lemma klingenEisensteinSubspaceKJ_eq_range (hk : 4 < k) (hj : Even j) :
    klingenEisensteinSubspaceKJ k j = LinearMap.range (vectorKlingenEisensteinLinear k j hk) := by
  have h : Submodule.span ℂ (Set.range fun f : CuspForm 𝒮ℒ (k + j) ↦
      vectorKlingenEisenstein k j f) = LinearMap.range (vectorKlingenEisensteinLinear k j hk) :=
    (congrArg _ (LinearMap.coe_range (vectorKlingenEisensteinLinear k j hk)).symm).trans
      (Submodule.span_eq _)
  rw [klingenEisensteinSubspaceKJ, h, inf_eq_left]
  rintro _ ⟨f, rfl⟩
  rcases Int.even_or_odd k with hk' | hk'
  · exact vectorKlingenEisenstein_mem_modularFormsKJ f hk hk'
  · rw [cuspForm_eq_zero_of_odd f hk' hj, map_zero]
    exact Submodule.zero_mem _

/-- **The Klingen–Eisenstein series meet the cusp forms trivially**, for `k > 4`: for `j` odd there
are no nonzero modular forms; for `j` even and `k` even the Siegel operator of a cusp form vanishes,
while that of `E(f)` is `f e₁^j`; for `j` even and `k` odd there are no nonzero cusp forms `f`. -/
lemma disjoint_klingenEisensteinSubspaceKJ_cuspFormsKJ (hk : 4 < k) : Disjoint
    (klingenEisensteinSubspaceKJ k j) (cuspFormsKJ k j (SymplecticGroup.integral (Fin 2))) := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [Submodule.disjoint_def, klingenEisensteinSubspaceKJ_eq_range hk hj]
    rintro _ ⟨f, rfl⟩ hF
    rcases Int.even_or_odd k with hk' | hk'
    · rcases Projective.exists_dual_ne_zero ℂ (tprod_single_ne_zero (j := j)) with ⟨φ, hφ⟩
      have hf : f = 0 := by
        refine DFunLike.ext _ _ fun τ' ↦ ?_
        have h₂ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (slash (rhoKJ k j) (SymplecticGroup.map
            (algebraMap ℚ ℝ) 1) (vectorKlingenEisensteinLinear k j hk f) (diagPoint τ' t))) atTop
            (𝓝 0) :=
          hF.2 1 τ' φ
        rw [map_one, slash_one] at h₂
        exact (mul_eq_zero.mp (tendsto_nhds_unique
          (tendsto_dual_vectorKlingenEisenstein_diagPoint f φ τ' hk hk') h₂)).resolve_right hφ
      rw [hf, map_zero]
    · rw [cuspForm_eq_zero_of_odd f hk' hj, map_zero]
  · exact disjoint_bot_left.mono_left <|
      (klingenEisensteinSubspaceKJ_le_modularFormsKJ k j).trans_eq (modularFormsKJ_eq_bot_of_odd hj)

/-- **`KE_{j,k}(Γ₂)` is isomorphic to the space of cusp forms of weight `k + j` on `SL(2, ℤ)`**
(LMFDB `mf.siegel.subspace.degree.two`), through `f ↦ E(f)`, for `k > 4` and `j` even. For `j` odd
the knowl's statement fails: `M_{j,k}(Γ₂) = 0`
(`SiegelUpperHalfSpace.modularFormsKJ_eq_bot_of_odd`), while `S_{k+j}(SL(2, ℤ)) ≠ 0` in general,
for instance for `(k, j) = (5, 7)`. -/
noncomputable def klingenEisensteinEquiv (hk : 4 < k) (hj : Even j) :
    CuspForm 𝒮ℒ (k + j) ≃ₗ[ℂ] klingenEisensteinSubspaceKJ k j :=
  (LinearEquiv.ofInjective _ (vectorKlingenEisensteinLinear_injective hk hj)).trans
    (LinearEquiv.ofEq _ _ (klingenEisensteinSubspaceKJ_eq_range hk hj).symm)

lemma coe_klingenEisensteinEquiv (hk : 4 < k) (hj : Even j) :
    (klingenEisensteinEquiv hk hj f : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) =
      vectorKlingenEisenstein k j f :=
  rfl

end SiegelUpperHalfSpace
