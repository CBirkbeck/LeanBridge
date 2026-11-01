import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.WeightTwoVanishing
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftModularity
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftParabolic
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParabolicDecomposition
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The theorem of Maass

The Maass lift `F = Vφ` (`SiegelUpperHalfSpace.maassLift`, LMFDB `mf.siegel.lift.maass`) of a
Jacobi cusp form `φ ∈ J_{k,1}^cusp` of weight `k ≥ 3` is a Siegel cusp form: `Φ(F ∣ γ) = 0` for
every `γ ∈ Sp(4, ℚ)`. As `Sp(4, ℚ) = Sp(4, ℤ) P(ℚ)`
(`SymplecticGroup.exists_mem_integral_inv_mul_mem_siegelParabolic`) and `F` is invariant under
`Sp(4, ℤ)`, it suffices to take `γ = p = (A, B; 0, D)` in the Siegel parabolic subgroup, which acts
by `Z ↦ AZAᵀ + BAᵀ`. At `Z = diag(τ', it)` the term of `T = (n, r/2; r/2, m)` of the Fourier
expansion of `F(pZ)` has absolute value `|a(T)| e^{-2π(Im τ' Q(a₁) + t Q(a₂))}`, where
`Q(x) = xᵀTx` and `a₁, a₂` are the columns of `A`. For a cusp form `a(T) ≠ 0` only for positive
definite `T` (`c(n, r) = 0` unless `4n - r² > 0`, and `a(T)` is a sum of such coefficients with the
same sign of `4nm - r²`), so `Q(a₂) > 0` and every term tends to `0` as `t → ∞`, dominated by its
value at `t = 1`: by dominated convergence `F(p diag(τ', it)) → 0`.

With `J_{2,1} = 0` (`ModularForm.eq_zero_of_mem_jacobiFormSpace_two`), this proves the theorem of
Maass `SiegelUpperHalfSpace.MaassLiftTheorem` in full: the series of `Vφ` converges absolutely on
`ℋ₂`, `Vφ ∈ M_k(Sp(4, ℤ))` for every `φ ∈ J_{k,1}`, and `Vφ ∈ S_k(Sp(4, ℤ))` for every Jacobi cusp
form `φ` (Eichler and Zagier, Theorem 6.2). The lift is then a linear map
`V : J_{k,1} → M_k(Sp(4, ℤ))`, the series being additive in the Fourier coefficients.

## Main definitions

* `SiegelUpperHalfSpace.maassLiftLinearMap` (LMFDB `mf.siegel.lift.maass`): the Maass lift
  `J_{k,1} → M_k(Sp(4, ℤ))` as a linear map.

## Main results

* `SiegelUpperHalfSpace.tendsto_maassLift_smul_diagPoint`: `F(p diag(τ', it)) → 0` as `t → ∞` for
  `p` in the Siegel parabolic subgroup of `Sp(4, ℝ)`.
* `SiegelUpperHalfSpace.siegelOperatorVanishes_slash_maassLift`: `Φ(F ∣ p) = 0` for such `p`.
* `SiegelUpperHalfSpace.isCuspForm_maassLift`: the Maass lift of a Jacobi cusp form of weight
  `k ≥ 3` is a cusp form.
* `SiegelUpperHalfSpace.maassLiftTheorem`: the theorem of Maass.
-/

open Complex Filter Matrix ModularForm Real SymplecticGroup Topology

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} {P : symplecticGroup (Fin 2) ℝ} (τ' : ℍ) (n r m : ℤ)
    (c c' : ℤ × ℤ → ℂ) (u : ℂ)

lemma maassCoeff_eq_zero_of_le (hφ : φ ∈ jacobiCuspFormSpace k 1) (h : 4 * n * m ≤ r ^ 2) :
    maassCoeff k (jacobiCoeff φ) n r m = 0 := by
  rw [maassCoeff]
  split_ifs with h₀ h₁
  · rw [jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2 (by simp), mul_zero]
  · refine Finset.sum_eq_zero fun d hd ↦ ?_
    rw [jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2, mul_zero]
    intro hlt
    simp only [Nat.cast_one] at hlt
    nlinarith [sq_mul_disc_of_mem_divisors n r m hd,
      mul_pos (pow_pos (Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd) : (0 : ℤ) < d) 2)
        (sub_pos.mpr hlt)]
  · rfl

lemma pos_of_maassCoeff_ne_zero (hφ : φ ∈ jacobiCuspFormSpace k 1)
    (h : maassCoeff k (jacobiCoeff φ) n r m ≠ 0) {x y : ℝ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < n * x ^ 2 + r * x * y + m * y ^ 2 := by
  have hr : r ^ 2 < 4 * n * m := not_le.mp fun h' ↦ h (maassCoeff_eq_zero_of_le n r m hφ h')
  have hp : 0 ≤ n ∧ 0 ≤ m ∧ r ^ 2 ≤ 4 * n * m :=
    not_not.mp fun h' ↦ h (maassCoeff_eq_zero_of_not_posSemidef n r m hφ.1 h')
  have hn : 0 < n := lt_of_le_of_ne hp.1 fun h0 ↦ by
    rw [← h0] at hr
    nlinarith [sq_nonneg r]
  have hn' : (0 : ℝ) < n := Int.cast_pos.mpr hn
  have hr' : (r : ℝ) ^ 2 < 4 * n * m := by
    exact_mod_cast hr
  rcases eq_or_ne y 0 with rfl | hy
  · nlinarith [sq_pos_iff.mpr <| hxy.resolve_right fun h ↦ h rfl]
  · have h4 : 0 < 4 * n * (n * x ^ 2 + r * x * y + m * y ^ 2) := by
      nlinarith [sq_nonneg (2 * n * x + r * y),
        mul_pos (sub_pos.mpr hr') (pow_pos (abs_pos.mpr hy) 2), sq_abs y]
    nlinarith

lemma im_smul_diagPoint (hP : P ∈ siegelParabolic (Fin 2) ℝ) (t : Set.Ioi (0 : ℝ)) (i j : Fin 2) :
    ((P • diagPoint τ' t).val i j).im = P.1.toBlocks₁₁ i 0 * P.1.toBlocks₁₁ j 0 * τ'.im +
      P.1.toBlocks₁₁ i 1 * P.1.toBlocks₁₁ j 1 * t := by
  have hD : P.1.toBlocks₂₂.map ofReal * P.1.toBlocks₁₁ᵀ.map ofReal = 1 := by
    have h : (P.1.toBlocks₂₂ * P.1.toBlocks₁₁ᵀ).map ofRealHom =
        (1 : Matrix (Fin 2) (Fin 2) ℝ).map ofRealHom :=
      congrArg (Matrix.map · ofRealHom) (toBlocks₂₂_mul_transpose_toBlocks₁₁ hP)
    rwa [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [val_smul, num, denom, (hP : P.1.toBlocks₂₁ = 0), Matrix.map_zero _ ofReal_zero,
    Matrix.zero_mul, zero_add, inv_eq_right_inv hD]
  simp [Matrix.mul_apply, diagPoint]
  ring1

private lemma norm_liftExp (W : SiegelUpperHalfSpace (Fin 2)) : ‖liftExp 1 n r m W‖ =
    rexp (-(2 * π * (n * (W.val 0 0).im + r * (W.val 0 1).im + m * (W.val 1 1).im))) := by
  rw [liftExp, Complex.norm_exp]
  congr 1
  norm_num

/-- **The Maass lift of a Jacobi cusp form vanishes at the cusp `diag(τ', i∞)` after any element of
the Siegel parabolic subgroup**: for `φ ∈ J_{k,1}^cusp` and `p = (A, B; 0, D) ∈ Sp(4, ℝ)`,
`(Vφ)(p diag(τ', it)) → 0` as `t → ∞`. The term of `T = (n, r/2; r/2, m)` has absolute value
`|a(T)| e^{-2π(Im τ' Q(a₁) + t Q(a₂))}` with `Q(x) = xᵀTx` and `a₁, a₂` the columns of `A`, and
`Q(a₂) > 0` when `a(T) ≠ 0`, `T` being then positive definite; dominated convergence concludes. -/
lemma tendsto_maassLift_smul_diagPoint (hφ : φ ∈ jacobiCuspFormSpace k 1)
    (hP : P ∈ siegelParabolic (Fin 2) ℝ) :
    Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ maassLift k φ (P • diagPoint τ' t)) atTop (𝓝 0) := by
  let Q : ℤ × ℤ × ℤ → Fin 2 → ℝ := fun q j ↦ q.1 * P.1.toBlocks₁₁ 0 j ^ 2 +
    q.2.1 * P.1.toBlocks₁₁ 0 j * P.1.toBlocks₁₁ 1 j + q.2.2 * P.1.toBlocks₁₁ 1 j ^ 2
  have hnorm (q : ℤ × ℤ × ℤ) (t : Set.Ioi (0 : ℝ)) :
      ‖liftExp 1 q.1 q.2.1 q.2.2 (P • diagPoint τ' t)‖ =
        rexp (-(2 * π * (τ'.im * Q q 0 + t * Q q 1))) := by
    rw [norm_liftExp, im_smul_diagPoint τ' hP, im_smul_diagPoint τ' hP, im_smul_diagPoint τ' hP]
    congr 1
    ring1
  have hdet : P.1.toBlocks₂₂.det * P.1.toBlocks₁₁.det = 1 := by
    rw [← det_transpose P.1.toBlocks₁₁, ← det_mul, toBlocks₂₂_mul_transpose_toBlocks₁₁ hP, det_one]
  have hcol : P.1.toBlocks₁₁ 0 1 ≠ 0 ∨ P.1.toBlocks₁₁ 1 1 ≠ 0 := by
    refine not_and_or.mp fun h ↦ right_ne_zero_of_mul_eq_one hdet ?_
    rw [det_fin_two, h.1, h.2]
    ring1
  have hpos (q : ℤ × ℤ × ℤ) (hq : maassCoeff k (jacobiCoeff φ) q.1 q.2.1 q.2.2 ≠ 0) : 0 < Q q 1 :=
    pos_of_maassCoeff_ne_zero q.1 q.2.1 q.2.2 hφ hq hcol
  have hs : Summable fun q : ℤ × ℤ × ℤ ↦ ‖maassCoeff k (jacobiCoeff φ) q.1 q.2.1 q.2.2 *
      liftExp 1 q.1 q.2.1 q.2.2 (P • diagPoint τ' ⟨1, Set.mem_Ioi.mpr one_pos⟩)‖ :=
    summable_norm_iff.mpr (summable_maassLift_of_mem_jacobiFormSpace hφ.1 _)
  have hab (q : ℤ × ℤ × ℤ) : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦
      maassCoeff k (jacobiCoeff φ) q.1 q.2.1 q.2.2 * liftExp 1 q.1 q.2.1 q.2.2 (P • diagPoint τ' t))
        atTop (𝓝 0) := by
    by_cases hq : maassCoeff k (jacobiCoeff φ) q.1 q.2.1 q.2.2 = 0
    · simp [hq]
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simp only [norm_mul, hnorm]
    have ht : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ (t : ℝ)) atTop atTop :=
      tendsto_Ioi_atTop.mp tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <|
      (tendsto_atTop_add_const_left _ _ (ht.atTop_mul_const (hpos q hq))).const_mul_atTop
        two_pi_pos).const_mul ‖maassCoeff k (jacobiCoeff φ) q.1 q.2.1 q.2.2‖
  have hb : ∀ᶠ t : Set.Ioi (0 : ℝ) in atTop, ∀ q : ℤ × ℤ × ℤ,
      ‖maassCoeff k (jacobiCoeff φ) q.1 q.2.1 q.2.2 *
          liftExp 1 q.1 q.2.1 q.2.2 (P • diagPoint τ' t)‖ ≤
        ‖maassCoeff k (jacobiCoeff φ) q.1 q.2.1 q.2.2 *
          liftExp 1 q.1 q.2.1 q.2.2 (P • diagPoint τ' ⟨1, Set.mem_Ioi.mpr one_pos⟩)‖ := by
    refine eventually_atTop.mpr ⟨⟨1, Set.mem_Ioi.mpr one_pos⟩, fun t ht q ↦ ?_⟩
    by_cases hq : maassCoeff k (jacobiCoeff φ) q.1 q.2.1 q.2.2 = 0
    · simp [hq]
    rw [norm_mul, norm_mul, hnorm, hnorm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : (1 : ℝ) ≤ t := ht
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (hpos q hq).le, Real.pi_pos]
  simpa [maassLift] using tendsto_tsum_of_dominated_convergence hs hab hb

/-- **The Siegel operator vanishes on the Maass lift of a Jacobi cusp form slashed by the Siegel
parabolic subgroup**: `Φ(Vφ ∣ p) = 0` for `φ ∈ J_{k,1}^cusp` and `p = (A, B; 0, D) ∈ Sp(4, ℝ)`,
the automorphy factor `det(D)^{-k}` of `p` being constant. -/
lemma siegelOperatorVanishes_slash_maassLift (hφ : φ ∈ jacobiCuspFormSpace k 1)
    (hP : P ∈ siegelParabolic (Fin 2) ℝ) :
    SiegelOperatorVanishes (slash (TauCeti.detPowerRep ℂ 2 k) P (maassLift k φ)) := by
  intro τ ℓ
  have hd (Z : SiegelUpperHalfSpace (Fin 2)) :
      denomGL P Z = denomGL P (diagPoint τ ⟨1, Set.mem_Ioi.mpr one_pos⟩) :=
    Units.ext <| by
      simp only [coe_denomGL, denom, show P.1.toBlocks₂₁ = 0 from hP, Matrix.map_zero _ ofReal_zero,
        Matrix.zero_mul]
  let L : ℂ →ₗ[ℂ] ℂ := ℓ ∘ₗ TauCeti.detPowerRep ℂ 2 k
    (denomGL P (diagPoint τ ⟨1, Set.mem_Ioi.mpr one_pos⟩))⁻¹
  refine ((L.continuous_of_finiteDimensional.tendsto' 0 0 (map_zero L)).comp
    (tendsto_maassLift_smul_diagPoint τ hφ hP)).congr fun t ↦ ?_
  simp only [slash_apply, hd, Function.comp_apply, L, LinearMap.comp_apply]

private lemma map_mem_siegelParabolic {p : symplecticGroup (Fin 2) ℚ}
    (hp : p ∈ siegelParabolic (Fin 2) ℚ) : map (algebraMap ℚ ℝ) p ∈ siegelParabolic (Fin 2) ℝ := by
  ext i j
  have h : (p : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inr i) (.inl j) = 0 :=
    congrFun (congrFun hp i) j
  simp [toBlocks₂₁, h]

/-- **The Maass lift of a Jacobi cusp form is a cusp form** (LMFDB `mf.siegel.lift.maass`): for
`φ ∈ J_{k,1}^cusp`, `k ≥ 3`, `Φ(Vφ ∣ γ) = 0` for every `γ ∈ Sp(4, ℚ)`. Write `γ = gp` with
`g ∈ Sp(4, ℤ)` and `p` in the Siegel parabolic subgroup; then `Vφ ∣ γ = Vφ ∣ p`. -/
lemma isCuspForm_maassLift (hφ : φ ∈ jacobiCuspFormSpace k 1) (hk : 3 ≤ k) :
    IsCuspForm (TauCeti.detPowerRep ℂ 2 k) (maassLift k φ) := by
  intro γ
  rcases exists_mem_integral_inv_mul_mem_siegelParabolic γ with ⟨g, hg, hp⟩
  have hF : slash (TauCeti.detPowerRep ℂ 2 k) (map (algebraMap ℚ ℝ) g) (maassLift k φ) =
      maassLift k φ := by
    simpa using ((mem_modularForms_iff_slash _ _ _ _).mp
      (maassLift_mem_scalarModularForms_of_three_le hφ.1 hk)).2 ⟨g, hg⟩
  rw [← mul_inv_cancel_left g γ, map_mul, slash_mul, hF]
  exact siegelOperatorVanishes_slash_maassLift hφ (map_mem_siegelParabolic hp)

/-- **The theorem of Maass** (LMFDB `mf.siegel.lift.maass`; Eichler and Zagier, Theorem 6.2): for
every Jacobi form `φ ∈ J_{k,1}` the series of the Maass lift `Vφ` converges absolutely on `ℋ₂`,
`Vφ` is a Siegel modular form of weight `k` on `Sp(4, ℤ)`, and it is a cusp form if `φ` is one.
So `V` is a map `J_{k,1} → M_k(Sp(4, ℤ))` sending `J_{k,1}^cusp` to `S_k(Sp(4, ℤ))`. -/
lemma maassLiftTheorem : MaassLiftTheorem :=
  maassLiftTheorem_of_forall (fun _ hφ n ↦ tsum_sq_mul_jacobiCoeff_eq_zero n hφ)
    fun _ _ hk hφ ↦ isCuspForm_maassLift hφ hk

private lemma maassCoeff_add :
    maassCoeff k (c + c') n r m = maassCoeff k c n r m + maassCoeff k c' n r m := by
  simp only [maassCoeff, liftDivisorSum]
  split_ifs <;> simp [mul_add, Finset.sum_add_distrib]

private lemma maassCoeff_smul : maassCoeff k (u • c) n r m = u * maassCoeff k c n r m := by
  simp only [maassCoeff, liftDivisorSum]
  split_ifs <;> simp [Finset.mul_sum, mul_left_comm]

private lemma maassLift_add {ψ : ℍ × ℂ → ℂ} (hφ : φ ∈ jacobiFormSpace k 1)
    (hψ : ψ ∈ jacobiFormSpace k 1) : maassLift k (φ + ψ) = maassLift k φ + maassLift k ψ :=
  funext fun Z ↦ by
    rw [Pi.add_apply, maassLift, maassLift, maassLift,
      ← (summable_maassLift_of_mem_jacobiFormSpace hφ Z).tsum_add
        (summable_maassLift_of_mem_jacobiFormSpace hψ Z)]
    refine tsum_congr fun p ↦ ?_
    rw [((hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ).add
      (hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hψ)).jacobiCoeff_eq,
      maassCoeff_add, add_mul]

private lemma maassLift_smul (hφ : φ ∈ jacobiFormSpace k 1) :
    maassLift k (u • φ) = u • maassLift k φ :=
  funext fun Z ↦ by
    rw [Pi.smul_apply, smul_eq_mul, maassLift, maassLift, ← tsum_mul_left]
    refine tsum_congr fun p ↦ ?_
    rw [((hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hφ).const_smul
      u).jacobiCoeff_eq, maassCoeff_smul, mul_assoc]

variable (k) in
/-- The **Maass lift** (LMFDB `mf.siegel.lift.maass`) as a linear map `V : J_{k,1} → M_k(Sp(4, ℤ))`
from the Jacobi forms of weight `k` and index `1` to the Siegel modular forms of weight `k` and
degree `2` on the Siegel modular group: `φ ↦ maassLift k φ`, which lies in `M_k(Sp(4, ℤ))` by the
theorem of Maass (`SiegelUpperHalfSpace.maassLiftTheorem`). It sends Jacobi cusp forms to cusp
forms. -/
noncomputable def maassLiftLinearMap :
    jacobiFormSpace k 1 →ₗ[ℂ] scalarModularForms k (integral (Fin 2)) where
  toFun φ := ⟨maassLift k φ, maassLiftTheorem.mem_modularForms k φ φ.2⟩
  map_add' φ ψ := Subtype.ext <| maassLift_add φ.2 ψ.2
  map_smul' u φ := Subtype.ext <| maassLift_smul u φ.2

end SiegelUpperHalfSpace
