import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CuspCriterion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonDefinite
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SiegelSetIntegral
import Mathlib.Analysis.Matrix.Order

/-!
# Convergence of the Petersson product of Siegel modular forms of degree 2

On the Siegel set, `Y = Im Z` dominates `(1/2) diag(y₀₀, y₁₁)`, with `y₀₀, y₁₁ ≥ 4/5`. So a function
`f(Z) = ∑ a(n) e^{2πi tr(nZ)}` with a positive semidefinite expansion is bounded on the Siegel set,
by the value of the majorant series at `diag(2i/5, 2i/5)`, and if the expansion is positive
definite, with `n₀₀, n₁₁ ≥ ε` on its support, then `f` decays like `e^{-πε(y₀₀ + y₁₁)}`. The same
holds for `f ∘ T`, for a transformation `T` with `Im T(Z)` a rational multiple of `A (Im Z) Aᵀ`, as
for the slash of `f` by an element of `GSp(4, ℚ)⁺`.

So the Petersson integrand `b(ρ(Im Z) F(Z), G(Z))` of `F ∈ M_ρ(Sp(4, ℤ))` and a cusp form `G` decays
exponentially on the Siegel set, as soon as `b(ρ(Y) v, w)` grows at most polynomially there, which
is `SiegelUpperHalfSpace.IsModerateForm`. Since the norm of the integrand is invariant under
`Sp(4, ℤ)` and every orbit meets the Siegel set, the integrand is integrable on every fundamental
domain. Hence the Petersson product is definite on the cusp forms.

## Main definitions

* `SiegelUpperHalfSpace.IsModerateForm`: `b(ρ(Im Z) v, w)` is continuous in `Z` and grows at most
  polynomially on the Siegel set.

## Main results

* `SiegelUpperHalfSpace.IsHolomorphic.continuous_dual`: holomorphic functions are continuous.
* `SiegelUpperHalfSpace.exists_norm_dual_le_of_posSemidef`: a positive semidefinite expansion is
  bounded on the Siegel set.
* `SiegelUpperHalfSpace.exists_norm_dual_le_of_posDef`: a positive definite expansion decays
  exponentially on the Siegel set.
* `SiegelUpperHalfSpace.exists_norm_dual_comp_le_of_posDef`: the same after a transformation with
  rational linear imaginary part.
* `SiegelUpperHalfSpace.tendsto_dual_comp_scalarPoint`: the constant term as a limit, after such a
  transformation.
* `SiegelUpperHalfSpace.peterssonIntegrand_map_smul`: the Petersson integrand of modular forms is
  invariant.
* `SiegelUpperHalfSpace.peterssonForm_pos`: the Petersson form is positive.
* `SiegelUpperHalfSpace.continuous_peterssonIntegrand`: the Petersson integrand is continuous.
* `SiegelUpperHalfSpace.exists_norm_peterssonIntegrand_le`: the Petersson integrand on the Siegel
  set.
* `SiegelUpperHalfSpace.integrableOn_peterssonIntegrand_of_decay`: integrability from decay on the
  Siegel set.
* `SiegelUpperHalfSpace.exists_norm_dual_le_of_mem_modularForms`: a modular form on `Sp(4, ℤ)` is
  bounded on the Siegel set.
* `SiegelUpperHalfSpace.exists_norm_dual_le_of_mem_cuspForms`: a cusp form on `Sp(4, ℤ)` decays
  exponentially on the Siegel set.
* `SiegelUpperHalfSpace.integrableOn_peterssonIntegrand`: the Petersson integrand of a modular form
  and a cusp form on `Sp(4, ℤ)` is integrable on every fundamental domain.
* `SiegelUpperHalfSpace.isPeterssonDefinite_cuspForms`: the Petersson product is definite on the
  cusp forms on `Sp(4, ℤ)`.
-/

open Complex Matrix MeasureTheory Module Real SymplecticGroup

open scoped ComplexConjugate ComplexOrder ENNReal

namespace SiegelUpperHalfSpace

/-- **Holomorphic functions on `ℋ_g` are continuous**, through every linear form. -/
lemma IsHolomorphic.continuous_dual {l V : Type*} [AddCommGroup V] [Module ℂ V]
    {f : SiegelUpperHalfSpace l → V} (hf : IsHolomorphic f) (φ : Dual ℂ V) :
    Continuous fun τ ↦ φ (f τ) := by
  have hsym (τ : SiegelUpperHalfSpace l) : symmetrize τ.val = τ.val := by
    ext i j
    have h : τ.val j i = τ.val i j := congrFun (congrFun τ.transpose_val i) j
    have h₂ : symmetrize τ.val i j = 2⁻¹ * (τ.val i j + τ.val j i) := rfl
    rw [h₂, h]
    ring1
  have hmem (τ : SiegelUpperHalfSpace l) : (τ.val : l → l → ℂ) ∈ symmetrizePreimage l := by
    have h : ((symmetrize τ.val).map im).PosDef := by
      rw [hsym]
      exact τ.posDef_im
    exact h
  have e (τ : SiegelUpperHalfSpace l) : φ (f τ) = extend (φ ∘ f) τ.val := by
    rw [extend_of_mem _ (hmem τ)]
    exact congrArg (φ ∘ f) (SiegelUpperHalfSpace.ext (hsym τ).symm)
  rw [funext e]
  exact (hf φ).continuousOn.comp_continuous
    (continuous_pi fun i ↦ continuous_pi fun j ↦ (continuous_apply_apply i j).comp continuous_val)
    hmem

/-! ### Fourier expansions on the Siegel set -/

section Fourier

private lemma half_add_le {a b c u v w : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c)
    (hv : 2 * |v| ≤ u) (huw : u ≤ w) : (a * u + c * w) / 2 ≤ a * u + b * v + (b * v + c * w) := by
  have hu : 0 ≤ u := (mul_nonneg zero_le_two (abs_nonneg v)).trans hv
  have hv₂ : 4 * v ^ 2 ≤ u * w := by
    have h₁ : (2 * |v|) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hv 2
    rw [mul_pow, sq_abs] at h₁
    nlinarith
  have hB : (2 * b * v) ^ 2 ≤ a * u * (c * w) := by
    have h₁ : b ^ 2 * (4 * v ^ 2) ≤ a * c * (u * w) :=
      mul_le_mul hb hv₂ (by positivity) (mul_nonneg ha hc)
    nlinarith
  have hA : 0 ≤ a * u + c * w := add_nonneg (mul_nonneg ha hu) (mul_nonneg hc (hu.trans huw))
  have h₂ : |2 * b * v| ≤ (a * u + c * w) / 2 :=
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (a * u - c * w)]) (by positivity)
  linarith [(abs_le.mp h₂).1]

private lemma scalar_le_of_le {a c u w : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hu : 4 / 5 ≤ u)
    (hw : 4 / 5 ≤ w) : 4 / 5 * (a + c) ≤ a * u + c * w := by
  nlinarith [mul_le_mul_of_nonneg_left hu ha, mul_le_mul_of_nonneg_left hw hc]

private lemma exponent_le {a c u w ε : ℝ} (ha : ε ≤ a) (hc : ε ≤ c) (hu : 4 / 5 ≤ u)
    (hw : 4 / 5 ≤ w) :
    -(π * (a * u + c * w)) ≤ -(π * ε) * (u + w) + π * ε * (8 / 5) + -(π * (4 / 5 * (a + c))) := by
  have h₁ : 0 ≤ (a - ε) * (u - 4 / 5) := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hu)
  have h₂ : 0 ≤ (c - ε) * (w - 4 / 5) := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hw)
  have h₃ : 0 ≤ π * ((a - ε) * (u - 4 / 5) + (c - ε) * (w - 4 / 5)) :=
    mul_nonneg Real.pi_pos.le (add_nonneg h₁ h₂)
  linarith

private lemma pi_mul_le {A B : ℝ} (h : A / 2 ≤ B) : π * A ≤ 2 * π * B := by
  have h₁ : 2 * π * (A / 2) ≤ 2 * π * B := mul_le_mul_of_nonneg_left h two_pi_pos.le
  have e : 2 * π * (A / 2) = π * A := by
    ring1
  rwa [e] at h₁

lemma sq_apply_le_of_posSemidef {n : Matrix (Fin 2) (Fin 2) ℚ} (hn : n.PosSemidef) :
    n 0 1 ^ 2 ≤ n 0 0 * n 1 1 := by
  have hs : n 1 0 = n 0 1 := by
    simpa using congrFun (congrFun hn.isHermitian 0) 1
  rcases eq_or_ne (n 1 1) 0 with h | h
  · rw [apply_zero_one_eq_zero hn h, h]
    simp
  have h₁ : 0 < n 1 1 := lt_of_le_of_ne hn.diag_nonneg h.symm
  have hv : 0 ≤ star ![n 1 1, -n 0 1] ⬝ᵥ n *ᵥ ![n 1 1, -n 0 1] :=
    hn.dotProduct_mulVec_nonneg ![n 1 1, -n 0 1]
  simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two, cons_val_zero, cons_val_one,
    hs] at hv
  nlinarith

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {f : SiegelUpperHalfSpace (Fin 2) → V} {a : dualLattice Γ → V}
    {Z : SiegelUpperHalfSpace (Fin 2)}

private lemma norm_fourierExp_le (n : dualLattice Γ)
    (hn : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) (hZ : Z ∈ siegelSet) : ‖fourierExp n Z‖ ≤
      rexp (-(π * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) * (Z.val 0 0).im +
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) * (Z.val 1 1).im))) := by
  have hs : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 :=
    congrFun (congrFun n.2.1 0) 1
  have hZs : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  have h₀ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) := by
    exact_mod_cast hn.diag_nonneg
  have h₁ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    exact_mod_cast hn.diag_nonneg
  have hd : ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℝ) ^ 2 ≤
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) * ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    have h : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 ^ 2 ≤
        (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 * (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 :=
      sq_apply_le_of_posSemidef hn
    exact_mod_cast h
  rw [norm_fourierExp, hs, hZs, Real.exp_le_exp]
  exact neg_le_neg (pi_mul_le (half_add_le h₀ h₁ hd hZ.2.1 hZ.2.2.1))

private lemma two_fifths_mem : (2 / 5 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
  norm_num

private lemma norm_fourierExp_scalarPoint (n : dualLattice Γ) :
    ‖fourierExp n (scalarPoint ⟨2 / 5, two_fifths_mem⟩)‖ =
      rexp (-(π * (4 / 5 * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) +
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ))))) := by
  rw [norm_fourierExp]
  congr 1
  simp [scalarPoint, diagPoint]
  ring1

/-- **A positive semidefinite Fourier expansion is bounded on the Siegel set.** -/
lemma exists_norm_dual_le_of_posSemidef (ha : HasSiegelFourierExpansion Γ f a)
    (hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) (φ : Dual ℂ V) :
    ∃ C, 0 ≤ C ∧ ∀ Z ∈ siegelSet, ‖φ (f Z)‖ ≤ C := by
  have hs : Summable fun n ↦ ‖fourierExp n (scalarPoint ⟨2 / 5, two_fifths_mem⟩) * φ (a n)‖ :=
    (ha _ φ).summable.norm
  refine ⟨_, tsum_nonneg fun n ↦ norm_nonneg _, fun Z hZ ↦ (ha Z φ).norm_le_of_bounded hs.hasSum
    fun n ↦ ?_⟩
  by_cases hn : a n = 0
  · simp [hn]
  have hn' : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef := hpsd n hn
  rw [norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_fourierExp_le n hn' hZ).trans ?_) (norm_nonneg _)
  rw [norm_fourierExp_scalarPoint, Real.exp_le_exp]
  have h₀ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) := by
    exact_mod_cast hn'.diag_nonneg
  have h₁ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    exact_mod_cast hn'.diag_nonneg
  exact neg_le_neg <| mul_le_mul_of_nonneg_left (scalar_le_of_le h₀ h₁
    (four_fifths_le_im_zero_zero hZ) (four_fifths_le_im_one_one hZ)) Real.pi_pos.le

/-- **A positive definite Fourier expansion decays exponentially on the Siegel set**: if `a(n) ≠ 0`
only for positive semidefinite `n` with `n₀₀, n₁₁ ≥ ε`, then `f` decays like
`e^{-πε(y₀₀ + y₁₁)}`. -/
lemma exists_norm_dual_le_of_posDef (ha : HasSiegelFourierExpansion Γ f a) {ε : ℚ}
    (hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hn₀ : ∀ n, a n ≠ 0 → ε ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0)
    (hn₁ : ∀ n, a n ≠ 0 → ε ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1) (φ : Dual ℂ V) : ∃ C, 0 ≤ C ∧
      ∀ Z ∈ siegelSet, ‖φ (f Z)‖ ≤ C * rexp (-(π * ε) * ((Z.val 0 0).im + (Z.val 1 1).im)) := by
  have hs : Summable fun n ↦ ‖fourierExp n (scalarPoint ⟨2 / 5, two_fifths_mem⟩) * φ (a n)‖ :=
    (ha _ φ).summable.norm
  refine ⟨rexp (π * ε * (8 / 5)) *
    ∑' n, ‖fourierExp n (scalarPoint ⟨2 / 5, two_fifths_mem⟩) * φ (a n)‖,
      mul_nonneg (Real.exp_nonneg _) (tsum_nonneg fun n ↦ norm_nonneg _), fun Z hZ ↦ ?_⟩
  have hb : HasSum (fun n ↦ rexp (-(π * ε) * ((Z.val 0 0).im + (Z.val 1 1).im)) *
      (rexp (π * ε * (8 / 5)) * ‖fourierExp n (scalarPoint ⟨2 / 5, two_fifths_mem⟩) * φ (a n)‖))
      (rexp (-(π * ε) * ((Z.val 0 0).im + (Z.val 1 1).im)) * (rexp (π * ε * (8 / 5)) *
        ∑' n, ‖fourierExp n (scalarPoint ⟨2 / 5, two_fifths_mem⟩) * φ (a n)‖)) :=
    (hs.hasSum.mul_left _).mul_left _
  rw [mul_comm]
  refine (ha Z φ).norm_le_of_bounded hb fun n ↦ ?_
  by_cases hn : a n = 0
  · simp [hn]
  have hn' : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef := hpsd n hn
  rw [norm_mul, norm_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ((norm_fourierExp_le n hn' hZ).trans ?_) (norm_nonneg _)
  rw [norm_fourierExp_scalarPoint, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h₀ : ((ε : ℚ) : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) := by
    exact_mod_cast hn₀ n hn
  have h₁ : ((ε : ℚ) : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
    exact_mod_cast hn₁ n hn
  exact exponent_le h₀ h₁ (four_fifths_le_im_zero_zero hZ) (four_fifths_le_im_one_one hZ)

/-- **A positive definite Fourier expansion decays exponentially on the Siegel set, also after a
transformation `T` with `Im T(Z) = s A (Im Z) Aᵀ`**, for a rational `s > 0`, an invertible rational
matrix `A` and a subgroup whose translation lattice contains the `x xᵀ` for `x` integral. The term
of `n` depends on `n' = s Aᵀ n A`, which is positive definite with diagonal entries bounded below
by `s / m²`, for an integer `m ≠ 0` with `m A` integral. -/
lemma exists_norm_dual_comp_le_of_posDef (ha : HasSiegelFourierExpansion Γ f a)
    (hL : ∀ x : Fin 2 → ℤ, (vecMulVec x x).map (Int.cast : ℤ → ℚ) ∈ translationLattice Γ)
    (hpd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef) {A : Matrix (Fin 2) (Fin 2) ℚ}
    (hA : A.det ≠ 0) {s : ℚ} (hs : 0 < s)
    {T : SiegelUpperHalfSpace (Fin 2) → SiegelUpperHalfSpace (Fin 2)}
    (hT : ∀ Z i j, ((T Z).val i j).im = s * ∑ k, ∑ l, (A i k : ℝ) * (Z.val k l).im * (A j l : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ φ : Dual ℂ V, ∃ C, 0 ≤ C ∧ ∀ Z ∈ siegelSet, ‖φ (f (T Z))‖ ≤
      C * rexp (-ε * ((Z.val 0 0).im + (Z.val 1 1).im)) := by
  rcases IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun p : Fin 2 × Fin 2 ↦ A p.1 p.2) with ⟨m, hm⟩
  choose B hB using hm
  have hm₀ : ((m : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero m)
  have hB' (i k : Fin 2) : ((B (i, k) : ℤ) : ℚ) = ((m : ℤ) : ℚ) * A i k := by
    simpa using hB (i, k)
  have hinj : Function.Injective A.mulVec :=
    mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det A).mpr hA.isUnit)
  let n' (n : dualLattice Γ) : Matrix (Fin 2) (Fin 2) ℚ :=
    s • (Aᵀ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A)
  have hn'pd (n : dualLattice Γ) (hn : a n ≠ 0) : (n' n).PosDef := by
    have h : (Aᴴ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A).PosDef :=
      (hpd n hn).conjTranspose_mul_mul_same hinj
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact h.smul hs
  have hdiag (n : dualLattice Γ) (hn : a n ≠ 0) (c : Fin 2) : s / ((m : ℤ) : ℚ) ^ 2 ≤ n' n c c := by
    rcases n.2.2 _ (hL fun i ↦ B (i, c)) with ⟨z, hz⟩
    have hq : ((m : ℤ) : ℚ) ^ 2 * (Aᵀ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A) c c = z := by
      rw [← hz]
      simp [trace, Matrix.mul_apply, vecMulVec_apply, hB']
      ring1
    have hpos : 0 < (Aᵀ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A) c c := by
      have h : 0 < (Aᴴ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A) c c :=
        ((hpd n hn).conjTranspose_mul_mul_same hinj).diag_pos (i := c)
      rwa [conjTranspose_eq_transpose_of_trivial] at h
    have hz₀ : 0 < z := by
      have h : (0 : ℚ) < z := hq ▸ mul_pos (by positivity) hpos
      exact_mod_cast h
    have hz₁ : (1 : ℚ) ≤ z := by
      exact_mod_cast hz₀
    have h₂ : (((m : ℤ) : ℚ) ^ 2)⁻¹ ≤ (Aᵀ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A) c c := by
      rw [inv_le_iff_one_le_mul₀' (by positivity), hq]
      exact hz₁
    simpa [n', div_eq_mul_inv] using mul_le_mul_of_nonneg_left h₂ hs.le
  have hnorm (n : dualLattice Γ) (Z : SiegelUpperHalfSpace (Fin 2)) : ‖fourierExp n (T Z)‖ =
      rexp (-(2 * π * ((n' n 0 0 : ℝ) * (Z.val 0 0).im + (n' n 0 1 : ℝ) * (Z.val 1 0).im +
        ((n' n 1 0 : ℝ) * (Z.val 0 1).im + (n' n 1 1 : ℝ) * (Z.val 1 1).im)))) := by
    rw [norm_fourierExp, hT, hT, hT, hT]
    congr 3
    simp [n', Matrix.mul_apply]
    ring1
  generalize hZ₀ : scalarPoint ⟨2 / 5, two_fifths_mem⟩ = Z₀
  have hZ₀' (i j : Fin 2) : (Z₀.val i j).im = if i = j then 2 / 5 else 0 := by
    rw [← hZ₀]
    fin_cases i <;> fin_cases j <;> simp [scalarPoint, diagPoint]
  have hbase (n : dualLattice Γ) :
      ‖fourierExp n (T Z₀)‖ = rexp (-(π * (4 / 5 * ((n' n 0 0 : ℝ) + (n' n 1 1 : ℝ))))) := by
    rw [hnorm]
    congr 1
    simp [hZ₀']
    ring1
  generalize hε : ((s / ((m : ℤ) : ℚ) ^ 2 : ℚ) : ℝ) = ε
  have hε₀ : 0 < ε := by
    have h : 0 < s / ((m : ℤ) : ℚ) ^ 2 := div_pos hs (by positivity)
    rw [← hε]
    exact_mod_cast h
  refine ⟨π * ε, mul_pos Real.pi_pos hε₀, fun φ ↦ ?_⟩
  have hsum : Summable fun n ↦ ‖fourierExp n (T Z₀) * φ (a n)‖ :=
    (ha _ φ).summable.norm
  refine ⟨rexp (π * ε * (8 / 5)) * ∑' n, ‖fourierExp n (T Z₀) * φ (a n)‖,
    mul_nonneg (Real.exp_nonneg _) (tsum_nonneg fun n ↦ norm_nonneg _), fun Z hZ ↦ ?_⟩
  have hb : HasSum (fun n ↦ rexp (-(π * ε) * ((Z.val 0 0).im + (Z.val 1 1).im)) *
      (rexp (π * ε * (8 / 5)) * ‖fourierExp n (T Z₀) * φ (a n)‖))
      (rexp (-(π * ε) * ((Z.val 0 0).im + (Z.val 1 1).im)) * (rexp (π * ε * (8 / 5)) *
        ∑' n, ‖fourierExp n (T Z₀) * φ (a n)‖)) :=
    (hsum.hasSum.mul_left _).mul_left _
  rw [mul_comm]
  refine (ha (T Z) φ).norm_le_of_bounded hb fun n ↦ ?_
  by_cases hn : a n = 0
  · simp [hn]
  rw [norm_mul, norm_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hN : (n' n).PosSemidef := (hn'pd n hn).posSemidef
  have hs₁ : n' n 1 0 = n' n 0 1 := by
    simpa using congrFun (congrFun hN.isHermitian 0) 1
  have hZs : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  have h₀ : ε ≤ (n' n 0 0 : ℝ) := by
    rw [← hε]
    exact_mod_cast hdiag n hn 0
  have h₁ : ε ≤ (n' n 1 1 : ℝ) := by
    rw [← hε]
    exact_mod_cast hdiag n hn 1
  have hd : (n' n 0 1 : ℝ) ^ 2 ≤ (n' n 0 0 : ℝ) * (n' n 1 1 : ℝ) := by
    exact_mod_cast sq_apply_le_of_posSemidef hN
  rw [hnorm, hbase, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, hs₁, hZs]
  exact (neg_le_neg (pi_mul_le (half_add_le (hε₀.le.trans h₀) (hε₀.le.trans h₁) hd hZ.2.1
    hZ.2.2.1))).trans (exponent_le h₀ h₁ (four_fifths_le_im_zero_zero hZ)
      (four_fifths_le_im_one_one hZ))

/-- **The constant term of a positive semidefinite Fourier expansion, after a transformation `T`
with `Im T(Z) = s A (Im Z) Aᵀ`**: `φ(f(T(diag(it, it)))) → φ(a(0))` as `t → ∞`, by dominated
convergence: the term of `n` has absolute value `e^{-2πt tr(n')} |φ(a(n))|` with `n' = s Aᵀ n A`. -/
lemma tendsto_dual_comp_scalarPoint (ha : HasSiegelFourierExpansion Γ f a)
    (hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) {A : Matrix (Fin 2) (Fin 2) ℚ}
    (hA : A.det ≠ 0) {s : ℚ} (hs : 0 < s)
    {T : SiegelUpperHalfSpace (Fin 2) → SiegelUpperHalfSpace (Fin 2)}
    (hT : ∀ Z i j, ((T Z).val i j).im = s * ∑ k, ∑ l, (A i k : ℝ) * (Z.val k l).im * (A j l : ℝ))
    (φ : Dual ℂ V) : Filter.Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (f (T (scalarPoint t))))
      Filter.atTop (nhds (φ (a 0))) := by
  classical
  have ht : Filter.Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ (t : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_Ioi_atTop.mp Filter.tendsto_id
  let n' (n : dualLattice Γ) : Matrix (Fin 2) (Fin 2) ℚ :=
    s • (Aᵀ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A)
  have hn'psd (n : dualLattice Γ) (hn : a n ≠ 0) : (n' n).PosSemidef := by
    have h : (Aᴴ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A).PosSemidef :=
      (hpsd n hn).conjTranspose_mul_mul_same A
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact h.smul hs.le
  have hnorm (n : dualLattice Γ) (t : Set.Ioi (0 : ℝ)) : ‖fourierExp n (T (scalarPoint t))‖ =
      rexp (-(2 * π * ((t : ℝ) * ((n' n 0 0 : ℝ) + (n' n 1 1 : ℝ))))) := by
    rw [norm_fourierExp, hT, hT, hT, hT]
    congr 3
    simp [n', Matrix.mul_apply, scalarPoint, diagPoint]
    ring1
  have hnn (n : dualLattice Γ) (hn : a n ≠ 0) : (0 : ℝ) ≤ (n' n 0 0 : ℝ) + (n' n 1 1 : ℝ) := by
    have h₀ : (0 : ℝ) ≤ (n' n 0 0 : ℝ) := by
      exact_mod_cast (hn'psd n hn).diag_nonneg
    have h₁ : (0 : ℝ) ≤ (n' n 1 1 : ℝ) := by
      exact_mod_cast (hn'psd n hn).diag_nonneg
    exact add_nonneg h₀ h₁
  have hpos (n : dualLattice Γ) (hn : a n ≠ 0) (hn₀ : n ≠ 0) :
      0 < (n' n 0 0 : ℝ) + (n' n 1 1 : ℝ) := by
    refine lt_of_le_of_ne (hnn n hn) fun h ↦ hn₀ ?_
    have h₀ : (0 : ℝ) ≤ (n' n 0 0 : ℝ) := by
      exact_mod_cast (hn'psd n hn).diag_nonneg
    have h₁ : (0 : ℝ) ≤ (n' n 1 1 : ℝ) := by
      exact_mod_cast (hn'psd n hn).diag_nonneg
    rcases (add_eq_zero_iff_of_nonneg h₀ h₁).mp h.symm with ⟨h₂, h₃⟩
    have e₀ : n' n 0 0 = 0 := by
      exact_mod_cast h₂
    have e₁ : n' n 1 1 = 0 := by
      exact_mod_cast h₃
    have e₂ : n' n 0 1 = 0 := apply_zero_one_eq_zero (hn'psd n hn) e₁
    have e₃ : n' n 1 0 = 0 := by
      rw [← e₂]
      simpa using congrFun (congrFun (hn'psd n hn).isHermitian 0) 1
    have hz : n' n = 0 := by
      ext x y
      fin_cases x <;> fin_cases y <;> simp [e₀, e₁, e₂, e₃]
    have hu : IsUnit A := (isUnit_iff_isUnit_det A).mpr hA.isUnit
    have hut : IsUnit Aᵀ := by
      rw [isUnit_iff_isUnit_det, det_transpose]
      exact hA.isUnit
    have hz₁ : Aᵀ * (n : Matrix (Fin 2) (Fin 2) ℚ) * A = 0 :=
      (smul_eq_zero.mp hz).resolve_left hs.ne'
    have hz₂ : (n : Matrix (Fin 2) (Fin 2) ℚ) = 0 :=
      hut.mul_right_eq_zero.mp (hu.mul_left_eq_zero.mp hz₁)
    exact Subtype.ext hz₂
  have hlim (n : dualLattice Γ) : Filter.Tendsto (fun t : Set.Ioi (0 : ℝ) ↦
      fourierExp n (T (scalarPoint t)) * φ (a n)) Filter.atTop
        (nhds (if n = 0 then φ (a 0) else 0)) := by
    split_ifs with hn₀
    · subst hn₀
      simp [fourierExp]
    by_cases hc : a n = 0
    · simp [hc]
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simp only [norm_mul, hnorm]
    have h₂ : Filter.Tendsto (fun t : Set.Ioi (0 : ℝ) ↦
        rexp (-(2 * π * ((t : ℝ) * ((n' n 0 0 : ℝ) + (n' n 1 1 : ℝ)))))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <|
        (ht.atTop_mul_const (hpos n hc hn₀)).const_mul_atTop two_pi_pos
    simpa using h₂.mul_const ‖φ (a n)‖
  have hb : ∀ᶠ t : Set.Ioi (0 : ℝ) in Filter.atTop, ∀ n : dualLattice Γ,
      ‖fourierExp n (T (scalarPoint t)) * φ (a n)‖ ≤
        ‖fourierExp n (T (scalarPoint tOne)) * φ (a n)‖ := by
    filter_upwards [ht.eventually_ge_atTop 1] with t ht₁ n
    by_cases hc : a n = 0
    · simp [hc]
    rw [norm_mul, norm_mul, hnorm, hnorm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h₃ :
        (1 : ℝ) * ((n' n 0 0 : ℝ) + (n' n 1 1 : ℝ)) ≤ (t : ℝ) * ((n' n 0 0 : ℝ) + (n' n 1 1 : ℝ)) :=
      mul_le_mul_of_nonneg_right ht₁ (hnn n hc)
    exact neg_le_neg (mul_le_mul_of_nonneg_left h₃ two_pi_pos.le)
  have key : Filter.Tendsto (fun t : Set.Ioi (0 : ℝ) ↦
      ∑' n, fourierExp n (T (scalarPoint t)) * φ (a n)) Filter.atTop
        (nhds (∑' n : dualLattice Γ, if n = 0 then φ (a 0) else 0)) :=
    tendsto_tsum_of_dominated_convergence (ha _ φ).summable.norm hlim hb
  rw [tsum_ite_eq] at key
  exact key.congr fun t ↦ (ha _ φ).tsum_eq

end Fourier

/-! ### The Petersson integrand on the Siegel set -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

/-- The sesquilinear form `b` is **moderate** for the representation `ρ` of `GL(2, ℂ)`: the
coefficients `b(ρ(Im τ) v, w)` are continuous in `τ` and grow at most polynomially on the Siegel
set, in `1 + y₀₀ + y₁₁`, with an exponent independent of `v, w`. This is what the convergence of the
Petersson product needs of the weight; it holds for `ρ_{k,j}`
(`SiegelUpperHalfSpace.isModerateForm_rhoKJ`). -/
structure IsModerateForm : Prop where
  continuous (v w : V) : Continuous fun τ : SiegelUpperHalfSpace (Fin 2) ↦ b (ρ (imGL τ) v) w
  exists_bound : ∃ N : ℕ, ∀ v w : V, ∃ C : ℝ, ∀ τ ∈ siegelSet,
    ‖b (ρ (imGL τ) v) w‖ ≤ C * (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N

variable {ρ b} {f g : SiegelUpperHalfSpace (Fin 2) → V}

/-- **The Petersson integrand of modular forms is invariant** under the transformations induced by
`Γ`, for an admissible form. -/
lemma peterssonIntegrand_map_smul {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)}
    (hadm : IsAdmissibleForm ρ b) (hf : f ∈ modularForms ρ Γ 1) (hg : g ∈ modularForms ρ Γ 1)
    (γ : transformationGroup Γ) (τ : SiegelUpperHalfSpace (Fin 2)) :
    peterssonIntegrand ρ b f g (γ • τ) = peterssonIntegrand ρ b f g τ := by
  rcases γ with ⟨_, γ, hγ, rfl⟩
  have hc : ‖(((1 : Γ →* ℂˣ) ⟨γ, hγ⟩ : ℂˣ) : ℂ)‖ = 1 := by
    simp
  exact peterssonIntegrand_smul τ f g hadm hc (hf.2 ⟨γ, hγ⟩) (hg.2 ⟨γ, hγ⟩)

open Norms in
open scoped MatrixOrder L2Operator in
lemma exists_star_mul_eq_imGL (τ : SiegelUpperHalfSpace (Fin 2)) :
    ∃ M : GL (Fin 2) ℂ, imGL τ = star M * M := by
  rcases CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    (posDef_map_ofReal_iff.mpr τ.posDef_im).isStrictlyPositive with ⟨y, hy, h⟩
  lift y to GL (Fin 2) ℂ using hy
  exact ⟨y, Units.ext h⟩

variable (b) in
/-- **The Petersson form is positive** for an admissible positive definite `b`:
`b(ρ(Y) v, v) = b(ρ(M) v, ρ(M) v) > 0` for `Y = Mᴴ M`. -/
lemma peterssonForm_pos (hadm : IsAdmissibleForm ρ b) (hpos : ∀ v, v ≠ 0 → 0 < b v v)
    (τ : SiegelUpperHalfSpace (Fin 2)) {v : V} (hv : v ≠ 0) : 0 < b (ρ (imGL τ) v) v := by
  rcases exists_star_mul_eq_imGL τ with ⟨M, hM⟩
  rw [hM, map_mul, End.mul_apply, hadm, star_star]
  refine hpos _ fun h ↦ hv ?_
  rw [← ρ.inv_self_apply M v, h, map_zero]

variable [FiniteDimensional ℂ V]

private lemma peterssonIntegrand_eq_sum (τ : SiegelUpperHalfSpace (Fin 2)) :
    peterssonIntegrand ρ b f g τ = ∑ i, ∑ l, (finBasis ℂ V).coord i (f τ) *
      conj ((finBasis ℂ V).coord l (g τ)) * b (ρ (imGL τ) (finBasis ℂ V i)) (finBasis ℂ V l) := by
  conv_lhs => rw [peterssonIntegrand_apply, ← (finBasis ℂ V).sum_repr (f τ),
    ← (finBasis ℂ V).sum_repr (g τ)]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    smul_eq_mul, Basis.coord_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  ring1

lemma continuous_peterssonIntegrand_of_dual (hb : IsModerateForm ρ b)
    (hf : ∀ φ : Dual ℂ V, Continuous fun τ ↦ φ (f τ))
    (hg : ∀ φ : Dual ℂ V, Continuous fun τ ↦ φ (g τ)) :
    Continuous (peterssonIntegrand ρ b f g) := by
  rw [funext peterssonIntegrand_eq_sum]
  exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun l _ ↦
    ((hf _).mul (Complex.continuous_conj.comp (hg _))).mul (hb.continuous _ _)

/-- **The Petersson integrand of holomorphic functions is continuous**, for a moderate form. -/
lemma continuous_peterssonIntegrand (hb : IsModerateForm ρ b) (hf : IsHolomorphic f)
    (hg : IsHolomorphic g) : Continuous (peterssonIntegrand ρ b f g) :=
  continuous_peterssonIntegrand_of_dual hb hf.continuous_dual hg.continuous_dual

/-- **The Petersson integrand on the Siegel set**: a bound `|φ(f)| |ψ(g)| ≤ C A` for all linear
forms `φ, ψ` gives `|b(ρ(Im τ) f(τ), g(τ))| ≤ C' A(τ) (1 + y₀₀ + y₁₁)^N`, for a moderate form
`b`. -/
lemma exists_norm_peterssonIntegrand_le (hb : IsModerateForm ρ b)
    {A : SiegelUpperHalfSpace (Fin 2) → ℝ}
    (hfg : ∀ φ ψ : Dual ℂ V, ∃ C, ∀ τ ∈ siegelSet, ‖φ (f τ)‖ * ‖ψ (g τ)‖ ≤ C * A τ) :
    ∃ (C : ℝ) (N : ℕ), ∀ τ ∈ siegelSet, ‖peterssonIntegrand ρ b f g τ‖ ≤
      C * A τ * (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N := by
  rcases hb.exists_bound with ⟨N, hN⟩
  choose C₁ hC₁ using fun i l ↦ hN (finBasis ℂ V i) (finBasis ℂ V l)
  choose C₂ hC₂ using fun i l ↦ hfg ((finBasis ℂ V).coord i) ((finBasis ℂ V).coord l)
  refine ⟨∑ i, ∑ l, C₂ i l * C₁ i l, N, fun τ hτ ↦ ?_⟩
  rw [peterssonIntegrand_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm (i l : Fin (finrank ℂ V)) : ‖(finBasis ℂ V).coord i (f τ) *
      conj ((finBasis ℂ V).coord l (g τ)) * b (ρ (imGL τ) (finBasis ℂ V i)) (finBasis ℂ V l)‖ ≤
        C₂ i l * C₁ i l * A τ * (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N := by
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    have h₁ : ‖(finBasis ℂ V).coord i (f τ)‖ * ‖(finBasis ℂ V).coord l (g τ)‖ ≤ C₂ i l * A τ :=
      hC₂ i l τ hτ
    have h₂ : ‖b (ρ (imGL τ) (finBasis ℂ V i)) (finBasis ℂ V l)‖ ≤
        C₁ i l * (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ N :=
      hC₁ i l τ hτ
    have h₃ : 0 ≤ C₂ i l * A τ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans h₁
    refine (mul_le_mul h₁ h₂ (norm_nonneg _) h₃).trans_eq ?_
    ring1
  refine (Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ ↦ hterm i l)).trans_eq ?_
  simp only [Finset.sum_mul]

variable {s : Set (SiegelUpperHalfSpace (Fin 2))}

/-- **Integrability of the Petersson integrand from its decay on the Siegel set**: if `φ(f) ψ(g)`
decays exponentially on the Siegel set, for all linear forms `φ, ψ`, the Petersson integrand of the
modular forms `f, g` on `Sp(4, ℤ)` is integrable on every fundamental domain. -/
lemma integrableOn_peterssonIntegrand_of_decay (hb : IsModerateForm ρ b)
    (hadm : IsAdmissibleForm ρ b) (hf : f ∈ modularForms ρ (integral (Fin 2)) 1)
    (hg : g ∈ modularForms ρ (integral (Fin 2)) 1) {c : ℝ} (hc : 0 < c)
    (hfg : ∀ φ ψ : Dual ℂ V, ∃ C, ∀ τ ∈ siegelSet, ‖φ (f τ)‖ * ‖ψ (g τ)‖ ≤
      C * rexp (-c * ((τ.val 0 0).im + (τ.val 1 1).im)))
    (hs : IsFundamentalDomain (transformationGroup (integral (Fin 2))) s
      (invariantMeasure (Fin 2))) :
    IntegrableOn (peterssonIntegrand ρ b f g) s (invariantMeasure (Fin 2)) := by
  refine hs.integrableOn_of_setLIntegral_lt_top (t := siegelSet)
    (continuous_peterssonIntegrand hb hf.1 hg.1).aestronglyMeasurable
    (fun γ τ ↦ by rw [peterssonIntegrand_map_smul hadm hf hg])
    (.of_forall exists_smul_mem_siegelSet_transformationGroup) ?_
  rcases exists_norm_peterssonIntegrand_le hb hfg with ⟨C, N, hC⟩
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_siegelSet fun τ hτ ↦ ?_)
    (lintegral_siegelSet_mul_pow_lt_top C N hc)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC τ hτ)

/-! ### Modular forms and cusp forms on `Sp(4, ℤ)` -/

lemma exists_intCast_eq_apply (n : dualLattice (integral (Fin 2))) (i : Fin 2) :
    ∃ z : ℤ, (n : Matrix (Fin 2) (Fin 2) ℚ) i i = z := by
  have hs : (single i i (1 : ℚ)) ∈ translationLattice (integral (Fin 2)) := by
    refine ⟨transpose_single i i 1, SymplecticGroup.map (Int.castRingHom ℚ)
      (symTranslation _ (transpose_single i i 1)), ⟨_, trivial, rfl⟩, ?_⟩
    · rw [SymplecticGroup.coe_map_apply, coe_symTranslation, fromBlocks_map]
      simp
      ext a c
      by_cases h : i = a ∧ i = c <;> simp [single_apply]
  rcases n.2.2 _ hs with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [← hz, trace_single_mul]
  simp

/-- **A modular form on `Sp(4, ℤ)` is bounded on the Siegel set**, through every linear form. -/
lemma exists_norm_dual_le_of_mem_modularForms (hf : f ∈ modularForms ρ (integral (Fin 2)) 1)
    (φ : Dual ℂ V) : ∃ C, 0 ≤ C ∧ ∀ Z ∈ siegelSet, ‖φ (f Z)‖ ≤ C := by
  rcases exists_hasSiegelFourierExpansion ρ (isArithmetic_integral (Fin 2)) hf with ⟨a, ha⟩
  exact exists_norm_dual_le_of_posSemidef ha (koecherPrinciple ρ (isArithmetic_integral (Fin 2))
    (by simp) f hf a ha) φ

/-- **A cusp form on `Sp(4, ℤ)` decays exponentially on the Siegel set**, through every linear
form. -/
lemma exists_norm_dual_le_of_mem_cuspForms (hf : f ∈ cuspForms ρ (integral (Fin 2)) 1)
    (φ : Dual ℂ V) : ∃ C, 0 ≤ C ∧ ∀ Z ∈ siegelSet, ‖φ (f Z)‖ ≤
      C * rexp (-π * ((Z.val 0 0).im + (Z.val 1 1).im)) := by
  rcases exists_hasSiegelFourierExpansion ρ (isArithmetic_integral (Fin 2)) hf.1 with ⟨a, ha⟩
  have hv : SiegelOperatorVanishes f := by
    have h : SiegelOperatorVanishes (slash ρ (map (algebraMap ℚ ℝ) 1) f) := hf.2 1
    rwa [map_one, slash_one] at h
  have hpd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef :=
    posDef_of_siegelOperatorVanishes hf.1 ha hv
  have hn (n : dualLattice (integral (Fin 2))) (hn : a n ≠ 0) (i : Fin 2) :
      1 ≤ (n : Matrix (Fin 2) (Fin 2) ℚ) i i := by
    rcases exists_intCast_eq_apply n i with ⟨z, hz⟩
    have h₀ : 0 < (n : Matrix (Fin 2) (Fin 2) ℚ) i i := (hpd n hn).diag_pos
    rw [hz] at h₀ ⊢
    have h₁ : 0 < z := by
      exact_mod_cast h₀
    exact_mod_cast h₁
  simpa using exists_norm_dual_le_of_posDef ha (ε := 1) (fun n hn ↦ (hpd n hn).posSemidef)
    (fun n h ↦ hn n h 0) (fun n h ↦ hn n h 1) φ

lemma vecMulVec_mem_translationLattice (x : Fin 2 → ℤ) :
    (vecMulVec x x).map (Int.cast : ℤ → ℚ) ∈ translationLattice (integral (Fin 2)) := by
  have hS : (vecMulVec x x)ᵀ = vecMulVec x x := by
    ext i j
    simp [vecMulVec_apply, mul_comm]
  refine ⟨by rw [← transpose_map, hS],
    SymplecticGroup.map (Int.castRingHom ℚ) (symTranslation _ hS), ⟨_, trivial, rfl⟩, ?_⟩
  rw [SymplecticGroup.coe_map_apply, coe_symTranslation, fromBlocks_map]
  simp

variable {F G : SiegelUpperHalfSpace (Fin 2) → V}

/-- **Convergence of the Petersson product on `Sp(4, ℤ)`**: for a moderate admissible form, the
Petersson integrand of a modular form `F` and a cusp form `G` is integrable on every fundamental
domain. -/
lemma integrableOn_peterssonIntegrand (hb : IsModerateForm ρ b) (hadm : IsAdmissibleForm ρ b)
    (hF : F ∈ modularForms ρ (integral (Fin 2)) 1) (hG : G ∈ cuspForms ρ (integral (Fin 2)) 1)
    (hs : IsFundamentalDomain (transformationGroup (integral (Fin 2))) s
      (invariantMeasure (Fin 2))) :
    IntegrableOn (peterssonIntegrand ρ b F G) s (invariantMeasure (Fin 2)) := by
  refine integrableOn_peterssonIntegrand_of_decay hb hadm hF hG.1 Real.pi_pos (fun φ ψ ↦ ?_) hs
  rcases exists_norm_dual_le_of_mem_modularForms hF φ with ⟨C₁, hC₁, h₁⟩
  rcases exists_norm_dual_le_of_mem_cuspForms hG ψ with ⟨C₂, hC₂, h₂⟩
  refine ⟨C₁ * C₂, fun τ hτ ↦ ?_⟩
  rw [mul_assoc]
  exact mul_le_mul (h₁ τ hτ) (h₂ τ hτ) (norm_nonneg _) hC₁

lemma integrableOn_peterssonIntegrand_of_cuspForms (hb : IsModerateForm ρ b)
    (hadm : IsAdmissibleForm ρ b) (hF : F ∈ cuspForms ρ (integral (Fin 2)) 1)
    (hG : G ∈ modularForms ρ (integral (Fin 2)) 1)
    (hs : IsFundamentalDomain (transformationGroup (integral (Fin 2))) s
      (invariantMeasure (Fin 2))) :
    IntegrableOn (peterssonIntegrand ρ b F G) s (invariantMeasure (Fin 2)) := by
  refine integrableOn_peterssonIntegrand_of_decay hb hadm hF.1 hG Real.pi_pos (fun φ ψ ↦ ?_) hs
  rcases exists_norm_dual_le_of_mem_cuspForms hF φ with ⟨C₁, hC₁, h₁⟩
  rcases exists_norm_dual_le_of_mem_modularForms hG ψ with ⟨C₂, hC₂, h₂⟩
  refine ⟨C₁ * C₂, fun τ hτ ↦ ?_⟩
  rw [mul_right_comm]
  exact mul_le_mul (h₁ τ hτ) (h₂ τ hτ) (norm_nonneg _) (mul_nonneg hC₁ (Real.exp_nonneg _))

/-! ### Definiteness -/

/-- **The Petersson product is definite on the cusp forms on `Sp(4, ℤ)`**, for a moderate
admissible positive definite form `b`. -/
lemma isPeterssonDefinite_cuspForms (hb : IsModerateForm ρ b) (hadm : IsAdmissibleForm ρ b)
    (hpos : ∀ v, v ≠ 0 → 0 < b v v) :
    IsPeterssonDefinite (integral (Fin 2)) ρ b (cuspForms ρ (integral (Fin 2)) 1) :=
  IsPeterssonDefinite.of_integrableOn (fun τ _ hv ↦ peterssonForm_pos b hadm hpos τ hv)
    (exists_isFundamentalDomain (isArithmetic_integral (Fin 2))) (cuspForms_le_modularForms _ _ _)
    fun _ _ hf hg ↦ integrableOn_peterssonIntegrand hb hadm (cuspForms_le_modularForms _ _ _ hf) hg
      (isFundamentalDomain_fundamentalDomain (isArithmetic_integral (Fin 2)))

end SiegelUpperHalfSpace
