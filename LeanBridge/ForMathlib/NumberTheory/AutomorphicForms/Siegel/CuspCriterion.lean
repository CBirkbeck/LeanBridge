import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.FourierExistence
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.KoecherPrinciple
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParabolicDecomposition
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.VectorKlingenTerm
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The cusp condition on `Sp(4, ℤ)` from the Fourier expansion

A Siegel modular form `F` of degree `2` and weight `ρ` on `Sp(4, ℤ)` has a Fourier expansion
`F(Z) = ∑ a(n) e^{2πi tr(nZ)}` with `a(n) ≠ 0` only for positive semidefinite `n`
(`SiegelUpperHalfSpace.exists_hasSiegelFourierExpansion`, `SiegelUpperHalfSpace.koecherPrinciple`).
By dominated convergence, `F(diag(τ', it))` tends to `∑_{n₁₁ = 0} a(n) e^{2πi n₀₀ τ'}` as `t → ∞`.

If `Φ(F) = 0`, the uniqueness of Fourier expansions gives `a(n) = 0` for `n₁₁ = 0`. Every singular
positive semidefinite `n` is `Uᵀ n' U` for such an `n'` and some `U ∈ GL(2, ℤ)`, with
`a(Uᵀ n U) = ρ(Uᵀ) a(n)` (`SiegelUpperHalfSpace.apply_dualLevi`), so `a` is supported on the
positive definite `n`. Writing `γ ∈ Sp(4, ℚ)` as `γ = gp` with `g ∈ Sp(4, ℤ)` and `p` in the Siegel
parabolic subgroup, the positive definiteness gives `Φ(F ∣ γ) = Φ(F ∣ p) = 0`: on `Sp(4, ℤ)`, a form
with vanishing Siegel operator is a cusp form.

## Main definitions

* `SiegelUpperHalfSpace.phiTerm`: the term `d(n) e^{2πi n₀₀ z}` of the series of `Φ(F)`.

## Main results

* `SiegelUpperHalfSpace.tendsto_dual_smul_diagPoint_of_posDef`: a function with a positive definite
  Fourier expansion vanishes at `diag(τ', i∞)` after the Siegel parabolic subgroup.
* `SiegelUpperHalfSpace.siegelOperatorVanishes_slash_of_posDef`: `Φ(F ∣ p) = 0` for such a function.
* `SiegelUpperHalfSpace.isCuspForm_of_posDef`: a modular form on `Sp(4, ℤ)` with a positive definite
  expansion is a cusp form.
* `SiegelUpperHalfSpace.tendsto_dual_diagPoint`: the limit along `diag(τ', it)`.
* `SiegelUpperHalfSpace.eq_zero_of_tsum_phiTerm_eq_zero`: the uniqueness of the series of `Φ(F)`.
* `SiegelUpperHalfSpace.posDef_of_siegelOperatorVanishes`: `Φ(F) = 0` implies positive definite
  support.
* `SiegelUpperHalfSpace.isCuspForm_of_siegelOperatorVanishes`: `Φ(F) = 0` implies that `F` is a cusp
  form.
-/

open Complex Filter Matrix Module Real SymplecticGroup Topology

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {F : SiegelUpperHalfSpace (Fin 2) → V} {a : dualLattice Γ → V} (τ' : ℍ) (φ : Dual ℂ V)
    {P : symplecticGroup (Fin 2) ℝ}

/-! ### Binary quadratic forms -/

section Quadratic

variable {n : Matrix (Fin 2) (Fin 2) ℚ}

private lemma quad_pos (hn : n.PosDef) {x y : ℝ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < (n 0 0 : ℝ) * x ^ 2 + (n 0 1 : ℝ) * x * y + (n 1 0 : ℝ) * y * x + (n 1 1 : ℝ) * y ^ 2 := by
  have hs : n 1 0 = n 0 1 := by
    simpa using congrFun (congrFun hn.isHermitian 0) 1
  have h₀ : 0 < n 0 0 := by
    have h : 0 < star ![(1 : ℚ), 0] ⬝ᵥ n *ᵥ ![(1 : ℚ), 0] :=
      (posDef_iff_dotProduct_mulVec.mp hn).2 (by simp)
    simpa using h
  have hd : 0 < n.det := hn.det_pos
  rw [det_fin_two, hs] at hd
  have h₀' : (0 : ℝ) < n 0 0 := by
    exact_mod_cast h₀
  have hd' : (0 : ℝ) < n 0 0 * n 1 1 - n 0 1 * n 0 1 := by
    exact_mod_cast hd
  rw [hs]
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x ≠ 0 := hxy.resolve_right fun h ↦ h rfl
    have hx₂ : 0 < x ^ 2 := by
      positivity
    nlinarith
  · have hy₂ : 0 < y ^ 2 := by
      positivity
    have h4 : 0 < (n 0 0 : ℝ) * ((n 0 0 : ℝ) * x ^ 2 + (n 0 1 : ℝ) * x * y + (n 0 1 : ℝ) * y * x +
        (n 1 1 : ℝ) * y ^ 2) := by
      nlinarith [sq_nonneg ((n 0 0 : ℝ) * x + (n 0 1 : ℝ) * y), mul_pos hd' hy₂]
    exact (pos_iff_pos_of_mul_pos h4).mp h₀'

lemma apply_zero_one_eq_zero (hn : n.PosSemidef) (h : n 1 1 = 0) : n 0 1 = 0 := by
  have h₁ : star ![(0 : ℚ), 1] ⬝ᵥ n *ᵥ ![0, 1] = 0 := by
    simp [h]
  simpa using congrFun (hn.dotProduct_mulVec_zero_iff.mp h₁) 0

private lemma exists_isCoprime_mul_eq {p q : ℚ} (h : ¬(p = 0 ∧ q = 0)) :
    ∃ (x y : ℤ) (r : ℚ), IsCoprime x y ∧ r ≠ 0 ∧ p = r * x ∧ q = r * y := by
  have hp : (p.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.den_ne_zero
  have hq : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hg : 0 < (p.num * q.den).gcd (q.num * p.den) := by
    refine Nat.pos_of_ne_zero fun h₀ ↦ h ?_
    rcases Int.gcd_eq_zero_iff.mp h₀ with ⟨h₁, h₂⟩
    have e₁ : p.num = 0 := by
      simpa using h₁
    have e₂ : q.num = 0 := by
      simpa using h₂
    exact ⟨Rat.num_eq_zero.mp e₁, Rat.num_eq_zero.mp e₂⟩
  rcases Int.exists_gcd_one hg with ⟨x, y, hxy, hx, hy⟩
  have hg₀ : (((p.num * q.den).gcd (q.num * p.den) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hg.ne'
  refine ⟨x, y, ((p.num * q.den).gcd (q.num * p.den) : ℕ) / (p.den * q.den),
    Int.isCoprime_iff_gcd_eq_one.mpr hxy, div_ne_zero hg₀ (mul_ne_zero hp hq), ?_, ?_⟩
  · have e : (p.num : ℚ) * q.den = x * ((p.num * q.den).gcd (q.num * p.den) : ℕ) := by
      exact_mod_cast hx
    conv_lhs => rw [← Rat.num_div_den p]
    field_simp
    linear_combination e
  · have e : (q.num : ℚ) * p.den = y * ((p.num * q.den).gcd (q.num * p.den) : ℕ) := by
      exact_mod_cast hy
    conv_lhs => rw [← Rat.num_div_den q]
    field_simp
    linear_combination e

private lemma exists_isCoprime_quad_eq_zero (hd : n 0 0 * n 1 1 = n 0 1 * n 0 1) :
    ∃ x y : ℤ, IsCoprime x y ∧ n 0 0 * x ^ 2 + 2 * n 0 1 * x * y + n 1 1 * y ^ 2 = 0 := by
  by_cases h : n 0 1 = 0 ∧ -n 0 0 = 0
  · refine ⟨1, 0, isCoprime_one_left, ?_⟩
    simpa using h.2
  · rcases exists_isCoprime_mul_eq h with ⟨x, y, r, hxy, hr, hx, hy⟩
    refine ⟨x, y, hxy, mul_left_cancel₀ (pow_ne_zero 2 hr) ?_⟩
    have hx' : r * x = n 0 1 := hx.symm
    have hy' : r * y = -n 0 0 := hy.symm
    have e : r ^ 2 * (n 0 0 * x ^ 2 + 2 * n 0 1 * x * y + n 1 1 * y ^ 2) =
        n 0 0 * (r * x) ^ 2 + 2 * n 0 1 * (r * x) * (r * y) + n 1 1 * (r * y) ^ 2 := by
      ring1
    rw [e, hx', hy']
    linear_combination (n 0 0) * hd

end Quadratic

/-! ### Positive definite support -/

lemma norm_fourierExp (n : dualLattice Γ) (W : SiegelUpperHalfSpace (Fin 2)) : ‖fourierExp n W‖ =
    rexp (-(2 * π * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) * (W.val 0 0).im +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℝ) * (W.val 1 0).im +
        (((n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 : ℝ) * (W.val 0 1).im +
          ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) * (W.val 1 1).im)))) := by
  rw [fourierExp, Complex.norm_exp]
  congr 1
  simp [trace, Matrix.mul_apply]

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

private lemma rexp_mul_le {A B : ℝ} (hB : 0 ≤ B) {t : Set.Ioi (0 : ℝ)} (ht : tOne ≤ t) :
    rexp (-(2 * π * (A + t * B))) ≤ rexp (-(2 * π * (A + (tOne : ℝ) * B))) := by
  have h₁ : (1 : ℝ) ≤ t := ht
  have e : ((tOne : Set.Ioi (0 : ℝ)) : ℝ) = 1 :=
    rfl
  refine Real.exp_le_exp.mpr ?_
  rw [e]
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) hB, Real.pi_pos]

private lemma tendsto_rexp_mul {A B : ℝ} (hB : 0 < B) :
    Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ rexp (-(2 * π * (A + t * B)))) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ (t : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  exact Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <|
    (tendsto_atTop_add_const_left _ _ (ht.atTop_mul_const hB)).const_mul_atTop two_pi_pos

/-- **A function with a positive definite Fourier expansion vanishes at the cusp `diag(τ', i∞)`
after any element of the Siegel parabolic subgroup**: if `a(n) ≠ 0` only for positive definite `n`,
then `F(p diag(τ', it)) → 0` as `t → ∞`, for `p = (A, B; 0, D) ∈ Sp(4, ℝ)`. The term of `n` has
absolute value `|a(n)| e^{-2π(Im τ' Q(a₁) + t Q(a₂))}` with `Q(x) = xᵀnx` and `a₁, a₂` the columns
of `A`, and `Q(a₂) > 0`; dominated convergence concludes. -/
lemma tendsto_dual_smul_diagPoint_of_posDef (hP : P ∈ siegelParabolic (Fin 2) ℝ)
    (ha : HasSiegelFourierExpansion Γ F a)
    (hpd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef) :
    Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ φ (F (P • diagPoint τ' t))) atTop (𝓝 0) := by
  let Q : dualLattice Γ → Fin 2 → ℝ := fun n c ↦
    ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) * P.1.toBlocks₁₁ 0 c ^ 2 +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 : ℝ) * P.1.toBlocks₁₁ 0 c * P.1.toBlocks₁₁ 1 c +
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 : ℝ) * P.1.toBlocks₁₁ 1 c * P.1.toBlocks₁₁ 0 c +
          ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) * P.1.toBlocks₁₁ 1 c ^ 2
  have hnorm (n : dualLattice Γ) (t : Set.Ioi (0 : ℝ)) :
      ‖fourierExp n (P • diagPoint τ' t)‖ = rexp (-(2 * π * (τ'.im * Q n 0 + t * Q n 1))) := by
    rw [norm_fourierExp, im_smul_diagPoint τ' hP, im_smul_diagPoint τ' hP, im_smul_diagPoint τ' hP,
      im_smul_diagPoint τ' hP]
    congr 1
    ring1
  have hdet : P.1.toBlocks₂₂.det * P.1.toBlocks₁₁.det = 1 := by
    rw [← det_transpose P.1.toBlocks₁₁, ← det_mul, toBlocks₂₂_mul_transpose_toBlocks₁₁ hP, det_one]
  have hcol : P.1.toBlocks₁₁ 0 1 ≠ 0 ∨ P.1.toBlocks₁₁ 1 1 ≠ 0 := by
    refine not_and_or.mp fun h ↦ right_ne_zero_of_mul_eq_one hdet ?_
    rw [det_fin_two, h.1, h.2]
    ring1
  have hpos (n : dualLattice Γ) (hn : a n ≠ 0) : 0 < Q n 1 :=
    quad_pos (hpd n hn) hcol
  have hs : Summable fun n ↦ ‖fourierExp n (P • diagPoint τ' tOne) * φ (a n)‖ :=
    (ha _ φ).summable.norm
  have hab (n : dualLattice Γ) : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦
      fourierExp n (P • diagPoint τ' t) * φ (a n)) atTop (𝓝 0) := by
    by_cases hn : a n = 0
    · simp [hn]
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simp only [norm_mul, hnorm]
    simpa using (tendsto_rexp_mul (hpos n hn)).mul_const ‖φ (a n)‖
  have hb : ∀ᶠ t : Set.Ioi (0 : ℝ) in atTop, ∀ n : dualLattice Γ,
      ‖fourierExp n (P • diagPoint τ' t) * φ (a n)‖ ≤
        ‖fourierExp n (P • diagPoint τ' tOne) * φ (a n)‖ := by
    refine eventually_atTop.mpr ⟨tOne, fun t ht n ↦ ?_⟩
    by_cases hn : a n = 0
    · simp [hn]
    rw [norm_mul, norm_mul, hnorm, hnorm]
    exact mul_le_mul_of_nonneg_right (rexp_mul_le (hpos n hn).le ht) (norm_nonneg _)
  have h₁ : Tendsto (fun t : Set.Ioi (0 : ℝ) ↦ ∑' n : dualLattice Γ,
      fourierExp n (P • diagPoint τ' t) * φ (a n)) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hs hab hb
  exact h₁.congr fun t ↦ (ha _ φ).tsum_eq

variable (ρ : Representation ℂ (GL (Fin 2) ℂ) V)

/-- **The Siegel operator vanishes on the slashes by the Siegel parabolic subgroup** of a function
with a positive definite Fourier expansion. -/
lemma siegelOperatorVanishes_slash_of_posDef (hP : P ∈ siegelParabolic (Fin 2) ℝ)
    (ha : HasSiegelFourierExpansion Γ F a)
    (hpd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef) :
    SiegelOperatorVanishes (slash ρ P F) := by
  intro τ ℓ
  have hP₀ : P.1.toBlocks₂₁ = 0 := hP
  have hd (Z : SiegelUpperHalfSpace (Fin 2)) : denomGL P Z = denomGL P (diagPoint τ tOne) :=
    Units.ext <| by
      simp only [coe_denomGL, denom, hP₀, Matrix.map_zero _ ofReal_zero, Matrix.zero_mul]
  refine (tendsto_dual_smul_diagPoint_of_posDef τ (ℓ ∘ₗ ρ (denomGL P (diagPoint τ tOne))⁻¹) hP ha
    hpd).congr fun t ↦ ?_
  simp only [slash_apply, hd, LinearMap.comp_apply]

private lemma map_mem_siegelParabolic {p : symplecticGroup (Fin 2) ℚ}
    (hp : p ∈ siegelParabolic (Fin 2) ℚ) : map (algebraMap ℚ ℝ) p ∈ siegelParabolic (Fin 2) ℝ := by
  ext i j
  have h : (p : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) (.inr i) (.inl j) = 0 :=
    congrFun (congrFun hp i) j
  simp [toBlocks₂₁, h]

variable {b : dualLattice (integral (Fin 2)) → V}

/-- **A Siegel modular form on `Sp(4, ℤ)` with a positive definite Fourier expansion is a cusp
form**: write `γ ∈ Sp(4, ℚ)` as `γ = gp` with `g ∈ Sp(4, ℤ)` and `p` in the Siegel parabolic
subgroup, so that `F ∣ γ = F ∣ p`. -/
lemma isCuspForm_of_posDef (hF : F ∈ modularForms ρ (integral (Fin 2)) 1)
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b)
    (hpd : ∀ n, b n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef) : IsCuspForm ρ F := by
  intro γ
  rcases exists_mem_integral_inv_mul_mem_siegelParabolic γ with ⟨g, hg, hp⟩
  have hF' : slash ρ (map (algebraMap ℚ ℝ) g) F = F := by
    simpa using ((mem_modularForms_iff_slash ρ F _ 1).mp hF).2 ⟨g, hg⟩
  rw [← mul_inv_cancel_left g γ, map_mul, slash_mul, hF']
  exact siegelOperatorVanishes_slash_of_posDef ρ (map_mem_siegelParabolic hp) hb hpd

/-! ### The limit along `diag(τ', it)` -/

/-- The term `c(n) e^{2πi n₀₀ z}` of `n` in the series of `Φ(F)(z)`, for `n₁₁ = 0`, and `0`
otherwise, for a family `c` of coefficients. -/
noncomputable def phiTerm (c : dualLattice Γ → ℂ) (z : ℂ) (n : dualLattice Γ) : ℂ :=
  if (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 then
    cexp (2 * π * I * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℚ) * z)) * c n else 0

variable {c : dualLattice Γ → ℂ} {m : dualLattice Γ} {t : Set.Ioi (0 : ℝ)}

private lemma fourierExp_diagPoint : fourierExp m (diagPoint τ' t) =
    cexp (2 * π * I * (((m : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℚ) * τ')) *
      rexp (-(2 * π * ((m : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) * t)) := by
  rw [fourierExp, ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [trace, diag_apply, Matrix.mul_apply, diagPoint]
  simp
  linear_combination (2 * π * ((m : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) * (t : ℝ) : ℂ) * I_mul_I

private lemma phiTerm_eq_of_eq_zero (hm : (m : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0) :
    fourierExp m (diagPoint τ' t) * c m = phiTerm c τ' m := by
  rw [fourierExp_diagPoint, phiTerm, ite_eq_left hm, hm]
  simp

private lemma norm_phiTerm_le : ‖phiTerm c τ' m‖ ≤ ‖fourierExp m (diagPoint τ' t) * c m‖ := by
  by_cases hm : (m : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0
  · rw [phiTerm_eq_of_eq_zero τ' hm]
  · rw [phiTerm, ite_eq_right hm, norm_zero]
    exact norm_nonneg _

lemma summable_phiTerm (hs : ∀ τ, Summable fun n ↦ fourierExp n τ * c n) :
    Summable (phiTerm c τ') :=
  (hs (diagPoint τ' tOne)).norm.of_norm_bounded fun _ ↦ norm_phiTerm_le τ'

lemma tendsto_tsum_fourierExp_diagPoint (hs : ∀ τ, Summable fun n ↦ fourierExp n τ * c n)
    (hpsd : ∀ n, c n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) : Tendsto
    (fun t : Set.Ioi (0 : ℝ) ↦ ∑' n, fourierExp n (diagPoint τ' t) * c n) atTop
      (𝓝 (∑' n, phiTerm c τ' n)) := by
  have hnorm (n : dualLattice Γ) (t : Set.Ioi (0 : ℝ)) : ‖fourierExp n (diagPoint τ' t)‖ =
      rexp (-(2 * π * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℝ) * τ'.im +
        t * ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ)))) := by
    rw [norm_fourierExp]
    congr 1
    simp [diagPoint]
    ring1
  refine tendsto_tsum_of_dominated_convergence (hs (diagPoint τ' tOne)).norm (fun n ↦ ?_) ?_
  · by_cases hn : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0
    · exact tendsto_const_nhds.congr fun t ↦ (phiTerm_eq_of_eq_zero τ' hn).symm
    · rw [phiTerm, ite_eq_right hn]
      by_cases hc : c n = 0
      · simp [hc]
      have h₀ : (0 : ℝ) < ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
        exact_mod_cast lt_of_le_of_ne (hpsd n hc).diag_nonneg (Ne.symm hn)
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      simp only [norm_mul, hnorm]
      simpa using (tendsto_rexp_mul h₀).mul_const ‖c n‖
  · refine eventually_atTop.mpr ⟨tOne, fun t ht n ↦ ?_⟩
    by_cases hc : c n = 0
    · simp [hc]
    have h₀ : (0 : ℝ) ≤ ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℝ) := by
      exact_mod_cast (hpsd n hc).diag_nonneg
    rw [norm_mul, norm_mul, hnorm, hnorm]
    exact mul_le_mul_of_nonneg_right (rexp_mul_le h₀ ht) (norm_nonneg _)

/-- **The limit of a function with a positive semidefinite Fourier expansion along `diag(τ', it)`**:
`φ(F(diag(τ', it))) → ∑_{n₁₁ = 0} φ(a(n)) e^{2πi n₀₀ τ'}` as `t → ∞`, by dominated convergence. -/
lemma tendsto_dual_diagPoint (ha : HasSiegelFourierExpansion Γ F a)
    (hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) : Tendsto
    (fun t : Set.Ioi (0 : ℝ) ↦ φ (F (diagPoint τ' t))) atTop
      (𝓝 (∑' n, phiTerm (fun n ↦ φ (a n)) τ' n)) := by
  refine (tendsto_tsum_fourierExp_diagPoint τ' (fun τ ↦ (ha τ φ).summable) fun n hn ↦ hpsd n fun h ↦
    hn ?_).congr fun t ↦ (ha _ φ).tsum_eq
  rw [h, map_zero]

/-! ### Cusp forms are the kernel of the Siegel operator -/

/-- **Uniqueness of the series `Φ(F)`**: if `∑_{n₁₁ = 0} d(n) e^{2πi n₀₀ τ'} = 0` for every `τ'`,
then `d(n) = 0` for `n₁₁ = 0`, by the uniqueness of Fourier expansions on `ℋ₂`, as
`e^{2πi n₀₀ τ₀₀} = e^{2πi tr(nτ)}` when `n` is positive semidefinite and `n₁₁ = 0`. -/
lemma eq_zero_of_tsum_phiTerm_eq_zero {d : dualLattice (integral (Fin 2)) → ℂ}
    (hs : ∀ τ, Summable fun n ↦ fourierExp n τ * d n)
    (hpsd : ∀ n, d n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (h : ∀ τ' : ℍ, ∑' n, phiTerm d τ' n = 0) {n : dualLattice (integral (Fin 2))}
    (hn : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0) : d n = 0 := by
  have hc : (fun n : dualLattice (integral (Fin 2)) ↦
      if (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 then d n else 0) = 0 := by
    refine eq_zero_of_hasSum_fourierExp (Nat.factorial_ne_zero _)
      (smul_mem_translationLattice_of_isArithmetic · · (isArithmetic_integral (Fin 2))) fun τ ↦ ?_
    have h₁ : HasSum (phiTerm d (topLeft τ)) 0 :=
      h (topLeft τ) ▸ (summable_phiTerm (topLeft τ) hs).hasSum
    refine h₁.congr_fun fun m ↦ ?_
    by_cases hm : (m : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0
    · rw [ite_eq_left hm, phiTerm, ite_eq_left hm]
      by_cases hd : d m = 0
      · simp [hd]
      have h01 : (m : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = 0 :=
        apply_zero_one_eq_zero (hpsd m hd) hm
      have h10 : (m : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
        rw [← h01]
        exact congrFun (congrFun m.2.1 0) 1
      rw [fourierExp]
      congr 2
      simp [trace, Matrix.mul_apply, hm, h01, h10, coe_topLeft]
    · simp [phiTerm, hm]
  simpa [hn] using congrFun hc n

variable {ρ}

private lemma apply_eq_zero_of_det_eq_zero (hF : F ∈ modularForms ρ (integral (Fin 2)) 1)
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b)
    (h₁₁ : ∀ n : dualLattice (integral (Fin 2)), (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 → b n = 0)
    (n : dualLattice (integral (Fin 2))) (hd : (n : Matrix (Fin 2) (Fin 2) ℚ).det = 0) :
    b n = 0 := by
  have hs : (n : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 :=
    congrFun (congrFun n.2.1 0) 1
  have hd' : (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 * (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 =
      (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 := by
    rw [det_fin_two, hs, sub_eq_zero] at hd
    exact hd
  rcases exists_isCoprime_quad_eq_zero hd' with ⟨x, y, hxy, hq⟩
  rcases ModularGroup.bottom_row_surj (a := ![x, y]) (by simpa using hxy) with ⟨g, -, hg⟩
  let U : GL (Fin 2) ℤ := (SpecialLinearGroup.transpose g : SpecialLinearGroup (Fin 2) ℤ)
  have hU₀ : (U : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = x :=
    congrFun hg 0
  have hU₁ : (U : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = y :=
    congrFun hg 1
  have hU : leviRat U ∈ integral (Fin 2) := leviRat_mem_integral U
  have h₀ : b (dualLevi U hU n) = 0 := by
    refine h₁₁ _ ?_
    rw [coe_dualLevi]
    simp [Matrix.mul_apply, hU₀, hU₁, hs]
    linear_combination hq
  let D : GL (Fin 2) ℂ :=
    denomGL (map (algebraMap ℚ ℝ) (leviRat U)) (diagPoint UpperHalfPlane.I tOne)
  have h₁ : b (dualLevi U hU n) = ρ D⁻¹ (b n) :=
    apply_dualLevi (diagPoint UpperHalfPlane.I tOne) ρ hU n (isArithmetic_integral (Fin 2)) hF hb
  rw [h₀] at h₁
  have h₂ : ρ D 0 = ρ D (ρ D⁻¹ (b n)) := congrArg _ h₁
  rw [map_zero, ← End.mul_apply, ← map_mul, mul_inv_cancel, map_one, End.one_apply] at h₂
  exact h₂.symm

/-- **Forms with vanishing Siegel operator have positive definite support**: for
`F ∈ M_ρ(Sp(4, ℤ))` with `Φ(F) = 0` and Fourier coefficients `a`, one has `a(n) ≠ 0` only for
positive definite `n`. By the uniqueness of the series of `Φ(F)` one has `a(n) = 0` for `n₁₁ = 0`,
and each singular `n` is `Uᵀ n' U` for such an `n'` and some `U ∈ GL(2, ℤ)`. -/
lemma posDef_of_siegelOperatorVanishes [FiniteDimensional ℂ V]
    (hF : F ∈ modularForms ρ (integral (Fin 2)) 1)
    (hb : HasSiegelFourierExpansion (integral (Fin 2)) F b) (hv : SiegelOperatorVanishes F)
    (n : dualLattice (integral (Fin 2))) (hn : b n ≠ 0) :
    (n : Matrix (Fin 2) (Fin 2) ℚ).PosDef := by
  have hpsd : ∀ n, b n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
    koecherPrinciple ρ (isArithmetic_integral (Fin 2)) (by simp) F hF b hb
  have h₁₁ (m : dualLattice (integral (Fin 2))) (hm : (m : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0) :
      b m = 0 := by
    refine (forall_dual_apply_eq_zero_iff ℂ _).mp fun φ ↦ ?_
    refine eq_zero_of_tsum_phiTerm_eq_zero (fun τ ↦ (hb τ φ).summable)
      (fun m hm ↦ hpsd m fun h ↦ hm ?_) (fun τ' ↦ ?_) hm
    · rw [h, map_zero]
    · exact tendsto_nhds_unique (tendsto_dual_diagPoint τ' φ hb hpsd) (hv τ' φ)
  exact (hpsd n hn).posDef_iff_det_ne_zero.mpr fun hd ↦
    hn (apply_eq_zero_of_det_eq_zero hF hb h₁₁ n hd)

/-- **A Siegel modular form on `Sp(4, ℤ)` with vanishing Siegel operator is a cusp form**:
`Φ(F) = 0` implies `Φ(F ∣ γ) = 0` for every `γ ∈ Sp(4, ℚ)`. -/
lemma isCuspForm_of_siegelOperatorVanishes [FiniteDimensional ℂ V]
    (hF : F ∈ modularForms ρ (integral (Fin 2)) 1) (hv : SiegelOperatorVanishes F) :
    IsCuspForm ρ F := by
  rcases exists_hasSiegelFourierExpansion ρ (isArithmetic_integral (Fin 2)) hF with ⟨b, hb⟩
  exact isCuspForm_of_posDef ρ hF hb (posDef_of_siegelOperatorVanishes hF hb hv)

end SiegelUpperHalfSpace
