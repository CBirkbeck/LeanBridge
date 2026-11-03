import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ArithmeticPetersson

/-!
# The cusp forms of degree 2 and weight `ρ_{k,j}` on an arithmetic subgroup are finite-dimensional

The argument of `SiegelUpperHalfSpace.finiteDimensional_cuspFormsKJ` for `Sp(4, ℤ)` extends to an
arithmetic subgroup. It suffices to treat the image of a normal subgroup `H` of finite index of
`Sp(4, ℤ)`, whose translation lattice contains `N · Sym₂(ℤ)` for an integer `N`, so that the traces
of the elements of the dual lattice lie in `M⁻¹ ℤ`, for `M = 2 N`. The invariant function
`c(ρ(Y) F(Z), F(Z))` of a cusp form `F` is bounded, by the decay of `F ∣ g` on the Siegel set for
the finitely many representatives `g` of `Sp(4, ℤ) / H`. If the Fourier coefficients of every
`F ∣ g` vanish for `M tr n < R`, then at a point `Z₀` of the Siegel set, by the Fourier series in
`x` of `(F ∣ g)(Z₀ + (M x - i / 5) 1)`, the value of the invariant function of `F ∣ g` is at most
`θ_R` times the supremum of the invariant function of `F`, with `θ_R → 0` as `R → ∞`. So `F` is
determined by the finitely many coefficients of the `F ∣ g` at the positive semidefinite `n` with
`M tr n < R`.

## Main results

* `SiegelUpperHalfSpace.finiteDimensional_cuspFormsKJ_map`: `S_{k,j}(H)` is finite-dimensional, for
  the image of a normal subgroup `H` of finite index of `Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.finiteDimensional_cuspFormsKJ_of_isArithmetic`: `S_{k,j}(Γ)` is
  finite-dimensional, for every arithmetic subgroup `Γ`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_mul zpow_neg one_zpow

open Complex MeasureTheory Module Real Set SymplecticGroup

open scoped ComplexConjugate ComplexOrder TensorProduct

namespace SiegelUpperHalfSpace

variable {Γ : Subgroup (symplecticGroup (Fin 2) ℚ)} {k : ℤ} {j : ℕ}

/-! ### The frequencies -/

variable (Γ) in
/-- The denominator `M = 2 N` of the entries of the dual lattice of an arithmetic `Γ`, for `N` the
factorial of the index of `Γ ∩ Sp(4, ℤ)` in `Sp(4, ℤ)`. -/
private noncomputable def dualDenom : ℕ :=
  2 * (Γ.relIndex (integral (Fin 2))).factorial

private lemma dualDenom_pos : 0 < dualDenom Γ :=
  Nat.mul_pos two_pos (Nat.factorial_pos _)

private lemma exists_intCast_eq_dualDenom (hΓ : IsArithmetic Γ) (n : dualLattice Γ) (a b : Fin 2) :
    ∃ z : ℤ, (z : ℚ) = dualDenom Γ * (n : Matrix (Fin 2) (Fin 2) ℚ) a b := by
  rcases exists_intCast_eq (smul_mem_translationLattice_of_isArithmetic · · hΓ) n (a, b) with
    ⟨z, hz⟩
  refine ⟨z, hz.trans ?_⟩
  simp [dualDenom]

/-- The frequency `M tr n` of an element `n` of the dual lattice. -/
private noncomputable def traceFreq (n : dualLattice Γ) : ℕ :=
  ⌊(dualDenom Γ : ℚ) * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 + (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1)⌋₊

private lemma cast_traceFreq (hΓ : IsArithmetic Γ) {n : dualLattice Γ}
    (hn : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) : ((traceFreq n : ℕ) : ℚ) =
      dualDenom Γ * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 + (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1) := by
  rcases exists_intCast_eq_dualDenom hΓ n 0 0 with ⟨z₀, hz₀⟩
  rcases exists_intCast_eq_dualDenom hΓ n 1 1 with ⟨z₁, hz₁⟩
  have h₀ : (0 : ℚ) ≤ z₀ := hz₀ ▸ mul_nonneg (Nat.cast_nonneg _) hn.diag_nonneg
  have h₁ : (0 : ℚ) ≤ z₁ := hz₁ ▸ mul_nonneg (Nat.cast_nonneg _) hn.diag_nonneg
  have h₀' : 0 ≤ z₀ := by
    exact_mod_cast h₀
  have h₁' : 0 ≤ z₁ := by
    exact_mod_cast h₁
  rcases Int.eq_ofNat_of_zero_le h₀' with ⟨N₀, rfl⟩
  rcases Int.eq_ofNat_of_zero_le h₁' with ⟨N₁, rfl⟩
  have e : (dualDenom Γ : ℚ) * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 +
      (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1) = ((N₀ + N₁ : ℕ) : ℚ) := by
    rw [mul_add, ← hz₀, ← hz₁]
    push_cast
    rfl
  rw [traceFreq, e, Nat.floor_natCast]

private lemma natCast_traceFreq (hΓ : IsArithmetic Γ) {n : dualLattice Γ}
    (hn : (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef) : ((traceFreq n : ℕ) : ℂ) =
      dualDenom Γ * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) +
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ)) := by
  exact_mod_cast congrArg (fun q : ℚ ↦ (q : ℂ)) (cast_traceFreq hΓ hn)

private lemma finite_setOf_traceFreq_lt (hΓ : IsArithmetic Γ) (R : ℕ) :
    {n : dualLattice Γ | (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef ∧ traceFreq n < R}.Finite := by
  have hM : (0 : ℚ) < dualDenom Γ := by
    exact_mod_cast dualDenom_pos
  let coords (n : dualLattice Γ) : ℤ × ℤ × ℤ :=
    (⌊(dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0⌋,
      ⌊(dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1⌋,
        ⌊(dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1⌋)
  have hinj : Function.Injective coords := by
    intro n n' h
    rcases exists_intCast_eq_dualDenom hΓ n 0 0 with ⟨z₀, hz₀⟩
    rcases exists_intCast_eq_dualDenom hΓ n 0 1 with ⟨w, hw⟩
    rcases exists_intCast_eq_dualDenom hΓ n 1 1 with ⟨z₁, hz₁⟩
    rcases exists_intCast_eq_dualDenom hΓ n' 0 0 with ⟨z₀', hz₀'⟩
    rcases exists_intCast_eq_dualDenom hΓ n' 0 1 with ⟨w', hw'⟩
    rcases exists_intCast_eq_dualDenom hΓ n' 1 1 with ⟨z₁', hz₁'⟩
    simp only [coords, ← hz₀, ← hw, ← hz₁, ← hz₀', ← hw', ← hz₁'] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    have hcancel {a b : ℚ} (hab : (dualDenom Γ : ℚ) * a = dualDenom Γ * b) : a = b :=
      mul_left_cancel₀ hM.ne' hab
    have h₁₀ (m : dualLattice Γ) :
        (m : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (m : Matrix (Fin 2) (Fin 2) ℚ) 0 1 :=
      congrFun (congrFun m.2.1 0) 1
    refine Subtype.ext ?_
    ext i l
    fin_cases i <;> fin_cases l
    · exact hcancel (hz₀.symm.trans hz₀')
    · exact hcancel (hw.symm.trans hw')
    · exact (h₁₀ n).trans ((hcancel (hw.symm.trans hw')).trans (h₁₀ n').symm)
    · exact hcancel (hz₁.symm.trans hz₁')
  refine ((Set.finite_Icc ((0 : ℤ), -(R : ℤ), (0 : ℤ)) ((R : ℤ), (R : ℤ), (R : ℤ))).preimage
    hinj.injOn).subset ?_
  rintro n ⟨hn, hR⟩
  have hR' : (dualDenom Γ : ℚ) * ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 +
      (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1) < R := by
    rw [← cast_traceFreq hΓ hn]
    exact_mod_cast hR
  have h₀ : (0 : ℚ) ≤ (dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 :=
    mul_nonneg hM.le hn.diag_nonneg
  have h₁ : (0 : ℚ) ≤ (dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 :=
    mul_nonneg hM.le hn.diag_nonneg
  rw [mul_add] at hR'
  have h₂ : ((dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1) ^ 2 ≤
      ((dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 0) *
        ((dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 1 1) := by
    nlinarith [mul_le_mul_of_nonneg_left (sq_apply_le_of_posSemidef hn)
      (sq_nonneg (dualDenom Γ : ℚ))]
  have h₃ : |(dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1| ≤ R := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    nlinarith
  have h₄ : -(R : ℚ) ≤ (dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 ∧
      (dualDenom Γ : ℚ) * (n : Matrix (Fin 2) (Fin 2) ℚ) 0 1 ≤ R :=
    abs_le.mp h₃
  have hup {q : ℚ} {N : ℤ} (h : q ≤ N) : ⌊q⌋ ≤ N := by
    simpa using Int.floor_mono h
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact Int.floor_nonneg.mpr h₀
  · refine Int.le_floor.mpr ?_
    push_cast
    linarith [h₄.1]
  · exact Int.floor_nonneg.mpr h₁
  · refine hup ?_
    push_cast
    linarith
  · refine hup ?_
    push_cast
    linarith [h₄.2]
  · refine hup ?_
    push_cast
    linarith

/-! ### Fourier expansions at the shifted point -/

variable (Γ) in
/-- The radius `e^{-2π / (5 M)}` of the Fourier series in the variable `x`. -/
private noncomputable def freqRadius : ℝ :=
  rexp (-(2 * π / (5 * dualDenom Γ)))

private lemma freqRadius_nonneg : 0 ≤ freqRadius Γ :=
  Real.exp_nonneg _

private lemma freqRadius_lt_one : freqRadius Γ < 1 := by
  have hM : (0 : ℝ) < dualDenom Γ := by
    exact_mod_cast dualDenom_pos
  rw [freqRadius, Real.exp_lt_one_iff, neg_lt_zero]
  positivity

variable {Z₀ : SiegelUpperHalfSpace (Fin 2)} (hZ₀ : Z₀ ∈ siegelSet) (x : ℝ) (n : dualLattice Γ)

private lemma fourierExp_shiftedPoint' : fourierExp n (shiftedPoint hZ₀ x) = fourierExp n Z₀ *
    cexp (2 * π * I * (((x : ℂ) - I / 5) * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) +
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ)))) := by
  rw [fourierExp, fourierExp, ← Complex.exp_add]
  congr 1
  have e : (shiftedPoint hZ₀ x).val = Z₀.val + (((x : ℂ) - I / 5)) • 1 := rfl
  have hT : ((n : Matrix (Fin 2) (Fin 2) ℚ).map ((↑) : ℚ → ℂ)).trace =
      ((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) + ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ) := by
    simp [trace_fin_two]
  rw [e, Matrix.mul_add, trace_add, Matrix.mul_smul, Matrix.mul_one, trace_smul, hT, smul_eq_mul]
  ring1

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {f : SiegelUpperHalfSpace (Fin 2) → V}
    {a : dualLattice Γ → V} {R : ℕ} {B : ℝ}

private lemma norm_dual_le_of_forall_shiftedPoint' (hΓ : IsArithmetic Γ)
    (ha : HasSiegelFourierExpansion Γ f a)
    (hpsd : ∀ n, a n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hR : ∀ n, a n ≠ 0 → R ≤ traceFreq n) (ψ : Dual ℂ V)
    (hB : ∀ x ∈ Icc (0 : ℝ) 1, ‖ψ (f (shiftedPoint hZ₀ (dualDenom Γ * x)))‖ ≤ B) :
    ‖ψ (f Z₀)‖ ≤ B * (freqRadius Γ ^ R / (1 - freqRadius Γ)) := by
  have hM : (dualDenom Γ : ℂ) ≠ 0 := by
    exact_mod_cast dualDenom_pos.ne'
  have hc : Summable fun n ↦ ‖fourierExp n (shiftedPoint hZ₀ 0) * ψ (a n)‖ :=
    (ha _ ψ).summable.norm
  have hterm (n : dualLattice Γ) (x : ℝ) :
      fourierExp n (shiftedPoint hZ₀ 0) * ψ (a n) * cexp (2 * π * I * ((traceFreq n : ℂ) * x)) =
        fourierExp n (shiftedPoint hZ₀ (dualDenom Γ * x)) * ψ (a n) := by
    by_cases hn : a n = 0
    · simp [hn]
    rw [fourierExp_shiftedPoint', fourierExp_shiftedPoint', natCast_traceFreq hΓ (hpsd n hn),
      mul_right_comm]
    congr 1
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring1
  have hterm₀ (n : dualLattice Γ) :
      fourierExp n (shiftedPoint hZ₀ 0) * ψ (a n) * ((freqRadius Γ : ℝ) : ℂ) ^ traceFreq n =
        fourierExp n Z₀ * ψ (a n) := by
    by_cases hn : a n = 0
    · simp [hn]
    have e : ((freqRadius Γ : ℝ) : ℂ) ^ traceFreq n = cexp (-(2 * π / (5 * dualDenom Γ)) *
        (traceFreq n : ℂ)) := by
      rw [freqRadius, ofReal_exp, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring1
    have e₁ : 2 * (π : ℂ) * I * ((((0 : ℝ) : ℂ) - I / 5) *
        (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) + ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ))) +
          -(2 * π / (5 * dualDenom Γ)) * (traceFreq n : ℂ) = 0 := by
      rw [natCast_traceFreq hΓ (hpsd n hn)]
      field_simp
      push_cast
      linear_combination (-(2 * π * (((n : Matrix (Fin 2) (Fin 2) ℚ) 0 0 : ℂ) +
        ((n : Matrix (Fin 2) (Fin 2) ℚ) 1 1 : ℂ)))) * I_mul_I
    rw [fourierExp_shiftedPoint', e, mul_right_comm, mul_assoc (fourierExp n Z₀),
      mul_assoc (fourierExp n Z₀), ← Complex.exp_add, e₁, Complex.exp_zero, one_mul]
  have h₁ : ‖∑' n, fourierExp n (shiftedPoint hZ₀ 0) * ψ (a n) *
      ((freqRadius Γ : ℝ) : ℂ) ^ traceFreq n‖ ≤ B * (freqRadius Γ ^ R / (1 - freqRadius Γ)) :=
    norm_tsum_mul_pow_le hc (fun n hn ↦ hR n (fun h ↦ hn (by simp [h]))) freqRadius_nonneg
      freqRadius_lt_one fun x hx ↦ by
        simp only [hterm]
        rw [(ha _ ψ).tsum_eq]
        exact hB x hx
  simp only [hterm₀] at h₁
  rwa [(ha _ ψ).tsum_eq] at h₁

/-! ### The vanishing of cusp forms with only large frequencies -/

variable {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}

private lemma normFn_le_of_forall_le' (hZ : Z₀ ∈ siegelSet) (hΓ : IsArithmetic Γ)
    {b : dualLattice Γ → Sym[ℂ]^j (Fin 2 → ℂ)} (hb : HasSiegelFourierExpansion Γ F b)
    (hpsd : ∀ n, b n ≠ 0 → (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef)
    (hR : ∀ n, b n ≠ 0 → R ≤ traceFreq n) {Λ : ℝ} (hΛ : ∀ Z, normFn k F Z ≤ Λ) : normFn k F Z₀ ≤
    2 ^ j * (max (4 ^ k) 1 * 16 ^ j * Λ) * (freqRadius Γ ^ R / (1 - freqRadius Γ)) ^ 2 := by
  rcases exists_star_mul_eq_imGL Z₀ with ⟨M, hM⟩
  rcases exists_star_mul_eq_imGL (shiftedPoint hZ 0) with ⟨L, hL⟩
  have hL' (x : ℝ) : imGL (shiftedPoint hZ x) = star L * L := by
    rw [imGL_shiftedPoint, hL]
  generalize hK : max ((4 : ℝ) ^ k) 1 * 16 ^ j * Λ = K
  have hK₀ : 0 ≤ K := by
    rw [← hK]
    have h₁ : 0 ≤ Λ := (normFn_nonneg Z₀).trans (hΛ Z₀)
    positivity
  generalize hq : freqRadius Γ ^ R / (1 - freqRadius Γ) = q
  have hq₀ : 0 ≤ q := by
    rw [← hq]
    exact div_nonneg (pow_nonneg freqRadius_nonneg R) (by linarith [freqRadius_lt_one (Γ := Γ)])
  have hcoord (r : Fin j → Fin 2) : ‖symCoord r (rhoKJ k j M (F Z₀))‖ ^ 2 ≤ K * q ^ 2 := by
    have h₁ : ‖symCoord r (rhoKJ k j M (F Z₀))‖ ≤ √K * (freqRadius Γ ^ R / (1 - freqRadius Γ)) :=
      norm_dual_le_of_forall_shiftedPoint' hZ hΓ hb hpsd hR (symCoord r ∘ₗ rhoKJ k j M)
        fun x _ ↦ by
          refine Real.le_sqrt_of_sq_le ?_
          refine (norm_symCoord_sq_le _ r).trans ?_
          refine (symNormSq_rhoKJ_le_shift hZ (dualDenom Γ * x) _ hM (hL' _)).trans ?_
          rw [← normFn_eq (hL' (dualDenom Γ * x)), ← hK]
          exact mul_le_mul_of_nonneg_left (hΛ _) (by positivity)
    rw [hq] at h₁
    have h₂ : ‖symCoord r (rhoKJ k j M (F Z₀))‖ ^ 2 ≤ (√K * q) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    rwa [mul_pow, Real.sq_sqrt hK₀] at h₂
  rw [normFn_eq hM, symNormSq]
  refine (Finset.sum_le_sum fun r _ ↦ hcoord r).trans_eq ?_
  simp
  ring1

variable (k j Γ) in
private lemma exists_frequency_bound' : ∃ R : ℕ, 2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j) *
    (freqRadius Γ ^ R / (1 - freqRadius Γ)) ^ 2 < 1 := by
  have h₁ : Filter.Tendsto (fun R : ℕ ↦ 2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j) *
      (freqRadius Γ ^ R / (1 - freqRadius Γ)) ^ 2) Filter.atTop (nhds 0) := by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one freqRadius_nonneg
      freqRadius_lt_one).div_const (1 - freqRadius Γ)).pow 2).const_mul
        (2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j))
  exact (h₁.eventually (gt_mem_nhds zero_lt_one)).exists

variable {H : Subgroup (symplecticGroup (Fin 2) ℤ)}

private lemma normFn_slash (g : symplecticGroup (Fin 2) ℝ) (Z : SiegelUpperHalfSpace (Fin 2)) :
    normFn k (slash (rhoKJ k j) g F) Z = normFn k F (g • Z) := by
  rw [normFn, normFn, peterssonIntegrand_slash (isAdmissibleForm_symHermitianForm k)]

private lemma normFn_smul_map_of_mem
    (hF : F ∈ modularForms (rhoKJ k j) (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1)
    {δ : symplecticGroup (Fin 2) ℤ} (hδ : δ ∈ H) (Z : SiegelUpperHalfSpace (Fin 2)) :
    normFn k F (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z) = normFn k F Z := by
  have e : SymplecticGroup.map (algebraMap ℚ ℝ) (SymplecticGroup.map (Int.castRingHom ℚ) δ) • Z =
      SymplecticGroup.map (Int.castRingHom ℝ) δ • Z := by
    rw [map_algebraMap_map_intCast]
  rw [normFn, normFn, ← e]
  exact congrArg Complex.re (peterssonIntegrand_map_smul (isAdmissibleForm_symHermitianForm k) hF hF
    ⟨_, SymplecticGroup.map (Int.castRingHom ℚ) δ, ⟨_, hδ, rfl⟩, rfl⟩ Z)

variable [H.Normal] [H.FiniteIndex]

private lemma bddAbove_range_normFn'
    (hF : F ∈ cuspForms (rhoKJ k j) (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1) :
    BddAbove (Set.range (normFn k F)) := by
  have hq (q : symplecticGroup (Fin 2) ℤ ⧸ H) :
      ∃ Λ, ∀ σ ∈ siegelSet, normFn k F (SymplecticGroup.map (Int.castRingHom ℝ) q.out • σ) ≤ Λ := by
    rcases exists_norm_peterssonIntegrand_smul_le (isModerateForm_rhoKJ k _)
      (isAdmissibleForm_symHermitianForm k) (fun g _ hf ↦ hf.slash_rhoKJ k g) hF.1 hF q.out with
        ⟨c, C, N, hc, h⟩
    refine ⟨|C| * (N.factorial / (c / 2) ^ N * rexp (c / 2)), fun σ hσ ↦ ?_⟩
    refine (Complex.re_le_norm _).trans ((h σ hσ).trans ?_)
    have hT : 0 ≤ (σ.val 0 0).im + (σ.val 1 1).im :=
      add_nonneg (by linarith [four_fifths_le_im_zero_zero hσ])
        (by linarith [four_fifths_le_im_one_one hσ])
    rw [add_assoc]
    refine (mul_rexp_mul_pow_le C N hc hT).trans <|
      mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
    nlinarith
  choose Λ hΛ using hq
  rcases Finite.bddAbove_range Λ with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rintro _ ⟨Z, rfl⟩
  rcases exists_smul_eq_out_smul_of_normal (H := H) Z with ⟨δ, hδ, q, σ, hσ, h⟩
  rw [← normFn_smul_map_of_mem hF.1 hδ, h]
  exact (hΛ q σ hσ).trans (hB ⟨q, rfl⟩)

private lemma eq_zero_of_forall_traceFreq_le (hθ : 2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j) *
      (freqRadius (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) ^ R /
        (1 - freqRadius (H.map (SymplecticGroup.map (Int.castRingHom ℚ))))) ^ 2 < 1)
    (hF : F ∈ cuspForms (rhoKJ k j) (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1)
    {b : symplecticGroup (Fin 2) ℤ ⧸ H →
      dualLattice (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) → Sym[ℂ]^j (Fin 2 → ℂ)}
    (hb : ∀ q, HasSiegelFourierExpansion (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))
      (slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out) F) (b q))
    (hR : ∀ q n, b q n ≠ 0 → R ≤ traceFreq n) : F = 0 := by
  have hbdd : BddAbove (Set.range (normFn k F)) := bddAbove_range_normFn' hF
  generalize hθ' : 2 ^ j * (max ((4 : ℝ) ^ k) 1 * 16 ^ j) *
    (freqRadius (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) ^ R /
      (1 - freqRadius (H.map (SymplecticGroup.map (Int.castRingHom ℚ))))) ^ 2 = θ at hθ
  have : Nonempty (SiegelUpperHalfSpace (Fin 2)) := ⟨scalarPoint tOne⟩
  have hle : ⨆ Z, normFn k F Z ≤ θ * ⨆ Z, normFn k F Z := by
    refine ciSup_le fun Z ↦ ?_
    rcases exists_smul_eq_out_smul_of_normal (H := H) Z with ⟨δ, hδ, q, σ, hσ, h⟩
    rw [← normFn_smul_map_of_mem hF.1 hδ, h, ← normFn_slash]
    refine (normFn_le_of_forall_le' hσ (isArithmetic_map H) (hb q) (koecherPrinciple _
      (isArithmetic_map H) (by simp) _ (slash_mem_modularForms_map
        (fun g _ hf ↦ hf.slash_rhoKJ k g) hF.1 q.out) (b q) (hb q)) (hR q)
          (Λ := ⨆ Z, normFn k F Z) fun Z ↦ ?_).trans_eq ?_
    · rw [normFn_slash]
      exact le_ciSup hbdd _
    · rw [← hθ']
      ring1
  have hΛ : ⨆ Z, normFn k F Z ≤ 0 := by
    nlinarith [hle, le_ciSup hbdd (scalarPoint tOne),
      normFn_nonneg (k := k) (F := F) (scalarPoint tOne)]
  funext Z
  by_contra hne
  rcases exists_star_mul_eq_imGL Z with ⟨M, hM⟩
  have hv : rhoKJ k j M (F Z) ≠ 0 := fun h ↦ hne <| by
    have h₁ : rhoKJ k j M⁻¹ (rhoKJ k j M (F Z)) = F Z := (rhoKJ k j).inv_self_apply M (F Z)
    rw [h, map_zero] at h₁
    exact h₁.symm
  have h₁ : 0 < symHermitianForm j (rhoKJ k j M (F Z)) (rhoKJ k j M (F Z)) :=
    symHermitianForm_pos hv
  rw [symHermitianForm_self, zero_lt_real, ← normFn_eq hM] at h₁
  linarith [le_ciSup hbdd Z]

/-! ### Finite dimension -/

/-- A choice of Fourier coefficients of the slash of a cusp form by a representative of
`Sp(4, ℤ) / H`. -/
private noncomputable def slashCoeff
    (G : cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))))
    (q : symplecticGroup (Fin 2) ℤ ⧸ H) :
    dualLattice (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) → Sym[ℂ]^j (Fin 2 → ℂ) :=
  (exists_hasSiegelFourierExpansion (rhoKJ k j) (isArithmetic_map H)
    (slash_mem_modularForms_map (fun g _ hf ↦ hf.slash_rhoKJ k g) G.2.1 q.out)).choose

private lemma hasSiegelFourierExpansion_slashCoeff
    (G : cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))))
    (q : symplecticGroup (Fin 2) ℤ ⧸ H) :
    HasSiegelFourierExpansion (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))
      (slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out)
        (G : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ))) (slashCoeff G q) :=
  (exists_hasSiegelFourierExpansion (rhoKJ k j) (isArithmetic_map H)
    (slash_mem_modularForms_map (fun g _ hf ↦ hf.slash_rhoKJ k g) G.2.1 q.out)).choose_spec

variable (R k j H) in
/-- The Fourier coefficients of the slashes of a cusp form by the representatives of `Sp(4, ℤ) / H`,
at the finitely many positive semidefinite `n` of frequency below `R`, as a linear map. -/
private noncomputable def slashCoeffMap :
    cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) →ₗ[ℂ]
      (symplecticGroup (Fin 2) ℤ ⧸ H →
        {n : dualLattice (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) |
          (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef ∧ traceFreq n < R} → Sym[ℂ]^j (Fin 2 → ℂ)) where
  toFun F q n := slashCoeff F q n
  map_add' F G := by
    funext q n
    have h : HasSiegelFourierExpansion (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))
        (slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out)
          ((F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) + G)) (slashCoeff (F + G) q) :=
      hasSiegelFourierExpansion_slashCoeff (F + G) q
    rw [slash_add] at h
    exact (congrFun (((hasSiegelFourierExpansion_slashCoeff F q).add _
      (hasSiegelFourierExpansion_slashCoeff G q)).unique_of_isArithmetic (isArithmetic_map H) h)
        n).symm
  map_smul' c F := by
    funext q n
    have h : HasSiegelFourierExpansion (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))
        (slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) q.out)
          (c • (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)))) (slashCoeff (c • F) q) :=
      hasSiegelFourierExpansion_slashCoeff (c • F) q
    rw [slash_smul] at h
    exact (congrFun (((hasSiegelFourierExpansion_slashCoeff F q).const_smul _
      c).unique_of_isArithmetic (isArithmetic_map H) h) n).symm

variable (k j H) in
/-- **The space `S_{k,j}(H)` is finite-dimensional**, for the image in `Sp(4, ℚ)` of a normal
subgroup `H` of finite index of `Sp(4, ℤ)`. A cusp form `F` is determined by the Fourier
coefficients of the `F ∣ g`, for representatives `g` of `Sp(4, ℤ) / H`, at the `n` of frequency
`M tr n < R`, for `R` large enough. -/
lemma finiteDimensional_cuspFormsKJ_map :
    FiniteDimensional ℂ (cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) := by
  rcases exists_frequency_bound' (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) k j with
    ⟨R, hR⟩
  have : Finite {n : dualLattice (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) |
      (n : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef ∧ traceFreq n < R} :=
    (finite_setOf_traceFreq_lt (isArithmetic_map H) R).to_subtype
  refine FiniteDimensional.of_injective (slashCoeffMap k j R H) ((injective_iff_map_eq_zero _).mpr
    fun F hF ↦ Subtype.ext ?_)
  refine eq_zero_of_forall_traceFreq_le hR F.2 (hasSiegelFourierExpansion_slashCoeff F)
    fun q n hn ↦ ?_
  by_contra hlt
  exact hn (congrFun (congrFun hF q) ⟨n, koecherPrinciple _ (isArithmetic_map H) (by simp) _
    (slash_mem_modularForms_map (fun g _ hf ↦ hf.slash_rhoKJ k g) F.2.1 q.out) _
      (hasSiegelFourierExpansion_slashCoeff F q) n hn, not_le.mp hlt⟩)

variable (k j) in
/-- **The space `S_{k,j}(Γ)` is finite-dimensional, for every arithmetic subgroup `Γ` of
`Sp(4, ℚ)`**: it is contained in `S_{k,j}(H)`, for the image of a normal subgroup `H` of finite
index of `Sp(4, ℤ)`. -/
lemma finiteDimensional_cuspFormsKJ_of_isArithmetic (hΓ : IsArithmetic Γ) :
    FiniteDimensional ℂ (cuspFormsKJ k j Γ) := by
  rcases exists_normal_map_le hΓ with ⟨H, hN, hH, hle⟩
  have : FiniteDimensional ℂ (cuspFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) :=
    finiteDimensional_cuspFormsKJ_map k j H
  exact Submodule.finiteDimensional_of_le (cuspForms_le_of_le hle)

end SiegelUpperHalfSpace
