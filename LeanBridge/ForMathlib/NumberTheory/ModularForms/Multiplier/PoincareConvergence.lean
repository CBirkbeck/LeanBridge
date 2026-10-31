import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.Poincare
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable

/-!
# Well-definedness and convergence of Poincaré series

The `n`-th Poincaré series of weight `k` and multiplier `v` on `G ≤ SL(2, ℤ)` at the cusp
`s = γ_s ∞` of width `w` (LMFDB `specialfunction.poincare`) is the sum over the right cosets
`G_s g` of the cusp stabiliser `G_s` of the terms `conj(v(g)) e^{2πi (n/w) γ_s⁻¹ g z}
j(γ_s⁻¹ g, z)^{-k}` (`ModularForm.poincareSeries`, with chosen representatives). This file proves
that the terms are constant on these cosets, so that the series does not depend on the
representatives, and that for `k ≥ 3` and `n ≥ 0` it converges absolutely and locally uniformly,
by comparison with the Eisenstein series (the bottom rows of the `γ_s⁻¹ g` over the cosets are
distinct), so that it is holomorphic on `ℍ`.

The terms are constant on the cosets when `w` divides the translation of every `γ_s⁻¹ h γ_s = ±T^b`
with `h ∈ G_s`, that is when `w` is a multiple of the width, and `v(h) = (±1)^k` for these `h`.
The latter is the LMFDB's conditions `v(-I) = (-1)^k` and "`v` is trivial on `G_s`" read on the
translations `T^b`: taken literally on all of `G_s`, the second fails at `-I` for odd `k`, and at an
irregular cusp of odd weight it would make the terms depend on the representatives up to sign.

The matrices of `SL(2, ℤ)` mapping `∞` to `s` are the `±γ_s T^m`, and they all have the same
stabiliser `G_s`. Replacing `γ_s` by `γ_s T^m` multiplies every term, hence the series, by
`e^{-2πi n m / w}`, a power of `e^{2πi n / w}`, so that nothing changes for `w ∣ n`, as the LMFDB
says; replacing `γ_s` by `-γ_s` multiplies them by `(-1)^k`, so that for odd `k` the series is
determined by the cusp only up to sign, even for `w ∣ n`. That the series is a cusp form (its
transformation law under `G` and its vanishing at the cusps) and that the Poincaré series span the
cusp forms are not proved here.

## Main results

* `ModularForm.mem_cuspStabilizer_iff`: `h ∈ G_s` exactly when `γ_s⁻¹ h γ_s` fixes `∞`.
* `ModularForm.poincareTerm_mul_of_mem_cuspStabilizer`,
  `ModularForm.poincareTerm_eq_of_rightRel`: the terms are constant on the cosets `G_s g`.
* `ModularForm.poincareSeries_eq_tsum_of_section`: the Poincaré series can be computed with any
  choice of coset representatives.
* `ModularForm.summable_norm_poincareTerm`, `ModularForm.summable_poincareTerm`: for `k ≥ 3` and
  `n ≥ 0` the series converges absolutely.
* `ModularForm.tendstoLocallyUniformly_poincareSeries`,
  `ModularForm.mdifferentiable_poincareSeries`: for `k ≥ 3` and `n ≥ 0` the series converges
  locally uniformly, and is holomorphic on `ℍ`.
* `ModularForm.cuspStabilizer_mul_T_zpow`, `ModularForm.poincareTerm_mul_T_zpow`,
  `ModularForm.poincareTerm_mul_T_zpow_of_dvd`, `ModularForm.cuspStabilizer_neg`,
  `ModularForm.poincareTerm_neg`: the dependence on the choice of `γ_s`.
-/

open UpperHalfPlane Matrix SpecialLinearGroup OnePoint EisensteinSeries ModularGroup

open scoped MatrixGroups ComplexConjugate Manifold

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (v : G →* Circle) (k n : ℤ) (w : ℕ) (z : ℍ)
    (m : ℤ) {h : G} (g : G)

/-- **The stabiliser of the cusp `γ_s ∞`**: `h ∈ G_s` exactly when `γ_s⁻¹ h γ_s` fixes `∞`, that
is when its lower left entry vanishes. -/
lemma mem_cuspStabilizer_iff : h ∈ cuspStabilizer G γ ↔ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 0 = 0 := by
  have hM (M : SL(2, ℤ)) : (mapGL ℝ M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (M 1 0 : ℝ) :=
    rfl
  rw [cuspStabilizer, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ← inv_smul_eq_iff, smul_smul, smul_smul, ← map_inv, ← map_mul,
    ← map_mul, smul_infty_eq_self_iff, hM, Int.cast_eq_zero]

lemma injective_poincareBottomRow :
    Function.Injective fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      ![(γ⁻¹ * (q.out : SL(2, ℤ))) 1 0, (γ⁻¹ * (q.out : SL(2, ℤ))) 1 1] := by
  intro q q' hqq
  have h₀ : (γ⁻¹ * (q.out : SL(2, ℤ))) 1 0 = (γ⁻¹ * (q'.out : SL(2, ℤ))) 1 0 := congrFun hqq 0
  have h₁ : (γ⁻¹ * (q.out : SL(2, ℤ))) 1 1 = (γ⁻¹ * (q'.out : SL(2, ℤ))) 1 1 := congrFun hqq 1
  refine Quotient.out_equiv_out.mp (QuotientGroup.rightRel_apply.mpr ?_)
  rw [mem_cuspStabilizer_iff, Subgroup.coe_mul, Subgroup.coe_inv,
    show γ⁻¹ * ((q'.out : SL(2, ℤ)) * (q.out : SL(2, ℤ))⁻¹) * γ =
      γ⁻¹ * (q'.out : SL(2, ℤ)) * (γ⁻¹ * (q.out : SL(2, ℤ)))⁻¹ by group]
  generalize γ⁻¹ * (q.out : SL(2, ℤ)) = A at h₀ h₁
  generalize γ⁻¹ * (q'.out : SL(2, ℤ)) = B at h₀ h₁
  simp [Matrix.mul_apply, Matrix.adjugate_fin_two, ← h₀, ← h₁]
  ring1

variable {k n} in
lemma norm_poincareTerm_le (hn : 0 ≤ n) : ‖poincareTerm γ v k n w z g‖ ≤
    ‖eisSummand k ![(γ⁻¹ * (g : SL(2, ℤ))) 1 0, (γ⁻¹ * (g : SL(2, ℤ))) 1 1] z‖ := by
  have hden : denom (γ⁻¹ * (g : SL(2, ℤ))) z ^ (-k) =
      eisSummand k ![(γ⁻¹ * (g : SL(2, ℤ))) 1 0, (γ⁻¹ * (g : SL(2, ℤ))) 1 1] z := by
    rw [← map_mul, ← map_mul, ModularGroup.denom_apply]
    simp [eisSummand]
  rw [poincareTerm, norm_mul, norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul, hden]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp
  exact mul_nonneg (mul_nonneg (by positivity) (div_nonneg (Int.cast_nonneg hn)
    (Nat.cast_nonneg w))) (UpperHalfPlane.im_pos _).le

variable {k n} in
/-- **Poincaré series of weight `k ≥ 3` and index `n ≥ 0` converge absolutely**, by comparison
with the Eisenstein series of weight `k`, the bottom rows of the `γ_s⁻¹ g` over the cosets `G_s g`
being distinct. -/
lemma summable_norm_poincareTerm (hk : 3 ≤ k) (hn : 0 ≤ n) :
    Summable fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      ‖poincareTerm γ v k n w z q.out‖ :=
  (summable_norm_eisSummand hk z).comp_injective (injective_poincareBottomRow γ)
  |>.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun q ↦ norm_poincareTerm_le γ v w z q.out hn

variable {k n} in
/-- **Poincaré series of weight `k ≥ 3` and index `n ≥ 0` converge**, absolutely
(`summable_norm_poincareTerm`), so that `ModularForm.poincareSeries` is their sum. -/
lemma summable_poincareTerm (hk : 3 ≤ k) (hn : 0 ≤ n) :
    Summable fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      poincareTerm γ v k n w z q.out :=
  (summable_norm_poincareTerm γ v w z hk hn).of_norm

lemma poincareTerm_eq_denom : poincareTerm γ v k n w z g = conj (v g : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (n / w) * ↑((γ⁻¹ * (g : SL(2, ℤ))) • z)) *
    denom (γ⁻¹ * (g : SL(2, ℤ)) : SL(2, ℤ)) z ^ (-k) := by
  rw [poincareTerm, map_mul, map_mul]

/-- **The terms are invariant under the cusp stabiliser**: for `h ∈ G_s` with
`γ_s⁻¹ h γ_s = ±T^b`, if `w ∣ b` and `v(h) = (±1)^k`, then the terms at `h g` and `g` agree. -/
lemma poincareTerm_mul_of_mem_cuspStabilizer (hh : h ∈ cuspStabilizer G γ)
    (hw : (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k) :
    poincareTerm γ v k n w z (h * g) = poincareTerm γ v k n w z g := by
  rw [poincareTerm_eq_denom, poincareTerm_eq_denom, map_mul, Circle.coe_mul, map_mul, hv,
    Subgroup.coe_mul, show γ⁻¹ * ((h : SL(2, ℤ)) * g) = γ⁻¹ * h * γ * (γ⁻¹ * g) by group,
    mul_smul]
  rw [mem_cuspStabilizer_iff] at hh
  generalize γ⁻¹ * (h : SL(2, ℤ)) * γ = P at hh hw ⊢
  generalize γ⁻¹ * (g : SL(2, ℤ)) = A
  have hdet : P 0 0 * P 1 1 = 1 := by
    have hP : (P : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := P.det_coe
    rw [Matrix.det_fin_two, hh, mul_zero, sub_zero] at hP
    exact hP
  have hden : denom (P * A : SL(2, ℤ)) z = P 1 1 * denom (A : SL(2, ℤ)) z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply]
    simp [Matrix.mul_apply, hh]
    ring1
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (n / w) * (P 0 0 * P 0 1 : ℤ)) = 1 := by
    rcases hw with ⟨c, hc⟩
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · rw [hc, ← Complex.exp_int_mul_two_pi_mul_I (n * P 0 0 * c)]
      congr 1
      push_cast
      field_simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hsmul : (↑(P • (A • z)) : ℂ) = ↑(A • z) + (P 0 0 * P 0 1 : ℤ) := by
      rw [coe_specialLinearGroup_apply]
      simp [hh, h0, h1]
    rw [hsmul, hden, mul_add, Complex.exp_add, hexp, h1]
    simp
  · have hsmul : (↑(P • (A • z)) : ℂ) = ↑(A • z) + (P 0 0 * P 0 1 : ℤ) := by
      rw [coe_specialLinearGroup_apply]
      simp [hh, h0, h1]
      ring1
    rw [hsmul, hden, mul_add, Complex.exp_add, hexp, h1]
    simp
    rw [neg_eq_neg_one_mul (denom _ _), mul_zpow, mul_inv]
    field_simp

variable {g} in
/-- **The terms are constant on the cosets `G_s g`**, when `w` divides the translations of the
`γ_s⁻¹ h γ_s = ±T^b`, `h ∈ G_s` (in particular when `w` is the width of the cusp), and
`v(h) = (±1)^k` on `G_s`. -/
lemma poincareTerm_eq_of_rightRel
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k) {g' : G}
    (hgg : QuotientGroup.rightRel (cuspStabilizer G γ) g g') :
    poincareTerm γ v k n w z g' = poincareTerm γ v k n w z g := by
  have hmem : g' * g⁻¹ ∈ cuspStabilizer G γ := QuotientGroup.rightRel_apply.mp hgg
  simpa using poincareTerm_mul_of_mem_cuspStabilizer γ v k n w z g hmem (hw _ hmem) (hv _ hmem)

/-- **The Poincaré series does not depend on the coset representatives**: under the hypotheses of
`poincareTerm_eq_of_rightRel`, it is the sum of the terms at any choice of representatives. -/
lemma poincareSeries_eq_tsum_of_section
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    (σ : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) → G)
    (hσ : ∀ q, Quotient.mk (QuotientGroup.rightRel (cuspStabilizer G γ)) (σ q) = q) :
    poincareSeries γ v k n w z = ∑' q, poincareTerm γ v k n w z (σ q) :=
  tsum_congr fun q ↦ poincareTerm_eq_of_rightRel γ v k n w z hw hv
    (Quotient.exact ((hσ q).trans (Quotient.out_eq q).symm))

/-- **The cusp stabiliser does not depend on the choice of `γ_s`**: `γ_s T^m` also maps `∞` to
`s`, and has the same stabiliser `G_s`. -/
lemma cuspStabilizer_mul_T_zpow : cuspStabilizer G (γ * T ^ m) = cuspStabilizer G γ := by
  ext h
  rw [mem_cuspStabilizer_iff, mem_cuspStabilizer_iff,
    show (γ * T ^ m)⁻¹ * (h : SL(2, ℤ)) * (γ * T ^ m) = T ^ (-m) * (γ⁻¹ * h * γ) * T ^ m by
      group]
  generalize γ⁻¹ * (h : SL(2, ℤ)) * γ = P
  simp [Matrix.mul_apply, coe_T_zpow, Matrix.vecMul, dotProduct]

/-- **Changing `γ_s` multiplies the terms by a root of unity** (LMFDB
`specialfunction.poincare`): replacing `γ_s` by `γ_s T^m` multiplies every term by
`e^{-2πi n m / w}`, a power of `e^{2πi n / w}`, and so multiplies the Poincaré series by the same
factor, the cosets `G_s g` being unchanged (`cuspStabilizer_mul_T_zpow`). -/
lemma poincareTerm_mul_T_zpow : poincareTerm (γ * T ^ m) v k n w z g =
    Complex.exp (-(2 * Real.pi * Complex.I * (n / w) * m)) * poincareTerm γ v k n w z g := by
  have hden : denom (T ^ (-m) * (γ⁻¹ * (g : SL(2, ℤ))) : SL(2, ℤ)) z =
      denom (γ⁻¹ * (g : SL(2, ℤ)) : SL(2, ℤ)) z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply]
    simp [Matrix.mul_apply, coe_T_zpow]
  rw [poincareTerm_eq_denom, poincareTerm_eq_denom,
    show (γ * T ^ m)⁻¹ * (g : SL(2, ℤ)) = T ^ (-m) * (γ⁻¹ * g) by group, mul_smul,
    coe_T_zpow_smul_eq, hden, mul_add, Complex.exp_add, Int.cast_neg, mul_neg]
  ring1

/-- **For `w ∣ n` the terms do not change when `γ_s` is replaced by `γ_s T^m`** (LMFDB
`specialfunction.poincare`), nor does the Poincaré series; replacing `γ_s` by `-γ_s` still
multiplies them by `(-1)^k` (`poincareTerm_neg`). -/
lemma poincareTerm_mul_T_zpow_of_dvd (hwn : (w : ℤ) ∣ n) :
    poincareTerm (γ * T ^ m) v k n w z g = poincareTerm γ v k n w z g := by
  rw [poincareTerm_mul_T_zpow]
  rcases hwn with ⟨j, rfl⟩
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  · have hexp : Complex.exp (-(2 * Real.pi * Complex.I * (((w * j : ℤ) : ℂ) / w) * m)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I (-(j * m))]
      congr 1
      push_cast
      field_simp
    rw [hexp, one_mul]

/-- **The cusp stabiliser is the same for `-γ_s`**, which also maps `∞` to `s`. -/
lemma cuspStabilizer_neg : cuspStabilizer G (-γ) = cuspStabilizer G γ := by
  ext h
  rw [mem_cuspStabilizer_iff, mem_cuspStabilizer_iff, inv_neg, neg_mul, mul_neg, neg_mul, neg_neg]

/-- **Replacing `γ_s` by `-γ_s` multiplies the terms by `(-1)^k`**, and so the Poincaré series,
the cosets `G_s g` being unchanged (`cuspStabilizer_neg`): for odd `k` the series depends on the
choice of `γ_s` also when `w ∣ n`, up to sign. -/
lemma poincareTerm_neg : poincareTerm (-γ) v k n w z g = (-1) ^ k * poincareTerm γ v k n w z g := by
  have hden : denom (-(γ⁻¹ * (g : SL(2, ℤ))) : SL(2, ℤ)) z =
      -denom (γ⁻¹ * (g : SL(2, ℤ)) : SL(2, ℤ)) z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply]
    simp
    ring1
  rw [poincareTerm_eq_denom, poincareTerm_eq_denom, inv_neg, neg_mul, SL_neg_smul, hden,
    neg_eq_neg_one_mul (denom _ _), mul_zpow, zpow_neg, ← inv_zpow, inv_neg_one]
  ring1

variable {k n} in
/-- **Poincaré series of weight `k ≥ 3` and index `n ≥ 0` converge locally uniformly on `ℍ`**, by
the Weierstrass test against the Eisenstein series on vertical strips. -/
lemma tendstoLocallyUniformly_poincareSeries (hk : 3 ≤ k) (hn : 0 ≤ n) : TendstoLocallyUniformly
    (fun s : Finset (Quotient (QuotientGroup.rightRel (cuspStabilizer G γ))) ↦
      (∑ q ∈ s, poincareTerm γ v k n w · q.out)) (poincareSeries γ v k n w ·) Filter.atTop := by
  have hk' : (2 : ℝ) < k := by
    norm_cast
  have p_sum : Summable fun q : Quotient (QuotientGroup.rightRel (cuspStabilizer G γ)) ↦
      ‖![(γ⁻¹ * (q.out : SL(2, ℤ))) 1 0, (γ⁻¹ * (q.out : SL(2, ℤ))) 1 1]‖ ^ (-k : ℝ) :=
    (summable_one_div_norm_rpow hk').comp_injective (injective_poincareBottomRow γ)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rcases subset_verticalStrip_of_isCompact hK with ⟨A, B, hB, HABK⟩
  refine (tendstoUniformlyOn_tsum (hu := p_sum.mul_left <| r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))
    (fun q z hz ↦ (norm_poincareTerm_le γ v w z q.out hn).trans ?_)).mono HABK
  simpa only [eisSummand, norm_zpow, ← Real.rpow_intCast, Int.cast_neg] using
    summand_bound_of_mem_verticalStrip (by positivity) _ hB hz

lemma mdifferentiable_poincareTerm : MDiff fun z : ℍ ↦ poincareTerm γ v k n w z g := by
  have hdet : 0 < ((γ⁻¹ * (g : SL(2, ℤ)) : SL(2, ℤ)) : GL (Fin 2) ℝ).det.val := by
    simp
  refine MDifferentiable.mul (MDifferentiable.mul mdifferentiable_const ?_)
    (mdifferentiable_denom_zpow _ _)
  exact Complex.differentiable_exp.comp_mdifferentiable <| MDifferentiable.mul mdifferentiable_const
    (mdifferentiable_coe.comp (mdifferentiable_smul hdet))

variable {k n} in
/-- **Poincaré series of weight `k ≥ 3` and index `n ≥ 0` are holomorphic on `ℍ`** (LMFDB
`specialfunction.poincare`), as locally uniform limits of holomorphic functions. -/
lemma mdifferentiable_poincareSeries (hk : 3 ≤ k) (hn : 0 ≤ n) :
    MDiff (poincareSeries γ v k n w) := by
  have h : TendstoLocallyUniformlyOn
      (fun s : Finset (Quotient (QuotientGroup.rightRel (cuspStabilizer G γ))) ↦
        ↑ₕ(fun z : ℍ ↦ ∑ q ∈ s, poincareTerm γ v k n w z q.out))
      (↑ₕ(poincareSeries γ v k n w)) Filter.atTop {z : ℂ | 0 < z.im} := by
    rw [← upperHalfPlaneSet, ← range_coe, ← Set.image_univ]
    refine TendstoLocallyUniformlyOn.comp (s := ⊤) ?_ _ ?_
      (OpenPartialHomeomorph.continuousOn_symm _)
    · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
      exact tendstoLocallyUniformly_poincareSeries γ v w hk hn
    · exact Set.mapsTo_univ _ _
  rw [UpperHalfPlane.mdifferentiable_iff]
  exact h.differentiableOn (.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun q _ ↦ UpperHalfPlane.mdifferentiable_iff.mp <|
      mdifferentiable_poincareTerm γ v k n w q.out) isOpen_upperHalfPlaneSet

end ModularForm
