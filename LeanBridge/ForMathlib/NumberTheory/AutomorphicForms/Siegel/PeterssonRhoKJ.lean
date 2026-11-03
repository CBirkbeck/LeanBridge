import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonConvergence

/-!
# The Petersson product in weight `ρ_{k,j} = det^k ⊗ Sym^j`

Every sesquilinear form `c` on `Sym^j(ℂ²)` is moderate for `ρ_{k,j}`: `c(ρ_{k,j}(Y) v, w)` is
`det(Y)^k` times a polynomial of degree `j` in the entries of `Y`, and on the Siegel set `det Y` is
bounded below by a positive constant and above by `(y₀₀ + y₁₁)²`.

There is a positive definite admissible Hermitian form on `Sym^j(ℂ²)`, unique up to a scalar since
`ρ_{k,j}` is irreducible, for which the Petersson product of Siegel modular forms of weight
`ρ_{k,j}` is taken. It is induced by the standard Hermitian form on `ℂ²`: a symmetric tensor `v` has
coordinates `T_r(v)`, `r : Fin j → Fin 2`, with `T_r(u₁ ⋯ u_j) = ∑_σ ∏_i u_{σ i}(r i)`, and
`c(v, w) = ∑_r T_r(v) conj(T_r(w))`.

## Main definitions

* `SiegelUpperHalfSpace.symCoord`: the coordinates `T_r` of a symmetric tensor.
* `SiegelUpperHalfSpace.symHermitianForm`: the Hermitian form `c`.

## Main results

* `SiegelUpperHalfSpace.exists_norm_dual_symPowerRep_le`: the coefficients of `Sym^j` are polynomial
  of degree `j`.
* `SiegelUpperHalfSpace.isModerateForm_rhoKJ`: every sesquilinear form is moderate for `ρ_{k,j}`.
* `SiegelUpperHalfSpace.isAdmissibleForm_symHermitianForm`: `c` is admissible for `ρ_{k,j}`.
* `SiegelUpperHalfSpace.symHermitianForm_pos`: `c` is positive definite.
* `SiegelUpperHalfSpace.conj_symHermitianForm`: `c` is Hermitian.
-/

open Matrix hiding zpow_neg

open Complex Module Real SymplecticGroup

open scoped ComplexConjugate ComplexOrder TensorProduct

namespace SiegelUpperHalfSpace

variable {j : ℕ} (φ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ))) (v : Sym[ℂ]^j (Fin 2 → ℂ))

private lemma symPowerRep_tprod (A : GL (Fin 2) ℂ) (m : Fin j → Fin 2 → ℂ) :
    TauCeti.symPowerRep ℂ 2 j A (⨂ₛ[ℂ] i, m i) = ⨂ₛ[ℂ] i, (A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ m i :=
  Representation.symmetricPower_apply_tprod _ _ _ _

private lemma norm_mulVec_apply_le {A : Matrix (Fin 2) (Fin 2) ℂ} {M : ℝ} (hA : ∀ a c, ‖A a c‖ ≤ M)
    (u : Fin 2 → ℂ) (a : Fin 2) : ‖(A *ᵥ u) a‖ ≤ 2 * M * ‖u‖ := by
  rw [mulVec, dotProduct, Fin.sum_univ_two]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 0)
  have h (c : Fin 2) : ‖A a c * u c‖ ≤ M * ‖u‖ := by
    rw [norm_mul]
    exact mul_le_mul (hA a c) (norm_le_pi_norm u c) (norm_nonneg _) hM
  refine (norm_add_le _ _).trans ((add_le_add (h 0) (h 1)).trans_eq ?_)
  ring1

/-- **The coefficients of `Sym^j` are polynomial of degree `j`**: `|φ(Sym^j(A) v)| ≤ C M^j` when the
entries of `A` are bounded by `M`, with `C` depending on `φ` and `v` only. -/
lemma exists_norm_dual_symPowerRep_le : ∃ C : ℝ, ∀ (A : GL (Fin 2) ℂ) (M : ℝ),
    (∀ a c, ‖(A : Matrix (Fin 2) (Fin 2) ℂ) a c‖ ≤ M) → ‖φ (TauCeti.symPowerRep ℂ 2 j A v)‖ ≤
      C * M ^ j := by
  have hv : v ∈ Submodule.span ℂ (Set.range (SymmetricPower.tprod ℂ)) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨m, rfl⟩
    refine ⟨dualBound φ * ∏ i, (2 * ‖m i‖), fun A M hA ↦ ?_⟩
    have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 0)
    rw [show SymmetricPower.tprod ℂ m = ⨂ₛ[ℂ] i, m i from rfl, symPowerRep_tprod,
      dual_tprod_mulVec, dualBound, Finset.sum_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_)
    rw [norm_mul, norm_prod, mul_comm, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hprod : ∏ i, ‖((A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ m i) (r i)‖ ≤ ∏ i, (2 * M * ‖m i‖) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ norm_mulVec_apply_le hA (m i) (r i)
    refine hprod.trans_eq ?_
    simp [Finset.prod_mul_distrib]
    ring1
  | zero =>
    exact ⟨0, fun A M _ ↦ by simp⟩
  | add x y _ _ hx hy =>
    rcases hx with ⟨C₁, h₁⟩
    rcases hy with ⟨C₂, h₂⟩
    refine ⟨C₁ + C₂, fun A M hA ↦ ?_⟩
    rw [map_add, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ A M hA) (h₂ A M hA))
  | smul a x _ hx =>
    rcases hx with ⟨C, h⟩
    refine ⟨‖a‖ * C, fun A M hA ↦ ?_⟩
    rw [map_smul, map_smul, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h A M hA) (norm_nonneg _)

variable (k : ℤ) (c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ)

lemma rhoKJ_apply (A : GL (Fin 2) ℂ) (u : Sym[ℂ]^j (Fin 2 → ℂ)) :
    rhoKJ k j A u = ((A.det ^ k : ℂˣ) : ℂ) • TauCeti.symPowerRep ℂ 2 j A u :=
  rfl

private lemma val_det_imGL_zpow (τ : SiegelUpperHalfSpace (Fin 2)) :
    (((imGL τ).det ^ k : ℂˣ) : ℂ) = (((τ.val.map im).det ^ k : ℝ) : ℂ) := by
  rw [Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, coe_imGL, det_map_ofReal,
    ofReal_zpow]

private lemma continuous_symPowerRep_imGL (ψ : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ)))
    (u : Sym[ℂ]^j (Fin 2 → ℂ)) :
    Continuous fun τ : SiegelUpperHalfSpace (Fin 2) ↦ ψ (TauCeti.symPowerRep ℂ 2 j (imGL τ) u) := by
  have h : Continuous fun τ : SiegelUpperHalfSpace (Fin 2) ↦
      (fun a c ↦ ((τ.val a c).im : ℂ) : Fin 2 → Fin 2 → ℂ) :=
    continuous_pi fun a ↦ continuous_pi fun c ↦ continuous_ofReal.comp (continuous_im_apply a c)
  refine ((differentiable_symmetricPower_map ψ u).continuous.comp h).congr fun τ ↦ ?_
  rw [Function.comp_apply, Representation.symmetricPower_apply, TauCeti.stdRep_apply]
  rfl

private lemma continuous_det_zpow :
    Continuous fun τ : SiegelUpperHalfSpace (Fin 2) ↦ (τ.val.map im).det ^ k := by
  have h : Continuous fun τ : SiegelUpperHalfSpace (Fin 2) ↦ (τ.val.map im).det :=
    Continuous.matrix_det (continuous_matrix fun a c ↦ continuous_im_apply a c)
  exact h.zpow₀ k fun τ ↦ Or.inl τ.posDef_im.det_pos.ne'

private lemma norm_det_zpow_le {τ : SiegelUpperHalfSpace (Fin 2)} (hτ : τ ∈ siegelSet) :
    (τ.val.map im).det ^ k ≤ ((25 : ℝ) / 12) ^ k.natAbs *
      (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ (2 * k.natAbs) := by
  have hτs : τ.val 1 0 = τ.val 0 1 := congrFun (congrFun τ.transpose_val 0) 1
  have h₀ : 4 / 5 ≤ (τ.val 0 0).im := four_fifths_le_im_zero_zero hτ
  have h₁ : 4 / 5 ≤ (τ.val 1 1).im := four_fifths_le_im_one_one hτ
  have hD : 12 / 25 ≤ (τ.val.map im).det := twelve_div_le_det_im hτ
  have hP : 1 ≤ 1 + (τ.val 0 0).im + (τ.val 1 1).im := by
    linarith
  have hDP : (τ.val.map im).det ≤ (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ 2 := by
    rw [det_fin_two]
    simp only [map_apply, hτs]
    nlinarith [mul_self_nonneg (τ.val 0 1).im]
  have hc₁ : (1 : ℝ) ≤ (25 / 12) ^ k.natAbs := one_le_pow₀ (by norm_num)
  have hc₂ : (1 : ℝ) ≤ (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ (2 * k.natAbs) := one_le_pow₀ hP
  generalize (τ.val.map im).det = D at hD hDP
  generalize 1 + (τ.val 0 0).im + (τ.val 1 1).im = P at hP hDP hc₂
  have hD₀ : 0 < D := by
    linarith
  rcases Int.natAbs_eq k with hk | hk
  · rw [hk, Int.natAbs_natCast, zpow_natCast, pow_mul]
    have h₂ : D ^ k.natAbs ≤ (P ^ 2) ^ k.natAbs := pow_le_pow_left₀ hD₀.le hDP _
    rw [pow_mul] at hc₂
    nlinarith [pow_pos hD₀ k.natAbs]
  · rw [hk, Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, ← inv_pow]
    have h₂ : D⁻¹ ≤ 25 / 12 := by
      rw [inv_le_comm₀ hD₀ (by norm_num)]
      convert hD using 1
      norm_num
    have h₃ : D⁻¹ ^ k.natAbs ≤ (25 / 12) ^ k.natAbs :=
      pow_le_pow_left₀ (inv_pos.mpr hD₀).le h₂ _
    nlinarith [pow_pos (inv_pos.mpr hD₀) k.natAbs]

/-- **Every sesquilinear form on `Sym^j(ℂ²)` is moderate for `ρ_{k,j}`.** -/
lemma isModerateForm_rhoKJ : IsModerateForm (rhoKJ k j) c where
  continuous v w := by
    have e : (fun τ : SiegelUpperHalfSpace (Fin 2) ↦ c (rhoKJ k j (imGL τ) v) w) = fun τ ↦
        (((τ.val.map im).det ^ k : ℝ) : ℂ) * c.flip w (TauCeti.symPowerRep ℂ 2 j (imGL τ) v) := by
      funext τ
      rw [rhoKJ_apply, val_det_imGL_zpow, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rfl
    rw [e]
    exact (continuous_ofReal.comp (continuous_det_zpow k)).mul (continuous_symPowerRep_imGL _ v)
  exists_bound := by
    refine ⟨2 * k.natAbs + j, fun v w ↦ ?_⟩
    rcases exists_norm_dual_symPowerRep_le (c.flip w) v with ⟨C, hC⟩
    refine ⟨((25 : ℝ) / 12) ^ k.natAbs * C, fun τ hτ ↦ ?_⟩
    have hτs : τ.val 1 0 = τ.val 0 1 := congrFun (congrFun τ.transpose_val 0) 1
    have h₀ : 4 / 5 ≤ (τ.val 0 0).im := four_fifths_le_im_zero_zero hτ
    have h₁ : 4 / 5 ≤ (τ.val 1 1).im := four_fifths_le_im_one_one hτ
    have h₂ : |(τ.val 0 1).im| ≤ (τ.val 0 0).im := abs_im_zero_one_le hτ
    have hentries (a c : Fin 2) : ‖((imGL τ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) a c‖ ≤ 1 +
        (τ.val 0 0).im + (τ.val 1 1).im := by
      rw [coe_imGL]
      simp only [map_apply, Complex.norm_real, Real.norm_eq_abs]
      fin_cases a <;> fin_cases c <;> simp only [Fin.zero_eta, Fin.mk_one, hτs]
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · linarith
      · linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    have h₃ : ‖c (TauCeti.symPowerRep ℂ 2 j (imGL τ) v) w‖ ≤
        C * (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ j :=
      hC (imGL τ) _ hentries
    have h₅ : (τ.val.map im).det ^ k ≤ ((25 : ℝ) / 12) ^ k.natAbs *
        (1 + (τ.val 0 0).im + (τ.val 1 1).im) ^ (2 * k.natAbs) :=
      norm_det_zpow_le k hτ
    have hD : 0 ≤ (τ.val.map im).det ^ k := zpow_nonneg τ.posDef_im.det_pos.le k
    rw [rhoKJ_apply, val_det_imGL_zpow, map_smul, LinearMap.smul_apply, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hD]
    refine (mul_le_mul h₅ h₃ (norm_nonneg _) ?_).trans_eq ?_
    · have hP : 0 ≤ 1 + (τ.val 0 0).im + (τ.val 1 1).im := by
        linarith
      positivity
    · rw [pow_add]
      ring1

/-! ### The Hermitian form on `Sym^j(ℂ²)` -/

/-- The coordinate `u₁ ⊗ ⋯ ⊗ u_j ↦ ∏ᵢ uᵢ(r i)` of a tensor. -/
private noncomputable def tensorCoord (r : Fin j → Fin 2) : (⨂[ℂ] _ : Fin j, Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin j) ℂ).compLinearMap
    fun i ↦ LinearMap.proj (r i))

private lemma tensorCoord_tprod (r : Fin j → Fin 2) (m : Fin j → Fin 2 → ℂ) :
    tensorCoord r (⨂ₜ[ℂ] i, m i) = ∏ i, m i (r i) := by
  simp [tensorCoord]

private lemma tensorCoord_map (A : Matrix (Fin 2) (Fin 2) ℂ) (r : Fin j → Fin 2)
    (x : ⨂[ℂ] _ : Fin j, Fin 2 → ℂ) : tensorCoord r (PiTensorProduct.map (fun _ ↦ mulVecLin A) x) =
      ∑ s, (∏ i, A (r i) (s i)) * tensorCoord s x := by
  have h : tensorCoord r ∘ₗ PiTensorProduct.map (fun _ ↦ mulVecLin A) =
      ∑ s, (∏ i, A (r i) (s i)) • tensorCoord s := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun m ↦ ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      tensorCoord_tprod, mulVecLin_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      mulVec, dotProduct, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.prod_mul_distrib]
  simpa using LinearMap.congr_fun h x

private lemma eq_sum_tensorCoord (x : ⨂[ℂ] _ : Fin j, Fin 2 → ℂ) :
    x = ∑ r : Fin j → Fin 2, tensorCoord r x • ⨂ₜ[ℂ] i, (Pi.single (r i) 1 : Fin 2 → ℂ) := by
  have h : LinearMap.id = ∑ r : Fin j → Fin 2,
      (tensorCoord r).smulRight (⨂ₜ[ℂ] i, (Pi.single (r i) 1 : Fin 2 → ℂ)) := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun m ↦ ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      tensorCoord_tprod]
    conv_lhs => rw [funext fun i ↦ pi_eq_sum_univ' (m i), MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun r _ ↦ MultilinearMap.map_smul_univ _ _ _
  simpa using LinearMap.congr_fun h x

/-- The **coordinate** `T_r` of a symmetric tensor in `Sym^j(ℂ²)`, for `r : Fin j → Fin 2`:
`T_r(u₁ ⋯ u_j) = ∑_σ ∏_i u_{σ i}(r i)`. -/
noncomputable def symCoord (r : Fin j → Fin 2) : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
  tensorCoord r ∘ₗ SymmetricPower.toTensorPower ℂ (Fin j) (Fin 2 → ℂ)

lemma symCoord_symPowerRep (A : GL (Fin 2) ℂ) (r : Fin j → Fin 2) (u : Sym[ℂ]^j (Fin 2 → ℂ)) :
    symCoord r (TauCeti.symPowerRep ℂ 2 j A u) =
      ∑ s, (∏ i, (A : Matrix (Fin 2) (Fin 2) ℂ) (r i) (s i)) * symCoord s u := by
  have h : SymmetricPower.toTensorPower ℂ (Fin j) (Fin 2 → ℂ)
      (SymmetricPower.map (ι := Fin j) (mulVecLin (A : Matrix (Fin 2) (Fin 2) ℂ)) u) =
        PiTensorProduct.map (fun _ ↦ mulVecLin (A : Matrix (Fin 2) (Fin 2) ℂ))
          (SymmetricPower.toTensorPower ℂ (Fin j) (Fin 2 → ℂ) u) :=
    LinearMap.congr_fun (SymmetricPower.toTensorPower_comp_map (R := ℂ) (ι := Fin j)
      (mulVecLin (A : Matrix (Fin 2) (Fin 2) ℂ))) u
  rw [symCoord, LinearMap.comp_apply, Representation.symmetricPower_apply, TauCeti.stdRep_apply, h,
    tensorCoord_map]
  rfl

private lemma exists_symCoord_ne_zero {u : Sym[ℂ]^j (Fin 2 → ℂ)} (hu : u ≠ 0) :
    ∃ r, symCoord r u ≠ 0 := by
  by_contra hall
  push Not at hall
  refine hu (SymmetricPower.toTensorPower_injective (R := ℂ) (ι := Fin j) (M := Fin 2 → ℂ)
    (IsUnit.mk0 _ (by exact_mod_cast Nat.factorial_ne_zero _)) ?_)
  rw [map_zero, eq_sum_tensorCoord (SymmetricPower.toTensorPower ℂ (Fin j) (Fin 2 → ℂ) u)]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  have h : tensorCoord r (SymmetricPower.toTensorPower ℂ (Fin j) (Fin 2 → ℂ) u) = 0 := hall r
  rw [h, zero_smul]

variable (j) in
/-- The **Hermitian form** `c(v, w) = ∑_r T_r(v) conj(T_r(w))` on `Sym^j(ℂ²)`, induced by the
standard Hermitian form on `ℂ²`. It is positive definite (`symHermitianForm_pos`) and admissible for
`ρ_{k,j}` (`isAdmissibleForm_symHermitianForm`), and it is the form with respect to which the
Petersson product of vector-valued Siegel modular forms of degree 2 is taken. -/
noncomputable def symHermitianForm : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w ↦ ∑ r, symCoord r v * conj (symCoord r w))
    (fun v v' w ↦ by simp [add_mul, Finset.sum_add_distrib])
    (fun a v w ↦ by simp [Finset.mul_sum, mul_assoc])
    (fun v w w' ↦ by simp [mul_add, Finset.sum_add_distrib])
    (fun a v w ↦ by simp [Finset.mul_sum, mul_left_comm])

lemma symHermitianForm_apply (u w : Sym[ℂ]^j (Fin 2 → ℂ)) :
    symHermitianForm j u w = ∑ r, symCoord r u * conj (symCoord r w) :=
  rfl

/-- **The form `symHermitianForm` is Hermitian.** -/
lemma conj_symHermitianForm (u w : Sym[ℂ]^j (Fin 2 → ℂ)) :
    conj (symHermitianForm j u w) = symHermitianForm j w u := by
  simp [symHermitianForm_apply, mul_comm]

/-- **The form `symHermitianForm` is positive definite.** -/
lemma symHermitianForm_pos {u : Sym[ℂ]^j (Fin 2 → ℂ)} (hu : u ≠ 0) :
    0 < symHermitianForm j u u := by
  rcases exists_symCoord_ne_zero hu with ⟨r, hr⟩
  rw [symHermitianForm_apply]
  have hpos (s : Fin j → Fin 2) : 0 ≤ symCoord s u * conj (symCoord s u) := by
    rw [mul_conj]
    exact zero_le_real.mpr (normSq_nonneg _)
  refine Finset.sum_pos' (fun s _ ↦ hpos s) ⟨r, Finset.mem_univ r, ?_⟩
  rw [mul_conj]
  exact zero_lt_real.mpr (normSq_pos.mpr hr)

private lemma symHermitianForm_symPowerRep (A : GL (Fin 2) ℂ) (u w : Sym[ℂ]^j (Fin 2 → ℂ)) :
    symHermitianForm j (TauCeti.symPowerRep ℂ 2 j A u) w =
      symHermitianForm j u (TauCeti.symPowerRep ℂ 2 j (star A) w) := by
  simp only [symHermitianForm_apply, symCoord_symPowerRep, map_sum, map_mul, map_prod,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun r _ ↦ ?_
  have e : ∏ i, conj (((star A : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) (s i) (r i)) =
      ∏ i, (A : Matrix (Fin 2) (Fin 2) ℂ) (r i) (s i) :=
    Finset.prod_congr rfl fun i _ ↦ by simp
  rw [e]
  ring1

/-- **The form `symHermitianForm` is admissible for `ρ_{k,j}`**: `c(ρ(A) v, w) = c(v, ρ(Aᴴ) w)`. -/
lemma isAdmissibleForm_symHermitianForm : IsAdmissibleForm (rhoKJ k j) (symHermitianForm j) := by
  intro A u w
  have hdet : ((GeneralLinearGroup.det (star A) ^ k : ℂˣ) : ℂ) =
      conj ((GeneralLinearGroup.det A ^ k : ℂˣ) : ℂ) := by
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀]
    simp [star_eq_conjTranspose]
  rw [rhoKJ_apply, rhoKJ_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hdet,
    Complex.conj_conj, symHermitianForm_symPowerRep]

end SiegelUpperHalfSpace
