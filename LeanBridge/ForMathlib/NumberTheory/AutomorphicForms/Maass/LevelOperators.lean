import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeSelfAdjoint
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.LaplacianMoebius
import LeanBridge.ForMathlib.NumberTheory.ModularForms.LowerUnipotent

/-!
# Level-changing operators on Maass forms

For a function `F` on `ℍ` and a prime `q`, this file studies the operators

* `(U_q F)(w) = ∑_{j < q} F((w + j)/q)`;
* `(E_q F)(z) = q⁻¹ ∑_{j < q} F(z + j/q) = q⁻¹ (U_q F)(qz)`;
* `(Tr H)(z) = q⁻¹ ∑_{i < q} H(!![1, 0; N i, 1] z)`, the trace from `Γ₀(Nq)` to `Γ₀(N)`, for
  `q ∣ N`.

For `F` in `M(N, 1, λ)` with `q ∣ N`, `U_q F` lies in `M(N, 1, λ)`, and in `M(N / q, 1, λ)` if
`q² ∣ N`; `E_q F` lies in `M(Nq, 1, λ)`; and the trace maps `M(Nq, 1, λ)` to `M(N, 1, λ)` and
commutes with the level raising `G ↦ G(d ·)`. The key identity behind the Main Lemma of Atkin and
Lehner (`UpperHalfPlane.sub_maassLevelTrace_maassPeriodAverage`) is: for `N = qM`,
`F - Tr (E_q F) = c (F - Z(q ·))` with `c ≠ 0` and `Z` in `M(M, 1, λ)`. Writing `G(w) = F(w / q)`, a
function invariant under `Γ₀(M) ∩ Γ⁰(q) = diag(q, 1) Γ₀(qM) diag(q, 1)⁻¹`, one has
`q² Tr (E_q F)(z) = ∑_{i, j} G(T^j !![1, 0; M i, 1] (qz))`. If `q ∣ M`, the matrices `T^j` represent
the `q` cosets of `Γ₀(M) ∩ Γ⁰(q)` in `Γ₀(M)` and `!![1, 0; M i, 1]` changes nothing: `Tr (E_q F) =
q⁻¹ (U_q F)(q ·)`, with `U_q F` of level `M`, so that `c = 1`. If `q ∤ M`, there are `q + 1` cosets:
the matrices with `j = 0` lie in the trivial one, and those with a given `j ≠ 0` run once through
the `q` others, so that `q² Tr (E_q F) = F + (q - 1) Y(q ·)` for `Y` the trace of `G` to `Γ₀(M)`,
and `c = 1 - q⁻²`.

## Main definitions

* `UpperHalfPlane.IsRightCosetTransversal`: systems of representatives of right cosets.
* `UpperHalfPlane.gammaZeroUpper`: the subgroup `Γ₀(M) ∩ Γ⁰(q)`.
* `UpperHalfPlane.maassLevelLower`: the function `w ↦ F(w / q)`.
* `UpperHalfPlane.maassUpOperator`: the operator `U_q`.
* `UpperHalfPlane.maassPeriodAverage`: the operator `E_q`.
* `UpperHalfPlane.maassLevelTrace`: the trace from `Γ₀(Nq)` to `Γ₀(N)`.
* `UpperHalfPlane.maassLowerTrace`: the trace of `w ↦ F(w / q)` to `Γ₀(M)` for a prime `q ∤ M`.
* `UpperHalfPlane.maassTraceConstant`, `UpperHalfPlane.maassTraceRemainder`: the constant `c` and
  the function `Z` of the key identity.

## Main results

* `UpperHalfPlane.sum_comp_mem_maassSpace`: the trace along a coset transversal is a Maass form.
* `UpperHalfPlane.isRightCosetTransversal_lowerUnipotent`,
  `UpperHalfPlane.isRightCosetTransversal_T_zpow`, `UpperHalfPlane.isRightCosetTransversal_option`:
  the coset representatives.
* `UpperHalfPlane.maassLevelLower_smul`: `w ↦ F(w / q)` is invariant under `Γ₀(M) ∩ Γ⁰(q)`.
* `UpperHalfPlane.maassUpOperator_mem_maassSpace`: `U_q` lowers the level.
* `UpperHalfPlane.maassPeriodAverage_mem_maassSpace`: `E_q` raises the level by `q`.
* `UpperHalfPlane.maassLevelTrace_mem_maassSpace`: the trace lowers the level by `q`.
* `UpperHalfPlane.maassLevelTrace_maassLevelRaise`: the trace commutes with the level raising.
* `UpperHalfPlane.sub_maassLevelTrace_maassPeriodAverage`: the key identity.
-/

open CongruenceSubgroup ModularGroup Matrix SpecialLinearGroup HeckeRing

open scoped MatrixGroups

namespace UpperHalfPlane

variable {Γ' Γ : Subgroup SL(2, ℤ)} {ι ι' : Type*} {r : ι → SL(2, ℤ)} {γ δ g : SL(2, ℤ)} {j x : ℤ}
  {N M q d : ℕ} {χ : DirichletCharacter ℂ N} {eigenvalue : ℂ} {F G H : ℍ → ℂ}

variable (Γ' Γ r) in
/-- `r` is a **system of representatives of the right cosets** `Γ' r_i` of `Γ'` in `Γ`: every `r_i`
lies in `Γ`, and every `γ ∈ Γ` lies in exactly one coset `Γ' r_i`. No inclusion `Γ' ≤ Γ` is
asked for. -/
def IsRightCosetTransversal : Prop :=
  (∀ i, r i ∈ Γ) ∧ ∀ γ ∈ Γ, ∃! i, r i * γ⁻¹ ∈ Γ'

lemma IsRightCosetTransversal.sum_eq [Fintype ι] [Fintype ι'] {r' : ι' → SL(2, ℤ)}
    (hr : IsRightCosetTransversal Γ' Γ r) (hr' : IsRightCosetTransversal Γ' Γ r')
    (hH : ∀ δ ∈ Γ', ∀ τ : ℍ, H (δ • τ) = H τ) (τ : ℍ) : ∑ i, H (r i • τ) = ∑ i, H (r' i • τ) := by
  choose f hf using fun i ↦ (hr'.2 (r i) (hr.1 i)).exists
  have hbij : Function.Bijective f := by
    refine ⟨fun i j hij ↦ ?_, fun i' ↦ ?_⟩
    · refine (hr.2 (r j) (hr.1 j)).unique ?_ (by simp)
      have h1 : r' (f j) * (r i)⁻¹ ∈ Γ' := hij ▸ hf i
      have h : r i * (r j)⁻¹ = (r' (f j) * (r i)⁻¹)⁻¹ * (r' (f j) * (r j)⁻¹) := by
        group
      rw [h]
      exact mul_mem (inv_mem h1) (hf j)
    · rcases (hr.2 (r' i') (hr'.1 i')).exists with ⟨i, hi⟩
      refine ⟨i, (hr'.2 (r i) (hr.1 i)).unique (hf i) ?_⟩
      simpa using inv_mem hi
  rw [← hbij.sum_comp fun i' ↦ H (r' i' • τ)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : r' (f i) = (r' (f i) * (r i)⁻¹) * r i := by
    group
  rw [h, mul_smul, hH _ (hf i)]

lemma IsRightCosetTransversal.mul_right (hr : IsRightCosetTransversal Γ' Γ r) (hγ : γ ∈ Γ) :
    IsRightCosetTransversal Γ' Γ fun i ↦ r i * γ := by
  refine ⟨fun i ↦ mul_mem (hr.1 i) hγ, fun g hg ↦ ?_⟩
  simpa [mul_assoc] using hr.2 (g * γ⁻¹) (mul_mem hg (inv_mem hγ))

lemma IsRightCosetTransversal.sum_smul_smul [Fintype ι] (hr : IsRightCosetTransversal Γ' Γ r)
    (hH : ∀ δ ∈ Γ', ∀ τ : ℍ, H (δ • τ) = H τ) (hγ : γ ∈ Γ) (τ : ℍ) :
    ∑ i, H (r i • γ • τ) = ∑ i, H (r i • τ) := by
  simpa only [mul_smul] using (hr.mul_right hγ).sum_eq hr hH τ

variable [NeZero N] in
/-- **The trace of an invariant function along a coset transversal is a Maass form**: for `H`
invariant under `Γ'` all of whose compositions with `SL(2, ℤ)` lie in `maassTileSpace λ`, and `r` a
system of representatives of the right cosets of `Γ'` in `Γ₀(N)`, the function
`z ↦ ∑_i H(r_i z)` lies in `M(N, 1, λ)`. -/
lemma sum_comp_mem_maassSpace [Fintype ι] (hr : IsRightCosetTransversal Γ' (Gamma0 N) r)
    (hH : ∀ δ ∈ Γ', ∀ τ : ℍ, H (δ • τ) = H τ)
    (hmem : ∀ σ : SL(2, ℤ), (fun τ ↦ H (σ • τ)) ∈ maassTileSpace eigenvalue) :
    (fun τ ↦ ∑ i, H (r i • τ)) ∈ maassSpace N 1 eigenvalue := by
  refine mem_maassSpace_of_mem_maassTileSpace ?_ fun γ hγ τ ↦ hr.sum_smul_smul hH hγ τ
  have h : (fun τ ↦ ∑ i, H (r i • τ)) = ∑ i, fun τ ↦ H (r i • τ) := by
    funext τ
    simp
  rw [h]
  exact Submodule.sum_mem _ fun i _ ↦ hmem (r i)

variable (x) in
lemma lowerUnipotent_apply_zero_zero : lowerUnipotent x 0 0 = 1 :=
  rfl

variable (x) in
lemma lowerUnipotent_apply_zero_one : lowerUnipotent x 0 1 = 0 :=
  rfl

variable (x) in
lemma lowerUnipotent_apply_one_zero : lowerUnipotent x 1 0 = x :=
  rfl

variable (x) in
lemma lowerUnipotent_apply_one_one : lowerUnipotent x 1 1 = 1 :=
  rfl

variable (M q) in
/-- The subgroup `Γ₀(M) ∩ Γ⁰(q)` of `SL(2, ℤ)`: the matrices `!![a, b; c, d]` with `M ∣ c` and
`q ∣ b`. For `F` invariant under `Γ₀(qM)`, the function `w ↦ F(w / q)` is invariant under it
(`maassLevelLower_smul`). -/
def gammaZeroUpper : Subgroup SL(2, ℤ) where
  carrier := {γ | (M : ℤ) ∣ γ 1 0 ∧ (q : ℤ) ∣ γ 0 1}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · rw [sl_mul_apply_one_zero]
      exact dvd_add (hx.1.mul_right _) (hy.1.mul_left _)
    · have h : (x * y) 0 1 = x 0 0 * y 0 1 + x 0 1 * y 1 1 := by
        simp [Matrix.mul_apply]
      rw [h]
      exact dvd_add (hy.2.mul_left _) (hx.2.mul_right _)
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' {x} hx := by
    refine ⟨?_, ?_⟩
    · rw [inv_apply_one_zero]
      exact dvd_neg.mpr hx.1
    · rw [inv_apply_zero_one]
      exact dvd_neg.mpr hx.2

lemma mem_gammaZeroUpper_iff : γ ∈ gammaZeroUpper M q ↔ (M : ℤ) ∣ γ 1 0 ∧ (q : ℤ) ∣ γ 0 1 :=
  Iff.rfl

variable (γ q) in
lemma det_intCast_zmod : ((γ 0 0 : ℤ) : ZMod q) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
  have h : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := (det_fin_two _).symm.trans γ.2
  exact_mod_cast congrArg (Int.cast : ℤ → ZMod q) h

lemma intCast_mul_intCast_eq_one (h : ((γ 0 1 : ℤ) : ZMod q) * (γ 1 0 : ℤ) = 0) :
    ((γ 0 0 : ℤ) : ZMod q) * (γ 1 1 : ℤ) = 1 := by
  linear_combination det_intCast_zmod γ q + h

variable (g) in
lemma T_zpow_mul_apply_zero_one : (T ^ j * g) 0 1 = g 0 1 + j * g 1 1 := by
  simp [Matrix.mul_apply, coe_T_zpow]

variable (g) in
lemma T_zpow_mul_apply_one_zero : (T ^ j * g) 1 0 = g 1 0 := by
  simp

variable (x g) in
lemma lowerUnipotent_mul_apply_zero_one : (lowerUnipotent x * g) 0 1 = g 0 1 := by
  simp [Matrix.mul_apply, lowerUnipotent_apply_zero_zero, lowerUnipotent_apply_zero_one]

variable (x g) in
lemma lowerUnipotent_mul_apply_one_one : (lowerUnipotent x * g) 1 1 = x * g 0 1 + g 1 1 := by
  simp [Matrix.mul_apply, lowerUnipotent_apply_one_zero, lowerUnipotent_apply_one_one]

variable (x g) in
lemma lowerUnipotent_mul_apply_one_zero : (lowerUnipotent x * g) 1 0 = x * g 0 0 + g 1 0 := by
  simp [Matrix.mul_apply, lowerUnipotent_apply_one_zero, lowerUnipotent_apply_one_one]

lemma lowerUnipotent_mem_gamma0_iff : lowerUnipotent x ∈ Gamma0 N ↔ (N : ℤ) ∣ x := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, lowerUnipotent_apply_one_zero]

variable [NeZero q] in
lemma sum_range_eq_sum_zmod {E : Type*} [AddCommMonoid E] (f : ℕ → E) :
    ∑ j ∈ Finset.range q, f j = ∑ x : ZMod q, f x.val := by
  rcases q with _ | n
  · exact absurd rfl (NeZero.ne 0)
  · exact (Fin.sum_univ_eq_sum_range f (n + 1)).symm

variable [NeZero N] in
lemma comp_sl_smul_mem_maassTileSpace (hF : F ∈ maassSpace N χ eigenvalue) (σ : SL(2, ℤ)) :
    (fun τ ↦ F (σ • τ)) ∈ maassTileSpace eigenvalue := by
  have h : (fun z ↦ F ((mapGL ℚ σ).map (algebraMap ℚ ℝ) • z)) ∈ maassTileSpace eigenvalue :=
    comp_smul_mem_maassTileSpace hF (mapGL ℚ σ) (by simp [← Int.cast_det])
  simp only [map_mapGL] at h
  exact h

variable [NeZero N] in
lemma maassSpace_le_of_dvd {N' : ℕ} [NeZero N'] (h : N ∣ N') (hF : F ∈ maassSpace N 1 eigenvalue) :
    F ∈ maassSpace N' 1 eigenvalue := by
  refine mem_maassSpace_of_mem_maassTileSpace ?_
    fun γ hγ τ ↦ smul_eq_of_mem_maassSpace_one hF (Gamma0_le_Gamma0_of_dvd h hγ)
  simpa using comp_sl_smul_mem_maassTileSpace hF 1

variable (q F) in
/-- The function `w ↦ F(w / q)` on `ℍ`: the inverse of `maassLevelRaise q`
(`maassLevelRaise_maassLevelLower`). -/
noncomputable def maassLevelLower : ℍ → ℂ :=
  fun w ↦ F (ofComplex ((w : ℂ) / q))

lemma maassLevelRaise_maassLevelLower (hq : q ≠ 0) :
    maassLevelRaise q (maassLevelLower q F) = F := by
  funext z
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hz : 0 < ((q : ℂ) * z).im := by
    simpa using mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)) z.im_pos
  rw [maassLevelRaise, maassLevelLower, coe_ofComplex_of_im_pos hz, mul_div_cancel_left₀ _ hq',
    ofComplex_apply]

/-- **`w ↦ F(w / q)` is invariant under `Γ₀(M) ∩ Γ⁰(q)`** for `F` invariant under `Γ₀(qM)`:
`diag(q, 1)` conjugates `Γ₀(qM)` onto `Γ₀(M) ∩ Γ⁰(q)`. -/
lemma maassLevelLower_smul (hq : q ≠ 0) (hF : ∀ γ ∈ Gamma0 (q * M), ∀ τ : ℍ, F (γ • τ) = F τ)
    (hδ : δ ∈ gammaZeroUpper M q) (w : ℍ) :
    maassLevelLower q F (δ • w) = maassLevelLower q F w := by
  rcases hδ.2 with ⟨k, hk⟩
  have hdet : δ 0 0 * δ 1 1 - k * ((q : ℤ) * δ 1 0) = 1 := by
    have h : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := (det_fin_two _).symm.trans δ.2
    rw [hk] at h
    linear_combination h
  let γ : SL(2, ℤ) := ⟨!![δ 0 0, k; (q : ℤ) * δ 1 0, δ 1 1], by rwa [det_fin_two_of]⟩
  have hγ : γ ∈ Gamma0 (q * M) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul]
    exact mul_dvd_mul_left _ hδ.1
  have hd : (q : ℤ) ∣ γ 1 0 := dvd_mul_right _ _
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hz : 0 < ((w : ℂ) / q).im := by
    simpa using div_pos w.im_pos (Nat.cast_pos.mpr hq0)
  have hscale : gammaZeroScale q γ hd = δ := by
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact hk.symm
    · exact Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hq)
    · rfl
  have h1 : ((q : ℂ) * ((ofComplex ((w : ℂ) / q) : ℍ) : ℂ)) = w := by
    rw [coe_ofComplex_of_im_pos hz, mul_div_cancel₀ _ hq']
  have h2 : ((δ • w : ℍ) : ℂ) / q = ((γ • ofComplex ((w : ℂ) / q) : ℍ) : ℂ) := by
    have h3 : ((δ • w : ℍ) : ℂ) = (q : ℂ) * ((γ • ofComplex ((w : ℂ) / q) : ℍ) : ℂ) := by
      rw [← coe_gammaZeroScale_smul hd hq0, hscale, h1, ofComplex_apply]
    rw [h3, mul_div_cancel_left₀ _ hq']
  rw [maassLevelLower, maassLevelLower, h2, ofComplex_apply, hF γ hγ]

variable [NeZero N] in
lemma maassLevelLower_comp_mem_maassTileSpace (hq : q ≠ 0) (hF : F ∈ maassSpace N χ eigenvalue)
    (σ : SL(2, ℤ)) : (fun τ ↦ maassLevelLower q F (σ • τ)) ∈ maassTileSpace eigenvalue := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq
  let b : Fin q := ⟨0, hq0⟩
  have hdet : ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    simp [← Int.cast_det]
  have h : (fun z ↦ F ((GL2.upperTriRep q b * mapGL ℚ σ).map (algebraMap ℚ ℝ) • z)) ∈
      maassTileSpace eigenvalue :=
    comp_smul_mem_maassTileSpace hF (GL2.upperTriRep q b * mapGL ℚ σ) <| by
      rw [Units.val_mul, det_mul, hdet, mul_one]
      exact GL2.det_upperTriRep_pos q b
  convert h using 2 with τ
  rw [maassLevelLower, map_mul, map_mapGL, mul_smul, ← ofComplex_apply
    ((GeneralLinearGroup.map (algebraMap ℚ ℝ)) (GL2.upperTriRep q b) • _), GL2.coe_upperTriRep_smul]
  simp only [b, Nat.cast_zero, add_zero]
  rfl

variable (q F) in
/-- The operator `U_q` on functions on `ℍ`, without normalisation:
`(U_q F)(w) = ∑_{j < q} F((w + j)/q)`, written as `∑_{j < q} G(T^j w)` for `G(w) = F(w / q)`. It
preserves `M(N, 1, λ)` for a prime `q ∣ N` and lowers the level of `F` to `N / q` when `q² ∣ N`
(`maassUpOperator_mem_maassSpace`). -/
noncomputable def maassUpOperator : ℍ → ℂ :=
  fun w ↦ ∑ j ∈ Finset.range q, maassLevelLower q F (T ^ (j : ℤ) • w)

variable (q F) in
/-- The average `(E_q F)(z) = q⁻¹ ∑_{j < q} F(z + j/q)` of a function `F` on `ℍ` over the
translations by `j / q`. For `F` with a Fourier expansion in `x`, it keeps exactly the terms whose
index is divisible by `q`. -/
noncomputable def maassPeriodAverage : ℍ → ℂ :=
  fun z ↦ (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, F (ofComplex ((z : ℂ) + j / q))

lemma maassPeriodAverage_eq (hq : q ≠ 0) (z : ℍ) :
    maassPeriodAverage q F z = (q : ℂ)⁻¹ * maassLevelRaise q (maassUpOperator q F) z := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hz : 0 < ((q : ℂ) * z).im := by
    simpa using mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)) z.im_pos
  rw [maassPeriodAverage, maassLevelRaise, maassUpOperator]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [maassLevelLower, coe_T_zpow_smul_eq, coe_ofComplex_of_im_pos hz]
  congr 2
  push_cast
  field_simp

variable (N q H) in
/-- The normalised trace `(Tr H)(z) = q⁻¹ ∑_{i < q} H(!![1, 0; N i, 1] z)` of a function `H` on
`ℍ`, from `Γ₀(Nq)` to `Γ₀(N)` for a prime `q ∣ N`: the matrices represent the right cosets of
`Γ₀(Nq)` in `Γ₀(N)` (`isRightCosetTransversal_lowerUnipotent`). -/
noncomputable def maassLevelTrace : ℍ → ℂ :=
  fun z ↦ (q : ℂ)⁻¹ * ∑ i ∈ Finset.range q, H (lowerUnipotent (N * i) • z)

lemma ofComplex_mul_lowerUnipotent_smul (hd : 0 < d) (z : ℍ) :
    ofComplex ((d : ℂ) * ((lowerUnipotent (d * x) • z : ℍ) : ℂ)) =
      lowerUnipotent x • ofComplex ((d : ℂ) * z) := by
  have hd' : (d : ℤ) ∣ lowerUnipotent (d * x) 1 0 := dvd_mul_right _ _
  have hscale : gammaZeroScale d (lowerUnipotent (d * x)) hd' = lowerUnipotent x := by
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · simp [gammaZeroScale, lowerUnipotent]
    · exact Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hd.ne')
    · rfl
  rw [← coe_gammaZeroScale_smul hd' hd, hscale, ofComplex_apply]

/-- **The trace commutes with the level raising**: for `d ≠ 0`,
`Tr_{dN, q} (G(d ·)) = (Tr_{N, q} G)(d ·)`, as `diag(d, 1)` conjugates the representatives
`!![1, 0; dN i, 1]` to `!![1, 0; N i, 1]`. -/
lemma maassLevelTrace_maassLevelRaise (hd : 0 < d) :
    maassLevelTrace (d * M) q (maassLevelRaise d G) =
      maassLevelRaise d (maassLevelTrace M q G) := by
  funext z
  simp only [maassLevelTrace, maassLevelRaise]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : ((d * M : ℕ) : ℤ) * i = d * (M * i) := by
    push_cast
    ring1
  rw [h, ofComplex_mul_lowerUnipotent_smul hd]

lemma maassLevelTrace_maassPeriodAverage (hq : q ≠ 0) (z : ℍ) :
    maassLevelTrace (q * M) q (maassPeriodAverage q F) z = (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ *
      ∑ i ∈ Finset.range q,
        maassUpOperator q F (lowerUnipotent (M * i) • ofComplex ((q : ℂ) * z))) := by
  rw [maassLevelTrace]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : ((q * M : ℕ) : ℤ) * i = q * (M * i) := by
    push_cast
    ring1
  rw [maassPeriodAverage_eq hq, maassLevelRaise, h,
    ofComplex_mul_lowerUnipotent_smul (Nat.pos_of_ne_zero hq)]

variable (M q F) in
/-- The trace of `w ↦ F(w / q)` from `Γ₀(M) ∩ Γ⁰(q)` to `Γ₀(M)` for a prime `q ∤ M`, along the
representatives `1` and `T !![1, 0; M i, 1]`, `i` modulo `q`, of
`isRightCosetTransversal_option`. -/
noncomputable def maassLowerTrace [NeZero q] : ℍ → ℂ :=
  fun w ↦ ∑ p : Option (ZMod q), maassLevelLower q F
    ((p.elim 1 fun i ↦ T ^ (1 : ℤ) * lowerUnipotent (M * i.val) : SL(2, ℤ)) • w)

variable (M q) in
/-- The constant `c` of the key identity `F - Tr (E_q F) = c (F - Z(q ·))`
(`sub_maassLevelTrace_maassPeriodAverage`): `1` if `q ∣ M`, and `1 - q⁻²` otherwise. -/
noncomputable def maassTraceConstant : ℂ :=
  if q ∣ M then 1 else 1 - (q : ℂ)⁻¹ * (q : ℂ)⁻¹

variable (M q F) in
/-- The function `Z` of the key identity `F - Tr (E_q F) = c (F - Z(q ·))`
(`sub_maassLevelTrace_maassPeriodAverage`), of level `M`: `q⁻¹ U_q F` if `q ∣ M`, and
`q⁻² (q - 1) c⁻¹ Y` otherwise, for `Y` the trace `maassLowerTrace M q F`. -/
noncomputable def maassTraceRemainder [NeZero q] : ℍ → ℂ :=
  if q ∣ M then (q : ℂ)⁻¹ • maassUpOperator q F
  else ((q : ℂ)⁻¹ * (q : ℂ)⁻¹ * ((q : ℂ) - 1) / maassTraceConstant M q) • maassLowerTrace M q F

variable [hq : Fact q.Prime]

/-- **The lower unipotent matrices `!![1, 0; M i, 1]`, `i` modulo `q`, represent the right cosets
of `Γ₀(Mq)` in `Γ₀(M)`** for a prime `q ∣ M ≠ 0`. -/
lemma isRightCosetTransversal_lowerUnipotent (hqM : q ∣ M) (hM : M ≠ 0) :
    IsRightCosetTransversal (Gamma0 (M * q)) (Gamma0 M)
      fun i : ZMod q ↦ lowerUnipotent (M * i.val) := by
  refine ⟨fun i ↦ lowerUnipotent_mem_gamma0_iff.mpr (dvd_mul_right _ _), fun γ hγ ↦ ?_⟩
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ with ⟨c, hc⟩
  have hM' : (M : ℤ) ≠ 0 := by
    exact_mod_cast hM
  have key (i : ZMod q) : lowerUnipotent (M * i.val) * γ⁻¹ ∈ Gamma0 (M * q) ↔
      i * ((γ 1 1 : ℤ) : ZMod q) = c := by
    have h : (lowerUnipotent (M * i.val) * γ⁻¹) 1 0 = M * (i.val * γ 1 1 - c) := by
      rw [lowerUnipotent_mul_apply_one_zero, inv_apply_zero_zero, inv_apply_one_zero, hc]
      ring1
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, h, Nat.cast_mul, mul_dvd_mul_iff_left hM',
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, sub_eq_zero]
  have hd : ((γ 1 1 : ℤ) : ZMod q) ≠ 0 := right_ne_zero_of_mul_eq_one <|
    intCast_mul_intCast_eq_one <| mul_eq_zero_of_right _ <|
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr <| (Int.natCast_dvd_natCast.mpr hqM).trans ⟨c, hc⟩
  exact ⟨c / ((γ 1 1 : ℤ) : ZMod q), (key _).mpr (div_mul_cancel₀ _ hd),
    fun i hi ↦ eq_div_of_mul_eq hd ((key i).mp hi)⟩

/-- **The translations `T^j`, `j` modulo `q`, represent the right cosets of `Γ₀(M) ∩ Γ⁰(q)` in
`Γ₀(M)`** for a prime `q ∣ M`. -/
lemma isRightCosetTransversal_T_zpow (hqM : q ∣ M) :
    IsRightCosetTransversal (gammaZeroUpper M q) (Gamma0 M) fun j : ZMod q ↦ T ^ (j.val : ℤ) := by
  refine ⟨fun j ↦ ?_, fun γ hγ ↦ ?_⟩
  · rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [coe_T_zpow]
  · have hM : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
    have key (j : ZMod q) : T ^ (j.val : ℤ) * γ⁻¹ ∈ gammaZeroUpper M q ↔
        j * ((γ 0 0 : ℤ) : ZMod q) = (γ 0 1 : ℤ) := by
      rw [mem_gammaZeroUpper_iff, T_zpow_mul_apply_one_zero, T_zpow_mul_apply_zero_one,
        inv_apply_one_zero, inv_apply_zero_one, inv_apply_one_one,
        ← ZMod.intCast_zmod_eq_zero_iff_dvd _ q]
      push_cast
      rw [ZMod.natCast_zmod_val, neg_add_eq_sub, sub_eq_zero]
      exact and_iff_right (dvd_neg.mpr hM)
    have ha : ((γ 0 0 : ℤ) : ZMod q) ≠ 0 := left_ne_zero_of_mul_eq_one <|
      intCast_mul_intCast_eq_one <| mul_eq_zero_of_right _ <|
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr <| (Int.natCast_dvd_natCast.mpr hqM).trans hM
    exact ⟨(γ 0 1 : ℤ) / ((γ 0 0 : ℤ) : ZMod q), (key _).mpr (div_mul_cancel₀ _ ha),
      fun i hi ↦ eq_div_of_mul_eq ha ((key i).mp hi)⟩

/-- **For a prime `q ∤ M`, `1` and `T^j !![1, 0; M i, 1]`, `i` modulo `q`, represent the right
cosets of `Γ₀(M) ∩ Γ⁰(q)` in `Γ₀(M)`**, for every `j` prime to `q`. -/
lemma isRightCosetTransversal_option (hqM : ¬q ∣ M) (hj : (j : ZMod q) ≠ 0) :
    IsRightCosetTransversal (gammaZeroUpper M q) (Gamma0 M) fun p : Option (ZMod q) ↦
      p.elim 1 fun i ↦ T ^ j * lowerUnipotent (M * i.val) := by
  have hM0 : (M : ZMod q) ≠ 0 := fun h ↦ hqM ((ZMod.natCast_eq_zero_iff _ _).mp h)
  refine ⟨fun p ↦ ?_, fun γ hγ ↦ ?_⟩
  · rcases p with _ | i
    · exact one_mem _
    · refine mul_mem ?_ (lowerUnipotent_mem_gamma0_iff.mpr (dvd_mul_right _ _))
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [coe_T_zpow]
  · have hM : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
    have key0 : (1 : SL(2, ℤ)) * γ⁻¹ ∈ gammaZeroUpper M q ↔ ((γ 0 1 : ℤ) : ZMod q) = 0 := by
      rw [one_mul, mem_gammaZeroUpper_iff, inv_apply_one_zero, inv_apply_zero_one, dvd_neg, dvd_neg,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact and_iff_right hM
    have key (i : ZMod q) : T ^ j * lowerUnipotent (M * i.val) * γ⁻¹ ∈ gammaZeroUpper M q ↔
        (j : ZMod q) * (γ 0 0 : ℤ) = (γ 0 1 : ℤ) * (1 + j * M * i) := by
      rw [mem_gammaZeroUpper_iff, mul_assoc, T_zpow_mul_apply_one_zero, T_zpow_mul_apply_zero_one,
        lowerUnipotent_mul_apply_one_zero, lowerUnipotent_mul_apply_zero_one,
        lowerUnipotent_mul_apply_one_one, inv_apply_zero_zero, inv_apply_one_zero,
        inv_apply_zero_one, inv_apply_one_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd _ q]
      push_cast
      rw [ZMod.natCast_zmod_val, and_iff_right
        (dvd_add ((dvd_mul_right _ _).mul_right _) (dvd_neg.mpr hM))]
      constructor <;> intro h <;> linear_combination h
    by_cases hb : ((γ 0 1 : ℤ) : ZMod q) = 0
    · have ha : ((γ 0 0 : ℤ) : ZMod q) ≠ 0 := left_ne_zero_of_mul_eq_one <|
        intCast_mul_intCast_eq_one <| mul_eq_zero_of_left hb _
      refine ⟨none, key0.mpr hb, ?_⟩
      rintro (_ | i) hi
      · rfl
      · have h : (j : ZMod q) * (γ 0 0 : ℤ) = (γ 0 1 : ℤ) * (1 + j * M * i) := (key i).mp hi
        rw [hb, zero_mul] at h
        exact absurd h (mul_ne_zero hj ha)
    · refine ⟨some (((j : ZMod q) * (γ 0 0 : ℤ) / (γ 0 1 : ℤ) - 1) / (j * M)), ?_, ?_⟩
      · refine (key _).mpr ?_
        field_simp
        ring1
      · rintro (_ | i) hi
        · exact absurd (key0.mp hi) hb
        · have h : (j : ZMod q) * (γ 0 0 : ℤ) = (γ 0 1 : ℤ) * (1 + j * M * i) := (key i).mp hi
          refine congrArg some ?_
          field_simp
          linear_combination -h

lemma maassUpOperator_eq_sum_zmod (w : ℍ) :
    maassUpOperator q F w = ∑ j : ZMod q, maassLevelLower q F (T ^ (j.val : ℤ) • w) :=
  sum_range_eq_sum_zmod _

lemma maassLevelTrace_eq_sum_zmod (z : ℍ) :
    maassLevelTrace M q H z = (q : ℂ)⁻¹ * ∑ i : ZMod q, H (lowerUnipotent (M * i.val) • z) := by
  rw [maassLevelTrace, sum_range_eq_sum_zmod fun i : ℕ ↦ H (lowerUnipotent (M * i) • z)]

lemma maassLevelTrace_eq_self (hF : F ∈ maassSpace M 1 eigenvalue) : maassLevelTrace M q F = F := by
  funext z
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  have h (i : ℕ) : F (lowerUnipotent (M * i) • z) = F z := smul_eq_of_mem_maassSpace_one hF <|
    lowerUnipotent_mem_gamma0_iff.mpr (dvd_mul_right _ _)
  simp only [maassLevelTrace, h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

lemma sum_maassLevelLower_T_zpow (hqM : ¬q ∣ M) (hj : (j : ZMod q) ≠ 0)
    (hF : ∀ γ ∈ Gamma0 (q * M), ∀ τ : ℍ, F (γ • τ) = F τ) (w : ℍ) :
    ∑ i ∈ Finset.range q, maassLevelLower q F (T ^ j • lowerUnipotent (M * i) • w) =
      maassLowerTrace M q F w - maassLevelLower q F w := by
  have h : ∑ p : Option (ZMod q), maassLevelLower q F
      ((p.elim 1 fun i ↦ T ^ j * lowerUnipotent (M * i.val) : SL(2, ℤ)) • w) =
        maassLowerTrace M q F w :=
    (isRightCosetTransversal_option (j := j) hqM hj).sum_eq
      (isRightCosetTransversal_option (j := 1) hqM (by simp))
      (fun δ hδ τ ↦ maassLevelLower_smul hq.out.ne_zero hF hδ τ) w
  rw [← h, Fintype.sum_option, sum_range_eq_sum_zmod
    fun i : ℕ ↦ maassLevelLower q F (T ^ j • lowerUnipotent (M * i) • w)]
  simp [mul_smul]

lemma sum_maassUpOperator_of_not_dvd (hqM : ¬q ∣ M)
    (hF : ∀ γ ∈ Gamma0 (q * M), ∀ τ : ℍ, F (γ • τ) = F τ) (w : ℍ) :
    ∑ i ∈ Finset.range q, maassUpOperator q F (lowerUnipotent (M * i) • w) = maassLevelLower q F w +
      ((q : ℂ) - 1) * maassLowerTrace M q F w := by
  have h0 (i : ℕ) : maassLevelLower q F (lowerUnipotent (M * i) • w) = maassLevelLower q F w :=
    maassLevelLower_smul hq.out.ne_zero hF
      ⟨(dvd_mul_right _ _ : (M : ℤ) ∣ M * i), (dvd_zero _ : (q : ℤ) ∣ 0)⟩ w
  simp only [maassUpOperator]
  rw [Finset.sum_comm]
  rcases Nat.exists_eq_succ_of_ne_zero hq.out.ne_zero with ⟨n, hn⟩
  have hsum : ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range q,
      maassLevelLower q F (T ^ (j : ℤ) • lowerUnipotent (M * i) • w) =
      ∑ j ∈ Finset.range n, (maassLowerTrace M q F w - maassLevelLower q F w) +
        (q : ℂ) * maassLevelLower q F w := by
    conv_lhs => rw [hn, Finset.sum_range_succ', ← hn]
    congr 1
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj' : j + 1 < q := by
        have hj1 : j < n := Finset.mem_range.mp hj
        omega
      refine sum_maassLevelLower_T_zpow hqM ?_ hF w
      intro h
      have h1 : ((j + 1 : ℕ) : ZMod q) = 0 := by
        exact_mod_cast h
      exact absurd (Nat.le_of_dvd (Nat.succ_pos _) ((ZMod.natCast_eq_zero_iff _ _).mp h1))
        (by omega)
    · simp only [Nat.cast_zero, zpow_zero, one_smul, h0, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn' : ((n : ℕ) : ℂ) = (q : ℂ) - 1 := by
    rw [hn]
    push_cast
    ring1
  rw [hn']
  ring1

lemma maassTraceConstant_ne_zero : maassTraceConstant M q ≠ 0 := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  rw [maassTraceConstant]
  split_ifs
  · exact one_ne_zero
  · intro h
    have h1 : (q : ℂ) * q = 1 := by
      field_simp at h
      linear_combination h
    have h2 : q * q = 1 := by
      exact_mod_cast h1
    exact hq.out.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h2)

variable [NeZero M]

/-- **`U_q` lowers the level**: for a prime `q ∣ M` and `F` in `M(qM, 1, λ)`, `U_q F` lies in
`M(M, 1, λ)`, the translations `T^j` representing the cosets of `Γ₀(M) ∩ Γ⁰(q)` in `Γ₀(M)`. -/
lemma maassUpOperator_mem_maassSpace (hqM : q ∣ M) (hF : F ∈ maassSpace (q * M) 1 eigenvalue) :
    maassUpOperator q F ∈ maassSpace M 1 eigenvalue := by
  have : NeZero (q * M) := ⟨mul_ne_zero hq.out.ne_zero (NeZero.ne M)⟩
  have h : (fun τ ↦ ∑ j : ZMod q, maassLevelLower q F (T ^ (j.val : ℤ) • τ)) ∈
      maassSpace M 1 eigenvalue :=
    sum_comp_mem_maassSpace (isRightCosetTransversal_T_zpow hqM)
      (fun δ hδ τ ↦ maassLevelLower_smul hq.out.ne_zero
        (fun γ hγ τ ↦ smul_eq_of_mem_maassSpace_one hF hγ) hδ τ)
      (maassLevelLower_comp_mem_maassTileSpace hq.out.ne_zero hF)
  have h0 : maassUpOperator q F = fun τ ↦ ∑ j : ZMod q, maassLevelLower q F (T ^ (j.val : ℤ) • τ) :=
    funext maassUpOperator_eq_sum_zmod
  rwa [h0]

/-- **`E_q` raises the level by `q`**: for a prime `q ∣ M` and `F` in `M(M, 1, λ)`, `E_q F` lies in
`M(Mq, 1, λ)`, being `q⁻¹ (U_q F)(qz)` with `U_q F` in `M(M, 1, λ)`. -/
lemma maassPeriodAverage_mem_maassSpace (hqM : q ∣ M) (hF : F ∈ maassSpace M 1 eigenvalue) :
    maassPeriodAverage q F ∈ maassSpace (M * q) 1 eigenvalue := by
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have : NeZero (q * M) := ⟨mul_ne_zero hq0 (NeZero.ne M)⟩
  have : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) hq0⟩
  have hU : maassUpOperator q F ∈ maassSpace M 1 eigenvalue :=
    maassUpOperator_mem_maassSpace hqM (maassSpace_le_of_dvd (dvd_mul_left M q) hF)
  have h : maassLevelRaise q (maassUpOperator q F) ∈ maassSpace (M * q)
      ((1 : DirichletCharacter ℂ M).changeLevel (dvd_mul_right M q)) eigenvalue :=
    maassLevelRaise_mem_maassSpace hU (Nat.pos_of_ne_zero hq0) (dvd_of_eq (mul_comm q M))
  rw [DirichletCharacter.changeLevel_one] at h
  have h0 : maassPeriodAverage q F = (q : ℂ)⁻¹ • maassLevelRaise q (maassUpOperator q F) :=
    funext (maassPeriodAverage_eq hq0)
  rw [h0]
  exact Submodule.smul_mem _ _ h

/-- **The trace lowers the level by `q`**: for a prime `q ∣ M`, `M ≠ 0`, and `H` in `M(Mq, 1, λ)`,
`Tr H` lies in `M(M, 1, λ)`. -/
lemma maassLevelTrace_mem_maassSpace (hqM : q ∣ M) (hH : H ∈ maassSpace (M * q) 1 eigenvalue) :
    maassLevelTrace M q H ∈ maassSpace M 1 eigenvalue := by
  have : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) hq.out.ne_zero⟩
  have h : (fun τ ↦ ∑ i : ZMod q, H (lowerUnipotent (M * i.val) • τ)) ∈ maassSpace M 1 eigenvalue :=
    sum_comp_mem_maassSpace (isRightCosetTransversal_lowerUnipotent hqM (NeZero.ne M))
      (fun δ hδ τ ↦ smul_eq_of_mem_maassSpace_one hH hδ) (comp_sl_smul_mem_maassTileSpace hH)
  have h0 : maassLevelTrace M q H =
      (q : ℂ)⁻¹ • fun τ ↦ ∑ i : ZMod q, H (lowerUnipotent (M * i.val) • τ) :=
    funext maassLevelTrace_eq_sum_zmod
  rw [h0]
  exact Submodule.smul_mem _ _ h

variable (M) in
lemma maassLevelTrace_maassPeriodAverage_of_dvd (hqM : q ∣ M)
    (hF : F ∈ maassSpace (q * M) 1 eigenvalue) (z : ℍ) :
    maassLevelTrace (q * M) q (maassPeriodAverage q F) z =
      maassLevelRaise q ((q : ℂ)⁻¹ • maassUpOperator q F) z := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  have hU : maassUpOperator q F ∈ maassSpace M 1 eigenvalue :=
    maassUpOperator_mem_maassSpace hqM hF
  have h (i : ℕ) : maassUpOperator q F (lowerUnipotent (M * i) • ofComplex ((q : ℂ) * z)) =
      maassUpOperator q F (ofComplex ((q : ℂ) * z)) := smul_eq_of_mem_maassSpace_one hU <|
    lowerUnipotent_mem_gamma0_iff.mpr (dvd_mul_right _ _)
  rw [maassLevelTrace_maassPeriodAverage hq.out.ne_zero]
  simp only [h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, maassLevelRaise, Pi.smul_apply,
    smul_eq_mul]
  field_simp

lemma maassLowerTrace_mem_maassSpace (hqM : ¬q ∣ M) (hF : F ∈ maassSpace (q * M) 1 eigenvalue) :
    maassLowerTrace M q F ∈ maassSpace M 1 eigenvalue := by
  have : NeZero (q * M) := ⟨mul_ne_zero hq.out.ne_zero (NeZero.ne M)⟩
  exact sum_comp_mem_maassSpace (isRightCosetTransversal_option (j := 1) hqM (by simp))
    (fun δ hδ τ ↦ maassLevelLower_smul hq.out.ne_zero
      (fun γ hγ τ ↦ smul_eq_of_mem_maassSpace_one hF hγ) hδ τ)
    (maassLevelLower_comp_mem_maassTileSpace hq.out.ne_zero hF)

lemma maassTraceRemainder_mem_maassSpace (hF : F ∈ maassSpace (q * M) 1 eigenvalue) :
    maassTraceRemainder M q F ∈ maassSpace M 1 eigenvalue := by
  rw [maassTraceRemainder]
  split_ifs with hqM
  · exact Submodule.smul_mem _ _ (maassUpOperator_mem_maassSpace hqM hF)
  · exact Submodule.smul_mem _ _ (maassLowerTrace_mem_maassSpace hqM hF)

/-- **The key identity of the Main Lemma**: for a prime `q`, `M ≠ 0` and `F` in `M(qM, 1, λ)`,
`F - Tr (E_q F) = c (F - Z(q ·))` with `c = maassTraceConstant M q ≠ 0` and
`Z = maassTraceRemainder M q F` in `M(M, 1, λ)`. If `q ∣ M`, then `Tr (E_q F) = q⁻¹ (U_q F)(q ·)`
with `U_q F` of level `M`, so `c = 1`. If `q ∤ M`, then `q² Tr (E_q F) = F + (q - 1) Y(q ·)` with
`Y` the trace of `w ↦ F(w / q)` from `Γ₀(M) ∩ Γ⁰(q)` to `Γ₀(M)`, so `c = 1 - q⁻²`: the matrices
`T^j !![1, 0; M i, 1]` run over the `q + 1` cosets, those with `j = 0` all in the trivial coset, and
those with a given `j ≠ 0` once through the `q` others. -/
lemma sub_maassLevelTrace_maassPeriodAverage (hF : F ∈ maassSpace (q * M) 1 eigenvalue) (z : ℍ) :
    F z - maassLevelTrace (q * M) q (maassPeriodAverage q F) z =
      maassTraceConstant M q * (F z - maassLevelRaise q (maassTraceRemainder M q F) z) := by
  by_cases hqM : q ∣ M
  · rw [maassTraceConstant, maassTraceRemainder, ite_eq_left hqM, ite_eq_left hqM, one_mul,
      maassLevelTrace_maassPeriodAverage_of_dvd M hqM hF]
  · have hc : maassTraceConstant M q ≠ 0 := maassTraceConstant_ne_zero
    have h0 : maassTraceConstant M q = 1 - (q : ℂ)⁻¹ * (q : ℂ)⁻¹ := ite_eq_right hqM
    have h1 : maassLevelLower q F (ofComplex ((q : ℂ) * z)) = F z :=
      congrFun (maassLevelRaise_maassLevelLower hq.out.ne_zero) z
    rw [maassTraceRemainder, ite_eq_right hqM, maassLevelTrace_maassPeriodAverage hq.out.ne_zero,
      sum_maassUpOperator_of_not_dvd hqM (fun γ hγ τ ↦ smul_eq_of_mem_maassSpace_one hF hγ), h1]
    simp only [maassLevelRaise, Pi.smul_apply]
    linear_combination (maassLowerTrace M q F (ofComplex ((q : ℂ) * z))) *
      mul_div_cancel₀ ((q : ℂ)⁻¹ * (q : ℂ)⁻¹ * ((q : ℂ) - 1)) hc - F z * h0

end UpperHalfPlane
