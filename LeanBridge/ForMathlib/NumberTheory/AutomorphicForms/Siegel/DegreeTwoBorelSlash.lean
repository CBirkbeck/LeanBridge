import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoSatakeMapT1
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GritsenkoLift
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ScalarSimilitude

/-!
# The slash operator of Borel normal forms on Fourier series

A Borel normal form `M = (r D⁻ᵀ, X D; 0, D)`, `D = (d₀, 0; c, d₁)`
(`SiegelUpperHalfSpace.borelNF`), acts on the Siegel upper half-space `ℋ₂` by
`Z ↦ r D⁻ᵀ Z D⁻¹ + X`, with automorphy factor `D` and multiplier `r`, so that in weight `det^κ`
`(G ∣ M)(Z) = r^{2κ - 3} det(D)^{-κ} G(r D⁻ᵀ Z D⁻¹ + X)`. On an exponential
`e^{2πi(nτ + r'z + mω)}` of a Fourier series, `Z ↦ r D⁻ᵀ Z D⁻¹ + X` multiplies by the phase
`e^{2πi tr(T X)}` of `T = (n, r'/2; r'/2, m)` and replaces `T` by `r D⁻¹ T D⁻ᵀ`, whose entries are
rational (`SiegelUpperHalfSpace.borelExp`). The Hecke operators `T(p)` and `T_1(p²)` of
`Sp(4, ℤ)` are the sums of the slash operators of their right coset representatives in Borel normal
form, `SiegelUpperHalfSpace.tpRep` and `SiegelUpperHalfSpace.t1Rep`; this file reads the action of
a family of representatives with the same `D` on a Fourier series `G(Z) = ∑ a(T) e^{2πi tr(TZ)}`,
as a series in `T` in which the phases are summed over the family.

## Main definitions

* `SiegelUpperHalfSpace.borelExp`: the exponential of `r D⁻¹ T D⁻ᵀ`.
* `SiegelUpperHalfSpace.tpRepΔ`, `SiegelUpperHalfSpace.t1RepΔ`: the right coset representatives of
  `T(p)` and `T_1(p²)` as elements of the semigroup `S_p`.

## Main results

* `SiegelUpperHalfSpace.liftExp_gspSmul_of_eq_borelNF`: the exponentials at `r D⁻ᵀ Z D⁻¹ + X`.
* `SiegelUpperHalfSpace.heckeMonoidSlash_apply_of_eq_borelNF`: the slash operator of a Borel normal
  form in weight `det^κ`.
* `SiegelUpperHalfSpace.hasSum_sum_heckeMonoidSlash`: a family of Borel normal forms with the same
  `D` on a Fourier series.
* `SiegelUpperHalfSpace.heckeOperator_Tp_eq_sum`,
  `SiegelUpperHalfSpace.heckeOperator_T₁_eq_sum`: `F ∣ T(p)` and `F ∣ T_1(p²)` are the sums of the
  slash operators of the representatives.
-/

open Complex Real

open Matrix hiding mul_inv_rev inv_zpow'

open scoped Pointwise

namespace SiegelUpperHalfSpace

local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ

local notation "GL₄" => GL (Fin 2 ⊕ Fin 2) ℚ

local notation "Γ₂" => heckeGamma (Fin 2)

/-! ### The slash operator of a Borel normal form -/

variable {r d₀ d₁ c x₀₀ x₀₁ x₁₁ : ℚ} {β : gspPlus (Fin 2)} (Z : SiegelUpperHalfSpace (Fin 2))
    (κ : ℤ) {Δ : Submonoid GL₄} [Fact (Δ ≤ gspPlusGL (Fin 2))]

lemma multiplier_of_eq_borelNF (h : (β : M₄) = borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁) (hd₀ : d₀ ≠ 0)
    (hd₁ : d₁ ≠ 0) : multiplier β = r :=
  multiplier_eq β (h ▸ borelNF_transpose_mul_J_mul hd₀ hd₁)

lemma gspDenom_of_eq_borelNF (h : (β : M₄) = borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁) :
    gspDenom β Z = !![(d₀ : ℂ), 0; (c : ℂ), (d₁ : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gspDenom, h, borelNF]

lemma gspSmul_val_of_eq_borelNF (h : (β : M₄) = borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁) (hd₀ : d₀ ≠ 0)
    (hd₁ : d₁ ≠ 0) : (gspSmul β Z).val =
      gspNum β Z * !![(d₀ : ℂ)⁻¹, 0; -(c : ℂ) / (d₀ * d₁), (d₁ : ℂ)⁻¹] := by
  have hd₀' : (d₀ : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hd₀
  have hd₁' : (d₁ : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hd₁
  rw [gspSmul_val, gspDenom_of_eq_borelNF Z h, inv_eq_left_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring1

/-- The exponential `e^{2πi tr(N Z)}` of the rational matrix `N = r D⁻¹ T D⁻ᵀ`, for
`D = (d₀, 0; c, d₁)` and `T = (n, r'/2; r'/2, m)`: its entries are `N = (rn/d₀², R/2; R/2, M)` with
`R = r(r'd₀ - 2nc)/(d₀²d₁)` and `M = r(nc² - r'cd₀ + md₀²)/(d₀²d₁²)`. It is the exponential that
replaces `e^{2πi tr(TZ)}` under `Z ↦ r D⁻ᵀ Z D⁻¹ + X`, up to the phase `e^{2πi tr(TX)}`
(`SiegelUpperHalfSpace.liftExp_gspSmul_of_eq_borelNF`). -/
noncomputable def borelExp (r d₀ d₁ c : ℚ) (T : ℤ × ℤ × ℤ) (Z : SiegelUpperHalfSpace (Fin 2)) : ℂ :=
  cexp (2 * π * I * (((r * T.1 / d₀ ^ 2 : ℚ) : ℂ) * Z.val 0 0 +
    ((r * (T.2.1 * d₀ - 2 * T.1 * c) / (d₀ ^ 2 * d₁) : ℚ) : ℂ) * Z.val 0 1 +
      ((r * (T.1 * c ^ 2 - T.2.1 * c * d₀ + T.2.2 * d₀ ^ 2) / (d₀ ^ 2 * d₁ ^ 2) : ℚ) : ℂ) *
        Z.val 1 1))

/-- **The exponentials at a Borel normal form**: under `Z ↦ r D⁻ᵀ Z D⁻¹ + X`, the exponential
`e^{2πi tr(TZ)}` becomes `e^{2πi tr(TX)} e^{2πi tr(r D⁻¹ T D⁻ᵀ Z)}`. -/
lemma liftExp_gspSmul_of_eq_borelNF (h : (β : M₄) = borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁)
    (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) (T : ℤ × ℤ × ℤ) : liftExp 1 T.1 T.2.1 T.2.2 (gspSmul β Z) =
      cexp (2 * π * I * ((T.1 * x₀₀ + T.2.1 * x₀₁ + T.2.2 * x₁₁ : ℚ) : ℂ)) *
        borelExp r d₀ d₁ c T Z := by
  have hd₀' : (d₀ : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hd₀
  have hd₁' : (d₁ : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hd₁
  have h10 : Z.val 1 0 = Z.val 0 1 := congrFun (congrFun Z.transpose_val 0) 1
  rw [liftExp, borelExp, ← Complex.exp_add, gspSmul_val_of_eq_borelNF Z h hd₀ hd₁]
  congr 1
  simp [gspNum, h, borelNF, mul_apply, h10]
  field_simp
  ring1

lemma borelExp_eq_liftExp {T : ℤ × ℤ × ℤ} {N R M : ℤ} (h₁ : r * T.1 / d₀ ^ 2 = N)
    (h₂ : r * (T.2.1 * d₀ - 2 * T.1 * c) / (d₀ ^ 2 * d₁) = R)
    (h₃ : r * (T.1 * c ^ 2 - T.2.1 * c * d₀ + T.2.2 * d₀ ^ 2) / (d₀ ^ 2 * d₁ ^ 2) = M) :
    borelExp r d₀ d₁ c T Z = liftExp 1 N R M Z := by
  rw [borelExp, liftExp, h₁, h₂, h₃]
  simp

/-- **The slash operator of a Borel normal form** `M = (r D⁻ᵀ, X D; 0, D)` in weight `det^κ`:
`(G ∣ M)(Z) = r^{2κ - 3} det(D)^{-κ} G(r D⁻ᵀ Z D⁻¹ + X)`. -/
lemma heckeMonoidSlash_apply_of_eq_borelNF {x : Δ}
    (h : ((x : GL₄) : M₄) = borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁) (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0)
    (G : SiegelUpperHalfSpace (Fin 2) → ℂ) : heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) x G Z =
      (r : ℂ) ^ (2 * κ - 3) * ((d₀ * d₁ : ℚ) : ℂ) ^ (-κ) *
          G (gspSmul (submonoidToGSpPlus x) Z) := by
  have hβ : ((submonoidToGSpPlus x : gspPlus (Fin 2)) : M₄) = borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ :=
    h
  simp only [heckeMonoidSlash, LinearMap.coe_mk, AddHom.coe_mk, gspSlash, slashExponent_detPowerRep,
    multiplier_of_eq_borelNF hβ hd₀ hd₁, TauCeti.detPowerRep_apply, map_inv,
    Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply,
    coe_gspDenomGL, gspDenom_of_eq_borelNF Z hβ, det_fin_two_of, smul_eq_mul]
  rw [zero_mul, sub_zero, inv_zpow', Rat.cast_mul, mul_assoc]

variable {a : ℤ × ℤ × ℤ → ℂ} {G : SiegelUpperHalfSpace (Fin 2) → ℂ}

/-- **A family of Borel normal forms with the same `D` on a Fourier series**: if
`G(W) = ∑ a(T) e^{2πi tr(TW)}` on `ℋ₂`, then `∑_s (G ∣ M_s)(Z)` for the normal forms
`M_s = (r D⁻ᵀ, X_s D; 0, D)` is the sum over `T` of
`r^{2κ - 3} det(D)^{-κ} a(T) e^{2πi tr(r D⁻¹ T D⁻ᵀ Z)} ∑_s e^{2πi tr(T X_s)}`. -/
lemma hasSum_sum_heckeMonoidSlash {S : Type*} [Fintype S] {x : S → Δ} {y : S → ℚ × ℚ × ℚ}
    (hx : ∀ s, ((x s : GL₄) : M₄) = borelNF r d₀ d₁ c (y s).1 (y s).2.1 (y s).2.2)
    (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0)
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ a T * liftExp 1 T.1 T.2.1 T.2.2 W) (G W)) :
    HasSum (fun T ↦ (r : ℂ) ^ (2 * κ - 3) * ((d₀ * d₁ : ℚ) : ℂ) ^ (-κ) * a T *
      borelExp r d₀ d₁ c T Z * ∑ s, cexp (2 * π * I *
        ((T.1 * (y s).1 + T.2.1 * (y s).2.1 + T.2.2 * (y s).2.2 : ℚ) : ℂ)))
      (∑ s, heckeMonoidSlash (TauCeti.detPowerRep ℂ 2 κ) (x s) G Z) := by
  have hβ (s : S) : ((submonoidToGSpPlus (x s) : gspPlus (Fin 2)) : M₄) =
      borelNF r d₀ d₁ c (y s).1 (y s).2.1 (y s).2.2 :=
    hx s
  simp only [heckeMonoidSlash_apply_of_eq_borelNF Z κ (hx _) hd₀ hd₁]
  refine (hasSum_sum fun s _ ↦ ((hG (gspSmul (submonoidToGSpPlus (x s)) Z)).mul_left
    ((r : ℂ) ^ (2 * κ - 3) * ((d₀ * d₁ : ℚ) : ℂ) ^ (-κ)))).congr_fun fun T ↦ ?_
  simp only [liftExp_gspSmul_of_eq_borelNF Z (hβ _) hd₀ hd₁, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  ring1

lemma hasSum_of_ne_zero_bij {ι ι' : Type*} {f : ι → ℂ} {g : ι' → ℂ} {s : ℂ} (hf : HasSum f s)
    (j : ι' → ι) (hj : Set.InjOn j (Function.support g)) (hfg : ∀ N, g N ≠ 0 → f (j N) = g N)
    (hsupp : ∀ T, f T ≠ 0 → ∃ N, g N ≠ 0 ∧ j N = T) : HasSum g s :=
  (hasSum_iff_hasSum_of_ne_zero_bij (fun N : Function.support g ↦ j N)
    (fun N N' h ↦ Subtype.ext (hj N.2 N'.2 h)) (fun T hT ↦ by
      rcases hsupp T hT with ⟨N, hN, rfl⟩
      exact ⟨⟨N, hN⟩, rfl⟩) fun N ↦ hfg N N.2).mp hf

/-! ### The Hecke operators as sums over the representatives -/

variable {p : ℕ} [Fact p.Prime]

/-- The right coset representatives `SiegelUpperHalfSpace.tpRep` of `T(p)`, as elements of the
semigroup `S_p`. -/
noncomputable def tpRepΔ (i : TpIndex p) : heckeMonoidAt (Fin 2) p :=
  ⟨tpRep i, borelNFGL_mem_heckeMonoidAt (tpRep_int i)⟩

/-- The right coset representatives `SiegelUpperHalfSpace.t1Rep` of `T_1(p²)`, as elements of the
semigroup `S_p`. -/
noncomputable def t1RepΔ (i : T1Index p) : heckeMonoidAt (Fin 2) p :=
  ⟨t1Rep i, borelNFGL_mem_heckeMonoidAt ⟨t1Mat i, t1Mat_cast i⟩⟩

@[simp]
lemma coe_tpRepΔ (i : TpIndex p) : (tpRepΔ i : GL₄) = tpRep i :=
  rfl

@[simp]
lemma coe_t1RepΔ (i : T1Index p) : (t1RepΔ i : GL₄) = t1Rep i :=
  rfl

lemma doubleCoset_Tp_eq_iUnion : DoubleCoset.doubleCoset ((heckeCosetDiag p 0 0 1).out : GL₄)
    (Γ₂ : Set GL₄) Γ₂ = ⋃ i : TpIndex p, MulOpposite.op (tpRepΔ i : GL₄) • (Γ₂ : Set GL₄) := by
  ext x
  simp only [Set.mem_iUnion, mem_rightCoset_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
  · rcases exists_borelNF_of_mem_doubleCoset hx with
      ⟨γ, hγ, d₀, d₁, c, x₀₀, x₀₁, x₁₁, hd₀, hd₁, hc, hc', h₀₀, h₀₀', h₀₁, h₀₁', h₁₁, h₁₁',
        ⟨M, hM⟩, h⟩
    simp only [mul_zero, zero_add] at hM h
    rcases exists_tpRep_eq hd₀ hd₁ hc hc' h₀₀ h₀₀' h₀₁ h₀₁' h₁₁ h₁₁' M hM with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [coe_tpRepΔ, hi, ← h, mul_inv_rev, mul_inv_cancel_left]
    exact inv_mem hγ
  · rw [← inv_mul_cancel_right x (tpRep i)]
    exact mul_mem_doubleCoset hi (tpRep_mem i)

lemma injective_op_tpRepΔ_smul :
    Function.Injective fun i : TpIndex p ↦ MulOpposite.op (tpRepΔ i : GL₄) • (Γ₂ : Set GL₄) :=
  fun _ _ h ↦ (eq_of_tpRep_mul_inv_mem (rightCoset_eq_iff Γ₂ |>.mp h)).symm

lemma doubleCoset_T₁_eq_iUnion : DoubleCoset.doubleCoset ((heckeCosetDiag p 0 1 0).out : GL₄)
    (Γ₂ : Set GL₄) Γ₂ = ⋃ i : T1Index p, MulOpposite.op (t1RepΔ i : GL₄) • (Γ₂ : Set GL₄) := by
  ext x
  simp only [Set.mem_iUnion, mem_rightCoset_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
  · rcases exists_borelNF_of_mem_doubleCoset hx with
      ⟨γ, hγ, d₀, d₁, c, x₀₀, x₀₁, x₁₁, hd₀, hd₁, hc, hc', h₀₀, h₀₀', h₀₁, h₀₁', h₁₁, h₁₁', -, h⟩
    simp only [mul_zero] at h
    have hmem : borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁ ∈
        DoubleCoset.doubleCoset (symplecticDiag p 0 1 0 : GL₄) (Γ₂ : Set GL₄) Γ₂ := by
      rw [← h, ← DoubleCoset.doubleCoset_eq_of_mem
        (rep_mem_doubleCoset_symplecticDiag (p := p) 0 1 0)]
      exact mul_mem_doubleCoset hγ hx
    have hmin : MinorsDvd p 1 (borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁) :=
      (minorsDvd_symplecticDiag 0 1 0).of_mem_doubleCoset hmem
    have hent : ¬EntriesDvd p 1 (borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁) := fun he ↦
      Nat.not_succ_le_zero 0
        (le_of_entriesDvd_symplecticDiag (he.of_mem_doubleCoset (mem_doubleCoset_symm hmem)))
    rcases exists_t1Rep_eq hd₀ hd₁ hc hc' h₀₀ h₀₀' h₀₁ h₀₁' h₁₁ h₁₁' hmin hent with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [coe_t1RepΔ, hi, ← h, mul_inv_rev, mul_inv_cancel_left]
    exact inv_mem hγ
  · rw [← inv_mul_cancel_right x (t1Rep i)]
    exact mul_mem_doubleCoset hi (t1Rep_mem i)

lemma injective_op_t1RepΔ_smul :
    Function.Injective fun i : T1Index p ↦ MulOpposite.op (t1RepΔ i : GL₄) • (Γ₂ : Set GL₄) :=
  fun _ _ h ↦ (eq_of_t1Rep_mul_inv_mem (rightCoset_eq_iff Γ₂ |>.mp h)).symm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (F : slashInvariantsOf ρ (heckeMonoidAt (Fin 2) p) Γ₂)

/-- **`T(p)` as a sum over its right coset representatives**: `F ∣ T(p) = ∑ᵢ F ∣ αᵢ` over the
`1 + p + p² + p³` Borel normal forms `SiegelUpperHalfSpace.tpRep`. -/
lemma heckeOperator_Tp_eq_sum : (heckeOperator ρ (heckeCosetDiag p 0 0 1) F :
    SiegelUpperHalfSpace (Fin 2) → V) = ∑ i : TpIndex p, heckeMonoidSlash ρ (tpRepΔ i) F :=
  heckeOperator_eq_sum ρ _ tpRepΔ doubleCoset_Tp_eq_iUnion injective_op_tpRepΔ_smul F

/-- **`T_1(p²)` as a sum over its right coset representatives**: `F ∣ T_1(p²) = ∑ᵢ F ∣ αᵢ` over
the `p (p + 1)(p² + 1)` Borel normal forms `SiegelUpperHalfSpace.t1Rep`. -/
lemma heckeOperator_T₁_eq_sum : (heckeOperator ρ (heckeCosetDiag p 0 1 0) F :
    SiegelUpperHalfSpace (Fin 2) → V) = ∑ i : T1Index p, heckeMonoidSlash ρ (t1RepΔ i) F :=
  heckeOperator_eq_sum ρ _ t1RepΔ doubleCoset_T₁_eq_iUnion injective_op_t1RepΔ_smul F

end SiegelUpperHalfSpace
