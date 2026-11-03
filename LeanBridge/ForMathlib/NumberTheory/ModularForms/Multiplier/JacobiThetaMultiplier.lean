import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ThetaMultiplier

/-!
# The theta multiplier of Jacobi's theta function in two variables

Let `ϑ(z, ξ) = ∑_{b ∈ ℤ} e(b² z + b ξ)`, where `e(x) = e^{2πix}`, which is Mathlib's
`jacobiTheta₂ ξ (2 z)`. For `γ = (a, b; c, d) ∈ Γ₀(4)`, Jacobi's law is

`ϑ(γ z, ξ / (c z + d)) = j(γ, z) e(c ξ² / (4 (c z + d))) ϑ(z, ξ)`,

with Shimura's theta multiplier `j(γ, z) = (c / d) ε_d⁻¹ (c z + d) ^ (1/2)`, the same factor as for
`θ(z) = ϑ(z, 0)` (`ModularForm.thetaSeries_smul`).

The proof has two steps. For `γ` running over `T^b`, `-1` and `(1, 0; 4 m, 1)` the two sides differ
by a factor independent of `ξ`, by the functional equation of `jacobiTheta₂`, used twice for
`(1, 0; 4 m, 1) = W T^(-m) W`, with `W z = -1 / (4 z)`. That property passes to products, and these
matrices generate `Γ₀(4)` by Euclid's algorithm. So for every `γ ∈ Γ₀(4)` there is a factor
independent of `ξ`, and `ξ = 0` identifies it with `j(γ, z)` wherever `θ(z) ≠ 0`, the law for `θ`
being already known. Both sides are continuous in `z` and the zeros of `θ` are isolated, so the law
holds for all `z`; the nonvanishing of `θ`, which is not proved at the pins, is not needed.

## Main results

* `ModularForm.jacobiTheta₂_two_mul_smul`: **Jacobi's law** on `Γ₀(4)`.
-/

open Complex CongruenceSubgroup Filter ModularGroup Matrix SpecialLinearGroup Topology

open scoped Real MatrixGroups Manifold ComplexConjugate

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {γ γ₁ γ₂ : SL(2, ℤ)} (z : ℍ) (ξ : ℂ)

variable (γ) in
lemma coe_smul_eq_div :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
  simpa only [eq_intCast, ofReal_intCast] using UpperHalfPlane.coe_specialLinearGroup_apply γ z

variable (γ) in
lemma denomZ_ne_zero : (γ 1 0 : ℂ) * (z : ℂ) + γ 1 1 ≠ 0 := by
  rw [← ModularGroup.denom_apply]
  exact denom_ne_zero γ z

variable (γ) in
lemma denomZ_conj_ne_zero : (γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1 ≠ 0 := by
  intro h
  have h1 : conj ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1) = conj 0 := congrArg conj h
  simp only [map_add, map_mul, conj_conj, map_intCast, map_zero] at h1
  exact denomZ_ne_zero γ z h1

variable (γ) in
lemma conj_coe_smul : conj ((γ • z : ℍ) : ℂ) =
    ((γ 0 0 : ℂ) * conj (z : ℂ) + γ 0 1) / ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1) := by
  rw [coe_smul_eq_div]
  simp only [map_div₀, map_add, map_mul, map_intCast]

variable (γ) in
lemma coe_im_smul : (((γ • z : ℍ).im : ℝ) : ℂ) =
    (z.im : ℂ) / (((γ 1 0 : ℂ) * z + γ 1 1) * ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1)) := by
  have h1 : (γ • z : ℍ).im = z.im / normSq (denom γ z) := ModularGroup.im_smul_eq_div_normSq γ z
  have h2 : ((normSq (denom γ z) : ℝ) : ℂ) =
      ((γ 1 0 : ℂ) * z + γ 1 1) * ((γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1) := by
    rw [← Complex.mul_conj, ModularGroup.denom_apply]
    simp only [map_add, map_mul, map_intCast]
  rw [h1]
  push_cast
  rw [h2]

private lemma mul_apply_int_one_zero :
    (γ₁ * γ₂ : SL(2, ℤ)) 1 0 = γ₁ 1 0 * γ₂ 0 0 + γ₁ 1 1 * γ₂ 1 0 := by
  simp [Matrix.mul_apply]

private lemma mul_apply_int_one_one :
    (γ₁ * γ₂ : SL(2, ℤ)) 1 1 = γ₁ 1 0 * γ₂ 0 1 + γ₁ 1 1 * γ₂ 1 1 := by
  simp [Matrix.mul_apply]

private lemma mul_apply_one_zero :
    ((γ₁ * γ₂ : SL(2, ℤ)) 1 0 : ℂ) = (γ₁ 1 0 : ℂ) * γ₂ 0 0 + (γ₁ 1 1 : ℂ) * γ₂ 1 0 := by
  simp [Matrix.mul_apply]

private lemma mul_apply_one_one :
    ((γ₁ * γ₂ : SL(2, ℤ)) 1 1 : ℂ) = (γ₁ 1 0 : ℂ) * γ₂ 0 1 + (γ₁ 1 1 : ℂ) * γ₂ 1 1 := by
  simp [Matrix.mul_apply]

variable (γ) in
private lemma smul_mul_denomZ :
    ((γ • z : ℍ) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) = (γ 0 0 : ℂ) * z + γ 0 1 := by
  rw [coe_smul_eq_div γ z]
  exact div_mul_cancel₀ _ (denomZ_ne_zero γ z)

private lemma denomZ_mul : ((γ₁ * γ₂ : SL(2, ℤ)) 1 0 : ℂ) * z + ((γ₁ * γ₂ : SL(2, ℤ)) 1 1 : ℂ) =
    ((γ₁ 1 0 : ℂ) * ((γ₂ • z : ℍ) : ℂ) + γ₁ 1 1) * ((γ₂ 1 0 : ℂ) * z + γ₂ 1 1) := by
  rw [add_mul, mul_assoc, smul_mul_denomZ, mul_apply_one_zero, mul_apply_one_one]
  ring1

variable (γ) in
/-- The two sides of Jacobi's law at `γ` differ by a factor independent of `ξ`. -/
private def HasThetaLaw : Prop :=
  ∃ C : ℍ → ℂ, ∀ (z : ℍ) (ξ : ℂ),
    jacobiTheta₂ (ξ / ((γ 1 0 : ℂ) * z + γ 1 1)) (2 * ((γ • z : ℍ) : ℂ)) =
      C z * cexp (2 * π * I * (γ 1 0 : ℂ) * ξ ^ 2 / (4 * ((γ 1 0 : ℂ) * z + γ 1 1))) *
        jacobiTheta₂ ξ (2 * z)

private lemma HasThetaLaw.mul (h₁ : HasThetaLaw γ₁) (h₂ : HasThetaLaw γ₂) :
    HasThetaLaw (γ₁ * γ₂) := by
  rcases h₁ with ⟨C₁, h₁⟩
  rcases h₂ with ⟨C₂, h₂⟩
  refine ⟨fun z ↦ C₁ (γ₂ • z) * C₂ z, fun z ξ ↦ ?_⟩
  have hJ₂ : (γ₂ 1 0 : ℂ) * z + γ₂ 1 1 ≠ 0 := denomZ_ne_zero γ₂ z
  have hJ₁ : (γ₁ 1 0 : ℂ) * ((γ₂ • z : ℍ) : ℂ) + γ₁ 1 1 ≠ 0 := denomZ_ne_zero γ₁ (γ₂ • z)
  have hξ : ξ / (((γ₁ * γ₂ : SL(2, ℤ)) 1 0 : ℂ) * z + ((γ₁ * γ₂ : SL(2, ℤ)) 1 1 : ℂ)) =
      ξ / ((γ₂ 1 0 : ℂ) * z + γ₂ 1 1) / ((γ₁ 1 0 : ℂ) * ((γ₂ • z : ℍ) : ℂ) + γ₁ 1 1) := by
    rw [denomZ_mul, div_div, mul_comm]
  have hdet : (γ₂ 0 0 : ℂ) * γ₂ 1 1 - (γ₂ 0 1 : ℂ) * γ₂ 1 0 = 1 := by
    exact_mod_cast γ₂.fin_two_mul_sub_mul_eq_one
  have hkey : (γ₁ 1 0 : ℂ) + (γ₂ 1 0 : ℂ) * ((γ₁ 1 0 : ℂ) * ((γ₂ • z : ℍ) : ℂ) + γ₁ 1 1) *
      ((γ₂ 1 0 : ℂ) * z + γ₂ 1 1) =
        ((γ₁ * γ₂ : SL(2, ℤ)) 1 0 : ℂ) * ((γ₂ 1 0 : ℂ) * z + γ₂ 1 1) := by
    rw [mul_apply_one_zero]
    linear_combination ((γ₂ 1 0 : ℂ) * (γ₁ 1 0 : ℂ)) * smul_mul_denomZ γ₂ z - (γ₁ 1 0 : ℂ) * hdet
  have hE : 2 * π * I * (γ₁ 1 0 : ℂ) * (ξ / ((γ₂ 1 0 : ℂ) * z + γ₂ 1 1)) ^ 2 /
      (4 * ((γ₁ 1 0 : ℂ) * ((γ₂ • z : ℍ) : ℂ) + γ₁ 1 1)) +
        2 * π * I * (γ₂ 1 0 : ℂ) * ξ ^ 2 / (4 * ((γ₂ 1 0 : ℂ) * z + γ₂ 1 1)) =
          2 * π * I * ((γ₁ * γ₂ : SL(2, ℤ)) 1 0 : ℂ) * ξ ^ 2 /
            (4 * (((γ₁ * γ₂ : SL(2, ℤ)) 1 0 : ℂ) * z + ((γ₁ * γ₂ : SL(2, ℤ)) 1 1 : ℂ))) := by
    rw [denomZ_mul]
    field_simp
    linear_combination (ξ ^ 2) * hkey
  rw [hξ, mul_smul, h₁ (γ₂ • z) (ξ / ((γ₂ 1 0 : ℂ) * z + γ₂ 1 1)), h₂ z ξ, ← hE, Complex.exp_add]
  ring1

private lemma HasThetaLaw.of_entries (hc : γ 1 0 = 0) (hd : γ 1 1 = 1) : HasThetaLaw γ := by
  refine ⟨fun _ ↦ 1, fun z ξ ↦ ?_⟩
  have hdet : γ 0 0 = 1 := by
    have h : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
    rwa [hc, hd, mul_one, mul_zero, sub_zero] at h
  have hs : ((γ • z : ℍ) : ℂ) = z + ((γ 0 1 : ℤ) : ℂ) := by
    rw [coe_smul_eq_div γ z, hc, hd, hdet]
    simp
  have hp : Function.Periodic (fun τ : ℂ ↦ jacobiTheta₂ ξ τ) 2 := fun τ ↦ jacobiTheta₂_add_right ξ τ
  have h2 : 2 * ((z : ℂ) + ((γ 0 1 : ℤ) : ℂ)) = 2 * z + ((γ 0 1 : ℤ) : ℂ) * 2 := by ring1
  have h3 : jacobiTheta₂ ξ (2 * z + ((γ 0 1 : ℤ) : ℂ) * 2) = jacobiTheta₂ ξ (2 * z) :=
    hp.int_mul (γ 0 1) (2 * z)
  have h4 : ξ / (((0 : ℤ) : ℂ) * z + ((1 : ℤ) : ℂ)) = ξ := by simp
  rw [hc, hd, hs, h2, h4, h3]
  simp

private lemma hasThetaLaw_neg_one : HasThetaLaw (-1) := by
  refine ⟨fun _ ↦ 1, fun z ξ ↦ ?_⟩
  have hs : ((-1 : SL(2, ℤ)) • z : ℍ) = z := by
    rw [ModularGroup.SL_neg_smul, one_smul]
  have h1 : ((-1 : SL(2, ℤ)) 1 0 : ℂ) = 0 := by simp
  have h2 : ((-1 : SL(2, ℤ)) 1 1 : ℂ) = -1 := by simp
  have h3 : ξ / ((0 : ℂ) * z + -1) = -ξ := by
    rw [zero_mul, zero_add, div_neg, div_one]
  rw [h1, h2, hs, h3, jacobiTheta₂_neg_left]
  simp

private lemma jacobiTheta₂_lower_aux {w : ℂ} (m : ℤ) (hw : w ≠ 0) (hJ : 4 * (m : ℂ) * w + 1 ≠ 0) :
    jacobiTheta₂ (ξ / (4 * m * w + 1)) (2 * (w / (4 * m * w + 1))) = (-I * (2 * w)) ^ (1 / 2 : ℂ) *
      (-I * (-1 / (2 * w) - m * 2)) ^ (1 / 2 : ℂ) *
        cexp (2 * π * I * (4 * m) * ξ ^ 2 / (4 * (4 * m * w + 1))) * jacobiTheta₂ ξ (2 * w) := by
  have e : -1 / (2 * w) - m * 2 = -(4 * m * w + 1) / (2 * w) := by
    field_simp
    ring1
  have hτ₂ : -1 / (2 * w) - m * 2 ≠ 0 := by
    rw [e]
    exact div_ne_zero (neg_ne_zero.mpr hJ) (mul_ne_zero two_ne_zero hw)
  have hp : Function.Periodic (fun τ : ℂ ↦ jacobiTheta₂ (ξ / (2 * w)) τ) 2 :=
    fun τ ↦ jacobiTheta₂_add_right _ τ
  have h₁ : jacobiTheta₂ ξ (2 * w) = 1 / (-I * (2 * w)) ^ (1 / 2 : ℂ) *
      cexp (-π * I * ξ ^ 2 / (2 * w)) * jacobiTheta₂ (ξ / (2 * w)) (-1 / (2 * w)) :=
    jacobiTheta₂_functional_equation ξ (2 * w)
  have h₂ : jacobiTheta₂ (ξ / (2 * w)) (-1 / (2 * w)) =
      jacobiTheta₂ (ξ / (2 * w)) (-1 / (2 * w) - m * 2) :=
    (hp.sub_int_mul_eq m).symm
  have h₃ : jacobiTheta₂ (ξ / (2 * w)) (-1 / (2 * w) - m * 2) =
      1 / (-I * (-1 / (2 * w) - m * 2)) ^ (1 / 2 : ℂ) *
        cexp (-π * I * (ξ / (2 * w)) ^ 2 / (-1 / (2 * w) - m * 2)) *
          jacobiTheta₂ (ξ / (2 * w) / (-1 / (2 * w) - m * 2)) (-1 / (-1 / (2 * w) - m * 2)) :=
    jacobiTheta₂_functional_equation _ _
  have h₄ : ξ / (2 * w) / (-1 / (2 * w) - m * 2) = -(ξ / (4 * m * w + 1)) := by
    rw [e]
    field_simp
  have h₅ : -1 / (-1 / (2 * w) - m * 2) = 2 * (w / (4 * m * w + 1)) := by
    rw [e]
    field_simp
  have hE : 2 * π * I * (4 * m) * ξ ^ 2 / (4 * (4 * m * w + 1)) =
      -(-π * I * ξ ^ 2 / (2 * w)) + -(-π * I * (ξ / (2 * w)) ^ 2 / (-1 / (2 * w) - m * 2)) := by
    rw [e]
    field_simp
    ring1
  have hA₁ : (-I * (2 * w)) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr <|
      mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (mul_ne_zero two_ne_zero hw)
  have hA₂ : (-I * (-1 / (2 * w) - m * 2)) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr <|
      mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ₂
  rw [h₂, h₃, h₄, h₅, jacobiTheta₂_neg_left] at h₁
  rw [hE, Complex.exp_add, Complex.exp_neg, Complex.exp_neg, h₁]
  have hE₁ : cexp (-π * I * ξ ^ 2 / (2 * w)) ≠ 0 := Complex.exp_ne_zero _
  have hE₂ : cexp (-π * I * (ξ / (2 * w)) ^ 2 / (-1 / (2 * w) - m * 2)) ≠ 0 := Complex.exp_ne_zero _
  generalize (-I * (2 * w)) ^ (1 / 2 : ℂ) = A₁ at hA₁ ⊢
  generalize (-I * (-1 / (2 * w) - m * 2)) ^ (1 / 2 : ℂ) = A₂ at hA₂ ⊢
  generalize cexp (-π * I * ξ ^ 2 / (2 * w)) = E₁ at hE₁ ⊢
  generalize cexp (-π * I * (ξ / (2 * w)) ^ 2 / (-1 / (2 * w) - m * 2)) = E₂ at hE₂ ⊢
  field_simp

private lemma hasThetaLaw_lowerUnipotent (m : ℤ) : HasThetaLaw (lowerUnipotent (4 * m)) := by
  refine ⟨fun z ↦ (-I * (2 * (z : ℂ))) ^ (1 / 2 : ℂ) *
    (-I * (-1 / (2 * (z : ℂ)) - m * 2)) ^ (1 / 2 : ℂ), fun z ξ ↦ ?_⟩
  have h10 : ((lowerUnipotent (4 * m) 1 0 : ℤ) : ℂ) = 4 * m := by
    simp [lowerUnipotent]
  have h11 : ((lowerUnipotent (4 * m) 1 1 : ℤ) : ℂ) = 1 := by
    simp [lowerUnipotent]
  have h00 : ((lowerUnipotent (4 * m) 0 0 : ℤ) : ℂ) = 1 := by
    simp [lowerUnipotent]
  have h01 : ((lowerUnipotent (4 * m) 0 1 : ℤ) : ℂ) = 0 := by
    simp [lowerUnipotent]
  have hJ : 4 * (m : ℂ) * z + 1 ≠ 0 := by
    simpa only [h10, h11] using denomZ_ne_zero (lowerUnipotent (4 * m)) z
  have hs : ((lowerUnipotent (4 * m) • z : ℍ) : ℂ) = z / (4 * m * z + 1) := by
    rw [coe_smul_eq_div _ z, h00, h01, h10, h11, one_mul, add_zero]
  rw [h10, h11, hs]
  exact jacobiTheta₂_lower_aux ξ m z.ne_zero hJ

private lemma exists_abs_add_mul_le (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    ∃ q : ℤ, 2 * |a + q * b| ≤ |b| := by
  have h1 : 0 ≤ a % b := Int.emod_nonneg a hb
  have h2 : a % b < |b| := Int.emod_lt_abs a hb
  have h3 : a + -(a / b) * b = a % b := by
    linear_combination -Int.emod_add_mul_ediv a b
  rcases le_or_gt (2 * (a % b)) |b| with h | h
  · refine ⟨-(a / b), ?_⟩
    rwa [h3, abs_of_nonneg h1]
  · rcases abs_cases b with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · refine ⟨-(a / b) - 1, ?_⟩
      have e : a + (-(a / b) - 1) * b = a % b - |b| := by
        rw [hb1]
        linear_combination h3
      rw [e, abs_of_nonpos (by omega)]
      omega
    · refine ⟨-(a / b) + 1, ?_⟩
      have e : a + (-(a / b) + 1) * b = a % b - |b| := by
        rw [hb1]
        linear_combination h3
      rw [e, abs_of_nonpos (by omega)]
      omega

private lemma hasThetaLaw_of_eq_zero (hc : γ 1 0 = 0) : HasThetaLaw γ := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have h : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
    rwa [hc, mul_zero, sub_zero] at h
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨-, hd⟩ | ⟨-, hd⟩
  · exact HasThetaLaw.of_entries hc hd
  · have h1 : γ = -1 * -γ := by simp
    rw [h1]
    refine hasThetaLaw_neg_one.mul (HasThetaLaw.of_entries ?_ ?_)
    · simp [hc]
    · simp [hd]

private lemma hasThetaLaw_of_natAbs_le (n : ℕ) :
    ∀ γ : SL(2, ℤ), γ ∈ Gamma0 4 → (γ 1 0).natAbs ≤ n → HasThetaLaw γ := by
  induction n with
  | zero =>
    exact fun γ _ h ↦ hasThetaLaw_of_eq_zero (Int.natAbs_eq_zero.mp (Nat.le_zero.mp h))
  | succ n ih =>
    intro γ hγ h
    rcases eq_or_ne (γ 1 0) 0 with hc | hc
    · exact hasThetaLaw_of_eq_zero hc
    rcases (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 4).mp (Gamma0_mem.mp hγ) with ⟨c', hc'⟩
    have hc4 : γ 1 0 = 4 * c' := by
      rw [hc']
      rfl
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
    have hodd : γ 1 1 % 2 = 1 := by
      rw [hc4] at hdet
      rcases Int.emod_two_eq_zero_or_one (γ 1 1) with h0 | h0
      · have h2 : (2 : ℤ) ∣ 1 := by
          rw [← hdet]
          exact ⟨γ 0 0 * (γ 1 1 / 2) - 2 * (γ 0 1 * c'), by
            have h3 : γ 1 1 = 2 * (γ 1 1 / 2) := by omega
            linear_combination (γ 0 0) * h3⟩
        omega
      · exact h0
    rcases exists_abs_add_mul_le (γ 1 1) hc with ⟨j, hj⟩
    have hodd1 : (γ 1 1 + j * γ 1 0) % 2 = 1 := by
      have e : γ 1 1 + j * γ 1 0 = γ 1 1 + 2 * (2 * (j * c')) := by
        rw [hc4]
        ring1
      rw [e]
      omega
    have hd0 : γ 1 1 + j * γ 1 0 ≠ 0 := fun h0 ↦ by
      rw [h0] at hodd1
      omega
    rcases exists_abs_add_mul_le c' hd0 with ⟨m, hm⟩
    have hlt : 2 * |γ 1 1 + j * γ 1 0| < |γ 1 0| := by
      rcases abs_cases (γ 1 1 + j * γ 1 0) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
        rcases abs_cases (γ 1 0) with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1] at hj ⊢ <;> rw [h2] at hj ⊢ <;>
          omega
    have h10 : (γ * T ^ j * lowerUnipotent (4 * m)) 1 0 = 4 * (c' + m * (γ 1 1 + j * γ 1 0)) := by
      have h00 : (T ^ j : SL(2, ℤ)) 0 0 = 1 := by simp [coe_T_zpow]
      have h01 : (T ^ j : SL(2, ℤ)) 0 1 = j := by simp [coe_T_zpow]
      have h10 : (T ^ j : SL(2, ℤ)) 1 0 = 0 := by simp [coe_T_zpow]
      have h11 : (T ^ j : SL(2, ℤ)) 1 1 = 1 := by simp [coe_T_zpow]
      have l00 : lowerUnipotent (4 * m) 0 0 = 1 := by simp [lowerUnipotent]
      have l10 : lowerUnipotent (4 * m) 1 0 = 4 * m := by simp [lowerUnipotent]
      rw [mul_apply_int_one_zero, mul_apply_int_one_zero, mul_apply_int_one_one, h00, h01, h10,
        h11, l00, l10, hc4]
      ring1
    have hmem : γ * T ^ j * lowerUnipotent (4 * m) ∈ Gamma0 4 := by
      rw [Gamma0_mem, h10]
      push_cast
      rw [show (4 : ZMod 4) = 0 from rfl, zero_mul]
    have hnat : ((γ * T ^ j * lowerUnipotent (4 * m)) 1 0).natAbs ≤ n := by
      rw [h10]
      have h1 : |4 * (c' + m * (γ 1 1 + j * γ 1 0))| < |γ 1 0| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 4)]
        omega
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h1
      omega
    have h1 : lowerUnipotent (4 * m) * lowerUnipotent (4 * -m) = 1 := by
      rw [← lowerUnipotent_add]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [lowerUnipotent]
    have h2 : γ = γ * T ^ j * lowerUnipotent (4 * m) * lowerUnipotent (4 * -m) * T ^ (-j) := by
      rw [mul_assoc (γ * T ^ j), h1, mul_one, zpow_neg T j, mul_inv_cancel_right]
    rw [h2]
    refine ((ih _ hmem hnat).mul (hasThetaLaw_lowerUnipotent (-m))).mul
      (HasThetaLaw.of_entries ?_ ?_)
    · simp [coe_T_zpow]
    · simp [coe_T_zpow]

variable (γ) in
private lemma continuous_thetaFactor : Continuous (thetaFactor γ) := by
  refine continuous_const.mul ?_
  rw [continuous_iff_continuousAt]
  intro z
  have hd : ContinuousAt (fun z : ℍ ↦ denom γ z) z := by
    simp only [ModularGroup.denom_apply]
    fun_prop
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have h : (fun z : ℍ ↦ denom γ z ^ (1 / 2 : ℂ)) = fun _ ↦ (γ 1 1 : ℂ) ^ (1 / 2 : ℂ) := by
      ext z
      rw [ModularGroup.denom_apply, hc]
      simp
    exact h ▸ continuousAt_const
  · have hmem : denom γ z ∈ slitPlane := by
      refine Or.inr ?_
      rw [ModularGroup.denom_apply]
      simp [hc, z.im_ne_zero]
    exact ContinuousAt.cpow hd continuousAt_const hmem

private lemma dense_thetaSeries_ne_zero : Dense {z : ℍ | thetaSeries z ≠ 0} := by
  have hA : AnalyticOnNhd ℂ (thetaSeries ∘ ofComplex) {w : ℂ | 0 < w.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_thetaSeries).analyticOnNhd
      isOpen_upperHalfPlaneSet
  refine dense_iff_inter_open.mpr fun U hU ⟨z₀, hz₀⟩ ↦ ?_
  by_contra hcon
  have hzero : ∀ z ∈ U, thetaSeries z = 0 := fun z hz ↦ by
    by_contra h
    exact hcon ⟨z, hz, h⟩
  have hev : (thetaSeries ∘ ofComplex) =ᶠ[𝓝 (z₀ : ℂ)] 0 := by
    have hopen : IsOpen (UpperHalfPlane.coe '' U) := isOpenEmbedding_coe.isOpenMap U hU
    filter_upwards [hopen.mem_nhds ⟨z₀, hz₀, rfl⟩] with w hw
    rcases hw with ⟨z, hz, rfl⟩
    rw [Function.comp_apply, ofComplex_apply]
    exact hzero z hz
  refine thetaSeries_ne_zero <| funext fun z ↦ ?_
  have h : thetaSeries (ofComplex (z : ℂ)) = 0 :=
    hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_halfSpace_im_gt 0).isPreconnected
      z₀.im_pos hev z.im_pos
  rwa [ofComplex_apply] at h

/-- **Jacobi's law on `Γ₀(4)`.** For `γ = (a, b; c, d) ∈ Γ₀(4)`, the theta function
`ϑ(z, ξ) = ∑_b e(b² z + b ξ)`, that is `jacobiTheta₂ ξ (2 z)`, satisfies
`ϑ(γ z, ξ / (c z + d)) = j(γ, z) e(c ξ² / (4 (c z + d))) ϑ(z, ξ)`, where `j` is Shimura's theta
multiplier `ModularForm.thetaFactor`. -/
lemma jacobiTheta₂_two_mul_smul (hγ : γ ∈ Gamma0 4) : jacobiTheta₂ (ξ / denom γ z)
    (2 * ((γ • z : ℍ) : ℂ)) = thetaFactor γ z *
      cexp (2 * π * I * (γ 1 0 : ℂ) * ξ ^ 2 / (4 * denom γ z)) * jacobiTheta₂ ξ (2 * z) := by
  rcases hasThetaLaw_of_natAbs_le _ γ hγ le_rfl with ⟨C, hC⟩
  have hd (z : ℍ) : denom γ z = (γ 1 0 : ℂ) * z + γ 1 1 := ModularGroup.denom_apply γ z
  have hθ (z : ℍ) : jacobiTheta₂ 0 (2 * (z : ℂ)) = thetaSeries z := by
    rw [thetaSeries_eq, jacobiTheta_eq_jacobiTheta₂]
  have hlaw (z : ℍ) (hz : thetaSeries z ≠ 0) (ξ : ℂ) :
      jacobiTheta₂ (ξ / denom γ z) (2 * ((γ • z : ℍ) : ℂ)) = thetaFactor γ z *
        cexp (2 * π * I * (γ 1 0 : ℂ) * ξ ^ 2 / (4 * denom γ z)) * jacobiTheta₂ ξ (2 * z) := by
    have h0 : C z * thetaSeries z = thetaFactor γ z * thetaSeries z := by
      simpa only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        Complex.exp_zero, mul_one, hθ, thetaSeries_smul z hγ] using (hC z 0).symm
    rw [hd, ← mul_right_cancel₀ hz h0]
    exact hC z ξ
  have hcL : Continuous fun z : ℍ ↦ jacobiTheta₂ (ξ / denom γ z) (2 * ((γ • z : ℍ) : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro z
    have him : 0 < (2 * ((γ • z : ℍ) : ℂ)).im := by
      have e : (2 * ((γ • z : ℍ) : ℂ)).im = 2 * (γ • z).im := by simp
      rw [e]
      exact mul_pos two_pos (γ • z).im_pos
    have hsm : Continuous fun z : ℍ ↦ ((γ • z : ℍ) : ℂ) := by
      simp only [coe_smul_eq_div γ]
      exact Continuous.div (by fun_prop) (by fun_prop) fun z ↦ denomZ_ne_zero γ z
    have hpair : ContinuousAt (fun z : ℍ ↦ (ξ / denom γ z, 2 * ((γ • z : ℍ) : ℂ))) z := by
      refine ContinuousAt.prodMk ?_ (continuous_const.mul hsm).continuousAt
      refine continuousAt_const.div ?_ (denom_ne_zero γ z)
      simp only [hd]
      fun_prop
    exact ContinuousAt.comp (f := fun z : ℍ ↦ (ξ / denom γ z, 2 * ((γ • z : ℍ) : ℂ)))
      (g := fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) (continuousAt_jacobiTheta₂ _ him) hpair
  have hcR : Continuous fun z : ℍ ↦ thetaFactor γ z *
      cexp (2 * π * I * (γ 1 0 : ℂ) * ξ ^ 2 / (4 * denom γ z)) * jacobiTheta₂ ξ (2 * z) := by
    rw [continuous_iff_continuousAt]
    intro z
    have him : 0 < (2 * (z : ℂ)).im := by
      have e : (2 * (z : ℂ)).im = 2 * z.im := by simp
      rw [e]
      exact mul_pos two_pos z.im_pos
    have h1 :
        ContinuousAt (fun z : ℍ ↦ cexp (2 * π * I * (γ 1 0 : ℂ) * ξ ^ 2 / (4 * denom γ z))) z := by
      refine Complex.continuous_exp.continuousAt.comp (continuousAt_const.div ?_ ?_)
      · simp only [hd]
        fun_prop
      · exact mul_ne_zero (by norm_num) (denom_ne_zero γ z)
    have h2 : ContinuousAt (fun z : ℍ ↦ jacobiTheta₂ ξ (2 * (z : ℂ))) z := by
      have hpair : ContinuousAt (fun z : ℍ ↦ (ξ, 2 * (z : ℂ))) z :=
        continuousAt_const.prodMk (continuous_const.mul continuous_coe).continuousAt
      exact ContinuousAt.comp (f := fun z : ℍ ↦ (ξ, 2 * (z : ℂ)))
        (g := fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) (continuousAt_jacobiTheta₂ _ him) hpair
    exact ((continuous_thetaFactor γ).continuousAt.mul h1).mul h2
  exact congrFun (hcL.ext_on dense_thetaSeries_ne_zero hcR fun z hz ↦ hlaw z hz ξ) z

end ModularForm
