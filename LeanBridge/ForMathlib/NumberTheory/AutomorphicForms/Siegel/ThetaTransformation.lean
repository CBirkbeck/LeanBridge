import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CongruenceSubgroups
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.HolomorphicOperations
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Convergence, holomorphy and transformation laws of theta constants

The theta constants `θ_{μ,ν}` (`SiegelUpperHalfSpace.thetaConstant`) transform under `Sp(2g, ℤ)`
by a change of characteristic, up to an eighth root of unity and, under the inversions, a square
root of `det(cΩ + d)`. This file proves the transformation law under the Siegel parabolic subgroup
`{c = 0}` of `Sp(2g, ℤ)` in every degree `g`, and under the partial inversion `J₁ ∈ Sp(4, ℤ)` in
degree 2, from Mathlib's functional equation of Jacobi's theta function `jacobiTheta₂`. The
parabolic subgroup and `J₁` generate `Sp(4, ℤ)`, a classical fact which is not proved here. These
are the transformation laws behind the modularity of the generators, polynomials in the ten even
theta constants of degree 2, of the rings of Siegel modular forms of the knowls
`mf.siegel.family.gamma0_2`, `mf.siegel.family.gamma0_4_psi_4` and `mf.siegel.family.gamma_2`.

In degree 2 the theta series converges absolutely and the theta constants are holomorphic: the
exponent has real part `-π xᵀ (Im Ω) x ≤ -π ε xᵀx` for real `x`, with
`ε = det(Im Ω) / tr(Im Ω) > 0`, which bounds the terms by a product of two Gaussian sums in one
variable, uniformly with the derivatives on a ball around each point. The transformation law under
`J₁` follows by summing first over the first coordinate, applying the functional equation of
`jacobiTheta₂` in the variable `τ = Ω₁₁`, and summing again.

## Main definitions

* `SymplecticGroup.partialInversion`: the partial inversion `J₁ ∈ Sp(4, ℤ)`, acting by
  `(τ, z; z, ω) ↦ (-1/τ, z/τ; z/τ, ω - z²/τ)`.

## Main results

* `SiegelUpperHalfSpace.thetaConstant_eq_zero_of_odd`: the theta constants of odd characteristic
  (`μ ⬝ᵥ ν` odd) vanish, which leaves the ten even ones in degree 2.
* `SiegelUpperHalfSpace.thetaConstant_smul_of_mem_siegelParabolic`: for `γ = (A, B; 0, D)` in
  `Sp(2g, ℤ)`, with `S = BAᵀ`,
  `θ_{μ,ν}(γΩ) = e^{-πi(μᵀSμ/4 + μᵀ diag(S)/2)} θ_{Aᵀμ, Dᵀ(ν + Sμ + diag(S))}(Ω)`.
* `SiegelUpperHalfSpace.summable_thetaConstant_term`: the theta series of degree 2 converges.
* `SiegelUpperHalfSpace.isHolomorphic_thetaConstant`: the theta constants of degree 2 are
  holomorphic.
* `SiegelUpperHalfSpace.thetaConstant_eq_partialInversion`: in degree 2,
  `θ_{μ,ν}(Ω) = (-iτ)^{-1/2} e^{πiμ₁ν₁/2} θ_{(-ν₁, μ₂), (μ₁, ν₂)}(J₁Ω)`.
* `SiegelUpperHalfSpace.thetaConstant_partialInversion_smul_pow_four`: the fourth powers, which
  span the forms of weight 2 on `Γ(2)` (Igusa), transform under `J₁` with weight 2:
  `θ_{(ν₁, μ₂), (μ₁, ν₂)}(J₁Ω)⁴ = -τ² θ_{μ,ν}(Ω)⁴`.
-/

open Complex Matrix Real

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] (μ ν : l → ℤ) (Ω : SiegelUpperHalfSpace l)

private lemma cexp_pi_mul_I_add_two_mul_add (z : ℂ) (k m : ℤ) :
    cexp (π * I * (z + 2 * k + m)) = (-1) ^ m * cexp (π * I * z) := by
  rw [show π * I * (z + 2 * k + m) = π * I * z + k * (2 * π * I) + m * (π * I) by ring1,
    Complex.exp_add, Complex.exp_add, exp_int_mul_two_pi_mul_I, exp_int_mul, exp_pi_mul_I]
  ring1

lemma thetaConstant_add_two_smul_left (a : l → ℤ) :
    thetaConstant (μ + 2 • a) ν Ω = thetaConstant μ ν Ω := by
  rw [thetaConstant, thetaConstant, ← (Equiv.subRight a).tsum_eq]
  refine tsum_congr fun n ↦ congrArg cexp ?_
  have h : (fun i ↦ (((Equiv.subRight a) n i : ℤ) : ℂ) + ((μ + 2 • a) i : ℤ) / 2) =
      fun i ↦ (n i : ℂ) + μ i / 2 := by
    ext i
    simp
    ring1
  rw [h]

lemma thetaConstant_add_two_smul_right (b : l → ℤ) :
    thetaConstant μ (ν + 2 • b) Ω = (-1) ^ (μ ⬝ᵥ b) * thetaConstant μ ν Ω := by
  rw [thetaConstant, thetaConstant, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  have h : ((fun i ↦ (n i : ℂ) + μ i / 2) ⬝ᵥ fun i ↦ (((ν + 2 • b) i : ℤ) : ℂ)) =
      ((fun i ↦ (n i : ℂ) + μ i / 2) ⬝ᵥ fun i ↦ ((ν i : ℤ) : ℂ)) + 2 * (n ⬝ᵥ b : ℤ) +
        (μ ⬝ᵥ b : ℤ) := by
    simp [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring1
  rw [h, ← add_assoc, ← add_assoc, cexp_pi_mul_I_add_two_mul_add]

lemma thetaConstant_neg : thetaConstant (-μ) (-ν) Ω = thetaConstant μ ν Ω := by
  rw [thetaConstant, thetaConstant, ← (Equiv.neg (l → ℤ)).tsum_eq]
  refine tsum_congr fun n ↦ congrArg cexp ?_
  have h : (fun i ↦ (((Equiv.neg (l → ℤ)) n i : ℤ) : ℂ) + ((-μ) i : ℤ) / 2) =
      -fun i ↦ (n i : ℂ) + μ i / 2 := by
    ext i
    simp
    ring1
  have hν : (fun i ↦ (((-ν) i : ℤ) : ℂ)) = -fun i ↦ (ν i : ℂ) := by
    ext i
    simp
  rw [h, hν, neg_dotProduct, mulVec_neg, dotProduct_neg, neg_neg, neg_dotProduct, dotProduct_neg,
    neg_neg]

/-- **The theta constants of odd characteristic vanish**: if `μ ⬝ᵥ ν` is odd, then
`θ_{μ,ν} = θ_{-μ,-ν} = (-1)^{μ ⬝ᵥ ν} θ_{μ,ν} = -θ_{μ,ν}`. In degree 2 this leaves the ten
theta constants of even characteristic `(μ, ν) ∈ {0, 1}² × {0, 1}²`. -/
lemma thetaConstant_eq_zero_of_odd (h : Odd (μ ⬝ᵥ ν)) : thetaConstant μ ν Ω = 0 := by
  have e : thetaConstant μ ν Ω = -thetaConstant μ ν Ω := by
    conv_lhs => rw [← thetaConstant_neg]
    rw [show -μ = μ + 2 • -μ by abel, show -ν = ν + 2 • -ν by abel, thetaConstant_add_two_smul_left,
      thetaConstant_add_two_smul_right, dotProduct_neg, h.neg.neg_one_zpow, neg_one_mul]
  exact CharZero.eq_neg_self_iff.mp e

private lemma two_dvd_dotProduct_mulVec_sub {S : Matrix l l ℤ} (hS : Sᵀ = S) (n : l → ℤ) :
    2 ∣ n ⬝ᵥ S *ᵥ n - n ⬝ᵥ S.diag := by
  classical
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  rw [← Nat.cast_ofNat, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [dotProduct, mulVec, diag, Finset.mul_sum, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  rw [← Finset.sum_sub_distrib]
  have e : ∀ i, ∑ j, (n i : ZMod 2) * ((S i j : ZMod 2) * (n j : ZMod 2)) -
      (n i : ZMod 2) * (S i i : ZMod 2) = ∑ j, ((n i : ZMod 2) * ((S i j : ZMod 2) *
        (n j : ZMod 2)) - if i = j then (n i : ZMod 2) * (S i i : ZMod 2) else 0) := fun i ↦ by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  simp only [e]
  rw [← Finset.sum_product']
  refine Finset.sum_ninvolution Prod.swap (fun p ↦ ?_) (fun p hp hpp ↦ hp ?_) (fun p ↦ by simp)
    (fun p ↦ by simp)
  · rcases p with ⟨i, j⟩
    rcases eq_or_ne i j with rfl | hij
    · exact h2 _
    have hji : S j i = S i j := by rw [← transpose_apply S i j, hS]
    rw [Prod.fst_swap, Prod.snd_swap, ite_eq_right hij, ite_eq_right hij.symm, sub_zero, sub_zero,
      hji, show (n j : ZMod 2) * ((S i j : ZMod 2) * n i) = n i * (S i j * n j) by ring1, h2]
  · rcases p with ⟨i, j⟩
    have hji : j = i := congrArg Prod.fst hpp
    subst hji
    simp only [↓reduceIte]
    rw [mul_comm (S j j : ZMod 2), ← mul_assoc, hsq, sub_self]

private lemma halfShift_dotProduct (u v a b : l → ℤ) :
    ((fun i ↦ (u i : ℂ) + v i / 2) ⬝ᵥ fun i ↦ (a i : ℂ) + b i / 2) =
      (u ⬝ᵥ a : ℤ) + ((u ⬝ᵥ b : ℤ) + (v ⬝ᵥ a : ℤ)) / 2 + (v ⬝ᵥ b : ℤ) / 4 := by
  simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring1

private lemma halfShift_dotProduct_intCast (u v w : l → ℤ) :
    ((fun i ↦ (u i : ℂ) + v i / 2) ⬝ᵥ fun i ↦ (w i : ℂ)) = (u ⬝ᵥ w : ℤ) + (v ⬝ᵥ w : ℤ) / 2 := by
  simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring1

private lemma map_intCast_mulVec_halfShift (S : Matrix l l ℤ) (u v : l → ℤ) :
    S.map (Int.castRingHom ℂ) *ᵥ (fun i ↦ (u i : ℂ) + v i / 2) =
      fun i ↦ ((S *ᵥ u) i : ℂ) + ((S *ᵥ v) i : ℂ) / 2 := by
  ext i
  simp only [mulVec, dotProduct, map_apply, eq_intCast, Int.cast_sum, Int.cast_mul,
    Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring1

variable {ι κ : Type*} (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ)

private lemma map_ofReal_toBlocks₁₁ :
    (M.map (Int.castRingHom ℝ)).toBlocks₁₁.map ofReal = M.toBlocks₁₁.map (Int.castRingHom ℂ) := by
  ext
  simp [toBlocks₁₁]

private lemma map_ofReal_toBlocks₁₂ :
    (M.map (Int.castRingHom ℝ)).toBlocks₁₂.map ofReal = M.toBlocks₁₂.map (Int.castRingHom ℂ) := by
  ext
  simp [toBlocks₁₂]

private lemma map_ofReal_toBlocks₂₁ :
    (M.map (Int.castRingHom ℝ)).toBlocks₂₁.map ofReal = M.toBlocks₂₁.map (Int.castRingHom ℂ) := by
  ext
  simp [toBlocks₂₁]

private lemma map_ofReal_toBlocks₂₂ :
    (M.map (Int.castRingHom ℝ)).toBlocks₂₂.map ofReal = M.toBlocks₂₂.map (Int.castRingHom ℂ) := by
  ext
  simp [toBlocks₂₂]

variable [DecidableEq l] {γ : symplecticGroup l ℤ}

private lemma mul_J_mul_transpose_of_mem_siegelParabolic
    (hγ : γ ∈ SymplecticGroup.siegelParabolic l ℤ) :
    fromBlocks (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂
      0 (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂ * J l ℤ *
      (fromBlocks (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁
        (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂ 0 (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂)ᵀ =
      J l ℤ := by
  rw [← show (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₁ = 0 from hγ, fromBlocks_toBlocks]
  exact SymplecticGroup.mem_iff.mp γ.2

lemma toBlocks₂₂_mul_transpose_toBlocks₁₁ (hγ : γ ∈ SymplecticGroup.siegelParabolic l ℤ) :
    (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂ * (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ᵀ = 1 := by
  simpa [J, fromBlocks_transpose, fromBlocks_multiply] using
    congrArg toBlocks₂₁ (mul_J_mul_transpose_of_mem_siegelParabolic hγ)

lemma toBlocks₁₂_mul_transpose_toBlocks₁₁ (hγ : γ ∈ SymplecticGroup.siegelParabolic l ℤ) :
    (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂ * (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ᵀ =
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ * (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂ᵀ := by
  refine add_neg_eq_zero.mp ?_
  simpa [J, fromBlocks_transpose, fromBlocks_multiply] using
    congrArg toBlocks₁₁ (mul_J_mul_transpose_of_mem_siegelParabolic hγ)

lemma denom_of_mem_siegelParabolic (hγ : γ ∈ SymplecticGroup.siegelParabolic l ℤ) :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Ω.val =
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂.map (Int.castRingHom ℂ) := by
  rw [denom, SymplecticGroup.coe_map_apply, map_ofReal_toBlocks₂₁, map_ofReal_toBlocks₂₂,
    show (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₁ = 0 from hγ, Matrix.map_zero _ (map_zero _),
    Matrix.zero_mul, zero_add]

lemma val_smul_of_mem_siegelParabolic (hγ : γ ∈ SymplecticGroup.siegelParabolic l ℤ) :
    (SymplecticGroup.map (Int.castRingHom ℝ) γ • Ω).val =
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁.map (Int.castRingHom ℂ) * Ω.val *
        (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ᵀ.map (Int.castRingHom ℂ) +
      ((γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂ *
        (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ᵀ).map (Int.castRingHom ℂ) := by
  have hD : ((γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂.map (Int.castRingHom ℂ))⁻¹ =
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ᵀ.map (Int.castRingHom ℂ) := by
    refine inv_eq_right_inv ?_
    rw [← Matrix.map_mul, toBlocks₂₂_mul_transpose_toBlocks₁₁ hγ, Matrix.map_one _ (map_zero _)
      (map_one _)]
  rw [val_smul, num, denom, SymplecticGroup.coe_map_apply, map_ofReal_toBlocks₁₁,
    map_ofReal_toBlocks₁₂, map_ofReal_toBlocks₂₁, map_ofReal_toBlocks₂₂,
    show (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₁ = 0 from hγ, Matrix.map_zero _ (map_zero _),
    Matrix.zero_mul, zero_add, hD, Matrix.add_mul, Matrix.map_mul]

/-- **The transformation law of theta constants under the Siegel parabolic subgroup** of
`Sp(2g, ℤ)`: for `γ = (A, B; 0, D)`, which acts by `Ω ↦ AΩAᵀ + S` with `S = BAᵀ` symmetric and
`D = A⁻ᵀ`, `θ_{μ,ν}(γΩ) = e^{-πi(μᵀSμ/4 + μᵀ diag(S)/2)} θ_{Aᵀμ, Dᵀ(ν + Sμ + diag(S))}(Ω)`. The
translation by `S` shifts `ν` by `Sμ + diag(S)`, since `nᵀSn ≡ nᵀ diag(S) (mod 2)` for integral
`n`, and the rotation `Ω ↦ AΩAᵀ` is the change of summation variable `n ↦ Aᵀn`. -/
lemma thetaConstant_smul_of_mem_siegelParabolic (hγ : γ ∈ SymplecticGroup.siegelParabolic l ℤ) :
    letI A : Matrix l l ℤ := (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁
    letI S : Matrix l l ℤ := (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂ * Aᵀ
    thetaConstant μ ν (SymplecticGroup.map (Int.castRingHom ℝ) γ • Ω) =
      cexp (-(π * I * ((μ ⬝ᵥ S *ᵥ μ : ℤ) / 4 + (μ ⬝ᵥ S.diag : ℤ) / 2))) *
        thetaConstant (Aᵀ *ᵥ μ) ((γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂ᵀ *ᵥ
          (ν + S *ᵥ μ + S.diag)) Ω := by
  have hDA : (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂ *
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ᵀ = 1 :=
    toBlocks₂₂_mul_transpose_toBlocks₁₁ hγ
  have hS : (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂ * (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ᵀ =
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁ * (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂ᵀ :=
    toBlocks₁₂_mul_transpose_toBlocks₁₁ hγ
  rw [thetaConstant, thetaConstant, val_smul_of_mem_siegelParabolic Ω hγ, ← tsum_mul_left]
  set A : Matrix l l ℤ := (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁
  set D : Matrix l l ℤ := (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂
  set S : Matrix l l ℤ := (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₂ * Aᵀ with hS'
  have hSS : Sᵀ = S := by
    rw [hS', transpose_mul, transpose_transpose, ← hS]
  let e : (l → ℤ) ≃ (l → ℤ) :=
    { toFun := fun n ↦ Aᵀ *ᵥ n
      invFun := fun n ↦ D *ᵥ n
      left_inv := fun n ↦ by simp only [mulVec_mulVec, hDA, one_mulVec]
      right_inv := fun n ↦ by simp only [mulVec_mulVec, mul_eq_one_comm.mp hDA, one_mulVec] }
  conv_rhs => rw [← e.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  have he : e n = Aᵀ *ᵥ n := rfl
  have hlin (u w : l → ℤ) : (Aᵀ *ᵥ u) ⬝ᵥ (Dᵀ *ᵥ w) = u ⬝ᵥ w := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hDA, one_mulVec]
  have hq : ((fun i ↦ (n i : ℂ) + μ i / 2) ⬝ᵥ
      (A.map (Int.castRingHom ℂ) * Ω.val * Aᵀ.map (Int.castRingHom ℂ)) *ᵥ
        fun i ↦ (n i : ℂ) + μ i / 2) =
      (fun i ↦ ((Aᵀ *ᵥ n) i : ℂ) + ((Aᵀ *ᵥ μ) i : ℂ) / 2) ⬝ᵥ Ω.val *ᵥ
        fun i ↦ ((Aᵀ *ᵥ n) i : ℂ) + ((Aᵀ *ᵥ μ) i : ℂ) / 2 := by
    rw [← map_intCast_mulVec_halfShift, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      ← mulVec_transpose, transpose_map]
  have hμn : μ ⬝ᵥ S *ᵥ n = n ⬝ᵥ S *ᵥ μ := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hSS, dotProduct_comm]
  rcases two_dvd_dotProduct_mulVec_sub hSS n with ⟨k, hk⟩
  rw [he, add_mulVec, dotProduct_add, hq, map_intCast_mulVec_halfShift, halfShift_dotProduct,
    halfShift_dotProduct_intCast, halfShift_dotProduct_intCast, hlin, hlin, hμn, ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, ?_⟩
  rw [sub_eq_iff_eq_add] at hk
  simp only [dotProduct_add, Int.cast_add, hk]
  push_cast
  ring1

end SiegelUpperHalfSpace

namespace SymplecticGroup

/-- The **partial inversion** `J₁ = (a, b; c, d) ∈ Sp(4, ℤ)`, with `a = d = diag(0, 1)`,
`b = diag(-1, 0)` and `c = diag(1, 0)`: the image of `(0, -1; 1, 0) ∈ SL(2, ℤ)` acting on the first
coordinate. It acts on `ℋ₂` by `(τ, z; z, ω) ↦ (-1/τ, z/τ; z/τ, ω - z²/τ)`
(`SiegelUpperHalfSpace.val_partialInversion_smul`), with automorphy factor `det(cΩ + d) = τ`. -/
def partialInversion : symplecticGroup (Fin 2) ℤ :=
  ⟨fromBlocks !![0, 0; 0, 1] !![-1, 0; 0, 0] !![1, 0; 0, 0] !![0, 0; 0, 1], by
    rw [mem_iff, J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [vecMul]⟩

end SymplecticGroup

namespace SiegelUpperHalfSpace

variable (Ω : SiegelUpperHalfSpace (Fin 2)) (μ ν : Fin 2 → ℤ)

private lemma val_one_zero : Ω.val 1 0 = Ω.val 0 1 := by
  rw [← transpose_apply Ω.val 0 1, Ω.transpose_val]

private lemma val_zero_zero_ne_zero : Ω.val 0 0 ≠ 0 := fun h ↦ by
  simpa [h] using Ω.posDef_im.diag_pos (i := 0)

lemma val_partialInversion_smul :
    (SymplecticGroup.map (Int.castRingHom ℝ) SymplecticGroup.partialInversion • Ω).val =
      !![-(Ω.val 0 0)⁻¹, Ω.val 0 1 / Ω.val 0 0; Ω.val 0 1 / Ω.val 0 0,
        Ω.val 1 1 - Ω.val 0 1 ^ 2 / Ω.val 0 0] := by
  have hτ : Ω.val 0 0 ≠ 0 := val_zero_zero_ne_zero Ω
  have hinv : (!![Ω.val 0 0, Ω.val 0 1; 0, 1])⁻¹ =
      !![(Ω.val 0 0)⁻¹, -(Ω.val 0 1 / Ω.val 0 0); 0, 1] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hτ, mul_div_cancel₀]
  have hden : denom (SymplecticGroup.map (Int.castRingHom ℝ) SymplecticGroup.partialInversion)
      Ω.val = !![Ω.val 0 0, Ω.val 0 1; 0, 1] := by
    rw [denom, SymplecticGroup.coe_map_apply, map_ofReal_toBlocks₂₁, map_ofReal_toBlocks₂₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SymplecticGroup.partialInversion, Matrix.mul_apply]
  have hnum : num (SymplecticGroup.map (Int.castRingHom ℝ) SymplecticGroup.partialInversion)
      Ω.val = !![-1, 0; Ω.val 0 1, Ω.val 1 1] := by
    rw [num, SymplecticGroup.coe_map_apply, map_ofReal_toBlocks₁₁, map_ofReal_toBlocks₁₂]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SymplecticGroup.partialInversion, Matrix.mul_apply, val_one_zero]
  rw [val_smul, hnum, hden, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring1

/-- The constant `ε = det(Im Ω) / tr(Im Ω) > 0` of `Ω ∈ ℋ₂`, for which `xᵀ (Im Ω) x ≥ ε xᵀx` for
every real vector `x`. -/
private noncomputable def decay : ℝ :=
  ((Ω.val 0 0).im * (Ω.val 1 1).im - (Ω.val 0 1).im ^ 2) / ((Ω.val 0 0).im + (Ω.val 1 1).im)

private lemma decay_pos : 0 < decay Ω := by
  have ha : 0 < (Ω.val 0 0).im := by simpa using Ω.posDef_im.diag_pos (i := 0)
  have hc : 0 < (Ω.val 1 1).im := by simpa using Ω.posDef_im.diag_pos (i := 1)
  have hdet : 0 < (Ω.val 0 0).im * (Ω.val 1 1).im - (Ω.val 0 1).im ^ 2 := by
    have h : 0 < (Ω.val.map im).det := Ω.posDef_im.det_pos
    rw [det_fin_two] at h
    simpa [val_one_zero, sq] using h
  exact div_pos hdet (add_pos ha hc)

private lemma decay_mul_le (r : Fin 2 → ℝ) : decay Ω * (r 0 ^ 2 + r 1 ^ 2) ≤
    (Ω.val 0 0).im * r 0 ^ 2 + 2 * (Ω.val 0 1).im * r 0 * r 1 + (Ω.val 1 1).im * r 1 ^ 2 := by
  have ha : 0 < (Ω.val 0 0).im := by simpa using Ω.posDef_im.diag_pos (i := 0)
  have hc : 0 < (Ω.val 1 1).im := by simpa using Ω.posDef_im.diag_pos (i := 1)
  rw [decay, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((Ω.val 0 0).im * r 0 + (Ω.val 0 1).im * r 1),
    sq_nonneg ((Ω.val 1 1).im * r 1 + (Ω.val 0 1).im * r 0)]

private lemma re_exponent (r : Fin 2 → ℝ) :
    (π * I * ((fun i ↦ (r i : ℂ)) ⬝ᵥ Ω.val *ᵥ (fun i ↦ (r i : ℂ)) +
      (fun i ↦ (r i : ℂ)) ⬝ᵥ fun i ↦ (ν i : ℂ))).re = -(π * ((Ω.val 0 0).im * r 0 ^ 2 +
        2 * (Ω.val 0 1).im * r 0 * r 1 + (Ω.val 1 1).im * r 1 ^ 2)) := by
  simp [dotProduct, mulVec, val_one_zero]
  ring1

private lemma summable_rexp_neg_mul_add_sq {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Summable fun n : ℤ ↦ rexp (-(π * ε * (n + c) ^ 2)) := by
  have h : ∀ n : ℤ, rexp (-(π * ε * (n + c) ^ 2)) =
      ‖jacobiTheta₂_term n (c * ε * I) (ε * I)‖ * rexp (-(π * ε * c ^ 2)) := fun n ↦ by
    rw [norm_jacobiTheta₂_term, ← Real.exp_add]
    congr 1
    simp
    ring1
  simp only [h]
  exact ((summable_jacobiTheta₂_term_iff _ _).mpr (by simpa using hε)).norm.mul_right _

/-- **The theta series of degree 2 converges**: for `Ω ∈ ℋ₂`, the terms of the series defining
`θ_{μ,ν}(Ω)` have norm `e^{-π xᵀ (Im Ω) x} ≤ e^{-πε x₁²} e^{-πε x₂²}`, with `x = n + μ/2` and
`ε = det(Im Ω) / tr(Im Ω) > 0`, a product of two convergent Gaussian sums. -/
lemma summable_thetaConstant_term :
    letI x : (Fin 2 → ℤ) → Fin 2 → ℂ := fun n i ↦ n i + μ i / 2
    Summable fun n ↦ cexp (π * I * (x n ⬝ᵥ Ω.val *ᵥ x n + x n ⬝ᵥ fun i ↦ (ν i : ℂ))) := by
  dsimp only
  refine Summable.of_norm_bounded (g := fun n : Fin 2 → ℤ ↦
    rexp (-(π * decay Ω * (n 0 + (μ 0 / 2 : ℝ)) ^ 2)) *
      rexp (-(π * decay Ω * (n 1 + (μ 1 / 2 : ℝ)) ^ 2))) ?_ fun n ↦ ?_
  · exact (finTwoArrowEquiv ℤ).summable_iff.mpr <|
      (summable_rexp_neg_mul_add_sq (decay_pos Ω) _).mul_of_nonneg
        (summable_rexp_neg_mul_add_sq (decay_pos Ω) _) (fun _ ↦ (Real.exp_pos _).le)
          fun _ ↦ (Real.exp_pos _).le
  · have hx : (fun i ↦ (n i : ℂ) + μ i / 2) = fun i ↦ ((n i + μ i / 2 : ℝ) : ℂ) := by
      ext i
      push_cast
      ring1
    rw [hx, Complex.norm_exp, re_exponent, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [decay_mul_le Ω fun i ↦ n i + μ i / 2, Real.pi_pos]

private lemma tsum_finTwo_eq {f : (Fin 2 → ℤ) → ℂ} (hf : Summable f) :
    ∑' n, f n = ∑' a : ℤ, ∑' b : ℤ, f ![b, a] := by
  rw [← ((Equiv.prodComm ℤ ℤ).trans (finTwoArrowEquiv ℤ).symm).tsum_eq]
  have h : Summable (f ∘ (Equiv.prodComm ℤ ℤ).trans (finTwoArrowEquiv ℤ).symm) :=
    ((Equiv.prodComm ℤ ℤ).trans (finTwoArrowEquiv ℤ).symm).summable_iff.mpr hf
  exact h.tsum_prod' fun a ↦ h.prod_factor a

/-- **The transformation law of theta constants of degree 2 under the partial inversion** `J₁`:
`θ_{μ,ν}(Ω) = (-iτ)^{-1/2} e^{πiμ₁ν₁/2} θ_{(-ν₁, μ₂), (μ₁, ν₂)}(J₁Ω)` for `Ω = (τ, z; z, ω)`, with
the principal branch of the square root, where `J₁Ω = (-1/τ, z/τ; z/τ, ω - z²/τ)`. Summing over the
first coordinate first, the inner sums are values of Jacobi's theta function `jacobiTheta₂` in the
variable `τ`, to which its functional equation applies. -/
lemma thetaConstant_eq_partialInversion : thetaConstant μ ν Ω =
    1 / (-I * Ω.val 0 0) ^ (1 / 2 : ℂ) * cexp (π * I * (μ 0 * ν 0 : ℤ) / 2) *
      thetaConstant ![-ν 0, μ 1] ![μ 0, ν 1]
        (SymplecticGroup.map (Int.castRingHom ℝ) SymplecticGroup.partialInversion • Ω) := by
  rw [thetaConstant, thetaConstant, tsum_finTwo_eq (summable_thetaConstant_term Ω μ ν),
    tsum_finTwo_eq (summable_thetaConstant_term _ _ _), val_partialInversion_smul,
    ← tsum_mul_left]
  refine tsum_congr fun a ↦ ?_
  have hτ : Ω.val 0 0 ≠ 0 := val_zero_zero_ne_zero Ω
  trans ∑' b : ℤ, cexp (π * I * (Ω.val 1 1 * (a + μ 1 / 2) ^ 2 + (a + μ 1 / 2) * ν 1 +
    Ω.val 0 0 * μ 0 ^ 2 / 4 + μ 0 * (Ω.val 0 1 * (a + μ 1 / 2) + ν 0 / 2))) *
      jacobiTheta₂_term b (Ω.val 0 0 * μ 0 / 2 + Ω.val 0 1 * (a + μ 1 / 2) + ν 0 / 2) (Ω.val 0 0)
  · refine tsum_congr fun b ↦ ?_
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    congr 1
    simp [dotProduct, mulVec, val_one_zero]
    ring1
  rw [tsum_mul_left, ← jacobiTheta₂, jacobiTheta₂_functional_equation, jacobiTheta₂,
    ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun m ↦ ?_
  rw [jacobiTheta₂_term, mul_assoc (1 / _) (cexp _) (cexp _),
    mul_assoc (1 / _) (cexp _) (cexp _), mul_left_comm]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp [dotProduct, mulVec]
  field_simp
  ring1

/-- **The fourth powers of the theta constants of degree 2 under `J₁`**: the square root disappears
and `θ_{(ν₁, μ₂), (μ₁, ν₂)}(J₁Ω)⁴ = -τ² θ_{μ,ν}(Ω)⁴`, where `τ = det(cΩ + d)` is the automorphy
factor of `J₁`: the fourth powers transform with weight 2, up to the sign and the exchange of
`μ₁` and `ν₁`. -/
lemma thetaConstant_partialInversion_smul_pow_four : thetaConstant ![ν 0, μ 1] ![μ 0, ν 1]
    (SymplecticGroup.map (Int.castRingHom ℝ) SymplecticGroup.partialInversion • Ω) ^ 4 =
      -Ω.val 0 0 ^ 2 * thetaConstant μ ν Ω ^ 4 := by
  have hτ : Ω.val 0 0 ≠ 0 := val_zero_zero_ne_zero Ω
  have hμ : ![ν 0, μ 1] = ![-ν 0, μ 1] + 2 • ![ν 0, 0] := by
    ext i
    fin_cases i <;> simp
    ring1
  have hs : ((-I * Ω.val 0 0) ^ (1 / 2 : ℂ)) ^ 4 = -Ω.val 0 0 ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, ← cpow_nat_mul]
    norm_num
    rw [mul_pow, I_sq, neg_one_mul]
  have he : cexp (π * I * (μ 0 * ν 0 : ℤ) / 2) ^ 4 = 1 := by
    rw [← Complex.exp_nat_mul, show (4 : ℕ) * (π * I * (μ 0 * ν 0 : ℤ) / 2) =
      (μ 0 * ν 0 : ℤ) * (2 * π * I) by push_cast; ring1, exp_int_mul_two_pi_mul_I]
  rw [thetaConstant_eq_partialInversion Ω μ ν, hμ, thetaConstant_add_two_smul_left, mul_pow,
    mul_pow, he, div_pow, hs]
  field_simp

/-- The linear form `Z ↦ ∑ᵢⱼ xᵢ Zᵢⱼ xⱼ` on the square matrices given by their entries, for a real
vector `x`. -/
private noncomputable def quadForm (x : Fin 2 → ℝ) : (Fin 2 → Fin 2 → ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun Z ↦ ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * Z i j
      map_add' := fun Z W ↦ by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c Z ↦ by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        ring1 }
    (∑ i, ∑ j, |x i| * |x j|) fun Z ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
      refine (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans <|
        Finset.sum_le_sum fun j _ ↦ ?_
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i))
        (by positivity)

private lemma quadForm_apply (x : Fin 2 → ℝ) (Z : Fin 2 → Fin 2 → ℂ) :
    quadForm x Z = ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * Z i j :=
  rfl

private lemma norm_quadForm_le (x : Fin 2 → ℝ) : ‖quadForm x‖ ≤ 2 * (x 0 ^ 2 + x 1 ^ 2) := by
  refine (LinearMap.mkContinuous_norm_le _ (by positivity) _).trans ?_
  simp only [Fin.sum_univ_two]
  nlinarith [sq_abs (x 0), sq_abs (x 1), sq_nonneg (|x 0| - |x 1|)]

variable {Z₀ : Fin 2 → Fin 2 → ℂ}

private lemma im_quadForm_ge (hZ₀ : Z₀ ∈ symmetrizePreimage (Fin 2)) (x : Fin 2 → ℝ)
    {Z : Fin 2 → Fin 2 → ℂ} {r : ℝ} (hZ : ‖Z - Z₀‖ < r) :
    (decay ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩ - 2 * r) * (x 0 ^ 2 + x 1 ^ 2) ≤
      (quadForm x Z).im := by
  have h1 : (quadForm x Z₀).im = (symmetrize Z₀ 0 0).im * x 0 ^ 2 +
      2 * (symmetrize Z₀ 0 1).im * x 0 * x 1 + (symmetrize Z₀ 1 1).im * x 1 ^ 2 := by
    simp [quadForm_apply, symmetrize]
    ring1
  have h2 : |(quadForm x (Z - Z₀)).im| ≤ 2 * (x 0 ^ 2 + x 1 ^ 2) * r :=
    (abs_im_le_norm _).trans <| ((quadForm x).le_opNorm _).trans <|
      mul_le_mul (norm_quadForm_le x) hZ.le (norm_nonneg _) (by positivity)
  have h3 : (quadForm x Z).im = (quadForm x Z₀).im + (quadForm x (Z - Z₀)).im := by
    rw [map_sub, sub_im, add_sub_cancel]
  nlinarith [decay_mul_le ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩ x, abs_le.mp h2]

/-- The term `e^{πi(xᵀZx + xᵀν)}` of the theta series, for `x = n + μ/2`, as a function of a square
matrix `Z` given by its entries. -/
private noncomputable def thetaTerm (n : Fin 2 → ℤ) (Z : Fin 2 → Fin 2 → ℂ) : ℂ :=
  cexp (π * I * (quadForm (fun i ↦ n i + μ i / 2) Z + ((∑ i, (n i + μ i / 2) * ν i : ℝ) : ℂ)))

private lemma hasFDerivAt_thetaTerm (n : Fin 2 → ℤ) (Z : Fin 2 → Fin 2 → ℂ) :
    HasFDerivAt (thetaTerm μ ν n) (thetaTerm μ ν n Z • (π * I) • quadForm fun i ↦ n i + μ i / 2)
      Z :=
  (((quadForm _).hasFDerivAt.add_const _).const_mul _).cexp

private lemma norm_thetaTerm_le (hZ₀ : Z₀ ∈ symmetrizePreimage (Fin 2)) (n : Fin 2 → ℤ)
    {Z : Fin 2 → Fin 2 → ℂ}
    (hZ : ‖Z - Z₀‖ < decay ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩ / 4) :
    ‖thetaTerm μ ν n Z‖ ≤ rexp (-(π * (decay ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩ / 2) *
      ((n 0 + μ 0 / 2) ^ 2 + (n 1 + μ 1 / 2) ^ 2))) := by
  have h : (decay ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩ -
      2 * (decay ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩ / 4)) *
        ((n 0 + μ 0 / 2) ^ 2 + (n 1 + μ 1 / 2) ^ 2) ≤
      (quadForm (fun i ↦ n i + μ i / 2) Z).im :=
    im_quadForm_ge hZ₀ (fun i ↦ n i + μ i / 2) hZ
  rw [thetaTerm, Complex.norm_exp, Real.exp_le_exp]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im]
  nlinarith [Real.pi_pos]

private lemma rexp_mul_le {ε t : ℝ} (hε : 0 < ε) :
    rexp (-(π * (ε / 2) * t)) * (π * (2 * t)) ≤ 8 / ε * rexp (-(π * (ε / 4) * t)) := by
  have hE : 0 ≤ rexp (-(π * (ε / 4) * t)) := (Real.exp_pos _).le
  have hEF : rexp (-(π * (ε / 4) * t)) * rexp (π * (ε / 4) * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hkey : π * (ε / 4) * t ≤ rexp (π * (ε / 4) * t) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hsq : rexp (-(π * (ε / 2) * t)) =
      rexp (-(π * (ε / 4) * t)) * rexp (-(π * (ε / 4) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring1
  rw [hsq, show rexp (-(π * (ε / 4) * t)) * rexp (-(π * (ε / 4) * t)) * (π * (2 * t)) =
      8 / ε * rexp (-(π * (ε / 4) * t)) * (rexp (-(π * (ε / 4) * t)) * (π * (ε / 4) * t)) by
    field_simp
    ring1]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hE) (by positivity)).trans ?_
  rw [hEF, mul_one]

private lemma hasFDerivAt_tsum_thetaTerm (hZ₀ : Z₀ ∈ symmetrizePreimage (Fin 2)) :
    HasFDerivAt (fun Z ↦ ∑' n, thetaTerm μ ν n Z)
      (∑' n, thetaTerm μ ν n Z₀ • (π * I) • quadForm fun i ↦ n i + μ i / 2) Z₀ := by
  set ε : ℝ := decay ⟨symmetrize Z₀, transpose_symmetrize Z₀, hZ₀⟩
  have hε0 : 0 < ε := decay_pos _
  have hε4 : 0 < ε / 4 := div_pos hε0 four_pos
  have hg : Summable fun n : Fin 2 → ℤ ↦ rexp (-(π * (ε / 4) * (n 0 + (μ 0 / 2 : ℝ)) ^ 2)) *
      rexp (-(π * (ε / 4) * (n 1 + (μ 1 / 2 : ℝ)) ^ 2)) :=
    (finTwoArrowEquiv ℤ).summable_iff.mpr <|
      (summable_rexp_neg_mul_add_sq hε4 _).mul_of_nonneg (summable_rexp_neg_mul_add_sq hε4 _)
        (fun _ ↦ (Real.exp_pos _).le) fun _ ↦ (Real.exp_pos _).le
  have hexp (n : Fin 2 → ℤ) :
      rexp (-(π * (ε / 4) * ((n 0 + μ 0 / 2) ^ 2 + (n 1 + μ 1 / 2) ^ 2))) =
        rexp (-(π * (ε / 4) * (n 0 + (μ 0 / 2 : ℝ)) ^ 2)) *
          rexp (-(π * (ε / 4) * (n 1 + (μ 1 / 2 : ℝ)) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring1
  refine hasFDerivAt_tsum_of_isPreconnected (hg.mul_left (8 / ε)) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (fun n Z _ ↦ hasFDerivAt_thetaTerm μ ν n Z) (fun n Z hZ ↦ ?_)
    (Metric.mem_ball_self hε4) ?_ (Metric.mem_ball_self hε4)
  · rw [Metric.mem_ball, dist_eq_norm] at hZ
    rw [norm_smul, norm_smul, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg
      Real.pi_pos.le, ← hexp]
    refine (mul_le_mul (norm_thetaTerm_le μ ν hZ₀ n hZ) (mul_le_mul_of_nonneg_left
      (norm_quadForm_le _) Real.pi_pos.le) (by positivity) (Real.exp_pos _).le).trans ?_
    exact rexp_mul_le hε0
  · refine hg.of_norm_bounded fun n ↦ ?_
    rw [← hexp]
    refine (norm_thetaTerm_le μ ν hZ₀ n (by rwa [sub_self, norm_zero])).trans ?_
    rw [Real.exp_le_exp, neg_le_neg_iff]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)
      (by positivity)

/-- **The theta constants of degree 2 are holomorphic** on the Siegel upper half-space: on a ball
around each point, `xᵀ (Im Z) x ≥ (ε/2) xᵀx` for real `x`, with `ε = det(Im Ω) / tr(Im Ω)` at the
centre, so the series of the derivatives of the terms converges uniformly there. -/
lemma isHolomorphic_thetaConstant : IsHolomorphic (thetaConstant μ ν) := by
  refine isHolomorphic_iff_differentiableOn.mpr <| DifferentiableOn.congr (fun Z₀ hZ₀ ↦
    (hasFDerivAt_tsum_thetaTerm μ ν hZ₀).differentiableAt.differentiableWithinAt) fun Z hZ ↦ ?_
  rw [extend_of_mem _ hZ, thetaConstant]
  refine tsum_congr fun n ↦ congrArg cexp (congrArg _ ?_)
  simp [dotProduct, mulVec, symmetrize, quadForm_apply]
  ring1

end SiegelUpperHalfSpace
