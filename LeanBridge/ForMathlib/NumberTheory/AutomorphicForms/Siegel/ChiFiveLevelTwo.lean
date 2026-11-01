import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ChiFiveTransformation
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IgusaLevelTwoModularity

/-!
# `χ₅` is a Siegel modular form of weight 5 on `Γ[2]`

The product `χ₅ = ∏ θ_m` of the ten even theta constants of degree 2 is a Siegel modular form of
weight 5 on the principal congruence subgroup `Γ[2]` of `Sp(4, ℤ)` (LMFDB
`mf.siegel.family.gamma_2`): the field `chi5_mem` of
`SiegelUpperHalfSpace.IgusaLevelTwo.IgusaLevelTwoStructure`. As for the fourth powers of the theta
constants, `Γ[2]` is the normal closure of `ι₁(1, 0; 2, 1)` and `P(ℤ) ∩ Γ[2]`
(`SiegelUpperHalfSpace.IgusaLevelTwo.Gamma_two_le_of_normal`), so it suffices that:
* every `γ ∈ Sp(4, ℤ)` sends `χ₅` to a constant multiple of itself, so that the stabiliser of `χ₅`
  in weight 5 is normal. For `J₁` the constant is `-1`; an element `(A, B; 0, D)` of the Siegel
  parabolic subgroup `P(ℤ)` sends each `θ_m` to a constant times `±θ_{m'}`, where `m ↦ m'` is the
  affine action `(μ, ν) ↦ (Aᵀμ, Dᵀ(ν + Sμ + diag S))`, `S = BAᵀ`, which permutes the ten even
  characteristics modulo 2, and `θ_{m'}` only depends on `m'` modulo 2 up to the sign
  `(-1)^{μ'ᵀb}` of the shift `ν' + 2b`;
* `ι₁(1, 0; 2, 1)` fixes `χ₅` in weight 5
  (`SiegelUpperHalfSpace.Ibukiyama.chi5_embedFirst_lowerUnipotent_smul`);
* `p = (A, B; 0, D) ∈ P(ℤ) ∩ Γ[2]` fixes `χ₅` in weight 5. Writing `S = 2T` and `Dᵀ = 1 + 2N`,
  `p` fixes the characteristics modulo 2, and `θ_m(pΩ) = e^{πi(μᵀw - μᵀTμ/2 - μᵀ diag T)} θ_m(Ω)`
  with `w = Nν + Dᵀ(Tμ + diag T)`. Over the ten even characteristics the exponents add up to
  `N₁₁ + N₂₂` modulo 2, so `χ₅(pΩ) = (-1)^{N₁₁ + N₂₂} χ₅(Ω) = det(D)⁵ χ₅(Ω)`, since
  `det D = det(1 + 2N) ≡ 1 + 2(N₁₁ + N₂₂) (mod 4)` and `det D = ±1`.

The space here is `M₅(Γ[2])`, as in Igusa's theorem and in the knowl; `χ₅` is moreover a cusp form,
which is not proved here: the cusp condition `Φ(χ₅ ∣ γ) = 0` for all `γ ∈ Sp(4, ℚ)` needs the
behaviour of the theta constants at the boundary.

## Main definitions

* `SiegelUpperHalfSpace.Ibukiyama.evenChars`: the ten even characteristics modulo 2.
* `SiegelUpperHalfSpace.Ibukiyama.chiFiveStabilizer`: the subgroup of `Sp(4, ℤ)` fixing `χ₅` in
  weight 5, and the instance `SiegelUpperHalfSpace.Ibukiyama.chiFiveStabilizer.Normal`.

## Main results

* `SiegelUpperHalfSpace.Ibukiyama.exists_slash_chi5_eq_smul`: every `γ ∈ Sp(4, ℤ)` sends `χ₅` to
  a constant multiple of itself in weight 5.
* `SiegelUpperHalfSpace.Ibukiyama.slash_chi5_of_mem_siegelParabolic_of_mem_Gamma_two`:
  `P(ℤ) ∩ Γ[2]` fixes `χ₅` in weight 5.
* `SiegelUpperHalfSpace.Ibukiyama.Gamma_two_le_chiFiveStabilizer`: `Γ[2]` fixes `χ₅` in weight 5.
* `SiegelUpperHalfSpace.Ibukiyama.chi5_mem_scalarModularForms`: `χ₅ ∈ M₅(Γ[2])`.
-/

open Complex Matrix Real SymplecticGroup

namespace SiegelUpperHalfSpace.Ibukiyama

variable (Ω : SiegelUpperHalfSpace (Fin 2)) {p γ : symplecticGroup (Fin 2) ℤ}
    {T N : Matrix (Fin 2) (Fin 2) ℤ}

/-- The ten **even characteristics** `(μ, ν) ∈ (ℤ/2ℤ)² × (ℤ/2ℤ)²`, those with `μ ⬝ᵥ ν = 0`
(LMFDB `mf.siegel.family.gamma_2`). -/
def evenChars : Finset ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  Finset.univ.filter fun v ↦ v.1 ⬝ᵥ v.2 = 0

lemma evenChars_eq : evenChars = {(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]),
    (![0, 0], ![1, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]), (![1, 0], ![0, 0]),
    (![1, 0], ![0, 1]), (![1, 1], ![0, 0]), (![1, 1], ![1, 1])} := by
  decide

lemma chi5_eq_prod : chi5 Ω = ∏ v ∈ evenChars, thetaConstant (liftChar v.1) (liftChar v.2) Ω := by
  rw [evenChars_eq, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [liftChar_cons, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one]
  simp only [chi5, Pi.mul_apply]
  ring1

variable {A D S : Matrix (Fin 2) (Fin 2) (ZMod 2)} {v w : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)}

private lemma charMap_mem_evenChars (hDA : D * Aᵀ = 1) (hS : Sᵀ = S) (hv : v ∈ evenChars) :
    charMap A D S v ∈ evenChars :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (charMap_fst_dotProduct_snd hDA hS).trans
    (Finset.mem_filter.mp hv).2⟩

private lemma charMapInv_mem_evenChars (hDA : D * Aᵀ = 1) (hS : Sᵀ = S) (hw : w ∈ evenChars) :
    charMapInv A D S w ∈ evenChars :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (charMapInv_fst_dotProduct_snd hDA hS).trans
    (Finset.mem_filter.mp hw).2⟩

variable (p) in
private lemma thetaConstant_liftChar_smul (hp : p ∈ siegelParabolic (Fin 2) ℤ) :
    letI S : Matrix (Fin 2) (Fin 2) ℤ := p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ
    letI w : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) := charMap
      (p.1.toBlocks₁₁.map (Int.castRingHom (ZMod 2)))
        (p.1.toBlocks₂₂.map (Int.castRingHom (ZMod 2))) (S.map (Int.castRingHom (ZMod 2))) v
    thetaConstant (liftChar v.1) (liftChar v.2) (map (Int.castRingHom ℝ) p • Ω) =
      cexp (-(π * I * ((liftChar v.1 ⬝ᵥ S *ᵥ liftChar v.1 : ℤ) / 4 +
        (liftChar v.1 ⬝ᵥ S.diag : ℤ) / 2))) * ((-1) ^ (liftChar w.1 ⬝ᵥ fun i ↦
          ((p.1.toBlocks₂₂ᵀ *ᵥ (liftChar v.2 + S *ᵥ liftChar v.1 + S.diag)) i - liftChar w.2 i) /
            2) * thetaConstant (liftChar w.1) (liftChar w.2) Ω) := by
  rw [thetaConstant_smul_of_mem_siegelParabolic _ _ Ω hp]
  congr 1
  refine IgusaLevelTwo.thetaConstant_eq_neg_one_zpow_mul Ω (fun i ↦ ?_) fun i ↦ ?_
  · rw [congrFun (intCast_liftChar _) i, charMap, intCast_mulVec_apply _ (intCast_liftChar v.1),
      transpose_map]
  · rw [congrFun (intCast_liftChar _) i, charMap, intCast_mulVec_apply _ (u' := v.2 + _ + _),
      transpose_map]
    ext j
    simp [congrFun (intCast_liftChar v.2) j, intCast_mulVec_apply _ (intCast_liftChar v.1) j]

variable (p) in
/-- The constant `c` with `χ₅(pΩ) = c χ₅(Ω)` for `p = (A, B; 0, D)` in the Siegel parabolic
subgroup: the product over the ten even characteristics `m = (μ, ν)` of the phases
`e^{-πi(μᵀSμ/4 + μᵀ diag S/2)}`, `S = BAᵀ`, of the law of `θ_m` under `p`, and of the signs by which
`θ_{m'}`, `m' = (Aᵀμ, Dᵀ(ν + Sμ + diag S))`, changes when `m'` is reduced modulo 2. -/
private noncomputable def chi5Factor : ℂ :=
  letI S : Matrix (Fin 2) (Fin 2) ℤ := p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ
  letI w : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) → (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) :=
    charMap (p.1.toBlocks₁₁.map (Int.castRingHom (ZMod 2)))
      (p.1.toBlocks₂₂.map (Int.castRingHom (ZMod 2))) (S.map (Int.castRingHom (ZMod 2)))
  (∏ v ∈ evenChars, cexp (-(π * I * ((liftChar v.1 ⬝ᵥ S *ᵥ liftChar v.1 : ℤ) / 4 +
    (liftChar v.1 ⬝ᵥ S.diag : ℤ) / 2)))) * ∏ v ∈ evenChars, (-1 : ℂ) ^ (liftChar (w v).1 ⬝ᵥ
      fun i ↦ ((p.1.toBlocks₂₂ᵀ *ᵥ (liftChar v.2 + S *ᵥ liftChar v.1 + S.diag)) i -
        liftChar (w v).2 i) / 2)

private lemma chi5_smul_of_mem_siegelParabolic (hp : p ∈ siegelParabolic (Fin 2) ℤ) :
    chi5 (map (Int.castRingHom ℝ) p • Ω) = chi5Factor p * chi5 Ω := by
  have hS : (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ)ᵀ = p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ := by
    rw [transpose_mul, transpose_transpose, ← toBlocks₁₂_mul_transpose_toBlocks₁₁ hp]
  have hDA : p.1.toBlocks₂₂.map (Int.castRingHom (ZMod 2)) *
      (p.1.toBlocks₁₁.map (Int.castRingHom (ZMod 2)))ᵀ = 1 := by
    rw [← transpose_map, ← Matrix.map_mul, toBlocks₂₂_mul_transpose_toBlocks₁₁ hp,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hS' : ((p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ).map (Int.castRingHom (ZMod 2)))ᵀ =
      (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ).map (Int.castRingHom (ZMod 2)) := by
    rw [← transpose_map, hS]
  rw [chi5_eq_prod, chi5_eq_prod,
    Finset.prod_congr rfl fun v _ ↦ thetaConstant_liftChar_smul Ω p hp, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, chi5Factor, mul_assoc]
  congr 2
  exact Finset.prod_nbij' _ _ (fun v hv ↦ charMap_mem_evenChars hDA hS' hv)
    (fun w hw ↦ charMapInv_mem_evenChars hDA hS' hw) (fun v _ ↦ charMapInv_charMap v hDA)
      (fun w _ ↦ charMap_charMapInv w hDA) fun v _ ↦ rfl

private lemma slash_chi5_of_mem_siegelParabolic (hp : p ∈ siegelParabolic (Fin 2) ℤ) :
    slash (TauCeti.detPowerRep ℂ 2 5) (map (Int.castRingHom ℝ) p) chi5 =
      (chi5Factor p / (p.1.toBlocks₂₂.map (Int.castRingHom ℂ)).det ^ 5) • chi5 := by
  refine (slash_eq_smul_iff _ _ _ _).mpr fun τ ↦ ?_
  have hd : (p.1.toBlocks₂₂.map (Int.castRingHom ℂ)).det ≠ 0 := by
    rw [← denom_of_mem_siegelParabolic τ hp]
    exact (isUnit_det_denom _ τ).ne_zero
  rw [chi5_smul_of_mem_siegelParabolic τ hp, detPowerRep_denomGL, denom_of_mem_siegelParabolic τ hp,
    zpow_ofNat, smul_eq_mul]
  field_simp

lemma slash_inv_partialInversion_chi5 : slash (TauCeti.detPowerRep ℂ 2 5)
    (map (Int.castRingHom ℝ) partialInversion⁻¹) chi5 = -chi5 := by
  have h : slash (TauCeti.detPowerRep ℂ 2 5) (map (Int.castRingHom ℝ) partialInversion⁻¹)
      (slash (TauCeti.detPowerRep ℂ 2 5) (map (Int.castRingHom ℝ) partialInversion) chi5) =
        slash (TauCeti.detPowerRep ℂ 2 5) (map (Int.castRingHom ℝ) partialInversion⁻¹) (-chi5) :=
    congrArg _ slash_partialInversion_chi5
  rw [← slash_mul, ← map_mul, mul_inv_cancel, map_one, slash_one, ← neg_one_smul ℂ chi5,
    slash_smul, neg_one_smul] at h
  exact (neg_eq_iff_eq_neg.mpr h).symm

variable (γ) in
/-- **`Sp(4, ℤ)` sends `χ₅` to constant multiples of itself**: for every `γ ∈ Sp(4, ℤ)`,
`χ₅ ∣₅ γ = c χ₅` for a constant `c`. This holds for `J₁`, with `c = -1`, and for the Siegel
parabolic subgroup, which permutes the ten even characteristics modulo 2, and these generate
`Sp(4, ℤ)`. -/
lemma exists_slash_chi5_eq_smul :
    ∃ c : ℂ, slash (TauCeti.detPowerRep ℂ 2 5) (map (Int.castRingHom ℝ) γ) chi5 = c • chi5 := by
  have hγ : γ ∈ Subgroup.closure (insert partialInversion (siegelParabolic (Fin 2) ℤ)) := by
    rw [closure_insert_partialInversion_eq_top]
    exact Subgroup.mem_top γ
  induction hγ using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨-1, by rw [slash_partialInversion_chi5, neg_one_smul]⟩
    · exact ⟨_, slash_chi5_of_mem_siegelParabolic hx⟩
  | inv_mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨-1, by rw [slash_inv_partialInversion_chi5, neg_one_smul]⟩
    · exact ⟨_, slash_chi5_of_mem_siegelParabolic (inv_mem hx)⟩
  | one => exact ⟨1, by rw [map_one, slash_one, one_smul]⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨c, h⟩
    rcases hy with ⟨c', h'⟩
    exact ⟨c * c', by rw [map_mul, slash_mul, h, slash_smul, h', smul_smul, mul_comm]⟩

lemma thetaConstant_smul_of_mem_siegelParabolic_of_eq (hp : p ∈ siegelParabolic (Fin 2) ℤ)
    (hA : p.1.toBlocks₁₁.map (Int.castRingHom (ZMod 2)) = 1)
    (hT : p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ = 2 • T) (hN : p.1.toBlocks₂₂ᵀ = 1 + 2 • N)
    (μ ν : Fin 2 → ℤ) : thetaConstant μ ν (map (Int.castRingHom ℝ) p • Ω) =
      cexp (π * I * ((μ ⬝ᵥ (N *ᵥ ν + p.1.toBlocks₂₂ᵀ *ᵥ (T *ᵥ μ + T.diag)) : ℤ) -
        ((μ ⬝ᵥ (2 • T) *ᵥ μ : ℤ) / 4 + (μ ⬝ᵥ (2 • T).diag : ℤ) / 2))) * thetaConstant μ ν Ω := by
  have hb : p.1.toBlocks₂₂ᵀ *ᵥ (ν + (2 • T) *ᵥ μ + (2 • T).diag) =
      ν + 2 • (N *ᵥ ν + p.1.toBlocks₂₂ᵀ *ᵥ (T *ᵥ μ + T.diag)) := by
    conv_lhs => rw [smul_mulVec, diag_smul, add_assoc, ← smul_add, mulVec_add, mulVec_smul,
      hN, add_mulVec, one_mulVec, smul_mulVec, ← hN]
    rw [smul_add, add_assoc]
  have hc : ∀ i, ((p.1.toBlocks₁₁ᵀ *ᵥ μ) i : ZMod 2) = μ i :=
    IgusaLevelTwo.intCast_transpose_mulVec_apply μ hA
  have hd : ∀ i, ((ν + 2 • (N *ᵥ ν + p.1.toBlocks₂₂ᵀ *ᵥ (T *ᵥ μ + T.diag))) i : ZMod 2) = ν i :=
    fun i ↦ by
      have h2 : (2 : ZMod 2) = 0 := by decide
      simp [h2]
  have hw : (fun i ↦ ((ν + 2 • (N *ᵥ ν + p.1.toBlocks₂₂ᵀ *ᵥ (T *ᵥ μ + T.diag))) i - ν i) / 2) =
      N *ᵥ ν + p.1.toBlocks₂₂ᵀ *ᵥ (T *ᵥ μ + T.diag) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [nsmul_eq_mul, Nat.cast_ofNat]
    omega
  have he (n : ℤ) : (-1 : ℂ) ^ n = cexp (π * I * n) := by
    rw [mul_comm, Complex.exp_int_mul, exp_pi_mul_I]
  rw [thetaConstant_smul_of_mem_siegelParabolic μ ν Ω hp, hT, hb,
    IgusaLevelTwo.thetaConstant_eq_neg_one_zpow_mul Ω hc hd, hw, he, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring1

lemma chi5_smul_of_mem_siegelParabolic_of_eq (hp : p ∈ siegelParabolic (Fin 2) ℤ)
    (hA : p.1.toBlocks₁₁.map (Int.castRingHom (ZMod 2)) = 1)
    (hT : p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ = 2 • T) (hT' : T 1 0 = T 0 1)
    (hN : p.1.toBlocks₂₂ᵀ = 1 + 2 • N) :
    chi5 (map (Int.castRingHom ℝ) p • Ω) = cexp (π * I * (N 0 0 + N 1 1 : ℤ)) * chi5 Ω := by
  rw [chi5_eq_prod, chi5_eq_prod, Finset.prod_congr rfl fun v _ ↦
    thetaConstant_smul_of_mem_siegelParabolic_of_eq Ω hp hA hT hN _ _, Finset.prod_mul_distrib,
    ← Complex.exp_sum]
  congr 1
  refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨N 0 1 + N 1 0 +
    (![0, 1] ⬝ᵥ p.1.toBlocks₂₂ᵀ *ᵥ (T *ᵥ ![0, 1] + T.diag)) +
      (![1, 0] ⬝ᵥ p.1.toBlocks₂₂ᵀ *ᵥ (T *ᵥ ![1, 0] + T.diag)) +
        (![1, 1] ⬝ᵥ p.1.toBlocks₂₂ᵀ *ᵥ (T *ᵥ ![1, 1] + T.diag)) - 3 * T 0 0 - 3 * T 1 1 -
          T 0 1, ?_⟩
  rw [evenChars_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h2T (i j : Fin 2) : ((2 : Matrix (Fin 2) (Fin 2) ℤ) * T) i j = 2 * T i j := by
    rw [two_mul, Matrix.add_apply, two_mul]
  simp only [liftChar_cons, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one]
  simp [dotProduct, mulVec, hT', h2T]
  ring1

lemma cexp_pi_mul_I_eq_det_pow (hp : p ∈ siegelParabolic (Fin 2) ℤ)
    (hN : p.1.toBlocks₂₂ᵀ = 1 + 2 • N) :
    cexp (π * I * (N 0 0 + N 1 1 : ℤ)) = (p.1.toBlocks₂₂.det : ℂ) ^ 5 := by
  have hdet : p.1.toBlocks₂₂.det =
      1 + 2 * (N 0 0 + N 1 1) + 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0) := by
    rw [← det_transpose, hN, det_fin_two]
    simp only [Matrix.add_apply]
    simp
    ring1
  have he : cexp (π * I * (N 0 0 + N 1 1 : ℤ)) = (-1) ^ (N 0 0 + N 1 1) := by
    rw [mul_comm, Complex.exp_int_mul, exp_pi_mul_I]
  generalize N 0 0 * N 1 1 - N 0 1 * N 1 0 = P at hdet
  rw [he]
  rcases Int.isUnit_iff.mp (SymplecticGroup.isUnit_det_toBlocks₂₂ ⟨p, hp⟩ :
    IsUnit p.1.toBlocks₂₂.det) with h | h
  · have h2 : 2 * (N 0 0 + N 1 1) + 4 * P = 0 := by
      linarith
    rw [Even.neg_one_zpow ⟨-P, by omega⟩, h]
    norm_num
  · have h2 : 2 * (N 0 0 + N 1 1) + 4 * P = -2 := by
      linarith
    rw [Odd.neg_one_zpow ⟨-P - 1, by omega⟩, h]
    norm_num

/-- **`P(ℤ) ∩ Γ[2]` fixes `χ₅` in weight 5**: for `p = (A, B; 0, D)` in the Siegel parabolic
subgroup with `p ≡ 1 (mod 2)`, write `BAᵀ = 2T` and `Dᵀ = 1 + 2N`; then `p` fixes the ten even
characteristics modulo 2 and `χ₅(pΩ) = (-1)^{N₁₁ + N₂₂} χ₅(Ω) = det(D)⁵ χ₅(Ω)`. -/
lemma slash_chi5_of_mem_siegelParabolic_of_mem_Gamma_two (hp : p ∈ siegelParabolic (Fin 2) ℤ)
    (hp₂ : p ∈ SymplecticGroup.Gamma (Fin 2) 2) :
    slash (TauCeti.detPowerRep ℂ 2 5) (map (Int.castRingHom ℝ) p) chi5 = chi5 := by
  have hS : (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ).map (Int.castRingHom (ZMod 2)) = 0 :=
    IgusaLevelTwo.map_mul_transpose_eq_zero_of_mem_Gamma_two hp₂
  have hT : p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ =
      2 • of fun i j ↦ (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ) i j / 2 := by
    ext i j
    have h : (2 : ℤ) ∣ (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ) i j :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by simpa using congrFun (congrFun hS i) j)
    rw [Matrix.smul_apply, of_apply, nsmul_eq_mul, Nat.cast_ofNat]
    omega
  have hD' : (p.1.toBlocks₂₂ᵀ - 1).map (Int.castRingHom (ZMod 2)) = 0 := by
    rw [Matrix.map_sub _ (map_sub (Int.castRingHom (ZMod 2))), transpose_map,
      IgusaLevelTwo.map_toBlocks₂₂_eq_one_of_mem_Gamma_two hp₂, transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _), sub_self]
  have hN : p.1.toBlocks₂₂ᵀ = 1 + 2 • of fun i j ↦ (p.1.toBlocks₂₂ᵀ - 1) i j / 2 := by
    ext i j
    have h : (2 : ℤ) ∣ (p.1.toBlocks₂₂ᵀ - 1) i j :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by simpa using congrFun (congrFun hD' i) j)
    rw [Matrix.sub_apply] at h
    rw [Matrix.add_apply, Matrix.smul_apply, of_apply, nsmul_eq_mul, Nat.cast_ofNat,
      Matrix.sub_apply]
    omega
  have hS10 :
      (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ) 1 0 = (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ) 0 1 := by
    rw [← transpose_apply (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ) 0 1, transpose_mul,
      transpose_transpose, ← toBlocks₁₂_mul_transpose_toBlocks₁₁ hp]
  conv_rhs => rw [← one_smul ℂ chi5]
  rw [slash_eq_smul_iff]
  intro τ
  rw [chi5_smul_of_mem_siegelParabolic_of_eq τ hp
    (IgusaLevelTwo.map_toBlocks₁₁_eq_one_of_mem_Gamma_two hp₂) hT (congrArg (· / 2) hS10) hN,
    cexp_pi_mul_I_eq_det_pow hp hN, one_smul, detPowerRep_denomGL,
    denom_of_mem_siegelParabolic τ hp, zpow_ofNat, Int.cast_det]
  rfl

/-- The subgroup of `Sp(4, ℤ)` **fixing `χ₅`** in weight 5: the `γ` with `χ₅ ∣₅ γ = χ₅`, that is
`χ₅(γΩ) = det(CΩ + D)⁵ χ₅(Ω)`: the stabiliser `slashCharStabilizer` of `χ₅` in `Sp(4, ℤ)` with the
trivial character. -/
noncomputable def chiFiveStabilizer : Subgroup (symplecticGroup (Fin 2) ℤ) :=
  slashCharStabilizer (TauCeti.detPowerRep ℂ 2 5) chi5 ⊤ 1

lemma mem_chiFiveStabilizer_iff : γ ∈ chiFiveStabilizer ↔ slash (TauCeti.detPowerRep ℂ 2 5)
    (map (Int.castRingHom ℝ) γ) chi5 = chi5 := by
  simp [chiFiveStabilizer, slashCharStabilizer]

instance : chiFiveStabilizer.Normal where
  conj_mem h hh γ := by
    rcases exists_slash_chi5_eq_smul γ with ⟨c, e⟩
    rw [mem_chiFiveStabilizer_iff, map_mul, map_mul, slash_mul, slash_mul, e, slash_smul,
      mem_chiFiveStabilizer_iff.mp hh, ← e, ← slash_mul, ← map_mul, mul_inv_cancel, map_one,
      slash_one]

lemma embedFirst_lowerUnipotent_mem_chiFiveStabilizer :
    embedFirst (lowerUnipotent 2) ∈ chiFiveStabilizer := by
  rw [mem_chiFiveStabilizer_iff]
  conv_rhs => rw [← one_smul ℂ chi5]
  refine (slash_eq_smul_iff _ _ _ _).mpr fun τ ↦ ?_
  rw [one_smul, detPowerRep_denomGL, zpow_ofNat]
  exact chi5_embedFirst_lowerUnipotent_smul τ 1

/-- **`Γ[2]` fixes `χ₅` in weight 5**: the stabiliser of `χ₅` is normal and contains
`ι₁(1, 0; 2, 1)` and `P(ℤ) ∩ Γ[2]`, which generate `Γ[2]` as a normal subgroup. -/
lemma Gamma_two_le_chiFiveStabilizer : SymplecticGroup.Gamma (Fin 2) 2 ≤ chiFiveStabilizer :=
  IgusaLevelTwo.Gamma_two_le_of_normal embedFirst_lowerUnipotent_mem_chiFiveStabilizer
    fun _ hq ↦ mem_chiFiveStabilizer_iff.mpr <| slash_chi5_of_mem_siegelParabolic_of_mem_Gamma_two
      (Subgroup.mem_inf.mp hq).1 (Subgroup.mem_inf.mp hq).2

/-- **`χ₅` is a Siegel modular form of weight 5 on `Γ[2]`** (LMFDB `mf.siegel.family.gamma_2`):
the field `chi5_mem` of `SiegelUpperHalfSpace.IgusaLevelTwo.IgusaLevelTwoStructure` holds. -/
lemma chi5_mem_scalarModularForms : chi5 ∈ scalarModularForms 5 IgusaLevelTwo.principal :=
  IgusaLevelTwo.mem_scalarModularForms_of_slash_eq isHolomorphic_chi5 fun _ hγ ↦
    mem_chiFiveStabilizer_iff.mp (Gamma_two_le_chiFiveStabilizer hγ)

end SiegelUpperHalfSpace.Ibukiyama
