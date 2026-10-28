import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ModularForm
import LeanBridge.ForMathlib.RepresentationTheory.HighestWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The slash operator of `GSp(2g, ℚ)⁺` on Siegel modular forms

The group `GSp(2g, ℚ)⁺` of rational symplectic similitudes with positive multiplier: the matrices
`α` with `αᵀ J α = r(α) J` for some rational `r(α) > 0`. Such an `α` is `√r(α)` times a real
symplectic matrix `α₁`, and acts on the Siegel upper half-space through `α₁`; its automorphy factor
`cτ + d` is `√r(α)` times that of `α₁`. The slash operator of weight `ρ`, for an irreducible
representation `ρ` of `GL(g, ℂ)` of highest weight `λ₁ ≥ ⋯ ≥ λ_g`, is
`(f ∣_ρ α)(τ) = r(α) ^ (λ₁ + ⋯ + λ_g - g(g + 1) / 2) ρ(cτ + d)⁻¹ f(ατ)`. Mathlib's
`Matrix.symplecticGroup` uses `J = (0, -1; 1, 0)`, the negative of the LMFDB's `J`, which gives the
same similitudes and multipliers.

## Main definitions

* `SiegelUpperHalfSpace.gspPlus`: the monoid `GSp(2g, ℚ)⁺`, and
  `SiegelUpperHalfSpace.multiplier` its multiplier `r`.
* `SiegelUpperHalfSpace.integralGSpPlus`: the semigroup `S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)` of the Hecke
  algebra (LMFDB `mf.siegel.hecke_operator`).
* `SiegelUpperHalfSpace.toSp`: the real symplectic matrix `r(α)^(-1/2) α`.
* `SiegelUpperHalfSpace.gspSmul`: the action `τ ↦ (aτ + b)(cτ + d)⁻¹` of `GSp(2g, ℚ)⁺`.
* `SiegelUpperHalfSpace.gspDenom`: the automorphy factor `cτ + d`.
* `SiegelUpperHalfSpace.gspSlash` (LMFDB `mf.siegel.slash.op`): the slash operator.

## Main results

* `SiegelUpperHalfSpace.gspSmul_val`: `α` acts by `τ ↦ (aτ + b)(cτ + d)⁻¹`.
* `SiegelUpperHalfSpace.gspSlash_ofSp`: on `Sp(2g, ℚ)` the slash operator is the one of
  `SiegelUpperHalfSpace.slash`.
-/

open Matrix Complex

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l]

variable (l) in
/-- The monoid `GSp(2g, ℚ)⁺` (LMFDB `mf.siegel.slash.op`, `mf.siegel.hecke_operator`) of rational
`2g × 2g` matrices `α` with `αᵀ J α = r J` for some rational `r > 0`. Its elements are invertible,
so it is the group of the LMFDB. -/
def gspPlus : Submonoid (Matrix (l ⊕ l) (l ⊕ l) ℚ) where
  carrier := {α | ∃ r : ℚ, 0 < r ∧ αᵀ * J l ℚ * α = r • J l ℚ}
  mul_mem' {α β} := by
    rintro ⟨r, hr, hα⟩ ⟨s, hs, hβ⟩
    refine ⟨r * s, mul_pos hr hs, ?_⟩
    have h : (α * β)ᵀ * J l ℚ * (α * β) = βᵀ * (αᵀ * J l ℚ * α) * β := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [h, hα, Matrix.mul_smul, Matrix.smul_mul, hβ, smul_smul]
  one_mem' := ⟨1, one_pos, by simp⟩

variable (l) in
/-- The semigroup `S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)` (LMFDB `mf.siegel.hecke_operator`) of integral
symplectic similitudes with positive multiplier, from whose double cosets the Hecke algebra of
`Sp(2g, ℤ)` is built. -/
def integralGSpPlus : Submonoid (Matrix (l ⊕ l) (l ⊕ l) ℚ) :=
  gspPlus l ⊓ (Int.castRingHom ℚ).mapMatrix.range.toSubmonoid

/-- The element `diag(1_g, p 1_g)` of `S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)`, of multiplier `p`, whose
double coset is the Hecke operator `T(p)` (LMFDB `mf.siegel.hecke_operator`). -/
def heckeDiag (p : ℕ) (hp : 0 < p) : integralGSpPlus l :=
  ⟨fromBlocks 1 0 0 ((p : ℚ) • 1), ⟨p, by exact_mod_cast hp, by
    simp [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]⟩,
    fromBlocks 1 0 0 ((p : ℤ) • 1), by simp [fromBlocks_map, smul_one_eq_diagonal]⟩

variable (α : gspPlus l) (τ : SiegelUpperHalfSpace l)

/-- The **multiplier** `r(α) > 0` of `α ∈ GSp(2g, ℚ)⁺`, with `αᵀ J α = r(α) J`. It is unique
when `g ≥ 1`; for `g = 0` it is a choice, which does not matter, the matrices being empty. -/
noncomputable def multiplier : ℚ :=
  α.2.choose

lemma multiplier_pos : 0 < multiplier α :=
  α.2.choose_spec.1

lemma transpose_mul_J_mul : (α : Matrix (l ⊕ l) (l ⊕ l) ℚ)ᵀ * J l ℚ * α = multiplier α • J l ℚ :=
  α.2.choose_spec.2

lemma multiplier_eq [Nonempty l] {r : ℚ}
    (h : (α : Matrix (l ⊕ l) (l ⊕ l) ℚ)ᵀ * J l ℚ * α = r • J l ℚ) : multiplier α = r := by
  rcases ‹Nonempty l› with ⟨i⟩
  have h' : multiplier α • J l ℚ = r • J l ℚ := (transpose_mul_J_mul α).symm.trans h
  simpa [J] using congrFun (congrFun h' (Sum.inr i)) (Sum.inl i)

private lemma map_transpose_mul_J_mul : ((α : Matrix (l ⊕ l) (l ⊕ l) ℚ).map (algebraMap ℚ ℝ))ᵀ *
    J l ℝ * (α : Matrix (l ⊕ l) (l ⊕ l) ℚ).map (algebraMap ℚ ℝ) = (multiplier α : ℝ) • J l ℝ := by
  rw [← map_J l (algebraMap ℚ ℝ), ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
    transpose_mul_J_mul]
  ext i j
  simp only [map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, eq_ratCast]

/-- The real symplectic matrix `r(α)^(-1/2) α` of `α ∈ GSp(2g, ℚ)⁺`. -/
noncomputable def toSp : symplecticGroup l ℝ :=
  ⟨(√(multiplier α : ℝ))⁻¹ • (α : Matrix (l ⊕ l) (l ⊕ l) ℚ).map (algebraMap ℚ ℝ), by
    rw [SymplecticGroup.mem_iff', transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, map_transpose_mul_J_mul, smul_smul, ← mul_inv,
      Real.mul_self_sqrt (Rat.cast_nonneg.mpr (multiplier_pos α).le),
      inv_mul_cancel₀ (Rat.cast_ne_zero.mpr (multiplier_pos α).ne'), one_smul]⟩

/-- The action `τ ↦ ατ = (aτ + b)(cτ + d)⁻¹` of `α ∈ GSp(2g, ℚ)⁺` on the Siegel upper half-space,
through the real symplectic matrix `r(α)^(-1/2) α`, which acts in the same way. -/
noncomputable def gspSmul : SiegelUpperHalfSpace l :=
  toSp α • τ

/-- The numerator `aτ + b` of the action of `α = (a, b; c, d) ∈ GSp(2g, ℚ)⁺`. -/
noncomputable def gspNum : Matrix l l ℂ :=
  (α : Matrix (l ⊕ l) (l ⊕ l) ℚ).toBlocks₁₁.map (↑) * τ.val +
    (α : Matrix (l ⊕ l) (l ⊕ l) ℚ).toBlocks₁₂.map (↑)

/-- The automorphy factor `cτ + d` of `α = (a, b; c, d) ∈ GSp(2g, ℚ)⁺`. -/
noncomputable def gspDenom : Matrix l l ℂ :=
  (α : Matrix (l ⊕ l) (l ⊕ l) ℚ).toBlocks₂₁.map (↑) * τ.val +
    (α : Matrix (l ⊕ l) (l ⊕ l) ℚ).toBlocks₂₂.map (↑)

private lemma sqrt_multiplier_ne_zero : (√(multiplier α : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.mpr <| Rat.cast_pos.mpr <| multiplier_pos α

lemma gspNum_eq : gspNum α τ = (√(multiplier α : ℝ) : ℂ) • num (toSp α) τ.val := by
  ext i j
  simp [gspNum, num, toSp, Matrix.mul_apply, toBlocks₁₁, toBlocks₁₂, mul_add, Finset.mul_sum,
    ← mul_assoc, sqrt_multiplier_ne_zero α]

lemma gspDenom_eq : gspDenom α τ = (√(multiplier α : ℝ) : ℂ) • denom (toSp α) τ.val := by
  ext i j
  simp [gspDenom, denom, toSp, Matrix.mul_apply, toBlocks₂₁, toBlocks₂₂, mul_add,
    Finset.mul_sum, ← mul_assoc, sqrt_multiplier_ne_zero α]

lemma isUnit_gspDenom : IsUnit (gspDenom α τ) := by
  rw [gspDenom_eq, isUnit_iff_isUnit_det, det_smul]
  exact ((sqrt_multiplier_ne_zero α).isUnit.pow _).mul <| isUnit_det_denom _ τ

/-- **`α ∈ GSp(2g, ℚ)⁺` acts by `τ ↦ (aτ + b)(cτ + d)⁻¹`.** -/
lemma gspSmul_val : (gspSmul α τ).val = gspNum α τ * (gspDenom α τ)⁻¹ := by
  have h : (√(multiplier α : ℝ) : ℂ) ≠ 0 := sqrt_multiplier_ne_zero α
  have hinv : ((√(multiplier α : ℝ) : ℂ) • denom (toSp α) τ.val)⁻¹ =
      (√(multiplier α : ℝ) : ℂ)⁻¹ • (denom (toSp α) τ.val)⁻¹ :=
    inv_eq_left_inv <| by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h,
      one_smul, nonsing_inv_mul _ (isUnit_det_denom _ τ)]
  rw [gspSmul, val_smul, gspNum_eq, gspDenom_eq, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ h, one_smul]

/-- The automorphy factor `cτ + d` of `α ∈ GSp(2g, ℚ)⁺` at `τ`, as an element of `GL(g, ℂ)`. -/
noncomputable def gspDenomGL : GL l ℂ :=
  (isUnit_gspDenom α τ).unit

@[simp]
lemma coe_gspDenomGL : (gspDenomGL α τ : Matrix l l ℂ) = gspDenom α τ :=
  rfl

/-- The element `γ` of `GSp(2g, ℚ)⁺` given by `γ ∈ Sp(2g, ℚ)`, of multiplier `1`. -/
def ofSp (γ : symplecticGroup l ℚ) : gspPlus l :=
  ⟨γ, 1, one_pos, by rw [one_smul, ← SymplecticGroup.mem_iff']; exact γ.2⟩

lemma multiplier_ofSp [Nonempty l] (γ : symplecticGroup l ℚ) : multiplier (ofSp γ) = 1 :=
  multiplier_eq _ <| by
    rw [one_smul, ← SymplecticGroup.mem_iff']
    exact γ.2

lemma toSp_ofSp [Nonempty l] (γ : symplecticGroup l ℚ) :
    toSp (ofSp γ) = SymplecticGroup.map (algebraMap ℚ ℝ) γ := by
  ext : 1
  simp [toSp, multiplier_ofSp]
  rfl

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℂ) V) (β : gspPlus (Fin n))
    (f : SiegelUpperHalfSpace (Fin n) → V)

/-- The exponent `λ₁ + ⋯ + λ_g - g(g + 1) / 2` of the multiplier in the slash operator of weight
`ρ`, where `λ` is the highest weight of `ρ`. -/
noncomputable def slashExponent : ℤ :=
  ∑ i, ρ.highestWeight i - (n * (n + 1) / 2 : ℕ)

/-- The **slash operator** (LMFDB `mf.siegel.slash.op`) of weight `ρ` by
`α = (a, b; c, d) ∈ GSp(2g, ℚ)⁺` on functions `f : ℋ_g → V`:
`(f ∣_ρ α)(τ) = r(α) ^ (λ₁ + ⋯ + λ_g - g(g + 1) / 2) ρ(cτ + d)⁻¹ f((aτ + b)(cτ + d)⁻¹)`, where
`λ` is the highest weight of `ρ` (`Representation.highestWeight`). The LMFDB takes `ρ`
irreducible and finite-dimensional, which is not imposed here; for such `ρ`, the highest weight is
the usual one. -/
noncomputable def gspSlash : SiegelUpperHalfSpace (Fin n) → V :=
  fun τ ↦ ((multiplier β : ℂ) ^ slashExponent ρ) • ρ (gspDenomGL β τ)⁻¹ (f (gspSmul β τ))

/-- **On `Sp(2g, ℚ)` the slash operator is the one of `SiegelUpperHalfSpace.slash`**, whose
invariants are the Siegel modular forms. -/
lemma gspSlash_ofSp [NeZero n] (γ : symplecticGroup (Fin n) ℚ) :
    gspSlash ρ (ofSp γ) f = slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ) f := by
  have h : gspDenomGL (ofSp γ) = denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) γ) := by
    funext τ
    ext : 1
    rw [coe_gspDenomGL, coe_denomGL, gspDenom_eq, multiplier_ofSp, toSp_ofSp]
    simp
  ext τ
  simp [gspSlash, slash_apply, multiplier_ofSp, gspSmul, toSp_ofSp, h]

end SiegelUpperHalfSpace
