import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.ExponentialSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Twists of exponential sums by Dirichlet characters modulo a prime

For a nontrivial Dirichlet character `ψ` modulo a prime `r`, the Gauss sum identity
`∑_u ψ⁻¹(u) e(n u / r) = ψ(n) τ(ψ⁻¹)`, valid for every `n`, expresses the twist
`∑ ψ(n) c n e(n z)` of an exponential sum `F` by the translates `F(z + u / r)`.

## Main definitions

* `ModularForm.twistSeq`: the twisted sequence `n ↦ ψ(n) c n`.

## Main results

* `ModularForm.expSum_slash_upperRightHom_one`: an exponential sum is `1`-periodic.
* `ModularForm.sum_smul_expSum_slash_upperRightHom`: the sum of the `ψ⁻¹(u) F(z + u / r)` is
  `τ(ψ⁻¹)` times the exponential sum of the twisted sequence.
-/

open Complex DirichletCharacter TauCeti

open scoped Real Manifold ModularForm

open UpperHalfPlane hiding I I_re I_im

open Matrix GeneralLinearGroup

namespace ModularForm

/-- The **twist** `n ↦ ψ(n) c n` of a sequence by a Dirichlet character `ψ`. -/
noncomputable def twistSeq {r : ℕ} (ψ : DirichletCharacter ℂ r) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ψ n * c n

variable {c : ℕ → ℂ} {k : ℤ} {r : ℕ} {ψ : DirichletCharacter ℂ r}

variable (ψ) in
lemma HasPolyGrowth.twistSeq (hc : HasPolyGrowth c) : HasPolyGrowth (twistSeq ψ c) := by
  rcases hc with ⟨C, m, hC⟩
  refine ⟨C, m, fun n hn ↦ ?_⟩
  rw [ModularForm.twistSeq, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one _)).trans (hC n hn)

variable [Fact r.Prime]

variable (ψ) in
lemma twistSeq_zero : twistSeq ψ c 0 = 0 := by
  simp [twistSeq, MulChar.map_zero]

lemma expSum_vadd (x : ℝ) (z : ℍ) :
    expSum c (x +ᵥ z) = ∑' n : ℕ, c n * cexp (2 * π * I * n * x) * cexp (2 * π * I * n * z) := by
  rw [expSum]
  refine tsum_congr fun n ↦ ?_
  rw [mul_assoc (c n), ← Complex.exp_add, UpperHalfPlane.coe_vadd]
  congr 2
  ring1

/-- **An exponential sum is `1`-periodic.** -/
lemma expSum_slash_upperRightHom_one : expSum c ∣[k] upperRightHom (1 : ℝ) = expSum c := by
  ext z
  rw [ModularForm.slash_upperRightHom_apply, expSum_vadd, expSum]
  refine tsum_congr fun n ↦ ?_
  have h : cexp (2 * π * I * n * ((1 : ℝ) : ℂ)) = 1 := by
    have h1 : (2 * π * I * n * ((1 : ℝ) : ℂ) : ℂ) = n * (2 * π * I) := by
      push_cast
      ring1
    rw [h1, Complex.exp_nat_mul_two_pi_mul_I]
  rw [h, mul_one]

private lemma cexp_eq_stdAddChar (n : ℕ) (u : ZMod r) :
    cexp (2 * π * I * n * (((u.val : ℝ) / r : ℝ) : ℂ)) = ZMod.stdAddChar ((n : ZMod r) * u) := by
  have h1 : ((n : ZMod r) * u) = ((n * u.val : ℕ) : ℤ) := by
    simp
  rw [h1, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring1

private lemma isPrimitive_of_ne_one (hψ : ψ ≠ 1) : ψ.IsPrimitive :=
  ((Fact.out : r.Prime).eq_one_or_self_of_dvd _ ψ.conductor_dvd_level).resolve_left fun h ↦
    hψ (ψ.eq_one_iff_conductor_eq_one.mpr h)

private lemma sum_inv_mul_stdAddChar (hψ : ψ ≠ 1) (n : ℕ) : ∑ u : ZMod r, ψ⁻¹ u *
    ZMod.stdAddChar ((n : ZMod r) * u) = ψ n * gaussSum ψ⁻¹ ZMod.stdAddChar := by
  have h1 : ∑ u : ZMod r, ψ⁻¹ u * ZMod.stdAddChar ((n : ZMod r) * u) =
      gaussSum ψ⁻¹ ((ZMod.stdAddChar (N := r)).mulShift n) := by
    simp [gaussSum]
  rw [h1, gaussSum_mulShift_of_isPrimitive _ (isPrimitive_of_ne_one (inv_ne_one.mpr hψ)), inv_inv]

lemma gaussSum_mul_gaussSum_inv (hψ : ψ ≠ 1) :
    gaussSum ψ ZMod.stdAddChar * gaussSum ψ⁻¹ ZMod.stdAddChar = ψ (-1) * r := by
  simpa using gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive
    (isPrimitive_of_ne_one hψ) (ZMod.isPrimitive_stdAddChar r)

/-- **The twist of an exponential sum by a nontrivial character modulo a prime**: the sum of
`ψ⁻¹(u) F(z + u / r)` over the residues `u` modulo `r` is `τ(ψ⁻¹)` times the exponential sum of the
twist `n ↦ ψ(n) c n`. -/
lemma sum_smul_expSum_slash_upperRightHom (hc : HasPolyGrowth c) (hψ : ψ ≠ 1) : ∑ u : ZMod r,
    ψ⁻¹ u • expSum c ∣[k] upperRightHom ((u.val : ℝ) / r) =
      gaussSum ψ⁻¹ ZMod.stdAddChar • expSum (twistSeq ψ c) := by
  ext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ModularForm.slash_upperRightHom_apply]
  have hsum : ∀ u : ZMod r, Summable fun n : ℕ ↦ ψ⁻¹ u *
      (c n * cexp (2 * π * I * n * (((u.val : ℝ) / r : ℝ) : ℂ)) * cexp (2 * π * I * n * z)) :=
    fun u ↦ by
      refine ((hc.summable_mul_cexp (((u.val : ℝ) / r) +ᵥ z).im_pos).mul_left (ψ⁻¹ u)).congr
        fun n ↦ ?_
      rw [mul_assoc (c n), ← Complex.exp_add, UpperHalfPlane.coe_vadd]
      congr 3
      push_cast
      ring1
  simp only [expSum_vadd, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun u _ ↦ hsum u, expSum, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  have h3 : ∑ u : ZMod r, ψ⁻¹ u * (c n * ZMod.stdAddChar ((n : ZMod r) * u) *
      cexp (2 * π * I * n * z)) = c n * cexp (2 * π * I * n * z) *
        ∑ u : ZMod r, ψ⁻¹ u * ZMod.stdAddChar ((n : ZMod r) * u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ ↦ by ring1
  simp only [cexp_eq_stdAddChar, twistSeq]
  rw [h3, sum_inv_mul_stdAddChar hψ n]
  ring1

end ModularForm
