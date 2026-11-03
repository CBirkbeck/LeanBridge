import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Trace
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The characteristic polynomial of a modular form over level one

A modular form `f` of level `𝒢`, a group of finite index in `SL₂(ℤ)`, is a root of the monic
polynomial `∏_γ (X - f ∣ γ)`, for `γ` running over representatives of `𝒢 \ SL₂(ℤ)`. Its coefficients
are, up to sign, the elementary symmetric functions of the translates of `f`, which are modular
forms of level one by Newton's identities, since the power sums of the translates are the traces of
the powers of `f`. If `f` is a cusp form, the coefficients other than the leading one are cusp
forms.

## Main definitions

* `TauCeti.GaloisAction.esymmForm`: the `n`-th elementary symmetric function of the translates of a
  modular form down to level one.

## Main results

* `TauCeti.GaloisAction.isCuspForm_esymmForm`: it is a cusp form if `f` is one and `n ≠ 0`.
* `TauCeti.GaloisAction.sum_esymmForm_mul_pow_eq_zero`: every translate of `f` is a root of the
  characteristic polynomial.
-/

open UpperHalfPlane SlashInvariantForm

open scoped MatrixGroups

namespace TauCeti.GaloisAction

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ] {k : ℤ} (f : ModularForm 𝒢 k)

local notation "𝒬" => 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ

/-- The `n`-th elementary symmetric function of the translates of a modular form of level `𝒢` down
to level one, a modular form of level one and weight `n * k`. -/
noncomputable def esymmForm (n : ℕ) : ℍ → ℂ :=
  fun z ↦ letI : Fintype 𝒬 := Fintype.ofFinite _
    (Finset.univ.val.map fun q : 𝒬 ↦ quotientFunc f q z).esymm n

lemma esymmForm_zero : esymmForm f 0 = 1 :=
  funext fun z ↦ by simp [esymmForm]

/-- **Every translate of `f` is a root of its characteristic polynomial over level one.** -/
lemma sum_esymmForm_mul_pow_eq_zero (q : 𝒬) (z : ℍ) : ∑ j ∈ Finset.range (Nat.card 𝒬 + 1),
    (-1) ^ j * (esymmForm f j z * quotientFunc f q z ^ (Nat.card 𝒬 - j)) = 0 := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  let s : Multiset ℂ := Finset.univ.val.map fun q : 𝒬 ↦ quotientFunc f q z
  have hcard : Multiset.card s = Nat.card 𝒬 := by
    simp [s]
  have h : ((s.map fun t ↦ Polynomial.X - Polynomial.C t).prod).eval (quotientFunc f q z) =
      (∑ j ∈ Finset.range (Multiset.card s + 1), (-1) ^ j *
        (Polynomial.C (s.esymm j) * Polynomial.X ^ (Multiset.card s - j))).eval
          (quotientFunc f q z) := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm]
  rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero, hcard] at h
  · simpa [Polynomial.eval_finsetSum, esymmForm] using h.symm
  · exact Multiset.mem_map.mpr ⟨_, Multiset.mem_map.mpr
      ⟨_, Multiset.mem_map.mpr ⟨q, Finset.mem_univ_val q, rfl⟩, rfl⟩, by simp⟩

lemma sum_esymmForm_smul_mul_pow_eq_zero : ∑ j ∈ Finset.range (Nat.card 𝒬 + 1),
    ((-1) ^ j : ℂ) • (esymmForm f j * ⇑f ^ (Nat.card 𝒬 - j)) = 0 := by
  ext τ
  have h : ∑ j ∈ Finset.range (Nat.card 𝒬 + 1), (-1) ^ j *
      (esymmForm f j τ * quotientFunc f (cosetOf 𝒢 1) τ ^ (Nat.card 𝒬 - j)) = 0 :=
    sum_esymmForm_mul_pow_eq_zero f (cosetOf 𝒢 1) τ
  rw [quotientFunc_cosetOf] at h
  simpa using h

variable [𝒢.HasDetOne]

lemma cast_mul_esymmForm_apply (n : ℕ) (z : ℍ) : (n : ℂ) * esymmForm f n z =
    (-1) ^ (n + 1) * ∑ a ∈ Finset.antidiagonal n with a.1 < n,
      (-1) ^ a.1 * esymmForm f a.1 z * ModularForm.trace 𝒮ℒ (f.pow a.2) z := by
  classical
  let : Fintype 𝒬 := Fintype.ofFinite _
  have h : MvPolynomial.aeval (fun q : 𝒬 ↦ quotientFunc f q z)
      ((n : MvPolynomial 𝒬 ℂ) * MvPolynomial.esymm 𝒬 ℂ n) =
        MvPolynomial.aeval (fun q : 𝒬 ↦ quotientFunc f q z) ((-1) ^ (n + 1) *
          ∑ a ∈ Finset.antidiagonal n with a.1 < n, (-1) ^ a.1 * MvPolynomial.esymm 𝒬 ℂ a.1 *
            MvPolynomial.psum 𝒬 ℂ a.2) := by
    rw [MvPolynomial.mul_esymm_eq_sum]
  have he (m : ℕ) : MvPolynomial.eval (fun q : 𝒬 ↦ quotientFunc f q z)
      (MvPolynomial.esymm 𝒬 ℂ m) = esymmForm f m z :=
    MvPolynomial.aeval_esymm_eq_multiset_esymm 𝒬 ℂ m _
  simpa [MvPolynomial.psum, quotientFunc_pow, he] using h

lemma esymmForm_eq {n : ℕ} (hn : n ≠ 0) : esymmForm f n = (n : ℂ)⁻¹ • ((-1) ^ (n + 1) : ℂ) •
    ∑ a ∈ Finset.antidiagonal n with a.1 < n,
      ((-1) ^ a.1 : ℂ) • (esymmForm f a.1 * ModularForm.trace 𝒮ℒ (f.pow a.2)) := by
  ext z
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.mul_apply]
  rw [eq_inv_mul_iff_mul_eq₀ (Nat.cast_ne_zero.mpr hn), cast_mul_esymmForm_apply f n z]
  simp only [mul_assoc]

lemma isForm_esymmForm (n : ℕ) : IsForm 𝒮ℒ (n * k) (esymmForm f n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [esymmForm_zero] using isForm_one
    · rw [esymmForm_eq f hn]
      refine ((IsForm.sum fun a ha ↦ ?_).smul _).smul _
      rcases Finset.mem_filter.mp ha with ⟨ha₁, ha₂⟩
      refine (((ih a.1 ha₂).mul (isForm_coe (ModularForm.trace 𝒮ℒ (f.pow a.2)))).cast ?_).smul _
      rw [← Finset.mem_antidiagonal.mp ha₁]
      push_cast
      ring1

lemma isCuspForm_trace_pow (hf : IsCuspForm 𝒢 k f) {n : ℕ} (hn : n ≠ 0) :
    IsCuspForm 𝒮ℒ (n * k) (ModularForm.trace 𝒮ℒ (f.pow n)) := by
  rcases hf.pow hn with ⟨g, hg⟩
  refine ⟨CuspForm.trace 𝒮ℒ g, funext fun z ↦ ?_⟩
  let : Fintype 𝒬 := Fintype.ofFinite _
  rw [CuspForm.coe_trace, Finset.sum_apply, trace_apply_eq_sum (f.pow n) z]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rcases exists_cosetOf_eq q with ⟨δ, rfl⟩
  rw [quotientFunc_cosetOf, quotientFunc_cosetOf, hg, ModularForm.coe_pow]

/-- **If `f` is a cusp form, the elementary symmetric functions of its translates down to level one
are cusp forms in degree `n ≠ 0`.** -/
lemma isCuspForm_esymmForm (hf : IsCuspForm 𝒢 k f) {n : ℕ} (hn : n ≠ 0) :
    IsCuspForm 𝒮ℒ (n * k) (esymmForm f n) := by
  rw [esymmForm_eq f hn]
  refine ((IsCuspForm.sum fun a ha ↦ ?_).smul _).smul _
  rcases Finset.mem_filter.mp ha with ⟨ha₁, ha₂⟩
  have ha₃ : a.1 + a.2 = n := Finset.mem_antidiagonal.mp ha₁
  rw [mul_comm (esymmForm f a.1)]
  refine (((isCuspForm_trace_pow f hf (n := a.2) (by omega)).mul_isForm
    (isForm_esymmForm f a.1)).cast ?_).smul _
  rw [← ha₃]
  push_cast
  ring1

end TauCeti.GaloisAction
