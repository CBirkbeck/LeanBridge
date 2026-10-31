import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.NumberTheory.ModularForms.LFunction.EulerProduct
import TauCeti.NumberTheory.ModularForms.LFunction.Sign
import TauCeti.NumberTheory.ModularForms.Newforms.Fricke

/-!
# The functional equation of the L-function of a newform

Let `f ∈ S_k^new(N, χ)` be a newform with `q`-expansion `f(z) = ∑ aₙ n^((k-1)/2) qⁿ`. Its
L-function in the analytic normalisation is `L(s, f) = ∑ aₙ n^(-s)`, and its completed L-function
`Λ(s, f) = N^(s/2) Γ_ℂ(s + (k-1)/2) L(s, f)` satisfies the functional equation
`Λ(s, f) = ε Λ̄(1 - s, f)`, where `Λ̄(s, f) = conj (Λ(conj s, f))` is the completed L-function of
the dual form `f_ρ`, the newform with the complex-conjugate coefficients, and `ε` is the sign of
the functional equation (LMFDB `cmf.lfunction`). Here `ε = i^k λ_N(f)`, where `λ_N(f)` is the
pseudo-eigenvalue of the Fricke involution, `𝒲_N f = λ_N(f) f_ρ` (Tau Ceti's
`HeckeRing.GL2.Newform.frickePseudoEigenvalue`).

The functional equation follows from Hecke's two-form equation
`Λ_N(k - s, f) = i^k Λ_N(s, 𝒲_N f)` of Tau Ceti
(`CuspForm.frickeCompletedL_functional_equation_gamma1`) in the classical normalisation, the
pseudo-eigenvalue equation, and the fact that the completed L-function of `f_ρ` is the reflection
of that of `f`: on the imaginary axis `f_ρ(it) = conj (f(it))`, so the Mellin transforms are
conjugate. The Euler product is Tau Ceti's `HeckeRing.GL2.Newform.L_eulerProduct_tprod`, in the
classical normalisation, rewritten here in the analytic one.

The LMFDB says that the sign is `±1` for trivial character, proved here, and that "in general it
is a root of unity". The latter is not true: what holds is `|ε| = 1`, proved here. For a newform
`f` of level `1` and a primitive character `ψ` modulo a prime `p`, the twist `f ⊗ ψ` is a newform
of level `p²` whose sign is a root of unity times `τ(ψ)² / p` (Atkin–Li), and for the cubic
characters `ψ` modulo `7`, `τ(ψ)² / 7` is not a root of unity: its cube is `J(ψ, ψ)² / 7`, which
is not an algebraic integer, as the Jacobi sum `J(ψ, ψ)` generates one of the two distinct primes
of `ℤ[ζ₃]` above `7`.

## Main definitions

* `HeckeRing.GL2.Newform.analyticCoeff`: the normalised coefficients `aₙ`.
* `HeckeRing.GL2.Newform.analyticL`: the L-function `L(s, f)` in the analytic normalisation.
* `HeckeRing.GL2.Newform.analyticCompletedL`: the completed L-function `Λ(s, f)` in the analytic
  normalisation, an entire function.
* `HeckeRing.GL2.Newform.rootNumber`: the sign `ε` of the functional equation.

## Main results

* `CuspForm.frickeCompletedL_conj`: the completed L-function of the conjugate form `f_ρ` is the
  reflection of that of `f`.
* `HeckeRing.GL2.Newform.hasSum_analyticL`: `L(s, f) = ∑ aₙ n^(-s)` for `Re s > 3/2`.
* `HeckeRing.GL2.Newform.analyticL_eulerProduct`: the Euler product of `L(s, f)`.
* `HeckeRing.GL2.Newform.analyticCompletedL_eq_cpow_mul_Gammaℂ_mul_analyticL`:
  `Λ(s, f) = N^(s/2) Γ_ℂ(s + (k-1)/2) L(s, f)` where `Γ_ℂ(s + (k-1)/2)` has no pole.
* `HeckeRing.GL2.Newform.differentiable_analyticCompletedL`: `Λ(s, f)` is entire.
* `HeckeRing.GL2.Newform.analyticCompletedL_eq_rootNumber_mul_conj`: the functional equation
  `Λ(s, f) = ε Λ(1 - s, f_ρ)`.
* `HeckeRing.GL2.Newform.analyticCompletedL_eq_rootNumber_mul`: the functional equation
  `Λ(s, f) = ε conj (Λ(1 - conj s, f))`.
* `HeckeRing.GL2.Newform.eq_rootNumber_of_forall_analyticCompletedL_eq`: `ε` is the only constant
  with this property.
* `HeckeRing.GL2.Newform.norm_rootNumber`: `|ε| = 1`.
* `HeckeRing.GL2.Newform.rootNumber_eq_one_or_neg_one`: `ε = ±1` for trivial character.
-/

open Matrix SpecialLinearGroup CongruenceSubgroup TauCeti Complex

namespace CuspForm

variable {N : ℕ} {k : ℤ}

/-- **The completed L-function of the conjugate form is the reflection of that of `f`**:
`Λ_M(s, f_ρ) = conj (Λ_M(conj s, f))`, since `f_ρ(it) = conj (f(it))` on the imaginary axis. -/
lemma frickeCompletedL_conj (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (M : ℕ+) (s : ℂ) :
    (f.conj (Gamma1_map_le_conjAct_inv_J N)).frickeCompletedL M s =
      starRingEnd ℂ (f.frickeCompletedL M (starRingEnd ℂ s)) := by
  simp only [frickeCompletedL_apply, mellin]
  rw [← integral_conj]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have hu : 0 < t / Real.sqrt M :=
    div_pos ht (Real.sqrt_pos.mpr (Nat.cast_pos.mpr M.pos))
  have harg : (t : ℂ).arg ≠ Real.pi :=
    (arg_ofReal_of_nonneg (le_of_lt ht)).trans_ne Real.pi_ne_zero.symm
  have hJ : UpperHalfPlane.J • (⟨I * (t / Real.sqrt M : ℝ), by simpa using hu⟩ : UpperHalfPlane) =
      ⟨I * (t / Real.sqrt M : ℝ), by simpa using hu⟩ :=
    UpperHalfPlane.ext <| by simp [UpperHalfPlane.coe_J_smul]
  rw [UpperHalfPlane.resToImagAxis_of_pos _ hu, UpperHalfPlane.resToImagAxis_of_pos _ hu,
    CuspForm.conj_apply, hJ, smul_eq_mul, smul_eq_mul, map_mul, ← map_one (starRingEnd ℂ),
    ← map_sub, ← conj_cpow _ _ harg, conj_ofReal, map_one]

end CuspForm

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)

/-- The **normalised coefficients** `aₙ = Aₙ / n^((k-1)/2)` (LMFDB `cmf.lfunction`) of a newform
`f` of weight `k` with `q`-expansion `f = ∑ Aₙ qⁿ`, so that `f(z) = ∑ aₙ n^((k-1)/2) qⁿ`. -/
noncomputable def analyticCoeff (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n / (n : ℂ) ^ (((k : ℂ) - 1) / 2)

/-- The **L-function** `L(s, f)` (LMFDB `cmf.lfunction`) of a newform `f` of positive weight `k`,
in the analytic normalisation: `L(s, f) = ∑ aₙ n^(-s)` for the normalised coefficients
`aₙ = Aₙ / n^((k-1)/2)` (`analyticCoeff`, `hasSum_analyticL`), continued to an entire function.
It is Mathlib's `ModularForm.L`, in the classical normalisation, at `s + (k-1)/2`. -/
noncomputable def analyticL (hk : 0 < k) (s : ℂ) : ℂ :=
  ModularForm.L hk f.toCuspForm (s + ((k : ℂ) - 1) / 2)

/-- The **completed L-function** `Λ(s, f) = N^(s/2) Γ_ℂ(s + (k-1)/2) L(s, f)` (LMFDB
`cmf.lfunction`) of a newform `f` of level `N` and weight `k`, in the analytic normalisation
(`analyticCompletedL_eq_cpow_mul_Gammaℂ_mul_analyticL`). It is defined through Tau Ceti's entire
completed L-function `Λ_N(s, f) = N^(s/2) (2π)^(-s) Γ(s) L(s, f)` of the classical
normalisation, as `Λ(s, f) = 2 N^(-(k-1)/4) Λ_N(s + (k-1)/2, f)`: this is the product formula
wherever `Γ_ℂ(s + (k-1)/2)` has no pole, and its entire continuation elsewhere, where the product
formula would take Mathlib's junk value of `Γ` at its poles. -/
noncomputable def analyticCompletedL (s : ℂ) : ℂ :=
  2 * ((N : ℝ) ^ (-((k : ℝ) - 1) / 4) : ℝ) *
    f.toCuspForm.frickeCompletedL (N.toPNat (NeZero.pos N)) (s + ((k : ℂ) - 1) / 2)

/-- The **sign** `ε` of the functional equation (LMFDB `lfunction.sign`) of the L-function of a
newform `f` of weight `k`: `ε = i^k λ_N(f)`, where `λ_N(f)` is the Fricke pseudo-eigenvalue,
`𝒲_N f = λ_N(f) f_ρ` (Tau Ceti's `HeckeRing.GL2.Newform.frickePseudoEigenvalue`). It is the only
constant with `Λ(s, f) = ε conj (Λ(1 - conj s, f))` (`analyticCompletedL_eq_rootNumber_mul`,
`eq_rootNumber_of_forall_analyticCompletedL_eq`). -/
noncomputable def rootNumber : ℂ :=
  I ^ k * f.frickePseudoEigenvalue

variable {s : ℂ}

private lemma half_add_one_lt_re_add (hs : 3 / 2 < s.re) :
    (k : ℝ) / 2 + 1 < (s + ((k : ℂ) - 1) / 2).re := by
  rw [add_re, div_ofNat_re, sub_re, intCast_re, one_re]
  linarith

/-- **The L-function is the Dirichlet series of the normalised coefficients**:
`L(s, f) = ∑ aₙ n^(-s)` with `aₙ = Aₙ / n^((k-1)/2)`, for `Re s > 3/2`. -/
lemma hasSum_analyticL (hk : 0 < k) (hs : 3 / 2 < s.re) :
    HasSum (fun n : ℕ ↦ f.analyticCoeff n / (n : ℂ) ^ s) (f.analyticL hk s) := by
  have hw : (k : ℝ) / 2 + 1 < (s + ((k : ℂ) - 1) / 2).re := half_add_one_lt_re_add hs
  have hs0 : s ≠ 0 := fun h ↦ by
    rw [h, zero_re] at hs
    linarith
  have hw0 : s + ((k : ℂ) - 1) / 2 ≠ 0 := fun h ↦ by
    rw [h, zero_re] at hw
    linarith [(Int.cast_pos.mpr hk : (0 : ℝ) < k)]
  have h : HasSum (fun n : ℕ ↦ (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n /
      (n : ℂ) ^ (s + ((k : ℂ) - 1) / 2)) (f.analyticL hk s) := by
    simpa [analyticL] using CuspForm.hasSum_L hk f.toCuspForm hw
  convert h using 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [analyticCoeff, Nat.cast_zero, zero_cpow hs0, zero_cpow hw0, div_zero, div_zero]
  · rw [analyticCoeff, div_div, ← cpow_add _ _ (Nat.cast_ne_zero.mpr hn), add_comm]

lemma analyticCompletedL_eq_cpow_mul_Λ (hk : 0 < k) : f.analyticCompletedL s =
    (N : ℂ) ^ (s / 2) * (2 * ModularForm.Λ hk f.toCuspForm (s + ((k : ℂ) - 1) / 2)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h : (N : ℂ) ^ (-((k : ℂ) - 1) / 4) * (N : ℂ) ^ ((s + ((k : ℂ) - 1) / 2) / 2) =
      (N : ℂ) ^ (s / 2) := by
    rw [← cpow_add _ _ hN]
    congr 1
    ring1
  rw [analyticCompletedL, f.toCuspForm.frickeCompletedL_eq_cpow_mul_Λ _ hk,
    ofReal_cpow (Nat.cast_nonneg N)]
  push_cast
  simp only [Nat.toPNat, PNat.mk_coe]
  rw [← h]
  ring1

/-- **The Euler product** (LMFDB `cmf.lfunction`), in the analytic normalisation: for `Re s > 3/2`,
`L(s, f) = ∏_p (1 - a_p p^(-s) + χ(p) p^(-2s))⁻¹` with `a_p = A_p / p^((k-1)/2)`, the character
being extended by zero at the primes dividing the level. -/
lemma analyticL_eulerProduct (hk : 0 < k) (hs : 3 / 2 < s.re) : ∏' p : Nat.Primes,
    (1 - f.analyticCoeff p.val * (p.val : ℂ) ^ (-s) +
      f.dirichletLift p.val * (p.val : ℂ) ^ (-2 * s))⁻¹ = f.analyticL hk s := by
  rw [analyticL, ← f.L_eulerProduct_tprod hk (half_add_one_lt_re_add hs)]
  congr
  funext p
  have hp : (p.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  have h₁ : (p.val : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) =
      (p.val : ℂ) ^ (-s) / (p.val : ℂ) ^ (((k : ℂ) - 1) / 2) := by
    rw [neg_add, cpow_add _ _ hp, cpow_neg _ (((k : ℂ) - 1) / 2), ← div_eq_mul_inv]
  have h₂ : (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * (s + ((k : ℂ) - 1) / 2)) =
      (p.val : ℂ) ^ (-2 * s) := by
    rw [← cpow_intCast, ← cpow_add _ _ hp]
    congr 1
    push_cast
    ring1
  rw [analyticCoeff, mul_assoc (f.dirichletLift p.val), h₂, h₁]
  ring1

/-- **The completed L-function is `N^(s/2) Γ_ℂ(s + (k-1)/2) L(s, f)`** wherever
`Γ_ℂ(s + (k-1)/2)` has no pole, that is unless `s + (k-1)/2` is an integer `≤ 0`. -/
lemma analyticCompletedL_eq_cpow_mul_Gammaℂ_mul_analyticL (hk : 0 < k)
    (hs : ∀ m : ℕ, s + ((k : ℂ) - 1) / 2 ≠ -m) : f.analyticCompletedL s =
    (N : ℂ) ^ (s / 2) * Gammaℂ (s + ((k : ℂ) - 1) / 2) * f.analyticL hk s := by
  have hΓ : Gammaℂ (s + ((k : ℂ) - 1) / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (.inl (mul_ne_zero two_ne_zero
      (ofReal_ne_zero.mpr Real.pi_ne_zero))))) (Gamma_ne_zero hs)
  rw [f.analyticCompletedL_eq_cpow_mul_Λ hk, analyticL, ModularForm.L, mul_assoc]
  generalize s + ((k : ℂ) - 1) / 2 = w at hΓ ⊢
  field_simp

/-- **The completed L-function is entire.** -/
lemma differentiable_analyticCompletedL (hk : 0 < k) : Differentiable ℂ f.analyticCompletedL :=
  (f.toCuspForm.differentiable_frickeCompletedL _ hk).comp (differentiable_id.add_const _)
  |>.const_mul _

variable (s) in
lemma analyticCompletedL_conj :
    f.conj.analyticCompletedL s = starRingEnd ℂ (f.analyticCompletedL (starRingEnd ℂ s)) := by
  rw [analyticCompletedL, analyticCompletedL, toCuspForm_conj, CuspForm.frickeCompletedL_conj,
    map_mul, map_mul, map_ofNat, conj_ofReal, map_add, map_div₀, map_sub, map_intCast, map_one,
    map_ofNat]

variable (s) in
/-- **The functional equation with the dual form** `f_ρ`: `Λ(s, f) = ε Λ(1 - s, f_ρ)`. -/
lemma analyticCompletedL_eq_rootNumber_mul_conj (hk : 0 < k) :
    f.analyticCompletedL s = f.rootNumber * f.conj.analyticCompletedL (1 - s) := by
  have h : f.toCuspForm.frickeCompletedL (N.toPNat (NeZero.pos N)) (s + ((k : ℂ) - 1) / 2) =
      I ^ k * (f.frickePseudoEigenvalue *
        f.conj.toCuspForm.frickeCompletedL (N.toPNat (NeZero.pos N))
          (1 - s + ((k : ℂ) - 1) / 2)) := by
    rw [← CuspForm.frickeCompletedL_smul,
      ← f.normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul,
      ← f.toCuspForm.frickeCompletedL_functional_equation_gamma1 hk]
    congr 1
    ring1
  rw [analyticCompletedL, analyticCompletedL, h, rootNumber]
  ring1

variable (s) in
/-- **The functional equation** (LMFDB `cmf.lfunction`): `Λ(s, f) = ε Λ̄(1 - s, f)`, where
`Λ̄(s, f) = conj (Λ(conj s, f))`. -/
lemma analyticCompletedL_eq_rootNumber_mul (hk : 0 < k) : f.analyticCompletedL s =
    f.rootNumber * starRingEnd ℂ (f.analyticCompletedL (1 - starRingEnd ℂ s)) := by
  rw [f.analyticCompletedL_eq_rootNumber_mul_conj s hk, analyticCompletedL_conj, map_sub, map_one]

lemma exists_analyticCompletedL_ne_zero (hk : 0 < k) : ∃ s, f.analyticCompletedL s ≠ 0 := by
  rcases Function.ne_iff.mp (f.L_ne_zero hk) with ⟨w, hw⟩
  refine ⟨w - ((k : ℂ) - 1) / 2, ?_⟩
  rw [f.analyticCompletedL_eq_cpow_mul_Λ hk, sub_add_cancel]
  refine mul_ne_zero (cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr (NeZero.ne N))))
    (mul_ne_zero two_ne_zero fun hΛ ↦ hw ?_)
  rw [Pi.zero_apply, ModularForm.L, hΛ, zero_mul]

/-- **The sign is determined by the functional equation**: a constant `c` with
`Λ(s, f) = c conj (Λ(1 - conj s, f))` for every `s` is the sign `ε`. -/
lemma eq_rootNumber_of_forall_analyticCompletedL_eq (hk : 0 < k) {c : ℂ} (h : ∀ s,
    f.analyticCompletedL s = c * starRingEnd ℂ (f.analyticCompletedL (1 - starRingEnd ℂ s))) :
    c = f.rootNumber := by
  rcases f.exists_analyticCompletedL_ne_zero hk with ⟨t, ht⟩
  have h₁ : f.rootNumber * starRingEnd ℂ (f.analyticCompletedL t) =
      c * starRingEnd ℂ (f.analyticCompletedL t) := by
    have h₂ : (1 : ℂ) - starRingEnd ℂ (1 - starRingEnd ℂ t) = t := by
      rw [map_sub, map_one, starRingEnd_self_apply, sub_sub_cancel]
    rw [← h₂, ← f.analyticCompletedL_eq_rootNumber_mul _ hk, h]
  exact (mul_right_cancel₀ ((map_ne_zero _).mpr ht) h₁).symm

/-- **The sign has absolute value `1`.** -/
lemma norm_rootNumber : ‖f.rootNumber‖ = 1 := by
  simp [rootNumber, f.norm_frickePseudoEigenvalue]

/-- **For trivial character the sign is `1` or `-1`.** -/
lemma rootNumber_eq_one_or_neg_one (hχ : f.χ = 1) : f.rootNumber = 1 ∨ f.rootNumber = -1 := by
  rw [rootNumber, f.frickePseudoEigenvalue_eq_frickeSign hχ]
  exact f.I_zpow_mul_frickeSign_eq_one_or_neg_one hχ

end HeckeRing.GL2.Newform
