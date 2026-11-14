import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.QuasiModularDepth
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# The eta multiplier of real weight

The Dedekind eta function `η(z) = q^(1/24) ∏_{n ≥ 1} (1 - qⁿ)`, `q = e^{2πiz}`, has no zero on the
upper half-plane `ℍ`, where it has the holomorphic logarithm
`log η(z) = 2πiz/24 + ∑_{n ≥ 1} log(1 - qⁿ)` (principal logarithms). So the powers
`η^r = exp(r log η)` are defined on `ℍ` for every complex `r`. For `γ = (a, b; c, d)` in `SL(2, ℤ)`,

`log η(γz) = log η(z) + log(cz + d) / 2 + iφ(γ)` for every `z ∈ ℍ`,

with the principal logarithm of `cz + d` and a real number `φ(γ)` that does not depend on `z`. The
two sides have the same derivative, since the logarithmic derivative of `η` is `(πi/12) E₂` and
`E₂(γz) = (cz + d)² E₂(z) - (6i/π) c (cz + d)`, so their difference is a constant; it is purely
imaginary because `Δ = η²⁴` is invariant in weight `12`, which also gives `24 φ(γ) ∈ 2πℤ`.

The **eta multiplier** of real weight `k` is `v_η^{2k}(γ) = e^{2ikφ(γ)}`. It has absolute value
`1`, and `η^{2k}(γz) = v_η^{2k}(γ) (cz + d)^k η^{2k}(z)` with the principal power `(cz + d)^k`: it
is the multiplier system of the form `η^{2k}` of weight `k`. For `k = 1/2` this is the
transformation law `η(γz) = v_η(γ) (cz + d)^(1/2) η(z)` of the eta function.

The LMFDB (`mf.maass.mwf.character`, and `mf.maass.mwf`) writes
`v(A) = v_η^{2k} := η(Az)^{2k} / η(z)^{2k}`. This quotient depends on `z`: for `A = S` it is
`v_η^{2k}(S) z^k` (`ModularForm.etaPow_S_smul_div_etaPow`), of absolute value `|z|^k`. The factor
`(cz + d)^k` is missing, and the definition is
`v_η^{2k}(A) = η(Az)^{2k} / ((cz + d)^k η(z)^{2k})`, which is `ModularForm.coe_etaMultiplier`.
The right side does not depend on `z`, nor on the logarithm of `η` that defines `η^{2k}`: every
holomorphic logarithm of `η` on `ℍ` gives the same multiplier
(`ModularForm.coe_etaMultiplier_of_cexp_eq`).

## Main definitions

* `ModularForm.etaLog`: the logarithm `log η` of the eta function on the upper half-plane.
* `ModularForm.etaPow`: the powers `η^r = exp(r log η)`.
* `ModularForm.etaPhase`: the phase `φ(γ)`.
* `ModularForm.etaMultiplier` (LMFDB `mf.maass.mwf.character`): the eta multiplier `v_η^{2k}` of
  weight `k`.

## Main results

* `ModularForm.exp_etaLog`: `exp(log η) = η` on `ℍ`.
* `ModularForm.hasDerivAt_etaLog`: `log η` is holomorphic on `ℍ`, with derivative `(πi/12) E₂`.
* `ModularForm.etaPow_natCast`: `η^n` is the `n`-th power of `η` for a natural number `n`.
* `ModularForm.etaLog_smul`: `log η(γz) = log η(z) + log(cz + d) / 2 + iφ(γ)` on `SL(2, ℤ)`.
* `ModularForm.eta_smul`: the transformation law `η(γz) = v_η(γ) (cz + d)^(1/2) η(z)`.
* `ModularForm.etaPow_smul`: `η^{2k}(γz) = v_η^{2k}(γ) (cz + d)^k η^{2k}(z)`.
* `ModularForm.coe_etaMultiplier` (LMFDB `mf.maass.mwf.character`):
  `v_η^{2k}(γ) = η^{2k}(γz) / ((cz + d)^k η^{2k}(z))` for every `z ∈ ℍ`.
* `ModularForm.coe_etaMultiplier_of_cexp_eq`: the same formula with `exp(2k L)` in place of
  `η^{2k}`, for every holomorphic logarithm `L` of `η` on `ℍ`.
* `ModularForm.etaPow_S_smul_div_etaPow`: `η^{2k}(Sz) / η^{2k}(z) = v_η^{2k}(S) z^k`, which
  depends on `z`.
* `ModularForm.etaMultiplier_mul_cpow_denom`: the consistency relation
  `v(γδ) j(γδ, z)^k = v(γ) v(δ) j(γ, δz)^k j(δ, z)^k` of a multiplier system of weight `k`, for
  `v = v_η^{2k}` and `j(γ, z) = cz + d`.
* `ModularForm.etaMultiplier_twelve`: `v_η^{24} = 1` on `SL(2, ℤ)`.
* `ModularForm.etaPhase_T`, `ModularForm.etaPhase_S`, `ModularForm.etaPhase_neg_one`:
  `φ(T) = π/12`, `φ(S) = -π/4` and `φ(-1) = -π/2`, that is, `v_η(T) = e^{πi/12}` and
  `v_η(S) = e^{-πi/4}`.
* `ModularForm.etaMultiplier_neg_one`: `v_η^{2k}(-1) = e^{-πik}`.

## References

* M. I. Knopp, *Modular Functions in Analytic Number Theory*, Markham, 1970, Chapter 3.
* F. Strömberg, *Computation of Maass waveforms with nontrivial multiplier systems*, Math. Comp.
  77 (2008), 2375–2416.
-/

open Complex EisensteinSeries Function Matrix

open UpperHalfPlane hiding I

open scoped MatrixGroups Real

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

namespace ModularForm

variable (k : ℝ) (r : ℂ) (n : ℕ) (g : GL (Fin 2) ℝ) (γ δ : SL(2, ℤ)) (z w : ℍ) {u : ℂ} {L : ℂ → ℂ}

variable (u) in
/-- The **logarithm of the Dedekind eta function** on the upper half-plane:
`log η(z) = 2πiz/24 + ∑_{n ≥ 1} log(1 - qⁿ)` for `q = e^{2πiz}`, with the principal logarithms of
the factors `1 - qⁿ`, which lie in the right half-plane. It is holomorphic on `ℍ`
(`hasDerivAt_etaLog`), with `exp(log η) = η` (`exp_etaLog`). -/
noncomputable def etaLog : ℂ :=
  2 * π * I * u / 24 + ∑' n, log (1 - eta_q n u)

lemma summable_log_one_sub_eta_q : Summable fun n ↦ log (1 - eta_q n z) := by
  simpa [sub_eq_add_neg] using summable_log_one_add_of_summable (summable_eta_q z).of_norm

/-- **`exp(log η) = η`** on the upper half-plane. -/
lemma exp_etaLog : cexp (etaLog z) = η z := by
  rw [etaLog, exp_add, cexp_tsum_eq_tprod (fun n ↦ one_sub_eta_q_ne_zero n z.2)
    (summable_log_one_sub_eta_q z)]
  simp [eta, Periodic.qParam]

lemma summableLocallyUniformlyOn_log_one_sub_pow :
    SummableLocallyUniformlyOn (fun n q ↦ log (1 - q ^ (n + 1))) (Metric.ball (0 : ℂ) 1) := by
  refine ⟨fun q ↦ ∑' n, log (1 - q ^ (n + 1)), ?_⟩
  simp_rw [sub_eq_add_neg]
  refine hasSumLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball fun K hK hcK ↦ ?_
  rcases exists_pos_lt_subset_ball one_pos hcK.isClosed hK with ⟨ρ, hρ, hKρ⟩
  have hs : Summable fun n : ℕ ↦ ρ ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr <| summable_geometric_of_lt_one hρ.1.le hρ.2
  exact hs.hasSumUniformlyOn_log_one_add <| .of_forall fun n x hx ↦ by
    simpa using pow_le_pow_left₀ (norm_nonneg x) (mem_ball_zero_iff.mp <| hKρ hx).le (n + 1)

lemma differentiableAt_etaLog (hu : u ∈ ℍₒ) : DifferentiableAt ℂ etaLog u := by
  have hq : 𝕢 1 u ∈ Metric.ball 0 1 := by simpa using norm_qParam_lt_one 1 ⟨u, hu⟩
  have h : DifferentiableOn ℂ (fun q ↦ ∑' n, log (1 - q ^ (n + 1))) (Metric.ball 0 1) :=
    summableLocallyUniformlyOn_log_one_sub_pow.differentiableOn Metric.isOpen_ball fun n x hx ↦
      (differentiableAt_const _ |>.sub <| differentiableAt_id.pow _).clog <| by
        simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one <| by
          simpa using pow_lt_one₀ (norm_nonneg x) (by simpa using hx) n.succ_ne_zero
  exact .add (by fun_prop) <| (h.differentiableAt <| Metric.isOpen_ball.mem_nhds hq).comp u <| by
    fun_prop

/-- **`log η` is holomorphic on the upper half-plane, with derivative `(πi/12) E₂`**, the
logarithmic derivative of `η`. -/
lemma hasDerivAt_etaLog : HasDerivAt etaLog (π * I / 12 * E2 z) z := by
  have h : HasDerivAt etaLog (deriv etaLog z) z := (differentiableAt_etaLog z.2).hasDerivAt
  have h' : HasDerivAt η (cexp (etaLog z) * deriv etaLog z) z :=
    h.cexp.congr_of_eventuallyEq <| Filter.eventually_of_mem
      (isOpen_upperHalfPlaneSet.mem_nhds z.2) fun x hx ↦ (exp_etaLog ⟨x, hx⟩).symm
  rwa [← logDeriv_eta_eq_E2, logDeriv_apply, h'.deriv, exp_etaLog,
    mul_div_cancel_left₀ _ (eta_ne_zero z.2)]

variable (u) in
lemma etaLog_add_one : etaLog (u + 1) = etaLog u + π * I / 12 := by
  have h : 𝕢 1 (u + 1) = 𝕢 1 u := by simp [Periodic.qParam, mul_add, exp_add]
  simp only [etaLog, eta_q, h]
  ring1

variable (u) in
/-- The **power `η^r` of the Dedekind eta function** with a complex exponent `r`, on the upper
half-plane: `η(z)^r = exp(r log η(z))` for the logarithm `etaLog` of `η`, that is,
`q^(r/24) ∏_{n ≥ 1} (1 - qⁿ)^r` with the principal powers of the factors. For a natural number `r`
it is the `r`-th power of `η` (`etaPow_natCast`). -/
noncomputable def etaPow : ℂ :=
  cexp (r * etaLog u)

/-- **`η^n` is the `n`-th power of `η`** on the upper half-plane, for a natural number `n`. -/
lemma etaPow_natCast : etaPow n z = η z ^ n := by
  rw [etaPow, exp_nat_mul, exp_etaLog]

variable (u) in
lemma etaPow_ne_zero : etaPow r u ≠ 0 :=
  exp_ne_zero _

lemma differentiableAt_etaPow (hu : u ∈ ℍₒ) : DifferentiableAt ℂ (etaPow r) u :=
  ((differentiableAt_etaLog hu).const_mul r).cexp

lemma differentiableOn_etaPow : DifferentiableOn ℂ (etaPow r) ℍₒ :=
  fun _ hu ↦ (differentiableAt_etaPow r hu).differentiableWithinAt

lemma norm_etaPow_ofReal : ‖etaPow k z‖ = ‖η z‖ ^ k := by
  rw [etaPow, norm_exp, ← exp_etaLog, norm_exp, ← Real.exp_mul, re_ofReal_mul, mul_comm]

lemma hasDerivAt_log_denom : HasDerivAt (fun u ↦ log (denom γ u)) ((γ 1 0 : ℂ) / denom γ z) z := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · simpa [denom, hc] using hasDerivAt_const (z : ℂ) (log (γ 1 1 : ℂ))
  · have hd : HasDerivAt (denom γ ·) (γ 1 0 : ℂ) z := by
      simpa [denom] using
        (hasDerivAt_id (z : ℂ)).const_mul ((γ 1 0 : ℤ) : ℂ) |>.add_const ((γ 1 1 : ℤ) : ℂ)
    exact hd.clog <| mem_slitPlane_iff.mpr <| .inr <| by simp [denom, hc, z.im_ne_zero]

lemma hasDerivAt_etaLog_smul_sub :
    HasDerivAt (fun u ↦ etaLog ↑(γ • ofComplex u) - etaLog u - log (denom γ u) / 2) 0 z := by
  have hdet : (γ : GL (Fin 2) ℝ).val.det = 1 :=
    (SpecialLinearGroup.map (Int.castRingHom ℝ) γ).det_coe
  have hd : denom γ z ≠ 0 := denom_ne_zero γ z
  refine ((((hasDerivAt_etaLog (γ • z)).comp_of_eq (z : ℂ)
    (hasStrictDerivAt_smul (g := γ) (hdet ▸ one_pos) z).hasDerivAt (by simp)).sub <|
      hasDerivAt_etaLog z).sub <| (hasDerivAt_log_denom γ z).div_const 2).congr_deriv ?_
  rw [E2_smul, hdet, ofReal_one]
  field_simp
  linear_combination (-12 * (γ 1 0 : ℂ)) * I_sq

lemma etaLog_smul_sub : etaLog ↑(γ • z) - etaLog z - log (denom γ z) / 2 = etaLog ↑(γ • w) -
    etaLog w - log (denom γ w) / 2 := by
  have h (x : ℂ) (hx : x ∈ ℍₒ) :
      HasDerivAt (fun u ↦ etaLog ↑(γ • ofComplex u) - etaLog u - log (denom γ u) / 2) 0 x :=
    hasDerivAt_etaLog_smul_sub γ ⟨x, hx⟩
  simpa using isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun x hx ↦ (h x hx).differentiableAt.differentiableWithinAt) (fun x hx ↦ (h x hx).deriv)
    z.2 w.2

lemma exp_etaLog_smul_sub : cexp (24 * (etaLog ↑(γ • z) - etaLog z - log (denom γ z) / 2)) = 1 := by
  have hΔ : η ↑(γ • z) ^ 24 = denom γ z ^ 12 * η z ^ 24 := by
    simpa [discriminant] using SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ)
      CuspForm.discriminant (γ := (γ : GL (Fin 2) ℝ)) ⟨γ, rfl⟩ z
  have h : 24 * (etaLog ↑(γ • z) - etaLog z - log (denom γ z) / 2) = (24 : ℕ) * etaLog ↑(γ • z) -
      ((24 : ℕ) * etaLog z + (12 : ℕ) * log (denom γ z)) := by
    push_cast
    ring1
  rw [h, exp_sub, exp_add, exp_nat_mul, exp_nat_mul, exp_nat_mul, exp_etaLog, exp_etaLog,
    exp_log (denom_ne_zero γ z), hΔ]
  exact div_eq_one_iff_eq (mul_ne_zero (pow_ne_zero _ <| eta_ne_zero z.2) <|
    pow_ne_zero _ <| denom_ne_zero γ z) |>.mpr <| mul_comm _ _

/-- The **phase of the eta multiplier**: the real number
`φ(γ) = Im (log η(γi) - log η(i) - log(ci + d) / 2)` for `γ = (a, b; c, d)`, with the principal
logarithm of `ci + d`. For `γ ∈ SL(2, ℤ)` it satisfies
`log η(γz) = log η(z) + log(cz + d) / 2 + iφ(γ)` for every `z ∈ ℍ` (`etaLog_smul`), and
`24 φ(γ) ∈ 2πℤ` (`etaMultiplier_twelve`). It is defined for every `γ ∈ GL(2, ℝ)`, and meant for
`γ ∈ SL(2, ℤ)`. -/
noncomputable def etaPhase : ℝ :=
  (etaLog ↑(g • UpperHalfPlane.I) - etaLog UpperHalfPlane.I - log (denom g UpperHalfPlane.I) / 2).im

/-- **The transformation law of `log η`**: for `γ = (a, b; c, d)` in `SL(2, ℤ)` and `z ∈ ℍ`,
`log η(γz) = log η(z) + log(cz + d) / 2 + iφ(γ)`, with the principal logarithm of `cz + d` and the
phase `φ(γ)` of `etaPhase`, which does not depend on `z`. -/
lemma etaLog_smul : etaLog ↑(γ • z) = etaLog z + log (denom γ z) / 2 + etaPhase γ * I := by
  have hre : (etaLog ↑(γ • z) - etaLog z - log (denom γ z) / 2).re = 0 := by
    simpa [norm_exp] using congrArg norm (exp_etaLog_smul_sub γ z)
  have him : (etaLog ↑(γ • z) - etaLog z - log (denom γ z) / 2).im = etaPhase γ :=
    congrArg Complex.im (etaLog_smul_sub γ z UpperHalfPlane.I)
  have h : ((0 : ℝ) : ℂ) + etaPhase γ * I = etaLog ↑(γ • z) - etaLog z - log (denom γ z) / 2 :=
    hre ▸ him ▸ re_add_im _
  linear_combination ofReal_zero - h

/-- The **eta multiplier** `v_η^{2k}` of real weight `k` (LMFDB `mf.maass.mwf.character`), the
multiplier system of the powers of the Dedekind eta function: `v_η^{2k}(γ) = e^{2ikφ(γ)}` for the
phase `φ` of `etaPhase`, a complex number of absolute value `1`. For `γ = (a, b; c, d)` in
`SL(2, ℤ)` and every `z ∈ ℍ` it is `η^{2k}(γz) / ((cz + d)^k η^{2k}(z))`, with
`η^{2k} = exp(2k log η)` and the principal power `(cz + d)^k` (`coe_etaMultiplier`), whichever
holomorphic logarithm of `η` is taken for `log η` (`coe_etaMultiplier_of_cexp_eq`): this is the
LMFDB's `v_η^{2k}(A) = η(Az)^{2k} / η(z)^{2k}` with the missing factor `(cz + d)^k` restored,
without which the quotient depends on `z`. It is defined for every `γ ∈ GL(2, ℝ)`, and meant for
`γ ∈ SL(2, ℤ)`. -/
noncomputable def etaMultiplier : Circle :=
  Circle.exp (2 * k * etaPhase g)

lemma etaMultiplier_add (l : ℝ) :
    etaMultiplier (k + l) g = etaMultiplier k g * etaMultiplier l g := by
  rw [etaMultiplier, mul_add, add_mul, Circle.exp_add, etaMultiplier, etaMultiplier]

lemma etaMultiplier_neg : etaMultiplier (-k) g = (etaMultiplier k g)⁻¹ := by
  rw [etaMultiplier, mul_neg, neg_mul, Circle.exp_neg, etaMultiplier]

/-- **The transformation law of the powers of `η`**: for `γ = (a, b; c, d)` in `SL(2, ℤ)`, real `k`
and `z ∈ ℍ`, `η^{2k}(γz) = v_η^{2k}(γ) (cz + d)^k η^{2k}(z)`, with the principal power of
`cz + d`. -/
lemma etaPow_smul :
    etaPow (2 * k) ↑(γ • z) = etaMultiplier k γ * denom γ z ^ (k : ℂ) * etaPow (2 * k) z := by
  rw [etaPow, etaLog_smul, etaMultiplier, Circle.coe_exp, cpow_def_of_ne_zero (denom_ne_zero γ z),
    etaPow, ← exp_add, ← exp_add]
  congr 1
  push_cast
  ring1

/-- **The eta multiplier is the automorphy factor of `η^{2k}`** (LMFDB `mf.maass.mwf.character`,
with the factor `(cz + d)^k` restored): for `γ = (a, b; c, d)` in `SL(2, ℤ)` and every `z ∈ ℍ`,
`v_η^{2k}(γ) = η^{2k}(γz) / ((cz + d)^k η^{2k}(z))`. In particular the right side does not depend
on `z`, and has absolute value `1`. -/
lemma coe_etaMultiplier : (etaMultiplier k γ : ℂ) =
    etaPow (2 * k) ↑(γ • z) / (denom γ z ^ (k : ℂ) * etaPow (2 * k) z) := by
  rw [etaPow_smul, mul_assoc, mul_div_assoc, div_self <| mul_ne_zero
    (cpow_ne_zero_iff.mpr <| .inl <| denom_ne_zero γ z) <| etaPow_ne_zero _ _, mul_one]

lemma hasDerivAt_sub_etaLog (hL : DifferentiableOn ℂ L ℍₒ) (hη : ∀ x ∈ ℍₒ, cexp (L x) = η x)
    (hu : u ∈ ℍₒ) : HasDerivAt (fun x ↦ L x - etaLog x) 0 u := by
  have hn : ℍₒ ∈ nhds u := isOpen_upperHalfPlaneSet.mem_nhds hu
  have hd : HasDerivAt (fun x ↦ L x - etaLog x) (deriv L u - deriv etaLog u) u :=
    (hL.differentiableAt hn).hasDerivAt.sub (differentiableAt_etaLog hu).hasDerivAt
  have h : HasDerivAt (fun x ↦ cexp (L x - etaLog x)) 0 u :=
    (hasDerivAt_const u (1 : ℂ)).congr_of_eventuallyEq <| Filter.eventually_of_mem hn fun x hx ↦
      (exp_sub _ _).trans <| by rw [hη x hx, exp_etaLog ⟨x, hx⟩, div_self (eta_ne_zero hx)]
  exact (mul_eq_zero.mp <| hd.cexp.unique h).resolve_left (exp_ne_zero _) ▸ hd

/-- **The eta multiplier does not depend on the logarithm of `η`**: for every holomorphic
logarithm `L` of `η` on `ℍ`, that is, every holomorphic `L` with `exp(L) = η`, and for
`γ = (a, b; c, d)` in `SL(2, ℤ)` and every `z ∈ ℍ`,
`v_η^{2k}(γ) = exp(2k L(γz)) / ((cz + d)^k exp(2k L(z)))`. Two such logarithms differ by a
constant, which cancels. So the LMFDB's formula, with the factor `(cz + d)^k` restored, gives
`v_η^{2k}` for every holomorphic branch `exp(2k L)` of `η^{2k}`, taken in the numerator and in the
denominator. -/
lemma coe_etaMultiplier_of_cexp_eq (hL : DifferentiableOn ℂ L ℍₒ)
    (hη : ∀ x ∈ ℍₒ, cexp (L x) = η x) : (etaMultiplier k γ : ℂ) =
    cexp (2 * k * L ↑(γ • z)) / (denom γ z ^ (k : ℂ) * cexp (2 * k * L z)) := by
  have h : L ↑(γ • z) - etaLog ↑(γ • z) = L z - etaLog z :=
    isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun _ hx ↦ (hasDerivAt_sub_etaLog hL hη hx).differentiableAt.differentiableWithinAt)
      (fun _ hx ↦ (hasDerivAt_sub_etaLog hL hη hx).deriv) (γ • z).2 z.2
  rw [coe_etaMultiplier k γ z, etaPow, etaPow, div_mul_eq_div_div_swap, div_mul_eq_div_div_swap,
    ← exp_sub, ← exp_sub]
  congr 2
  linear_combination -(2 * (k : ℂ)) * h

/-- **The quotient `η^{2k}(γz) / η^{2k}(z)` depends on `z`**: for the inversion `S : z ↦ -1/z` it
is `v_η^{2k}(S) z^k`, of absolute value `|z|^k`. This quotient is the LMFDB's formula for
`v_η^{2k}` (`mf.maass.mwf.character`), which lacks the factor `(cz + d)^k` of
`coe_etaMultiplier`. -/
lemma etaPow_S_smul_div_etaPow : etaPow (2 * k) ↑(ModularGroup.S • z) / etaPow (2 * k) z =
    etaMultiplier k ModularGroup.S * (z : ℂ) ^ (k : ℂ) := by
  rw [etaPow_smul, ModularGroup.denom_S, mul_div_cancel_right₀ _ (etaPow_ne_zero _ _)]

/-- **The eta multiplier is a multiplier system of weight `k`**: it satisfies the consistency
relation `v(γδ) j(γδ, z)^k = v(γ) v(δ) j(γ, δz)^k j(δ, z)^k` on `SL(2, ℤ)`, where
`j(γ, z) = cz + d` and the powers are principal. With `|v| = 1` and `v(-1) = e^{-πik}`
(`etaMultiplier_neg_one`), these are the conditions on a multiplier system of real weight `k`. -/
lemma etaMultiplier_mul_cpow_denom : (etaMultiplier k ↑(γ * δ) : ℂ) * denom ↑(γ * δ) z ^ (k : ℂ) =
    etaMultiplier k γ * etaMultiplier k δ * denom γ ↑(δ • z) ^ (k : ℂ) * denom δ z ^ (k : ℂ) := by
  have h : etaPow (2 * k) ↑((γ * δ) • z) =
      etaMultiplier k ↑(γ * δ) * denom ↑(γ * δ) z ^ (k : ℂ) * etaPow (2 * k) z :=
    etaPow_smul k (γ * δ) z
  rw [mul_smul, etaPow_smul, etaPow_smul] at h
  exact mul_right_cancel₀ (etaPow_ne_zero (2 * k) z) <| by linear_combination -h

/-- **The transformation law of the Dedekind eta function** on `SL(2, ℤ)`: for
`γ = (a, b; c, d)` and `z ∈ ℍ`, `η(γz) = v_η(γ) (cz + d)^(1/2) η(z)`, with the principal square
root and the eta multiplier `v_η` of weight `1/2`. -/
lemma eta_smul : η ↑(γ • z) = etaMultiplier (1 / 2) γ * denom γ z ^ (1 / 2 : ℂ) * η z := by
  simpa [etaPow, exp_etaLog] using etaPow_smul (1 / 2) γ z

/-- **`v_η^{24} = 1`** on `SL(2, ℤ)`: the eta multiplier of weight `12` is trivial, as
`Δ = η²⁴` is a modular form of weight `12` with trivial multiplier. That is, `24 φ(γ) ∈ 2πℤ`. -/
lemma etaMultiplier_twelve : etaMultiplier 12 γ = 1 := by
  refine Circle.ext ?_
  rw [etaMultiplier, Circle.coe_exp, Circle.coe_one, ← exp_etaLog_smul_sub γ UpperHalfPlane.I,
    etaLog_smul]
  congr 1
  push_cast
  ring1

lemma etaMultiplier_add_twelve : etaMultiplier (k + 12) γ = etaMultiplier k γ := by
  rw [etaMultiplier_add, etaMultiplier_twelve, mul_one]

/-- **`φ(T) = π/12`**: the eta multiplier of the translation `T : z ↦ z + 1` is
`v_η(T) = e^{πi/12}`, as `log η(z + 1) = log η(z) + πi/12`. -/
lemma etaPhase_T : etaPhase ModularGroup.T = π / 12 := by
  have h : ((ModularGroup.T • UpperHalfPlane.I : ℍ) : ℂ) = UpperHalfPlane.I + 1 := by
    rw [modular_T_smul, coe_vadd, ofReal_one, add_comm]
  have hd : denom ModularGroup.T UpperHalfPlane.I = 1 := by
    rw [ModularGroup.denom_apply]
    simp
  rw [etaPhase, ← ModularGroup.sl_moeb, h, hd, etaLog_add_one]
  simp

/-- **`φ(S) = -π/4`**: the eta multiplier of the inversion `S : z ↦ -1/z` is
`v_η(S) = e^{-πi/4}`, in accordance with `η(-1/z) = (z/i)^(1/2) η(z)`. -/
lemma etaPhase_S : etaPhase ModularGroup.S = -(π / 4) := by
  have h : ((ModularGroup.S • UpperHalfPlane.I : ℍ) : ℂ) = UpperHalfPlane.I := by
    rw [modular_S_smul]
    simp
  rw [etaPhase, ← ModularGroup.sl_moeb, h, ModularGroup.denom_S, coe_I, log_I]
  norm_num [div_div]

/-- **`φ(-1) = -π/2`**: `-1` acts trivially on `ℍ` with `cz + d = -1`, and the principal
logarithm of `-1` is `πi`. -/
lemma etaPhase_neg_one : etaPhase (-1) = -(π / 2) := by
  rw [etaPhase, UpperHalfPlane.neg_smul, one_smul, denom_neg, denom_one, log_neg_one]
  simp

/-- **`v_η^{2k}(-1) = e^{-πik}`**: the value of the eta multiplier of weight `k` at `-1`, the one
that a nonzero function of weight `k` forces on its multiplier. For an integer `k` it is `(-1)^k`,
the value at `-I` of a multiplier system of integral weight `k` (LMFDB `mf.multipliersystem`). -/
lemma etaMultiplier_neg_one : etaMultiplier k (-1) = Circle.exp (-(π * k)) := by
  rw [etaMultiplier, etaPhase_neg_one]
  congr 1
  ring1

end ModularForm
