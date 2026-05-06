import LeanBridge.ForMathlib.QExpansion.Generic
import LeanBridge.ForMathlib.QExpansion.Examples
import LeanBridge.ForMathlib.QExpansion.Sturm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# LMFDB level-1 modular form `1.24.a.a` (one of two Galois-conjugate cusp forms in S₂₄)

The Hecke field is `K = ℚ(α)` with minimal polynomial `α² - 1080 α - 20468736 = 0`. The two
roots are `α = 540 ± 12√144169`. The LMFDB labels `1.24.a.a` and `1.24.a.b` denote the two
Galois conjugates (we pick the `+` sign here).

The form decomposes as `f = f_rat + α · f_irrat` where `f_rat` and `f_irrat` are level-1
weight-24 modular forms with rational coefficients in `(E₄, E₆)`. Each is certified by the
existing rational framework; the LMFDB-published `c_n = c_n^(0) + α · c_n^(1)` is then matched
by `linear_combination` against the minimal-polynomial relation.
-/

namespace LeanBridge.QExpansion

open ModularForm EisensteinSeries PowerSeries UpperHalfPlane
open scoped MatrixGroups

/-! ## The algebraic generator α for LMFDB form `1.24.a.a` -/

/-- `β = √144169 : ℂ` (real, positive). -/
noncomputable def β_24 : ℂ := Complex.ofReal (Real.sqrt 144169)

lemma β_24_sq : β_24 ^ 2 = 144169 := by
  unfold β_24
  rw [show (Complex.ofReal (Real.sqrt 144169)) ^ 2 =
        Complex.ofReal ((Real.sqrt 144169) ^ 2) from by push_cast; ring,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 144169)]
  norm_num

/-- `α = 540 + 12 √144169`, a root of `x² - 1080 x - 20468736 = 0`.
This is the Hecke eigenvalue `a₂` of the LMFDB form `1.24.a.a`. -/
noncomputable def α_24 : ℂ := 540 + 12 * β_24

lemma α_24_minpoly : α_24 ^ 2 - 1080 * α_24 - 20468736 = 0 := by
  unfold α_24
  linear_combination 144 * β_24_sq

/-! ## Rational decomposition of `f = f_rat + α · f_irrat`

Sage computed:
- `f_rat   = -29/124416 · E₆⁴ - 7/62208 · E₄³ E₆² + 43/124416 · E₄⁶`
- `f_irrat = 1/2985984 · E₆⁴ - 1/1492992 · E₄³ E₆² + 1/2985984 · E₄⁶`
-/

def f_rat_24_polyData : List (ℕ × ℕ × ℚ) :=
  [(0, 4, -(29/124416)), (3, 2, -(7/62208)), (6, 0, 43/124416)]

def f_irrat_24_polyData : List (ℕ × ℕ × ℚ) :=
  [(0, 4, 1/2985984), (3, 2, -(1/1492992)), (6, 0, 1/2985984)]

noncomputable def f_rat_24 : ModularForm 𝒮ℒ 24 :=
  (-(29/124416) : ℂ) • mkMonomForm 0 4 24 (by decide) +
  ((-(7/62208)) : ℂ) • mkMonomForm 3 2 24 (by decide) +
  ((43/124416) : ℂ) • mkMonomForm 6 0 24 (by decide)

noncomputable def f_irrat_24 : ModularForm 𝒮ℒ 24 :=
  ((1/2985984) : ℂ) • mkMonomForm 0 4 24 (by decide) +
  ((-(1/1492992)) : ℂ) • mkMonomForm 3 2 24 (by decide) +
  ((1/2985984) : ℂ) • mkMonomForm 6 0 24 (by decide)

/-! ## Bridge for the two rational pieces -/

lemma f_rat_24_qExpansion_eq_evalEisPS :
    qExpansion 1 (f_rat_24 : ℍ → ℂ) = evalEisPS f_rat_24_polyData := by
  unfold f_rat_24
  -- For 3 monomials, interleave coe_add and qExpansion_add (outer to inner)
  rw [ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
    ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
    ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    qExpansion_mkMonomForm, qExpansion_mkMonomForm, qExpansion_mkMonomForm]
  unfold evalEisPS f_rat_24_polyData monomialEisPS
  simp only [List.foldr_cons, List.foldr_nil, add_zero]
  push_cast
  module

lemma f_irrat_24_qExpansion_eq_evalEisPS :
    qExpansion 1 (f_irrat_24 : ℍ → ℂ) = evalEisPS f_irrat_24_polyData := by
  unfold f_irrat_24
  rw [ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
    ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
    ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    qExpansion_mkMonomForm, qExpansion_mkMonomForm, qExpansion_mkMonomForm]
  unfold evalEisPS f_irrat_24_polyData monomialEisPS
  simp only [List.foldr_cons, List.foldr_nil, add_zero]
  push_cast
  module

theorem f_rat_24_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (f_rat_24 : ℍ → ℂ))
      = ((evalEisList f_rat_24_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 _ _ f_rat_24_qExpansion_eq_evalEisPS N n hn

theorem f_irrat_24_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (f_irrat_24 : ℍ → ℂ))
      = ((evalEisList f_irrat_24_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 _ _ f_irrat_24_qExpansion_eq_evalEisPS N n hn

/-! ## The combined LMFDB form -/

/-- LMFDB form `1.24.a.a`, defined as `f_rat + α · f_irrat`. -/
noncomputable def lmfdb_1_24_a_a : ModularForm 𝒮ℒ 24 :=
  f_rat_24 + α_24 • f_irrat_24

/-- Coefficient of `lmfdb_1_24_a_a` decomposes as `(rat coeff) + α · (irrat coeff)`. -/
lemma lmfdb_1_24_a_a_coeff_decomp (n : ℕ) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (lmfdb_1_24_a_a : ℍ → ℂ))
      = (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (f_rat_24 : ℍ → ℂ))
        + α_24 * (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (f_irrat_24 : ℍ → ℂ)) := by
  unfold lmfdb_1_24_a_a
  rw [ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
    ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  simp [smul_eq_mul]

/-! ## Sturm-bound certificates

Sturm bound for weight 24: ⌊24/12⌋ + 1 = 3. The first 3 q-coefficients of `1.24.a.a` are
`[0, 1, α]` where `α` is our `α_24`. -/

/-- `c_0 = 0` (cusp form). -/
example :
    (PowerSeries.coeff (R := ℂ) 0)
      (qExpansion 1 (lmfdb_1_24_a_a : ℍ → ℂ)) = 0 := by
  rw [lmfdb_1_24_a_a_coeff_decomp,
    f_rat_24_qExpansion_coeff 3 0 (by decide),
    f_irrat_24_qExpansion_coeff 3 0 (by decide),
    show (evalEisList f_rat_24_polyData 3).getD 0 0 = (0 : ℚ) from by decide +kernel,
    show (evalEisList f_irrat_24_polyData 3).getD 0 0 = (0 : ℚ) from by decide +kernel]
  push_cast; ring

/-- `c_1 = 1` (normalized newform). -/
example :
    (PowerSeries.coeff (R := ℂ) 1)
      (qExpansion 1 (lmfdb_1_24_a_a : ℍ → ℂ)) = 1 := by
  rw [lmfdb_1_24_a_a_coeff_decomp,
    f_rat_24_qExpansion_coeff 3 1 (by decide),
    f_irrat_24_qExpansion_coeff 3 1 (by decide),
    show (evalEisList f_rat_24_polyData 3).getD 1 0 = (1 : ℚ) from by decide +kernel,
    show (evalEisList f_irrat_24_polyData 3).getD 1 0 = (0 : ℚ) from by decide +kernel]
  push_cast; ring

/-- `c_2 = α` (the Hecke eigenvalue at p = 2). -/
example :
    (PowerSeries.coeff (R := ℂ) 2)
      (qExpansion 1 (lmfdb_1_24_a_a : ℍ → ℂ)) = α_24 := by
  rw [lmfdb_1_24_a_a_coeff_decomp,
    f_rat_24_qExpansion_coeff 3 2 (by decide),
    f_irrat_24_qExpansion_coeff 3 2 (by decide),
    show (evalEisList f_rat_24_polyData 3).getD 2 0 = (0 : ℚ) from by decide +kernel,
    show (evalEisList f_irrat_24_polyData 3).getD 2 0 = (1 : ℚ) from by decide +kernel]
  push_cast; ring

/-! ## Sturm-bound certified named lemmas

We package the three Sturm-bound certificates as named lemmas, then use them with
`ModularForm.eq_of_sturm_bound` to prove the uniqueness theorem below. -/

lemma lmfdb_1_24_a_a_qExpansion_coeff_zero :
    (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (lmfdb_1_24_a_a : ℍ → ℂ)) = 0 := by
  rw [lmfdb_1_24_a_a_coeff_decomp,
    f_rat_24_qExpansion_coeff 3 0 (by decide),
    f_irrat_24_qExpansion_coeff 3 0 (by decide),
    show (evalEisList f_rat_24_polyData 3).getD 0 0 = (0 : ℚ) from by decide +kernel,
    show (evalEisList f_irrat_24_polyData 3).getD 0 0 = (0 : ℚ) from by decide +kernel]
  push_cast; ring

lemma lmfdb_1_24_a_a_qExpansion_coeff_one :
    (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (lmfdb_1_24_a_a : ℍ → ℂ)) = 1 := by
  rw [lmfdb_1_24_a_a_coeff_decomp,
    f_rat_24_qExpansion_coeff 3 1 (by decide),
    f_irrat_24_qExpansion_coeff 3 1 (by decide),
    show (evalEisList f_rat_24_polyData 3).getD 1 0 = (1 : ℚ) from by decide +kernel,
    show (evalEisList f_irrat_24_polyData 3).getD 1 0 = (0 : ℚ) from by decide +kernel]
  push_cast; ring

lemma lmfdb_1_24_a_a_qExpansion_coeff_two :
    (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (lmfdb_1_24_a_a : ℍ → ℂ)) = α_24 := by
  rw [lmfdb_1_24_a_a_coeff_decomp,
    f_rat_24_qExpansion_coeff 3 2 (by decide),
    f_irrat_24_qExpansion_coeff 3 2 (by decide),
    show (evalEisList f_rat_24_polyData 3).getD 2 0 = (0 : ℚ) from by decide +kernel,
    show (evalEisList f_irrat_24_polyData 3).getD 2 0 = (1 : ℚ) from by decide +kernel]
  push_cast; ring

/-- **Uniqueness theorem**. Any level-1 weight-24 modular form `f` whose first three
q-coefficients are `[0, 1, α_24]` (the Sturm-bound-many published values for `1.24.a.a`)
is equal to our explicit construction `lmfdb_1_24_a_a`. Proven via
`ModularForm.eq_of_sturm_bound` (Sturm bound for level-1 modular forms). -/
theorem identifies_lmfdb_1_24_a_a (f : ModularForm 𝒮ℒ 24)
    (h_0 : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (f : ℍ → ℂ)) = 0)
    (h_1 : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (f : ℍ → ℂ)) = 1)
    (h_2 : (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (f : ℍ → ℂ)) = α_24) :
    f = lmfdb_1_24_a_a := by
  apply ModularForm.eq_of_sturm_bound
  intro i hi
  -- 12 * i ≤ 24 means i ∈ {0, 1, 2}
  have : i ≤ 2 := by omega
  interval_cases i
  · rw [h_0, lmfdb_1_24_a_a_qExpansion_coeff_zero]
  · rw [h_1, lmfdb_1_24_a_a_qExpansion_coeff_one]
  · rw [h_2, lmfdb_1_24_a_a_qExpansion_coeff_two]

/-! ## Beyond Sturm: `c_3 = -48 α + 195660` -/

example :
    (PowerSeries.coeff (R := ℂ) 3)
      (qExpansion 1 (lmfdb_1_24_a_a : ℍ → ℂ)) = -48 * α_24 + 195660 := by
  rw [lmfdb_1_24_a_a_coeff_decomp,
    f_rat_24_qExpansion_coeff 4 3 (by decide),
    f_irrat_24_qExpansion_coeff 4 3 (by decide),
    show (evalEisList f_rat_24_polyData 4).getD 3 0 = (195660 : ℚ) from by decide +kernel,
    show (evalEisList f_irrat_24_polyData 4).getD 3 0 = (-48 : ℚ) from by decide +kernel]
  push_cast; ring

end LeanBridge.QExpansion
