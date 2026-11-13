import LeanBridge.ForMathlib.NumberTheory.LFunction.TrivialZero

/-!
# The completed L-function as a product on the whole plane

The completed L-function of an analytic L-function `L` of conductor `N` is
`Λ(s) = N ^ (s / 2) L_∞(s) L(s)`, where `L_∞(s) = ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` is its gamma
factor. The axioms of `AnalyticLFunction` record `Λ` as a function, holomorphic away from
`s = 0, 1`, that equals this product for `re s > 1`. The gamma factor is analytic and nonzero away
from its poles `AnalyticLFunction.SelbergData.gammaPoles`, where Mathlib's `Γ` takes the junk value
`0`. The set of poles is countable, so its complement with `0` and `1` removed is connected, and the
identity theorem extends the product formula from the half-plane `re s > 1` to every `s ≠ 0, 1`
that is not a pole of the gamma factor.

## Main results

* `Complex.Gammaℂ_eq_zero_iff`: `Γ_ℂ(s)` takes Mathlib's junk value `0` exactly at its poles, the
  non-positive integers.
* `AnalyticLFunction.SelbergData.gammaFactor_eq_zero_iff`: the gamma factor vanishes exactly at its
  poles.
* `AnalyticLFunction.SelbergData.analyticAt_gammaFactor`: the gamma factor is analytic away from
  its poles.
* `AnalyticLFunction.completed_eq_of_notMem_gammaPoles` (LMFDB `lfunction.completed`): the
  completed L-function is `Λ(s) = N ^ (s / 2) L_∞(s) L(s)` at every `s ≠ 0, 1` that is not a pole
  of the gamma factor.
-/

open Complex Filter Set

open scoped Topology

/-- `Γ_ℂ(s) = 2 (2π) ^ (-s) Γ(s)` takes Mathlib's junk value `0` exactly at the poles of `Γ`, the
non-positive integers. -/
lemma Complex.Gammaℂ_eq_zero_iff {s : ℂ} : Gammaℂ s = 0 ↔ ∃ n : ℕ, s = -n := by
  simp [Gammaℂ_def, Gamma_eq_zero_iff]

namespace AnalyticLFunction.SelbergData

variable (D : SelbergData) {s : ℂ}

lemma countable_gammaPoles : D.gammaPoles.Countable := by
  refine .union ((D.μ.toFinset.finite_toSet.countable.prod countable_univ).image
    (fun p : ℂ × ℕ ↦ -p.1 - 2 * p.2) |>.mono ?_)
    ((D.ν.toFinset.finite_toSet.countable.prod countable_univ).image
    (fun p : ℂ × ℕ ↦ -p.1 - p.2) |>.mono ?_) <;>
  rintro _ ⟨x, hx, n, rfl⟩ <;>
  exact ⟨(x, n), ⟨by simpa using hx, trivial⟩, rfl⟩

/-- The gamma factor `∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)` vanishes exactly at its poles, where
Mathlib's `Γ` takes the junk value `0`: it has no zeros. -/
lemma gammaFactor_eq_zero_iff : D.gammaFactor s = 0 ↔ s ∈ D.gammaPoles := by
  simp only [gammaFactor, mul_eq_zero, Multiset.prod_eq_zero_iff, Multiset.mem_map,
    Gammaℝ_eq_zero_iff, Gammaℂ_eq_zero_iff]
  refine or_congr (exists_congr fun x ↦ and_congr_right fun _ ↦ exists_congr fun n ↦
    ⟨fun h ↦ ?_, fun h ↦ ?_⟩) (exists_congr fun x ↦ and_congr_right fun _ ↦ exists_congr fun n ↦
    ⟨fun h ↦ ?_, fun h ↦ ?_⟩) <;>
  linear_combination h

lemma differentiable_inv_gammaFactor : Differentiable ℂ fun s ↦ (D.gammaFactor s)⁻¹ := by
  simp only [gammaFactor, mul_inv, ← Multiset.prod_map_inv]
  exact fun s ↦ (DifferentiableAt.multiset_prod fun x _ ↦ differentiable_Gammaℝ_inv.comp
    (differentiable_id.add_const x) s).mul (.multiset_prod fun x _ ↦ differentiable_Gammaℂ_inv.comp
      (differentiable_id.add_const x) s)

lemma notMem_gammaPoles_of_re_pos (hs : 0 < s.re) : s ∉ D.gammaPoles :=
  fun h ↦ D.gammaFactor_ne_zero hs <| D.gammaFactor_eq_zero_iff.mpr h

/-- The gamma factor is analytic away from its poles. -/
lemma analyticAt_gammaFactor (hs : s ∉ D.gammaPoles) : AnalyticAt ℂ D.gammaFactor s := by
  simpa using (D.differentiable_inv_gammaFactor.analyticAt s).fun_inv <|
    inv_ne_zero <| mt D.gammaFactor_eq_zero_iff.mp hs

end AnalyticLFunction.SelbergData

namespace AnalyticLFunction

variable (L : AnalyticLFunction) {s : ℂ}

/-- **The completed L-function is the product of the L-function, its gamma factor and
`N ^ (s / 2)`** (LMFDB `lfunction.completed`):
`Λ(s) = N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ) L(s)` at every `s ≠ 0, 1` that is not a pole of
the gamma factor. The axioms give it for `re s > 1`; both sides are analytic on the complement of
the poles and of `0` and `1`, which is connected. -/
lemma completed_eq_of_notMem_gammaPoles (hs : s ∉ L.selbergData.gammaPoles) (hs₀ : s ≠ 0)
    (hs₁ : s ≠ 1) :
    L.completed s = (L.conductor : ℂ) ^ (s / 2) * L.selbergData.gammaFactor s * L.toFun s := by
  have hU : IsPreconnected (L.selbergData.gammaPoles ∪ {0, 1})ᶜ :=
    (L.selbergData.countable_gammaPoles.union (toFinite {0, 1}).countable
      |>.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have h₂ : (2 : ℂ) ∈ (L.selbergData.gammaPoles ∪ {0, 1})ᶜ := by
    simp [L.selbergData.notMem_gammaPoles_of_re_pos (by norm_num : (0 : ℝ) < (2 : ℂ).re)]
  refine (L.differentiableOn_completed.analyticOnNhd (toFinite {0, 1}).isClosed.isOpen_compl).mono
    (compl_subset_compl.mpr subset_union_right) |>.eqOn_of_preconnected_of_eventuallyEq
    (g := fun s ↦ (L.conductor : ℂ) ^ (s / 2) * L.selbergData.gammaFactor s * L.toFun s)
    (fun z hz ↦ ?_) hU h₂ ?_ (by simp [hs, hs₀, hs₁])
  · rcases not_or.mp hz with ⟨hzΓ, hz₀₁⟩
    exact (L.analyticAt_conductor_cpow.fun_mul (L.selbergData.analyticAt_gammaFactor hzΓ)).fun_mul
      (L.analyticOnNhd_toFun z fun h ↦ hz₀₁ <| .inr h)
  · filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by norm_num : (2 : ℂ) ∈ re ⁻¹' Ioi 1)] with z hz
    exact L.completed_eq hz

end AnalyticLFunction
