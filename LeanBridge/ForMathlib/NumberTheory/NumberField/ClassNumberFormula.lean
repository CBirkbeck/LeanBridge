import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# The analytic class number formula

Mathlib's `NumberField.dedekindZeta_residue K` is the quantity `2 ^ r₁ (2π) ^ r₂ R h / (w √|D|)`,
and `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` is the limit of `(s - 1) ζ_K(s)` as the
real number `s` tends to `1` from above. Tau Ceti continues `ζ_K(s) - ρ / (s - 1)` holomorphically
to the half-plane `Re s > 1 - 1 / [K : ℚ]`. Together they give the analytic class number formula
as a statement about the residue of the meromorphic continuation of `ζ_K` at `s = 1`.

## Main results

* `NumberField.exists_tendsto_sub_one_mul_dedekindZeta` (LMFDB `nf.class_number_formula`): `ζ_K`
  continues holomorphically to `Re s > 1 - 1 / [K : ℚ]` minus `s = 1`, and `(s - 1) ζ_K(s)` tends
  to `2 ^ r₁ (2π) ^ r₂ R h / (w √|D|)` as the complex number `s` tends to `1`.

The continuation of `ζ_K` to the whole complex plane, which the LMFDB knowl also asserts, is
Hecke's theorem and is not available.
-/

open Filter Topology

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **The analytic class number formula** (LMFDB `nf.class_number_formula`): the Dedekind zeta
function of `K` continues holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]` minus the
point `s = 1`, and the continuation `F` satisfies `lim_{s → 1} (s - 1) F(s) = ρ`, where
`ρ = dedekindZeta_residue K = 2 ^ r₁ (2π) ^ r₂ R h / (w √|D|)` (`dedekindZeta_residue_def`). -/
lemma exists_tendsto_sub_one_mul_dedekindZeta : ∃ F : ℂ → ℂ, DifferentiableOn ℂ F
    ({s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} \ {1}) ∧ (∀ s : ℂ, 1 < s.re → F s =
    dedekindZeta K s) ∧ Tendsto (fun s ↦ (s - 1) * F s) (𝓝[≠] 1) (𝓝 (dedekindZeta_residue K)) := by
  rcases TauCeti.exists_differentiableOn_eq_dedekindZeta_sub K with ⟨G, hG, hGζ⟩
  refine ⟨fun s ↦ G s + dedekindZeta_residue K / (s - 1), (hG.mono Set.sdiff_subset).add <|
    (differentiableOn_const _).div (differentiableOn_id.sub_const 1) fun _ hs ↦
    sub_ne_zero.mpr hs.2, fun s hs ↦ (congrArg (· + _) (hGζ s hs)).trans (sub_add_cancel _ _), ?_⟩
  have h1 : (1 : ℂ) ∈ {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
    TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K (by simp)
  have hG1 : ContinuousAt G 1 :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1 |> hG.differentiableAt
    |>.continuousAt
  have h : Tendsto (fun s ↦ (s - 1) * G s + dedekindZeta_residue K) (𝓝[≠] 1)
      (𝓝 ((1 - 1) * G 1 + dedekindZeta_residue K)) :=
    ((continuousAt_id.sub continuousAt_const).mul hG1).tendsto.mono_left nhdsWithin_le_nhds
    |>.add_const _
  rw [sub_self, zero_mul, zero_add] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
  beta_reduce
  rw [mul_add, mul_div_cancel₀ _ (sub_ne_zero.mpr hs)]

end NumberField
