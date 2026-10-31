import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Group.FundamentalDomain

/-!
# Unfolding an integral over a fundamental domain

Let a countable group `Γ` act measurably on `X`, preserving a measure `μ`, let `D` be a fundamental
domain for `Γ`, and let `H ≤ Γ` be a subgroup with fundamental domain `F`. For an `H`-invariant
function `φ` integrable on `F`, the integral over `D` of its periodisation
`x ↦ Σ_{H g ∈ H \ Γ} φ(g x)` is the integral of `φ` over `F`: the translates `g D` over a right
transversal of `H` tile a fundamental domain for `H`, and the two fundamental domains for `H` give
the same integral of `φ`. This is the unfolding behind the Petersson product of a Poincaré series
(LMFDB `specialfunction.poincare`).

## Main results

* `MeasureTheory.IsFundamentalDomain.setIntegral_tsum_smul_eq`: the unfolding formula
  `∫_D Σ_i φ(r_i x) dμ = ∫_F φ dμ` for a right transversal `(r_i)` of `H` in `Γ`.
-/

open Function

open scoped Pointwise

namespace MeasureTheory.IsFundamentalDomain

variable {Γ X ι E : Type*} [Group Γ] [Countable Γ] [MulAction Γ X] [MeasurableSpace X]
    [MeasurableConstSMul Γ X] {μ : Measure X} [SMulInvariantMeasure Γ X μ] [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Subgroup Γ} {D F : Set X} {r : ι → Γ}
    {φ : X → E}

/-- **Unfolding**: let `D` be a fundamental domain for `Γ`, `F` one for a subgroup `H`, and
`r : ι → Γ` a right transversal of `H` (the classes of the `(r i)⁻¹` enumerate `Γ ⧸ H`). For an
`H`-invariant `φ` integrable on `F`, `∫_D Σ_i φ(r_i x) dμ = ∫_F φ dμ`. -/
lemma setIntegral_tsum_smul_eq (hD : IsFundamentalDomain Γ D μ) (hF : IsFundamentalDomain H F μ)
    (hr : Bijective fun i ↦ (QuotientGroup.mk (r i)⁻¹ : Γ ⧸ H))
    (hφ : ∀ (h : H) (x : X), φ (h • x) = φ x) (hφF : IntegrableOn φ F μ) :
    ∫ x in D, ∑' i, φ (r i • x) ∂μ = ∫ x in F, φ x ∂μ := by
  have hU : IsFundamentalDomain H (⋃ i, r i • D) μ :=
    hD.iUnion_smul_of_transversal (fun i ↦ hD.nullMeasurableSet_smul _) hr
  have hφU : IntegrableOn φ (⋃ i, r i • D) μ := (hF.integrableOn_iff hU hφ).mp hφF
  have hm (i : ι) : NullMeasurableSet (r i • D) μ := hD.nullMeasurableSet_smul _
  have hd : Pairwise (AEDisjoint μ on fun i ↦ r i • D) := fun i j hij ↦
    hD.aedisjoint fun hr' ↦ hij <| hr.injective <| by simp only [hr']
  have hint (i : ι) : Integrable (fun x ↦ φ (r i • x)) (μ.restrict D) :=
    ((measurePreserving_smul (r i) μ).integrableOn_image (measurableEmbedding_const_smul _)).mp
      (hφU.mono_set (Set.subset_iUnion (fun i ↦ r i • D) i))
  have hsum : Summable fun i ↦ ∫ x in D, ‖φ (r i • x)‖ ∂μ := by
    simp_rw [← (measurePreserving_smul _ μ).setIntegral_image_emb
      (measurableEmbedding_const_smul _) (fun x ↦ ‖φ x‖) D]
    exact (hasSum_integral_iUnion_ae hm hd hφU.norm).summable
  rw [hF.setIntegral_eq hU hφ, ← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [← (measurePreserving_smul _ μ).setIntegral_image_emb
    (measurableEmbedding_const_smul _) φ D]
  exact (hasSum_integral_iUnion_ae hm hd hφU).tsum_eq

end MeasureTheory.IsFundamentalDomain
