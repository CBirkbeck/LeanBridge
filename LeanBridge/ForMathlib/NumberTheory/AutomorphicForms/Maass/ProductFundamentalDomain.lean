import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fundamental domains of the diagonal action on a product

If a countable group `G` acts on a measure space `(α, μ)` preserving `μ`, with fundamental domain
`D`, then `D × α` and `α × D` are fundamental domains of the diagonal action of `G` on `α × α` for
the product measure. So for a function `Ψ` on `α × α` invariant under the diagonal action,
`∫_{D × α} Ψ(z, w) = ∫_{D × α} Ψ(w, z)`. This is the symmetry of a kernel operator with an invariant
kernel on `L²(G \ α)` (the symmetry of point-pair invariants on `Γ \ ℍ`).

## Main results

* `MeasureTheory.IsFundamentalDomain.prod_univ`, `MeasureTheory.IsFundamentalDomain.univ_prod`: the
  fundamental domains of the diagonal action.
* `MeasureTheory.IsFundamentalDomain.integral_prod_swap_eq`,
  `MeasureTheory.IsFundamentalDomain.lintegral_prod_swap_eq`: the symmetry of the integrals of an
  invariant function.
-/

open Set

open scoped ENNReal Pointwise

namespace MeasureTheory

variable {G α E : Type*} [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α} [SFinite μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {D : Set α}

instance [MeasurableConstSMul G α] : MeasurableConstSMul G (α × α) :=
  ⟨fun g ↦ (measurable_const_smul g).prodMap (measurable_const_smul g)⟩

instance [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] :
    SMulInvariantMeasure G (α × α) (μ.prod μ) :=
  ⟨fun g _ hs ↦ ((measurePreserving_smul g μ).prod (measurePreserving_smul g μ)).measure_preimage
    hs.nullMeasurableSet⟩

/-- **`D × α` is a fundamental domain of the diagonal action** on `α × α`, for a fundamental domain
`D` of the action on `α`. -/
lemma IsFundamentalDomain.prod_univ (hD : IsFundamentalDomain G D μ) :
    IsFundamentalDomain G (D ×ˢ (univ : Set α)) (μ.prod μ) where
  nullMeasurableSet := hD.nullMeasurableSet.prod nullMeasurableSet_univ
  ae_covers := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hD.ae_covers] with p hp
    rcases hp with ⟨g, hg⟩
    exact ⟨g, hg, mem_univ _⟩
  aedisjoint := fun g h hgh ↦ by
    have h0 : μ ((g • D) ∩ (h • D)) = 0 := hD.aedisjoint hgh
    have h1 : (g • (D ×ˢ (univ : Set α))) ∩ (h • (D ×ˢ (univ : Set α))) =
        ((g • D) ∩ (h • D)) ×ˢ (univ : Set α) := by
      rw [smul_set_prod, smul_set_prod, smul_set_univ, smul_set_univ, prod_inter_prod, inter_self]
    have h2 : (μ.prod μ) ((g • (D ×ˢ (univ : Set α))) ∩ (h • (D ×ˢ (univ : Set α)))) = 0 := by
      rw [h1, Measure.prod_prod, h0, zero_mul]
    exact h2

/-- **`α × D` is a fundamental domain of the diagonal action** on `α × α`, for a fundamental domain
`D` of the action on `α`. -/
lemma IsFundamentalDomain.univ_prod (hD : IsFundamentalDomain G D μ) :
    IsFundamentalDomain G ((univ : Set α) ×ˢ D) (μ.prod μ) where
  nullMeasurableSet := nullMeasurableSet_univ.prod hD.nullMeasurableSet
  ae_covers := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hD.ae_covers] with p hp
    rcases hp with ⟨g, hg⟩
    exact ⟨g, mem_univ _, hg⟩
  aedisjoint := fun g h hgh ↦ by
    have h0 : μ ((g • D) ∩ (h • D)) = 0 := hD.aedisjoint hgh
    have h1 : (g • ((univ : Set α) ×ˢ D)) ∩ (h • ((univ : Set α) ×ˢ D)) =
        (univ : Set α) ×ˢ ((g • D) ∩ (h • D)) := by
      rw [smul_set_prod, smul_set_prod, smul_set_univ, smul_set_univ, prod_inter_prod, inter_self]
    have h2 : (μ.prod μ) ((g • ((univ : Set α) ×ˢ D)) ∩ (h • ((univ : Set α) ×ˢ D))) = 0 := by
      rw [h1, Measure.prod_prod, h0, mul_zero]
    exact h2

variable (μ D) in
lemma prod_restrict_univ_left :
    (μ.restrict D).prod μ = (μ.prod μ).restrict (D ×ˢ (univ : Set α)) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

variable (μ D) in
lemma prod_restrict_univ_right :
    μ.prod (μ.restrict D) = (μ.prod μ).restrict ((univ : Set α) ×ˢ D) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

variable [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] [Countable G]

/-- **The swap of an invariant function on the product of a fundamental domain with the whole
space**: for `Ψ` on `α × α` invariant under the diagonal action of `G` and a fundamental domain `D`
of `G`, `∫_{D × α} Ψ(z, w) = ∫_{D × α} Ψ(w, z)`, the sets `D × α` and `α × D` being fundamental
domains of the diagonal action. -/
lemma IsFundamentalDomain.integral_prod_swap_eq (hD : IsFundamentalDomain G D μ) {Ψ : α × α → E}
    (hΨ : ∀ (g : G) (p : α × α), Ψ (g • p) = Ψ p) :
    ∫ p, Ψ p ∂(μ.restrict D).prod μ = ∫ p, Ψ p.swap ∂(μ.restrict D).prod μ := by
  rw [integral_prod_swap, prod_restrict_univ_left, prod_restrict_univ_right]
  exact hD.prod_univ.setIntegral_eq hD.univ_prod hΨ

/-- **The swap of an invariant function, for the lower integral**: for `Ψ` on `α × α` with values
in `[0, ∞]`, invariant under the diagonal action of `G`, and a fundamental domain `D` of `G`,
`∫⁻_{D × α} Ψ(z, w) = ∫⁻_{D × α} Ψ(w, z)`. -/
lemma IsFundamentalDomain.lintegral_prod_swap_eq (hD : IsFundamentalDomain G D μ) {Ψ : α × α → ℝ≥0∞}
    (hΨ : ∀ (g : G) (p : α × α), Ψ (g • p) = Ψ p) :
    ∫⁻ p, Ψ p ∂(μ.restrict D).prod μ = ∫⁻ p, Ψ p.swap ∂(μ.restrict D).prod μ := by
  rw [lintegral_prod_swap, prod_restrict_univ_left, prod_restrict_univ_right]
  exact hD.prod_univ.setLIntegral_eq hD.univ_prod Ψ hΨ

end MeasureTheory
