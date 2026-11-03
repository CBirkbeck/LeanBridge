import LeanBridge.ForMathlib.MeasureTheory.Group.FundamentalDomainUnfolding
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals over fundamental domains, by covers and by averaging

Let a countable group `G` act measurably on `X`, preserving a measure `μ`, and let `s` be a
fundamental domain. For an invariant function `f ≥ 0` and a set `t` meeting almost every orbit,
`∫_s f ≤ ∫_t f`: an integral over a fundamental domain can be bounded over any cover, such as a
Siegel set, which is not a fundamental domain. If `H ≤ G` is a subgroup with right transversal
`(r_i)`, an `H`-invariant function `φ` is integrable on a fundamental domain of `H` as soon as
`∫_t ∑_i |φ(r_i x)| < ∞`, which is the integrability needed to unfold.

For a transformation `k` conjugating a subgroup `H` to a subgroup `H'`,
`∫_s ∑_i φ(k r_i x) = ∫_s ∑_j φ(r'_j x)` for transversals `(r_i)` of `H` and `(r'_j)` of `H'`: this
is how a Hecke operator moves across the Petersson product.

Finally, if `(T_u)_{u ∈ [0, 1]}` are measure-preserving transformations with `T_u s` a fundamental
domain for every `u`, and `φ` is an invariant function, integrable on `s`, with
`∫_0^1 φ(T_u x) du = 0` for all `x`, then `∫_s φ = 0`: integrating over `u` and exchanging the
integrals. This is how the Petersson product of an Eisenstein series with a cusp form vanishes.

## Main results

* `MeasureTheory.IsFundamentalDomain.setLIntegral_le_of_ae_exists_smul_mem`: `∫_s f ≤ ∫_t f` for a
  cover `t`.
* `MeasureTheory.IsFundamentalDomain.integrableOn_of_setLIntegral_lt_top`: integrability on `s` from
  integrability on a cover.
* `MeasureTheory.IsFundamentalDomain.integrableOn_of_setLIntegral_tsum_lt_top`: integrability on a
  fundamental domain of a subgroup, from the convergence of the periodisation on a cover.
* `MeasureTheory.IsFundamentalDomain.smul_of_forall_smul_comm`: a measure-preserving transformation
  commuting with `G` maps fundamental domains of `G` to fundamental domains of `G`.
* `MeasureTheory.IsFundamentalDomain.setIntegral_tsum_smul_smul_eq`: the transfer along a
  transformation conjugating two subgroups.
* `MeasureTheory.IsFundamentalDomain.setIntegral_eq_zero_of_average`: the vanishing by averaging.
-/

open Function Set

open scoped ENNReal Pointwise

namespace MeasureTheory.IsFundamentalDomain

variable {G X E ι K : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
    {s t : Set X} [NormedAddCommGroup E] [Group K] [MulAction K X] [MeasurableConstSMul K X]
    [SMulInvariantMeasure K X μ] {k : K}

/-- A measure-preserving transformation commuting with `G` maps fundamental domains of `G` to
fundamental domains of `G`. -/
lemma smul_of_forall_smul_comm (hs : IsFundamentalDomain G s μ)
    (hk : ∀ (g : G) (x : X), k • g • x = g • k • x) : IsFundamentalDomain G (k • s) μ :=
  hs.image_of_equiv (MulAction.toPerm k) (measurePreserving_smul k⁻¹ μ).quasiMeasurePreserving
    (Equiv.refl G) fun g x ↦ hk g x

variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]

/-- **An integral over a fundamental domain is bounded by the integral over a cover**: for an
invariant `f ≥ 0` and a set `t` meeting almost every orbit, `∫_s f ≤ ∫_t f`. -/
lemma setLIntegral_le_of_ae_exists_smul_mem (hs : IsFundamentalDomain G s μ) {f : X → ℝ≥0∞}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) (ht : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ t) :
    ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ := by
  rw [hs.setLIntegral_eq_tsum' f t]
  simp only [hf]
  refine (lintegral_mono_set' ?_).trans (lintegral_iUnion_le _ _)
  filter_upwards [ht] with x hx hxs
  rcases hx with ⟨g, hg⟩
  exact mem_iUnion.mpr ⟨g⁻¹, by
    rwa [mem_inv_smul_set_iff], hxs⟩

/-- **Integrability on a fundamental domain from integrability on a cover**: a measurable function
with invariant norm is integrable on a fundamental domain if it is integrable on a set meeting
almost every orbit. -/
lemma integrableOn_of_setLIntegral_lt_top (hs : IsFundamentalDomain G s μ) {f : X → E}
    (hm : AEStronglyMeasurable f (μ.restrict s)) (hf : ∀ (g : G) (x : X), ‖f (g • x)‖ = ‖f x‖)
    (ht : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ t) (hfin : ∫⁻ x in t, ‖f x‖ₑ ∂μ < ∞) : IntegrableOn f s μ :=
  ⟨hm, (hs.setLIntegral_le_of_ae_exists_smul_mem (fun g x ↦ by
    rw [← ofReal_norm, ← ofReal_norm, hf]) ht).trans_lt hfin⟩

variable [Countable ι] {H : Subgroup G} {F : Set X} {r : ι → G} {φ : X → E}

/-- **Integrability on a fundamental domain of a subgroup**: if `H ≤ G` has right transversal
`(r_i)` and `t` meets almost every orbit of `G`, an `H`-invariant `φ` is integrable on a fundamental
domain of `H` as soon as `∫_t ∑_i |φ(r_i x)| < ∞`. -/
lemma integrableOn_of_setLIntegral_tsum_lt_top (hF : IsFundamentalDomain H F μ)
    (hr : Surjective fun i ↦ (QuotientGroup.mk (r i)⁻¹ : G ⧸ H))
    (hm : AEStronglyMeasurable φ (μ.restrict F)) (hmt : ∀ i, AEMeasurable (fun x ↦ ‖φ (r i • x)‖ₑ)
      (μ.restrict t)) (hφ : ∀ (h : H) (x : X), φ (h • x) = φ x) (ht : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ t)
    (hfin : ∫⁻ x in t, ∑' i, ‖φ (r i • x)‖ₑ ∂μ < ∞) : IntegrableOn φ F μ := by
  have hcover : ∀ᵐ x ∂μ, ∃ h : H, h • x ∈ ⋃ i, r i • t := by
    filter_upwards [ht] with x hx
    rcases hx with ⟨g, hg⟩
    rcases hr (QuotientGroup.mk g) with ⟨i, hi⟩
    have hmem : (r i) * g ∈ H := by
      have h₁ : ((r i)⁻¹ : G)⁻¹ * g ∈ H := QuotientGroup.eq.mp hi
      rwa [inv_inv] at h₁
    refine ⟨⟨(r i) * g, hmem⟩, mem_iUnion.mpr ⟨i, ?_⟩⟩
    rw [Submonoid.mk_smul, mul_smul]
    exact smul_mem_smul_set hg
  refine integrableOn_of_setLIntegral_lt_top hF hm (fun h x ↦ by rw [hφ]) hcover ?_
  refine (lt_of_le_of_lt ?_ hfin)
  refine (lintegral_iUnion_le _ _).trans ?_
  rw [lintegral_tsum hmt]
  refine ENNReal.tsum_le_tsum fun i ↦ ?_
  rw [(measurePreserving_smul (r i) μ).setLIntegral_comp_emb
    (measurableEmbedding_const_smul (r i)) (fun x ↦ ‖φ x‖ₑ) t, image_smul]

/-- **Transfer along a transformation conjugating two subgroups**: let `k` be a measure-preserving
transformation with `k H k⁻¹ = H'`, for subgroups `H, H'` of `G` with right transversals `(r_i)` and
`(r'_j)`. For an `H'`-invariant `φ`, integrable on a fundamental domain of `H'`, and a fundamental
domain `s` of `G`, `∫_s ∑_i φ(k r_i x) = ∫_s ∑_j φ(r'_j x)`: both are the integral of `φ` over a
fundamental domain of `H'`. This is how a Hecke operator moves across the Petersson product. -/
lemma setIntegral_tsum_smul_smul_eq [NormedSpace ℝ E] {ι' : Type*} [Countable ι'] {H' : Subgroup G}
    {r' : ι' → G} (hs : IsFundamentalDomain G s μ) (hF : IsFundamentalDomain H' F μ)
    (hr : Bijective fun i ↦ (QuotientGroup.mk (r i)⁻¹ : G ⧸ H))
    (hr' : Bijective fun j ↦ (QuotientGroup.mk (r' j)⁻¹ : G ⧸ H')) (e : H ≃ H')
    (he : ∀ (h : H) (x : X), k • h • x = e h • k • x) (hφ : ∀ (h : H') (x : X), φ (h • x) = φ x)
    (hφF : IntegrableOn φ F μ) :
    ∫ x in s, ∑' i, φ (k • r i • x) ∂μ = ∫ x in s, ∑' j, φ (r' j • x) ∂μ := by
  have hF₁ : IsFundamentalDomain H ((fun x ↦ k • x) ⁻¹' F) μ := by
    rw [preimage_smul]
    exact hF.image_of_equiv (MulAction.toPerm k⁻¹)
      (measurePreserving_smul (k⁻¹)⁻¹ μ).quasiMeasurePreserving e fun h x ↦ by
        have h₂ : k • h • k⁻¹ • x = e h • k • k⁻¹ • x := he h (k⁻¹ • x)
        rw [smul_inv_smul] at h₂
        simp only [MulAction.toPerm_apply]
        rw [← h₂, inv_smul_smul]
  have hint : IntegrableOn (fun x ↦ φ (k • x)) ((fun x ↦ k • x) ⁻¹' F) μ :=
    ((measurePreserving_smul k μ).integrableOn_comp_preimage
      (measurableEmbedding_const_smul k)).mpr hφF
  rw [hs.setIntegral_tsum_smul_eq hF₁ hr (φ := fun x ↦ φ (k • x)) (fun h x ↦ by rw [he, hφ]) hint,
    hs.setIntegral_tsum_smul_eq hF hr' hφ hφF]
  exact (measurePreserving_smul k μ).setIntegral_preimage_emb (measurableEmbedding_const_smul k) φ F

private lemma setIntegral_smul_eq {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {g : X → F'} (hg : ∀ (h : G) (x : X), g (h • x) = g x) (hs : IsFundamentalDomain G s μ)
    (hk : IsFundamentalDomain G (k • s) μ) : ∫ x in s, g (k • x) ∂μ = ∫ x in s, g x ∂μ := by
  rw [← (measurePreserving_smul k μ).setIntegral_image_emb (measurableEmbedding_const_smul k) g s,
    image_smul]
  exact hk.setIntegral_eq hs hg

variable [NormedSpace ℝ E] [CompleteSpace E] [SFinite μ] {c : ℝ → K} {f : X → E}

/-- **Vanishing by averaging**: if `T_u = c u` are measure-preserving and `T_u s` is a fundamental
domain for every `u ∈ [0, 1]`, an invariant function `f`, integrable on `s`, with
`∫_0^1 f(T_u x) du = 0` for all `x`, has `∫_s f = 0`: for each `u`,
`∫_s f(T_u x) dμ = ∫_s f dμ`, and the integrals over `u` and `x` can be exchanged. -/
lemma setIntegral_eq_zero_of_average (hs : IsFundamentalDomain G s μ)
    (hc : ∀ u ∈ Icc (0 : ℝ) 1, IsFundamentalDomain G (c u • s) μ)
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) (hfs : IntegrableOn f s μ)
    (hm : AEStronglyMeasurable (fun p : ℝ × X ↦ f (c p.1 • p.2))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (μ.restrict s)))
    (h₀ : ∀ x, ∫ u in Icc (0 : ℝ) 1, f (c u • x) = 0) : ∫ x in s, f x ∂μ = 0 := by
  have hint (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : IntegrableOn (fun x ↦ f (c u • x)) s μ := by
    have h₁ : IntegrableOn f (c u • s) μ := ((hc u hu).integrableOn_iff hs hf).mpr hfs
    rw [← image_smul] at h₁
    exact ((measurePreserving_smul (c u) μ).integrableOn_image
      (measurableEmbedding_const_smul (c u))).mp h₁
  have hprod : Integrable (fun p : ℝ × X ↦ f (c p.1 • p.2))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (μ.restrict s)) := by
    refine (integrable_prod_iff hm).mpr ⟨(ae_restrict_iff' measurableSet_Icc).mpr
      (ae_of_all _ fun u hu ↦ hint u hu), ?_⟩
    have hconst : IntegrableOn (fun _ : ℝ ↦ ∫ x in s, ‖f x‖ ∂μ) (Icc (0 : ℝ) 1) :=
      integrableOn_const (by simp) (by simp)
    refine hconst.congr_fun (fun u hu ↦ ?_) measurableSet_Icc
    exact (setIntegral_smul_eq (g := fun x ↦ ‖f x‖) (fun h x ↦ by rw [hf]) hs (hc u hu)).symm
  have hswap : ∫ u in Icc (0 : ℝ) 1, ∫ x in s, f (c u • x) ∂μ =
      ∫ x in s, (∫ u in Icc (0 : ℝ) 1, f (c u • x)) ∂μ :=
    integral_integral_swap (f := fun u x ↦ f (c u • x)) hprod
  have hL : ∫ u in Icc (0 : ℝ) 1, ∫ x in s, f (c u • x) ∂μ = ∫ x in s, f x ∂μ := by
    rw [setIntegral_congr_fun measurableSet_Icc fun u hu ↦ setIntegral_smul_eq hf hs (hc u hu),
      setIntegral_const]
    simp
  rw [← hL, hswap]
  simp [h₀]

end MeasureTheory.IsFundamentalDomain
