import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.FourierInversion
import Mathlib.RingTheory.Complex

/-!
# The lattices `σ(t𝒪_K)` of an imaginary quadratic field

Let `K` be an imaginary quadratic field, embedded in `ℂ` by `σ`. For `0 ≠ t ∈ K`, the additive
subgroup `σ(t𝒪_K)` of `ℂ` (`bianchiScaledLattice`) is a lattice, with a bounded fundamental domain
(`exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice`). The fundamental domains transform
under the affine maps `x ↦ τx + b` (`isAddFundamentalDomain_image_mul_add`), with the change of
variables `∫_{τP + b} h = |τ|² ∫_P h(τx + b) dx` (`setIntegral_image_mul_add`). For a function `h`
which is periodic for `σ(t𝒪_K)` and `0 ≠ w ∈ 𝒪_K`, the integral of `h` over a fundamental domain of
`σ(tw𝒪_K)` is `|𝒪_K / (w)|` times its integral over a fundamental domain of `σ(t𝒪_K)`
(`setIntegral_bianchiScaledLattice_mul`), so that the vanishing of the mean of `h` does not depend
on the lattice of periods.

## Main definitions

* `HyperbolicThreeSpace.bianchiScaledLattice`: the lattice `σ(t𝒪_K)`.

## Main results

* `HyperbolicThreeSpace.exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice`:
  `σ(t𝒪_K)` has a bounded fundamental domain.
* `HyperbolicThreeSpace.setIntegral_image_mul_add`: the change of variables `x ↦ τx + b`.
* `HyperbolicThreeSpace.isAddFundamentalDomain_image_mul_add`: fundamental domains under the affine
  maps `x ↦ τx + b`.
* `HyperbolicThreeSpace.isAddFundamentalDomain_iUnion_vadd`: the tiling of a fundamental domain of a
  subgroup by translates of a fundamental domain.
* `HyperbolicThreeSpace.setIntegral_iUnion_vadd`: the integral over such a tiling.
* `HyperbolicThreeSpace.map_mul_add_volume`: the image of the Lebesgue measure under `x ↦ τx + b`.
* `HyperbolicThreeSpace.setIntegral_bianchiScaledLattice_mul`: the comparison of the means of a
  periodic function on two lattices of periods.
-/

open Bornology Complex Ideal MeasureTheory Module NumberField Set

open Ideal renaming Quotient.mk → quotientMk

open scoped Pointwise

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] (σ : K →+* ℂ) {t : K} {τ : ℂ}

variable (t) in
/-- The additive subgroup `σ(t𝒪_K)` of `ℂ`, for `t ∈ K`: a lattice for `K` imaginary quadratic and
`t ≠ 0`. -/
def bianchiScaledLattice : AddSubgroup ℂ :=
  AddMonoidHom.range <| (σ : K →+ ℂ).comp <| (AddMonoidHom.mulLeft t).comp
    (algebraMap (𝓞 K) K : 𝓞 K →+ K)

variable {σ}

lemma mem_bianchiScaledLattice {l : ℂ} : l ∈ bianchiScaledLattice σ t ↔ ∃ a : 𝓞 K, σ (t * a) = l :=
  Iff.rfl

variable (σ t) in
lemma apply_mul_mem_bianchiScaledLattice (a : 𝓞 K) : σ (t * a) ∈ bianchiScaledLattice σ t :=
  ⟨a, rfl⟩

lemma bianchiScaledLattice_mul_le (w : 𝓞 K) :
    bianchiScaledLattice σ (t * w) ≤ bianchiScaledLattice σ t := by
  rintro _ ⟨a, rfl⟩
  exact ⟨w * a, by simp [mul_assoc]⟩

/-- The map `x ↦ τx + b` of `ℂ`, for `τ ≠ 0`, as a bijection. -/
private noncomputable def mulAddEquiv (hτ : τ ≠ 0) (b : ℂ) : ℂ ≃ ℂ where
  toFun x := τ * x + b
  invFun x := τ⁻¹ * (x - b)
  left_inv x := by
    simp [hτ]
  right_inv x := by
    simp [hτ]

private lemma measurableEmbedding_mul_add (hτ : τ ≠ 0) (b : ℂ) :
    MeasurableEmbedding fun x : ℂ ↦ τ * x + b :=
  (Homeomorph.mk (mulAddEquiv hτ b) (by unfold mulAddEquiv; fun_prop)
    (by unfold mulAddEquiv; fun_prop)).measurableEmbedding

private lemma det_mulLeft : LinearMap.det (Algebra.lmul ℝ ℂ τ) = normSq τ := by
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply]

/-- The Lebesgue measure of `ℂ` under the affine map `x ↦ τx + b`, `τ ≠ 0`. -/
lemma map_mul_add_volume (hτ : τ ≠ 0) (b : ℂ) :
    Measure.map (fun x : ℂ ↦ τ * x + b) volume = ENNReal.ofReal (normSq τ)⁻¹ • volume := by
  have hdet : LinearMap.det (Algebra.lmul ℝ ℂ τ) ≠ 0 := by
    rw [det_mulLeft]
    exact normSq_eq_zero.not.mpr hτ
  have h₁ : Measure.map (fun x : ℂ ↦ τ * x) volume = ENNReal.ofReal (normSq τ)⁻¹ • volume := by
    have h : Measure.map (Algebra.lmul ℝ ℂ τ) volume =
      ENNReal.ofReal |(LinearMap.det (Algebra.lmul ℝ ℂ τ))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hdet
    rw [det_mulLeft, abs_of_nonneg (inv_nonneg.mpr (normSq_nonneg τ))] at h
    exact h
  have h₂ : (fun x : ℂ ↦ τ * x + b) = (· + b) ∘ fun x : ℂ ↦ τ * x :=
    rfl
  rw [h₂, ← Measure.map_map (by fun_prop) (by fun_prop), h₁, Measure.map_smul,
    (measurePreserving_add_right volume b).map_eq]
  fun_prop

variable {Λ Λ' : AddSubgroup ℂ} {P P' : Set ℂ} {V : Type*} [NormedAddCommGroup V] {h : ℂ → V}

variable [NormedSpace ℝ V] (h P) in
/-- **The change of variables `x ↦ τx + b`**: for `τ ≠ 0` and any function `h` and subset `P` of
`ℂ`, `∫_{τP + b} h = |τ|² ∫_P h(τx + b) dx`. -/
lemma setIntegral_image_mul_add (hτ : τ ≠ 0) (b : ℂ) :
    ∫ x in (fun x ↦ τ * x + b) '' P, h x = normSq τ • ∫ x in P, h (τ * x + b) := by
  have hn : 0 < normSq τ := normSq_pos.mpr hτ
  have hm : MeasurableEmbedding fun x : ℂ ↦ τ * x + b := measurableEmbedding_mul_add hτ b
  have h₁ : ∫ y in (fun x ↦ τ * x + b) '' P, h y ∂Measure.map (fun x ↦ τ * x + b) volume =
      ∫ x in (fun x ↦ τ * x + b) ⁻¹' ((fun x ↦ τ * x + b) '' P), h (τ * x + b) :=
    hm.setIntegral_map (μ := volume) h ((fun x ↦ τ * x + b) '' P)
  rw [preimage_image_eq _ hm.injective, map_mul_add_volume hτ b, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hn.le)] at h₁
  rw [← h₁, smul_inv_smul₀ hn.ne']

/-- **Fundamental domains under the affine maps**: if `P` is a fundamental domain of an additive
subgroup `Λ` of `ℂ` and `τ ≠ 0`, then `τP + b` is a fundamental domain of `τΛ`. -/
lemma isAddFundamentalDomain_image_mul_add (hP : IsAddFundamentalDomain Λ P volume) (hτ : τ ≠ 0)
    (b : ℂ) (hΛ' : ∀ l, l ∈ Λ' ↔ τ⁻¹ * l ∈ Λ) :
    IsAddFundamentalDomain Λ' ((fun x ↦ τ * x + b) '' P) volume := by
  let e : Λ' ≃ Λ :=
    { toFun := fun l ↦ ⟨τ⁻¹ * l, (hΛ' l).mp l.2⟩
      invFun := fun l ↦ ⟨τ * l, (hΛ' _).mpr (by simp [hτ])⟩
      left_inv := fun l ↦ Subtype.ext (by simp [hτ])
      right_inv := fun l ↦ Subtype.ext (by simp [hτ]) }
  have hq : QuasiMeasurePreserving (mulAddEquiv hτ b).symm volume volume := by
    have hτ' : τ⁻¹ ≠ 0 := inv_ne_zero hτ
    have h₁ : ((mulAddEquiv hτ b).symm : ℂ → ℂ) = fun x ↦ τ⁻¹ * x + -(τ⁻¹ * b) := by
      funext x
      simp only [mulAddEquiv, Equiv.coe_fn_symm_mk]
      ring1
    rw [h₁]
    refine ⟨(measurableEmbedding_mul_add hτ' _).measurable, ?_⟩
    rw [map_mul_add_volume hτ']
    exact Measure.smul_absolutelyContinuous
  refine hP.image_of_equiv (mulAddEquiv hτ b) hq e fun l x ↦ ?_
  simp only [mulAddEquiv, e, Equiv.coe_fn_mk, AddSubgroup.vadd_def, vadd_eq_add]
  field_simp
  ring1

/-- **The tiling of a fundamental domain of a subgroup**: if `P` is a fundamental domain of an
additive subgroup `Λ` of `ℂ`, `Λ' ≤ Λ` and `(rᵢ)` is a family of elements of `Λ` meeting every coset
of `Λ'` in `Λ` exactly once, then `⋃ᵢ (rᵢ + P)` is a fundamental domain of `Λ'`. -/
lemma isAddFundamentalDomain_iUnion_vadd (hP : IsAddFundamentalDomain Λ P volume) {ι : Type*}
    [Countable ι] {r : ι → ℂ} (hr : ∀ i, r i ∈ Λ) (hcov : ∀ l ∈ Λ, ∃ i, l - r i ∈ Λ')
    (hinj : ∀ i j, r i - r j ∈ Λ' → i = j) (hle : Λ' ≤ Λ) :
    IsAddFundamentalDomain Λ' (⋃ i, r i +ᵥ P) volume where
  nullMeasurableSet := .iUnion fun i ↦ (hP.vadd_of_comm (r i)).nullMeasurableSet
  ae_covers := by
    filter_upwards [hP.ae_covers] with x hx
    rcases hx with ⟨g, hg⟩
    rcases hcov (-g) (neg_mem g.2) with ⟨i, hi⟩
    have hm : (g : ℂ) + r i ∈ Λ' := by
      simpa [add_comm] using neg_mem hi
    refine ⟨⟨_, hm⟩, mem_iUnion.mpr ⟨i, ?_⟩⟩
    refine ⟨(g : ℂ) + x, hg, ?_⟩
    simp only [AddSubgroup.vadd_def, vadd_eq_add]
    ring1
  aedisjoint l l' hll' := by
    simp only [vadd_set_iUnion, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff]
    intro j i
    have hne :
        (⟨l + r i, add_mem (hle l.2) (hr i)⟩ : Λ) ≠ ⟨l' + r j, add_mem (hle l'.2) (hr j)⟩ := by
      intro he
      have he' : (l : ℂ) + r i = l' + r j := congrArg Subtype.val he
      have hm : r i - r j ∈ Λ' := by
        have h₁ : r i - r j = (l' : ℂ) - l := by
          linear_combination he'
        rw [h₁]
        exact sub_mem l'.2 l.2
      have hij : i = j := hinj i j hm
      subst hij
      exact hll' (Subtype.ext (add_right_cancel he'))
    simpa only [AddSubgroup.vadd_def, vadd_vadd] using hP.aedisjoint hne

variable [NormedSpace ℝ V] in
/-- **The integral over a tiling**: under the hypotheses of `isAddFundamentalDomain_iUnion_vadd`,
for a function `h` which is periodic for `Λ`, integrable on the tiling `⋃ᵢ (rᵢ + P)`, indexed by a
finite type,`∫_{⋃ᵢ (rᵢ + P)} h = n ∫_P h`, for `n` the number of the `rᵢ`. -/
lemma setIntegral_iUnion_vadd [Countable Λ] (hP : IsAddFundamentalDomain Λ P volume) {ι : Type*}
    [Fintype ι] {r : ι → ℂ} (hr : ∀ i, r i ∈ Λ) (hne : Function.Injective r)
    (hper : ∀ l ∈ Λ, ∀ x, h (l + x) = h x) (hh : IntegrableOn h (⋃ i, r i +ᵥ P) volume) :
    ∫ x in ⋃ i, r i +ᵥ P, h x = Fintype.card ι • ∫ x in P, h x := by
  have hm (i : ι) : NullMeasurableSet (r i +ᵥ P) volume :=
    (hP.vadd_of_comm (r i)).nullMeasurableSet
  have hd : Pairwise (Function.onFun (AEDisjoint volume) fun i ↦ r i +ᵥ P) := fun i j hij ↦ by
    have hne' : (⟨r i, hr i⟩ : Λ) ≠ ⟨r j, hr j⟩ := fun he ↦ hij (hne (congrArg Subtype.val he))
    exact hP.aedisjoint hne'
  have hi (i : ι) : ∫ x in r i +ᵥ P, h x = ∫ x in P, h x :=
    (hP.vadd_of_comm (r i)).setIntegral_eq hP fun l x ↦ hper l l.2 x
  rw [integral_iUnion_ae hm hd hh, tsum_fintype, Finset.sum_congr rfl fun i _ ↦ hi i,
    Finset.sum_const, Finset.card_univ]

variable [NumberField K]

instance : Countable (𝓞 K) :=
  (RingOfIntegers.basis K).equivFun.injective.countable

instance : Countable (bianchiScaledLattice σ t) :=
  (Set.countable_range _).to_subtype

lemma map_mem_span_integralLatticeBasis {x : K} (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (a : 𝓞 K) : σ a ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)) := by
  have h : σ a = ∑ i, (RingOfIntegers.basis K).repr a i • σ (RingOfIntegers.basis K i) := by
    have h' : σ ((∑ i, (RingOfIntegers.basis K).repr a i • RingOfIntegers.basis K i : 𝓞 K) : K) =
        σ a := by
      rw [(RingOfIntegers.basis K).sum_repr a]
    rw [← h']
    simp
  rw [h]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, integralLatticeBasis_apply hK hx i⟩)

lemma toAddSubgroup_span_integralLatticeBasis {x : K} (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) :
    (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))).toAddSubgroup =
      bianchiScaledLattice σ 1 := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_int_eq_addSubgroupClosure, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [integralLatticeBasis_apply]
    exact ⟨RingOfIntegers.basis K i, by simp⟩
  · rintro _ ⟨a, rfl⟩
    have h : (σ (1 * (a : K))) = σ a := by
      rw [one_mul]
    exact h ▸ map_mem_span_integralLatticeBasis hK hx a

lemma isAddFundamentalDomain_bianchiScaledLattice_one {x : K} (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0) : IsAddFundamentalDomain (bianchiScaledLattice σ 1)
      (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) volume :=
  toAddSubgroup_span_integralLatticeBasis hK hx ▸ ZSpan.isAddFundamentalDomain' _ _

lemma coe_mem_bianchiScaledLattice_one {x : K} (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (v : Submodule.span ℤ (range (integralLatticeBasis σ hK hx))) :
    (v : ℂ) ∈ bianchiScaledLattice σ 1 :=
  toAddSubgroup_span_integralLatticeBasis hK hx ▸ v.2

variable [IsTotallyComplex K]

/-- **`σ(t𝒪_K)` has a bounded fundamental domain**: for an imaginary quadratic field `K` and
`t ≠ 0`, the image under `x ↦ σ(t)x` of the fundamental parallelogram of `σ(𝒪_K)`. -/
lemma exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice (hK : finrank ℚ K = 2)
    (ht : t ≠ 0) :
    ∃ P : Set ℂ, IsBounded P ∧ IsAddFundamentalDomain (bianchiScaledLattice σ t) P volume := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hσt : σ t ≠ 0 := (map_ne_zero σ).mpr ht
  refine ⟨(fun z ↦ σ t * z + 0) '' ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx), ?_,
    isAddFundamentalDomain_image_mul_add (isAddFundamentalDomain_bianchiScaledLattice_one hK hx)
      hσt 0 fun l ↦ ?_⟩
  · have hb : IsBounded (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) :=
      ZSpan.fundamentalDomain_isBounded _
    exact (hb.isCompact_closure.image (by fun_prop)).isBounded.subset (image_mono subset_closure)
  · refine ⟨fun hl ↦ ?_, fun hl ↦ ?_⟩
    · rcases mem_bianchiScaledLattice.mp hl with ⟨a, rfl⟩
      exact mem_bianchiScaledLattice.mpr ⟨a, by simp [hσt]⟩
    · rcases mem_bianchiScaledLattice.mp hl with ⟨a, ha⟩
      refine mem_bianchiScaledLattice.mpr ⟨a, ?_⟩
      have ha' : σ a = (σ t)⁻¹ * l := by
        simpa using ha
      rw [map_mul, ha']
      field_simp

lemma integrableOn_of_continuous_of_periodic (hK : finrank ℚ K = 2) (ht : t ≠ 0) (hc : Continuous h)
    (hper : ∀ l ∈ bianchiScaledLattice σ t, ∀ x, h (l + x) = h x)
    (hP : IsAddFundamentalDomain (bianchiScaledLattice σ t) P volume) :
    IntegrableOn h P volume := by
  rcases exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice (σ := σ) hK ht with
    ⟨P₀, hb, hP₀⟩
  exact (hP₀.integrableOn_iff hP fun l x ↦ hper l l.2 x).mp <|
    (hc.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure

variable [NormedSpace ℝ V] in
/-- **The comparison of the means of a periodic function on two lattices of periods**: for an
imaginary quadratic field `K`, `0 ≠ t ∈ K`, `0 ≠ w ∈ 𝒪_K` and a continuous function `h` periodic for
`σ(t𝒪_K)`, the integral of `h` over a fundamental domain of `σ(tw𝒪_K)` is `|𝒪_K / (w)|` times its
integral over a fundamental domain of `σ(t𝒪_K)`. -/
lemma setIntegral_bianchiScaledLattice_mul (hK : finrank ℚ K = 2) (ht : t ≠ 0) {w : 𝓞 K}
    (hw : w ≠ 0) (hc : Continuous h) (hper : ∀ l ∈ bianchiScaledLattice σ t, ∀ x, h (l + x) = h x)
    (hP : IsAddFundamentalDomain (bianchiScaledLattice σ t) P volume)
    (hP' : IsAddFundamentalDomain (bianchiScaledLattice σ (t * w)) P' volume) :
    ∫ x in P', h x = Nat.card (𝓞 K ⧸ Ideal.span {w}) • ∫ x in P, h x := by
  have htw : t * (w : K) ≠ 0 := mul_ne_zero ht (RingOfIntegers.coe_ne_zero_iff.mpr hw)
  have hfin : Finite (𝓞 K ⧸ Ideal.span {w}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hw)
  let _ : Fintype (𝓞 K ⧸ Ideal.span {w}) := Fintype.ofFinite _
  let r : 𝓞 K ⧸ Ideal.span {w} → ℂ := fun i ↦ σ (t * (Quotient.out i : 𝓞 K))
  have hle : bianchiScaledLattice σ (t * w) ≤ bianchiScaledLattice σ t :=
    bianchiScaledLattice_mul_le w
  have hsub (a b : 𝓞 K) : σ (t * (a : K)) - σ (t * (b : K)) ∈ bianchiScaledLattice σ (t * w) ↔
      a - b ∈ Ideal.span {w} := by
    rw [Ideal.mem_span_singleton', mem_bianchiScaledLattice]
    refine ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← map_sub, ← mul_sub] at hc
      have h₁ : t * (w : K) * (c : K) = t * ((a : K) - (b : K)) := σ.injective hc
      have h₂ : ((w : K) * (c : K)) = (a : K) - (b : K) := by
        apply mul_left_cancel₀ ht
        rw [← mul_assoc]
        exact h₁
      apply RingOfIntegers.coe_injective
      push_cast
      rw [mul_comm, h₂]
    · rintro ⟨c, hc⟩
      have e : (w : K) * (c : K) = (a : K) - (b : K) := by
        have h₁ : ((c * w : 𝓞 K) : K) = ((a - b : 𝓞 K) : K) := congrArg _ hc
        push_cast at h₁
        rw [mul_comm]
        exact h₁
      refine ⟨c, ?_⟩
      rw [← map_sub, ← mul_sub, ← e, mul_assoc]
  have hU : IsAddFundamentalDomain (bianchiScaledLattice σ (t * w)) (⋃ i, r i +ᵥ P) volume := by
    refine isAddFundamentalDomain_iUnion_vadd hP
      (fun i ↦ apply_mul_mem_bianchiScaledLattice σ t _) (fun l hl ↦ ?_) (fun i j hij ↦ ?_) hle
    · rcases mem_bianchiScaledLattice.mp hl with ⟨a, rfl⟩
      refine ⟨quotientMk _ a, (hsub a _).mpr ?_⟩
      rw [← Quotient.mk_eq_mk_iff_sub_mem]
      exact (Quotient.out_eq (quotientMk (Ideal.span {w}) a)).symm
    · simpa using (Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ((hsub _ _).mp hij)
  rcases exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice (σ := σ) hK htw with
    ⟨P₀, hb, hP₀⟩
  have hper' (l : bianchiScaledLattice σ (t * w)) (x : ℂ) : h (l +ᵥ x) = h x :=
    hper l (hle l.2) x
  have hint : IntegrableOn h (⋃ i, r i +ᵥ P) volume :=
    (hP₀.integrableOn_iff hU hper').mp <| (hc.continuousOn.integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  have hr : Function.Injective r := fun i j hij ↦ by
    have h₁ : (Quotient.out i : 𝓞 K) = Quotient.out j :=
      RingOfIntegers.coe_injective (mul_left_cancel₀ ht (σ.injective hij))
    rw [← Quotient.out_eq i, h₁, Quotient.out_eq]
  rw [hP'.setIntegral_eq hU hper', setIntegral_iUnion_vadd hP
    (fun i ↦ apply_mul_mem_bianchiScaledLattice σ t _) hr hper hint, Nat.card_eq_fintype_card]

end HyperbolicThreeSpace
