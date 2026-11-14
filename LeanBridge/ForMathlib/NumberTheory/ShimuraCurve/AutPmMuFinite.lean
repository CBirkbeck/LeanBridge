import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EnhancedGroupTopology
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionTraceNorm

/-!
# The group `Aut_{±μ}(O)` of a polarized quaternion order is finite

Let `O` be an order of a quaternion algebra `B` over `ℚ` and let `μ ∈ B` have a square `μ² = m`
that is a negative rational number, for instance a polarization of `O` (LMFDB
`shimcurve.polarized_order`). Then `Aut_{±μ}(O) = {γ ∈ N_{B^×}(O)/ℚ^× : γ⁻¹ μ γ = ±μ}` (LMFDB
`shimcurve.aut_pm_mu_o`, `Subalgebra.autPmMu`) is a finite group.

An element `γ` of the normalizer `N_{B^×}(O)` that commutes with `μ` lies in `ℚ + ℚ μ`, the
centraliser of `μ`: `γ = s + t μ`. Conjugation by `γ` maps the lattice `O` onto itself, so its
trace on `B`, which is `trd(γ) trd(γ⁻¹) = trd(γ)² / nrd(γ) = 4 s² / (s² - m t²)`, is an integer
`c`; it lies in `[0, 4)` when `t ≠ 0`, and then `(4 - c) (s / t)² = -c m` leaves finitely many
values for `s / t`, which determines the class of `γ` modulo `ℚ^×`. The elements with
`γ⁻¹ μ γ = -μ` form at most one coset of those commuting with `μ`.

So the enhanced group `Aut_{±μ}(O) ⋉ Ô^×` of a polarized order of a quaternion algebra over `ℚ` is
compact for its topology (`Subalgebra.enhancedGroupTopology`): its open subgroups are its open
compact subgroups, the subgroups `H` defining the Shimura curves `X_H`, and they have finite index
(LMFDB `shimcurve.index`) and a positive level (LMFDB `shimcurve.level`).

## Main results

* `Subalgebra.exists_sq_reducedTrace_div_eq_intCast`: `trd(γ)² / nrd(γ)` is an integer for `γ` in
  the normalizer of an order.
* `Subalgebra.finite_autPmMu` (LMFDB `shimcurve.aut_pm_mu_o`): `Aut_{±μ}(O)` is finite for an order
  `O` of a quaternion algebra over `ℚ` and `μ` with `μ²` a negative rational number.
* `PolarizedQuaternionOrder.finite_autPmMu` (LMFDB `shimcurve.aut_pm_mu_o`): `Aut_{±μ}(O)` is
  finite for a polarized order `(O, μ)`.
* `PolarizedQuaternionOrder.compactSpace_enhancedGroup` (LMFDB `shimcurve.enhanced_group`): the
  enhanced group of a polarized order is compact.
* `PolarizedQuaternionOrder.isCompact_of_isOpen` (LMFDB `shimcurve.level`, `shimcurve.index`): its
  open subgroups are compact.
* `PolarizedQuaternionOrder.finiteIndex_of_isOpen` (LMFDB `shimcurve.index`): its open subgroups
  have finite index, so the index of a Shimura curve is a positive integer.
-/

open Module QuaternionAlgebra Topology

namespace Subalgebra

lemma finite_setOf_mul_sq_eq {a : ℚ} (ha : a ≠ 0) (q : ℚ) : {r : ℚ | a * r ^ 2 = q}.Finite := by
  by_cases h : ∃ r₀ : ℚ, a * r₀ ^ 2 = q
  · rcases h with ⟨r₀, rfl⟩
    exact ((Set.finite_singleton (-r₀)).insert r₀).subset fun r hr ↦
      sq_eq_sq_iff_eq_or_eq_neg.mp (mul_left_cancel₀ ha hr)
  · exact Set.finite_empty.subset fun r hr ↦ h ⟨r, hr⟩

lemma finite_setOf_exists_lt_four_mul_sq_eq (m : ℚ) :
    {r : ℚ | ∃ c : ℕ, c < 4 ∧ (4 - (c : ℚ)) * r ^ 2 = -(c * m)}.Finite := by
  have h : {r : ℚ | ∃ c : ℕ, c < 4 ∧ (4 - (c : ℚ)) * r ^ 2 = -(c * m)} =
      ⋃ c ∈ Set.Iio (4 : ℕ), {r : ℚ | (4 - (c : ℚ)) * r ^ 2 = -(c * m)} := by
    ext r
    simp
  rw [h]
  exact (Set.finite_Iio 4).biUnion fun c hc ↦
    finite_setOf_mul_sq_eq (sub_ne_zero.mpr (by exact_mod_cast (Set.mem_Iio.mp hc).ne')) _

variable {B : Type*} [Ring B] [Algebra ℚ B] [Algebra.IsCentral ℚ B] [IsSimpleRing B]
  {O : Subalgebra ℤ B} {μ : B} {m : ℚ} {γ : Bˣ}

/-- **`trd(γ)² / nrd(γ)` is an integer for `γ` in the normalizer of an order** of a quaternion
algebra over `ℚ`: it is the trace of the conjugation by `γ`, which maps the order onto itself. -/
lemma exists_sq_reducedTrace_div_eq_intCast (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder)
    (hγ : γ ∈ O.unitsNormalizer) :
    ∃ z : ℤ, reducedTrace B (γ : B) ^ 2 / reducedNorm B (γ : B) = z := by
  rcases exists_trace_eq_intCast h4 hO
    (LinearMap.mulLeft ℚ (γ : B) ∘ₗ LinearMap.mulRight ℚ (↑γ⁻¹ : B)) fun x hx ↦ by
      rw [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, ← mul_assoc]
      exact conj_mem_of_mem_unitsNormalizer hγ hx with ⟨z, hz⟩
  exact ⟨z, by
    rw [← hz, trace_mulLeft_comp_mulRight _ _ h4, reducedTrace_inv h4, sq, mul_div_assoc]⟩

lemma exists_lt_four_mul_sq_eq (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) (hm : m < 0)
    (hμ : μ * μ = algebraMap ℚ B m) (hγ : γ ∈ O.unitsNormalizer) {s t : ℚ} (ht : t ≠ 0)
    (hst : (γ : B) = algebraMap ℚ B s + t • μ) :
    ∃ c : ℕ, c < 4 ∧ (4 - (c : ℚ)) * (s / t) ^ 2 = -(c * m) := by
  rcases exists_sq_reducedTrace_div_eq_intCast h4 hO hγ with ⟨z, hz⟩
  have hmt : 0 < -m * t ^ 2 := mul_pos (neg_pos.mpr hm) (sq_pos_of_ne_zero ht)
  have hD : 0 < s ^ 2 - m * t ^ 2 := by
    nlinarith [sq_nonneg s]
  rw [hst, reducedTrace_add, reducedTrace_algebraMap _ h4, reducedTrace_smul,
    reducedTrace_eq_zero_of_mul_self_eq h4 hm hμ, mul_zero, add_zero,
    reducedNorm_algebraMap_add_smul h4 hm hμ, div_eq_iff hD.ne'] at hz
  have hz0 : (0 : ℚ) ≤ z := nonneg_of_mul_nonneg_left (hz ▸ sq_nonneg _) hD
  have hz4 : (z : ℚ) < 4 := lt_of_mul_lt_mul_right (by nlinarith) hD.le
  lift z to ℕ using by exact_mod_cast hz0
  refine ⟨z, by exact_mod_cast hz4, ?_⟩
  rw [Int.cast_natCast] at hz
  rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 ht)]
  linear_combination hz

lemma finite_image_mk_setOf_mul_comm (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) (hm : m < 0)
    (hμ : μ * μ = algebraMap ℚ B m) : (QuotientGroup.mk' O.normalizerRatUnits ''
      {γ : O.unitsNormalizer | ((γ : Bˣ) : B) * μ = μ * ((γ : Bˣ) : B)}).Finite := by
  classical
  let P : ℚ → O.unitsNormalizer → Prop := fun r δ ↦
    ∃ t : ℚ, t ≠ 0 ∧ ((δ : Bˣ) : B) = t • (algebraMap ℚ B r + μ)
  have hP (r : ℚ) (δ₁ δ₂ : O.unitsNormalizer) (h₁ : P r δ₁) (h₂ : P r δ₂) :
      QuotientGroup.mk' O.normalizerRatUnits δ₁ = QuotientGroup.mk' O.normalizerRatUnits δ₂ := by
    rcases h₁ with ⟨t₁, ht₁, h₁⟩
    rcases h₂ with ⟨t₂, ht₂, h₂⟩
    have h : ((δ₂ : Bˣ) : B) = (t₂ / t₁) • ((δ₁ : Bˣ) : B) := by
      rw [h₁, h₂, smul_smul, div_mul_cancel₀ _ ht₁]
    refine QuotientGroup.eq.mpr <| Subgroup.mem_subgroupOf.mpr
      ⟨Units.mk0 (t₂ / t₁) (div_ne_zero ht₂ ht₁), Units.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, h, mul_smul_comm, Units.inv_mul,
      Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, Algebra.algebraMap_eq_smul_one]
  let g : ℚ → O.NormalizerModScalars := fun r ↦
    if h : ∃ δ, P r δ then QuotientGroup.mk' O.normalizerRatUnits h.choose else 1
  refine ((Set.finite_singleton 1).union
    ((finite_setOf_exists_lt_four_mul_sq_eq m).image g)).subset ?_
  rintro _ ⟨γ, hγ, rfl⟩
  let s : ℚ := reducedTrace B ((γ : Bˣ) : B) / 2
  let t : ℚ := reducedTrace B (((γ : Bˣ) : B) * μ) / (2 * m)
  have hst : ((γ : Bˣ) : B) = algebraMap ℚ B s + t • μ :=
    eq_algebraMap_add_smul_of_mul_comm h4 hm hμ hγ
  by_cases ht : t = 0
  · rw [ht, zero_smul, add_zero] at hst
    have hs : s ≠ 0 := fun hs ↦ (γ : Bˣ).ne_zero (by rw [hst, hs, map_zero])
    exact Or.inl <| (QuotientGroup.eq_one_iff γ).mpr <| Subgroup.mem_subgroupOf.mpr
      ⟨Units.mk0 _ hs, Units.ext hst.symm⟩
  · have hPγ : P (s / t) γ := ⟨t, ht, by
      rw [smul_add, Algebra.algebraMap_eq_smul_one, smul_smul, mul_div_cancel₀ _ ht,
        ← Algebra.algebraMap_eq_smul_one]
      exact hst⟩
    have hex : ∃ δ, P (s / t) δ := ⟨γ, hPγ⟩
    exact Or.inr ⟨s / t, exists_lt_four_mul_sq_eq h4 hO hm hμ γ.2 ht hst,
      (dite_eq_left hex).trans (hP _ _ _ hex.choose_spec hPγ)⟩

/-- **The group `Aut_{±μ}(O)` is finite** (LMFDB `shimcurve.aut_pm_mu_o`) for an order `O` of a
quaternion algebra over `ℚ` and an element `μ` whose square is a negative rational number: the
classes of the elements of the normalizer of `O` commuting with `μ` are finitely many, and those
with `γ⁻¹ μ γ = -μ` form at most one coset of them. -/
lemma finite_autPmMu (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) (hm : m < 0)
    (hμ : μ * μ = algebraMap ℚ B m) : Finite (O.autPmMu μ) := by
  have hF : (QuotientGroup.mk' O.normalizerRatUnits ''
      {γ : O.unitsNormalizer | ((γ : Bˣ) : B) * μ = μ * ((γ : Bˣ) : B)}).Finite :=
    finite_image_mk_setOf_mul_comm h4 hO hm hμ
  have hc (γ : O.unitsNormalizer) (h : (↑(γ : Bˣ)⁻¹ : B) * μ * (γ : Bˣ) = μ) :
      ((γ : Bˣ) : B) * μ = μ * ((γ : Bˣ) : B) := by
    rw [← h, mul_assoc, mul_assoc, Units.mul_inv_cancel_left, ← mul_assoc, ← mul_assoc, h]
  by_cases hδ : ∃ δ : O.unitsNormalizer, (↑(δ : Bˣ)⁻¹ : B) * μ * (δ : Bˣ) = -μ
  · rcases hδ with ⟨δ, hδ⟩
    refine ((hF.union (hF.image (QuotientGroup.mk' _ δ * ·))).subset ?_).to_subtype
    rintro _ ⟨γ, hγ | hγ, rfl⟩
    · exact Or.inl ⟨γ, hc γ hγ, rfl⟩
    · refine Or.inr ⟨_, ⟨δ⁻¹ * γ, hc _ ?_, rfl⟩,
        (map_mul _ _ _).symm.trans (congrArg _ (mul_inv_cancel_left δ γ))⟩
      have h₁ : ((δ : Bˣ) : B) * μ * ↑(δ : Bˣ)⁻¹ = -μ := by
        conv_lhs => rw [← neg_neg μ, ← hδ]
        simp [mul_assoc]
      have h₂ : (↑(γ : Bˣ)⁻¹ : B) * (δ : Bˣ) * μ * (↑(δ : Bˣ)⁻¹ * (γ : Bˣ)) =
          ↑(γ : Bˣ)⁻¹ * ((δ : Bˣ) * μ * ↑(δ : Bˣ)⁻¹) * (γ : Bˣ) := by
        simp only [mul_assoc]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul,
        h₂, h₁, mul_neg, neg_mul, hγ, neg_neg]
  · refine (hF.subset ?_).to_subtype
    rintro _ ⟨γ, hγ | hγ, rfl⟩
    · exact ⟨γ, hc γ hγ, rfl⟩
    · exact absurd ⟨γ, hγ⟩ hδ

end Subalgebra

namespace PolarizedQuaternionOrder

variable {B : Type*} [Ring B] [Algebra ℚ B] [Algebra.IsCentral ℚ B] [IsSimpleRing B]
  (P : PolarizedQuaternionOrder B)
  {H : Subgroup (P.order.EnhancedGroup (P.polarization : B))}

/-- **The group `Aut_{±μ}(O)` of a polarized order `(O, μ)` is finite** (LMFDB
`shimcurve.aut_pm_mu_o`), for a quaternion algebra over `ℚ`. -/
lemma finite_autPmMu (h4 : finrank ℚ B = 4) : Finite (P.order.autPmMu (P.polarization : B)) := by
  rcases P.isPolarization.exists_sq_eq with ⟨m, hm, hμ⟩
  exact Subalgebra.finite_autPmMu h4 P.isQuaternionOrder (Int.cast_lt_zero.mpr hm) <| by
    rw [← sq, hμ, map_intCast]

/-- **The enhanced group of a polarized order is compact** (LMFDB `shimcurve.enhanced_group`), for
a quaternion algebra over `ℚ`: it is the semidirect product of the profinite group `Ô^×` by the
finite group `Aut_{±μ}(O)`. -/
lemma compactSpace_enhancedGroup (h4 : finrank ℚ B = 4) :
    letI _ : TopologicalSpace (P.order.EnhancedGroup (P.polarization : B)) :=
      P.order.enhancedGroupTopology (P.polarization : B)
    CompactSpace (P.order.EnhancedGroup (P.polarization : B)) := by
  have _ : Module.Finite ℤ P.order := P.order.module_finite_of_isQuaternionOrder P.isQuaternionOrder
  have _ : Finite (P.order.autPmMu (P.polarization : B)) := P.finite_autPmMu h4
  exact P.order.compactSpace_enhancedGroup _

/-- **The open subgroups of the enhanced group of a polarized order are compact** (LMFDB
`shimcurve.level`, `shimcurve.index`), for a quaternion algebra over `ℚ`: they are the open compact
subgroups `H` defining the Shimura curves `X_H`. -/
lemma isCompact_of_isOpen (h4 : finrank ℚ B = 4)
    (hH : IsOpen[P.order.enhancedGroupTopology (P.polarization : B)] (H : Set _)) :
    letI _ : TopologicalSpace (P.order.EnhancedGroup (P.polarization : B)) :=
      P.order.enhancedGroupTopology (P.polarization : B)
    IsCompact (H : Set (P.order.EnhancedGroup (P.polarization : B))) := by
  have _ : Module.Finite ℤ P.order := P.order.module_finite_of_isQuaternionOrder P.isQuaternionOrder
  have _ : Finite (P.order.autPmMu (P.polarization : B)) := P.finite_autPmMu h4
  exact P.order.isCompact_of_isOpen_enhancedGroup _ hH

/-- **The open subgroups of the enhanced group of a polarized order have finite index** (LMFDB
`shimcurve.index`), for a quaternion algebra over `ℚ`: the index of the Shimura curve `X_H`, the
index of `H` in the enhanced group, is a positive integer. -/
lemma finiteIndex_of_isOpen (h4 : finrank ℚ B = 4)
    (hH : IsOpen[P.order.enhancedGroupTopology (P.polarization : B)] (H : Set _)) :
    H.FiniteIndex := by
  have _ : Module.Finite ℤ P.order := P.order.module_finite_of_isQuaternionOrder P.isQuaternionOrder
  have _ : Finite (P.order.autPmMu (P.polarization : B)) := P.finite_autPmMu h4
  exact P.order.finiteIndex_of_isOpen_enhancedGroup _ hH

end PolarizedQuaternionOrder
