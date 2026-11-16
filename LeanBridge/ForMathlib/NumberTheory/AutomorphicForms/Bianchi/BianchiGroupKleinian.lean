import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.KleinianGroup

/-!
# The Bianchi groups are discrete, non-cocompact subgroups of `PSL(2, ℂ)`

Let `K` be an imaginary quadratic field, embedded in `ℂ` by `σ`. The Bianchi group `PSL(2, 𝒪_K)`
(LMFDB `mf.bianchi.bianchigroup`) is a subgroup of `PSL(2, ℂ)` (`bianchiToPSL_injective`), and its
image `bianchiSubgroup σ` is

* **discrete**, and acts **properly discontinuously** on `ℋ₃` with a measurable fundamental domain:
  there are finitely many integers of `K` of bounded absolute value, and the representatives in
  `SL(2, ℂ)` of an element of `PSL(2, 𝒪_K)` are `±` a matrix of `SL(2, 𝒪_K)`;
* **not cocompact**: `PSL(2, 𝒪_K) \ ℋ₃` is not compact, as `(a, b; c, d) ∈ SL(2, 𝒪_K)` sends a
  point of height `y` to a height `y / (|cx + d|² + |c|²y²)`, which is `y` if `c = 0` (then `d` is
  a unit, of absolute value `1`) and at most `1 / y` otherwise (then `|c| ≥ 1`);
* of **finite covolume** when `𝒪_K` is a principal ideal domain: by reduction theory every point of
  `ℋ₃` is moved by `SL(2, 𝒪_K)` above a fixed height, and then by a translation by `𝒪_K` into a
  Siegel set of finite volume.

That `PSL(2, ℂ)` acts faithfully by isometries is `HyperbolicThreeSpace.pslToIsom_injective`, and
that it is the group of orientation-preserving isometries of `ℋ₃` is
`HyperbolicThreeSpace.pslEquivOrientationPreservingIsom`. The finite volume for class number
greater than `1` is not proved here.

## Main definitions

* `HyperbolicThreeSpace.bianchiToPSL` (LMFDB `mf.bianchi.bianchigroup`): the homomorphism
  `PSL(2, 𝒪_K) → PSL(2, ℂ)`.
* `HyperbolicThreeSpace.bianchiSubgroup` (LMFDB `mf.bianchi.bianchigroup`): the Bianchi group as a
  subgroup of `PSL(2, ℂ)`.

## Main results

* `HyperbolicThreeSpace.bianchiToPSL_injective` (LMFDB `mf.bianchi.bianchigroup`): the Bianchi
  group is a subgroup of `PSL(2, ℂ)`.
* `HyperbolicThreeSpace.discreteTopology_bianchiSubgroup` (LMFDB `mf.bianchi.bianchigroup`): it is
  discrete.
* `HyperbolicThreeSpace.properlyDiscontinuousSMul_bianchiSubgroup` (LMFDB
  `mf.bianchi.bianchigroup`): it acts properly discontinuously on `ℋ₃`.
* `HyperbolicThreeSpace.exists_isFundamentalDomain_bianchiSubgroup`: it has a measurable
  fundamental domain.
* `HyperbolicThreeSpace.not_compactSpace_quotient_bianchiSubgroup` (LMFDB
  `mf.bianchi.bianchigroup`): the quotient `PSL(2, 𝒪_K) \ ℋ₃` is not compact.
* `HyperbolicThreeSpace.not_compactSpace_quotientGroup_bianchiSubgroup`: the Bianchi group is not
  a cocompact subgroup of `PSL(2, ℂ)`.
* `HyperbolicThreeSpace.covolume_bianchiSubgroup_lt_top` (LMFDB `mf.bianchi.bianchigroup`): it has
  finite volume when `𝒪_K` is a principal ideal domain.
-/

open Complex Matrix MeasureTheory Module MulAction NumberField Set TauCeti

open scoped MatrixGroups Pointwise

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] (σ : K →+* ℂ)

/-- The homomorphism `PSL(2, 𝒪_K) → PSL(2, ℂ)` (LMFDB `mf.bianchi.bianchigroup`) induced by the
embedding `σ : K → ℂ`, through which the Bianchi group acts on `ℋ₃`. -/
noncomputable def bianchiToPSL : PSL(2, 𝓞 K) →* PSL(2, ℂ) :=
  SpecialLinear.projectiveMap 2 (σ.comp (algebraMap (𝓞 K) K))

/-- The **Bianchi group** `PSL(2, 𝒪_K)` as a subgroup of `PSL(2, ℂ)` (LMFDB
`mf.bianchi.bianchigroup`): the image of `bianchiToPSL σ`, which is injective
(`bianchiToPSL_injective`). -/
noncomputable abbrev bianchiSubgroup : Subgroup PSL(2, ℂ) :=
  (bianchiToPSL σ).range

/-- **The Bianchi group is a subgroup of `PSL(2, ℂ)`** (LMFDB `mf.bianchi.bianchigroup`): the
homomorphism `PSL(2, 𝒪_K) → PSL(2, ℂ)` is injective. -/
lemma bianchiToPSL_injective : Function.Injective (bianchiToPSL σ) :=
  projectiveMap_injective (σ.injective.comp RingOfIntegers.coe_injective)

variable [NumberField K] [IsTotallyComplex K] {σ}

lemma finite_setOf_mem_bianchiSubgroup (hK : finrank ℚ K = 2) (C : ℝ) : {γ : PSL(2, ℂ) |
    γ ∈ bianchiSubgroup σ ∧ ∃ g : SL(2, ℂ), (QuotientGroup.mk g : PSL(2, ℂ)) = γ ∧
      ∀ i j, ‖g i j‖ ≤ C}.Finite := by
  let F : Set SL(2, 𝓞 K) := {a | ∀ i j, ‖σ (a i j : 𝓞 K)‖ ≤ C}
  have hF : F.Finite := by
    refine Finite.of_finite_image (f := fun a : SL(2, 𝓞 K) ↦
      ((a : Matrix (Fin 2) (Fin 2) (𝓞 K)) : Fin 2 → Fin 2 → 𝓞 K)) ?_ Subtype.val_injective.injOn
    refine (Finite.pi fun _ : Fin 2 ↦ Finite.pi fun _ : Fin 2 ↦
      finite_setOf_norm_apply_le (σ := σ) hK C).subset ?_
    rintro _ ⟨a, ha, rfl⟩ i - j -
    exact ha i j
  refine (hF.image fun a ↦ bianchiToPSL σ (QuotientGroup.mk a)).subset ?_
  rintro _ ⟨⟨γ, rfl⟩, g, hg, hgC⟩
  induction γ using QuotientGroup.induction_on with
  | H a =>
    exact ⟨a, fun i j ↦ (norm_apply_eq_of_mk_eq (a := SpecialLinearGroup.map
      (σ.comp (algebraMap (𝓞 K) K)) a) hg.symm i j).symm.trans_le (hgC i j), rfl⟩

/-- **The Bianchi group is a discrete subgroup of `PSL(2, ℂ)`** (LMFDB `mf.bianchi.bianchigroup`),
for an imaginary quadratic field `K`. -/
lemma discreteTopology_bianchiSubgroup (hK : finrank ℚ K = 2) :
    DiscreteTopology (bianchiSubgroup σ) :=
  discreteTopology_of_finite (finite_setOf_mem_bianchiSubgroup hK)

/-- **The Bianchi group acts properly discontinuously on `ℋ₃`** (LMFDB `mf.bianchi.bianchigroup`),
for an imaginary quadratic field `K`. -/
lemma properlyDiscontinuousSMul_bianchiSubgroup (hK : finrank ℚ K = 2) :
    ProperlyDiscontinuousSMul (bianchiSubgroup σ) HyperbolicThreeSpace :=
  properlyDiscontinuousSMul_of_finite (finite_setOf_mem_bianchiSubgroup hK)

/-- **The Bianchi group has a measurable fundamental domain** in `ℋ₃`, for an imaginary quadratic
field `K`. -/
lemma exists_isFundamentalDomain_bianchiSubgroup (hK : finrank ℚ K = 2) :
    ∃ s : Set HyperbolicThreeSpace, MeasurableSet s ∧
      IsFundamentalDomain (bianchiSubgroup σ) s hyperbolicVolume :=
  exists_isFundamentalDomain_of_finite (finite_setOf_mem_bianchiSubgroup hK)

lemma height_smul_bianchiSubgroup (hK : finrank ℚ K = 2) {γ : PSL(2, ℂ)}
    (hγ : γ ∈ bianchiSubgroup σ) (z : HyperbolicThreeSpace) :
    (γ • z).height = z.height ∨ (γ • z).height ≤ z.height⁻¹ := by
  rcases hγ with ⟨γ, rfl⟩
  induction γ using QuotientGroup.induction_on with
  | H a =>
    have hy : 0 < z.coords.2 := coords_snd_pos z
    have hz : z.height = z.coords.2 :=
      rfl
    have e : bianchiToPSL σ (QuotientGroup.mk a) • z =
        SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) a • z :=
      rfl
    have hD : moebiusDenom (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) a) z.coords =
        ‖σ (a 1 0 : 𝓞 K) * z.coords.1 + σ (a 1 1 : 𝓞 K)‖ ^ 2 +
          ‖σ (a 1 0 : 𝓞 K)‖ ^ 2 * z.coords.2 ^ 2 := by
      rw [moebiusDenom, normSq_eq_norm_sq, normSq_eq_norm_sq]
      rfl
    rw [e, height_smul, hz]
    by_cases hc : a 1 0 = 0
    · have hdet : a 1 1 * a 0 0 = 1 := by
        have h : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1 := a.fin_two_mul_sub_mul_eq_one
        rwa [hc, mul_zero, sub_zero, mul_comm] at h
      have hd : ‖σ (a 1 1 : 𝓞 K)‖ = 1 := norm_unit_eq_one hK (Units.mkOfMulEqOne _ _ hdet)
      left
      rw [hD]
      simp [hc, hd]
    · right
      have hD' : z.coords.2 ^ 2 ≤
          moebiusDenom (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) a) z.coords := by
        rw [hD]
        have h₁ : 1 ≤ ‖σ (a 1 0 : 𝓞 K)‖ ^ 2 := one_le_pow₀ (one_le_norm_apply hK hc)
        nlinarith [sq_nonneg ‖σ (a 1 0 : 𝓞 K) * z.coords.1 + σ (a 1 1 : 𝓞 K)‖,
          sq_nonneg z.coords.2]
      rw [div_le_iff₀ (moebiusDenom_pos _ hy), ← div_eq_inv_mul, le_div_iff₀ hy, ← sq]
      exact hD'

/-- **The Bianchi group is not cocompact** (LMFDB `mf.bianchi.bianchigroup`): for an imaginary
quadratic field `K`, the quotient `PSL(2, 𝒪_K) \ ℋ₃` is not compact. -/
lemma not_compactSpace_quotient_bianchiSubgroup (hK : finrank ℚ K = 2) :
    ¬CompactSpace (orbitRel.Quotient (bianchiSubgroup σ) HyperbolicThreeSpace) :=
  not_compactSpace_quotient_of_height fun _ ↦ height_smul_bianchiSubgroup hK

/-- **The Bianchi group is not a cocompact subgroup of `PSL(2, ℂ)`**: for an imaginary quadratic
field `K`, the coset space `PSL(2, ℂ) / PSL(2, 𝒪_K)` is not compact. -/
lemma not_compactSpace_quotientGroup_bianchiSubgroup (hK : finrank ℚ K = 2) :
    ¬CompactSpace (PSL(2, ℂ) ⧸ bianchiSubgroup σ) :=
  fun h ↦ not_compactSpace_quotient_bianchiSubgroup hK
    (compactSpace_quotient_of_compactSpace_quotientGroup h)

variable [IsPrincipalIdealRing (𝓞 K)]

lemma exists_mem_bianchiSubgroup_smul_mem (hK : finrank ℚ K = 2) : ∃ U : Set HyperbolicThreeSpace,
    hyperbolicVolume U < ⊤ ∧ ∀ z : HyperbolicThreeSpace, ∃ γ ∈ bianchiSubgroup σ, γ • z ∈ U := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  rcases exists_le_height_smul (σ := σ) hK with ⟨y₀, hy₀, hred⟩
  refine ⟨{z | z.coords.1 ∈ ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx) ∧
    y₀ ≤ z.coords.2}, hyperbolicVolume_siegelSet_lt_top (ZSpan.fundamentalDomain_isBounded _)
      (ZSpan.fundamentalDomain_measurableSet _) hy₀, fun z ↦ ?_⟩
  rcases hred z with ⟨γ, hγ⟩
  rcases ZSpan.exist_unique_vadd_mem_fundamentalDomain (integralLatticeBasis σ hK hx)
    (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.1 with ⟨v, hv, -⟩
  rcases mem_bianchiScaledLattice.mp (coe_mem_bianchiScaledLattice_one hK hx v) with ⟨a, ha⟩
  rw [one_mul] at ha
  let u : SL(2, 𝓞 K) := ⟨!![1, a; 0, 1], by simp⟩
  have hM₁₀ : SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) u 1 0 = 0 :=
    map_zero (σ.comp (algebraMap (𝓞 K) K))
  have hM₀₀ : SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) u 0 0 = 1 :=
    map_one (σ.comp (algebraMap (𝓞 K) K))
  have hM₀₁ : SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) u 0 1 = σ a :=
    rfl
  have hco : (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) (u * γ) • z).coords =
      ((SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.1 + σ a,
        (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.2) := by
    rw [map_mul, mul_smul, coords_smul, moebius_eq_of_apply_one_zero hM₁₀, hM₀₀, hM₀₁]
    simp
  refine ⟨bianchiToPSL σ (QuotientGroup.mk (u * γ)), ⟨_, rfl⟩, ?_, ?_⟩
  · have e : (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.1 + σ a =
        v +ᵥ (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) γ • z).coords.1 := by
      rw [ha, add_comm]
      rfl
    have h : (bianchiToPSL σ (QuotientGroup.mk (u * γ)) • z).coords.1 =
        (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) (u * γ) • z).coords.1 :=
      rfl
    rw [h, hco, e]
    exact hv
  · have h : (bianchiToPSL σ (QuotientGroup.mk (u * γ)) • z).coords.2 =
        (SpecialLinearGroup.map (σ.comp (algebraMap (𝓞 K) K)) (u * γ) • z).coords.2 :=
      rfl
    rw [h, hco]
    exact hγ

/-- **The Bianchi group has finite covolume** (LMFDB `mf.bianchi.bianchigroup`) when `𝒪_K` is a
principal ideal domain: every fundamental domain has the volume of one of them, at most that of a
Siegel set of finite volume whose translates under the group cover `ℋ₃`. Fundamental domains exist
(`exists_isFundamentalDomain_bianchiSubgroup`), so this is not the value `0` that Mathlib's
`covolume` takes when there is none. -/
lemma covolume_bianchiSubgroup_lt_top (hK : finrank ℚ K = 2) :
    covolume (bianchiSubgroup σ) HyperbolicThreeSpace hyperbolicVolume < ⊤ := by
  have : Countable (bianchiSubgroup σ) := countable_of_finite (finite_setOf_mem_bianchiSubgroup hK)
  rcases exists_isFundamentalDomain_bianchiSubgroup (σ := σ) hK with ⟨s, -, hs⟩
  rcases exists_mem_bianchiSubgroup_smul_mem (σ := σ) hK with ⟨U, hU, hcov⟩
  rw [hs.covolume_eq_volume]
  exact hyperbolicVolume_lt_top_of_forall_exists_smul_mem hU hcov hs

end HyperbolicThreeSpace
