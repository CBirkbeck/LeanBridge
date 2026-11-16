import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.KleinianGroup
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.MaassPicard

/-!
# The Picard group is a discrete, cofinite, non-cocompact subgroup of `PSL(2, ℂ)`

The Picard group `Γ = PSL(2, ℤ[i])` (LMFDB `mf.maass.picard`) is a subgroup of `PSL(2, ℂ)`
through the inclusion `ℤ[i] ⊆ ℂ` (`picardToPSL_injective`), acting on hyperbolic 3-space `ℋ₃` in
the same way (`picardToPSL_smul`), and its image `picardSubgroup` is

* **discrete**: there are finitely many Gaussian integers of bounded absolute value, and the
  representatives in `SL(2, ℂ)` of an element of `Γ` are `±` a matrix of `SL(2, ℤ[i])`;
* **cofinite**: it has a measurable fundamental domain in `ℋ₃`, of finite hyperbolic volume. By
  reduction theory every point of `ℋ₃` is moved by `SL(2, ℤ[i])` into the set
  `{(x, y) : |x| ≤ 1, y ≥ 1/2}` of finite volume: a point `w = (x, y)` of maximal height in its
  orbit (there are finitely many lower rows `(c, d)` with `|cx + d|² + |c|²y² ≤ 1`) is translated by
  a Gaussian integer into `|Re x|, |Im x| ≤ 1/2`, and then `|x|² + y² ≥ 1`, or else
  `(0, -1; 1, 0)` would raise its height `y` to `y / (|x|² + y²)`;
* **not cocompact**: the quotient `Γ \ ℋ₃` is not compact, and so neither is `PSL(2, ℂ) / Γ`, as
  an element `(a, b; c, d)` of `SL(2, ℤ[i])` sends a point of height `y` to a height
  `y / (|cx + d|² + |c|²y²)`, which is `y` if `c = 0` (then `d` is a unit) and at most `1 / y`
  otherwise (then `|c| ≥ 1`).

Through the fundamental domains of `picardSubgroup`, the Picard group itself has measurable
fundamental domains, and the square-integrability of an invariant function on one of them does not
depend on the choice: this makes the condition `f ∈ L²(Γ \ ℋ₃)` of `IsPicardMaassForm` meaningful.

## Main definitions

* `HyperbolicThreeSpace.picardToPSL` (LMFDB `mf.maass.picard`): the homomorphism
  `PSL(2, ℤ[i]) → PSL(2, ℂ)`.
* `HyperbolicThreeSpace.picardSubgroup` (LMFDB `mf.maass.picard`): the Picard group as a subgroup
  of `PSL(2, ℂ)`.

## Main results

* `HyperbolicThreeSpace.picardToPSL_injective` (LMFDB `mf.maass.picard`): the Picard group is a
  subgroup of `PSL(2, ℂ)`.
* `HyperbolicThreeSpace.picardToPSL_smul`: it acts on `ℋ₃` through `PSL(2, ℂ)`.
* `HyperbolicThreeSpace.discreteTopology_picardSubgroup` (LMFDB `mf.maass.picard`): it is
  discrete.
* `HyperbolicThreeSpace.exists_isFundamentalDomain_picardSubgroup` (LMFDB `mf.maass.picard`): it
  has a measurable fundamental domain.
* `HyperbolicThreeSpace.exists_norm_le_one_and_le_height`: reduction theory for the Picard group.
* `HyperbolicThreeSpace.hyperbolicVolume_lt_top_picardSubgroup` (LMFDB `mf.maass.picard`): its
  fundamental domains have finite volume.
* `HyperbolicThreeSpace.covolume_picardSubgroup_lt_top` (LMFDB `mf.maass.picard`): it is
  cofinite.
* `HyperbolicThreeSpace.not_compactSpace_quotient_picardSubgroup` (LMFDB `mf.maass.picard`): the
  quotient `Γ \ ℋ₃` is not compact.
* `HyperbolicThreeSpace.not_compactSpace_quotientGroup_picardSubgroup` (LMFDB `mf.maass.picard`):
  the Picard group is not a cocompact subgroup of `PSL(2, ℂ)`.
* `HyperbolicThreeSpace.isFundamentalDomain_picardGroup_iff`: the fundamental domains of the Picard
  group are those of `picardSubgroup`.
* `HyperbolicThreeSpace.exists_isFundamentalDomain_picardGroup` (LMFDB `mf.maass.picard`): the
  Picard group has a measurable fundamental domain.
* `HyperbolicThreeSpace.integrableOn_iff_of_isFundamentalDomain_picardGroup` (LMFDB
  `mf.maass.picard`): integrability of an invariant function does not depend on the fundamental
  domain.
-/

open Complex Matrix MeasureTheory Metric MulAction Set TauCeti

open scoped ComplexConjugate MatrixGroups Pointwise

namespace HyperbolicThreeSpace

variable (C : ℝ) (γ : PicardGroup) (z : HyperbolicThreeSpace) {s : Set HyperbolicThreeSpace}

/-- The homomorphism `PSL(2, ℤ[i]) → PSL(2, ℂ)` (LMFDB `mf.maass.picard`) induced by
`ℤ[i] ⊆ ℂ`, through which the Picard group acts on `ℋ₃` (`picardToPSL_smul`). -/
noncomputable def picardToPSL : PicardGroup →* PSL(2, ℂ) :=
  SpecialLinear.projectiveMap 2 GaussianInt.toComplex

/-- The **Picard group** `PSL(2, ℤ[i])` as a subgroup of `PSL(2, ℂ)` (LMFDB `mf.maass.picard`):
the image of `picardToPSL`, which is injective (`picardToPSL_injective`). -/
noncomputable abbrev picardSubgroup : Subgroup PSL(2, ℂ) :=
  picardToPSL.range

/-- **The Picard group is a subgroup of `PSL(2, ℂ)`** (LMFDB `mf.maass.picard`): the homomorphism
`PSL(2, ℤ[i]) → PSL(2, ℂ)` is injective. -/
lemma picardToPSL_injective : Function.Injective picardToPSL :=
  projectiveMap_injective GaussianInt.toComplex_injective

/-- **The Picard group acts on `ℋ₃` through `PSL(2, ℂ)`**: `γ z` is the image of `z` under the
image of `γ` in `PSL(2, ℂ)`. -/
lemma picardToPSL_smul : picardToPSL γ • z = γ • z :=
  QuotientGroup.induction_on γ fun _ ↦ rfl

private lemma finite_setOf_norm_le : {a : GaussianInt | ‖(a : ℂ)‖ ≤ C}.Finite := by
  refine ((finite_Icc (-⌈C⌉) ⌈C⌉).prod (finite_Icc (-⌈C⌉) ⌈C⌉)).preimage
    (f := fun a : GaussianInt ↦ (a.re, a.im))
    (fun a _ b _ h ↦ Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)) |>.subset ?_
  intro a ha
  have hre : |(a.re : ℝ)| ≤ C := by
    rw [GaussianInt.intCast_re]
    exact (abs_re_le_norm _).trans ha
  have him : |(a.im : ℝ)| ≤ C := by
    rw [GaussianInt.intCast_im]
    exact (abs_im_le_norm _).trans ha
  have hre' : |a.re| ≤ ⌈C⌉ := by
    exact_mod_cast hre.trans (Int.le_ceil C)
  have him' : |a.im| ≤ ⌈C⌉ := by
    exact_mod_cast him.trans (Int.le_ceil C)
  exact ⟨abs_le.mp hre', abs_le.mp him'⟩

lemma finite_setOf_mem_picardSubgroup : {δ : PSL(2, ℂ) | δ ∈ picardSubgroup ∧ ∃ g : SL(2, ℂ),
    (QuotientGroup.mk g : PSL(2, ℂ)) = δ ∧ ∀ i j, ‖g i j‖ ≤ C}.Finite := by
  let F : Set SL(2, GaussianInt) := {a | ∀ i j, ‖((a i j : GaussianInt) : ℂ)‖ ≤ C}
  have hF : F.Finite := by
    refine Finite.of_finite_image (f := fun a : SL(2, GaussianInt) ↦
      ((a : Matrix (Fin 2) (Fin 2) GaussianInt) : Fin 2 → Fin 2 → GaussianInt)) ?_
        Subtype.val_injective.injOn
    refine (Finite.pi fun _ : Fin 2 ↦ Finite.pi fun _ : Fin 2 ↦ finite_setOf_norm_le C).subset ?_
    rintro _ ⟨a, ha, rfl⟩ i - j -
    exact ha i j
  refine (hF.image fun a ↦ picardToPSL (QuotientGroup.mk a)).subset ?_
  rintro _ ⟨⟨γ, rfl⟩, g, hg, hgC⟩
  induction γ using QuotientGroup.induction_on with
  | H a =>
    exact ⟨a, fun i j ↦
      (norm_apply_eq_of_mk_eq (a := gaussianIntToSL2C a) hg.symm i j).symm.trans_le (hgC i j), rfl⟩

/-- **The Picard group is a discrete subgroup of `PSL(2, ℂ)`** (LMFDB `mf.maass.picard`). -/
lemma discreteTopology_picardSubgroup : DiscreteTopology picardSubgroup :=
  discreteTopology_of_finite finite_setOf_mem_picardSubgroup

instance : Countable picardSubgroup :=
  countable_of_finite finite_setOf_mem_picardSubgroup

instance : ProperlyDiscontinuousSMul picardSubgroup HyperbolicThreeSpace :=
  properlyDiscontinuousSMul_of_finite finite_setOf_mem_picardSubgroup

/-- **The Picard group has a measurable fundamental domain** in `ℋ₃` (LMFDB `mf.maass.picard`). -/
lemma exists_isFundamentalDomain_picardSubgroup : ∃ s : Set HyperbolicThreeSpace, MeasurableSet s ∧
    IsFundamentalDomain picardSubgroup s hyperbolicVolume :=
  exists_isFundamentalDomain_of_finite finite_setOf_mem_picardSubgroup

lemma exists_forall_height_smul_le : ∃ a : SL(2, GaussianInt), ∀ b : SL(2, GaussianInt),
    (gaussianIntToSL2C b • z).height ≤ (gaussianIntToSL2C a • z).height := by
  have hy : 0 < z.coords.2 := coords_snd_pos z
  let f : GaussianInt × GaussianInt → ℝ := fun p ↦
    normSq ((p.1 : ℂ) * z.coords.1 + p.2) + normSq (p.1 : ℂ) * z.coords.2 ^ 2
  have hD (b : SL(2, GaussianInt)) :
      moebiusDenom (gaussianIntToSL2C b) z.coords = f (b 1 0, b 1 1) :=
    rfl
  let T : Set (GaussianInt × GaussianInt) :=
    (fun b : SL(2, GaussianInt) ↦ (b 1 0, b 1 1)) '' {b | f (b 1 0, b 1 1) ≤ 1}
  have hT : T.Finite := by
    refine ((finite_setOf_norm_le z.coords.2⁻¹).prod
      (finite_setOf_norm_le (1 + z.coords.2⁻¹ * ‖z.coords.1‖))).subset ?_
    rintro _ ⟨b, hb, rfl⟩
    have h₁ : normSq ((b 1 0 : GaussianInt) : ℂ) * z.coords.2 ^ 2 ≤ 1 :=
      (le_add_of_nonneg_left (normSq_nonneg _)).trans hb
    have h₂ : normSq (((b 1 0 : GaussianInt) : ℂ) * z.coords.1 + (b 1 1 : GaussianInt)) ≤ 1 :=
      (le_add_of_nonneg_right (mul_nonneg (normSq_nonneg _) (sq_nonneg _))).trans hb
    rw [normSq_eq_norm_sq] at h₁ h₂
    have hc : ‖((b 1 0 : GaussianInt) : ℂ)‖ ≤ z.coords.2⁻¹ := by
      rw [← one_div, le_div_iff₀ hy]
      nlinarith [mul_nonneg (norm_nonneg ((b 1 0 : GaussianInt) : ℂ)) hy.le]
    have hcd : ‖((b 1 0 : GaussianInt) : ℂ) * z.coords.1 + (b 1 1 : GaussianInt)‖ ≤ 1 := by
      nlinarith [norm_nonneg (((b 1 0 : GaussianInt) : ℂ) * z.coords.1 + (b 1 1 : GaussianInt))]
    refine ⟨hc, ?_⟩
    have e : ((b 1 1 : GaussianInt) : ℂ) =
        (((b 1 0 : GaussianInt) : ℂ) * z.coords.1 + (b 1 1 : GaussianInt)) -
          ((b 1 0 : GaussianInt) : ℂ) * z.coords.1 := by
      ring1
    simp only [mem_ofPred_eq]
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add hcd ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  have hne : T.Nonempty := ⟨_, 1, by simp [f], rfl⟩
  rcases exists_min_image T f hT hne with ⟨_, ⟨a, ha, rfl⟩, hmin⟩
  refine ⟨a, fun b ↦ ?_⟩
  have hDa : 0 < moebiusDenom (gaussianIntToSL2C a) z.coords := moebiusDenom_pos _ hy
  have hle : moebiusDenom (gaussianIntToSL2C a) z.coords ≤
      moebiusDenom (gaussianIntToSL2C b) z.coords := by
    rw [hD, hD]
    by_cases hb : f (b 1 0, b 1 1) ≤ 1
    · exact hmin _ ⟨b, hb, rfl⟩
    · exact ha.trans (not_le.mp hb).le
  rw [height_smul, height_smul]
  exact div_le_div_of_nonneg_left hy.le hDa hle

/-- **Reduction theory for the Picard group**: every point of `ℋ₃` is moved by `SL(2, ℤ[i])` to a
point `(x, y)` with `|x| ≤ 1` and `y ≥ 1/2`. -/
lemma exists_norm_le_one_and_le_height : ∃ a : SL(2, GaussianInt),
    ‖(gaussianIntToSL2C a • z).coords.1‖ ≤ 1 ∧ 1 / 2 ≤ (gaussianIntToSL2C a • z).coords.2 := by
  rcases exists_forall_height_smul_le z with ⟨a, ha⟩
  let x : ℂ := (gaussianIntToSL2C a • z).coords.1
  let t : GaussianInt := ⟨-round x.re, -round x.im⟩
  let u : SL(2, GaussianInt) := ⟨!![1, t; 0, 1], by simp⟩
  let m : SL(2, GaussianInt) := ⟨!![0, -1; 1, 0], by simp⟩
  have hu₁₀ : (gaussianIntToSL2C u) 1 0 = 0 := map_zero GaussianInt.toComplex
  have hu₀₀ : (gaussianIntToSL2C u) 0 0 = 1 := map_one GaussianInt.toComplex
  have hu₀₁ : (gaussianIntToSL2C u) 0 1 = t :=
    rfl
  have hu :
      (gaussianIntToSL2C (u * a) • z).coords = (x + t, (gaussianIntToSL2C a • z).coords.2) := by
    rw [map_mul, mul_smul, coords_smul, moebius_eq_of_apply_one_zero hu₁₀, hu₀₀, hu₀₁]
    simp [x]
  have hy : 0 < (gaussianIntToSL2C a • z).coords.2 := coords_snd_pos _
  have hre : |(x + t).re| ≤ 1 / 2 := by
    simpa [t, ← sub_eq_add_neg] using abs_sub_round x.re
  have him : |(x + t).im| ≤ 1 / 2 := by
    simpa [t, ← sub_eq_add_neg] using abs_sub_round x.im
  have hs : (gaussianIntToSL2C (m * (u * a)) • z).height ≤ (gaussianIntToSL2C a • z).height :=
    ha _
  rw [map_mul, mul_smul, height_smul, hu] at hs
  have hN : moebiusDenom (gaussianIntToSL2C m) (x + t, (gaussianIntToSL2C a • z).coords.2) =
      normSq (x + t) + (gaussianIntToSL2C a • z).coords.2 ^ 2 := by
    have hm₁₀ : (gaussianIntToSL2C m) 1 0 = 1 := map_one GaussianInt.toComplex
    have hm₁₁ : (gaussianIntToSL2C m) 1 1 = 0 := map_zero GaussianInt.toComplex
    simp [moebiusDenom, hm₁₀, hm₁₁]
  have hN₀ : 0 < normSq (x + t) + (gaussianIntToSL2C a • z).coords.2 ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (pow_pos hy 2)
  have h₀ : (gaussianIntToSL2C (u * a) • z).coords.2 = (gaussianIntToSL2C a • z).coords.2 := by
    rw [hu]
  have hh : (gaussianIntToSL2C (u * a) • z).height = (gaussianIntToSL2C a • z).coords.2 :=
    h₀
  have hya : (gaussianIntToSL2C a • z).height = (gaussianIntToSL2C a • z).coords.2 :=
    rfl
  rw [hh, hN, div_le_iff₀ hN₀, hya] at hs
  have h₁ : 1 ≤ normSq (x + t) + (gaussianIntToSL2C a • z).coords.2 ^ 2 :=
    (le_mul_iff_one_le_right hy).mp hs
  have h₂ : normSq (x + t) ≤ 1 / 2 := by
    rw [normSq_apply]
    nlinarith [abs_le.mp hre, abs_le.mp him]
  refine ⟨u * a, ?_, ?_⟩
  · rw [hu]
    exact (norm_le_abs_re_add_abs_im _).trans (by linarith)
  · rw [hu]
    nlinarith

lemma exists_mem_picardSubgroup_smul_mem : ∃ δ ∈ picardSubgroup, δ • z ∈
    {w : HyperbolicThreeSpace | w.coords.1 ∈ closedBall 0 1 ∧ 1 / 2 ≤ w.coords.2} := by
  rcases exists_norm_le_one_and_le_height z with ⟨a, ha₁, ha₂⟩
  exact ⟨picardToPSL (QuotientGroup.mk a), ⟨_, rfl⟩, mem_closedBall_zero_iff.mpr ha₁, ha₂⟩

/-- **The fundamental domains of the Picard group have finite volume** (LMFDB
`mf.maass.picard`). -/
lemma hyperbolicVolume_lt_top_picardSubgroup
    (hs : IsFundamentalDomain picardSubgroup s hyperbolicVolume) : hyperbolicVolume s < ⊤ :=
  hyperbolicVolume_lt_top_of_forall_exists_smul_mem (hyperbolicVolume_siegelSet_lt_top
    isBounded_closedBall isClosed_closedBall.measurableSet (by norm_num))
    exists_mem_picardSubgroup_smul_mem hs

/-- **The Picard group is cofinite** (LMFDB `mf.maass.picard`): its covolume, the hyperbolic volume
of its fundamental domains, is finite. Fundamental domains exist
(`exists_isFundamentalDomain_picardSubgroup`), so this is not the value `0` that Mathlib's
`covolume` takes when there is none. -/
lemma covolume_picardSubgroup_lt_top :
    covolume picardSubgroup HyperbolicThreeSpace hyperbolicVolume < ⊤ := by
  rcases exists_isFundamentalDomain_picardSubgroup with ⟨s, -, hs⟩
  rw [hs.covolume_eq_volume]
  exact hyperbolicVolume_lt_top_picardSubgroup hs

private lemma one_le_normSq {c : GaussianInt} (hc : c ≠ 0) : 1 ≤ normSq (c : ℂ) := by
  have h : 0 < c.norm := GaussianInt.norm_pos.mpr hc
  have h₁ : 1 ≤ c.norm := by
    omega
  rw [← GaussianInt.intCast_real_norm]
  exact_mod_cast h₁

private lemma normSq_eq_one_of_mul_eq_one {a d : GaussianInt} (h : a * d = 1) :
    normSq (d : ℂ) = 1 := by
  have h₁ : a.norm * d.norm = 1 := by
    rw [← Zsqrtd.norm_mul, h, Zsqrtd.norm_one]
  rw [← GaussianInt.intCast_real_norm]
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one_right _ h₁) with h₂ | h₂
  · rw [h₂, Int.cast_one]
  · have h₃ : 0 ≤ d.norm := GaussianInt.norm_nonneg d
    omega

lemma height_smul_picardSubgroup {δ : PSL(2, ℂ)} (hδ : δ ∈ picardSubgroup) :
    (δ • z).height = z.height ∨ (δ • z).height ≤ z.height⁻¹ := by
  rcases hδ with ⟨δ, rfl⟩
  induction δ using QuotientGroup.induction_on with
  | H a =>
    have hy : 0 < z.coords.2 := coords_snd_pos z
    have hz : z.height = z.coords.2 :=
      rfl
    have e : picardToPSL (QuotientGroup.mk a) • z = gaussianIntToSL2C a • z :=
      rfl
    rw [e, height_smul, hz]
    by_cases hc : a 1 0 = 0
    · have hdet : a 0 0 * a 1 1 = 1 := by
        have h : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1 := a.fin_two_mul_sub_mul_eq_one
        rwa [hc, mul_zero, sub_zero] at h
      left
      have hD : moebiusDenom (gaussianIntToSL2C a) z.coords = 1 := by
        simp [moebiusDenom, hc, normSq_eq_one_of_mul_eq_one hdet]
      rw [hD, div_one]
    · right
      have h₁ : 1 ≤ normSq ((a 1 0 : GaussianInt) : ℂ) := one_le_normSq hc
      have hD : z.coords.2 ^ 2 ≤ moebiusDenom (gaussianIntToSL2C a) z.coords := by
        have h₂ : moebiusDenom (gaussianIntToSL2C a) z.coords =
            normSq (((a 1 0 : GaussianInt) : ℂ) * z.coords.1 + (a 1 1 : GaussianInt)) +
              normSq ((a 1 0 : GaussianInt) : ℂ) * z.coords.2 ^ 2 :=
          rfl
        rw [h₂]
        nlinarith [normSq_nonneg (((a 1 0 : GaussianInt) : ℂ) * z.coords.1 + (a 1 1 : GaussianInt)),
          sq_nonneg z.coords.2]
      rw [div_le_iff₀ (moebiusDenom_pos _ hy), ← div_eq_inv_mul, le_div_iff₀ hy, ← sq]
      exact hD

/-- **The Picard group is not cocompact** (LMFDB `mf.maass.picard`): the quotient `Γ \ ℋ₃` is not
compact. -/
lemma not_compactSpace_quotient_picardSubgroup :
    ¬CompactSpace (orbitRel.Quotient picardSubgroup HyperbolicThreeSpace) :=
  not_compactSpace_quotient_of_height fun _ hδ z ↦ height_smul_picardSubgroup z hδ

/-- **The Picard group is not a cocompact subgroup of `PSL(2, ℂ)`** (LMFDB `mf.maass.picard`): the
coset space `PSL(2, ℂ) / Γ` is not compact, as `Γ \ ℋ₃` is not. -/
lemma not_compactSpace_quotientGroup_picardSubgroup : ¬CompactSpace (PSL(2, ℂ) ⧸ picardSubgroup) :=
  fun h ↦ not_compactSpace_quotient_picardSubgroup
    (compactSpace_quotient_of_compactSpace_quotientGroup h)

lemma rangeRestrict_picardToPSL_smul : picardToPSL.rangeRestrict γ • z = γ • z :=
  picardToPSL_smul γ z

variable (s) in
lemma rangeRestrict_picardToPSL_smul_set : picardToPSL.rangeRestrict γ • s = γ • s := by
  rw [← image_smul, ← image_smul]
  exact congrArg (· '' s) (funext (rangeRestrict_picardToPSL_smul γ))

/-- **The fundamental domains of the Picard group are those of its image in `PSL(2, ℂ)`**, the two
groups acting in the same way. -/
lemma isFundamentalDomain_picardGroup_iff : IsFundamentalDomain PicardGroup s hyperbolicVolume ↔
    IsFundamentalDomain picardSubgroup s hyperbolicVolume := by
  refine ⟨fun h ↦ ⟨h.nullMeasurableSet, h.ae_covers.mono fun z ⟨γ, hγ⟩ ↦
    ⟨picardToPSL.rangeRestrict γ, by rwa [rangeRestrict_picardToPSL_smul]⟩, ?_⟩,
    fun h ↦ ⟨h.nullMeasurableSet, h.ae_covers.mono fun z ⟨γ', hγ'⟩ ↦ ?_, fun γ δ hγδ ↦ ?_⟩⟩
  · intro γ' δ' hγδ
    rcases picardToPSL.rangeRestrict_surjective γ' with ⟨γ, rfl⟩
    rcases picardToPSL.rangeRestrict_surjective δ' with ⟨δ, rfl⟩
    dsimp only [Function.onFun]
    rw [rangeRestrict_picardToPSL_smul_set, rangeRestrict_picardToPSL_smul_set]
    exact h.aedisjoint fun e ↦ hγδ (by rw [e])
  · rcases picardToPSL.rangeRestrict_surjective γ' with ⟨γ, rfl⟩
    exact ⟨γ, by rwa [← rangeRestrict_picardToPSL_smul]⟩
  · have h' := h.aedisjoint ((MonoidHom.rangeRestrict_injective_iff.mpr picardToPSL_injective).ne
      hγδ)
    dsimp only [Function.onFun] at h'
    rwa [rangeRestrict_picardToPSL_smul_set, rangeRestrict_picardToPSL_smul_set] at h'

/-- **The Picard group has a measurable fundamental domain** in `ℋ₃` (LMFDB `mf.maass.picard`),
so that the condition `f ∈ L²(Γ \ ℋ₃)` of `IsPicardMaassForm` is not vacuous. -/
lemma exists_isFundamentalDomain_picardGroup : ∃ s : Set HyperbolicThreeSpace, MeasurableSet s ∧
    IsFundamentalDomain PicardGroup s hyperbolicVolume := by
  rcases exists_isFundamentalDomain_picardSubgroup with ⟨s, hs, hF⟩
  exact ⟨s, hs, isFundamentalDomain_picardGroup_iff.mpr hF⟩

/-- **Integrability on `Γ \ ℋ₃` does not depend on the fundamental domain** (LMFDB
`mf.maass.picard`): for a function `f` invariant under the Picard group, such as `|f|²` for a Maass
form `f` (`IsPicardMaassForm`), integrability on one fundamental domain is integrability on any
other. -/
lemma integrableOn_iff_of_isFundamentalDomain_picardGroup {E : Type*} [NormedAddCommGroup E]
    {f : HyperbolicThreeSpace → E} (hf : ∀ (δ : PicardGroup) (w : HyperbolicThreeSpace),
    f (δ • w) = f w) {t : Set HyperbolicThreeSpace}
    (hs : IsFundamentalDomain PicardGroup s hyperbolicVolume)
    (ht : IsFundamentalDomain PicardGroup t hyperbolicVolume) :
    IntegrableOn f s hyperbolicVolume ↔ IntegrableOn f t hyperbolicVolume :=
  (isFundamentalDomain_picardGroup_iff.mp hs).integrableOn_iff
    (isFundamentalDomain_picardGroup_iff.mp ht) fun γ' z ↦ by
      rcases picardToPSL.rangeRestrict_surjective γ' with ⟨γ, rfl⟩
      rw [rangeRestrict_picardToPSL_smul]
      exact hf γ z

end HyperbolicThreeSpace
