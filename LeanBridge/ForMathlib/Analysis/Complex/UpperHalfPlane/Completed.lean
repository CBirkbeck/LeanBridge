import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The completed upper half-plane

The LMFDB's completed upper half-plane `ℍ* = ℍ ∪ ℚ ∪ {∞}` is the upper half-plane `ℍ` (Mathlib's
`UpperHalfPlane`, with the topology induced from `ℂ`) together with the cusps `ℚ ∪ {∞}`, here the
points of `OnePoint ℚ`. Its topology is the one in which `ℍ` is an open subspace, the disks tangent
to the real line at `r ∈ ℚ` (together with `r`) form a fundamental system of neighbourhoods of `r`,
and the strips `{z | Im z > y}` (together with `∞`) form one of `∞`. The modular group `SL₂(ℤ)` acts
on `ℍ*` by Möbius transformations, by homeomorphisms.

Both kinds of basic neighbourhood of a cusp `c` are horoballs `{z | A < height c z}` for the height
function `height ∞ z = Im z`, `height r z = Im z / |z - r|²`, and `γ ∈ SL₂(ℤ)` scales heights:
`height (γ c) (γ z) = μ · height c z` for a constant `μ > 0` depending only on `γ` and `c`. This is
what makes the action continuous at the cusps.

The LMFDB also says that `SL₂(ℤ)` acts properly discontinuously on `ℍ` and on `ℍ*`. On `ℍ` this is
Mathlib's instance `ProperlyDiscontinuousSMul 𝒮ℒ ℍ`, for the image `𝒮ℒ` of `SL₂(ℤ)` in `GL₂(ℝ)`.
On `ℍ*` it is false (`not_properlyDiscontinuousSMul`): the stabiliser of the cusp `∞` contains the
infinitely many translations `z ↦ z + n`.

## Main definitions

* `UpperHalfPlane.Completed` (LMFDB `mf.upper_half_plane`): the completed upper half-plane, with its
  topology and its action of `SL₂(ℤ)`.
* `UpperHalfPlane.Completed.height`, `UpperHalfPlane.Completed.horoball`: the heights above a cusp
  and the horoballs at a cusp.

## Main results

* `UpperHalfPlane.Completed.isOpenEmbedding_ofUpperHalfPlane`: `ℍ` is an open subspace of `ℍ*`.
* `UpperHalfPlane.Completed.horoball_ratCast`: the horoballs at `r ∈ ℚ` are the disks tangent to the
  real line at `r`.
* `UpperHalfPlane.Completed.hasBasis_nhds_cusp`: the horoballs at a cusp form a fundamental system
  of its neighbourhoods.
* `UpperHalfPlane.Completed.hasBasis_nhds_infty`: the strips form a fundamental system of
  neighbourhoods of `∞`.
* `UpperHalfPlane.Completed.hasBasis_nhds_ratCast`: the disks tangent to the real line at `r` form a
  fundamental system of neighbourhoods of `r ∈ ℚ`.
* `UpperHalfPlane.Completed.height_smul_smul`: `SL₂(ℤ)` scales the heights above the cusps.
* The instance `ContinuousConstSMul SL(2, ℤ) UpperHalfPlane.Completed`: `SL₂(ℤ)` acts on `ℍ*` by
  homeomorphisms.
* `UpperHalfPlane.Completed.not_properlyDiscontinuousSMul`: `SL₂(ℤ)` does not act properly
  discontinuously on `ℍ*`.
-/

open Filter Set Topology OnePoint Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane

namespace UpperHalfPlane

/-- The **completed upper half-plane** `ℍ* = ℍ ∪ ℚ ∪ {∞}` (LMFDB `mf.upper_half_plane`): the points
of the upper half-plane `ℍ` together with the cusps, the points of `ℚ ∪ {∞} = OnePoint ℚ`. Its
topology (`hasBasis_nhds_infty`, `hasBasis_nhds_ratCast`, `isOpenEmbedding_ofUpperHalfPlane`) and
its action of `SL₂(ℤ)` (`smul_ofUpperHalfPlane`, `smul_cusp`) are those of the LMFDB. -/
inductive Completed
  /-- A point of the upper half-plane. -/
  | ofUpperHalfPlane (z : ℍ)
  /-- A cusp: a rational number or `∞`. -/
  | cusp (c : OnePoint ℚ)

namespace Completed

variable (γ : SL(2, ℤ)) (c : OnePoint ℚ) (r : ℚ) (z : ℍ) (A : ℝ)

/-- The **height** of `z ∈ ℍ` above a cusp `c`: `Im z` above `∞`, and `Im z / |z - r|²` above
`r ∈ ℚ`. The horoballs `{z | A < height c z}` are the strips at `∞` and the disks tangent to the
real line at `r` (`horoball_ratCast`). -/
noncomputable def height : ℝ :=
  c.elim z.im fun r ↦ z.im / Complex.normSq ((z : ℂ) - r)

/-- The **horoball** of height `A` at a cusp `c`: the points of `ℍ` of height above `c` greater
than `A`. -/
def horoball : Set ℍ :=
  {z | A < height c z}

@[simp]
lemma height_infty : height ∞ z = z.im :=
  rfl

@[simp]
lemma height_ratCast : height r z = z.im / Complex.normSq ((z : ℂ) - r) :=
  rfl

lemma normSq_sub_ratCast_pos : 0 < Complex.normSq ((z : ℂ) - r) :=
  Complex.normSq_pos.mpr <| sub_ne_zero.mpr <| mod_cast z.ne_ofReal r

lemma height_pos : 0 < height c z := by
  cases c with
  | infty => exact z.im_pos
  | coe r => exact div_pos z.im_pos (normSq_sub_ratCast_pos r z)

lemma continuous_height : Continuous (height c) := by
  cases c with
  | infty => exact continuous_im
  | coe r => exact continuous_im.div (by fun_prop) fun z ↦ (normSq_sub_ratCast_pos r z).ne'

lemma isOpen_horoball : IsOpen (horoball c A) :=
  isOpen_lt continuous_const (continuous_height c)

lemma horoball_antitone : Antitone (horoball c) :=
  fun _ _ h _ hz ↦ h.trans_lt hz

variable {A} in
/-- **The horoballs at `r ∈ ℚ` are the disks tangent to the real line at `r`**: for `A > 0`, the
horoball of height `A` at `r` is the open disk of centre `r + i / (2A)` and radius `1 / (2A)`. -/
lemma horoball_ratCast (hA : 0 < A) :
    horoball r A = {z : ℍ | dist (z : ℂ) (r + (2 * A)⁻¹ * Complex.I) < (2 * A)⁻¹} := by
  ext z
  rw [horoball, mem_ofPred_eq, mem_ofPred_eq, height_ratCast,
    lt_div_iff₀ (normSq_sub_ratCast_pos r z), Complex.dist_eq, Complex.norm_def,
    Real.sqrt_lt' (by positivity)]
  simp [Complex.normSq_apply]
  have hρ : A * (A⁻¹ * 2⁻¹) = 2⁻¹ := by
    rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
  have hρ₀ : 0 < A⁻¹ * 2⁻¹ := by positivity
  constructor <;> intro h
  · nlinarith [mul_lt_mul_of_pos_left h hρ₀]
  · nlinarith [mul_lt_mul_of_pos_left h hA]

/-- The neighbourhood filters of the topology of `ℍ*`. -/
private noncomputable def nhdsAux : Completed → Filter Completed
  | ofUpperHalfPlane z => map ofUpperHalfPlane (𝓝 z)
  | cusp c => ⨅ A ∈ Ioi (0 : ℝ), 𝓟 (insert (cusp c) (ofUpperHalfPlane '' horoball c A))

private lemma hasBasis_nhdsAux_cusp : (nhdsAux (cusp c)).HasBasis (fun A : ℝ ↦ 0 < A) fun A ↦ insert
    (cusp c) (ofUpperHalfPlane '' horoball c A) := by
  refine hasBasis_biInf_principal (fun A₁ hA₁ A₂ _ ↦
    ⟨max A₁ A₂, mem_Ioi.mpr (lt_max_of_lt_left (mem_Ioi.mp hA₁)), ?_, ?_⟩) nonempty_Ioi
  · exact insert_subset_insert (image_mono (horoball_antitone c (le_max_left A₁ A₂)))
  · exact insert_subset_insert (image_mono (horoball_antitone c (le_max_right A₁ A₂)))

noncomputable instance : TopologicalSpace Completed :=
  TopologicalSpace.mkOfNhds nhdsAux

private lemma nhds_eq_nhdsAux (x : Completed) : 𝓝 x = nhdsAux x := by
  refine TopologicalSpace.nhds_mkOfNhds _ _ (fun y ↦ ?_) fun y s hs ↦ ?_
  · cases y with
    | ofUpperHalfPlane z => exact map_mono (pure_le_nhds z)
    | cusp c => exact (hasBasis_nhdsAux_cusp c).ge_iff.mpr fun _ _ ↦ mem_insert _ _
  cases y with
  | ofUpperHalfPlane z => exact eventually_map.mpr (Eventually.eventually_nhds hs)
  | cusp c =>
    rcases (hasBasis_nhdsAux_cusp c).mem_iff.mp hs with ⟨A, hA, hAs⟩
    refine Filter.mem_of_superset ((hasBasis_nhdsAux_cusp c).mem_of_mem hA) fun x hx ↦ ?_
    rcases hx with rfl | ⟨z, hz, rfl⟩
    · exact hs
    · exact Filter.mem_of_superset ((isOpen_horoball c A).mem_nhds hz)
        fun w hw ↦ hAs (mem_insert_of_mem _ (mem_image_of_mem ofUpperHalfPlane hw))

lemma nhds_ofUpperHalfPlane : 𝓝 (ofUpperHalfPlane z) = map ofUpperHalfPlane (𝓝 z) :=
  nhds_eq_nhdsAux _

/-- **The horoballs form a fundamental system of neighbourhoods of a cusp.** -/
lemma hasBasis_nhds_cusp : (𝓝 (cusp c)).HasBasis (fun A : ℝ ↦ 0 < A) fun A ↦ insert (cusp c)
    (ofUpperHalfPlane '' horoball c A) :=
  nhds_eq_nhdsAux (cusp c) ▸ hasBasis_nhdsAux_cusp c

/-- **The strips form a fundamental system of neighbourhoods of `∞`**: the sets
`{z | Im z > y} ∪ {∞}`, `y > 0`. -/
lemma hasBasis_nhds_infty : (𝓝 (cusp ∞)).HasBasis (fun y : ℝ ↦ 0 < y) fun y ↦ insert (cusp ∞)
    (ofUpperHalfPlane '' {z | y < z.im}) :=
  hasBasis_nhds_cusp ∞

/-- **The tangent disks form a fundamental system of neighbourhoods of `r ∈ ℚ`**: the sets
`D ∪ {r}`, for `D` the open disks tangent to the real line at `r`, of centre `r + iρ` and
radius `ρ > 0`. -/
lemma hasBasis_nhds_ratCast : (𝓝 (cusp r)).HasBasis (fun ρ : ℝ ↦ 0 < ρ) fun ρ ↦ insert (cusp r)
    (ofUpperHalfPlane '' {z : ℍ | dist (z : ℂ) (r + ρ * Complex.I) < ρ}) := by
  refine (hasBasis_nhds_cusp r).to_hasBasis (fun A hA ↦ ⟨(2 * A)⁻¹, by positivity, ?_⟩)
    fun ρ hρ ↦ ⟨(2 * ρ)⁻¹, by positivity, ?_⟩
  · rw [horoball_ratCast r hA]
  · rw [horoball_ratCast r (by positivity), mul_inv, inv_inv, inv_mul_cancel_left₀ two_ne_zero]

/-- **The upper half-plane is an open subspace of `ℍ*`.** -/
lemma isOpenEmbedding_ofUpperHalfPlane : IsOpenEmbedding ofUpperHalfPlane := by
  refine .of_continuous_injective_isOpenMap ?_ (fun _ _ ↦ ofUpperHalfPlane.inj) fun U hU ↦ ?_
  · exact continuous_iff_continuousAt.mpr fun z ↦ (nhds_ofUpperHalfPlane z).ge
  · refine isOpen_iff_mem_nhds.mpr <| forall_mem_image.mpr fun z hz ↦ ?_
    rw [nhds_ofUpperHalfPlane]
    exact image_mem_map (hU.mem_nhds hz)

/-! ### The action of `SL₂(ℤ)` -/

noncomputable instance : SMul SL(2, ℤ) Completed where
  smul γ
    | ofUpperHalfPlane z => ofUpperHalfPlane (γ • z)
    | cusp c => cusp (mapGL ℚ γ • c)

@[simp]
lemma smul_ofUpperHalfPlane : γ • ofUpperHalfPlane z = ofUpperHalfPlane (γ • z) :=
  rfl

@[simp]
lemma smul_cusp : γ • cusp c = cusp (mapGL ℚ γ • c) :=
  rfl

noncomputable instance : MulAction SL(2, ℤ) Completed where
  one_smul x := by cases x <;> simp
  mul_smul γ γ' x := by cases x <;> simp [mul_smul]

private lemma det_eq : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
  (Matrix.det_fin_two _).symm.trans γ.det_coe

private lemma det_eq_complex : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
  mod_cast det_eq γ

private lemma coe_smul_eq :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [coe_specialLinearGroup_apply]
  simp

private lemma im_smul_eq : (γ • z).im = z.im / Complex.normSq ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [MulAction.compHom_smul_def, im_smul_eq_div_normSq, det_mapGL]
  simp [denom]

private lemma denom_ne_zero' : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  simpa [denom] using z.denom_ne_zero (mapGL ℝ γ)

private lemma smul_infty_eq :
    mapGL ℚ γ • (∞ : OnePoint ℚ) = if γ 1 0 = 0 then ∞ else ((γ 0 0 / γ 1 0 : ℚ) : OnePoint ℚ) := by
  rw [smul_infty_eq_ite]
  simp

private lemma smul_ratCast_eq : mapGL ℚ γ • (r : OnePoint ℚ) = if γ 1 0 * r + γ 1 1 = 0 then ∞
    else (((γ 0 0 * r + γ 0 1) / (γ 1 0 * r + γ 1 1) : ℚ) : OnePoint ℚ) := by
  rw [smul_some_eq_ite]
  simp

private lemma height_smul_infty_of_eq_zero (h : γ 1 0 = 0) :
    height (mapGL ℚ γ • ∞) (γ • z) = height ∞ z := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by simpa [h] using det_eq γ
  rw [smul_infty_eq, ite_eq_left h, height_infty, height_infty, im_smul_eq, h]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, hd⟩ | ⟨-, hd⟩ <;> simp [hd]

private lemma height_smul_infty_of_ne_zero (h : γ 1 0 ≠ 0) :
    height (mapGL ℚ γ • ∞) (γ • z) = (γ 1 0 : ℝ) ^ 2 * height ∞ z := by
  have hc : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast h
  have hdiff : ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) - ((γ 0 0 / γ 1 0 : ℚ) : ℂ) =
      -1 / (γ 1 0 * ((γ 1 0 : ℂ) * z + γ 1 1)) := by
    push_cast
    rw [div_sub_div _ _ (denom_ne_zero' γ z) hc]
    congr 1
    · linear_combination -det_eq_complex γ
    · ring1
  rw [smul_infty_eq, ite_eq_right h, height_ratCast, height_infty, im_smul_eq, coe_smul_eq, hdiff,
    Complex.normSq_div, Complex.normSq_neg, Complex.normSq_one, Complex.normSq_mul,
    Complex.normSq_intCast]
  have hn : Complex.normSq ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 :=
    Complex.normSq_pos.mpr (denom_ne_zero' γ z) |>.ne'
  field_simp

variable {r}

private lemma ne_zero_of_add_eq_zero (h : γ 1 0 * r + γ 1 1 = 0) : γ 1 0 ≠ 0 := by
  intro h0
  rw [h0, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h
  simpa [h0, h] using det_eq γ

private lemma height_smul_ratCast_of_eq_zero (h : γ 1 0 * r + γ 1 1 = 0) :
    height (mapGL ℚ γ • ↑r) (γ • z) = ((γ 1 0 : ℝ) ^ 2)⁻¹ * height r z := by
  have hC : (γ 1 0 : ℂ) * r + γ 1 1 = 0 := by exact_mod_cast h
  have hcz : (γ 1 0 : ℂ) * z + γ 1 1 = γ 1 0 * (z - r) := by linear_combination hC
  rw [smul_ratCast_eq, ite_eq_left h, height_infty, height_ratCast, im_smul_eq, hcz,
    Complex.normSq_mul, Complex.normSq_intCast]
  field_simp

private lemma height_smul_ratCast_of_ne_zero (h : γ 1 0 * r + γ 1 1 ≠ 0) :
    height (mapGL ℚ γ • ↑r) (γ • z) = ((γ 1 0 * r + γ 1 1 : ℚ) : ℝ) ^ 2 * height r z := by
  have hC : ((γ 1 0 * r + γ 1 1 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast h
  have hdiff : ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) -
      (((γ 0 0 * r + γ 0 1) / (γ 1 0 * r + γ 1 1) : ℚ) : ℂ) =
      (z - r) / (((γ 1 0 : ℂ) * z + γ 1 1) * ((γ 1 0 * r + γ 1 1 : ℚ) : ℂ)) := by
    rw [Rat.cast_div, div_sub_div _ _ (denom_ne_zero' γ z) hC]
    congr 1
    push_cast
    linear_combination ((z : ℂ) - r) * det_eq_complex γ
  rw [smul_ratCast_eq, ite_eq_right h, height_ratCast, height_ratCast, im_smul_eq, coe_smul_eq,
    hdiff, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ratCast]
  have hn : Complex.normSq ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 :=
    Complex.normSq_pos.mpr (denom_ne_zero' γ z) |>.ne'
  field_simp

/-- **`SL₂(ℤ)` scales the heights above the cusps**: for `γ ∈ SL₂(ℤ)` and a cusp `c` there is
`μ > 0` with `height (γ c) (γ w) = μ · height c w` for every `w ∈ ℍ`. Hence `γ` maps the horoball
of height `A` at `c` onto the horoball of height `μA` at `γ c`. -/
lemma height_smul_smul :
    ∃ μ : ℝ, 0 < μ ∧ ∀ w : ℍ, height (mapGL ℚ γ • c) (γ • w) = μ * height c w := by
  cases c with
  | infty =>
    by_cases h : γ 1 0 = 0
    · exact ⟨1, one_pos, fun w ↦ by rw [height_smul_infty_of_eq_zero γ w h, one_mul]⟩
    · have hc : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast h
      exact ⟨(γ 1 0 : ℝ) ^ 2, by positivity, fun w ↦ height_smul_infty_of_ne_zero γ w h⟩
  | coe r =>
    by_cases h : γ 1 0 * r + γ 1 1 = 0
    · have hc : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast ne_zero_of_add_eq_zero γ h
      exact ⟨((γ 1 0 : ℝ) ^ 2)⁻¹, by positivity, fun w ↦ height_smul_ratCast_of_eq_zero γ w h⟩
    · exact ⟨_, by positivity, fun w ↦ height_smul_ratCast_of_ne_zero γ w h⟩

instance : ContinuousConstSMul SL(2, ℤ) Completed where
  continuous_const_smul γ := by
    refine continuous_iff_continuousAt.mpr fun x ↦ ?_
    cases x with
    | ofUpperHalfPlane z =>
      rw [ContinuousAt, nhds_ofUpperHalfPlane, smul_ofUpperHalfPlane, nhds_ofUpperHalfPlane,
        tendsto_map'_iff]
      exact tendsto_map.comp (continuous_const_smul (mapGL ℝ γ)).continuousAt
    | cusp c =>
      rcases height_smul_smul γ c with ⟨μ, hμ, hheight⟩
      refine ((hasBasis_nhds_cusp c).tendsto_iff (hasBasis_nhds_cusp (mapGL ℚ γ • c))).mpr
        fun B hB ↦ ⟨B / μ, by positivity, ?_⟩
      rintro _ (rfl | ⟨w, hw, rfl⟩)
      · exact mem_insert _ _
      · refine mem_insert_of_mem _ ⟨γ • w, ?_, rfl⟩
        rw [horoball, mem_ofPred_eq, hheight]
        exact (div_lt_iff₀' hμ).mp hw

/-- **`SL₂(ℤ)` does not act properly discontinuously on `ℍ*`**, although the LMFDB says it does: the
stabiliser of the cusp `∞` contains the infinitely many translations `T ^ n`, `n ∈ ℤ`. -/
lemma not_properlyDiscontinuousSMul : ¬ProperlyDiscontinuousSMul SL(2, ℤ) Completed := by
  intro h
  have hinj : Function.Injective (ModularGroup.T ^ · : ℤ → SL(2, ℤ)) := fun m n hmn ↦ by
    simpa [ModularGroup.coe_T_zpow] using congrArg (fun g : SL(2, ℤ) ↦ g 0 1) hmn
  have hfin : {γ : SL(2, ℤ) | ((γ • ·) '' {cusp ∞} ∩ {cusp ∞}).Nonempty}.Finite :=
    h.finite_disjoint_inter_image isCompact_singleton isCompact_singleton
  refine infinite_range_of_injective hinj (hfin.subset ?_)
  rintro _ ⟨n, rfl⟩
  refine ⟨cusp ∞, ⟨cusp ∞, rfl, congrArg cusp <| (smul_infty_eq _).trans <| ite_eq_left ?_⟩, rfl⟩
  simp [ModularGroup.coe_T_zpow]

end Completed

end UpperHalfPlane
