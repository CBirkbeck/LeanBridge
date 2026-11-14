import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# The Möbius transformation of the LMFDB's portraits

The LMFDB draws a classical modular form, through its trace form (LMFDB `cmf.picture_description`,
`portrait.cmf`), or a Maass form (LMFDB `portrait.maass`) on the unit disc `𝔻`: the point `z ∈ 𝔻`
is coloured by the value of the form at `μ(z)` for the Möbius transformation
`μ(z) = (1 - iz) / (z - i)`. It is the action on the Riemann sphere `ℂ ∪ {∞}` (`OnePoint ℂ`) of the
matrix `!![-i, 1; 1, -i]`, of determinant `-2`, and it maps `𝔻` bijectively onto the upper
half-plane `ℍ`, since `μ(z) = C(-iz)` for the inverse Cayley transform `C(w) = i(1 + w) / (1 - w)`
of Tau Ceti (`TauCeti.bijOn_I_mul_one_add_div_one_sub_ball`) and `z ↦ -iz` is a rotation of `𝔻`.

It keeps the apparent orientation of the imaginary axis: it maps the vertical diameter
`{it : -1 < t < 1}` onto the positive imaginary axis, `μ(it) = i(1 + t) / (1 - t)`, increasingly,
from `μ(-i) = 0` at the bottom of the disc through `μ(0) = i` at its centre to `μ(i) = ∞` at its
top, the cusp `i∞` of `ℍ`. More precisely, the neighbourhoods of `i∞` in `ℍ`, the horoballs
`{w : Im w > (1 - r) / r}`, are the images of the horodiscs at `i`, the discs `B(i(1 - r), r)` of
radius `r ≤ 1` tangent to the unit circle at `i`, since `Im μ(z) = (1 - |z|²) / |z - i|²`.

## Main definitions

* `UpperHalfPlane.portraitMoebius` (LMFDB `cmf.picture_description`, `portrait.cmf`,
  `portrait.maass`): the Möbius transformation `μ(z) = (1 - iz) / (z - i)`.
* `UpperHalfPlane.portraitMoebiusMatrix`: its matrix `!![-i, 1; 1, -i]` in `GL(2, ℂ)`.

## Main results

* `UpperHalfPlane.bijOn_portraitMoebius`: `μ` maps the unit disc bijectively onto `ℍ`.
* `UpperHalfPlane.portraitMoebiusMatrix_smul_coe`: `μ` is the Möbius transformation of its matrix.
* `UpperHalfPlane.portraitMoebiusMatrix_smul_I`: the top `i` of the disc goes to `∞`.
* `UpperHalfPlane.portraitMoebius_neg_I`: the bottom `-i` of the disc goes to `0`.
* `UpperHalfPlane.portraitMoebius_zero`: the centre of the disc goes to `i`.
* `UpperHalfPlane.portraitMoebius_I_mul`: `μ(it) = i(1 + t) / (1 - t)` on the imaginary axis.
* `UpperHalfPlane.strictMonoOn_im_portraitMoebius_I_mul`: `μ` keeps the orientation of the
  vertical diameter.
* `UpperHalfPlane.tendsto_im_portraitMoebius_I_mul`: `μ(it)` tends to `i∞` as `t` tends to `1`.
* `UpperHalfPlane.im_portraitMoebius`: `Im μ(z) = (1 - |z|²) / |z - i|²`.
* `UpperHalfPlane.bijOn_portraitMoebius_ball`: `μ` maps the horodisc `B(i(1 - r), r)` onto the
  horoball `{w : Im w > (1 - r) / r}`.
-/

open Complex Filter Matrix Metric Set Topology

namespace UpperHalfPlane

/-- The **Möbius transformation** `μ(z) = (1 - iz) / (z - i)` (LMFDB `cmf.picture_description`,
`portrait.cmf`, `portrait.maass`), which maps the unit disc onto the upper half-plane
(`bijOn_portraitMoebius`): the LMFDB colours a point `z` of the unit disc by the value of a
modular form or a Maass form at `μ(z)`. It is the Möbius transformation of
`portraitMoebiusMatrix` (`portraitMoebiusMatrix_smul_coe`), which sends the pole `i` to `∞`
(`portraitMoebiusMatrix_smul_I`); here `μ(i)` is the junk value `0`. -/
noncomputable def portraitMoebius (z : ℂ) : ℂ :=
  (1 - Complex.I * z) / (z - Complex.I)

/-- The matrix `!![-i, 1; 1, -i]` of the Möbius transformation `portraitMoebius`, of
determinant `-2`. -/
noncomputable def portraitMoebiusMatrix : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![-Complex.I, 1; 1, -Complex.I] <| by
    rw [det_fin_two_of, neg_mul_neg, I_mul_I, mul_one]
    norm_num

variable {z : ℂ} {r : ℝ} (t : ℝ)

@[simp]
lemma val_portraitMoebiusMatrix : portraitMoebiusMatrix.val = !![-Complex.I, 1; 1, -Complex.I] :=
  rfl

variable (z) in
lemma portraitMoebius_eq_comp :
    portraitMoebius z = Complex.I * (1 + -Complex.I * z) / (1 - -Complex.I * z) := by
  have h : 1 - -Complex.I * z = Complex.I * (z - Complex.I) := by
    rw [mul_sub, I_mul_I]
    ring1
  rw [h, mul_div_mul_left _ _ I_ne_zero, portraitMoebius, neg_mul, ← sub_eq_add_neg]

/-- **`μ` maps the unit disc bijectively onto the upper half-plane** (LMFDB
`cmf.picture_description`, `portrait.cmf`, `portrait.maass`: "`μ : 𝒟 ⟶ ℋ`"): it is the inverse
Cayley transform `w ↦ i(1 + w) / (1 - w)` after the rotation `z ↦ -iz` of the disc. -/
lemma bijOn_portraitMoebius : BijOn portraitMoebius (ball 0 1) upperHalfPlaneSet := by
  have hrot : BijOn (fun z : ℂ ↦ -Complex.I * z) (ball 0 1) (ball 0 1) := by
    refine ⟨fun z hz ↦ ?_, fun z _ w _ h ↦ ?_, fun w hw ↦ ⟨Complex.I * w, ?_, ?_⟩⟩
    · simpa using hz
    · simpa using h
    · simpa using hw
    · dsimp only
      rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  have h :
      portraitMoebius = (fun w : ℂ ↦ Complex.I * (1 + w) / (1 - w)) ∘ fun z : ℂ ↦ -Complex.I * z :=
    funext portraitMoebius_eq_comp
  rw [h]
  exact TauCeti.bijOn_I_mul_one_add_div_one_sub_ball.comp hrot

/-- **`μ` is the Möbius transformation of the matrix `!![-i, 1; 1, -i]`** on the Riemann sphere
`ℂ ∪ {∞}` (LMFDB `cmf.picture_description`, `portrait.cmf`, `portrait.maass`: "the Möbius
transform `μ`"), away from its pole `i`. -/
lemma portraitMoebiusMatrix_smul_coe (hz : z ≠ Complex.I) :
    portraitMoebiusMatrix • (z : OnePoint ℂ) = (portraitMoebius z : OnePoint ℂ) := by
  have hz' : 1 * z + -Complex.I ≠ 0 := by
    rw [one_mul, ← sub_eq_add_neg]
    exact sub_ne_zero.mpr hz
  rw [OnePoint.smul_some_eq_ite]
  simp only [val_portraitMoebiusMatrix, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one]
  rw [ite_eq_right_of_eq_false _ _ (eq_false hz'), portraitMoebius, one_mul, ← sub_eq_add_neg,
    neg_mul, neg_add_eq_sub]

/-- **The top `i` of the disc goes to `∞`** (LMFDB `portrait.maass`: "the point `(0, 1)` in `𝒟`
corresponds to `i∞` in `ℋ`"): the Möbius transformation of `portraitMoebiusMatrix` sends `i` to
the point `∞` of the Riemann sphere, the cusp `i∞` of `ℍ`. -/
lemma portraitMoebiusMatrix_smul_I :
    portraitMoebiusMatrix • (Complex.I : OnePoint ℂ) = OnePoint.infty := by
  rw [OnePoint.smul_some_eq_ite, ite_eq_left_of_eq_true _ _ (eq_true ?_)]
  simp

/-- **The bottom `-i` of the disc goes to `0`** (LMFDB `portrait.maass`: "the point `(0, -1)` in
`𝒟` corresponds to `0` in `ℋ`"). -/
lemma portraitMoebius_neg_I : portraitMoebius (-Complex.I) = 0 := by
  simp [portraitMoebius]

/-- **The centre of the disc goes to `i`** (LMFDB `portrait.maass`: "the center of `𝒟` corresponds
to `i` in `ℋ`"). -/
lemma portraitMoebius_zero : portraitMoebius 0 = Complex.I := by
  simp [portraitMoebius]

/-- **`μ` on the imaginary axis**: `μ(it) = i(1 + t) / (1 - t)` for every real `t` (both sides
being `0` at `t = 1`), so `μ` maps the vertical diameter of the disc onto the positive imaginary
axis (LMFDB `portrait.maass`). -/
lemma portraitMoebius_I_mul :
    portraitMoebius (Complex.I * t) = Complex.I * (((1 + t) / (1 - t) : ℝ) : ℂ) := by
  rcases eq_or_ne t 1 with rfl | ht
  · simp [portraitMoebius]
  have h1 : (1 : ℂ) - t ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht.symm)
  have h2 : Complex.I * t - Complex.I ≠ 0 := by
    rw [← mul_sub_one]
    exact mul_ne_zero I_ne_zero (sub_ne_zero.mpr (by exact_mod_cast ht))
  rw [portraitMoebius, ofReal_div, ofReal_add, ofReal_sub, ofReal_one, div_eq_iff h2,
    mul_div_assoc', div_mul_eq_mul_div, eq_div_iff h1]
  linear_combination (1 - (t : ℂ)) * I_mul_I

lemma im_portraitMoebius_I_mul : (portraitMoebius (Complex.I * t)).im = (1 + t) / (1 - t) := by
  rw [portraitMoebius_I_mul, mul_im, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im, zero_mul,
    one_mul, zero_add]

/-- **`μ` keeps the orientation of the imaginary axis** (LMFDB `portrait.maass`: "This transform
preserves the apparent orientation of the imaginary axis in `ℋ`"): along the vertical diameter
`{it : -1 < t < 1}` of the disc, from bottom to top, the imaginary part of `μ(it)` increases. -/
lemma strictMonoOn_im_portraitMoebius_I_mul :
    StrictMonoOn (fun t : ℝ ↦ (portraitMoebius (Complex.I * t)).im) (Ioo (-1) 1) := by
  intro s hs t ht hst
  simp only [im_portraitMoebius_I_mul]
  rw [div_lt_div_iff₀ (by linarith [hs.2]) (by linarith [ht.2])]
  nlinarith

/-- **The top of the vertical diameter goes to `i∞`** (LMFDB `portrait.maass`): as `t` tends to `1`
from below, the imaginary part of `μ(it)` tends to `∞`. -/
lemma tendsto_im_portraitMoebius_I_mul :
    Tendsto (fun t : ℝ ↦ (portraitMoebius (Complex.I * t)).im) (𝓝[<] 1) atTop := by
  simp only [im_portraitMoebius_I_mul]
  have h1 : Tendsto (fun t : ℝ ↦ 1 + t) (𝓝[<] 1) (𝓝 2) := by
    refine ((continuous_const.add continuous_id).tendsto' 1 2 ?_).mono_left nhdsWithin_le_nhds
    norm_num
  have h2 : Tendsto (fun t : ℝ ↦ 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.sub continuous_id).tendsto' 1 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun t ht ↦ mem_Ioi.mpr (sub_pos.mpr ht)
  exact h1.pos_mul_atTop two_pos (tendsto_inv_nhdsGT_zero.comp h2)

variable (z) in
/-- **The imaginary part of `μ(z)` is `(1 - |z|²) / |z - i|²`**: positive exactly inside the unit
disc. -/
lemma im_portraitMoebius : (portraitMoebius z).im = (1 - normSq z) / normSq (z - Complex.I) := by
  rw [portraitMoebius, div_im, ← sub_div]
  congr 1
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, mul_re, mul_im, Complex.I_re,
    Complex.I_im]
  ring1

lemma dist_lt_iff_lt_im_portraitMoebius (hr : 0 < r) (hz : z ≠ Complex.I) :
    dist z (Complex.I * (1 - r : ℝ)) < r ↔ (1 - r) / r < (portraitMoebius z).im := by
  have hD : 0 < normSq (z - Complex.I) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hz)
  rw [im_portraitMoebius, div_lt_div_iff₀ hr hD, dist_eq, ← sq_lt_sq₀ (norm_nonneg _) hr.le,
    Complex.sq_norm]
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, Complex.I_re, Complex.I_im, ofReal_re,
    ofReal_im]
  constructor <;> intro h <;> nlinarith

/-- **`μ` maps the horodisc `B(i(1 - r), r)` onto the horoball `{w : Im w > (1 - r) / r}`**
(LMFDB `portrait.maass`): for `0 < r ≤ 1`, the disc of radius `r` tangent to the unit circle at the
top `i` of the disc goes onto the neighbourhood `{w : Im w > (1 - r) / r}` of the cusp `i∞`, so
that near the top of the disc means near `i∞` in `ℍ`. -/
lemma bijOn_portraitMoebius_ball (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    BijOn portraitMoebius (ball (Complex.I * (1 - r : ℝ)) r) {w | (1 - r) / r < w.im} := by
  have hsub : ball (Complex.I * (1 - r : ℝ)) r ⊆ ball 0 1 := by
    intro z hz
    have hc : dist (Complex.I * (1 - r : ℝ)) 0 = 1 - r := by
      rw [dist_zero_right, norm_mul, norm_I, one_mul, norm_real, Real.norm_of_nonneg (by linarith)]
    exact mem_ball.mpr <| (dist_triangle z _ 0).trans_lt (by linarith [mem_ball.mp hz])
  have hne {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : z ≠ Complex.I := by
    rintro rfl
    simp at hz
  refine ⟨fun z hz ↦ (dist_lt_iff_lt_im_portraitMoebius hr₀ (hne (hsub hz))).mp hz,
    bijOn_portraitMoebius.injOn.mono hsub, fun w hw ↦ ?_⟩
  have hw' : w ∈ upperHalfPlaneSet :=
    (div_nonneg (by linarith) hr₀.le).trans_lt hw
  rcases bijOn_portraitMoebius.surjOn hw' with ⟨z, hz, rfl⟩
  exact ⟨z, (dist_lt_iff_lt_im_portraitMoebius hr₀ (hne hz)).mpr hw, rfl⟩

end UpperHalfPlane
