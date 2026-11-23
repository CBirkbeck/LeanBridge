import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The sphere measure is invariant under linear isometries

Let `μ` be an additive Haar measure on a finite-dimensional real normed space `E`, and `μ.toSphere`
the measure on the unit sphere with `μ.toSphere s = dim E · μ ((0, 1) • s)`. A linear isometry
equivalence `g` of `E` maps the unit sphere onto itself; if it also preserves `μ`, the induced map
of the sphere preserves `μ.toSphere`, since `(0, 1) • g⁻¹(s) = g⁻¹((0, 1) • s)` has the measure of
`(0, 1) • s`. So integrals and averages over the unit sphere are invariant under such maps, for
instance under every linear isometry of a Euclidean space, which preserves its volume.

Tau Ceti's main branch, past the pin, has the more general `LinearIsometryEquiv.map_toSphere`: a
linear isometric equivalence `f` carries `μ.toSphere` to `(μ.map f).toSphere`. At the bump the
first result below follows from it.

## Main definitions

* `LinearIsometryEquiv.sphereHomeomorph`: the homeomorphism of the unit sphere induced by a linear
  isometry equivalence.

## Main results

* `LinearIsometryEquiv.measurePreserving_sphereHomeomorph`: it preserves `μ.toSphere`.
* `LinearIsometryEquiv.average_toSphere_comp`: averages over the unit sphere are invariant under
  linear isometries preserving `μ`.
-/

open MeasureTheory Metric Set

open scoped Pointwise

namespace LinearIsometryEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E ≃ₗᵢ[ℝ] E)

/-- The homeomorphism of the unit sphere of `E` induced by a linear isometry equivalence `g` of
`E`. -/
def sphereHomeomorph : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  g.toHomeomorph.subtype fun x ↦ by simp

@[simp]
lemma coe_sphereHomeomorph_apply (x : sphere (0 : E) 1) : (g.sphereHomeomorph x : E) = g x :=
  rfl

lemma image_coe_preimage_sphereHomeomorph (s : Set (sphere (0 : E) 1)) :
    ((↑) '' (g.sphereHomeomorph ⁻¹' s) : Set E) = g ⁻¹' ((↑) '' s) := by
  ext x
  refine ⟨?_, fun ⟨y, hy, hgy⟩ ↦ ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g.sphereHomeomorph y, hy, rfl⟩
  have hx : x ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, ← g.norm_map, ← hgy, ← mem_sphere_zero_iff_norm]
    exact y.2
  have hy' : g.sphereHomeomorph ⟨x, hx⟩ = y := Subtype.ext hgy.symm
  exact ⟨⟨x, hx⟩, by rwa [mem_preimage, hy'], rfl⟩

lemma smul_preimage (T : Set ℝ) (A : Set E) : T • g ⁻¹' A = g ⁻¹' (T • A) := by
  ext x
  simp only [mem_smul, mem_preimage]
  refine ⟨fun ⟨t, ht, a, ha, hx⟩ ↦ ⟨t, ht, g a, ha, by rw [← hx, map_smul]⟩,
    fun ⟨t, ht, b, hb, hx⟩ ↦ ⟨t, ht, g.symm b, by rwa [apply_symm_apply], ?_⟩⟩
  rw [← map_smul, hx, symm_apply_apply]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- **Linear isometries preserve the sphere measure**: if a linear isometry equivalence `g` of `E`
preserves the measure `μ`, the induced homeomorphism of the unit sphere preserves `μ.toSphere`. -/
lemma measurePreserving_sphereHomeomorph (hg : MeasurePreserving g μ μ) :
    MeasurePreserving g.sphereHomeomorph μ.toSphere μ.toSphere := by
  refine ⟨g.sphereHomeomorph.continuous.measurable, Measure.ext fun s hs ↦ ?_⟩
  have hg' : MeasurePreserving g.toHomeomorph.toMeasurableEquiv μ μ := hg
  rw [Measure.map_apply g.sphereHomeomorph.continuous.measurable hs,
    Measure.toSphere_apply' _ (g.sphereHomeomorph.continuous.measurable hs),
    Measure.toSphere_apply' _ hs, image_coe_preimage_sphereHomeomorph, smul_preimage]
  exact congrArg _ (hg'.measure_preimage_equiv _)

/-- **Averages over the unit sphere are invariant under linear isometries**: if a linear isometry
equivalence `g` of `E` preserves `μ`, then `⨍ f(g x) dσ(x) = ⨍ f(x) dσ(x)` over the unit sphere,
`σ = μ.toSphere`. -/
lemma average_toSphere_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hg : MeasurePreserving g μ μ) (f : sphere (0 : E) 1 → F) :
    ⨍ x, f (g.sphereHomeomorph x) ∂μ.toSphere = ⨍ x, f x ∂μ.toSphere := by
  rw [average_eq, average_eq, (g.measurePreserving_sphereHomeomorph hg).integral_comp
    g.sphereHomeomorph.measurableEmbedding]

end LinearIsometryEquiv
