import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.Cartan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Spherical averages on `GL₂` of a local field, and Gelfand's trick

Let `K` be a compact open subgroup of a topological group `G`, and let `dk` be the Haar measure of
`K` of total mass one (Tau Ceti's `TauCeti.haarProb`). The **spherical average** at `y ∈ G` of a
function `ψ` on `G` is `E_y ψ : h ↦ ∫_K ψ(h k y) dk`. If `ψ` is right invariant under the open
subgroup `K`, then it is locally constant, so that these are integrals of continuous functions, and
`E_y ψ` is again right invariant under `K`.

**Gelfand's trick** is the commutation `E_y E_z ψ = E_z E_y ψ` for such a `ψ`, when `G` has an
anti-automorphism `σ` preserving `K` and all the double cosets `K y K`. Fix `h`, and put
`Θ(y) = (E_y ψ)(h)`. Then `Θ(y k) = Θ(y)` by the invariance of `ψ` and `Θ(k y) = Θ(y)` by the right
invariance of `dk`, so that `Θ(σ y) = Θ(y)`. By Fubini `(E_y E_z ψ)(h)` is
`∫∫ ψ(h k₁ y k₂ z) dk₂ dk₁ = ∫ Θ(y k z) dk`, and this is
`∫ Θ(σ z σ k σ y) dk = ∫ Θ(z k y) dk = (E_z E_y ψ)(h)`, since `σ z ∈ K z K`, `σ y ∈ K y K`, and
since `dk` is invariant under the translations and under `σ`: the image of `dk` under `σ` is again a
Haar measure of total mass one. The integrands of Fubini's theorem are invariant in `k₂` under an
open subgroup of `K`, which has finite index, so the theorem reduces to the exchange of a finite sum
and an integral, with no condition on the topology of `G`.

For a field `L` with a compact open valuation subring `O`, `G = GL₂(L)` and `K = GL₂(O)`, the
anti-automorphism `σ` is the transpose, by the Cartan decomposition. With `d = (1, 0; 0, ϖ)`, the
sum of `ψ` over the `q + 1` cosets of `K d K / K` is `q + 1` times `E_d ψ`, because the sum is right
invariant under `K` and all the cosets are `k d K` with `k ∈ K`. So the Hecke sum commutes with the
spherical averages. Finally, the average of `ψ` twisted by a character of `K` nontrivial on a matrix
`diag(u, 1)` vanishes, as `diag(u, 1)` commutes with the diagonal matrices of the Cartan
decomposition.

## Main definitions

* `MeasureTheory.haarMean`: the average `∫_C f(k) dk` of a function on a compact group. Tau Ceti's
  `TauCeti.haarAverage` is the same integral, bundled as a continuous linear map on `C(C, V)`; the
  version here is on all functions, so that `AdelicGL2.localAverage` is defined on all functions on
  `GL₂(𝔸_F)`, and it is named differently so that both can be used with `TauCeti` open. The Borel
  `σ`-algebra used to define it is a local instance of this file.
* `Subgroup.sphericalAverage`: the spherical average `E_y ψ`.
* `ValuationSubring.transposeHomeomorph`: the transpose on `GL₂(O)`.

## Main results

* `Subgroup.sphericalAverage_comm`: Gelfand's trick.
* `ValuationSubring.heckeSum_eq_card_mul_sphericalAverage`: the Hecke sum is `q + 1` times `E_d`.
* `ValuationSubring.heckeSum_sphericalAverage`: the Hecke sum commutes with the spherical averages.
* `ValuationSubring.haarMean_inv_mul_eq_zero`: the twisted averages vanish.

The instance `CompactSpace O.gl2` says that `GL₂(O)` is compact when `O` is.
-/

open Matrix hiding mul_inv_rev

open GeneralLinearGroup MeasureTheory TauCeti

open MulAction renaming Quotient.smul_mk → quotient_smul_mk

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma IsOpen.continuous_of_forall_mul_eq {U : Subgroup G} {ψ : G → ℂ} (hU : IsOpen (U : Set G))
    (hψ : ∀ x, ∀ u ∈ U, ψ (x * u) = ψ x) : Continuous ψ :=
  IsLocallyConstant.continuous <| (IsLocallyConstant.iff_exists_open ψ).mpr fun x ↦
    ⟨(x⁻¹ * ·) ⁻¹' U, hU.preimage (continuous_const.mul continuous_id), by simp,
      fun y hy ↦ by
        have h : ψ (x * (x⁻¹ * y)) = ψ x := hψ x _ hy
        rwa [mul_inv_cancel_left] at h⟩

namespace MeasureTheory

variable {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
  (f : C → ℂ)

attribute [local instance] borel

local instance : BorelSpace C := ⟨rfl⟩

/-- The **average** `∫_C f(k) dk` of a function `f` on a compact group `C`, for the Haar measure of
total mass one. -/
noncomputable def haarMean : ℂ :=
  ∫ k, f k ∂haarProb C

lemma haarMean_const (c : ℂ) : haarMean (fun _ : C ↦ c) = c := by
  simp [haarMean]

variable {f} in
private lemma integrable_haarProb (hf : Continuous f) : Integrable f (haarProb C) :=
  hf.integrable_of_hasCompactSupport (.of_compactSpace f)

variable {f} in
lemma haarMean_add {g : C → ℂ} (hf : Continuous f) (hg : Continuous g) :
    haarMean (fun k ↦ f k + g k) = haarMean f + haarMean g :=
  integral_add (integrable_haarProb hf) (integrable_haarProb hg)

lemma haarMean_const_mul (c : ℂ) : haarMean (fun k ↦ c * f k) = c * haarMean f :=
  integral_const_mul c f

lemma haarMean_sum {ι : Type*} (s : Finset ι) {F : ι → C → ℂ} (hF : ∀ i ∈ s, Continuous (F i)) :
    haarMean (fun k ↦ ∑ i ∈ s, F i k) = ∑ i ∈ s, haarMean (F i) :=
  integral_finsetSum s fun i hi ↦ integrable_haarProb (hF i hi)

lemma haarMean_mul_left (a : C) : haarMean (fun k ↦ f (a * k)) = haarMean f :=
  integral_mul_left_eq_self f a

lemma haarMean_mul_right (a : C) : haarMean (fun k ↦ f (k * a)) = haarMean f :=
  integral_mul_right_eq_self f a

lemma haarMean_comp_homeomorph (τ : C ≃ₜ C) (hτ : ∀ a b, τ (a * b) = τ b * τ a) :
    haarMean (fun k ↦ f (τ k)) = haarMean f := by
  have hl : ((haarProb C).map τ).IsMulLeftInvariant := ⟨fun g ↦ by
    have he : (g * ·) ∘ τ = τ ∘ (· * τ.symm g) :=
      funext fun k ↦ by simp [hτ]
    rw [Measure.map_map (measurable_const_mul g) τ.measurable, he,
      ← Measure.map_map τ.measurable (measurable_mul_const _), map_mul_right_eq_self]⟩
  have hH : ((haarProb C).map τ).IsHaarMeasure :=
    { toIsMulLeftInvariant := hl
      toIsOpenPosMeasure := τ.continuous.isOpenPosMeasure_map τ.surjective }
  have he : (haarProb C).map τ = haarProb C :=
    eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure C _
  rw [haarMean, ← τ.measurableEmbedding.integral_map, he, haarMean]

variable {U : Subgroup C} {f}

lemma card_mul_haarMean [Fintype (C ⧸ U)] (hU : IsOpen (U : Set C))
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) :
    (Fintype.card (C ⧸ U) : ℂ) * haarMean f = ∑ c : C ⧸ U, f c.out := by
  have hc : Continuous f := hU.continuous_of_forall_mul_eq hf
  have h₁ (k : C) (c : C ⧸ U) : f (k * c.out) = f (k • c).out := by
    have he : k • c = ((k * c.out : C) : C ⧸ U) := by
      rw [← QuotientGroup.out_eq' c, quotient_smul_mk, QuotientGroup.out_eq']
      simp
    rcases QuotientGroup.mk_out_eq_mul U (k * c.out) with ⟨u, hu⟩
    rw [he, hu, hf _ _ u.2]
  have h₂ (k : C) : ∑ c : C ⧸ U, f (k * c.out) = ∑ c : C ⧸ U, f c.out := by
    simp only [h₁]
    exact Equiv.sum_comp (MulAction.toPerm k) fun c : C ⧸ U ↦ f c.out
  have h₃ : (Fintype.card (C ⧸ U) : ℂ) * haarMean f =
      ∑ c : C ⧸ U, haarMean fun k ↦ f (k * c.out) := by
    simp only [haarMean_mul_right]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h₄ : (haarMean fun k ↦ ∑ c : C ⧸ U, f (k * c.out)) =
      ∑ c : C ⧸ U, haarMean fun k ↦ f (k * c.out) :=
    haarMean_sum Finset.univ fun c _ ↦ hc.comp (continuous_id.mul continuous_const)
  rw [h₃, ← h₄]
  simp only [h₂, haarMean_const]

lemma haarMean_comm (hU : IsOpen (U : Set C)) {F : C → C → ℂ}
    (hF : ∀ a b, ∀ u ∈ U, F a (b * u) = F a b) (hF' : ∀ b, Continuous fun a ↦ F a b) :
    haarMean (fun a ↦ haarMean (F a)) = haarMean fun b ↦ haarMean fun a ↦ F a b := by
  have hfin : Finite (C ⧸ U) := U.quotient_finite_of_isOpen hU
  let _ : Fintype (C ⧸ U) := Fintype.ofFinite _
  have h₀ : (Fintype.card (C ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine mul_left_cancel₀ h₀ ?_
  rw [← haarMean_const_mul, card_mul_haarMean hU fun b u hu ↦ ?_]
  · simp only [card_mul_haarMean hU (hF _)]
    rw [haarMean_sum _ fun c _ ↦ hF' _]
  · exact congrArg haarMean (funext fun a ↦ hF a b u hu)

end MeasureTheory

namespace Subgroup

variable (K : Subgroup G) [CompactSpace K]

/-- The **spherical average** `E_y ψ : h ↦ ∫_K ψ(h k y) dk` at `y ∈ G` of a function `ψ` on a group
`G`, for a compact subgroup `K` of `G`. -/
noncomputable def sphericalAverage (y : G) (ψ : G → ℂ) (h : G) : ℂ :=
  haarMean fun k : K ↦ ψ (h * k * y)

variable {K} {ψ : G → ℂ} {y z h k : G}

lemma sphericalAverage_mul (hk : k ∈ K) :
    K.sphericalAverage y ψ (h * k) = K.sphericalAverage y ψ h := by
  refine Eq.trans ?_ (haarMean_mul_left (fun k' : K ↦ ψ (h * k' * y)) ⟨k, hk⟩)
  simp only [sphericalAverage, coe_mul, mul_assoc]

lemma sphericalAverage_mem_mul (hk : k ∈ K) :
    K.sphericalAverage (k * y) ψ h = K.sphericalAverage y ψ h := by
  refine Eq.trans ?_ (haarMean_mul_right (fun k' : K ↦ ψ (h * k' * y)) ⟨k, hk⟩)
  simp only [sphericalAverage, coe_mul, mul_assoc]

lemma sphericalAverage_mul_mem (hψ : ∀ x, ∀ k ∈ K, ψ (x * k) = ψ x) (hk : k ∈ K) :
    K.sphericalAverage (y * k) ψ h = K.sphericalAverage y ψ h := by
  refine congrArg haarMean (funext fun k' ↦ ?_)
  rw [← mul_assoc, hψ _ _ hk]

lemma sphericalAverage_sphericalAverage (hK : IsOpen (K : Set G))
    (hψ : ∀ x, ∀ k ∈ K, ψ (x * k) = ψ x) : K.sphericalAverage y (K.sphericalAverage z ψ) h =
      haarMean fun k : K ↦ K.sphericalAverage (y * k * z) ψ h := by
  let U : Subgroup K := K.comap ((MulAut.conj z⁻¹).toMonoidHom.comp K.subtype)
  have hU : IsOpen (U : Set K) :=
    hK.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hc : Continuous ψ := hK.continuous_of_forall_mul_eq hψ
  simp only [sphericalAverage, mul_assoc]
  refine haarMean_comm (F := fun a b ↦ ψ (h * (a * (y * (b * z))))) hU (fun a b u hu ↦ ?_)
    fun b ↦ hc.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const))
  have hu' : z⁻¹ * u * z ∈ K := by
    simpa [U] using hu
  have he : h * (a * (y * (((b * u : K) : G) * z))) = h * (a * (y * (b * z))) * (z⁻¹ * u * z) := by
    simp only [coe_mul]
    group
  rw [he, hψ _ _ hu']

/-- **Gelfand's trick**: if an anti-automorphism `σ` of `G` preserves `K` and all the double cosets
`K y K`, then the operators `E_y : ψ ↦ (h ↦ ∫_K ψ(h k y) dk)` commute on the functions `ψ` right
invariant under the compact open subgroup `K`. -/
lemma sphericalAverage_comm (hK : IsOpen (K : Set G)) (hψ : ∀ x, ∀ k ∈ K, ψ (x * k) = ψ x)
    {σ : G → G} (hσ : ∀ a b, σ (a * b) = σ b * σ a)
    (hσK : ∀ y, ∃ k₁ ∈ K, ∃ k₂ ∈ K, σ y = k₁ * y * k₂) (τ : K ≃ₜ K)
    (hτ : ∀ k : K, (τ k : G) = σ k) : K.sphericalAverage y (K.sphericalAverage z ψ) h =
      K.sphericalAverage z (K.sphericalAverage y ψ) h := by
  rw [sphericalAverage_sphericalAverage hK hψ, sphericalAverage_sphericalAverage hK hψ]
  have hΘ (w : G) : K.sphericalAverage (σ w) ψ h = K.sphericalAverage w ψ h := by
    rcases hσK w with ⟨k₁, hk₁, k₂, hk₂, he⟩
    rw [he, sphericalAverage_mul_mem hψ hk₂, sphericalAverage_mem_mul hk₁]
  rcases hσK z with ⟨a₁, ha₁, a₂, ha₂, hz⟩
  rcases hσK y with ⟨b₁, hb₁, b₂, hb₂, hy⟩
  let f : K → ℂ := fun k ↦ K.sphericalAverage (z * k * y) ψ h
  have h₁ (k : K) : K.sphericalAverage (y * k * z) ψ h = f (⟨a₂, ha₂⟩ * τ k * ⟨b₁, hb₁⟩) := by
    have he : σ (y * k * z) = a₁ * (z * (⟨a₂, ha₂⟩ * τ k * ⟨b₁, hb₁⟩ : K) * y) * b₂ := by
      rw [hσ, hσ, hz, hy, coe_mul, coe_mul, hτ]
      group
    rw [← hΘ, he, sphericalAverage_mul_mem hψ hb₂, sphericalAverage_mem_mul ha₁]
  simp only [h₁]
  exact (haarMean_comp_homeomorph (fun k ↦ f (⟨a₂, ha₂⟩ * k * ⟨b₁, hb₁⟩)) τ fun a b ↦
    Subtype.ext <| by rw [hτ, coe_mul, hσ, coe_mul, hτ, hτ]).trans <|
      (haarMean_mul_left (fun k ↦ f (k * ⟨b₁, hb₁⟩)) ⟨a₂, ha₂⟩).trans <|
        haarMean_mul_right f ⟨b₁, hb₁⟩

lemma haarMean_inv_mul_eq_zero (hψ : ∀ x, ∀ k ∈ K, ψ (x * k) = ψ x) (ρ : K →* ℂˣ) {t t' : K}
    (ht : ρ t ≠ 1) (hy : (t : G) * y = y * t') :
    haarMean (fun k : K ↦ ((ρ k)⁻¹ : ℂˣ) * ψ (h * k * y)) = 0 := by
  have h₁ : (haarMean fun k : K ↦ ((ρ (k * t))⁻¹ : ℂˣ) * ψ (h * (k * t : K) * y)) =
      haarMean fun k : K ↦ ((ρ k)⁻¹ : ℂˣ) * ψ (h * k * y) :=
    haarMean_mul_right (fun k : K ↦ ((ρ k)⁻¹ : ℂˣ) * ψ (h * k * y)) t
  have h₂ (k : K) : ((ρ (k * t))⁻¹ : ℂˣ) * ψ (h * (k * t : K) * y) =
      ((ρ t)⁻¹ : ℂˣ) * (((ρ k)⁻¹ : ℂˣ) * ψ (h * k * y)) := by
    have he : h * (k * t : K) * y = h * k * y * t' := by
      simp only [coe_mul, mul_assoc, hy]
    rw [he, hψ _ _ t'.2, map_mul, mul_inv, Units.val_mul]
    ring1
  simp only [h₂] at h₁
  rw [haarMean_const_mul] at h₁
  have h₃ : (((ρ t)⁻¹ : ℂˣ) : ℂ) ≠ 1 := fun h ↦ ht <| by
    have h₄ : (ρ t)⁻¹ = 1 := Units.ext h
    simpa using h₄
  exact (mul_left_eq_self₀.mp h₁).resolve_left h₃

end Subgroup

namespace ValuationSubring

variable {L : Type*} [Field L] [TopologicalSpace L] {O : ValuationSubring L}

lemma continuous_transposeGL : Continuous (transposeGL : GL (Fin 2) L → GL (Fin 2) L) :=
  Units.continuous_iff.mpr ⟨continuous_id.matrix_transpose.comp Units.continuous_val,
    continuous_id.matrix_transpose.comp Units.continuous_coe_inv⟩

variable (O) in
/-- The transpose, as a homeomorphism of `K = GL₂(O)`. -/
def transposeHomeomorph : O.gl2 ≃ₜ O.gl2 where
  toFun k := ⟨transposeGL k, transposeGL_mem_gl k.2⟩
  invFun k := ⟨transposeGL k, transposeGL_mem_gl k.2⟩
  left_inv k := Subtype.ext <| transposeGL_transposeGL k.1
  right_inv k := Subtype.ext <| transposeGL_transposeGL k.1
  continuous_toFun := (continuous_transposeGL.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_transposeGL.comp continuous_subtype_val).subtype_mk _

variable [IsTopologicalRing L] [T2Space L] [CompactSpace O]

instance : CompactSpace O.gl2 := by
  have hO : IsCompact (O : Set L) := isCompact_iff_compactSpace.mpr ‹_›
  let S : Set (Matrix (Fin 2) (Fin 2) L) := {m | ∀ i j, m i j ∈ O}
  have hS : IsCompact S := by
    have he : S = Set.pi Set.univ fun _ ↦ Set.pi Set.univ fun _ ↦ (O : Set L) := by
      ext m
      exact ⟨fun h i _ j _ ↦ h i j, fun h i j ↦ h i trivial j trivial⟩
    rw [he]
    exact isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ hO
  have hS' : IsCompact (MulOpposite.unop ⁻¹' S) :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.isCompact_preimage hS
  have hK : IsCompact (O.gl2 : Set (GL (Fin 2) L)) := by
    have he : (O.gl2 : Set (GL (Fin 2) L)) =
        Units.embedProduct _ ⁻¹' (S ×ˢ (MulOpposite.unop ⁻¹' S)) := by
      ext k
      exact ⟨fun h ↦ ⟨fun i j ↦ (h i j).1, fun i j ↦ (h i j).2⟩, fun h i j ↦ ⟨h.1 i j, h.2 i j⟩⟩
    rw [he]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  exact isCompact_iff_compactSpace.mp hK

variable {ψ : GL (Fin 2) L → ℂ} {ι : Type*} [Fintype ι] {ϖ : Lˣ} {r : ι → L} {m h : GL (Fin 2) L}

/-- **The Hecke sum is an average**: for `ψ` right invariant under `K = GL₂(O)`, with `d` the matrix
`(1, 0; 0, ϖ)`, one has `∑ ψ(h x) = (q + 1) ∫_K ψ(h k d) dk`, the sum being over the Hecke
representatives `x`, and `q + 1` being their number. -/
lemma heckeSum_eq_card_mul_sphericalAverage (hO : IsOpen (O : Set L)) (hϖ : O.IsUniformizer ϖ)
    (hr : O.IsResidueSystem ϖ r) (hψ : ∀ x, ∀ k ∈ O.gl2, ψ (x * k) = ψ x) : heckeSum ϖ r ψ h =
      (Fintype.card (Option ι) : ℂ) * O.gl2.sphericalAverage (heckeRep ϖ r none) ψ h := by
  have hc : Continuous ψ := (Subring.isOpen_gl hO).continuous_of_forall_mul_eq hψ
  have h₁ (o : Option ι) : O.gl2.sphericalAverage (heckeRep ϖ r none) ψ h =
      haarMean fun k : O.gl2 ↦ ψ (h * k * heckeRep ϖ r o) := by
    rcases hr.exists_mul_heckeRep_none_eq o with ⟨k₀, hk₀, w, hw, he⟩
    rw [← Subgroup.sphericalAverage_mem_mul hk₀, he, Subgroup.sphericalAverage_mul_mem hψ hw]
    rfl
  have h₂ : (haarMean fun k : O.gl2 ↦ ∑ o, ψ (h * k * heckeRep ϖ r o)) =
      ∑ o, haarMean fun k : O.gl2 ↦ ψ (h * k * heckeRep ϖ r o) :=
    haarMean_sum Finset.univ fun o _ ↦
      hc.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have h₃ (k : O.gl2) : ∑ o, ψ (h * k * heckeRep ϖ r o) = heckeSum ϖ r ψ h :=
    hϖ.heckeSum_mul hr hψ h k.2
  simp only [h₃, haarMean_const, ← h₁] at h₂
  rw [h₂, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The Hecke sum commutes with the spherical averages**, for `ψ` right invariant under
`GL₂(O)`. -/
lemma heckeSum_sphericalAverage (hO : IsOpen (O : Set L)) (hϖ : O.IsUniformizer ϖ)
    (hr : O.IsResidueSystem ϖ r) (hψ : ∀ x, ∀ k ∈ O.gl2, ψ (x * k) = ψ x) :
    heckeSum ϖ r (O.gl2.sphericalAverage m ψ) h = O.gl2.sphericalAverage m (heckeSum ϖ r ψ) h := by
  have he : heckeSum ϖ r ψ = fun x ↦ (Fintype.card (Option ι) : ℂ) *
      O.gl2.sphericalAverage (heckeRep ϖ r none) ψ x :=
    funext fun x ↦ heckeSum_eq_card_mul_sphericalAverage hO hϖ hr hψ
  rw [heckeSum_eq_card_mul_sphericalAverage hO hϖ hr fun x k hk ↦ Subgroup.sphericalAverage_mul hk,
    Subgroup.sphericalAverage_comm (Subring.isOpen_gl hO) hψ transposeGL_mul
      exists_transposeGL_eq_mul_mul (transposeHomeomorph O) fun _ ↦ rfl, he]
  exact (haarMean_const_mul _ _).symm

/-- **Twisted averages vanish**: if `ρ` is a character of `K = GL₂(O)` nontrivial on some matrix
`diag(u, 1)`, then `∫_K ρ(k)⁻¹ ψ(h k m) dk = 0` for all `ψ` right invariant under `K`. -/
lemma haarMean_inv_mul_eq_zero (ρ : O.gl2 →* ℂˣ) {u : Lˣ} (hu : diagGL ![u, 1] ∈ O.gl2)
    (hρ : ρ ⟨_, hu⟩ ≠ 1) (hψ : ∀ x, ∀ k ∈ O.gl2, ψ (x * k) = ψ x) :
    haarMean (fun k : O.gl2 ↦ ((ρ k)⁻¹ : ℂˣ) * ψ (h * k * m)) = 0 := by
  rcases exists_eq_mul_diagGL_mul (O := O) m with ⟨k₁, hk₁, k₂, hk₂, α, β, rfl⟩
  refine Subgroup.haarMean_inv_mul_eq_zero hψ ρ (t := ⟨k₁, hk₁⟩ * ⟨_, hu⟩ * ⟨k₁, hk₁⟩⁻¹)
    (t' := ⟨k₂, hk₂⟩⁻¹ * ⟨_, hu⟩ * ⟨k₂, hk₂⟩) ?_ ?_
  · rwa [map_mul, map_mul, map_inv, mul_comm (ρ ⟨k₁, hk₁⟩), mul_inv_cancel_right]
  · have hc : diagGL ![u, 1] * diagGL ![α, β] = diagGL ![α, β] * diagGL ![u, 1] := by
      rw [← map_mul, mul_comm, map_mul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_left]
    rw [← mul_assoc (diagGL ![u, 1]), hc, mul_assoc]

end ValuationSubring
