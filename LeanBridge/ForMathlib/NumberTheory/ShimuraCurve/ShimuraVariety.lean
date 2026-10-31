import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Hermitian symmetric domains

A connected complex manifold `M` is a **Hermitian symmetric domain** (LMFDB `ag.shimura_variety`)
if every point of `M` is the only fixed point of some holomorphic involution of `M`, and `M` is
biholomorphic to a bounded open subset of `ℂⁿ` for some `n`. For a bounded domain, a holomorphic
involution with an isolated fixed point is an isometry of the Bergman metric, so no Hermitian metric
is part of the definition, as in the knowl. The unit polydisc `𝔻ⁿ`, biholomorphic to `ℍⁿ`, is a
Hermitian symmetric domain (`isHermitianSymmetricDomain_polydisc`): the involution at a point `a`
is, in each coordinate `i`, the geodesic symmetry `z ↦ (2aᵢ - (1 + |aᵢ|²) z) / (1 + |aᵢ|² - 2 āᵢ z)`
of the unit disc at `aᵢ`.

The knowl defines the **connected Shimura varieties** as the quotients `Γ \ M` of Hermitian
symmetric domains `M` by torsion-free subgroups `Γ` of their groups of holomorphic automorphisms.
This omits the condition that `Γ` be arithmetic (Milne, *Introduction to Shimura varieties*, §3-4):
commensurable with the image of `G(ℤ)` under a surjective homomorphism with compact kernel from
`G(ℝ)` onto the identity component of `Aut(M)`, for an algebraic group `G` over `ℚ`. Without it,
`Γ \ M` need not be an algebraic variety, nor even Hausdorff, as `Γ` need not be discrete, and the
compact Riemann surfaces `Γ \ ℍ` given by the non-arithmetic cocompact Fuchsian groups are not
Shimura curves. Connected Shimura varieties, with this arithmeticity condition, are formalised in
`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.ConnectedShimuraVariety`.

Holomorphic maps are the complex analytic ones, `ContMDiff` of order `ω` for the models `𝓘(ℂ, E)`,
and the holomorphic automorphisms of `M` form a subgroup of its permutations.

## Main definitions

* `biholomorphismGroup`: the group of holomorphic automorphisms of a complex manifold.
* `IsHermitianSymmetricDomain` (LMFDB `ag.shimura_variety`).

## Main results

* `isHermitianSymmetricDomain_polydisc`: the unit polydisc of `ℂⁿ` is a Hermitian symmetric domain.
-/

open Complex Function Metric TopologicalSpace
open scoped ComplexConjugate ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Type*) [TopologicalSpace M]
  [ChartedSpace E M] {a z : ℂ} {n : ℕ}

/-- The group of **holomorphic automorphisms** of a complex manifold `M`, modelled on `E`: the
permutations `f` of `M` such that `f` and `f⁻¹` are holomorphic, that is, complex analytic. -/
def biholomorphismGroup : Subgroup (Equiv.Perm M) where
  carrier := {f | ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω f ∧ ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω f.symm}
  one_mem' := ⟨contMDiff_id, contMDiff_id⟩
  mul_mem' hf hg := ⟨hf.1.comp hg.1, hg.2.comp hf.2⟩
  inv_mem' hf := ⟨hf.2, hf.1⟩

/-- A complex manifold `M` is a **Hermitian symmetric domain** (LMFDB `ag.shimura_variety`) if it is
connected, every point `p` of `M` is the only fixed point of some holomorphic involution of `M`, and
`M` is biholomorphic to a bounded open subset of `ℂⁿ` for some `n`. -/
def IsHermitianSymmetricDomain : Prop :=
  IsManifold 𝓘(ℂ, E) ω M ∧ ConnectedSpace M ∧
    (∀ p : M, ∃ s ∈ biholomorphismGroup (E := E) M, s * s = 1 ∧ ∀ x, s x = x ↔ x = p) ∧
    ∃ (n : ℕ) (U : Opens (Fin n → ℂ)), Bornology.IsBounded (U : Set (Fin n → ℂ)) ∧
      Nonempty (M ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, Fin n → ℂ)⟯ U)

variable (a z) in
/-- The holomorphic involution `z ↦ (2a - (1 + |a|²) z) / (1 + |a|² - 2 ā z)` of the unit disc,
whose only fixed point is `a`. -/
private noncomputable def discSymm : ℂ :=
  (2 * a - (1 + a * conj a) * z) / (1 + a * conj a - 2 * conj a * z)

variable (a z) in
private lemma normSq_den_sub_normSq_num : normSq (1 + a * conj a - 2 * conj a * z) -
    normSq (2 * a - (1 + a * conj a) * z) = (1 - normSq a) ^ 2 * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, one_re, one_im, conj_re,
    conj_im, re_ofNat, im_ofNat]
  ring1

private lemma normSq_den_pos (ha : normSq a < 1) (hz : normSq z < 1) :
    0 < normSq (1 + a * conj a - 2 * conj a * z) := by
  nlinarith [normSq_den_sub_normSq_num a z, normSq_nonneg (2 * a - (1 + a * conj a) * z),
    mul_pos (pow_pos (sub_pos.mpr ha) 2) (sub_pos.mpr hz)]

private lemma den_ne_zero (ha : normSq a < 1) (hz : normSq z < 1) :
    1 + a * conj a - 2 * conj a * z ≠ 0 :=
  normSq_pos.mp (normSq_den_pos ha hz)

private lemma normSq_discSymm_lt_one (ha : normSq a < 1) (hz : normSq z < 1) :
    normSq (discSymm a z) < 1 := by
  rw [discSymm, normSq_div, div_lt_one (normSq_den_pos ha hz)]
  nlinarith [normSq_den_sub_normSq_num a z, mul_pos (pow_pos (sub_pos.mpr ha) 2) (sub_pos.mpr hz)]

private lemma discSymm_discSymm (ha : normSq a < 1) (hz : normSq z < 1) :
    discSymm a (discSymm a z) = z := by
  have h : 1 - a * conj a ≠ 0 := by
    rw [mul_conj, ← ofReal_one, ← ofReal_sub, ofReal_ne_zero]
    exact (sub_pos.mpr ha).ne'
  have h' : (1 + a * conj a) * (1 + a * conj a - 2 * conj a * z) -
      2 * conj a * (2 * a - (1 + a * conj a) * z) = (1 - a * conj a) ^ 2 := by
    ring1
  have hden : 1 + a * conj a - 2 * conj a * z ≠ 0 := den_ne_zero ha hz
  rw [discSymm, discSymm]
  field_simp
  rw [h', div_eq_iff (pow_ne_zero 2 h)]
  ring1

private lemma discSymm_eq_self_iff (ha : normSq a < 1) (hz : normSq z < 1) :
    discSymm a z = z ↔ z = a := by
  rw [discSymm, div_eq_iff (den_ne_zero ha hz)]
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases mul_eq_zero.mp (by linear_combination (1 / 2 : ℂ) * h : (conj a * z - 1) * (z - a) = 0)
      with h | h
    · have h' : normSq (conj a * z) = 1 := by
        rw [sub_eq_zero.mp h, map_one]
      rw [normSq_mul, normSq_conj] at h'
      nlinarith [normSq_nonneg a, normSq_nonneg z]
    · exact sub_eq_zero.mp h
  · rintro rfl
    ring1

private lemma contDiffAt_discSymm (ha : normSq a < 1) (hz : normSq z < 1) :
    ContDiffAt ℂ ω (discSymm a) z := by
  have hden : 1 + a * conj a - 2 * conj a * z ≠ 0 := den_ne_zero ha hz
  unfold discSymm
  fun_prop (disch := exact hden)

private lemma mem_ball_iff {v : Fin n → ℂ} :
    v ∈ ball (0 : Fin n → ℂ) 1 ↔ ∀ i, normSq (v i) < 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  exact forall_congr' fun i ↦ by rw [normSq_eq_norm_sq, sq_lt_one_iff₀ (norm_nonneg _)]

variable (n) in
/-- The unit polydisc `𝔻ⁿ`, the open unit ball of `ℂⁿ` for the sup norm. -/
private noncomputable abbrev polydisc : Opens (Fin n → ℂ) :=
  ⟨ball 0 1, isOpen_ball⟩

variable (p : polydisc n)

/-- The holomorphic involution of `𝔻ⁿ` whose only fixed point is `p`: `discSymm` in each
coordinate. -/
private noncomputable def polydiscSymm (v : polydisc n) : polydisc n :=
  ⟨fun i ↦ discSymm (p.1 i) (v.1 i), mem_ball_iff.mpr fun i ↦
    normSq_discSymm_lt_one (mem_ball_iff.mp p.2 i) (mem_ball_iff.mp v.2 i)⟩

private lemma polydiscSymm_involutive : Involutive (polydiscSymm p) :=
  fun v ↦ Subtype.ext <| funext fun i ↦
    discSymm_discSymm (mem_ball_iff.mp p.2 i) (mem_ball_iff.mp v.2 i)

private lemma contMDiff_polydiscSymm :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (polydiscSymm p) :=
  fun v ↦ (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (polydiscSymm p) _ v).mp <|
    (contMDiffAt_subtype_iff (f := fun (w : Fin n → ℂ) i ↦ discSymm (p.1 i) (w i))).mpr <|
      contMDiffAt_iff_contDiffAt.mpr <| contDiffAt_pi.mpr fun i ↦
        (contDiffAt_discSymm (mem_ball_iff.mp p.2 i) (mem_ball_iff.mp v.2 i)).fun_comp v.1
          (contDiffAt_apply ℂ (fun _ ↦ ℂ) i v.1)

/-- **The unit polydisc `𝔻ⁿ = {z ∈ ℂⁿ : |zᵢ| < 1}` is a Hermitian symmetric domain**: it is the
open unit ball of `ℂⁿ` for the sup norm, and the geodesic symmetry of the disc at `pᵢ` in each
coordinate is a holomorphic involution whose only fixed point is `p`. It is biholomorphic to `ℍⁿ`,
the Hermitian symmetric domain of the Hilbert modular varieties, `ℍ²` for the Hilbert modular
surfaces. -/
lemma isHermitianSymmetricDomain_polydisc :
    IsHermitianSymmetricDomain (E := Fin n → ℂ) (⟨ball 0 1, isOpen_ball⟩ : Opens (Fin n → ℂ)) := by
  refine ⟨inferInstance, isConnected_iff_connectedSpace.mp <|
    (convex_ball 0 1).isConnected (nonempty_ball.mpr one_pos), fun p ↦ ?_, n,
    ⟨ball 0 1, isOpen_ball⟩, isBounded_ball, ⟨Diffeomorph.refl _ _ _⟩⟩
  refine ⟨(polydiscSymm_involutive p).toPerm _,
    ⟨contMDiff_polydiscSymm p, contMDiff_polydiscSymm p⟩, Equiv.ext (polydiscSymm_involutive p),
    fun v ↦ ?_⟩
  rw [Involutive.coe_toPerm, Subtype.ext_iff, Subtype.ext_iff, funext_iff, funext_iff]
  exact forall_congr' fun i ↦ discSymm_eq_self_iff (mem_ball_iff.mp p.2 i) (mem_ball_iff.mp v.2 i)
