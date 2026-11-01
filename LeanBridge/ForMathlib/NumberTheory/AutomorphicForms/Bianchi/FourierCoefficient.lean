import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerUnique
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Fourier coefficients of Bianchi modular forms

Let `F : ℋ₃ → ℂ^{k+1}` be invariant under the translations `x ↦ x + λ` by an additive subgroup `Λ`
of `ℂ` (for a Bianchi modular form of level `Γ`, any subgroup of the translations fixing the cusp
`∞`, `IsBianchiSlashInvariant.extend_add_eq`), `P` a bounded fundamental domain of `Λ` and `μ ∈ ℂ`
a frequency of the dual lattice, `ψ(μλ) = 1` on `Λ`, where `ψ(z) = e^{2πi(z + z̄)}`. The Fourier
coefficient `φ_μ(y) = vol(P)⁻¹ ∫_P ψ(-μx) F(x, y) dx` (`bianchiFourierCoeff`) gives the Fourier mode
`ψ(μx) φ_μ(y)` (`bianchiFourierMode`), which is the translation average
`∫_P vol(P)⁻¹ ψ(-μt) F(x + t, y) dt` of `F` (`translationAverage`,
`bianchiFourierMode_bianchiFourierCoeff`).

Translation averages of harmonic real analytic functions are harmonic
(`IsBianchiHarmonic.translationAverage`): the lift of the average to `SL(2, ℂ)` is the average
`g ↦ ∫_P ω(t) Φ_F(n(t) g) dt` of the lift `Φ_F` over the left translations by the unipotent elements
`n(t) = (1, t; 0, 1)` (`unipotentAverage`), and the Casimir operators, which are made of
derivatives along one-parameter subgroups acting on the right, commute with it. The derivatives are
taken under the integral sign: `(t, s, r) ↦ Φ_F(n(t) g e^{sX} e^{rY})` is `C²`, so the integrands
have derivatives bounded on `closure P × [-1, 1]`. Hence the Fourier modes of a harmonic function
are harmonic (`isBianchiHarmonic_bianchiFourierMode_bianchiFourierCoeff`). The Fourier coefficients
of a real analytic function are `Cⁿ` on `(0, ∞)` for every `n` (`contDiffOn_bianchiFourierCoeff`,
by differentiation under the integral sign), they inherit the polynomial growth of `F`
(`norm_bianchiFourierCoeff_le`), and the constant coefficient of a cusp form vanishes
(`IsBianchiCuspidal.bianchiFourierCoeff_zero`). By the uniqueness of the harmonic Whittaker function
of moderate growth (`isBianchiHarmonic_bianchiFourierMode_iff`), for `k ≥ 1` and `μ ≠ 0` the Fourier
mode of a Bianchi modular form of weight `k` is `φ_μ(1)₀ / W_k(u, 4π|μ|)₀` times the Fourier–Bessel
function `y W_k(u, 4π|μ|y) ψ(μx)` (`bianchiFourierMode_bianchiFourierCoeff_eq_smul`,
`IsBianchiModularForm.fourierMode_eq_smul_bianchiWhittakerFunction`). So a Bianchi modular form
whose Fourier series over the frequencies `μ = σ(α) / δ`, `0 ≠ α ∈ 𝒪_K`, converges to it has the
Fourier–Bessel expansion of weight `k` (`HasBianchiWhittakerExpansion`) with
`c(α) = φ_μ(1)₀ / W_k(u, 4π|μ|)₀` (`IsBianchiModularForm.hasBianchiWhittakerExpansion`).

For a lattice spanned by an `ℝ`-basis of `ℂ`, the fundamental parallelogram is a bounded
fundamental domain (`IsBianchiModularForm.hasBianchiWhittakerExpansion_of_basis`). For a quadratic
field `K` with `σ(K) ⊄ ℝ`, the images of an integral basis form such a basis
(`integralLatticeBasis`), spanning `σ(𝒪_K)`. For `δ² = Δ` the frequencies `σ(α) / δ`, `α ∈ 𝒪_K`,
are dual to `σ(𝒪_K)` (`exists_intCast_eq_of_sq_eq_discr`: `𝒪_K / √Δ` lies in the inverse different;
with an integral basis `(e₀, e₁)`, `Δ = D²` for `D = σ(e₀) conj(σ(e₁)) - σ(e₁) conj(σ(e₀))`, as the
trace is `σ + conj ∘ σ`). So the expansion holds over `σ(𝒪_K)`, with `δ = √Δ`, for every level
containing the unipotent matrices of `𝒪_K`, such as `Γ₀(𝔑)`, as soon as the Fourier series
converges (`IsBianchiModularForm.hasBianchiWhittakerExpansion_of_finrank_eq_two`).

Conversely every frequency dual to `σ(𝒪_K)` is `σ(α) / δ` for some `α ∈ 𝒪_K`
(`exists_div_eq_of_dual`: the trace pairing matrix of an integral basis has determinant `-1`), so
the frequencies `σ(α) / δ`, `α ≠ 0`, are exactly the nonzero points of the dual lattice.

For a cusp form the constant term vanishes, the translations of the level fixing `∞` being
exactly `σ(𝒪_K)`, so it suffices that the full Fourier series over the dual lattice converges
(`IsBianchiModularForm.hasBianchiWhittakerExpansion_of_isBianchiCuspidal`).

Not proved here, and the remaining hypothesis of these theorems: that the Fourier series of the
smooth periodic function `x ↦ F(x, y)` over the dual lattice of `σ(𝒪_K)` converges to it (Fourier
inversion on `ℂ / σ(𝒪_K)`, which needs the decay of the Fourier coefficients of smooth functions on
a two-dimensional torus, not in Mathlib).

## Main definitions

* `HyperbolicThreeSpace.unipotentAverage`: the average of a function on `SL(2, ℂ)` over the left
  translations by unipotent elements.
* `HyperbolicThreeSpace.translationAverage`: the average of `F : ℋ₃ → ℂ^{k+1}` over translations.
* `HyperbolicThreeSpace.bianchiFourierCoeff` (LMFDB `mf.bianchi.spaces`): the Fourier coefficient
  `φ_μ(y)`.
* `HyperbolicThreeSpace.integralLatticeBasis`: the `ℝ`-basis of `ℂ` spanning `σ(𝒪_K)`, for a
  quadratic field `K`.

## Main results

* `HyperbolicThreeSpace.IsBianchiHarmonic.translationAverage`: translation averages of harmonic
  functions are harmonic.
* `HyperbolicThreeSpace.bianchiFourierMode_bianchiFourierCoeff`: a Fourier mode is a translation
  average.
* `HyperbolicThreeSpace.isBianchiHarmonic_bianchiFourierMode_bianchiFourierCoeff`: the Fourier modes
  of a harmonic function are harmonic.
* `HyperbolicThreeSpace.norm_bianchiFourierCoeff_le`: the Fourier coefficients have moderate growth.
* `HyperbolicThreeSpace.contDiffOn_bianchiFourierCoeff`: the Fourier coefficients are smooth.
* `HyperbolicThreeSpace.bianchiFourierMode_bianchiFourierCoeff_eq_smul`: the Fourier modes are
  multiples of the Fourier–Bessel function.
* `HyperbolicThreeSpace.IsBianchiSlashInvariant.extend_add_eq`: periodicity of invariant functions.
* `HyperbolicThreeSpace.IsBianchiCuspidal.bianchiFourierCoeff_zero`: the constant term of a cusp
  form vanishes.
* `HyperbolicThreeSpace.IsBianchiModularForm.fourierMode_eq_smul_bianchiWhittakerFunction`: the
  Fourier modes of a Bianchi modular form are multiples of the Fourier–Bessel function.
* `HyperbolicThreeSpace.IsBianchiModularForm.hasBianchiWhittakerExpansion`: the Fourier–Bessel
  expansion of a Bianchi modular form whose Fourier series converges.
* `HyperbolicThreeSpace.IsBianchiModularForm.hasBianchiWhittakerExpansion_of_basis`: the same over a
  lattice given by a basis.
* `HyperbolicThreeSpace.exists_intCast_eq_of_sq_eq_discr`: the frequencies `σ(α) / √Δ` are dual to
  `σ(𝒪_K)`, for a quadratic field `K`.
* `HyperbolicThreeSpace.exists_div_eq_of_dual`: every frequency dual to `σ(𝒪_K)` is of this form.
* `HyperbolicThreeSpace.IsBianchiModularForm.hasBianchiWhittakerExpansion_of_finrank_eq_two`: the
  same over `σ(𝒪_K)`, for a quadratic field `K` and `δ = √Δ`.
* `HyperbolicThreeSpace.IsBianchiModularForm.hasBianchiWhittakerExpansion_of_isBianchiCuspidal`:
  the expansion of a cusp form whose full Fourier series converges.
-/

open Bornology Complex Matrix MeasureTheory Metric Module NumberField Set

open scoped ComplexConjugate MatrixGroups Pointwise Real

namespace HyperbolicThreeSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {P : Set ℂ} {ω : ℂ → ℂ} {μ : ℂ} {Φ Φ₁ Φ₂ : SL(2, ℂ) → V} (b b' : Fin 3)
  (w w' : ℂ) (g : SL(2, ℂ)) (t : ℂ)

variable (P ω Φ) in
/-- The average `g ↦ ∫_{t ∈ P} ω(t) Φ(n(t) g)` of `Φ : SL(2, ℂ) → V` over the left translations by
the unipotent elements `n(t) = (1, t; 0, 1)`, `t ∈ P`, with the weight `ω`. -/
noncomputable def unipotentAverage : SL(2, ℂ) → V :=
  fun g ↦ ∫ t in P, ω t • Φ (sl2Exp 1 t * g)

variable (Φ) in
/-- `t ↦ Φ(n(t) g)` is continuous for every `g`. -/
private def IsUnipotentContinuous : Prop :=
  ∀ g : SL(2, ℂ), Continuous fun t ↦ Φ (sl2Exp 1 t * g)

variable (Φ) in
/-- `Φ : SL(2, ℂ) → V` is `C¹` along the left unipotent translations and the one-parameter
subgroups: `(t, s) ↦ Φ(n(t) g e^{swX_b})` is `C¹` for all `g`, `b` and `w`. -/
private def IsUnipotentC1 : Prop :=
  ∀ (g : SL(2, ℂ)) (b : Fin 3) (w : ℂ),
    ContDiff ℝ 1 fun p : ℂ × ℝ ↦ Φ (sl2Exp 1 p.1 * g * sl2Exp b (p.2 * w))

variable (Φ) in
/-- `Φ : SL(2, ℂ) → V` is `C²` along the left unipotent translations and two one-parameter
subgroups: `(t, s, r) ↦ Φ(n(t) g e^{sw₁X_{b₁}} e^{rw₂X_{b₂}})` is `C²` for all `g`, `bᵢ` and
`wᵢ`. -/
private def IsUnipotentC2 : Prop :=
  ∀ (g : SL(2, ℂ)) (b₁ : Fin 3) (w₁ : ℂ) (b₂ : Fin 3) (w₂ : ℂ), ContDiff ℝ 2 fun p : ℂ × ℝ × ℝ ↦
    Φ (sl2Exp 1 p.1 * g * sl2Exp b₁ (p.2.1 * w₁) * sl2Exp b₂ (p.2.2 * w₂))

private lemma IsUnipotentC1.add (h₁ : IsUnipotentC1 Φ₁) (h₂ : IsUnipotentC1 Φ₂) :
    IsUnipotentC1 (Φ₁ + Φ₂) :=
  fun g b w ↦ (h₁ g b w).add (h₂ g b w)

private lemma IsUnipotentC1.sub (h₁ : IsUnipotentC1 Φ₁) (h₂ : IsUnipotentC1 Φ₂) :
    IsUnipotentC1 (Φ₁ - Φ₂) :=
  fun g b w ↦ (h₁ g b w).sub (h₂ g b w)

private lemma IsUnipotentC1.const_smul (c : ℂ) (h : IsUnipotentC1 Φ) : IsUnipotentC1 (c • Φ) :=
  fun g b w ↦ (h g b w).const_smul c

private lemma IsUnipotentC2.isUnipotentC1 (h : IsUnipotentC2 Φ) : IsUnipotentC1 Φ := by
  intro g b w
  have h₀ : ContDiff ℝ 2 ((fun p : ℂ × ℝ × ℝ ↦ Φ (sl2Exp 1 p.1 * g * sl2Exp b (p.2.1 * w) *
      sl2Exp b (p.2.2 * 0))) ∘ fun p : ℂ × ℝ ↦ (p.1, p.2, (0 : ℝ))) :=
    (h g b w b 0).comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  simp only [mul_zero, sl2Exp_zero, mul_one] at h₀
  exact h₀.of_le (by norm_num)

private lemma IsUnipotentC2.isUnipotentC1_lieDeriv (h : IsUnipotentC2 Φ) :
    IsUnipotentC1 (lieDeriv b' w' Φ) := by
  intro g b w
  have hH : ContDiff ℝ 2 fun q : ℂ × ℝ × ℝ ↦
      Φ (sl2Exp 1 q.1 * g * sl2Exp b (q.2.1 * w) * sl2Exp b' (q.2.2 * w')) :=
    h g b w b' w'
  have he (p : ℂ × ℝ) : lieDeriv b' w' Φ (sl2Exp 1 p.1 * g * sl2Exp b (p.2 * w)) =
      fderiv ℝ (fun q : ℂ × ℝ × ℝ ↦ Φ (sl2Exp 1 q.1 * g * sl2Exp b (q.2.1 * w) *
        sl2Exp b' (q.2.2 * w'))) (p.1, p.2, 0) (0, 0, 1) := by
    have hd : HasDerivAt (fun r : ℝ ↦ (p.1, p.2, r)) ((0 : ℂ), (0 : ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) p.1).prodMk
        ((hasDerivAt_const (0 : ℝ) p.2).prodMk (hasDerivAt_id' 0))
    have hD : HasDerivAt ((fun q : ℂ × ℝ × ℝ ↦ Φ (sl2Exp 1 q.1 * g * sl2Exp b (q.2.1 * w) *
        sl2Exp b' (q.2.2 * w'))) ∘ fun r : ℝ ↦ (p.1, p.2, r))
        (fderiv ℝ (fun q : ℂ × ℝ × ℝ ↦ Φ (sl2Exp 1 q.1 * g * sl2Exp b (q.2.1 * w) *
          sl2Exp b' (q.2.2 * w'))) (p.1, p.2, 0) (0, 0, 1)) 0 :=
      ((hH.differentiable two_ne_zero) (p.1, p.2, 0)).hasFDerivAt.comp_hasDerivAt 0 hd
    exact hD.deriv
  rw [funext he]
  exact ((hH.fderiv_right le_rfl).comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))).clm_apply contDiff_const

private lemma IsUnipotentC2.isUnipotentC1_lieDerivOne (h : IsUnipotentC2 Φ) :
    IsUnipotentC1 (lieDerivOne b' Φ) :=
  ((h.isUnipotentC1_lieDeriv b' 1).sub ((h.isUnipotentC1_lieDeriv b' I).const_smul I)).const_smul _

private lemma IsUnipotentC2.isUnipotentC1_lieDerivTwo (h : IsUnipotentC2 Φ) :
    IsUnipotentC1 (lieDerivTwo b' Φ) :=
  ((h.isUnipotentC1_lieDeriv b' 1).add ((h.isUnipotentC1_lieDeriv b' I).const_smul I)).const_smul _

private lemma IsUnipotentC1.isUnipotentContinuous (h : IsUnipotentC1 Φ) :
    IsUnipotentContinuous Φ := by
  intro g
  have h₀ : Continuous ((fun p : ℂ × ℝ ↦ Φ (sl2Exp 1 p.1 * g * sl2Exp 0 (p.2 * 0))) ∘
      fun t : ℂ ↦ (t, (0 : ℝ))) :=
    (h g 0 0).continuous.comp (continuous_id.prodMk continuous_const)
  simpa only [Function.comp_def, mul_zero, sl2Exp_zero, mul_one] using h₀

private lemma IsUnipotentC1.hasDerivAt (h : IsUnipotentC1 Φ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Φ (sl2Exp 1 t * g * sl2Exp b (s * w)))
      (fderiv ℝ (fun p : ℂ × ℝ ↦ Φ (sl2Exp 1 p.1 * g * sl2Exp b (p.2 * w))) (t, s) (0, 1)) s := by
  have hd : HasDerivAt (fun r : ℝ ↦ (t, r)) ((0 : ℂ), (1 : ℝ)) s :=
    (hasDerivAt_const s t).prodMk (hasDerivAt_id' s)
  exact (((h g b w).differentiable one_ne_zero) (t, s)).hasFDerivAt.comp_hasDerivAt s hd

private lemma IsUnipotentC1.lieDeriv_eq (h : IsUnipotentC1 Φ) : lieDeriv b w Φ (sl2Exp 1 t * g) =
    fderiv ℝ (fun p : ℂ × ℝ ↦ Φ (sl2Exp 1 p.1 * g * sl2Exp b (p.2 * w))) (t, 0) (0, 1) :=
  (h.hasDerivAt b w g t 0).deriv

private lemma IsUnipotentC1.isUnipotentContinuous_lieDeriv (h : IsUnipotentC1 Φ) :
    IsUnipotentContinuous (lieDeriv b w Φ) := by
  intro g
  rw [funext (h.lieDeriv_eq b w g)]
  exact (((h g b w).continuous_fderiv one_ne_zero).comp
    (continuous_id.prodMk continuous_const)).clm_apply continuous_const

private lemma IsUnipotentC1.isUnipotentContinuous_lieDerivOne (h : IsUnipotentC1 Φ) :
    IsUnipotentContinuous (lieDerivOne b Φ) := fun g ↦
  ((h.isUnipotentContinuous_lieDeriv b 1 g).sub
    ((h.isUnipotentContinuous_lieDeriv b I g).const_smul I)).const_smul (2⁻¹ : ℂ)

private lemma IsUnipotentC1.isUnipotentContinuous_lieDerivTwo (h : IsUnipotentC1 Φ) :
    IsUnipotentContinuous (lieDerivTwo b Φ) := fun g ↦
  ((h.isUnipotentContinuous_lieDeriv b 1 g).add
    ((h.isUnipotentContinuous_lieDeriv b I g).const_smul I)).const_smul (2⁻¹ : ℂ)

private lemma integrableOn_smul_of_continuous (hP : IsBounded P) (hω : Continuous ω) {f : ℂ → V}
    (hf : Continuous f) : IntegrableOn (fun t ↦ ω t • f t) P :=
  ((hω.smul hf).continuousOn.integrableOn_compact hP.isCompact_closure).mono_set subset_closure

private lemma unipotentAverage_add (hP : IsBounded P) (hω : Continuous ω)
    (h₁ : IsUnipotentContinuous Φ₁) (h₂ : IsUnipotentContinuous Φ₂) :
    unipotentAverage P ω (Φ₁ + Φ₂) = unipotentAverage P ω Φ₁ + unipotentAverage P ω Φ₂ := by
  funext g
  simp only [unipotentAverage, Pi.add_apply, smul_add]
  exact integral_add (integrableOn_smul_of_continuous hP hω (h₁ g))
    (integrableOn_smul_of_continuous hP hω (h₂ g))

private lemma unipotentAverage_sub (hP : IsBounded P) (hω : Continuous ω)
    (h₁ : IsUnipotentContinuous Φ₁) (h₂ : IsUnipotentContinuous Φ₂) :
    unipotentAverage P ω (Φ₁ - Φ₂) = unipotentAverage P ω Φ₁ - unipotentAverage P ω Φ₂ := by
  funext g
  simp only [unipotentAverage, Pi.sub_apply, smul_sub]
  exact integral_sub (integrableOn_smul_of_continuous hP hω (h₁ g))
    (integrableOn_smul_of_continuous hP hω (h₂ g))

lemma unipotentAverage_smul (c : ℂ) :
    unipotentAverage P ω (c • Φ) = c • unipotentAverage P ω Φ := by
  funext g
  simp only [unipotentAverage, Pi.smul_apply, ← integral_smul]
  exact integral_congr_ae (.of_forall fun t ↦ smul_comm (ω t) c _)

private lemma lieDeriv_unipotentAverage (hP : IsBounded P) (hω : Continuous ω)
    (h : IsUnipotentC1 Φ) :
    lieDeriv b w (unipotentAverage P ω Φ) = unipotentAverage P ω (lieDeriv b w Φ) := by
  funext g
  let H : ℂ × ℝ → V := fun p ↦ Φ (sl2Exp 1 p.1 * g * sl2Exp b (p.2 * w))
  have hH : ContDiff ℝ 1 H := h g b w
  have hD : Continuous fun p : ℂ × ℝ ↦ fderiv ℝ H p (0, 1) :=
    (hH.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rcases (hP.isCompact_closure.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    hD.continuousOn with ⟨B, hB⟩
  rcases hP.isCompact_closure.exists_bound_of_continuousOn hω.continuousOn with ⟨B', hB'⟩
  have hc (s : ℝ) : Continuous fun t : ℂ ↦ (t, s) :=
    continuous_id.prodMk continuous_const
  have hbound : ∀ᵐ t ∂volume.restrict P, ∀ s ∈ ball (0 : ℝ) 1,
      ‖ω t • fderiv ℝ H (t, s) (0, 1)‖ ≤ B' * B :=
    ae_restrict_of_ae_restrict_of_subset subset_closure <|
      ae_restrict_of_forall_mem isClosed_closure.measurableSet fun t ht s hs ↦ by
        rw [norm_smul]
        exact mul_le_mul (hB' t ht) (hB (t, s) ⟨ht, ball_subset_closedBall hs⟩) (norm_nonneg _)
          ((norm_nonneg _).trans (hB' t ht))
  have hint : HasDerivAt (fun s : ℝ ↦ ∫ t in P, ω t • H (t, s))
      (∫ t in P, ω t • fderiv ℝ H (t, 0) (0, 1)) 0 :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds 0 one_pos)
      (.of_forall fun s ↦ (hω.smul (hH.continuous.comp (hc s))).aestronglyMeasurable)
      (integrableOn_smul_of_continuous hP hω (hH.continuous.comp (hc 0)))
      (hω.smul (hD.comp (hc 0))).aestronglyMeasurable hbound
      (integrableOn_const hP.measure_lt_top.ne)
      (.of_forall fun t s _ ↦ (h.hasDerivAt b w g t s).const_smul (ω t))).2
  have he : (fun s : ℝ ↦ unipotentAverage P ω Φ (g * sl2Exp b (s * w))) =
      fun s ↦ ∫ t in P, ω t • H (t, s) := by
    funext s
    simp only [unipotentAverage, H, mul_assoc]
  have hl : lieDeriv b w (unipotentAverage P ω Φ) g =
      deriv (fun s : ℝ ↦ ∫ t in P, ω t • H (t, s)) 0 := by
    rw [← he]
    rfl
  rw [hl, hint.deriv]
  simp only [unipotentAverage, h.lieDeriv_eq b w g]
  rfl

private lemma lieDerivOne_unipotentAverage (hP : IsBounded P) (hω : Continuous ω)
    (h : IsUnipotentC1 Φ) :
    lieDerivOne b (unipotentAverage P ω Φ) = unipotentAverage P ω (lieDerivOne b Φ) := by
  rw [lieDerivOne, lieDerivOne, lieDeriv_unipotentAverage b 1 hP hω h,
    lieDeriv_unipotentAverage b I hP hω h, unipotentAverage_smul,
    unipotentAverage_sub hP hω (h.isUnipotentContinuous_lieDeriv b 1) ?_, unipotentAverage_smul]
  exact fun g ↦ (h.isUnipotentContinuous_lieDeriv b I g).const_smul I

private lemma lieDerivTwo_unipotentAverage (hP : IsBounded P) (hω : Continuous ω)
    (h : IsUnipotentC1 Φ) :
    lieDerivTwo b (unipotentAverage P ω Φ) = unipotentAverage P ω (lieDerivTwo b Φ) := by
  rw [lieDerivTwo, lieDerivTwo, lieDeriv_unipotentAverage b 1 hP hω h,
    lieDeriv_unipotentAverage b I hP hω h, unipotentAverage_smul,
    unipotentAverage_add hP hω (h.isUnipotentContinuous_lieDeriv b 1) ?_, unipotentAverage_smul]
  exact fun g ↦ (h.isUnipotentContinuous_lieDeriv b I g).const_smul I

private lemma casimirOne_unipotentAverage (hP : IsBounded P) (hω : Continuous ω)
    (h : IsUnipotentC2 Φ) :
    casimirOne (unipotentAverage P ω Φ) = unipotentAverage P ω (casimirOne Φ) := by
  have h₂ (b b' : Fin 3) : lieDerivOne b (lieDerivOne b' (unipotentAverage P ω Φ)) =
      unipotentAverage P ω (lieDerivOne b (lieDerivOne b' Φ)) := by
    rw [lieDerivOne_unipotentAverage b' hP hω h.isUnipotentC1,
      lieDerivOne_unipotentAverage b hP hω (h.isUnipotentC1_lieDerivOne b')]
  have hc (b b' : Fin 3) : IsUnipotentContinuous (lieDerivOne b (lieDerivOne b' Φ)) :=
    (h.isUnipotentC1_lieDerivOne b').isUnipotentContinuous_lieDerivOne b
  rw [casimirOne, casimirOne, h₂, h₂, h₂, unipotentAverage_add hP hω ?_ (hc 2 1),
    unipotentAverage_add hP hω ?_ (hc 1 2), unipotentAverage_smul]
  · exact fun g ↦ (hc 0 0 g).const_smul (2⁻¹ : ℂ)
  · exact fun g ↦ ((hc 0 0 g).const_smul (2⁻¹ : ℂ)).add (hc 1 2 g)

private lemma casimirTwo_unipotentAverage (hP : IsBounded P) (hω : Continuous ω)
    (h : IsUnipotentC2 Φ) :
    casimirTwo (unipotentAverage P ω Φ) = unipotentAverage P ω (casimirTwo Φ) := by
  have h₂ (b b' : Fin 3) : lieDerivTwo b (lieDerivTwo b' (unipotentAverage P ω Φ)) =
      unipotentAverage P ω (lieDerivTwo b (lieDerivTwo b' Φ)) := by
    rw [lieDerivTwo_unipotentAverage b' hP hω h.isUnipotentC1,
      lieDerivTwo_unipotentAverage b hP hω (h.isUnipotentC1_lieDerivTwo b')]
  have hc (b b' : Fin 3) : IsUnipotentContinuous (lieDerivTwo b (lieDerivTwo b' Φ)) :=
    (h.isUnipotentC1_lieDerivTwo b').isUnipotentContinuous_lieDerivTwo b
  rw [casimirTwo, casimirTwo, h₂, h₂, h₂, unipotentAverage_add hP hω ?_ (hc 2 1),
    unipotentAverage_add hP hω ?_ (hc 1 2), unipotentAverage_smul]
  · exact fun g ↦ (hc 0 0 g).const_smul (2⁻¹ : ℂ)
  · exact fun g ↦ ((hc 0 0 g).const_smul (2⁻¹ : ℂ)).add (hc 1 2 g)

private lemma contDiff_sl2Exp_mul_apply (i j : Fin 2) :
    ContDiff ℝ 2 fun s : ℝ ↦ (sl2Exp b (s * w) : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp only [sl2Exp, Fin.zero_eta, Fin.mk_one, of_apply, cons_val_zero, cons_val_one] <;> fun_prop

private lemma contDiff_sl2Exp_one_apply (i j : Fin 2) :
    ContDiff ℝ 2 fun t : ℂ ↦ (sl2Exp 1 t : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [sl2Exp, Fin.zero_eta, Fin.mk_one, of_apply, cons_val_zero, cons_val_one] <;> fun_prop

private lemma contDiff_mul_apply_of_contDiff {γ₁ γ₂ : E → SL(2, ℂ)}
    (h₁ : ∀ i j, ContDiff ℝ 2 fun x ↦ (γ₁ x : Matrix (Fin 2) (Fin 2) ℂ) i j)
    (h₂ : ∀ i j, ContDiff ℝ 2 fun x ↦ (γ₂ x : Matrix (Fin 2) (Fin 2) ℂ) i j) (i j : Fin 2) :
    ContDiff ℝ 2 fun x ↦ ((γ₁ x * γ₂ x : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  simp only [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  exact ((h₁ i 0).mul (h₂ 0 j)).add ((h₁ i 1).mul (h₂ 1 j))

variable {k : ℕ} {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {y : ℝ}

private lemma contDiff_bianchiLift_comp_of_analyticAt
    (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) {γ : E → SL(2, ℂ)}
    (hγ : ∀ i j, ContDiff ℝ 2 fun x ↦ (γ x : Matrix (Fin 2) (Fin 2) ℂ) i j) :
    ContDiff ℝ 2 fun x ↦ bianchiLift k F (γ x) := by
  have h₀₀ : ContDiff ℝ 2 fun x ↦ (γ x : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := hγ 0 0
  have h₀₁ : ContDiff ℝ 2 fun x ↦ (γ x : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := hγ 0 1
  have h₁₀ : ContDiff ℝ 2 fun x ↦ (γ x : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := hγ 1 0
  have h₁₁ : ContDiff ℝ 2 fun x ↦ (γ x : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := hγ 1 1
  have hN (x : E) : moebiusDenom (γ x) (0, 1) ≠ 0 :=
    (moebiusDenom_pos (γ x) (p := (0, 1)) one_pos).ne'
  have hD : ContDiff ℝ 2 fun x ↦ moebiusDenom (γ x) (0, 1) := by
    simp only [moebiusDenom]
    fun_prop
  have hM : ContDiff ℝ 2 fun x ↦ moebius (γ x) (0, 1) := by
    simp only [moebius, div_eq_mul_inv, ← ofReal_inv]
    fun_prop (disch := first | exact hN | exact hN _)
  have hE : ContDiff ℝ 2 fun x ↦ extend F (moebius (γ x) (0, 1)) :=
    contDiff_iff_contDiffAt.2 fun x ↦
      ContDiffAt.comp (g := extend F) x (hF (γ x • basePoint)).contDiffAt hM.contDiffAt
  simp only [bianchiLift_apply, inv_automorphyFactor]
  refine contDiff_pi.2 fun i ↦ ?_
  simp only [mulVec]
  refine ContDiff.sum fun j _ ↦ ContDiff.mul ?_ (contDiff_pi.1 hE j)
  simp only [symPowMatrix, of_apply, Matrix.smul_apply, cons_val_zero, cons_val_one, ← ofReal_inv]
  fun_prop (disch := first | exact hN | exact hN _)

private lemma isUnipotentC2_bianchiLift
    (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) :
    IsUnipotentC2 (bianchiLift k F) := fun _ b₁ w₁ b₂ w₂ ↦
  contDiff_bianchiLift_comp_of_analyticAt hF <| contDiff_mul_apply_of_contDiff
    (contDiff_mul_apply_of_contDiff (contDiff_mul_apply_of_contDiff
      (fun i j ↦ (contDiff_sl2Exp_one_apply i j).comp contDiff_fst) fun _ _ ↦ contDiff_const)
      fun i j ↦ (contDiff_sl2Exp_mul_apply b₁ w₁ i j).comp (contDiff_fst.comp contDiff_snd))
    fun i j ↦ (contDiff_sl2Exp_mul_apply b₂ w₂ i j).comp (contDiff_snd.comp contDiff_snd)

private lemma sl2Exp_one_mul_apply_one (j : Fin 2) : (sl2Exp 1 t * g : SL(2, ℂ)) 1 j = g 1 j := by
  rw [SpecialLinearGroup.coe_mul]
  simp [sl2Exp, mul_apply]

private lemma automorphyFactor_sl2Exp_one_mul (p : ℂ × ℝ) :
    automorphyFactor (sl2Exp 1 t * g) p = automorphyFactor g p := by
  simp only [automorphyFactor, sl2Exp_one_mul_apply_one]

private lemma moebius_sl2Exp_one (p : ℂ × ℝ) : moebius (sl2Exp 1 t) p = (p.1 + t, p.2) := by
  simp [moebius, moebiusDenom, sl2Exp]

private lemma moebius_sl2Exp_one_mul :
    moebius (sl2Exp 1 t * g) (0, 1) = ((moebius g (0, 1)).1 + t, (moebius g (0, 1)).2) := by
  rw [moebius_mul _ g (p := (0, 1)) one_pos, moebius_sl2Exp_one]

variable (P ω F) in
/-- The **translation average** `G(x, y) = ∫_{t ∈ P} ω(t) F(x + t, y) dt` of
`F : ℋ₃ → ℂ^{k+1}` over `P ⊆ ℂ` with the weight `ω`. -/
noncomputable def translationAverage : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  fun z ↦ ∫ t in P, ω t • extend F (z.coords.1 + t, z.coords.2)

private lemma extend_translationAverage {p : ℂ × ℝ} (hp : 0 < p.2) :
    extend (translationAverage P ω F) p = ∫ t in P, ω t • extend F (p.1 + t, p.2) := by
  rw [extend, dite_eq_left hp]
  rfl

private lemma continuous_extend_add
    (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) {p : ℂ × ℝ} (hp : 0 < p.2) :
    Continuous fun t : ℂ ↦ extend F (p.1 + t, p.2) :=
  continuous_iff_continuousAt.2 fun t ↦
    (hF (.mk (WithLp.toLp 2 (p.1 + t, p.2)) hp)).continuousAt.comp
      (f := fun t : ℂ ↦ (p.1 + t, p.2)) (by fun_prop)

lemma bianchiLift_translationAverage
    (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) (hP : IsBounded P)
    (hω : Continuous ω) :
    bianchiLift k (translationAverage P ω F) = unipotentAverage P ω (bianchiLift k F) := by
  funext g
  have hpos : 0 < (moebius g (0, 1)).2 := moebius_snd_pos g one_pos
  let L : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ :=
    LinearMap.toContinuousLinearMap (symPowMatrix k (automorphyFactor g (0, 1))⁻¹).mulVecLin
  have hL (v : Fin (k + 1) → ℂ) : L v = symPowMatrix k (automorphyFactor g (0, 1))⁻¹ *ᵥ v :=
    rfl
  rw [bianchiLift_apply, extend_translationAverage hpos, ← hL,
    ← L.integral_comp_comm (integrableOn_smul_of_continuous hP hω (continuous_extend_add hF hpos))]
  simp only [unipotentAverage, hL, mulVec_smul, bianchiLift_apply, automorphyFactor_sl2Exp_one_mul,
    moebius_sl2Exp_one_mul]

/-- **Translation averages of harmonic functions are harmonic**: if `F : ℋ₃ → ℂ^{k+1}` is real
analytic and harmonic (`IsBianchiHarmonic k`), then so is `(x, y) ↦ ∫_P ω(t) F(x + t, y) dt` for
every bounded `P ⊆ ℂ` and continuous `ω`. The lift of the average is the average of the lift over
left translations by unipotent elements, with which the Casimir operators commute. -/
lemma IsBianchiHarmonic.translationAverage
    (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) (h : IsBianchiHarmonic k F)
    (hP : IsBounded P) (hω : Continuous ω) : IsBianchiHarmonic k (translationAverage P ω F) := by
  have hΦ : IsUnipotentC2 (bianchiLift k F) := isUnipotentC2_bianchiLift hF
  rw [IsBianchiHarmonic, bianchiLift_translationAverage hF hP hω,
    casimirOne_unipotentAverage hP hω hΦ, casimirTwo_unipotentAverage hP hω hΦ, h.1, h.2,
    unipotentAverage_smul]
  exact ⟨rfl, rfl⟩

variable (Λ : AddSubgroup ℂ) [Countable Λ]

private lemma setIntegral_add_left_eq (hP : IsAddFundamentalDomain Λ P) {f : ℂ → V}
    (hf : ∀ l ∈ Λ, ∀ s, f (l + s) = f s) (x : ℂ) : ∫ t in P, f (x + t) = ∫ s in P, f s := by
  have hx : (fun t ↦ x + t) '' P = x +ᵥ P :=
    rfl
  rw [← (measurePreserving_add_left volume x).setIntegral_image_emb
    (MeasurableEquiv.addLeft x).measurableEmbedding f P, hx]
  exact (hP.vadd_of_comm x).setIntegral_eq hP fun l s ↦ hf l l.2 s

variable (P μ F y) in
/-- The **Fourier coefficient** `φ_μ(y) = vol(P)⁻¹ ∫_{x ∈ P} ψ(-μx) F(x, y) dx` (LMFDB
`mf.bianchi.spaces`) of `F : ℋ₃ → ℂ^{k+1}` at the frequency `μ ∈ ℂ`, over `P ⊆ ℂ`, where
`ψ(z) = e^{2πi(z + z̄)}`: for `F` invariant under the translations by a lattice `Λ` of `ℂ`, `P` a
fundamental domain of `Λ` and `μ` in the dual lattice (`ψ(μλ) = 1` on `Λ`), it is the coefficient
of `ψ(μx)` in the Fourier series of `x ↦ F(x, y)`. -/
noncomputable def bianchiFourierCoeff : Fin (k + 1) → ℂ :=
  (volume.real P : ℂ)⁻¹ • ∫ x in P, cexp (-(2 * π * I * (μ * x + conj (μ * x)))) • extend F (x, y)

/-- **A Fourier mode is a translation average**: if `F` is invariant under the translations by a
countable subgroup `Λ` of `ℂ`, `P` is a fundamental domain of `Λ` and `ψ(μλ) = 1` on `Λ`, the
Fourier mode `ψ(μx) φ_μ(y)` of `F` is `∫_P vol(P)⁻¹ ψ(-μt) F(x + t, y) dt`. -/
lemma bianchiFourierMode_bianchiFourierCoeff (hP : IsAddFundamentalDomain Λ P)
    (hF : ∀ l ∈ Λ, ∀ p : ℂ × ℝ, extend F (l + p.1, p.2) = extend F p)
    (hμ : ∀ l ∈ Λ, cexp (2 * π * I * (μ * l + conj (μ * l))) = 1) :
    bianchiFourierMode μ (bianchiFourierCoeff P μ F) = translationAverage P
      (fun t ↦ (volume.real P : ℂ)⁻¹ * cexp (-(2 * π * I * (μ * t + conj (μ * t))))) F := by
  funext z
  have he (x t : ℂ) : cexp (-(2 * π * I * (μ * (x + t) + conj (μ * (x + t))))) =
      cexp (-(2 * π * I * (μ * x + conj (μ * x)))) *
        cexp (-(2 * π * I * (μ * t + conj (μ * t)))) := by
    rw [← exp_add]
    congr 1
    simp only [mul_add, map_add]
    ring1
  have hf (l : ℂ) (hl : l ∈ Λ) (s : ℂ) :
      cexp (-(2 * π * I * (μ * (l + s) + conj (μ * (l + s))))) • extend F (l + s, z.coords.2) =
        cexp (-(2 * π * I * (μ * s + conj (μ * s)))) • extend F (s, z.coords.2) := by
    rw [he, hF l hl (s, z.coords.2), exp_neg (2 * π * I * (μ * l + conj (μ * l))), hμ l hl,
      inv_one, one_mul]
  simp only [bianchiFourierMode, bianchiFourierCoeff]
  rw [← setIntegral_add_left_eq Λ hP (f := fun s ↦ cexp (-(2 * π * I * (μ * s + conj (μ * s)))) •
    extend F (s, z.coords.2)) hf z.coords.1, ← integral_smul, ← integral_smul]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  simp only [he, smul_smul]
  congr 1
  rw [exp_neg (2 * π * I * (μ * z.coords.1 + conj (μ * z.coords.1)))]
  field_simp

/-- **The Fourier modes of a harmonic function are harmonic** (LMFDB `mf.bianchi.spaces`): if
`F : ℋ₃ → ℂ^{k+1}` is real analytic, harmonic and invariant under the translations by a countable
subgroup `Λ` of `ℂ` with a bounded fundamental domain `P`, and `ψ(μλ) = 1` on `Λ`, then the Fourier
mode `ψ(μx) φ_μ(y)` of `F` (`bianchiFourierCoeff`) is harmonic. -/
lemma isBianchiHarmonic_bianchiFourierMode_bianchiFourierCoeff
    (hFa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) (h : IsBianchiHarmonic k F)
    (hP : IsAddFundamentalDomain Λ P) (hPb : IsBounded P)
    (hF : ∀ l ∈ Λ, ∀ p : ℂ × ℝ, extend F (l + p.1, p.2) = extend F p)
    (hμ : ∀ l ∈ Λ, cexp (2 * π * I * (μ * l + conj (μ * l))) = 1) :
    IsBianchiHarmonic k (bianchiFourierMode μ (bianchiFourierCoeff P μ F)) := by
  rw [bianchiFourierMode_bianchiFourierCoeff Λ hP hF hμ]
  exact h.translationAverage hFa hPb (by fun_prop)

/-- **The Fourier coefficients have moderate growth**: if `‖F(x, y)‖ ≤ C yⁿ` for `y ≥ 1`, then
`‖φ_μ(y)‖ ≤ C yⁿ` for `y ≥ 1`, over a bounded `P`. -/
lemma norm_bianchiFourierCoeff_le (hPb : IsBounded P) {C : ℝ} {n : ℕ}
    (hC : ∀ z : HyperbolicThreeSpace, 1 ≤ z.height → ‖F z‖ ≤ C * z.height ^ n) (hy : 1 ≤ y) :
    ‖bianchiFourierCoeff P μ F y‖ ≤ C * y ^ n := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hb (x : ℂ) : ‖extend F (x, y)‖ ≤ C * y ^ n := by
    rw [extend, dite_eq_left hy₀]
    exact hC _ hy
  have hC₀ : 0 ≤ C * y ^ n := (norm_nonneg _).trans (hb 0)
  have hI : ‖∫ x in P, cexp (-(2 * π * I * (μ * x + conj (μ * x)))) • extend F (x, y)‖ ≤
      C * y ^ n * volume.real P :=
    norm_setIntegral_le_of_norm_le_const hPb.measure_lt_top fun x _ ↦ by
      have hre : (-(2 * π * I * (μ * x + conj (μ * x)))).re = 0 := by
        rw [add_conj]
        simp
      rw [norm_smul, norm_exp, hre, Real.exp_zero, one_mul]
      exact hb x
  rw [bianchiFourierCoeff, norm_smul, norm_inv, norm_real, Real.norm_of_nonneg measureReal_nonneg]
  rcases measureReal_nonneg.eq_or_lt with h₀ | h₀
  · rw [← h₀]
    simpa using hC₀
  · rw [inv_mul_le_iff₀ h₀]
    linarith

private lemma hasDerivAt_setIntegral {f : ℂ × ℝ → V} (hf : ContDiffOn ℝ 1 f (univ ×ˢ Ioi 0))
    (hP : IsBounded P) (hy : 0 < y) :
    HasDerivAt (fun s : ℝ ↦ ∫ t in P, f (t, s)) (∫ t in P, fderiv ℝ f (t, y) (0, 1)) y := by
  have hU : IsOpen (univ ×ˢ Ioi (0 : ℝ) : Set (ℂ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioi
  have hD : ContinuousOn (fun p : ℂ × ℝ ↦ fderiv ℝ f p (0, 1)) (univ ×ˢ Ioi 0) :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hsub : closedBall y (y / 2) ⊆ Ioi 0 := fun s hs ↦ by
    have h : |s - y| ≤ y / 2 := mem_closedBall.mp hs
    have h' : -(y / 2) ≤ s - y := (abs_le.mp h).1
    simp only [mem_Ioi]
    linarith
  rcases (hP.isCompact_closure.prod (isCompact_closedBall y (y / 2))).exists_bound_of_continuousOn
    (hD.mono fun p hp ↦ ⟨mem_univ _, hsub hp.2⟩) with ⟨B, hB⟩
  have hc (s : ℝ) (hs : 0 < s) : Continuous fun t : ℂ ↦ f (t, s) :=
    hf.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      fun _ ↦ ⟨mem_univ _, hs⟩
  have hc' : Continuous fun t : ℂ ↦ fderiv ℝ f (t, y) (0, 1) :=
    hD.comp_continuous (continuous_id.prodMk continuous_const) fun _ ↦ ⟨mem_univ _, hy⟩
  have hdiff (t : ℂ) (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun s : ℝ ↦ f (t, s)) (fderiv ℝ f (t, s) (0, 1)) s := by
    have hd : HasDerivAt (fun r : ℝ ↦ (t, r)) ((0 : ℂ), (1 : ℝ)) s :=
      (hasDerivAt_const s t).prodMk (hasDerivAt_id' s)
    exact ((hf.differentiableOn one_ne_zero (t, s) ⟨mem_univ _, hs⟩).differentiableAt
      (hU.mem_nhds ⟨mem_univ _, hs⟩)).hasFDerivAt.comp_hasDerivAt s hd
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds y (half_pos hy))
    (Filter.mem_of_superset (Ioi_mem_nhds hy) fun s hs ↦ (hc s hs).aestronglyMeasurable)
    (((hc y hy).continuousOn.integrableOn_compact hP.isCompact_closure).mono_set subset_closure)
    hc'.aestronglyMeasurable
    (ae_restrict_of_ae_restrict_of_subset subset_closure <|
      ae_restrict_of_forall_mem isClosed_closure.measurableSet fun t ht s hs ↦
        hB (t, s) ⟨ht, ball_subset_closedBall hs⟩)
    (integrableOn_const hP.measure_lt_top.ne)
    (.of_forall fun t s hs ↦ hdiff t s (hsub (ball_subset_closedBall hs)))).2

private lemma contDiffOn_setIntegral (hP : IsBounded P) (n : ℕ) {f : ℂ × ℝ → V}
    (hf : ContDiffOn ℝ ⊤ f (univ ×ˢ Ioi 0)) :
    ContDiffOn ℝ n (fun s : ℝ ↦ ∫ t in P, f (t, s)) (Ioi 0) := by
  induction n generalizing f with
  | zero =>
    exact contDiffOn_zero.2 fun y hy ↦
      (hasDerivAt_setIntegral (hf.of_le le_top) hP hy).continuousAt.continuousWithinAt
  | succ n ih =>
    have hU : IsOpen (univ ×ˢ Ioi (0 : ℝ) : Set (ℂ × ℝ)) :=
      isOpen_univ.prod isOpen_Ioi
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy ↦ (hasDerivAt_setIntegral (hf.of_le le_top) hP
      hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih ((hf.fderiv_of_isOpen hU le_top).clm_apply contDiffOn_const)).congr fun y hy ↦
      (hasDerivAt_setIntegral (hf.of_le le_top) hP hy).deriv

/-- **The Fourier coefficients are smooth**: the Fourier coefficient `φ_μ` of a real analytic
`F : ℋ₃ → ℂ^{k+1}`, over a bounded `P`, is `Cⁿ` on `(0, ∞)` for every `n`. -/
lemma contDiffOn_bianchiFourierCoeff
    (hFa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) (hPb : IsBounded P)
    (n : ℕ) : ContDiffOn ℝ n (bianchiFourierCoeff P μ F) (Ioi 0) := by
  have hE : ContDiffOn ℝ ⊤ (extend F) (univ ×ˢ Ioi 0) := fun p hp ↦
    (hFa (.mk (WithLp.toLp 2 p) hp.2)).contDiffAt.contDiffWithinAt
  have hψ : ContDiff ℝ ⊤ fun p : ℂ × ℝ ↦ cexp (-(2 * π * I * (μ * p.1 + conj (μ * p.1)))) := by
    fun_prop
  exact (contDiffOn_setIntegral hPb n (hψ.contDiffOn.smul hE)).const_smul _

variable {K : Type*} [Field K] {σ : K →+* ℂ} {Γ : Subgroup (GL (Fin 2) (𝓞 K))}

lemma exists_mem_gamma0GL (𝔑 : Ideal (𝓞 K)) (a : 𝓞 K) :
    ∃ γ ∈ 𝔑.gamma0GL, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1] :=
  ⟨SpecialLinearGroup.toGL ⟨!![1, a; 0, 1], by simp⟩, 𝔑.zero_mem, rfl⟩

lemma HasPolynomialGrowthAtCusps.exists_norm_le (h : HasPolynomialGrowthAtCusps σ k F) :
    ∃ (C : ℝ) (n : ℕ), ∀ z : HyperbolicThreeSpace, 1 ≤ z.height → ‖F z‖ ≤ C * z.height ^ n := by
  simpa only [map_one, bianchiSlash_one] using h 1

/-- **The Fourier modes of a harmonic function of moderate growth are Fourier–Bessel functions**
(LMFDB `mf.bianchi.spaces`, `mf.bianchi.newform`): for `k ≥ 1` and `μ ≠ 0`, if `F : ℋ₃ → ℂ^{k+1}`
is real analytic, harmonic, of moderate growth (`‖F(x, y)‖ ≤ C yⁿ` for `y ≥ 1`) and invariant under
the translations by a countable subgroup `Λ` of `ℂ` with a bounded fundamental domain `P`, and
`ψ(μλ) = 1` on `Λ`, then its Fourier mode `ψ(μx) φ_μ(y)` is `φ_μ(1)₀ / W_k(u, 4π|μ|)₀` times
`y W_k(u, 4π|μ|y) ψ(μx)` (`bianchiWhittakerFunction`). -/
lemma bianchiFourierMode_bianchiFourierCoeff_eq_smul (hk : k ≠ 0) (hμ₀ : μ ≠ 0)
    (hFa : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) (h : IsBianchiHarmonic k F)
    (hP : IsAddFundamentalDomain Λ P) (hPb : IsBounded P)
    (hF : ∀ l ∈ Λ, ∀ p : ℂ × ℝ, extend F (l + p.1, p.2) = extend F p)
    (hμ : ∀ l ∈ Λ, cexp (2 * π * I * (μ * l + conj (μ * l))) = 1)
    (hgrowth : ∃ (C : ℝ) (n : ℕ), ∀ z : HyperbolicThreeSpace, 1 ≤ z.height →
      ‖F z‖ ≤ C * z.height ^ n) : bianchiFourierMode μ (bianchiFourierCoeff P μ F) =
      (bianchiFourierCoeff P μ F 1 0 / bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖) 0) •
        bianchiWhittakerFunction μ k := by
  rcases hgrowth with ⟨C, n, hC⟩
  exact bianchiFourierMode_eq_smul_bianchiWhittakerFunction hk hμ₀
    (by exact_mod_cast contDiffOn_bianchiFourierCoeff hFa hPb 2)
    ⟨C, n, fun y hy ↦ norm_bianchiFourierCoeff_le hPb hC hy⟩
    (isBianchiHarmonic_bianchiFourierMode_bianchiFourierCoeff Λ hFa h hP hPb hF hμ)

private lemma bianchiSlash_sl2Exp_one (z : HyperbolicThreeSpace) :
    bianchiSlash k (sl2Exp 1 t) F z = extend F (z.coords.1 + t, z.coords.2) := by
  have hA : automorphyFactor (sl2Exp 1 t) z.coords = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [automorphyFactor, sl2Exp]
  rw [bianchiSlash, hA, inv_one, symPowMatrix_one, one_mulVec,
    ← extend_coords (sl2Exp 1 t • z) F, coords_smul, moebius_sl2Exp_one]

/-- **Invariant functions are periodic**: if `F` is invariant under `Γ` (`IsBianchiSlashInvariant`),
then `F(x + λ, y) = F(x, y)` for every translation `λ` fixing the cusp `∞` (`cuspTranslations`). -/
lemma IsBianchiSlashInvariant.extend_add_eq (hF : IsBianchiSlashInvariant σ Γ k F) {l : ℂ}
    (hl : l ∈ cuspTranslations σ Γ 1) (p : ℂ × ℝ) : extend F (l + p.1, p.2) = extend F p := by
  induction hl using AddSubgroup.closure_induction generalizing p with
  | mem l hl =>
    rcases hl with ⟨a, ⟨γ, hγ, he⟩, rfl⟩
    have he' (i j : Fin 2) : algebraMap (𝓞 K) K ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j) =
        !![1, a; 0, 1] i j := by
      simpa using congrFun (congrFun he i) j
    have hinv : bianchiSlash k (sl2Exp 1 (σ a)) F = F := by
      refine hF γ hγ _ 1 ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2Exp, he']
    by_cases hp : 0 < p.2
    · have h := congrFun hinv (.mk (WithLp.toLp 2 p) hp)
      rw [bianchiSlash_sl2Exp_one] at h
      rw [add_comm (σ a)]
      exact h.trans (extend_coords _ F).symm
    · simp [extend, hp]
  | zero => simp
  | add l₁ l₂ _ _ h₁ h₂ =>
    rw [add_assoc, h₁ (l₂ + p.1, p.2), h₂]
  | neg l _ h =>
    rw [← h (-l + p.1, p.2), add_neg_cancel_left]

/-- **The constant term of a cusp form vanishes** (LMFDB `mf.bianchi.spaces`): the Fourier
coefficient `φ_0` of a cuspidal `F` (`IsBianchiCuspidal`) over a fundamental domain of the
translations fixing `∞` is `0`. -/
lemma IsBianchiCuspidal.bianchiFourierCoeff_zero (hF : IsBianchiCuspidal σ Γ k F)
    (hP : IsAddFundamentalDomain (cuspTranslations σ Γ 1) P) (hy : 0 < y) :
    bianchiFourierCoeff P 0 F y = 0 := by
  have h : ∫ x in P, extend F (x, y) = 0 := by
    simpa only [map_one, bianchiSlash_one] using (hF 1 y P hy hP).2
  simp [bianchiFourierCoeff, h]

/-- **The Fourier modes of a Bianchi modular form are Fourier–Bessel functions** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): for a Bianchi modular form `F` of weight `k ≥ 1` and
level `Γ`, a countable subgroup `Λ` of the translations fixing `∞` with a bounded fundamental domain
`P` and a frequency `μ ≠ 0` with `ψ(μλ) = 1` on `Λ`, the Fourier mode `ψ(μx) φ_μ(y)` of `F` is
`φ_μ(1)₀ / W_k(u, 4π|μ|)₀` times `y W_k(u, 4π|μ|y) ψ(μx)`. -/
lemma IsBianchiModularForm.fourierMode_eq_smul_bianchiWhittakerFunction
    (hF : IsBianchiModularForm σ Γ k F) (hΛ : Λ ≤ cuspTranslations σ Γ 1) (hk : k ≠ 0) (hμ₀ : μ ≠ 0)
    (hP : IsAddFundamentalDomain Λ P) (hPb : IsBounded P)
    (hμ : ∀ l ∈ Λ, cexp (2 * π * I * (μ * l + conj (μ * l))) = 1) :
    bianchiFourierMode μ (bianchiFourierCoeff P μ F) =
      (bianchiFourierCoeff P μ F 1 0 / bianchiWhittakerVector k (μ / ‖μ‖) (4 * π * ‖μ‖) 0) •
        bianchiWhittakerFunction μ k :=
  bianchiFourierMode_bianchiFourierCoeff_eq_smul Λ hk hμ₀ hF.analyticAt hF.harmonic hP hPb
    (fun _ hl ↦ hF.invariant.extend_add_eq (hΛ hl)) hμ hF.growth.exists_norm_le

variable [NumberField K] {δ : ℂ}

/-- **The Fourier–Bessel expansion of a Bianchi modular form** (LMFDB `mf.bianchi.spaces`,
`mf.bianchi.newform`): let `F` be a Bianchi modular form of weight `k ≥ 1` and level `Γ` over a
number field `K` embedded in `ℂ` by `σ`, `Λ` a countable subgroup of the translations fixing `∞`
with a bounded fundamental domain `P`, and `δ` with `|δ| = √|Δ|` such that the frequencies
`σ(α) / δ`, `α ∈ 𝒪_K`, are dual to `Λ`. If the Fourier series `∑_{α ≠ 0} ψ(μx) φ_μ(y)`,
`μ = σ(α) / δ`, converges to `F` (Fourier inversion, with vanishing constant term, an unproved
hypothesis here), then `F` has the Fourier–Bessel expansion of weight `k`
(`HasBianchiWhittakerExpansion`) with `c(α) = φ_μ(1)₀ / W_k(u, 4π|μ|)₀`. -/
lemma IsBianchiModularForm.hasBianchiWhittakerExpansion (hF : IsBianchiModularForm σ Γ k F)
    (hΛ : Λ ≤ cuspTranslations σ Γ 1) (hk : k ≠ 0) (hδ : ‖δ‖ = √|(discr K : ℝ)|)
    (hP : IsAddFundamentalDomain Λ P) (hPb : IsBounded P)
    (hdual : ∀ α : 𝓞 K, ∀ l ∈ Λ, cexp (2 * π * I * (σ α / δ * l + conj (σ α / δ * l))) = 1)
    (hsum : ∀ z : HyperbolicThreeSpace, HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦
      bianchiFourierMode (σ α.1 / δ) (bianchiFourierCoeff P (σ α.1 / δ) F) z) (F z)) :
    HasBianchiWhittakerExpansion σ δ k (extend F) fun α ↦ bianchiFourierCoeff P (σ α / δ) F 1 0 /
      bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 := by
  intro p hp
  have he (α : {α : 𝓞 K // α ≠ 0}) : bianchiFourierMode (σ α.1 / δ)
      (bianchiFourierCoeff P (σ α.1 / δ) F) (.mk (WithLp.toLp 2 p) hp) =
        bianchiWhittakerTerm σ δ k (fun α ↦ bianchiFourierCoeff P (σ α / δ) F 1 0 /
          bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0) p α :=
    bianchiFourierMode_eq_bianchiWhittakerTerm hk hδ α.2
      (by exact_mod_cast contDiffOn_bianchiFourierCoeff hF.analyticAt hPb 2)
      (hF.growth.exists_norm_le.imp fun _ ↦ Exists.imp fun _ hC _ hy ↦
        norm_bianchiFourierCoeff_le hPb hC hy)
      (isBianchiHarmonic_bianchiFourierMode_bianchiFourierCoeff Λ hF.analyticAt hF.harmonic hP hPb
        (fun _ hl ↦ hF.invariant.extend_add_eq (hΛ hl)) (hdual α)) _
  rw [extend, dite_eq_left hp]
  simpa only [he] using hsum (.mk (WithLp.toLp 2 p) hp)

/-- **The Fourier–Bessel expansion of a Bianchi modular form, over a lattice given by a basis**
(LMFDB `mf.bianchi.spaces`, `mf.bianchi.newform`): the expansion of
`IsBianchiModularForm.hasBianchiWhittakerExpansion` for the lattice `Λ` spanned over `ℤ` by an
`ℝ`-basis `e` of `ℂ`, contained in the translations fixing `∞`, and its fundamental parallelogram
`P = {s e₀ + t e₁ | 0 ≤ s, t < 1}`. -/
lemma IsBianchiModularForm.hasBianchiWhittakerExpansion_of_basis (hF : IsBianchiModularForm σ Γ k F)
    {ι : Type*} [Finite ι] (e : Basis ι ℝ ℂ)
    (hΛ : (Submodule.span ℤ (range e)).toAddSubgroup ≤ cuspTranslations σ Γ 1) (hk : k ≠ 0)
    (hδ : ‖δ‖ = √|(discr K : ℝ)|) (hdual : ∀ α : 𝓞 K, ∀ l ∈ Submodule.span ℤ (range e),
      cexp (2 * π * I * (σ α / δ * l + conj (σ α / δ * l))) = 1)
    (hsum : ∀ z : HyperbolicThreeSpace, HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ bianchiFourierMode
      (σ α.1 / δ) (bianchiFourierCoeff (ZSpan.fundamentalDomain e) (σ α.1 / δ) F) z) (F z)) :
    HasBianchiWhittakerExpansion σ δ k (extend F) fun α ↦
      bianchiFourierCoeff (ZSpan.fundamentalDomain e) (σ α / δ) F 1 0 /
        bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 := by
  have : Countable (Submodule.span ℤ (range e)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (range e)))
  exact hF.hasBianchiWhittakerExpansion _ hΛ hk hδ (ZSpan.isAddFundamentalDomain' e _)
    (ZSpan.fundamentalDomain_isBounded e) hdual hsum

variable (σ) {x : K}

private lemma mem_span_integralBasis (z : K) :
    σ z ∈ Submodule.span ℝ (range fun i ↦ σ (integralBasis K i)) := by
  rw [← (integralBasis K).sum_repr z, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have h : σ ((integralBasis K).repr z i • integralBasis K i) =
      (((integralBasis K).repr z i : ℚ) : ℝ) • σ (integralBasis K i) := by
    rw [Rat.smul_def, map_mul, map_ratCast, real_smul, ofReal_ratCast]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma top_le_span_integralBasis (hx : (σ x).im ≠ 0) :
    ⊤ ≤ Submodule.span ℝ (range fun i ↦ σ (integralBasis K i)) := by
  intro z _
  have hz : z = (z.re - z.im * (σ x).re / (σ x).im) • σ 1 + (z.im / (σ x).im) • σ x := by
    apply Complex.ext
    · simp only [map_one, add_re, smul_re, one_re, smul_eq_mul]
      field_simp
      ring1
    · simp only [map_one, add_im, smul_im, one_im, smul_eq_mul, mul_zero, zero_add]
      field_simp
  rw [hz]
  exact add_mem (Submodule.smul_mem _ _ (mem_span_integralBasis σ 1))
    (Submodule.smul_mem _ _ (mem_span_integralBasis σ x))

private lemma linearIndependent_integralBasis (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) :
    LinearIndependent ℝ fun i ↦ σ (integralBasis K i) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span_integralBasis σ hx) <| by
    rw [Complex.finrank_real_complex, ← hK, ← RingOfIntegers.rank,
      finrank_eq_card_chooseBasisIndex]

private lemma algebraMap_trace_eq (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (z : K) :
    algebraMap ℚ ℂ (Algebra.trace ℚ K z) = σ z + conj (σ z) := by
  classical
  have hne : σ.toRatAlgHom ≠ ((starRingEnd ℂ).comp σ).toRatAlgHom := by
    intro h
    have h' : σ x = conj (σ x) := congrArg (fun φ : K →ₐ[ℚ] ℂ ↦ φ x) h
    exact hx (conj_eq_iff_im.mp h'.symm)
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) =
      {σ.toRatAlgHom, ((starRingEnd ℂ).comp σ).toRatAlgHom} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, AlgHom.card, hK, Finset.card_pair hne])).symm
  rw [trace_eq_sum_embeddings (E := ℂ), huniv, Finset.sum_pair hne]
  rfl

variable (K) in
private lemma card_chooseBasisIndex (hK : finrank ℚ K = 2) :
    Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
  rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hK]

variable (K) in
/-- An integral basis of a quadratic field `K`, indexed by `Fin 2`. -/
private noncomputable def finTwoBasis (hK : finrank ℚ K = 2) : Basis (Fin 2) ℤ (𝓞 K) :=
  (RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq (card_chooseBasisIndex K hK))

private lemma discr_eq_sq (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) : (discr K : ℂ) =
    (σ (finTwoBasis K hK 0) * conj (σ (finTwoBasis K hK 1)) -
      σ (finTwoBasis K hK 1) * conj (σ (finTwoBasis K hK 0))) ^ 2 := by
  let e : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (card_chooseBasisIndex K hK)
  have h₁ : (discr K : ℚ) = Algebra.discr ℚ ((integralBasis K).reindex e) := by
    rw [coe_discr, Basis.coe_reindex, Algebra.discr_reindex]
  have hb (i : Fin 2) : (integralBasis K).reindex e i = (finTwoBasis K hK i : K) := by
    rw [Basis.reindex_apply, integralBasis_apply, finTwoBasis, Basis.reindex_apply]
  have h₂ : (discr K : ℂ) = algebraMap ℚ ℂ (discr K : ℚ) := by
    simp
  rw [h₂, h₁, Algebra.discr_def, det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb, map_sub, map_mul,
    algebraMap_trace_eq σ hK hx]
  ring1

private lemma finTwoBasis_det_ne_zero (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) :
    σ (finTwoBasis K hK 0) * conj (σ (finTwoBasis K hK 1)) -
      σ (finTwoBasis K hK 1) * conj (σ (finTwoBasis K hK 0)) ≠ 0 := by
  intro h
  have h' : ((discr K : ℤ) : ℂ) = 0 := by
    rw [discr_eq_sq σ hK hx, h, zero_pow two_ne_zero]
  exact discr_ne_zero K (Int.cast_eq_zero.mp h')

private lemma conj_mul_conj_sub (u v : ℂ) :
    conj (u * conj v - v * conj u) = -(u * conj v - v * conj u) := by
  simp only [map_sub, map_mul, conj_conj]
  ring1

variable (K) in
private lemma ne_zero_of_sq_eq_discr (hδ : δ ^ 2 = discr K) : δ ≠ 0 := by
  intro h
  rw [h, zero_pow two_ne_zero, eq_comm, Int.cast_eq_zero] at hδ
  exact discr_ne_zero K hδ

/-- **The frequencies `σ(z) / √Δ`, `z ∈ 𝒪_K`, are dual to `σ(𝒪_K)`**: for a quadratic field `K`
embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ` and `δ² = Δ`, `σ(z) / δ + conj(σ(z) / δ)` is an integer
for every `z ∈ 𝒪_K`, that is, `𝒪_K / √Δ` lies in the inverse different of `K`. With an integral
basis `(e₀, e₁)`, `Δ = D²` for `D = σ(e₀) conj(σ(e₁)) - σ(e₁) conj(σ(e₀))`, and writing
`1 = c e₀ + d e₁`, `z = m e₀ + n e₁`, one has `σ(z) - conj(σ(z)) = (md - nc) D`. -/
lemma exists_intCast_eq_of_sq_eq_discr (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) (z : 𝓞 K) : ∃ n : ℤ, σ z / δ + conj (σ z / δ) = n := by
  let B : Basis (Fin 2) ℤ (𝓞 K) := finTwoBasis K hK
  let D : ℂ := σ (B 0) * conj (σ (B 1)) - σ (B 1) * conj (σ (B 0))
  have hD : δ ^ 2 = D ^ 2 := hδ.trans (discr_eq_sq σ hK hx)
  have hD₀ : D ≠ 0 := finTwoBasis_det_ne_zero σ hK hx
  have hconj : conj D = -D := conj_mul_conj_sub _ _
  have hcoord (w : 𝓞 K) : σ w = (B.repr w 0 : ℂ) * σ (B 0) + (B.repr w 1 : ℂ) * σ (B 1) := by
    have h : σ ((∑ i, B.repr w i • B i : 𝓞 K) : K) = σ w := by
      rw [B.sum_repr w]
    rw [← h]
    simp
  have h₁ : (B.repr 1 0 : ℂ) * σ (B 0) + (B.repr 1 1 : ℂ) * σ (B 1) = 1 := by
    rw [← hcoord 1]
    simp
  have h₂ : (B.repr 1 0 : ℂ) * conj (σ (B 0)) + (B.repr 1 1 : ℂ) * conj (σ (B 1)) = 1 := by
    simpa using congrArg conj h₁
  have key : σ z - conj (σ z) =
      ((B.repr z 0 * B.repr 1 1 - B.repr z 1 * B.repr 1 0 : ℤ) : ℂ) * D := by
    rw [hcoord z]
    simp only [map_add, map_mul, map_intCast]
    push_cast
    linear_combination ((B.repr z 0 : ℂ) * conj (σ (B 0)) + (B.repr z 1 : ℂ) * conj (σ (B 1))) *
      h₁ - ((B.repr z 0 : ℂ) * σ (B 0) + (B.repr z 1 : ℂ) * σ (B 1)) * h₂
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hD with h | h
  · refine ⟨B.repr z 0 * B.repr 1 1 - B.repr z 1 * B.repr 1 0, ?_⟩
    rw [map_div₀, h, hconj, div_neg, ← sub_eq_add_neg, ← sub_div, key, mul_div_cancel_right₀ _ hD₀]
  · refine ⟨-(B.repr z 0 * B.repr 1 1 - B.repr z 1 * B.repr 1 0), ?_⟩
    rw [map_div₀, h, map_neg, hconj, neg_neg, div_neg, neg_add_eq_sub, ← sub_div, ← neg_sub, key,
      Int.cast_neg, neg_div, mul_div_cancel_right₀ _ hD₀]

private lemma cexp_eq_one_of_sq_eq_discr (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) (α a : 𝓞 K) :
    cexp (2 * π * I * (σ α / δ * σ a + conj (σ α / δ * σ a))) = 1 := by
  rcases exists_intCast_eq_of_sq_eq_discr σ hK hx hδ (α * a) with ⟨n, hn⟩
  have e : σ α / δ * σ a = σ (α * a : 𝓞 K) / δ := by
    push_cast
    rw [map_mul]
    ring1
  rw [e, hn, mul_comm, exp_int_mul_two_pi_mul_I]

private lemma eq_zero_of_add_conj_eq_zero {u v z : ℂ} (hD : u * conj v - v * conj u ≠ 0)
    (hu : z * u + conj (z * u) = 0) (hv : z * v + conj (z * v) = 0) : z = 0 := by
  have h : z * (u * conj v - v * conj u) = 0 := by
    simp only [map_mul] at hu hv
    linear_combination conj v * hu - conj u * hv
  exact (mul_eq_zero.mp h).resolve_right hD

/-- **The dual lattice of `σ(𝒪_K)` is `σ(𝒪_K) / √Δ`**: for a quadratic field `K` embedded in `ℂ`
by `σ` with `σ(K) ⊄ ℝ` and `δ² = Δ`, every `ν ∈ ℂ` with `ν σ(z) + conj(ν σ(z)) ∈ ℤ` for all
`z ∈ 𝒪_K` is `σ(α) / δ` for some `α ∈ 𝒪_K`: the matrix of the pairing `(σ(e_i e_j) - conj(σ(e_i
e_j))) / δ` on an integral basis has integer entries (`exists_intCast_eq_of_sq_eq_discr`) and
determinant `-1`. -/
lemma exists_div_eq_of_dual (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (hδ : δ ^ 2 = discr K)
    {ν : ℂ} (hν : ∀ z : 𝓞 K, ∃ n : ℤ, ν * σ z + conj (ν * σ z) = n) : ∃ α : 𝓞 K, σ α / δ = ν := by
  let B : Basis (Fin 2) ℤ (𝓞 K) := finTwoBasis K hK
  let D : ℂ := σ (B 0) * conj (σ (B 1)) - σ (B 1) * conj (σ (B 0))
  have hD : δ ^ 2 = D ^ 2 := hδ.trans (discr_eq_sq σ hK hx)
  have hδ₀ : δ ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  have hconjD : conj D = -D := conj_mul_conj_sub _ _
  have hconjδ : conj δ = -δ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hD with h | h
    · rw [h, hconjD]
    · rw [h, map_neg, hconjD]
  have ht (z : 𝓞 K) : ∃ n : ℤ, σ z - conj (σ z) = n * δ := by
    rcases exists_intCast_eq_of_sq_eq_discr σ hK hx hδ z with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hn, map_div₀, hconjδ]
    field_simp
    ring1
  rcases ht (B 0 * B 0) with ⟨m₀₀, h₀₀⟩
  rcases ht (B 0 * B 1) with ⟨m₀₁, h₀₁⟩
  rcases ht (B 1 * B 1) with ⟨m₁₁, h₁₁⟩
  rcases hν (B 0) with ⟨p, hp⟩
  rcases hν (B 1) with ⟨q, hq⟩
  push_cast at h₀₀ h₀₁ h₁₁
  simp only [map_mul] at h₀₀ h₀₁ h₁₁
  have hdet : m₀₀ * m₁₁ - m₀₁ ^ 2 = -1 := by
    have h : ((m₀₀ * m₁₁ - m₀₁ ^ 2 : ℤ) : ℂ) * δ ^ 2 = -1 * δ ^ 2 := by
      push_cast
      linear_combination -(m₁₁ : ℂ) * δ * h₀₀ -
        (σ (B 0) * σ (B 0) - conj (σ (B 0)) * conj (σ (B 0))) * h₁₁ +
        (σ (B 0) * σ (B 1) - conj (σ (B 0)) * conj (σ (B 1)) + (m₀₁ : ℂ) * δ) * h₀₁ + hD
    exact_mod_cast mul_right_cancel₀ (pow_ne_zero 2 hδ₀) h
  have hα : σ (((-m₁₁ * p + m₀₁ * q) • B 0 + (m₀₁ * p - m₀₀ * q) • B 1 : 𝓞 K) : K) =
      ((-m₁₁ * p + m₀₁ * q : ℤ) : ℂ) * σ (B 0) + ((m₀₁ * p - m₀₀ * q : ℤ) : ℂ) * σ (B 1) := by
    simp
  have hdetC : (m₀₀ : ℂ) * m₁₁ - (m₀₁ : ℂ) ^ 2 = -1 := by
    exact_mod_cast hdet
  refine ⟨(-m₁₁ * p + m₀₁ * q) • B 0 + (m₀₁ * p - m₀₀ * q) • B 1, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_add_conj_eq_zero (finTwoBasis_det_ne_zero σ hK hx) ?_ ?_
  · rw [hα]
    simp only [map_add, map_sub, map_mul, map_div₀, map_intCast, hconjδ] at hp ⊢
    field_simp
    push_cast
    linear_combination (-(m₁₁ : ℂ) * p + m₀₁ * q) * h₀₀ + ((m₀₁ : ℂ) * p - m₀₀ * q) * h₀₁ -
      δ * hp - δ * p * hdetC
  · rw [hα]
    simp only [map_add, map_sub, map_mul, map_div₀, map_intCast, hconjδ] at hq ⊢
    field_simp
    push_cast
    linear_combination (-(m₁₁ : ℂ) * p + m₀₁ * q) * h₀₁ + ((m₀₁ : ℂ) * p - m₀₀ * q) * h₁₁ -
      δ * hq - δ * q * hdetC

/-- The **basis `(σ(e_i))_i` of `ℂ` over `ℝ`** given by an integral basis `(e_i)_i` of a quadratic
field `K` embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ`, such as an imaginary quadratic field: it spans
the lattice `σ(𝒪_K)` over `ℤ`. -/
noncomputable def integralLatticeBasis (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ ℂ :=
  .mk (linearIndependent_integralBasis σ hK hx) (top_le_span_integralBasis σ hx)

variable {σ}

private lemma integralLatticeBasis_apply (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    integralLatticeBasis σ hK hx i = σ (RingOfIntegers.basis K i) := by
  rw [integralLatticeBasis, Basis.mk_apply, integralBasis_apply]

private lemma span_integralLatticeBasis_le (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hΓ : ∀ a : 𝓞 K, ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1]) :
    (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))).toAddSubgroup ≤
      cuspTranslations σ Γ 1 := by
  rw [Submodule.span_int_eq_addSubgroupClosure, AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases hΓ (RingOfIntegers.basis K i) with ⟨γ, hγ, he⟩
  refine AddSubgroup.subset_closure ⟨integralBasis K i, ⟨γ, hγ, ?_⟩, ?_⟩
  · rw [he, integralBasis_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [integralLatticeBasis]

private lemma cexp_eq_one_of_mem_closure {s : Set ℂ}
    (hs : ∀ l ∈ s, cexp (2 * π * I * (μ * l + conj (μ * l))) = 1) {l : ℂ}
    (hl : l ∈ AddSubgroup.closure s) : cexp (2 * π * I * (μ * l + conj (μ * l))) = 1 := by
  induction hl using AddSubgroup.closure_induction with
  | mem l hl => exact hs l hl
  | zero => simp
  | add l₁ l₂ _ _ h₁ h₂ =>
    have e : 2 * π * I * (μ * (l₁ + l₂) + conj (μ * (l₁ + l₂))) =
        2 * π * I * (μ * l₁ + conj (μ * l₁)) + 2 * π * I * (μ * l₂ + conj (μ * l₂)) := by
      simp only [mul_add, map_add]
      ring1
    rw [e, exp_add, h₁, h₂, one_mul]
  | neg l _ h =>
    have e : 2 * π * I * (μ * -l + conj (μ * -l)) = -(2 * π * I * (μ * l + conj (μ * l))) := by
      simp only [mul_neg, map_neg]
      ring1
    rw [e, exp_neg, h, inv_one]

private lemma cexp_eq_one_of_mem_span (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) (α : 𝓞 K) {l : ℂ}
    (hl : l ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx))) :
    cexp (2 * π * I * (σ α / δ * l + conj (σ α / δ * l))) = 1 := by
  have hgen (l : ℂ) (hl : l ∈ range (integralLatticeBasis σ hK hx)) :
      cexp (2 * π * I * (σ α / δ * l + conj (σ α / δ * l))) = 1 := by
    rcases hl with ⟨i, rfl⟩
    rw [integralLatticeBasis_apply]
    exact cexp_eq_one_of_sq_eq_discr σ hK hx hδ α (RingOfIntegers.basis K i)
  refine cexp_eq_one_of_mem_closure hgen ?_
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  exact hl

private lemma mem_span_integralLatticeBasis (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (z : 𝓞 K) :
    σ z ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)) := by
  have h : σ z = ∑ i, (RingOfIntegers.basis K).repr z i • σ (RingOfIntegers.basis K i) := by
    have h' : σ ((∑ i, (RingOfIntegers.basis K).repr z i • RingOfIntegers.basis K i : 𝓞 K) : K) =
        σ z := by
      rw [(RingOfIntegers.basis K).sum_repr z]
    rw [← h']
    simp
  rw [h]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, integralLatticeBasis_apply hK hx i⟩)

/-- The bijection `α ↦ σ(α) / δ` from the nonzero integers of a quadratic field `K` onto the
nonzero frequencies dual to `σ(𝒪_K)`, for `δ² = Δ`. -/
private noncomputable def dualEquiv (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) : {α : 𝓞 K // α ≠ 0} ≃ {ν : ℂ // ν ≠ 0 ∧
      ∀ l ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)),
        cexp (2 * π * I * (ν * l + conj (ν * l))) = 1} :=
  haveI hδ₀ : δ ≠ 0 := ne_zero_of_sq_eq_discr K hδ
  Equiv.ofBijective (fun α ↦ ⟨σ α.1 / δ, div_ne_zero ((map_ne_zero σ).mpr
    (RingOfIntegers.coe_ne_zero_iff.mpr α.2)) hδ₀, fun _ ↦ cexp_eq_one_of_mem_span hK hx hδ α.1⟩)
    ⟨fun α β h ↦ Subtype.ext <| RingOfIntegers.coe_injective <| σ.injective <|
      (div_left_inj' hδ₀).mp (congrArg Subtype.val h), fun ν ↦ by
      have hν (z : 𝓞 K) : ∃ n : ℤ, ν.1 * σ z + conj (ν.1 * σ z) = n := by
        rcases exp_eq_one_iff.mp (ν.2.2 _ (mem_span_integralLatticeBasis hK hx z)) with ⟨n, hn⟩
        refine ⟨n, mul_left_cancel₀ two_pi_I_ne_zero ?_⟩
        rw [hn]
        ring1
      rcases exists_div_eq_of_dual σ hK hx hδ hν with ⟨α, hα⟩
      refine ⟨⟨α, fun h ↦ ν.2.1 ?_⟩, Subtype.ext hα⟩
      rw [← hα, h]
      simp⟩

/-- **The Fourier–Bessel expansion of a Bianchi modular form over a quadratic field** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): let `K` be a quadratic field embedded in `ℂ` by `σ`
with `σ(K) ⊄ ℝ` (an imaginary quadratic field), `Γ` a level containing the unipotent matrices
`(1, a; 0, 1)`, `a ∈ 𝒪_K` (such as `Γ₀(𝔑)`, `exists_mem_gamma0GL`), `F` a Bianchi modular form of
weight `k ≥ 1` and level `Γ`, and `δ` a square root of the discriminant `Δ` (such as the `Δ^{1/2}`
of `BianchiNewformOfWeight`), so that the frequencies `σ(α) / δ`, `α ∈ 𝒪_K`, are exactly the
points of the dual lattice of `σ(𝒪_K)` (`exists_intCast_eq_of_sq_eq_discr`,
`exists_div_eq_of_dual`). If the Fourier series `∑_{ν ≠ 0} ψ(νx) φ_ν(y)` of `F` over the nonzero
points `ν` of that dual lattice converges to `F` (Fourier inversion on `ℂ / σ(𝒪_K)`, with
vanishing constant term, not proved here), then `F` has the Fourier–Bessel expansion of weight `k`
with `c(α) = φ_μ(1)₀ / W_k(u, 4π|μ|)₀`, `μ = σ(α) / δ`, the Fourier coefficients being taken over
the fundamental parallelogram of `σ(𝒪_K)`. -/
lemma IsBianchiModularForm.hasBianchiWhittakerExpansion_of_finrank_eq_two
    (hF : IsBianchiModularForm σ Γ k F) (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hΓ : ∀ a : 𝓞 K, ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1]) (hk : k ≠ 0)
    (hδ : δ ^ 2 = discr K)
    (hsum : ∀ z : HyperbolicThreeSpace, HasSum (fun ν : {ν : ℂ // ν ≠ 0 ∧
      ∀ l ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)),
        cexp (2 * π * I * (ν * l + conj (ν * l))) = 1} ↦ bianchiFourierMode ν.1
      (bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) ν.1 F) z)
        (F z)) : HasBianchiWhittakerExpansion σ δ k (extend F) fun α ↦
    bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) F 1 0 /
      bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 := by
  have hδ' : ‖δ‖ = √|(discr K : ℝ)| := by
    rw [← Real.sqrt_sq (norm_nonneg δ), ← norm_pow, hδ, norm_intCast]
  exact hF.hasBianchiWhittakerExpansion_of_basis _ (span_integralLatticeBasis_le hK hx hΓ) hk hδ'
    (fun α _ ↦ cexp_eq_one_of_mem_span hK hx hδ α) fun z ↦
      (dualEquiv hK hx hδ).hasSum_iff.mpr (hsum z)

private lemma cuspTranslations_le_span (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) :
    cuspTranslations σ Γ 1 ≤
      (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))).toAddSubgroup := by
  rw [cuspTranslations, AddSubgroup.closure_le]
  rintro _ ⟨a, ⟨γ, -, he⟩, rfl⟩
  have ha : a = algebraMap (𝓞 K) K ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 1) := by
    simpa using (congrFun (congrFun he 0) 1).symm
  rw [ha]
  exact mem_span_integralLatticeBasis hK hx _

/-- **The Fourier–Bessel expansion of a Bianchi cusp form over a quadratic field** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): under the hypotheses of
`IsBianchiModularForm.hasBianchiWhittakerExpansion_of_finrank_eq_two`, for a cusp form `F` it
suffices that the full Fourier series `∑_ν ψ(νx) φ_ν(y)` of `F` over the dual lattice of
`σ(𝒪_K)` converges to `F` (Fourier inversion on `ℂ / σ(𝒪_K)`, not proved here): its constant term
vanishes (`IsBianchiCuspidal.bianchiFourierCoeff_zero`), the translations of `Γ` fixing `∞` being
exactly `σ(𝒪_K)`. -/
lemma IsBianchiModularForm.hasBianchiWhittakerExpansion_of_isBianchiCuspidal
    (hF : IsBianchiModularForm σ Γ k F) (hc : IsBianchiCuspidal σ Γ k F) (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0)
    (hΓ : ∀ a : 𝓞 K, ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1]) (hk : k ≠ 0)
    (hδ : δ ^ 2 = discr K)
    (hsum : ∀ z : HyperbolicThreeSpace, HasSum (fun ν : {ν : ℂ //
      ∀ l ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)),
        cexp (2 * π * I * (ν * l + conj (ν * l))) = 1} ↦ bianchiFourierMode ν.1
      (bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) ν.1 F) z)
        (F z)) : HasBianchiWhittakerExpansion σ δ k (extend F) fun α ↦
    bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) F 1 0 /
      bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 := by
  have hT : cuspTranslations σ Γ 1 =
      (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))).toAddSubgroup :=
    le_antisymm (cuspTranslations_le_span hK hx) (span_integralLatticeBasis_le hK hx hΓ)
  have hP : IsAddFundamentalDomain (cuspTranslations σ Γ 1)
      (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) :=
    hT ▸ ZSpan.isAddFundamentalDomain' _ _
  refine hF.hasBianchiWhittakerExpansion_of_finrank_eq_two hK hx hΓ hk hδ fun z ↦ ?_
  let m : ℂ → Fin (k + 1) → ℂ := fun ν ↦ bianchiFourierMode ν
    (bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) ν F) z
  have h₀ : m 0 = 0 := by
    simp only [m, bianchiFourierMode, hc.bianchiFourierCoeff_zero hP (coords_snd_pos z), smul_zero]
  let S : Set ℂ := {ν | ∀ l ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)),
    cexp (2 * π * I * (ν * l + conj (ν * l))) = 1}
  let T : Set ℂ := {ν | ν ≠ 0 ∧ ν ∈ S}
  have hind : T.indicator m = S.indicator m := by
    funext ν
    by_cases hS : ν ∈ S
    · by_cases hν : ν = 0
      · rw [Set.indicator_of_notMem (fun h : ν ∈ T ↦ h.1 hν), Set.indicator_of_mem hS, hν, h₀]
      · rw [Set.indicator_of_mem (⟨hν, hS⟩ : ν ∈ T), Set.indicator_of_mem hS]
    · rw [Set.indicator_of_notMem (fun h : ν ∈ T ↦ hS h.2), Set.indicator_of_notMem hS]
  have hS : HasSum (m ∘ ((↑) : S → ℂ)) (F z) :=
    hsum z
  exact hasSum_subtype_iff_indicator.mpr (hind ▸ hasSum_subtype_iff_indicator.mp hS)

end HyperbolicThreeSpace
