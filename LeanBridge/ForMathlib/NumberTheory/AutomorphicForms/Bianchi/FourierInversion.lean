import LeanBridge.ForMathlib.Analysis.Fourier.LatticeFourierSeries
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.FourierCoefficient
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Fourier inversion for Bianchi modular forms

Let `K` be a quadratic field embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ` (an imaginary quadratic
field), `Γ` a level containing the unipotent matrices `(1, a; 0, 1)`, `a ∈ 𝒪_K` (such as
`Γ₀(𝔑)`), and `F` a Bianchi modular form of weight `k` and level `Γ`. For every `y > 0` the
function `x ↦ F(x, y)` is real analytic and periodic for the lattice `σ(𝒪_K)`, so it is the sum of
its Fourier series over the dual lattice (`hasSum_fourierSeries_zlattice_of_contDiff`, applied to
each coordinate): `F(x, y) = ∑_ν ψ(νx) φ_ν(y)`, the Fourier coefficients `φ_ν`
(`bianchiFourierCoeff`) being taken over the fundamental parallelogram of `σ(𝒪_K)`
(`IsBianchiModularForm.hasSum_bianchiFourierMode`). For `k ≥ 1` the terms `ν ≠ 0` are
Fourier–Bessel functions, so `F` is its constant term `φ₀(y)` plus a series of Fourier–Bessel
functions (`IsBianchiModularForm.hasSum_ite_bianchiWhittakerFunction`).

Fourier inversion is the hypothesis `hsum` of
`IsBianchiModularForm.hasBianchiWhittakerExpansion_of_isBianchiCuspidal`, which therefore holds
unconditionally: every Bianchi cusp form of weight `k ≥ 1` has the Fourier–Bessel expansion of
weight `k` (`HasBianchiWhittakerExpansion`) with `c(α) = φ_μ(1)₀ / W_k(u, 4π|μ|)₀`, `μ = σ(α) / δ`,
for every square root `δ` of the discriminant (`IsBianchiCuspidal.hasBianchiWhittakerExpansion`),
in particular every form of `S_k(Γ₀(𝔑))`, such as the forms of the newspace `S_k(𝔑)^new`, of an
imaginary quadratic field, with the principal square root `Δ^{1/2}` used by
`BianchiNewformOfWeight` (`exists_hasBianchiWhittakerExpansion_of_mem_bianchiCuspForms`).

## Main results

* `HyperbolicThreeSpace.IsBianchiModularForm.hasSum_bianchiFourierMode`: a Bianchi modular form is
  the sum of its Fourier series over the dual lattice of `σ(𝒪_K)`.
* `HyperbolicThreeSpace.IsBianchiModularForm.hasSum_ite_bianchiWhittakerFunction`: a Bianchi
  modular form of weight `k ≥ 1` is its constant term plus a series of Fourier–Bessel functions.
* `HyperbolicThreeSpace.IsBianchiCuspidal.hasBianchiWhittakerExpansion`: every Bianchi cusp form of
  weight `k ≥ 1` has the Fourier–Bessel expansion.
* `HyperbolicThreeSpace.exists_hasBianchiWhittakerExpansion_of_mem_bianchiCuspForms`: so does every
  form of `S_k(Γ₀(𝔑))` over an imaginary quadratic field, with `δ = Δ^{1/2}`.
-/

open Complex Matrix MeasureTheory Module NumberField Set

open scoped ComplexConjugate ContDiff MatrixGroups Real

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ}

variable (σ) [IsTotallyComplex K] in
private lemma exists_im_ne_zero : ∃ x : K, (σ x).im ≠ 0 := by
  by_contra h
  exact IsTotallyComplex.complexEmbedding_not_isReal σ <| ComplexEmbedding.isReal_iff.mpr <|
    RingHom.ext fun x ↦ conj_eq_iff_im.mpr <| not_not.mp fun hx ↦ h ⟨x, hx⟩

variable [NumberField K] {Γ : Subgroup (GL (Fin 2) (𝓞 K))} {k : ℕ}
  {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {x : K} (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
  (z : HyperbolicThreeSpace)

private lemma contDiff_extend_apply
    (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords) {y : ℝ} (hy : 0 < y)
    (j : Fin (k + 1)) : ContDiff ℝ ∞ fun t : ℂ ↦ extend F (t, y) j :=
  contDiff_iff_contDiffAt.mpr fun t ↦ contDiffAt_pi.mp
    ((hF (.mk (WithLp.toLp 2 (t, y)) hy)).contDiffAt.comp t (f := fun t : ℂ ↦ (t, y))
      (by fun_prop)) j

private lemma span_integralLatticeBasis_le_cuspTranslations
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

/-- **Fourier inversion for Bianchi modular forms** (LMFDB `mf.bianchi.spaces`): let `K` be a
quadratic field embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ`, `Γ` a level containing the unipotent
matrices `(1, a; 0, 1)`, `a ∈ 𝒪_K` (such as `Γ₀(𝔑)`, `exists_mem_gamma0GL`), and `F` a Bianchi
modular form of level `Γ`. Then `F(x, y) = ∑_ν ψ(νx) φ_ν(y)`, the sum running over the frequencies
`ν ∈ ℂ` dual to `σ(𝒪_K)` (`ψ(νl) = 1` for `l ∈ σ(𝒪_K)`, `ψ(z) = e^{2πi(z + z̄)}`) and converging
absolutely, with the Fourier coefficients `φ_ν` (`bianchiFourierCoeff`) over the fundamental
parallelogram of `σ(𝒪_K)`. -/
lemma IsBianchiModularForm.hasSum_bianchiFourierMode (hF : IsBianchiModularForm σ Γ k F)
    (hΓ : ∀ a : 𝓞 K, ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1]) :
    HasSum (fun ν : {ν : ℂ // ∀ l ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)),
      cexp (2 * π * I * (ν * l + conj (ν * l))) = 1} ↦ bianchiFourierMode ν.1
      (bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) ν.1 F) z)
        (F z) := by
  refine Pi.hasSum.mpr fun j ↦ ?_
  have hy : 0 < z.coords.2 := coords_snd_pos z
  have hc (i : Fin (k + 1)) : Continuous fun t : ℂ ↦ extend F (t, z.coords.2) i :=
    (contDiff_extend_apply hF.analyticAt hy i).continuous
  convert hasSum_fourierSeries_zlattice_of_contDiff z.coords.1 (integralLatticeBasis σ hK hx)
    (contDiff_extend_apply hF.analyticAt hy j) (fun l hl t ↦ by
      rw [hF.invariant.extend_add_eq (span_integralLatticeBasis_le_cuspTranslations hK hx hΓ hl)
        (t, z.coords.2)]) using 1
  · funext ν
    simp only [bianchiFourierMode, bianchiFourierCoeff, Pi.smul_apply]
    congr 2
    rw [eval_integral]
    · rfl
    · intro i
      exact ((by fun_prop : Continuous fun t : ℂ ↦ cexp (-(2 * π * I * (ν.1 * t +
        conj (ν.1 * t)))) * extend F (t, z.coords.2) i).continuousOn.integrableOn_compact
          (ZSpan.fundamentalDomain_isBounded _).isCompact_closure).mono_set subset_closure
  · exact (congrFun (extend_coords z F) j).symm

/-- **The Fourier–Bessel expansion of a Bianchi modular form, with its constant term** (LMFDB
`mf.bianchi.spaces`): under the hypotheses of `IsBianchiModularForm.hasSum_bianchiFourierMode`, a
Bianchi modular form `F` of weight `k ≥ 1` is
`F(x, y) = φ₀(y) + ∑_{ν ≠ 0} (φ_ν(1)₀ / W_k(u, 4π|ν|)₀) y W_k(u, 4π|ν|y) ψ(νx)`, `u = ν / |ν|`,
over the frequencies `ν` dual to `σ(𝒪_K)` (`bianchiWhittakerFunction`), the series converging
absolutely: the constant term `φ₀(y)` of the Fourier series and its other terms, which are
Fourier–Bessel functions (`IsBianchiModularForm.fourierMode_eq_smul_bianchiWhittakerFunction`). -/
lemma IsBianchiModularForm.hasSum_ite_bianchiWhittakerFunction (hF : IsBianchiModularForm σ Γ k F)
    (hΓ : ∀ a : 𝓞 K, ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1]) (hk : k ≠ 0) :
    HasSum (fun ν : {ν : ℂ // ∀ l ∈ Submodule.span ℤ (range (integralLatticeBasis σ hK hx)),
      cexp (2 * π * I * (ν * l + conj (ν * l))) = 1} ↦ if ν.1 = 0 then
      bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) 0 F z.coords.2
    else (bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) ν.1 F 1 0 /
      bianchiWhittakerVector k (ν.1 / ‖ν.1‖) (4 * π * ‖ν.1‖) 0) •
        bianchiWhittakerFunction ν.1 k z) (F z) := by
  have : Countable (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (range (integralLatticeBasis σ hK hx))))
  refine (hF.hasSum_bianchiFourierMode hK hx z hΓ).congr_fun fun ν ↦ ?_
  split_ifs with hν
  · simp [bianchiFourierMode, hν]
  · exact (congrFun (hF.fourierMode_eq_smul_bianchiWhittakerFunction _
      (span_integralLatticeBasis_le_cuspTranslations hK hx hΓ) hk hν
      (ZSpan.isAddFundamentalDomain' _ volume) (ZSpan.fundamentalDomain_isBounded _) ν.2) z).symm

/-- **The Fourier–Bessel expansion of a Bianchi cusp form** (LMFDB `mf.bianchi.spaces`,
`mf.bianchi.newform`): let `K` be a quadratic field embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ`, `Γ` a
level containing the unipotent matrices `(1, a; 0, 1)`, `a ∈ 𝒪_K` (such as `Γ₀(𝔑)`), `δ` a square
root of the discriminant `Δ` of `K` and `F` a Bianchi cusp form of weight `k ≥ 1` and level `Γ`.
Then `F` has the Fourier–Bessel expansion of weight `k` (`HasBianchiWhittakerExpansion`)
`F(x, y) = ∑_{0 ≠ α ∈ 𝒪_K} c(α) y W_k(u, 4π|μ|y) ψ(μx)`, `μ = σ(α) / δ`, with
`c(α) = φ_μ(1)₀ / W_k(u, 4π|μ|)₀`, the Fourier coefficients `φ_μ` being taken over the fundamental
parallelogram of `σ(𝒪_K)`: Fourier inversion (`IsBianchiModularForm.hasSum_bianchiFourierMode`)
discharges the hypothesis of
`IsBianchiModularForm.hasBianchiWhittakerExpansion_of_isBianchiCuspidal`. -/
lemma IsBianchiCuspidal.hasBianchiWhittakerExpansion (hc : IsBianchiCuspidal σ Γ k F)
    (hF : IsBianchiModularForm σ Γ k F)
    (hΓ : ∀ a : 𝓞 K, ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1]) (hk : k ≠ 0)
    {δ : ℂ} (hδ : δ ^ 2 = discr K) : HasBianchiWhittakerExpansion σ δ k (extend F) fun α ↦
      bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) F 1 0 /
        bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 :=
  hF.hasBianchiWhittakerExpansion_of_isBianchiCuspidal hc hK hx hΓ hk hδ
    (hF.hasSum_bianchiFourierMode hK hx · hΓ)

/-- **Every Bianchi cusp form of level `Γ₀(𝔑)` has a Fourier–Bessel expansion** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): for an imaginary quadratic field `K` embedded in `ℂ` by
`σ`, every form of `S_k(Γ₀(𝔑))` of weight `k ≥ 1`, in particular every form of the newspace
`S_k(𝔑)^new` (`bianchiNewSubspace_le`), has the Fourier–Bessel expansion of weight `k`
(`HasBianchiWhittakerExpansion`) with the principal square root `Δ^{1/2}` of the discriminant used
by `BianchiNewformOfWeight`. -/
lemma exists_hasBianchiWhittakerExpansion_of_mem_bianchiCuspForms [IsTotallyComplex K]
    (hK₂ : finrank ℚ K = 2) {𝔑 : Ideal (𝓞 K)} (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k)
    (hk : k ≠ 0) :
    ∃ c : 𝓞 K → ℂ, HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) c := by
  rcases exists_im_ne_zero σ with ⟨y, hy⟩
  exact ⟨_, hF.2.hasBianchiWhittakerExpansion hK₂ hy hF.1 (exists_mem_gamma0GL 𝔑) hk
    (cpow_ofNat_inv_pow _ 2)⟩

end HyperbolicThreeSpace
