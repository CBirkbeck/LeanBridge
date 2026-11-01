import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.FourierInversion
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.FourierUniqueness

/-!
# The Fourier–Bessel coefficients of Bianchi modular forms

Let `K` be a quadratic field embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ` (an imaginary quadratic field)
and `δ` a square root of its discriminant `Δ`. The Fourier–Bessel expansion of weight `k`
(`HasBianchiWhittakerExpansion`) `F(x, y) = ∑_{0 ≠ α ∈ 𝒪_K} c(α) y W_k(u, 4π|μ|y) ψ(μx)`,
`μ = σ(α) / δ`, determines its coefficients `c(α)`, `α ≠ 0`
(`HasBianchiWhittakerExpansion.eq_zero`, `HasBianchiWhittakerExpansion.coeff_eq`). More generally,
for `0 ≠ p ∈ 𝒪_K`, if `∑_{β ≠ 0} c(β) y W_k(u, 4π|μ|y) ψ(μx)`, `μ = σ(β) / (δ σ(p))`, vanishes
everywhere, then at height `1` its first coordinate is a Fourier series on the torus
`ℂ / σ(p𝒪_K)`: with an integral basis `(e_i)` of `𝒪_K` and `x = ∑ v_i σ(p e_i)`,
`ψ(μx) = e^{2πi ∑ m_i v_i}` for the integers `m_i = Tr(β e_i / √Δ)`
(`exists_intCast_eq_of_sq_eq_discr`), which determine `β`, and a Fourier series on `(ℝ / ℤ)²`
which converges absolutely and vanishes everywhere has zero coefficients
(`UnitAddTorus.eq_zero_of_hasSum_mFourier`); as `W_k(u, t)₀ = (iu)^{k/2} K_{-k/2}(t) ≠ 0` for
`t > 0`, every `c(β)` vanishes (`eq_zero_of_hasSum_smul_bianchiWhittakerFunction`).

So the **Fourier–Bessel coefficients** `c(α)` of a function `F` with such an expansion are well
defined (`bianchiWhittakerCoeff`, `HasBianchiWhittakerExpansion.bianchiWhittakerCoeff_eq`); every
form of `S_k(Γ₀(𝔑))` of weight `k ≥ 1` has an expansion with them
(`hasBianchiWhittakerExpansion_bianchiWhittakerCoeff`), and for a cusp form they are the Fourier
coefficients `c(α) = φ_μ(1)₀ / W_k(u, 4π|μ|)₀` of `F` over the fundamental parallelogram of
`σ(𝒪_K)` (`IsBianchiCuspidal.bianchiWhittakerCoeff_eq`). Hence the normalisation `c(1) = 1` of a
Bianchi newform of weight `k` (`BianchiNewformOfWeight`) is a condition on the form `F` alone: the
coefficients of a newform are those of its form (`BianchiNewformOfWeight.coeff_eq`), whose
coefficient of `(1)` is `1` (`BianchiNewformOfWeight.bianchiWhittakerCoeff_one`), and conversely a
newspace eigenform of weight `k ≥ 1` whose coefficient of `(1)` is `1` is a newform
(`BianchiNewformOfWeight.ofBianchiWhittakerCoeff`).

## Main definitions

* `HyperbolicThreeSpace.bianchiWhittakerCoeff` (LMFDB `mf.bianchi.spaces`, `mf.bianchi.newform`):
  the Fourier–Bessel coefficients `c(α)` of `F`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.ofBianchiWhittakerCoeff` (LMFDB
  `mf.bianchi.newform`): a newspace eigenform with `c(1) = 1` as a newform.

## Main results

* `HyperbolicThreeSpace.eq_zero_of_hasSum_smul_bianchiWhittakerFunction`: a Fourier–Bessel series
  over `σ(𝒪_K) / (δ σ(p))` which vanishes everywhere has zero coefficients.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.eq_zero`: a Fourier–Bessel expansion of `0`
  has zero coefficients.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.coeff_eq`: the coefficients of a
  Fourier–Bessel expansion are unique.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.bianchiWhittakerCoeff_eq`: they are the
  Fourier–Bessel coefficients of `F`.
* `HyperbolicThreeSpace.hasBianchiWhittakerExpansion_bianchiWhittakerCoeff`: every form of
  `S_k(Γ₀(𝔑))` is the sum of its Fourier–Bessel series.
* `HyperbolicThreeSpace.IsBianchiCuspidal.bianchiWhittakerCoeff_eq`: the Fourier–Bessel coefficients
  of a cusp form are its normalised Fourier coefficients.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.coeff_eq`: the coefficients of a newform are those of
  its form.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.bianchiWhittakerCoeff_one`: the form of a newform has
  `c(1) = 1`.
-/

open Complex Module NumberField UnitAddTorus

open scoped ComplexConjugate Real

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ}

variable (σ) [IsTotallyComplex K] in
lemma exists_im_ne_zero_of_isTotallyComplex : ∃ x : K, (σ x).im ≠ 0 := by
  by_contra h
  exact IsTotallyComplex.complexEmbedding_not_isReal σ <| ComplexEmbedding.isReal_iff.mpr <|
    RingHom.ext fun x ↦ conj_eq_iff_im.mpr <| not_not.mp fun hx ↦ h ⟨x, hx⟩

private lemma eq_zero_of_forall_add_conj {ι : Type*} [Fintype ι] (b : Basis ι ℝ ℂ) {ν : ℂ}
    (h : ∀ i, ν * b i + conj (ν * b i) = 0) : ν = 0 := by
  have hz (z : ℂ) : ν * z + conj (ν * z) = 0 := by
    rw [← b.sum_repr z, Finset.mul_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Complex.real_smul, mul_left_comm, map_mul, conj_ofReal, ← mul_add, h i, mul_zero]
  have h₁ : ν * conj ν + conj (ν * conj ν) = 0 := hz (conj ν)
  rw [mul_conj, conj_ofReal, ← two_mul] at h₁
  simpa using h₁

variable [NumberField K] {δ : ℂ} {k : ℕ} {x : K} {f : ℂ × ℝ → Fin (k + 1) → ℂ} {c c' : 𝓞 K → ℂ}
  {α : 𝓞 K}

lemma norm_eq_sqrt_of_sq_eq_discr (hδ : δ ^ 2 = discr K) : ‖δ‖ = √|(discr K : ℝ)| := by
  rw [← Real.sqrt_sq (norm_nonneg δ), ← norm_pow, hδ, norm_intCast]

private lemma integralLatticeBasis_apply_eq (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    integralLatticeBasis σ hK hx i = σ (RingOfIntegers.basis K i) := by
  rw [integralLatticeBasis, Basis.mk_apply, integralBasis_apply]

private lemma bianchiWhittakerVector_zero_ne_zero {u : ℂ} (hu : u ≠ 0) {t : ℝ} (ht : 0 < t) :
    bianchiWhittakerVector k u t 0 ≠ 0 := by
  have h : ((((0 : Fin (k + 1)) : ℕ) : ℂ) - (k : ℂ) / 2) = ((-(k / 2 : ℝ) : ℝ) : ℂ) := by
    push_cast [Fin.val_zero]
    ring1
  rw [bianchiWhittakerVector, h]
  exact mul_ne_zero (zpow_ne_zero _ (mul_ne_zero I_ne_zero hu)) (besselK_ofReal_ne_zero _ ht)

/-- **A vanishing Fourier–Bessel series has zero coefficients** (LMFDB `mf.bianchi.spaces`): for a
quadratic field `K` embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ`, `δ² = Δ` and `0 ≠ p ∈ 𝒪_K`, if
`∑_{β ≠ 0} c(β) y W_k(u, 4π|μ|y) ψ(μx) = 0`, `μ = σ(β) / (δ σ(p))`, on `ℋ₃`
(`bianchiWhittakerFunction`), the series converging unconditionally, then `c(β) = 0` for every
`β ≠ 0`: at height `1` this is an absolutely convergent Fourier series on the torus `ℂ / σ(p𝒪_K)`,
whose frequencies are the `σ(β) / (δ σ(p))`. -/
lemma eq_zero_of_hasSum_smul_bianchiWhittakerFunction (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) {p : 𝓞 K} (hp : p ≠ 0)
    (hc : ∀ z : HyperbolicThreeSpace, HasSum (fun β : {β : 𝓞 K // β ≠ 0} ↦
      c β • bianchiWhittakerFunction (σ β.1 / (δ * σ p)) k z) 0) (hα : α ≠ 0) : c α = 0 := by
  choose m hm using fun (β : {α : 𝓞 K // α ≠ 0}) i ↦
    exists_intCast_eq_of_sq_eq_discr σ hK hx hδ (β.1 * RingOfIntegers.basis K i)
  have hδ₀ : δ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, Int.cast_eq_zero] at hδ
    exact discr_ne_zero K hδ
  have hp₀ : σ (p : K) ≠ 0 := (map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hp)
  have hexp (β : {α : 𝓞 K // α ≠ 0}) (v : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) :
      cexp (2 * π * I * (σ (β.1 : K) / (δ * σ p) *
        (∑ i, (v i : ℂ) * (σ p * σ (RingOfIntegers.basis K i))) +
          conj (σ (β.1 : K) / (δ * σ p) *
            (∑ i, (v i : ℂ) * (σ p * σ (RingOfIntegers.basis K i)))))) =
        mFourier (m β) fun i ↦ (v i : UnitAddCircle) := by
    simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply, ← Complex.exp_sum]
    congr 1
    have h (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
        σ (β.1 : K) / (δ * σ p) * ((v i : ℂ) * (σ p * σ (RingOfIntegers.basis K i))) +
          conj (σ (β.1 : K) / (δ * σ p) * ((v i : ℂ) * (σ p * σ (RingOfIntegers.basis K i)))) =
            (v i : ℂ) * m β i := by
      have e : σ (β.1 : K) / (δ * σ p) * ((v i : ℂ) * (σ p * σ (RingOfIntegers.basis K i))) =
          (v i : ℂ) * (σ ((β.1 * RingOfIntegers.basis K i : 𝓞 K) : K) / δ) := by
        push_cast
        rw [map_mul]
        field_simp
      rw [e, map_mul, conj_ofReal, ← mul_add, hm β i]
    rw [Finset.mul_sum, map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h i]
    push_cast
    ring1
  have hinj : Function.Injective m := by
    intro β β' h
    have hν : (σ (β.1 : K) - σ (β'.1 : K)) / (δ * σ p) * σ p = 0 := by
      refine eq_zero_of_forall_add_conj (integralLatticeBasis σ hK hx) fun i ↦ ?_
      have h₁ : σ ((β.1 * RingOfIntegers.basis K i : 𝓞 K) : K) / δ +
          conj (σ ((β.1 * RingOfIntegers.basis K i : 𝓞 K) : K) / δ) = m β' i := by
        rw [hm β i, h]
      have h₂ : σ ((β'.1 * RingOfIntegers.basis K i : 𝓞 K) : K) / δ +
          conj (σ ((β'.1 * RingOfIntegers.basis K i : 𝓞 K) : K) / δ) = m β' i :=
        hm β' i
      have e : (σ (β.1 : K) - σ (β'.1 : K)) / (δ * σ p) * σ p =
          (σ (β.1 : K) - σ (β'.1 : K)) / δ := by
        field_simp
      rw [integralLatticeBasis_apply_eq, e]
      push_cast at h₁ h₂
      simp only [map_sub, map_mul, map_div₀] at h₁ h₂ ⊢
      linear_combination h₁ - h₂
    exact Subtype.ext <| RingOfIntegers.coe_injective <| σ.injective <| sub_eq_zero.mp <|
      (div_eq_zero_iff.mp ((mul_eq_zero.mp hν).resolve_right hp₀)).resolve_right
        (mul_ne_zero hδ₀ hp₀)
  let w (β : {α : 𝓞 K // α ≠ 0}) : ℂ :=
    bianchiWhittakerVector k (σ (β.1 : K) / (δ * σ p) / ‖σ (β.1 : K) / (δ * σ p)‖)
      (4 * π * ‖σ (β.1 : K) / (δ * σ p)‖ * 1) 0
  let e : (Free.ChooseBasisIndex ℤ (𝓞 K) → ℤ) → ℂ := Function.extend m (fun β ↦ c β * w β) 0
  let z (v : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) : HyperbolicThreeSpace :=
    .mk (WithLp.toLp 2 (∑ i, (v i : ℂ) * (σ p * σ (RingOfIntegers.basis K i)), 1)) one_pos
  have hterm (β : {α : 𝓞 K // α ≠ 0}) (v : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) :
      (c β • bianchiWhittakerFunction (σ β.1 / (δ * σ p)) k (z v)) 0 =
        c β * w β * mFourier (m β) fun i ↦ (v i : UnitAddCircle) := by
    have hco : (z v).coords = (∑ i, (v i : ℂ) * (σ p * σ (RingOfIntegers.basis K i)), 1) :=
      rfl
    rw [← hexp β v]
    simp only [Pi.smul_apply, bianchiWhittakerFunction, hco, ofReal_one]
    ring1
  have hd (v : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) :
      HasSum (fun n ↦ e n * mFourier n fun i ↦ (v i : UnitAddCircle)) 0 := by
    refine (hinj.hasSum_iff fun n hn ↦ ?_).mp ((Pi.hasSum.mp (hc (z v)) 0).congr_fun fun β ↦ ?_)
    · rw [show e n = 0 from Function.extend_apply' _ _ _ hn, zero_mul]
    · rw [Function.comp_apply, show e (m β) = _ from hinj.extend_apply _ _ β, hterm]
  have he : e = 0 := by
    refine eq_zero_of_hasSum_mFourier (by simpa [mFourier] using (hd 0).summable) fun y ↦ ?_
    choose t ht using fun i ↦ QuotientAddGroup.mk_surjective (y i)
    exact (funext ht : (fun i ↦ (t i : UnitAddCircle)) = y) ▸ hd t
  have h₀ : c α * w ⟨α, hα⟩ = 0 := by
    simpa [e, hinj.extend_apply] using congrFun he (m ⟨α, hα⟩)
  have hσ : σ (α : K) / (δ * σ p) ≠ 0 := div_ne_zero
    ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hα)) (mul_ne_zero hδ₀ hp₀)
  refine (mul_eq_zero.mp h₀).resolve_right (bianchiWhittakerVector_zero_ne_zero ?_ ?_)
  · exact div_ne_zero hσ <| ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr hσ
  · exact mul_pos (mul_pos (by positivity) (norm_pos_iff.mpr hσ)) one_pos

/-- **A vanishing Fourier–Bessel expansion has zero coefficients** (LMFDB `mf.bianchi.spaces`): for
a quadratic field `K` embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ` and `δ² = Δ`, if `0` has the
Fourier–Bessel expansion of weight `k` with coefficients `c`, then `c(α) = 0` for every
`α ≠ 0`. -/
lemma HasBianchiWhittakerExpansion.eq_zero (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) (hc : HasBianchiWhittakerExpansion σ δ k 0 c) (hα : α ≠ 0) :
    c α = 0 := by
  refine eq_zero_of_hasSum_smul_bianchiWhittakerFunction (k := k) hK hx hδ one_ne_zero
    (fun z ↦ ?_) hα
  simpa [bianchiWhittakerTerm_coords (hδ := norm_eq_sqrt_of_sq_eq_discr hδ)] using
    hc z.coords (coords_snd_pos z)

lemma bianchiWhittakerTerm_sub (p : ℂ × ℝ) : bianchiWhittakerTerm σ δ k (c - c') p α =
    bianchiWhittakerTerm σ δ k c p α - bianchiWhittakerTerm σ δ k c' p α := by
  simp only [bianchiWhittakerTerm, Pi.sub_apply, sub_mul, sub_smul]

/-- **The coefficients of a Fourier–Bessel expansion are unique** (LMFDB `mf.bianchi.spaces`,
`mf.bianchi.newform`): for a quadratic field `K` embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ` and
`δ² = Δ`, two Fourier–Bessel expansions of weight `k` of the same function have the same
coefficients `c(α)`, `α ≠ 0`. -/
lemma HasBianchiWhittakerExpansion.coeff_eq (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) (hc : HasBianchiWhittakerExpansion σ δ k f c)
    (hc' : HasBianchiWhittakerExpansion σ δ k f c') (hα : α ≠ 0) : c α = c' α :=
  sub_eq_zero.mp <| HasBianchiWhittakerExpansion.eq_zero (c := c - c') hK hx hδ (fun p hp ↦ by
    simpa only [bianchiWhittakerTerm_sub, sub_self, Pi.zero_apply] using
      (hc p hp).sub (hc' p hp)) hα

open scoped Classical in
variable (σ δ k f) in
/-- The **Fourier–Bessel coefficients** `c(α)` (LMFDB `mf.bianchi.spaces`, `mf.bianchi.newform`) of
`f : ℋ₃ → ℂ^{k+1}`, given on `ℂ × ℝ`: the coefficients of a Fourier–Bessel expansion of weight `k`
(`HasBianchiWhittakerExpansion`) `f(x, y) = ∑_{0 ≠ α ∈ 𝒪_K} c(α) y W_k(u, 4π|μ|y) ψ(μx)`,
`μ = σ(α) / δ`, and the junk value `0` if `f` has none. For a quadratic field `K` with
`σ(K) ⊄ ℝ` and `δ² = Δ`, the coefficients `c(α)`, `α ≠ 0`, of every expansion of `f` are these
(`HasBianchiWhittakerExpansion.bianchiWhittakerCoeff_eq`); the expansion does not involve `c(0)`,
which is not determined by `f`. -/
noncomputable def bianchiWhittakerCoeff : 𝓞 K → ℂ :=
  if h : ∃ c, HasBianchiWhittakerExpansion σ δ k f c then h.choose else 0

lemma HasBianchiWhittakerExpansion.hasBianchiWhittakerExpansion_bianchiWhittakerCoeff
    (hc : HasBianchiWhittakerExpansion σ δ k f c) :
    HasBianchiWhittakerExpansion σ δ k f (bianchiWhittakerCoeff σ δ k f) := by
  have h : ∃ c, HasBianchiWhittakerExpansion σ δ k f c := ⟨c, hc⟩
  rw [bianchiWhittakerCoeff, dite_eq_left h]
  exact h.choose_spec

/-- **The coefficients of a Fourier–Bessel expansion are the Fourier–Bessel coefficients** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): for a quadratic field `K` embedded in `ℂ` by `σ` with
`σ(K) ⊄ ℝ` and `δ² = Δ`, if `f` has the Fourier–Bessel expansion of weight `k` with coefficients
`c`, then `c(α)` is the coefficient `bianchiWhittakerCoeff σ δ k f α` of `f` for `α ≠ 0`. -/
lemma HasBianchiWhittakerExpansion.bianchiWhittakerCoeff_eq (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0) (hδ : δ ^ 2 = discr K) (hc : HasBianchiWhittakerExpansion σ δ k f c)
    (hα : α ≠ 0) : bianchiWhittakerCoeff σ δ k f α = c α :=
  hc.hasBianchiWhittakerExpansion_bianchiWhittakerCoeff.coeff_eq hK hx hδ hc hα

variable {Γ : Subgroup (GL (Fin 2) (𝓞 K))} {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

/-- **The Fourier–Bessel coefficients of a cusp form are its normalised Fourier coefficients**
(LMFDB `mf.bianchi.spaces`, `mf.bianchi.newform`): for a quadratic field `K` embedded in `ℂ` by `σ`
with `σ(K) ⊄ ℝ`, `δ² = Δ`, a level `Γ` containing the unipotent matrices `(1, a; 0, 1)`,
`a ∈ 𝒪_K` (such as `Γ₀(𝔑)`), and a Bianchi cusp form `F` of weight `k ≥ 1` and level `Γ`,
`c(α) = φ_μ(1)₀ / W_k(u, 4π|μ|)₀`, `μ = σ(α) / δ`, for `α ≠ 0`, the Fourier coefficient `φ_μ` being
taken over the fundamental parallelogram of `σ(𝒪_K)`. -/
lemma IsBianchiCuspidal.bianchiWhittakerCoeff_eq (hc : IsBianchiCuspidal σ Γ k F)
    (hF : IsBianchiModularForm σ Γ k F) (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hΓ : ∀ a : 𝓞 K, ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, a; 0, 1]) (hk : k ≠ 0)
    (hδ : δ ^ 2 = discr K) (hα : α ≠ 0) : bianchiWhittakerCoeff σ δ k (extend F) α =
      bianchiFourierCoeff (ZSpan.fundamentalDomain (integralLatticeBasis σ hK hx)) (σ α / δ) F 1 0 /
        bianchiWhittakerVector k (σ α / δ / ‖σ α / δ‖) (4 * π * ‖σ α / δ‖) 0 :=
  (hc.hasBianchiWhittakerExpansion hK hx hF hΓ hk hδ).bianchiWhittakerCoeff_eq hK hx hδ hα

variable [IsTotallyComplex K] {𝔑 : Ideal (𝓞 K)}

/-- **Every Bianchi cusp form of level `Γ₀(𝔑)` is the sum of its Fourier–Bessel series** (LMFDB
`mf.bianchi.spaces`, `mf.bianchi.newform`): for an imaginary quadratic field `K` embedded in `ℂ` by
`σ`, every form of `S_k(Γ₀(𝔑))` of weight `k ≥ 1`, in particular every form of the newspace, has
the Fourier–Bessel expansion of weight `k` with its Fourier–Bessel coefficients
(`bianchiWhittakerCoeff`), for the principal square root `Δ^{1/2}` of the discriminant. -/
lemma hasBianchiWhittakerExpansion_bianchiWhittakerCoeff (hK : finrank ℚ K = 2)
    (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k) (hk : k ≠ 0) :
    HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F)
      (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F)) := by
  rcases exists_hasBianchiWhittakerExpansion_of_mem_bianchiCuspForms hK hF hk with ⟨c, hc⟩
  exact hc.hasBianchiWhittakerExpansion_bianchiWhittakerCoeff

namespace BianchiNewformOfWeight

variable [IsPrincipalIdealRing (𝓞 K)] [NeZero 𝔑] (G : BianchiNewformOfWeight σ k 𝔑)

/-- **The coefficients of a newform are those of its form** (LMFDB `mf.bianchi.newform`): over an
imaginary quadratic field, the coefficients `c(α)`, `α ≠ 0`, carried by a Bianchi newform of
weight `k` (`BianchiNewformOfWeight`) are the Fourier–Bessel coefficients of its function `F`
(`bianchiWhittakerCoeff`), so they only depend on `F`. -/
lemma coeff_eq (hK : finrank ℚ K = 2) (hα : α ≠ 0) :
    G.coeff α = bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G.toFun) α := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨y, hy⟩
  exact (G.hasWhittakerExpansion.bianchiWhittakerCoeff_eq hK hy (cpow_ofNat_inv_pow _ 2) hα).symm

/-- **The form of a newform has `c(1) = 1`** (LMFDB `mf.bianchi.newform`): over an imaginary
quadratic field, the normalisation of a Bianchi newform of weight `k` is the condition
`c(1) = 1` on the Fourier–Bessel coefficients (`bianchiWhittakerCoeff`) of its function `F`. -/
lemma bianchiWhittakerCoeff_one (hK : finrank ℚ K = 2) :
    bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G.toFun) 1 = 1 :=
  (G.coeff_eq hK one_ne_zero).symm.trans G.coeff_one

variable (σ 𝔑) in
/-- A **Bianchi newform** of weight `k ≥ 1` (LMFDB `mf.bianchi.newform`) given by its function: over
an imaginary quadratic field `K` of class number `1`, a form `F` of the newspace `S_k(𝔑)^new` which
is an eigenform of every arithmetic Hecke operator `T_𝔭` (`bianchiHeckeTPrimeArith`), with
eigenvalues `a_𝔭`, and whose Fourier–Bessel coefficient (`bianchiWhittakerCoeff`) of `(1)` is `1`,
with its Fourier–Bessel coefficients. With `BianchiNewformOfWeight.bianchiWhittakerCoeff_one`, the
normalisation `c(1) = 1` of `BianchiNewformOfWeight` is exactly this condition on `F`. -/
noncomputable def ofBianchiWhittakerCoeff (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hF : F ∈ bianchiNewSubspace σ k 𝔑) (a : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ)
    (ha : ∀ 𝔭, (bianchiHeckeTPrimeArith σ k 𝔑 𝔭.1 𝔭.2.2
      ⟨F, bianchiNewSubspace_le_bianchiModularForms σ k 𝔑 hF⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) = a 𝔭 • F)
    (h₁ : bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) 1 = 1) :
    BianchiNewformOfWeight σ k 𝔑 where
  toFun := F
  mem_bianchiNewSubspace := hF
  eigenvalue := a
  isEigen := ha
  coeff := bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F)
  hasWhittakerExpansion :=
    hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK (bianchiNewSubspace_le σ k 𝔑 hF) hk
  coeff_one := h₁

end BianchiNewformOfWeight

end HyperbolicThreeSpace
