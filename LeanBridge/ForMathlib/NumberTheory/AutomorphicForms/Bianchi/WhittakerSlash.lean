import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerHarmonic

/-!
# Upper triangular matrices on Fourier–Bessel expansions

Let `g = (a, b; 0, a⁻¹) ∈ SL(2, ℂ)` be upper triangular. It acts on `ℋ₃` by
`(x, y) ↦ (a²x + ab, |a|²y)` with the automorphy factor `J(g, z) = diag(a⁻¹, conj(a)⁻¹)`, so that
`Sym^k(J(g, z)⁻¹)` is the diagonal matrix `(a^{k-j} conj(a)^j)_j`. For even `k` this phase is
`|a|^k (a² / |a|²)^{k/2 - j}`, which is the change of `(iu)^{k/2 - j}` when the frequency `μ`
becomes `μa²`. Hence the Fourier–Bessel function `y W_k(μ / |μ|, 4π|μ|y) ψ(μx)`
(`bianchiWhittakerFunction`) is mapped by `∣_k g` to `|a|^{k+2} ψ(μab)` times the Fourier–Bessel
function of frequency `μa²` (`bianchiSlash_bianchiWhittakerFunction`), and a function with a
Fourier–Bessel expansion of weight `k` with coefficients `c(α)` (`HasBianchiWhittakerExpansion`) is
mapped to the series `∑_{α ≠ 0} c(α) |a|^{k+2} ψ(μ_α ab) y W_k(…) ψ(μ_α a² x)`, `μ_α = σ(α) / δ`
(`HasBianchiWhittakerExpansion.hasSum_bianchiSlash`).

These are the terms of the Hecke operator `T_𝔭`, `𝔭 = (π)`, on Fourier–Bessel expansions: its
right cosets are represented, for `𝔭 ∤ 𝔑`, by `(1, β; 0, π)`, `β ∈ 𝒪_K / 𝔭`, and `(π, 0; 0, 1)`,
whose `SL(2, ℂ)`-representatives are upper triangular with `a = π^{-1/2}`, `ab = σ(β) / π`, and
`a = π^{1/2}`, `b = 0`; the resulting action of `T_𝔭` on the Fourier–Bessel coefficients is in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerHecke`.

## Main results

* `HyperbolicThreeSpace.bianchiSlash_bianchiWhittakerFunction`: an upper triangular matrix maps a
  Fourier–Bessel function to a multiple of a Fourier–Bessel function.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.hasSum_bianchiSlash`: the image of a
  Fourier–Bessel expansion under an upper triangular matrix.
-/

open Complex Matrix NumberField

open scoped ComplexConjugate MatrixGroups Real

namespace HyperbolicThreeSpace

variable {k : ℕ} {μ : ℂ} {g : SL(2, ℂ)} {p : ℂ × ℝ}

private lemma symPowMatrix_diag (a b : ℂ) : symPowMatrix k !![a, 0; 0, b] =
    diagonal fun i : Fin (k + 1) ↦ a ^ (k - i : ℕ) * b ^ (i : ℕ) := by
  refine eq_of_mulVec_monomialVector fun x ↦ ?_
  rw [symPowMatrix_mulVec_monomialVector]
  ext i
  simp only [monomialVector, mulVec_diagonal, of_apply, cons_val_zero, cons_val_one, zero_mul]
  ring1

lemma mul_apply_one_one_eq_one_of_apply_one_zero (hg : g 1 0 = 0) : g 0 0 * g 1 1 = 1 := by
  have h : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := g.det_coe
  rw [det_fin_two, hg] at h
  simpa using h

lemma inv_automorphyFactor_eq_of_apply_one_zero (hg : g 1 0 = 0) :
    (automorphyFactor g p)⁻¹ = !![g 0 0, 0; 0, conj (g 0 0)] := by
  rw [automorphyFactor_of_apply_one_zero g p hg]
  refine inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply_one_one_eq_one_of_apply_one_zero hg, ← map_mul]

lemma moebius_eq_of_apply_one_zero (hg : g 1 0 = 0) :
    moebius g p = (g 0 0 ^ 2 * p.1 + g 0 0 * g 0 1, ‖g 0 0‖ ^ 2 * p.2) := by
  have h₁ : g 0 0 * g 1 1 = 1 := mul_apply_one_one_eq_one_of_apply_one_zero hg
  have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one h₁
  simp only [moebius, moebiusDenom, hg, zero_mul, zero_add, map_zero, mul_zero, add_zero,
    eq_inv_of_mul_eq_one_right h₁]
  ext
  · simp only
    rw [normSq_inv, map_inv₀]
    field_simp
    rw [one_div, ← inv_def, div_inv_eq_mul, mul_comm]
  · simp only
    rw [normSq_inv, normSq_eq_norm_sq]
    field_simp

private lemma pow_mul_conj_pow_eq {a : ℂ} (ha : a ≠ 0) {n j : ℕ} (hj : j ≤ n + n) :
    a ^ (n + n - j) * conj a ^ j =
      ((‖a‖ ^ (n + n) : ℝ) : ℂ) * (a ^ 2 / ((‖a‖ ^ 2 : ℝ) : ℂ)) ^ ((n : ℤ) - j) := by
  have hn : ((‖a‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  have hc : conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) / a := by
    rw [eq_div_iff ha, mul_comm, mul_conj, normSq_eq_norm_sq]
  have hb : a ^ 2 / ((‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 ha) (by push_cast; exact pow_ne_zero 2 hn)
  rw [hc, zpow_sub₀ hb, zpow_natCast, zpow_natCast, div_pow, div_pow, div_pow, ← pow_mul,
    ← two_mul, pow_mul]
  push_cast
  field_simp
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

/-- **Upper triangular matrices on Fourier–Bessel functions** (LMFDB `mf.bianchi.spaces`): for even
`k`, `μ ≠ 0` and `g = (a, b; 0, a⁻¹) ∈ SL(2, ℂ)`, the slash operator `∣_k g` maps the Fourier–Bessel
function `y W_k(μ / |μ|, 4π|μ|y) ψ(μx)` (`bianchiWhittakerFunction`) to `|a|^{k+2} ψ(μab)` times the
Fourier–Bessel function of frequency `μa²`, where `ψ(z) = e^{2πi(z + z̄)}`. -/
lemma bianchiSlash_bianchiWhittakerFunction (hk : Even k) (hμ : μ ≠ 0) (hg : g 1 0 = 0) :
    bianchiSlash k g (bianchiWhittakerFunction μ k) =
      (((‖g 0 0‖ ^ (k + 2) : ℝ) : ℂ) *
        cexp (2 * π * I * (μ * (g 0 0 * g 0 1) + conj (μ * (g 0 0 * g 0 1))))) •
          bianchiWhittakerFunction (μ * g 0 0 ^ 2) k := by
  rcases hk with ⟨n, rfl⟩
  have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one (mul_apply_one_one_eq_one_of_apply_one_zero hg)
  funext z
  ext j
  rw [bianchiSlash, inv_automorphyFactor_eq_of_apply_one_zero hg, symPowMatrix_diag,
    mulVec_diagonal]
  simp only [bianchiWhittakerFunction, coords_smul, moebius_eq_of_apply_one_zero hg, Pi.smul_apply,
    bianchiWhittakerVector]
  have hn : (n + n) / 2 = n := by
    omega
  have hB : 4 * π * ‖μ‖ * (‖g 0 0‖ ^ 2 * z.coords.2) = 4 * π * ‖μ * g 0 0 ^ 2‖ * z.coords.2 := by
    rw [norm_mul, norm_pow]
    ring1
  have hE : cexp (2 * π * I * (μ * (g 0 0 ^ 2 * z.coords.1 + g 0 0 * g 0 1) +
      conj (μ * (g 0 0 ^ 2 * z.coords.1 + g 0 0 * g 0 1)))) =
      cexp (2 * π * I * (μ * (g 0 0 * g 0 1) + conj (μ * (g 0 0 * g 0 1)))) *
        cexp (2 * π * I * (μ * g 0 0 ^ 2 * z.coords.1 + conj (μ * g 0 0 ^ 2 * z.coords.1))) := by
    rw [← exp_add]
    congr 1
    simp only [map_add, map_mul]
    ring1
  have hμ' : ((‖μ‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hμ)
  have ha' : ((‖g 0 0‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  have hu : μ * g 0 0 ^ 2 / ‖μ * g 0 0 ^ 2‖ = μ / ‖μ‖ * (g 0 0 ^ 2 / ((‖g 0 0‖ ^ 2 : ℝ) : ℂ)) := by
    rw [norm_mul, norm_pow]
    push_cast
    field_simp
  rw [hn, hB, hE, hu, ← mul_assoc I, mul_zpow (I * (μ / ‖μ‖)), pow_mul_conj_pow_eq ha j.is_le]
  push_cast
  ring1

variable {K : Type*} [Field K] [NumberField K] {σ : K →+* ℂ} {δ : ℂ} {c : 𝓞 K → ℂ}
  {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

/-- **Upper triangular matrices on Fourier–Bessel expansions** (LMFDB `mf.bianchi.spaces`,
`mf.bianchi.newform`): for even `k`, `|δ| = √|Δ|` and `g = (a, b; 0, a⁻¹) ∈ SL(2, ℂ)`, if `F` has
the Fourier–Bessel expansion of weight `k` with coefficients `c(α)`, then
`(F ∣_k g)(x, y) = ∑_{α ≠ 0} c(α) |a|^{k+2} ψ(μ_α ab) y W_k(…) ψ(μ_α a² x)`, `μ_α = σ(α) / δ`, the
terms being the Fourier–Bessel functions of the frequencies `μ_α a²` and the series converging
unconditionally at every point. -/
lemma HasBianchiWhittakerExpansion.hasSum_bianchiSlash (hk : Even k) (hδ : ‖δ‖ = √|(discr K : ℝ)|)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c) (hg : g 1 0 = 0)
    (z : HyperbolicThreeSpace) : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦
      (c α * (((‖g 0 0‖ ^ (k + 2) : ℝ) : ℂ) *
        cexp (2 * π * I * (σ α.1 / δ * (g 0 0 * g 0 1) + conj (σ α.1 / δ * (g 0 0 * g 0 1)))))) •
          bianchiWhittakerFunction (σ α.1 / δ * g 0 0 ^ 2) k z) (bianchiSlash k g F z) := by
  have hδ₀ : δ ≠ 0 := norm_ne_zero_iff.mp <| hδ ▸ (Real.sqrt_pos.mpr <| abs_pos.mpr <|
    Int.cast_ne_zero.mpr <| discr_ne_zero K).ne'
  have h : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ symPowMatrix k (automorphyFactor g z.coords)⁻¹ *ᵥ
      bianchiWhittakerTerm σ δ k c (g • z).coords α)
        (symPowMatrix k (automorphyFactor g z.coords)⁻¹ *ᵥ extend F (g • z).coords) :=
    (LinearMap.toContinuousLinearMap (mulVecLin (symPowMatrix k
      (automorphyFactor g z.coords)⁻¹))).hasSum (hc (g • z).coords (coords_snd_pos (g • z)))
  rw [extend_coords] at h
  refine h.congr_fun fun α ↦ ?_
  have hμ : σ α.1 / δ ≠ 0 :=
    div_ne_zero ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr α.2)) hδ₀
  rw [bianchiWhittakerTerm_coords k σ δ c α hδ, mulVec_smul, ← smul_smul]
  exact congrArg (c α • ·) (congrFun (bianchiSlash_bianchiWhittakerFunction hk hμ hg) z).symm

end HyperbolicThreeSpace
