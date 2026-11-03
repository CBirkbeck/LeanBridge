import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HeckeCosetDecomposition
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerCoefficient
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerSlash

/-!
# Hecke operators on Fourier–Bessel coefficients

Let `K` be a quadratic field embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ` (an imaginary quadratic field),
`δ² = Δ`, `k` even, and `F : ℋ₃ → ℂ^{k+1}` with a Fourier–Bessel expansion of weight `k`
(`HasBianchiWhittakerExpansion`) with coefficients `c(α)`. Let `ϖ = p ∈ 𝒪_K`, `p ≠ 0`. For a prime
`𝔭 = (ϖ) ∤ 𝔑`, the right cosets of the Hecke operator `T_𝔭` (`bianchiHeckeTPrime`) are represented
by `(1, β; 0, ϖ)`, `β ∈ 𝒪_K / 𝔭`, and `(ϖ, 0; 0, 1)` (`HilbertModularGroup.heckeUpper`,
`HilbertModularGroup.heckeLower`), acting through their `SL(2, ℂ)`-representatives
`s⁻¹ (1, β; 0, ϖ)` and `s⁻¹ (ϖ, 0; 0, 1)`, `s² = σ(ϖ)`, which are upper triangular. By
`HasBianchiWhittakerExpansion.hasSum_bianchiSlash`, `F ∣_k s⁻¹ (1, β; 0, ϖ)` is the series of the
Fourier–Bessel functions of the frequencies `σ(α) / (δ σ(ϖ))` with coefficients
`|ϖ|^{-(k/2+1)} ψ(σ(αβ) / (δ σ(ϖ))) c(α)`, and `F ∣_k s⁻¹ (ϖ, 0; 0, 1)` that of the frequencies
`σ(ϖα) / δ` with coefficients `|ϖ|^{k/2+1} c(α)`. All these frequencies lie in the lattice
`σ(𝒪_K) / (δ σ(ϖ))`, dual to `σ(ϖ𝒪_K)`, on which Fourier–Bessel series are unique
(`eq_zero_of_hasSum_smul_bianchiWhittakerFunction`). So if
`∑_β F ∣_k s⁻¹ (1, β; 0, ϖ) + F ∣_k s⁻¹ (ϖ, 0; 0, 1) = a F`, comparing the coefficients of the
frequency `σ(ϖα) / (δ σ(ϖ)) = σ(α) / δ`, at which every character value `ψ(σ(αβ) / δ)` is `1`,
gives `a c(α) = n |ϖ|^{-(k/2+1)} c(ϖα) + |ϖ|^{k/2+1} c(α / ϖ)`, `n` being the number of
representatives `β` and `c(α / ϖ) = 0` unless `ϖ ∣ α`
(`HasBianchiWhittakerExpansion.mul_coeff_eq_of_sum_bianchiSlash_eq`); in particular
`a c(1) = n |ϖ|^{-(k/2+1)} c(ϖ)` when `ϖ` is not a unit
(`HasBianchiWhittakerExpansion.mul_coeff_one_eq_of_sum_bianchiSlash_eq`).

By the coset decomposition of `Γ₀(𝔑) diag(1, ϖ) Γ₀(𝔑)` (`coe_bianchiHeckeTPrime_eq_sum`), this
applies to every Bianchi modular form `F` of level `Γ₀(𝔑)` over an imaginary quadratic field of
class number `1` with a Fourier–Bessel expansion (such as every cusp form) and `T_𝔭 F = a F`,
`𝔭 ⊔ 𝔑 = 𝒪_K`, with `n = |𝒪_K / 𝔭|`
(`HasBianchiWhittakerExpansion.mul_coeff_eq_of_bianchiHeckeTPrime`). A function invariant under a
level in odd weight is `0`, as `-1` acts by `(-1)^k` (`IsBianchiSlashInvariant.eq_zero_of_odd`), so
a Bianchi newform (`BianchiNewformOfWeight`), normalised by `c(1) = 1`, has even weight
(`BianchiNewformOfWeight.even`). For a newform whose eigenvalue for the arithmetic Hecke operator
`N(𝔭)^{(k-2)/4} T_𝔭` (`bianchiHeckeTPrimeArith`) is `a_𝔭`, as `n = N(𝔭) = |ϖ|²`
(`HilbertModularForm.natCard_heckeTranslations` and the product formula for the unique, complex,
infinite place), this is the Hecke recursion `a_𝔭 c(α) = c(ϖα) + N(𝔭)^{k/2} c(α / ϖ)`
(`BianchiNewformOfWeight.eigenvalue_mul_coeff_eq`), and in particular **`a_𝔭 = c(𝔭)`** for every
prime `𝔭 ∤ 𝔑`, in every weight, the statement of LMFDB `mf.bianchi.newform`
(`BianchiNewformOfWeight.eigenvalue_eq_coeff`), with `c(𝔭)` the coefficient at the generator `ϖ` of
`𝔭` used by `bianchiHeckeTPrime`.

## Main results

* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.mul_coeff_eq_of_sum_bianchiSlash_eq`: the
  Hecke relation `a c(α) = n |ϖ|^{-(k/2+1)} c(ϖα) + |ϖ|^{k/2+1} c(α / ϖ)`.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.mul_coeff_one_eq_of_sum_bianchiSlash_eq`: its
  case `α = 1`, `a c(1) = n |ϖ|^{-(k/2+1)} c(ϖ)`.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.mul_coeff_eq_of_bianchiHeckeTPrime`: the Hecke
  relation for an eigenform of `T_𝔭`.
* `HyperbolicThreeSpace.IsBianchiSlashInvariant.eq_zero_of_odd`: forms of odd weight vanish.
* `HyperbolicThreeSpace.norm_sq_apply_eq_abs_norm`: `|σ(x)|² = |N(x)|` for an imaginary quadratic
  field.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.even`: newforms have even weight.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.eigenvalue_mul_coeff_eq`: the Hecke recursion
  `a_𝔭 c(α) = c(ϖα) + N(𝔭)^{k/2} c(α / ϖ)` of a newform.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.eigenvalue_eq_coeff`: `a_𝔭 = c(𝔭)` for a newform and
  `𝔭 ∤ 𝔑`.
-/

open Complex Matrix Module NumberField HilbertModularGroup HilbertModularForm

open Submodule (IsPrincipal)

open scoped ComplexConjugate MatrixGroups Real nonZeroDivisors

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {ϖ : Kˣ} {k : ℕ} {w : ℂ} {c : 𝓞 K → ℂ} {p α : 𝓞 K}
  {Γ : Subgroup (GL (Fin 2) (𝓞 K))} {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

variable (σ ϖ) in
lemma coe_slRepresentative_heckeUpper (b : K) : (slRepresentative σ (heckeUpper ϖ b) : SL(2, ℂ)) =
    !![(σ ϖ ^ (2⁻¹ : ℂ))⁻¹, (σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ b; 0, (σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slRepresentative, heckeUpper, det_fin_two]

variable (ϖ) in
lemma coe_slRepresentative_heckeLower :
    (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ, 0; 0, (σ ϖ ^ (2⁻¹ : ℂ))⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slRepresentative, heckeLower, det_fin_two]

private lemma norm_inv_pow_eq (hk : Even k) :
    ‖(w ^ (2⁻¹ : ℂ))⁻¹‖ ^ (k + 2) = (‖w‖ ^ (k / 2 + 1))⁻¹ := by
  rcases hk with ⟨n, rfl⟩
  rw [norm_inv, inv_pow, (by omega : n + n + 2 = 2 * (n + 1)), (by omega : (n + n) / 2 = n),
    pow_mul, ← norm_pow (w ^ (2⁻¹ : ℂ)), cpow_ofNat_inv_pow]

lemma norm_inv_cpow_mul_pow_eq (hk : Even k) (hw : w ≠ 0) :
    ‖(w ^ (2⁻¹ : ℂ))⁻¹ * w‖ ^ (k + 2) = ‖w‖ ^ (k / 2 + 1) := by
  have hs : (w ^ (2⁻¹ : ℂ)) ^ 2 = w := cpow_ofNat_inv_pow _ 2
  have e : ‖(w ^ (2⁻¹ : ℂ))⁻¹ * w‖ ^ 2 = ‖w‖ := by
    rw [← norm_pow, mul_pow, inv_pow, hs, sq w, inv_mul_cancel_left₀ hw]
  rcases hk with ⟨m, rfl⟩
  rw [(by omega : m + m + 2 = 2 * (m + 1)), (by omega : (m + m) / 2 = m), pow_mul, e]

lemma sq_rpow_mul_sq_mul_inv_pow_eq_one (hk : Even k) {t : ℝ} (ht : 0 < t) :
    (t ^ 2) ^ (((k : ℝ) - 2) / 4) * t ^ 2 * (t ^ (k / 2 + 1))⁻¹ = 1 := by
  have e : ((2 : ℕ) : ℝ) * (((k : ℝ) - 2) / 4) + ((2 : ℕ) : ℝ) + -((k / 2 + 1 : ℕ) : ℝ) = 0 := by
    rcases hk with ⟨m, rfl⟩
    rw [(by omega : (m + m) / 2 = m)]
    push_cast
    ring1
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht.le, ← Real.rpow_natCast _ (k / 2 + 1),
    ← Real.rpow_neg ht.le, ← Real.rpow_add ht, ← Real.rpow_add ht, e, Real.rpow_zero]

lemma hasSum_extend_mul_smul {V : Type*} [AddCommMonoid V] [TopologicalSpace V] [Module ℂ V]
    {q : 𝓞 K} (hq : q ≠ 0) (a : ℂ) (G : 𝓞 K → V) {v : V}
    (h : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ (a * c α) • G (q * α)) v) :
    HasSum (fun β : {β : 𝓞 K // β ≠ 0} ↦ (a * Function.extend (q * ·) c 0 β) • G β) v := by
  have hinj : Function.Injective fun α : {α : 𝓞 K // α ≠ 0} ↦
      (⟨q * α, mul_ne_zero hq α.2⟩ : {β : 𝓞 K // β ≠ 0}) :=
    fun α α' h ↦ Subtype.ext <| mul_right_injective₀ hq <| congrArg Subtype.val h
  refine (hinj.hasSum_iff fun β hβ ↦ ?_).mp (h.congr_fun fun α ↦ ?_)
  · rw [Function.extend_apply' _ _ _ fun ⟨α, hα⟩ ↦ hβ ⟨⟨α, fun h₀ ↦ β.2 (by rw [← hα, h₀,
      mul_zero])⟩, Subtype.ext hα⟩, Pi.zero_apply, mul_zero, zero_smul]
  · rw [Function.comp_apply, (mul_right_injective₀ hq).extend_apply]

/-- **Bianchi modular forms of odd weight vanish** (LMFDB `mf.bianchi.weight`): the matrix
`-1 ∈ SL(2, ℂ)` represents `1 ∈ Γ` and acts on `ℂ^{k+1}` by `(-1)^k`, so a function invariant under
`Γ` in odd weight `k` (`IsBianchiSlashInvariant`) is `0`. -/
lemma IsBianchiSlashInvariant.eq_zero_of_odd (hF : IsBianchiSlashInvariant σ Γ k F) (hk : Odd k) :
    F = 0 := by
  have h : bianchiSlash k (-1) F = F := hF 1 (one_mem _) (-1) (-1) (by simp)
  rw [bianchiSlash_neg_one, hk.neg_one_pow, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul ℂ,
    smul_eq_zero] at h
  exact h.resolve_left two_ne_zero

variable [NumberField K] {δ : ℂ} {x : K} {ι : Type*} [Fintype ι] {a : ℂ}

lemma HasBianchiWhittakerExpansion.hasSum_bianchiSlash_heckeLower (hk : Even k)
    (hδ : ‖δ‖ = √|(discr K : ℝ)|) (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c)
    (hϖ : algebraMap (𝓞 K) K p = ϖ) (z : HyperbolicThreeSpace) :
    HasSum (fun γ : {γ : 𝓞 K // γ ≠ 0} ↦ (((‖σ ϖ‖ ^ (k / 2 + 1) : ℝ) : ℂ) *
      Function.extend (p * ·) c 0 γ) • bianchiWhittakerFunction (σ γ.1 / δ) k z)
        (bianchiSlash k (slRepresentative σ (heckeLower ϖ)) F z) := by
  have hp : p ≠ 0 := by
    rintro rfl
    exact ϖ.ne_zero (by rw [← hϖ, map_zero])
  have hσp : σ (p : K) = σ ϖ := congrArg σ hϖ
  have hs : (σ ϖ ^ (2⁻¹ : ℂ)) ^ 2 = σ ϖ := cpow_ofNat_inv_pow _ 2
  have hg : (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    rw [coe_slRepresentative_heckeLower]
    rfl
  have h₀₀ : (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      (σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ := by
    rw [coe_slRepresentative_heckeLower]
    rfl
  have h₀₁ : (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
    rw [coe_slRepresentative_heckeLower]
    rfl
  refine hasSum_extend_mul_smul hp _ (fun γ ↦ bianchiWhittakerFunction (σ γ / δ) k z)
    ((hc.hasSum_bianchiSlash hk hδ hg z).congr_fun fun γ ↦ ?_)
  have e : σ (γ.1 : K) / δ * ((σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ) ^ 2 = σ ((p * γ.1 : 𝓞 K) : K) / δ := by
    rw [mul_pow, inv_pow, hs]
    push_cast
    rw [map_mul, hσp]
    field_simp
  simp only [h₀₀, h₀₁, mul_zero, map_zero, add_zero, exp_zero, mul_one]
  rw [norm_inv_cpow_mul_pow_eq hk ((map_ne_zero σ).mpr ϖ.ne_zero), e, mul_comm]

/-- **The Hecke relation for Fourier–Bessel coefficients** (LMFDB `mf.bianchi.newform`): for a
quadratic field `K` embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ`, `δ² = Δ`, even `k`, `F` with the
Fourier–Bessel expansion of weight `k` with coefficients `c`, `ϖ = p ∈ 𝒪_K` nonzero and elements
`(βᵢ)` of `𝒪_K`, if `∑ᵢ F ∣_k s⁻¹ (1, βᵢ; 0, ϖ) + F ∣_k s⁻¹ (ϖ, 0; 0, 1) = a F`, the matrices acting
through their `SL(2, ℂ)`-representatives (`slRepresentative`), as for an eigenform of the Hecke
operator `T_(ϖ)` with eigenvalue `a`, then for every `α ≠ 0`,
`a c(α) = n |ϖ|^{-(k/2+1)} c(ϖα) + |ϖ|^{k/2+1} c(α / ϖ)`, where `n` is the number of the `βᵢ` and
`c(α / ϖ) = 0` unless `ϖ ∣ α`. -/
lemma HasBianchiWhittakerExpansion.mul_coeff_eq_of_sum_bianchiSlash_eq (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0) (hδ : δ ^ 2 = discr K) (hk : Even k)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c) (hϖ : algebraMap (𝓞 K) K p = ϖ)
    (β : ι → 𝓞 K) (hT : ∑ i, bianchiSlash k (slRepresentative σ (heckeUpper ϖ (β i))) F +
      bianchiSlash k (slRepresentative σ (heckeLower ϖ)) F = a • F) (hα : α ≠ 0) :
    a * c α = Fintype.card ι * ((‖σ ϖ‖ ^ (k / 2 + 1))⁻¹ : ℝ) * c (p * α) +
      ((‖σ ϖ‖ ^ (k / 2 + 1) : ℝ) : ℂ) * Function.extend (p * ·) c 0 α := by
  have hδ' : ‖δ‖ = √|(discr K : ℝ)| := norm_eq_sqrt_of_sq_eq_discr hδ
  have hp : p ≠ 0 := by
    rintro rfl
    exact ϖ.ne_zero (by rw [← hϖ, map_zero])
  have hσp : σ (p : K) = σ ϖ := congrArg σ hϖ
  have hs : (σ ϖ ^ (2⁻¹ : ℂ)) ^ 2 = σ ϖ := cpow_ofNat_inv_pow _ 2
  have he (γ : 𝓞 K) : σ ((p * γ : 𝓞 K) : K) / (δ * σ p) = σ γ / δ := by
    push_cast
    rw [map_mul, hσp]
    field_simp
  have hU (b : 𝓞 K) (z : HyperbolicThreeSpace) : HasSum (fun γ : {γ : 𝓞 K // γ ≠ 0} ↦
      (c γ * ((((‖σ ϖ‖ ^ (k / 2 + 1))⁻¹ : ℝ) : ℂ) *
        cexp (2 * π * I * (σ γ.1 / δ * (σ b / σ ϖ) + conj (σ γ.1 / δ * (σ b / σ ϖ)))))) •
          bianchiWhittakerFunction (σ γ.1 / (δ * σ p)) k z)
      (bianchiSlash k (slRepresentative σ (heckeUpper ϖ b)) F z) := by
    have hg : (slRepresentative σ (heckeUpper ϖ b) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      rw [coe_slRepresentative_heckeUpper]
      rfl
    have h₀₀ : (slRepresentative σ (heckeUpper ϖ b) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
        (σ ϖ ^ (2⁻¹ : ℂ))⁻¹ := by
      rw [coe_slRepresentative_heckeUpper]
      rfl
    have h₀₁ : (slRepresentative σ (heckeUpper ϖ b) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 =
        (σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ b := by
      rw [coe_slRepresentative_heckeUpper]
      rfl
    have e₁ : (σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * ((σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ b) = σ b / σ ϖ := by
      rw [← mul_assoc, ← mul_inv, ← sq, hs, inv_mul_eq_div]
    refine (hc.hasSum_bianchiSlash hk hδ' hg z).congr_fun fun γ ↦ ?_
    have e₂ : σ (γ.1 : K) / δ * (σ ϖ ^ (2⁻¹ : ℂ))⁻¹ ^ 2 = σ γ.1 / (δ * σ p) := by
      rw [inv_pow, hs, hσp, ← div_eq_mul_inv, div_div]
    rw [h₀₀, h₀₁, e₁, e₂, norm_inv_pow_eq hk]
  have hL (z : HyperbolicThreeSpace) : HasSum (fun γ : {γ : 𝓞 K // γ ≠ 0} ↦
      (((‖σ ϖ‖ ^ (k / 2 + 1) : ℝ) : ℂ) *
        Function.extend (p * ·) (Function.extend (p * ·) c 0) 0 γ) •
          bianchiWhittakerFunction (σ γ.1 / (δ * σ p)) k z)
      (bianchiSlash k (slRepresentative σ (heckeLower ϖ)) F z) := by
    refine hasSum_extend_mul_smul hp _ (fun γ ↦ bianchiWhittakerFunction (σ γ / (δ * σ p)) k z)
      ((hc.hasSum_bianchiSlash_heckeLower hk hδ' hϖ z).congr_fun fun γ ↦ ?_)
    simp only [he]
  have hE (z : HyperbolicThreeSpace) : HasSum (fun γ : {γ : 𝓞 K // γ ≠ 0} ↦
      (a * Function.extend (p * ·) c 0 γ) • bianchiWhittakerFunction (σ γ.1 / (δ * σ p)) k z)
      (a • F z) := by
    have h : HasSum (fun γ : {γ : 𝓞 K // γ ≠ 0} ↦ a • bianchiWhittakerTerm σ δ k c z.coords γ)
        (a • F z) := by
      simpa only [extend_coords] using (hc z.coords (coords_snd_pos z)).const_smul a
    refine hasSum_extend_mul_smul hp a (fun γ ↦ bianchiWhittakerFunction (σ γ / (δ * σ p)) k z)
      (h.congr_fun fun γ ↦ ?_)
    simp only [he]
    rw [bianchiWhittakerTerm_coords k σ δ c γ hδ', smul_smul]
  let d : 𝓞 K → ℂ := fun γ ↦ (∑ i, c γ * ((((‖σ ϖ‖ ^ (k / 2 + 1))⁻¹ : ℝ) : ℂ) *
    cexp (2 * π * I * (σ γ / δ * (σ (β i) / σ ϖ) + conj (σ γ / δ * (σ (β i) / σ ϖ)))))) +
      ((‖σ ϖ‖ ^ (k / 2 + 1) : ℝ) : ℂ) * Function.extend (p * ·) (Function.extend (p * ·) c 0) 0 γ -
        a * Function.extend (p * ·) c 0 γ
  have hsum (z : HyperbolicThreeSpace) : HasSum (fun γ : {γ : 𝓞 K // γ ≠ 0} ↦
      d γ • bianchiWhittakerFunction (σ γ.1 / (δ * σ p)) k z) 0 := by
    have hz : ∑ i, bianchiSlash k (slRepresentative σ (heckeUpper ϖ (β i))) F z +
        bianchiSlash k (slRepresentative σ (heckeLower ϖ)) F z - a • F z = 0 := by
      rw [sub_eq_zero, ← Finset.sum_apply, ← Pi.add_apply, hT, Pi.smul_apply]
    refine (hz ▸ ((hasSum_sum fun i _ ↦ hU (β i) z).add (hL z)).sub (hE z)).congr_fun fun γ ↦ ?_
    rw [← Finset.sum_smul, ← add_smul, ← sub_smul]
  have h₀ : d (p * α) = 0 :=
    eq_zero_of_hasSum_smul_bianchiWhittakerFunction hK hx hδ hp hsum (mul_ne_zero hp hα)
  have hψ (b : 𝓞 K) : cexp (2 * π * I * (σ ((p * α : 𝓞 K) : K) / δ * (σ b / σ ϖ) +
      conj (σ ((p * α : 𝓞 K) : K) / δ * (σ b / σ ϖ)))) = 1 := by
    have e : σ ((p * α : 𝓞 K) : K) / δ * (σ b / σ ϖ) = σ ((α * b : 𝓞 K) : K) / δ := by
      push_cast
      rw [map_mul, map_mul, hσp]
      field_simp
    rw [e]
    exact cexp_two_pi_mul_eq_one hK hx hδ (α * b)
  simp only [d, hψ, Finset.sum_const, Finset.card_univ,
    (mul_right_injective₀ hp).extend_apply] at h₀
  linear_combination -h₀

/-- **The Hecke relation at `(1)`** (LMFDB `mf.bianchi.newform`): under the hypotheses of
`HasBianchiWhittakerExpansion.mul_coeff_eq_of_sum_bianchiSlash_eq`, if `ϖ = p` is not a unit, then
`a c(1) = n |ϖ|^{-(k/2+1)} c(ϖ)`, `n` being the number of the `βᵢ`. -/
lemma HasBianchiWhittakerExpansion.mul_coeff_one_eq_of_sum_bianchiSlash_eq (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0) (hδ : δ ^ 2 = discr K) (hk : Even k)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c) (hϖ : algebraMap (𝓞 K) K p = ϖ)
    (hp : ¬IsUnit p) (β : ι → 𝓞 K)
    (hT : ∑ i, bianchiSlash k (slRepresentative σ (heckeUpper ϖ (β i))) F +
      bianchiSlash k (slRepresentative σ (heckeLower ϖ)) F = a • F) :
    a * c 1 = Fintype.card ι * ((‖σ ϖ‖ ^ (k / 2 + 1))⁻¹ : ℝ) * c p := by
  rw [hc.mul_coeff_eq_of_sum_bianchiSlash_eq hK hx hδ hk hϖ β hT one_ne_zero, mul_one,
    Function.extend_apply' _ _ _ fun ⟨γ, hγ⟩ ↦ hp (.of_mul_eq_one γ hγ), Pi.zero_apply,
    mul_zero, add_zero]

variable [IsTotallyComplex K] {𝔑 : Ideal (𝓞 K)}

lemma subsingleton_infinitePlace (hK : finrank ℚ K = 2) : Subsingleton (InfinitePlace K) := by
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    have h : InfinitePlace.nrRealPlaces K + 2 * InfinitePlace.nrComplexPlaces K = finrank ℚ K :=
      InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero_iff.mpr inferInstance, hK] at h
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      nrRealPlaces_eq_zero_iff.mpr inferInstance]
    omega
  exact Fintype.card_le_one_iff_subsingleton.mp hcard.le

variable (x) in
/-- **The absolute value and the norm**: for an imaginary quadratic field `K` embedded in `ℂ` by
`σ`, `|σ(x)|² = |N(x)|` for `x ∈ K`. -/
lemma norm_sq_apply_eq_abs_norm (hK : finrank ℚ K = 2) :
    ‖σ x‖ ^ 2 = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have : Subsingleton (InfinitePlace K) := subsingleton_infinitePlace hK
  have h₁ : ∏ w : InfinitePlace K, w x ^ w.mult = ((|Algebra.norm ℚ x| : ℚ) : ℝ) :=
    InfinitePlace.prod_eq_abs_norm x
  rw [Fintype.prod_eq_single (InfinitePlace.mk σ) fun w hw ↦ absurd (Subsingleton.elim w _) hw,
    IsTotallyComplex.mult_eq, InfinitePlace.apply] at h₁
  exact h₁

variable (σ) in
lemma sq_norm_apply_eq_absNorm (hK : finrank ℚ K = 2) (a : 𝓞 K) :
    ‖σ (a : K)‖ ^ 2 = Ideal.absNorm (Ideal.span {a}) := by
  rw [norm_sq_apply_eq_abs_norm _ hK, ← Algebra.coe_norm_int, Ideal.absNorm_span_singleton]
  simp

section

variable {𝔭 : Ideal (𝓞 K)}

variable (σ) [IsPrincipalIdealRing (𝓞 K)] [NeZero 𝔑]

/-- **The Hecke operator `T_𝔭` on the Fourier–Bessel coefficients of an eigenform** (LMFDB
`mf.bianchi.newform`): for an imaginary quadratic field `K` whose ring of integers is a principal
ideal domain, even `k`, a prime `𝔭 = (ϖ)` of `𝒪_K` with `𝔭 ⊔ 𝔑 = 𝒪_K` and a Bianchi modular form
`F` of weight `k` and level `Γ₀(𝔑)` with Fourier–Bessel coefficients `c` (for the square root
`Δ^{1/2}` of `BianchiNewformOfWeight`) such that `T_𝔭 F = a F` (`bianchiHeckeTPrime`), for every
`α ≠ 0`, `a c(α) = n |ϖ|^{-(k/2+1)} c(ϖα) + |ϖ|^{k/2+1} c(α / ϖ)`, where `n` is the number of
elements of `𝒪_K / 𝔭` and `c(α / ϖ) = 0` unless `ϖ ∣ α`. -/
lemma HasBianchiWhittakerExpansion.mul_coeff_eq_of_bianchiHeckeTPrime (hK : finrank ℚ K = 2)
    (hk : Even k) {G : bianchiModularForms σ 𝔑.gamma0GL k}
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G) c) (h𝔭 : 𝔭 ≠ ⊥)
    (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤) [Fintype (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1)]
    (hT : bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 G = a • G) (hα : α ≠ 0) :
    a * c α = Fintype.card (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) *
      ((‖σ (bianchiIdealGenerator 𝔭 h𝔭)‖ ^ (k / 2 + 1))⁻¹ : ℝ) * c (IsPrincipal.generator 𝔭 * α) +
        ((‖σ (bianchiIdealGenerator 𝔭 h𝔭)‖ ^ (k / 2 + 1) : ℝ) : ℂ) *
          Function.extend (IsPrincipal.generator 𝔭 * ·) c 0 α := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hq (q : HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) :
      (q.out : K) ∈ (1 : Submodule (𝓞 K) K) := by
    simpa only [translationLattice, inv_one, Units.val_one, FractionalIdeal.coe_one] using q.out.2
  choose β hβ using fun q ↦ Submodule.mem_one.mp (hq q)
  refine hc.mul_coeff_eq_of_sum_bianchiSlash_eq hK hx (cpow_ofNat_inv_pow _ 2) hk rfl β ?_ hα
  have h : (bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 G : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
      a • (G : HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
    congrArg Subtype.val hT
  rw [coe_bianchiHeckeTPrime_eq_sum σ k h𝔭 h𝔭p h𝔭𝔑 G, Fintype.sum_option] at h
  rw [← h, add_comm (bianchiSlash k (slRepresentative σ
    (heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 none)) G)]
  refine congrArg (· + _) (Finset.sum_congr rfl fun q _ ↦ ?_)
  have hβ' : ((β q : 𝓞 K) : K) = q.out := hβ q
  rw [hβ']
  rfl

end

variable [IsPrincipalIdealRing (𝓞 K)] [NeZero 𝔑]

/-- **Bianchi newforms have even weight** (LMFDB `mf.bianchi.newform`, `mf.bianchi.weight`): over
an imaginary quadratic field, the weight `k` of a Bianchi newform (`BianchiNewformOfWeight`) is
even, as a form of odd weight vanishes (`IsBianchiSlashInvariant.eq_zero_of_odd`) and the
Fourier–Bessel coefficients of `0` vanish (`HasBianchiWhittakerExpansion.eq_zero`), while a newform
has `c(1) = 1`. -/
lemma BianchiNewformOfWeight.even (G : BianchiNewformOfWeight σ k 𝔑) (hK : finrank ℚ K = 2) :
    Even k := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  refine Nat.not_odd_iff_even.mp fun hk ↦ one_ne_zero <| G.coeff_one.symm.trans <|
    HasBianchiWhittakerExpansion.eq_zero (k := k) hK hx (cpow_ofNat_inv_pow _ 2) ?_ one_ne_zero
  have h : G.toFun = 0 :=
    (IsBianchiModularForm.invariant G.toBianchiModularForm.2).eq_zero_of_odd hk
  simpa only [h, extend_zero] using G.hasWhittakerExpansion

variable (G : BianchiNewformOfWeight σ k 𝔑) (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})

/-- **The Hecke recursion of a newform** (LMFDB `mf.bianchi.newform`): for a Bianchi newform of
weight `k` and level `Γ₀(𝔑)` over an imaginary quadratic field `K` of class number `1`
(`BianchiNewformOfWeight`; `k` is even, `BianchiNewformOfWeight.even`), a prime `𝔭 = (ϖ)` of `𝒪_K`
not dividing the level, `𝔑 ⊄ 𝔭`, and `α ≠ 0`, the eigenvalue `a_𝔭` of the arithmetic Hecke operator
`N(𝔭)^{(k-2)/4} T_𝔭` (`bianchiHeckeTPrimeArith`) satisfies
`a_𝔭 c(α) = c(ϖα) + N(𝔭)^{k/2} c(α / ϖ)`, where `c(α / ϖ) = 0` unless `ϖ ∣ α`: the relation of
`HasBianchiWhittakerExpansion.mul_coeff_eq_of_bianchiHeckeTPrime`, as `𝒪_K / 𝔭` has
`N(𝔭) = |ϖ|²` elements (`HilbertModularForm.natCard_heckeTranslations` and the product formula for
the unique infinite place of `K`). -/
lemma BianchiNewformOfWeight.eigenvalue_mul_coeff_eq (hK : finrank ℚ K = 2) (h𝔭𝔑 : ¬𝔑 ≤ 𝔭.1)
    (hα : α ≠ 0) : G.eigenvalue 𝔭 * G.coeff α = G.coeff (IsPrincipal.generator 𝔭.1 * α) +
      (Ideal.absNorm 𝔭.1 : ℂ) ^ (k / 2) *
        Function.extend (IsPrincipal.generator 𝔭.1 * ·) G.coeff 0 α := by
  have hk : Even k := G.even hK
  have h𝔭𝔑' : 𝔭.1 ⊔ 𝔑 = ⊤ := (𝔭.2.1.isMaximal 𝔭.2.2).out.2 _
    (lt_of_le_not_ge le_sup_left fun h ↦ h𝔭𝔑 (le_sup_right.trans h))
  have hcard : Nat.card (HeckeTranslations (bianchiIdealGenerator 𝔭.1 𝔭.2.2) 1) =
      Ideal.absNorm 𝔭.1 :=
    natCard_heckeTranslations _ 𝔭.1 (spanSingleton_bianchiIdealGenerator 𝔭.1 𝔭.2.2)
  have hN₀ : Ideal.absNorm 𝔭.1 ≠ 0 := (Ideal.absNorm_eq_zero_iff).not.mpr 𝔭.2.2
  have : Finite (HeckeTranslations (bianchiIdealGenerator 𝔭.1 𝔭.2.2) 1) :=
    Nat.finite_of_card_ne_zero (hcard ▸ hN₀)
  let _ : Fintype (HeckeTranslations (bianchiIdealGenerator 𝔭.1 𝔭.2.2) 1) :=
    Fintype.ofFinite _
  have hN : (Ideal.absNorm 𝔭.1 : ℝ) = ‖σ (bianchiIdealGenerator 𝔭.1 𝔭.2.2)‖ ^ 2 := by
    rw [bianchiIdealGenerator, Units.val_mk0, ← RingOfIntegers.coe_eq_algebraMap,
      sq_norm_apply_eq_absNorm σ hK, Ideal.span_singleton_generator]
  have ht : 0 < ‖σ (bianchiIdealGenerator 𝔭.1 𝔭.2.2)‖ :=
    norm_pos_iff.mpr ((map_ne_zero σ).mpr (bianchiIdealGenerator 𝔭.1 𝔭.2.2).ne_zero)
  have hN' : (((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN₀))
      _).ne'
  have hT : bianchiHeckeTPrime σ k 𝔑 𝔭.1 𝔭.2.2 G.toBianchiModularForm =
      ((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * G.eigenvalue 𝔭) •
        G.toBianchiModularForm := by
    rw [mul_smul, ← G.bianchiHeckeTPrimeArith_toBianchiModularForm 𝔭, bianchiHeckeTPrimeArith,
      LinearMap.smul_apply, inv_smul_smul₀ hN']
  have h : (((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * G.eigenvalue 𝔭 *
      G.coeff α = Fintype.card (HeckeTranslations (bianchiIdealGenerator 𝔭.1 𝔭.2.2) 1) *
        ((‖σ (bianchiIdealGenerator 𝔭.1 𝔭.2.2)‖ ^ (k / 2 + 1))⁻¹ : ℝ) *
          G.coeff (IsPrincipal.generator 𝔭.1 * α) +
            ((‖σ (bianchiIdealGenerator 𝔭.1 𝔭.2.2)‖ ^ (k / 2 + 1) : ℝ) : ℂ) *
              Function.extend (IsPrincipal.generator 𝔭.1 * ·) G.coeff 0 α :=
    G.hasWhittakerExpansion.mul_coeff_eq_of_bianchiHeckeTPrime σ hK hk 𝔭.2.2 𝔭.2.1 h𝔭𝔑' hT hα
  rw [Fintype.card_eq_nat_card, hcard] at h
  rcases hk with ⟨n, rfl⟩
  have hfac₁ : (Ideal.absNorm 𝔭.1 : ℝ) ^ ((((n + n : ℕ) : ℝ) - 2) / 4) *
      (Ideal.absNorm 𝔭.1 : ℝ) * (‖σ (bianchiIdealGenerator 𝔭.1 𝔭.2.2)‖ ^ ((n + n) / 2 + 1))⁻¹ =
        1 := by
    rw [hN]
    exact sq_rpow_mul_sq_mul_inv_pow_eq_one ⟨n, rfl⟩ ht
  have hfac₂ : (Ideal.absNorm 𝔭.1 : ℝ) ^ ((((n + n : ℕ) : ℝ) - 2) / 4) *
      ‖σ (bianchiIdealGenerator 𝔭.1 𝔭.2.2)‖ ^ ((n + n) / 2 + 1) =
        (Ideal.absNorm 𝔭.1 : ℝ) ^ ((n + n) / 2) := by
    rw [hN, (by omega : (n + n) / 2 + 1 = n + 1), (by omega : (n + n) / 2 = n),
      ← Real.rpow_natCast _ 2, ← Real.rpow_mul ht.le, ← Real.rpow_natCast _ (n + 1),
      ← Real.rpow_add ht, ← Real.rpow_natCast _ n, ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring1
  have h₁ : (((Ideal.absNorm 𝔭.1 : ℝ) ^ ((((n + n : ℕ) : ℝ) - 2) / 4) : ℝ) : ℂ) *
      (Ideal.absNorm 𝔭.1 : ℂ) *
        (((‖σ (bianchiIdealGenerator 𝔭.1 𝔭.2.2)‖ ^ ((n + n) / 2 + 1))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hfac₁,
      Complex.ofReal_one]
  have h₂ : (((Ideal.absNorm 𝔭.1 : ℝ) ^ ((((n + n : ℕ) : ℝ) - 2) / 4) : ℝ) : ℂ) *
      ((‖σ (bianchiIdealGenerator 𝔭.1 𝔭.2.2)‖ ^ ((n + n) / 2 + 1) : ℝ) : ℂ) =
        (Ideal.absNorm 𝔭.1 : ℂ) ^ ((n + n) / 2) := by
    rw [← Complex.ofReal_mul, hfac₂]
    push_cast
    rfl
  linear_combination (((Ideal.absNorm 𝔭.1 : ℝ) ^ ((((n + n : ℕ) : ℝ) - 2) / 4) : ℝ) : ℂ) * h -
    G.eigenvalue 𝔭 * G.coeff α * mul_inv_cancel₀ hN' +
      G.coeff (IsPrincipal.generator 𝔭.1 * α) * h₁ +
        Function.extend (IsPrincipal.generator 𝔭.1 * ·) G.coeff 0 α * h₂

/-- **The Hecke eigenvalue `a_𝔭` of a newform is its Fourier–Bessel coefficient `c(𝔭)`** (LMFDB
`mf.bianchi.newform`): for a Bianchi newform of weight `k` and level `Γ₀(𝔑)` over an imaginary
quadratic field `K` of class number `1` (`BianchiNewformOfWeight`) and a prime `𝔭 = (ϖ)` of `𝒪_K`
not dividing the level, `𝔑 ⊄ 𝔭`, the eigenvalue `a_𝔭` of the arithmetic Hecke operator `T_𝔭`
(`bianchiHeckeTPrimeArith`) is the coefficient `c(ϖ)` of its Fourier–Bessel expansion, for the
generator `ϖ = IsPrincipal.generator 𝔭` of `bianchiHeckeTPrime`: the case `α = 1` of
`BianchiNewformOfWeight.eigenvalue_mul_coeff_eq`, as `c(1) = 1`. -/
lemma BianchiNewformOfWeight.eigenvalue_eq_coeff (hK : finrank ℚ K = 2) (h𝔭𝔑 : ¬𝔑 ≤ 𝔭.1) :
    G.eigenvalue 𝔭 = G.coeff (IsPrincipal.generator 𝔭.1) := by
  have hp : ¬IsUnit (IsPrincipal.generator 𝔭.1) := fun hu ↦ 𝔭.2.1.ne_top <| by
    rw [← Ideal.span_singleton_generator 𝔭.1, Ideal.span_singleton_eq_top]
    exact hu
  have h : G.eigenvalue 𝔭 * G.coeff 1 = G.coeff (IsPrincipal.generator 𝔭.1 * 1) +
      (Ideal.absNorm 𝔭.1 : ℂ) ^ (k / 2) *
        Function.extend (IsPrincipal.generator 𝔭.1 * ·) G.coeff 0 1 :=
    G.eigenvalue_mul_coeff_eq 𝔭 hK h𝔭𝔑 one_ne_zero
  rwa [G.coeff_one, mul_one, mul_one, Function.extend_apply' _ _ _
    fun ⟨γ, hγ⟩ ↦ hp (.of_mul_eq_one γ hγ), Pi.zero_apply, mul_zero, add_zero] at h

end HyperbolicThreeSpace
