import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HeckeSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# The Hecke operators on Fourier–Bessel coefficients of Bianchi forms

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `𝔑 ≠ 0` an
ideal of `𝒪_K`. The Hecke operators `T_𝔭`, `𝔭 ∤ 𝔑`, are self-adjoint on the finite dimensional space
`S_k(𝔑)` for the Petersson product. So every form of `S_k(𝔑)` is a sum of eigenforms of `T_𝔭`, and
from the Hecke relation for eigenforms, `T_𝔭` acts on the Fourier–Bessel coefficients of every form
of `S_k(𝔑)` by `c(α) ↦ N(𝔭) |ϖ|^{-(k/2+1)} c(ϖα) + |ϖ|^{k/2+1} c(α / ϖ)`. For a prime `𝔭 = (q) ∣ 𝔑`,
the operator `T_𝔭` is `U_q`, acting by `c(α) ↦ N(𝔭) |ϖ|^{-(k/2+1)} c(ϖα)`. On coefficients, these
operators and the level raisings commute, whence the Hecke operators commute, and preserve the
oldforms. As the adjoint of `U_q` is `W_N U_q W_N`, they all preserve the newspace.

## Main definitions

* `HyperbolicThreeSpace.bianchiCoeffHecke`: the action of the Hecke operators on coefficients.
* `HyperbolicThreeSpace.bianchiPeterssonCore`: the Petersson inner product on a subspace of
  `S_k(𝔑)`.
* `HyperbolicThreeSpace.bianchiHeckeTPrimeCusp`: the Hecke operator `T_𝔭` on `S_k(𝔑)`.

## Main results

* `HyperbolicThreeSpace.eq_of_hasBianchiWhittakerExpansion`: a function is determined by its
  Fourier–Bessel coefficients.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.bianchiLevelRaise`: the coefficients of
  `F ∣ (d, 0; 0, 1)`.
* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.coeff_bianchiUpOperator`: the coefficients of
  `U_d F`.
* `HyperbolicThreeSpace.iSup_iInf_eigenspace_of_le`: the spectral theorem on a subspace of `S_k(𝔑)`.
* `HyperbolicThreeSpace.hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp`,
  `HyperbolicThreeSpace.hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_of_le`,
  `HyperbolicThreeSpace.hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_ite`: the coefficients
  of `T_𝔭 Φ`, for `𝔭 ∤ 𝔑`, for `𝔭 ∣ 𝔑`, and in general.
* `HyperbolicThreeSpace.coe_bianchiHeckeTPrime_eq_bianchiUpOperator`: `T_𝔭` is `U_q` for
  `𝔭 = (q) ∣ 𝔑`.
* `HyperbolicThreeSpace.commute_bianchiHeckeTPrimeCusp`: the Hecke operators commute.
* `HyperbolicThreeSpace.bianchiHeckeTPrimeCusp_mem_bianchiOldforms_of_coe_eq`,
  `HyperbolicThreeSpace.bianchiHeckeTPrimeCusp_mem_bianchiOldforms`: they preserve the oldforms.
* `HyperbolicThreeSpace.bianchiGLSlash_frickeMatrix_bianchiUpOperator`,
  `HyperbolicThreeSpace.bianchiPetersson_bianchiUpOperator`: the adjoint of `U_q` is `W_N U_q W_N`.
* `HyperbolicThreeSpace.bianchiHeckeTPrimeCusp_mem_bianchiNewSubspace`: the Hecke operators preserve
  the newspace.
-/

open Complex Ideal LinearMap Matrix MeasureTheory Module NumberField HilbertModularGroup
  HilbertModularForm

open Ideal renaming Quotient.mk_out → quotientMk_out

open Submodule (IsPrincipal)

open scoped ComplexConjugate MatrixGroups nonZeroDivisors Real

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {δ : ℂ} {x : K} {k : ℕ} {𝔑 𝔭 𝔮 : Ideal (𝓞 K)}
  {c c' : 𝓞 K → ℂ} {F G : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {p q α : 𝓞 K} {d N : (𝓞 K)⁰}

variable (σ k) in
/-- The action on Fourier–Bessel coefficients of the Hecke operators of `ϖ`, with parameters `n`
and `e`: `a(α) ↦ n |σ(ϖ)|^{-(k/2+1)} a(ϖα) + e |σ(ϖ)|^{k/2+1} a(α / ϖ)`, with `a(α / ϖ) = 0` unless
`ϖ ∣ α`. Here `n = N((ϖ))`, and `e = 1` for `ϖ` prime to the level, `e = 0` otherwise; the
parameters `n = 0` and `e = 1` give the action of the level raising `F ↦ F ∣ (ϖ, 0; 0, 1)`. -/
noncomputable def bianchiCoeffHecke (ϖ : 𝓞 K) (n e : ℂ) (a : 𝓞 K → ℂ) : 𝓞 K → ℂ :=
  fun α ↦ n * ((‖σ ϖ‖ ^ (k / 2 + 1))⁻¹ : ℝ) * a (ϖ * α) +
    e * ((‖σ ϖ‖ ^ (k / 2 + 1) : ℝ) : ℂ) * Function.extend (ϖ * ·) a 0 α

lemma extend_mul_apply (hp : p ≠ 0) (β : 𝓞 K) : Function.extend (p * ·) c 0 (p * β) = c β :=
  (mul_right_injective₀ hp).extend_apply c 0 β

lemma extend_mul_of_not_dvd (h : ¬p ∣ α) : Function.extend (p * ·) c 0 α = 0 :=
  Function.extend_apply' _ _ _ fun ⟨β, hβ⟩ ↦ h ⟨β, hβ.symm⟩

lemma extend_mul_mul_of_isCoprime (hq : q ≠ 0) (h : IsCoprime q p) :
    Function.extend (q * ·) c 0 (p * α) = Function.extend (q * ·) (fun β ↦ c (p * β)) 0 α := by
  by_cases hd : q ∣ α
  · rcases hd with ⟨β, rfl⟩
    rw [mul_left_comm, extend_mul_apply hq, extend_mul_apply hq]
  · rw [extend_mul_of_not_dvd hd, extend_mul_of_not_dvd fun h' ↦ hd (h.dvd_of_dvd_mul_left h')]

lemma extend_mul_extend_mul_comm (hp : p ≠ 0) (hq : q ≠ 0) (h : IsCoprime p q) :
    Function.extend (p * ·) (Function.extend (q * ·) c 0) 0 α =
      Function.extend (q * ·) (Function.extend (p * ·) c 0) 0 α := by
  by_cases hd : p ∣ α
  · rcases hd with ⟨β, rfl⟩
    rw [extend_mul_apply hp, extend_mul_mul_of_isCoprime hq h.symm]
    simp only [extend_mul_apply hp]
  · rw [extend_mul_of_not_dvd hd]
    by_cases hd' : q ∣ α
    · rcases hd' with ⟨γ, rfl⟩
      rw [extend_mul_apply hq, extend_mul_of_not_dvd fun h' ↦ hd (h'.mul_left q)]
    · rw [extend_mul_of_not_dvd hd']

lemma extend_mul_add_mul (hp : p ≠ 0) (a b : ℂ) (f g : 𝓞 K → ℂ) :
    Function.extend (p * ·) (fun β ↦ a * f β + b * g β) 0 α = a * Function.extend (p * ·) f 0 α +
      b * Function.extend (p * ·) g 0 α := by
  by_cases hd : p ∣ α
  · rcases hd with ⟨β, rfl⟩
    simp only [extend_mul_apply hp]
  · simp only [extend_mul_of_not_dvd hd, mul_zero, add_zero]

lemma extend_mul_mul_mul (hp : p ≠ 0) (hq : q ≠ 0) :
    Function.extend (p * ·) (Function.extend (q * ·) c 0) 0 α =
      Function.extend (p * q * ·) c 0 α := by
  by_cases hd : p * q ∣ α
  · rcases hd with ⟨β, rfl⟩
    rw [mul_assoc, extend_mul_apply hp, extend_mul_apply hq, ← mul_assoc,
      extend_mul_apply (mul_ne_zero hp hq)]
  · rw [extend_mul_of_not_dvd hd]
    by_cases hd' : p ∣ α
    · rcases hd' with ⟨γ, rfl⟩
      rw [extend_mul_apply hp, extend_mul_of_not_dvd fun h' ↦ hd (mul_dvd_mul_left p h')]
    · rw [extend_mul_of_not_dvd hd']

lemma extend_mul_congr (hp : p ≠ 0) (h : ∀ α, α ≠ 0 → c α = c' α) (hα : α ≠ 0) :
    Function.extend (p * ·) c 0 α = Function.extend (p * ·) c' 0 α := by
  by_cases hd : p ∣ α
  · rcases hd with ⟨β, rfl⟩
    rw [extend_mul_apply hp, extend_mul_apply hp, h _ (right_ne_zero_of_mul hα)]
  · rw [extend_mul_of_not_dvd hd, extend_mul_of_not_dvd hd]

lemma bianchiCoeffHecke_congr (hp : p ≠ 0) (n e : ℂ) (h : ∀ α, α ≠ 0 → c α = c' α) (hα : α ≠ 0) :
    bianchiCoeffHecke σ k p n e c α = bianchiCoeffHecke σ k p n e c' α := by
  rw [bianchiCoeffHecke, bianchiCoeffHecke, h _ (mul_ne_zero hp hα), extend_mul_congr hp h hα]

lemma bianchiCoeffHecke_add (hp : p ≠ 0) (n e : ℂ) : bianchiCoeffHecke σ k p n e (c + c') =
    bianchiCoeffHecke σ k p n e c + bianchiCoeffHecke σ k p n e c' := by
  ext α
  have h : Function.extend (p * ·) (c + c') 0 α = Function.extend (p * ·) c 0 α +
      Function.extend (p * ·) c' 0 α := by
    have e : c + c' = fun β ↦ 1 * c β + 1 * c' β := by
      simp only [one_mul]
      rfl
    rw [e, extend_mul_add_mul hp, one_mul, one_mul]
  simp only [bianchiCoeffHecke, Pi.add_apply, h]
  ring1

lemma bianchiCoeffHecke_smul (hp : p ≠ 0) (a n e : ℂ) :
    bianchiCoeffHecke σ k p n e (a • c) = a • bianchiCoeffHecke σ k p n e c := by
  ext α
  have h : Function.extend (p * ·) (a • c) 0 α = a * Function.extend (p * ·) c 0 α := by
    have e : a • c = fun β ↦ a * c β + 0 * c β := by
      simp only [zero_mul, add_zero]
      rfl
    rw [e, extend_mul_add_mul hp, zero_mul, add_zero]
  simp only [bianchiCoeffHecke, Pi.smul_apply, h]
  ring1

lemma bianchiCoeffHecke_comm (hp : p ≠ 0) (hq : q ≠ 0) (h : IsCoprime p q) (n e m f : ℂ) :
    bianchiCoeffHecke σ k p n e (bianchiCoeffHecke σ k q m f c) =
      bianchiCoeffHecke σ k q m f (bianchiCoeffHecke σ k p n e c) := by
  ext α
  have e₁ : bianchiCoeffHecke σ k q m f c = fun β ↦
      (m * ((‖σ q‖ ^ (k / 2 + 1))⁻¹ : ℝ)) * c (q * β) +
        (f * ((‖σ q‖ ^ (k / 2 + 1) : ℝ) : ℂ)) * Function.extend (q * ·) c 0 β :=
    rfl
  have e₂ : bianchiCoeffHecke σ k p n e c = fun β ↦
      (n * ((‖σ p‖ ^ (k / 2 + 1))⁻¹ : ℝ)) * c (p * β) +
        (e * ((‖σ p‖ ^ (k / 2 + 1) : ℝ) : ℂ)) * Function.extend (p * ·) c 0 β :=
    rfl
  simp only [bianchiCoeffHecke]
  rw [e₁, e₂, extend_mul_add_mul hp, extend_mul_add_mul hq, extend_mul_mul_of_isCoprime hq h.symm,
    extend_mul_mul_of_isCoprime hp h, extend_mul_extend_mul_comm hp hq h, mul_left_comm p q]
  ring1

lemma extend_mul_mul_mul_cancel (hp : p ≠ 0) (hq : q ≠ 0) :
    Function.extend (p * q * ·) c 0 (p * α) = Function.extend (q * ·) c 0 α := by
  by_cases hd : q ∣ α
  · rcases hd with ⟨β, rfl⟩
    rw [← mul_assoc, extend_mul_apply (mul_ne_zero hp hq), extend_mul_apply hq]
  · rw [extend_mul_of_not_dvd hd, extend_mul_of_not_dvd]
    exact fun h ↦ hd ((mul_dvd_mul_iff_left hp).mp h)

lemma norm_coe_mul_pow (m : ℕ) :
    ‖σ ((p * q : 𝓞 K) : K)‖ ^ m = ‖σ (p : K)‖ ^ m * ‖σ (q : K)‖ ^ m := by
  push_cast
  rw [map_mul, norm_mul, mul_pow]

lemma bianchiCoeffHecke_bianchiCoeffHecke_of_dvd (hp : p ≠ 0) (hq : q ≠ 0) (n : ℂ) :
    bianchiCoeffHecke σ k p n 0 (bianchiCoeffHecke σ k (p * q) 0 1 c) α =
      n * bianchiCoeffHecke σ k q 0 1 c α := by
  have hX : ((‖σ (p : K)‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
    ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hp)))
  simp only [bianchiCoeffHecke, zero_mul, zero_add, add_zero]
  rw [extend_mul_mul_mul_cancel hp hq, norm_coe_mul_pow]
  push_cast
  field_simp

lemma bianchiCoeffHecke_sub_bianchiCoeffHecke (hd : q ≠ 0) (hp : p ≠ 0) (n : ℂ) :
    bianchiCoeffHecke σ k q 0 1 (bianchiCoeffHecke σ k p n 1 c) α -
      bianchiCoeffHecke σ k (q * p) 0 1 c α =
        bianchiCoeffHecke σ k q 0 1 (bianchiCoeffHecke σ k p n 0 c) α := by
  have e₁ : bianchiCoeffHecke σ k p n 1 c = fun β ↦
      (n * ((‖σ p‖ ^ (k / 2 + 1))⁻¹ : ℝ)) * c (p * β) +
        (1 * ((‖σ p‖ ^ (k / 2 + 1) : ℝ) : ℂ)) * Function.extend (p * ·) c 0 β :=
    rfl
  have e₂ : bianchiCoeffHecke σ k p n 0 c = fun β ↦
      (n * ((‖σ p‖ ^ (k / 2 + 1))⁻¹ : ℝ)) * c (p * β) +
        (0 * ((‖σ p‖ ^ (k / 2 + 1) : ℝ) : ℂ)) * Function.extend (p * ·) c 0 β :=
    rfl
  simp only [bianchiCoeffHecke]
  rw [e₁, e₂, extend_mul_add_mul hd, extend_mul_add_mul hd, extend_mul_mul_mul hd hp,
    norm_coe_mul_pow]
  push_cast
  ring1

lemma bianchiLevelRaise_mem_bianchiOldforms {𝔐 : Ideal (𝓞 K)} (h𝔐 : 𝔑 < 𝔐)
    (hle : 𝔑 ≤ Ideal.span {(d : 𝓞 K)} * 𝔐) (hG : G ∈ bianchiCuspForms σ 𝔐.gamma0GL k) :
    bianchiLevelRaise σ k d G ∈ bianchiOldforms σ k 𝔑 := by
  refine Submodule.subset_span ⟨𝔐, h𝔐, d, nonZeroDivisors.ne_zero d.2, hle, G, hG, ?_⟩
  rw [bianchiLevelRaise, bianchiGLSlash, rowScale_eq_heckeLower]
  rfl

lemma bianchiSlash_rowScale_eq_bianchiLevelRaise (h : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0) :
    bianchiSlash k (slRepresentative σ (GeneralLinearGroup.rowScale 0
      (Units.mk0 (algebraMap (𝓞 K) K (d : 𝓞 K)) h))) G = bianchiLevelRaise σ k d G := by
  rw [bianchiLevelRaise, bianchiGLSlash, rowScale_eq_heckeLower]
  rfl

lemma glLower_mul_glLower (a b : 𝓞 K) : glLower a * glLower b = glLower (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_glLower]

lemma glSlash_glLower_congr (hk : Even k) {M : (𝓞 K)⁰}
    (hH : ∀ δ ∈ (Ideal.span {(M : 𝓞 K)}).gamma0GL, glSlash σ k δ F = F) {a b : 𝓞 K}
    (hd : (M : 𝓞 K) ∣ b - a) : glSlash σ k (glLower b) F = glSlash σ k (glLower a) F := by
  have e : glLower b = glLower (b - a) * glLower a := by
    rw [glLower_mul_glLower, sub_add_cancel]
  rw [e, glSlash_mul hk, hH _ (glLower_mem_gamma0GL_iff.mpr hd)]

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma le_span_mul_mul_of_prime {𝔐 : Ideal (𝓞 K)} {δ₀ : 𝓞 K} (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime)
    (hle : 𝔑 ≤ Ideal.span {δ₀} * 𝔐) (h𝔑𝔭 : 𝔑 ≤ 𝔭) (hδ : ¬IsPrincipal.generator 𝔭 ∣ δ₀)
    (h𝔐 : ¬𝔐 ≤ 𝔭) : 𝔑 ≤ Ideal.span {δ₀ * IsPrincipal.generator 𝔭} * 𝔐 := by
  have hp : Prime (IsPrincipal.generator 𝔭) := prime_generator h𝔭 h𝔭p
  rcases (⟨(IsPrincipalIdealRing.principal 𝔐).principal⟩ : Nonempty (∃ M, 𝔐 = Ideal.span {M})) with
    ⟨M, rfl⟩
  have hM : ¬IsPrincipal.generator 𝔭 ∣ M := fun h ↦ h𝔐 <| by
    conv_rhs => rw [← Ideal.span_singleton_generator 𝔭]
    exact Ideal.span_singleton_le_span_singleton.mpr h
  rw [Ideal.span_singleton_mul_span_singleton] at hle ⊢
  intro n hn
  rcases Ideal.mem_span_singleton.mp (hle hn) with ⟨e, rfl⟩
  have h₃ : IsPrincipal.generator 𝔭 ∣ δ₀ * M * e :=
    (IsPrincipal.mem_iff_generator_dvd 𝔭).mp (h𝔑𝔭 hn)
  rcases hp.dvd_or_dvd h₃ with h₄ | h₄
  · exact absurd (hp.dvd_or_dvd h₄) (by simp only [hδ, hM, or_self, not_false_eq_true])
  · rcases h₄ with ⟨e', rfl⟩
    exact Ideal.mem_span_singleton.mpr ⟨e', by ring1⟩

variable [NumberField K]

lemma natCast_card_residue :
    (Fintype.card (𝓞 K ⧸ Ideal.span {(d : 𝓞 K)}) : ℂ) = Ideal.absNorm (Ideal.span {(d : 𝓞 K)}) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

lemma HasBianchiWhittakerExpansion.congr {f : ℂ × ℝ → Fin (k + 1) → ℂ}
    (h : HasBianchiWhittakerExpansion σ δ k f c) (hcc : ∀ α, α ≠ 0 → c α = c' α) :
    HasBianchiWhittakerExpansion σ δ k f c' :=
  fun p hp ↦ (h p hp).congr_fun fun α ↦ by
    simp only [bianchiWhittakerTerm, hcc α.1 α.2]

/-- **A function is determined by its Fourier–Bessel coefficients.** -/
lemma eq_of_hasBianchiWhittakerExpansion (h : HasBianchiWhittakerExpansion σ δ k (extend F) c)
    (h' : HasBianchiWhittakerExpansion σ δ k (extend G) c') (hcc : ∀ α, α ≠ 0 → c α = c' α) :
    F = G := by
  funext z
  have h₁ : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ bianchiWhittakerTerm σ δ k c z.coords α)
      (extend F z.coords) := h z.coords (coords_snd_pos z)
  have h₂ : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ bianchiWhittakerTerm σ δ k c z.coords α)
      (extend G z.coords) := h'.congr (fun α hα ↦ (hcc α hα).symm) z.coords (coords_snd_pos z)
  rw [extend_coords] at h₁ h₂
  exact h₁.unique h₂

lemma hasBianchiWhittakerExpansion_of_forall (hδ : ‖δ‖ = √|(discr K : ℝ)|)
    (h : ∀ z, HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦
      c α • bianchiWhittakerFunction (σ α.1 / δ) k z) (F z)) :
    HasBianchiWhittakerExpansion σ δ k (extend F) c := by
  intro p hp
  have e : coords (.mk (WithLp.toLp 2 p) hp) = p := rfl
  rw [← e, extend_coords]
  simp only [bianchiWhittakerTerm_coords k σ δ c _ hδ]
  exact h _

/-- **The Fourier–Bessel coefficients of the level raising** `F ∣ (d, 0; 0, 1)`: if `F` has the
coefficients `c`, then `F ∣ (d, 0; 0, 1)` has the coefficients `|d|^{k/2+1} c(α / d)`, where
`c(α / d) = 0` unless `d ∣ α`. -/
lemma HasBianchiWhittakerExpansion.bianchiLevelRaise (hk : Even k) (hδ : ‖δ‖ = √|(discr K : ℝ)|)
    (h : HasBianchiWhittakerExpansion σ δ k (extend F) c) :
    HasBianchiWhittakerExpansion σ δ k (extend (bianchiLevelRaise σ k d F))
      (bianchiCoeffHecke σ k d 0 1 c) :=
  hasBianchiWhittakerExpansion_of_forall hδ fun z ↦
    (h.hasSum_bianchiSlash_heckeLower hk hδ rfl z).congr_fun fun β ↦ by
      simp only [bianchiCoeffHecke, coe_bianchiUnit, zero_mul, one_mul, zero_add]

open scoped Classical in
/-- **The Fourier–Bessel coefficients of `U_d F`**, in terms of those of `F`. -/
lemma HasBianchiWhittakerExpansion.coeff_bianchiUpOperator (hK : finrank ℚ K = 2)
    (hx : (σ x).im ≠ 0) (hδ : δ ^ 2 = discr K) (hk : Even k) {e : 𝓞 K → ℂ}
    (h : HasBianchiWhittakerExpansion σ δ k (extend F) c)
    (he : HasBianchiWhittakerExpansion σ δ k (extend (bianchiUpOperator σ k d F)) e) (hα : α ≠ 0) :
    e α = bianchiCoeffHecke σ k d (Fintype.card (𝓞 K ⧸ Ideal.span {(d : 𝓞 K)})) 0 c α := by
  have hd₀ : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hu : σ ((d : 𝓞 K) : K) ≠ 0 :=
    (map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hd₀)
  have hX : ((‖σ ((d : 𝓞 K) : K)‖ ^ (k / 2 + 1) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hu))
  have hn : (Fintype.card (𝓞 K ⧸ Ideal.span {(d : 𝓞 K)}) : ℂ) ≠ 0 := card_residue_ne_zero d
  have h₁ : HasBianchiWhittakerExpansion σ δ k (extend (F - bianchiPrimeFilter σ k d F))
      (c - fun α ↦ if (d : 𝓞 K) ∣ α then 0 else c α) := h.sub (h.primeFilter hK hx hδ)
  rw [bianchiPrimeFilter, sub_sub_cancel, bianchiPeriodAverage_eq hk] at h₁
  have h₂ : HasBianchiWhittakerExpansion σ δ k
      (extend ((Fintype.card (𝓞 K ⧸ Ideal.span {(d : 𝓞 K)}) : ℂ)⁻¹ •
        HyperbolicThreeSpace.bianchiLevelRaise σ k d (bianchiUpOperator σ k d F)))
      ((Fintype.card (𝓞 K ⧸ Ideal.span {(d : 𝓞 K)}) : ℂ)⁻¹ • bianchiCoeffHecke σ k d 0 1 e) :=
    (he.bianchiLevelRaise hk (norm_eq_sqrt_of_sq_eq_discr hδ)).smul _
  have h₃ : (c - fun α ↦ if (d : 𝓞 K) ∣ α then 0 else c α) (d * α) =
      ((Fintype.card (𝓞 K ⧸ Ideal.span {(d : 𝓞 K)}) : ℂ)⁻¹ • bianchiCoeffHecke σ k d 0 1 e)
        (d * α) := h₁.coeff_eq hK hx hδ h₂ (mul_ne_zero hd₀ hα)
  simp only [Pi.sub_apply, dvd_mul_right, ite_true, sub_zero, Pi.smul_apply, smul_eq_mul,
    bianchiCoeffHecke, zero_mul, zero_add, extend_mul_apply hd₀] at h₃
  simp only [bianchiCoeffHecke, zero_mul, add_zero, h₃]
  push_cast
  field_simp

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma isCoprime_generator (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) (h𝔮 : 𝔮 ≠ ⊥) (h𝔮p : 𝔮.IsPrime)
    (hne : 𝔭 ≠ 𝔮) : IsCoprime (IsPrincipal.generator 𝔭) (IsPrincipal.generator 𝔮) := by
  refine (prime_generator h𝔭 h𝔭p).coprime_iff_not_dvd.mpr fun hd ↦ hne ?_
  have hle : 𝔮 ≤ 𝔭 := by
    rw [← Ideal.span_singleton_generator 𝔭, ← Ideal.span_singleton_generator 𝔮]
    exact Ideal.span_singleton_le_span_singleton.mpr hd
  exact ((h𝔮p.isMaximal h𝔮).eq_of_le h𝔭p.ne_top hle).symm

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)]

variable (σ) in
/-- **The Petersson inner product on a subspace `E` of `S_k(𝔑)`**, for `K` imaginary quadratic of
class number `1` and `k ≥ 1`: `inner x y = bianchiPetersson σ k 𝔑 y x`, conjugate linear in `x` as
in Mathlib. -/
noncomputable abbrev bianchiPeterssonCore (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔑 : 𝔑 ≠ ⊥)
    {E : Submodule ℂ (HyperbolicThreeSpace → Fin (k + 1) → ℂ)}
    (hE : E ≤ bianchiCuspForms σ 𝔑.gamma0GL k) : InnerProductSpace.Core ℂ E where
  inner x y := bianchiPetersson σ k 𝔑 y x
  conj_inner_symm x y := conj_bianchiPetersson hK ((isBianchiSlashInvariant_iff_mem 𝔑).mp
    (hE x.2).1.invariant) ((isBianchiSlashInvariant_iff_mem 𝔑).mp (hE y.2).1.invariant)
  re_inner_nonneg x := by
    rcases bianchiPetersson_self_eq_ofReal (σ := σ) (𝔑 := 𝔑) hK
      ((isBianchiSlashInvariant_iff_mem 𝔑).mp (hE x.2).1.invariant) with ⟨r, hr, he⟩
    simp only [he]
    exact hr
  add_left x y z := by
    have hinv {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ} (hH : H ∈ E) :
        H ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) :=
      (isBianchiSlashInvariant_iff_mem 𝔑).mp (hE hH).1.invariant
    have h₁ : conj (bianchiPetersson σ k 𝔑 z (x + y : E)) =
        conj (bianchiPetersson σ k 𝔑 z x + bianchiPetersson σ k 𝔑 z y) := by
      rw [conj_bianchiPetersson hK (hinv z.2) (hinv (x + y).2), map_add,
        conj_bianchiPetersson hK (hinv z.2) (hinv x.2),
        conj_bianchiPetersson hK (hinv z.2) (hinv y.2)]
      exact bianchiPetersson_add_left hK hk h𝔑 (hE x.2) (hE y.2) (hE z.2)
    exact (starRingEnd ℂ).injective h₁
  smul_left x y r := by
    have hinv {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ} (hH : H ∈ E) :
        H ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) :=
      (isBianchiSlashInvariant_iff_mem 𝔑).mp (hE hH).1.invariant
    have h₁ : conj (bianchiPetersson σ k 𝔑 y (r • x : E)) =
        conj (conj r * bianchiPetersson σ k 𝔑 y x) := by
      rw [conj_bianchiPetersson hK (hinv y.2) (hinv (r • x).2), map_mul, Complex.conj_conj,
        conj_bianchiPetersson hK (hinv y.2) (hinv x.2)]
      exact bianchiPetersson_smul_left hK r (hinv x.2) (hinv y.2)
    exact (starRingEnd ℂ).injective h₁
  definite x hx := Subtype.ext ((bianchiPetersson_self_eq_zero_iff hK hk h𝔑 (hE x.2)).mp hx)

/-- **The spectral theorem on a subspace of `S_k(𝔑)`** for a commuting family of operators symmetric
for the Petersson product. -/
lemma iSup_iInf_eigenspace_of_le {ι : Type*} (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔑 : 𝔑 ≠ ⊥)
    {E : Submodule ℂ (HyperbolicThreeSpace → Fin (k + 1) → ℂ)}
    (hE : E ≤ bianchiCuspForms σ 𝔑.gamma0GL k) {T : ι → Module.End ℂ E}
    (hT : ∀ i (x y : E), bianchiPetersson σ k 𝔑 (T i x : HyperbolicThreeSpace → Fin (k + 1) → ℂ) y =
      bianchiPetersson σ k 𝔑 x (T i y : HyperbolicThreeSpace → Fin (k + 1) → ℂ))
    (hC : Pairwise (Function.onFun Commute T)) :
    ⨆ χ : ι → ℂ, ⨅ i, End.eigenspace (T i) (χ i) = ⊤ := by
  have : FiniteDimensional ℂ (bianchiCuspForms σ 𝔑.gamma0GL k) :=
    finiteDimensional_bianchiCuspForms hK hk h𝔑
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le hE
  let core : InnerProductSpace.Core ℂ E := bianchiPeterssonCore σ hK hk h𝔑 hE
  let _ : NormedAddCommGroup E := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ E := InnerProductSpace.ofCore core.toCore
  exact IsSymmetric.iSup_iInf_eq_top_of_commute (fun i x y ↦ (hT i y x).symm) hC

variable (σ k 𝔑) in
/-- The Hecke operator `T_𝔯` on the space `S_k(𝔑)`, which it preserves. -/
noncomputable def bianchiHeckeTPrimeCusp [NeZero 𝔑] (hK : finrank ℚ K = 2) (𝔯 : Ideal (𝓞 K))
    (h𝔯 : 𝔯 ≠ ⊥) : Module.End ℂ (bianchiCuspForms σ 𝔑.gamma0GL k) :=
  LinearMap.codRestrict _ ((bianchiModularForms σ 𝔑.gamma0GL k).subtype ∘ₗ
    bianchiHeckeTPrime σ k 𝔑 𝔯 h𝔯 ∘ₗ Submodule.inclusion (bianchiCuspForms_le σ _ k))
      fun Φ ↦ bianchiHeckeOperatorModularForms_mem_bianchiCuspForms hK _ _ Φ.2

lemma coe_bianchiHeckeTPrimeCusp [NeZero 𝔑] (hK : finrank ℚ K = 2) (h𝔭 : 𝔭 ≠ ⊥)
    (Φ : bianchiCuspForms σ 𝔑.gamma0GL k) :
    (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
      bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 ⟨Φ, bianchiCuspForms_le σ _ k Φ.2⟩ :=
  rfl

lemma bianchiPetersson_bianchiHeckeTPrimeCusp [NeZero 𝔑] (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤) (Φ Ψ : bianchiCuspForms σ 𝔑.gamma0GL k) :
    bianchiPetersson σ k 𝔑
      (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) Ψ =
        bianchiPetersson σ k 𝔑 Φ (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Ψ :
          HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
  bianchiPetersson_bianchiHeckeTPrime (Φ := ⟨Φ, bianchiCuspForms_le σ _ k Φ.2⟩)
    (Ψ := ⟨Ψ, bianchiCuspForms_le σ _ k Ψ.2⟩) hK hk h𝔭 h𝔭p h𝔭𝔑 Φ.2 Ψ.2

/-- **The Hecke operator `T_𝔭` on Fourier–Bessel coefficients, for `𝔭 ∤ 𝔑`**: for `K` imaginary
quadratic of class number `1`, a prime `𝔭 = (ϖ)` with `𝔭 ⊔ 𝔑 = 𝒪_K` and `Φ` in `S_k(𝔑)`, `k ≥ 1`
even, with Fourier–Bessel coefficients `c`, the form `T_𝔭 Φ` has the coefficients
`α ↦ N(𝔭) |ϖ|^{-(k/2+1)} c(ϖα) + |ϖ|^{k/2+1} c(α / ϖ)`. Every form being a sum of eigenforms of
`T_𝔭` (`iSup_iInf_eigenspace_of_le`), this follows from the case of eigenforms
(`HasBianchiWhittakerExpansion.mul_coeff_eq_of_bianchiHeckeTPrime`). -/
lemma hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp [NeZero 𝔑] (hK : finrank ℚ K = 2)
    (hk : k ≠ 0) (hk' : Even k) (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤)
    (Φ : bianchiCuspForms σ 𝔑.gamma0GL k)
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ) c) :
    HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
      (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ))
        (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 1 c) := by
  have hp₀ : IsPrincipal.generator 𝔭 ≠ 0 := generator_ne_zero h𝔭
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hδ : ((discr K : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = discr K := cpow_ofNat_inv_pow _ 2
  have htop :
      ⨆ χ : Unit → ℂ, ⨅ i, End.eigenspace (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭) (χ i) = ⊤ :=
    iSup_iInf_eigenspace_of_le hK hk (NeZero.ne 𝔑) le_rfl
    (T := fun _ : Unit ↦ bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭)
    (fun _ x y ↦ bianchiPetersson_bianchiHeckeTPrimeCusp hK hk h𝔭 h𝔭p h𝔭𝔑 x y)
    fun i j hij ↦ absurd (Subsingleton.elim i j) hij
  have hmem : Φ ∈ ⨆ μ, End.eigenspace (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭) μ := by
    have hle : (⊤ : Submodule ℂ (bianchiCuspForms σ 𝔑.gamma0GL k)) ≤
        ⨆ μ, End.eigenspace (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭) μ := by
      rw [← htop]
      exact iSup_le fun χ ↦ (iInf_le _ ()).trans
        (le_iSup (fun μ ↦ End.eigenspace (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭) μ) (χ ()))
    exact hle Submodule.mem_top
  have hexp (Ψ : bianchiCuspForms σ 𝔑.gamma0GL k) :
      HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Ψ)
        (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Ψ)) :=
    hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK Ψ.2 hk
  have key : ∀ Ψ ∈ ⨆ μ, End.eigenspace (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭) μ,
      ∀ c : 𝓞 K → ℂ, HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Ψ) c →
        HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
          (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Ψ))
            (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 1 c) := by
    intro Ψ hΨ
    induction hΨ using Submodule.iSup_induction' with
    | mem μ Ψ hΨ =>
      intro c hc
      have hTc : (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Ψ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
          μ • (Ψ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
        congrArg Subtype.val (End.mem_eigenspace_iff.mp hΨ)
      have hT : bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 ⟨Ψ, bianchiCuspForms_le σ _ k Ψ.2⟩ =
          μ • ⟨Ψ, bianchiCuspForms_le σ _ k Ψ.2⟩ := Subtype.ext hTc
      rw [hTc]
      refine (hc.smul μ).congr fun α hα ↦ ?_
      have hcard : Nat.card (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) = Ideal.absNorm 𝔭 :=
        natCard_heckeTranslations _ _ (spanSingleton_bianchiIdealGenerator _ h𝔭)
      have hN₀ : Ideal.absNorm 𝔭 ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr h𝔭
      have hfin : Finite (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) :=
        Nat.finite_of_card_ne_zero (hcard ▸ hN₀)
      let _ : Fintype (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) := Fintype.ofFinite _
      have hrel : μ * c α = Fintype.card (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) *
          ((‖σ (bianchiIdealGenerator 𝔭 h𝔭)‖ ^ (k / 2 + 1))⁻¹ : ℝ) *
            c (IsPrincipal.generator 𝔭 * α) +
          ((‖σ (bianchiIdealGenerator 𝔭 h𝔭)‖ ^ (k / 2 + 1) : ℝ) : ℂ) *
            Function.extend (IsPrincipal.generator 𝔭 * ·) c 0 α :=
        hc.mul_coeff_eq_of_bianchiHeckeTPrime σ (G := ⟨Ψ, bianchiCuspForms_le σ _ k Ψ.2⟩) hK hk' h𝔭
          h𝔭p h𝔭𝔑 hT hα
      rw [Fintype.card_eq_nat_card, hcard] at hrel
      rw [Pi.smul_apply, smul_eq_mul, hrel, bianchiCoeffHecke, one_mul]
      rfl
    | zero =>
      intro c hc
      have h₀ : ∀ α, α ≠ 0 → c α = 0 := fun α hα ↦
        HasBianchiWhittakerExpansion.eq_zero hK hx hδ
          (by simpa only [Submodule.coe_zero, extend_zero] using hc) hα
      rw [map_zero]
      refine hc.congr fun α hα ↦ ?_
      rw [h₀ α hα, bianchiCoeffHecke_congr hp₀ _ _ (c' := (0 : ℂ) • c) (fun β hβ ↦ ?_) hα,
        bianchiCoeffHecke_smul hp₀, zero_smul, Pi.zero_apply]
      rw [h₀ β hβ, Pi.smul_apply, zero_smul]
    | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
      intro c hc
      have h₃ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
          (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Ψ₁ +
            bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Ψ₂ : HyperbolicThreeSpace → Fin (k + 1) → ℂ))
          (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 1
              (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Ψ₁)) +
            bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 1
              (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Ψ₂))) :=
        (h₁ _ (hexp Ψ₁)).add (h₂ _ (hexp Ψ₂))
      have h₄ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
          (extend (Ψ₁ + Ψ₂ : HyperbolicThreeSpace → Fin (k + 1) → ℂ))
          (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Ψ₁) +
            bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Ψ₂)) :=
        (hexp Ψ₁).add (hexp Ψ₂)
      rw [← bianchiCoeffHecke_add hp₀] at h₃
      rw [map_add]
      refine h₃.congr fun α hα ↦ bianchiCoeffHecke_congr hp₀ _ _ (fun β hβ ↦ ?_) hα
      exact h₄.coeff_eq hK hx hδ hc hβ
  exact key Φ hmem c hc

/-- **`T_𝔭` is `U_q` for `𝔭 = (q) ∣ 𝔑`.** -/
lemma coe_bianchiHeckeTPrime_eq_bianchiUpOperator (h𝔭 : 𝔭 ≠ ⊥)
    (hq : (d : 𝓞 K) = IsPrincipal.generator 𝔭) (hqp : Prime (d : 𝓞 K)) (hqN : (d : 𝓞 K) ∣ N)
    (Φ : bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
    (bianchiHeckeTPrime σ k (Ideal.span {(N : 𝓞 K)}) 𝔭 h𝔭 Φ :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) = bianchiUpOperator σ k d Φ :=
  coe_bianchiHeckeTPrime_eq_sum_glSlash_bianchiLevelLower h𝔭 hq
    (isRightTransversal_glUpper hqp hqN) Φ

/-- **The Hecke operator `T_𝔭` on Fourier–Bessel coefficients, for `𝔭 ∣ 𝔑`**: for `K` imaginary
quadratic of class number `1`, a prime `𝔭 = (ϖ)` with `𝔑 ≤ 𝔭` and `Φ` in `S_k(𝔑)`, `k ≥ 1` even,
with Fourier–Bessel coefficients `c`, the form `T_𝔭 Φ` has the coefficients
`α ↦ N(𝔭) |ϖ|^{-(k/2+1)} c(ϖα)`. -/
lemma hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_of_le [NeZero 𝔑] (hK : finrank ℚ K = 2)
    (hk : k ≠ 0) (hk' : Even k) (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) (hle : 𝔑 ≤ 𝔭)
    (Φ : bianchiCuspForms σ 𝔑.gamma0GL k)
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ) c) :
    HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
      (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ))
        (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 0 c) := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have hδ : ((discr K : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = discr K := cpow_ofNat_inv_pow _ 2
  rcases exists_span_eq (NeZero.ne 𝔑) with ⟨N, rfl⟩
  rcases exists_coe_eq_generator h𝔭 with ⟨q, hq⟩
  have hspan : Ideal.span {(q : 𝓞 K)} = 𝔭 := span_coe_eq_of_coe_eq_generator hq
  have hqN : (q : 𝓞 K) ∣ N := Ideal.span_singleton_le_span_singleton.mp (hspan ▸ hle)
  have hexp : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
      (extend (bianchiHeckeTPrimeCusp σ k (Ideal.span {(N : 𝓞 K)}) hK 𝔭 h𝔭 Φ))
      (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
        (extend (bianchiHeckeTPrimeCusp σ k (Ideal.span {(N : 𝓞 K)}) hK 𝔭 h𝔭 Φ))) :=
    hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK
      (bianchiHeckeTPrimeCusp σ k _ hK 𝔭 h𝔭 Φ).2 hk
  have hT : (bianchiHeckeTPrimeCusp σ k (Ideal.span {(N : 𝓞 K)}) hK 𝔭 h𝔭 Φ :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) = bianchiUpOperator σ k q Φ :=
    coe_bianchiHeckeTPrime_eq_bianchiUpOperator h𝔭 hq (hq ▸ prime_generator h𝔭 h𝔭p) hqN _
  have hexp' : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
      (extend (bianchiUpOperator σ k q Φ)) (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
        (extend (bianchiHeckeTPrimeCusp σ k (Ideal.span {(N : 𝓞 K)}) hK 𝔭 h𝔭 Φ))) := by
    rw [← hT]
    exact hexp
  refine hexp.congr fun α hα ↦ ?_
  rw [hc.coeff_bianchiUpOperator hK hx hδ hk' hexp' hα, natCast_card_residue, hspan, hq]

open scoped Classical in
/-- **The Hecke operators `T_𝔭` on Fourier–Bessel coefficients.** -/
lemma hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_ite [NeZero 𝔑] (hK : finrank ℚ K = 2)
    (hk : k ≠ 0) (hk' : Even k) (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) (Φ : bianchiCuspForms σ 𝔑.gamma0GL k)
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ) c) :
    HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
      (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ))
        (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭)
          (if 𝔑 ≤ 𝔭 then 0 else 1) c) := by
  split_ifs with hle
  · exact hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_of_le hK hk hk' h𝔭 h𝔭p hle Φ hc
  · exact hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp hK hk hk' h𝔭 h𝔭p
      ((h𝔭p.isMaximal h𝔭).out.2 _ <| lt_of_le_of_ne le_sup_left
        fun e ↦ hle (sup_eq_left.mp e.symm)) Φ hc

/-- **The Hecke operators commute** (LMFDB `mf.bianchi.hecke_algebra`, `mf.bianchi.spaces`): for
`K` imaginary quadratic of class number `1`, `k ≥ 1` and distinct nonzero primes `𝔭` and `𝔮`, the
operators `T_𝔭` and `T_𝔮` commute on `S_k(𝔑)`. -/
lemma commute_bianchiHeckeTPrimeCusp [NeZero 𝔑] (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔭 : 𝔭 ≠ ⊥)
    (h𝔭p : 𝔭.IsPrime) (h𝔮 : 𝔮 ≠ ⊥) (h𝔮p : 𝔮.IsPrime) (hne : 𝔭 ≠ 𝔮) :
    Commute (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭) (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮 h𝔮) := by
  classical
  refine LinearMap.ext fun Φ ↦ Subtype.ext ?_
  rcases Nat.even_or_odd k with hk' | hodd
  · have hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ)
        (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ)) :=
      hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK Φ.2 hk
    have h₁ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
        (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮 h𝔮 Φ)))
        (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) (if 𝔑 ≤ 𝔭 then 0 else 1)
          (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔮) (Ideal.absNorm 𝔮)
            (if 𝔑 ≤ 𝔮 then 0 else 1)
            (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ)))) :=
      hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_ite hK hk hk' h𝔭 h𝔭p _
        (hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_ite hK hk hk' h𝔮 h𝔮p Φ hc)
    have h₂ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
        (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮 h𝔮 (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ)))
        (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔮) (Ideal.absNorm 𝔮) (if 𝔑 ≤ 𝔮 then 0 else 1)
          (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭)
            (if 𝔑 ≤ 𝔭 then 0 else 1)
            (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ)))) :=
      hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_ite hK hk hk' h𝔮 h𝔮p _
        (hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_ite hK hk hk' h𝔭 h𝔭p Φ hc)
    rw [End.mul_apply, End.mul_apply]
    refine eq_of_hasBianchiWhittakerExpansion h₁ h₂ fun α _ ↦ ?_
    rw [bianchiCoeffHecke_comm (generator_ne_zero h𝔭) (generator_ne_zero h𝔮)
      (isCoprime_generator h𝔭 h𝔭p h𝔮 h𝔮p hne)]
  · rw [((bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 *
      bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮 h𝔮) Φ).2.1.invariant.eq_zero_of_odd hodd,
      ((bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮 h𝔮 *
        bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭) Φ).2.1.invariant.eq_zero_of_odd hodd]

/-- A level raising of a form of a lower level, seen at level `𝔑`, stays old under `T_𝔭`. -/
lemma bianchiHeckeTPrimeCusp_mem_bianchiOldforms_of_coe_eq [NeZero 𝔑] (hK : finrank ℚ K = 2)
    (hk : k ≠ 0) (hk' : Even k) (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) {𝔐 : Ideal (𝓞 K)} (h𝔐 : 𝔑 < 𝔐)
    (hle : 𝔑 ≤ Ideal.span {(d : 𝓞 K)} * 𝔐) (hG : G ∈ bianchiCuspForms σ 𝔐.gamma0GL k)
    (Φ : bianchiCuspForms σ 𝔑.gamma0GL k)
    (hΦ : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) = bianchiLevelRaise σ k d G) :
    (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
      bianchiOldforms σ k 𝔑 := by
  have : NeZero 𝔐 := ⟨fun h ↦ (NeZero.ne 𝔑 : 𝔑 ≠ ⊥) (le_bot_iff.mp (h𝔐.le.trans h.le))⟩
  have hδ : ‖((discr K : ℂ) ^ (2⁻¹ : ℂ))‖ = √|(discr K : ℝ)| :=
    norm_eq_sqrt_of_sq_eq_discr (cpow_ofNat_inv_pow _ 2)
  have hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G)
      (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G)) :=
    hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK hG hk
  have hΦc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ)
      (bianchiCoeffHecke σ k d 0 1 (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
        (extend G))) := by
    rw [hΦ]
    exact hc.bianchiLevelRaise hk' hδ
  have hp : IsPrincipal.generator 𝔭 ≠ 0 := generator_ne_zero h𝔭
  have hd₀ : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmax {𝔄 : Ideal (𝓞 K)} (h𝔄 : ¬𝔄 ≤ 𝔭) : 𝔭 ⊔ 𝔄 = ⊤ :=
    (h𝔭p.isMaximal h𝔭).out.2 _ <| lt_of_le_of_ne le_sup_left
      fun e ↦ h𝔄 (sup_eq_left.mp e.symm)
  by_cases h𝔑𝔭 : 𝔑 ≤ 𝔭
  · have hT : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
        (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ))
        (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 0
          (bianchiCoeffHecke σ k d 0 1
            (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G)))) :=
      hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_of_le hK hk hk' h𝔭 h𝔭p h𝔑𝔭 Φ hΦc
    by_cases hpd : IsPrincipal.generator 𝔭 ∣ d
    · rcases hpd with ⟨d₁, hd₁⟩
      have hd₁₀ : d₁ ≠ 0 := right_ne_zero_of_mul (hd₁ ▸ hd₀)
      rcases (⟨⟨d₁, mem_nonZeroDivisors_of_ne_zero hd₁₀⟩, rfl⟩ :
        ∃ d' : (𝓞 K)⁰, (d' : 𝓞 K) = d₁) with ⟨d', rfl⟩
      have hmem : bianchiLevelRaise σ k d' G ∈ bianchiOldforms σ k 𝔑 :=
        bianchiLevelRaise_mem_bianchiOldforms h𝔐 (hle.trans (Ideal.mul_mono_left
          (Ideal.span_singleton_le_span_singleton.mpr ⟨_, by rw [hd₁, mul_comm]⟩))) hG
      rw [hd₁] at hT
      rw [eq_of_hasBianchiWhittakerExpansion hT ((hc.bianchiLevelRaise (d := d') hk' hδ).smul
        (Ideal.absNorm 𝔭 : ℂ)) fun α _ ↦ bianchiCoeffHecke_bianchiCoeffHecke_of_dvd hp hd₁₀ _]
      exact Submodule.smul_mem _ _ hmem
    · have hcop : IsCoprime (IsPrincipal.generator 𝔭) (d : 𝓞 K) :=
        (prime_generator h𝔭 h𝔭p).coprime_iff_not_dvd.mpr hpd
      by_cases h𝔐𝔭 : 𝔐 ≤ 𝔭
      · have hT' : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
            (extend (bianchiHeckeTPrimeCusp σ k 𝔐 hK 𝔭 h𝔭 ⟨G, hG⟩))
            (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 0
              (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G))) :=
          hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_of_le hK hk hk' h𝔭 h𝔭p h𝔐𝔭 ⟨G, hG⟩ hc
        rw [eq_of_hasBianchiWhittakerExpansion hT (hT'.bianchiLevelRaise (d := d) hk' hδ) fun α _ ↦
          by rw [bianchiCoeffHecke_comm hp hd₀ hcop]]
        exact bianchiLevelRaise_mem_bianchiOldforms h𝔐 hle (Subtype.property _)
      · have hT' : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
            (extend (bianchiHeckeTPrimeCusp σ k 𝔐 hK 𝔭 h𝔭 ⟨G, hG⟩))
            (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 1
              (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G))) :=
          hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp hK hk hk' h𝔭 h𝔭p (hmax h𝔐𝔭) ⟨G, hG⟩ hc
        rcases (⟨⟨(d : 𝓞 K) * IsPrincipal.generator 𝔭,
          mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hd₀ hp)⟩, rfl⟩ :
            ∃ d₂ : (𝓞 K)⁰, (d₂ : 𝓞 K) = (d : 𝓞 K) * IsPrincipal.generator 𝔭) with ⟨d₂, hd₂⟩
        have hmem : bianchiLevelRaise σ k d₂ G ∈ bianchiOldforms σ k 𝔑 :=
          bianchiLevelRaise_mem_bianchiOldforms h𝔐
            (hd₂ ▸ le_span_mul_mul_of_prime h𝔭 h𝔭p hle h𝔑𝔭 hpd h𝔐𝔭) hG
        have h₂ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
            (extend (bianchiLevelRaise σ k d₂ G)) (bianchiCoeffHecke σ k d₂ 0 1
              (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G))) :=
          hc.bianchiLevelRaise hk' hδ
        rw [hd₂] at h₂
        rw [eq_of_hasBianchiWhittakerExpansion hT
          ((hT'.bianchiLevelRaise (d := d) hk' hδ).sub h₂) fun α _ ↦ ?_]
        · exact sub_mem (bianchiLevelRaise_mem_bianchiOldforms h𝔐 hle (Subtype.property _)) hmem
        · rw [bianchiCoeffHecke_comm hp hd₀ hcop, Pi.sub_apply,
            bianchiCoeffHecke_sub_bianchiCoeffHecke hd₀ hp]
  · have hs𝔑 : 𝔭 ⊔ 𝔑 = ⊤ := hmax h𝔑𝔭
    have hs𝔐 : 𝔭 ⊔ 𝔐 = ⊤ := top_unique (hs𝔑 ▸ sup_le_sup_left h𝔐.le _)
    have hpd : ¬IsPrincipal.generator 𝔭 ∣ d := fun hd ↦ h𝔑𝔭 <| by
      refine hle.trans (Ideal.mul_le_left.trans ?_)
      conv_rhs => rw [← Ideal.span_singleton_generator 𝔭]
      exact Ideal.span_singleton_le_span_singleton.mpr hd
    have hcop : IsCoprime (IsPrincipal.generator 𝔭) (d : 𝓞 K) :=
      (prime_generator h𝔭 h𝔭p).coprime_iff_not_dvd.mpr hpd
    have hT : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
        (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ))
        (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 1
          (bianchiCoeffHecke σ k d 0 1
            (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G)))) :=
      hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp hK hk hk' h𝔭 h𝔭p hs𝔑 Φ hΦc
    have hT' : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
        (extend (bianchiHeckeTPrimeCusp σ k 𝔐 hK 𝔭 h𝔭 ⟨G, hG⟩))
        (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭) (Ideal.absNorm 𝔭) 1
          (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G))) :=
      hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp hK hk hk' h𝔭 h𝔭p hs𝔐 ⟨G, hG⟩ hc
    rw [eq_of_hasBianchiWhittakerExpansion hT (hT'.bianchiLevelRaise (d := d) hk' hδ) fun α _ ↦
      by rw [bianchiCoeffHecke_comm hp hd₀ hcop]]
    exact bianchiLevelRaise_mem_bianchiOldforms h𝔐 hle (Subtype.property _)

/-- **The Hecke operators preserve the oldforms** (LMFDB `mf.bianchi.spaces`): for `K` imaginary
quadratic of class number `1`, `k ≥ 1` and a nonzero prime `𝔭`, dividing the level or not, `T_𝔭`
maps the oldforms of level `𝔑` to oldforms. -/
lemma bianchiHeckeTPrimeCusp_mem_bianchiOldforms [NeZero 𝔑] (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ}
    (hH : H ∈ bianchiOldforms σ k 𝔑) : (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭
      ⟨H, bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne 𝔑) hH⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiOldforms σ k 𝔑 := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
    rcases Nat.even_or_odd k with hk' | hodd
    · rcases hx with ⟨𝔐, h𝔐, δ₀, hδ₀, hle, G, hG, rfl⟩
      rcases (⟨⟨δ₀, mem_nonZeroDivisors_of_ne_zero hδ₀⟩, rfl⟩ : ∃ d : (𝓞 K)⁰, (d : 𝓞 K) = δ₀) with
        ⟨d, rfl⟩
      exact bianchiHeckeTPrimeCusp_mem_bianchiOldforms_of_coe_eq hK hk hk' h𝔭 h𝔭p h𝔐 hle hG _
        (bianchiSlash_rowScale_eq_bianchiLevelRaise _)
    · rw [(bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 ⟨x, bianchiOldforms_le_bianchiCuspForms hK
        (NeZero.ne 𝔑) (Submodule.subset_span hx)⟩).2.1.invariant.eq_zero_of_odd hodd]
      exact zero_mem _
  | zero =>
    have e : (⟨0, bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne 𝔑) (zero_mem _)⟩ :
        bianchiCuspForms σ 𝔑.gamma0GL k) = 0 := rfl
    rw [e, map_zero]
    exact zero_mem _
  | add x y hx hy h₁ h₂ =>
    have e : (⟨x + y, bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne 𝔑) (add_mem hx hy)⟩ :
        bianchiCuspForms σ 𝔑.gamma0GL k) =
          ⟨x, bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne 𝔑) hx⟩ +
            ⟨y, bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne 𝔑) hy⟩ := rfl
    rw [e, map_add]
    exact add_mem h₁ h₂
  | smul a x hx h₁ =>
    have e : (⟨a • x, bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne 𝔑)
        (Submodule.smul_mem _ a hx)⟩ : bianchiCuspForms σ 𝔑.gamma0GL k) =
          a • ⟨x, bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne 𝔑) hx⟩ := rfl
    rw [e, map_smul]
    exact Submodule.smul_mem _ a h₁

/-- **The adjoint of `U_q` is `W_N U_q W_N`**: for `G ∈ S_k(N)`, `k` even,
`∑_{i mod q} (G ∣ (q, 0; 0, 1)) ∣ (1, 0; N i, 1) = W_N (U_q (W_N G))`, as
`W_N (1, b; 0, q) W_N = -N (q, 0; -N b, 1)`. -/
lemma bianchiGLSlash_frickeMatrix_bianchiUpOperator (hK : finrank ℚ K = 2) (hk : Even k)
    (hG : G ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
    bianchiGLSlash σ k (frickeMatrix (N : 𝓞 K)) (bianchiUpOperator σ k d
      (bianchiGLSlash σ k (frickeMatrix (N : 𝓞 K)) G)) =
        ∑ i : 𝓞 K ⧸ Ideal.span {(d : 𝓞 K)}, glSlash σ k (glLower ((N : 𝓞 K) * Quotient.out i))
          (bianchiLevelRaise σ k d G) := by
  have hN₀ : ((N : 𝓞 K) : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (NeZero.ne (N : 𝓞 K))
  have hterm (b : 𝓞 K) : bianchiGLSlash σ k (frickeMatrix (N : 𝓞 K)) (glSlash σ k (glUpper b)
      (bianchiLevelLower σ k d (bianchiGLSlash σ k (frickeMatrix (N : 𝓞 K)) G))) =
        glSlash σ k (glLower ((N : 𝓞 K) * -b)) (bianchiLevelRaise σ k d G) := by
    rw [glSlash, bianchiLevelLower, glSlash, bianchiLevelRaise, ← bianchiGLSlash_mul hk,
      ← bianchiGLSlash_mul hk, ← bianchiGLSlash_mul hk, ← bianchiGLSlash_mul hk]
    refine bianchiGLSlash_of_coe_eq_smul hk (c := -((N : 𝓞 K) : K)) ?_ (neg_ne_zero.mpr hN₀)
    ext i j
    simp only [Units.val_mul, mul_apply, Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;> simp [frickeMatrix, heckeUpper, heckeLower, coe_glUpper,
      coe_glLower, mul_comm]
  have hC : bianchiLevelRaise σ k d G ∈
      bianchiCuspForms σ (Ideal.span {((d * N : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k :=
    bianchiLevelRaise_mem_bianchiCuspForms hK hk hG
  rw [bianchiUpOperator, bianchiGLSlash_sum]
  simp only [hterm]
  rw [← Equiv.sum_comp (Equiv.neg (𝓞 K ⧸ Ideal.span {(d : 𝓞 K)}))]
  refine Finset.sum_congr rfl fun j _ ↦
    glSlash_glLower_congr hk (fun δ hδ ↦ hC.1.invariant.glSlash_eq hδ) ?_
  have hq : (d : 𝓞 K) ∣ Quotient.out j + Quotient.out (-j) := by
    rw [← Ideal.mem_span_singleton, ← Quotient.eq_zero_iff_mem, map_add]
    simp only [quotientMk_out, add_neg_cancel]
  rcases hq with ⟨e, he⟩
  refine ⟨-e, ?_⟩
  rw [Submonoid.coe_mul, Equiv.neg_apply]
  linear_combination -(N : 𝓞 K) * he

/-- **The adjoint of `U_q` on `S_k(N)`**, for a prime `q ∣ N` and even `k ≥ 1`:
`⟨U_q F, G⟩ = ⟨F, W_N (U_q (W_N G))⟩`. -/
lemma bianchiPetersson_bianchiUpOperator (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hk' : Even k)
    (hd : Prime (d : 𝓞 K)) (hdN : (d : 𝓞 K) ∣ N)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k)
    (hG : G ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
    bianchiPetersson σ k (Ideal.span {(N : 𝓞 K)}) (bianchiUpOperator σ k d F) G =
      bianchiPetersson σ k (Ideal.span {(N : 𝓞 K)}) F
        (bianchiGLSlash σ k (frickeMatrix (N : 𝓞 K)) (bianchiUpOperator σ k d
          (bianchiGLSlash σ k (frickeMatrix (N : 𝓞 K)) G))) := by
  rw [bianchiGLSlash_frickeMatrix_bianchiUpOperator hK hk' hG]
  exact bianchiPetersson_sum_glSlash_bianchiLevelLower hK hk hk' (isRightTransversal_glUpper hd hdN)
    (isRightTransversal_glLower hd hdN) hF hG

/-- **The Hecke operators preserve the newspace** (LMFDB `mf.bianchi.spaces`): for `K` imaginary
quadratic of class number `1`, `k ≥ 1` and a nonzero prime `𝔭`, dividing the level or not, `T_𝔭`
maps the newspace of level `𝔑` to itself. For `𝔭 ∤ 𝔑` this follows from self-adjointness, for
`𝔭 ∣ 𝔑` from the adjoint `W_𝔑 T_𝔭 W_𝔑` of `T_𝔭`, as `T_𝔭` and `W_𝔑` preserve the oldforms. -/
lemma bianchiHeckeTPrimeCusp_mem_bianchiNewSubspace [NeZero 𝔑] (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) (Φ : bianchiCuspForms σ 𝔑.gamma0GL k)
    (hΦ : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiNewSubspace σ k 𝔑) :
    (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
      bianchiNewSubspace σ k 𝔑 := by
  rw [mem_bianchiNewSubspace_iff hK hk (NeZero.ne 𝔑)]
  refine ⟨Subtype.property _, fun G hG ↦ ?_⟩
  have hΦ' : ∀ G ∈ bianchiOldforms σ k 𝔑,
      bianchiPetersson σ k 𝔑 (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) G = 0 :=
    ((mem_bianchiNewSubspace_iff hK hk (NeZero.ne 𝔑)).mp hΦ).2
  rcases Nat.even_or_odd k with hk' | hodd
  · by_cases hle : 𝔑 ≤ 𝔭
    · rcases exists_span_eq (NeZero.ne 𝔑) with ⟨N, rfl⟩
      rcases exists_coe_eq_generator h𝔭 with ⟨q, hq⟩
      have hqN : (q : 𝓞 K) ∣ N := Ideal.span_singleton_le_span_singleton.mp
        (span_coe_eq_of_coe_eq_generator hq ▸ hle)
      have hqp : Prime (q : 𝓞 K) := hq ▸ prime_generator h𝔭 h𝔭p
      have hT {Ψ : bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k} :
          (bianchiHeckeTPrimeCusp σ k (Ideal.span {(N : 𝓞 K)}) hK 𝔭 h𝔭 Ψ :
            HyperbolicThreeSpace → Fin (k + 1) → ℂ) = bianchiUpOperator σ k q Ψ :=
        coe_bianchiHeckeTPrime_eq_bianchiUpOperator h𝔭 hq hqp hqN _
      rw [hT, bianchiPetersson_bianchiUpOperator hK hk hk' hqp hqN Φ.2
        (bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne _) hG)]
      refine hΦ' _ ?_
      have hWG : bianchiGLSlash σ k (frickeMatrix (N : 𝓞 K)) G ∈
          bianchiOldforms σ k (Ideal.span {(N : 𝓞 K)}) :=
        bianchiSlash_frickeMatrix_mem_bianchiOldforms (N : 𝓞 K) hK hG
      have hU : bianchiUpOperator σ k q (bianchiGLSlash σ k (frickeMatrix (N : 𝓞 K)) G) ∈
          bianchiOldforms σ k (Ideal.span {(N : 𝓞 K)}) :=
        hT (Ψ := ⟨_, bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne _) hWG⟩) ▸
          bianchiHeckeTPrimeCusp_mem_bianchiOldforms hK hk h𝔭 h𝔭p hWG
      exact bianchiSlash_frickeMatrix_mem_bianchiOldforms (N : 𝓞 K) hK hU
    · have h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤ := (h𝔭p.isMaximal h𝔭).out.2 _ <|
        lt_of_le_of_ne le_sup_left fun e ↦ hle (sup_eq_left.mp e.symm)
      have hG' : G ∈ bianchiCuspForms σ 𝔑.gamma0GL k :=
        bianchiOldforms_le_bianchiCuspForms hK (NeZero.ne 𝔑) hG
      rw [bianchiPetersson_bianchiHeckeTPrimeCusp hK hk h𝔭 h𝔭p h𝔭𝔑 Φ ⟨G, hG'⟩]
      exact hΦ' _ (bianchiHeckeTPrimeCusp_mem_bianchiOldforms hK hk h𝔭 h𝔭p hG)
  · rw [(bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ).2.1.invariant.eq_zero_of_odd hodd,
      ← Φ.2.1.invariant.eq_zero_of_odd hodd]
    exact hΦ' G hG

end HyperbolicThreeSpace
