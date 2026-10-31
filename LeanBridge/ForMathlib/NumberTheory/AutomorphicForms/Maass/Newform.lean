import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Hecke
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective
import TauCeti.NumberTheory.ModularForms.Petersson.Basic

/-!
# Maass newforms with character on `Γ₀(N)`

A Maass form of weight `0` on `Γ₀(N)` with character `χ` (a Dirichlet character modulo `N`) and
Laplace eigenvalue `λ` is a smooth function `f` on `ℍ`, square-integrable on `Γ₀(N) \ ℍ`, with
`f(γz) = χ(d) f(z)` for `γ = !![a, b; c, d] ∈ Γ₀(N)` and `(Δ + λ) f = 0`. They form a complex
vector space `M(N, χ, λ)`, with the Petersson inner product `⟨F, G⟩ = ∫_{Γ₀(N) \ ℍ} F conj(G) dμ`,
which converges and is definite. For `d M ∣ N ≠ 0`, a Maass form `G` of level `M` and character
`χ'` inducing `χ` gives the oldform `G(dz)`, which lies in `M(N, χ, λ)`: it is smooth, transforms
under `Γ₀(N)` with `χ`, has the same eigenvalue, and is square-integrable on `Γ₀(N) \ ℍ`, since
`diag(d, 1)` conjugates `Γ₀(N)` into a congruence subgroup of `Γ₀(M)`. The old space is spanned by
the oldforms with `M` a proper divisor of `N` (the oldforms of Atkin and Lehner), the new space is
its orthogonal complement in `M(N, χ, λ)` for the Petersson inner product, which meets it only in
`0`, and the multiplicity of `λ` (LMFDB `mf.maass.mwf.dimension`) is the dimension of the new
space. Maass newforms are the nonzero elements of the new space that are eigenfunctions of the
Hecke operators `T_p`, `p ∤ N`.

Functions on `ℍ` are given as functions `ℍ → ℂ`, extended to `ℂ` by
`UpperHalfPlane.ofComplex` to take derivatives. Square-integrability is the integrability of
`|f|²` on the fundamental domain `gammaZeroDomain N` of `Γ₀(N)`, a union of translates of the
open standard domain, for the invariant measure `dx dy / y²`; it does not depend on the
fundamental domain (`integrableOn_iff_of_isFundamentalDomain`), nor does the Petersson inner
product (`maassPetersson_eq_setIntegral`).

Not proved here: that the new space is finite-dimensional and spanned by newforms (Selberg's
spectral theory of `L²(Γ₀(N) \ ℍ)`, and the self-adjointness and commutativity of the Hecke
operators on it). The multiplicity is therefore defined as a cardinal, the rank of the new space,
which is the LMFDB's dimension without assuming its finiteness.

## Main definitions

* `UpperHalfPlane.gammaZeroDomain`: a fundamental domain of `Γ₀(N)`.
* `UpperHalfPlane.IsMaassFormWithCharacter` (LMFDB `mf.maass.mwf`): Maass forms of weight `0` on
  `Γ₀(N)` with character `χ`.
* `UpperHalfPlane.maassSpace`: the space `M(N, χ, λ)` of these forms on `ℍ`.
* `UpperHalfPlane.maassPetersson`: the Petersson inner product.
* `UpperHalfPlane.gammaZeroScale`: the matrix `!![a, d b; c / d, d']` with
  `d (γ z) = γ' (d z)`.
* `UpperHalfPlane.maassLevelRaise`: the oldform `z ↦ G(dz)`.
* `UpperHalfPlane.maassOldSpace`, `UpperHalfPlane.maassNewSpace` (LMFDB
  `mf.maass.mwf.dimension`): the old and new spaces.
* `UpperHalfPlane.maassMultiplicity` (LMFDB `mf.maass.mwf.dimension`): the multiplicity of `λ`.
* `UpperHalfPlane.maassHeckeOperatorChar`: the Hecke operator `T_p` with character `χ`.
* `UpperHalfPlane.IsMaassNewform` (LMFDB `mf.maass.mwf.dimension`,
  `mf.maass.mwf.coefficients`): Maass newforms.

## Main results

* `UpperHalfPlane.isFundamentalDomain_gammaZeroDomain`: `gammaZeroDomain N` is a fundamental
  domain of `Γ₀(N)`.
* `UpperHalfPlane.integrableOn_iff_of_isFundamentalDomain`: square-integrability does not depend
  on the fundamental domain.
* `UpperHalfPlane.integrableOn_mul_conj`: the integral of the Petersson inner product converges.
* `UpperHalfPlane.maassPetersson_eq_setIntegral`: the Petersson inner product does not depend on
  the fundamental domain.
* `UpperHalfPlane.eq_zero_of_maassPetersson_self_eq_zero`: the Petersson inner product is
  definite.
* `UpperHalfPlane.maassLevelRaise_smul`, `UpperHalfPlane.contDiffOn_maassLevelRaise`,
  `UpperHalfPlane.hyperbolicLaplacian_maassLevelRaise_add_mul`: `G(dz)` transforms under `Γ₀(N)`
  with the character `χ` induced by that of `G`, is smooth, and has the eigenvalue of `G`.
* `UpperHalfPlane.integrableOn_maassLevelRaise`: `G(dz)` is square-integrable on `Γ₀(N) \ ℍ`.
* `UpperHalfPlane.maassLevelRaise_mem_maassSpace`: `G(dz)` lies in `M(N, χ, λ)`.
* `UpperHalfPlane.maassLevelRaise_mem_maassOldSpace`: every oldform lies in the old space.
* `UpperHalfPlane.disjoint_maassOldSpace_maassNewSpace`: the old and new spaces meet only in `0`.
* `UpperHalfPlane.maassHeckeOperatorChar_one`: for the trivial character, `T_p` is
  `UpperHalfPlane.maassHeckeOperator`.
-/

open MeasureTheory CongruenceSubgroup ModularGroup Matrix SpecialLinearGroup HeckeRing TauCeti

open scoped MatrixGroups ComplexConjugate ContDiff Pointwise

namespace UpperHalfPlane

variable (N : ℕ) (χ : DirichletCharacter ℂ N) {f g : ℂ → ℂ} (eigenvalue : ℂ) {d M : ℕ}
  {F G : ℍ → ℂ} {γ : SL(2, ℤ)} {w : ℂ} {τ : ℍ} {D : Set ℍ} (p : ℕ)

/-- The fundamental domain `⋃_q q⁻¹ 𝒟ᵒ` of `Γ₀(N)` acting on `ℍ`, where `q` runs over
representatives of the cosets of `Γ₀(N) · {±1}` in `SL(2, ℤ)` and `𝒟ᵒ` is the open standard
fundamental domain of `SL(2, ℤ)` (`isFundamentalDomain_gammaZeroDomain`). -/
noncomputable def gammaZeroDomain : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ (Gamma0 N).withCenter, (q.out : SL(2, ℤ))⁻¹ • fdo

/-- **`gammaZeroDomain N` is a fundamental domain** of the image of `Γ₀(N)` in `PSL(2, ℤ)`, which
acts faithfully on `ℍ`, for the invariant measure. -/
lemma isFundamentalDomain_gammaZeroDomain : IsFundamentalDomain
    ((Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (gammaZeroDomain N) volume :=
  isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter (Gamma0 N)

variable (f) in
/-- A function `f` on the upper half-plane, given on `ℂ`, is a **Maass form** of weight `0` on
`Γ₀(N)` with **character** `χ`, a Dirichlet character modulo `N`, and eigenvalue `λ` (LMFDB
`mf.maass.mwf`, with the character of `cmf.character`) if it is smooth on `ℍ`, square-integrable
on `Γ₀(N) \ ℍ`, satisfies `f(γz) = χ(d) f(z)` for every `γ = !![a, b; c, d] ∈ Γ₀(N)`, and
`(Δ + λ) f = 0` for the hyperbolic Laplacian `Δ` of `hyperbolicLaplacian`.

Square-integrability is the integrability of `|f|²`, which is `Γ₀(N)`-invariant, on the
fundamental domain `gammaZeroDomain N` for the invariant measure `dx dy / y²`; any other
fundamental domain gives the same condition (`integrableOn_iff_of_isFundamentalDomain`). For the
trivial character these are the Maass forms on `Γ₀(N)` of `IsMaassForm`, whose
square-integrability is taken on a fundamental domain in `PGL(2, ℝ)` instead
(`UpperHalfPlane.isMaassFormWithCharacter_one_iff`). -/
def IsMaassFormWithCharacter : Prop :=
  ContDiffOn ℝ ∞ f {z | 0 < z.im} ∧ IntegrableOn (fun z : ℍ ↦ ‖f z‖ ^ 2) (gammaZeroDomain N) ∧
    (∀ γ ∈ Gamma0 N, ∀ z : ℍ, f ↑(γ • z) = χ (γ 1 1 : ℤ) * f z) ∧
    ∀ z : ℂ, 0 < z.im → hyperbolicLaplacian f z + eigenvalue * f z = 0

lemma continuous_comp_coe (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im}) : Continuous fun z : ℍ ↦ f z :=
  hf.continuousOn.comp_continuous continuous_coe fun z ↦ z.im_pos

lemma memLp_two_of_integrableOn (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im})
    (h : IntegrableOn (fun z : ℍ ↦ ‖f z‖ ^ 2) D) : MemLp (fun z : ℍ ↦ f z) 2 (volume.restrict D) :=
  (memLp_two_iff_integrable_sq_norm (continuous_comp_coe hf).aestronglyMeasurable).mpr h

lemma contDiffAt_two_of_contDiffOn (hf : ContDiffOn ℝ ∞ f {z | 0 < z.im}) (hw : 0 < w.im) :
    ContDiffAt ℝ 2 f w :=
  (hf.contDiffAt <| isOpen_upperHalfPlaneSet.mem_nhds hw).of_le <| by norm_num

variable {N χ eigenvalue}

lemma IsMaassFormWithCharacter.add (hf : IsMaassFormWithCharacter N χ f eigenvalue)
    (hg : IsMaassFormWithCharacter N χ g eigenvalue) :
    IsMaassFormWithCharacter N χ (fun z ↦ f z + g z) eigenvalue := by
  have hfg : ContDiffOn ℝ ∞ (fun z ↦ f z + g z) {z | 0 < z.im} := hf.1.add hg.1
  refine ⟨hfg, ?_, fun γ hγ z ↦ ?_, fun z hz ↦ ?_⟩
  · exact (memLp_two_iff_integrable_sq_norm (continuous_comp_coe hfg).aestronglyMeasurable).mp <|
      (memLp_two_of_integrableOn hf.1 hf.2.1).add <| memLp_two_of_integrableOn hg.1 hg.2.1
  · dsimp only
    rw [hf.2.2.1 γ hγ z, hg.2.2.1 γ hγ z]
    ring1
  · rw [hyperbolicLaplacian_add (contDiffAt_two_of_contDiffOn hf.1 hz)
      (contDiffAt_two_of_contDiffOn hg.1 hz)]
    linear_combination hf.2.2.2 z hz + hg.2.2.2 z hz

lemma IsMaassFormWithCharacter.const_mul (hf : IsMaassFormWithCharacter N χ f eigenvalue) (c : ℂ) :
    IsMaassFormWithCharacter N χ (fun z ↦ c * f z) eigenvalue := by
  refine ⟨contDiffOn_const.mul hf.1, ?_, fun γ hγ z ↦ ?_, fun z hz ↦ ?_⟩
  · simp only [norm_mul, mul_pow]
    exact hf.2.1.const_mul _
  · dsimp only
    rw [hf.2.2.1 γ hγ z]
    ring1
  · rw [hyperbolicLaplacian_const_mul c (contDiffAt_two_of_contDiffOn hf.1 hz)]
    linear_combination c * hf.2.2.2 z hz

variable (N χ eigenvalue) in
lemma isMaassFormWithCharacter_zero : IsMaassFormWithCharacter N χ (fun _ ↦ 0) eigenvalue := by
  refine ⟨contDiffOn_const, by simp, fun γ _ z ↦ by simp, fun z _ ↦ ?_⟩
  simp [hyperbolicLaplacian]

lemma isCoprime_of_mem_gamma0 (hγ : γ ∈ Gamma0 N) : IsCoprime (γ 1 1) (N : ℤ) := by
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ with ⟨k, hk⟩
  refine ⟨γ 0 0, -(γ 0 1 * k), ?_⟩
  linear_combination -γ.2.symm.trans (det_fin_two _) + γ 0 1 * hk

variable (χ) in
lemma norm_dirichletCharacter_of_mem_gamma0 (hγ : γ ∈ Gamma0 N) : ‖χ (γ 1 1 : ℤ)‖ = 1 := by
  rw [← ZMod.coe_unitOfIsCoprime _ (isCoprime_of_mem_gamma0 hγ)]
  exact χ.unit_norm_eq_one _

lemma norm_sq_smul_eq (hf : ∀ γ ∈ Gamma0 N, ∀ z : ℍ, f ↑(γ • z) = χ (γ 1 1 : ℤ) * f z)
    (σ : (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (z : ℍ) :
    ‖f ↑(σ • z)‖ ^ 2 = ‖f z‖ ^ 2 := by
  rcases σ.2 with ⟨γ, hγ, hσ⟩
  rw [Subgroup.smul_def, ← hσ, QuotientGroup.mk'_apply, pslMk_smul, hf γ hγ z, norm_mul,
    norm_dirichletCharacter_of_mem_gamma0 χ hγ, one_mul]

/-- **Square-integrability does not depend on the fundamental domain**: for `f` transforming
under `Γ₀(N)` with a character, `|f|²` is integrable on a fundamental domain of `Γ₀(N)` if and
only if it is integrable on `gammaZeroDomain N`. -/
lemma integrableOn_iff_of_isFundamentalDomain
    (hf : ∀ γ ∈ Gamma0 N, ∀ z : ℍ, f ↑(γ • z) = χ (γ 1 1 : ℤ) * f z)
    (hD : IsFundamentalDomain ((Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D
      volume) : IntegrableOn (fun z : ℍ ↦ ‖f z‖ ^ 2) D ↔
    IntegrableOn (fun z : ℍ ↦ ‖f z‖ ^ 2) (gammaZeroDomain N) :=
  hD.integrableOn_iff (isFundamentalDomain_gammaZeroDomain N) <| norm_sq_smul_eq hf

variable (N χ eigenvalue) in
/-- The space `M(N, χ, λ)` of **Maass forms** of weight `0` on `Γ₀(N)` with character `χ` and
eigenvalue `λ` (LMFDB `mf.maass.mwf`, `mf.maass.mwf.dimension`), as a complex subspace of the
functions on `ℍ`: those `F` whose extension `F ∘ ofComplex` to `ℂ` satisfies
`IsMaassFormWithCharacter`. -/
noncomputable def maassSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | IsMaassFormWithCharacter N χ (F ∘ ofComplex) eigenvalue}
  add_mem' hF hG := hF.add hG
  zero_mem' := isMaassFormWithCharacter_zero N χ eigenvalue
  smul_mem' c _ hF := hF.const_mul c

lemma smul_eq_of_mem_maassSpace (hF : F ∈ maassSpace N χ eigenvalue) (hγ : γ ∈ Gamma0 N) :
    F (γ • τ) = χ (γ 1 1 : ℤ) * F τ := by
  simpa using hF.2.2.1 γ hγ τ

lemma memLp_of_mem_maassSpace (hF : F ∈ maassSpace N χ eigenvalue) :
    MemLp F 2 (volume.restrict (gammaZeroDomain N)) := by
  simpa using memLp_two_of_integrableOn hF.1 hF.2.1

lemma continuous_of_mem_maassSpace (hF : F ∈ maassSpace N χ eigenvalue) : Continuous F := by
  simpa using continuous_comp_coe hF.1

variable (N F G) in
/-- The **Petersson inner product** `⟨F, G⟩ = ∫_{Γ₀(N) \ ℍ} F(z) conj(G(z)) dx dy / y²` of two
functions on `ℍ`, integrated over the fundamental domain `gammaZeroDomain N` of `Γ₀(N)`: linear in
`F` and conjugate-linear in `G`, as the LMFDB's Petersson scalar product
(`cmf.petersson_scalar_product`), here without its normalisation by the index of `Γ₀(N)`, which
does not change orthogonality. The integral converges on `M(N, χ, λ)` (`integrableOn_mul_conj`),
where it does not depend on the fundamental domain (`maassPetersson_eq_setIntegral`) and is
definite (`eq_zero_of_maassPetersson_self_eq_zero`). -/
noncomputable def maassPetersson : ℂ :=
  ∫ z in gammaZeroDomain N, F z * conj (G z)

/-- **The Petersson inner product converges** on Maass forms: `F conj(G)` is integrable on
`Γ₀(N) \ ℍ` for `F` and `G` in `M(N, χ, λ)`, by the Cauchy–Schwarz inequality. -/
lemma integrableOn_mul_conj (hF : F ∈ maassSpace N χ eigenvalue)
    (hG : G ∈ maassSpace N χ eigenvalue) :
    IntegrableOn (fun z ↦ F z * conj (G z)) (gammaZeroDomain N) :=
  (memLp_of_mem_maassSpace hF).integrable_mul (memLp_of_mem_maassSpace hG).star

/-- **The Petersson inner product does not depend on the fundamental domain**: for `F` and `G` in
`M(N, χ, λ)` and any fundamental domain `D` of `Γ₀(N)`, `⟨F, G⟩ = ∫_D F conj(G) dμ`. -/
lemma maassPetersson_eq_setIntegral (hF : F ∈ maassSpace N χ eigenvalue)
    (hG : G ∈ maassSpace N χ eigenvalue)
    (hD : IsFundamentalDomain ((Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D
      volume) : maassPetersson N F G = ∫ z in D, F z * conj (G z) := by
  refine (isFundamentalDomain_gammaZeroDomain N).setIntegral_eq hD fun g z ↦ ?_
  rcases g.2 with ⟨γ, hγ, hg⟩
  have h : χ (γ 1 1 : ℤ) * conj (χ (γ 1 1 : ℤ)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_dirichletCharacter_of_mem_gamma0 χ hγ]
    norm_num
  rw [Subgroup.smul_def, ← hg, QuotientGroup.mk'_apply, pslMk_smul,
    smul_eq_of_mem_maassSpace hF hγ, smul_eq_of_mem_maassSpace hG hγ, map_mul]
  linear_combination F z * conj (G z) * h

/-- **The Petersson inner product is definite** on Maass forms: `⟨F, F⟩ = 0` forces `F = 0`.
`|F|²` vanishes almost everywhere on the fundamental domain, hence, being `Γ₀(N)`-invariant, almost
everywhere on `ℍ`, hence everywhere, `F` being continuous. -/
lemma eq_zero_of_maassPetersson_self_eq_zero (hF : F ∈ maassSpace N χ eigenvalue)
    (h : maassPetersson N F F = 0) : F = 0 := by
  have hint : IntegrableOn (fun z ↦ ‖F z‖ ^ 2) (gammaZeroDomain N) := by
    simpa using hF.2.1
  have h0 : ∫ z in gammaZeroDomain N, ‖F z‖ ^ 2 = 0 := by
    have h1 (z : ℍ) : F z * conj (F z) = ((‖F z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [maassPetersson, h1] at h
    exact_mod_cast h
  have hae : ∀ᵐ z ∂(volume.restrict (gammaZeroDomain N)), ‖F z‖ ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z ↦ by positivity) hint).mp h0
  have hopen : IsOpen {z | F z ≠ 0} :=
    isOpen_ne_fun (continuous_of_mem_maassSpace hF) continuous_const
  have hnull : volume {z | F z ≠ 0} = 0 := by
    refine (isFundamentalDomain_gammaZeroDomain N).measure_zero_of_invariant _ (fun g ↦ ?_) ?_
    · ext z
      have h3 : ‖F (g⁻¹ • z)‖ = ‖F z‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
        simpa only [Function.comp_apply, ofComplex_apply] using norm_sq_smul_eq hF.2.2.1 g⁻¹ z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact norm_ne_zero_iff.symm.trans <| h3 ▸ norm_ne_zero_iff
    · rw [← Measure.restrict_apply hopen.measurableSet]
      rw [ae_iff] at hae
      simpa using hae
  have ht : {z | F z ≠ 0} = ∅ := (hopen.measure_eq_zero_iff volume).mp hnull
  funext z
  simpa using congrArg (z ∈ ·) ht

variable (d γ) in
/-- The matrix `γ' = !![a, d b; c / d, d']` of `SL(2, ℤ)` for `γ = !![a, b; c, d']` with `d ∣ c`,
so that `d (γ z) = γ' (d z)` on `ℍ` (`coe_gammaZeroScale_smul`): the conjugate of `γ` by
`diag(d, 1)`. -/
def gammaZeroScale (hd : (d : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, d * γ 0 1; γ 1 0 / d, γ 1 1], by
    rw [det_fin_two_of]
    linear_combination -γ 0 1 * Int.mul_ediv_cancel' hd - γ.2.symm.trans (det_fin_two _)⟩

lemma coe_gammaZeroScale_smul (hd : (d : ℤ) ∣ γ 1 0) (hd0 : 0 < d) :
    ↑(gammaZeroScale d γ hd • ofComplex (d * τ)) = (d : ℂ) * ↑(γ • τ) := by
  have hz : 0 < ((d : ℂ) * τ).im := by
    simpa using mul_pos (Nat.cast_pos.mpr hd0) τ.im_pos
  have hden : ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have h : denom γ τ ≠ 0 := denom_ne_zero γ τ
    rwa [denom_apply] at h
  have hdc : ((d : ℤ) : ℂ) * (((γ 1 0 / d : ℤ)) : ℂ) = ((γ 1 0 : ℤ) : ℂ) := by
    exact_mod_cast Int.mul_ediv_cancel' hd
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply, ofComplex_apply_of_im_pos hz]
  simp only [gammaZeroScale, of_apply, eq_intCast]
  push_cast at hdc ⊢
  rw [← hdc] at hden ⊢
  field_simp

variable (d F) in
/-- The **oldform** `z ↦ F(dz)` on `ℍ` of a function `F` on `ℍ` and a positive integer `d`: for a
Maass form `F` of level `M` and `d M ∣ N` it transforms under `Γ₀(N)`
(`maassLevelRaise_smul`). -/
noncomputable def maassLevelRaise : ℍ → ℂ :=
  fun z ↦ F (ofComplex (d * z))

lemma hyperbolicLaplacian_congr (h : f =ᶠ[nhds w] g) :
    hyperbolicLaplacian f w = hyperbolicLaplacian g w := by
  have h1 (v : ℂ) : (fun u ↦ fderiv ℝ f u v) =ᶠ[nhds w] fun u ↦ fderiv ℝ g u v :=
    (h.fderiv (𝕜 := ℝ)).mono fun u hu ↦ congrArg (· v) hu
  simp only [hyperbolicLaplacian, (h1 1).fderiv_eq, (h1 Complex.I).fderiv_eq]

variable (d F) in
lemma maassLevelRaise_comp_eqOn : Set.EqOn (maassLevelRaise d F ∘ ofComplex)
    (fun u ↦ (F ∘ ofComplex) ((d : ℝ) * u + (0 : ℝ))) {z | 0 < z.im} := by
  intro u hu
  simp [maassLevelRaise, ofComplex_apply_of_im_pos (hu : 0 < u.im)]

variable {χ' : DirichletCharacter ℂ M}

/-- **Oldforms are smooth**: for a Maass form `F` and `d > 0`, `z ↦ F(dz)` is smooth on `ℍ`. -/
lemma contDiffOn_maassLevelRaise (hF : F ∈ maassSpace M χ' eigenvalue) (hd0 : 0 < d) :
    ContDiffOn ℝ ∞ (maassLevelRaise d F ∘ ofComplex) {z | 0 < z.im} :=
  ContDiffOn.congr (fun _ hz ↦
    (contDiffAt_comp_affine hF.1 (Nat.cast_pos.mpr hd0) 0 hz).contDiffWithinAt)
    (maassLevelRaise_comp_eqOn d F)

/-- **Oldforms have the eigenvalue of the form**: for a Maass form `F` with eigenvalue `λ` and
`d > 0`, `z ↦ F(dz)` satisfies `(Δ + λ) F(dz) = 0`, the hyperbolic Laplacian commuting with
`z ↦ dz`. -/
lemma hyperbolicLaplacian_maassLevelRaise_add_mul (hF : F ∈ maassSpace M χ' eigenvalue)
    (hd0 : 0 < d) (hw : 0 < w.im) : hyperbolicLaplacian (maassLevelRaise d F ∘ ofComplex) w +
      eigenvalue * (maassLevelRaise d F ∘ ofComplex) w = 0 := by
  have hdw : 0 < ((d : ℝ) * w + (0 : ℝ) : ℂ).im := by
    simpa using mul_pos (Nat.cast_pos.mpr hd0) hw
  rw [hyperbolicLaplacian_congr <| Filter.eventuallyEq_of_mem
    (isOpen_upperHalfPlaneSet.mem_nhds hw) (maassLevelRaise_comp_eqOn d F),
    hyperbolicLaplacian_comp_affine, maassLevelRaise_comp_eqOn d F hw]
  exact hF.2.2.2 _ hdw

/-- **Oldforms transform under `Γ₀(N)`**: for a Maass form `F` on `Γ₀(M)` with character `χ'`,
`d > 0` and `d M ∣ N`, `F(d γ z) = χ'(d') F(dz)` for every `γ = !![a, b; c, d'] ∈ Γ₀(N)`, since
`d (γ z) = γ' (d z)` with `γ' = !![a, d b; c / d, d'] ∈ Γ₀(M)`. -/
lemma maassLevelRaise_smul (hF : F ∈ maassSpace M χ' eigenvalue) (hd0 : 0 < d) (h : d * M ∣ N)
    (hγ : γ ∈ Gamma0 N) : maassLevelRaise d F (γ • τ) = χ' (γ 1 1 : ℤ) * maassLevelRaise d F τ := by
  have hN : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have hd : (d : ℤ) ∣ γ 1 0 :=
    (Int.natCast_dvd_natCast.mpr <| dvd_of_mul_right_dvd h).trans hN
  have hγ' : gammaZeroScale d γ hd ∈ Gamma0 M := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_div_of_mul_dvd <| (Int.natCast_dvd_natCast.mpr h).trans hN
  have h1 : F (ofComplex (d * ↑(γ • τ))) =
      χ' (gammaZeroScale d γ hd 1 1 : ℤ) * F (ofComplex (d * τ)) := by
    simpa only [Function.comp_apply, ofComplex_apply, coe_gammaZeroScale_smul hd hd0] using
      hF.2.2.1 _ hγ' (ofComplex (d * τ))
  exact h1

lemma maassLevelRaise_comp_smul (hF : F ∈ maassSpace M χ' eigenvalue) (hd0 : 0 < d) (h : d * M ∣ N)
    (hγ : γ ∈ Gamma0 N) : (maassLevelRaise d F ∘ ofComplex) ↑(γ • τ) =
      χ'.changeLevel (dvd_of_mul_left_dvd h) (γ 1 1 : ℤ) * (maassLevelRaise d F ∘ ofComplex) τ := by
  simp only [Function.comp_apply, ofComplex_apply, maassLevelRaise_smul hF hd0 h hγ,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ (isCoprime_of_mem_gamma0 hγ)]

lemma integrableOn_sl_smul_iff {ψ : ℍ → ℝ} (k : SL(2, ℤ)) (A : Set ℍ)
    (hψ : ∀ u, ψ (k⁻¹ • u) = ψ u) : IntegrableOn ψ (k • A) ↔ IntegrableOn ψ A := by
  have h : IntegrableOn (ψ ∘ (k⁻¹ • ·)) ((k⁻¹ • ·) ⁻¹' A) ↔ IntegrableOn ψ A :=
    (measurePreserving_smul k⁻¹ volume).integrableOn_comp_preimage
      (measurableEmbedding_const_smul k⁻¹)
  have hψ' : ψ ∘ (k⁻¹ • ·) = ψ := funext hψ
  rwa [Set.preimage_smul, inv_inv, hψ'] at h

lemma integrableOn_norm_sq_smul_fdo (hF : F ∈ maassSpace M χ' eigenvalue) (σ : SL(2, ℤ)) :
    IntegrableOn (fun u ↦ ‖F u‖ ^ 2) (σ • fdo) := by
  rcases QuotientGroup.mk_out_eq_mul (Gamma0 M).withCenter σ⁻¹ with ⟨k, hk⟩
  have hk' : (k : SL(2, ℤ)) ∈ Gamma0 M :=
    (Subgroup.withCenter_eq_self_iff.mpr <| CongruenceSubgroup.center_le_Gamma0 M).le k.2
  have hsub : ((QuotientGroup.mk σ⁻¹ : SL(2, ℤ) ⧸ (Gamma0 M).withCenter).out)⁻¹ • fdo ⊆
      gammaZeroDomain M :=
    Set.subset_iUnion (fun q : SL(2, ℤ) ⧸ (Gamma0 M).withCenter ↦ (q.out : SL(2, ℤ))⁻¹ • fdo) _
  have hσ : σ • (fdo : Set ℍ) = (k : SL(2, ℤ)) •
      (((QuotientGroup.mk σ⁻¹ : SL(2, ℤ) ⧸ (Gamma0 M).withCenter).out)⁻¹ • fdo) := by
    rw [hk, smul_smul]
    congr 1
    group
  rw [hσ, integrableOn_sl_smul_iff]
  · simpa using hF.2.1.mono_set hsub
  · intro u
    rw [smul_eq_of_mem_maassSpace hF (inv_mem hk'), norm_mul,
      norm_dirichletCharacter_of_mem_gamma0 χ' (inv_mem hk'), one_mul]

lemma scaleRep_map_mul_mapGL (hd0 : 0 < d) (hd : (d : ℤ) ∣ γ 1 0) :
    (GL2.scaleRep d).map (Rat.castHom ℝ) * mapGL ℝ γ =
      mapGL ℝ (gammaZeroScale d γ hd) * (GL2.scaleRep d).map (Rat.castHom ℝ) := by
  have h01 : gammaZeroScale d γ hd 0 1 = d * γ 0 1 := rfl
  have h11 : gammaZeroScale d γ hd 1 1 = γ 1 1 := rfl
  ext i j
  simp only [GeneralLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, GL2.coe_scaleRep d hd0, h01, h11]
  · exact mul_comm _ _
  · exact_mod_cast (Int.ediv_mul_cancel hd).symm

lemma toConjAct_smul_gamma0_eq (hd0 : 0 < d) (hdN : d ∣ N) :
    ConjAct.toConjAct ((GL2.scaleRep d).map (Rat.castHom ℝ)) • (Gamma0 N).map (mapGL ℝ) =
      (conjGL (Gamma0 N) ((GL2.scaleRep d).map (Rat.castHom ℝ))⁻¹).map (mapGL ℝ) := by
  rw [conjGL, inv_inv, Subgroup.map_comap_eq, eq_comm, inf_eq_right]
  intro x hx
  rcases Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx with ⟨γ, hγ, hγx⟩
  have hd : (d : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hdN).trans <|
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  refine ⟨gammaZeroScale d γ hd, ?_⟩
  rw [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hγx
  have h : (GL2.scaleRep d).map (Rat.castHom ℝ) * mapGL ℝ γ =
      mapGL ℝ (gammaZeroScale d γ hd) * (GL2.scaleRep d).map (Rat.castHom ℝ) :=
    scaleRep_map_mul_mapGL hd0 hd
  rw [hγx, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h
  exact (mul_right_cancel h).symm

lemma coe_scaleRep_map_smul (hd0 : 0 < d) :
    ↑((GL2.scaleRep d).map (Rat.castHom ℝ) • τ) = (d : ℂ) * τ := by
  rw [coe_smul_of_det_pos]
  · simp [num, denom, GL2.coe_scaleRep d hd0]
  · rw [GeneralLinearGroup.val_det_apply, det_fin_two]
    simp [hd0]

variable [NeZero N] in
/-- **Oldforms are square-integrable**: for a Maass form `F` on `Γ₀(M)` with character `χ'`,
`d > 0` and `d M ∣ N ≠ 0`, the function `z ↦ F(dz)` is square-integrable on `Γ₀(N) \ ℍ`. With
`α = diag(d, 1)`, `α Γ₀(N) α⁻¹` is the subgroup `Δ = SL(2, ℤ) ∩ α Γ₀(N) α⁻¹` of `Γ₀(M)` (a
congruence subgroup), so `α⁻¹ D` is a fundamental domain of `Γ₀(N)` for the fundamental domain `D`
of `Δ` made of finitely many translates `g 𝒟ᵒ`, `g ∈ SL(2, ℤ)`, and
`∫_{α⁻¹ D} |F(dz)|² dμ = ∫_D |F|² dμ` is finite since `|F|` is `Γ₀(M)`-invariant and
square-integrable on every `g 𝒟ᵒ`. -/
lemma integrableOn_maassLevelRaise (hF : F ∈ maassSpace M χ' eigenvalue) (hd0 : 0 < d)
    (h : d * M ∣ N) : IntegrableOn (fun z ↦ ‖maassLevelRaise d F z‖ ^ 2) (gammaZeroDomain N) := by
  have hΔ : (conjGL (Gamma0 N) ((GL2.scaleRep d).map (Rat.castHom ℝ))⁻¹).FiniteIndex := by
    rw [← map_inv]
    exact ((Gamma0_is_congruence N).conjGL (GL2.scaleRep d)⁻¹).finiteIndex
  have hcomp : (fun z : ℍ ↦ ‖maassLevelRaise d F z‖ ^ 2) =
      (fun u ↦ ‖F u‖ ^ 2) ∘ ((GL2.scaleRep d).map (Rat.castHom ℝ) • ·) := by
    funext z
    simp [maassLevelRaise, ← coe_scaleRep_map_smul hd0]
  refine ((isFundamentalDomain_smul_of_inv_conjAct_eq (Γ' := Gamma0 N)
    (α := ((GL2.scaleRep d).map (Rat.castHom ℝ))⁻¹)
    (by rw [inv_inv]; exact toConjAct_smul_gamma0_eq hd0 (dvd_of_mul_right_dvd h))
    (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter _)).integrableOn_iff
      (isFundamentalDomain_gammaZeroDomain N) fun σ z ↦ ?_).mp ?_
  · simpa only [Function.comp_apply, ofComplex_apply] using
      norm_sq_smul_eq (fun _ hγ _ ↦ maassLevelRaise_comp_smul hF hd0 h hγ) σ z
  · rw [hcomp, ← Set.preimage_smul, (measurePreserving_smul _ volume).integrableOn_comp_preimage
      (measurableEmbedding_const_smul _)]
    exact integrableOn_finite_iUnion.mpr fun q ↦ integrableOn_norm_sq_smul_fdo hF _

variable [NeZero N] in
/-- **Oldforms are Maass forms**: for a Maass form `F` on `Γ₀(M)` with character `χ'` and
eigenvalue `λ`, `d > 0` and `d M ∣ N ≠ 0`, the function `z ↦ F(dz)` lies in `M(N, χ, λ)` for the
character `χ` modulo `N` induced by `χ'`. -/
lemma maassLevelRaise_mem_maassSpace (hF : F ∈ maassSpace M χ' eigenvalue) (hd0 : 0 < d)
    (h : d * M ∣ N) :
    maassLevelRaise d F ∈ maassSpace N (χ'.changeLevel (dvd_of_mul_left_dvd h)) eigenvalue :=
  ⟨contDiffOn_maassLevelRaise hF hd0, by simpa using integrableOn_maassLevelRaise hF hd0 h,
    fun _ hγ _ ↦ maassLevelRaise_comp_smul hF hd0 h hγ,
    fun _ hw ↦ hyperbolicLaplacian_maassLevelRaise_add_mul hF hd0 hw⟩

variable (N χ eigenvalue)

/-- The **old space** (LMFDB `mf.maass.mwf.dimension`) of `M(N, χ, λ)`: the span of the oldforms
`z ↦ G(dz)` in `M(N, χ, λ)`, for `G` a Maass form of level `M` with a character `χ'` modulo `M`
inducing `χ`, `M` a proper divisor of `N` and `d M ∣ N` (the oldforms of Atkin and Lehner). For
`N ≠ 0` every such oldform lies in `M(N, χ, λ)` (`maassLevelRaise_mem_maassSpace`), so that the old
space is the span of all of them (`maassLevelRaise_mem_maassOldSpace`); the condition only matters
for the degenerate level `N = 0`. -/
noncomputable def maassOldSpace : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ {F | F ∈ maassSpace N χ eigenvalue ∧ ∃ (M d : ℕ) (hM : M ∣ N)
    (χ' : DirichletCharacter ℂ M), M ≠ N ∧ d * M ∣ N ∧ χ'.changeLevel hM = χ ∧
      ∃ G ∈ maassSpace M χ' eigenvalue, maassLevelRaise d G = F}

lemma maassOldSpace_le : maassOldSpace N χ eigenvalue ≤ maassSpace N χ eigenvalue :=
  Submodule.span_le.mpr fun _ hF ↦ hF.1

variable {N eigenvalue} [NeZero N] in
/-- **Every oldform lies in the old space**: for a Maass form `G` on `Γ₀(M)` with character `χ'`,
`M` a proper divisor of `N ≠ 0` and `d M ∣ N`, the function `z ↦ G(dz)` lies in the old space of
`M(N, χ, λ)` for the character `χ` induced by `χ'`. -/
lemma maassLevelRaise_mem_maassOldSpace (hG : G ∈ maassSpace M χ' eigenvalue) (h : d * M ∣ N)
    (hMN : M ≠ N) :
    maassLevelRaise d G ∈ maassOldSpace N (χ'.changeLevel (dvd_of_mul_left_dvd h)) eigenvalue := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun hd ↦ NeZero.ne N <| by simpa [hd] using h
  exact Submodule.subset_span ⟨maassLevelRaise_mem_maassSpace hG hd0 h, M, d, _, χ', hMN, h, rfl,
    G, hG, rfl⟩

/-- The **new space** (LMFDB `mf.maass.mwf.dimension`) of `M(N, χ, λ)`: the orthogonal complement
of the old space `maassOldSpace` in `M(N, χ, λ)` for the Petersson inner product
`maassPetersson`, the knowl's eigenspace `M(Γ₀(N), χ, λ)` of Maass newforms of level `N`,
character `χ` and eigenvalue `λ`. That it is spanned by the Maass newforms of `IsMaassNewform` (the
Hecke eigenforms in it) is a theorem of spectral and Hecke theory, not proved here. -/
noncomputable def maassNewSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | F ∈ maassSpace N χ eigenvalue ∧
    ∀ G ∈ maassOldSpace N χ eigenvalue, maassPetersson N F G = 0}
  add_mem' {F₁ F₂} hF₁ hF₂ := ⟨add_mem hF₁.1 hF₂.1, fun G hG ↦ by
    have hG' : G ∈ maassSpace N χ eigenvalue := maassOldSpace_le N χ eigenvalue hG
    simp only [maassPetersson, Pi.add_apply, add_mul]
    rw [integral_add (integrableOn_mul_conj hF₁.1 hG') (integrableOn_mul_conj hF₂.1 hG')]
    simpa only [maassPetersson, add_zero] using
      congrArg₂ (· + ·) (hF₁.2 G hG) (hF₂.2 G hG)⟩
  zero_mem' := ⟨zero_mem _, fun _ _ ↦ by simp [maassPetersson]⟩
  smul_mem' c F hF := ⟨Submodule.smul_mem _ c hF.1, fun G hG ↦ by
    simp only [maassPetersson, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    rw [← maassPetersson, hF.2 G hG, mul_zero]⟩

lemma maassNewSpace_le : maassNewSpace N χ eigenvalue ≤ maassSpace N χ eigenvalue :=
  fun _ hF ↦ hF.1

/-- **The old and new spaces meet only in `0`**, the Petersson inner product being definite
(`eq_zero_of_maassPetersson_self_eq_zero`). -/
lemma disjoint_maassOldSpace_maassNewSpace :
    Disjoint (maassOldSpace N χ eigenvalue) (maassNewSpace N χ eigenvalue) :=
  Submodule.disjoint_def.mpr fun _ hF hF' ↦ eq_zero_of_maassPetersson_self_eq_zero hF'.1 <|
    hF'.2 _ hF

/-- The **multiplicity** (LMFDB `mf.maass.mwf.dimension`) of an eigenvalue `λ` of the Laplacian
for Maass forms of weight `0` on `Γ₀(N)` with character `χ`: the dimension of the knowl's
eigenspace `M(Γ₀(N), χ, λ)` of Maass newforms with eigenvalue `λ`, which is the new space
`maassNewSpace N χ λ` (not the full space `maassSpace N χ λ`), as a cardinal (the rank). It is
finite, by the spectral theory of `L²(Γ₀(N) \ ℍ)`, which is not available, so that its
`Module.finrank` would only be meaningful through that theorem; by Hecke theory (not proved here
either) it is also the number of newforms with eigenvalue `λ` in a basis of Hecke eigenforms. It
is expected to be `0` or `1` unless `χ` has a quadratic factor or `9 ∣ N` (the knowl's remarks).
The knowl also lists eigenvalues coming from an Atkin–Lehner oldspace among the sources of
multiplicity, which concerns the full space `maassSpace N χ λ` rather than its new space. -/
noncomputable def maassMultiplicity : Cardinal :=
  Module.rank ℂ (maassNewSpace N χ eigenvalue)

variable {N} in
/-- The **Hecke operator** `T_p` with character `χ` on functions `φ` on the upper half-plane,
given on `ℂ`: `(T_p φ)(z) = p^{-1/2} (χ(p) φ(pz) + ∑_{j < p} φ((z + j)/p))`, the LMFDB's
normalisation of `maassHeckeOperator` (for which the `p`-th coefficient of a normalised eigenform
is its eigenvalue) with the factor `χ(p)` of the nebentypus. It is meant for primes `p ∤ N`; for
the trivial character it is `maassHeckeOperator` (`maassHeckeOperatorChar_one`). -/
noncomputable def maassHeckeOperatorChar (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((√p)⁻¹ : ℝ) * (χ p * φ (p * z) + ∑ j ∈ Finset.range p, φ ((z + j) / p))

variable {N p} in
/-- **For the trivial character, `T_p` is `maassHeckeOperator`** at every `p ∤ N`. -/
lemma maassHeckeOperatorChar_one (hp : p.Coprime N) :
    maassHeckeOperatorChar (1 : DirichletCharacter ℂ N) p f = maassHeckeOperator p f := by
  funext z
  rw [maassHeckeOperatorChar, maassHeckeOperator,
    MulChar.one_apply <| (ZMod.isUnit_iff_coprime p N).mpr hp, one_mul]

variable (F) in
/-- A **Maass newform** (LMFDB `mf.maass.mwf.dimension`, `mf.maass.mwf.coefficients`) of weight
`0` on `Γ₀(N)` with character `χ` and eigenvalue `λ`: a nonzero function `F` on `ℍ` in the new
space `maassNewSpace N χ λ` that is an eigenfunction of every Hecke operator `T_p`, `p ∤ N`, of
`maassHeckeOperatorChar`. -/
def IsMaassNewform : Prop :=
  F ∈ maassNewSpace N χ eigenvalue ∧ F ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬p ∣ N →
    ∃ c : ℂ, ∀ z : ℍ, maassHeckeOperatorChar χ p (F ∘ ofComplex) z = c * F z

end UpperHalfPlane
