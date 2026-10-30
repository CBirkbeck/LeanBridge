import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.InvariantMeasure
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ScalarValued
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Petersson inner product of Siegel modular forms

For Siegel modular forms `f, g` of weight `ρ` on a subgroup `Γ` of `Sp(2g, ℚ)`, with `ρ` a
representation of `GL(g, ℂ)` on `V`, the Petersson inner product is
`⟨f, g⟩ = ∫_𝔉 b(ρ(Im τ) f(τ), g(τ)) det(Im τ)^{-g-1} dX dY`, where `𝔉` is a fundamental domain of
`Γ` acting on the Siegel upper half-space and `b` is a Hermitian inner product on `V` with
`b(ρ(A)v, w) = b(v, ρ(Aᴴ)w)` for `A ∈ GL(g, ℂ)`. For scalar weight `ρ = det^k` and
`b(v, w) = v w̄`, which is Mathlib's `(innerₛₗ ℂ).flip`, the integrand is
`f(τ) conj(g(τ)) det(Im τ)^k`. The integrand is invariant under
`Γ` and the measure `det(Y)^{-g-1} dX dY` under `Sp(2g, ℝ)`
(`SiegelUpperHalfSpace.invariantMeasure_smul`), so the integral does not depend on the
fundamental domain.

The group `Γ` acts on `ℋ_g` through its image in the permutations of `ℋ_g`, on which `-1` acts
trivially: fundamental domains are those of this image. The LMFDB has no knowl for the Petersson
inner product of Siegel modular forms; it uses it to define new subspaces and the orthogonal
complement of the cusp forms. No normalisation by the volume of `Γ \ ℋ_g` is made, which does not
affect orthogonality. The integral converges when one of `f`, `g` is a cusp form, which is not
proved here.

## Main definitions

* `SiegelUpperHalfSpace.transformationGroup`: the image of `Γ` in the permutations of `ℋ_g`.
* `SiegelUpperHalfSpace.imGL`: the imaginary part of `τ ∈ ℋ_g`, in `GL(g, ℂ)`.
* `SiegelUpperHalfSpace.IsAdmissibleForm`: `b(ρ(A)v, w) = b(v, ρ(Aᴴ)w)` for all `A`.
* `SiegelUpperHalfSpace.peterssonIntegrand`: the integrand `b(ρ(Im τ) f(τ), g(τ))`.
* `SiegelUpperHalfSpace.fundamentalDomain`: a chosen fundamental domain of `Γ`.
* `SiegelUpperHalfSpace.peterssonProduct`: the Petersson inner product.
* `SiegelUpperHalfSpace.IsPeterssonOrthogonal`: Petersson orthogonality.
* `SiegelUpperHalfSpace.peterssonOrthogonal`: the orthogonal complement of a space of forms in
  another.

## Main results

* `SiegelUpperHalfSpace.peterssonIntegrand_smul`: the integrand is invariant under `Γ`.
* `SiegelUpperHalfSpace.peterssonProduct_eq_setIntegral`: the Petersson inner product is the
  integral over any fundamental domain of `Γ`.
* `SiegelUpperHalfSpace.conj_peterssonProduct`: Hermitian symmetry.
* `SiegelUpperHalfSpace.peterssonIntegrand_detPowerRep`: in scalar weight `k` the integrand is
  `det(Im τ)^k f(τ) conj(g(τ))`.
-/

open Matrix Complex MeasureTheory

open scoped ComplexConjugate ComplexOrder

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] (Γ : Subgroup (symplecticGroup l ℚ))

/-- The group of transformations of the Siegel upper half-space induced by a subgroup `Γ` of
`Sp(2g, ℚ)`: the image of `Γ` in the permutations of `ℋ_g`, through which `Γ` acts. The
fundamental domains of `Γ` are those of this group, on which `-1` no longer acts trivially. -/
noncomputable def transformationGroup : Subgroup (Equiv.Perm (SiegelUpperHalfSpace l)) :=
  Γ.map ((MulAction.toPermHom (symplecticGroup l ℝ) (SiegelUpperHalfSpace l)).comp
    (SymplecticGroup.map (algebraMap ℚ ℝ)))

instance : MeasurableSpace (transformationGroup Γ) :=
  ⊤

instance : MeasurableSMul (transformationGroup Γ) (SiegelUpperHalfSpace l) where
  measurable_const_smul g := by
    rcases g with ⟨_, γ, -, rfl⟩
    exact measurable_symplectic_smul _
  measurable_smul_const _ := measurable_from_top

instance : Countable (transformationGroup Γ) := by
  have : Countable (Matrix (l ⊕ l) (l ⊕ l) ℚ) :=
    inferInstanceAs (Countable ((l ⊕ l) → (l ⊕ l) → ℚ))
  exact Set.countable_coe_iff.mpr ((Set.to_countable (Γ : Set (symplecticGroup l ℚ))).image _)

instance :
    SMulInvariantMeasure (transformationGroup Γ) (SiegelUpperHalfSpace l) (invariantMeasure l) where
  measure_preimage_smul g _ hs := by
    rcases g with ⟨_, γ, -, rfl⟩
    exact SMulInvariantMeasure.measure_preimage_smul (SymplecticGroup.map (algebraMap ℚ ℝ) γ) hs

variable (τ : SiegelUpperHalfSpace l)

/-- The imaginary part `Im τ` of a point of the Siegel upper half-space, as an element of
`GL(g, ℂ)`: it is positive definite, hence invertible. -/
noncomputable def imGL : GL l ℂ :=
  (posDef_map_ofReal_iff.mpr τ.posDef_im).isUnit.unit

@[simp]
lemma coe_imGL : (imGL τ : Matrix l l ℂ) = (τ.val.map im).map ofReal :=
  rfl

lemma star_imGL : star (imGL τ) = imGL τ :=
  Units.ext (posDef_map_ofReal_iff.mpr τ.posDef_im).isHermitian

lemma star_denomGL_mul_imGL_smul_mul_denomGL (γ : symplecticGroup l ℝ) :
    star (denomGL γ τ) * imGL (γ • τ) * denomGL γ τ = imGL τ := by
  have hJ : IsUnit (denom γ τ.val).det := isUnit_det_denom γ τ
  have hJ' : IsUnit (denom γ τ.val)ᴴ.det := by
    rwa [det_conjTranspose, isUnit_star]
  ext : 1
  rw [Units.val_mul, Units.val_mul, Units.coe_star, coe_denomGL, coe_imGL, coe_imGL, map_im_smul,
    star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [nonsing_inv_mul _ hJ, Matrix.mul_one, ← Matrix.mul_assoc, conjTranspose_nonsing_inv,
    mul_nonsing_inv _ hJ', Matrix.one_mul]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL l ℂ) V)
    (b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (f g : SiegelUpperHalfSpace l → V)

/-- A sesquilinear form `b` on `V`, linear in its first and conjugate-linear in its second argument,
is **admissible** for the representation `ρ` of `GL(g, ℂ)` on `V` if
`b(ρ(A)v, w) = b(v, ρ(Aᴴ)w)` for all `A ∈ GL(g, ℂ)`. The Petersson inner product of Siegel modular
forms of weight `ρ` is taken with respect to such a Hermitian inner product `b`; for an irreducible
rational `ρ`, these are the `U(g)`-invariant Hermitian inner products on `V`. -/
def IsAdmissibleForm : Prop :=
  ∀ (A : GL l ℂ) (v w : V), b (ρ A v) w = b v (ρ (star A) w)

/-- The **Petersson integrand** `τ ↦ b(ρ(Im τ) f(τ), g(τ))` of `f, g : ℋ_g → V`, to be integrated
against the invariant measure `det(Im τ)^{-g-1} dX dY`. -/
noncomputable def peterssonIntegrand : SiegelUpperHalfSpace l → ℂ :=
  fun τ ↦ b (ρ (imGL τ) (f τ)) (g τ)

lemma peterssonIntegrand_apply : peterssonIntegrand ρ b f g τ = b (ρ (imGL τ) (f τ)) (g τ) :=
  rfl

variable {ρ b}

/-- **The Petersson integrand is invariant under `γ ∈ Sp(2g, ℝ)`** when `f` and `g` transform with
the same factor `c ρ(cτ + d)` of absolute value `|c| = 1` under `γ`: since
`Im(γτ) = (cτ + d)⁻ᴴ Im(τ) (cτ + d)⁻¹` and `b` is admissible,
`b(ρ(Im γτ) f(γτ), g(γτ)) = b(ρ(Im τ) f(τ), g(τ))`. -/
lemma peterssonIntegrand_smul (hb : IsAdmissibleForm ρ b) {γ : symplecticGroup l ℝ} {c : ℂ}
    (hc : ‖c‖ = 1) (hf : ∀ τ, f (γ • τ) = c • ρ (denomGL γ τ) (f τ))
    (hg : ∀ τ, g (γ • τ) = c • ρ (denomGL γ τ) (g τ)) :
    peterssonIntegrand ρ b f g (γ • τ) = peterssonIntegrand ρ b f g τ := by
  have hcc : conj c * c = 1 := by
    rw [conj_mul', hc, ofReal_one, one_pow]
  have hJ (x y : V) : b x (ρ (denomGL γ τ) y) = b (ρ (star (denomGL γ τ)) x) y := by
    rw [hb, star_star]
  simp only [peterssonIntegrand_apply, hf, hg, map_smul, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, smul_eq_mul]
  rw [← mul_assoc, hcc, one_mul, hJ, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
    ← map_mul, star_denomGL_mul_imGL_smul_mul_denomGL]

open scoped Classical in
/-- A **fundamental domain** of `Γ` for its action on the Siegel upper half-space through
`SiegelUpperHalfSpace.transformationGroup`, measurable up to null sets with respect to the
invariant measure: a chosen one, or `∅` if there is none. For arithmetic `Γ` a fundamental domain
exists (Siegel), which is not proved here. -/
noncomputable def fundamentalDomain : Set (SiegelUpperHalfSpace l) :=
  if h : ∃ F, IsFundamentalDomain (transformationGroup Γ) F (invariantMeasure l) then h.choose
  else ∅

variable (ρ b)

/-- The **Petersson inner product** of `f, g : ℋ_g → V` on `Γ`, with respect to a Hermitian form
`b` on `V`: `⟨f, g⟩ = ∫_𝔉 b(ρ(Im τ) f(τ), g(τ)) det(Im τ)^{-g-1} dX dY`, over the chosen
fundamental domain `𝔉` of `Γ` (`SiegelUpperHalfSpace.fundamentalDomain`). For Siegel modular forms
of weight `ρ` with a unitary character, and `b` admissible, it is the integral over any fundamental
domain (`SiegelUpperHalfSpace.peterssonProduct_eq_setIntegral`). It is linear in `f` and
conjugate-linear in `g` where the integrals converge, which they do when `f` or `g` is a cusp form
(not proved here); elsewhere it takes the value of the Bochner integral. -/
noncomputable def peterssonProduct : ℂ :=
  ∫ τ in fundamentalDomain Γ, peterssonIntegrand ρ b f g τ ∂invariantMeasure l

variable {ρ b f g}

/-- **The Petersson inner product does not depend on the fundamental domain**: for Siegel modular
forms `f, g ∈ M_ρ(Γ, ψ)` with a unitary character `ψ` and an admissible form `b`,
`⟨f, g⟩ = ∫_F b(ρ(Im τ) f(τ), g(τ)) det(Im τ)^{-g-1} dX dY` for every fundamental domain `F` of
`Γ`. -/
lemma peterssonProduct_eq_setIntegral (hb : IsAdmissibleForm ρ b) {ψ : Γ →* ℂˣ}
    (hψ : ∀ γ, ‖(ψ γ : ℂ)‖ = 1) (hf : f ∈ modularForms ρ Γ ψ) (hg : g ∈ modularForms ρ Γ ψ)
    {F : Set (SiegelUpperHalfSpace l)}
    (hF : IsFundamentalDomain (transformationGroup Γ) F (invariantMeasure l)) :
    peterssonProduct Γ ρ b f g = ∫ τ in F, peterssonIntegrand ρ b f g τ ∂invariantMeasure l := by
  have hex : ∃ F, IsFundamentalDomain (transformationGroup Γ) F (invariantMeasure l) := ⟨F, hF⟩
  rw [peterssonProduct, fundamentalDomain, dite_eq_left hex]
  refine hex.choose_spec.setIntegral_eq hF fun γ τ ↦ ?_
  rcases γ with ⟨_, γ, hγ, rfl⟩
  exact peterssonIntegrand_smul τ f g hb (hψ ⟨γ, hγ⟩) (hf.2 ⟨γ, hγ⟩) (hg.2 ⟨γ, hγ⟩)

/-- **Hermitian symmetry of the Petersson inner product**: `⟨g, f⟩ = conj ⟨f, g⟩` when `b` is
Hermitian and admissible, `ρ(Im τ)` being self-adjoint. -/
lemma conj_peterssonProduct (hb : IsAdmissibleForm ρ b) (hb' : ∀ v w, conj (b v w) = b w v) :
    conj (peterssonProduct Γ ρ b f g) = peterssonProduct Γ ρ b g f := by
  rw [peterssonProduct, peterssonProduct, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun τ ↦ ?_)
  simp only [peterssonIntegrand_apply]
  rw [hb', hb, star_imGL]

variable (f g)

lemma peterssonIntegrand_add_left (f' : SiegelUpperHalfSpace l → V) :
    peterssonIntegrand ρ b (f + f') g = peterssonIntegrand ρ b f g +
      peterssonIntegrand ρ b f' g := by
  ext τ
  simp [peterssonIntegrand_apply]

lemma peterssonIntegrand_smul_left (c : ℂ) :
    peterssonIntegrand ρ b (c • f) g = c • peterssonIntegrand ρ b f g := by
  ext τ
  simp [peterssonIntegrand_apply]

lemma peterssonIntegrand_zero_left : peterssonIntegrand ρ b 0 g = 0 := by
  ext τ
  simp [peterssonIntegrand_apply]

lemma peterssonIntegrand_zero_right : peterssonIntegrand ρ b f 0 = 0 := by
  ext τ
  simp [peterssonIntegrand_apply]

variable (ρ b)

/-- The function `f` is **Petersson orthogonal** to `g` on `Γ`: the Petersson integrand is
integrable over the chosen fundamental domain and the Petersson inner product `⟨f, g⟩` vanishes.
For cusp forms the integral converges absolutely, which is not proved here, so this is
orthogonality for the Petersson inner product. -/
def IsPeterssonOrthogonal : Prop :=
  IntegrableOn (peterssonIntegrand ρ b f g) (fundamentalDomain Γ) (invariantMeasure l) ∧
    peterssonProduct Γ ρ b f g = 0

variable {ρ b f g} in
lemma isPeterssonOrthogonal_of_peterssonIntegrand_eq_zero (h : peterssonIntegrand ρ b f g = 0) :
    IsPeterssonOrthogonal Γ ρ b f g := by
  rw [IsPeterssonOrthogonal, peterssonProduct, h]
  exact ⟨integrableOn_zero, integral_zero _ _⟩

/-- The **Petersson orthogonal complement** of `W` in `S`, two spaces of functions `ℋ_g → V`: the
`f ∈ S` that are Petersson orthogonal on `Γ` (`SiegelUpperHalfSpace.IsPeterssonOrthogonal`) to
every `g ∈ W`. -/
def peterssonOrthogonal (S W : Submodule ℂ (SiegelUpperHalfSpace l → V)) :
    Submodule ℂ (SiegelUpperHalfSpace l → V) where
  carrier := {f | f ∈ S ∧ ∀ g ∈ W, IsPeterssonOrthogonal Γ ρ b f g}
  add_mem' {f f'} hf hf' := ⟨add_mem hf.1 hf'.1, fun g hg ↦ by
    rcases hf.2 g hg with ⟨hi, h0⟩
    rcases hf'.2 g hg with ⟨hi', h0'⟩
    refine ⟨?_, ?_⟩
    · rw [peterssonIntegrand_add_left]
      exact hi.add hi'
    · rw [peterssonProduct, peterssonIntegrand_add_left]
      simp only [Pi.add_apply]
      rw [integral_add hi hi', ← peterssonProduct, ← peterssonProduct, h0, h0', add_zero]⟩
  zero_mem' := ⟨zero_mem S, fun g _ ↦
    isPeterssonOrthogonal_of_peterssonIntegrand_eq_zero Γ (peterssonIntegrand_zero_left g)⟩
  smul_mem' c f hf := ⟨S.smul_mem c hf.1, fun g hg ↦ by
    rcases hf.2 g hg with ⟨hi, h0⟩
    refine ⟨?_, ?_⟩
    · rw [peterssonIntegrand_smul_left]
      exact hi.smul c
    · rw [peterssonProduct, peterssonIntegrand_smul_left]
      simp only [Pi.smul_apply]
      rw [integral_smul, ← peterssonProduct, h0, smul_zero]⟩

/-! ### Scalar weight -/

private lemma flip_innerₛₗ_apply (v w : ℂ) : (innerₛₗ ℂ).flip v w = v * conj w := by
  rw [LinearMap.flip_apply, innerₛₗ_apply_apply, RCLike.inner_apply]

variable {n : ℕ} (k : ℤ)

lemma isAdmissibleForm_detPowerRep :
    IsAdmissibleForm (TauCeti.detPowerRep ℂ n k) (innerₛₗ ℂ).flip := by
  intro A v w
  have hdet : ((GeneralLinearGroup.det (star A) ^ k : ℂˣ) : ℂ) =
      conj ((GeneralLinearGroup.det A ^ k : ℂˣ) : ℂ) := by
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀]
    simp [star_eq_conjTranspose]
  rw [TauCeti.detPowerRep_apply, TauCeti.detPowerRep_apply, flip_innerₛₗ_apply,
    flip_innerₛₗ_apply, map_mul, hdet, conj_conj]
  ring1

variable (Z : SiegelUpperHalfSpace (Fin n)) (F G : SiegelUpperHalfSpace (Fin n) → ℂ)

/-- **The Petersson integrand in scalar weight `k`** is `det(Im Z)^k F(Z) conj(G(Z))`, for
`ρ = det^k` and the form `b(v, w) = v w̄`, Mathlib's `(innerₛₗ ℂ).flip`. -/
lemma peterssonIntegrand_detPowerRep :
    peterssonIntegrand (TauCeti.detPowerRep ℂ n k) (innerₛₗ ℂ).flip F G Z =
      ((Z.val.map im).det : ℂ) ^ k * F Z * conj (G Z) := by
  rw [peterssonIntegrand_apply, TauCeti.detPowerRep_apply, flip_innerₛₗ_apply,
    Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, coe_imGL, det_map_ofReal]

end SiegelUpperHalfSpace
