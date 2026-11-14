import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ModularForm
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.QuasiModular
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.EllipticInvariance
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.RingTheory.Binomial
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# New modular forms from given ones: products and derivatives

The modular forms of weight `k ∈ ℤ` and multiplier system `v` on a subgroup `Γ` of `SL(2, ℝ)` form
a complex vector space (`ModularForm.multiplierSpace`), and those with trivial multiplier form a
graded ring (Mathlib's instance `DirectSum.GCommRing (ModularForm Γ)`). This file proves the other
ways of creating new modular forms from given ones on the same group that the LMFDB lists (LMFDB
`mf.gl2.history.new`): products, and the derivative with its repairs.

Write `f'` for the derivative of `f`, so that Mathlib's normalised derivative is `D f = f' / 2πi`.
Differentiating the modular identity `f(γz) = v(γ) (cz + d)^k f(z)` with `(γz)' = (cz + d)⁻²` gives
`f'(γz) = v(γ) ((cz + d)^(k + 2) f'(z) + k c (cz + d)^(k + 1) f(z))`, so `f'` is a quasi-modular
form of weight `k + 2` and depth at most `1`, and a modular form of weight `2` if `k = 0`. The
LMFDB's formula omits the factor `c` of the second term, without which it fails already for
translations. The defect of modularity is repaired in three ways.

* By the auxiliary function `1 / y`: the Maass–Shimura derivative `f' + k f / (2iy)` transforms
  with weight `k + 2`.
* By the Eisenstein series `E₂`: on subgroups of `SL(2, ℤ)`, the Serre derivative
  `D f - (k / 12) E₂ f` is a modular form of weight `k + 2` with the multiplier of `f`.
* By combinations: if `g` has weight `ℓ` and multiplier `w`, then `f^ℓ / g^k` transforms with
  weight `0`, so its derivative transforms with weight `2`; it is
  `f^(ℓ - 1) g^(-k - 1) (ℓ f' g - k f g')`, and `ℓ f' g - k f g'`, the first Rankin–Cohen bracket,
  is a modular form of weight `k + ℓ + 2` and multiplier `v w`.

## Main definitions

* `ModularForm.derivOfComplex`: the derivative `f'` of a function on the upper half-plane.
* `ModularForm.maassShimura`: the Maass–Shimura derivative `f' + k f / (2iy)`.
* `ModularForm.rankinCohen`: the first Rankin–Cohen bracket `ℓ f' g - k f g'`.
* `ModularForm.rankinCohenBracket`: the `n`-th Rankin–Cohen bracket `[f, g]ₙ`.

## Main results

* `ModularForm.mul_mem_multiplierSpace`: the product of modular forms of weights `k`, `ℓ` and
  multipliers `v`, `w` is a modular form of weight `k + ℓ` and multiplier `v w`.
* `ModularForm.apply_smul_of_mem_multiplierSpace`: the modular identity
  `f(γz) = v(γ) (cz + d)^k f(z)`.
* `ModularForm.hasDerivAt_smul_coe`: `(γz)' = (cz + d)⁻²`.
* `ModularForm.derivOfComplex_slash`: the derivative of `f ∣[k] γ`, for `γ` of determinant `1`.
* `ModularForm.derivOfComplex_smul`: the transformation law of `f'`.
* `ModularForm.eq_zero_of_derivOfComplex_smul`: the law fails without the factor `c`.
* `ModularForm.isQuasiModularForm_derivOfComplex`: `f'` is quasi-modular of weight `k + 2`.
* `ModularForm.derivOfComplex_mem_multiplierSpace`: `f'` is modular of weight `2` if `k = 0`.
* `ModularForm.maassShimura_slash`: the transformation law of the Maass–Shimura derivative.
* `ModularForm.serreDerivative_mem_multiplierSpace`: the Serre derivative keeps the multiplier.
* `ModularForm.rankinCohen_slash`, `ModularForm.rankinCohen_mem_multiplierSpace`: the first
  Rankin–Cohen bracket commutes with the slash action, and is a modular form of weight `k + ℓ + 2`.
* `ModularForm.rankinCohenBracket_one`: `ℓ f' g - k f g'` is, up to sign, the case `n = 1` of the
  Rankin–Cohen brackets.
* `ModularForm.zpow_div_zpow_slash`, `ModularForm.derivOfComplex_zpow_div_zpow_slash`: `f^ℓ / g^k`
  transforms with weight `0` and its derivative with weight `2`.
* `ModularForm.derivOfComplex_slash_of_slash_eq`: the derivative of any function transforming with
  weight `0` transforms with weight `2`.
* `ModularForm.derivOfComplex_zpow_div_zpow`: the derivative of `f^ℓ / g^k`.

## References

* H. Cohen and F. Strömberg, *Modular forms: a classical approach*, Graduate Studies in
  Mathematics 179, AMS, 2017.
* D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer, 2008, §5.
-/

open Complex Derivative Filter Matrix GeneralLinearGroup SpecialLinearGroup Subgroup

open UpperHalfPlane hiding I

open scoped ComplexConjugate Manifold MatrixGroups ModularForm Real

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {v w : Γ →* Circle} {k l : ℤ} {u : ℂ}
  {f g : ℍ → ℂ} {α : GL (Fin 2) ℝ} (γ : Γ) (z : ℍ) (r : ℕ)

/-- **The product of two modular forms** (LMFDB `mf.gl2.history.new`): if `f` and `g` are modular
forms on `Γ` of weights `k` and `ℓ` and multiplier systems `v` and `w`, then `f g` is a modular form
of weight `k + ℓ` and multiplier system `v w`. -/
lemma mul_mem_multiplierSpace (hf : f ∈ multiplierSpace k v) (hg : g ∈ multiplierSpace l w) :
    f * g ∈ multiplierSpace (k + l) (v * w) := by
  refine ⟨hf.1.mul hg.1, fun γ ↦ ?_, fun hc α hα ↦ ?_⟩
  · rw [mul_slash, hf.2.1, hg.2.1, HasDetOne.det_eq γ.2, Units.val_one, abs_one, one_smul,
      smul_mul_smul_comm, MonoidHom.mul_apply, Circle.coe_mul]
  · rw [mul_slash]
    exact ((hf.2.2 hc α hα).mul (hg.2.2 hc α hα)).smul _

/-- **The modular identity** (LMFDB `mf.gl2.history.new`): a modular form `f` of weight `k` and
multiplier system `v` on `Γ` satisfies `f(γz) = v(γ) (cz + d)^k f(z)` for `γ = (a, b; c, d) ∈ Γ`. -/
lemma apply_smul_of_mem_multiplierSpace (hf : f ∈ multiplierSpace k v) :
    f ((γ : GL (Fin 2) ℝ) • z) = v γ * denom γ z ^ k * f z := by
  have h : (f ∣[k] (γ : GL (Fin 2) ℝ)) z = ((v γ : ℂ) • f) z := congrFun (hf.2.1 γ) z
  rw [slash_apply_of_det_eq_one (congrArg Units.val (HasDetOne.det_eq γ.2)), zpow_neg (denom _ _),
    ← div_eq_mul_inv, div_eq_iff (zpow_ne_zero _ (denom_ne_zero _ z))] at h
  rw [h, Pi.smul_apply, smul_eq_mul, mul_right_comm]

variable (f) in
/-- The **derivative** `f'` of a function `f` on the upper half-plane, as a function on the upper
half-plane: `2πi` times Mathlib's normalised derivative `D f`. It is `0` where `f` is not
differentiable. -/
noncomputable def derivOfComplex : ℂ :=
  deriv (f ∘ ofComplex) z

variable (f) in
lemma derivOfComplex_eq_smul : derivOfComplex f = (2 * π * I) • D f :=
  funext fun z ↦ (mul_inv_cancel_left₀ two_pi_I_ne_zero (deriv (f ∘ ofComplex) z)).symm

variable (u f) in
lemma derivOfComplex_const_smul : derivOfComplex (u • f) = u • derivOfComplex f :=
  funext fun _ ↦ deriv_const_mul_field u

lemma mdifferentiable_derivOfComplex (hf : MDiff f) : MDiff (derivOfComplex f) :=
  derivOfComplex_eq_smul f ▸ (normalizedDerivOfComplex_mdifferentiable hf).const_smul _

lemma isBoundedAtImInfty_derivOfComplex (hf : MDiff f) (hb : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (derivOfComplex f) :=
  derivOfComplex_eq_smul f ▸ (isBoundedAtImInfty_normalizedDerivOfComplex hf hb).const_smul_left _

lemma derivOfComplex_add (hf : MDiff f) (hg : MDiff g) :
    derivOfComplex (f + g) = derivOfComplex f + derivOfComplex g := by
  rw [derivOfComplex_eq_smul, normalizedDerivOfComplex_add f g hf hg, smul_add,
    ← derivOfComplex_eq_smul, ← derivOfComplex_eq_smul]

lemma derivOfComplex_mul (hf : MDiff f) (hg : MDiff g) :
    derivOfComplex (f * g) = derivOfComplex f * g + f * derivOfComplex g := by
  rw [derivOfComplex_eq_smul, normalizedDerivOfComplex_mul f g hf hg, smul_add, ← smul_mul_assoc,
    ← mul_smul_comm, ← derivOfComplex_eq_smul, ← derivOfComplex_eq_smul]

lemma mdifferentiable_iterate_derivOfComplex (hf : MDiff f) : MDiff (derivOfComplex^[r] f) := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    exact Function.iterate_succ_apply' derivOfComplex r f ▸ mdifferentiable_derivOfComplex ih

lemma isBoundedAtImInfty_iterate_derivOfComplex (hf : MDiff f) (hb : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (derivOfComplex^[r] f) := by
  induction r with
  | zero => exact hb
  | succ r ih =>
    exact Function.iterate_succ_apply' derivOfComplex r f ▸
      isBoundedAtImInfty_derivOfComplex (mdifferentiable_iterate_derivOfComplex r hf) ih

lemma iterate_derivOfComplex_const_smul (c : ℂ) :
    derivOfComplex^[r] (c • f) = c • derivOfComplex^[r] f := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, derivOfComplex_const_smul, Function.iterate_succ_apply']

private lemma val_det_pos (hα : α.det = 1) : 0 < α.val.det := by
  rw [← val_det_apply, hα]
  exact one_pos

/-- **The derivative of a Möbius transformation** (LMFDB `mf.gl2.history.new`): for
`γ = (a, b; c, d)` of determinant `1`, `(γz)' = (cz + d)⁻²`. -/
lemma hasDerivAt_smul_coe (hα : α.det = 1) :
    HasDerivAt (fun w ↦ ((α • ofComplex w : ℍ) : ℂ)) (denom α z ^ (-2 : ℤ)) z := by
  simpa [← val_det_apply, hα] using (hasStrictDerivAt_smul (val_det_pos hα) z).hasDerivAt

/-- **The derivative of a slash**: for `γ = (a, b; c, d)` of determinant `1` and holomorphic `f`,
`(f ∣[k] γ)' = f' ∣[k + 2] γ - k (c / (cz + d)) (f ∣[k] γ)`. This is Mathlib's
`Derivative.normalizedDerivOfComplex_slash` for the derivative `f'`. -/
lemma derivOfComplex_slash (hf : MDiff f) (hα : α.det = 1) : derivOfComplex (f ∣[k] α) =
    derivOfComplex f ∣[k + 2] α - fun z : ℍ ↦ k * ((α 1 0 : ℂ) / denom α z) * (f ∣[k] α) z := by
  rw [derivOfComplex_eq_smul, normalizedDerivOfComplex_slash hf (val_det_pos hα),
    derivOfComplex_eq_smul, smul_slash_of_det_pos _ (val_det_pos hα)]
  ext z
  simp only [← val_det_apply, hα, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  simp

lemma isBoundedAt_derivOfComplex (hf : MDiff f) {c : OnePoint ℝ} (hc : c.IsBoundedAt f k) :
    c.IsBoundedAt (derivOfComplex f) (k + 2) := by
  rcases c.exists_mem_SL2 ℝ with ⟨δ, rfl⟩
  rw [OnePoint.isBoundedAt_iff rfl, eq_add_of_sub_eq (derivOfComplex_slash hf (by simp)).symm]
  exact (isBoundedAtImInfty_derivOfComplex (hf.slash k _) (hc _ rfl)).add <|
    ((const_boundedAtFilter _ (k : ℂ)).mul (isBoundedAtImInfty_div_denom _)).mul (hc _ rfl)

lemma derivOfComplex_slash_eq (hf : f ∈ multiplierSpace k v) :
    derivOfComplex f ∣[k + 2] (γ : GL (Fin 2) ℝ) =
      (v γ : ℂ) • quasiModularPolynomial 1 ![derivOfComplex f, (k : ℂ) • f] γ := by
  have h : (v γ : ℂ) • derivOfComplex f = derivOfComplex f ∣[k + 2] (γ : GL (Fin 2) ℝ) -
      fun z : ℍ ↦ k * (((γ : GL (Fin 2) ℝ) 1 0 : ℂ) / denom γ z) * ((v γ : ℂ) • f) z := by
    rw [← derivOfComplex_const_smul, ← hf.2.1 γ, derivOfComplex_slash hf.1 (HasDetOne.det_eq γ.2)]
  ext z
  rw [eq_add_of_sub_eq h.symm]
  simp [quasiModularPolynomial]
  ring1

/-- **The transformation law of the derivative** (LMFDB `mf.gl2.history.new`): if `f` is a modular
form of weight `k` and multiplier system `v` on `Γ`, then
`f'(γz) = v(γ) ((cz + d)^(k + 2) f'(z) + k c (cz + d)^(k + 1) f(z))` for `γ = (a, b; c, d) ∈ Γ`.
The LMFDB's formula lacks the factor `c` of the second term. -/
lemma derivOfComplex_smul (hf : f ∈ multiplierSpace k v) :
    derivOfComplex f ((γ : GL (Fin 2) ℝ) • z) = v γ * (denom γ z ^ (k + 2) * derivOfComplex f z +
      k * (γ : GL (Fin 2) ℝ) 1 0 * denom γ z ^ (k + 1) * f z) := by
  have hd : denom γ z ≠ 0 := denom_ne_zero _ z
  have h2 : denom γ z ^ (k + 2) = denom γ z ^ (k + 1) * denom γ z := by
    rw [← zpow_add_one₀ hd, add_assoc, one_add_one_eq_two]
  have h : (derivOfComplex f ∣[k + 2] (γ : GL (Fin 2) ℝ)) z =
      ((v γ : ℂ) • quasiModularPolynomial 1 ![derivOfComplex f, (k : ℂ) • f] γ) z :=
    congrFun (derivOfComplex_slash_eq γ hf) z
  rw [slash_apply_of_det_eq_one (congrArg Units.val (HasDetOne.det_eq γ.2)), zpow_neg (denom _ _),
    ← div_eq_mul_inv, div_eq_iff (zpow_ne_zero _ hd)] at h
  rw [h, h2]
  simp [quasiModularPolynomial]
  field_simp

/-- **The law fails without the factor `c`**: if a modular form `f` of weight `k` satisfies the
LMFDB's formula `f'(γz) = v(γ) ((cz + d)^(k + 2) f'(z) + k (cz + d)^(k + 1) f(z))` at
`γ = (a, b; c, d) ∈ Γ` and `z`, then `k = 0` or `c = 1` or `f(z) = 0`. -/
lemma eq_zero_of_derivOfComplex_smul (hf : f ∈ multiplierSpace k v)
    (h : derivOfComplex f ((γ : GL (Fin 2) ℝ) • z) =
      v γ * (denom γ z ^ (k + 2) * derivOfComplex f z + k * denom γ z ^ (k + 1) * f z)) :
    k = 0 ∨ (γ : GL (Fin 2) ℝ) 1 0 = 1 ∨ f z = 0 := by
  have h0 :
      (v γ : ℂ) * denom γ z ^ (k + 1) * (k * (((γ : GL (Fin 2) ℝ) 1 0 : ℝ) - 1) * f z) = 0 := by
    linear_combination h - derivOfComplex_smul γ z hf
  simpa [zpow_ne_zero _ (denom_ne_zero _ z), sub_eq_zero, or_assoc] using h0

/-- **The derivative of a modular form is quasi-modular** (LMFDB `mf.gl2.history.new`): if `f` is a
modular form of weight `k` and multiplier system `v` on `Γ`, then `f'` is a quasi-modular form of
weight `k + 2`, depth at most `1` and multiplier system `v`, with `P(z, X) = f'(z) + k f(z) X`. -/
lemma isQuasiModularForm_derivOfComplex (hf : f ∈ multiplierSpace k v) :
    IsQuasiModularForm Γ (k + 2) 1 v (derivOfComplex f) :=
  ⟨mdifferentiable_derivOfComplex hf.1, fun hc ↦ isBoundedAt_derivOfComplex hf.1 (hf.2.2 hc),
    ![derivOfComplex f, (k : ℂ) • f], Fin.forall_fin_two.mpr
      ⟨mdifferentiable_derivOfComplex hf.1, hf.1.const_smul _⟩, (derivOfComplex_slash_eq · hf)⟩

/-- **The derivative of a modular form of weight `0` is modular of weight `2`** (LMFDB
`mf.gl2.history.new`), with the same multiplier system. -/
lemma derivOfComplex_mem_multiplierSpace (hf : f ∈ multiplierSpace 0 v) :
    derivOfComplex f ∈ multiplierSpace 2 v := by
  refine ⟨mdifferentiable_derivOfComplex hf.1, fun γ ↦ ?_,
    fun hc ↦ zero_add (2 : ℤ) ▸ isBoundedAt_derivOfComplex hf.1 (hf.2.2 hc)⟩
  rw [← zero_add (2 : ℤ), derivOfComplex_slash_eq γ hf]
  ext z
  simp [quasiModularPolynomial]

variable (k f) in
/-- The **Maass–Shimura derivative** `f' + k f / (2iy)` of weight `k` of a function `f` on the upper
half-plane, where `y` is the imaginary part: the repair of the derivative of a modular form of
weight `k` by the auxiliary function `1 / y` (LMFDB `mf.gl2.history.new`). It is `2πi` times the
usual `D f - k f / (4πy)`. -/
noncomputable def maassShimura : ℂ :=
  derivOfComplex f z + k / (2 * I * z.im) * f z

/-- **The Maass–Shimura derivative transforms with weight `k + 2`** (LMFDB `mf.gl2.history.new`):
if `f` is a modular form of weight `k` and multiplier system `v` on `Γ`, then
`f' + k f / (2iy)` satisfies the functional equation of weight `k + 2` and multiplier system `v`.
It is not holomorphic. -/
lemma maassShimura_slash (hf : f ∈ multiplierSpace k v) :
    maassShimura k f ∣[k + 2] (γ : GL (Fin 2) ℝ) = (v γ : ℂ) • maassShimura k f := by
  ext z
  have hγ : (γ : GL (Fin 2) ℝ).det.val = 1 := congrArg Units.val (HasDetOne.det_eq γ.2)
  have hd : denom γ z ≠ 0 := denom_ne_zero _ z
  have hy : (z.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr z.im_ne_zero
  have hc : conj (denom γ z) = denom γ z - 2 * I * ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) * z.im := by
    apply Complex.ext <;> simp [denom]
    ring1
  have hd' : denom γ z - 2 * I * ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) * z.im ≠ 0 :=
    hc ▸ (map_ne_zero _).mpr hd
  have him : (((γ : GL (Fin 2) ℝ) • z).im : ℂ) =
      z.im / (denom γ z * (denom γ z - 2 * I * ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) * z.im)) := by
    rw [im_smul_eq_div_normSq, hγ, abs_one, one_mul, ofReal_div, ← hc, mul_conj]
  have hk : denom γ z ^ (k + 2) = denom γ z ^ k * denom γ z ^ 2 := zpow_add₀ hd k 2
  have hP : denom γ z ^ k ≠ 0 := zpow_ne_zero k hd
  rw [slash_apply_of_det_eq_one hγ, Pi.smul_apply, smul_eq_mul, maassShimura, maassShimura,
    derivOfComplex_smul γ z hf, apply_smul_of_mem_multiplierSpace γ z hf, him,
    zpow_neg (denom _ _), hk, zpow_add_one₀ hd k]
  field_simp
  ring1

/-- **The Serre derivative keeps the multiplier** (LMFDB `mf.gl2.history.new`): if `f` is a modular
form of weight `k` and multiplier system `v` on a subgroup `Γ` of `SL(2, ℤ)`, then its Serre
derivative `D f - (k / 12) E₂ f`, the repair of the derivative by the Eisenstein series `E₂`, is a
modular form of weight `k + 2` and multiplier system `v`. For `v = 1` this is Mathlib's
`Derivative.serreDerivativeMF`. -/
lemma serreDerivative_mem_multiplierSpace (hΓ : Γ ≤ 𝒮ℒ) (hf : f ∈ multiplierSpace k v) :
    serreDerivative k f ∈ multiplierSpace (k + 2) v := by
  refine ⟨serreDerivative_mdifferentiable k hf.1, fun γ ↦ ?_, fun {c} hc ↦ ?_⟩
  · rcases hΓ γ.2 with ⟨δ, hδ⟩
    have h : serreDerivative k f ∣[k + 2] mapGL ℝ δ = serreDerivative k (f ∣[k] mapGL ℝ δ) :=
      serreDerivative_slash_equivariant hf.1
    rwa [hδ, hf.2.1 γ, serreDerivative_smul _ _ hf.1] at h
  · rw [OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono hΓ)]
    intro δ hδ
    rw [serreDerivative_slash_equivariant hf.1]
    exact isBoundedAtImInfty_serreDerivative k (hf.1.slash k _)
      ((OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono hΓ)).mp (hf.2.2 hc) δ hδ)

variable (k l f g) in
/-- The **first Rankin–Cohen bracket** `ℓ f' g - k f g'` of functions `f` and `g` on the upper
half-plane, taken in weights `k` and `ℓ` (LMFDB `mf.gl2.history.new`). -/
noncomputable def rankinCohen : ℍ → ℂ :=
  (l : ℂ) • (derivOfComplex f * g) - (k : ℂ) • (f * derivOfComplex g)

/-- **The first Rankin–Cohen bracket commutes with the slash action**: for `γ` of determinant `1`
and holomorphic `f` and `g`, `[f, g] ∣[k + ℓ + 2] γ = [f ∣[k] γ, g ∣[ℓ] γ]`. -/
lemma rankinCohen_slash (hf : MDiff f) (hg : MDiff g) (hα : α.det = 1) :
    rankinCohen k l f g ∣[k + l + 2] α = rankinCohen k l (f ∣[k] α) (g ∣[l] α) := by
  ext z
  have hd : denom α z ≠ 0 := denom_ne_zero α z
  have h1 : denom α z ^ (-(k + l + 2)) = denom α z ^ (-(k + 2)) * denom α z ^ (-l) := by
    rw [← zpow_add₀ hd]
    congr 1
    ring1
  have h2 : denom α z ^ (-(k + l + 2)) = denom α z ^ (-k) * denom α z ^ (-(l + 2)) := by
    rw [← zpow_add₀ hd]
    congr 1
    ring1
  simp only [rankinCohen, derivOfComplex_slash hf hα, derivOfComplex_slash hg hα,
    slash_apply_of_det_eq_one (congrArg Units.val hα), Pi.sub_apply, Pi.smul_apply, Pi.mul_apply]
  linear_combination (l * derivOfComplex f (α • z) * g (α • z)) * h1 -
    (k * f (α • z) * derivOfComplex g (α • z)) * h2

/-- **The first Rankin–Cohen bracket of two modular forms is a modular form** (LMFDB
`mf.gl2.history.new`): if `f` and `g` are modular forms on `Γ` of weights `k` and `ℓ` and multiplier
systems `v` and `w`, then `ℓ f' g - k f g'` is a modular form of weight `k + ℓ + 2` and multiplier
system `v w`. -/
lemma rankinCohen_mem_multiplierSpace (hf : f ∈ multiplierSpace k v)
    (hg : g ∈ multiplierSpace l w) : rankinCohen k l f g ∈ multiplierSpace (k + l + 2) (v * w) := by
  refine ⟨?_, fun γ ↦ ?_, fun {c} hc ↦ ?_⟩
  · exact (((mdifferentiable_derivOfComplex hf.1).mul hg.1).const_smul _).sub
      ((hf.1.mul (mdifferentiable_derivOfComplex hg.1)).const_smul _)
  · rw [rankinCohen_slash hf.1 hg.1 (HasDetOne.det_eq γ.2), hf.2.1, hg.2.1]
    ext z
    simp [rankinCohen, derivOfComplex_const_smul]
    ring1
  · rcases c.exists_mem_SL2 ℝ with ⟨δ, rfl⟩
    rw [OnePoint.isBoundedAt_iff rfl, rankinCohen_slash hf.1 hg.1 (by simp)]
    exact (((isBoundedAtImInfty_derivOfComplex (hf.1.slash k _) (hf.2.2 hc _ rfl)).mul
      (hg.2.2 hc _ rfl)).const_smul_left _).sub <| ((hf.2.2 hc _ rfl).mul <|
        isBoundedAtImInfty_derivOfComplex (hg.1.slash l _) (hg.2.2 hc _ rfl)).const_smul_left _

variable (k l f g) in
/-- The **`n`-th Rankin–Cohen bracket**
`[f, g]ₙ = ∑_{r + s = n} (-1)^r C(k + n - 1, s) C(ℓ + n - 1, r) f^(r) g^(s)` of functions `f` and
`g` on the upper half-plane, taken in weights `k` and `ℓ`, where `f^(r)` is the `r`-th derivative:
the series of bilinear operators of which `ℓ f' g - k f g'` is, up to sign, the case `n = 1` (LMFDB
`mf.gl2.history.new`). That `[f, g]ₙ` is a modular form of weight `k + ℓ + 2n` for modular forms
`f` and `g` (Cohen) is `ModularForm.rankinCohenBracket_mem_multiplierSpace`. -/
noncomputable def rankinCohenBracket (n : ℕ) : ℍ → ℂ :=
  ∑ r ∈ Finset.range (n + 1),
    ((-1) ^ r * Ring.choose (k + n - 1) (n - r) * Ring.choose (l + n - 1) r : ℤ) •
      (derivOfComplex^[r] f * derivOfComplex^[n - r] g)

variable (k l f g) in
lemma rankinCohenBracket_zero : rankinCohenBracket k l f g 0 = f * g := by
  simp [rankinCohenBracket]

variable (k l f g) in
/-- **The first Rankin–Cohen bracket is a special case of the Rankin–Cohen brackets** (LMFDB
`mf.gl2.history.new`): `[f, g]₁ = k f g' - ℓ f' g`, the negative of `ℓ f' g - k f g'`. -/
lemma rankinCohenBracket_one : rankinCohenBracket k l f g 1 = -rankinCohen k l f g := by
  ext z
  simp [rankinCohenBracket, rankinCohen, Finset.sum_range_succ]
  ring1

/-- **The quotient `f^ℓ / g^k` has weight `0`** (LMFDB `mf.gl2.history.new`): if `f` and `g` are
modular forms on `Γ` of weights `k` and `ℓ` and multiplier systems `v` and `w`, then `f^ℓ / g^k`
satisfies the functional equation of weight `0` and multiplier system `v^ℓ / w^k`. -/
lemma zpow_div_zpow_slash (hf : f ∈ multiplierSpace k v) (hg : g ∈ multiplierSpace l w) :
    (f ^ l / g ^ k) ∣[(0 : ℤ)] (γ : GL (Fin 2) ℝ) = ((v ^ l / w ^ k) γ : ℂ) • (f ^ l / g ^ k) := by
  ext z
  have hd : (denom γ z ^ k) ^ l ≠ 0 := zpow_ne_zero _ (zpow_ne_zero _ (denom_ne_zero _ z))
  rw [slash_apply_of_det_eq_one (congrArg Units.val (HasDetOne.det_eq γ.2))]
  simp only [Pi.div_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul, neg_zero, zpow_zero, mul_one,
    apply_smul_of_mem_multiplierSpace _ _ hf, apply_smul_of_mem_multiplierSpace _ _ hg, mul_zpow,
    MonoidHom.div_apply, MonoidHom.zpow_apply, Circle.coe_div, Circle.coe_zpow]
  rw [zpow_comm (denom _ _) l k, mul_right_comm _ _ (f z ^ l), mul_right_comm _ _ (g z ^ k),
    mul_div_mul_right _ _ hd, mul_div_mul_comm]

private lemma derivOfComplex_smul_mul_of_slash_eq (hα : α.det = 1) (hf : f ∣[(0 : ℤ)] α = u • f)
    (hd : DifferentiableAt ℂ (f ∘ ofComplex) ↑(α • z)) :
    derivOfComplex f (α • z) * denom α z ^ (-2 : ℤ) = u * derivOfComplex f z := by
  have hd' : HasDerivAt (f ∘ ofComplex) (deriv (f ∘ ofComplex) ↑(α • z)) ↑(α • ofComplex (z : ℂ)) :=
    (ofComplex_apply z).symm ▸ hd.hasDerivAt
  have hc : HasDerivAt (fun w ↦ (f ∘ ofComplex) ↑(α • ofComplex w))
      (deriv (f ∘ ofComplex) ↑(α • z) * denom α z ^ (-2 : ℤ)) z :=
    hd'.comp (z : ℂ) (hasDerivAt_smul_coe z hα)
  have he :
      (fun w ↦ u * (f ∘ ofComplex) w) =ᶠ[nhds ↑z] fun w ↦ (f ∘ ofComplex) ↑(α • ofComplex w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have h0 : (f ∣[(0 : ℤ)] α) (ofComplex w) = (u • f) (ofComplex w) := congrFun hf (ofComplex w)
    rw [slash_apply_of_det_eq_one (congrArg Units.val hα), neg_zero, zpow_zero, mul_one] at h0
    simp [h0]
  exact (hc.congr_of_eventuallyEq he).deriv.symm.trans (deriv_const_mul_field u)

/-- **The derivative of a function of weight `0` has weight `2`** (LMFDB `mf.gl2.history.new`): if
`f ∣[0] γ = u f` for `γ` of determinant `1` and a constant `u ≠ 0`, then `f' ∣[2] γ = u f'`. No
differentiability is assumed: `f` is differentiable at `γz` exactly when it is at `z`. -/
lemma derivOfComplex_slash_of_slash_eq (hα : α.det = 1) (hu : u ≠ 0) (hf : f ∣[(0 : ℤ)] α = u • f) :
    derivOfComplex f ∣[(2 : ℤ)] α = u • derivOfComplex f := by
  ext z
  rw [slash_apply_of_det_eq_one (congrArg Units.val hα), Pi.smul_apply, smul_eq_mul]
  by_cases hd : DifferentiableAt ℂ (f ∘ ofComplex) ↑(α • z)
  · exact derivOfComplex_smul_mul_of_slash_eq z hα hf hd
  rw [derivOfComplex, deriv_zero_of_not_differentiableAt hd, zero_mul]
  by_cases hd' : DifferentiableAt ℂ (f ∘ ofComplex) z
  · have hα' : α⁻¹.det = 1 := by
      rw [map_inv, hα, inv_one]
    have hf' : f ∣[(0 : ℤ)] α⁻¹ = u⁻¹ • f := by
      rw [eq_inv_smul_iff₀ hu, ← smul_slash_of_det_pos _ (val_det_pos hα'), ← hf,
        ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    have h0 : derivOfComplex f (α⁻¹ • α • z) * denom α⁻¹ ↑(α • z) ^ (-2 : ℤ) =
        u⁻¹ * derivOfComplex f (α • z) :=
      derivOfComplex_smul_mul_of_slash_eq (α • z) hα' hf' (by rwa [inv_smul_smul])
    rw [inv_smul_smul, derivOfComplex, derivOfComplex, deriv_zero_of_not_differentiableAt hd,
      mul_zero, mul_eq_zero, or_iff_left (zpow_ne_zero _ (denom_ne_zero _ _))] at h0
    rw [derivOfComplex, h0, mul_zero]
  · rw [derivOfComplex, deriv_zero_of_not_differentiableAt hd', mul_zero]

/-- **The derivative of `f^ℓ / g^k` has weight `2`** (LMFDB `mf.gl2.history.new`): if `f` and `g`
are modular forms on `Γ` of weights `k` and `ℓ` and multiplier systems `v` and `w`, then the
derivative of `f^ℓ / g^k` satisfies the functional equation of weight `2` and multiplier system
`v^ℓ / w^k`. -/
lemma derivOfComplex_zpow_div_zpow_slash (hf : f ∈ multiplierSpace k v)
    (hg : g ∈ multiplierSpace l w) : derivOfComplex (f ^ l / g ^ k) ∣[(2 : ℤ)] (γ : GL (Fin 2) ℝ) =
      ((v ^ l / w ^ k) γ : ℂ) • derivOfComplex (f ^ l / g ^ k) :=
  derivOfComplex_slash_of_slash_eq (HasDetOne.det_eq γ.2) (Circle.coe_ne_zero _)
    (zpow_div_zpow_slash γ hf hg)

variable {z} in
/-- **The derivative of `f^ℓ / g^k`** (LMFDB `mf.gl2.history.new`): for holomorphic `f` and `g`,
`(f^ℓ / g^k)' = f^(ℓ - 1) g^(-k - 1) (ℓ f' g - k f g')` wherever `f` and `g` do not vanish. -/
lemma derivOfComplex_zpow_div_zpow (hf : MDiff f) (hg : MDiff g) (hfz : f z ≠ 0) (hgz : g z ≠ 0) :
    derivOfComplex (f ^ l / g ^ k) z = f z ^ (l - 1) * g z ^ (-k - 1) * rankinCohen k l f g z := by
  have hF : (f ∘ ofComplex) z = f z := congrArg f (ofComplex_apply z)
  have hG : (g ∘ ofComplex) z = g z := congrArg g (ofComplex_apply z)
  have h1 : HasDerivAt ((· ^ l) ∘ f ∘ ofComplex)
      (l * (f ∘ ofComplex) z ^ (l - 1) * deriv (f ∘ ofComplex) z) z :=
    (hasDerivAt_zpow l _ (.inl (hF ▸ hfz))).comp (z : ℂ)
      (mdifferentiableAt_iff.mp (hf z)).hasDerivAt
  have h2 : HasDerivAt ((· ^ k) ∘ g ∘ ofComplex)
      (k * (g ∘ ofComplex) z ^ (k - 1) * deriv (g ∘ ofComplex) z) z :=
    (hasDerivAt_zpow k _ (.inl (hG ▸ hgz))).comp (z : ℂ)
      (mdifferentiableAt_iff.mp (hg z)).hasDerivAt
  have hP : f z ^ l = f z ^ (l - 1) * f z := by
    rw [← zpow_add_one₀ hfz, sub_add_cancel]
  have hQ : g z ^ k = g z ^ (k - 1) * g z := by
    rw [← zpow_add_one₀ hgz, sub_add_cancel]
  have hQ' : g z ^ (-k - 1) = (g z ^ (k - 1) * g z ^ 2)⁻¹ := by
    rw [← zpow_natCast (g z) 2, ← zpow_add₀ hgz, ← zpow_neg (g z)]
    congr 1
    ring1
  have hQ0 : g z ^ (k - 1) ≠ 0 := zpow_ne_zero _ hgz
  refine (h1.div h2 (zpow_ne_zero k (hG ▸ hgz))).deriv.trans ?_
  simp only [Function.comp_apply, rankinCohen, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, derivOfComplex, ofComplex_apply]
  rw [hP, hQ, hQ']
  field_simp

end ModularForm
