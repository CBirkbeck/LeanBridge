import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.ClassicalLift
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.DerivativeLaw

/-!
# The Casimir eigenvalue of the adelic lift

Let `N ≥ 1` and `k` be integers, `f` a holomorphic function on the upper half plane `ℍ` invariant
under `Γ₁(N)` in weight `k`, and `φ_f` its adelic lift `AdelicGL2.adelicLift`. The Casimir operator
`Ω = H² / 2 + E F + F E` at the real place of `ℚ` acts on `φ_f` by the scalar `k (k - 2) / 2`, so
that `φ_f` is finite under the Casimir operators.

Near every point `g` of `GL₂(𝔸_ℚ)`, `φ_f(g x) = c (G ∣[k] x)(i)` for the real matrices `x` of
determinant `1`, with a constant `c` and the holomorphic function `G = f ∣[k] h₀` for a real matrix
`h₀` of positive determinant. The actions of `H`, `E` and `F` are derivatives along the
one-parameter subgroups `diag(eᵗ, e⁻ᵗ)`, `(1, t; 0, 1)` and `(1, 0; t, 1)` of `SL₂(ℝ)`, computed
from the complex derivatives of `G` at `i` and, for the second derivatives, from Mathlib's formula
for the derivative of a slash. With `φ₁ = E φ_f` and `φ₂ = E φ₁`, this gives `F φ_f = φ₁ - i k φ_f`,
`H φ_f = k φ_f + 2 i φ₁`, `H φ₁ = (k + 2) φ₁ + 2 i φ₂` and `F φ₁ = φ₂ - (k + 2) i φ₁ - k φ_f`, and
the terms in `φ₁` and `φ₂` cancel in `Ω φ_f`.

## Main results

* `AdelicGL2.lieDeriv_two_adelicLift`, `AdelicGL2.lieDeriv_zero_adelicLift`: the actions of `F`
  and `H` on `φ_f`.
* `AdelicGL2.casimirReal_adelicLift`: the Casimir eigenvalue `k (k - 2) / 2` of `φ_f`.
* `AdelicGL2.isCasimirFinite_adelicLift`: `φ_f` is finite under the Casimir operators.
-/

open Filter IsDedekindDomain NumberField UpperHalfPlane

open Matrix hiding mul_inv_rev one_zpow zpow_mul zpow_neg

open mixedEmbedding (mixedSpace)

open Derivative (normalizedDerivOfComplex normalizedDerivOfComplex_mdifferentiable)

open scoped AdeleRing Classical Manifold MatrixGroups ModularForm

namespace AdelicGL2

variable {k : ℤ} {f : ℍ → ℂ} {e : ℝ → GL (Fin 2) ℝ} {h m h₀ : GL (Fin 2) ℝ} {τ : ℍ} {b : Fin 3}
  {w : mixedSpace ℚ} (v : {v : InfinitePlace ℚ // v.IsReal}) (t : ℝ) {N : ℕ} [NeZero N]
  {g : AdelicGL2 ℚ} {d : ℂ}

lemma hasDerivAt_slash_upper (hf : MDiffAt f I) (he : ∀ t, (e t).val = !![1, t; 0, 1]) :
    HasDerivAt (fun t ↦ (f ∣[k] e t) I) (deriv (f ∘ ofComplex) I) 0 := by
  have hs : (fun t ↦ (f ∣[k] e t) I) = fun t : ℝ ↦ (f ∘ ofComplex) (Complex.I + t) :=
    funext fun t ↦ by
      have hd : ((e t).det : ℝ) = 1 := by
        rw [GeneralLinearGroup.val_det_apply, he, det_fin_two_of]
        ring1
      have hp : 0 < ((e t).det : ℝ) := hd ▸ one_pos
      rw [ModularForm.slash_apply_of_det_pos k hp, ← comp_ofComplex f, coe_smul_of_det_pos hp,
        num, denom, hd]
      simp [he]
  have hG : HasDerivAt (f ∘ ofComplex) (deriv (f ∘ ofComplex) I) (Complex.I + ((0 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_zero, add_zero]
    exact (mdifferentiableAt_iff.mp hf).hasDerivAt
  rw [hs]
  exact (hG.comp_const_add Complex.I _).comp_ofReal

lemma hasDerivAt_slash_lower (hf : MDiffAt f I) (he : ∀ t, (e t).val = !![1, 0; t, 1]) :
    HasDerivAt (fun t ↦ (f ∣[k] e t) I) (deriv (f ∘ ofComplex) I - Complex.I * k * f I) 0 := by
  have hs : (fun t ↦ (f ∣[k] e t) I) = fun t : ℝ ↦
      (f ∘ ofComplex) (Complex.I / (t * Complex.I + 1)) * (t * Complex.I + 1) ^ (-k) :=
    funext fun t ↦ by
      have hd : ((e t).det : ℝ) = 1 := by
        rw [GeneralLinearGroup.val_det_apply, he, det_fin_two_of]
        ring1
      have hp : 0 < ((e t).det : ℝ) := hd ▸ one_pos
      rw [ModularForm.slash_apply_of_det_pos k hp, ← comp_ofComplex f, coe_smul_of_det_pos hp,
        num, denom, hd]
      simp [he]
  have hl : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * Complex.I + 1) Complex.I 0 :=
    (hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const Complex.I |>.add_const 1 |>.congr_deriv (by simp)
  have hw : HasDerivAt (fun t : ℝ ↦ Complex.I / (t * Complex.I + 1)) 1 0 :=
    (hasDerivAt_const (0 : ℝ) Complex.I).fun_div hl (by simp) |>.congr_deriv (by simp)
  have hz : HasDerivAt (fun t : ℝ ↦ ((t : ℂ) * Complex.I + 1) ^ (-k)) (-k * Complex.I) 0 :=
    (hasDerivAt_zpow (-k) 1 (Or.inl one_ne_zero)).comp_of_eq 0 hl (by simp) |>.congr_deriv
      (by simp)
  have hI : ofComplex Complex.I = I := ofComplex_apply I
  rw [hs]
  refine ((mdifferentiableAt_iff.mp hf).hasDerivAt.comp_of_eq 0 hw (by simp)).fun_mul hz
    |>.congr_deriv ?_
  simp [hI]
  ring1

lemma hasDerivAt_slash_diagonal (hf : MDiffAt f I)
    (he : ∀ t, (e t).val = !![Real.exp t, 0; 0, Real.exp (-t)]) :
    HasDerivAt (fun t ↦ (f ∣[k] e t) I) (k * f I + 2 * Complex.I * deriv (f ∘ ofComplex) I) 0 := by
  have hs : (fun t ↦ (f ∣[k] e t) I) = fun t : ℝ ↦
      (f ∘ ofComplex) (Complex.exp t * Complex.I / Complex.exp (-t)) * Complex.exp (-t) ^ (-k) :=
    funext fun t ↦ by
      have hd : ((e t).det : ℝ) = 1 := by
        rw [GeneralLinearGroup.val_det_apply, he, det_fin_two_of, ← Real.exp_add]
        simp
      have hp : 0 < ((e t).det : ℝ) := hd ▸ one_pos
      rw [ModularForm.slash_apply_of_det_pos k hp, ← comp_ofComplex f, coe_smul_of_det_pos hp,
        num, denom, hd]
      simp [he]
  have h₁ : HasDerivAt (fun t : ℝ ↦ Complex.exp t) 1 0 :=
    (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal.congr_deriv (by simp)
  have h₂ : HasDerivAt (fun t : ℝ ↦ Complex.exp (-t)) (-1) 0 :=
    (hasDerivAt_neg ((0 : ℝ) : ℂ)).cexp.comp_ofReal.congr_deriv (by simp)
  have hw : HasDerivAt (fun t : ℝ ↦ Complex.exp t * Complex.I / Complex.exp (-t))
      (2 * Complex.I) 0 := by
    refine (h₁.mul_const Complex.I).fun_div h₂ (by simp) |>.congr_deriv ?_
    simp
    ring1
  have hz : HasDerivAt (fun t : ℝ ↦ Complex.exp (-t) ^ (-k)) k 0 :=
    (hasDerivAt_zpow (-k) 1 (Or.inl one_ne_zero)).comp_of_eq 0 h₂ (by simp) |>.congr_deriv
      (by simp)
  have hI : ofComplex Complex.I = I := ofComplex_apply I
  rw [hs]
  refine ((mdifferentiableAt_iff.mp hf).hasDerivAt.comp_of_eq 0 hw (by simp)).fun_mul hz
    |>.congr_deriv ?_
  simp [hI]
  ring1

lemma deriv_slash_comp_ofComplex (hf : MDiff f) (hm : (m.det : ℝ) = 1) :
    deriv (f ∣[k] m ∘ ofComplex) τ =
      2 * Real.pi * Complex.I * (normalizedDerivOfComplex f ∣[k + 2] m) τ -
        k * (m 1 0 / denom m τ) * (f ∣[k] m) τ := by
  have hm₁ : m.val.det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hm]
  refine (congrFun (ModularForm.derivOfComplex_slash hf (Units.ext hm)) τ).trans ?_
  rw [ModularForm.derivOfComplex_eq_smul, ModularForm.smul_slash_of_det_pos _ (hm₁ ▸ one_pos)]
  rfl

lemma deriv_normalizedDerivOfComplex_comp_ofComplex :
    deriv (normalizedDerivOfComplex f ∘ ofComplex) τ =
      (2 * Real.pi * Complex.I)⁻¹ * deriv (deriv (f ∘ ofComplex)) τ := by
  rw [← deriv_const_mul_field]
  refine EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
  simp [normalizedDerivOfComplex, ofComplex_apply_of_im_pos hw]

lemma hasDerivAt_deriv_slash_upper (hf : MDiff f) (he : ∀ t, (e t).val = !![1, t; 0, 1]) :
    HasDerivAt (fun t ↦ deriv (f ∣[k] e t ∘ ofComplex) I) (deriv (deriv (f ∘ ofComplex)) I) 0 := by
  have hs : (fun t ↦ deriv (f ∣[k] e t ∘ ofComplex) I) = fun t ↦
      2 * Real.pi * Complex.I * (normalizedDerivOfComplex f ∣[k + 2] e t) I :=
    funext fun t ↦ by
      have hd : ((e t).det : ℝ) = 1 := by
        rw [GeneralLinearGroup.val_det_apply, he, det_fin_two_of]
        ring1
      rw [deriv_slash_comp_ofComplex hf hd]
      simp [he]
  rw [hs]
  refine (hasDerivAt_slash_upper (normalizedDerivOfComplex_mdifferentiable hf I) he).const_mul _
    |>.congr_deriv ?_
  rw [deriv_normalizedDerivOfComplex_comp_ofComplex, mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero]

lemma hasDerivAt_deriv_slash_lower (hf : MDiff f) (he : ∀ t, (e t).val = !![1, 0; t, 1]) :
    HasDerivAt (fun t ↦ deriv (f ∣[k] e t ∘ ofComplex) I) (deriv (deriv (f ∘ ofComplex)) I -
      (k + 2) * Complex.I * deriv (f ∘ ofComplex) I - k * f I) 0 := by
  have hs : (fun t ↦ deriv (f ∣[k] e t ∘ ofComplex) I) = fun t ↦
      2 * Real.pi * Complex.I * (normalizedDerivOfComplex f ∣[k + 2] e t) I -
        k * (t / (t * Complex.I + 1)) * (f ∣[k] e t) I :=
    funext fun t ↦ by
      have hd : ((e t).det : ℝ) = 1 := by
        rw [GeneralLinearGroup.val_det_apply, he, det_fin_two_of]
        ring1
      rw [deriv_slash_comp_ofComplex hf hd]
      simp [denom, he]
  have hl : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * Complex.I + 1) Complex.I 0 :=
    (hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const Complex.I |>.add_const 1 |>.congr_deriv (by simp)
  have hq : HasDerivAt (fun t : ℝ ↦ (t : ℂ) / (t * Complex.I + 1)) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).ofReal_comp.fun_div hl (by simp) |>.congr_deriv (by simp)
  have he₀ : e 0 = 1 := Units.ext ((he 0).trans one_fin_two.symm)
  rw [hs]
  refine (hasDerivAt_slash_lower (normalizedDerivOfComplex_mdifferentiable hf I) he).const_mul _
    |>.fun_sub ((hq.const_mul _).fun_mul (hasDerivAt_slash_lower (hf I) he)) |>.congr_deriv ?_
  rw [deriv_normalizedDerivOfComplex_comp_ofComplex, he₀, SlashAction.slash_one,
    normalizedDerivOfComplex]
  field_simp
  push_cast
  ring1

lemma hasDerivAt_deriv_slash_diagonal (hf : MDiff f)
    (he : ∀ t, (e t).val = !![Real.exp t, 0; 0, Real.exp (-t)]) :
    HasDerivAt (fun t ↦ deriv (f ∣[k] e t ∘ ofComplex) I) ((k + 2) * deriv (f ∘ ofComplex) I +
      2 * Complex.I * deriv (deriv (f ∘ ofComplex)) I) 0 := by
  have hs : (fun t ↦ deriv (f ∣[k] e t ∘ ofComplex) I) = fun t ↦
      2 * Real.pi * Complex.I * (normalizedDerivOfComplex f ∣[k + 2] e t) I :=
    funext fun t ↦ by
      have hd : ((e t).det : ℝ) = 1 := by
        rw [GeneralLinearGroup.val_det_apply, he, det_fin_two_of, ← Real.exp_add]
        simp
      rw [deriv_slash_comp_ofComplex hf hd]
      simp [he]
  rw [hs]
  refine (hasDerivAt_slash_diagonal (normalizedDerivOfComplex_mdifferentiable hf I) he).const_mul _
    |>.congr_deriv ?_
  rw [deriv_normalizedDerivOfComplex_comp_ofComplex, normalizedDerivOfComplex]
  field_simp
  push_cast
  ring1

lemma classicalFun_mul_of_det_eq_one (hh : 0 < (h.det : ℝ)) (hm : (m.det : ℝ) = 1) :
    classicalFun k f (h * m) = ((√|(h.det : ℝ)| ^ (2 - k) : ℝ) : ℂ) * ((f ∣[k] h) ∣[k] m) I := by
  have hp : 0 < ((h * m).det : ℝ) := by
    rw [map_mul, Units.val_mul, hm, mul_one]
    exact hh
  rw [classicalFun_of_pos k f hp, normalizedSlash_mul, normalizedSlash, hm, abs_one, Real.sqrt_one,
    one_zpow, Complex.ofReal_one, one_mul]

lemma det_ratInfEquiv_sl2Exp : ((ratInfEquiv (sl2Exp b w)).det : ℝ) = 1 :=
  (ratMixedEquiv.map_det (sl2Exp b w).val).symm.trans <| by
    rw [← GeneralLinearGroup.val_det_apply, det_sl2Exp, Units.val_one, map_one]

lemma ratMixedEquiv_smul_realUnit : ratMixedEquiv (t • realUnit v) = t := by
  simp [ratMixedEquiv, realUnit, Subsingleton.elim _ v]

lemma val_ratInfEquiv_sl2Exp_zero :
    (ratInfEquiv (sl2Exp 0 (t • realUnit v))).val = !![Real.exp t, 0; 0, Real.exp (-t)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ratInfEquiv_apply, sl2Exp, mixedExp, ratMixedEquiv, realUnit, Subsingleton.elim _ v]

lemma val_ratInfEquiv_sl2Exp_one :
    (ratInfEquiv (sl2Exp 1 (t • realUnit v))).val = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratInfEquiv_apply, sl2Exp, ratMixedEquiv_smul_realUnit]

lemma val_ratInfEquiv_sl2Exp_two :
    (ratInfEquiv (sl2Exp 2 (t • realUnit v))).val = !![1, 0; t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratInfEquiv_apply, sl2Exp, ratMixedEquiv_smul_realUnit]

lemma adelicLift_eq_of_mul_ofInf_eq (hh₀ : 0 < (h₀.det : ℝ))
    (he : ∀ y, adelicLift N k f (g * ofInf ℚ y) = classicalFun k f (h₀ * ratInfEquiv y)) :
    adelicLift N k f g = ((√|(h₀.det : ℝ)| ^ (2 - k) : ℝ) : ℂ) * (f ∣[k] h₀) I := by
  have h₁ : adelicLift N k f g = classicalFun k f h₀ := by
    simpa using he 1
  rw [h₁, classicalFun_of_pos k f hh₀, normalizedSlash]

lemma lieDeriv_adelicLift_of_hasDerivAt (hh₀ : 0 < (h₀.det : ℝ))
    (he : ∀ y, adelicLift N k f (g * ofInf ℚ y) = classicalFun k f (h₀ * ratInfEquiv y))
    (hd : HasDerivAt (fun t : ℝ ↦ ((f ∣[k] h₀) ∣[k] ratInfEquiv (sl2Exp b (t • w))) I) d 0) :
    lieDeriv b w (adelicLift N k f) g = ((√|(h₀.det : ℝ)| ^ (2 - k) : ℝ) : ℂ) * d :=
  ((hd.const_mul _).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ by
    rw [he, classicalFun_mul_of_det_eq_one hh₀ det_ratInfEquiv_sl2Exp])).deriv

lemma lieDeriv_lieDeriv_adelicLift_of_hasDerivAt (hh : MDiff f) (hh₀ : 0 < (h₀.det : ℝ))
    (he : ∀ y, adelicLift N k f (g * ofInf ℚ y) = classicalFun k f (h₀ * ratInfEquiv y))
    (hd : HasDerivAt
      (fun t : ℝ ↦ deriv ((f ∣[k] h₀) ∣[k] ratInfEquiv (sl2Exp b (t • w)) ∘ ofComplex) I) d 0) :
    lieDeriv b w (lieDeriv 1 (realUnit v) (adelicLift N k f)) g =
      ((√|(h₀.det : ℝ)| ^ (2 - k) : ℝ) : ℂ) * d :=
  ((hd.const_mul _).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ by
    have hp : 0 < ((h₀ * ratInfEquiv (sl2Exp b (t • w))).det : ℝ) := by
      rw [map_mul, Units.val_mul, det_ratInfEquiv_sl2Exp, mul_one]
      exact hh₀
    rw [lieDeriv_adelicLift_of_hasDerivAt hp
      (fun y ↦ by rw [mul_assoc, ← map_mul, he, map_mul, mul_assoc])
      (hasDerivAt_slash_upper (hh.slash k _ I) (val_ratInfEquiv_sl2Exp_one v)), map_mul,
      Units.val_mul, det_ratInfEquiv_sl2Exp, mul_one, SlashAction.slash_mul])).deriv

/-- **The action of `F` on the adelic lift of a holomorphic function**: `F φ_f = E φ_f - i k φ_f`,
that is, `φ_f` has weight `k` under the generator `E - F` of the Lie algebra of the rotations. -/
lemma lieDeriv_two_adelicLift (hh : MDiff f)
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f) :
    lieDeriv 2 (realUnit v) (adelicLift N k f) = lieDeriv 1 (realUnit v) (adelicLift N k f) -
      (Complex.I * k) • adelicLift N k f :=
  funext fun g ↦ by
    rcases exists_adelicLift_mul_ofInf N hf g with ⟨h₀, hh₀, he⟩
    rw [Pi.sub_apply, Pi.smul_apply, lieDeriv_adelicLift_of_hasDerivAt hh₀ he
      (hasDerivAt_slash_lower (hh.slash k h₀ I) (val_ratInfEquiv_sl2Exp_two v)),
      lieDeriv_adelicLift_of_hasDerivAt hh₀ he
        (hasDerivAt_slash_upper (hh.slash k h₀ I) (val_ratInfEquiv_sl2Exp_one v)),
      adelicLift_eq_of_mul_ofInf_eq hh₀ he]
    ring1

/-- **The action of `H` on the adelic lift of a holomorphic function**:
`H φ_f = k φ_f + 2 i E φ_f`. With `AdelicGL2.lieDeriv_two_adelicLift`, this says that
`(H - i (E + F)) φ_f = 0`. -/
lemma lieDeriv_zero_adelicLift (hh : MDiff f)
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f) :
    lieDeriv 0 (realUnit v) (adelicLift N k f) = (k : ℂ) • adelicLift N k f +
      (2 * Complex.I) • lieDeriv 1 (realUnit v) (adelicLift N k f) :=
  funext fun g ↦ by
    rcases exists_adelicLift_mul_ofInf N hf g with ⟨h₀, hh₀, he⟩
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, lieDeriv_adelicLift_of_hasDerivAt hh₀ he
      (hasDerivAt_slash_diagonal (hh.slash k h₀ I) (val_ratInfEquiv_sl2Exp_zero v)),
      lieDeriv_adelicLift_of_hasDerivAt hh₀ he
        (hasDerivAt_slash_upper (hh.slash k h₀ I) (val_ratInfEquiv_sl2Exp_one v)),
      adelicLift_eq_of_mul_ofInf_eq hh₀ he]
    ring1

lemma lieDeriv_zero_lieDeriv_one_adelicLift (hh : MDiff f)
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f) :
    lieDeriv 0 (realUnit v) (lieDeriv 1 (realUnit v) (adelicLift N k f)) =
      ((k : ℂ) + 2) • lieDeriv 1 (realUnit v) (adelicLift N k f) +
        (2 * Complex.I) • lieDeriv 1 (realUnit v) (lieDeriv 1 (realUnit v) (adelicLift N k f)) :=
  funext fun g ↦ by
    rcases exists_adelicLift_mul_ofInf N hf g with ⟨h₀, hh₀, he⟩
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, lieDeriv_lieDeriv_adelicLift_of_hasDerivAt v
      hh hh₀ he (hasDerivAt_deriv_slash_diagonal (hh.slash k h₀) (val_ratInfEquiv_sl2Exp_zero v)),
      lieDeriv_lieDeriv_adelicLift_of_hasDerivAt v hh hh₀ he
        (hasDerivAt_deriv_slash_upper (hh.slash k h₀) (val_ratInfEquiv_sl2Exp_one v)),
      lieDeriv_adelicLift_of_hasDerivAt hh₀ he
        (hasDerivAt_slash_upper (hh.slash k h₀ I) (val_ratInfEquiv_sl2Exp_one v))]
    ring1

lemma lieDeriv_two_lieDeriv_one_adelicLift (hh : MDiff f)
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f) :
    lieDeriv 2 (realUnit v) (lieDeriv 1 (realUnit v) (adelicLift N k f)) =
      lieDeriv 1 (realUnit v) (lieDeriv 1 (realUnit v) (adelicLift N k f)) -
        (((k : ℂ) + 2) * Complex.I) • lieDeriv 1 (realUnit v) (adelicLift N k f) -
          (k : ℂ) • adelicLift N k f :=
  funext fun g ↦ by
    rcases exists_adelicLift_mul_ofInf N hf g with ⟨h₀, hh₀, he⟩
    rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply,
      lieDeriv_lieDeriv_adelicLift_of_hasDerivAt v hh hh₀ he
        (hasDerivAt_deriv_slash_lower (hh.slash k h₀) (val_ratInfEquiv_sl2Exp_two v)),
      lieDeriv_lieDeriv_adelicLift_of_hasDerivAt v hh hh₀ he
        (hasDerivAt_deriv_slash_upper (hh.slash k h₀) (val_ratInfEquiv_sl2Exp_one v)),
      lieDeriv_adelicLift_of_hasDerivAt hh₀ he
        (hasDerivAt_slash_upper (hh.slash k h₀ I) (val_ratInfEquiv_sl2Exp_one v)),
      adelicLift_eq_of_mul_ofInf_eq hh₀ he]
    ring1

/-- **The Casimir eigenvalue of the adelic lift**: for a holomorphic function `f` invariant under
`Γ₁(N)` in weight `k`, the Casimir operator `Ω = H² / 2 + E F + F E` at the real place of `ℚ` acts
on the adelic lift `φ_f` by the scalar `k (k - 2) / 2`. -/
lemma casimirReal_adelicLift (hh : MDiff f)
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f) :
    casimirReal v (adelicLift N k f) = ((k : ℂ) * (k - 2) / 2) • adelicLift N k f := by
  have hφ : IsSmoothAtInfinity (adelicLift N k f) := isSmoothAtInfinity_adelicLift hh hf
  have hφ₁ : IsSmoothAtInfinity (lieDeriv 1 (realUnit v) (adelicLift N k f)) := hφ.lieDeriv 1 _
  have h₁₂ : lieDeriv 1 (realUnit v) (lieDeriv 2 (realUnit v) (adelicLift N k f)) =
      lieDeriv 1 (realUnit v) (lieDeriv 1 (realUnit v) (adelicLift N k f)) -
        (Complex.I * k) • lieDeriv 1 (realUnit v) (adelicLift N k f) := by
    rw [lieDeriv_two_adelicLift v hh hf]
    exact funext fun g ↦ ((hφ₁.hasDerivAt 1 _ g).sub ((hφ.hasDerivAt 1 _ g).const_mul _)).deriv
  rw [casimirReal, casimirOf, h₁₂, lieDeriv_zero_adelicLift v hh hf,
    lieDeriv_add 0 _ (hφ.const_smul _) (hφ₁.const_smul _), lieDeriv_const_smul 0 _ _ hφ,
    lieDeriv_const_smul 0 _ _ hφ₁, lieDeriv_zero_adelicLift v hh hf,
    lieDeriv_zero_lieDeriv_one_adelicLift v hh hf, lieDeriv_two_lieDeriv_one_adelicLift v hh hf]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  linear_combination (2 * lieDeriv 1 (realUnit v) (lieDeriv 1 (realUnit v) (adelicLift N k f)) g) *
    Complex.I_sq

/-- **The adelic lift of a holomorphic function is finite under the Casimir operators**: it spans
a line of smooth functions stable under the Casimir operator at the real place of `ℚ`, which acts
on it by `k (k - 2) / 2`, and `ℚ` has no complex place. -/
lemma isCasimirFinite_adelicLift (hh : MDiff f)
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f) :
    IsCasimirFinite (adelicLift N k f) := by
  have hφ : IsSmoothAtInfinity (adelicLift N k f) := isSmoothAtInfinity_adelicLift hh hf
  refine ⟨Submodule.span ℂ {adelicLift N k f}, inferInstance, Submodule.mem_span_singleton_self _,
    fun ψ hψ ↦ ?_, fun u ψ hψ ↦ ?_, fun u ↦ ?_, fun u ↦ ?_⟩
  · rcases Submodule.mem_span_singleton.mp hψ with ⟨c, rfl⟩
    exact hφ.const_smul c
  · rcases Submodule.mem_span_singleton.mp hψ with ⟨c, rfl⟩
    rw [(isSmoothOperator_casimirReal u).smul c _ hφ, casimirReal_adelicLift u hh hf, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact absurd u.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal _))
  · exact absurd u.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal _))

end AdelicGL2
