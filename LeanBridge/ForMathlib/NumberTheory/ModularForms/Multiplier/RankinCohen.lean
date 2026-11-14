import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.DerivativeLaw
import LeanBridge.ForMathlib.RingTheory.Derivation.RankinCohen
import TauCeti.Order.Filter.ZeroAndBoundedAtFilter

/-!
# The Rankin–Cohen brackets of modular forms

For modular forms `f` and `g` of weights `k` and `ℓ` and multiplier systems `v` and `w` on a
subgroup `Γ` of `SL(2, ℝ)`, the `n`-th Rankin–Cohen bracket
`[f, g]ₙ = ∑_{r + s = n} (-1)^r C(k + n - 1, s) C(ℓ + n - 1, r) f^(r) g^(s)`
(`ModularForm.rankinCohenBracket`) is a modular form of weight `k + ℓ + 2n` and multiplier system
`v w`. This is Cohen's theorem. For `n = 1` it is the modularity of `ℓ f' g - k f g'`, which is a
special case of this series of bilinear operators, the Rankin–Cohen operators (LMFDB
`mf.gl2.history.new`). The derivatives are taken with respect to `z`, so `[f, g]ₙ` is `(2πi)^n`
times the bracket in Zagier's normalisation, which uses `D = (2πi)⁻¹ d/dz`.

The bracket commutes with the slash action of the matrices `γ = (a, b; c, d)` of determinant `1`.
Indeed the holomorphic functions on the upper half-plane form a differential ring, in which the
function `x = c / (cz + d)` satisfies `x' = -x²`, and the slashes `f^(r) ∣[k + 2r] γ` of the
derivatives of `f` are the iterated covariant derivatives of `f ∣[k] γ`, by the formula for the
derivative of a slash. So the bracket of the slashes of the derivatives is the bracket of
`f ∣[k] γ` and `g ∣[ℓ] γ` (`Differential.aeval_rankinCohenPoly`).

## Main definitions

* `ModularForm.holomorphicSubalgebra`: the algebra of holomorphic functions on the upper
  half-plane, a differential ring for the derivative `f ↦ f'` (the instance
  `Differential holomorphicSubalgebra`).
* `ModularForm.slashDefect`: the holomorphic function `z ↦ c / (cz + d)`.

## Main results

* `ModularForm.rankinCohenBracket_slash`: `[f, g]ₙ ∣[k + ℓ + 2n] γ = [f ∣[k] γ, g ∣[ℓ] γ]ₙ` for
  holomorphic `f` and `g` and `γ` of determinant `1`.
* `ModularForm.rankinCohenBracket_mem_multiplierSpace`: Cohen's theorem.

## References

* H. Cohen, *Sums involving the values at negative integers of L-functions of quadratic
  characters*, Math. Ann. 217 (1975), 271–285.
* D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer, 2008, §5.2.
-/

open Derivative Filter Finset Polynomial Subgroup UpperHalfPlane

open scoped Differential Manifold

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {v w : Γ →* Circle} {k l : ℤ} {f g : ℍ → ℂ}
  {α : GL (Fin 2) ℝ} (n r : ℕ) (c d : ℂ)

lemma rankinCohenBracket_eq_sum_antidiagonal : rankinCohenBracket k l f g n = ∑ p ∈ antidiagonal n,
    ((-1) ^ p.1 * Ring.choose (k + n - 1) p.2 * Ring.choose (l + n - 1) p.1 : ℤ) •
      (derivOfComplex^[p.1] f * derivOfComplex^[p.2] g) :=
  (Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
    ((-1) ^ i * Ring.choose (k + n - 1) j * Ring.choose (l + n - 1) i : ℤ) •
      (derivOfComplex^[i] f * derivOfComplex^[j] g)) n).symm

lemma rankinCohenBracket_smul_smul :
    rankinCohenBracket k l (c • f) (d • g) n = (c * d) • rankinCohenBracket k l f g n := by
  simp only [rankinCohenBracket, iterate_derivOfComplex_const_smul, smul_mul_smul_comm, smul_sum]
  exact sum_congr rfl fun i _ ↦ smul_comm _ _ _

lemma mdifferentiable_rankinCohenBracket (hf : MDiff f) (hg : MDiff g) :
    MDiff (rankinCohenBracket k l f g n) := by
  simp only [rankinCohenBracket, ← Int.cast_smul_eq_zsmul ℂ]
  exact MDifferentiable.sum fun i _ ↦ ((mdifferentiable_iterate_derivOfComplex i hf).mul
    (mdifferentiable_iterate_derivOfComplex (n - i) hg)).const_smul _

lemma isBoundedAtImInfty_rankinCohenBracket (hf : MDiff f) (hg : MDiff g)
    (hbf : IsBoundedAtImInfty f) (hbg : IsBoundedAtImInfty g) :
    IsBoundedAtImInfty (rankinCohenBracket k l f g n) := by
  simp only [rankinCohenBracket]
  exact BoundedAtFilter.sum fun i _ ↦ ((isBoundedAtImInfty_iterate_derivOfComplex i hf hbf).mul
    (isBoundedAtImInfty_iterate_derivOfComplex (n - i) hg hbg)).const_smul_left _

/-- The **algebra of holomorphic functions** on the upper half-plane. With the derivative
`f ↦ f'` it is a differential ring. -/
def holomorphicSubalgebra : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | MDiff f}
  mul_mem' hf hg := hf.mul hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' _ := mdifferentiable_const

noncomputable instance : Differential holomorphicSubalgebra where
  deriv := Derivation.mk' (AddMonoidHom.toIntLinearMap <| AddMonoidHom.mk'
    (fun f ↦ ⟨derivOfComplex f, mdifferentiable_derivOfComplex f.2⟩)
    fun f g ↦ Subtype.ext <| derivOfComplex_add f.2 g.2) fun f g ↦ Subtype.ext <| by
      simpa [add_comm, mul_comm] using derivOfComplex_mul f.2 g.2

namespace holomorphicSubalgebra

variable (a b : holomorphicSubalgebra)

lemma coe_deriv : ↑a′ = derivOfComplex a :=
  rfl

lemma coe_iterate_deriv :
    ↑((Differential.deriv : holomorphicSubalgebra → holomorphicSubalgebra)^[r] a) =
      derivOfComplex^[r] a := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', coe_deriv, ih, Function.iterate_succ_apply']

lemma coe_rankinCohenBracket :
    ↑(Differential.rankinCohenBracket k l a b n) = rankinCohenBracket k l a b n := by
  rw [rankinCohenBracket_eq_sum_antidiagonal, Differential.rankinCohenBracket]
  simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul, Subalgebra.coe_mul,
    coe_iterate_deriv]

end holomorphicSubalgebra

variable (α) in
/-- The holomorphic function `z ↦ c / (cz + d)` on the upper half-plane, for `γ = (a, b; c, d)`:
the defect of the derivative of a slash,
`(f ∣[k] γ)' = f' ∣[k + 2] γ - k (c / (cz + d)) (f ∣[k] γ)`. -/
noncomputable def slashDefect : holomorphicSubalgebra :=
  ⟨fun z ↦ (α 1 0 : ℂ) / denom α z,
    mdifferentiable_const.div (mdifferentiable_denom α) (denom_ne_zero α)⟩

lemma deriv_slashDefect : (slashDefect α)′ = -slashDefect α ^ 2 := by
  refine Subtype.ext <| funext fun z ↦ ?_
  have h : HasDerivAt (fun w : ℂ ↦ (α 1 0 : ℂ) * denom α w ^ (-1 : ℤ))
      ((α 1 0 : ℂ) * (((-1 : ℤ) : ℂ) * α 1 0 * denom α z ^ ((-1 : ℤ) - 1))) z :=
    (hasDerivAt_denom_zpow α (-1) z).const_mul _
  have he : (fun z : ℍ ↦ (α 1 0 : ℂ) / denom α z) ∘ ofComplex =ᶠ[nhds (z : ℂ)]
      fun w ↦ (α 1 0 : ℂ) * denom α w ^ (-1 : ℤ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp [ofComplex_apply_of_im_pos hw, div_eq_mul_inv]
  have hd : denom α z ≠ 0 := denom_ne_zero α z
  have h2 : denom α z ^ ((-1 : ℤ) - 1) = (denom α z ^ 2)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg (denom α z)]
    rfl
  refine (he.deriv_eq.trans h.deriv).trans ?_
  simp only [h2, NegMemClass.coe_neg, SubmonoidClass.coe_pow, Pi.neg_apply, Pi.pow_apply,
    slashDefect]
  field_simp
  push_cast
  ring1

lemma coe_aeval_weightDerivPoly (hf : MDiff f) (hα : α.det = 1) :
    ↑(aeval (slashDefect α) (Differential.weightDerivPoly k
      (⟨f ∣[k] α, hf.slash k α⟩ : holomorphicSubalgebra) r)) =
      derivOfComplex^[r] f ∣[k + 2 * r] α := by
  induction r with
  | zero => simp [Differential.weightDerivPoly_zero]
  | succ r ih =>
    have hw : k + 2 * ((r + 1 : ℕ) : ℤ) = k + 2 * r + 2 := by
      push_cast
      ring1
    rw [Differential.aeval_weightDerivPoly_succ k _ r deriv_slashDefect, hw,
      Function.iterate_succ_apply',
      eq_add_of_sub_eq (derivOfComplex_slash (mdifferentiable_iterate_derivOfComplex r hf) hα).symm,
      ← ih]
    ext z
    simp only [Subalgebra.coe_add, AddSubgroupClass.coe_zsmul, Subalgebra.coe_mul,
      holomorphicSubalgebra.coe_deriv, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, slashDefect]
    rw [zsmul_eq_mul]
    ring1

lemma coe_aeval_rankinCohenPoly (hf : MDiff f) (hg : MDiff g) (hα : α.det = 1) :
    ↑(aeval (slashDefect α) (Differential.rankinCohenPoly k l
      (⟨f ∣[k] α, hf.slash k α⟩ : holomorphicSubalgebra) ⟨g ∣[l] α, hg.slash l α⟩ n)) =
      rankinCohenBracket k l f g n ∣[k + l + 2 * n] α := by
  simp only [Differential.rankinCohenPoly, map_sum, map_zsmul, map_mul,
    AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul, Subalgebra.coe_mul,
    coe_aeval_weightDerivPoly _ hf hα, coe_aeval_weightDerivPoly _ hg hα,
    rankinCohenBracket_eq_sum_antidiagonal]
  ext z
  have hd : α.det.val = 1 := congrArg Units.val hα
  rw [slash_apply_of_det_eq_one hd, Finset.sum_apply, Finset.sum_apply, sum_mul]
  refine sum_congr rfl fun p hp ↦ ?_
  have hz : denom α z ^ (-(k + l + 2 * (n : ℤ))) =
      denom α z ^ (-(k + 2 * (p.1 : ℤ))) * denom α z ^ (-(l + 2 * (p.2 : ℤ))) := by
    rw [← zpow_add₀ (denom_ne_zero α z), ← mem_antidiagonal.mp hp]
    congr 1
    push_cast
    ring1
  simp only [Pi.smul_apply, Pi.mul_apply, slash_apply_of_det_eq_one hd, hz]
  ring1

/-- **The Rankin–Cohen brackets commute with the slash action**: for holomorphic `f` and `g` and
`γ` of determinant `1`, `[f, g]ₙ ∣[k + ℓ + 2n] γ = [f ∣[k] γ, g ∣[ℓ] γ]ₙ`. -/
lemma rankinCohenBracket_slash (hf : MDiff f) (hg : MDiff g) (hα : α.det = 1) :
    rankinCohenBracket k l f g n ∣[k + l + 2 * n] α =
      rankinCohenBracket k l (f ∣[k] α) (g ∣[l] α) n := by
  have : HasUniqueDiv holomorphicSubalgebra := .of_module_rat _
  rw [← coe_aeval_rankinCohenPoly n hf hg hα, Differential.aeval_rankinCohenPoly,
    holomorphicSubalgebra.coe_rankinCohenBracket]

/-- **Cohen's theorem**: if `f` and `g` are modular forms on `Γ` of weights `k` and `ℓ` and
multiplier systems `v` and `w`, then their `n`-th Rankin–Cohen bracket `[f, g]ₙ` is a modular form
of weight `k + ℓ + 2n` and multiplier system `v w`. For `n = 1` this is the modularity of
`ℓ f' g - k f g'` (LMFDB `mf.gl2.history.new`), by `rankinCohenBracket_one`. -/
lemma rankinCohenBracket_mem_multiplierSpace (hf : f ∈ multiplierSpace k v)
    (hg : g ∈ multiplierSpace l w) :
    rankinCohenBracket k l f g n ∈ multiplierSpace (k + l + 2 * n) (v * w) := by
  refine ⟨mdifferentiable_rankinCohenBracket n hf.1 hg.1, fun γ ↦ ?_, fun {c} hc ↦ ?_⟩
  · rw [rankinCohenBracket_slash n hf.1 hg.1 (HasDetOne.det_eq γ.2), hf.2.1, hg.2.1,
      rankinCohenBracket_smul_smul, MonoidHom.mul_apply, Circle.coe_mul]
  · rcases c.exists_mem_SL2 ℝ with ⟨δ, rfl⟩
    rw [OnePoint.isBoundedAt_iff rfl, rankinCohenBracket_slash n hf.1 hg.1 (by simp)]
    exact isBoundedAtImInfty_rankinCohenBracket n (hf.1.slash k _) (hg.1.slash l _)
      (hf.2.2 hc _ rfl) (hg.2.2 hc _ rfl)

end ModularForm
