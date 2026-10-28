import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.Level
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic

/-!
# Hilbert modular forms

Let `F` be a totally real number field of degree `n > 1` with real places `v₁, …, vₙ`. An element
`γ = (a, b; c, d)` of `GL₂(F)` whose determinant is totally positive acts on `ℍⁿ` by
`γ z = ((v₁(a) z₁ + v₁(b)) / (v₁(c) z₁ + v₁(d)), …)`, and for a weight `k = (k₁, …, kₙ)` its
automorphy factor is `∏ᵢ (vᵢ(c) zᵢ + vᵢ(d)) ^ kᵢ · vᵢ(det γ) ^ (-kᵢ / 2)`. For a nonzero ideal `𝔑`
of `𝒪_F` and an invertible fractional ideal `𝔟`, the group `Γ₀(𝔑)_𝔟` is
`HilbertModularGroup.gammaZero 𝔟 (HilbertModularGroup.glPlus 𝔟) 𝔑`: the matrices with `a, d ∈ 𝒪_F`,
`b ∈ 𝔟⁻¹`, `c ∈ 𝔑𝔟` and totally positive unit determinant. A Hilbert modular form of weight `k` and
level `𝔑` is a tuple `(f_𝔟)` of holomorphic functions on `ℍⁿ`, indexed by representatives `𝔟` of
the narrow class group, with `f_𝔟(γ z)` equal to the automorphy factor times `f_𝔟(z)` for
`γ ∈ Γ₀(𝔑)_𝔟`; it is a cusp form if each `f_𝔟` vanishes at every cusp.

Holomorphy at the cusps is imposed as boundedness of every slash `f ∣ α`, `α ∈ SL₂(F)`, when all
the imaginary parts tend to infinity: for `n > 1` it is automatic (Koecher principle), as the LMFDB
assumes, and for `n = 1` it is needed, as otherwise unbounded functions such as `exp ∘ j` would be
modular forms. Vanishing
at the cusps is formalised as: for every `α ∈ SL₂(F)`, the slash `f ∣ α` tends to `0` when all the
imaginary parts tend to infinity, which says that the constant term of the Fourier expansion of `f`
at the cusp `α ∞` vanishes; every cusp is of this form.

The real places are indexed by `{w : InfinitePlace F // w.IsReal}`, and the definitions make sense
for every number field; the LMFDB's restrictions (`F` totally real of degree `n > 1`, weights
`kᵢ ≥ 2` of the same parity, integral representatives `𝔟`) are not imposed.

## Main definitions

* `HilbertModularForm.smul`: the action of `GL₂(F)` on `ℍⁿ`.
* `HilbertModularForm.automorphyFactor`: the automorphy factor of weight `k`.
* `HilbertModularForm.IsHolomorphic`: holomorphy on `ℍⁿ`.
* `HilbertModularForm.IsBoundedAtCusps`: boundedness at every cusp.
* `HilbertModularForm.VanishesAtCusps`: vanishing at every cusp.
* `HilbertModularForm` (LMFDB `mf.hilbert`): Hilbert modular forms of weight `k` and level `𝔑`.
* `HilbertModularForm.IsCuspForm` (LMFDB `mf.hilbert`): Hilbert cusp forms.
* `HilbertModularForm.level` and `HilbertModularForm.levelNorm` (LMFDB `mf.hilbert.level_norm`).
* `HilbertModularForm.weight` and `HilbertModularForm.IsParallelWeight` (LMFDB
  `mf.hilbert.weight_vector`).

## Main results

* `HilbertModularForm.coe_smul_apply`: the action is by Möbius transformations through the real
  places on matrices with totally positive determinant.
* `HilbertModularForm.automorphyFactor_ne_zero`: the automorphy factor of such a matrix is nonzero.
-/

open Filter Matrix NumberField InfinitePlace UpperHalfPlane Topology
open scoped nonZeroDivisors

variable {F : Type*} [Field F]

namespace HilbertModularForm

variable (k : {w : InfinitePlace F // w.IsReal} → ℤ) (g : GL (Fin 2) F)
  (z : {w : InfinitePlace F // w.IsReal} → ℍ) (f : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)

/-- The image of a matrix of `GL₂(F)` in `GL₂(ℝ)` under the real place `w`. -/
noncomputable def mapGL (w : {w : InfinitePlace F // w.IsReal}) : GL (Fin 2) F →* GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (embedding_of_isReal w.2)

/-- The action of `GL₂(F)` on `ℍⁿ`, `n` the number of real places of `F`: the matrix `g` acts on
the coordinate of the real place `w` through its image `w(g)` in `GL₂(ℝ)`. -/
noncomputable def smul : {w : InfinitePlace F // w.IsReal} → ℍ :=
  fun w ↦ mapGL w g • z w

lemma det_mapGL_pos (hg : IsTotallyPositive g.det.val) (w : {w : InfinitePlace F // w.IsReal}) :
    0 < (mapGL w g).det.val :=
  (hg w.1 w.2).trans_eq (RingHom.map_det _ _)

/-- **On a matrix with totally positive determinant, the action is the Möbius action through the
real places.** -/
lemma coe_smul_apply (hg : IsTotallyPositive g.det.val) (w : {w : InfinitePlace F // w.IsReal}) :
    (smul g z w : ℂ) = num (mapGL w g) (z w) / denom (mapGL w g) (z w) :=
  coe_smul_of_det_pos (det_mapGL_pos g hg w) (z w)

variable [NumberField F]

open scoped Classical in
/-- The **automorphy factor** of weight `k = (k_w)` of `g = (a, b; c, d)` at `z ∈ ℍⁿ`:
`∏_w (w(c) z_w + w(d)) ^ k_w · w(det g) ^ (-k_w / 2)`, the power of `w(det g)` being the real power,
as in the LMFDB's transformation law (LMFDB `mf.hilbert`). -/
noncomputable def automorphyFactor : ℂ :=
  ∏ w, denom (mapGL w g) (z w) ^ k w *
    ((embedding_of_isReal w.2 g.det.val ^ (-(k w : ℝ) / 2) : ℝ) : ℂ)

/-- A function on `ℍⁿ` is **holomorphic** if it is complex differentiable on the open subset `ℍⁿ`
of `ℂⁿ`. -/
def IsHolomorphic : Prop :=
  DifferentiableOn ℂ (fun z : {w : InfinitePlace F // w.IsReal} → ℂ ↦ f fun w ↦ ofComplex (z w))
    {z | ∀ w, 0 < (z w).im}

/-- The filter on `ℍⁿ` along which all the imaginary parts tend to infinity. -/
def atImInfty : Filter ({w : InfinitePlace F // w.IsReal} → ℍ) :=
  comap (fun z w ↦ (z w).im) (pi fun _ ↦ atTop)

/-- The slash `f ∣ₖ g` of a function on `ℍⁿ` by `g ∈ GL₂(F)`:
`z ↦ (automorphyFactor k g z)⁻¹ f(g z)`. -/
noncomputable def slash : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ :=
  fun z ↦ (automorphyFactor k g z)⁻¹ * f (smul g z)

/-- A function `f` on `ℍⁿ` is **bounded at the cusps** in weight `k` if for every `α ∈ SL₂(F)` the
slash `f ∣ₖ α` is bounded as all the imaginary parts tend to infinity. -/
def IsBoundedAtCusps : Prop :=
  ∀ α : GL (Fin 2) F, α.det = 1 → BoundedAtFilter atImInfty (slash k α f)

/-- A function `f` on `ℍⁿ` **vanishes at the cusps** in weight `k` if for every `α ∈ SL₂(F)` the
slash `f ∣ₖ α` tends to `0` as all the imaginary parts tend to infinity, that is, the constant term
of the Fourier expansion of `f` at every cusp `α ∞` vanishes. -/
def VanishesAtCusps : Prop :=
  ∀ α : GL (Fin 2) F, α.det = 1 → Tendsto (slash k α f) atImInfty (𝓝 0)

open scoped Classical in
/-- **The automorphy factor of a matrix with totally positive determinant is nonzero.** -/
lemma automorphyFactor_ne_zero (hg : IsTotallyPositive g.det.val) : automorphyFactor k g z ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun (w : {w : InfinitePlace F // w.IsReal}) _ ↦
    mul_ne_zero (zpow_ne_zero _ (denom_ne_zero _ _)) <|
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hg w.1 w.2) _).ne'

end HilbertModularForm

variable [NumberField F]

/-- A **Hilbert modular form** (LMFDB `mf.hilbert`) of weight `k = (k_w)` and level `𝔑`, relative
to a family `𝔟` of representatives of the narrow class group of `F` (`h𝔟`): a tuple `(f_c)` of
holomorphic functions on `ℍⁿ`, indexed by the narrow classes `c`, bounded at the cusps, such that
`f_c(γ z) = automorphyFactor k γ z · f_c(z)` for every `γ ∈ Γ₀(𝔑)_{𝔟 c}`. Boundedness at the cusps
is automatic in degree `n > 1` (Koecher principle), which the LMFDB assumes; it is imposed so that
the definition is also right in degree `1`. The LMFDB's further restrictions (`F` totally real,
`kᵢ ≥ 2` of the same parity, integral representatives) are not imposed. As for any trivial
character, a unit `u` with `∏ᵢ sign(vᵢ(u)) ^ kᵢ = -1` (acting through the scalar matrix `u`) forces
every form of weight `k` to vanish. -/
structure HilbertModularForm (𝔑 : Ideal (𝓞 F)) (k : {w : InfinitePlace F // w.IsReal} → ℤ)
    (𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c)
    where
  /-- The component `f_c` of the tuple. -/
  toFun : NarrowClassGroup F → ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ
  isHolomorphic (c : NarrowClassGroup F) : HilbertModularForm.IsHolomorphic (toFun c)
  isBoundedAtCusps (c : NarrowClassGroup F) : HilbertModularForm.IsBoundedAtCusps k (toFun c)
  smul_eq (c : NarrowClassGroup F) :
    ∀ γ ∈ HilbertModularGroup.gammaZero (𝔟 c : FractionalIdeal (𝓞 F)⁰ F)
      (HilbertModularGroup.glPlus (𝔟 c : FractionalIdeal (𝓞 F)⁰ F)) 𝔑,
      ∀ z, toFun c (HilbertModularForm.smul γ z) =
        HilbertModularForm.automorphyFactor k γ z * toFun c z

namespace HilbertModularForm

variable {𝔑 : Ideal (𝓞 F)} {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ} {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c}
  (f : HilbertModularForm 𝔑 k 𝔟 h𝔟)

/-- A Hilbert modular form is a **Hilbert cusp form** (LMFDB `mf.hilbert`) if each of its
components vanishes at every cusp. -/
def IsCuspForm : Prop :=
  ∀ c, VanishesAtCusps k (f.toFun c)

/-- The **level** (LMFDB `mf.hilbert.level_norm`) of a Hilbert modular form: the nonzero ideal `𝔑`
of `𝒪_F` determining the groups `Γ₀(𝔑)_𝔟` under which it transforms. Its LMFDB label is a database
convention, not formalised. -/
def level (_ : HilbertModularForm 𝔑 k 𝔟 h𝔟) : Ideal (𝓞 F) :=
  𝔑

/-- The **level norm** (LMFDB `mf.hilbert.level_norm`) of a Hilbert modular form: the absolute norm
of its level. -/
noncomputable def levelNorm : ℕ :=
  Ideal.absNorm f.level

/-- The **weight** (LMFDB `mf.hilbert.weight_vector`) of a Hilbert modular form: the vector
`(k_w)` of integers, indexed by the real places, of its transformation law. -/
def weight (_ : HilbertModularForm 𝔑 k 𝔟 h𝔟) : {w : InfinitePlace F // w.IsReal} → ℤ :=
  k

/-- A Hilbert modular form has **parallel weight** `m` (LMFDB `mf.hilbert.weight_vector`) if all
the entries of its weight are equal to `m`. -/
def IsParallelWeight (m : ℤ) : Prop :=
  ∀ w, f.weight w = m

end HilbertModularForm
