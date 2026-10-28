import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.UpperHalfSpace
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The Siegel `Φ` operator

The Siegel `Φ` operator sends a function `f` on the Siegel upper half-space `ℋ_g` to the function
`Φ(f)(τ) = lim_{t → ∞} f(diag(τ, it))` on `ℋ_{g-1}`, where it exists. Here `ℋ_g` is indexed by
`l ⊕ Unit` and `ℋ_{g-1}` by `l`; the limit is taken coordinatewise, through every linear form on
the target space `V`, as in `SiegelUpperHalfSpace.SiegelOperatorVanishes`.

## Main definitions

* `SiegelUpperHalfSpace.phiPoint`: the point `diag(τ, it)` of `ℋ_g`.
* `SiegelUpperHalfSpace.HasSiegelPhi`: `F` is the limit `Φ(f)`.
* `SiegelUpperHalfSpace.siegelPhi` (LMFDB `mf.siegel.phi`): the Siegel `Φ` operator.

## Main results

* `SiegelUpperHalfSpace.siegelPhi_eq`: `Φ(f) = F` whenever `f(diag(τ, it))` tends to `F(τ)`.
* `SiegelUpperHalfSpace.HasSiegelPhi.add` and `SiegelUpperHalfSpace.HasSiegelPhi.const_smul`: `Φ`
  is linear where it is defined.
-/

open Filter Matrix Module
open scoped Topology

namespace SiegelUpperHalfSpace

private lemma posDef_fromBlocks {l : Type*} [Fintype l] {A : Matrix l l ℝ} (hA : A.PosDef) {s : ℝ}
    (hs : 0 < s) : (fromBlocks A 0 0 (diagonal fun _ : Unit ↦ s)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec] at hA ⊢
  refine ⟨hA.1.fromBlocks (by simp) (by simp), fun x hx ↦ ?_⟩
  have hq : star x ⬝ᵥ (fromBlocks A 0 0 (diagonal fun _ : Unit ↦ s) *ᵥ x) =
      (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + s * (x (Sum.inr ()) * x (Sum.inr ())) := by
    simp [dotProduct, mulVec]
    ring1
  rw [hq]
  rcases eq_or_ne (x ∘ Sum.inl) 0 with h | h
  · have hr : x (Sum.inr ()) ≠ 0 := fun hr ↦ hx <| funext fun i ↦ by
      rcases i with i | -
      · exact congrFun h i
      · exact hr
    rw [h, zero_dotProduct, zero_add]
    exact mul_pos hs <| mul_self_pos.mpr hr
  · simpa using add_pos_of_pos_of_nonneg (hA.2 h) (mul_nonneg hs.le <| mul_self_nonneg _)

variable {l : Type*} [Fintype l] (τ : SiegelUpperHalfSpace l) (t : Set.Ioi (0 : ℝ))
    {V : Type*} [AddCommGroup V] [Module ℂ V] (f g : SiegelUpperHalfSpace (l ⊕ Unit) → V)
    (F G : SiegelUpperHalfSpace l → V)

/-- The point `diag(τ, it)` of the Siegel upper half-space `ℋ_g`, indexed by `l ⊕ Unit`, for `τ`
in `ℋ_{g-1}` and `t > 0`. -/
def phiPoint : SiegelUpperHalfSpace (l ⊕ Unit) where
  val := fromBlocks τ.val 0 0 (diagonal fun _ ↦ (t : ℝ) * Complex.I)
  transpose_val := by
    rw [fromBlocks_transpose, τ.transpose_val, transpose_zero, transpose_zero,
      diagonal_transpose]
  posDef_im := by
    rw [fromBlocks_map, diagonal_map (by simp)]
    simpa using posDef_fromBlocks τ.posDef_im t.2

/-- The function `F : ℋ_{g-1} → V` is **the image `Φ(f)` of `f : ℋ_g → V` under the Siegel `Φ`
operator**: `f(diag(τ, it))` tends to `F(τ)` as `t → ∞`, for every `τ`. The limit is taken
coordinatewise, through every linear form on `V`, which is the limit in the usual topology when
`V` is finite-dimensional. -/
def HasSiegelPhi : Prop :=
  ∀ (τ : SiegelUpperHalfSpace l) (φ : Dual ℂ V),
    Tendsto (fun t ↦ φ (f (phiPoint τ t))) atTop (𝓝 (φ (F τ)))

open scoped Classical in
/-- The **Siegel `Φ` operator** (LMFDB `mf.siegel.phi`)
`Φ(f)(τ) = lim_{t → ∞} f(diag(τ, it))`, sending `f : ℋ_g → V` to a function on `ℋ_{g-1}`. The
limit is taken coordinatewise, through every linear form on `V`, and `Φ(f)(τ)` is `0` where it
does not exist. That it exists, and that `Φ` sends Siegel modular forms of degree `g` to Siegel
modular forms of degree `g - 1`, is a theorem which is not proved here. -/
noncomputable def siegelPhi : SiegelUpperHalfSpace l → V :=
  fun τ ↦ if h : ∃ v : V, ∀ φ : Dual ℂ V, Tendsto (fun t ↦ φ (f (phiPoint τ t))) atTop (𝓝 (φ v))
    then h.choose else 0

variable {f g F G}

/-- **`Φ(f) = F` whenever `f(diag(τ, it))` tends to `F(τ)`**, by uniqueness of limits, linear
forms separating the points of `V`. -/
lemma siegelPhi_eq (h : HasSiegelPhi f F) : siegelPhi f = F := by
  funext τ
  have hex : ∃ v : V, ∀ φ : Dual ℂ V, Tendsto (fun t ↦ φ (f (phiPoint τ t))) atTop (𝓝 (φ v)) :=
    ⟨F τ, h τ⟩
  simp only [siegelPhi, hex, ↓reduceDIte]
  refine sub_eq_zero.mp <| (forall_dual_apply_eq_zero_iff ℂ _).mp fun φ ↦ ?_
  rw [map_sub, tendsto_nhds_unique (hex.choose_spec φ) (h τ φ), sub_self]

/-- **`Φ` is additive** where it is defined. -/
lemma HasSiegelPhi.add (hf : HasSiegelPhi f F) (hg : HasSiegelPhi g G) :
    HasSiegelPhi (f + g) (F + G) :=
  fun τ φ ↦ by simpa using (hf τ φ).add (hg τ φ)

/-- **`Φ` is `ℂ`-linear** where it is defined. -/
lemma HasSiegelPhi.const_smul (hf : HasSiegelPhi f F) (c : ℂ) : HasSiegelPhi (c • f) (c • F) :=
  fun τ φ ↦ by simpa using (hf τ φ).const_mul c

end SiegelUpperHalfSpace
