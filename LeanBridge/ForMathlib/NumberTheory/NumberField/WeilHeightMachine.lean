import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilHeight
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.NumberTheory.Height.MvPolynomial

/-!
# Heights attached to maps into projective space

Besides the Weil heights of rational numbers, of algebraic numbers and of points of projective
space `ℙⁿ(K)` over a number field `K` (Mathlib's `Height.logHeight₁` and
`NumberField.absLogHeight₁`, and `Projectivization.absLogHeight`), the LMFDB knowl
`nf.weil_height` defines the height `h_L(P) = h(ι(P))` attached to a very ample line bundle `L` on
a projective variety `V`, through the embedding `ι : V ↪ ℙⁿ` given by a basis of the global
sections of `L`, and extends it to all line bundles by the linearity
`h_{L₁ ⊗ L₂} = h_{L₁} + h_{L₂}`.

Here the height attached to a map `φ : V → ℙⁿ(K)` is the pullback `h ∘ φ` of the height of
projective space, and the two facts that make the knowl's `h_L` meaningful are proved for it. The
embedding given by `L` depends on the choice of a basis of the sections of `L`, and another choice
composes it with a linear automorphism of `ℙⁿ`, which changes the height by a bounded function.
The products `s_i t_j` of the sections `s_i` of `L₁` and `t_j` of `L₂` are sections of `L₁ ⊗ L₂`,
and the map they give is the Segre map applied to the maps given by `L₁` and `L₂`, under which
heights add exactly.

Line bundles on projective varieties, the embeddings they give, and hence `h_L` itself, are not
available with the pinned Mathlib and Tau Ceti (the twisting sheaves `𝒪(1)` of `Proj` are only on
Tau Ceti's newer `main`); neither is the comparison of the Segre map with the embedding given by
the complete linear system of `L₁ ⊗ L₂`, which differ by a linear projection.

## Main definitions

* `Projectivization.segre`: the Segre map `ℙ(K^ι) × ℙ(K^ι') → ℙ(K^{ι × ι'})`.
* `Projectivization.linearMapHeightBound`: the bound `log |ι| + h(A) [K : ℚ]⁻¹` by which a linear
  map with matrix `A` can increase heights.
* `Projectivization.pullbackHeight` (LMFDB `nf.weil_height`): the height `h_φ = h ∘ φ` attached to a
  map `φ` into projective space.

## Main results

* `Projectivization.absLogHeight_mk_vecCons_one`: the height of `α ∈ K` is the height of the point
  `[α : 1]`, so that the knowl's heights of elements and of points agree.
* `Projectivization.segre_mk`: the Segre map is `([x], [y]) ↦ [(x_i y_j)_{i, j}]`.
* `Projectivization.absLogHeight_segre`: `h(segre(P, Q)) = h(P) + h(Q)`.
* `Projectivization.absLogHeight_map_le`: an injective linear map with matrix `A` increases heights
  by at most `log |ι| + h(A) [K : ℚ]⁻¹`.
* `Projectivization.abs_absLogHeight_mk_sub_le`: two points whose coordinates are linear
  combinations of each other, as the values of two spanning families of the sections of the same
  line bundle, have heights differing by a bounded amount.
* `Projectivization.abs_absLogHeight_map_sub_le`: in particular, a linear change of coordinates
  changes heights by a bounded amount.
* `Projectivization.pullbackHeight_segre` and `Projectivization.abs_pullbackHeight_smul_sub_le`:
  the same two facts for the heights attached to maps into projective space, the change of
  coordinates being the action of the general linear group.
-/

open Height Real

namespace Projectivization

variable {K : Type*} [Field K] {ι ι' V : Type*} {x : ι → K} {y : ι' → K}
  (P : Projectivization K (ι → K)) (Q : Projectivization K (ι' → K))

lemma fun_mul_ne_zero (hx : x ≠ 0) (hy : y ≠ 0) : (fun i : ι × ι' ↦ x i.1 * y i.2) ≠ 0 := by
  rcases Function.ne_iff.mp hx with ⟨i, hi⟩
  rcases Function.ne_iff.mp hy with ⟨j, hj⟩
  exact Function.ne_iff.mpr ⟨(i, j), mul_ne_zero hi hj⟩

/-- The **Segre map** `ℙ(K^ι) × ℙ(K^ι') → ℙ(K^{ι × ι'})`, `([x], [y]) ↦ [(x_i y_j)_{i, j}]`
(`Projectivization.segre_mk`). If `φ₁` and `φ₂` are the maps to projective space given by bases
`(s_i)` and `(t_j)` of the sections of line bundles `L₁` and `L₂`, then the products `s_i t_j` are
sections of `L₁ ⊗ L₂` and the map they give is `P ↦ segre (φ₁ P) (φ₂ P)`. -/
noncomputable def segre : Projectivization K (ι × ι' → K) :=
  mk K (fun i ↦ P.rep i.1 * Q.rep i.2) (fun_mul_ne_zero P.rep_nonzero Q.rep_nonzero)

/-- **The Segre map is `([x], [y]) ↦ [(x_i y_j)_{i, j}]`**, independently of the representatives. -/
lemma segre_mk (hx : x ≠ 0) (hy : y ≠ 0) :
    segre (mk K x hx) (mk K y hy) = mk K (fun i ↦ x i.1 * y i.2) (fun_mul_ne_zero hx hy) := by
  rcases exists_smul_eq_mk_rep K x hx with ⟨a, ha⟩
  rcases exists_smul_eq_mk_rep K y hy with ⟨b, hb⟩
  rw [segre, mk_eq_mk_iff']
  refine ⟨a * b, funext fun i ↦ ?_⟩
  rw [← ha, ← hb]
  simp only [Units.smul_def, Pi.smul_apply]
  ring1

variable [NumberField K] [Finite ι] [Finite ι']

/-- **The height of the Segre product of two points is the sum of their heights**, since
`max_{i, j} ‖x_i y_j‖_v = max_i ‖x_i‖_v max_j ‖y_j‖_v` at every place `v`: this is the linearity
`h_{L₁ ⊗ L₂} = h_{L₁} + h_{L₂}` of the knowl. -/
lemma absLogHeight_segre : (segre P Q).absLogHeight = P.absLogHeight + Q.absLogHeight := by
  rw [segre, absLogHeight_mk, logHeight_fun_mul_eq P.rep_nonzero Q.rep_nonzero, add_div,
    ← absLogHeight_mk P.rep_nonzero, ← absLogHeight_mk Q.rep_nonzero, mk_rep, mk_rep]

/-- **The height of an element `α` of `K` is the height of the point `[α : 1]`** of the projective
line: `(1 / [K : ℚ]) ∑_v [K_v : ℚ_v] log max(‖α‖_v, 1)`, the knowl's height of `α`, is the knowl's
height of the point `[α : 1]`. -/
lemma absLogHeight_mk_vecCons_one (α : K) :
    (mk K ![α, 1] (by simp)).absLogHeight = logHeight₁ α / Module.finrank ℚ K := by
  rw [absLogHeight_mk, logHeight₁_eq_logHeight]

variable (φ : V → Projectivization K (ι → K))

/-- The **Weil height** `h_φ = h ∘ φ` (LMFDB `nf.weil_height`) attached to a map `φ : V → ℙ(K^ι)`
into projective space over a number field `K`, `h` being the absolute logarithmic Weil height
`Projectivization.absLogHeight`. For the points `V` of a projective variety over `K` and the
embedding `φ` given by a basis of the sections of a very ample line bundle `L`, it is the height
`h_L` of the knowl. -/
noncomputable def pullbackHeight (v : V) : ℝ :=
  (φ v).absLogHeight

/-- **The height attached to the Segre product of two maps into projective space is the sum of
their heights**: the linearity `h_{L₁ ⊗ L₂} = h_{L₁} + h_{L₂}` of the knowl. -/
lemma pullbackHeight_segre (ψ : V → Projectivization K (ι' → K)) :
    pullbackHeight (fun v ↦ segre (φ v) (ψ v)) = pullbackHeight φ + pullbackHeight ψ :=
  funext fun v ↦ absLogHeight_segre (φ v) (ψ v)

variable [Fintype ι] [DecidableEq ι] (f : (ι → K) →ₗ[K] (ι' → K))

/-- The bound `log |ι| + h(A) / [K : ℚ]` by which a linear map `f : K^ι → K^ι'` with matrix `A`
can increase the absolute logarithmic heights of points of projective space, `h(A)` being the
logarithmic height of the tuple of the entries of `A`. -/
noncomputable def linearMapHeightBound : ℝ :=
  (totalWeight K * log (Nat.card ι) +
    Height.logHeight fun p : ι' × ι ↦ LinearMap.toMatrix' f p.1 p.2) / Module.finrank ℚ K

lemma absLogHeight_mk_apply_le (hx : x ≠ 0) (hy : f x ≠ 0) :
    (mk K (f x) hy).absLogHeight ≤ (mk K x hx).absLogHeight + linearMapHeightBound f := by
  have hfx : f x = fun j ↦ ∑ i, LinearMap.toMatrix' f j i * x i := by
    rw [← LinearMap.toMatrix'_mulVec]
    rfl
  have hle : Height.logHeight (f x) ≤ totalWeight K * log (Nat.card ι) +
      Height.logHeight (fun p : ι' × ι ↦ LinearMap.toMatrix' f p.1 p.2) + Height.logHeight x :=
    hfx ▸ logHeight_linearMap_apply_le (fun p : ι' × ι ↦ LinearMap.toMatrix' f p.1 p.2) x
  rw [absLogHeight_mk, absLogHeight_mk, linearMapHeightBound, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  linarith

/-- **An injective linear map with matrix `A` increases heights by at most
`log |ι| + h(A) / [K : ℚ]`.** -/
lemma absLogHeight_map_le (hf : Function.Injective f) :
    (map f hf P).absLogHeight ≤ P.absLogHeight + linearMapHeightBound f := by
  induction P using ind with
  | h x hx => exact absLogHeight_mk_apply_le f hx _

variable [Fintype ι'] [DecidableEq ι'] in
/-- **Two spanning families of the same space of sections give heights differing by a bounded
amount**: if the coordinates `A x` of a point are linear combinations of the coordinates `x` of
another, and conversely `x = B (A x)`, as for the values at a point of two spanning families of the
global sections of the same line bundle `L`, then the heights of `[A x]` and `[x]` differ by at
most `max(c(A), c(B))`, the bounds `Projectivization.linearMapHeightBound` of `A` and `B`. So the
height `h_L` attached to the complete linear system of `L` does not depend, up to a bounded
function, on the choice of a basis or of a spanning family of the sections of `L`. -/
lemma abs_absLogHeight_mk_sub_le (A : (ι → K) →ₗ[K] (ι' → K)) (B : (ι' → K) →ₗ[K] (ι → K))
    (hx : x ≠ 0) (hAx : A x ≠ 0) (hB : B (A x) = x) :
    |(mk K (A x) hAx).absLogHeight - (mk K x hx).absLogHeight| ≤
      max (linearMapHeightBound A) (linearMapHeightBound B) := by
  have h₁ : (mk K (A x) hAx).absLogHeight ≤ (mk K x hx).absLogHeight + linearMapHeightBound A :=
    absLogHeight_mk_apply_le A hx hAx
  have h₂ : (mk K x hx).absLogHeight ≤ (mk K (A x) hAx).absLogHeight + linearMapHeightBound B := by
    simpa only [hB] using absLogHeight_mk_apply_le B hAx (hB.symm ▸ hx)
  rw [abs_sub_le_iff]
  constructor
  · linarith [le_max_left (linearMapHeightBound A) (linearMapHeightBound B)]
  · linarith [le_max_right (linearMapHeightBound A) (linearMapHeightBound B)]

/-- **A linear change of coordinates changes heights by a bounded amount**: the height `h_L`
attached to a very ample line bundle `L` depends on the basis of the sections of `L` only up to a
bounded function. -/
lemma abs_absLogHeight_map_sub_le (e : (ι → K) ≃ₗ[K] (ι → K)) :
    |(map e.toLinearMap e.injective P).absLogHeight - P.absLogHeight| ≤
      max (linearMapHeightBound e.toLinearMap) (linearMapHeightBound e.symm.toLinearMap) := by
  induction P using ind with
  | h x hx => exact abs_absLogHeight_mk_sub_le _ _ hx _ (e.symm_apply_apply x)

/-- **The height attached to a map into projective space depends on the coordinates only up to a
bounded function**: composing the map with a linear automorphism of projective space, as when the
basis of the sections of a very ample line bundle `L` is changed, changes the height `h_L` by a
bounded amount. -/
lemma abs_pullbackHeight_smul_sub_le (g : LinearMap.GeneralLinearGroup K (ι → K)) (v : V) :
    |pullbackHeight (fun w ↦ g • φ w) v - pullbackHeight φ v| ≤
      max (linearMapHeightBound g.val) (linearMapHeightBound g⁻¹.val) :=
  abs_absLogHeight_map_sub_le (φ v) g.toLinearEquiv

end Projectivization
