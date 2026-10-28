import LeanBridge.ForMathlib.LinearAlgebra.Lattice.Universal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import TauCeti.LinearAlgebra.IntegralLattice.Unit

/-!
# Algebraic lattices

A lattice is algebraic (LMFDB `lattice.algebraic`) if it can be realized as a free `ℤ`-module in
an algebraic number field. The knowl does not say which bilinear form the number field carries;
we take the classical one for lattices of Euclidean space, as for the algebraic lattices of coding
theory: a number field `K` of degree `n` is embedded in `ℝⁿ = ℝ^{r₁} × ℂ^{r₂}` by its canonical
(Minkowski) embedding `σ`, and carries the Minkowski form `(x, y) ↦ ⟨σ(x), σ(y)⟩`, which is the
trace form `Tr_{K/ℚ}(xy)` when `K` is totally real. An integral lattice is then algebraic if it is
isometric to a free `ℤ`-module of rank `n` in `K` with the Minkowski form; its image under `σ` is
a lattice of `ℝⁿ`, an algebraic lattice in the sense of coding theory (Oggier and Viterbo).
Twisted embeddings, giving the forms `Tr_{K/ℚ}(αxy)` of Bayer-Fluckiger's ideal lattices, are not
included: the knowl realizes the lattice in the number field itself, and the twists would make the
class much larger, every lattice `⟨a⟩` of rank `1` with `a > 0` becoming algebraic, whereas with
the Minkowski form `⟨2⟩` is not, a lattice of rank `1` being realized in `ℚ`, as some `cℤ` of norm
`c²`. The Minkowski form being positive definite, an algebraic lattice is positive definite. The
lattice `ℤ` with the form `(x, y) ↦ xy` is algebraic, realized as `ℤ ⊆ ℚ`.

## Main definitions

* `NumberField.minkowskiForm`: the Minkowski form of a number field.
* `TauCeti.IntegralLattice.IsAlgebraic` (LMFDB `lattice.algebraic`).

## Main results

* `NumberField.minkowskiForm_eq_sum`: the Minkowski form is
  `∑_{w real} w(x) w(y) + ∑_{w complex} Re(w(y) w̄(x))`.
* `NumberField.minkowskiForm_self_pos`: the Minkowski form is positive definite.
* `NumberField.minkowskiForm_rat`: the Minkowski form of `ℚ` is `(x, y) ↦ xy`.
* `TauCeti.IntegralLattice.IsAlgebraic.isPosDef`: an algebraic lattice is positive definite.
* `TauCeti.IntegralLattice.isAlgebraic_unitLattice_unit`: the lattice `ℤ` with the form
  `(x, y) ↦ xy` is algebraic.
-/

open NumberField InfinitePlace mixedEmbedding
open scoped ComplexConjugate InnerProductSpace

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The **Minkowski form** `(x, y) ↦ ⟨σ(x), σ(y)⟩` of a number field `K`, where `σ` is the
canonical embedding of `K` in `ℝ^{r₁} × ℂ^{r₂}`, a Euclidean space of dimension `[K : ℚ]`. -/
noncomputable def minkowskiForm (x y : K) : ℝ :=
  ⟪(euclidean.toMixed K).symm (mixedEmbedding K x),
    (euclidean.toMixed K).symm (mixedEmbedding K y)⟫_ℝ

open scoped Classical in
/-- **The Minkowski form is `∑_{w real} w(x) w(y) + ∑_{w complex} Re(w(y) w̄(x))`**, with `w(x)`
the image of `x` under the embedding chosen for the infinite place `w`. -/
lemma minkowskiForm_eq_sum (x y : K) : minkowskiForm K x y =
    ∑ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 x * embedding_of_isReal w.2 y +
      ∑ w : {w : InfinitePlace K // IsComplex w},
        (w.1.embedding y * conj (w.1.embedding x)).re := by
  simp [minkowskiForm, euclidean.toMixed, PiLp.inner_apply, mul_comm]

variable {K} in
open scoped Classical in
/-- **The Minkowski form is positive definite.** -/
lemma minkowskiForm_self_pos {x : K} (hx : x ≠ 0) : 0 < minkowskiForm K x x := by
  rw [minkowskiForm, real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr ((map_ne_zero_iff _ (euclidean.toMixed K).symm.injective).mpr
    ((map_ne_zero_iff _ (mixedEmbedding_injective K)).mpr hx))) 2

/-- **The Minkowski form of `ℚ` is `(x, y) ↦ xy`.** -/
lemma minkowskiForm_rat (x y : ℚ) : minkowskiForm ℚ x y = x * y := by
  classical
  have : IsEmpty {w : InfinitePlace ℚ // IsComplex w} := ⟨fun w ↦ not_isComplex_iff_isReal.mpr
    (Subsingleton.elim Rat.infinitePlace w.1 ▸ Rat.isReal_infinitePlace) w.2⟩
  have hcard : Fintype.card {w : InfinitePlace ℚ // IsReal w} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩,
      fun w ↦ Subtype.ext (Subsingleton.elim _ _)⟩
  rw [minkowskiForm_eq_sum]
  simp [hcard]

end NumberField

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- An integral lattice `L` is **algebraic** (LMFDB `lattice.algebraic`) if it can be realized as
a free `ℤ`-module of full rank in a number field `K` with its Minkowski form: there is an injective
`ℤ`-linear map `f : L → K` whose image spans `K` over `ℚ` and which carries the form `B` of `L` to
the Minkowski form, `B(x, y) = ⟨σ(f x), σ(f y)⟩` for the canonical embedding `σ` of `K` in
`ℝ^{[K : ℚ]}`. -/
def IsAlgebraic : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (f : L →ₗ[ℤ] K), Function.Injective f ∧
    Submodule.span ℚ (Set.range f) = ⊤ ∧
      ∀ x y : L, (L.integralForm x y : ℝ) = minkowskiForm K (f x) (f y)

variable {L} in
/-- **An algebraic lattice is positive definite.** -/
lemma IsAlgebraic.isPosDef (hL : L.IsAlgebraic) : L.IsPosDef := by
  rcases hL with ⟨K, _, _, f, hf, -, hform⟩
  refine L.isPosDef_iff.mpr fun v hv ↦ ?_
  rcases L.exists_zsmul_mem_carrier v with ⟨n, hn, hmem⟩
  have hn' : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hx : (⟨n • v, hmem⟩ : L) ≠ 0 := fun h ↦ smul_ne_zero hn' hv <| by
    rw [Int.cast_smul_eq_zsmul]
    exact congrArg Subtype.val h
  have hpos : (0 : ℝ) < L.integralNorm ⟨n • v, hmem⟩ := by
    rw [integralNorm_apply, hform]
    exact minkowskiForm_self_pos ((map_ne_zero_iff f hf).mpr hx)
  have hpos' : (0 : ℚ) < (n : ℚ) ^ 2 * L.form v v :=
    L.integralNorm_mk_zsmul hmem ▸ (by exact_mod_cast hpos)
  exact pos_of_mul_pos_right hpos' (sq_nonneg _)

/-- **The lattice `ℤ` with the form `(x, y) ↦ xy`, Tau Ceti's `unitLattice Unit`, is algebraic**,
realized as `ℤ ⊆ ℚ`. -/
lemma isAlgebraic_unitLattice_unit : (unitLattice Unit).IsAlgebraic := by
  let f : unitLattice Unit →ₗ[ℤ] ℚ :=
    ((LinearMap.proj () : (Unit → ℚ) →ₗ[ℚ] ℚ).restrictScalars ℤ).comp
      (unitLattice Unit).carrier.subtype
  refine ⟨ℚ, inferInstance, inferInstance, f, fun x y hxy ↦ Subtype.ext (funext fun _ ↦ hxy),
    eq_top_iff.mpr fun q _ ↦ ?_, fun x y ↦ ?_⟩
  · have h1 : (1 : ℚ) ∈ Set.range f := ⟨unitLatticeBasis Unit (), by simp [f]⟩
    simpa using Submodule.smul_mem _ q (Submodule.subset_span h1)
  · rw [minkowskiForm_rat, ← Rat.cast_mul, ← Rat.cast_intCast, integralForm_cast,
      unitLattice_form_apply, Fintype.sum_unique]
    rfl

end TauCeti.IntegralLattice
