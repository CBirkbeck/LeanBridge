import LeanBridge.ForMathlib.Algebra.Module.ZLattice.Arithmetic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Arithmetic lattices in real quadratic spaces

A lattice (LMFDB `lattice.definition`) is a finitely generated discrete `ℤ`-submodule `L` of a real
quadratic space `(V, B)`, `B` a nonsingular symmetric bilinear form of any signature, and it is
integral if `B(L, L) ⊆ ℤ`. Lattices `L ⊆ (V, B)` and `M ⊆ (W, B')` are similar (LMFDB
`lattice.similarity`) if `L` is isometric to `αM` for a real constant `α ≠ 0`, and `L` is
arithmetic (LMFDB `lattice.arithmetic`) if it is similar to an integral lattice.

Scaling a lattice by `α` multiplies its form by `α²`, so a lattice similar to an integral lattice
satisfies `c B(L, L) ⊆ ℤ` for `c = α⁻² > 0`, in whatever quadratic space the integral lattice lies;
conversely, if `c B(L, L) ⊆ ℤ` with `c > 0` then `√c L` is integral and `L = (√c)⁻¹ (√c L)`, and
`√c L` is a lattice, finitely generated and discrete, when `L` is. So `L` is arithmetic exactly
when `c B(L, L) ⊆ ℤ` for some real `c > 0`, which is the definition used here
(`LinearMap.BilinForm.IsArithmeticLattice`); in a real inner product space it is LeanBridge's
`ZLattice.IsArithmetic`. None of this uses the nondegeneracy of `B`, and indefinite forms are
included.

The isometries of LMFDB `lattice.isometry` are, as written, arbitrary maps `σ` with
`Q(σ x) = Q(x)`, neither linear nor bijective, and `lattice.similarity` allows `α = 0`. Similarity
is formalised with `ℤ`-linear bijections preserving the forms and `α ≠ 0`, but the arithmetic
lattices do not depend on the reading: for a symmetric `B`, any map `σ : L → αM` with `M` integral
and `Q(σ x) = Q(x)` gives `2 B(L, L) ⊆ α² ℤ` by polarisation, so `L` is again arithmetic.

## Main definitions

* `LinearMap.BilinForm.IsIntegralLattice` (LMFDB `lattice.definition`): `B(L, L) ⊆ ℤ`.
* `LinearMap.BilinForm.IsSimilarLattice` (LMFDB `lattice.similarity`): `L` is isometric to `αM`.
* `LinearMap.BilinForm.IsArithmeticLattice` (LMFDB `lattice.arithmetic`): `c B(L, L) ⊆ ℤ` for a
  real `c > 0`.

## Main results

* `LinearMap.BilinForm.IsSimilarLattice.isArithmeticLattice` (LMFDB `lattice.arithmetic`): a
  lattice similar to an integral lattice, in any real quadratic space, is arithmetic.
* `LinearMap.BilinForm.isArithmeticLattice_of_apply_self_eq` (LMFDB `lattice.arithmetic`): the
  same for the literal reading of `lattice.isometry`, a map `σ : L → αM`, linear or not, with
  `Q(σ x) = Q(x)`.
* `LinearMap.BilinForm.isSimilarLattice_smul`: `L` is similar to `aL` for every real `a ≠ 0`.
* `LinearMap.BilinForm.isIntegralLattice_sqrt_smul`: if `c B(L, L) ⊆ ℤ` with `c ≥ 0`, then `√c L`
  is integral.
* `Submodule.FG.pointwise_smul` and `Submodule.discreteTopology_pointwise_smul`: `aL`, `a ≠ 0`, is
  finitely generated and discrete when `L` is.
* `LinearMap.BilinForm.isArithmeticLattice_iff` (LMFDB `lattice.arithmetic`): a finitely generated
  discrete `L` is arithmetic exactly when it is similar to an integral lattice, finitely generated
  and discrete, of the same space; it can be taken to be `√c L`.
* `LinearMap.BilinForm.isArithmeticLattice_innerₗ_iff`: in a real inner product space this is
  `ZLattice.IsArithmetic`.
-/

open scoped InnerProductSpace Pointwise

open LinearMap (BilinForm)

namespace Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {L : Submodule ℤ V}

/-- **The scaling `aL` of a finitely generated `ℤ`-submodule `L` is finitely generated.** -/
lemma FG.pointwise_smul (hL : L.FG) (a : ℝ) : (a • L).FG :=
  hL.map _

/-- **The scaling `aL`, `a ≠ 0`, of a discrete `ℤ`-submodule `L` is discrete**, `x ↦ a x` being a
homeomorphism. -/
lemma discreteTopology_pointwise_smul [TopologicalSpace V] [ContinuousConstSMul ℝ V]
    [DiscreteTopology L] {a : ℝ} (ha : a ≠ 0) : DiscreteTopology ↥(a • L) :=
  ((Homeomorph.smulOfNeZero a ha).subtype fun x ↦
    (Set.smul_mem_smul_set_iff₀ ha (L : Set V) x).symm).discreteTopology

end Submodule

namespace LinearMap.BilinForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (B : BilinForm ℝ V) (L : Submodule ℤ V) (B' : BilinForm ℝ W) (M : Submodule ℤ W)

/-- A `ℤ`-submodule `L` of a real vector space with a bilinear form `B` is an **integral** lattice
(LMFDB `lattice.definition`) if `B(L, L) ⊆ ℤ`. The knowl's lattices are moreover finitely generated
and discrete, in a finite-dimensional space with a nonsingular symmetric form. -/
def IsIntegralLattice : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, B x y = n

/-- A lattice `L` in a real quadratic space `(V, B)` is **similar** (LMFDB `lattice.similarity`) to
a lattice `M` in `(W, B')` if `L` is isometric to `αM` for a real constant `α ≠ 0`: some `ℤ`-linear
bijection `e : L → αM` satisfies `B'(e x, e y) = B(x, y)` (LMFDB `lattice.isometry` asks for
`Q(e x) = Q(x)`, the same for a linear bijection, `B` being recovered from `Q` by polarisation). -/
def IsSimilarLattice : Prop :=
  ∃ α : ℝ, α ≠ 0 ∧ ∃ e : L ≃ₗ[ℤ] ↥(α • M), ∀ x y : L, B' (e x) (e y) = B x y

/-- A lattice `L` in a real quadratic space `(V, B)` is **arithmetic** (LMFDB `lattice.arithmetic`)
if `c B(L, L) ⊆ ℤ` for some real `c > 0`. This is the knowl's definition, similarity to an integral
lattice (`LinearMap.BilinForm.isArithmeticLattice_iff`,
`LinearMap.BilinForm.IsSimilarLattice.isArithmeticLattice`), and for a real inner product space it
is `ZLattice.IsArithmetic` (`LinearMap.BilinForm.isArithmeticLattice_innerₗ_iff`). -/
def IsArithmeticLattice : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, c * B x y = n

variable {B B' L M}

/-- **A lattice similar to an integral lattice is arithmetic** (LMFDB `lattice.arithmetic`), the
integral lattice lying in any real quadratic space: if `L` is isometric to `αM` with `M` integral,
then `α⁻² B(L, L) ⊆ ℤ`. -/
lemma IsSimilarLattice.isArithmeticLattice (h : B.IsSimilarLattice L B' M)
    (hM : B'.IsIntegralLattice M) : B.IsArithmeticLattice L := by
  rcases h with ⟨α, hα, e, he⟩
  refine ⟨(α ^ 2)⁻¹, by positivity, fun x hx y hy ↦ ?_⟩
  rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (e ⟨x, hx⟩).2 with ⟨m, hm, hmx⟩
  rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (e ⟨y, hy⟩).2 with ⟨m', hm', hmy⟩
  rcases hM m hm m' hm' with ⟨n, hn⟩
  have hxy : B' (e ⟨x, hx⟩ : W) (e ⟨y, hy⟩ : W) = B x y :=
    he _ _
  rw [← hmx, ← hmy, smul_left, smul_right, hn] at hxy
  refine ⟨n, ?_⟩
  rw [← hxy]
  field_simp

/-- **A lattice with a norm-preserving map to a scaled integral lattice is arithmetic** (LMFDB
`lattice.arithmetic`, with `lattice.similarity` and `lattice.isometry` read literally): if `B` is
symmetric, `M` is integral and some map `σ : L → αM`, `α ∈ ℝ`, linear or not, satisfies
`B'(σ x, σ x) = B(x, x)`, then `L` is arithmetic, since `B(x, x) ∈ α² ℤ` on `L` and
`2 B(x, y) = B(x + y, x + y) - B(x, x) - B(y, y)`. -/
lemma isArithmeticLattice_of_apply_self_eq (hB : B.IsSymm) (hM : B'.IsIntegralLattice M) {α : ℝ}
    (σ : L → ↥(α • M)) (hσ : ∀ x : L, B' (σ x) (σ x) = B x x) : B.IsArithmeticLattice L := by
  have hQ (x : V) (hx : x ∈ L) : ∃ n : ℤ, B x x = α ^ 2 * n := by
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (σ ⟨x, hx⟩).2 with ⟨m, hm, hmx⟩
    rcases hM m hm m hm with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hσ ⟨x, hx⟩, ← hmx, smul_left, smul_right, hn, ← mul_assoc, sq]
  have h2 (x : V) (hx : x ∈ L) (y : V) (hy : y ∈ L) : ∃ n : ℤ, 2 * B x y = α ^ 2 * n := by
    rcases hQ (x + y) (L.add_mem hx hy) with ⟨a, ha⟩
    rcases hQ x hx with ⟨b, hb⟩
    rcases hQ y hy with ⟨c, hc⟩
    have hyx : B y x = B x y := (hB.eq x y).symm
    refine ⟨a - b - c, ?_⟩
    rw [add_left, add_right, add_right, hyx] at ha
    push_cast
    linarith
  rcases eq_or_ne α 0 with rfl | hα
  · refine ⟨1, one_pos, fun x hx y hy ↦ ⟨0, ?_⟩⟩
    rcases h2 x hx y hy with ⟨n, hn⟩
    simp_all
  · refine ⟨2 / α ^ 2, by positivity, fun x hx y hy ↦ ?_⟩
    rcases h2 x hx y hy with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    field_simp
    linarith

variable (B L)

/-- **A lattice `L` is similar to `aL` for every real `a ≠ 0`**: `L = a⁻¹ (aL)`. -/
lemma isSimilarLattice_smul {a : ℝ} (ha : a ≠ 0) : B.IsSimilarLattice L B (a • L) :=
  ⟨a⁻¹, inv_ne_zero ha, LinearEquiv.ofEq _ _ (inv_smul_smul₀ ha L).symm, fun _ _ ↦ rfl⟩

variable {B L}

/-- **If `c B(L, L) ⊆ ℤ` with `c ≥ 0`, then `√c L` is integral**, scaling by `√c` multiplying the
form by `c`. -/
lemma isIntegralLattice_sqrt_smul {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, c * B x y = n) : B.IsIntegralLattice (√c • L) := by
  rintro _ hx' _ hy'
  rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx' with ⟨x, hx, rfl⟩
  rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy' with ⟨y, hy, rfl⟩
  rcases h x hx y hy with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [smul_left, smul_right, ← mul_assoc, Real.mul_self_sqrt hc, hn]

variable [TopologicalSpace V] [ContinuousConstSMul ℝ V] in
/-- **A lattice is arithmetic exactly when it is similar to an integral lattice** (LMFDB
`lattice.arithmetic`): a finitely generated discrete `ℤ`-submodule `L` satisfies `c B(L, L) ⊆ ℤ`
for some real `c > 0` exactly when it is similar to a finitely generated discrete `ℤ`-submodule `K`
of the same space with `B(K, K) ⊆ ℤ`, which can be taken to be `√c L`. An integral lattice in any
other real quadratic space works as well
(`LinearMap.BilinForm.IsSimilarLattice.isArithmeticLattice`). -/
lemma isArithmeticLattice_iff (hL : L.FG) [DiscreteTopology L] : B.IsArithmeticLattice L ↔
    ∃ K : Submodule ℤ V, K.FG ∧ DiscreteTopology K ∧ B.IsIntegralLattice K ∧
    B.IsSimilarLattice L B K :=
  ⟨fun ⟨c, hc, h⟩ ↦ ⟨√c • L, hL.pointwise_smul √c,
    Submodule.discreteTopology_pointwise_smul (Real.sqrt_ne_zero'.mpr hc),
    isIntegralLattice_sqrt_smul hc.le h, isSimilarLattice_smul B L (Real.sqrt_ne_zero'.mpr hc)⟩,
    fun ⟨_, _, _, hM, h⟩ ↦ h.isArithmeticLattice hM⟩

/-- **In a real inner product space, arithmeticity for the inner product is LeanBridge's
`ZLattice.IsArithmetic`.** -/
lemma isArithmeticLattice_innerₗ_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Λ : Submodule ℤ E) : IsArithmeticLattice (innerₗ E) Λ ↔ ZLattice.IsArithmetic Λ :=
  Iff.rfl

end LinearMap.BilinForm
