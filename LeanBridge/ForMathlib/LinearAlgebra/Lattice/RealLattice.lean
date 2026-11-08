import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import TauCeti.LinearAlgebra.IntegralLattice.Gram
import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import LeanBridge.ForMathlib.Algebra.Module.ZLattice.ArithmeticBilinear

/-!
# Lattices in quadratic spaces and their rational models

A quadratic space `(V, Q)` (LMFDB `lattice.definition`) is a finite-dimensional vector space `V`
over a topological field `F` with a nonsingular symmetric bilinear form `B` and the quadratic map
`Q(v) = B(v, v)`; in a basis `v₁, …, vₙ` it is the homogeneous quadratic polynomial
`f(x) = ∑ᵢⱼ B(vᵢ, vⱼ) xᵢ xⱼ`, whose value at `x` is `Q(∑ xᵢ vᵢ)`. For a subring `R` of `F`, an
`R`-lattice is a finitely generated `R`-submodule of `V` that is a discrete subset of `V`, with the
restriction of `B`. Over `F = ℝ` a lattice is a `ℤ`-lattice `L`, integral if `B(L, L) ⊆ ℤ`
(`LinearMap.BilinForm.IsIntegralLattice`); for instance `ℤⁿ` in Euclidean `n`-space. The topology
of `V` is its natural one, that of `Fⁿ` through any basis: Mathlib's `IsModuleTopology F V`, or for
`F = ℝ` any Hausdorff topological vector space topology.

The integral lattices of LeanBridge and Tau Ceti (`TauCeti.IntegralLattice`) are full lattices in
rational spaces with integral rational forms: rational models of these real lattices. The bridge
works in both directions and for every signature, degenerate lattices included:

* an integral lattice `L` of a real quadratic space, finitely generated and so free, has an
  integer-valued form, and Tau Ceti's rationalisation of it is an integral lattice in `ℚ ⊗ L`, the
  rational model of `L`, whose integral form is isometric to that of `L`;
* conversely, every Tau Ceti integral lattice `L₀`, with Gram matrix `G` in a basis, is isometric
  to the rational model of the lattice `ℤ^ι ⊕ 0` of the real quadratic space `ℝ^(ι ⊕ ι)` with the
  block matrix `[[G, 1], [1, 0]]`, which is nonsingular even when `G` is singular.

The genus of an integral lattice `L` on `V` (LMFDB `lattice.genus`) is the set of lattices `M` on
`V` whose localisations `M_p = ℤ_p ⊗ M` are isometric to `L_p` for every prime `p`. These are the
lattices on the real space `V`, which need not lie in the rational span of `L`; their rational
models satisfy the local conditions of Tau Ceti's genus relation.

## Main definitions

* `Submodule.IsDiscreteLattice` (LMFDB `lattice.definition`): an `R`-lattice.
* `LinearMap.BilinForm.IsQuadraticSpace` (LMFDB `lattice.definition`): a quadratic space.
* `LinearMap.BilinForm.gramPolynomial` (LMFDB `lattice.definition`): the quadratic form of a
  bilinear form in a basis.
* `LinearMap.BilinForm.integralForm`: the integral form of an integral lattice.
* `LinearMap.BilinForm.ratModel`: the rational model of an integral lattice.
* `LinearMap.BilinForm.ratModelIsometry`: the isometry between an integral lattice and its
  rational model.
* `LinearMap.BilinForm.genus` (LMFDB `lattice.genus`): the genus of an integral lattice.
* `Matrix.gramRealForm` and `Matrix.gramRealLattice`: the real quadratic space and the lattice
  realising an integer symmetric matrix.
* `TauCeti.IntegralLattice.realisationIsometry` (LMFDB `lattice.definition`): every Tau Ceti
  integral lattice is isometric to the rational model of an integral lattice of a nonsingular real
  quadratic space.

## Main results

* `LinearMap.BilinForm.isHomogeneous_gramPolynomial` and `LinearMap.BilinForm.eval_gramPolynomial`
  (LMFDB `lattice.definition`): the quadratic form of `B` in a basis is homogeneous of degree `2`
  and evaluates to `Q`.
* `Matrix.isQuadraticSpace_toBilin'_one`, `Matrix.isDiscreteLattice_span_basisFun` and
  `Matrix.isIntegralLattice_span_basisFun` (LMFDB `lattice.definition`): `ℤⁿ` is an integral
  lattice in Euclidean `n`-space.
* `Matrix.isQuadraticSpace_gramRealForm`: the block form `[[G, 1], [1, 0]]` is nonsingular.
* `LinearMap.BilinForm.equivalent_localIntegralForm_ratModel_of_mem_genus` (LMFDB `lattice.genus`):
  the rational models of lattices of the same genus are locally isometric at every prime.
-/

open Module TauCeti

open scoped TensorProduct

open LinearMap (BilinForm BilinMap)

open IntegralLattice (ofIntegralForm)

namespace Submodule

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] [TopologicalSpace V]

/-- An **`R`-lattice** (LMFDB `lattice.definition`) in a topological module `V`: a finitely
generated `R`-submodule of `V` that is a discrete subset of `V`. The knowl's `V` is a vector space
over a topological field `F` with its natural topology, and `R` a subring of `F`. -/
structure IsDiscreteLattice (L : Submodule R V) : Prop where
  fg : L.FG
  discreteTopology : DiscreteTopology L

end Submodule

namespace LinearMap.BilinForm

section QuadraticSpace

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (B : BilinForm F V) {ι : Type*}
  [Fintype ι] (v : Basis ι F V)

/-- A **quadratic space** (LMFDB `lattice.definition`) `(V, Q)`: a vector space `V` with a
nonsingular symmetric bilinear form `B`, whose quadratic map is `Q(v) = B(v, v)`
(`LinearMap.BilinMap.toQuadraticMap`). -/
structure IsQuadraticSpace : Prop where
  isSymm : B.IsSymm
  nondegenerate : B.Nondegenerate

/-- The **quadratic form** (LMFDB `lattice.definition`) of a bilinear form `B` in a basis
`v₁, …, vₙ`: the homogeneous polynomial `f(x₁, …, xₙ) = ∑ᵢⱼ B(vᵢ, vⱼ) xᵢ xⱼ` of degree `2`
(`LinearMap.BilinForm.isHomogeneous_gramPolynomial`), whose value at `x` is
`Q(x₁ v₁ + ⋯ + xₙ vₙ)` (`LinearMap.BilinForm.eval_gramPolynomial`). -/
noncomputable def gramPolynomial : MvPolynomial ι F :=
  ∑ i, ∑ j, MvPolynomial.C (B (v i) (v j)) * MvPolynomial.X i * MvPolynomial.X j

/-- **The quadratic form of `B` in a basis is homogeneous of degree `2`** (LMFDB
`lattice.definition`). -/
lemma isHomogeneous_gramPolynomial : (B.gramPolynomial v).IsHomogeneous 2 :=
  .sum _ _ _ fun i _ ↦ .sum _ _ _ fun j _ ↦
    ((MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X _ i)).mul
      (MvPolynomial.isHomogeneous_X _ j)

/-- **The quadratic form of `B` in a basis `v` evaluates to `Q`** (LMFDB `lattice.definition`):
`f(x) = Q(x₁ v₁ + ⋯ + xₙ vₙ)`. -/
lemma eval_gramPolynomial (x : ι → F) :
    MvPolynomial.eval x (B.gramPolynomial v) = BilinMap.toQuadraticMap B (v.equivFun.symm x) := by
  simp only [gramPolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    BilinMap.toQuadraticMap_apply, Basis.equivFun_symm_apply, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
    ring1)

end QuadraticSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (B : BilinForm ℝ V) (L : Submodule ℤ V)

lemma le_dualSubmodule_of_isIntegralLattice (hL : B.IsIntegralLattice L) :
    L ≤ B.dualSubmodule L := by
  refine fun x hx ↦ (mem_dualSubmodule B).mpr fun y hy ↦ ?_
  rcases hL x hx y hy with ⟨n, hn⟩
  exact Submodule.mem_one.mpr ⟨n, by rw [hn, algebraMap_int_eq, eq_intCast]⟩

/-- The **integral form** of an integral lattice `L` in a real quadratic space `(V, B)`: the
restriction of `B` to `L`, as a `ℤ`-valued bilinear form, `B(L, L) ⊆ ℤ`
(`LinearMap.BilinForm.IsIntegralLattice`). -/
noncomputable def integralForm (hL : B.IsIntegralLattice L) : BilinForm ℤ L :=
  (B.dualSubmoduleToDual L).comp
    (Submodule.inclusion (B.le_dualSubmodule_of_isIntegralLattice L hL))

variable {B L}

@[simp]
lemma intCast_integralForm (hL : B.IsIntegralLattice L) (x y : L) :
    (B.integralForm L hL x y : ℝ) = B x y := by
  rw [integralForm, LinearMap.comp_apply, dualSubmoduleToDual_apply_apply,
    ← eq_intCast (algebraMap ℤ ℝ)]
  exact B.dualSubmodulePairing_spec _ y

lemma isSymm_integralForm (hB : B.IsSymm) (hL : B.IsIntegralLattice L) :
    (B.integralForm L hL).IsSymm :=
  ⟨fun x y ↦ Int.cast_injective (α := ℝ) <| by simp [hB.eq x y]⟩

lemma free_of_fg (hfg : L.FG) : Module.Free ℤ L := by
  have hfin : Module.Finite ℤ L := .of_fg hfg
  have htf : IsTorsionFree ℤ V := .trans_faithfulSMul ℤ ℝ V
  infer_instance

/-- The **rational model** of an integral lattice `L` in a real quadratic space `(V, B)`: Tau Ceti's
integral lattice in the rational space `ℚ ⊗ L` with the rational extension of the integral form of
`L`, whose carrier is `1 ⊗ L`. Its integral form is that of `L`
(`LinearMap.BilinForm.ratModelIsometry`). -/
noncomputable def ratModel (hB : B.IsSymm) (hL : B.IsIntegralLattice L) (hfg : L.FG) :
    IntegralLattice (ℚ ⊗[ℤ] L) :=
  haveI : Module.Finite ℤ L := .of_fg hfg
  haveI : Module.Free ℤ L := free_of_fg hfg
  ofIntegralForm (B.integralForm L hL) (isSymm_integralForm hB hL)

/-- The **isometry between an integral lattice and its rational model**: the identification of `L`
with the carrier `1 ⊗ L` of `LinearMap.BilinForm.ratModel` carries the integral form of `L` to that
of its rational model. -/
noncomputable def ratModelIsometry (hB : B.IsSymm) (hL : B.IsIntegralLattice L) (hfg : L.FG) :
    (B.integralForm L hL).IsometryEquiv (B.ratModel hB hL hfg).integralForm :=
  haveI : Module.Finite ℤ L := .of_fg hfg
  haveI : Module.Free ℤ L := free_of_fg hfg
  ofIntegralForm.carrierIsometry _ _

lemma gramMatrix_ratModel (hB : B.IsSymm) (hL : B.IsIntegralLattice L) (hfg : L.FG) {κ : Type*}
    (b : Basis κ ℤ L) : (B.ratModel hB hL hfg).gramMatrix (b.map (ratModelIsometry hB hL hfg)) =
      Matrix.of fun i j ↦ B.integralForm L hL (b i) (b j) := by
  ext i j
  rw [IntegralLattice.gramMatrix_apply, Basis.map_apply, Basis.map_apply]
  exact (ratModelIsometry hB hL hfg).map_app (b j) (b i)

variable [TopologicalSpace V]

variable (B L) in
/-- The **genus** (LMFDB `lattice.genus`) of an integral lattice `L` in a real quadratic space
`(V, B)`: the set of the lattices `M` on `V`, finitely generated, discrete and spanning `V`, whose
localisations `M_p = ℤ_p ⊗ M` are isometric to `L_p` for every prime `p`, each carrying the
`ℤ_p`-bilinear extension of its form. `M_p` is a quadratic `ℤ_p`-module, as `L_p` is, only when
the form of `M` takes `ℤ_p`-integral values, so `M` is integral
(`LinearMap.BilinForm.IsIntegralLattice`), and `M_p` carries the base change of its integral
form. -/
def genus (hL : B.IsIntegralLattice L) : Set (Submodule ℤ V) :=
  {M | M.IsDiscreteLattice ∧ Submodule.span ℝ (M : Set V) = ⊤ ∧ ∃ hM : B.IsIntegralLattice M,
    ∀ (p : ℕ) [Fact p.Prime],
      ((B.integralForm M hM).baseChange ℤ_[p]).Equivalent ((B.integralForm L hL).baseChange ℤ_[p])}

lemma mem_genus_self (hL : B.IsIntegralLattice L) (hd : L.IsDiscreteLattice)
    (hs : Submodule.span ℝ (L : Set V) = ⊤) : L ∈ B.genus L hL :=
  ⟨hd, hs, hL, fun _ _ ↦ Equivalent.refl _⟩

/-- **The rational models of lattices of the same genus are locally isometric** (LMFDB
`lattice.genus`): if `M` lies in the genus of `L`, the integral localisations of their rational
models are isometric at every prime, the local half of Tau Ceti's
`TauCeti.IntegralLattice.SameGenus`. -/
lemma equivalent_localIntegralForm_ratModel_of_mem_genus (hB : B.IsSymm)
    (hL : B.IsIntegralLattice L) (hfg : L.FG) {M : Submodule ℤ V} (h : M ∈ B.genus L hL) (p : ℕ)
    [Fact p.Prime] : ((B.ratModel hB h.2.2.1 h.1.fg).localIntegralForm p).Equivalent
      ((B.ratModel hB hL hfg).localIntegralForm p) :=
  (Equivalent.trans ⟨((ratModelIsometry hB h.2.2.1 h.1.fg).baseChange ℤ_[p]).symm⟩
    (h.2.2.2 p)).trans ⟨(ratModelIsometry hB hL hfg).baseChange ℤ_[p]⟩

end LinearMap.BilinForm

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- **`ℤⁿ` is a lattice in `ℝⁿ`** (LMFDB `lattice.definition`): the `ℤ`-span of the standard basis
is finitely generated and discrete. -/
lemma isDiscreteLattice_span_basisFun :
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).IsDiscreteLattice :=
  ⟨Submodule.fg_span (Set.finite_range _), inferInstance⟩

variable (ι) in
/-- The lattice `ℤ^ι ⊕ 0` in `ℝ^(ι ⊕ ι)`, on which `Matrix.gramRealForm G` is the form of `G`. -/
noncomputable def gramRealLattice : Submodule ℤ (ι ⊕ ι → ℝ) :=
  Submodule.span ℤ (Set.range fun i ↦ Pi.basisFun ℝ (ι ⊕ ι) (Sum.inl i))

lemma gramRealLattice_le :
    gramRealLattice ι ≤ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (ι ⊕ ι))) :=
  Submodule.span_mono <| Set.range_comp_subset_range _ _

lemma isDiscreteLattice_gramRealLattice : (gramRealLattice ι).IsDiscreteLattice := by
  have h :
      DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (ι ⊕ ι))) : Set (ι ⊕ ι → ℝ)) :=
    inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (ι ⊕ ι)))))
  exact ⟨Submodule.fg_span (Set.finite_range _), DiscreteTopology.of_continuous_injective
    (continuous_inclusion gramRealLattice_le) (Set.inclusion_injective gramRealLattice_le)⟩

variable (ι) in
/-- The basis `(eᵢ, 0)` of `ℤ^ι ⊕ 0`. -/
noncomputable def gramRealLatticeBasis : Basis ι ℤ (gramRealLattice ι) :=
  Basis.span <| ((Pi.basisFun ℝ (ι ⊕ ι)).linearIndependent.comp Sum.inl
    Sum.inl_injective).restrict_scalars' ℤ

variable [DecidableEq ι]

lemma coe_gramRealLatticeBasis (i : ι) :
    (gramRealLatticeBasis ι i : ι ⊕ ι → ℝ) = Pi.single (Sum.inl i) 1 :=
  (congrArg Subtype.val (Basis.span_apply _ i)).trans (Pi.basisFun_apply ℝ _ _)

lemma isQuadraticSpace_toBilin' {M : Matrix ι ι ℝ} (hM : M.IsSymm) (hdet : IsUnit M.det) :
    (toBilin' M).IsQuadraticSpace := by
  refine ⟨⟨fun x y ↦ ?_⟩,
    nondegenerate_toBilin'_iff.mpr (nondegenerate_of_det_ne_zero hdet.ne_zero)⟩
  rw [toBilin'_apply', toBilin'_apply', dotProduct_mulVec, ← mulVec_transpose, hM.eq,
    dotProduct_comm]

/-- **Euclidean `n`-space `(ℝⁿ, ·)` is a quadratic space** (LMFDB `lattice.definition`): the dot
product, the bilinear form of the identity matrix, is symmetric and nonsingular. -/
lemma isQuadraticSpace_toBilin'_one : (toBilin' (1 : Matrix ι ι ℝ)).IsQuadraticSpace :=
  isQuadraticSpace_toBilin' isSymm_one (by simp)

lemma isIntegralLattice_map_intCast (G : Matrix ι ι ℤ) :
    (toBilin' (G.map (Int.cast : ℤ → ℝ))).IsIntegralLattice
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
  intro x hx y hy
  rw [Basis.mem_span_iff_repr_mem] at hx hy
  choose a ha using hx
  choose b hb using hy
  refine ⟨a ⬝ᵥ G *ᵥ b, ?_⟩
  rcases funext ha with rfl
  rcases funext hb with rfl
  rw [toBilin'_apply']
  push_cast [dotProduct, mulVec]
  rfl

/-- **`ℤⁿ` is an integral lattice in Euclidean `n`-space** (LMFDB `lattice.definition`): the dot
product of two integer vectors is an integer. -/
lemma isIntegralLattice_span_basisFun :
    (toBilin' (1 : Matrix ι ι ℝ)).IsIntegralLattice
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
  simpa using isIntegralLattice_map_intCast (1 : Matrix ι ι ℤ)

variable (G : Matrix ι ι ℤ)

/-- The **real quadratic space of an integer matrix** `G`: `ℝ^(ι ⊕ ι)` with the bilinear form of
the block matrix `[[G, 1], [1, 0]]`, nonsingular for every symmetric `G`
(`Matrix.isQuadraticSpace_gramRealForm`), which is the form of `G` on `ℝ^ι ⊕ 0`. -/
noncomputable def gramRealForm : BilinForm ℝ (ι ⊕ ι → ℝ) :=
  toBilin' (fromBlocks (G.map (Int.cast : ℤ → ℝ)) 1 1 0)

/-- **The block form `[[G, 1], [1, 0]]` of a symmetric integer matrix `G` is nonsingular**, its
inverse being `[[0, 1], [1, -G]]`, even when `G` is singular. -/
lemma isQuadraticSpace_gramRealForm (hG : G.IsSymm) : (gramRealForm G).IsQuadraticSpace := by
  refine isQuadraticSpace_toBilin' ((hG.map _).fromBlocks transpose_one isSymm_zero) <|
    isUnit_det_of_right_inverse (B := fromBlocks 0 1 1 (-G.map (Int.cast : ℤ → ℝ))) ?_
  rw [fromBlocks_multiply]
  simp

lemma isIntegralLattice_gramRealLattice : (gramRealForm G).IsIntegralLattice (gramRealLattice ι) :=
  fun x hx y hy ↦ by
    have h : (toBilin' ((fromBlocks G 1 1 0).map (Int.cast : ℤ → ℝ))).IsIntegralLattice
        (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (ι ⊕ ι)))) :=
      isIntegralLattice_map_intCast (fromBlocks G 1 1 0)
    rw [fromBlocks_map, Matrix.map_one _ Int.cast_zero Int.cast_one,
      Matrix.map_zero _ Int.cast_zero] at h
    exact h x (gramRealLattice_le hx) y (gramRealLattice_le hy)

lemma integralForm_gramRealLatticeBasis (i j : ι) :
    (gramRealForm G).integralForm (gramRealLattice ι) (isIntegralLattice_gramRealLattice G)
      (gramRealLatticeBasis ι i) (gramRealLatticeBasis ι j) = G i j := by
  refine Int.cast_injective (α := ℝ) ?_
  rw [BilinForm.intCast_integralForm, coe_gramRealLatticeBasis,
    coe_gramRealLatticeBasis, gramRealForm, toBilin'_single, fromBlocks_apply₁₁, map_apply]

end Matrix

namespace TauCeti.IntegralLattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W] (L₀ : IntegralLattice W)

open Classical in
/-- **Every Tau Ceti integral lattice is the rational model of an integral lattice of a
nonsingular real quadratic space** (LMFDB `lattice.definition`): for the chosen basis of `L₀`, with
Gram matrix `G`, the lattice `ℤ^ι ⊕ 0` (`Matrix.gramRealLattice`) of the real quadratic space
`Matrix.gramRealForm G`, nonsingular (`Matrix.isQuadraticSpace_gramRealForm`), is a finitely
generated, discrete (`Matrix.isDiscreteLattice_gramRealLattice`) integral lattice whose rational
model is isometric to `L₀`. With `LinearMap.BilinForm.ratModelIsometry`, Tau Ceti's integral
lattices are, up to isometry, exactly the integral lattices of nonsingular real quadratic spaces, of
any signature, degenerate or not. -/
noncomputable def realisationIsometry :
    ((L₀.gramMatrix (Free.chooseBasis ℤ L₀)).gramRealForm.ratModel
      (Matrix.isQuadraticSpace_gramRealForm _ (L₀.isSymm_gramMatrix _)).isSymm
      (Matrix.isIntegralLattice_gramRealLattice _)
      Matrix.isDiscreteLattice_gramRealLattice.fg).Isometry L₀ :=
  Isometry.ofGramMatrixEq _ (Free.chooseBasis ℤ L₀) <|
    (BilinForm.gramMatrix_ratModel _ _ _ _).trans <|
      Matrix.ext fun i j ↦ Matrix.integralForm_gramRealLatticeBasis _ i j

end TauCeti.IntegralLattice
