import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import TauCeti.Algebra.Lie.GeneralLinear.Casimir

/-!
# Maass forms on `GL(n)`

A Maass form on `GL_n` is an automorphic form on `GL_n(ℝ)` that is not holomorphic but an
eigenfunction of the Casimir element `Σ_{i,j} E_ij E_ji` of the universal enveloping algebra
`U(gl_n)` (Tau Ceti's `TauCeti.glCasimir`). The Lie algebra `gl_n(ℝ)` acts on smooth functions on
`GL_n(ℝ)` by the left-invariant differential operators `(X_A f)(g) = Df(g)(gA)`, and
`[X_A, X_B] = X_{[A, B]}` by the symmetry of second derivatives; this makes the smooth functions a
Lie module, hence a `U(gl_n)`-module. Functions on `GL_n(ℝ)` are given on all square real matrices
(as `n → n → ℝ`, with its norm), only their values on invertible matrices mattering.

## Main definitions

* `Matrix.GeneralLinearGroup.smoothFunctions`: the smooth functions on `GL_n(ℝ)`, a Lie module
  over `gl_n(ℝ)` through `Matrix.GeneralLinearGroup.leftInvariantDeriv`.
* `Matrix.GeneralLinearGroup.casimirOperator`: the action of the Casimir element of `U(gl_n)`.
* `Matrix.GeneralLinearGroup.IsMaassForm` (LMFDB `mf.maass`).

## Main results

* The instance `LieModule ℝ (Matrix n n ℝ) (smoothFunctions n)`.
* `Matrix.GeneralLinearGroup.casimirOperator_apply`: the Casimir operator is
  `Σ_{i,j} X_{E_ij} X_{E_ji}`.
-/

open TauCeti
open scoped ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) {f : (n → n → ℝ) → ℂ}
    {g : n → n → ℝ}

variable (n) in
/-- The invertible matrices among the square real matrices, given by their entries. -/
def glSet : Set (n → n → ℝ) :=
  {g | IsUnit (of g).det}

lemma isOpen_glSet : IsOpen (glSet n) := by
  have h : glSet n = (fun g : n → n → ℝ ↦ (of g).det) ⁻¹' {0}ᶜ := by
    ext g
    simp [glSet]
  rw [h]
  exact isOpen_compl_singleton.preimage continuous_id.matrix_det

/-- Right multiplication `g ↦ gA` by a square matrix `A`, as a continuous linear map. -/
noncomputable def mulRightCLM : (n → n → ℝ) →L[ℝ] (n → n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun g := of.symm (of g * A)
      map_add' g h := by
        ext i j
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' c g := by
        ext i j
        simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

omit [DecidableEq n] in
lemma mulRightCLM_apply : mulRightCLM A g = of.symm (of g * A) :=
  rfl

omit [DecidableEq n] in
lemma mulRightCLM_mulRightCLM : mulRightCLM B (mulRightCLM A g) = mulRightCLM (A * B) g := by
  simp [mulRightCLM_apply, Matrix.mul_assoc]

omit [DecidableEq n] in
lemma mulRightCLM_add : mulRightCLM (A + B) g = mulRightCLM A g + mulRightCLM B g := by
  ext i j
  simp [mulRightCLM_apply, Matrix.mul_add]

omit [DecidableEq n] in
lemma mulRightCLM_sub : mulRightCLM (A - B) g = mulRightCLM A g - mulRightCLM B g := by
  ext i j
  simp [mulRightCLM_apply, Matrix.mul_sub]

omit [DecidableEq n] in
lemma mulRightCLM_smul (t : ℝ) : mulRightCLM (t • A) g = t • mulRightCLM A g := by
  ext i j
  simp [mulRightCLM_apply]

variable (f g) in
open scoped Classical in
/-- The left-invariant differential operator `(X_A f)(g) = d/dt f(g(1 + tA))|_{t = 0} = Df(g)(gA)`
of `A ∈ gl_n(ℝ)` on functions `f` on `GL_n(ℝ)`, given on all square matrices (and `0` at the
singular ones). -/
noncomputable def leftInvariantDeriv : ℂ :=
  if g ∈ glSet n then fderiv ℝ f g (mulRightCLM A g) else 0

variable (n) in
/-- The smooth functions on `GL_n(ℝ)`, given on all square real matrices: the functions that are
smooth on the open set of invertible matrices. -/
def smoothFunctions : Submodule ℂ ((n → n → ℝ) → ℂ) where
  carrier := {f | ContDiffOn ℝ ∞ f (glSet n)}
  add_mem' hf hg := hf.add hg
  zero_mem' := contDiffOn_const
  smul_mem' c _ hf := hf.const_smul c

lemma contDiffOn_leftInvariantDeriv (hf : ContDiffOn ℝ ∞ f (glSet n)) :
    ContDiffOn ℝ ∞ (leftInvariantDeriv A f) (glSet n) := by
  refine ((hf.fderiv_of_isOpen isOpen_glSet le_rfl).clm_apply
    (mulRightCLM A).contDiff.contDiffOn).congr fun g hg ↦ ?_
  simp [leftInvariantDeriv, hg]

private lemma differentiableAt_of_mem (hf : ContDiffOn ℝ ∞ f (glSet n)) (hg : g ∈ glSet n) :
    DifferentiableAt ℝ f g :=
  (hf.contDiffAt (isOpen_glSet.mem_nhds hg)).differentiableAt (by simp)

private lemma differentiableAt_fderiv_of_mem (hf : ContDiffOn ℝ ∞ f (glSet n)) (hg : g ∈ glSet n) :
    DifferentiableAt ℝ (fderiv ℝ f) g :=
  ((hf.fderiv_of_isOpen (m := ∞) isOpen_glSet le_rfl).contDiffAt
    (isOpen_glSet.mem_nhds hg)).differentiableAt (by simp)

private lemma leftInvariantDeriv_leftInvariantDeriv (hf : ContDiffOn ℝ ∞ f (glSet n))
    (hg : g ∈ glSet n) : leftInvariantDeriv A (leftInvariantDeriv B f) g =
      fderiv ℝ f g (mulRightCLM (A * B) g) +
        fderiv ℝ (fderiv ℝ f) g (mulRightCLM A g) (mulRightCLM B g) := by
  have he : leftInvariantDeriv B f =ᶠ[nhds g] fun g' ↦ fderiv ℝ f g' (mulRightCLM B g') :=
    Filter.eventually_of_mem (isOpen_glSet.mem_nhds hg) fun g' hg' ↦ by
      simp [leftInvariantDeriv, hg']
  simp only [leftInvariantDeriv, hg]
  rw [he.fderiv_eq,
    fderiv_clm_apply (differentiableAt_fderiv_of_mem hf hg) (mulRightCLM B).differentiableAt,
    ContinuousLinearMap.fderiv]
  simp [mulRightCLM_mulRightCLM]

noncomputable instance : Bracket (Matrix n n ℝ) (smoothFunctions n) where
  bracket A f := ⟨leftInvariantDeriv A f, contDiffOn_leftInvariantDeriv A f.2⟩

variable (F : smoothFunctions n)

lemma coe_bracket : ((⁅A, F⁆ : smoothFunctions n) : (n → n → ℝ) → ℂ) = leftInvariantDeriv A F :=
  rfl

noncomputable instance : LieRingModule (Matrix n n ℝ) (smoothFunctions n) where
  add_lie A B F := Subtype.ext <| funext fun g ↦ by
    by_cases hg : g ∈ glSet n <;> simp [coe_bracket, leftInvariantDeriv, hg, mulRightCLM_add]
  lie_add A F F' := Subtype.ext <| funext fun g ↦ by
    by_cases hg : g ∈ glSet n
    · simp [coe_bracket, leftInvariantDeriv, hg,
        fderiv_add (differentiableAt_of_mem F.2 hg) (differentiableAt_of_mem F'.2 hg)]
    · simp [coe_bracket, leftInvariantDeriv, hg]
  leibniz_lie A B F := Subtype.ext <| funext fun g ↦ by
    by_cases hg : g ∈ glSet n
    · have hs : fderiv ℝ (fderiv ℝ (F : (n → n → ℝ) → ℂ)) g (mulRightCLM A g) (mulRightCLM B g) =
          fderiv ℝ (fderiv ℝ (F : (n → n → ℝ) → ℂ)) g (mulRightCLM B g) (mulRightCLM A g) :=
        (F.2.contDiffAt (isOpen_glSet.mem_nhds hg)).isSymmSndFDerivAt (by simp) _ _
      simp only [Submodule.coe_add, Pi.add_apply, coe_bracket]
      rw [leftInvariantDeriv_leftInvariantDeriv A B F.2 hg,
        leftInvariantDeriv_leftInvariantDeriv B A F.2 hg]
      simp only [leftInvariantDeriv, hg, ↓reduceIte]
      rw [Ring.lie_def, mulRightCLM_sub, map_sub, hs]
      ring1
    · simp [coe_bracket, leftInvariantDeriv, hg]

instance : LieModule ℝ (Matrix n n ℝ) (smoothFunctions n) where
  smul_lie t A F := Subtype.ext <| funext fun g ↦ by
    simp [coe_bracket, leftInvariantDeriv, mulRightCLM_smul]
  lie_smul t A F := Subtype.ext <| funext fun g ↦ by
    by_cases hg : g ∈ glSet n
    · simp [coe_bracket, leftInvariantDeriv, fderiv_const_smul (differentiableAt_of_mem F.2 hg)]
    · simp [coe_bracket, leftInvariantDeriv, hg]

/-- The **Casimir operator** on smooth functions on `GL_n(ℝ)`: the action of the Casimir element
`Σ_{i,j} E_ij E_ji` (Tau Ceti's `TauCeti.glCasimir`) of the universal enveloping algebra of
`gl_n(ℝ)`, through the Lie module of smooth functions. -/
noncomputable def casimirOperator : Module.End ℝ (smoothFunctions n) :=
  UniversalEnvelopingAlgebra.representation ℝ (Matrix n n ℝ) (smoothFunctions n) (glCasimir ℝ n)

/-- **The Casimir operator is `Σ_{i,j} X_{E_ij} X_{E_ji}`**. -/
lemma casimirOperator_apply : casimirOperator F = ∑ i, ∑ j,
    ⁅(single i j 1 : Matrix n n ℝ), ⁅(single j i 1 : Matrix n n ℝ), F⁆⁆ :=
  representation_glCasimir_apply ℝ n F

variable (Γ : Subgroup (GL n ℤ))

/-- A function `φ` on `GL_n(ℝ)`, given on all square real matrices, is a **Maass form** (LMFDB
`mf.maass`) for a subgroup `Γ` of `GL_n(ℤ)` (such as `SL_n(ℤ)`) with Casimir eigenvalue `λ` if it
is smooth on `GL_n(ℝ)`, left `Γ`-invariant, right invariant under the orthogonal group `O(n)` and
under the positive scalars (a function on the symmetric space `GL_n(ℝ) / O(n) ℝ_{>0}`, hence not
holomorphic), of moderate growth (bounded by a power of `‖g‖ + ‖g⁻¹‖`), and an eigenfunction of
the Casimir element of `U(gl_n)` with eigenvalue `λ`. These are the spherical Maass forms: the
LMFDB's term also covers non-spherical ones, such as Maass forms of nonzero weight on `GL(2)`. -/
def IsMaassForm (φ : (n → n → ℝ) → ℂ) (eigenvalue : ℂ) : Prop :=
  ∃ hφ : φ ∈ smoothFunctions n,
    (∀ γ ∈ Γ, ∀ g, φ (of.symm ((γ : Matrix n n ℤ).map (↑) * of g)) = φ g) ∧
    (∀ k ∈ orthogonalGroup n ℝ, ∀ g, φ (of.symm (of g * k)) = φ g) ∧
    (∀ t : ℝ, 0 < t → ∀ g, φ (t • g) = φ g) ∧
    (∃ (C : ℝ) (N : ℕ), ∀ g ∈ glSet n, ‖φ g‖ ≤ C * (‖g‖ + ‖of.symm (of g)⁻¹‖) ^ N) ∧
    ∀ g ∈ glSet n, (casimirOperator ⟨φ, hφ⟩ : (n → n → ℝ) → ℂ) g = eigenvalue * φ g

lemma isMaassForm_const (c : ℂ) : IsMaassForm Γ (fun _ ↦ c) 0 := by
  refine ⟨contDiffOn_const, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
    ⟨‖c‖, 0, fun _ _ ↦ by simp⟩, fun g _ ↦ ?_⟩
  have h : ∀ A : Matrix n n ℝ, ⁅A, (⟨fun _ ↦ c, contDiffOn_const⟩ : smoothFunctions n)⁆ = 0 :=
    fun A ↦ Subtype.ext <| funext fun g ↦ by simp [coe_bracket, leftInvariantDeriv]
  simp [casimirOperator_apply, h]

end Matrix.GeneralLinearGroup
