import LeanBridge.ForMathlib.Geometry.Manifold.Algebra.ClosedSubgroupExp
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.LieGroup

/-!
# One-parameter subgroups of a Sato–Tate group

A Sato–Tate group `G` of degree `d` (LMFDB `st_group.definition`) is a closed subgroup of the
unitary group `U(d)`, so its image in `GL_d(ℂ)` is a closed subgroup of the units of the matrix
algebra. Near the identity this image is the exponential image of its Lie algebra
(`Subgroup.exists_mem_nhds_one_forall_exists_expUnit_eq`, from Cartan's closed-subgroup theorem in
Tau Ceti). So the one-parameter subgroups `t ↦ exp (t • X)` of `G`
(`SatoTateGroup.expOneParameter`), for the matrices `X` whose exponential line stays in `G`
(`SatoTateGroup.matrixLieAlgebra`), generate an open subgroup of `G`, which contains the identity
component `G⁰` (`SatoTateGroup.connectedComponentOfOne_le_closure_iUnion_range_expOneParameter`).

Along such a one-parameter subgroup, every polynomial function of the entries is real-analytic,
the matrix exponential being analytic (`Matrix.analyticAt_eval_mul_exp_smul_mul`). This is what
Serre's argument for the probabilities of a Sato–Tate group needs (LMFDB `st_group.probabilities`).

The matrix exponential is `NormedSpace.exp`, which depends only on the topology of the matrices;
the operator norm, whose topology is the entrywise topology of the matrices though not the same
instance, is selected only inside proofs, as in `SatoTateGroup.isEmbeddedLieSubgroup`.

## Main definitions

* `SatoTateGroup.matrixLieAlgebra`: the Lie algebra of a Sato–Tate group, as a set of matrices.
* `SatoTateGroup.expOneParameter`: the one-parameter subgroup `t ↦ exp (t • X)` of a Sato–Tate
  group, for `X` in its Lie algebra.

## Main results

* `Matrix.analyticAt_eval_mul_exp_smul_mul`: a polynomial in the entries of `A * exp (t • X) * B`
  is real-analytic in `t`.
* `SatoTateGroup.connectedComponentOfOne_le_closure_iUnion_range_expOneParameter`: the
  one-parameter subgroups `t ↦ exp (t • X)` of a Sato–Tate group generate a subgroup containing
  its identity component.
-/

open NormedSpace TauCeti

open scoped Topology

open Subgroup (connectedComponentOfOne)

attribute [local instance] TauCeti.normedAlgebraRatOfReal

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] (A B X : Matrix n n ℂ) (s : ℝ)

lemma analyticAt_exp_smul_apply (i j : n) :
    AnalyticAt ℝ (fun t : ℝ ↦ (A * exp (t • X) * B) i j) s := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have h₀ : AnalyticAt ℝ (fun t : ℝ ↦ t • X) s :=
    analyticAt_id.smul analyticAt_const
  have h₁ : AnalyticAt ℝ (fun t : ℝ ↦ exp (t • X)) s :=
    (exp_analytic (𝕂 := ℝ) (s • X)).comp_of_eq h₀ rfl
  let L : Matrix n n ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (entryLinearMap ℝ ℂ i j)
  exact L.analyticAt _ |>.comp ((analyticAt_const.mul h₁).mul analyticAt_const)

/-- **A polynomial in the entries of `A * exp (t • X) * B` is real-analytic in `t`**, the matrix
exponential being analytic. -/
lemma analyticAt_eval_mul_exp_smul_mul (P : MvPolynomial (n × n) ℂ) :
    AnalyticAt ℝ (fun t : ℝ ↦ MvPolynomial.eval (fun p ↦ (A * exp (t • X) * B) p.1 p.2) P) s := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add P Q hP hQ => simpa using hP.fun_add hQ
  | mul_X P p hP => simpa using hP.fun_mul (analyticAt_exp_smul_apply A B X s p.1 p.2)

end Matrix

namespace SatoTateGroup

variable (G : SatoTateGroup)

open scoped Matrix.Norms.Operator in
/-- The **Lie algebra** of a Sato–Tate group `G` of degree `d`, as a set of matrices: the `X` whose
exponential line `t ↦ exp (t • X)` lies in the image of `G` in `GL_d(ℂ)`. -/
def matrixLieAlgebra : Set (Matrix (Fin G.degree) (Fin G.degree) ℂ) :=
  {X | ∀ t : ℝ, expUnit (t • X) ∈ G.toSubgroup.map Unitary.toUnits}

variable {G} (X : G.matrixLieAlgebra) (t : ℝ)

open scoped Matrix.Norms.Operator in
/-- The **one-parameter subgroup** `t ↦ exp (t • X)` of a Sato–Tate group `G`, for a matrix `X` of
its Lie algebra `SatoTateGroup.matrixLieAlgebra`. -/
noncomputable def expOneParameter : G.toSubgroup :=
  (G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective).symm
    ⟨expUnit (t • X.1), X.2 t⟩

open scoped Matrix.Norms.Operator in
lemma matrix_expOneParameter : G.matrix (expOneParameter X t) = exp (t • X.1) := by
  let e : G.toSubgroup ≃* G.toSubgroup.map Unitary.toUnits :=
    G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective
  have h : (e (expOneParameter X t) : GL (Fin G.degree) ℂ) = expUnit (t • X.1) :=
    congrArg Subtype.val (e.apply_symm_apply _)
  exact (congrArg Units.val h).trans (expUnit_coe _)

open scoped Matrix.Norms.Operator in
lemma continuous_expOneParameter : Continuous (expOneParameter X) :=
  G.toUnitsEquiv.symm.continuous.comp <|
    (continuous_expUnit.comp (continuous_id.smul continuous_const)).subtype_mk fun t ↦ X.2 t

lemma expOneParameter_zero : expOneParameter X 0 = 1 := by
  simp [expOneParameter]

lemma expOneParameter_neg : expOneParameter X (-t) = (expOneParameter X t)⁻¹ := by
  simp only [expOneParameter, neg_smul, expUnit_neg]
  exact map_inv (G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective).symm
    ⟨_, X.2 t⟩

variable (G) in
open scoped Matrix.Norms.Operator in
/-- **The one-parameter subgroups of a Sato–Tate group generate its identity component**: the
subgroup generated by the one-parameter subgroups `t ↦ exp (t • X)` of `G`, for `X` in its Lie
algebra, contains the identity component `G⁰`. Every element of `G` close enough to `1` lies on one
of them, by Cartan's closed-subgroup theorem, so they generate an open subgroup. -/
lemma connectedComponentOfOne_le_closure_iUnion_range_expOneParameter :
    connectedComponentOfOne G.toSubgroup ≤
      Subgroup.closure (⋃ X : G.matrixLieAlgebra, Set.range (expOneParameter X)) := by
  let K : Subgroup (GL (Fin G.degree) ℂ) := G.toSubgroup.map Unitary.toUnits
  rcases Subgroup.exists_mem_nhds_one_forall_exists_expUnit_eq G.isClosed_map_toUnits with
    ⟨U, hU, hUK⟩
  let e : G.toSubgroup ≃* K :=
    G.toSubgroup.equivMapOfInjective Unitary.toUnits Unitary.toUnits_injective
  have he : Continuous e := G.toUnitsEquiv.continuous
  have hV : {g : G.toSubgroup | ((e g : K) : GL (Fin G.degree) ℂ) ∈ U} ⊆
      Subgroup.closure (⋃ X : G.matrixLieAlgebra, Set.range (expOneParameter X)) := by
    intro g hg
    rcases hUK (e g) (e g).2 hg with ⟨X, hX, hXg⟩
    refine Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨⟨X, hX⟩, 1, e.injective ?_⟩)
    simp only [expOneParameter, one_smul]
    exact (e.apply_symm_apply _).trans (Subtype.ext hXg)
  have hU' : U ∈ 𝓝 ((e 1 : K) : GL (Fin G.degree) ℂ) := by
    rw [map_one, Subgroup.coe_one]
    exact hU
  exact Subgroup.connectedComponentOfOne_le_of_mem_nhds_one <| Filter.mem_of_superset
    ((continuous_subtype_val.comp he).continuousAt.preimage_mem_nhds hU') hV

end SatoTateGroup
