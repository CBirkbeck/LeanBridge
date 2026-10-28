import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Geometry.Lie.Subgroup.Unitary
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Sato–Tate groups and their moment statistics

An LMFDB Sato–Tate group (LMFDB `st_group.definition`) of weight `w` and degree `d` is a compact
subgroup of `USp(d)` (odd `w`) or `O(d)` (even `w`), both viewed inside the unitary group
`U(d) ⊆ GL_d(ℂ)`. We bundle such a group as a closed subgroup of `Matrix.unitaryGroup (Fin d) ℂ`
contained in the ambient group, and define the statistics the LMFDB attaches to it, all with
respect to the Haar probability measure `TauCeti.haarProb`.

## Main definitions

* `Matrix.satoTateForm`: the standard alternating form on `ℂ^d` defining `USp(d)`.
* `SatoTateGroup.ambientGroup`, `SatoTateGroup.ambient` (LMFDB `st_group.ambient`).
* `SatoTateGroup`: a closed subgroup of `U(d)` inside its ambient group; its field `degree`
  is the degree (LMFDB `st_group.degree`).
* `SatoTateGroup.charpolyCoeff`, `SatoTateGroup.esymmEigen`, `SatoTateGroup.powerSum`: the random
  variables `aᵢ`, `eᵢ`, `sᵢ`; `SatoTateGroup.moment` the moment sequence (LMFDB `st_group.moments`).
* `SatoTateGroup.traceMoment` (LMFDB `st_group.trace_moments`), `SatoTateGroup.secondTraceMoment`
  (LMFDB `st_group.second_trace_moment`), `SatoTateGroup.fourthTraceMoment`
  (LMFDB `st_group.fourth_trace_moment`), `SatoTateGroup.firstA2Moment`
  (LMFDB `st_group.first_a2_moment`).
* `SatoTateGroup.mixedMoment`, `SatoTateGroup.momentSimplexRow`
  (LMFDB `st_group.moment_simplex`).
* `SatoTateGroup.probability` (LMFDB `st_group.probabilities`).
* `SatoTateGroup.traceZeroDensity` (LMFDB `st_group.trace_zero_density`).
* `SatoTateGroup.realDimension` (LMFDB `st_group.real_dimension`).

## Main theorems

* `Matrix.reindex_J_eq_satoTateForm`: `satoTateForm (g + g)` is Mathlib's `Matrix.J (Fin g) ℂ`.
* `SatoTateGroup.mem_ambientGroup_iff_of_even`: in even weight the ambient group is `O(d)`.
* `SatoTateGroup.natDegree_charpoly`: the degree is the degree of the characteristic polynomials.
* `SatoTateGroup.esymmEigen_eq`: `eᵢ = (-1)ⁱ aᵢ`.
* `SatoTateGroup.charpolyCoeff_one`: `a₁ = -t`.
* `SatoTateGroup.moment_zero`: the zeroth moment is `1`.
-/

open Matrix MeasureTheory Polynomial TauCeti

namespace Matrix

/-- The standard alternating form on `ℂ^d` used to define the unitary symplectic group `USp(d)`
(LMFDB `st_group.usp`): the matrix `Ω` with `Ω i (i + d / 2) = -1` and `Ω (i + d / 2) i = 1`. For
`d = g + g` it is Mathlib's `Matrix.J (Fin g) ℂ` with the blocks indexed by `Fin (g + g)`; for odd
`d` it is not alternating, but Sato–Tate groups of odd weight have even degree. -/
def satoTateForm (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  of fun i j => if (i : ℕ) + d / 2 = j then -1 else if (j : ℕ) + d / 2 = i then 1 else 0

/-- **`satoTateForm (g + g)` is Mathlib's standard symplectic form `Matrix.J (Fin g) ℂ`**, so the
unitary symplectic group it defines is the LMFDB's `USp(2g)`. -/
lemma reindex_J_eq_satoTateForm (g : ℕ) :
    (J (Fin g) ℂ).reindex finSumFinEquiv finSumFinEquiv = satoTateForm (g + g) := by
  have h : (g + g) / 2 = g := by
    omega
  ext i j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;>
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j <;>
    simp only [reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, J, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂] <;>
    simp only [satoTateForm, h, of_apply, neg_apply, one_apply, Fin.val_castAdd, Fin.val_natAdd,
      Fin.ext_iff] <;>
    split_ifs <;> first | omega | simp

end Matrix

namespace SatoTateGroup

/-- The form preserved by the ambient group: `satoTateForm d` in odd weight, the identity (the
standard symmetric form) in even weight. -/
def ambientForm (w d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  if Odd w then satoTateForm d else 1

/-- The **ambient group** (LMFDB `st_group.ambient`) of weight `w` and degree `d`, as a subgroup of
the unitary group `U(d)`: the unitary matrices `A` with `Aᵀ Ω A = Ω`, for `Ω = ambientForm w d`.
For odd `w` this is `USp(d)`. For even `w` it is the unitary matrices with `Aᵀ A = 1`, which are
exactly the real orthogonal matrices `O(d)`, the compact form the LMFDB means. -/
def ambientGroup (w d : ℕ) : Subgroup (unitaryGroup (Fin d) ℂ) where
  carrier := {A | (A : Matrix (Fin d) (Fin d) ℂ)ᵀ * ambientForm w d * A = ambientForm w d}
  one_mem' := by
    simp
  mul_mem' {A B} hA hB := by
    simpa only [Set.mem_ofPred_eq, Submonoid.coe_mul, transpose_mul, Matrix.mul_assoc] using
      (congrArg (fun M ↦ (B : Matrix (Fin d) (Fin d) ℂ)ᵀ * M * B) hA).trans hB
  inv_mem' {A} hA := by
    have h : (A : Matrix (Fin d) (Fin d) ℂ) * star (A : Matrix (Fin d) (Fin d) ℂ) = 1 :=
      Unitary.mul_star_self_of_mem A.2
    rw [Set.mem_ofPred_eq] at hA
    rw [Set.mem_ofPred_eq, ← Unitary.star_eq_inv, Unitary.coe_star]
    nth_rw 1 [← hA]
    simp only [Matrix.mul_assoc, h, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, ← transpose_mul, h, transpose_one, Matrix.one_mul]

lemma mem_ambientGroup {w d : ℕ} (A : unitaryGroup (Fin d) ℂ) : A ∈ ambientGroup w d ↔
    (A : Matrix (Fin d) (Fin d) ℂ)ᵀ * ambientForm w d * A = ambientForm w d :=
  Iff.rfl

lemma ambientForm_of_even {w : ℕ} (hw : Even w) (d : ℕ) : ambientForm w d = 1 :=
  ite_eq_right_iff.mpr fun h ↦ absurd h <| Nat.not_odd_iff_even.mpr hw

/-- **In even weight the ambient group is the real orthogonal group `O(d)`**: a unitary matrix lies
in it if and only if it is a real orthogonal matrix. -/
lemma mem_ambientGroup_iff_of_even {w d : ℕ} (hw : Even w) (A : unitaryGroup (Fin d) ℂ) :
    A ∈ ambientGroup w d ↔
      ∃ B ∈ orthogonalGroup (Fin d) ℝ, B.map Complex.ofReal = (A : Matrix (Fin d) (Fin d) ℂ) := by
  rw [mem_ambientGroup, ambientForm_of_even hw, Matrix.mul_one]
  constructor
  · intro hA
    have h : star (A : Matrix (Fin d) (Fin d) ℂ) = (A : Matrix (Fin d) (Fin d) ℂ)ᵀ := by
      rw [← Matrix.mul_one (star _), ← mul_eq_one_comm.mp hA, ← Matrix.mul_assoc,
        Unitary.star_mul_self_of_mem A.2, Matrix.one_mul]
    have hB : ((A : Matrix (Fin d) (Fin d) ℂ).map Complex.re).map Complex.ofReal = A := by
      ext i j
      have hij : ((A : Matrix (Fin d) (Fin d) ℂ) i j).im = 0 :=
        Complex.conj_eq_iff_im.mp <| by simpa using congrFun (congrFun h j) i
      apply Complex.ext <;> simp [hij]
    refine ⟨(A : Matrix (Fin d) (Fin d) ℂ).map Complex.re, (mem_orthogonalGroup_iff' _ _).mpr ?_,
      hB⟩
    apply map_injective Complex.ofReal_injective
    refine (Matrix.map_mul (f := Complex.ofRealHom)).trans ?_
    rw [← transpose_map]
    exact (congrArg (fun M ↦ Mᵀ * M) hB).trans <| hA.trans
      (Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one).symm
  · rintro ⟨B, hB, hBA⟩
    rw [← hBA, ← transpose_map]
    exact (Matrix.map_mul (f := Complex.ofRealHom)).symm.trans <| by
      rw [(mem_orthogonalGroup_iff' _ _).mp hB]
      simp

end SatoTateGroup

/-- A **Sato–Tate group** (LMFDB `st_group.definition`) of weight `w` and degree `d`, as the LMFDB
stores it: a compact subgroup of `USp(d)` (odd `w`, even `d`) or of `O(d)` (even `w`), given as a
closed subgroup of the unitary group `U(d) ⊆ GL_d(ℂ)` contained in the ambient group. The
**degree** (LMFDB `st_group.degree`) is the matrix size `d`. This records the group with its
embedding; that it is the Sato–Tate group of a given motive is not part of the data. -/
structure SatoTateGroup where
  /-- The motivic weight `w`. -/
  weight : ℕ
  /-- The **degree** `d` (LMFDB `st_group.degree`): the size of the matrices. -/
  degree : ℕ
  even_degree_of_odd_weight : Odd weight → Even degree
  /-- The group, as a subgroup of `U(d)`. -/
  toSubgroup : Subgroup (unitaryGroup (Fin degree) ℂ)
  isClosed : IsClosed (toSubgroup : Set (unitaryGroup (Fin degree) ℂ))
  le_ambientGroup : toSubgroup ≤ SatoTateGroup.ambientGroup weight degree

namespace SatoTateGroup

variable (G : SatoTateGroup)

/-- The **ambient group** (LMFDB `st_group.ambient`) of a Sato–Tate group: `USp(d)` in odd weight
and `O(d)` in even weight. -/
def ambient : Subgroup (unitaryGroup (Fin G.degree) ℂ) :=
  ambientGroup G.weight G.degree

instance : CompactSpace G.toSubgroup :=
  isCompact_iff_compactSpace.mp G.isClosed.isCompact

noncomputable instance : MeasurableSpace G.toSubgroup :=
  borel G.toSubgroup

instance : BorelSpace G.toSubgroup :=
  ⟨rfl⟩

/-- The matrix in `GL_d(ℂ)` of an element of a Sato–Tate group. -/
def matrix (g : G.toSubgroup) : Matrix (Fin G.degree) (Fin G.degree) ℂ :=
  ((g : unitaryGroup (Fin G.degree) ℂ) : Matrix (Fin G.degree) (Fin G.degree) ℂ)

/-- The random variable `aᵢ` (LMFDB `st_group.moments`) on a Sato–Tate group of degree `d`: the
coefficient of `x ^ (d - i)` in the characteristic polynomial
`x ^ d + a₁ x ^ (d - 1) + ⋯ + a_d`, so the `i`th coefficient of its reverse, and `0` for `i > d`.
This is the LMFDB's indexing, with `a₁ = -t` for the trace `t` (`charpolyCoeff_one`); the knowl's
`∑ aᵢ xⁱ` indexes the other way. -/
noncomputable def charpolyCoeff (i : ℕ) (g : G.toSubgroup) : ℂ :=
  (G.matrix g).charpoly.reverse.coeff i

/-- The random variable `eᵢ` (LMFDB `st_group.moments`): the `i`th elementary symmetric function
of the eigenvalues. -/
noncomputable def esymmEigen (i : ℕ) (g : G.toSubgroup) : ℂ :=
  (G.matrix g).charpoly.roots.esymm i

/-- The random variable `sᵢ` (LMFDB `st_group.moments`): the `i`th power sum of the eigenvalues. -/
noncomputable def powerSum (i : ℕ) (g : G.toSubgroup) : ℂ :=
  ((G.matrix g).charpoly.roots.map (· ^ i)).sum

/-- The trace `t` of an element of a Sato–Tate group, as a random variable. -/
def trace (g : G.toSubgroup) : ℂ :=
  (G.matrix g).trace

/-- The expected value `E[X]` of a random variable on a Sato–Tate group, for its Haar probability
measure. -/
noncomputable def expectation (X : G.toSubgroup → ℂ) : ℂ :=
  ∫ g, X g ∂haarProb G.toSubgroup

/-- The **moment sequence** (LMFDB `st_group.moments`) `n ↦ E[Xⁿ]` of a random variable `X` on a
Sato–Tate group, under the pushforward of the Haar probability measure: its **moment
statistics**. It starts with `E[X⁰] = 1` (`moment_zero`). -/
noncomputable def moment (X : G.toSubgroup → ℂ) (n : ℕ) : ℂ :=
  G.expectation (X ^ n)

/-- The `n`th trace **moment** (LMFDB `st_group.trace_moments`) `Mₙ[t] = E[tⁿ]`. -/
noncomputable def traceMoment (n : ℕ) : ℂ :=
  G.moment G.trace n

/-- The **second trace moment** (LMFDB `st_group.second_trace_moment`) `E[t²]`. -/
noncomputable def secondTraceMoment : ℂ :=
  G.traceMoment 2

/-- The **fourth trace moment** (LMFDB `st_group.fourth_trace_moment`) `E[t⁴]`. -/
noncomputable def fourthTraceMoment : ℂ :=
  G.traceMoment 4

/-- The **first `a₂` moment** (LMFDB `st_group.first_a2_moment`) `E[a₂]`, with `a₂` the coefficient
of `x ^ (d - 2)` in the characteristic polynomial, following the LMFDB's indexing; in odd weight the
characteristic polynomials are palindromic, so it is also the coefficient of `x ^ 2`. -/
noncomputable def firstA2Moment : ℂ :=
  G.expectation (G.charpolyCoeff 2)

/-- The mixed moment `E[a₁^{e₁} ⋯ a_g^{e_g}]` (LMFDB `st_group.moment_simplex`) of an exponent
vector `e`, a finitely supported function from indices to exponents. -/
noncomputable def mixedMoment (e : ℕ →₀ ℕ) : ℂ :=
  G.expectation fun g ↦ e.prod fun i k ↦ G.charpolyCoeff i g ^ k

/-- The weighted degree `∑ i eᵢ` of an exponent vector. -/
def weightedDegree (e : ℕ →₀ ℕ) : ℕ :=
  e.sum fun i k ↦ i * k

/-- The row of weighted degree `2 k` of the **moment simplex** (LMFDB `st_group.moment_simplex`) of
a Sato–Tate group of degree `2 g`: the exponent vectors `(e₁, …, e_g)` of weighted degree `2 k`
whose mixed moment is nonzero; the entries are their mixed moments. The LMFDB's ordering of a row
is a display convention and is not recorded. -/
def momentSimplexRow (k : ℕ) : Set (ℕ →₀ ℕ) :=
  {e | ↑e.support ⊆ Set.Icc 1 (G.degree / 2) ∧ weightedDegree e = 2 * k ∧ G.mixedMoment e ≠ 0}

/-- The **probability** (LMFDB `st_group.probabilities`) `Pr[aᵢ = n]` that a Haar-random element
of a Sato–Tate group has `aᵢ = n`. -/
noncomputable def probability (i : ℕ) (n : ℤ) : ℝ :=
  (haarProb G.toSubgroup).real {g | G.charpolyCoeff i g = n}

/-- The **trace zero density** (LMFDB `st_group.trace_zero_density`): the probability that a
Haar-random element of a Sato–Tate group has trace zero. -/
noncomputable def traceZeroDensity : ℝ :=
  (haarProb G.toSubgroup).real {g | G.trace g = 0}

open scoped Manifold Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
/-- The **real dimension** (LMFDB `st_group.real_dimension`) of a Sato–Tate group: its dimension
as a real Lie group, the real dimension of its Lie algebra, Tau Ceti's
`TauCeti.Lie.lieSubalgebraOfSubgroup` of its image in the Lie group `GL_d(ℂ)`. For a closed
subgroup, as here, this is the dimension of the Lie group by the closed-subgroup theorem. -/
noncomputable def realDimension : ℕ :=
  Module.finrank ℝ <| Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin G.degree) (Fin G.degree) ℂ)) (G.toSubgroup.map Unitary.toUnits)

/-- **The degree of a Sato–Tate group is the degree of the characteristic polynomials of its
elements** (LMFDB `st_group.degree`). -/
lemma natDegree_charpoly (g : G.toSubgroup) : (G.matrix g).charpoly.natDegree = G.degree := by
  simp

/-- **Vieta: `eᵢ = (-1)ⁱ aᵢ`** for `i ≤ d`. -/
lemma esymmEigen_eq {i : ℕ} (hi : i ≤ G.degree) (g : G.toSubgroup) :
    G.esymmEigen i g = (-1) ^ i * G.charpolyCoeff i g := by
  rw [charpolyCoeff, coeff_reverse, G.natDegree_charpoly, revAt_le hi,
    coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits (G.matrix g).charpoly) (by simp),
    (G.matrix g).charpoly_monic.leadingCoeff, G.natDegree_charpoly, Nat.sub_sub_self hi]
  simp [esymmEigen, ← mul_assoc, ← mul_pow]

/-- **`a₁ = -t`** (LMFDB `st_group.trace_moments`) in positive degree. -/
lemma charpolyCoeff_one (hd : 0 < G.degree) (g : G.toSubgroup) :
    G.charpolyCoeff 1 g = -G.trace g := by
  have : Nonempty (Fin G.degree) := Fin.pos_iff_nonempty.mp hd
  simp [charpolyCoeff, coeff_reverse, revAt_le hd, trace, trace_eq_neg_charpoly_coeff]

lemma charpolyCoeff_of_lt {i : ℕ} (hi : G.degree < i) (g : G.toSubgroup) :
    G.charpolyCoeff i g = 0 := by
  rw [charpolyCoeff, coeff_reverse, G.natDegree_charpoly, revAt_eq_self_of_lt hi]
  exact coeff_eq_zero_of_natDegree_lt <| (G.natDegree_charpoly g).trans_lt hi

lemma trace_eq_powerSum_one (g : G.toSubgroup) : G.trace g = G.powerSum 1 g := by
  simpa [trace, powerSum] using (G.matrix g).trace_eq_sum_roots_charpoly

/-- **The zeroth moment is `1`** (LMFDB `st_group.moments`). -/
lemma moment_zero (X : G.toSubgroup → ℂ) : G.moment X 0 = 1 := by
  simp [moment, expectation]

end SatoTateGroup
