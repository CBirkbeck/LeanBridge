import LeanBridge.ForMathlib.RepresentationTheory.FaithfulDegree
import Mathlib.LinearAlgebra.Matrix.Permutation
import TauCeti.Algebra.GroupAction.PermutationRepresentation

/-!
# The least positive degree of a faithful matrix representation

The LMFDB's minimal degree of a faithful complex, or rational, representation of a group `G`
(LMFDB `group.min_complex_rep_deg`, `group.min_rational_rep_deg`) is the smallest positive integer
`d` such that `G` admits a faithful representation `G ↪ GL_d(ℂ)`, or `G ↪ GL_d(ℚ)`. LeanBridge's
`linearDegree R G` takes the least `n`, positive or not, with a faithful `G ↪ GL_n(R)`; for the
trivial group it is `0`, the map to the trivial group `GL_0(R)` being injective, where the knowls
give `1`. Here `minFaithfulDegree R G` is the least positive such `n`.
It agrees with `linearDegree R G` for a nontrivial group and is `1` for the trivial group, and for
a finite group and a nontrivial ring it is attained, by the regular representation through
permutation matrices.

## Main definitions

* `minFaithfulDegree` (LMFDB `group.min_complex_rep_deg` for `R = ℂ`,
  `group.min_rational_rep_deg` for `R = ℚ`): the least positive degree of a faithful matrix
  representation.

## Main results

* `isLeast_minFaithfulDegree`: for a finite group and a nontrivial ring, `minFaithfulDegree R G` is
  the least positive degree of a faithful matrix representation.
* `minFaithfulDegree_eq_linearDegree`: it is `linearDegree R G` for a nontrivial group.
* `minFaithfulDegree_eq_one`: it is `1` for the trivial group.
* `minFaithfulDegree_eq_max_linearDegree_one`: `minFaithfulDegree R G = max (linearDegree R G) 1`
  for a finite group and a nontrivial ring.
-/

open Equiv Function Matrix

variable {R G : Type*} [CommRing R] [Group G] {n : ℕ} {ρ : G →* GL (Fin n) R}

lemma Matrix.permMatrix_injective {ι : Type*} [DecidableEq ι] [Nontrivial R] :
    Injective fun σ : Perm ι ↦ σ.permMatrix R :=
  fun _ _ h ↦ Equiv.ext fun a ↦ by simpa using congrArg (· a) (PEquiv.toMatrix_injective h)

variable (R G) in
/-- The **least positive degree of a faithful matrix representation** of a group `G` over a ring
`R` (LMFDB `group.min_complex_rep_deg` for `R = ℂ`, `group.min_rational_rep_deg` for `R = ℚ`): the
smallest positive integer `d` such that `G` has a faithful representation `G ↪ GL_d(R)`. For a
finite group and a nontrivial ring it is attained (`isLeast_minFaithfulDegree`), by the regular
representation; when `G` has no faithful representation of positive degree it is `0` by
convention. Unlike `linearDegree R G`, it is `1`, not `0`, for the trivial group. -/
noncomputable def minFaithfulDegree : ℕ :=
  sInf {n | 0 < n ∧ ∃ ρ : G →* GL (Fin n) R, Injective ρ}

lemma minFaithfulDegree_le (hn : 0 < n) (hρ : Injective ρ) : minFaithfulDegree R G ≤ n :=
  Nat.sInf_le ⟨hn, ρ, hρ⟩

lemma pos_of_injective_generalLinearGroup [Nontrivial G] (hρ : Injective ρ) : 0 < n := by
  refine Nat.pos_of_ne_zero fun hn ↦ not_subsingleton G ?_
  subst hn
  exact hρ.subsingleton

variable (R G)

/-- **The least positive degree of a faithful representation of a nontrivial group is its linear
degree** `linearDegree R G`: the trivial group `GL_0(R)` receives no injective map from `G`. -/
lemma minFaithfulDegree_eq_linearDegree [Nontrivial G] : minFaithfulDegree R G = linearDegree R G :=
  congrArg sInf <| Set.ext fun _ ↦
    ⟨fun h ↦ h.2, fun ⟨ρ, hρ⟩ ↦ ⟨pos_of_injective_generalLinearGroup hρ, ρ, hρ⟩⟩

lemma linearDegree_eq_zero [Subsingleton G] : linearDegree R G = 0 :=
  Nat.eq_zero_of_le_zero <| Nat.sInf_le (s := {n | ∃ ρ : G →* GL (Fin n) R, Injective ρ})
    ⟨1, injective_of_subsingleton _⟩

/-- **The least positive degree of a faithful representation of the trivial group is `1`**, where
`linearDegree R G = 0` (`linearDegree_eq_zero`). -/
lemma minFaithfulDegree_eq_one [Subsingleton G] : minFaithfulDegree R G = 1 := by
  have h : 1 ∈ {n | 0 < n ∧ ∃ ρ : G →* GL (Fin n) R, Injective ρ} :=
    ⟨one_pos, 1, injective_of_subsingleton _⟩
  exact (Nat.sInf_le h).antisymm (Nat.sInf_mem ⟨1, h⟩).1

variable [Finite G] [Nontrivial R]

lemma toHomUnits_permMatrixHom_comp_injective :
    Injective (permMatrixHom.toHomUnits.comp (permutationRepresentation (Finite.equivFin G)) :
      G →* GL (Fin (Nat.card G)) R) :=
  fun _ _ h ↦ permutationRepresentation_injective (Finite.equivFin G) <| inv_injective <|
    permMatrix_injective (R := R) <| by simpa using congrArg Units.val h

/-- **The least positive degree of a faithful representation is attained** for a finite group
`G` and a nontrivial ring `R`: it is the least positive `d` such that `G` has a faithful
representation `G ↪ GL_d(R)` (LMFDB `group.min_complex_rep_deg`, `group.min_rational_rep_deg`).
The regular representation, through permutation matrices, is faithful of degree `|G|`. -/
lemma isLeast_minFaithfulDegree :
    IsLeast {n | 0 < n ∧ ∃ ρ : G →* GL (Fin n) R, Injective ρ} (minFaithfulDegree R G) :=
  ⟨Nat.sInf_mem ⟨_, Nat.card_pos, _, toHomUnits_permMatrixHom_comp_injective R G⟩,
    fun _ h ↦ Nat.sInf_le h⟩

/-- **`minFaithfulDegree R G = max (linearDegree R G) 1`** for a finite group `G` and a nontrivial
ring `R`: the two agree except for the trivial group. -/
lemma minFaithfulDegree_eq_max_linearDegree_one :
    minFaithfulDegree R G = max (linearDegree R G) 1 := by
  rcases subsingleton_or_nontrivial G with hG | hG
  · rw [minFaithfulDegree_eq_one, linearDegree_eq_zero, max_eq_right zero_le_one]
  · rw [← minFaithfulDegree_eq_linearDegree, max_eq_left (isLeast_minFaithfulDegree R G).1.1]
