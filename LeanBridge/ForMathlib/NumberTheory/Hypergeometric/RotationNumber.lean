import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.CuspIndex
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The rotation number of a hypergeometric family

The defining parameters `(A, B)` of a hypergeometric family give two multisets of roots of unity:
the primitive `a`-th roots of unity for the entries `a` of `A`, with multiplicity, and likewise for
`B`. Their common rotational symmetry group `R` is the group of `ζ ∈ ℂ^×` with `ζ S_A = S_A` and
`ζ S_B = S_B`, and the rotation number is its order.

## Main definitions

* `Hypergeometric.CuspIndex.rootsOfUnity`: the multiset `S_C` of a cusp-index `C`.
* `Hypergeometric.Parameters.rotationGroup` (LMFDB `hgm.rotation_number`): the group `R`.
* `Hypergeometric.Parameters.rotationNumber` (LMFDB `hgm.rotation_number`,
  `hgm.imprimitivity_index`): the rotation number `#R`.

## Main results

* `Hypergeometric.Parameters.finite_rotationGroup`: for positive degree, `R` is finite.
* `Hypergeometric.Parameters.rotationNumber_pos`: for positive degree, the rotation number is
  positive.
-/

namespace Hypergeometric

variable {d : ℕ} (c : CuspIndex d) (P : Parameters d)

/-- The multiset `S_C` of roots of unity of a cusp-index `C` (LMFDB `hgm.rotation_number`): the
primitive `c`-th roots of unity in `ℂ` for the entries `c` of `C`, repeated according to their
multiplicities in `C`. -/
noncomputable def CuspIndex.rootsOfUnity : Multiset ℂ :=
  (c.toList : Multiset ℕ).bind fun a ↦ (primitiveRoots a ℂ).val

lemma multiset_map_mul_map_mul (ζ η : ℂ) (S : Multiset ℂ) :
    (S.map (η * ·)).map (ζ * ·) = S.map (ζ * η * ·) := by
  simp [Multiset.map_map, mul_assoc]

/-- The **rotational symmetry group** `R` of a hypergeometric family with defining parameters
`(A, B)` (LMFDB `hgm.rotation_number`): the subgroup of the `ζ ∈ ℂ^×` with `ζ S_A = S_A` and
`ζ S_B = S_B`, as multisets. For positive degree its elements are roots of unity, as they map a
root of unity to a root of unity. -/
def Parameters.rotationGroup : Subgroup ℂˣ where
  carrier := {ζ | P.A.rootsOfUnity.map ((ζ : ℂ) * ·) = P.A.rootsOfUnity ∧
    P.B.rootsOfUnity.map ((ζ : ℂ) * ·) = P.B.rootsOfUnity}
  mul_mem' {ζ η} hζ hη := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, ← multiset_map_mul_map_mul] at *
    rw [hη.1, hζ.1, hη.2, hζ.2]
    exact ⟨rfl, rfl⟩
  one_mem' := by simp
  inv_mem' {ζ} hζ := by
    simp only [Set.mem_ofPred_eq] at *
    nth_rw 1 [← hζ.1, ← hζ.2]
    simp

/-- The **rotation number** of a hypergeometric family (LMFDB `hgm.rotation_number`, also stated as
`hgm.imprimitivity_index`): the order of its rotational symmetry group `R`
(`Hypergeometric.Parameters.rotationGroup`). For positive degree the group is finite
(`Hypergeometric.Parameters.finite_rotationGroup`), so this is a positive integer; for degree `0`,
where `A` and `B` are empty, the group is all of `ℂ^×` and `Nat.card` gives the junk value `0`. -/
noncomputable def Parameters.rotationNumber : ℕ :=
  Nat.card P.rotationGroup

lemma CuspIndex.card_rootsOfUnity : Multiset.card c.rootsOfUnity = d := by
  simpa [CuspIndex.rootsOfUnity, Function.comp_def, Complex.card_primitiveRoots] using c.sum_totient

/-- **The rotational symmetry group of a family of positive degree is finite**: it maps a root of
unity `s ∈ S_A` into the finite multiset `S_A`. -/
lemma Parameters.finite_rotationGroup (hd : d ≠ 0) : Finite P.rotationGroup := by
  rcases Multiset.card_pos_iff_exists_mem.mp (P.A.card_rootsOfUnity.symm ▸ Nat.pos_of_ne_zero hd)
    with ⟨s, hs⟩
  refine Set.Finite.subset (s := (fun ζ : ℂˣ ↦ (ζ : ℂ) * s) ⁻¹' P.A.rootsOfUnity.toFinset) ?_
    fun ζ hζ ↦ ?_
  · have hs0 : s ≠ 0 := by
      rcases Multiset.mem_bind.mp hs with ⟨a, ha, has⟩
      exact ((mem_primitiveRoots <| P.A.pos a ha).mp has).ne_zero (P.A.pos a ha).ne'
    exact P.A.rootsOfUnity.toFinset.finite_toSet.preimage (f := fun ζ : ℂˣ ↦ (ζ : ℂ) * s)
      fun ζ _ η _ h ↦ Units.val_injective <| mul_right_cancel₀ hs0 h
  · rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, ← hζ.1]
    exact Multiset.mem_map_of_mem _ hs

/-- **The rotation number of a family of positive degree is positive.** -/
lemma Parameters.rotationNumber_pos (hd : d ≠ 0) : 0 < P.rotationNumber :=
  have : Finite P.rotationGroup := P.finite_rotationGroup hd
  Nat.card_pos

end Hypergeometric
