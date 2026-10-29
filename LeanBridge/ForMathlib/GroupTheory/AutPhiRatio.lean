import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The `φ`-ratio of a group

The `φ`-ratio of a finite group `G` is the order of its automorphism group divided by `φ(|G|)`,
Euler's totient of the order of `G`. For a cyclic group of order `n`, the automorphism group is
`(ℤ/nℤ)ˣ`, of order `φ(n)`, so the ratio is `1`.

## Main definitions

* `Group.autPhiRatio` (LMFDB `group.aut_phi_ratio`).

## Main results

* `IsCyclic.autPhiRatio_eq_one`: the `φ`-ratio of a finite cyclic group is `1`.
-/

variable (G : Type*) [Group G]

/-- The **`φ`-ratio** (LMFDB `group.aut_phi_ratio`) of a group `G`: the order `|Aut(G)|` of its
automorphism group divided by `φ(|G|)`, Euler's totient of the order of `G`, as a rational number.
The LMFDB considers finite groups only; for an infinite group, `Nat.card G = 0` and `φ(0) = 0`, so
the ratio is `0`. -/
noncomputable def Group.autPhiRatio : ℚ :=
  Nat.card (MulAut G) / (Nat.card G).totient

/-- **The `φ`-ratio of a finite cyclic group is `1`** (LMFDB `group.aut_phi_ratio`): the
automorphism group of a cyclic group of order `n` has order `φ(n)`. -/
lemma IsCyclic.autPhiRatio_eq_one [Finite G] [IsCyclic G] : Group.autPhiRatio G = 1 := by
  rw [Group.autPhiRatio, IsCyclic.card_mulAut, div_self]
  exact_mod_cast (Nat.totient_pos.mpr Nat.card_pos).ne'
