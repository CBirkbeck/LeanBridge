import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolStopSign

/-!
# The label of the genus of an integral lattice, without parameters

The label of a genus of integral lattices (LMFDB `lattice.genus_label`), `r.s.d.j₁.⋯.jₖ.x`, is an
encoding of the Conway genus symbol (LMFDB `lattice.conway_genus_symbol`): the rank, the
signature, the absolute determinant, the Jordan ranks, the types of the dyadic constituents, the
oddities of the compartments and the signs of the trains of the canonical `2`-adic symbol, and the
signs at the odd primes. The encoding `TauCeti.IntegralLattice.genusLabel` of
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusLabel` takes the compartment oddities and the
train signs as parameters. Here they are those of the canonical `2`-adic symbol of the lattice
(`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolCanonical`), computed from its chosen
dyadic Jordan splitting by oddity fusion and sign walking, which makes the label a function of the
lattice alone. There are as many compartment oddities and train signs as the encoding reads.

Every input of the label but the compartment oddities is a genus invariant, the train signs by
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolStopSign`. So the label is a genus invariant
as soon as the compartment oddities are, which is proved when the `2`-adic symbol has no
compartment (all its constituents have type `II`) and when the dyadic localization is modular, for
instance when the determinant is odd. In general it is proved in
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolGaussSum`
(`TauCeti.IntegralLattice.SameGenus.canonicalGenusLabel_congr`), through the Gauss oddities of
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolOddity` and dyadic Gauss sums.

## Main definitions

* `TauCeti.IntegralLattice.canonicalGenusLabel` (LMFDB `lattice.genus_label`): the label of the
  genus of a lattice.

## Main results

* `TauCeti.IntegralLattice.SameGenus.canonicalGenusLabel_eq`: lattices in the same genus whose
  canonical `2`-adic symbols have the same compartment oddities have the same label.
* `TauCeti.IntegralLattice.SameGenus.canonicalGenusLabel_eq_of_compartmentOddities_eq_nil`: the
  label of a lattice whose `2`-adic symbol has no compartment is a genus invariant.
* `TauCeti.IntegralLattice.SameGenus.canonicalGenusLabel_eq_of_jordanRank_eq_zero`: the label of a
  lattice with a modular dyadic localization is a genus invariant.
* `TauCeti.IntegralLattice.SameGenus.canonicalGenusLabel_eq_of_odd`: the label of a lattice of odd
  determinant is a genus invariant.
-/

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]

variable (L) in
/-- The **label of the genus** (LMFDB `lattice.genus_label`) of a nondegenerate integral lattice
`L`, `r.s.d.j₁.⋯.jₖ.x`: the encoding `TauCeti.IntegralLattice.genusLabel` of its rank, signature,
absolute determinant, Jordan ranks, signs at the odd primes, dyadic types, and the oddities of the
compartments and the signs of the trains of its canonical `2`-adic symbol, computed from the
chosen dyadic Jordan splitting by oddity fusion and sign walking. -/
noncomputable def canonicalGenusLabel : String :=
  L.genusLabel (L.compartmentOddities.getD · 0) (L.trainSigns.getD · 1)

/-- **The label is a genus invariant once the compartment oddities are**: lattices in the same
genus whose canonical `2`-adic symbols have the same compartment oddities have the same label, the
other inputs of the label, the train signs included, being genus invariants. -/
lemma SameGenus.canonicalGenusLabel_eq (h : L.SameGenus M)
    (hodd : L.compartmentOddities = M.compartmentOddities) :
    L.canonicalGenusLabel = M.canonicalGenusLabel := by
  rw [canonicalGenusLabel, canonicalGenusLabel, hodd, h.trainSigns_eq, h.genusLabel_eq]

/-- **The label of a lattice whose `2`-adic symbol has no compartment is a genus invariant**: if
all the dyadic Jordan constituents of `L` have type `II`, lattices in the genus of `L` have the
same label. -/
lemma SameGenus.canonicalGenusLabel_eq_of_compartmentOddities_eq_nil (h : L.SameGenus M)
    (hL : L.compartmentOddities = []) : L.canonicalGenusLabel = M.canonicalGenusLabel :=
  h.canonicalGenusLabel_eq <| hL.trans (List.length_eq_zero_iff.mp <|
    h.length_compartmentOddities_eq ▸ congrArg List.length hL).symm

/-- **The label of a lattice with a modular dyadic localization is a genus invariant**: if the
dyadic Jordan decompositions of `L` have a single nonzero constituent, lattices in the genus of
`L` have the same label. -/
lemma SameGenus.canonicalGenusLabel_eq_of_jordanRank_eq_zero (h : L.SameGenus M) {k : ℕ}
    (hk : ∀ j, j ≠ k → L.jordanRank 2 j = 0) : L.canonicalGenusLabel = M.canonicalGenusLabel :=
  h.canonicalGenusLabel_eq
    (congrArg (fun l ↦ (DyadicBlock.compartments l).map (DyadicBlock.canonicalOddity l))
      (h.dyadicConstituents_eq_of_jordanRank_eq_zero k hk))

/-- **The label of a lattice of odd determinant is a genus invariant.** -/
lemma SameGenus.canonicalGenusLabel_eq_of_odd (h : L.SameGenus M) (hL : Odd L.determinant) :
    L.canonicalGenusLabel = M.canonicalGenusLabel :=
  h.canonicalGenusLabel_eq_of_jordanRank_eq_zero fun j hj ↦
    L.jordanRank_eq_zero_of_lt 2 <| by
      rw [Nat.factorization_eq_zero_of_not_dvd (Int.natAbs_odd.mpr hL).not_two_dvd_nat]
      exact Nat.pos_of_ne_zero hj

end TauCeti.IntegralLattice
