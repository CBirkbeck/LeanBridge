/- import Mathlib

noncomputable section

def min_poly : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C 1

abbrev K := AdjoinRoot min_poly

instance : Fact (Irreducible min_poly) := by
  refine { out := ?_ }
  simp [min_poly]

  sorry

axiom LMFDB_sdfsd : NumberField.IsCMField K := by sorry

end



 -/
