import IdealArithmetic.Galois.Examples.DegSixA4C2

/-!
# Galois-group certificates (bridged from `CertifyingInvariantsNF`)

This module makes the Galois-group certification library
(`IdealArithmetic.Galois`, developed in the `CertifyingInvariantsNF` project)
available inside LeanBridge, linking LMFDB Galois-group data (`nTk` labels) to
formal Lean proofs.

The showcase result, re-exported below: the degree-6 number field
`ℚ[x]/(x⁶ − 5x⁴ − 50x² + 125)` has Galois group `A₄ × C₂` — the transitive
group `6T6`, of order `24`. The underlying library also provides reusable
machinery (Dedekind/Frobenius cycle-type certificates, the discriminant square
test, cubic Galois-group determination) not re-exported here.
-/

namespace LeanBridge.Galois

open Polynomial IdealArithmetic.Galois.DegSix

/-- **`6T6`.** The Galois group of `x⁶ − 5x⁴ − 50x² + 125` over `ℚ` is isomorphic
to `A₄ × C₂`. Bridged from `IdealArithmetic.Galois.DegSix`. -/
theorem galoisGroup_degSix_isA4timesC2 :
    Nonempty ((f.map (Int.castRingHom ℚ)).Gal ≃*
      alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) :=
  gal_f_mulEquiv

/-- The Galois group of that degree-6 field has order `24`. -/
theorem galoisGroup_degSix_card : Nat.card (f.map (Int.castRingHom ℚ)).Gal = 24 :=
  card_gal_f

end LeanBridge.Galois
