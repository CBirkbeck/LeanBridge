import LeanBridge.Lookup.Lookup

open Lookup

example {F : Type*} [Field F] [NumberField F]
    (h1 : NumberField.classNumber F = 1) (h2 : Module.finrank ℚ F = 2) :
    |NumberField.discr F| ≤ 163 := by
  lookup

example {F : Type*} [Field F] [NumberField F]
    (h1 : NumberField.classNumber F = 4) (h2 : Module.finrank ℚ F = 2) :
    Nonempty (ClassGroup (NumberField.RingOfIntegers F) ≃* Multiplicative (ZMod 4)) := by
  lookup

example {W : WeierstrassCurve.Affine ℚ}
    (hW : 4 ≤ Nat.card (AddCommGroup.torsion W.Point)) :
    Module.finrank ℤ W.Point ≤ 0 := by
  lookup

example {W : WeierstrassCurve.Affine ℚ}
    (hW : 2 ≤ Module.finrank ℤ W.Point) :
    Nat.card (AddCommGroup.torsion W.Point) = 1 := by
  lookup

example {W : WeierstrassCurve.Affine ℚ}
    (hW : Nat.card (AddCommGroup.torsion W.Point) = 4) :
    Nonempty (AddCommGroup.torsion W.Point ≃+ ZMod 4) := by
  lookup

example {G : Type*} [Group G] [IsSimpleGroup G] : ¬ ∀ a b : G, a * b = b * a := by
  lookup
