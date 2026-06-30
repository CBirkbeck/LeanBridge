import LeanBridge.Lookup.Lookup

open Lookup

example {F : Type*} [Field F] [NumberField F]
    (h1 : NumberField.classNumber F = 1) (h2 : Module.finrank ℚ F = 2) :
    |NumberField.discr F| ≤ 163 := by
  lookup

example {F : Type*} [Field F] [NumberField F]
    (h2 : Module.finrank ℚ F = 2) :
    NumberField.classNumber F = 4 →
      ClassGroup (NumberField.RingOfIntegers F) ≃* Multiplicative (ZMod 4) := by
  lookup

example {W : WeierstrassCurve.Affine ℚ} [W.IsElliptic]
    (hW : 4 ≤ Nat.card (AddCommGroup.torsion W.Point)) :
    Module.finrank ℤ W.Point ≤ 0 := by
  lookup

example {W : WeierstrassCurve.Affine ℚ} [W.IsElliptic]
    (hW : 2 ≤ Module.finrank ℤ W.Point) :
    Nat.card (AddCommGroup.torsion W.Point) = 1 := by
  lookup

example {W : WeierstrassCurve.Affine ℚ} [W.IsElliptic]
    (hW : Nat.card (AddCommGroup.torsion W.Point) = 4) :
    Nonempty (AddCommGroup.torsion W.Point ≃+ ZMod 4) := by
  lookup

example {G : Type*} [Group G] [IsSimpleGroup G] : ¬ ∀ a b : G, a * b = b * a := by
  lookup

example {W : WeierstrassCurve.Affine ℚ} [W.IsElliptic]
    (e : AddCommGroup.torsion W.Point ≃+ ZMod 2 × ZMod 8) :
    False := by
  lookup

example {W : WeierstrassCurve.Affine ℚ} [W.IsElliptic]
    (e : AddCommGroup.torsion W.Point ≃+ ZMod 2 × ZMod 10) :
    False := by
  lookup

-- modular forms: `M₂(Γ₀(11))` is nonzero (the newspace `11.2.a`), so its dimension is not `≤ 0`
example : Module.finrank ℂ
    (ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 11)) 2) ≤ 0 := by
  lookup

-- no quadratic field is unramified at every prime: some prime ramifies
example {F : Type*} [Field F] [NumberField F] (h : Module.finrank ℚ F = 2) :
    Nat.card {p : PrimeSpectrum (NumberField.RingOfIntegers F) //
      ¬ Algebra.IsUnramifiedAt ℤ p.asIdeal} = 0 := by
  lookup
