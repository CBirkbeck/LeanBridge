import LeanBridge.Lookup.Lookup

/-! # `lookup` demo

Each example below is a *false* statement; `lookup` finds and reports a counterexample from
LMFDB (the smallest one, with the object's defining data and a clickable link), so each
`example` is expected to error with that report. -/

open Lookup

-- Number fields. "Every number field of class number 1 and degree 2 has |discriminant| ≤ 163"
-- is false (the bound is the *imaginary* quadratic class-number-1 theorem; real quadratic
-- fields have unbounded discriminant). `lookup` surfaces `2.2.172.1`.
example {F : Type*} [Field F] [NumberField F]
    (h1 : NumberField.classNumber F = 1) (h2 : Module.finrank ℚ F = 2) :
    |NumberField.discr F| ≤ 163 := by
  lookup

-- Signed-discriminant queries are supported too (the DB stores `disc_sign * disc_abs`, and
-- `lookup` case-splits on the sign so the query stays index-friendly):
-- `NumberField.discr F ≥ -100` finds the counterexample `2.0.163.1` (discriminant -163),
-- while `NumberField.discr F ≥ -163` finds none.

-- The ideal class group *structure* (LMFDB's `class_group`) is supported via `≃*`: "every
-- degree-2 field of class number 4 has cyclic class group ℤ/4" is false — some are C₂ × C₂.
-- The class group is multiplicative, so the right-hand side carries `Multiplicative`.
example {F : Type*} [Field F] [NumberField F]
    (h1 : NumberField.classNumber F = 4) (h2 : Module.finrank ℚ F = 2) :
    Nonempty (ClassGroup (NumberField.RingOfIntegers F) ≃* Multiplicative (ZMod 4)) := by
  lookup

-- Elliptic curves: `lookup` dispatches to `ec_curvedata`. "Every curve with a 4-torsion point
-- has rank ≤ 0" is false — e.g. `117.a3` has a 4-torsion point and positive rank.
example {W : WeierstrassCurve.Affine ℚ}
    (hW : 4 ≤ Nat.card (AddCommGroup.torsion W.Point)) :
    Module.finrank ℤ W.Point ≤ 0 := by
  lookup

-- "Every elliptic curve over ℚ with rank at least 2 has trivial torsion subgroup" is false:
-- e.g. `1088.a1` has rank 2 and a 2-torsion point.
example {W : WeierstrassCurve.Affine ℚ}
    (hW : 2 ≤ Module.finrank ℤ W.Point) :
    Nat.card (AddCommGroup.torsion W.Point) = 1 := by
  lookup

-- Torsion subgroup *structure* (LMFDB's `torsion_structure`): "every curve whose torsion
-- subgroup has order 4 has torsion subgroup ≅ ℤ/4" is false — some are ℤ/2 × ℤ/2. The torsion
-- subgroup is additive, hence `≃+`.
example {W : WeierstrassCurve.Affine ℚ}
    (hW : Nat.card (AddCommGroup.torsion W.Point) = 4) :
    Nonempty (AddCommGroup.torsion W.Point ≃+ ZMod 4) := by
  lookup

-- Groups: `lookup` dispatches boolean properties to `gps_groups`. "Every simple group is
-- nonabelian" is false — the cyclic groups of prime order are simple and abelian.
example {G : Type*} [Group G] [IsSimpleGroup G] : ¬ ∀ a b : G, a * b = b * a := by
  lookup
