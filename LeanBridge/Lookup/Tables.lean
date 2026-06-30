import LeanBridge.Lookup.Basic

/-! # LMFDB table registry

The object families `lookup` knows about. **To support a new family, add a `TableInfo` here**
(and list it in `tables`); **to teach an existing family a new column or property, add a
recogniser** to its `scalars`/`props` using the combinators from `LeanBridge.Lookup.Basic`. -/

open Lean

namespace Lookup

/-- Number fields. -/
def nfFields : TableInfo where
  table := "nf_fields"
  labelCol := "label"
  descSelects := #["coeffs::text AS coeffs"]
  describe row := s!"number field {rowStr row "label"}, with minimal polynomial \
    {formatPoly (rowStr row "coeffs")}"
  url label := s!"https://www.lmfdb.org/NumberField/{label}"
  orderBy := "disc_abs"
  scalars := #[
    -- `NumberField.classNumber F`  ↦  class_number
    headIs ``NumberField.classNumber "class_number" "class number",
    -- `Module.finrank ℚ F`  ↦  degree
    finrankOver ``Rat "degree" "degree",
    -- `|NumberField.discr F|`  ↦  disc_abs
    absOf ``NumberField.discr "disc_abs" "|discriminant|",
    -- `NumberField.discr F`  ↦  disc_sign · disc_abs  (signed, sign-split on comparison)
    signedValue ``NumberField.discr "disc_sign" "disc_abs" "discriminant",
    -- `NumberField.rootDiscr F`  ↦  rd
    headIs ``NumberField.rootDiscr "rd" "root discriminant",
    -- `NumberField.Units.regulator F`  ↦  regulator
    headIs ``NumberField.Units.regulator "regulator" "regulator",
    -- `NumberField.Units.torsionOrder F`  ↦  torsion_order (number of roots of unity)
    headIs ``NumberField.Units.torsionOrder "torsion_order" "number of roots of unity",
    -- `NumberField.InfinitePlace.nrComplexPlaces F`  ↦  r2
    headIs ``NumberField.InfinitePlace.nrComplexPlaces "r2" "number of complex places"]
  props := #[
    -- `ClassGroup (𝓞 F) ≃* Multiplicative (∏ ZMod nᵢ)`  ↦  class_group = [n₁, …]
    isoStructure ``MulEquiv ``ClassGroup "class_group::text" "class group" true,
    -- additive spelling: `Additive (ClassGroup (𝓞 F)) ≃+ (∏ ZMod nᵢ)`  ↦  class_group = [n₁, …]
    isoStructure ``AddEquiv ``ClassGroup "class_group::text" "class group" true,
    -- `NumberField.IsCMField F`  ↦  cm = 't'
    flagIs ``NumberField.IsCMField "cm",
    -- `IsGalois ℚ F`  ↦  is_galois = 't'
    flagIs ``IsGalois "is_galois",
    -- `IsAbelianGalois ℚ F`  ↦  gal_is_abelian = 't'
    flagIs ``IsAbelianGalois "gal_is_abelian",
    -- `NumberField.IsTotallyReal F`  ↦  no real-place column: r2 = 0
    flagCond ``NumberField.IsTotallyReal "r2 = 0" "r2 <> 0" #[("r2", "r2")],
    -- `NumberField.IsTotallyComplex F`  ↦  r1 = 0, i.e. degree = 2·r2 (no r1 column)
    flagCond ``NumberField.IsTotallyComplex "degree = 2 * r2" "degree <> 2 * r2"
      #[("degree", "degree"), ("r2", "r2")],
    -- `Algebra.IsQuadraticExtension ℚ F`  ↦  degree = 2
    flagCond ``Algebra.IsQuadraticExtension "degree = 2" "degree <> 2" #[("degree", "degree")],
    -- `IsPrincipalIdealRing (𝓞 F)`  ↦  class_number = 1  (trivial class group)
    flagCondMentions ``IsPrincipalIdealRing ``NumberField.RingOfIntegers
      "class_number = 1" "class_number <> 1" #[("class_number", "class_number")]]

/-- Elliptic curves over `ℚ`. -/
def ecCurvedata : TableInfo where
  table := "ec_curvedata"
  labelCol := "lmfdb_label"
  descSelects := #["ainvs::text AS ainvs"]
  describe row := s!"elliptic curve {rowStr row "label"}: {formatWeierstrass (rowStr row "ainvs")}"
  -- LMFDB EC labels like `15.a2` live at `.../EllipticCurve/Q/15/a/2`.
  url label :=
    match label.splitOn "." with
    | [conductor, iso] =>
        s!"https://www.lmfdb.org/EllipticCurve/Q/{conductor}/\
          {iso.takeWhile Char.isAlpha}/{iso.dropWhile Char.isAlpha}"
    | _ => s!"https://www.lmfdb.org/EllipticCurve/Q/{label}"
  orderBy := "conductor"
  scalars := #[
    -- `Module.finrank ℤ W.Point`  ↦  rank
    finrankOver ``Int "rank" "rank",
    -- `Nat.card (AddCommGroup.torsion W.Point)`  ↦  torsion
    cardMentions ``AddCommGroup.torsion "torsion" "torsion",
    -- `WeierstrassCurve.j W`  ↦  jinv  (model-independent, so exact)
    headIs ``WeierstrassCurve.j "jinv" "j-invariant"]
  props := #[
    -- `AddCommGroup.torsion W.Point ≃+ (∏ ZMod nᵢ)`  ↦  torsion_structure = {n₁, …}
    isoStructure ``AddEquiv ``AddCommGroup.torsion "torsion_structure" "torsion structure" false,
    -- `Finite W.Point`  ↦  rank = 0  (Mordell–Weil group finite ⟺ rank zero)
    flagCondMentions ``Finite ``WeierstrassCurve.Affine.Point "rank = 0" "rank <> 0"
      #[("rank", "rank")],
    -- `IsAddTorsionFree W.Point`  ↦  torsion = 1
    flagCondMentions ``IsAddTorsionFree ``WeierstrassCurve.Affine.Point "torsion = 1" "torsion <> 1"
      #[("torsion", "torsion")]]

/-- Finite groups. -/
def gpsGroups : TableInfo where
  table := "gps_groups"
  labelCol := "label"
  descSelects := #["tex_name::text AS tex_name"]
  describe row := s!"group {rowStr row "label"} ({rowStr row "tex_name"})"
  url label := s!"https://www.lmfdb.org/Groups/Abstract/{label}"
  -- `order` is a SQL reserved word, so it must be quoted.
  orderBy := "\"order\""
  scalars := #[
    -- `Monoid.exponent G`  ↦  exponent
    headIs ``Monoid.exponent "exponent" "exponent",
    -- `Group.nilpotencyClass G`  ↦  nilpotency_class
    headIs ``Group.nilpotencyClass "nilpotency_class" "nilpotency class",
    -- `Group.rank G`  ↦  rank (minimal number of generators)
    headIs ``Group.rank "rank" "rank",
    -- `Nat.card (Subgroup.center G)`  ↦  center_order
    cardMentions ``Subgroup.center "center_order" "order of the center",
    -- `Nat.card (ConjClasses G)`  ↦  number_conjugacy_classes
    cardMentions ``ConjClasses "number_conjugacy_classes" "number of conjugacy classes",
    -- `Nat.card (MulAut G)`  ↦  aut_order
    cardMentions ``MulAut "aut_order" "order of the automorphism group",
    -- `Nat.card G` / `Fintype.card G`  ↦  order  (generic cardinality; last, so the
    -- `cardMentions` recognisers above claim the cardinalities of named subobjects first)
    cardIs "\"order\"" "order"]
  props := #[
    -- `IsSimpleGroup G`  ↦  simple = 't'
    flagIs ``IsSimpleGroup "simple",
    -- `∀ a b : G, a * b = b * a`  ↦  abelian = 't'
    isAbelian "abelian",
    -- a `CommGroup G` / `AddCommGroup G` hypothesis  ↦  abelian = 't'
    flagIs ``CommGroup "abelian",
    flagIs ``AddCommGroup "abelian",
    -- `Group.IsNilpotent G`  ↦  nilpotent = 't'
    flagIs ``Group.IsNilpotent "nilpotent",
    -- `Group.IsPerfect G`  ↦  perfect = 't'
    flagIs ``Group.IsPerfect "perfect",
    -- `IsCyclic G`  ↦  cyclic = 't'  (generic head, but no other table recognises `IsCyclic`)
    flagIs ``IsCyclic "cyclic",
    -- `IsSolvable G`  ↦  solvable = 't'
    flagIs ``IsSolvable "solvable"]

/-- All supported object families. To support a new one, add its `TableInfo` here. -/
def tables : Array TableInfo := #[nfFields, ecCurvedata, gpsGroups]

/-- The table configuration for a table name. -/
def tableInfo? (name : String) : Option TableInfo := tables.find? (·.table == name)

end Lookup
