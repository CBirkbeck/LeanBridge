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
    signedValue ``NumberField.discr "disc_sign" "disc_abs" "discriminant"]
  props := #[
    -- `ClassGroup (𝓞 F) ≃* Multiplicative (∏ ZMod nᵢ)`  ↦  class_group = [n₁, …]
    isoStructure ``MulEquiv ``ClassGroup "class_group::text" "class group" true,
    -- additive spelling: `Additive (ClassGroup (𝓞 F)) ≃+ (∏ ZMod nᵢ)`  ↦  class_group = [n₁, …]
    isoStructure ``AddEquiv ``ClassGroup "class_group::text" "class group" true]

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
    cardMentions ``AddCommGroup.torsion "torsion" "torsion"]
  props := #[
    -- `AddCommGroup.torsion W.Point ≃+ (∏ ZMod nᵢ)`  ↦  torsion_structure = {n₁, …}
    isoStructure ``AddEquiv ``AddCommGroup.torsion "torsion_structure" "torsion structure" false]

/-- Finite groups. -/
def gpsGroups : TableInfo where
  table := "gps_groups"
  labelCol := "label"
  descSelects := #["tex_name::text AS tex_name"]
  describe row := s!"group {rowStr row "label"} ({rowStr row "tex_name"})"
  url label := s!"https://www.lmfdb.org/Groups/Abstract/{label}"
  -- `order` is a SQL reserved word, so it must be quoted.
  orderBy := "\"order\""
  props := #[
    -- `IsSimpleGroup G`  ↦  simple = 't'
    flagIs ``IsSimpleGroup "simple",
    -- `∀ a b : G, a * b = b * a`  ↦  abelian = 't'
    isAbelian "abelian"]

/-- All supported object families. To support a new one, add its `TableInfo` here. -/
def tables : Array TableInfo := #[nfFields, ecCurvedata, gpsGroups]

/-- The table configuration for a table name. -/
def tableInfo? (name : String) : Option TableInfo := tables.find? (·.table == name)

end Lookup
