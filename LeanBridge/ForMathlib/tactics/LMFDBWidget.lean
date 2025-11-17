import Lean
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.HtmlDisplay
import Lean.Data.Json
import Mathlib

open Lean Server ProofWidgets Jsx System

namespace LMFDBWidget

/-- Search parameters for LMFDB query -/
structure SearchParams where
  -- Basic parameters
  degree_min : Option Nat := none
  degree_max : Option Nat := none
  signature : Option String := none

  -- Discriminant
  disc_abs_min : Option Nat := none
  disc_abs_max : Option Nat := none
  disc_sign : Option Int := none

  -- Root discriminants
  rd_min : Option Float := none
  rd_max : Option Float := none
  grd_min : Option Float := none
  grd_max : Option Float := none

  -- Complex places
  r2_min : Option Nat := none
  r2_max : Option Nat := none

  -- Class numbers
  class_number : Option Nat := none
  narrow_class_number : Option Nat := none
  class_group : Option String := none
  narrow_class_group : Option String := none

  -- Galois properties
  is_galois : Option Bool := none
  galois_label : Option String := none
  gal_is_abelian : Option Bool := none
  gal_is_cyclic : Option Bool := none
  gal_is_solvable : Option Bool := none

  -- Ramification
  num_ram_min : Option Nat := none
  num_ram_max : Option Nat := none
  ramps : Option String := none
  unramified_primes : Option String := none
  inessentialp : Option String := none

  -- Other properties
  cm : Option Bool := none
  monogenic : Option Bool := none
  is_minimal_sibling : Option Bool := none

  -- Regulator
  regulator_min : Option Float := none
  regulator_max : Option Float := none

  -- Display
  limit : Nat := 50
  deriving Inhabited, Lean.ToJson, Lean.FromJson, Repr

/-- A number field result from LMFDB -/
structure NumberFieldResult where
  label : String
  class_number : Nat
  is_galois : Bool
  coeffs : String
  disc_abs : Nat
  disc_sign : Int
  cm : Bool
  deriving Inhabited, Lean.ToJson, Lean.FromJson, Repr

/-- Parameters for generating Lean files -/
structure GenerateParams where
  fields : Array NumberFieldResult
  generateUnits : Bool
  deriving Inhabited, Lean.ToJson, Lean.FromJson, Repr

-- Helper functions
def getSageCondaEnv : IO String := do
  match (← IO.getEnv "LMFDB_SAGE_CONDA_ENV") with
  | some env => return env
  | none => return "sage"

def findCondaPython (envName : String) : IO String := do
  let condaInfo ← IO.Process.output {
    cmd := "conda",
    args := #["info", "--base"],
    stdin := .null,
    stdout := .piped,
    stderr := .piped
  }

  if condaInfo.exitCode == 0 then
    let condaBase := condaInfo.stdout.trim
    let pythonPath := s!"{condaBase}/envs/{envName}/bin/python"
    let pathExists ← System.FilePath.pathExists pythonPath
    if pathExists then
      return pythonPath

  throw <| IO.userError s!"Could not find Python in conda environment '{envName}'"

def findCondaSage (envName : String) : IO String := do
  let condaInfo ← IO.Process.output {
    cmd := "conda",
    args := #["info", "--base"],
    stdin := .null,
    stdout := .piped,
    stderr := .piped
  }

  if condaInfo.exitCode != 0 then
    throw <| IO.userError "Could not find conda installation"

  let condaBase := condaInfo.stdout.trim
  let sagePath := s!"{condaBase}/envs/{envName}/bin/sage"

  let pathExists ← System.FilePath.pathExists sagePath
  if pathExists then
    return sagePath
  else
    throw <| IO.userError s!"Sage not found in conda environment '{envName}'"

/-- Build JSON object from search parameters -/
def buildJsonQuery (params : SearchParams) : Lean.Json := Id.run do
  let mut fields : Array (String × Lean.Json) := #[]

  -- Degree
  if let some v := params.degree_min then
    fields := fields.push ("degree_min", Lean.toJson v)
  if let some v := params.degree_max then
    fields := fields.push ("degree_max", Lean.toJson v)

  -- Signature
  if let some v := params.signature then
    fields := fields.push ("signature", Lean.toJson v)

  -- Discriminant
  if let some v := params.disc_abs_min then
    fields := fields.push ("disc_abs_min", Lean.toJson v)
  if let some v := params.disc_abs_max then
    fields := fields.push ("disc_abs_max", Lean.toJson v)
  if let some v := params.disc_sign then
    fields := fields.push ("disc_sign", Lean.toJson v)

  -- Root discriminants
  if let some v := params.rd_min then
    fields := fields.push ("rd_min", Lean.toJson v)
  if let some v := params.rd_max then
    fields := fields.push ("rd_max", Lean.toJson v)
  if let some v := params.grd_min then
    fields := fields.push ("grd_min", Lean.toJson v)
  if let some v := params.grd_max then
    fields := fields.push ("grd_max", Lean.toJson v)

  -- Complex places
  if let some v := params.r2_min then
    fields := fields.push ("r2_min", Lean.toJson v)
  if let some v := params.r2_max then
    fields := fields.push ("r2_max", Lean.toJson v)

  -- Class numbers
  if let some v := params.class_number then
    fields := fields.push ("class_number", Lean.toJson v)
  if let some v := params.narrow_class_number then
    fields := fields.push ("narrow_class_number", Lean.toJson v)
  if let some v := params.class_group then
    fields := fields.push ("class_group", Lean.toJson v)
  if let some v := params.narrow_class_group then
    fields := fields.push ("narrow_class_group", Lean.toJson v)

  -- Galois properties
  if let some v := params.is_galois then
    fields := fields.push ("is_galois", Lean.toJson v)
  if let some v := params.galois_label then
    fields := fields.push ("galois_label", Lean.toJson v)
  if let some v := params.gal_is_abelian then
    fields := fields.push ("gal_is_abelian", Lean.toJson v)
  if let some v := params.gal_is_cyclic then
    fields := fields.push ("gal_is_cyclic", Lean.toJson v)
  if let some v := params.gal_is_solvable then
    fields := fields.push ("gal_is_solvable", Lean.toJson v)

  -- Ramification
  if let some v := params.num_ram_min then
    fields := fields.push ("num_ram_min", Lean.toJson v)
  if let some v := params.num_ram_max then
    fields := fields.push ("num_ram_max", Lean.toJson v)
  if let some v := params.ramps then
    fields := fields.push ("ramps", Lean.toJson v)
  if let some v := params.unramified_primes then
    fields := fields.push ("unramified_primes", Lean.toJson v)
  if let some v := params.inessentialp then
    fields := fields.push ("inessentialp", Lean.toJson v)

  -- Other properties
  if let some v := params.cm then
    fields := fields.push ("cm", Lean.toJson v)
  if let some v := params.monogenic then
    fields := fields.push ("monogenic", Lean.toJson v)
  if let some v := params.is_minimal_sibling then
    fields := fields.push ("is_minimal_sibling", Lean.toJson v)

  -- Regulator
  if let some v := params.regulator_min then
    fields := fields.push ("regulator_min", Lean.toJson v)
  if let some v := params.regulator_max then
    fields := fields.push ("regulator_max", Lean.toJson v)

  -- Limit
  fields := fields.push ("limit", Lean.toJson params.limit)

  return Lean.Json.mkObj fields.toList

def doSearchLMFDB (params : SearchParams) : IO (Except String (Array NumberFieldResult)) := do
  try
    let python_cmd := "/home/chris/miniforge3/envs/sage/bin/python"
    let python_query_path := "LeanBridge/ForMathlib/tactics/lmfdb_query_range.py"

    let jsonObj := buildJsonQuery params
    let jsonStr := toString jsonObj

    let output ← IO.Process.output {
      cmd := python_cmd,
      args := #[python_query_path, jsonStr],
      stdin := .null,
      stdout := .piped,
      stderr := .piped
    }

    if output.exitCode != 0 then
      return .error s!"Query failed: {output.stderr}"

    let lines := (output.stdout.trim.splitOn "\n").filter (fun s => !s.isEmpty)
    let mut results : Array NumberFieldResult := #[]

    for line in lines do
      if line.startsWith "LMFDB_RECORDS_FOUND:" || line == "No fields found" then
        continue

      let parts := line.splitOn " "
      if parts.length == 7 then
        let label := parts[0]!
        let class_number := parts[1]!.toNat!
        let is_galois := parts[2]! == "True"
        let coeffs := parts[3]!
        let disc_abs := parts[4]!.toNat!
        let disc_sign := parts[5]!.toInt!
        let cm := parts[6]! == "True"

        results := results.push {
          label := label,
          class_number := class_number,
          is_galois := is_galois,
          coeffs := coeffs,
          disc_abs := disc_abs,
          disc_sign := disc_sign,
          cm := cm
        }

    return .ok results
  catch e =>
    return .error s!"{e}"

def doGenerateLeanFiles (fields : Array NumberFieldResult) (generateUnits : Bool := false) : IO (Except String String) := do
  try
    let sage_conda_env ← getSageCondaEnv
    let sage_cmd ← findCondaSage sage_conda_env

    let sage_proof_path := "LeanBridge/ForMathlib/Irreduciblepolys/IrreducibilityLeanProofWriter.sage"
    let proof_output_dir := "LeanBridge/ForMathlib/tactics"

    for field in fields do
      let validLabel := field.label.replace "." "_"
      let coeffsStr := field.coeffs

      let coeffsList := coeffsStr.splitOn ","
      let mut polyTerms : Array String := #[]
      let numCoeffs := coeffsList.length
      let coeffsListRev := coeffsList.reverse

      for i in [0:numCoeffs] do
        let coeffStr := coeffsListRev[i]!
        let exponent := numCoeffs - 1 - i
        if coeffStr != "0" then
          let term :=
            if exponent == 0 then s!"({coeffStr})"
            else if exponent == 1 then s!"({coeffStr}) * Polynomial.X"
            else s!"({coeffStr}) * Polynomial.X ^ {exponent}"
          polyTerms := polyTerms.push term

      let polyStr := " + ".intercalate polyTerms.toList

      let unitsFlag := if generateUnits then "true" else "false"
      let sageCommandStr := s!"load('{sage_proof_path}'); main_sage('{coeffsStr}', '{validLabel}', '{unitsFlag}')"

      let outputProof ← IO.Process.output {
        cmd := sage_cmd,
        args := #["-c", sageCommandStr],
        stdin := .null,
        stdout := .piped,
        stderr := .piped
      }

      -- DEBUG OUTPUT
      IO.println s!"[DEBUG] Sage exit code for {validLabel}: {outputProof.exitCode}"
      if outputProof.stderr.trim != "" then
        IO.println s!"[DEBUG] Sage stderr: {outputProof.stderr}"
      if outputProof.stdout.trim != "" then
        IO.println s!"[DEBUG] Sage stdout length: {outputProof.stdout.length}"

           -- Separate proof content from unit content
      let (proofContent, unitContent) :=
        if outputProof.exitCode != 0 then
          (s!"-- Proof generation failed for {validLabel}\n-- Exit code: {outputProof.exitCode}\n-- Error: {outputProof.stderr}\nsorry", "")
        else if generateUnits then
          -- Split the output: look for unit-related content
          let lines := outputProof.stdout.splitOn "\n"
          let splitIdx := lines.findIdx? (fun line => line.trim.startsWith "lemma K_int_")
          match splitIdx with
          | some idx =>
              let proofLines := (lines.take idx).filter (fun line => !line.trim.startsWith "import")
              let unitLines := lines.drop idx
              ("\n".intercalate proofLines, "\n".intercalate unitLines)
          | none =>
              let filteredLines := lines.filter (fun line => !line.trim.startsWith "import")
              ("\n".intercalate filteredLines, "")
        else
          let lines := outputProof.stdout.splitOn "\n"
          let filteredLines := lines.filter (fun line => !line.trim.startsWith "import")
          ("\n".intercalate filteredLines, "")

      let signedDiscr :=
        if field.disc_sign == -1 then s!"-{field.disc_abs}"
        else s!"{field.disc_abs}"

      let isGaloisAxiom :=
        if field.is_galois then s!"IsGalois ℚ K_{validLabel}"
        else s!"¬ IsGalois ℚ K_{validLabel}"

      let cmAxiom :=
        if field.cm then
          s!"\naxiom LMFDB_NF_{validLabel}_totallyComplex : IsTotallyComplex K_{validLabel}\n\ninstance LMFDB_NF_{validLabel}_totallyComplexInstance : IsTotallyComplex K_{validLabel} := LMFDB_NF_{validLabel}_totallyComplex\n\naxiom LMFDB_NF_{validLabel}_isCM : NumberField.IsCMField K_{validLabel}"
        else ""

      let kGenAbbrev :=
        if generateUnits then s!"\nabbrev K_gen_{validLabel} : K_{validLabel} := AdjoinRoot.root min_poly_{validLabel}\n"
        else ""

      let fileContent := s!"import Mathlib
import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest

namespace LMFDB_{validLabel}

noncomputable section

open NumberField Polynomial

abbrev min_poly_{validLabel} : Polynomial ℚ := {polyStr}

abbrev K_{validLabel} := AdjoinRoot min_poly_{validLabel}

{proofContent}
{kGenAbbrev}
lemma irreducible_poly : Irreducible min_poly_{validLabel} := by
  have := irreducible_T
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast] at this
  · convert this
    simp
    ring
  · refine Polynomial.Monic.isPrimitive ?_
    refine Polynomial.Monic.def.mpr ?_
    rw [T_ofList', ofList_leadingCoeff]
    · simp
    · apply List.cons_ne_nil _ _
    · rfl

instance : Fact (Irreducible min_poly_{validLabel}) := ⟨irreducible_poly⟩

{unitContent}

axiom LMFDB_NF_{validLabel}_discr : NumberField.discr K_{validLabel} = {signedDiscr}

axiom LMFDB_NF_{validLabel}_isGalois : {isGaloisAxiom}

axiom LMFDB_NF_{validLabel}_classNumber : NumberField.classNumber K_{validLabel} = {field.class_number}
{cmAxiom}

end
"



      let outputFile := s!"{proof_output_dir}/LMFDB_{validLabel}.lean"
      IO.FS.writeFile outputFile fileContent

    return .ok s!"Generated {fields.size} number field files in {proof_output_dir}"
  catch e =>
    return .error s!"{e}"

end LMFDBWidget

-- RPC methods OUTSIDE the namespace
open LMFDBWidget in
@[server_rpc_method]
def searchLMFDB (params : SearchParams) : RequestM (RequestTask (Array NumberFieldResult)) :=
  RequestM.asTask do
    match (← doSearchLMFDB params) with
    | .ok results => return results
    | .error e => throw { code := .internalError, message := e }

open LMFDBWidget in
@[server_rpc_method]
def generateLeanFiles (params : GenerateParams) : RequestM (RequestTask String) :=
  RequestM.asTask do
    match (← doGenerateLeanFiles params.fields params.generateUnits) with
    | .ok message => return message
    | .error e => throw { code := .internalError, message := e }

-- Widget module
@[widget_module]
def LMFDBSearchWidget : Component Unit where
  javascript := include_str ".."/".."/".."/"widget"/"lmfdb.js"

-- Command
open Lean Elab Command Widget in
elab "#lmfdb_search" : command => do
  let stx ← getRef
  let initialState : Lean.Json := Lean.Json.mkObj [
    ("searchParams", Lean.toJson ({} : LMFDBWidget.SearchParams)),
    ("results", Lean.toJson (#[] : Array LMFDBWidget.NumberFieldResult)),
    ("selected", Lean.toJson (#[] : Array Bool))
  ]

  liftCoreM <| savePanelWidgetInfo LMFDBSearchWidget.javascriptHash (pure initialState) stx

#lmfdb_search
