
import Lean
import Lean.Elab.Command
import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Mathlib
import LeanBridge.ForMathlib.tactics.LMFDB_Proof_2_2_13_1

open Lean Elab Command IO System

/-- Find an executable by trying multiple methods:
    1. Check if it's an absolute path
    2. Try to find it in PATH using 'which'
    3. Throw an error if not found -/
def findExecutable (name : String) (envVarName? : Option String := none) : IO String := do
  -- First try environment variable if provided
  if let some envVar := envVarName? then
    if let some path := (← IO.getEnv envVar) then
      if ← FilePath.pathExists path then
        return path

  -- If name is already an absolute path, check if it exists
  if name.startsWith "/" then
    if ← FilePath.pathExists name then
      return name
    else
      throw <| IO.userError s!"Specified path does not exist: {name}"

  -- Try to find in PATH using 'which'
  let output ← IO.Process.output {
    cmd := "which",
    args := #[name],
    stdin := .null,
    stdout := .piped,
    stderr := .piped
  }

  if output.exitCode == 0 then
    return output.stdout.trim
  else
    let envMsg := match envVarName? with
      | some envVar => s!" or set the {envVar} environment variable"
      | none => ""
    throw <| IO.userError s!"Could not find '{name}' in PATH{envMsg}. Please ensure it is installed."

/-- Get Sage conda environment name from environment variable or use default -/
def getSageCondaEnv : IO String := do
  if let some env := (← IO.getEnv "LMFDB_SAGE_CONDA_ENV") then
    return env
  else
    return "sage"  -- default conda environment name

/-- Find Python in the sage conda environment -/
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
    if ← FilePath.pathExists pythonPath then
      return pythonPath

  throw <| IO.userError s!"Could not find Python in conda environment '{envName}'"

/-- Find the full path to Sage in a conda environment -/
def findCondaSage (envName : String) : IO String := do
  -- Get conda base path
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

  -- Check if it exists
  if ← FilePath.pathExists sagePath then
    return sagePath
  else
    throw <| IO.userError s!"Sage not found in conda environment '{envName}' at {sagePath}. Please install sage in the environment with: conda install -c conda-forge sage"

elab "#LMFDB_search" degree:num r2:num D_abs:num : command => do
  let degree_val := degree.getNat
  let r2_val := r2.getNat
  let D_abs_val := D_abs.getNat

  -- Get the conda environment
  let sage_conda_env ← getSageCondaEnv

  -- Find the full paths to Python and Sage in the conda environment
  let python_cmd ← findCondaPython sage_conda_env
  let sage_cmd ← findCondaSage sage_conda_env

  -- Use relative paths from project root
  let python_query_path := "LeanBridge/ForMathlib/tactics/lmfdb_query.py"
  let sage_proof_path := "LeanBridge/ForMathlib/Irreduciblepolys/IrreducibilityLeanProofWriter.sage"
  let proof_output_dir := "LeanBridge/ForMathlib/tactics"
  let module_prefix := "LeanBridge.Mathlib.Irreduciblepolys"

  logInfo m!"Using Python: {python_cmd}"
  logInfo m!"Using Sage: {sage_cmd}"
  logInfo m!"Querying LMFDB with: degree={degree_val}, r2={r2_val}, disc_abs={D_abs_val}"

  -- 1. Run the Query Script (Python) - using full path
  let output_query ← IO.Process.output {
    cmd := python_cmd,
    args := #[python_query_path, toString degree_val, toString r2_val, toString D_abs_val],
    stdin := .null,
    stdout := .piped,
    stderr := .piped
  }

  if output_query.exitCode != 0 then
    logError s!"LMFDB Query script failed with exit code {output_query.exitCode}:\n{output_query.stderr}"
    return

  -- Logic to handle debug/success lines
  let response_lines := (output_query.stdout.trim.splitOn "\n").filter (fun s => !s.isEmpty)

  let mut data_lines := response_lines

  if let some first_line := response_lines.head? then
    if first_line.startsWith "LMFDB_RECORDS_FOUND:" then
      -- Remove the debug line and proceed with the rest of the lines
      data_lines := response_lines.tail!
    else if first_line == "No fields found: SQL returned 0 rows" then
      logInfo m!"No number fields found with the specified properties."
      return

  if data_lines.isEmpty then
    logInfo m!"No number fields found with the specified properties."
    return

  -- 2. Process Data Lines and Generate Axioms
  let mut suggestions_list : List (Meta.Tactic.TryThis.Suggestion) := []

  for line in data_lines do
    let parts := line.splitOn " "
    -- EXPECTING 7 parts: label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm
    if parts.length == 7 then
      let label_val := parts[0]!
      let class_number_val_str := parts[1]!
      let is_galois_val_str := parts[2]!
      let coeffs_str := parts[3]!
      let disc_abs_str := parts[4]!
      let disc_sign_str := parts[5]!
      let cm_str := parts[6]!

      let valid_label := label_val.replace "." "_"

      -- Irreducibility Proof Logic
      let mut irreducibility_import := ""
      let mut irreducibility_block := ""

      -- We must reverse the coefficients to build the polynomial string from highest power (descending order)
      let coeffs_list_str := coeffs_str.splitOn ","
      let mut poly_terms : Array String := #[]

      let num_coeffs := coeffs_list_str.length
      let coeffs_list_rev := coeffs_list_str.reverse

      for i in [0:num_coeffs] do
        let coeff_str := coeffs_list_rev[i]!
        let exponent := num_coeffs - 1 - i
        if coeff_str != "0" then
          let term :=
            if exponent == 0 then
              s!"({coeff_str})"
            else if exponent == 1 then
              s!"({coeff_str}) * Polynomial.X"
            else
              s!"({coeff_str}) * Polynomial.X ^ {exponent}"
          poly_terms := poly_terms.push term

      let poly_str := " + ".intercalate poly_terms.toList

      -- Run Sage using full path (no conda activation needed)
      let sage_command_str := s!"load('{sage_proof_path}'); main_sage('{coeffs_str}', '{valid_label}')"

      let output_proof ← IO.Process.output {
        cmd := sage_cmd,  -- Use full path to sage executable
        args := #["-c", sage_command_str],
        stdin := .null,
        stdout := .piped,
        stderr := .piped
      }

      if output_proof.exitCode != 0 then
        logWarning s!"Irreducibility proof generation failed for {valid_label} (Exit Code: {output_proof.exitCode}). Falling back to 'sorry'.\nSage Error: {output_proof.stderr}"
        irreducibility_block := s!"instance : Fact (Irreducible min_poly_{valid_label}) := by sorry"
      else
        let proof_module_name := s!"LMFDB_Proof_{valid_label}"
        let proof_file_path := proof_output_dir ++ "/" ++ s!"{proof_module_name}.lean"

        -- Write the proof to the correct file path using Lean's IO
        IO.FS.writeFile proof_file_path output_proof.stdout

        irreducibility_import := s!"import {module_prefix}.{proof_module_name}"
        irreducibility_block := s!"theorem irreducible_poly : Irreducible min_poly_{valid_label} := irreducible_T"

      -- Axiom Construction
      let signed_discr :=
        if disc_sign_str == "-1" then
          s!"- {disc_abs_str}"
        else
          disc_abs_str

      let is_galois_axiom_type :=
        if is_galois_val_str == "True" then s!"IsGalois ℚ K_{valid_label}"
        else s!"¬ IsGalois ℚ K_{valid_label}"

      let cm_axiom_type :=
        if cm_str == "True" then
          s!"\naxiom LMFDB_NF_{valid_label}_totallyComplex : IsTotallyComplex K_{valid_label} \n\ninstance LMFDB_NF_{valid_label}_totallyComplexInstance : IsTotallyComplex K_{valid_label} := LMFDB_NF_{valid_label}_totallyComplex\n\naxiom LMFDB_NF_{valid_label}_isCM : NumberField.IsCMField K_{valid_label}"
        else
          ""

      let class_number_axiom_type := s!"NumberField.classNumber K_{valid_label} = {class_number_val_str}"

      let declarations :=
s!"noncomputable section

open NumberField

abbrev min_poly_{valid_label} : Polynomial ℚ := {poly_str}

abbrev K_{valid_label} := AdjoinRoot min_poly_{valid_label}

lemma irreducible_poly :  Irreducible min_poly_{valid_label} := by
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

instance: Fact (Irreducible min_poly_{valid_label}) := ⟨irreducible_poly⟩

axiom LMFDB_NF_{valid_label}_discr : NumberField.discr K_{valid_label} = {signed_discr}

axiom LMFDB_NF_{valid_label}_isGalois : {is_galois_axiom_type}

axiom LMFDB_NF_{valid_label}_classNumber : {class_number_axiom_type}
{cm_axiom_type}

end"

      suggestions_list := suggestions_list.concat {
        suggestion := declarations,
        postInfo? := some s!"LMFDB entry for {valid_label}"
      }

  logInfo m!"Found {suggestions_list.length} number fields. Adding suggestions to infoview."
  liftTermElabM <|
    Meta.Tactic.TryThis.addSuggestions (←getRef) suggestions_list.toArray


noncomputable section

open NumberField

abbrev min_poly_2_2_13_1 : Polynomial ℚ := (1) * Polynomial.X ^ 2 + (-1) * Polynomial.X + (-3)

abbrev K_2_2_13_1 := AdjoinRoot min_poly_2_2_13_1

lemma irreducible_poly :  Irreducible min_poly_2_2_13_1 := by
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

instance: Fact (Irreducible min_poly_2_2_13_1) := ⟨irreducible_poly⟩

axiom LMFDB_NF_2_2_13_1_discr : NumberField.discr K_2_2_13_1 = 13

axiom LMFDB_NF_2_2_13_1_isGalois : IsGalois ℚ K_2_2_13_1

axiom LMFDB_NF_2_2_13_1_classNumber : NumberField.classNumber K_2_2_13_1 = 1


end
