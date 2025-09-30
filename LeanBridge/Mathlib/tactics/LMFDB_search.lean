import Lean
import Lean.Elab.Command
import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Mathlib

open Lean Elab Command IO

elab "#LMFDB_search" degree:num r2:num D_abs:num : command => do
  let degree_val := degree.getNat
  let r2_val := r2.getNat
  let D_abs_val := D_abs.getNat

  let python_cmd := "python3" -- You might need to install psycopg2 first. Look at lmfdb-lite for help
  let python_script_path := "./LeanBridge/Mathlib/tactics/lmfdb_query.py"

  logInfo m!"Querying LMFDB with: degree={degree_val}, r2={r2_val}, disc_abs={D_abs_val}"

  let output ← IO.Process.output {
    cmd := python_cmd,
    args := #[python_script_path, toString degree_val, toString r2_val, toString D_abs_val],
    stdin := .null,
    stdout := .piped,
    stderr := .piped
  }

  if output.exitCode != 0 then
    logError s!"Python script failed with exit code {output.exitCode}:\n{output.stderr}"
    return

  let response_lines := (output.stdout.trim.splitOn "\n").filter (fun s => !s.isEmpty)

  if response_lines.isEmpty || response_lines.head?.map String.trim == some "No fields found" then
    logInfo m!"No number fields found with the specified properties."
    return

  let mut suggestions_list : List (Meta.Tactic.TryThis.Suggestion) := []
  for line in response_lines do
    let parts := line.splitOn " "

    -- EXPECTING 7 PARTS: label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm
    if parts.length == 7 then
      let label_val := parts[0]!
      let class_number_val_str := parts[1]!
      let is_galois_val_str := parts[2]!
      let coeffs_str := parts[3]!
      let disc_abs_str := parts[4]!
      let disc_sign_str := parts[5]!
      let cm_str := parts[6]! -- Variable is 'cm_str' not 'cm' for consistency

      let valid_label := label_val.replace "." "_"

      let coeffs_list_str := coeffs_str.splitOn ","
      let mut poly_terms : Array String := #[]

      -- Polynomial Construction
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

      -- Calculate the signed discriminant
      let signed_discr :=
        if disc_sign_str == "-1" then
          s!"- {disc_abs_str}"
        else
          disc_abs_str

      -- Define the full axiom statements outside the final string interpolation
      let is_galois_axiom_type :=
        if is_galois_val_str == "True" then s!"IsGalois ℚ K_{valid_label}"
        else s!"¬ IsGalois ℚ K_{valid_label}"

   -- CORRECTED: Only generates axioms if cm_str is "True", otherwise it's an empty string.
      let cm_axiom_type :=
        if cm_str == "True" then
          s!"axiom LMFDB_NF_{valid_label}_totallyComplex : IsTotallyComplex K_{valid_label} \n\ninstance LMFDB_NF_{valid_label}_totallyComplexInstance : IsTotallyComplex K_{valid_label} := LMFDB_NF_{valid_label}_totallyComplex \n\naxiom LMFDB_NF_{valid_label}_isCM : IsCMField K_{valid_label}"
        else
          "" -- Insert nothing when the field is not CM

      let class_number_axiom_type := s!"classNumber K_{valid_label} = {class_number_val_str}"

      let declarations :=
s!"noncomputable section

open NumberField

def min_poly_{valid_label} : Polynomial ℚ := {poly_str}

abbrev K_{valid_label} := AdjoinRoot min_poly_{valid_label}

instance : Fact (Irreducible min_poly_{valid_label}) := by sorry

axiom LMFDB_NF_{valid_label}_discr : discr K_{valid_label} = {signed_discr}

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

def min_poly_2_0_23_1 : Polynomial ℚ := (1) * Polynomial.X ^ 2 + (-1) * Polynomial.X + (6)

abbrev K_2_0_23_1 := AdjoinRoot min_poly_2_0_23_1

instance : Fact (Irreducible min_poly_2_0_23_1) := by sorry

axiom LMFDB_NF_2_0_23_1_discr : discr K_2_0_23_1 = - 23

axiom LMFDB_NF_2_0_23_1_isGalois : IsGalois ℚ K_2_0_23_1

axiom LMFDB_NF_2_0_23_1_classNumber : classNumber K_2_0_23_1 = 3

axiom LMFDB_NF_2_0_23_1_totallyComplex : IsTotallyComplex K_2_0_23_1

instance LMFDB_NF_2_0_23_1_totallyComplexInstance : IsTotallyComplex K_2_0_23_1 := LMFDB_NF_2_0_23_1_totallyComplex

axiom LMFDB_NF_2_0_23_1_isCM : IsCMField K_2_0_23_1

end

noncomputable section

open NumberField

def min_poly_2_0_4_1 : Polynomial ℚ := (1) * Polynomial.X ^ 2 + (1)

abbrev K_2_0_4_1 := AdjoinRoot min_poly_2_0_4_1

instance : Fact (Irreducible min_poly_2_0_4_1) := by sorry

axiom LMFDB_NF_2_0_4_1_discr : discr K_2_0_4_1 = - 4

axiom LMFDB_NF_2_0_4_1_isGalois : IsGalois ℚ K_2_0_4_1

axiom LMFDB_NF_2_0_4_1_classNumber : classNumber K_2_0_4_1 = 1

axiom LMFDB_NF_2_0_4_1_totallyComplex : IsTotallyComplex K_2_0_4_1

instance LMFDB_NF_2_0_4_1_totallyComplexInstance : IsTotallyComplex K_2_0_4_1 := LMFDB_NF_2_0_4_1_totallyComplex

axiom LMFDB_NF_2_0_4_1_isCM : IsCMField K_2_0_4_1

end


#LMFDB_search 4 0 1008
--let python_path := "/home/chris/Github/LeanBridge/.venv/bin/python"
