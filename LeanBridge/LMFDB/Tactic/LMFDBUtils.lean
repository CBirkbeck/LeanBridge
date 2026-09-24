import Lean

open System

namespace LMFDBUtils

/-- Get conda base path, or none if conda is not installed. -/
def getCondaBase : IO (Option String) := do
  let result ← IO.Process.output {
    cmd := "conda",
    args := #["info", "--base"],
    stdin := .null,
    stdout := .piped,
    stderr := .piped
  }
  if result.exitCode == 0 then
    return some result.stdout.trim
  return none

/-- Get Sage conda environment name from LMFDB_SAGE_CONDA_ENV, defaulting to "sage". -/
def getSageCondaEnv : IO String := do
  match ← IO.getEnv "LMFDB_SAGE_CONDA_ENV" with
  | some env => return env
  | none => return "sage"

/-- Try to find an executable on system PATH using 'which'. -/
def findOnPath (name : String) : IO (Option String) := do
  let result ← IO.Process.output {
    cmd := "which",
    args := #[name],
    stdin := .null,
    stdout := .piped,
    stderr := .piped
  }
  if result.exitCode == 0 then
    return some result.stdout.trim
  return none

/-- Find Python for LMFDB queries. Checks in order:
    1. LMFDB_PYTHON environment variable (direct path)
    2. Python in the conda sage environment
    3. 'python3' on system PATH -/
def findPython : IO String := do
  -- 1. Direct env var override
  if let some path := (← IO.getEnv "LMFDB_PYTHON") then
    if ← FilePath.pathExists path then
      return path
    throw <| IO.userError s!"LMFDB_PYTHON is set to '{path}' but file does not exist"

  -- 2. Conda environment
  if let some condaBase := (← getCondaBase) then
    let envName ← getSageCondaEnv
    let pythonPath := s!"{condaBase}/envs/{envName}/bin/python"
    if ← FilePath.pathExists pythonPath then
      return pythonPath

  -- 3. System PATH
  if let some path := (← findOnPath "python3") then
    return path

  throw <| IO.userError
    "Could not find Python for LMFDB queries. Either:\n\
     • Set LMFDB_PYTHON env var to your Python path, or\n\
     • Install sage in a conda environment (default name: 'sage'), or\n\
     • Ensure python3 is on your PATH with lmfdb-lite installed"

/-- Find Sage. Checks in order:
    1. LMFDB_SAGE environment variable (direct path)
    2. Sage in the conda sage environment
    3. 'sage' on system PATH -/
def findSage : IO String := do
  -- 1. Direct env var override
  if let some path := (← IO.getEnv "LMFDB_SAGE") then
    if ← FilePath.pathExists path then
      return path
    throw <| IO.userError s!"LMFDB_SAGE is set to '{path}' but file does not exist"

  -- 2. Conda environment
  if let some condaBase := (← getCondaBase) then
    let envName ← getSageCondaEnv
    let sagePath := s!"{condaBase}/envs/{envName}/bin/sage"
    if ← FilePath.pathExists sagePath then
      return sagePath

  -- 3. System PATH
  if let some path := (← findOnPath "sage") then
    return path

  throw <| IO.userError
    "Could not find Sage. Either:\n\
     • Set LMFDB_SAGE env var to your Sage path, or\n\
     • Install sage in a conda environment (default name: 'sage'), or\n\
     • Ensure sage is on your PATH"

/-- Get the parent directory of an executable path. -/
def parentDir (path : String) : String :=
  let fp := FilePath.mk path
  match fp.parent with
  | some p => p.toString
  | none => "."

/-- Build a PATH environment string that includes the bin directory of a given executable.
    This ensures that related tools (like Singular for Sage) are discoverable. -/
def buildEnvPath (execPath : String) : IO String := do
  let binDir := parentDir execPath
  let currentPath := (← IO.getEnv "PATH").getD ""
  if currentPath.splitOn ":" |>.contains binDir then
    return currentPath
  return s!"{binDir}:{currentPath}"

/-- Run a Python script with the correct environment for Sage/LMFDB dependencies.
    Automatically sets PATH to include the Python executable's bin directory. -/
def runPythonScript (pythonCmd : String) (scriptPath : String) (args : Array String)
    : IO IO.Process.Output := do
  let envPath ← buildEnvPath pythonCmd
  IO.Process.output {
    cmd := pythonCmd,
    args := #[scriptPath] ++ args,
    stdin := .null,
    stdout := .piped,
    stderr := .piped,
    env := #[("PATH", some envPath)]
  }

/-- Run a Sage command with the correct environment. -/
def runSageCommand (sageCmd : String) (args : Array String)
    : IO IO.Process.Output := do
  let envPath ← buildEnvPath sageCmd
  IO.Process.output {
    cmd := sageCmd,
    args := args,
    stdin := .null,
    stdout := .piped,
    stderr := .piped,
    env := #[("PATH", some envPath)]
  }

end LMFDBUtils
