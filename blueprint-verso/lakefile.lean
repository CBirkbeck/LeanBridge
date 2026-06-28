import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.31.0"

package LeanBridgeBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib LeanBridgeBlueprint where

lean_exe «blueprint-gen» where
  root := `LeanBridgeBlueprintMain
