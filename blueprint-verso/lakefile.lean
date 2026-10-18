import Lake
open Lake DSL

-- VersoBlueprint's `v4.35.0` line targets Lean v4.35.0-rc4, but builds on v4.35.0 with Verso's
-- v4.35.0 releases, which are pinned here so that they take precedence over its rc4 pins.
-- `lean-toolchain` must match LeanBridge's, since LeanBridge is part of this workspace.
require verso from git "https://github.com/leanprover/verso"@"v4.35.0"
require «verso-slides» from git "https://github.com/leanprover/verso-slides"@"v4.35.0"
require subverso from git "https://github.com/leanprover/subverso"@"verso-v4.35.0"
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.35.0"

-- The declarations that the chapters link with `(lean := ...)`. Kept last so that its (and through
-- it, Mathlib's) pins of shared dependencies take precedence.
require LeanBridge from ".."

package LeanBridgeBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib LeanBridgeBlueprint where

lean_exe «blueprint-gen» where
  root := `LeanBridgeBlueprintMain
