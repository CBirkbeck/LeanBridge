import VersoManual
import VersoBlueprint.PreviewManifest
import LeanBridgeBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanBridgeBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
