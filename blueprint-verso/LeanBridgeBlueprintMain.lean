import VersoManual
import VersoBlueprint.PreviewManifest
import LeanBridgeBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

-- Elaborating the whole document takes more than the default 200000 heartbeats since the
-- blueprint holds every mathematical LMFDB knowl (between 300000 and 400000 in October 2026).
set_option maxHeartbeats 1000000 in
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanBridgeBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
