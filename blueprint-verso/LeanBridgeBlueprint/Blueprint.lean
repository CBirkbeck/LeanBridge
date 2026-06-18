import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanBridgeBlueprint.Chapters.Background
import LeanBridgeBlueprint.Chapters.NumberFields
import LeanBridgeBlueprint.Chapters.EllipticCurves
import LeanBridgeBlueprint.Chapters.ModularForms

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "LeanBridge Blueprint" =>

The plan is to formalize definitions from the L-functions and modular forms database
(LMFDB) in mathlib, as well as creating tactics to import relevant data from the LMFDB.
This blueprint catalogues the relevant LMFDB definitions, organised into number fields,
elliptic curves, and modular forms, with a background chapter for supporting notions. It
is migrated from the project's original LaTeX (leanblueprint) document; each definition
links back to its LMFDB knowl.

{include 0 LeanBridgeBlueprint.Chapters.Background}
{include 0 LeanBridgeBlueprint.Chapters.NumberFields}
{include 0 LeanBridgeBlueprint.Chapters.EllipticCurves}
{include 0 LeanBridgeBlueprint.Chapters.ModularForms}

{blueprint_graph}
{blueprint_summary}
