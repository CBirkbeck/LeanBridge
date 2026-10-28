import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanBridgeBlueprint.Chapters.Background
import LeanBridgeBlueprint.Chapters.NumberFields
import LeanBridgeBlueprint.Chapters.EllipticCurves
import LeanBridgeBlueprint.Chapters.ModularForms
import LeanBridgeBlueprint.Chapters.FurtherBackground
import LeanBridgeBlueprint.Chapters.Groups
import LeanBridgeBlueprint.Chapters.GaloisGroups
import LeanBridgeBlueprint.Chapters.LocalFields
import LeanBridgeBlueprint.Chapters.Characters
import LeanBridgeBlueprint.Chapters.ArtinRepresentations
import LeanBridgeBlueprint.Chapters.GaloisRepresentations
import LeanBridgeBlueprint.Chapters.LFunctions
import LeanBridgeBlueprint.Chapters.Varieties
import LeanBridgeBlueprint.Chapters.AbelianVarieties
import LeanBridgeBlueprint.Chapters.Genus2Curves
import LeanBridgeBlueprint.Chapters.HigherGenusCurves
import LeanBridgeBlueprint.Chapters.BelyiMaps
import LeanBridgeBlueprint.Chapters.ModularCurves
import LeanBridgeBlueprint.Chapters.ShimuraCurves
import LeanBridgeBlueprint.Chapters.HilbertModularSurfaces
import LeanBridgeBlueprint.Chapters.AutomorphicForms
import LeanBridgeBlueprint.Chapters.SatoTateGroups
import LeanBridgeBlueprint.Chapters.HypergeometricMotives
import LeanBridgeBlueprint.Chapters.Lattices

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "LeanBridge Blueprint" =>

The plan is to formalize definitions from the L-functions and modular forms database
(LMFDB) in mathlib, as well as creating tactics to import relevant data from the LMFDB.
This blueprint catalogues every LMFDB knowl that defines something. Its core is number
fields, elliptic curves, and modular forms, with a background chapter for the notions they
depend on; the other knowls follow in chapters by area. It is migrated from the project's
original LaTeX (leanblueprint) document; each definition links back to its LMFDB knowl.

{include 0 LeanBridgeBlueprint.Chapters.Background}
{include 0 LeanBridgeBlueprint.Chapters.NumberFields}
{include 0 LeanBridgeBlueprint.Chapters.EllipticCurves}
{include 0 LeanBridgeBlueprint.Chapters.ModularForms}
{include 0 LeanBridgeBlueprint.Chapters.FurtherBackground}
{include 0 LeanBridgeBlueprint.Chapters.Groups}
{include 0 LeanBridgeBlueprint.Chapters.GaloisGroups}
{include 0 LeanBridgeBlueprint.Chapters.LocalFields}
{include 0 LeanBridgeBlueprint.Chapters.Characters}
{include 0 LeanBridgeBlueprint.Chapters.ArtinRepresentations}
{include 0 LeanBridgeBlueprint.Chapters.GaloisRepresentations}
{include 0 LeanBridgeBlueprint.Chapters.LFunctions}
{include 0 LeanBridgeBlueprint.Chapters.Varieties}
{include 0 LeanBridgeBlueprint.Chapters.AbelianVarieties}
{include 0 LeanBridgeBlueprint.Chapters.Genus2Curves}
{include 0 LeanBridgeBlueprint.Chapters.HigherGenusCurves}
{include 0 LeanBridgeBlueprint.Chapters.BelyiMaps}
{include 0 LeanBridgeBlueprint.Chapters.ModularCurves}
{include 0 LeanBridgeBlueprint.Chapters.ShimuraCurves}
{include 0 LeanBridgeBlueprint.Chapters.HilbertModularSurfaces}
{include 0 LeanBridgeBlueprint.Chapters.AutomorphicForms}
{include 0 LeanBridgeBlueprint.Chapters.SatoTateGroups}
{include 0 LeanBridgeBlueprint.Chapters.HypergeometricMotives}
{include 0 LeanBridgeBlueprint.Chapters.Lattices}

{blueprint_graph}
{blueprint_summary}
