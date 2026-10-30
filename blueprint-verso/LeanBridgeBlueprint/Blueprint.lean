import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanBridgeBlueprint.Chapters.Background
import LeanBridgeBlueprint.Chapters.LFunctions
import LeanBridgeBlueprint.Chapters.ModularForms
import LeanBridgeBlueprint.Chapters.Varieties
import LeanBridgeBlueprint.Chapters.Fields
import LeanBridgeBlueprint.Chapters.Representations
import LeanBridgeBlueprint.Chapters.HypergeometricMotives
import LeanBridgeBlueprint.Chapters.Groups

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "LeanBridge Blueprint" =>

The plan is to formalize definitions from the L-functions and modular forms database
(LMFDB) in mathlib, as well as creating tactics to import relevant data from the LMFDB.
This blueprint catalogues every LMFDB knowl with mathematical content. Its chapters and
sections follow the LMFDB's categories of knowls, the part of a knowl's id before the first
or second dot, apart from a few knowls whose category is wrong. It is migrated from the
project's original LaTeX (leanblueprint) document; each definition links back to its LMFDB
knowl.

{include 0 LeanBridgeBlueprint.Chapters.Background}
{include 0 LeanBridgeBlueprint.Chapters.LFunctions}
{include 0 LeanBridgeBlueprint.Chapters.ModularForms}
{include 0 LeanBridgeBlueprint.Chapters.Varieties}
{include 0 LeanBridgeBlueprint.Chapters.Fields}
{include 0 LeanBridgeBlueprint.Chapters.Representations}
{include 0 LeanBridgeBlueprint.Chapters.HypergeometricMotives}
{include 0 LeanBridgeBlueprint.Chapters.Groups}

{blueprint_graph}
{blueprint_summary}
