/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.ForMathlib.AbstractHeckeRing.Basic
import LeanBridge.ForMathlib.AbstractHeckeRing.Multiplication
import LeanBridge.ForMathlib.AbstractHeckeRing.Associativity
import LeanBridge.ForMathlib.AbstractHeckeRing.Ring
import LeanBridge.ForMathlib.AbstractHeckeRing.Module
import LeanBridge.ForMathlib.AbstractHeckeRing.Commutativity
import LeanBridge.ForMathlib.AbstractHeckeRing.Degree
import LeanBridge.ForMathlib.AbstractHeckeRing.StabConjugation

/-!
# Abstract Hecke ring

The full construction of the abstract Hecke ring, following Shimura, *Introduction to the
Arithmetic Theory of Automorphic Functions*, Ch. 3. For an arithmetic pair `(H, Δ)`
(`H ≤ Δ ≤ commensurator(H)`), this assembles:

* `HeckeRing.HeckePair`, the double-coset quotient `HeckeRing.HeckeCoset`, and the Hecke ring
  type `HeckeRing.𝕋` (`Basic`);
* the convolution product (`Multiplication`, `Associativity`) and the resulting `Ring`
  structure (`Ring`);
* the Hecke module over the left cosets (`Module`);
* commutativity from an anti-involution (`Commutativity`), the degree map (`Degree`), and
  stabilizer/conjugation lemmas (`StabConjugation`).

Ported from the AINTLIB project
(`projects/LeanModularForms/LeanModularForms/HeckeRIngs/AbstractHeckeRing`).
-/
