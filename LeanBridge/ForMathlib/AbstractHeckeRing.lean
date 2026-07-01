/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.ForMathlib.AbstractHeckeRing.Ring

/-!
# Abstract Hecke ring: the ring structure

The abstract Hecke ring of a Hecke pair `(H, Δ)`, following Shimura, *Introduction to the Arithmetic
Theory of Automorphic Functions*, Ch. 3, together with the proof that it is a `Ring`. For an
arithmetic pair `H ≤ Δ ≤ commensurator(H)` this assembles:

* `HeckeRing.HeckePair`, the double-coset quotient `HeckeRing.HeckeCoset`, and the Hecke ring type
  `HeckeRing.𝕋` (`Basic`);
* the convolution product via Shimura's multiplicities (`Multiplication`), the module action used in
  the associativity argument (`Module`), associativity of the product (`Associativity`), and the
  resulting `Ring (𝕋 P ℤ)` instance (`Ring`).

Commutativity (from an anti-involution), the degree map, and the remaining API are deliberately left
to follow-up PRs.

Ported from the AINTLIB project
(`projects/LeanModularForms/LeanModularForms/HeckeRIngs/AbstractHeckeRing`).
-/
