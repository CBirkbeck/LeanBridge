import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Order.Lattice.Nat
import Mathlib.RepresentationTheory.Irreducible

/-!
# Minimal degrees of faithful linear representations

## Main definitions

* `Matrix.GeneralLinearGroup.representation`: the representation on `Rⁿ` of a homomorphism
  `G →* GL_n(R)`.
* `linearDegree` and `irreducibleDegree` (LMFDB `group.min_faithful_linear`).
-/

open Matrix

variable {R G : Type*} [CommRing R] [Group G]

namespace Matrix.GeneralLinearGroup

/-- The representation of `G` on `Rⁿ` given by a matrix representation `ρ : G →* GL_n(R)`. -/
def representation {n : ℕ} (ρ : G →* GL (Fin n) R) : Representation R G (Fin n → R) :=
  (Units.coeHom _).comp <| toLin.toMonoidHom.comp ρ

end Matrix.GeneralLinearGroup

variable (R G) in
/-- The **linear degree** `lin_R(G)` (LMFDB `group.min_faithful_linear`), the least `n` with a
faithful matrix representation `G ↪ GL_n(R)`. Such an `n` exists for finite `G` and `R ≠ 0`, by the
regular representation; otherwise this is `0` by convention. -/
noncomputable def linearDegree : ℕ :=
  sInf {n | ∃ ρ : G →* GL (Fin n) R, Function.Injective ρ}

open scoped Classical in
/-- The **irreducible degree** `irr_R(G)` (LMFDB `group.min_faithful_linear`), the least `n` with a
faithful irreducible matrix representation `G ↪ GL_n(R)` over a field `R`, and `-1` when there is
no faithful irreducible representation, following the LMFDB's convention. -/
noncomputable def irreducibleDegree (R G : Type*) [Field R] [Group G] : ℤ :=
  if h : ∃ n : ℕ, ∃ ρ : G →* GL (Fin n) R, Function.Injective ρ ∧
      (GeneralLinearGroup.representation ρ).IsIrreducible then
    Nat.find h
  else -1
