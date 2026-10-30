import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Conductor
import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Frobenius
import LeanBridge.ForMathlib.RepresentationTheory.FaithfulDegree

/-!
# The label of a mod-`ℓ` Galois representation

The LMFDB label of a mod-`ℓ` Galois representation `ρ : Gal(ℚ̄/ℚ) → GL_d(𝔽_ℓ)` has the form
`l.d.N.n` (LMFDB `modlgal.label`), where `l = ℓ` is its characteristic, `d` its dimension, `N` its
conductor, and `n` an identifier that tells apart the representations with the same `ℓ`, `d` and
`N`.

We formalise the prefix `l.d.N`. The conductor of `ρ` is that of the representation of the Galois
group of its splitting field `L` on `𝔽_ℓ ^ d` through which `ρ` factors (LeanBridge's
`MonoidHom.galoisFactor`, `Matrix.GeneralLinearGroup.representation` and
`Representation.modEllConductor`, LMFDB `modlgal.conductor`). It is the real number
`∏_{p ≠ ℓ} p ^ f(ρ, p)`, as the integrality of the exponents `f(ρ, p)` is not proved, so the prefix
is a relation: `s` is the prefix of `ρ` when it is `l.d.N` for a natural number `N` whose cast is
the conductor, which then determines it (`MonoidHom.IsModEllLabelPrefix.eq`).

The identifier `n` is not formalised: for `d ≥ 2` it is a numbering of the database, and for
`d = 1` it is `a-b` for the Conrey label `a.b` of a Dirichlet character lifting `ρ`, a lift that
the knowl does not single out, in a labelling of Dirichlet characters that is not available in the
pinned versions of Mathlib, Tau Ceti and LeanBridge.

## Main definitions

* `MonoidHom.modEllConductor` (LMFDB `modlgal.label`, `modlgal.conductor`): the conductor of `ρ`.
* `MonoidHom.IsModEllLabelPrefix` (LMFDB `modlgal.label`): the prefix `l.d.N` of the label of `ρ`.

## Main results

* `MonoidHom.IsModEllLabelPrefix.eq`: a mod-`ℓ` Galois representation has at most one label
  prefix.
-/

open Matrix

namespace MonoidHom

variable {n ℓ : ℕ} [Fact ℓ.Prime] {ρ : Gal(AlgebraicClosure ℚ/ℚ) →* GL (Fin n) (ZMod ℓ)}
  (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure ℚ/ℚ))) {s t : String}

/-- The **conductor** (LMFDB `modlgal.label`, `modlgal.conductor`) of a mod-`ℓ` Galois
representation `ρ` of `ℚ`: the conductor `∏_{p ≠ ℓ} p ^ f(ρ, p)` (`Representation.modEllConductor`)
of the representation on `𝔽_ℓ ^ n` (`GeneralLinearGroup.representation`) of the homomorphism
`galoisFactor` from the Galois group of the splitting field `L` of `ρ` to `GL_n(𝔽_ℓ)` through which
`ρ` factors (`galoisFactor_restrictNormalHom`), as the knowl defines the conductor for a
representation of `Gal(L/ℚ)`. It is a positive integer prime to `ℓ`, which is not proved here,
where it is a real number. -/
noncomputable def modEllConductor : ℝ :=
  (GeneralLinearGroup.representation (galoisFactor hρ)).modEllConductor ℓ

variable (s) in
/-- `s` is the **label prefix** `l.d.N` (LMFDB `modlgal.label`) of a mod-`ℓ` Galois representation
`ρ : Gal(ℚ̄/ℚ) → GL_n(𝔽_ℓ)`: its characteristic `l = ℓ`, its dimension `d = n` (the dimension of
`𝔽_ℓ ^ n`, `Module.finrank_fin_fun`) and its conductor `N` (`modEllConductor`), in decimal and
separated by dots. The conductor is a positive integer, which is not proved here, where it is a
real number: `s` is the prefix when it is `l.d.N` for a natural number `N` whose cast is the
conductor. The prefix is then unique (`IsModEllLabelPrefix.eq`). The LMFDB label continues with an
identifier that is not formalised: a numbering of the database, or for `n = 1` the Conrey label of
a lift of `ρ` to a Dirichlet character. -/
def IsModEllLabelPrefix : Prop :=
  ∃ N : ℕ, (N : ℝ) = modEllConductor hρ ∧ s = toString ℓ ++ "." ++ toString n ++ "." ++ toString N

variable {hρ} in
/-- **A mod-`ℓ` Galois representation has at most one label prefix**, since a real number is the
cast of at most one natural number. -/
lemma IsModEllLabelPrefix.eq (hs : IsModEllLabelPrefix hρ s) (ht : IsModEllLabelPrefix hρ t) :
    s = t := by
  rcases hs with ⟨N, hN, rfl⟩
  rcases ht with ⟨M, hM, rfl⟩
  rw [Nat.cast_injective (hN.trans hM.symm)]

end MonoidHom
