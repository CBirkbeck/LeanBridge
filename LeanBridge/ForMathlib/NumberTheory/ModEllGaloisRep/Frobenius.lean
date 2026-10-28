import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import LeanBridge.ForMathlib.NumberTheory.Artin.Basic
import TauCeti.NumberTheory.NumberField.ArtinSymbol
import TauCeti.NumberTheory.NumberField.FiniteGaloisIntermediateField

/-!
# Mod-`ℓ` Galois representations and their Frobenius invariants

A mod-`ℓ` Galois representation of a number field `K` is a continuous homomorphism
`ρ : Gal(K̄/K) → G(𝔽_ℓ)` to the `𝔽_ℓ`-points of an algebraic group `G`. The LMFDB's
representations take values in `GL_n(𝔽_ℓ)`, and we take `G = GL_n` (a representation into the
`𝔽_ℓ`-points of a closed subgroup of `GL_n` is one into `GL_n` with image in that subgroup).
Continuity for the discrete topology on the finite group `GL_n(𝔽_ℓ)` means that the kernel of `ρ`
is open, so that `ρ` factors through the Galois group `Gal(L/K)` of the splitting field `L` of
`ρ`, the fixed field of its kernel, a finite Galois extension of `K` (LeanBridge's
`MonoidHom.isGalois_fixedField_ker`).

At a prime `𝔭` of `K` at which `ρ` is unramified, that is, which is unramified in `L`, the Frobenius
elements of the primes of `L` above `𝔭` form a conjugacy class of `Gal(L/K)`, Tau Ceti's
`NumberField.artinSymbol`, whose image under `ρ` is a conjugacy class of `GL_n(𝔽_ℓ)`: its elements
are the Frobenius matrices of `ρ` at `𝔭`. Their characteristic polynomial, trace, determinant and
order are invariant under conjugation, hence well defined.

## Main definitions

* `MonoidHom.IsModEllGaloisRep` (LMFDB `modlgal`): mod-`ℓ` Galois representations.
* `MonoidHom.splittingField`: the splitting field of `ρ`, as a finite Galois extension of `K`.
* `MonoidHom.galoisFactor`: the homomorphism `Gal(L/K) → GL_n(𝔽_ℓ)` through which `ρ` factors.
* `MonoidHom.frobeniusClass` (LMFDB `modlgal.frobenius_matrix`): the conjugacy class of the
  Frobenius matrices at an unramified prime.
* `MonoidHom.IsFrobeniusMatrix` (LMFDB `modlgal.frobenius_matrix`): Frobenius matrices.
* `MonoidHom.frobeniusCharpoly` (LMFDB `modlgal.frobenius_charpoly`): the characteristic
  polynomial of Frobenius.
* `MonoidHom.frobeniusTrace` (LMFDB `modlgal.frobenius_trace`): the Frobenius trace.
* `MonoidHom.frobeniusDet` (LMFDB `modlgal.frobenius_determinant`): the Frobenius determinant.
* `MonoidHom.frobeniusOrder` (LMFDB `modlgal.frobenius_order`): the Frobenius order.

## Main results

* `MonoidHom.galoisFactor_restrictNormalHom`: `ρ` factors through `Gal(L/K)`.
* `MonoidHom.frobeniusCharpoly_eq`, `MonoidHom.frobeniusTrace_eq`, `MonoidHom.frobeniusDet_eq` and
  `MonoidHom.frobeniusOrder_eq`: the invariants are those of any Frobenius matrix.
-/

open IntermediateField Matrix NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {n ℓ : ℕ}
  (ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) (ZMod ℓ))

/-- A homomorphism `ρ : Gal(K̄/K) → GL_n(𝔽_ℓ)` from the absolute Galois group of a number field `K`
(Mathlib's `Field.absoluteGaloisGroup K`) is a **mod-`ℓ` Galois representation** (LMFDB `modlgal`)
if `ℓ` is prime and `ρ` is continuous for the discrete topology on `GL_n(𝔽_ℓ)`, that is, its kernel
is open in the Krull topology. The LMFDB allows values in the `𝔽_ℓ`-points of any algebraic group;
its data, and the representations here, take values in `GL_n(𝔽_ℓ)`. -/
structure IsModEllGaloisRep : Prop where
  /-- The characteristic `ℓ` is prime. -/
  prime : ℓ.Prime
  /-- A mod-`ℓ` Galois representation is continuous: its kernel is open. -/
  isOpen_ker : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))

variable {ρ} (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K)))

variable (ρ) in
/-- The **splitting field** `L` of a mod-`ℓ` Galois representation `ρ` (LMFDB
`modlgal.splitting_field`): the fixed field of the kernel of `ρ`, a finite Galois extension of `K`.
-/
noncomputable def splittingField : FiniteGaloisIntermediateField K (AlgebraicClosure K) where
  toIntermediateField := fixedField ρ.ker
  finiteDimensional := ρ.finiteDimensional_fixedField_ker hρ
  isGalois := ρ.isGalois_fixedField_ker hρ

/-- The homomorphism `Gal(L/K) → GL_n(𝔽_ℓ)` through which a mod-`ℓ` Galois representation factors,
`L` being its splitting field (`MonoidHom.galoisFactor_restrictNormalHom`). -/
noncomputable def galoisFactor : Gal(splittingField ρ hρ/K) →* GL (Fin n) (ZMod ℓ) :=
  (QuotientGroup.kerLift ρ).comp
    (InfiniteGalois.normalAutEquivQuotient ⟨ρ.ker, ρ.ker.isClosed_of_isOpen hρ⟩).symm.toMonoidHom

/-- **A mod-`ℓ` Galois representation factors through the Galois group of its splitting field.** -/
lemma galoisFactor_restrictNormalHom (σ : Gal(AlgebraicClosure K/K)) :
    galoisFactor hρ (AlgEquiv.restrictNormalHom (splittingField ρ hρ) σ) = ρ σ :=
  (congrArg (QuotientGroup.kerLift ρ) <| (MulEquiv.symm_apply_eq _).mpr
    (InfiniteGalois.normalAutEquivQuotient_apply ⟨ρ.ker, ρ.ker.isClosed_of_isOpen hρ⟩ σ).symm).trans
    (QuotientGroup.kerLift_mk ρ σ)

variable (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] (hur : ∀ (Q : Ideal (𝓞 (splittingField ρ hρ))) [Q.IsPrime]
  [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- The **conjugacy class of the Frobenius matrices** (LMFDB `modlgal.frobenius_matrix`) of a
mod-`ℓ` Galois representation `ρ` at a prime `𝔭` of `K` at which `ρ` is unramified, that is, which is
unramified in the splitting field `L` of `ρ`: the image under `ρ` of the conjugacy class of the
Frobenius elements of `Gal(L/K)` at the primes above `𝔭`, Tau Ceti's `NumberField.artinSymbol`. -/
noncomputable def frobeniusClass : ConjClasses (GL (Fin n) (ZMod ℓ)) :=
  (artinSymbol 𝔭 hur).map (galoisFactor hρ)

/-- A **Frobenius matrix** (LMFDB `modlgal.frobenius_matrix`) of a mod-`ℓ` Galois representation `ρ`
at a prime `𝔭` of `K` at which `ρ` is unramified: an element of the conjugacy class
`frobeniusClass` of the images of the Frobenius elements at `𝔭`. -/
def IsFrobeniusMatrix (A : GL (Fin n) (ZMod ℓ)) : Prop :=
  ConjClasses.mk A = frobeniusClass hρ 𝔭 hur

/-- The **characteristic polynomial of Frobenius** (LMFDB `modlgal.frobenius_charpoly`) of a mod-`ℓ`
Galois representation `ρ` at a prime `𝔭` at which `ρ` is unramified: the characteristic polynomial
of `ρ(Frob_𝔭)`, which does not depend on the Frobenius matrix (`MonoidHom.frobeniusCharpoly_eq`).
-/
noncomputable def frobeniusCharpoly : Polynomial (ZMod ℓ) :=
  Quotient.lift (s := IsConj.setoid _) (fun A : GL (Fin n) (ZMod ℓ) ↦ A.val.charpoly)
    (fun _ _ h ↦ by
      rcases isConj_iff.mp h with ⟨c, rfl⟩
      simp) (frobeniusClass hρ 𝔭 hur)

/-- The **Frobenius trace** (LMFDB `modlgal.frobenius_trace`) of a mod-`ℓ` Galois representation `ρ`
at a prime `𝔭` at which `ρ` is unramified: the trace of `ρ(Frob_𝔭)`, which does not depend on the
Frobenius matrix (`MonoidHom.frobeniusTrace_eq`). -/
noncomputable def frobeniusTrace : ZMod ℓ :=
  Quotient.lift (s := IsConj.setoid _) (fun A : GL (Fin n) (ZMod ℓ) ↦ A.val.trace)
    (fun _ _ h ↦ by
      rcases isConj_iff.mp h with ⟨c, rfl⟩
      rw [Units.val_mul, Units.val_mul, trace_units_conj]) (frobeniusClass hρ 𝔭 hur)

/-- The **Frobenius determinant** (LMFDB `modlgal.frobenius_determinant`) of a mod-`ℓ` Galois
representation `ρ` at a prime `𝔭` at which `ρ` is unramified: the determinant of `ρ(Frob_𝔭)`, the
value of the determinant character `det ∘ ρ` at `Frob_𝔭`, which does not depend on the Frobenius
matrix (`MonoidHom.frobeniusDet_eq`). -/
noncomputable def frobeniusDet : (ZMod ℓ)ˣ :=
  Quotient.lift (s := IsConj.setoid _) GeneralLinearGroup.det
    (fun _ _ h ↦ isConj_iff_eq.mp (GeneralLinearGroup.det.map_isConj h)) (frobeniusClass hρ 𝔭 hur)

/-- The **Frobenius order** (LMFDB `modlgal.frobenius_order`) of a mod-`ℓ` Galois representation
`ρ` at a prime `𝔭` at which `ρ` is unramified: the order of `ρ(Frob_𝔭)` in `GL_n(𝔽_ℓ)`, which does
not depend on the Frobenius matrix (`MonoidHom.frobeniusOrder_eq`). -/
noncomputable def frobeniusOrder : ℕ :=
  Quotient.lift (s := IsConj.setoid _) (fun A : GL (Fin n) (ZMod ℓ) ↦ orderOf A)
    (fun _ _ h ↦ by
      rcases isConj_iff.mp h with ⟨c, rfl⟩
      exact ((MulAut.conj c).orderOf_eq _).symm) (frobeniusClass hρ 𝔭 hur)

variable {hρ 𝔭 hur} {A : GL (Fin n) (ZMod ℓ)} (hA : IsFrobeniusMatrix hρ 𝔭 hur A)

include hA

/-- **The characteristic polynomial of Frobenius is that of any Frobenius matrix.** -/
lemma frobeniusCharpoly_eq : frobeniusCharpoly hρ 𝔭 hur = A.val.charpoly := by
  rw [frobeniusCharpoly, ← hA]
  rfl

/-- **The Frobenius trace is that of any Frobenius matrix.** -/
lemma frobeniusTrace_eq : frobeniusTrace hρ 𝔭 hur = A.val.trace := by
  rw [frobeniusTrace, ← hA]
  rfl

/-- **The Frobenius determinant is that of any Frobenius matrix.** -/
lemma frobeniusDet_eq : frobeniusDet hρ 𝔭 hur = GeneralLinearGroup.det A := by
  rw [frobeniusDet, ← hA]
  rfl

/-- **The Frobenius order is that of any Frobenius matrix.** -/
lemma frobeniusOrder_eq : frobeniusOrder hρ 𝔭 hur = orderOf A := by
  rw [frobeniusOrder, ← hA]
  rfl

end MonoidHom
