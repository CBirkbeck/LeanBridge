import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.GaloisRepresentation
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.IntegerEndomorphisms
import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.GaloisImageLabel

/-!
# Maximal mod-`ℓ` Galois images and nonmaximal primes of genus 2 curves

Let `A` be the Jacobian of a genus `2` curve over `ℚ`, as in the LMFDB, with its principal
polarization, and `ℓ` a prime. The mod-`ℓ` Galois representation of `A`
(`TauCeti.AlgebraicGeometry.AbelianVariety.torsionRep`) takes values in the group of symplectic
similitudes of the Weil pairing on `A[ℓ] ≅ 𝔽_ℓ⁴`, which is `GSp(4, 𝔽_ℓ)` in a symplectic basis, with
the mod-`ℓ` cyclotomic character as multiplier. Its image is maximal (LMFDB
`g2c.maximal_galois_rep`) if it is as large as possible given the constraints imposed by the Weil
pairing and the endomorphisms of `A`: for generic `A`, whose geometric endomorphism ring `End(A_ℚ̄)`
is `ℤ` (`TauCeti.AlgebraicGeometry.AbelianVariety.HasIntGeometricEndomorphismRing`), the maximal
image is all of `GSp(4, 𝔽_ℓ)`, and otherwise it is a proper subgroup, which the knowl does not
specify. The nonmaximal primes of `A` (LMFDB `g2c.galois_rep.non_maximal_primes`) are the finitely
many primes `ℓ` at which the image is not maximal; the LMFDB lists them only for generic `A`, for
which they are the primes at which the representation is not surjective onto `GSp(4, 𝔽_ℓ)`. The
definitions below make sense over any field `K`, but over a number field `K` the multiplier is onto
`𝔽_ℓˣ` only when `K ∩ ℚ(μ_ℓ) = ℚ`, and at the other primes the image is never all of `GSp(4, 𝔽_ℓ)`;
they are the LMFDB's notions for `K = ℚ`.

The Weil pairing is not available. As the image always lies in the group of symplectic similitudes
of the Weil pairing, a group isomorphic to `GSp(4, 𝔽_ℓ)`, it is that group if and only if, in some
basis of `A[ℓ]` over `𝔽_ℓ`, the matrices of the representation
(`TauCeti.AlgebraicGeometry.AbelianVariety.torsionRepMatrix`) form the standard `GSp(4, 𝔽_ℓ)` of the
symplectic form `Matrix.J` (`Matrix.generalSymplecticGroup`): a symplectic basis of the Weil pairing
is one, and conversely the image then has the order of `GSp(4, 𝔽_ℓ)`. This is how maximality is
defined here, in any dimension `g`, with `GSp(2g, 𝔽_ℓ)`: it is the knowl's maximality for generic
`A` of dimension `2`. That the image lies in the symplectic similitudes of the Weil pairing, the
maximal image for non-generic `A`, and the finiteness of the set of nonmaximal primes (from Serre's
open image theorem) are not formalised.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.HasMaximalTorsionImage` (LMFDB
  `g2c.maximal_galois_rep`): the mod-`ℓ` Galois image is `GSp(2g, 𝔽_ℓ)` in some basis of `A[ℓ]`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.nonmaximalPrimes` (LMFDB
  `g2c.galois_rep.non_maximal_primes`): the primes `ℓ` at which the mod-`ℓ` Galois image is not
  maximal.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.HasMaximalTorsionImage.exists_symplectic_mem_range`: a
  maximal mod-`ℓ` Galois image contains `Sp(2g, 𝔽_ℓ)` in some basis, so that it is not among the
  images that the LMFDB labels (LMFDB `g2c.galois_rep_modell_image`).
-/

universe u

namespace TauCeti.AlgebraicGeometry.AbelianVariety

variable {K : Type u} [Field K] (A : AbelianVariety K) (l : Type*) [Fintype l] [DecidableEq l]
  (ℓ : ℕ)

/-- The mod-`ℓ` Galois image of an abelian variety `A` over `K` is **maximal** (LMFDB
`g2c.maximal_galois_rep`) if it is the general symplectic group: in some basis of `A[ℓ] = A(Kˢ)[ℓ]`
over `𝔽_ℓ`, indexed by `l ⊕ l`, the matrices of the mod-`ℓ` Galois representation of `A`
(`torsionRepMatrix`) form the group `GSp(2g, 𝔽_ℓ)` of symplectic similitudes of the standard form
`Matrix.J` (`Matrix.generalSymplecticGroup`), for `g` the cardinality of `l`. For `A` of dimension
`g` with a principal polarization and `ℓ` invertible in `K`, the Weil pairing makes the mod-`ℓ`
image a subgroup of a group isomorphic to `GSp(2g, 𝔽_ℓ)` (not formalised), and this says that the
image is that whole group. For the Jacobian of a generic genus `2` curve over `ℚ`
(`HasIntGeometricEndomorphismRing`), with `l = Fin 2`, this is the LMFDB's maximality; for a
non-generic curve the LMFDB's maximal image is a proper subgroup of `GSp(4, 𝔽_ℓ)`, not specified
by the knowl, so that this condition is not the LMFDB's maximality. -/
def HasMaximalTorsionImage : Prop :=
  ∃ b : Module.Basis (l ⊕ l) (ZMod ℓ) (A.TorsionCoeff K ℓ),
    (A.torsionRepMatrix ℓ b).range = Matrix.generalSymplecticGroup l (ZMod ℓ)

/-- The **nonmaximal primes** (LMFDB `g2c.galois_rep.non_maximal_primes`) of an abelian variety `A`
over `K`: the primes `ℓ` at which the mod-`ℓ` Galois image of `A` is not maximal
(`HasMaximalTorsionImage`), with `l = Fin 2` for the Jacobian of a genus `2` curve. The LMFDB
gives them only for generic curves over `ℚ`, whose Jacobian has geometric endomorphism ring `ℤ`
(`HasIntGeometricEndomorphismRing`), for which they are the primes at which the mod-`ℓ` Galois
representation is not surjective onto `GSp(4, 𝔽_ℓ)`; that there are finitely many of them is not
formalised. -/
def nonmaximalPrimes : Set ℕ :=
  {ℓ | ℓ.Prime ∧ ¬A.HasMaximalTorsionImage l ℓ}

variable {A l ℓ}

lemma mem_nonmaximalPrimes : ℓ ∈ A.nonmaximalPrimes l ↔ ℓ.Prime ∧ ¬A.HasMaximalTorsionImage l ℓ :=
  Iff.rfl

/-- **A maximal mod-`ℓ` Galois image contains the symplectic group** `Sp(2g, 𝔽_ℓ)` in some basis of
`A[ℓ]`, the similitudes of multiplier `1`. -/
lemma HasMaximalTorsionImage.exists_symplectic_mem_range (h : A.HasMaximalTorsionImage l ℓ) :
    ∃ b : Module.Basis (l ⊕ l) (ZMod ℓ) (A.TorsionCoeff K ℓ), ∀ M : GL (l ⊕ l) (ZMod ℓ), M.val ∈
      Matrix.symplecticGroup l (ZMod ℓ) → M ∈ (A.torsionRepMatrix ℓ b).range := by
  rcases h with ⟨b, hb⟩
  exact ⟨b, fun M hM ↦ hb ▸ Matrix.mem_generalSymplecticGroup_of_mem_symplecticGroup hM⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
