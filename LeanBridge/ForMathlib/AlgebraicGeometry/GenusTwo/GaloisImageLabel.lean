import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The labels of the mod-`ℓ` Galois images of genus 2 curves

Let `ℓ` be a prime and `A` the Jacobian of a genus 2 curve over a number field `K`. The Weil pairing
makes the mod-`ℓ` Galois representation of `A` take values in the group `GSp(4, 𝔽_ℓ)` of symplectic
similitudes of `A[ℓ] ≅ 𝔽_ℓ⁴`. The LMFDB labels the subgroups `G` of `GSp(4, 𝔽_ℓ)` that do not
contain `Sp(4, 𝔽_ℓ)` and arise as images, up to conjugacy, by `L.i.n` (LMFDB
`g2c.galois_rep_modell_image`), where `L` is the prime `ℓ`, `i` the index of `G` in `GSp(4, 𝔽_ℓ)`
and `n` a positive integer that distinguishes the subgroups of the same index. The numbering `n` is
an enumeration of the LMFDB's database that the knowl does not define, and it is not formalised.
Neither is the mod-`ℓ` representation of the Jacobian, which needs the Galois action on the
`ℓ`-torsion of the Jacobian of a genus 2 curve and its Weil pairing, not available here.

What is formalised is the group `GSp(2n, R)` of symplectic similitudes over a commutative ring `R`,
the invertible matrices `A` with `A J Aᵀ = c J` for a unit `c`, where `J` is the standard
symplectic form `Matrix.J` of Mathlib's symplectic group `Matrix.symplecticGroup`, and the fact that
the index `i = [GSp(4, 𝔽_ℓ) : G]` of a subgroup `G` (`Subgroup.relIndex`) does not change under
conjugation in `GSp(4, 𝔽_ℓ)`, so that `L.i` is a function of the conjugacy class of `G`. The knowl
does not say which symplectic form defines `GSp(4, 𝔽_ℓ)`; another nondegenerate alternating form
gives a conjugate group in `GL₄(𝔽_ℓ)`, and the same indices.

## Main definitions

* `Matrix.generalSymplecticGroup` (LMFDB `g2c.galois_rep_modell_image`): the group `GSp(2n, R)`.

## Main results

* `Matrix.relIndex_map_conj_generalSymplecticGroup`: subgroups conjugate by an element of
  `GSp(2n, R)` have the same index in `GSp(2n, R)`.
-/

namespace Matrix

variable (l R : Type*) [DecidableEq l] [Fintype l] [CommRing R]

/-- The **general symplectic group** `GSp(2n, R)` (LMFDB `g2c.galois_rep_modell_image`, for
`R = 𝔽_ℓ` and `n = 2`) over a commutative ring `R`, for `l` of cardinality `n`: the group of
**symplectic similitudes**, the invertible matrices `A` with `A J Aᵀ = c J` for a unit `c` of `R`,
the multiplier of `A`, where `J` is the standard symplectic form `Matrix.J`. The similitudes with
multiplier `1` form Mathlib's symplectic group `Matrix.symplecticGroup`. -/
def generalSymplecticGroup : Subgroup (GL (l ⊕ l) R) where
  carrier := {A | ∃ c : Rˣ, A.val * J l R * A.valᵀ = (c : R) • J l R}
  mul_mem' := by
    rintro A B ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    have h₁ : (A * B).val * J l R * (A * B).valᵀ = A.val * (B.val * J l R * B.valᵀ) * A.valᵀ := by
      simp only [Units.val_mul, transpose_mul, mul_assoc]
    rw [h₁, hd, Matrix.mul_smul, Matrix.smul_mul, hc, smul_smul, Units.val_mul, mul_comm]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro A ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    have h₁ : A⁻¹.val * (A.val * J l R * A.valᵀ) * A⁻¹.valᵀ = J l R := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, ← transpose_mul,
        Units.inv_mul, transpose_one, mul_one]
    rw [hc, Matrix.mul_smul, Matrix.smul_mul, ← Units.smul_def] at h₁
    rw [← Units.smul_def]
    exact eq_inv_smul_iff.mpr h₁

variable {l R} {A P : GL (l ⊕ l) R}

lemma mem_generalSymplecticGroup_iff :
    A ∈ generalSymplecticGroup l R ↔ ∃ c : Rˣ, A.val * J l R * A.valᵀ = (c : R) • J l R :=
  Iff.rfl

lemma mem_generalSymplecticGroup_of_mem_symplecticGroup (hA : A.val ∈ symplecticGroup l R) :
    A ∈ generalSymplecticGroup l R :=
  ⟨1, (SymplecticGroup.mem_iff.mp hA).trans (one_smul R _).symm⟩

/-- **Subgroups conjugate by an element of `GSp(2n, R)` have the same index in `GSp(2n, R)`**, so
that the index `i` of the label `L.i.n` of a subgroup of `GSp(4, 𝔽_ℓ)` (LMFDB
`g2c.galois_rep_modell_image`) depends only on its conjugacy class. -/
lemma relIndex_map_conj_generalSymplecticGroup (hP : P ∈ generalSymplecticGroup l R)
    (G : Subgroup (GL (l ⊕ l) R)) : (G.map (MulAut.conj P).toMonoidHom).relIndex
    (generalSymplecticGroup l R) = G.relIndex (generalSymplecticGroup l R) := by
  have h : (generalSymplecticGroup l R).map (MulAut.conj P).toMonoidHom =
      generalSymplecticGroup l R := by
    rw [MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hP)
  rw [← Subgroup.relIndex_map_map_of_injective G (generalSymplecticGroup l R)
    (f := (MulAut.conj P).toMonoidHom) (MulAut.conj P).injective, h]

end Matrix
