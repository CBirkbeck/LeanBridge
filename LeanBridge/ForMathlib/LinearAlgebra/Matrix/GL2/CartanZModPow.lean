import LeanBridge.ForMathlib.RingTheory.Etale.QuadraticZModPow

/-!
# Cartan subgroups of `GL₂(ℤ/p^eℤ)`

Let `p` be a prime and `e ≥ 1`. A Cartan subgroup of `GL₂(ℤ/p^eℤ)` is the image of `Aˣ` for a free
étale algebra `A` of rank `2` over `ℤ/p^eℤ` with a basis (LMFDB `gl2.cartan`). Such an algebra is
the split algebra `ℤ/p^eℤ × ℤ/p^eℤ` or the non-split algebra `NonsplitCartanAlgebraPow p e`, and
changing the basis conjugates the Cartan subgroup, so every Cartan subgroup is conjugate to the
diagonal torus, the Cartan subgroup of the split algebra in its standard basis, or to the Cartan
subgroup of the non-split algebra in its basis `(1, ω)`. The diagonal torus is the Cartan subgroup
of `ℤ/p^eℤ × ℤ/p^eℤ` in its standard basis (`Matrix.GeneralLinearGroup.cartanSubgroup_finTwoProd`).

## Main results

* `Matrix.GeneralLinearGroup.IsCartanSubgroup.exists_map_conj_eq` (LMFDB `gl2.cartan`): every
  Cartan subgroup of `GL₂(ℤ/p^eℤ)` is conjugate to the diagonal torus or to the Cartan subgroup of
  the non-split algebra.
-/

open Module TauCeti

namespace Matrix.GeneralLinearGroup

variable {p e : ℕ} [Fact p.Prime] [NeZero e] {H : Subgroup (GL (Fin 2) (ZMod (p ^ e)))}

/-- **The Cartan subgroups of `GL₂(ℤ/p^eℤ)`** (LMFDB `gl2.cartan`): every Cartan subgroup of
`GL₂(ℤ/p^eℤ)` is conjugate to the diagonal torus, the Cartan subgroup of the split algebra in its
standard basis, or to the Cartan subgroup of the non-split algebra `NonsplitCartanAlgebraPow p e`
in its basis `(1, ω)`. -/
lemma IsCartanSubgroup.exists_map_conj_eq (hH : IsCartanSubgroup H) :
    ∃ g : GL (Fin 2) (ZMod (p ^ e)), H.map (MulAut.conj g).toMonoidHom = diagonalTorus _ 2 ∨
      H.map (MulAut.conj g).toMonoidHom = cartanSubgroup (QuadraticAlgebra.basis
        ((nonsplitCartanA p).val : ZMod (p ^ e)) ((nonsplitCartanB p).val : ZMod (p ^ e))) := by
  rcases hH with ⟨A, _, _, _, b, rfl⟩
  rcases nonempty_algEquiv_prod_or_nonempty_algEquiv_nonsplitCartanAlgebraPow b with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · rcases exists_map_conj_cartanSubgroup_eq b ((Basis.finTwoProd _).map φ.symm.toLinearEquiv) with
      ⟨g, hg⟩
    exact ⟨g, .inl ((hg.trans (cartanSubgroup_basis_map _ _)).trans (cartanSubgroup_finTwoProd _))⟩
  · rcases exists_map_conj_cartanSubgroup_eq b
      ((QuadraticAlgebra.basis _ _).map φ.symm.toLinearEquiv) with ⟨g, hg⟩
    exact ⟨g, .inr (hg.trans (cartanSubgroup_basis_map _ _))⟩

end Matrix.GeneralLinearGroup
