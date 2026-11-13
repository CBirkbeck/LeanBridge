import LeanBridge.ForMathlib.RingTheory.Etale.QuadraticZModPow

/-!
# Cartan subgroups of `GL₂(ℤ/p^eℤ)`

Let `p` be a prime and `e ≥ 1`. A Cartan subgroup of `GL₂(ℤ/p^eℤ)` is the image of `Aˣ` for a free
étale algebra `A` of rank `2` over `ℤ/p^eℤ` with a basis (LMFDB `gl2.cartan`). Such an algebra is
the split algebra `ℤ/p^eℤ × ℤ/p^eℤ` or the non-split algebra `NonsplitCartanAlgebraPow p e`, and
changing the basis conjugates the Cartan subgroup, so every Cartan subgroup is conjugate to the
diagonal torus, the Cartan subgroup of the split algebra in its standard basis, or to the Cartan
subgroup of the non-split algebra in its basis `(1, ω)`.

The Cartan and extended Cartan subgroups of an algebra in a basis do not change when the algebra
and its basis are moved along an algebra isomorphism, as the canonical involution `x ↦ Tr(x) - x`
commutes with it. So over every commutative ring `R`, in the standard basis `(1, 0), (0, 1)` of the
split algebra `R × R`, the Cartan subgroup is the group of invertible diagonal matrices and the
extended Cartan subgroup consists of the invertible diagonal and antidiagonal matrices, as for the
algebra `Fin 2 → R` (LMFDB `gl2.cartan`, there for `R = 𝔽_p`).

## Main results

* `Matrix.GeneralLinearGroup.cartanSubgroup_finTwoProd` and
  `Matrix.GeneralLinearGroup.mem_extendedCartanSubgroup_finTwoProd_iff` (LMFDB `gl2.cartan`): the
  Cartan and the extended Cartan subgroups of `R × R` in its standard basis.
* `Matrix.GeneralLinearGroup.IsCartanSubgroup.exists_map_conj_eq` (LMFDB `gl2.cartan`): every
  Cartan subgroup of `GL₂(ℤ/p^eℤ)` is conjugate to the diagonal torus or to the Cartan subgroup of
  the non-split algebra.
-/

open Module TauCeti

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R] {A A' : Type*} [CommRing A] [Algebra R A] [CommRing A']
  [Algebra R A'] {p e : ℕ} [Fact p.Prime] [NeZero e] {H : Subgroup (GL (Fin 2) (ZMod (p ^ e)))}

lemma canonicalInvolution_algEquiv (φ : A ≃ₐ[R] A') (x : A) :
    canonicalInvolution R A' (φ x) = φ (canonicalInvolution R A x) := by
  rw [canonicalInvolution_apply, canonicalInvolution_apply, Algebra.trace_eq_of_algEquiv,
    map_sub, AlgEquiv.commutes]

lemma canonicalInvolutionGL_basis_map (b : Basis (Fin 2) R A) (φ : A ≃ₐ[R] A') :
    canonicalInvolutionGL (b.map φ.toLinearEquiv) = canonicalInvolutionGL b := by
  refine Units.ext ?_
  ext i j
  simp [coe_canonicalInvolutionGL, LinearMap.toMatrix_apply, canonicalInvolution_algEquiv]

lemma extendedCartanSubgroup_basis_map (b : Basis (Fin 2) R A) (φ : A ≃ₐ[R] A') :
    extendedCartanSubgroup (b.map φ.toLinearEquiv) = extendedCartanSubgroup b := by
  rw [extendedCartanSubgroup, extendedCartanSubgroup, cartanSubgroup_basis_map,
    canonicalInvolutionGL_basis_map]

variable (R) in
lemma finTwoProd_eq_map : Basis.finTwoProd R =
    (Pi.basisFun R (Fin 2)).map (AlgEquiv.piFinTwo R fun _ ↦ R).toLinearEquiv := by
  refine Basis.eq_of_apply_eq fun i ↦ ?_
  fin_cases i <;> rfl

variable (R) in
/-- **The Cartan subgroup of the split algebra `R × R`** (LMFDB `gl2.cartan`): in the standard
basis `(1, 0), (0, 1)` it is the group of invertible diagonal matrices. -/
lemma cartanSubgroup_finTwoProd : cartanSubgroup (Basis.finTwoProd R) = diagonalTorus R 2 := by
  rw [finTwoProd_eq_map, cartanSubgroup_basis_map, cartanSubgroup_piBasisFun]

/-- **The extended Cartan subgroup of the split algebra `R × R`** (LMFDB `gl2.cartan`): in the
standard basis `(1, 0), (0, 1)` it consists of the invertible diagonal and antidiagonal matrices,
the Cartan subgroup together with its coset of antidiagonal matrices. -/
lemma mem_extendedCartanSubgroup_finTwoProd_iff {g : GL (Fin 2) R} :
    g ∈ extendedCartanSubgroup (Basis.finTwoProd R) ↔ (g 0 1 = 0 ∧ g 1 0 = 0) ∨
      (g 0 0 = 0 ∧ g 1 1 = 0) := by
  rw [finTwoProd_eq_map, extendedCartanSubgroup_basis_map,
    mem_extendedCartanSubgroup_piBasisFun_iff]

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
