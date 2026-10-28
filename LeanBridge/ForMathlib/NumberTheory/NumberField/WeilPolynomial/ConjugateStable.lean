import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.FrobeniusOrder

/-!
# Conjugate stable orders

The étale algebra `K = ℚ[F]` of an isogeny class of abelian varieties over `𝔽_q` with Weil
polynomial `h` comes with the algebra involution induced by `F ↦ V = q / F`, its CM-involution,
which is complex conjugation in every complex embedding of `K`. An order of `K` is conjugate stable
if the CM-involution preserves it. As for `Polynomial.EtaleAlgebra`, `K` is built from a Weil
`q`-polynomial `h`, by which the LMFDB indexes isogeny classes over `𝔽_q`.

## Main definitions

* `Polynomial.IsWeilPolynomial.cmInvolution` (LMFDB `av.fq.conjugate_stable`): the CM-involution of
  `K`.
* `Polynomial.IsWeilPolynomial.IsConjugateStable` (LMFDB `av.fq.conjugate_stable`): an order `R` of
  `K` is conjugate stable if `R = R̄`.

## Main results

* `Polynomial.IsWeilPolynomial.cmInvolution_cmInvolution`: the CM-involution is an involution.
* `Polynomial.IsWeilPolynomial.algHom_cmInvolution`: it is complex conjugation in every complex
  embedding of `K`.
* `Polynomial.IsWeilPolynomial.isConjugateStable_iff`: `R` is conjugate stable if and only if
  `R̄ ⊆ R`.
* `Polynomial.IsWeilPolynomial.isConjugateStable_frobeniusOrder` and
  `Polynomial.IsWeilPolynomial.isConjugateStable_integralClosure`: the Frobenius order `ℤ[F, V]`
  and the maximal order are conjugate stable.
-/

open ComplexConjugate

namespace Polynomial.IsWeilPolynomial

open EtaleAlgebra

variable {q : ℕ} {h : ℤ[X]} (hh : h.IsWeilPolynomial q) {R : Subalgebra ℤ h.EtaleAlgebra}
  (x : h.EtaleAlgebra)

include hh

lemma liftAlgHom_frobenius : AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ _) (verschiebung q h)
    hh.aeval_verschiebung (frobenius h) = verschiebung q h :=
  AdjoinRoot.liftAlgHom_root ..

lemma algHom_verschiebung (φ : h.EtaleAlgebra →ₐ[ℚ] h.EtaleAlgebra)
    (hφ : φ (frobenius h) = verschiebung q h) : φ (verschiebung q h) = frobenius h := by
  rw [hh.verschiebung_eq_mk, ← aeval_frobenius, ← aeval_algHom_apply, hφ,
    hh.aeval_verschiebung_verschiebungPoly]

/-- The **CM-involution** (LMFDB `av.fq.conjugate_stable`) `x ↦ x̄` of the étale algebra `ℚ[F]` of
a Weil `q`-polynomial `h` (for the LMFDB, the Weil polynomial of an isogeny class of abelian
varieties over `𝔽_q`): the algebra involution induced by `F ↦ V = q / F`, well defined as `V` is a
root of the radical of `h`. It is complex conjugation in every complex embedding of `ℚ[F]`
(`Polynomial.IsWeilPolynomial.algHom_cmInvolution`). -/
noncomputable def cmInvolution : h.EtaleAlgebra ≃ₐ[ℚ] h.EtaleAlgebra :=
  letI σ : h.EtaleAlgebra →ₐ[ℚ] h.EtaleAlgebra :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ _) (verschiebung q h) hh.aeval_verschiebung
  haveI hσ : σ.comp σ = AlgHom.id ℚ _ := EtaleAlgebra.algHom_ext <|
    (congrArg σ hh.liftAlgHom_frobenius).trans <| hh.algHom_verschiebung σ hh.liftAlgHom_frobenius
  AlgEquiv.ofAlgHom σ σ hσ hσ

lemma cmInvolution_frobenius : hh.cmInvolution (frobenius h) = verschiebung q h :=
  hh.liftAlgHom_frobenius

lemma cmInvolution_verschiebung : hh.cmInvolution (verschiebung q h) = frobenius h :=
  hh.algHom_verschiebung hh.cmInvolution hh.cmInvolution_frobenius

lemma symm_cmInvolution : hh.cmInvolution.symm = hh.cmInvolution :=
  rfl

/-- The CM-involution is an involution. -/
lemma cmInvolution_cmInvolution : hh.cmInvolution (hh.cmInvolution x) = x :=
  hh.cmInvolution.symm_apply_apply x

/-- The CM-involution of the étale algebra `ℚ[F]` of a Weil `q`-polynomial `h` is complex
conjugation in every complex embedding of `ℚ[F]`. -/
lemma algHom_cmInvolution (φ : h.EtaleAlgebra →ₐ[ℚ] ℂ) : φ (hh.cmInvolution x) = conj (φ x) := by
  have hφ :
      φ.comp hh.cmInvolution.toAlgHom = (Complex.conjAe.restrictScalars ℚ).toAlgHom.comp φ := by
    refine EtaleAlgebra.algHom_ext ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hh.cmInvolution_frobenius,
      hh.verschiebung_eq_mk, ← aeval_frobenius, ← aeval_algHom_apply]
    exact hh.aeval_verschiebungPoly <| (aeval_algHom_apply φ _ _).trans <| by
      rw [aeval_frobenius_frobeniusMinpoly, map_zero]
  exact DFunLike.congr_fun hφ x

variable (R) in
/-- An order `R` of the étale algebra `ℚ[F]` of a Weil `q`-polynomial `h` is **conjugate stable**
(LMFDB `av.fq.conjugate_stable`) if `R = R̄`, its image under the CM-involution. The definition
applies to every subring `R` of `ℚ[F]`, orders or not. -/
def IsConjugateStable : Prop :=
  R.map (hh.cmInvolution.restrictScalars ℤ).toAlgHom = R

/-- An order is conjugate stable if and only if the CM-involution maps it into itself. -/
lemma isConjugateStable_iff : hh.IsConjugateStable R ↔ ∀ x ∈ R, hh.cmInvolution x ∈ R :=
  ⟨fun hR x hx ↦ hR ▸ Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩, fun hR ↦
    (Subalgebra.map_le.mpr hR).antisymm fun x hx ↦
      Subalgebra.mem_map.mpr ⟨_, hR x hx, hh.cmInvolution_cmInvolution x⟩⟩

/-- The Frobenius order `ℤ[F, V]` is conjugate stable. -/
lemma isConjugateStable_frobeniusOrder : hh.IsConjugateStable (h.frobeniusOrder q) := by
  rw [IsConjugateStable, frobeniusOrder, AlgHom.map_adjoin, Set.image_pair]
  simp [cmInvolution_frobenius, cmInvolution_verschiebung, Set.pair_comm]

/-- The maximal order is conjugate stable. -/
lemma isConjugateStable_integralClosure :
    hh.IsConjugateStable (integralClosure ℤ h.EtaleAlgebra) :=
  integralClosure_map_algEquiv _

end Polynomial.IsWeilPolynomial
