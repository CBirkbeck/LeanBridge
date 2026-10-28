import LeanBridge.ForMathlib.NumberTheory.ModularCurve.CongruenceSubgroupOfOpen
import Mathlib.GroupTheory.DoubleCoset

/-!
# The genus of an open subgroup of `GL₂(ℤ̂)` or `GL₂(ℤ_ℓ)`

Let `H` be an open subgroup of `GL₂(ℤ̂)` or `GL₂(ℤ_ℓ)` of level `N`, let `H_N` be its reduction
modulo `N`, and let `Γ_H = ±H_N ∩ SL₂(ℤ/Nℤ)`. The genus of `H` is
`g(H) = 1 + i/12 - ν₂/4 - ν₃/3 - ν_∞/2`, where `i` is the index of `Γ_H` in `SL₂(ℤ/Nℤ)`, `ν₂` and
`ν₃` are the numbers of right cosets of `Γ_H` fixed by the right action of `[[0, 1], [-1, 0]]` and
`[[0, 1], [-1, -1]]`, and `ν_∞` is the number of orbits of the right cosets under the right action
of `[[1, 1], [0, 1]]`, that is, the number of double cosets `Γ_H \ SL₂(ℤ/Nℤ) / ⟨[[1, 1], [0, 1]]⟩`.

The formula is first defined for any subgroup `Γ` of a group `G` and three elements of `G`, then
applied to `Γ_H` inside `SL₂(ℤ/Nℤ)` and the reductions of the three matrices. As in
`LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, reduction modulo `N` of `GL₂(ℤ̂)` takes
values in `∏_ℓ GL₂(ℤ / ℓ ^ v_ℓ(N) ℤ) = GL₂(ℤ/Nℤ)`, and that of `GL₂(ℤ_ℓ)` in
`GL₂(ℤ / ℓ ^ v_ℓ(N) ℤ)`; `SL₂` is the kernel of the determinant there.

That `g(H)` is a nonnegative integer, independent of the choice of `N` among the multiples of the
level, and equal to the genus of the geometric components of the modular curve `X_H` and of the
Riemann surface `Γ \ ℍ*` for the inverse image `Γ` of `Γ_H` in `SL₂(ℤ)` is not formalised.

## Main definitions

* `Subgroup.numFixedRightCosets`: the number of right cosets of a subgroup fixed by an element.
* `Subgroup.modularGenusFormula`: the genus formula `1 + i/12 - ν₂/4 - ν₃/3 - ν_∞/2`.
* `Matrix.GeneralLinearGroup.adelicGenus` (LMFDB `gl2.genus`): the genus of a subgroup of `GL₂(ℤ̂)`.
* `Matrix.GeneralLinearGroup.padicGenus` (LMFDB `gl2.genus`): the genus of a subgroup of
  `GL₂(ℤ_ℓ)`.
-/

open scoped MatrixGroups

namespace Subgroup

variable {G : Type*} [Group G] (Γ : Subgroup G)

/-- The number of **right cosets** `Γg` of a subgroup `Γ` of `G` **fixed** by the right action of
`σ ∈ G`, that is, such that `Γgσ = Γg`, or equivalently `gσg⁻¹ ∈ Γ`. -/
noncomputable def numFixedRightCosets (σ : G) : ℕ :=
  Nat.card {x : Quotient (QuotientGroup.rightRel Γ) // ∃ g, Quotient.mk _ g = x ∧ g * σ * g⁻¹ ∈ Γ}

/-- The **genus formula** `1 + i/12 - ν₂/4 - ν₃/3 - ν_∞/2` for a subgroup `Γ` of a group `G` and
elements `σ₂, σ₃, δ ∈ G`: `i` is the index of `Γ`, `ν₂` and `ν₃` are the numbers of right cosets of
`Γ` fixed by `σ₂` and `σ₃`, and `ν_∞` is the number of double cosets `Γ \ G / ⟨δ⟩`, the orbits of
the right cosets under the right action of `δ`. For `G = SL₂(ℤ)` or `SL₂(ℤ/Nℤ)` and the matrices
`[[0, 1], [-1, 0]]`, `[[0, 1], [-1, -1]]` and `[[1, 1], [0, 1]]`, this is the genus of `Γ`. -/
noncomputable def modularGenusFormula (σ₂ σ₃ δ : G) : ℚ :=
  1 + Γ.index / 12 - Γ.numFixedRightCosets σ₂ / 4 - Γ.numFixedRightCosets σ₃ / 3 -
    Nat.card (DoubleCoset.Quotient (Γ : Set G) (zpowers δ)) / 2

end Subgroup

namespace Matrix.GeneralLinearGroup

/-- The matrix `[[0, 1], [-1, -1]]` of order three in `SL₂(ℤ)`. -/
def sl2zOrderThree : SL(2, ℤ) :=
  ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two_of]⟩

/-- The **genus formula of a reduction**: for a group `R` (such as `GL₂(ℤ/Nℤ)`) with a subgroup
`S` (such as `SL₂(ℤ/Nℤ)`), a morphism `ρ : SL₂(ℤ) → S` (reduction modulo `N`) and a subgroup `K` of
`R` (the reduction `H_N` of `H`), the genus formula for `Γ = ±K ∩ S` in `S` and the images under `ρ`
of `[[0, 1], [-1, 0]]`, `[[0, 1], [-1, -1]]` and `[[1, 1], [0, 1]]`. -/
noncomputable def reductionGenus {R : Type*} [Group R] [HasDistribNeg R] (S : Subgroup R)
    (ρ : SL(2, ℤ) →* S) (K : Subgroup R) : ℚ :=
  Subgroup.modularGenusFormula (K.adjoinNegOne.comap S.subtype) (ρ ModularGroup.S⁻¹)
    (ρ sl2zOrderThree) (ρ ModularGroup.T)

lemma det_map_sl2z {S : Type*} [CommRing S] (f : ℤ →+* S) (g : SL(2, ℤ)) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ).map f).det = 1 :=
  (SpecialLinearGroup.map f g).2

section Adelic

variable (N : ℕ) (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- The special linear group `SL₂(ℤ/Nℤ)` inside `∏_ℓ GL₂(ℤ / ℓ ^ v_ℓ(N) ℤ) = GL₂(ℤ/Nℤ)`. -/
noncomputable def adelicReductionSL :
    Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))) :=
  (MonoidHom.pi fun ℓ ↦ det.comp (Pi.evalMonoidHom
    (fun ℓ : Nat.Primes ↦ GL (Fin 2) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))) ℓ)).ker

/-- Reduction modulo `N` of `SL₂(ℤ)`, with values in `SL₂(ℤ/Nℤ)` inside
`∏_ℓ GL₂(ℤ / ℓ ^ v_ℓ(N) ℤ)`. -/
noncomputable def sl2zAdelicReduction : SL(2, ℤ) →* adelicReductionSL N :=
  ((adelicReduction N).comp sl2zToAdelic).codRestrict _ fun g ↦ funext fun ℓ ↦ Units.ext <| by
    simpa [adelicReduction, padicReduction, sl2zToAdelic] using
      det_map_sl2z ((PadicInt.toZModPow _).comp (Int.castRingHom ℤ_[ℓ])) g

/-- The **genus** (LMFDB `gl2.genus`) of a subgroup `H` of `GL₂(ℤ̂)` of level `N`:
`g(H) = 1 + i/12 - ν₂/4 - ν₃/3 - ν_∞/2` for `Γ_H = ±H_N ∩ SL₂(ℤ/Nℤ)` in `SL₂(ℤ/Nℤ)`, where `H_N`
is the reduction of `H` modulo `N` (see `reductionGenus`). -/
noncomputable def adelicGenus : ℚ :=
  reductionGenus _ (sl2zAdelicReduction (adelicLevel ⊤ H)) (H.map (adelicReduction _))

end Adelic

section Padic

variable (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ) (H : Subgroup (GL (Fin 2) ℤ_[ℓ]))

/-- Reduction modulo `N` of `SL₂(ℤ)`, with values in `SL₂(ℤ / ℓ ^ v_ℓ(N) ℤ)`. -/
noncomputable def sl2zPadicReduction :
    SL(2, ℤ) →* (det : GL (Fin 2) (ZMod (ℓ ^ N.factorization ℓ)) →* _).ker :=
  ((padicReduction ℓ N).comp (SpecialLinearGroup.mapGL ℤ_[ℓ])).codRestrict _ fun g ↦ Units.ext <| by
    simpa [padicReduction] using
      det_map_sl2z ((PadicInt.toZModPow _).comp (Int.castRingHom ℤ_[ℓ])) g

/-- The **genus** (LMFDB `gl2.genus`) of a subgroup `H` of `GL₂(ℤ_ℓ)` of level `N`:
`g(H) = 1 + i/12 - ν₂/4 - ν₃/3 - ν_∞/2` for `Γ_H = ±H_N ∩ SL₂(ℤ/Nℤ)` in `SL₂(ℤ/Nℤ)`, where `H_N`
is the reduction of `H` modulo `N`, a power of `ℓ` (see `reductionGenus`). -/
noncomputable def padicGenus : ℚ :=
  reductionGenus _ (sl2zPadicReduction ℓ (padicLevel ℓ ⊤ H)) (H.map (padicReduction ℓ _))

end Padic

end Matrix.GeneralLinearGroup
