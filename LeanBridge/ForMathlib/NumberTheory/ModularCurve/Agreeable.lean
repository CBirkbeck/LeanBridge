import LeanBridge.ForMathlib.NumberTheory.ModularCurve.CongruenceSubgroupOfOpen

/-!
# Agreeable subgroups of `GL₂(ℤ̂)`

Following Zywina (*Explicit open images for elliptic curves over `ℚ`*, §1.4), an open subgroup `H`
of `GL₂(ℤ̂)` is agreeable if `det(H) = ℤ̂ˣ`, `H` contains the scalar matrices, and the levels of
`H ≤ GL₂(ℤ̂)` and of `H ∩ SL₂(ℤ̂) ≤ SL₂(ℤ̂)` have the same odd prime divisors. As in
`LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL₂(ℤ̂)` is the product `∏_ℓ GL₂(ℤ_ℓ)`.

That `H` is normal in its agreeable closure `H̃` with abelian quotient `H̃ / H` (Zywina,
Prop. 8.1) is not formalised; the agreeable quotient is defined as the coset space `H̃ / H`, a
group as soon as `H` is normal in `H̃`.

## Main definitions

* `Matrix.GeneralLinearGroup.adelicScalars`: the subgroup of scalar matrices of `GL₂(ℤ̂)`.
* `Matrix.GeneralLinearGroup.IsAgreeable` (LMFDB `modcurve.agreeable`): agreeable subgroups.
* `Matrix.GeneralLinearGroup.agreeableClosure` (LMFDB `modcurve.agreeable`): the agreeable closure.
* `Matrix.GeneralLinearGroup.AgreeableQuotient` (LMFDB `modcurve.agreeable`): the agreeable
  quotient.

## Main results

* `Matrix.GeneralLinearGroup.isAgreeable_top`: `GL₂(ℤ̂)` itself is agreeable.
* `Matrix.GeneralLinearGroup.le_agreeableClosure`: a subgroup is contained in its agreeable closure.
-/

namespace Matrix.GeneralLinearGroup

variable (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- The subgroup of **scalar matrices** of `GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)`, the image of
`ℤ̂ˣ = ∏_ℓ ℤ_ℓˣ`. -/
noncomputable def adelicScalars : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) :=
  MonoidHom.range <| MonoidHom.pi fun ℓ ↦
    (scalar (Fin 2)).comp (Pi.evalMonoidHom (fun ℓ : Nat.Primes ↦ ℤ_[ℓ]ˣ) ℓ)

/-- An open subgroup `H` of `GL₂(ℤ̂)` is **agreeable** (LMFDB `modcurve.agreeable`, after Zywina) if
`det(H) = ℤ̂ˣ`, `H` contains the scalar matrices, and the level of `H ≤ GL₂(ℤ̂)` and the level of
`H ∩ SL₂(ℤ̂) ≤ SL₂(ℤ̂)` have the same odd prime divisors. -/
structure IsAgreeable : Prop where
  /-- An agreeable subgroup is open. -/
  isOpen : IsOpen (H : Set (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))
  /-- The determinant of an agreeable subgroup is surjective onto `ℤ̂ˣ`. -/
  map_adelicDet : H.map adelicDet = ⊤
  /-- An agreeable subgroup contains the scalar matrices. -/
  adelicScalars_le : adelicScalars ≤ H
  /-- The levels of `H` and of `H ∩ SL₂(ℤ̂)` have the same odd prime divisors. -/
  primeFactors_erase_two : (adelicLevel ⊤ H).primeFactors.erase 2 =
    (adelicLevel adelicSL (H ⊓ adelicSL)).primeFactors.erase 2

/-- The **agreeable closure** (LMFDB `modcurve.agreeable`) of a subgroup `H` of `GL₂(ℤ̂)`: the
intersection of the agreeable open subgroups of `GL₂(ℤ̂)` that contain `H`. -/
noncomputable def agreeableClosure : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) :=
  sInf {K | IsAgreeable K ∧ H ≤ K}

/-- The **agreeable quotient** (LMFDB `modcurve.agreeable`) `H̃ / H` of a subgroup `H` of `GL₂(ℤ̂)`
by its agreeable closure `H̃`, as a coset space; it is a group when `H` is normal in `H̃`, which
holds for open `H` (Zywina, Prop. 8.1, not formalised), and it is then finite abelian. -/
abbrev AgreeableQuotient : Type :=
  agreeableClosure H ⧸ H.subgroupOf (agreeableClosure H)

/-- **A subgroup of `GL₂(ℤ̂)` is contained in its agreeable closure.** -/
lemma le_agreeableClosure : H ≤ agreeableClosure H :=
  le_sInf fun _ hK ↦ hK.2

lemma adelicLevel_self : adelicLevel H H = 1 :=
  le_antisymm (Nat.sInf_le ⟨one_pos, inf_eq_left.mpr (Subgroup.le_comap_map _ H)⟩)
    (Nat.sInf_mem (⟨1, one_pos, inf_eq_left.mpr (Subgroup.le_comap_map _ H)⟩ :
      ∃ N, N ∈ {N : ℕ | 0 < N ∧ H ⊓ (H.map (adelicReduction N)).comap (adelicReduction N) = H})).1

/-- **`GL₂(ℤ̂)` is agreeable.** -/
lemma isAgreeable_top : IsAgreeable ⊤ where
  isOpen := isOpen_univ
  map_adelicDet := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact fun u ↦ ⟨fun ℓ ↦ (det_surjective (u ℓ)).choose,
      funext fun ℓ ↦ (det_surjective (u ℓ)).choose_spec⟩
  adelicScalars_le := le_top
  primeFactors_erase_two := by rw [top_inf_eq, adelicLevel_self, adelicLevel_self]

end Matrix.GeneralLinearGroup
