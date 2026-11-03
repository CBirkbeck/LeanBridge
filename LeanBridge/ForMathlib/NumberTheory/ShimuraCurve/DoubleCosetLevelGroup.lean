import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.DoubleCosetHalfPlanes

/-!
# The two models of the complex points of the Shimura curve `X_H`

The stabilizers of `LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.AdelicEllipticPoint` are
computed on the model `X_H(ℂ) = B^×_+ \ (ℍ × B̂^×) / K_H` (`Subalgebra.ShimuraCurvePoints`), while
the LMFDB (knowl `shimcurve`) writes the double coset space `B^× \ (ℋ^± × B̂^×) / K_H`
(`Subalgebra.ShimuraDoubleCoset`). This file proves that the two models agree: the bijection
`[τ, b] ↦ [τ, b]` exists because a unit of `B` of negative norm exchanges the two half-planes while
an element of `B^×` mapping a point of `ℍ` into `ℍ` has positive norm, and it carries the elliptic
points of `Subalgebra.shimuraCurveEllipticPoints` to the points of `B^× \ (ℋ^± × B̂^×) / K_H` with a
nontrivial stabilizer group. So the knowl `shimcurve.elliptic_points` holds on the double coset
space of the knowl `shimcurve`: every stabilizer group has order `1`, `2`, `3`, `4` or `6`, and this
order only depends on the point.

## Main definitions

* `Subalgebra.shimuraCurvePointsToDoubleCoset`: the map
  `B^×_+ \ (ℍ × B̂^×) / K_H → B^× \ (ℋ^± × B̂^×) / K_H`.
* `Subalgebra.shimuraCurvePointsEquivDoubleCoset` (LMFDB `shimcurve`): it is a bijection.

## Main results

* `Subalgebra.shimuraCurvePointsToDoubleCoset_injective`,
  `Subalgebra.shimuraCurvePointsToDoubleCoset_surjective`: `[τ, b] ↦ [τ, b]` is bijective.
* `Subalgebra.natCard_shimuraDoubleCosetStabilizer_ofUpperHalfPlane`: the stabilizer groups of the
  two models have the same order.
* `Subalgebra.natCard_shimuraDoubleCosetStabilizer_mem` (LMFDB `shimcurve.elliptic_points`): every
  stabilizer group of `B^× \ (ℋ^± × B̂^×) / K_H` has order `1`, `2`, `3`, `4` or `6`.
* `Subalgebra.quotientMk_mem_shimuraDoubleCosetEllipticPoints_iff_natCard_mem` (LMFDB
  `shimcurve.elliptic_points`): the elliptic points of `B^× \ (ℋ^± × B̂^×) / K_H` are the points
  whose stabilizer group has order `2`, `3`, `4` or `6`.
* `Subalgebra.shimuraCurvePointsEquivDoubleCoset_mem_iff` (LMFDB `shimcurve.elliptic_points`): the
  bijection between the two models carries the elliptic points of one to those of the other.
-/

open Module MulAction UpperHalfPlane

open Matrix hiding mul_smul

private lemma ne_one_iff_mem_of_mem {n : ℕ} (h : n ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    n ≠ 1 ↔ n ∈ ({2, 3, 4, 6} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  omega

namespace Subalgebra

open UpperLowerHalfPlane

variable {B : Type*} [Ring B] [Algebra ℚ B] {O : Subalgebra ℤ B} (hO : O.IsQuaternionOrder)
  (ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (μ : B) (H : Subgroup (O.EnhancedGroup μ))

/-- The map `B^×_+ \ (ℍ × B̂^×) / K_H → B^× \ (ℋ^± × B̂^×) / K_H`, `[τ, b] ↦ [τ, b]`. -/
noncomputable def shimuraCurvePointsToDoubleCoset :
    ShimuraCurvePoints hO μ H ι → ShimuraDoubleCoset hO ι (shimuraLevelGroup hO μ H) :=
  Quotient.map' (fun p ↦ (ofUpperHalfPlane p.1, p.2)) fun _ q ⟨g, hg⟩ ↦ by
    subst hg
    exact ⟨shimuraActing hO ι g.1 g.2.2, Prod.ext
      (ofUpperHalfPlane_smul q.1 ((mem_glpos _).mp g.1.2)).symm rfl⟩

variable (b : O.FiniteAdelicAlgebraˣ) (τ : ℍ)

lemma shimuraCurvePointsToDoubleCoset_mk :
    shimuraCurvePointsToDoubleCoset hO ι μ H (Quotient.mk _ (τ, b)) =
      Quotient.mk _ (ofUpperHalfPlane τ, b) :=
  rfl

/-- **The map `B^×_+ \ (ℍ × B̂^×) / K_H → B^× \ (ℋ^± × B̂^×) / K_H` is injective**: an element of
`B^×` mapping a point of `ℍ` into `ℍ` has positive norm. -/
lemma shimuraCurvePointsToDoubleCoset_injective :
    Function.Injective (shimuraCurvePointsToDoubleCoset hO ι μ H) := by
  intro x y h
  induction x using Quotient.inductionOn with | h p => ?_
  induction y using Quotient.inductionOn with | h q => ?_
  rcases Quotient.exact h with ⟨g, hg⟩
  rcases g with ⟨_, ⟨β, k⟩, ⟨_, hk⟩, rfl⟩
  have h₁ : Units.map ι.toMonoidHom β • ofUpperHalfPlane q.1 = ofUpperHalfPlane p.1 :=
    congrArg Prod.fst hg
  have h₂ : Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β * q.2 * k⁻¹ = p.2 :=
    congrArg Prod.snd hg
  have hpos : 0 < (GeneralLinearGroup.det (Units.map ι.toMonoidHom β)).val :=
    det_pos_of_smul_eq h₁
  exact Quotient.sound ⟨(⟨β, Subgroup.mem_comap.mpr ((mem_glpos _).mpr hpos)⟩, ⟨k, hk⟩), Prod.ext
    (ofUpperHalfPlane_injective ((ofUpperHalfPlane_smul q.1 hpos).trans h₁)) h₂⟩

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B] in
/-- **The map `B^×_+ \ (ℍ × B̂^×) / K_H → B^× \ (ℋ^± × B̂^×) / K_H` is surjective**: a unit of
negative norm (`AlgHom.exists_unit_det_lt_zero`) maps the lower half-plane into the upper
half-plane. -/
lemma shimuraCurvePointsToDoubleCoset_surjective (hB : finrank ℚ B = 4) :
    Function.Surjective (shimuraCurvePointsToDoubleCoset hO ι μ H) := by
  intro x
  induction x using Quotient.inductionOn with | h p => ?_
  rcases exists_smul_ofUpperHalfPlane_eq hO ι _ p hB with ⟨g, τ', b', hg⟩
  exact ⟨Quotient.mk _ (τ', b'), Quotient.sound ⟨g⁻¹, inv_smul_eq_iff.mpr hg.symm⟩⟩

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B] in
/-- **The complex points of the Shimura curve `X_H` are the knowl's double coset space**: for an
order `O` of a quaternion algebra `B` over `ℚ`, `[τ, b] ↦ [τ, b]` is a bijection
`B^×_+ \ (ℍ × B̂^×) / K_H ≃ B^× \ (ℋ^± × B̂^×) / K_H` (LMFDB `shimcurve`). -/
noncomputable def shimuraCurvePointsEquivDoubleCoset (hB : finrank ℚ B = 4) :
    ShimuraCurvePoints hO μ H ι ≃ ShimuraDoubleCoset hO ι (shimuraLevelGroup hO μ H) :=
  Equiv.ofBijective _ ⟨shimuraCurvePointsToDoubleCoset_injective hO ι μ H,
    shimuraCurvePointsToDoubleCoset_surjective hO ι μ H hB⟩

/-- The stabilizer of `τ` in `Γ_b`, as a subgroup of `N_{B^×}(O_b)^+`. -/
private noncomputable abbrev adelicStabilizerSource :
    Subgroup ((adelicOrder hO b).shimuraGammaPlus 0 ⊤ ι) :=
  stabilizer ((adelicOrder hO b).shimuraGammaPlus 0 ⊤ ι) τ ⊓ shimuraAdelicGammaPlus hO μ H b ι

/-- The inclusion in `B^×` of the stabilizer of `τ` in `Γ_b`. -/
private noncomputable def adelicStabilizerToUnits : adelicStabilizerSource hO ι μ H b τ →* Bˣ :=
  (adelicOrder hO b).unitsNormalizer.subtype.comp
    (((adelicOrder hO b).shimuraGammaPlus 0 ⊤ ι).subtype.comp
      (adelicStabilizerSource hO ι μ H b τ).subtype)

private lemma mem_normalizerRatUnits_subgroupOf_iff {O' : Subalgebra ℤ B}
    {G : Subgroup O'.unitsNormalizer} (x : G) : x ∈ O'.normalizerRatUnits.subgroupOf G ↔
      ((x : O'.unitsNormalizer) : Bˣ) ∈ (Units.map (algebraMap ℚ B : ℚ →* B)).range :=
  Iff.rfl

private lemma shimuraAdelicStabilizer_eq_range : shimuraAdelicStabilizer hO μ H b ι τ =
    ((QuotientGroup.mk' ((adelicOrder hO b).normalizerRatUnits.subgroupOf
      ((adelicOrder hO b).shimuraGammaPlus 0 ⊤ ι))).comp
        (adelicStabilizerSource hO ι μ H b τ).subtype).range := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

private lemma exists_adelicStabilizerToUnits_eq (β : Bˣ)
    (hdet : 0 < (GeneralLinearGroup.det (Units.map ι.toMonoidHom β)).val)
    (hfix : Units.map ι.toMonoidHom β • τ = τ) (hk : (MulAut.conj b⁻¹).toMonoidHom
      (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β) ∈ shimuraLevelGroup hO μ H) :
    ∃ s, adelicStabilizerToUnits hO ι μ H b τ s = β := by
  have hΓ : β ∈ shimuraAdelicGamma hO μ H b ι := Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_comap.mpr hk, Subgroup.mem_comap.mpr ((mem_glpos _).mpr hdet)⟩
  let δ : (adelicOrder hO b).unitsNormalizer :=
    ⟨β, shimuraAdelicGamma_le_unitsNormalizer hO μ H b ι hΓ⟩
  let γ : (adelicOrder hO b).shimuraGammaPlus 0 ⊤ ι :=
    ⟨δ, mem_shimuraGammaPlus_zero_top ι hdet⟩
  exact ⟨⟨γ, mem_stabilizer_iff.mpr hfix, hΓ⟩, rfl⟩

private lemma adelicStabilizerQuotient_eq_one_iff (s : adelicStabilizerSource hO ι μ H b τ) :
    ((QuotientGroup.mk' ((adelicOrder hO b).normalizerRatUnits.subgroupOf
      ((adelicOrder hO b).shimuraGammaPlus 0 ⊤ ι))).comp
        (adelicStabilizerSource hO ι μ H b τ).subtype) s = 1 ↔
    adelicStabilizerToUnits hO ι μ H b τ s ∈ (Units.map (algebraMap ℚ B : ℚ →* B)).range :=
  (QuotientGroup.eq_one_iff _).trans (mem_normalizerRatUnits_subgroupOf_iff _)

variable [IsSimpleRing B] in
/-- **The stabilizer groups of the two models of `X_H(ℂ)` have the same order**: the stabilizer of
`(τ, b)` in `B^× × K_H` modulo the `(q, q)`, and the stabilizer of `τ` in `Γ_b = B^×_+ ∩ b K_H b⁻¹`
modulo `ℚ^×`, are isomorphic through `β ↦ (β, b⁻¹ β b)`. -/
lemma natCard_shimuraDoubleCosetStabilizer_ofUpperHalfPlane :
    Nat.card (shimuraDoubleCosetStabilizer hO ι (shimuraLevelGroup hO μ H)
      (ofUpperHalfPlane τ, b)) = Nat.card (shimuraAdelicStabilizer hO μ H b ι τ) := by
  rw [shimuraAdelicStabilizer_eq_range]
  exact natCard_shimuraDoubleCosetStabilizer_eq_natCard_range hO ι τ b
    (t := adelicStabilizerToUnits hO ι μ H b τ) (fun s ↦ (Subgroup.mem_inf.mp s.2.2).1)
    (fun s ↦ zero_lt_det_normalizerToGL _) (fun s ↦ s.2.1)
    (exists_adelicStabilizerToUnits_eq hO ι μ H b τ)
    (adelicStabilizerQuotient_eq_one_iff hO ι μ H b τ)

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B] in
/-- **The stabilizer group of a point of `B^× \ (ℋ^± × B̂^×) / K_H` has order `1`, `2`, `3`, `4` or
`6`** (LMFDB `shimcurve.elliptic_points`), for an order `O` of a quaternion algebra `B` over `ℚ`:
the point has a representative `(τ, b)` with `τ ∈ ℍ`, and the stabilizer groups of the
representatives have the same order, which is that of the stabilizer of `τ` in `Γ_b` modulo `ℚ^×`
(`Subalgebra.natCard_shimuraAdelicStabilizer_mem`). -/
lemma natCard_shimuraDoubleCosetStabilizer_mem (hB : finrank ℚ B = 4)
    (p : UpperLowerHalfPlane × O.FiniteAdelicAlgebraˣ) :
    Nat.card (shimuraDoubleCosetStabilizer hO ι (shimuraLevelGroup hO μ H) p) ∈
      ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rcases exists_smul_ofUpperHalfPlane_eq hO ι (shimuraLevelGroup hO μ H) p hB with ⟨g, τ', b', rfl⟩
  rw [natCard_shimuraDoubleCosetStabilizer_smul,
    natCard_shimuraDoubleCosetStabilizer_ofUpperHalfPlane]
  exact natCard_shimuraAdelicStabilizer_mem hO μ H b' ι τ' hB

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B] in
/-- **The elliptic points of `B^× \ (ℋ^± × B̂^×) / K_H` are the points whose stabilizer group has
order `2`, `3`, `4` or `6`** (LMFDB `shimcurve.elliptic_points`). -/
lemma quotientMk_mem_shimuraDoubleCosetEllipticPoints_iff_natCard_mem (hB : finrank ℚ B = 4)
    (p : UpperLowerHalfPlane × O.FiniteAdelicAlgebraˣ) :
    (Quotient.mk _ p : ShimuraDoubleCoset hO ι (shimuraLevelGroup hO μ H)) ∈
      shimuraDoubleCosetEllipticPoints hO ι (shimuraLevelGroup hO μ H) ↔
    Nat.card (shimuraDoubleCosetStabilizer hO ι (shimuraLevelGroup hO μ H) p) ∈
      ({2, 3, 4, 6} : Finset ℕ) :=
  (quotientMk_mem_shimuraDoubleCosetEllipticPoints_iff hO ι _ p).trans <|
    Subgroup.card_eq_one.not.symm.trans <|
      ne_one_iff_mem_of_mem (natCard_shimuraDoubleCosetStabilizer_mem hO ι μ H hB p)

private lemma quotientMk_ofUpperHalfPlane_mem_iff [IsSimpleRing B] :
    (Quotient.mk _ (ofUpperHalfPlane τ, b) : ShimuraDoubleCoset hO ι (shimuraLevelGroup hO μ H)) ∈
      shimuraDoubleCosetEllipticPoints hO ι (shimuraLevelGroup hO μ H) ↔
    shimuraAdelicStabilizer hO μ H b ι τ ≠ ⊥ :=
  (quotientMk_mem_shimuraDoubleCosetEllipticPoints_iff hO ι _ _).trans <| not_congr <|
    Subgroup.card_eq_one.symm.trans <| (congrArg (· = 1)
      (natCard_shimuraDoubleCosetStabilizer_ofUpperHalfPlane hO ι μ H b τ)).to_iff.trans
        Subgroup.card_eq_one

private lemma quotientMk_mem_shimuraCurveEllipticPoints_iff_ne_bot :
    (Quotient.mk _ (τ, b) : ShimuraCurvePoints hO μ H ι) ∈ shimuraCurveEllipticPoints hO μ H ι ↔
      shimuraAdelicStabilizer hO μ H b ι τ ≠ ⊥ :=
  (quotientMk_mem_shimuraCurveEllipticPoints_iff_mem_shimuraAdelicEllipticPoints hO μ H b ι τ).trans
    ((quotientMk_mem_shimuraAdelicEllipticPoints_iff hO μ H b ι τ).trans
      (shimuraAdelicStabilizer_ne_bot_iff hO μ H b ι τ).symm)

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B] in
/-- **The elliptic points of the two models of `X_H(ℂ)` correspond** (LMFDB
`shimcurve.elliptic_points`): under the bijection
`B^×_+ \ (ℍ × B̂^×) / K_H ≃ B^× \ (ℋ^± × B̂^×) / K_H`, the elliptic points
`Subalgebra.shimuraCurveEllipticPoints` are the points with a nontrivial stabilizer group of the
double coset space of the knowl `shimcurve`. -/
lemma shimuraCurvePointsEquivDoubleCoset_mem_iff (hB : finrank ℚ B = 4)
    (x : ShimuraCurvePoints hO μ H ι) : shimuraCurvePointsEquivDoubleCoset hO ι μ H hB x ∈
      shimuraDoubleCosetEllipticPoints hO ι (shimuraLevelGroup hO μ H) ↔
    x ∈ shimuraCurveEllipticPoints hO μ H ι := by
  induction x using Quotient.inductionOn with | h p => ?_
  exact (quotientMk_ofUpperHalfPlane_mem_iff hO ι μ H p.2 p.1).trans
    (quotientMk_mem_shimuraCurveEllipticPoints_iff_ne_bot hO ι μ H p.2 p.1).symm

end Subalgebra
