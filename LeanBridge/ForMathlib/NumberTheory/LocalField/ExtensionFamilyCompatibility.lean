import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamilyInvariants
import LeanBridge.ForMathlib.NumberTheory.LocalField.HerbrandInvariantCompatibility

/-!
# A `p`-adic field is compatible with the Herbrand invariants of its extensions

Let `K` be a `p`-adic field with absolute ramification index `e_K = v_K(p)`. LMFDB
`lf.herbrand_invariant` states that for a Herbrand invariant `I = (r_1, …, r_w)_ε^f` to be the
Herbrand invariant of some extension `L / K`, the field `K` must be compatible with `I`: for each
distinct ram `b_i`, of multiplicity `d_i`, the number `(p ^ d_i - 1) b_i` is an integer, and either
it is prime to `p` and `b_i < p ^ (d_1 + ⋯ + d_{i - 1} + 1) ε e_K / (p - 1)`, or `d_i = 1` and
`b_i = p ^ (d_1 + ⋯ + d_{i - 1} + 1) ε e_K / (p - 1)`. This file proves it, for the extensions `E`
of `K` inside `K̄` with Herbrand invariant `I` in the sense of
`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf`, that is the extensions in the family
`I / K`: the invariant is admissible for the valuation of `p` in the unramified extension `K_f` of
`K` of degree `f` (Monge's conditions at the vertices of the ramification polygon), which is
`e_K`, and an admissible invariant is compatible
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible.isCompatible`). Every finite
extension of `K` inside `K̄` has a Herbrand invariant
(`IsNonarchimedeanLocalField.isInvariantOf_visibleHerbrandInvariant`), so the theorems apply to
all of them.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.isAdmissible`: the Herbrand
  invariant of an extension of `K` is admissible for `v_K(p)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.den_pow_ramMultiplicity_sub_one_mul`
  (LMFDB `lf.herbrand_invariant`): `(p ^ d_i - 1) b_i` is an integer.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.isCompatible` (LMFDB
  `lf.herbrand_invariant`): the Herbrand invariant of an extension of `K` is compatible with
  `v_K(p)`.
* `IsNonarchimedeanLocalField.addVal_natCast_eq_absoluteRamificationIndex`: for a finite extension
  `K` of `ℚ_p`, `v_K(p)` is the absolute ramification index of `K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.isCompatibleWith` (LMFDB
  `lf.herbrand_invariant`): a finite extension `K` of `ℚ_p` is compatible with the Herbrand
  invariant of each of its extensions.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isCompatibleWith_iff_of_eq` (LMFDB
  `lf.herbrand_invariant`): compatibility depends only on the absolute ramification index.
-/

open IsDiscreteValuationRing TauCeti ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {p e₀ : ℕ}

variable (K p) in
/-- **The valuation of `p` is the absolute ramification index**: for a finite extension `K` of
`ℚ_p`, the normalised valuation of `p` in `𝒪[K]` is the absolute ramification index `e_K` of
`K`. -/
lemma addVal_natCast_eq_absoluteRamificationIndex [Fact p.Prime] [FinitePadicExtension K p] :
    addVal 𝒪[K] (p : 𝒪[K]) = absoluteRamificationIndex K p := by
  rw [IsDiscreteValuationRing.addVal_natCast K p (NeZero.ne _),
    absoluteRamificationIndex_eq_natCastValuation]

namespace HerbrandInvariant

variable {I : HerbrandInvariant p} {b : ℚ}

variable [Fact p.Prime] [FinitePadicExtension K p] in
/-- **Compatibility depends only on the absolute ramification index** (LMFDB
`lf.herbrand_invariant`): two finite extensions of `ℚ_p` with the same absolute ramification index
are compatible with the same Herbrand invariants. -/
lemma isCompatibleWith_iff_of_eq {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K'] [FinitePadicExtension K' p]
    (h : absoluteRamificationIndex K p = absoluteRamificationIndex K' p) :
    I.IsCompatibleWith K ↔ I.IsCompatibleWith K' := by
  rw [IsCompatibleWith, IsCompatibleWith, h]

variable [CharZero K] {E : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E]

/-- **The Herbrand invariant of an extension is admissible for `v_K(p)`**: if `E` is an extension
inside `K̄` with Herbrand invariant `I`, at the residue characteristic `p` of `K`, then `I` is
admissible for the valuation `e₀` of `p` in `K`, which is its valuation in the unramified extension
of `K` of degree `f`. -/
lemma IsInvariantOf.isAdmissible (hp : ringChar 𝓀[K] = p) (hE : I.IsInvariantOf K E)
    (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀) : I.IsAdmissible e₀ := by
  have hf₀ : I.f ≠ 0 := I.f_pos.ne'
  have hur : IsUnramified K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    isUnramified_unramifiedExtension hf₀
  have he : addVal 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f]
      (p : 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f]) = e₀ := by
    rw [← map_natCast (algebraMap 𝒪[K] 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f]),
      TauCeti.addVal_algebraMap, IsUnramified.ramificationIndex_eq_one, one_nsmul, he₀]
  exact isAdmissible_of_isInvariantOf _ E hp (unramifiedExtension_le_of_isInvariantOf hE)
    (finrank_unramifiedExtension hf₀) hur hE he

/-- **`(p ^ d - 1) b` is an integer** (LMFDB `lf.herbrand_invariant`): if `E` is an extension
inside `K̄` with Herbrand invariant `I`, at the residue characteristic `p` of `K`, and `b` is a ram
of `I` of multiplicity `d`, then `(p ^ d - 1) b` is an integer. -/
lemma IsInvariantOf.den_pow_ramMultiplicity_sub_one_mul (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) (hb : b ∈ (Finset.Icc 1 I.w).image I.ram) :
    (((p : ℚ) ^ I.ramMultiplicity b - 1) * b).den = 1 := by
  have hfact : Fact p.Prime := ⟨hp ▸ CharP.prime_ringChar _⟩
  have he : addVal 𝒪[K] (p : 𝒪[K]) = TauCeti.natCastValuation K p (NeZero.ne _) :=
    IsDiscreteValuationRing.addVal_natCast K p _
  exact (hE.isAdmissible hp he).den_pow_ramMultiplicity_sub_one_mul hb

/-- **Compatibility is necessary** (LMFDB `lf.herbrand_invariant`): if `E` is an extension inside
`K̄` of a `p`-adic field `K` with Herbrand invariant `I = (r_1, …, r_w)_ε^f`, at the residue
characteristic `p` of `K`, then `I` is compatible with the valuation `e₀` of `p` in `K`: every
distinct ram `b` of `I`, of multiplicity `d` and with `c` rams smaller than it, is geometric
(`(p ^ d - 1) b` is an integer prime to `p` and `b < p ^ (c + 1) ε e₀ / (p - 1)`) or arithmetic
(`d = 1` and `b = p ^ (c + 1) ε e₀ / (p - 1)`). -/
lemma IsInvariantOf.isCompatible (hp : ringChar 𝓀[K] = p) (hE : I.IsInvariantOf K E)
    (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀) : I.IsCompatible e₀ := by
  have hfact : Fact p.Prime := ⟨hp ▸ CharP.prime_ringChar _⟩
  exact (hE.isAdmissible hp he₀).isCompatible

variable [Fact p.Prime] [FinitePadicExtension K p] in
/-- **A `p`-adic field is compatible with the Herbrand invariants of its extensions** (LMFDB
`lf.herbrand_invariant`): if a finite extension `K` of `ℚ_p` has an extension `E` inside `K̄` with
Herbrand invariant `I`, then `K` is compatible with `I`, that is `I` is compatible with the
absolute ramification index `e_K` of `K`. -/
lemma IsInvariantOf.isCompatibleWith (hE : I.IsInvariantOf K E) : I.IsCompatibleWith K :=
  hE.isCompatible (ringChar_residueField_eq K p) (addVal_natCast_eq_absoluteRamificationIndex K p)

end HerbrandInvariant

end IsNonarchimedeanLocalField
