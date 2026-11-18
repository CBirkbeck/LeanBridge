import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamilyCompatibility
import LeanBridge.ForMathlib.NumberTheory.LocalField.PossibleRamSet
import LeanBridge.ForMathlib.NumberTheory.LocalField.VisibleSlopes

/-!
# The Herbrand invariants of the extensions of a `p`-adic field

Let `K` be a `p`-adic field with `v_K(p) = e₀`, its absolute ramification index, and
`I = (r_1, …, r_w)_ε^f` a Herbrand invariant at `p`. LMFDB `lf.herbrand_invariant` gives necessary
conditions for `I` to be the Herbrand invariant of an extension of `K`: `I` must be compatible with
`e₀` (`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.isCompatible`). This file proves
that they are sufficient, so that the family `I / K` is not empty exactly when `I` is compatible
with `e₀`, and deduces the description of the possible rams of LMFDB `lf.rams` through the sets
`𝓡_k^z` (`IsNonarchimedeanLocalField.HerbrandInvariant.possibleRamSet`, with the arithmetic ram
`p z / (p - 1)` in `𝓡_1^z`):

* the possible rams `r_1 = ⋯ = r_w` of the totally ramified extensions of degree `p ^ w` of `K`
  are the elements of `𝓡_w^{e₀}`;
* the possible rams `(r_1, …, r_w)` over `K`, with tame degree `ε` and residue degree `f`, are those
  whose blocks of equal rams `b`, of multiplicity `d` and with `c` smaller rams, lie in
  `𝓡_d^{e₀ ε p ^ c}`; the strictly increasing ones are those with `r_k` in `𝓡_1^{e₀ ε p ^ (k - 1)}`.

A compatible invariant is admissible, and for an admissible invariant every specialisation of
Monge's generic polynomial over the ring of integers of the unramified extension `K_f` of degree
`f`, with unit coefficients at the `D`-point and the `A`-points, is an Eisenstein polynomial whose
roots in `K̄` generate over `K_f` an extension with Herbrand invariant `I` (Monge, §2.2): its
ramification polygon is the polygon of `I`, which determines the rams. Taking all coefficients
equal to `1` gives an extension in `I / K`.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.isInvariantOf_of_eval₂_specialisation_eq_zero`: a
  root of a specialisation of the generic polynomial of an admissible invariant with unit
  coefficients at the `D`- and `A`-points generates an extension with that invariant.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible.family_nonempty` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.IsCompatible.family_nonempty` (LMFDB `lf.rams`):
  an admissible, or compatible, invariant is the Herbrand invariant of an extension of `K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.family_nonempty_iff_isCompatible` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.family_nonempty_iff_isCompatibleWith` (LMFDB
  `lf.rams`, `lf.herbrand_invariant`): the Herbrand invariants of the extensions of `K` are the
  invariants compatible with `K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.family_nonempty_iff_forall_mem_possibleRamSet` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.family_nonempty_iff_of_ram_lt` (LMFDB `lf.rams`):
  the possible rams over `K`, block by block, and the strictly increasing ones.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.den_dvd_pow_ramMultiplicity_sub_one`
  (LMFDB `lf.rams`): the denominator of a ram of multiplicity `k` divides `p ^ k - 1`.
* `IsNonarchimedeanLocalField.mem_possibleRamSet_iff_exists_visibleRams_eq_replicate` (LMFDB
  `lf.rams`): the possible rams `r_1 = ⋯ = r_w` of the totally ramified extensions of degree `p ^ w`
  of `K` are the elements of `𝓡_w^{e₀}`.
* `IsNonarchimedeanLocalField.exists_visibleRams_eq_singleton_arithmetic` (LMFDB `lf.rams`): the
  arithmetic ram `p e₀ / (p - 1)`, which the set `𝓡_1^{e₀}` of the knowl as written excludes, is
  the ram of a totally ramified extension of degree `p` of `K`.
* `IsNonarchimedeanLocalField.exists_visibleRams_eq_replicate_inv` (LMFDB `lf.rams`): the
  denominator `p ^ w - 1` of a ram of multiplicity `w` occurs.

## References

* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, §2.2.
-/

open IntermediateField IsDiscreteValuationRing Polynomial TauCeti ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {p e₀ : ℕ}

namespace HerbrandInvariant

variable {I : HerbrandInvariant p}

/-- **A root of a specialisation of the generic polynomial generates an extension with the
invariant** (Monge, arXiv:1109.4617, §2.2): let `I` be admissible for `v_F(p)`, for an unramified
extension `F` of `K` of degree `f` inside `K̄`, and `α ∈ K̄` a root of the specialisation of the
generic polynomial of `I` at coefficients `f_σ ∈ 𝒪[F]` that are units at `σ = 0` and at the
`A`-points. Then `E = F(α)` has Herbrand invariant `I`. -/
lemma isInvariantOf_of_eval₂_specialisation_eq_zero (F E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K F] [IsGalois K F] [FiniteDimensional K E] [IsUnramified K F]
    (hp : ringChar 𝓀[K] = p) (hfin : Module.finrank K F = I.f) (he₀ : addVal 𝒪[F] (p : 𝒪[F]) = e₀)
    (hadm : I.IsAdmissible e₀) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {f : ℕ → 𝒪[F]}
    (hA : ∀ σ ∈ I.genericIndices, I.pointType σ = .A → IsUnit (f σ)) (hf₀ : f 0 ∉ 𝓂[F])
    {α : AlgebraicClosure K} (hE : E = (adjoin F {α}).restrictScalars K)
    (hα : (I.specialisation ϖ f).eval₂
      ((algebraMap F (AlgebraicClosure K)).comp (algebraMap 𝒪[F] F)) α = 0) :
    I.IsInvariantOf K E := by
  subst hp
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  have hFE : F ≤ E := fun x hx ↦ hE ▸ IntermediateField.algebraMap_mem _ (⟨x, hx⟩ : F)
  have hαE : α ∈ E := hE ▸ mem_adjoin_simple_self F α
  have hEM : E ≤ Algebra.galoisClosure K E := le_galoisClosure E
  let aFE : Algebra F E := (inclusion hFE).toAlgebra
  let aFM : Algebra F (Algebra.galoisClosure K E) := (inclusion (hFE.trans hEM)).toAlgebra
  let aEM : Algebra E (Algebra.galoisClosure K E) := (inclusion hEM).toAlgebra
  have sFE : IsScalarTower K F E := .of_algebraMap_eq fun _ ↦ rfl
  have sFM : IsScalarTower K F (Algebra.galoisClosure K E) := .of_algebraMap_eq fun _ ↦ rfl
  have sEM : IsScalarTower K E (Algebra.galoisClosure K E) := .of_algebraMap_eq fun _ ↦ rfl
  have sFEM : IsScalarTower F E (Algebra.galoisClosure K E) := .of_algebraMap_eq fun _ ↦ rfl
  have vFE : ValuativeExtension F E := (inclusion hFE).valuativeExtension
  have vFM : ValuativeExtension F (Algebra.galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).valuativeExtension
  have vEM : ValuativeExtension E (Algebra.galoisClosure K E) := (inclusion hEM).valuativeExtension
  have fFM : Module.Finite F (Algebra.galoisClosure K E) := .of_restrictScalars_finite K F _
  have fEM : Module.Finite E (Algebra.galoisClosure K E) := .of_restrictScalars_finite K E _
  have hcL : CharP 𝓀[E] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[E]).injective _
  have halg : Algebra.IsAlgebraic F E := .tower_top (K := K) F
  have hmem : (⟨α, hαE⟩ : E) ∈ 𝒪[E] := by
    rw [integerRing_eq_integralClosure F E, Subalgebra.mem_toSubring, mem_integralClosure_iff]
    refine ⟨I.specialisation ϖ f, monic_specialisation ϖ f, ?_⟩
    refine (algebraMap E (AlgebraicClosure K)).injective ?_
    rw [hom_eval₂, map_zero]
    exact hα
  have hgen : F⟮((⟨⟨α, hαE⟩, hmem⟩ : 𝒪[E]) : E)⟯ = ⊤ :=
    adjoin_eq_top_of_eq_restrictScalars hFE hE
  have hcomp : ((algebraMap E (AlgebraicClosure K)).comp (algebraMap 𝒪[E] E)).comp
      (algebraMap 𝒪[F] 𝒪[E]) = (algebraMap F (AlgebraicClosure K)).comp (algebraMap 𝒪[F] F) :=
    RingHom.ext fun r ↦ congrArg (algebraMap E (AlgebraicClosure K)) (coe_algebraMap_integerRing r)
  have hinj : Function.Injective ((algebraMap E (AlgebraicClosure K)).comp (algebraMap 𝒪[E] E)) :=
    (algebraMap E (AlgebraicClosure K)).injective.comp Subtype.val_injective
  have hroot : ((I.specialisation ϖ f).map (algebraMap 𝒪[F] 𝒪[E])).IsRoot ⟨⟨α, hαE⟩, hmem⟩ := by
    rw [IsRoot, eval_map]
    refine hinj ?_
    rw [map_zero, hom_eval₂, hcomp]
    exact hα
  have hs : I.HasSameRams (visibleHerbrandInvariant E) := by
    rw [visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
    exact hasSameRams_of_specialisation K E (Algebra.galoisClosure K E) rfl hadm he₀ hϖ hA hf₀
      hroot hgen
  have hdeg : inertiaDegree K E = I.f := by
    rw [IsUnramified.inertiaDegree_tower_eq K F E, hfin,
      inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top (I.specialisation ϖ f)
        (isEisensteinAt_specialisation hϖ hf₀) _ hroot hgen, mul_one]
  exact (isInvariantOf_visibleHerbrandInvariant E).of_hasSameRams hs hdeg.symm

/-- **An admissible Herbrand invariant is the invariant of an extension**: if `K` is a `p`-adic
field with `v_K(p) = e₀` and `I = (r_1, …, r_w)_ε^f` is admissible for `e₀`, then the family `I / K`
is not empty: a root in `K̄` of the specialisation of the generic polynomial of `I` with all
coefficients `1`, over the unramified extension of `K` of degree `f`, generates an extension with
Herbrand invariant `I`. -/
lemma IsAdmissible.family_nonempty (hp : ringChar 𝓀[K] = p) (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀)
    (hadm : I.IsAdmissible e₀) : (I.family K).Nonempty := by
  have hfact : Fact p.Prime := ⟨hp ▸ CharP.prime_ringChar _⟩
  have hf₀ : I.f ≠ 0 := I.f_pos.ne'
  have hur : IsUnramified K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    isUnramified_unramifiedExtension hf₀
  have he : addVal 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f]
      (p : 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f]) = e₀ := by
    rw [← map_natCast (algebraMap 𝒪[K] 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f]),
      TauCeti.addVal_algebraMap, IsUnramified.ramificationIndex_eq_one, one_nsmul, he₀]
  rcases exists_irreducible 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f] with ⟨ϖ, hϖ⟩
  have hmonic : (I.specialisation ϖ fun _ ↦ 1).Monic := monic_specialisation ϖ _
  have hdeg : ((I.specialisation ϖ fun _ ↦ 1).map
      ((algebraMap (unramifiedExtension K (AlgebraicClosure K) I.f) (AlgebraicClosure K)).comp
        (algebraMap 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f]
          (unramifiedExtension K (AlgebraicClosure K) I.f)))).degree ≠ 0 := by
    rw [hmonic.degree_map, degree_eq_natDegree hmonic.ne_zero, natDegree_specialisation]
    exact_mod_cast I.ramificationIndex_pos.ne'
  rcases IsAlgClosed.exists_root _ hdeg with ⟨α, hα⟩
  rw [IsRoot, eval_map] at hα
  have hfd : FiniteDimensional K K⟮α⟯ :=
    adjoin.finiteDimensional ((AlgebraicClosure.isAlgebraic K).isAlgebraic α).isIntegral
  exact ⟨_, ⟨unramifiedExtension K (AlgebraicClosure K) I.f ⊔ K⟮α⟯, inferInstance⟩,
    isInvariantOf_of_eval₂_specialisation_eq_zero _ _ hp (finrank_unramifiedExtension hf₀) he hadm
      hϖ (fun _ _ _ ↦ isUnit_one) (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one)
      (restrictScalars_adjoin_eq_sup K _ {α}).symm hα, rfl⟩

/-- **A compatible Herbrand invariant is the invariant of an extension** (LMFDB `lf.rams`,
`lf.herbrand_invariant`): if `K` is a `p`-adic field with `v_K(p) = e₀` and
`I = (r_1, …, r_w)_ε^f` is compatible with `e₀`, each distinct ram being geometric or arithmetic,
then there is an extension `L / K` with Herbrand invariant `I`: the family `I / K` is not empty. -/
lemma IsCompatible.family_nonempty (hp : ringChar 𝓀[K] = p) (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀)
    (h : I.IsCompatible e₀) : (I.family K).Nonempty := by
  have hfact : Fact p.Prime := ⟨hp ▸ CharP.prime_ringChar _⟩
  exact h.isAdmissible.family_nonempty hp he₀

/-- **The Herbrand invariants of the extensions of `K` are the compatible ones** (LMFDB `lf.rams`,
`lf.herbrand_invariant`): for a `p`-adic field `K` with `v_K(p) = e₀`, a Herbrand invariant
`I = (r_1, …, r_w)_ε^f` at `p` is the Herbrand invariant of an extension of `K`, that is the family
`I / K` is not empty, if and only if `I` is compatible with `e₀`. -/
lemma family_nonempty_iff_isCompatible (hp : ringChar 𝓀[K] = p)
    (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀) : (I.family K).Nonempty ↔ I.IsCompatible e₀ := by
  refine ⟨?_, fun h ↦ h.family_nonempty hp he₀⟩
  rintro ⟨-, E, hE, -⟩
  have hfd : FiniteDimensional K E.1 := E.2
  exact hE.isCompatible hp he₀

variable [Fact p.Prime] [FinitePadicExtension K p] in
/-- **The fields compatible with a Herbrand invariant are those over which it occurs** (LMFDB
`lf.herbrand_invariant`, `lf.rams`): for a finite extension `K` of `ℚ_p`, there is an extension
`L / K` with Herbrand invariant `I` if and only if `K` is compatible with `I`. -/
lemma family_nonempty_iff_isCompatibleWith : (I.family K).Nonempty ↔ I.IsCompatibleWith K :=
  family_nonempty_iff_isCompatible (ringChar_residueField_eq K p)
    (addVal_natCast_eq_absoluteRamificationIndex K p)

/-- **The possible rams over `K`** (LMFDB `lf.rams`): for a `p`-adic field `K` with `v_K(p) = e₀`,
the rams `(r_1, …, r_w)` with tame degree `ε` and residue degree `f` occur over `K` if and only if
each distinct ram `b`, of multiplicity `d` and with `c` rams smaller than it, lies in
`𝓡_d^{e₀ ε p ^ c}`: the rams are chosen block by block, the block of `b` from the set attached to
the absolute ramification index `e₀ ε p ^ c` of the intermediate field cut out by the smaller
rams. -/
lemma family_nonempty_iff_forall_mem_possibleRamSet (hp : ringChar 𝓀[K] = p)
    (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀) : (I.family K).Nonempty ↔
      ∀ b ∈ (Finset.Icc 1 I.w).image I.ram,
        b ∈ possibleRamSet p (I.ramMultiplicity b) (e₀ * I.ε * p ^ I.ramCountLT b) := by
  have hfact : Fact p.Prime := ⟨hp ▸ CharP.prime_ringChar _⟩
  rw [family_nonempty_iff_isCompatible hp he₀, isCompatible_iff_forall_mem_possibleRamSet]

/-- **The strictly increasing possible rams over `K`** (LMFDB `lf.rams`): for a `p`-adic field `K`
with `v_K(p) = e₀`, strictly increasing rams `r_1 < ⋯ < r_w` with tame degree `ε` and residue
degree `f` occur over `K` if and only if `r_k` lies in `𝓡_1^{e₀ ε p ^ (k - 1)}` for `1 ≤ k ≤ w`. -/
lemma family_nonempty_iff_of_ram_lt (hp : ringChar 𝓀[K] = p) (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀)
    (hI : ∀ j < I.w, I.ram j < I.ram (j + 1)) : (I.family K).Nonempty ↔
      ∀ k ∈ Finset.Icc 1 I.w, I.ram k ∈ possibleRamSet p 1 (e₀ * I.ε * p ^ (k - 1)) := by
  have hfact : Fact p.Prime := ⟨hp ▸ CharP.prime_ringChar _⟩
  rw [family_nonempty_iff_isCompatible hp he₀, isCompatible_iff_of_ram_lt hI]

/-- **The denominator of a ram divides `p ^ k - 1`** (LMFDB `lf.rams`): if `E` is an extension
inside `K̄` of a `p`-adic field `K` with Herbrand invariant `I = (r_1, …, r_w)_ε^f`, at the residue
characteristic `p` of `K`, then the denominator of a ram `b` of `E / K` divides `p ^ k - 1`, where
`k` is the multiplicity of `b` among `r_1, …, r_w`. -/
lemma IsInvariantOf.den_dvd_pow_ramMultiplicity_sub_one
    {E : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E] {b : ℚ}
    (hp : ringChar 𝓀[K] = p) (hE : I.IsInvariantOf K E) (hb : b ∈ (Finset.Icc 1 I.w).image I.ram) :
    b.den ∣ p ^ I.ramMultiplicity b - 1 := by
  have hpp : p.Prime := hp ▸ CharP.prime_ringChar _
  have hd : (((p : ℚ) ^ I.ramMultiplicity b - 1) * b).den = 1 :=
    hE.den_pow_ramMultiplicity_sub_one_mul hp hb
  rwa [← Nat.cast_pow, ← Nat.cast_pred (pow_pos hpp.pos _), den_natCast_mul_eq_one_iff] at hd

lemma isCompatible_ofRams_iff (hp : p.Prime) {R : Multiset ℚ} (hR : ∀ r ∈ R, 0 < r) {e f : ℕ}
    (he : e ≠ 0) (hf : 0 < f) {w : ℕ} {α : ℚ} (hRα : R = Multiset.replicate w α) (hew : e = p ^ w)
    (hw : w ≠ 0) : (ofRams p hp R hR e f he hf).IsCompatible e₀ ↔ α ∈ possibleRamSet p w e₀ := by
  have hfact : Fact p.Prime := ⟨hp⟩
  subst hRα hew
  have hcard : (ofRams p hp (Multiset.replicate w α) hR (p ^ w) f he hf).w = w :=
    Multiset.card_replicate w α
  have h : (ofRams p hp (Multiset.replicate w α) hR (p ^ w) f he hf).IsCompatible e₀ ↔
      α ∈ possibleRamSet p (ofRams p hp (Multiset.replicate w α) hR (p ^ w) f he hf).w e₀ :=
    isCompatible_iff_of_forall_ram_eq (hcard.trans_ne hw) (Nat.ordCompl_self_pow hp)
      fun k hk ↦ Multiset.eq_of_mem_replicate <| ram_ofRams_mem p hp _ hR _ f he hf
        (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  rwa [hcard] at h

end HerbrandInvariant

lemma pos_of_addVal_natCast_eq (hp : ringChar 𝓀[K] = p) (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀) :
    0 < e₀ := by
  have hpp : p.Prime := hp ▸ CharP.prime_ringChar _
  have hn : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  rw [IsDiscreteValuationRing.addVal_natCast K p hn, Nat.cast_inj] at he₀
  exact Nat.pos_of_ne_zero <| he₀ ▸ (natCastValuation_ne_zero_iff_ringChar_eq K hpp hn).mpr hp

variable {w : ℕ} {α : ℚ}

/-- **The possible rams of the totally ramified extensions of degree `p ^ w`** (LMFDB `lf.rams`):
for a `p`-adic field `K` with absolute ramification index `e₀ = v_K(p)` and `w ≥ 1`, a rational
number `α` is the common value of the rams `r_1 = ⋯ = r_w` of a totally ramified extension of
degree `p ^ w` of `K` if and only if `α` lies in `𝓡_w^{e₀}`: it is positive and either
`(p ^ w - 1) α` is an integer prime to `p` and `α < p e₀ / (p - 1)`, or `w = 1` and
`α = p e₀ / (p - 1)`. -/
lemma mem_possibleRamSet_iff_exists_visibleRams_eq_replicate (hp : ringChar 𝓀[K] = p)
    (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀) (hw : w ≠ 0) : α ∈ HerbrandInvariant.possibleRamSet p w e₀ ↔
      ∃ (E : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K E),
        IsTotallyRamified K E ∧ Module.finrank K E = p ^ w ∧
          visibleRams E = Multiset.replicate w α := by
  subst hp
  have hpp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨hpp⟩
  constructor
  · intro hα
    have hR : ∀ r ∈ Multiset.replicate w α, 0 < r :=
      fun r hr ↦ Multiset.eq_of_mem_replicate hr ▸ hα.1
    have hε : (HerbrandInvariant.ofRams _ hpp _ hR (ringChar 𝓀[K] ^ w) 1
        (pow_ne_zero w hpp.ne_zero) one_pos).ε = 1 :=
      Nat.ordCompl_self_pow hpp
    have hcard : (HerbrandInvariant.ofRams _ hpp _ hR (ringChar 𝓀[K] ^ w) 1
        (pow_ne_zero w hpp.ne_zero) one_pos).w = w :=
      Multiset.card_replicate w α
    rcases ((HerbrandInvariant.isCompatible_ofRams_iff hpp hR (pow_ne_zero w hpp.ne_zero) one_pos
      rfl rfl hw).mpr hα).family_nonempty rfl he₀ with ⟨-, E, hE, -⟩
    have hfd : FiniteDimensional K E.1 := E.2
    refine ⟨E.1, hfd, (isTotallyRamified_iff_inertiaDegree_eq_one K E.1).mpr hE.1, ?_,
      (hE.visibleRams_eq rfl).trans (HerbrandInvariant.map_ram_ofRams hpp _ hR _ 1 _ _)⟩
    rw [← ramificationIndex_mul_inertiaDegree K E.1, hE.1, hE.2.1, hε, hcard, one_mul]
    exact mul_one _
  · rintro ⟨E, hfd, htr, hfin, hR⟩
    have hf : inertiaDegree K E = 1 := (isTotallyRamified_iff_inertiaDegree_eq_one K E).mp htr
    have he : ramificationIndex K E = ringChar 𝓀[K] ^ w := by
      rw [← hfin, ← ramificationIndex_mul_inertiaDegree K E, hf, mul_one]
    exact (HerbrandInvariant.isCompatible_ofRams_iff hpp (fun _ ↦ pos_of_mem_visibleRams E)
      ramificationIndex_pos.ne' inertiaDegree_pos hR he hw).mp <|
        (isInvariantOf_visibleHerbrandInvariant E).isCompatible rfl he₀

/-- **The arithmetic ram occurs** (LMFDB `lf.rams`): a `p`-adic field `K` with absolute
ramification index `e₀ = v_K(p)` has a totally ramified extension of degree `p` with the ram
`p e₀ / (p - 1)`. This number is not in the set `𝓡_1^{e₀}` of LMFDB `lf.rams` as written, whose
elements have a numerator prime to `p`
(`IsNonarchimedeanLocalField.HerbrandInvariant.natCast_mul_div_notMem_ramSet`). -/
lemma exists_visibleRams_eq_singleton_arithmetic (hp : ringChar 𝓀[K] = p)
    (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K E),
      IsTotallyRamified K E ∧ Module.finrank K E = p ∧
        visibleRams E = {(p * e₀ / (p - 1) : ℚ)} := by
  have hpp : p.Prime := hp ▸ CharP.prime_ringChar _
  have hpos : (0 : ℚ) < p * e₀ / (p - 1) :=
    div_pos (mul_pos (Nat.cast_pos.mpr hpp.pos) <| Nat.cast_pos.mpr <|
      pos_of_addVal_natCast_eq hp he₀) (sub_pos.mpr <| Nat.one_lt_cast.mpr hpp.one_lt)
  simpa only [pow_one, Multiset.replicate_one] using
    (mem_possibleRamSet_iff_exists_visibleRams_eq_replicate hp he₀ one_ne_zero).mp
      ⟨hpos, .inr ⟨rfl, rfl⟩⟩

/-- **The denominator `p ^ w - 1` of a ram of multiplicity `w` occurs** (LMFDB `lf.rams`): for
`w ≥ 1`, a `p`-adic field `K` has a totally ramified extension of degree `p ^ w` whose `w` rams are
all equal to `1 / (p ^ w - 1)`, of denominator `p ^ w - 1`. So the rams of an extension that is not
Galois need not be integers, and the bound of LMFDB `lf.rams` on their denominators is attained. -/
lemma exists_visibleRams_eq_replicate_inv (hp : ringChar 𝓀[K] = p)
    (he₀ : addVal 𝒪[K] (p : 𝒪[K]) = e₀) (hw : w ≠ 0) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K E),
      IsTotallyRamified K E ∧ Module.finrank K E = p ^ w ∧
        visibleRams E = Multiset.replicate w ((p ^ w - 1 : ℕ) : ℚ)⁻¹ := by
  have hpp : p.Prime := hp ▸ CharP.prime_ringChar _
  have hfact : Fact p.Prime := ⟨hpp⟩
  have he : (1 : ℚ) ≤ e₀ := Nat.one_le_cast.mpr (pos_of_addVal_natCast_eq hp he₀)
  have hp₁ : (1 : ℚ) < p := Nat.one_lt_cast.mpr hpp.one_lt
  have hn : 1 ≤ p ^ w - 1 := Nat.le_sub_one_of_lt (Nat.one_lt_pow hw hpp.one_lt)
  have hn' : (1 : ℚ) ≤ (p ^ w - 1 : ℕ) := Nat.one_le_cast.mpr hn
  have hcast : (p : ℚ) ^ w - 1 = (p ^ w - 1 : ℕ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hpp.pos), Nat.cast_pow, Nat.cast_one]
  refine (mem_possibleRamSet_iff_exists_visibleRams_eq_replicate hp he₀ hw).mp <|
    (HerbrandInvariant.mem_possibleRamSet_iff hw).mpr ⟨inv_pos.mpr (by linarith), .inl ?_⟩
  rw [hcast, mul_inv_cancel₀ (by linarith)]
  refine ⟨Rat.den_one, fun h ↦ hpp.one_lt.ne' ?_, ?_⟩
  · exact Int.natCast_inj.mp <| Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h
  · exact (inv_le_one_of_one_le₀ hn').trans_lt <| (lt_div_iff₀ (by linarith)).mpr <| by nlinarith

end IsNonarchimedeanLocalField
