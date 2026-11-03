import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeInvariance
import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeUnramifiedBase

/-!
# Monge's representation theorem for a family of extensions

This file proves Monge's representation theorem
(`IsNonarchimedeanLocalField.HerbrandInvariant.mongeRepresentation`, LMFDB `lf.family_polynomial`;
Monge, arXiv:1109.4617, the first statement of Theorem 1 with Proposition 3 and Remark 1, and §2.2
for the converse): if the family `I / K` of a Herbrand invariant `I` over a `p`-adic field `K` is
not empty, the extensions in the family are, up to `K`-isomorphism, exactly the fields `K_f(α)` for
the roots `α ∈ K̄` of the semicanonical polynomials over `𝒪_{K_f}`.

For the direct part, an extension `L` in the family has the rams of `I` over `K`, and so over `K_f`,
and its ramification polygon is that of `I`, so the reduction loop applies. For the converse, `I` is
admissible since the family is not empty, so the ramification polygon of a semicanonical polynomial
is that of `I`, and the rams of `K_f(α)` are those of `I` since the rams are determined by the
polygon. The number of semicanonical polynomials of an extension (the second statement of Monge's
Theorem 1, and the bound by the ambiguity of LMFDB `lf.family_ambiguity`) is not treated here.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_root_of_hasSameRams`: Monge's theorem over
  `K_f`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isAdmissible_of_hasSameRams`: the Herbrand invariant
  of an extension is admissible over `K_f`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.hasSameRams_of_specialisation`: the rams of a root
  of a semicanonical polynomial.
* `IsNonarchimedeanLocalField.HerbrandInvariant.hasSameRams_of_isInvariantOf`: a finite extension
  has at most one Herbrand invariant, up to the residue degree.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.of_hasSameRams`: a Herbrand invariant
  with the rams and the residue degree of an invariant of `L` is an invariant of `L`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_adjoin_of_isInvariantOf`: Monge's theorem
  inside `K̄`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isAdmissible_of_isInvariantOf`: the Herbrand
  invariants of the extensions in a family are admissible.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isInvariantOf_of_mem_mongeSemicanonicalPolynomials`:
  the converse of Monge's theorem inside `K̄`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mongeRepresentation` (LMFDB
  `lf.family_polynomial`): Monge's representation theorem.
-/

open Algebra Finset Ideal IntermediateField IsDiscreteValuationRing IsLocalRing Polynomial TauCeti
  ValuativeRel LocalFieldsRamification

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} {I : HerbrandInvariant p}

lemma exists_addVal_natCast_eq (K F : Type*) [Field K] [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra K F] [CharZero K] (hp : p ≠ 0) :
    ∃ e₀ : ℕ, addVal 𝒪[F] (p : 𝒪[F]) = e₀ := by
  have hF : CharZero F :=
    charZero_of_injective_algebraMap (algebraMap K F).injective
  exact ⟨_, IsDiscreteValuationRing.addVal_natCast F p (Nat.cast_ne_zero.mpr hp)⟩

section Tower

variable {K F L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Algebra K F] [ValuativeExtension K F] [Module.Finite K F]
  [IsGalois K F] [IsUnramified K F] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsGalois K M] [Algebra F M] [ValuativeExtension F M] [Module.Finite F M] [IsScalarTower K F M]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Algebra F L] [ValuativeExtension F L]
  [IsScalarTower K F L] [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [IsScalarTower K L M] [IsScalarTower F L M] {ϖ : 𝒪[F]} {e₀ : ℕ}

variable (K M) in
lemma IsMongeStage.isRamificationPolygon_of_hasSameRams
    (hI : I.HasSameRams (herbrandInvariantOfTower K M L)) {g : 𝒪[F][X]} {π : 𝒪[L]}
    (hst : IsMongeStage g π) : I.IsRamificationPolygon g π := by
  have hF : IsGalois F M :=
    IsGalois.tower_top_of_isGalois K F M
  exact (hI.trans (hasSameRams_herbrandInvariantOfTower K F L M).symm).isRamificationPolygon
    (isRamificationPolygon_herbrandInvariantOfTower M hst.monic hst.isEisensteinAt hst.isRoot
      hst.adjoin_eq_top)

variable (K L M) in
/-- **Monge's theorem over `K_f`** (Monge, arXiv:1109.4617, first statement of Theorem 1, with
Proposition 3 and Remark 1; LMFDB `lf.family_polynomial`): for an unramified extension `F / K`, a
tower `M / L / F` with `M / K` finite Galois, `K` of characteristic `0`, and a Herbrand invariant
`I` with the rams of `L / K` such that `F` is the maximal unramified subextension of `L / K`, `L` is
generated over `F` by a root of a semicanonical polynomial. -/
lemma exists_root_of_hasSameRams [CharZero K] (hI : I.HasSameRams (herbrandInvariantOfTower K M L))
    (hf : inertiaDegree K L = Module.finrank K F) (hϖ : Irreducible ϖ) (C : I.MongeChoice 𝓂[F]) :
    ∃ y : 𝒪[L], F⟮(y : L)⟯ = ⊤ ∧ (I.mongeSemicanonicalPolynomials ϖ y C).Nonempty := by
  have hF : IsGalois F M :=
    IsGalois.tower_top_of_isGalois K F M
  have htr : IsTotallyRamified F L :=
    (IsUnramified.isTotallyRamified_iff_finrank_eq K F L).mpr hf.symm
  rcases hI.prime_eq with rfl
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hcF : CharP 𝓀[F] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[F]).injective _
  have hcL : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  rcases exists_addVal_natCast_eq K F (Fact.out : (ringChar 𝓀[K]).Prime).ne_zero with ⟨e₀, he₀⟩
  have he : TauCeti.ramificationIndex F L = I.ramificationIndex := by
    rw [IsUnramified.ramificationIndex_tower_eq K F L, hI.ramificationIndex_eq,
      ← ε_mul_pow_w_herbrandInvariantOfTower K M L]
    rfl
  exact exists_mem_mongeSemicanonicalPolynomials htr
    (IsMongeStage.isRamificationPolygon_of_hasSameRams K M hI)
    (fun hst hst' hdvd ↦ funext fun σ ↦ mongeSubgroup_eq_of_pow_two_dvd_sub M 𝓂[F] σ hst.monic
      hst.isEisensteinAt hst.isRoot hst.adjoin_eq_top hst'.monic hst'.isEisensteinAt hst'.isRoot
      hst'.adjoin_eq_top hϖ hdvd) hϖ he₀ he C

variable (K F L M) in
/-- **The Herbrand invariant of an extension is admissible over `K_f`**: for an unramified extension
`F / K` and a tower `M / L / F` with `M / K` finite Galois, a Herbrand invariant `I` with the rams
of `L / K`, and `F` the maximal unramified subextension of `L / K`, is admissible for `v_F(p)`. -/
lemma isAdmissible_of_hasSameRams (hI : I.HasSameRams (herbrandInvariantOfTower K M L))
    (hf : inertiaDegree K L = Module.finrank K F) (he₀ : addVal 𝒪[F] (p : 𝒪[F]) = e₀) :
    I.IsAdmissible e₀ := by
  have htr : IsTotallyRamified F L :=
    (IsUnramified.isTotallyRamified_iff_finrank_eq K F L).mpr hf.symm
  rcases hI.prime_eq with rfl
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hcL : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[L] with ⟨π, hπ⟩
  have hst : IsMongeStage (minpoly 𝒪[F] π) π :=
    isMongeStage_minpoly htr hπ
  exact .of_isRamificationPolygon he₀ hst.isMongeRoot
    (IsMongeStage.isRamificationPolygon_of_hasSameRams K M hI hst)

variable (K L M) in
/-- **The rams of a root of a semicanonical polynomial** (Monge, arXiv:1109.4617, §2.2): for an
unramified extension `F / K` and a tower `M / L / F` with `M / K` finite Galois, let `I` be a
Herbrand invariant at the residue characteristic of `K`, admissible for `v_F(p)`, and `y ∈ 𝒪[L]`,
generating `L` over `F`, a root of the specialisation of the generic polynomial of `I` at
coefficients `f_σ` that are units at `σ = 0` and at the `A`-points. Then `L / K` has the rams of
`I`. -/
lemma hasSameRams_of_specialisation (hp : ringChar 𝓀[K] = p) (hadm : I.IsAdmissible e₀)
    (he₀ : addVal 𝒪[F] (p : 𝒪[F]) = e₀) (hϖ : Irreducible ϖ) {f : ℕ → 𝒪[F]}
    (hA : ∀ σ ∈ I.genericIndices, I.pointType σ = .A → IsUnit (f σ)) (hf₀ : f 0 ∉ 𝓂[F]) {y : 𝒪[L]}
    (hroot : ((I.specialisation ϖ f).map (algebraMap 𝒪[F] 𝒪[L])).IsRoot y) (hgen : F⟮(y : L)⟯ = ⊤) :
    I.HasSameRams (herbrandInvariantOfTower K M L) := by
  subst hp
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hcL : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  have hst : IsMongeStage (I.specialisation ϖ f) y :=
    ⟨monic_specialisation ϖ f, isEisensteinAt_specialisation hϖ hf₀, hroot, hgen⟩
  have hI : I.IsRamificationPolygon (I.specialisation ϖ f) y :=
    isRamificationPolygon_specialisation hadm he₀ hϖ hA hst.isMongeRoot
  have hJ : (herbrandInvariantOfTower K M L).IsRamificationPolygon (I.specialisation ϖ f) y :=
    IsMongeStage.isRamificationPolygon_of_hasSameRams K M (.refl _) hst
  have he : I.ramificationIndex = (herbrandInvariantOfTower K M L).ramificationIndex :=
    hI.natDegree_eq.symm.trans hJ.natDegree_eq
  have hw : I.w = (herbrandInvariantOfTower K M L).w := by
    rw [← padicValNat_ramificationIndex, he, padicValNat_ramificationIndex]
  have hε : I.ε = (herbrandInvariantOfTower K M L).ε := by
    rw [ramificationIndex, ramificationIndex, hw] at he
    exact Nat.eq_of_mul_eq_mul_right
      (pow_pos (Fact.out : (ringChar 𝓀[K]).Prime).pos _) he
  exact ⟨rfl, hw, hε, ram_eq_ram_of_isRamificationPolygon hI hJ hw hε⟩

end Tower

variable {R S S' T : Type*} [CommRing R] [CommRing S] [CommRing S'] [CommRing T] [Algebra R S]
  [Algebra R S'] [Algebra R T] {𝔪 : Ideal R} (ϖ : R) (π : S)

lemma mongeSemicanonicalPolynomials_algEquiv (C : I.MongeChoice 𝔪) (e : S ≃ₐ[R] S') :
    I.mongeSemicanonicalPolynomials ϖ (e π) C = I.mongeSemicanonicalPolynomials ϖ π C := by
  ext q
  have h : aeval (e π) q = e (aeval π q) :=
    aeval_algHom_apply e.toAlgHom π q
  simp only [mongeSemicanonicalPolynomials, Set.mem_ofPred_eq,
    funext fun σ ↦ mongeSubgroup_algEquiv ϖ 𝔪 q π σ e]
  rw [h, map_eq_zero_iff e e.injective]

lemma exists_algEquiv_adjoin (φ : S →ₐ[R] T) (hφ : Function.Injective φ) {y : S}
    (hy : Algebra.adjoin R {y} = ⊤) :
    ∃ e : S ≃ₐ[R] Algebra.adjoin R {φ y}, e y = ⟨φ y, subset_adjoin rfl⟩ := by
  have h : φ.range = Algebra.adjoin R {φ y} := by
    rw [← Algebra.map_top, ← hy, AlgHom.map_adjoin, Set.image_singleton]
  exact ⟨(AlgEquiv.ofInjective φ hφ).trans (Subalgebra.equivOfEq _ _ h), Subtype.ext rfl⟩

section Invariant

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K L]

/-- **A finite extension has at most one Herbrand invariant, up to the residue degree**: two
Herbrand invariants at the same prime of a finite extension `L` of `K` have the same rams. The rams
are determined by the Swan slopes. -/
lemma hasSameRams_of_isInvariantOf [Fact p.Prime] {J : HerbrandInvariant p}
    (hI : I.IsInvariantOf K L) (hJ : J.IsInvariantOf K L) : I.HasSameRams J := by
  have hp : p.Prime :=
    Fact.out
  rcases hI with ⟨-, heI, hsI⟩
  rcases hJ with ⟨-, heJ, hsJ⟩
  have he : I.ramificationIndex = J.ramificationIndex :=
    heI.symm.trans heJ
  have hw : I.w = J.w := by
    rw [← padicValNat_ramificationIndex, he, padicValNat_ramificationIndex]
  have hε : I.ε = J.ε := by
    rw [ramificationIndex, ramificationIndex, hw] at he
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) he
  have hs : (Multiset.range I.w).map (fun k ↦ (I.swanSlope (k + 1) : ℝ)) =
      (Multiset.range J.w).map fun k ↦ (J.swanSlope (k + 1) : ℝ) :=
    hsI.symm.trans hsJ
  rw [hw, ← Multiset.coe_range, Multiset.map_coe, Multiset.map_coe, Multiset.coe_eq_coe] at hs
  have hsorted (A : HerbrandInvariant p) :
      ((List.range J.w).map fun k ↦ (A.swanSlope (k + 1) : ℝ)).Pairwise (· ≤ ·) := by
    refine List.pairwise_map.mpr (List.pairwise_lt_range.imp fun hab ↦ ?_)
    exact Rat.cast_le.mpr (swanSlope_mono (by omega))
  have hlist : (List.range J.w).map (fun k ↦ (I.swanSlope (k + 1) : ℝ)) =
      (List.range J.w).map fun k ↦ (J.swanSlope (k + 1) : ℝ) :=
    hs.eq_of_pairwise' (hsorted I) (hsorted J)
  rw [List.map_inj_left] at hlist
  have hslope {k : ℕ} (hk : k < J.w) : I.swanSlope (k + 1) = J.swanSlope (k + 1) :=
    Rat.cast_injective (α := ℝ) (hlist k (List.mem_range.mpr hk))
  have hram {k : ℕ} (hk : k ≤ J.w) : I.ram k = J.ram k := by
    induction k with
    | zero => rw [I.ram_zero, J.ram_zero]
    | succ k ih =>
      have hk' : k < J.w :=
        hk
      have hsk : I.swanSlope k = J.swanSlope k := by
        rcases k with _ | k
        · simp [swanSlope]
        · exact hslope (by omega)
      have h₁ : I.swanSlope (k + 1) = J.swanSlope (k + 1) :=
        hslope hk'
      rw [swanSlope, swanSlope, sum_range_succ, sum_range_succ] at h₁
      have h₂ : ∑ x ∈ range k, (I.ram (x + 1) - I.ram x) / (I.ε * p ^ x) =
          ∑ x ∈ range k, (J.ram (x + 1) - J.ram x) / (J.ε * p ^ x) :=
        hsk
      rw [h₂, add_right_inj, hε, ih hk'.le, div_left_inj'] at h₁
      · linarith
      · have hp₀ : (0 : ℚ) < p :=
          natCast_prime_pos
        have hε₀ : (0 : ℚ) < J.ε :=
          J.natCast_ε_pos
        positivity
  refine ⟨rfl, hw, hε, funext fun k ↦ ?_⟩
  rcases le_total k J.w with hk | hk
  · exact hram hk
  · rw [I.ram_of_le k (hw ▸ hk), J.ram_of_le k hk, hw]
    exact hram le_rfl

/-- **A Herbrand invariant with the rams and the residue degree of an invariant of `L` is an
invariant of `L`.** -/
lemma IsInvariantOf.of_hasSameRams {p' : ℕ} {J : HerbrandInvariant p'} (hJ : J.IsInvariantOf K L)
    (h : I.HasSameRams J) (hf : I.f = J.f) : I.IsInvariantOf K L := by
  have h' : I.HasSameRams J :=
    h
  rcases h with ⟨rfl, hw, hε, -⟩
  rcases hJ with ⟨h₁, h₂, h₃⟩
  rw [HerbrandInvariant.IsInvariantOf]
  refine ⟨h₁.trans hf.symm, h₂.trans (by rw [hε, hw]), h₃.trans ?_⟩
  rw [hw]
  exact Multiset.map_congr rfl fun k _ ↦ by rw [h'.swanSlope_eq]

end Invariant

section Adjoin

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {F E : IntermediateField K Ω}

lemma map_adjoin_of_le (hFE : F ≤ E) (y : E) :
    letI : Algebra F E := (inclusion hFE).toAlgebra
    haveI : IsScalarTower F E Ω := .of_algebraMap_eq fun _ ↦ rfl
    (F⟮y⟯).map (IsScalarTower.toAlgHom F E Ω) = IntermediateField.adjoin F {(y : Ω)} := by
  let a : Algebra F E :=
    (inclusion hFE).toAlgebra
  have hs : IsScalarTower F E Ω :=
    .of_algebraMap_eq fun _ ↦ rfl
  rw [adjoin_map, Set.image_singleton]
  rfl

lemma restrictScalars_map_top_of_le (hFE : F ≤ E) :
    letI : Algebra F E := (inclusion hFE).toAlgebra
    haveI : IsScalarTower F E Ω := .of_algebraMap_eq fun _ ↦ rfl
    ((⊤ : IntermediateField F E).map (IsScalarTower.toAlgHom F E Ω)).restrictScalars K = E := by
  let a : Algebra F E :=
    (inclusion hFE).toAlgebra
  have hs : IsScalarTower F E Ω :=
    .of_algebraMap_eq fun _ ↦ rfl
  ext x
  exact ⟨by rintro ⟨z, -, rfl⟩; exact z.2, fun hx ↦ ⟨⟨x, hx⟩, IntermediateField.mem_top, rfl⟩⟩

lemma eq_restrictScalars_adjoin_of_adjoin_eq_top (hFE : F ≤ E) (y : E)
    (hgen : letI : Algebra F E := (inclusion hFE).toAlgebra
      F⟮y⟯ = ⊤) : E = (IntermediateField.adjoin F {(y : Ω)}).restrictScalars K := by
  rw [← map_adjoin_of_le hFE y, hgen, restrictScalars_map_top_of_le hFE]

lemma adjoin_eq_top_of_eq_restrictScalars (hFE : F ≤ E) {y : E}
    (hE : E = (IntermediateField.adjoin F {(y : Ω)}).restrictScalars K) :
    letI : Algebra F E := (inclusion hFE).toAlgebra
    F⟮y⟯ = ⊤ := by
  let a : Algebra F E :=
    (inclusion hFE).toAlgebra
  have hs : IsScalarTower F E Ω :=
    .of_algebraMap_eq fun _ ↦ rfl
  refine map_injective (IsScalarTower.toAlgHom F E Ω) <| restrictScalars_injective K ?_
  rw [map_adjoin_of_le hFE y, ← hE, restrictScalars_map_top_of_le hFE]

end Adjoin

variable [IsLocalRing R] in
lemma MongeChoice.isUnit_of_mem_reps (C : I.MongeChoice (maximalIdeal R)) {r : R} (hr : r ∈ C.reps)
    (hr₀ : r ≠ 0) : IsUnit r := by
  by_contra hu
  rcases C.existsUnique_mem_reps 0 with ⟨t, -, ht⟩
  have h₁ : (0 : R) = t :=
    ht 0 ⟨C.zero_mem_reps, map_zero _⟩
  have h₂ : r = t :=
    ht r ⟨hr, by
      rw [Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem]
      exact hu⟩
  exact hr₀ (h₂.trans h₁.symm)

section Concrete

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] (F E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K F]
  [IsGalois K F] [FiniteDimensional K E]

/-- **Monge's theorem inside `K̄`** (Monge, arXiv:1109.4617, first statement of Theorem 1, with
Proposition 3 and Remark 1; LMFDB `lf.family_polynomial`): let `E` be an extension inside `K̄` with
Herbrand invariant `I`, at the residue characteristic of `K`, and `F ≤ E` the unramified extension
of `K` of degree `f`. Then `E = F(α)` for a root `α` of a semicanonical polynomial over `𝒪[F]`. -/
lemma exists_adjoin_of_isInvariantOf (hp : ringChar 𝓀[K] = p) (hFE : F ≤ E)
    (hfin : Module.finrank K F = I.f)
    (hur : letI : ValuativeRel F := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) F
      letI : TopologicalSpace F := finiteIntermediateFieldTopology K (AlgebraicClosure K) F
      haveI : IsNonarchimedeanLocalField F :=
        finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) F
      haveI : ValuativeExtension K F :=
        finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) F
      IsUnramified K F) (hI : I.IsInvariantOf K E) :
    letI : ValuativeRel F := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) F
    letI : Algebra 𝒪[F] (AlgebraicClosure K) :=
      ((algebraMap F (AlgebraicClosure K)).comp (algebraMap 𝒪[F] F)).toAlgebra
    ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ C : I.MongeChoice 𝓂[F], ∃ α : AlgebraicClosure K,
      E = (IntermediateField.adjoin F {α}).restrictScalars K ∧
        (I.mongeSemicanonicalPolynomials ϖ
          (⟨α, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin 𝒪[F] {α}) C).Nonempty := by
  subst hp
  let vF : ValuativeRel F :=
    finiteIntermediateFieldValuativeRel K _ F
  let tF : TopologicalSpace F :=
    finiteIntermediateFieldTopology K _ F
  have hF : IsNonarchimedeanLocalField F :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ F
  have hKF : ValuativeExtension K F :=
    finiteIntermediateField_valuativeExtension K _ F
  have hur' : IsUnramified K F :=
    hur
  let vE : ValuativeRel E :=
    finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E :=
    finiteIntermediateFieldTopology K _ E
  have hE : IsNonarchimedeanLocalField E :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E :=
    finiteIntermediateField_valuativeExtension K _ E
  let vM : ValuativeRel (galoisClosure K E) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (galoisClosure K E) :=
    finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hEM : E ≤ galoisClosure K E :=
    galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
  let aFE : Algebra F E :=
    (inclusion hFE).toAlgebra
  let aFM : Algebra F (galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).toAlgebra
  let aEM : Algebra E (galoisClosure K E) :=
    (inclusion hEM).toAlgebra
  have sFE : IsScalarTower K F E :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sFM : IsScalarTower K F (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sEM : IsScalarTower K E (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sFEM : IsScalarTower F E (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have vFE : ValuativeExtension F E :=
    (inclusion hFE).valuativeExtension
  have vFM : ValuativeExtension F (galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).valuativeExtension
  have vEM : ValuativeExtension E (galoisClosure K E) :=
    (inclusion hEM).valuativeExtension
  have fFM : Module.Finite F (galoisClosure K E) :=
    .of_restrictScalars_finite K F _
  have fEM : Module.Finite E (galoisClosure K E) :=
    .of_restrictScalars_finite K E _
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hs : I.HasSameRams (herbrandInvariantOfTower K (galoisClosure K E) E) := by
    rw [← visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
    exact hasSameRams_of_isInvariantOf hI (isInvariantOf_visibleHerbrandInvariant E)
  have hf : inertiaDegree K E = Module.finrank K F :=
    hI.1.trans hfin.symm
  intro ϖ hϖ C
  rcases exists_root_of_hasSameRams K E (galoisClosure K E) hs hf hϖ C with ⟨y, hgen, q, hq⟩
  let aOK : Algebra 𝒪[F] (AlgebraicClosure K) :=
    ((algebraMap F (AlgebraicClosure K)).comp (algebraMap 𝒪[F] F)).toAlgebra
  let φ : 𝒪[E] →ₐ[𝒪[F]] AlgebraicClosure K :=
    { (algebraMap E (AlgebraicClosure K)).comp (algebraMap 𝒪[E] E) with
      commutes' := fun r ↦ by
        have h₁ : ((algebraMap 𝒪[F] 𝒪[E] r : 𝒪[E]) : E) = algebraMap F E (r : F) :=
          coe_algebraMap_integerRing r
        exact congrArg (algebraMap E (AlgebraicClosure K)) h₁ }
  have hφ : Function.Injective φ := fun a b hab ↦
    Subtype.ext ((algebraMap E (AlgebraicClosure K)).injective hab)
  have hEis : q.IsEisensteinAt 𝓂[F] :=
    isEisensteinAt_of_mem_mongeSemicanonicalPolynomials hϖ hq
  have hroot : (q.map (algebraMap 𝒪[F] 𝒪[E])).IsRoot y := by
    rw [IsRoot, eval_map, ← aeval_def]
    exact hq.1
  rcases exists_algEquiv_adjoin φ hφ
    (algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top hEis hroot hgen) with ⟨e, he⟩
  refine ⟨φ y, eq_restrictScalars_adjoin_of_adjoin_eq_top hFE (y : E) hgen, q, ?_⟩
  rw [← he, mongeSemicanonicalPolynomials_algEquiv]
  exact hq

/-- **The Herbrand invariants of the extensions in a family are admissible**: if `E` is an extension
inside `K̄` with Herbrand invariant `I`, at the residue characteristic of `K`, and `F ≤ E` is the
unramified extension of `K` of degree `f`, then `I` is admissible for `v_F(p)`. -/
lemma isAdmissible_of_isInvariantOf (hp : ringChar 𝓀[K] = p) (hFE : F ≤ E)
    (hfin : Module.finrank K F = I.f)
    (hur : letI : ValuativeRel F := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) F
      letI : TopologicalSpace F := finiteIntermediateFieldTopology K (AlgebraicClosure K) F
      haveI : IsNonarchimedeanLocalField F :=
        finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) F
      haveI : ValuativeExtension K F :=
        finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) F
      IsUnramified K F) (hI : I.IsInvariantOf K E) :
    letI : ValuativeRel F := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) F
    letI : TopologicalSpace F := finiteIntermediateFieldTopology K (AlgebraicClosure K) F
    haveI : IsNonarchimedeanLocalField F :=
      finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) F
    ∀ {e₀ : ℕ}, addVal 𝒪[F] (p : 𝒪[F]) = e₀ → I.IsAdmissible e₀ := by
  subst hp
  let vF : ValuativeRel F :=
    finiteIntermediateFieldValuativeRel K _ F
  let tF : TopologicalSpace F :=
    finiteIntermediateFieldTopology K _ F
  have hF : IsNonarchimedeanLocalField F :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ F
  have hKF : ValuativeExtension K F :=
    finiteIntermediateField_valuativeExtension K _ F
  have hur' : IsUnramified K F :=
    hur
  let vE : ValuativeRel E :=
    finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E :=
    finiteIntermediateFieldTopology K _ E
  have hE : IsNonarchimedeanLocalField E :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E :=
    finiteIntermediateField_valuativeExtension K _ E
  let vM : ValuativeRel (galoisClosure K E) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (galoisClosure K E) :=
    finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hEM : E ≤ galoisClosure K E :=
    galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
  let aFE : Algebra F E :=
    (inclusion hFE).toAlgebra
  let aFM : Algebra F (galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).toAlgebra
  let aEM : Algebra E (galoisClosure K E) :=
    (inclusion hEM).toAlgebra
  have sFE : IsScalarTower K F E :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sFM : IsScalarTower K F (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sEM : IsScalarTower K E (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sFEM : IsScalarTower F E (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have vFE : ValuativeExtension F E :=
    (inclusion hFE).valuativeExtension
  have vFM : ValuativeExtension F (galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).valuativeExtension
  have vEM : ValuativeExtension E (galoisClosure K E) :=
    (inclusion hEM).valuativeExtension
  have fFM : Module.Finite F (galoisClosure K E) :=
    .of_restrictScalars_finite K F _
  have fEM : Module.Finite E (galoisClosure K E) :=
    .of_restrictScalars_finite K E _
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hs : I.HasSameRams (herbrandInvariantOfTower K (galoisClosure K E) E) := by
    rw [← visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
    exact hasSameRams_of_isInvariantOf hI (isInvariantOf_visibleHerbrandInvariant E)
  intro e₀ he₀
  exact isAdmissible_of_hasSameRams K F E (galoisClosure K E) hs (hI.1.trans hfin.symm) he₀

/-- **The converse of Monge's theorem inside `K̄`** (Monge, arXiv:1109.4617, §2.2; LMFDB
`lf.family_polynomial`): let `I` be admissible for `v_F(p)`, for `F` the unramified extension of `K`
of degree `f`, and `α` a root of a semicanonical polynomial over `𝒪[F]`. Then `E = F(α)` has
Herbrand invariant `I`. -/
lemma isInvariantOf_of_mem_mongeSemicanonicalPolynomials (hp : ringChar 𝓀[K] = p)
    (hfin : Module.finrank K F = I.f)
    (hur : letI : ValuativeRel F := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) F
      letI : TopologicalSpace F := finiteIntermediateFieldTopology K (AlgebraicClosure K) F
      haveI : IsNonarchimedeanLocalField F :=
        finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) F
      haveI : ValuativeExtension K F :=
        finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) F
      IsUnramified K F) :
    letI : ValuativeRel F := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) F
    letI : Algebra 𝒪[F] (AlgebraicClosure K) :=
      ((algebraMap F (AlgebraicClosure K)).comp (algebraMap 𝒪[F] F)).toAlgebra
    letI : TopologicalSpace F := finiteIntermediateFieldTopology K (AlgebraicClosure K) F
    haveI : IsNonarchimedeanLocalField F :=
      finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) F
    ∀ {e₀ : ℕ}, addVal 𝒪[F] (p : 𝒪[F]) = e₀ → I.IsAdmissible e₀ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (C : I.MongeChoice 𝓂[F]) (α : AlgebraicClosure K),
        E = (IntermediateField.adjoin F {α}).restrictScalars K →
        (I.mongeSemicanonicalPolynomials ϖ
          (⟨α, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin 𝒪[F] {α}) C).Nonempty →
        I.IsInvariantOf K E := by
  subst hp
  let vF : ValuativeRel F :=
    finiteIntermediateFieldValuativeRel K _ F
  let tF : TopologicalSpace F :=
    finiteIntermediateFieldTopology K _ F
  have hF : IsNonarchimedeanLocalField F :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ F
  have hKF : ValuativeExtension K F :=
    finiteIntermediateField_valuativeExtension K _ F
  have hur' : IsUnramified K F :=
    hur
  let aOK : Algebra 𝒪[F] (AlgebraicClosure K) :=
    ((algebraMap F (AlgebraicClosure K)).comp (algebraMap 𝒪[F] F)).toAlgebra
  intro e₀ he₀ hadm ϖ hϖ C α hE hq
  rcases hq with ⟨q, hq₀, f, hf, rfl⟩
  have hfact : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hFE : F ≤ E := by
    intro x hx
    rw [hE]
    exact IntermediateField.algebraMap_mem _ (⟨x, hx⟩ : F)
  have hαE : α ∈ E := by
    rw [hE]
    exact IntermediateField.mem_adjoin_simple_self F α
  let vE : ValuativeRel E :=
    finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E :=
    finiteIntermediateFieldTopology K _ E
  have hE' : IsNonarchimedeanLocalField E :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E :=
    finiteIntermediateField_valuativeExtension K _ E
  let vM : ValuativeRel (galoisClosure K E) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (galoisClosure K E) :=
    finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hEM : E ≤ galoisClosure K E :=
    galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
  let aFE : Algebra F E :=
    (inclusion hFE).toAlgebra
  let aFM : Algebra F (galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).toAlgebra
  let aEM : Algebra E (galoisClosure K E) :=
    (inclusion hEM).toAlgebra
  have sFE : IsScalarTower K F E :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sFM : IsScalarTower K F (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sEM : IsScalarTower K E (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have sFEM : IsScalarTower F E (galoisClosure K E) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have vFE : ValuativeExtension F E :=
    (inclusion hFE).valuativeExtension
  have vFM : ValuativeExtension F (galoisClosure K E) :=
    (inclusion (hFE.trans hEM)).valuativeExtension
  have vEM : ValuativeExtension E (galoisClosure K E) :=
    (inclusion hEM).valuativeExtension
  have fFM : Module.Finite F (galoisClosure K E) :=
    .of_restrictScalars_finite K F _
  have fEM : Module.Finite E (galoisClosure K E) :=
    .of_restrictScalars_finite K E _
  have hcL : CharP 𝓀[E] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[E]).injective _
  rw [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe] at hq₀
  have halg : Algebra.IsAlgebraic F E :=
    .tower_top (K := K) F
  have hmem : (⟨α, hαE⟩ : E) ∈ 𝒪[E] := by
    rw [integerRing_eq_integralClosure F E, Subalgebra.mem_toSubring, mem_integralClosure_iff]
    refine ⟨I.specialisation ϖ f, monic_specialisation ϖ f, ?_⟩
    refine (algebraMap E (AlgebraicClosure K)).injective ?_
    rw [hom_eval₂, map_zero]
    exact hq₀
  have hgen : F⟮((⟨⟨α, hαE⟩, hmem⟩ : 𝒪[E]) : E)⟯ = ⊤ :=
    adjoin_eq_top_of_eq_restrictScalars hFE hE
  let φ : 𝒪[E] →ₐ[𝒪[F]] AlgebraicClosure K :=
    { (algebraMap E (AlgebraicClosure K)).comp (algebraMap 𝒪[E] E) with
      commutes' := fun r ↦ by
        have h₁ : ((algebraMap 𝒪[F] 𝒪[E] r : 𝒪[E]) : E) = algebraMap F E (r : F) :=
          coe_algebraMap_integerRing r
        exact congrArg (algebraMap E (AlgebraicClosure K)) h₁ }
  have hφ : Function.Injective φ := fun a b hab ↦
    Subtype.ext ((algebraMap E (AlgebraicClosure K)).injective hab)
  have hroot : ((I.specialisation ϖ f).map (algebraMap 𝒪[F] 𝒪[E])).IsRoot ⟨⟨α, hαE⟩, hmem⟩ := by
    rw [IsRoot, eval_map, ← aeval_def]
    refine hφ ?_
    rw [map_zero, ← aeval_algHom_apply]
    exact hq₀
  have hf₀ : f 0 ∉ 𝓂[F] :=
    SemicanonicalChoice.notMem_of_mem_unitReps _
      (SemicanonicalChoice.coeffSet_zero (C.toSemicanonicalChoice _) ▸
        hf 0 I.zero_mem_genericIndices)
  have hA : ∀ σ ∈ I.genericIndices, I.pointType σ = .A → IsUnit (f σ) := fun σ hσ hT ↦ by
    specialize hf σ hσ
    simp only [SemicanonicalChoice.coeffSet, hT] at hf
    exact C.isUnit_of_mem_reps hf.1 hf.2
  have hs : I.HasSameRams (visibleHerbrandInvariant E) := by
    rw [visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
    exact hasSameRams_of_specialisation K E (galoisClosure K E) rfl hadm he₀ hϖ hA hf₀ hroot hgen
  have hdeg : inertiaDegree K E = I.f := by
    rw [IsUnramified.inertiaDegree_tower_eq K F E, hfin,
      inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top (I.specialisation ϖ f)
        (isEisensteinAt_specialisation hϖ hf₀) _ hroot hgen, mul_one]
  exact IsInvariantOf.of_hasSameRams (isInvariantOf_visibleHerbrandInvariant E) hs hdeg.symm

end Concrete

variable (I) (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

/-- **Monge's representation theorem** (Monge, arXiv:1109.4617, the first statement of Theorem 1,
with Proposition 3 and Remark 1, and §2.2 for the converse; LMFDB `lf.family_polynomial`). If `K`
has residue characteristic `p` and `I / K` is not empty, then for every uniformiser `ϖ` of the
unramified extension `K_f` of `K` of degree `f` and all choices `C` of representatives, the
extensions in the family `I / K` are, up to `K`-isomorphism, exactly the fields `K_f(α)` for the
roots `α ∈ K̄` of the semicanonical polynomials over `𝒪_{K_f}`. The second statement of Monge's
Theorem 1, the number `B_{L/K} / #Aut(L / K)` of reduced polynomials generating `L`, is not proved,
nor is the bound on the number of semicanonical polynomials of an extension by the ambiguity (LMFDB
`lf.family_ambiguity`). -/
lemma mongeRepresentation : I.MongeRepresentation K := by
  let vF : ValuativeRel (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tF : TopologicalSpace (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateFieldTopology K _ _
  have hF : IsNonarchimedeanLocalField (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKF : ValuativeExtension K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hf₀ : I.f ≠ 0 :=
    I.f_pos.ne'
  have hfin : Module.finrank K (unramifiedExtension K (AlgebraicClosure K) I.f) = I.f :=
    finrank_unramifiedExtension hf₀
  have hur : IsUnramified K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    isUnramified_unramifiedExtension hf₀
  intro hp hne ϖ hϖ C c
  refine ⟨?_, ?_⟩
  · rintro ⟨E, hE, rfl⟩
    have hfd : FiniteDimensional K E.1 :=
      E.2
    rcases exists_adjoin_of_isInvariantOf _ E.1 hp (unramifiedExtension_le_of_isInvariantOf hE) hfin
      hur hE ϖ hϖ C with ⟨α, hα, hq⟩
    exact ⟨α, E, hα, rfl, hq⟩
  · rintro ⟨α, E, hE, rfl, hq⟩
    have hfd : FiniteDimensional K E.1 :=
      E.2
    rcases hne with ⟨-, E₀, hE₀, -⟩
    have hfd₀ : FiniteDimensional K E₀.1 :=
      E₀.2
    have hpp : p ≠ 0 :=
      hp ▸ (CharP.prime_ringChar 𝓀[K]).ne_zero
    rcases exists_addVal_natCast_eq K (unramifiedExtension K (AlgebraicClosure K) I.f) hpp with
      ⟨e₀, he₀⟩
    exact ⟨E, isInvariantOf_of_mem_mongeSemicanonicalPolynomials _ E.1 hp hfin hur he₀
      (isAdmissible_of_isInvariantOf _ E₀.1 hp (unramifiedExtension_le_of_isInvariantOf hE₀) hfin
        hur hE₀ he₀) ϖ hϖ C α hE hq, rfl⟩

end IsNonarchimedeanLocalField.HerbrandInvariant
