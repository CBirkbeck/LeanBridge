import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeReductionLoop
import TauCeti.NumberTheory.LocalField.Herbrand.Unramified

/-!
# The comparison of the invariants of an extension over `K` and over `K_f`

Monge's reduction (arXiv:1109.4617) takes place over the unramified extension `K_f` of `K` of degree
`f`, and the family of a Herbrand invariant `I` is defined through its invariants over `K`. This
file compares the two: for an unramified extension `F / K`, and a tower `M / L / F` with `M / K`
finite Galois, the ramification groups `G_j` of `M / F` and `M / K` are the same for `j ≥ 0`, so
`L / F` and `L / K` have the same rams, and the same `w` and `ε`. Only the residue degrees of the
invariants differ.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.HasSameRams`: two Herbrand invariants have the same
  prime, `w`, `ε` and rams.

## Main results

* `IsNonarchimedeanLocalField.ramsOfSubgroup_eq_ramsOfSubgroup`: the rams over `K` and over `K_f`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.hasSameRams_herbrandInvariantOfTower`: the
  comparison of the invariants over `K_f` and over `K`.
-/

open Finset IntermediateField IsDiscreteValuationRing IsLocalRing Polynomial TauCeti ValuativeRel
  LocalFieldsRamification

namespace IsNonarchimedeanLocalField

variable (K F L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Algebra K F] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsGalois K M] [Algebra F M] [ValuativeExtension F M] [Module.Finite F M] [IsScalarTower K F M]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [Algebra F L] [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [IsScalarTower K L M] [IsScalarTower F L M]

lemma herbrandOfSubgroup_eq (i : ℕ) :
    herbrandOfSubgroup F M (AlgEquiv.restrictScalarsHom (S := L) F).range i =
      herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range i := by
  have hF : IsGalois F M :=
    IsGalois.tower_top_of_isGalois K F M
  refine Rat.cast_injective (α := ℝ) ?_
  rw [herbrandOfSubgroup_range_restrictScalarsHom F M i L,
    herbrandOfSubgroup_range_restrictScalarsHom K M i L]

variable [ValuativeExtension K F] [Module.Finite K F] [IsGalois K F] [IsUnramified K F] {j : ℤ}

lemma lowerRamificationGroup_le_range (hj : 0 ≤ j) :
    lowerRamificationGroup K M j ≤ (AlgEquiv.restrictScalarsHom (S := F) K).range := by
  intro σ hσ
  have h₀ : σ ∈ upperRamificationGroup K M ⟨0, by norm_num⟩ := by
    rw [upperRamificationGroup_of_coe_le_zero K M le_rfl, lowerRamificationGroupReal_def,
      Int.ceil_zero]
    exact lowerRamificationGroup_antitone K M hj hσ
  have h₁ : AlgEquiv.restrictNormalHom F σ ∈
      (upperRamificationGroup K M ⟨0, by norm_num⟩).map (AlgEquiv.restrictNormalHom F) :=
    Subgroup.mem_map_of_mem _ h₀
  rw [map_restrictNormalHom_upperRamificationGroup K F M,
    upperRamificationGroup_eq_bot_of_isUnramified K F le_rfl, Subgroup.mem_bot] at h₁
  rw [AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K F M, MonoidHom.mem_ker]
  exact h₁

lemma natCard_lowerRamificationGroup_eq (hj : 0 ≤ j) :
    Nat.card (lowerRamificationGroup F M j) = Nat.card (lowerRamificationGroup K M j) := by
  have h : (lowerRamificationGroup F M j).map (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup K M j := by
    rw [map_restrictScalarsHom_lowerRamificationGroup K M F j,
      inf_eq_right.mpr (lowerRamificationGroup_le_range K F M hj)]
  rw [← h, Subgroup.card_map_of_injective (AlgEquiv.restrictScalars_injective K)]

lemma largestLowerJump_eq : largestLowerJump F M = largestLowerJump K M := by
  rw [largestLowerJump, largestLowerJump]
  congr 3
  ext n
  simp only [Set.mem_ofPred_eq, ← Subgroup.card_eq_one,
    natCard_lowerRamificationGroup_eq K F M (Int.natCast_nonneg n)]

lemma relIndex_lowerRamificationGroup_eq (hj : 0 ≤ j) :
    (AlgEquiv.restrictScalarsHom (S := L) F).range.relIndex (lowerRamificationGroup F M j) =
      (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex (lowerRamificationGroup K M j) := by
  have h₁ : (AlgEquiv.restrictScalarsHom (S := L) F).range.relIndex (lowerRamificationGroup F M j) *
      Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) F).range ⊓ lowerRamificationGroup F M j) =
        Nat.card (lowerRamificationGroup F M j) :=
    Subgroup.relIndex_mul_card _ _
  have h₂ : (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex (lowerRamificationGroup K M j) *
      Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K).range ⊓ lowerRamificationGroup K M j) =
        Nat.card (lowerRamificationGroup K M j) :=
    Subgroup.relIndex_mul_card _ _
  rw [← map_restrictScalarsHom_lowerRamificationGroup F M L,
    Subgroup.card_map_of_injective (AlgEquiv.restrictScalars_injective F),
    natCard_lowerRamificationGroup_eq K F M hj] at h₁
  rw [← map_restrictScalarsHom_lowerRamificationGroup K M L,
    Subgroup.card_map_of_injective (AlgEquiv.restrictScalars_injective K)] at h₂
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h₁.trans h₂.symm)

/-- **The rams over `K` and over `K_f`**: for an unramified extension `F / K` and a tower
`M / L / F` with `M / K` finite Galois, the rams of `L / F` and of `L / K` are the same. The
ramification groups of `M / F` at indices `j ≥ 0` are those of `M / K`, since these fix `F`. -/
lemma ramsOfSubgroup_eq_ramsOfSubgroup :
    ramsOfSubgroup F M (AlgEquiv.restrictScalarsHom (S := L) F).range =
      ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range := by
  rw [ramsOfSubgroup, ramsOfSubgroup, largestLowerJump_eq K F M, ← Algebra.ringChar_eq 𝓀[K] 𝓀[F]]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [relIndex_lowerRamificationGroup_eq K F L M (by omega),
    relIndex_lowerRamificationGroup_eq K F L M (by omega), herbrandOfSubgroup_eq K F L M]

namespace HerbrandInvariant

/-- Two Herbrand invariants **have the same rams** if they are at the same prime and have the same
`w`, `ε` and rams, so that they can only differ in their residue degrees. The Herbrand invariants of
`L / K` and of `L / K_f` are such (`hasSameRams_herbrandInvariantOfTower`). -/
structure HasSameRams {p p' : ℕ} (I : HerbrandInvariant p) (J : HerbrandInvariant p') : Prop where
  prime_eq : p = p'
  w_eq : I.w = J.w
  ε_eq : I.ε = J.ε
  ram_eq : I.ram = J.ram

variable {p p' p'' : ℕ} {I : HerbrandInvariant p} {J : HerbrandInvariant p'}
  {J' : HerbrandInvariant p''}

variable (I) in
lemma HasSameRams.refl : I.HasSameRams I :=
  ⟨rfl, rfl, rfl, rfl⟩

lemma HasSameRams.symm (h : I.HasSameRams J) : J.HasSameRams I :=
  ⟨h.prime_eq.symm, h.w_eq.symm, h.ε_eq.symm, h.ram_eq.symm⟩

lemma HasSameRams.trans (h : I.HasSameRams J) (h' : J.HasSameRams J') : I.HasSameRams J' :=
  ⟨h.prime_eq.trans h'.prime_eq, h.w_eq.trans h'.w_eq, h.ε_eq.trans h'.ε_eq,
    h.ram_eq.trans h'.ram_eq⟩

lemma HasSameRams.ramificationIndex_eq (h : I.HasSameRams J) :
    I.ramificationIndex = J.ramificationIndex := by
  rcases h with ⟨rfl, hw, hε, -⟩
  rw [ramificationIndex, ramificationIndex, hw, hε]

lemma HasSameRams.swanSlope_eq (h : I.HasSameRams J) (k : ℕ) : I.swanSlope k = J.swanSlope k := by
  rcases h with ⟨rfl, -, hε, hram⟩
  simp only [swanSlope, hε, hram]

lemma HasSameRams.mean_eq (h : I.HasSameRams J) (k : ℕ) : I.mean k = J.mean k := by
  rcases h with ⟨rfl, -, hε, hram⟩
  simp only [mean, hε, hram]

lemma HasSameRams.isRamificationPolygon {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Algebra R S] {g : R[X]} {π : S} (h : I.HasSameRams J)
    (hJ : J.IsRamificationPolygon g π) : I.IsRamificationPolygon g π := by
  refine ⟨by rw [h.ramificationIndex_eq]; exact hJ.natDegree_eq, fun {k r v} hk hr hv ↦ ?_,
    fun {k} hk hv ↦ ?_⟩
  · rw [h.ramificationIndex_eq, h.swanSlope_eq, h.ram_eq]
    exact hJ.le_addVal (h.w_eq ▸ hk) hr hv
  · have hv' : J.IsVertex k := by
      rw [IsVertex, ← h.w_eq, ← h.ram_eq]
      exact hv
    rcases h with ⟨rfl, hw, hε, hram⟩
    have h' : I.HasSameRams J :=
      ⟨rfl, hw, hε, hram⟩
    rw [h'.ramificationIndex_eq, h'.mean_eq, hw]
    exact hJ.exists_addVal_eq (hw ▸ hk) hv'

variable [ValuativeExtension K L] [ValuativeExtension F L] [IsScalarTower K F L] in
/-- **The comparison of the invariants over `K_f` and over `K`**: for an unramified extension
`F / K`, and a tower `M / L / F` with `M / K` finite Galois, the Herbrand invariants of `L / F` and
of `L / K` have the same rams; only the residue degrees differ. -/
lemma hasSameRams_herbrandInvariantOfTower :
    (herbrandInvariantOfTower F M L).HasSameRams (herbrandInvariantOfTower K M L) := by
  have hF : IsGalois F M :=
    IsGalois.tower_top_of_isGalois K F M
  have hR : ramsOfSubgroup F M (AlgEquiv.restrictScalarsHom (S := L) F).range =
      ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range :=
    ramsOfSubgroup_eq_ramsOfSubgroup K F L M
  have hε : (herbrandInvariantOfTower F M L).ε =
      ordCompl[ringChar 𝓀[F]] (TauCeti.ramificationIndex F L) :=
    rfl
  have hε' : (herbrandInvariantOfTower K M L).ε =
      ordCompl[ringChar 𝓀[K]] (TauCeti.ramificationIndex K L) :=
    rfl
  have hram : ∀ {R R' : Multiset ℚ} (h : R = R') (hR : ∀ r ∈ R, 0 < r) (hR' : ∀ r ∈ R', 0 < r)
      (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) (e e' f f' : ℕ) (he : e ≠ 0) (he' : e' ≠ 0)
      (hf : 0 < f) (hf' : 0 < f'), (ofRams q hq R hR e f he hf).ram =
        (ofRams q' hq' R' hR' e' f' he' hf').ram := by
    intro R R' h
    subst h
    intros
    rfl
  refine ⟨(Algebra.ringChar_eq 𝓀[K] 𝓀[F]).symm, congrArg Multiset.card hR, ?_,
    hram hR _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  rw [hε, hε', ← Algebra.ringChar_eq 𝓀[K] 𝓀[F], IsUnramified.ramificationIndex_tower_eq K F L]

end HerbrandInvariant

end IsNonarchimedeanLocalField
