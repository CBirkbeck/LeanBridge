import LeanBridge.ForMathlib.NumberTheory.LocalField.GaloisMeanSlope
import LeanBridge.ForMathlib.NumberTheory.LocalField.HerbrandInvariantRams
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolygon
import TauCeti.NumberTheory.LocalField.Different.Tower

/-!
# The discriminant exponent of an extension of local fields from its rams

Let `L / K` be a finite separable extension of nonarchimedean local fields of residue
characteristic `p`, which need not be Galois, with ramification index `e = ε p ^ w`, residue degree
`f` and Herbrand invariant `(r_1, …, r_w)_ε^f`, whose means are
`m_k = ∑_{j ≤ k} (p - 1) r_j / (ε p ^ j)`. Its different exponent is `d(L / K) = e - 1 + e m_w`
and its discriminant exponent is `c = f (e - 1 + e m_w)`: so the last mean `m_w` is the mean `m` of
`L / K` that LMFDB `lf.means` defines by `c = f (e - 1 + e m)`, and the discriminant exponent is
determined by the Herbrand invariant, as LMFDB `lf.family_invariants` states for the extensions in
a family `I / K`. For `L / K` Galois this is Hilbert's formula `d = ∑_{i ≥ 0} (#G_i - 1)`.

The proof computes in a finite Galois extension `M ⊇ L` of `K`, with group `G`, lower ramification
groups `G_i` and `H = Gal(M / L)`, whose lower ramification groups are the `H_i = H ∩ G_i`.
Hilbert's formula for `M / K` and `M / L` (Tau Ceti) and the tower formula for differents give
`#H_0 · d(L / K) = ∑_{i ≥ 0} (#G_i - #H_i)`. Up to an index `t` beyond the ramification breaks of
`M / K`, the partial sums are `#G_0 (1 + φ_{M/K}(t))` and `#H_0 (1 + φ_{M/L}(t))`, and the Herbrand
function of the Herbrand invariant takes the value `φ_{M/K}(t)` at `φ_{M/L}(t) ≥ r_w`, where it is
`s_w + (φ_{M/L}(t) - r_w) / e`. As `#G_0 = e #H_0` and `e s_w - r_w = e m_w`, this gives
`d(L / K) = e - 1 + e m_w`, and `c = f d(L / K)`.

## Main results

* `IsNonarchimedeanLocalField.natCast_differentExponent_herbrandInvariantOfTower`: the different
  exponent `d(L / K) = e - 1 + e m_w`, computed in a finite Galois extension `M ⊇ L`.
* `IsNonarchimedeanLocalField.natCast_discriminantExponent_herbrandInvariantOfTower` (LMFDB
  `lf.family_invariants`, `lf.means`): the discriminant exponent `c = f (e - 1 + e m_w)`.
* `IsNonarchimedeanLocalField.natCast_discriminantExponent_visibleHerbrandInvariant` (LMFDB
  `lf.family_invariants`, `lf.means`): the same for an extension inside `K̄`, with its Herbrand
  invariant `IsNonarchimedeanLocalField.visibleHerbrandInvariant`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §4, and Chapter IV, §1, Proposition 4.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  appendix.
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

namespace IsNonarchimedeanLocalField

variable (K M L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
  [Algebra L M] [IsScalarTower K L M] [ValuativeExtension L M] [Module.Finite L M] [IsGalois K M]
  [ValuativeExtension K L]

variable {K M} in
lemma natCast_differentExponent_eq_sum_range {N : ℕ}
    (hN : ∀ i, N ≤ i → Nat.card (lowerRamificationGroup K M i) = 1) : (differentExponent K M : ℝ) =
      ∑ i ∈ range N, ((Nat.card (lowerRamificationGroup K M i) : ℝ) - 1) := by
  have hsupp :
      (Function.support fun i : ℕ ↦ Nat.card (lowerRamificationGroup K M i) - 1) ⊆ ↑(range N) :=
    Function.support_subset_iff'.mpr fun i hi ↦ by
      rw [hN i (by simpa using hi), Nat.sub_self]
  rw [differentExponent_eq_finsum_lowerRamificationGroup, finsum_eq_sum_of_support_subset _ hsupp,
    Nat.cast_sum]
  exact sum_congr rfl fun i _ ↦ by rw [Nat.cast_sub Nat.card_pos, Nat.cast_one]

lemma natCast_differentExponent_herbrandInvariantOfTower_real : (differentExponent K L : ℝ) =
    ramificationIndex K L - 1 + ramificationIndex K L *
      ((herbrandInvariantOfTower K M L).mean (herbrandInvariantOfTower K M L).w : ℝ) := by
  have hL : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  set H : Subgroup (M ≃ₐ[K] M) := (AlgEquiv.restrictScalarsHom (S := L) K).range
  set T : ℕ := (largestLowerJump K M).toNat
  set I : HerbrandInvariant (ringChar 𝓀[K]) := herbrandInvariantOfTower K M L with hI
  have hbot (i : ℕ) (hi : T + 1 ≤ i) : lowerRamificationGroup K M i = ⊥ :=
    lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (by omega)
  have hcard (i : ℤ) :
      Nat.card (lowerRamificationGroup L M i) = Nat.card ↥(H ⊓ lowerRamificationGroup K M i) := by
    rw [← map_restrictScalarsHom_lowerRamificationGroup K M L,
      Subgroup.card_map_of_injective (AlgEquiv.restrictScalars_injective K)]
  have hKM : (differentExponent K M : ℝ) =
      ∑ i ∈ range (T + 1), ((Nat.card (lowerRamificationGroup K M i) : ℝ) - 1) :=
    natCast_differentExponent_eq_sum_range fun i hi ↦ by rw [hbot i hi, Subgroup.card_bot]
  have hLM : (differentExponent L M : ℝ) =
      ∑ i ∈ range (T + 1), ((Nat.card ↥(H ⊓ lowerRamificationGroup K M i) : ℝ) - 1) := by
    rw [natCast_differentExponent_eq_sum_range fun i hi ↦ by
      rw [hcard, hbot i hi, inf_bot_eq, Subgroup.card_bot]]
    exact sum_congr rfl fun i _ ↦ by rw [hcard]
  have htower : (differentExponent K M : ℝ) =
      differentExponent L M + ramificationIndex L M * differentExponent K L := by
    exact_mod_cast differentExponent_tower K L M
  have hrel : H.relIndex (lowerRamificationGroup K M 0) = ramificationIndex K L :=
    relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom K M L
  have hsplit (F : ℕ → ℝ) : ∑ i ∈ range (T + 1), F i = F 0 + ∑ i ∈ Icc 1 T, F i := by
    rw [sum_range_succ', sum_Icc_one_eq_sum_range, add_comm]
  have hsum : (differentExponent K M : ℝ) - differentExponent L M =
      (Nat.card (lowerRamificationGroup K M 0) : ℝ) - Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) +
        (∑ i ∈ Icc 1 T, (Nat.card (lowerRamificationGroup K M i) : ℝ) -
          ∑ i ∈ Icc 1 T, (Nat.card ↥(H ⊓ lowerRamificationGroup K M i) : ℝ)) := by
    rw [hKM, hLM, hsplit, hsplit]
    simp only [sum_sub_distrib, Nat.cast_zero]
    ring1
  have hg0 : (Nat.card (lowerRamificationGroup K M 0) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hh0 : (Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hSg : ∑ i ∈ Icc 1 T, (Nat.card (lowerRamificationGroup K M i) : ℝ) =
      herbrand K M ⟨T, Nat.cast_mem_ramificationIndexDomain T⟩ *
        Nat.card (lowerRamificationGroup K M 0) := by
    rw [coe_herbrand_of_coe_eq_natCast K M T rfl, div_mul_cancel₀ _ hg0]
  have hSh : ∑ i ∈ Icc 1 T, (Nat.card ↥(H ⊓ lowerRamificationGroup K M i) : ℝ) =
      herbrandOfSubgroup K M H T * Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) := by
    rw [herbrandOfSubgroup]
    push_cast
    exact (div_mul_cancel₀ _ hh0).symm
  have hB : (ramificationIndex L M : ℝ) = Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) := by
    rw [← natCard_lowerRamificationGroup_zero L M, hcard]
  have hC : (ramificationIndex K L : ℝ) * Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) =
      Nat.card (lowerRamificationGroup K M 0) := by
    rw [← hrel]
    exact_mod_cast H.relIndex_mul_card _
  have hI' : I = HerbrandInvariant.ofRams (ringChar 𝓀[K]) (CharP.prime_ringChar _)
      (ramsOfSubgroup K M H) (fun _ ↦ pos_of_mem_ramsOfSubgroup K M H)
      (H.relIndex (lowerRamificationGroup K M 0)) (inertiaDegree K L)
      Subgroup.index_ne_zero_of_finite inertiaDegree_pos := by
    rw [hI, herbrandInvariantOfTower]
    congr 1
    exact hrel.symm
  have hkey : I.herbrandFunction (herbrandOfSubgroup K M H T) =
      herbrand K M ⟨T, Nat.cast_mem_ramificationIndexDomain T⟩ := by
    rw [hI']
    exact herbrandFunction_ofRams_herbrandOfSubgroup K M H _ _
  have hle : I.ram I.w ≤ herbrandOfSubgroup K M H T := by
    rcases Nat.eq_zero_or_pos I.w with hw | hw
    · rw [hw, I.ram_zero, ← herbrandOfSubgroup_zero K M H]
      exact (herbrandOfSubgroup_strictMono K M H).monotone T.zero_le
    · have hmem : I.ram I.w ∈ ramsOfSubgroup K M H :=
        HerbrandInvariant.ram_ofRams_mem _ _ _ _ _ _ _ _ hw le_rfl
      rcases Multiset.mem_sum.mp hmem with ⟨i, hi, hr⟩
      rw [Multiset.eq_of_mem_replicate hr]
      exact (herbrandOfSubgroup_strictMono K M H).monotone (mem_range.mp hi)
  have hε : (I.ε : ℝ) * (ringChar 𝓀[K] : ℝ) ^ I.w = ramificationIndex K L := by
    exact_mod_cast ε_mul_pow_w_herbrandInvariantOfTower K M L
  have he : (ramificationIndex K L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ramificationIndex_pos.ne'
  have hE : (herbrand K M ⟨T, Nat.cast_mem_ramificationIndexDomain T⟩ : ℝ) * ramificationIndex K L =
      I.swanSlope I.w * ramificationIndex K L + herbrandOfSubgroup K M H T - I.ram I.w := by
    rw [← hkey, I.herbrandFunction_of_le (Rat.cast_le.mpr hle), hε]
    field_simp
    ring1
  have hF : (I.ram I.w : ℝ) = ramificationIndex K L * (I.swanSlope I.w - I.mean I.w) := by
    have h : I.ram I.w / (I.ε * ringChar 𝓀[K] ^ I.w) = I.swanSlope I.w - I.mean I.w :=
      I.tinyRam_eq_swanSlope_sub_mean (CharP.prime_ringChar 𝓀[K]).ne_zero I.w
    have h' : (I.ram I.w : ℝ) / ramificationIndex K L = I.swanSlope I.w - I.mean I.w := by
      rw [← hε]
      exact_mod_cast h
    rw [← h']
    field_simp
  refine mul_left_cancel₀ hh0 ?_
  linear_combination -htower + hsum + hSg - hSh - (differentExponent K L : ℝ) * hB -
    (1 + (herbrand K M ⟨T, Nat.cast_mem_ramificationIndexDomain T⟩ : ℝ)) * hC +
    (Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) : ℝ) * hE -
    (Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) : ℝ) * hF

/-- **The different exponent of an extension from its rams**: in a tower `M / L / K` of
nonarchimedean local fields with `M / K` finite Galois, the different exponent of `L / K` is
`d(L / K) = e - 1 + e m_w`, for `e = ε p ^ w` the ramification index of `L / K` and `m_w` the last
mean of its Herbrand invariant `(r_1, …, r_w)_ε^f`. For `L / K` Galois this is Hilbert's formula. -/
lemma natCast_differentExponent_herbrandInvariantOfTower : (differentExponent K L : ℚ) =
    ramificationIndex K L - 1 + ramificationIndex K L *
      (herbrandInvariantOfTower K M L).mean (herbrandInvariantOfTower K M L).w := by
  exact_mod_cast natCast_differentExponent_herbrandInvariantOfTower_real K M L

variable [Algebra.IsSeparable K L] in
/-- **The discriminant exponent of an extension from its rams** (LMFDB `lf.family_invariants`,
`lf.means`): in a tower `M / L / K` of nonarchimedean local fields with `M / K` finite Galois, the
discriminant exponent of `L / K` is `c = f (e - 1 + e m_w)`, for `f` the residue degree,
`e = ε p ^ w` the ramification index and `m_w` the last mean of the Herbrand invariant
`(r_1, …, r_w)_ε^f` of `L / K`. So `m_w` is the mean `m` of `L / K` of LMFDB `lf.means`, and `c`
depends only on the Herbrand invariant. -/
lemma natCast_discriminantExponent_herbrandInvariantOfTower : (discriminantExponent K L : ℚ) =
    inertiaDegree K L * (ramificationIndex K L - 1 + ramificationIndex K L *
      (herbrandInvariantOfTower K M L).mean (herbrandInvariantOfTower K M L).w) := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent, Nat.cast_mul,
    natCast_differentExponent_herbrandInvariantOfTower K M L]

variable {K} (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
  [Algebra.IsSeparable K E]

/-- **The discriminant exponent of an extension inside `K̄` from its rams** (LMFDB
`lf.family_invariants`, `lf.means`): a finite separable extension `E` of a nonarchimedean local
field `K` inside `K̄` has discriminant exponent `c = f (e - 1 + e m_w)`, for `f` the residue degree,
`e = ε p ^ w` the ramification index and `m_w` the last mean of its Herbrand invariant
`IsNonarchimedeanLocalField.visibleHerbrandInvariant E`, with Tau Ceti's spectral-norm local-field
structure on `E`. -/
lemma natCast_discriminantExponent_visibleHerbrandInvariant :
    letI : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
    letI : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
    haveI : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
    haveI : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
    (discriminantExponent K E : ℚ) = inertiaDegree K E * (ramificationIndex K E - 1 +
      ramificationIndex K E *
        (visibleHerbrandInvariant E).mean (visibleHerbrandInvariant E).w) := by
  let vE : ValuativeRel E := finiteIntermediateFieldValuativeRel K _ E
  let tE : TopologicalSpace E := finiteIntermediateFieldTopology K _ E
  have hE : IsNonarchimedeanLocalField E := finiteIntermediateField_isNonarchimedeanLocalField K _ E
  have hKE : ValuativeExtension K E := finiteIntermediateField_valuativeExtension K _ E
  let vM : ValuativeRel (Algebra.galoisClosure K E) := finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (Algebra.galoisClosure K E) := finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (Algebra.galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (Algebra.galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hEM : E ≤ Algebra.galoisClosure K E :=
    Algebra.galoisClosure_eq_normalClosure (F := K) E ▸ E.le_normalClosure
  let a : Algebra E (Algebra.galoisClosure K E) := (IntermediateField.inclusion hEM).toAlgebra
  have hs : IsScalarTower K E (Algebra.galoisClosure K E) := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension E (Algebra.galoisClosure K E) :=
    (IntermediateField.inclusion hEM).valuativeExtension
  have hf : Module.Finite E (Algebra.galoisClosure K E) := .of_restrictScalars_finite K E _
  rw [HerbrandInvariant.visibleHerbrandInvariant_eq_herbrandInvariantOfTower E]
  exact natCast_discriminantExponent_herbrandInvariantOfTower K (Algebra.galoisClosure K E) E

end IsNonarchimedeanLocalField
