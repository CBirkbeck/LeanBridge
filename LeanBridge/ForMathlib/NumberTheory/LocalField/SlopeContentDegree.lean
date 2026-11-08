import LeanBridge.ForMathlib.NumberTheory.LocalField.DeligneRamificationBreaks
import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# The degree of the Galois closure from the slope content

Let `L / K` be a finite Galois extension of nonarchimedean local fields of residue characteristic
`p`, with group `G`, ramification index `e`, residue degree `f`, lower ramification groups `G_i`
and upper ramification groups `G^v`. The LMFDB (`lf.slope_content`) writes `G^{(s)} = G^{s - 1}`
and `G^{(s+)} = ⋃_{ε > 0} G^{(s + ε)}`. We show `G^{(0)} = G`, `G^{(1)} = G_0` and
`G^{(1+)} = G_1`, so that `G^{(1)} / G^{(1+)} = G_0 / G_1` is cyclic of order the tame degree `t`
(prime to `p`). Since there are `v_p(e)` wild Artin slopes, `[L : K] = e f = t u p ^ k` for the
Artin slope content `[s_1, …, s_k]_t^u`; applied to the Galois closure of a finite separable
extension this is the LMFDB's `[L^gal : K] = t u p ^ k`.

## Main theorems

* `IsNonarchimedeanLocalField.finrank_galoisClosure_eq` (LMFDB `lf.slope_content`):
  `[L^gal : K] = t u p ^ k`.
* `IsNonarchimedeanLocalField.upperRamificationGroup_neg_one` and
  `IsNonarchimedeanLocalField.upperRamificationGroup_zero` (LMFDB `lf.slope_content`):
  `G^{(0)} = G` and `G^{(1)} = G_0`, the inertia group.
* `IsNonarchimedeanLocalField.iUnion_upperRamificationGroup_pos` (LMFDB `lf.slope_content`):
  `G^{(1+)} = ⋃_{ε > 0} G^ε = G_1`.
* `IsNonarchimedeanLocalField.relIndex_lowerRamificationGroup_one_zero` (LMFDB
  `lf.slope_content`): `[G^{(1)} : G^{(1+)}] = [G_0 : G_1] = t`.
* `IsNonarchimedeanLocalField.isCyclic_quotient_lowerRamificationGroup_one` (LMFDB
  `lf.slope_content`): `G^{(1)} / G^{(1+)} = G_0 / G_1` is cyclic.
-/

open ValuativeRel TauCeti LocalFieldsRamification

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- **`G^{(1)} / G^{(1+)}` is cyclic** (LMFDB `lf.slope_content`): `G_0 / G_1` embeds into the
multiplicative group of the residue field of `L` (Tau Ceti). -/
lemma isCyclic_quotient_lowerRamificationGroup_one : IsCyclic (lowerRamificationGroup K L 0 ⧸
    (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) :=
  isCyclic_ramificationGroupGraded_zero L (L ≃ₐ[K] L)

variable [IsGalois K L]

lemma card_wildArtinSlopesOfIsGalois : Multiset.card (wildArtinSlopesOfIsGalois K L) =
    (ramificationIndex K L).factorization (ringChar 𝓀[K]) := by
  rw [← Multiset.card_map (· - 1), ← swanSlopesOfIsGalois, ← swanSlopesOfSubgroup_bot,
    card_swanSlopesOfSubgroup, Subgroup.relIndex_bot_left, natCard_lowerRamificationGroup_zero]

lemma finrank_eq_tameDegree_mul_inertiaDegree_mul_pow : Module.finrank K L = tameDegree K L *
    inertiaDegree K L * ringChar 𝓀[K] ^ Multiset.card (wildArtinSlopesOfIsGalois K L) := by
  rw [card_wildArtinSlopesOfIsGalois, ← ramificationIndex_mul_inertiaDegree, tameDegree]
  nth_rw 1 [← Nat.ordProj_mul_ordCompl_eq_self (ramificationIndex K L) (ringChar 𝓀[K])]
  ring1

/-- **`G^{(0)} = G`** (LMFDB `lf.slope_content`): the upper ramification group `G^{-1}` is the whole
Galois group. -/
lemma upperRamificationGroup_neg_one : upperRamificationGroup K L ⟨-1, Set.self_mem_Ici⟩ = ⊤ := by
  rw [upperRamificationGroup_of_coe_le_zero K L (by norm_num), lowerRamificationGroupReal_def]
  exact lowerRamificationGroup_eq_top_of_le_neg_one K L (by norm_num)

/-- **`G^{(1)}` is the inertia group** (LMFDB `lf.slope_content`): the upper ramification group
`G^0` is the lower ramification group `G_0`, the inertia group (Tau Ceti's
`TauCeti.LocalFieldsRamification.lowerRamificationGroup_zero`), which is the kernel of the action
on the residue field (Tau Ceti's `TauCeti.ker_residueField_toAlgAut`). -/
lemma upperRamificationGroup_zero :
    upperRamificationGroup K L ⟨0, by norm_num⟩ = lowerRamificationGroup K L 0 := by
  rw [upperRamificationGroup_of_coe_le_zero K L le_rfl, lowerRamificationGroupReal_def]
  simp

/-- **`G^{(1+)} = G_1`** (LMFDB `lf.slope_content`): the union `⋃_{ε > 0} G^ε` of the upper
ramification groups at positive indices is the wild inertia group `G_1`. -/
lemma iUnion_upperRamificationGroup_pos : ⋃ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
    (upperRamificationGroup K L v : Set (L ≃ₐ[K] L)) = lowerRamificationGroup K L 1 := by
  refine subset_antisymm (Set.iUnion₂_subset fun v hv ↦ ?_) fun σ hσ ↦ ?_
  · have hψ : (0 : ℝ) < inverseHerbrand K L v := by
      have h : inverseHerbrand K L ⟨0, by norm_num⟩ < inverseHerbrand K L v :=
        inverseHerbrand_strictMono K L (Subtype.mk_lt_mk.mpr hv)
      rwa [inverseHerbrand_of_coe_le_zero K L le_rfl] at h
    rw [upperRamificationGroup_def, lowerRamificationGroupReal_def]
    exact lowerRamificationGroup_antitone K L (Int.one_le_ceil_iff.mpr hψ)
  · have hpos : (0 : ℝ) < herbrand K L ⟨(1 : ℕ), Nat.cast_mem_ramificationIndexDomain 1⟩ := by
      have h : herbrand K L ⟨0, by norm_num⟩ <
          herbrand K L ⟨(1 : ℕ), Nat.cast_mem_ramificationIndexDomain 1⟩ :=
        herbrand_strictMono K L (Subtype.mk_lt_mk.mpr (by norm_num))
      rwa [herbrand_of_coe_le_zero K L le_rfl] at h
    refine Set.mem_iUnion₂.mpr ⟨_, hpos, ?_⟩
    rw [SetLike.mem_coe, upperRamificationGroup_herbrand]
    simpa using hσ

/-- **The order of `G^{(1)} / G^{(1+)}` is the tame degree** (LMFDB `lf.slope_content`):
`[G_0 : G_1] = t`, the prime-to-`p` part of the ramification index. -/
lemma relIndex_lowerRamificationGroup_one_zero :
    (lowerRamificationGroup K L 1).relIndex (lowerRamificationGroup K L 0) = tameDegree K L := by
  have h : (lowerRamificationGroup K L 1).relIndex (lowerRamificationGroup K L 0) *
      Nat.card ↥(lowerRamificationGroup K L 1 ⊓ lowerRamificationGroup K L 0) =
        Nat.card (lowerRamificationGroup K L 0) :=
    (lowerRamificationGroup K L 1).relIndex_mul_card (lowerRamificationGroup K L 0)
  rw [inf_of_le_left (lowerRamificationGroup_antitone K L zero_le_one),
    natCard_lowerRamificationGroup_one, natCard_lowerRamificationGroup_zero] at h
  rw [tameDegree]
  exact (Nat.div_eq_of_eq_mul_left (pow_pos (CharP.prime_ringChar _).pos _) h.symm).symm

variable (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]

/-- **`[L^gal : K] = t u p ^ k`** (LMFDB `lf.slope_content`): for a finite separable extension `E`
of `K` with Artin slope content `[s_1, …, s_k]_t^u`, the degree of its Galois closure is
`t u p ^ k`. -/
lemma finrank_galoisClosure_eq : Module.finrank K (Algebra.galoisClosure K E) =
    galoisTameDegree K E * galoisUnramifiedDegree K E *
      ringChar 𝓀[K] ^ Multiset.card (wildArtinSlopes K E) :=
  finrank_eq_tameDegree_mul_inertiaDegree_mul_pow K (Algebra.galoisClosure K E)

end IsNonarchimedeanLocalField
