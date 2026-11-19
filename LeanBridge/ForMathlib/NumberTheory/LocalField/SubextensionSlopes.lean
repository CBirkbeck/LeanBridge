import LeanBridge.ForMathlib.NumberTheory.LocalField.SlopePolygonMeans

/-!
# The slopes of a subextension of an extension of `p`-adic fields

Let `K ⊆ L ⊆ L'` be finite separable extensions of nonarchimedean local fields of residue
characteristic `p`, inside `K̄`. We prove that the wild Swan slopes of `L / K` (LMFDB `lf.slopes`),
with their multiplicities, form a sub-multiset of the wild Swan slopes of `L' / K`, and likewise for
the wild Artin slopes. For `L'` the Galois closure of `L / K`, this is the statement behind the
hidden slopes of LMFDB `lf.hidden_slopes` and `lf.visible_slopes`.

Let `M / K` be a finite Galois extension containing `L'`, with group `G`, lower ramification groups
`G_i` and Herbrand function `φ`, and let `H' ⊆ H` be the groups of `L'` and `L`. The wild Swan
slopes of `L / K` are the `φ(i)`, `i ≥ 1`, each repeated `v_p(n_i / n_{i + 1})` times, where
`n_i = [G_i : H ∩ G_i]` is a power of `p`
(`IsNonarchimedeanLocalField.hullWildSwanSlopes_eq_visibleSwanSlopes`); they do not depend on `M`.
For `L'` the index is `n'_i = [G_i : H' ∩ G_i] = c_i n_i` with `c_i = [H ∩ G_i : H' ∩ G_i]`, and
`c_{i + 1} ≤ c_i`, because `(H ∩ G_{i + 1}) / (H' ∩ G_{i + 1})` embeds in
`(H ∩ G_i) / (H' ∩ G_i)`. So `v_p(n'_i / n'_{i + 1}) = v_p(n_i / n_{i + 1}) + v_p(c_i / c_{i + 1})`:
the slope `φ(i)` is repeated at least as often for `L'` as for `L`.

LMFDB `lf.slopes` calls the slope of every segment of its polygon `B` an Artin slope, and that slope
minus `1` a Swan slope, the wild ones being the Artin slopes greater than `1`; LMFDB
`lf.visible_slopes` and the LMFDB's pages list the wild slopes only. The segments of `B` that are
not wild have the slopes `0` and `1`: the Artin slope `0` occurs exactly when the residue degree `f`
of `L / K` is greater than `1`, and the Artin slope `1` exactly when its tame degree `ε` is. So that
the theorem holds for either list, we also prove it for the multiset of all the Artin slopes, the
wild ones with their multiplicities and `0` and `1` once each
(`IsNonarchimedeanLocalField.hullArtinSlopeMultiset`): `f(L / K)` divides `f(L' / K)`, and
`ε(L / K)` divides `ε(L' / K)`.

## Main definitions

* `IsNonarchimedeanLocalField.hullArtinSlopeMultiset` (LMFDB `lf.slopes`): the multiset of all the
  Artin slopes.
* `IsNonarchimedeanLocalField.hullSwanSlopeMultiset` (LMFDB `lf.slopes`): the multiset of all the
  Swan slopes.

## Main results

* `IsNonarchimedeanLocalField.swanSlopesOfSubgroup_le_of_le`: for subgroups `H' ⊆ H` of `G`, the
  Swan slopes of the fixed field of `H` form a sub-multiset of those of the fixed field of `H'`.
* `IsNonarchimedeanLocalField.swanSlopesOfSubgroup_fixingSubgroup_eq_of_le`: the Swan slopes of an
  extension inside `K̄` are the same in every finite Galois extension of `K` in `K̄` containing it.
* `IsNonarchimedeanLocalField.hullWildSwanSlopes_le_of_le` and
  `IsNonarchimedeanLocalField.hullWildArtinSlopes_le_of_le` (LMFDB `lf.hidden_slopes`,
  `lf.visible_slopes`): the wild Swan slopes and the wild Artin slopes of a subextension, with
  their multiplicities, form a sub-multiset of those of the extension.
* `IsNonarchimedeanLocalField.map_add_one_hullWildSwanSlopes` and
  `IsNonarchimedeanLocalField.map_add_one_hullSwanSlopeMultiset` (LMFDB `lf.slopes`): the Artin
  slopes are the Swan slopes plus `1`, for the wild slopes and for all the slopes.
* `IsNonarchimedeanLocalField.zero_mem_hullArtinSlopes_iff` and
  `IsNonarchimedeanLocalField.one_mem_hullArtinSlopes_iff` (LMFDB `lf.slopes`): the Artin slope `0`
  occurs exactly when `f > 1`, and the Artin slope `1` exactly when `ε > 1`.
* `IsNonarchimedeanLocalField.hullArtinSlopeMultiset_eq` and
  `IsNonarchimedeanLocalField.hullSwanSlopeMultiset_eq` (LMFDB `lf.slopes`): the multisets of all
  the Artin slopes and of all the Swan slopes, from `f`, `ε` and the wild slopes.
* `IsNonarchimedeanLocalField.mem_hullArtinSlopeMultiset_iff` and
  `IsNonarchimedeanLocalField.mem_hullSwanSlopeMultiset_iff` (LMFDB `lf.slopes`): the elements of
  these multisets are the Artin slopes and the Swan slopes.
* `IsNonarchimedeanLocalField.hullArtinSlopeMultiset_le_of_le` and
  `IsNonarchimedeanLocalField.hullSwanSlopeMultiset_le_of_le` (LMFDB `lf.hidden_slopes`): all the
  Artin slopes and all the Swan slopes of a subextension form a sub-multiset of those of the
  extension.
* `IsNonarchimedeanLocalField.hullSwanSlopeMultiset_sub_of_le` (LMFDB `lf.hidden_slopes`): the Swan
  slopes of the extension that are left are the wild ones that are left, with `-1` if
  `f(L / K) = 1 < f(L' / K)` and with `0` if `ε(L / K) = 1 < ε(L' / K)`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  appendix.
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable {a b : ℕ} (x : ℝ) {s : ℝ} {K M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsGalois K M] {H H' : Subgroup (M ≃ₐ[K] M)}
  {E L L' N N' : IntermediateField K (AlgebraicClosure K)}

private lemma ite_singleton_le_ite_singleton (h : a ≤ b) :
    (if 1 < a then {x} else 0 : Multiset ℝ) ≤ if 1 < b then {x} else 0 := by
  rcases em (1 < a) with h₁ | h₁
  · rw [ite_eq_left h₁, ite_eq_left (h₁.trans_le h)]
  · exact (ite_eq_right h₁).trans_le (Multiset.zero_le _)

private lemma ite_singleton_sub_ite_singleton (ha : 0 < a) (h : a ≤ b) :
    (if 1 < b then {x} else 0 : Multiset ℝ) - (if 1 < a then {x} else 0) =
      if a = 1 ∧ 1 < b then {x} else 0 := by
  rcases em (1 < a) with h₁ | h₁
  · rw [ite_eq_left h₁, ite_eq_left (h₁.trans_le h), ite_eq_right fun h' ↦ h₁.ne' h'.1, tsub_self]
  · rw [ite_eq_right h₁, tsub_zero]
    exact (if_congr (and_iff_right (by omega)) rfl rfl).symm

private lemma tsub_add_tsub_add_tsub {A A' B B' C C' : Multiset ℝ} (hA : A ≤ A') (hB : B ≤ B')
    (hC : C ≤ C') : A' - A + (B' - B) + (C' - C) = A' + B' + C' - (A + B + C) := by
  rw [tsub_add_tsub_comm hA hB, tsub_add_tsub_comm (add_le_add hA hB) hC]

private lemma map_add_one_map_sub_one (S : Multiset ℝ) : (S.map (· - 1)).map (· + 1) = S := by
  rw [Multiset.map_map]
  exact (Multiset.map_congr rfl fun y _ ↦ sub_add_cancel y 1).trans (Multiset.map_id _)

lemma padicValNat_relIndex_div_eq_add (h : H' ≤ H) (i : ℕ) : padicValNat (ringChar 𝓀[K])
    (H'.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
      H'.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) =
    padicValNat (ringChar 𝓀[K]) (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
      H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) +
      padicValNat (ringChar 𝓀[K]) (H'.relIndex (H ⊓ lowerRamificationGroup K M (i + 1 : ℕ)) /
        H'.relIndex (H ⊓ lowerRamificationGroup K M (i + 2 : ℕ))) := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨hp⟩
  have hle : lowerRamificationGroup K M (i + 2 : ℕ) ≤ lowerRamificationGroup K M (i + 1 : ℕ) :=
    lowerRamificationGroup_antitone K M (by omega)
  rcases exists_relIndex_lowerRamificationGroup_eq_pow K M H (by omega : 1 ≤ i + 1) with ⟨a, ha⟩
  rcases exists_relIndex_lowerRamificationGroup_eq_pow K M H (by omega : 1 ≤ i + 2) with ⟨b, hb⟩
  rcases exists_relIndex_lowerRamificationGroup_eq_pow K M H' (by omega : 1 ≤ i + 1) with ⟨a', ha'⟩
  rcases exists_relIndex_lowerRamificationGroup_eq_pow K M H' (by omega : 1 ≤ i + 2) with ⟨b', hb'⟩
  have h₁ : H'.relIndex (H ⊓ lowerRamificationGroup K M (i + 1 : ℕ)) *
      H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) =
        H'.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) := by
    rw [Subgroup.relIndex_inf_mul_relIndex, inf_of_le_left h]
  have h₂ : H'.relIndex (H ⊓ lowerRamificationGroup K M (i + 2 : ℕ)) *
      H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ)) =
        H'.relIndex (lowerRamificationGroup K M (i + 2 : ℕ)) := by
    rw [Subgroup.relIndex_inf_mul_relIndex, inf_of_le_left h]
  rcases (Nat.dvd_prime_pow hp).mp (ha' ▸ Dvd.intro _ h₁) with ⟨c, -, hc⟩
  rcases (Nat.dvd_prime_pow hp).mp (hb' ▸ Dvd.intro _ h₂) with ⟨d, -, hd⟩
  have hba : b ≤ a := by
    have h' : H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ)) ≤
        H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) :=
      Subgroup.relIndex_le_of_le_right hle Subgroup.index_ne_zero_of_finite
    rw [ha, hb] at h'
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h'
  have hdc : d ≤ c := by
    have h' : H'.relIndex (H ⊓ lowerRamificationGroup K M (i + 2 : ℕ)) ≤
        H'.relIndex (H ⊓ lowerRamificationGroup K M (i + 1 : ℕ)) :=
      Subgroup.relIndex_le_of_le_right (inf_le_inf_left H hle) Subgroup.index_ne_zero_of_finite
    rw [hc, hd] at h'
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h'
  have hac : a' = c + a := by
    rw [hc, ha, ha', ← pow_add] at h₁
    exact (Nat.pow_right_injective hp.two_le h₁).symm
  have hbd : b' = d + b := by
    rw [hd, hb, hb', ← pow_add] at h₂
    exact (Nat.pow_right_injective hp.two_le h₂).symm
  rw [ha, hb, ha', hb', hc, hd, Nat.pow_div hba hp.pos, Nat.pow_div hdc hp.pos,
    Nat.pow_div (by omega) hp.pos, padicValNat.prime_pow, padicValNat.prime_pow,
    padicValNat.prime_pow]
  omega

/-- **The Swan slopes of the fixed field of a larger subgroup**: for subgroups `H' ⊆ H` of the
Galois group `G` of a finite Galois extension `M / K` of nonarchimedean local fields, the Swan
slopes of `M^H / K`, with their multiplicities, form a sub-multiset of the Swan slopes of
`M^{H'} / K`. The slope `φ(i)` has the multiplicities `v_p(n_i / n_{i + 1})` and
`v_p(n'_i / n'_{i + 1})`, with `n_i = [G_i : H ∩ G_i]` and
`n'_i = [G_i : H' ∩ G_i] = n_i [H ∩ G_i : H' ∩ G_i]`, and `[H ∩ G_i : H' ∩ G_i]` decreases with
`i`. -/
lemma swanSlopesOfSubgroup_le_of_le (h : H' ≤ H) :
    swanSlopesOfSubgroup K M H ≤ swanSlopesOfSubgroup K M H' :=
  sum_le_sum fun i _ ↦ Multiset.replicate_mono _ <|
    (padicValNat_relIndex_div_eq_add h i).ge.trans' (Nat.le_add_right _ _)

variable [FiniteDimensional K N] [FiniteDimensional K N'] [IsGalois K N] [IsGalois K N'] in
/-- **The Swan slopes do not depend on the Galois extension inside `K̄`**: for finite Galois
extensions `N ⊆ N'` of `K` inside `K̄` and an extension `E ⊆ N` of `K`, the Swan slopes of `E / K`
computed in `N'`, from `Gal(N' / E)`, and in `N`, from `Gal(N / E)`, agree. -/
lemma swanSlopesOfSubgroup_fixingSubgroup_eq_of_le (hEN : E ≤ N) (h : N ≤ N') :
    swanSlopesOfSubgroup K N'
        (fixingSubgroup (N' ≃ₐ[K] N') (((↑) : N' → AlgebraicClosure K) ⁻¹' E)) =
      swanSlopesOfSubgroup K N
        (fixingSubgroup (N ≃ₐ[K] N) (((↑) : N → AlgebraicClosure K) ⁻¹' E)) := by
  let a : Algebra N N' := (IntermediateField.inclusion h).toAlgebra
  have hs : IsScalarTower K N N' := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension N N' := (IntermediateField.inclusion h).valuativeExtension
  have hf : Module.Finite N N' := .of_restrictScalars_finite K N N'
  rw [← swanSlopesOfSubgroup_comap_restrictNormalHom K N _ N']
  congr 1
  ext σ
  rw [Subgroup.mem_comap, mem_fixingSubgroup_iff, mem_fixingSubgroup_iff]
  exact ⟨fun hσ x hx ↦ (algebraMap N N').injective <|
      (σ.restrictNormal_commutes N x).trans (hσ (algebraMap N N' x) hx),
    fun hσ y hy ↦ (σ.restrictNormal_commutes N ⟨y, hEN hy⟩).symm.trans <|
      congrArg (algebraMap N N') (hσ ⟨y, hEN hy⟩ hy)⟩

variable [FiniteDimensional K L'] [Algebra.IsSeparable K L'] in
/-- **The wild Swan slopes of a subextension** (LMFDB `lf.hidden_slopes`, `lf.visible_slopes`): for
extensions `L ⊆ L'` of a nonarchimedean local field `K` inside `K̄`, with `L' / K` finite separable,
the wild Swan slopes of `L / K`, with their multiplicities, form a sub-multiset of the wild Swan
slopes of `L' / K`. -/
lemma hullWildSwanSlopes_le_of_le (h : L ≤ L') : hullWildSwanSlopes L ≤ hullWildSwanSlopes L' := by
  have hfin : FiniteDimensional K L := IntermediateField.finiteDimensional_of_le h
  have hsep : Algebra.IsSeparable K L := IntermediateField.isSeparable_of_le h
  rw [hullWildSwanSlopes_eq_visibleSwanSlopes, hullWildSwanSlopes_eq_visibleSwanSlopes,
    visibleSwanSlopes_eq_swanSlopesOfSubgroup, visibleSwanSlopes_eq_swanSlopesOfSubgroup,
    ← swanSlopesOfSubgroup_fixingSubgroup_eq_of_le (Algebra.le_galoisClosure L)
      (Algebra.galoisClosure_le_iff.mpr (h.trans (Algebra.le_galoisClosure L')))]
  exact swanSlopesOfSubgroup_le_of_le (fixingSubgroup_antitone _ _ (Set.preimage_mono h))

variable (L) in
/-- **The wild Artin slopes are the wild Swan slopes plus `1`** (LMFDB `lf.slopes`): adding `1` to
each wild Swan slope of an extension `L / K` inside `K̄` gives its wild Artin slopes. -/
lemma map_add_one_hullWildSwanSlopes : (hullWildSwanSlopes L).map (· + 1) = hullWildArtinSlopes L :=
  map_add_one_map_sub_one _

variable [FiniteDimensional K L'] [Algebra.IsSeparable K L'] in
/-- **The wild Artin slopes of a subextension** (LMFDB `lf.hidden_slopes`, `lf.visible_slopes`): for
extensions `L ⊆ L'` of a nonarchimedean local field `K` inside `K̄`, with `L' / K` finite separable,
the wild Artin slopes of `L / K`, with their multiplicities, form a sub-multiset of the wild Artin
slopes of `L' / K`. -/
lemma hullWildArtinSlopes_le_of_le (h : L ≤ L') :
    hullWildArtinSlopes L ≤ hullWildArtinSlopes L' := by
  rw [← map_add_one_hullWildSwanSlopes L, ← map_add_one_hullWildSwanSlopes L']
  exact Multiset.map_le_map (hullWildSwanSlopes_le_of_le h)

variable (L) in
/-- The **multiset of all the Artin slopes** (LMFDB `lf.slopes`) of an extension `L / K` inside
`K̄`: the slopes of the segments of its slope polygon `B`, where a wild slope is repeated `m` times
for its segment from `(n₁, c₁)` to `(n₂, c₂)` with `n₂ / n₁ = p ^ m`, as LMFDB `lf.slopes`
prescribes, and a slope at most `1` is listed once. The slopes at most `1` are `0` and `1`, which
occur exactly when the residue degree and the tame degree are greater than `1`
(`IsNonarchimedeanLocalField.hullArtinSlopeMultiset_eq`); the LMFDB lists the wild slopes only
(`IsNonarchimedeanLocalField.hullWildArtinSlopes`). -/
noncomputable def hullArtinSlopeMultiset : Multiset ℝ :=
  (∑ᶠ s ∈ hullArtinSlopes L ∩ {s | s ≤ 1}, {s}) + hullWildArtinSlopes L

variable (L) in
/-- The **multiset of all the Swan slopes** (LMFDB `lf.slopes`) of an extension `L / K` inside `K̄`:
its Artin slopes minus `1`, with the multiplicities of
`IsNonarchimedeanLocalField.hullArtinSlopeMultiset`. The LMFDB lists the wild ones only
(`IsNonarchimedeanLocalField.hullWildSwanSlopes`). -/
noncomputable def hullSwanSlopeMultiset : Multiset ℝ :=
  (hullArtinSlopeMultiset L).map (· - 1)

variable (L) in
/-- **All the Artin slopes are all the Swan slopes plus `1`** (LMFDB `lf.slopes`): adding `1` to
each element of the multiset of all the Swan slopes of an extension `L / K` inside `K̄` gives the
multiset of all its Artin slopes. -/
lemma map_add_one_hullSwanSlopeMultiset :
    (hullSwanSlopeMultiset L).map (· + 1) = hullArtinSlopeMultiset L :=
  map_add_one_map_sub_one _

section NonWild

variable (L) [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **The Artin slope `0`** (LMFDB `lf.slopes`): the slope polygon `B` of a finite separable
extension `L / K` inside `K̄` has a segment of slope `0`, from `(1, 0)` to `(f, 0)`, exactly when
the residue degree `f` of `L / K` is greater than `1`. -/
lemma zero_mem_hullArtinSlopes_iff : 0 ∈ hullArtinSlopes L ↔ 1 < inertiaDegree K L := by
  rw [mem_hullArtinSlopes_iff, ← index_fixingSubgroup_sup_lowerRamificationGroup_zero L]
  constructor
  · rintro ⟨t, ⟨-, hlt⟩, ht⟩
    have ht' : t = 0 := subgroupSlope_strictMono.injective <|
      (Rat.cast_eq_zero.mp ht).trans subgroupSlope_zero.symm
    subst ht'
    rwa [index_slopeVertexSubgroup_zero] at hlt
  · intro h
    refine ⟨0, ⟨Nat.zero_le _, ?_⟩, ?_⟩
    · rwa [index_slopeVertexSubgroup_zero]
    · rw [subgroupSlope_zero, Rat.cast_zero]

/-- **The Artin slope `1`** (LMFDB `lf.slopes`): the slope polygon `B` of a finite separable
extension `L / K` inside `K̄` has a segment of slope `1`, from the abscissa `f` to `f ε`, exactly
when the tame degree `ε` of `L / K` is greater than `1`. -/
lemma one_mem_hullArtinSlopes_iff : 1 ∈ hullArtinSlopes L ↔ 1 < tameDegree K L := by
  rw [mem_hullArtinSlopes_iff, ← Nat.lt_mul_iff_one_lt_right (inertiaDegree_pos (K := K) (L := L)),
    ← index_fixingSubgroup_sup_lowerRamificationGroup_one L,
    ← index_fixingSubgroup_sup_lowerRamificationGroup_zero L]
  constructor
  · rintro ⟨t, ⟨-, hlt⟩, ht⟩
    have ht' : t = 1 := subgroupSlope_strictMono.injective <|
      (Rat.cast_inj.mp (ht.trans Rat.cast_one.symm)).trans subgroupSlope_one.symm
    subst ht'
    exact hlt
  · intro h
    exact ⟨1, ⟨Nat.le_add_left _ _, h⟩, by rw [subgroupSlope_one, Rat.cast_one]⟩

/-- **All the Artin slopes** (LMFDB `lf.slopes`): the multiset of all the Artin slopes of a finite
separable extension `L / K` inside `K̄` consists of `0` if its residue degree `f` is greater than
`1`, of `1` if its tame degree `ε` is greater than `1`, and of its wild Artin slopes. -/
lemma hullArtinSlopeMultiset_eq : hullArtinSlopeMultiset L =
    (if 1 < inertiaDegree K L then {0} else 0) + (if 1 < tameDegree K L then {1} else 0) +
      hullWildArtinSlopes L := by
  classical
  have hset :
      hullArtinSlopes L ∩ {s | s ≤ 1} = ↑(({0, 1} : Finset ℝ).filter (· ∈ hullArtinSlopes L)) := by
    ext s
    rw [mem_coe, mem_filter, mem_insert, mem_singleton]
    exact ⟨fun hs ↦ ⟨eq_zero_or_eq_one_of_mem_hullArtinSlopes hs.1 hs.2, hs.1⟩,
      fun hs ↦ ⟨hs.2, hs.1.elim (fun h ↦ h.trans_le zero_le_one) Eq.le⟩⟩
  rw [hullArtinSlopeMultiset, hset, finsum_mem_coe_finset, sum_filter, sum_pair zero_ne_one]
  simp only [zero_mem_hullArtinSlopes_iff, one_mem_hullArtinSlopes_iff]

/-- **All the Swan slopes** (LMFDB `lf.slopes`): the multiset of all the Swan slopes of a finite
separable extension `L / K` inside `K̄` consists of `-1` if its residue degree `f` is greater than
`1`, of `0` if its tame degree `ε` is greater than `1`, and of its wild Swan slopes. -/
lemma hullSwanSlopeMultiset_eq : hullSwanSlopeMultiset L =
    (if 1 < inertiaDegree K L then {-1} else 0) + (if 1 < tameDegree K L then {0} else 0) +
      hullWildSwanSlopes L := by
  rw [hullSwanSlopeMultiset, hullArtinSlopeMultiset_eq, Multiset.map_add, Multiset.map_add,
    apply_ite (Multiset.map _), apply_ite (Multiset.map _), Multiset.map_singleton,
    Multiset.map_singleton, Multiset.map_zero, zero_sub, sub_self, hullWildSwanSlopes]

/-- **The elements of the multiset of all the Artin slopes are the Artin slopes** (LMFDB
`lf.slopes`): a real number occurs in the multiset of all the Artin slopes of a finite separable
extension `L / K` inside `K̄` exactly when it is an Artin slope of `L / K`, the slope of a segment
of its slope polygon `B`. -/
lemma mem_hullArtinSlopeMultiset_iff : s ∈ hullArtinSlopeMultiset L ↔ s ∈ hullArtinSlopes L := by
  rw [hullArtinSlopeMultiset_eq, Multiset.mem_add, Multiset.mem_add, mem_hullWildArtinSlopes_iff]
  grind [Multiset.mem_singleton, zero_mem_hullArtinSlopes_iff, one_mem_hullArtinSlopes_iff,
    eq_zero_or_eq_one_of_mem_hullArtinSlopes]

/-- **The elements of the multiset of all the Swan slopes are the Swan slopes** (LMFDB
`lf.slopes`): a real number occurs in the multiset of all the Swan slopes of a finite separable
extension `L / K` inside `K̄` exactly when it is a Swan slope of `L / K`, an Artin slope minus
`1`. -/
lemma mem_hullSwanSlopeMultiset_iff : s ∈ hullSwanSlopeMultiset L ↔ s ∈ hullSwanSlopes L :=
  Multiset.mem_map.trans <| exists_congr fun _ ↦ and_congr_left' (mem_hullArtinSlopeMultiset_iff L)

end NonWild

variable [FiniteDimensional K L'] [Algebra.IsSeparable K L'] in
/-- **All the Artin slopes of a subextension** (LMFDB `lf.hidden_slopes`): for extensions `L ⊆ L'`
of a nonarchimedean local field `K` inside `K̄`, with `L' / K` finite separable, the multiset of all
the Artin slopes of `L / K`, the slopes `0` and `1` of the segments that are not wild included,
is a sub-multiset of that of `L' / K`. -/
lemma hullArtinSlopeMultiset_le_of_le (h : L ≤ L') :
    hullArtinSlopeMultiset L ≤ hullArtinSlopeMultiset L' := by
  have hfin : FiniteDimensional K L := IntermediateField.finiteDimensional_of_le h
  have hsep : Algebra.IsSeparable K L := IntermediateField.isSeparable_of_le h
  rw [hullArtinSlopeMultiset_eq L, hullArtinSlopeMultiset_eq L']
  exact add_le_add (add_le_add (ite_singleton_le_ite_singleton 0 (inertiaDegree_le_of_le h))
    (ite_singleton_le_ite_singleton 1 (tameDegree_le_of_le h))) (hullWildArtinSlopes_le_of_le h)

variable [FiniteDimensional K L'] [Algebra.IsSeparable K L'] in
/-- **All the Swan slopes of a subextension** (LMFDB `lf.hidden_slopes`): for extensions `L ⊆ L'` of
a nonarchimedean local field `K` inside `K̄`, with `L' / K` finite separable, the multiset of all
the Swan slopes of `L / K`, the slopes `-1` and `0` of the segments that are not wild included, is a
sub-multiset of that of `L' / K`. -/
lemma hullSwanSlopeMultiset_le_of_le (h : L ≤ L') :
    hullSwanSlopeMultiset L ≤ hullSwanSlopeMultiset L' :=
  Multiset.map_le_map (hullArtinSlopeMultiset_le_of_le h)

variable [FiniteDimensional K L] [FiniteDimensional K L'] [Algebra.IsSeparable K L'] in
/-- **The Swan slopes of an extension that are not Swan slopes of a subextension** (LMFDB
`lf.hidden_slopes`): for finite extensions `L ⊆ L'` of a nonarchimedean local field `K` inside `K̄`,
with `L' / K` separable, subtracting the multiset of all the Swan slopes of `L / K` from that of
`L' / K` leaves the wild Swan slopes of `L' / K` that are not wild Swan slopes of `L / K`, together
with `-1` if `f(L / K) = 1 < f(L' / K)` and with `0` if `ε(L / K) = 1 < ε(L' / K)`. -/
lemma hullSwanSlopeMultiset_sub_of_le (h : L ≤ L') : hullSwanSlopeMultiset L' -
    hullSwanSlopeMultiset L = (if inertiaDegree K L = 1 ∧ 1 < inertiaDegree K L' then {-1} else 0) +
      (if tameDegree K L = 1 ∧ 1 < tameDegree K L' then {0} else 0) +
      (hullWildSwanSlopes L' - hullWildSwanSlopes L) := by
  have hsep : Algebra.IsSeparable K L := IntermediateField.isSeparable_of_le h
  have hf : inertiaDegree K L ≤ inertiaDegree K L' := inertiaDegree_le_of_le h
  have hε : tameDegree K L ≤ tameDegree K L' := tameDegree_le_of_le h
  rw [hullSwanSlopeMultiset_eq, hullSwanSlopeMultiset_eq L,
    ← ite_singleton_sub_ite_singleton (-1) inertiaDegree_pos hf,
    ← ite_singleton_sub_ite_singleton 0 tameDegree_pos hε]
  exact (tsub_add_tsub_add_tsub (ite_singleton_le_ite_singleton (-1) hf)
    (ite_singleton_le_ite_singleton 0 hε) (hullWildSwanSlopes_le_of_le h)).symm

end IsNonarchimedeanLocalField
