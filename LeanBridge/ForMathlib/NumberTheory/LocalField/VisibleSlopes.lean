import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamilyInvariants
import LeanBridge.ForMathlib.NumberTheory.LocalField.SubgroupSlopePolygon

/-!
# The visible slopes of an extension of `p`-adic fields

Let `L / K` be a finite separable extension of nonarchimedean local fields of residue
characteristic `p`, inside `K̄`. LMFDB `lf.slopes` plots the point `(n_E, c_E)`, degree and
discriminant exponent, of every subextension `E / K` of `L / K`
(`IsNonarchimedeanLocalField.subextensionPoints`), and takes the boundary `B` of the lower convex
hull of these points (`IsNonarchimedeanLocalField.slopesPolygon`). The slopes of the segments of `B`
are the Artin slopes of `L / K`, and those greater than `1` the wild Artin slopes; a segment of wild
slope running from `(n₁, c₁)` to `(n₂, c₂)` has `n₂ / n₁ = p ^ m`, and its slope is repeated `m`
times (`IsNonarchimedeanLocalField.hullWildArtinSlopes`). The Swan slopes are the Artin slopes minus
`1`, and the wild Swan slopes the positive ones. With the residue degree `f` and the tame degree
`ε`, the Artin slope content is `[a_1, …, a_w]_ε^f` and the Swan slope content `[s_1, …, s_w]_ε^f`.

We prove the knowl's theorem that the wild Swan slopes are the positive upper ramification breaks
of `L / K`, with multiplicities, in the sense of Deligne when `L / K` is not Galois. Let `M` be the
Galois closure of `L` in `K̄`, with group `G`, lower ramification groups `G_i` and `H = Gal(M / L)`.
The subextensions `E` of `L / K` are the fixed fields of the subgroups `J ⊇ H`, with `n_E = [G : J]`
and `c_E = [G : J] ∑_i (#G_i - #(J ∩ G_i)) / #G_0`
(`IsNonarchimedeanLocalField.subextensionPoints_eq`). The vertices of `B` are the points of `K` and
of the fixed fields of the subgroups `H G_t`
(`IsNonarchimedeanLocalField.isLowerHullVertices_subgroupSlopePoints`): the maximal unramified and
the maximal tamely ramified subextensions, and the subextensions at the jumps of the Swan slopes.
The wild segments of `B` have the slopes `1 + φ(i)`, `i ≥ 1`, for the Herbrand function `φ` of
`M / K`, and run from `n_t` to `n_{t + 1} = p ^ m n_t` with
`p ^ m = [G_i : H ∩ G_i] / [G_{i + 1} : H ∩ G_{i + 1}]`: this is Deligne's description of the upper
breaks of `L / K` (`IsNonarchimedeanLocalField.visibleSwanSlopes`). For `L / K` Galois they are the
positive upper ramification breaks of Serre's *Local Fields*, Chapter IV.

## Main definitions

* `IsNonarchimedeanLocalField.subextensionPoints` (LMFDB `lf.slopes`): the points `(n_E, c_E)`.
* `IsNonarchimedeanLocalField.slopesPolygon` (LMFDB `lf.slopes`): the polygon `B`.
* `IsNonarchimedeanLocalField.hullArtinSlopes` (LMFDB `lf.slopes`): the Artin slopes.
* `IsNonarchimedeanLocalField.hullWildArtinSlopes` (LMFDB `lf.slopes`): the wild Artin slopes,
  with multiplicities.
* `IsNonarchimedeanLocalField.hullSwanSlopes` (LMFDB `lf.slopes`): the Swan slopes.
* `IsNonarchimedeanLocalField.hullWildSwanSlopes` (LMFDB `lf.slopes`): the wild Swan slopes, with
  multiplicities.
* `IsNonarchimedeanLocalField.visibleArtinSlopeContent` and
  `IsNonarchimedeanLocalField.visibleSwanSlopeContent` (LMFDB `lf.slopes`): the Artin and Swan slope
  contents.

## Main results

* `IsNonarchimedeanLocalField.subextensionPoints_eq`: the points of the subextensions are the points
  `([G : J], c(J))` of the subgroups `J ⊇ Gal(M / L)`.
* `IsNonarchimedeanLocalField.div_eq_pow_slopeMultiplicity` (LMFDB `lf.slopes`): a segment of wild
  slope running from `(n₁, c₁)` to `(n₂, c₂)` has `n₂ / n₁ = p ^ m`, `m` the multiplicity of its
  slope.
* `IsNonarchimedeanLocalField.mem_hullWildSwanSlopes_iff` (LMFDB `lf.slopes`): the wild Swan slopes
  are the positive Swan slopes.
* `IsNonarchimedeanLocalField.eq_zero_or_eq_one_of_mem_hullArtinSlopes` and
  `IsNonarchimedeanLocalField.mem_hullWildArtinSlopes_iff` (LMFDB `lf.slopes`,
  `lf.visible_slopes`): an Artin slope at most `1` is `0` or `1`, and the wild Artin slopes are the
  Artin slopes greater than `1`.
* `IsNonarchimedeanLocalField.count_hullWildArtinSlopes` and
  `IsNonarchimedeanLocalField.slopeMultiplicity_pos` (LMFDB `lf.visible_slopes`): a wild Artin
  slope is listed `m` times, for the multiplicity `m` of its segment, and `m ≥ 1`.
* `IsNonarchimedeanLocalField.hullWildArtinSlopes_eq_visibleArtinSlopes` and
  `IsNonarchimedeanLocalField.hullWildSwanSlopes_eq_visibleSwanSlopes` (LMFDB `lf.slopes`): the wild
  Swan slopes are the positive upper ramification breaks of `L / K`, after Deligne, with
  multiplicities.
* `IsNonarchimedeanLocalField.hullWildSwanSlopes_eq_swanSlopesOfIsGalois` (LMFDB `lf.slopes`): for
  `L / K` Galois they are the positive upper ramification breaks of `Gal(L / K)`.
* `IsNonarchimedeanLocalField.hullWildArtinSlopes_eq_wildArtinSlopesOfIsGalois` (LMFDB
  `lf.visible_slopes`): for `L / K` Galois the wild Artin slopes are those of `Gal(L / K)`.
* `IsNonarchimedeanLocalField.visibleArtinSlopeContent_eq` and
  `IsNonarchimedeanLocalField.visibleSwanSlopeContent_eq` (LMFDB `lf.slopes`): the slope contents
  through the upper ramification breaks.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §4, and Chapter IV.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  appendix.
* J. W. Jones and D. P. Roberts, *A database of local fields*, J. Symbolic Comput. 41 (2006).
-/

open ValuativeRel TauCeti LocalFieldsRamification Set

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (AlgebraicClosure K))

/-- The **points `(n_E, c_E)` of the subextensions** (LMFDB `lf.slopes`) of an extension `L` of a
nonarchimedean local field `K` inside `K̄`: for each subextension `E / K` of `L / K`, finite and
separable, the degree `n_E = [E : K]` and the discriminant exponent `c_E` of `E / K`, for Tau Ceti's
spectral-norm local-field structure on `E`. For `L / K` finite separable every subextension is
finite and separable. -/
noncomputable def subextensionPoints : Set (ℝ × ℝ) :=
  {q | ∃ (E : IntermediateField K (AlgebraicClosure K)) (_ : E ≤ L) (_ : FiniteDimensional K E)
    (_ : Algebra.IsSeparable K E), q = ((Module.finrank K E : ℝ), (discriminantExponent K E : ℝ))}

/-- The **slope polygon** `B` (LMFDB `lf.slopes`) of an extension `L / K` inside `K̄`: the boundary
of the lower convex hull of the points `(n_E, c_E)` of its subextensions. -/
noncomputable def slopesPolygon : Set (ℝ × ℝ) :=
  lowerConvexHull (subextensionPoints L)

/-- The **Artin slopes** (LMFDB `lf.slopes`) of an extension `L / K` inside `K̄`: the slopes of the
segments of its slope polygon `B`. -/
noncomputable def hullArtinSlopes : Set ℝ :=
  segmentSlopes (slopesPolygon L)

/-- The **wild Artin slopes** (LMFDB `lf.slopes`) of an extension `L / K` inside `K̄`: the Artin
slopes greater than `1`, each repeated `m` times, where the segment of `B` of that slope runs from
`(n₁, c₁)` to `(n₂, c₂)` with `n₂ / n₁ = p ^ m`, for the residue characteristic `p` of `K`. -/
noncomputable def hullWildArtinSlopes : Multiset ℝ :=
  wildSegmentSlopes (ringChar 𝓀[K]) (slopesPolygon L)

/-- The **Swan slopes** (LMFDB `lf.slopes`) of an extension `L / K` inside `K̄`: its Artin slopes
minus `1`. -/
noncomputable def hullSwanSlopes : Set ℝ :=
  (· - 1) '' hullArtinSlopes L

/-- The **wild Swan slopes** (LMFDB `lf.slopes`) of an extension `L / K` inside `K̄`: its wild Artin
slopes minus `1`, with their multiplicities; they are its positive Swan slopes
(`IsNonarchimedeanLocalField.mem_hullWildSwanSlopes_iff`). -/
noncomputable def hullWildSwanSlopes : Multiset ℝ :=
  (hullWildArtinSlopes L).map (· - 1)

section Hull

variable [FiniteDimensional K L]

/-- The **Artin slope content** `[a_1, …, a_w]_ε^f` (LMFDB `lf.slopes`) of a finite extension
`L / K` inside `K̄`: its wild Artin slopes, its tame degree `ε` and its residue degree `f`. -/
noncomputable def visibleArtinSlopeContent : Multiset ℝ × ℕ × ℕ :=
  (hullWildArtinSlopes L, tameDegree K L, inertiaDegree K L)

/-- The **Swan slope content** `[s_1, …, s_w]_ε^f` (LMFDB `lf.slopes`) of a finite extension `L / K`
inside `K̄`: its wild Swan slopes, its tame degree `ε` and its residue degree `f`. -/
noncomputable def visibleSwanSlopeContent : Multiset ℝ × ℕ × ℕ :=
  (hullWildSwanSlopes L, tameDegree K L, inertiaDegree K L)

lemma natCast_discriminantExponent_eq_subgroupDiscriminantExponent_fixingSubgroup
    {E N : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E]
    [Algebra.IsSeparable K E] [FiniteDimensional K N] [IsGalois K N] (h : E ≤ N) :
    (discriminantExponent K E : ℚ) = subgroupDiscriminantExponent K N
      (fixingSubgroup (N ≃ₐ[K] N) (((↑) : N → AlgebraicClosure K) ⁻¹' E)) := by
  let a : Algebra E N := (IntermediateField.inclusion h).toAlgebra
  have hs : IsScalarTower K E N := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension E N := (IntermediateField.inclusion h).valuativeExtension
  have hf : Module.Finite E N := .of_restrictScalars_finite K E N
  rw [fixingSubgroup_preimage_eq_range_restrictScalarsHom h]
  exact natCast_discriminantExponent_eq_subgroupDiscriminantExponent E

variable [Algebra.IsSeparable K L] {s : ℝ}

/-- **The points of the subextensions are the points of the subgroups**: for a finite separable
extension `L / K` inside `K̄`, with Galois closure `M` in `K̄`, the points `(n_E, c_E)` of the
subextensions of `L / K` are the points `([G : J], c(J))` of the subgroups `J` of `G = Gal(M / K)`
containing `Gal(M / L)`: `E` is the fixed field of `J`. -/
lemma subextensionPoints_eq : subextensionPoints L = subgroupSlopePoints K
    (Algebra.galoisClosure K L)
    (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  ext q
  constructor
  · rintro ⟨E, hEL, hfin, hsep, rfl⟩
    refine ⟨fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' E),
      fixingSubgroup_antitone _ _ (preimage_mono hEL), ?_⟩
    dsimp only
    rw [← finrank_eq_index_fixingSubgroup (hEL.trans hLM),
      ← natCast_discriminantExponent_eq_subgroupDiscriminantExponent_fixingSubgroup
        (hEL.trans hLM), Rat.cast_natCast]
  · rintro ⟨J, hJ, rfl⟩
    have hle :
        IntermediateField.lift (IntermediateField.fixedField J) ≤ Algebra.galoisClosure K L :=
      IntermediateField.lift_le _
    have hfin : FiniteDimensional K (IntermediateField.lift (IntermediateField.fixedField J)) :=
      IntermediateField.finiteDimensional_of_le hle
    have hsep : Algebra.IsSeparable K (IntermediateField.lift (IntermediateField.fixedField J)) :=
      IntermediateField.isSeparable_of_le hle
    refine ⟨_, lift_fixedField_le hLM hJ, hfin, hsep, ?_⟩
    dsimp only
    rw [finrank_eq_index_fixingSubgroup hle, fixingSubgroup_preimage_lift_fixedField,
      ← Rat.cast_natCast (discriminantExponent K _),
      natCast_discriminantExponent_eq_subgroupDiscriminantExponent_fixingSubgroup hle,
      fixingSubgroup_preimage_lift_fixedField]

lemma strictMonoOn_subgroupSlope (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
    (k : ℕ) : StrictMonoOn (fun t ↦ (subgroupSlope K M t : ℝ)) (Iic k) :=
  (Rat.cast_strictMono.comp subgroupSlope_strictMono).strictMonoOn _

/-- **The wild Artin slopes are the upper ramification breaks plus `1`** (LMFDB `lf.slopes`): for a
finite separable extension `L / K` of nonarchimedean local fields inside `K̄`, the wild Artin slopes
read off the lower convex hull of the points `(n_E, c_E)` of the subextensions, each repeated
`log_p (n₂ / n₁)` times, are the positive upper ramification breaks of `L / K` in the sense of
Deligne plus `1`, with multiplicities (`IsNonarchimedeanLocalField.visibleArtinSlopes`). -/
lemma hullWildArtinSlopes_eq_visibleArtinSlopes : hullWildArtinSlopes L = visibleArtinSlopes L := by
  rw [hullWildArtinSlopes, slopesPolygon, subextensionPoints_eq,
    (isLowerHullVertices_subgroupSlopePoints _).wildSegmentSlopes_lowerConvexHull
      (strictMonoOn_subgroupSlope _ _), sum_filter_replicate_eq_map_swanSlopesOfSubgroup,
    visibleArtinSlopes, visibleSwanSlopes_eq_swanSlopesOfSubgroup]

/-- **The Swan slopes are the upper ramification breaks** (LMFDB `lf.slopes`): for a finite
separable extension `L / K` of nonarchimedean local fields inside `K̄`, the wild Swan slopes read
off the lower convex hull of the points `(n_E, c_E)` of the subextensions are the positive upper
ramification breaks of `L / K`, in the sense of Deligne, with multiplicities
(`IsNonarchimedeanLocalField.visibleSwanSlopes`). -/
lemma hullWildSwanSlopes_eq_visibleSwanSlopes : hullWildSwanSlopes L = visibleSwanSlopes L := by
  rw [hullWildSwanSlopes, hullWildArtinSlopes_eq_visibleArtinSlopes, visibleArtinSlopes,
    Multiset.map_map]
  exact (Multiset.map_congr rfl fun x _ ↦ add_sub_cancel_right x 1).trans (Multiset.map_id _)

/-- **The Swan slopes of a Galois extension are its upper ramification breaks** (LMFDB
`lf.slopes`): for a finite Galois extension `E / K` of nonarchimedean local fields inside `K̄`, the
wild Swan slopes read off the lower convex hull of the points of the subextensions are the positive
upper ramification breaks of `Gal(E / K)` (Serre, *Local Fields*, IV), with multiplicities. -/
lemma hullWildSwanSlopes_eq_swanSlopesOfIsGalois (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsGalois K E] : hullWildSwanSlopes E = swanSlopesOfIsGalois K E := by
  rw [hullWildSwanSlopes_eq_visibleSwanSlopes, visibleSwanSlopes_eq_swanSlopesOfIsGalois]

/-- **The Artin slope content through the upper ramification breaks** (LMFDB `lf.slopes`): the
Artin slope content `[a_1, …, a_w]_ε^f` of a finite separable extension `L / K` inside `K̄` consists
of its positive upper ramification breaks plus `1`, its tame degree and its residue degree. -/
lemma visibleArtinSlopeContent_eq :
    visibleArtinSlopeContent L = (visibleArtinSlopes L, tameDegree K L, inertiaDegree K L) := by
  rw [visibleArtinSlopeContent, hullWildArtinSlopes_eq_visibleArtinSlopes]

/-- **The Swan slope content through the upper ramification breaks** (LMFDB `lf.slopes`): the Swan
slope content `[s_1, …, s_w]_ε^f` of a finite separable extension `L / K` inside `K̄` consists of
its positive upper ramification breaks, its tame degree and its residue degree. -/
lemma visibleSwanSlopeContent_eq :
    visibleSwanSlopeContent L = (visibleSwanSlopes L, tameDegree K L, inertiaDegree K L) := by
  rw [visibleSwanSlopeContent, hullWildSwanSlopes_eq_visibleSwanSlopes]

/-- **A wild segment runs between degrees in the ratio `p ^ m`** (LMFDB `lf.slopes`): if a segment
of slope greater than `1` of the slope polygon `B` of a finite separable extension `L / K` inside
`K̄` runs from `(n₁, c₁)` to `(n₂, c₂)`, then `n₂ / n₁ = p ^ m` for the residue characteristic `p`,
where `m` is the multiplicity of its slope in the wild Artin slopes. -/
lemma div_eq_pow_slopeMultiplicity {q q' : ℝ × ℝ} (hq : q.1 < q'.1)
    (hσ : segment ℝ q q' ∈ polygonEdgesWithSlope (slopesPolygon L) (Ioi 1)) : q'.1 / q.1 =
      (ringChar 𝓀[K] : ℝ) ^
          slopeMultiplicity (ringChar 𝓀[K]) (slopesPolygon L) ((q'.2 - q.2) / (q'.1 - q.1)) := by
  rw [slopesPolygon, subextensionPoints_eq] at hσ ⊢
  set H : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)
  have hS : IsLowerHullVertices (subgroupSlopePoints K (Algebra.galoisClosure K L) H)
      ((largestLowerJump K (Algebra.galoisClosure K L)).toNat + 1)
      (fun t ↦ (slopeVertexSubgroup K _ H t).index)
      (fun t ↦ (subgroupDiscriminantExponent K _ (slopeVertexSubgroup K _ H t) : ℝ))
      (fun t ↦ (subgroupSlope K (Algebra.galoisClosure K L) t : ℝ)) :=
    isLowerHullVertices_subgroupSlopePoints H
  have hτ : StrictMonoOn (fun t ↦ (subgroupSlope K (Algebra.galoisClosure K L) t : ℝ))
      (Iic ((largestLowerJump K (Algebra.galoisClosure K L)).toNat + 1)) :=
    strictMonoOn_subgroupSlope _ _
  have hslope : (q'.2 - q.2) / (q'.1 - q.1) ∈ Ioi (1 : ℝ) :=
    slope_mem_of_mem_polygonEdgesWithSlope hq hσ
  rcases hS.exists_eq_of_mem_polygonEdges hτ hq hσ.1 with ⟨t, ht, hlt, h₁, h₂, h₃⟩
  have h2 : 2 ≤ t := by
    rw [mem_Ioi, h₃] at hslope
    exact one_lt_subgroupSlope_iff.mp (by exact_mod_cast hslope)
  rcases Nat.exists_eq_add_of_le' h2 with ⟨i, rfl⟩
  rw [h₃, hS.slopeMultiplicity_lowerConvexHull hτ ht hlt, h₁, h₂]
  simp only [slopeVertexSubgroup]
  rw [natCast_index_div_index_sup_lowerRamificationGroup H i, Nat.floor_natCast,
    Nat.log_pow (CharP.prime_ringChar 𝓀[K]).one_lt, Nat.cast_pow]

/-- **The wild Swan slopes are the positive Swan slopes** (LMFDB `lf.slopes`): a real number is a
wild Swan slope of a finite separable extension `L / K` inside `K̄` exactly when it is a positive
Swan slope. -/
lemma mem_hullWildSwanSlopes_iff : s ∈ hullWildSwanSlopes L ↔ s ∈ hullSwanSlopes L ∧ 0 < s := by
  rw [hullWildSwanSlopes, hullSwanSlopes, hullArtinSlopes, hullWildArtinSlopes, slopesPolygon,
    subextensionPoints_eq]
  set H : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)
  have hS : IsLowerHullVertices (subgroupSlopePoints K (Algebra.galoisClosure K L) H)
      ((largestLowerJump K (Algebra.galoisClosure K L)).toNat + 1)
      (fun t ↦ (slopeVertexSubgroup K _ H t).index)
      (fun t ↦ (subgroupDiscriminantExponent K _ (slopeVertexSubgroup K _ H t) : ℝ))
      (fun t ↦ (subgroupSlope K (Algebra.galoisClosure K L) t : ℝ)) :=
    isLowerHullVertices_subgroupSlopePoints H
  rw [hS.wildSegmentSlopes_lowerConvexHull (strictMonoOn_subgroupSlope _ _),
    hS.segmentSlopes_lowerConvexHull, Multiset.mem_map]
  simp only [Multiset.mem_sum, Finset.mem_filter, Finset.mem_range, Multiset.mem_replicate]
  constructor
  · rintro ⟨a, ⟨t, ⟨ht, hlt, hτt⟩, -, rfl⟩, rfl⟩
    exact ⟨⟨_, ⟨t, ⟨by omega, hlt⟩, rfl⟩, rfl⟩, by linarith⟩
  · rintro ⟨⟨a, ⟨t, ⟨ht, hlt⟩, rfl⟩, rfl⟩, hs⟩
    have h1 : (1 : ℝ) < subgroupSlope K (Algebra.galoisClosure K L) t := by linarith
    have h2 : 2 ≤ t := one_lt_subgroupSlope_iff.mp (by exact_mod_cast h1)
    refine ⟨_, ⟨t, ⟨by omega, hlt, by linarith⟩, ?_, rfl⟩, rfl⟩
    rcases Nat.exists_eq_add_of_le' h2 with ⟨i, rfl⟩
    simp only [slopeVertexSubgroup] at hlt ⊢
    rw [natCast_index_div_index_sup_lowerRamificationGroup H i, Nat.floor_natCast,
      Nat.log_pow (CharP.prime_ringChar 𝓀[K]).one_lt]
    intro h
    rw [index_sup_lowerRamificationGroup_add_two H i, h, pow_zero, mul_one] at hlt
    exact lt_irrefl _ hlt

variable {L} in
lemma mem_hullArtinSlopes_iff : s ∈ hullArtinSlopes L ↔
    ∃ t, (t ≤ (largestLowerJump K (Algebra.galoisClosure K L)).toNat + 1 ∧
      (slopeVertexSubgroup K (Algebra.galoisClosure K L) (fixingSubgroup _
        (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) t).index <
      (slopeVertexSubgroup K (Algebra.galoisClosure K L) (fixingSubgroup _
        (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) (t + 1)).index) ∧
      (subgroupSlope K (Algebra.galoisClosure K L) t : ℝ) = s := by
  rw [hullArtinSlopes, slopesPolygon, subextensionPoints_eq,
    (isLowerHullVertices_subgroupSlopePoints _).segmentSlopes_lowerConvexHull]
  exact Iff.rfl

variable {L} in
/-- **The Artin slopes that are not wild are `0` and `1`** (LMFDB `lf.slopes`): an Artin slope at
most `1` of a finite separable extension `L / K` inside `K̄` is `0` or `1`. -/
lemma eq_zero_or_eq_one_of_mem_hullArtinSlopes (hs : s ∈ hullArtinSlopes L) (h : s ≤ 1) :
    s = 0 ∨ s = 1 := by
  rcases mem_hullArtinSlopes_iff.mp hs with ⟨t, -, rfl⟩
  have ht : ¬2 ≤ t := fun h2 ↦ h.not_gt <| by exact_mod_cast one_lt_subgroupSlope_iff.mpr h2
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · exact .inl (by rw [subgroupSlope_zero, Rat.cast_zero])
  · exact .inr (by rw [subgroupSlope_one, Rat.cast_one])

/-- **The wild Artin slopes are the Artin slopes greater than `1`** (LMFDB `lf.slopes`,
`lf.visible_slopes`): a real number is a wild Artin slope of a finite separable extension `L / K`
inside `K̄`, a visible Artin slope, exactly when it is an Artin slope greater than `1`. -/
lemma mem_hullWildArtinSlopes_iff : s ∈ hullWildArtinSlopes L ↔ s ∈ hullArtinSlopes L ∧ 1 < s :=
  (Multiset.mem_map_of_injective sub_left_injective).symm.trans <|
    (mem_hullWildSwanSlopes_iff L).trans <| and_congr sub_left_injective.mem_set_image sub_pos

/-- **A wild slope is listed as often as its multiplicity** (LMFDB `lf.visible_slopes`,
`lf.slopes`): an Artin slope `s > 1` of a finite separable extension `L / K` inside `K̄` occurs `k`
times in the list of its visible Artin slopes, where the segment of slope `s` runs from `(n₁, c₁)`
to `(n₂, c₂)` with `n₂ / n₁ = p ^ k` (`IsNonarchimedeanLocalField.div_eq_pow_slopeMultiplicity`). -/
lemma count_hullWildArtinSlopes (hs : s ∈ hullArtinSlopes L) (h1 : 1 < s) :
    (hullWildArtinSlopes L).count s = slopeMultiplicity (ringChar 𝓀[K]) (slopesPolygon L) s := by
  rcases mem_hullArtinSlopes_iff.mp hs with ⟨t, ⟨ht, hlt⟩, rfl⟩
  rw [hullWildArtinSlopes, slopesPolygon, subextensionPoints_eq,
    (isLowerHullVertices_subgroupSlopePoints _).wildSegmentSlopes_lowerConvexHull
      (strictMonoOn_subgroupSlope _ _),
    (isLowerHullVertices_subgroupSlopePoints _).slopeMultiplicity_lowerConvexHull
      (strictMonoOn_subgroupSlope _ _) ht hlt, Multiset.count_sum']
  refine (Finset.sum_eq_single_of_mem t (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ht), hlt, h1⟩) fun t' _ hne ↦
      Multiset.count_eq_zero_of_notMem fun h ↦ hne ?_).trans (Multiset.count_replicate_self _ _)
  exact subgroupSlope_strictMono.injective <|
    Rat.cast_injective (Multiset.eq_of_mem_replicate h).symm

end Hull

variable {q q' : ℝ × ℝ} [FiniteDimensional K L]

variable [IsGalois K L] in
/-- **The visible Artin slopes of a Galois extension are its wild Artin slopes** (LMFDB
`lf.visible_slopes`): for a finite Galois extension `L / K` of nonarchimedean local fields inside
`K̄`, the wild Artin slopes read off the lower convex hull of the points `(n_E, c_E)` of the
subextensions are the wild Artin slopes of the ramification filtration of `Gal(L / K)` (LMFDB
`lf.wild_slopes`). -/
lemma hullWildArtinSlopes_eq_wildArtinSlopesOfIsGalois :
    hullWildArtinSlopes L = wildArtinSlopesOfIsGalois K L :=
  (hullWildArtinSlopes_eq_visibleArtinSlopes L).trans
    (visibleArtinSlopes_eq_wildArtinSlopesOfIsGalois L)

variable [Algebra.IsSeparable K L] in
/-- **A wild segment has positive multiplicity** (LMFDB `lf.visible_slopes`): if a segment of slope
greater than `1` of the slope polygon of a finite separable extension `L / K` inside `K̄` runs from
`(n₁, c₁)` to `(n₂, c₂)`, then the `k` with `n₂ / n₁ = p ^ k`
(`IsNonarchimedeanLocalField.div_eq_pow_slopeMultiplicity`), the number of times its slope is
listed, is positive. -/
lemma slopeMultiplicity_pos (hq : q.1 < q'.1)
    (hσ : segment ℝ q q' ∈ polygonEdgesWithSlope (slopesPolygon L) (Ioi 1)) :
    0 < slopeMultiplicity (ringChar 𝓀[K]) (slopesPolygon L) ((q'.2 - q.2) / (q'.1 - q.1)) := by
  refine Nat.pos_of_ne_zero fun h0 ↦ ?_
  have h : q'.1 / q.1 = 1 := by
    rw [div_eq_pow_slopeMultiplicity L hq hσ, h0, pow_zero]
  have hq0 : q.1 ≠ 0 := fun h' ↦ zero_ne_one <| by rw [← h, h', div_zero]
  exact hq.ne' ((div_eq_one_iff_eq hq0).mp h)

end IsNonarchimedeanLocalField
