import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionRamificationPolygon
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamSubextension
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolygonSegments

/-!
# The heights of an extension of `p`-adic fields

Let `L / K` be a finite separable extension of nonarchimedean local fields of residue
characteristic `p`, with discriminant exponent `c`, residue degree `f` and ramification index
`e = ε p ^ w`. LMFDB `lf.heights` defines the height `H(L / K)` by `c = f (e - 1 + H(L / K))`
(`IsNonarchimedeanLocalField.extensionHeight`), so that `H(L / K) = e m` for the mean `m` of
`L / K` (`IsNonarchimedeanLocalField.extensionHeight_eq_mul_extensionMean`). This file proves the
remaining statements of the knowl.

* `H(L / K) = d - (e - 1)` for the different exponent `d` of `L / K`, so that, by Dedekind's
  different theorem, `H(L / K)` is `0` if `L / K` is tamely ramified and positive otherwise.
* `H(L / K)` is the `0`-th index of inseparability `i_0` of `L / K` (LMFDB
  `lf.indices_of_inseparability`). The knowl states this for `L / K` totally ramified; as the
  indices of inseparability of `L / K` are defined through the maximal unramified subextension, it
  holds for every `L / K`.
* For `L` inside `K̄`, with maximal unramified subextension `K_f`, the segments of the ramification
  polygon of `L / K` (LMFDB `lf.ramification_polygon`) correspond to their slopes: `0`, when
  `ε > 1`, and the distinct rams of `L / K`. To the segment of slope `u` corresponds the
  subextension `L^(u)` of `L / K` fixed by the ramification groups of lower index greater than `u`
  (`IsNonarchimedeanLocalField.ramSubextension`): the segment of slope `u` ends at the point
  `(-[L : L^(u)], [L : L^(u)] H(L^(u) / K))`. These subextensions form the tower
  `K_f ⊂ L_1 ⊂ ⋯ ⊂ L_r = L` of the knowl (`IsNonarchimedeanLocalField.ramificationTower`): a chain
  of subextensions of `L` strictly containing `K_f`, which contains `L` exactly when `L / K` is
  ramified. The set of heights of `L / K` is `{H(L_i / K)}`
  (`IsNonarchimedeanLocalField.heightSet`), and it consists of `0`, when `ε > 1`, and of the
  ordinates `ε p ^ k m_k` of the vertices of abscissa `ε p ^ k`, `k ≥ 1`, of the slope polygon of
  LMFDB `lf.means`, for the means `m_k` of `L / K`.

The knowl writes the tower as `K ⊂ L_1 ⊂ ⋯ ⊂ L_r = L`. For `L / K` ramified this holds, with
`K ⊆ K_f ⊂ L_1`. For `L / K` unramified the ramification polygon is a point, there is no segment
and the tower is empty, so that `L_r = L` fails unless `L = K`: the chain starts at `K_f`.

## Main definitions

* `IsNonarchimedeanLocalField.ramificationTower` (LMFDB `lf.heights`): the subextensions of `L / K`
  that correspond to the segments of its ramification polygon.
* `IsNonarchimedeanLocalField.heightSet` (LMFDB `lf.heights`): the set of heights of `L / K`.

## Main results

* `IsNonarchimedeanLocalField.extensionHeight_eq_differentExponent_sub`: `H(L / K) = d - e + 1`.
* `IsNonarchimedeanLocalField.extensionHeight_eq_zero_iff` and
  `IsNonarchimedeanLocalField.extensionHeight_pos_iff` (LMFDB `lf.heights`): `H(L / K)` is `0` if
  `L / K` is tamely ramified, and positive otherwise.
* `IsNonarchimedeanLocalField.inseparabilityIndex_zero_of_tower` and
  `IsNonarchimedeanLocalField.map_inseparabilityIndex_zero` (LMFDB `lf.heights`): `H(L / K)` is the
  index of inseparability `i_0`.
* `IsNonarchimedeanLocalField.edgeEnd_visibleHerbrandInvariant` and
  `IsNonarchimedeanLocalField.mem_polygonEdges_reflectedPolygon_iff_exists_ramSubextension` (LMFDB
  `lf.heights`): the segments of the ramification polygon and the subextensions `L^(u)`.
* `IsNonarchimedeanLocalField.isChain_ramificationTower`,
  `IsNonarchimedeanLocalField.unramifiedExtension_lt_of_mem_ramificationTower` and
  `IsNonarchimedeanLocalField.self_mem_ramificationTower_iff` (LMFDB `lf.heights`): the tower
  `K_f ⊂ L_1 ⊂ ⋯ ⊂ L_r = L`.
* `IsNonarchimedeanLocalField.heightSet_eq` (LMFDB `lf.heights`): the set of heights consists of
  `0`, when `ε > 1`, and of the `ε p ^ k m_k` at the vertices `k ≥ 1`.
* `IsNonarchimedeanLocalField.ramificationTower_eq_of_irreducible`,
  `IsNonarchimedeanLocalField.mem_polygonEdges_ramificationPolygonOf_iff_exists_ramSubextension`
  and `IsNonarchimedeanLocalField.heightSet_eq_of_irreducible` (LMFDB `lf.heights`): the tower,
  its segments and the set of heights through the ramification polygon of `L / K` at a
  uniformiser.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §6, and Chapter IV.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory 8 (2012).
* V. Heiermann, *De nouveaux invariants numériques pour les extensions totalement ramifiées de
  corps locaux*, J. Number Theory 59 (1996).
-/

open ValuativeRel TauCeti

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

section Height

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

/-- **The height through the different**: for a finite separable extension `L / K` of
nonarchimedean local fields, `H(L / K) = d - e + 1`, for the different exponent `d` and the
ramification index `e` of `L / K`. -/
lemma extensionHeight_eq_differentExponent_sub :
    extensionHeight K L = differentExponent K L - ramificationIndex K L + 1 := by
  rw [extensionHeight, discriminantExponent_eq_inertiaDegree_mul_differentExponent, Nat.cast_mul,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr inertiaDegree_pos.ne')]

lemma extensionHeight_nonneg : 0 ≤ extensionHeight K L := by
  have he : 1 ≤ ramificationIndex K L := ramificationIndex_pos
  have h : ramificationIndex K L - 1 ≤ differentExponent K L :=
    ramificationIndex_sub_one_le_differentExponent K L
  have h' : (ramificationIndex K L : ℚ) ≤ differentExponent K L + 1 := by
    exact_mod_cast (by omega : ramificationIndex K L ≤ differentExponent K L + 1)
  rw [extensionHeight_eq_differentExponent_sub]
  linarith

/-- **The height of a tamely ramified extension is `0`** (LMFDB `lf.heights`): for a finite
separable extension `L / K` of nonarchimedean local fields, `H(L / K) = 0` if and only if `L / K`
is tamely ramified, that is the residue characteristic does not divide its ramification index. -/
lemma extensionHeight_eq_zero_iff : extensionHeight K L = 0 ↔ IsTamelyRamified K L := by
  have he : 1 ≤ ramificationIndex K L := ramificationIndex_pos
  rw [extensionHeight_eq_differentExponent_sub,
    ← differentExponent_eq_ramificationIndex_sub_one_iff]
  constructor
  · intro h
    have h' : (differentExponent K L : ℚ) + 1 = ramificationIndex K L := by linarith
    have h'' : differentExponent K L + 1 = ramificationIndex K L := by exact_mod_cast h'
    omega
  · intro h
    rw [h, Nat.cast_sub he, Nat.cast_one]
    ring1

/-- **The height of a wildly ramified extension is positive** (LMFDB `lf.heights`): for a finite
separable extension `L / K` of nonarchimedean local fields, `H(L / K) > 0` if and only if `L / K`
is not tamely ramified. -/
lemma extensionHeight_pos_iff : 0 < extensionHeight K L ↔ ¬IsTamelyRamified K L := by
  rw [← extensionHeight_eq_zero_iff, lt_iff_le_and_ne, ne_comm]
  exact and_iff_right (extensionHeight_nonneg K L)

end Height

/-- **The height is the index of inseparability `i_0`** (LMFDB `lf.heights`): for a finite
extension `L / K` of `p`-adic fields inside a finite Galois extension `M / K`, the `0`-th index of
inseparability of `L / K` is `d - e + 1 = H(L / K)`, for the different exponent `d` and the
ramification index `e` of `L / K`. -/
lemma inseparabilityIndex_zero_of_tower (K : Type*) {L : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [FiniteDimensional K L] (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
    [IsGalois K M] [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
    [IsScalarTower K L M] : inseparabilityIndex K L 0 =
      (((differentExponent K L + 1 - ramificationIndex K L : ℕ) : ℤ) : WithTop ℤ) := by
  have he : ramificationIndex K L - 1 ≤ differentExponent K L :=
    ramificationIndex_sub_one_le_differentExponent K L
  have hd : (differentExponent K L : ℚ) = ramificationIndex K L - 1 + ramificationIndex K L *
      (herbrandInvariantOfTower K M L).mean (herbrandInvariantOfTower K M L).w :=
    natCast_differentExponent_herbrandInvariantOfTower K M L
  have hσ : ((differentExponent K L + 1 - ramificationIndex K L : ℕ) : ℚ) =
      (herbrandInvariantOfTower K M L).ramificationIndex *
        (herbrandInvariantOfTower K M L).mean (herbrandInvariantOfTower K M L).w := by
    rw [Nat.cast_sub (by omega), HerbrandInvariant.ramificationIndex,
      ε_mul_pow_w_herbrandInvariantOfTower K M L]
    push_cast
    linarith
  have h : inseparabilityIndex K L ((herbrandInvariantOfTower K M L).w -
      (herbrandInvariantOfTower K M L).w) =
        (((differentExponent K L + 1 - ramificationIndex K L : ℕ) : ℤ) : WithTop ℤ) :=
    HerbrandInvariant.inseparabilityIndex_eq_of_isVertex M (.refl _) le_rfl (.inl rfl) hσ
  rwa [Nat.sub_self] at h

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] {u : ℚ}
  {L' : IntermediateField K (AlgebraicClosure K)} {σ : Set (ℝ × ℝ)} {π : 𝒪[L]}

variable [CharZero K] in
/-- **The height is the index of inseparability `i_0`, inside `K̄`** (LMFDB `lf.heights`): for a
finite extension `L / K` of `p`-adic fields inside `K̄`, the height `H(L / K)` is the `0`-th index
of inseparability `i_0` of `L / K` (LMFDB `lf.indices_of_inseparability`), which is finite. The
knowl states this for `L / K` totally ramified; the indices of inseparability of `L / K` being
those of `L` over its maximal unramified subextension, it holds for every `L / K`. -/
lemma map_inseparabilityIndex_zero :
    (inseparabilityIndex K L 0).map ((↑) : ℤ → ℚ) = ((extensionHeight K L : ℚ) : WithTop ℚ) := by
  have hLM : L ≤ Algebra.galoisClosure K L := le_galoisClosure L
  let a : Algebra L (Algebra.galoisClosure K L) := (IntermediateField.inclusion hLM).toAlgebra
  have hs : IsScalarTower K L (Algebra.galoisClosure K L) := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension L (Algebra.galoisClosure K L) :=
    (IntermediateField.inclusion hLM).valuativeExtension
  have hf : Module.Finite L (Algebra.galoisClosure K L) := .of_restrictScalars_finite K L _
  have he : ramificationIndex K L - 1 ≤ differentExponent K L :=
    ramificationIndex_sub_one_le_differentExponent K L
  have hq : (((differentExponent K L + 1 - ramificationIndex K L : ℕ) : ℤ) : ℚ) =
      extensionHeight K L := by
    rw [extensionHeight_eq_differentExponent_sub, Int.cast_natCast, Nat.cast_sub (by omega)]
    push_cast
    ring1
  rw [inseparabilityIndex_zero_of_tower K (Algebra.galoisClosure K L), WithTop.map_coe, hq]

/-- The **subextensions that correspond to the segments of the ramification polygon** (LMFDB
`lf.heights`) of a finite extension `L / K` of nonarchimedean local fields inside `K̄`: the
subextensions `L^(u)` of `L / K` (`IsNonarchimedeanLocalField.ramSubextension`) for the slopes `u`
of the segments of the ramification polygon of `L / K`, which are `0`, when the tame degree is not
`1`, and the distinct rams. The ramification polygon is that of the Herbrand invariant of `L / K`,
which is the ramification polygon of `L / K` at any uniformiser
(`IsNonarchimedeanLocalField.ramificationTower_eq_of_irreducible`). They form the tower
`K_f ⊂ L_1 ⊂ ⋯ ⊂ L_r = L` of the knowl, over the maximal unramified subextension `K_f`. -/
noncomputable def ramificationTower : Set (IntermediateField K (AlgebraicClosure K)) :=
  {L' | ∃ u : ℚ, (u : ℝ) ∈ segmentSlopes (visibleHerbrandInvariant L).reflectedPolygon ∧
    L' = ramSubextension L u}

variable [CharZero K] in
/-- **The tower through the ramification polygon at a uniformiser** (LMFDB `lf.heights`): for a
finite extension `L / K` of `p`-adic fields inside `K̄`, with maximal unramified subextension `K'`,
and a uniformiser `π` of `L`, the subextensions that correspond to the segments of the ramification
polygon of `L / K` are the `L^(u)` for the slopes `u` of the segments of the ramification polygon
of `L / K` at `π`, the lower convex hull of the points `(-i, v_L(ρ_i))` of LMFDB
`lf.ramification_polygon`. -/
lemma ramificationTower_eq_of_irreducible (hπ : Irreducible π) : ramificationTower L =
    {L' | ∃ u : ℚ, (u : ℝ) ∈ segmentSlopes (ramificationPolygonOf
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (π : L)) (π : L)) ∧
        L' = ramSubextension L u} := by
  rw [ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant L hπ, ramificationTower]

variable [Algebra.IsSeparable K L]

/-- The **set of heights** (LMFDB `lf.heights`) of a finite separable extension `L / K` of
nonarchimedean local fields inside `K̄`: the heights `H(L_i / K)` of the subextensions `L_i` of
`L / K` that correspond to the segments of the ramification polygon of `L / K`
(`IsNonarchimedeanLocalField.ramificationTower`), that is of the `L^(u)` for the slopes `u` of
these segments. -/
noncomputable def heightSet : Set ℚ :=
  {h | ∃ u : ℚ, (u : ℝ) ∈ segmentSlopes (visibleHerbrandInvariant L).reflectedPolygon ∧
    h = extensionHeight K (ramSubextension L u)}

/-- **The right end of the segment of slope `u`** (LMFDB `lf.heights`): for a finite separable
extension `L / K` inside `K̄` and `u ≥ 0`, the right end of the segment of slope `u` of the
ramification polygon of `L / K` is the point `(-[L : L^(u)], [L : L^(u)] H(L^(u) / K))`. So the
segment that ends at the vertex of abscissa `-x` corresponds to the subextension `L_i` of `L / K`
with `[L : L_i] = x`, and the ordinate of that vertex is `x H(L_i / K)`. -/
lemma edgeEnd_visibleHerbrandInvariant (hu : 0 ≤ u) : (visibleHerbrandInvariant L).edgeEnd u =
    (-(intermediateDegree (ramSubextension_le L u) : ℝ), ((intermediateDegree
      (ramSubextension_le L u) * extensionHeight K (ramSubextension L u) : ℚ) : ℝ)) := by
  have hkw : (visibleHerbrandInvariant L).ramCountLT u +
      (visibleHerbrandInvariant L).ramMultiplicity u ≤ (visibleHerbrandInvariant L).w :=
    (visibleHerbrandInvariant L).ramCountLT_add_ramMultiplicity_le u
  have hpow : (ringChar 𝓀[K] : ℚ) ^ (visibleHerbrandInvariant L).w =
      ringChar 𝓀[K] ^ ((visibleHerbrandInvariant L).w - ((visibleHerbrandInvariant L).ramCountLT u +
        (visibleHerbrandInvariant L).ramMultiplicity u)) *
      ringChar 𝓀[K] ^ ((visibleHerbrandInvariant L).ramCountLT u +
        (visibleHerbrandInvariant L).ramMultiplicity u) := by
    rw [← pow_add, Nat.sub_add_cancel hkw]
  rw [HerbrandInvariant.edgeEnd, intermediateDegree_ramSubextension_le L hu,
    extensionHeight_ramSubextension L hu, HerbrandInvariant.ramificationIndex]
  refine Prod.ext rfl (congrArg ((↑) : ℚ → ℝ) ?_)
  push_cast
  rw [hpow]
  ring1

/-- **The segments of the ramification polygon and the subextensions `L^(u)`** (LMFDB
`lf.heights`): for a finite separable extension `L / K` inside `K̄`, the segments of the
ramification polygon of `L / K` are the segments of slope `u` ending at the point
`(-[L : L^(u)], [L : L^(u)] H(L^(u) / K))`, for the slopes `u` of its segments: to the segment of
slope `u` corresponds the subextension `L^(u)` of `L / K`. -/
lemma mem_polygonEdges_reflectedPolygon_iff_exists_ramSubextension : σ ∈
    polygonEdges (visibleHerbrandInvariant L).reflectedPolygon ↔
      ∃ u : ℚ, (u : ℝ) ∈ segmentSlopes (visibleHerbrandInvariant L).reflectedPolygon ∧
        σ = segment ℝ ((visibleHerbrandInvariant L).edgeStart u)
          (-(intermediateDegree (ramSubextension_le L u) : ℝ), ((intermediateDegree
            (ramSubextension_le L u) * extensionHeight K (ramSubextension L u) : ℚ) : ℝ)) := by
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  rw [(visibleHerbrandInvariant L).mem_polygonEdges_reflectedPolygon_iff_exists]
  exact exists_congr fun u ↦ and_congr_right fun hu ↦ by
    rw [edgeEnd_visibleHerbrandInvariant L
      ((visibleHerbrandInvariant L).nonneg_of_ratCast_mem_segmentSlopes hu)]

variable [CharZero K] in
/-- **The segments of the ramification polygon at a uniformiser and the subextensions `L^(u)`**
(LMFDB `lf.heights`): for a finite extension `L / K` of `p`-adic fields inside `K̄`, with maximal
unramified subextension `K'`, and a uniformiser `π` of `L`, the segments of the ramification
polygon of `L / K` at `π`, the lower convex hull of the points `(-i, v_L(ρ_i))` of LMFDB
`lf.ramification_polygon`, are the segments of slope `u` ending at the point
`(-[L : L^(u)], [L : L^(u)] H(L^(u) / K))`, for the slopes `u` of its segments. -/
lemma mem_polygonEdges_ramificationPolygonOf_iff_exists_ramSubextension (hπ : Irreducible π) : σ ∈
    polygonEdges (ramificationPolygonOf
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (π : L)) (π : L)) ↔
      ∃ u : ℚ, (u : ℝ) ∈ segmentSlopes (ramificationPolygonOf
        (minpoly (unramifiedExtension K L (inertiaDegree K L)) (π : L)) (π : L)) ∧
        σ = segment ℝ ((visibleHerbrandInvariant L).edgeStart u)
          (-(intermediateDegree (ramSubextension_le L u) : ℝ), ((intermediateDegree
            (ramSubextension_le L u) * extensionHeight K (ramSubextension L u) : ℚ) : ℝ)) := by
  rw [ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant L hπ]
  exact mem_polygonEdges_reflectedPolygon_iff_exists_ramSubextension L

lemma le_of_mem_ramificationTower (h : L' ∈ ramificationTower L) : L' ≤ L := by
  rcases h with ⟨u, -, rfl⟩
  exact ramSubextension_le L u

/-- **The tower lies strictly above the maximal unramified subextension** (LMFDB `lf.heights`):
every subextension of a finite separable extension `L / K` inside `K̄` that corresponds to a segment
of its ramification polygon strictly contains the maximal unramified subextension `K_f`, and so
`K`. -/
lemma unramifiedExtension_lt_of_mem_ramificationTower (h : L' ∈ ramificationTower L) :
    unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) < L' := by
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  rcases h with ⟨u, hu, rfl⟩
  exact unramifiedExtension_lt_ramSubextension L
    ((visibleHerbrandInvariant L).nonneg_of_ratCast_mem_segmentSlopes hu)
    ((visibleHerbrandInvariant L).one_lt_ε_mul_pow_of_ratCast_mem_segmentSlopes hu)

/-- **The tower is a chain** (LMFDB `lf.heights`): the subextensions of a finite separable extension
`L / K` inside `K̄` that correspond to the segments of its ramification polygon are totally ordered
by inclusion. Distinct segments give distinct subextensions
(`IsNonarchimedeanLocalField.ramSubextension_lt_ramSubextension`). -/
lemma isChain_ramificationTower : IsChain (· ≤ ·) (ramificationTower L) := by
  rintro _ ⟨u, -, rfl⟩ _ ⟨v, -, rfl⟩ -
  exact (le_total u v).imp (ramSubextension_mono L) (ramSubextension_mono L)

/-- **The tower ends at `L`** (LMFDB `lf.heights`): a finite separable extension `L / K` inside `K̄`
is the largest of its subextensions that correspond to the segments of its ramification polygon,
`L_r = L`, exactly when `L / K` is ramified. For `L / K` unramified there is no segment. -/
lemma self_mem_ramificationTower_iff : L ∈ ramificationTower L ↔ ¬IsUnramified K L := by
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  constructor
  · intro h hur
    refine (unramifiedExtension_lt_of_mem_ramificationTower L h).ne <|
      IntermediateField.eq_of_le_of_finrank_eq (unramifiedExtension_inertiaDegree_le L) ?_
    rw [finrank_unramifiedExtension inertiaDegree_pos.ne',
      ← ramificationIndex_mul_inertiaDegree K L,
      (isUnramified_iff_ramificationIndex_eq_one K L).mp hur, one_mul]
  · intro hur
    have he : (visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^ (visibleHerbrandInvariant L).w ≠ 1 :=
      fun h ↦ hur <| (isUnramified_iff_ramificationIndex_eq_one K L).mpr <|
        (ε_mul_pow_w_visibleHerbrandInvariant L).symm.trans h
    rcases Nat.eq_zero_or_pos (visibleHerbrandInvariant L).w with hw | hw
    · rw [hw, pow_zero, mul_one] at he
      have hε : 1 < (visibleHerbrandInvariant L).ε :=
        lt_of_le_of_ne (visibleHerbrandInvariant L).ε_pos he.symm
      exact ⟨0, (visibleHerbrandInvariant L).ratCast_mem_segmentSlopes_reflectedPolygon_iff.mpr
        (.inl ⟨rfl, hε⟩), (ramSubextension_eq_self L le_rfl (hw ▸ Nat.zero_le _)).symm⟩
    · have hv : (visibleHerbrandInvariant L).IsVertex (visibleHerbrandInvariant L).w := .inl rfl
      exact ⟨_, (visibleHerbrandInvariant L).ratCast_mem_segmentSlopes_reflectedPolygon_iff.mpr
        (.inr (HerbrandInvariant.ram_mem_image hw.ne' le_rfl)),
        (ramSubextension_eq_self L ((visibleHerbrandInvariant L).ram_nonneg _)
          (hv.ramCountLT_add_ramMultiplicity le_rfl).ge).symm⟩

/-- **The set of heights** (LMFDB `lf.heights`): the set of heights of a finite separable extension
`L / K` inside `K̄`, with Herbrand invariant `(r_1, …, r_w)_ε^f` and means `m_k`, consists of `0`,
when `ε > 1` (the height of the maximal tamely ramified subextension), and of the numbers
`ε p ^ k m_k` for the vertices `1 ≤ k ≤ w`, those with `k = w` or `r_k < r_{k + 1}`: the ordinates
of the vertices of abscissa `ε p ^ k` of the slope polygon of LMFDB `lf.means`. -/
lemma heightSet_eq : heightSet L = {h | h = 0 ∧ 1 < (visibleHerbrandInvariant L).ε ∨
    ∃ k ∈ Finset.Icc 1 (visibleHerbrandInvariant L).w, (visibleHerbrandInvariant L).IsVertex k ∧
      h = ((visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^ k : ℕ) *
        (visibleHerbrandInvariant L).mean k} := by
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  have h₀ : extensionHeight K (ramSubextension L 0) = 0 := by
    rw [extensionHeight_ramSubextension L le_rfl, (visibleHerbrandInvariant L).ramCountLT_zero,
      (visibleHerbrandInvariant L).ramMultiplicity_zero, (visibleHerbrandInvariant L).mean_zero,
      mul_zero]
  ext h
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases (visibleHerbrandInvariant L).ratCast_mem_segmentSlopes_reflectedPolygon_iff.mp hu with
      ⟨rfl, hε⟩ | hb
    · exact .inl ⟨h₀, hε⟩
    · have hd : 0 < (visibleHerbrandInvariant L).ramMultiplicity u :=
        (visibleHerbrandInvariant L).ramMultiplicity_pos hb
      exact .inr ⟨_, Finset.mem_Icc.mpr ⟨Nat.add_pos_right _ hd,
        (visibleHerbrandInvariant L).ramCountLT_add_ramMultiplicity_le u⟩,
        (visibleHerbrandInvariant L).isVertex_ramCountLT_add_ramMultiplicity hb,
        extensionHeight_ramSubextension L
          ((visibleHerbrandInvariant L).nonneg_of_ratCast_mem_segmentSlopes hu)⟩
  · rintro (⟨rfl, hε⟩ | ⟨k, hk, hv, rfl⟩)
    · exact ⟨0, (visibleHerbrandInvariant L).ratCast_mem_segmentSlopes_reflectedPolygon_iff.mpr
        (.inl ⟨rfl, hε⟩), h₀.symm⟩
    · exact ⟨_, (visibleHerbrandInvariant L).ratCast_mem_segmentSlopes_reflectedPolygon_iff.mpr
        (.inr (HerbrandInvariant.ram_mem_image (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1)
          (Finset.mem_Icc.mp hk).2)),
        (extensionHeight_ramSubextension_ram L (Finset.mem_Icc.mp hk).2 hv).symm⟩

variable [CharZero K] in
/-- **The set of heights through the ramification polygon at a uniformiser** (LMFDB `lf.heights`):
for a finite extension `L / K` of `p`-adic fields inside `K̄`, with maximal unramified subextension
`K'`, and a uniformiser `π` of `L`, the set of heights of `L / K` consists of the heights of the
`L^(u)` for the slopes `u` of the segments of the ramification polygon of `L / K` at `π`. -/
lemma heightSet_eq_of_irreducible (hπ : Irreducible π) : heightSet L =
    {h | ∃ u : ℚ, (u : ℝ) ∈ segmentSlopes (ramificationPolygonOf
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (π : L)) (π : L)) ∧
        h = extensionHeight K (ramSubextension L u)} := by
  rw [ramificationPolygonOf_minpoly_eq_visibleHerbrandInvariant L hπ, heightSet]

end IsNonarchimedeanLocalField
