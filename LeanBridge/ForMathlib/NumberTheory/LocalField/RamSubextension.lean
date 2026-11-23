import LeanBridge.ForMathlib.NumberTheory.LocalField.CompatibleAdmissible
import LeanBridge.ForMathlib.NumberTheory.LocalField.SlopePolygonMeans

/-!
# The subextensions of an extension of `p`-adic fields cut out by its rams

Let `L / K` be a finite separable extension of nonarchimedean local fields of residue
characteristic `p`, inside `K̄`, with residue degree `f`, ramification index `e = ε p ^ w`, maximal
unramified subextension `K_f` and Herbrand invariant `(r_1, …, r_w)_ε^f`, with means `m_k`. Let `M`
be the Galois closure of `L` in `K̄`, with group `G`, lower ramification groups `G_t` and
`H = Gal(M / L)`, and let `φ_{M/L}(t) = (#H_1 + ⋯ + #H_t) / #H_0` be the Herbrand function of
`M / L`, so that the rams of `L / K` are the `φ_{M/L}(t)`, `t ≥ 1`, at which `[G_t : H ∩ G_t]`
drops.

For `t ≥ 0` the fixed field of `H G_t` is a subextension of `L / K_f`
(`IsNonarchimedeanLocalField.lowerSubextension`), equal to `K_f` for `t = 0` and to `L` for large
`t`. For a rational number `u ≥ 0` let `L^(u)` be the fixed field of `H G_{t + 1}` for the largest
`t` with `φ_{M/L}(t) ≤ u` (`IsNonarchimedeanLocalField.ramSubextension`): the subfield of `L` fixed
by the ramification groups of lower index greater than `u`, in Deligne's lower numbering of
`L / K`. With `k` the number of rams at most `u`, we prove that `[L^(u) : K_f] = ε p ^ k`,
`[L : L^(u)] = p ^ (w - k)`, `[L^(u) : K] = f ε p ^ k`, and that the height of `L^(u) / K` (LMFDB
`lf.heights`) is `ε p ^ k m_k`, the ordinate of the vertex of abscissa `ε p ^ k` of the slope
polygon of LMFDB `lf.means`. In particular, if `r_i < r_{i + 1}` then `L^(r_i)` is an intermediate
field of `L / K` with `[L^(r_i) : K_f] = ε p ^ i`, so that `[L^(r_i) : K] = f ε p ^ i`: this is the
fact of LMFDB `lf.rams`, which states the degree `ε p ^ i` over `K` and so holds as written for
`f = 1` only.

## Main definitions

* `IsNonarchimedeanLocalField.lowerSubextension`: the subextension of `L / K` fixed by `H G_t`.
* `IsNonarchimedeanLocalField.ramSubextension` (LMFDB `lf.rams`, `lf.heights`): the subextension
  `L^(u)` of `L / K` fixed by the ramification groups of lower index greater than `u`.

## Main results

* `IsNonarchimedeanLocalField.extensionHeight_eq_subgroupMeanOrdinate`: the height of a
  subextension of `L / K` containing `K_f` is the ordinate of its point in the slope polygon of
  LMFDB `lf.means`.
* `IsNonarchimedeanLocalField.relfinrank_ramSubextension`: `[L^(u) : K_f] = ε p ^ k`.
* `IsNonarchimedeanLocalField.relfinrank_ramSubextension_le`: `[L : L^(u)] = p ^ (w - k)`.
* `IsNonarchimedeanLocalField.finrank_ramSubextension`: `[L^(u) : K] = f ε p ^ k`.
* `IsNonarchimedeanLocalField.extensionHeight_ramSubextension` (LMFDB `lf.heights`):
  `H(L^(u) / K) = ε p ^ k m_k`.
* `IsNonarchimedeanLocalField.ramSubextension_lt_ramSubextension`: the subextensions `L^(u)` grow
  strictly at the rams.
* `IsNonarchimedeanLocalField.relfinrank_ramSubextension_ram` and
  `IsNonarchimedeanLocalField.finrank_ramSubextension_of_ram_lt` (LMFDB `lf.rams`): if
  `r_i < r_{i + 1}` then `L / K` has an intermediate field `L_i` with `[L_i : K_f] = ε p ^ i` and
  `[L_i : K] = f ε p ^ i`.
* `IsNonarchimedeanLocalField.relfinrank_ramSubextension_ram_le` and
  `IsNonarchimedeanLocalField.extensionHeight_ramSubextension_ram` (LMFDB `lf.heights`): at a
  vertex `k`, `[L : L_k] = p ^ (w - k)` and `H(L_k / K) = ε p ^ k m_k`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  appendix.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory 8 (2012).
-/

open ValuativeRel TauCeti LocalFieldsRamification Set

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] (t : ℕ) (u : ℚ)

/-- The **subextension fixed by `H G_t`** of a finite extension `L / K` of nonarchimedean local
fields inside `K̄`: with `M` the Galois closure of `L` in `K̄`, `G_t` the `t`-th lower ramification
group of `M / K` and `H = Gal(M / L)`, the fixed field of `H G_t`. It lies between the maximal
unramified subextension `K_f`, which it is for `t = 0`, and `L`, which it is for large `t`. -/
noncomputable def lowerSubextension : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.lift (IntermediateField.fixedField
    (fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
        lowerRamificationGroup K (Algebra.galoisClosure K L) t))

/-- The **subextension `L^(u)` cut out by the rams at most `u`** (LMFDB `lf.rams`, `lf.heights`) of
a finite extension `L / K` of nonarchimedean local fields inside `K̄`, for a rational number `u`:
with `M` the Galois closure of `L` in `K̄`, `G_t` the lower ramification groups of `M / K`,
`H = Gal(M / L)` and `φ_{M/L}` the Herbrand function of `M / L`, the fixed field of `H G_{t + 1}`
for the largest `t` with `φ_{M/L}(t) ≤ u`. It is the subfield of `L` fixed by the ramification
groups of lower index greater than `u`, in Deligne's lower numbering of `L / K`; for `u ≥ 0` its
degree over the maximal unramified subextension `K_f` is `ε p ^ k`, with `k` the number of rams of
`L / K` at most `u` (`IsNonarchimedeanLocalField.relfinrank_ramSubextension`). So `L^(0)` is
the maximal tamely ramified subextension, and `L^(u) = L` when `u` is at least the largest ram. -/
noncomputable def ramSubextension : IntermediateField K (AlgebraicClosure K) :=
  lowerSubextension L (Nat.findGreatest (fun t ↦ herbrandOfSubgroup K (Algebra.galoisClosure K L)
    (fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) t ≤ u)
    (largestLowerJump K (Algebra.galoisClosure K L)).toNat + 1)

lemma fixingSubgroup_lowerSubextension :
    fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' lowerSubextension L t) =
      fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
        lowerRamificationGroup K (Algebra.galoisClosure K L) t :=
  fixingSubgroup_preimage_lift_fixedField _

variable {u} in
lemma countP_le_herbrandOfSubgroup_findGreatest (hu : 0 ≤ u) :
    (visibleRams L).countP (· ≤ herbrandOfSubgroup K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
      (Nat.findGreatest (fun t ↦ herbrandOfSubgroup K (Algebra.galoisClosure K L)
        (fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
          (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) t ≤ u)
        (largestLowerJump K (Algebra.galoisClosure K L)).toNat)) =
      (visibleHerbrandInvariant L).ramCountLT u + (visibleHerbrandInvariant L).ramMultiplicity u :=
  (countP_le_ramsOfSubgroup K _ _ hu).symm.trans <|
    HerbrandInvariant.countP_le_ofRams _ _ _ _ _ _ _ hu

variable [Algebra.IsSeparable K L]

lemma lowerSubextension_le : lowerSubextension L t ≤ L :=
  lift_fixedField_le (Algebra.le_galoisClosure L) le_sup_left

lemma unramifiedExtension_le_lowerSubextension :
    unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) ≤ lowerSubextension L t :=
  le_lift_fixedField ((unramifiedExtension_inertiaDegree_le L).trans (Algebra.le_galoisClosure L))
    ((sup_lowerRamificationGroup_le_sup_zero _ t).trans (fixingSubgroup_unramifiedExtension L).ge)

lemma ramSubextension_le : ramSubextension L u ≤ L :=
  lowerSubextension_le L _

lemma unramifiedExtension_le_ramSubextension :
    unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) ≤ ramSubextension L u :=
  unramifiedExtension_le_lowerSubextension L _

instance : FiniteDimensional K (lowerSubextension L t) :=
  IntermediateField.finiteDimensional_of_le (lowerSubextension_le L t)

instance : Algebra.IsSeparable K (lowerSubextension L t) :=
  IntermediateField.isSeparable_of_le (lowerSubextension_le L t)

instance : FiniteDimensional K (ramSubextension L u) :=
  IntermediateField.finiteDimensional_of_le (ramSubextension_le L u)

instance : Algebra.IsSeparable K (ramSubextension L u) :=
  IntermediateField.isSeparable_of_le (ramSubextension_le L u)

lemma lowerSubextension_mono {s : ℕ} (h : s ≤ t) : lowerSubextension L s ≤ lowerSubextension L t :=
  le_lift_fixedField ((lowerSubextension_le L s).trans (Algebra.le_galoisClosure L)) <|
    (sup_le_sup_left (lowerRamificationGroup_antitone K _ (Nat.cast_le.mpr h)) _).trans
      (fixingSubgroup_lowerSubextension L s).ge

lemma relfinrank_lowerSubextension_le : (lowerSubextension L t).relfinrank L =
    (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)).relIndex
      (lowerRamificationGroup K (Algebra.galoisClosure K L) t) := by
  rw [relfinrank_eq_relIndex (lowerSubextension_le L t) (Algebra.le_galoisClosure L),
    fixingSubgroup_lowerSubextension, Subgroup.relIndex_sup_of_normal]

lemma relfinrank_unramifiedExtension_le_lowerSubextension :
    (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)).relfinrank
      (lowerSubextension L t) = subgroupMeanAbscissa K (Algebra.galoisClosure K L)
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
          lowerRamificationGroup K (Algebra.galoisClosure K L) t) := by
  rw [relfinrank_eq_subgroupMeanAbscissa L (unramifiedExtension_le_lowerSubextension L t)
    (lowerSubextension_le L t), fixingSubgroup_lowerSubextension]

variable {L' : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K L']
  [Algebra.IsSeparable K L'] in
/-- **The height of a subextension is the ordinate of its point in the slope polygon** (LMFDB
`lf.heights`, `lf.means`): for a finite separable extension `L / K` inside `K̄` with maximal
unramified subextension `K_f`, and a subextension `K_f ⊆ L' ⊆ L` with group `J = Gal(M / L')` in
the Galois closure `M` of `L`, the height `H(L' / K)` is `c(J) / f - [L' : K_f] + 1`, the ordinate
`e' m'` of the point of `L'` in the slope polygon of LMFDB `lf.means`. -/
lemma extensionHeight_eq_subgroupMeanOrdinate
    (h : unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) ≤ L') (hL' : L' ≤ L) :
    extensionHeight K L' = subgroupMeanOrdinate K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L')) := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  set H : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)
  set J : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L')
  have hHJ : H ≤ J := fixingSubgroup_antitone _ _ (preimage_mono hL')
  have hJ : J ≤ H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0 := by
    rw [← fixingSubgroup_unramifiedExtension L]
    exact fixingSubgroup_antitone _ _ (preimage_mono h)
  have hJ' : J ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0 =
      H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0 :=
    (sup_le hJ le_sup_right).antisymm (sup_le_sup_right hHJ _)
  have hc : (discriminantExponent K L' : ℚ) =
      subgroupDiscriminantExponent K (Algebra.galoisClosure K L) J :=
    natCast_discriminantExponent_eq_subgroupDiscriminantExponent_fixingSubgroup (hL'.trans hLM)
  have he : J.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0) =
      ramificationIndex K L' :=
    relIndex_lowerRamificationGroup_zero_fixingSubgroup (hL'.trans hLM)
  have hf :
      inertiaDegree K L' = (H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) 0).index := by
    refine Nat.eq_of_mul_eq_mul_left (ramificationIndex_pos (K := K) (L := L')) ?_
    rw [ramificationIndex_mul_inertiaDegree K L', finrank_eq_index_fixingSubgroup (hL'.trans hLM),
      ← hJ', ← he, mul_comm]
    exact (index_sup_mul_relIndex J 0).symm
  have ha : subgroupMeanAbscissa K (Algebra.galoisClosure K L) H J = ramificationIndex K L' := by
    rw [subgroupMeanAbscissa, ← hJ', Subgroup.relIndex_sup_of_normal, he]
  rw [extensionHeight, subgroupMeanOrdinate, hc, hf, ha]

lemma subgroupMeanOrdinate_sup_succ
    (ht : t ≤ (largestLowerJump K (Algebra.galoisClosure K L)).toNat) :
    subgroupMeanOrdinate K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L) ⊔
        lowerRamificationGroup K (Algebra.galoisClosure K L) (t + 1 : ℕ)) =
      (tameDegree K L * ringChar 𝓀[K] ^ (visibleRams L).countP (· ≤ herbrandOfSubgroup K
        (Algebra.galoisClosure K L)
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) t) : ℕ) *
      (visibleHerbrandInvariant L).mean ((visibleRams L).countP (· ≤ herbrandOfSubgroup K
        (Algebra.galoisClosure K L)
        (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) t)) := by
  have hLM : L ≤ Algebra.galoisClosure K L := Algebra.le_galoisClosure L
  set H : Subgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L) :=
    fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)
  set k : ℕ := (visibleRams L).countP (· ≤ herbrandOfSubgroup K (Algebra.galoisClosure K L) H t)
  have hS : IsLowerHullVertices (subgroupMeanPoints K (Algebra.galoisClosure K L) H)
      (largestLowerJump K (Algebra.galoisClosure K L)).toNat
      (fun s ↦ subgroupMeanAbscissa K _ H (H ⊔ lowerRamificationGroup K _ s))
      (fun s ↦ (subgroupMeanOrdinate K _ H (H ⊔ lowerRamificationGroup K _ s) : ℝ))
      (fun s ↦ (subgroupSlope K (Algebra.galoisClosure K L) (s + 1) - 1 : ℚ)) :=
    isLowerHullVertices_subgroupMeanPoints H
  have he :
      H.relIndex (lowerRamificationGroup K (Algebra.galoisClosure K L) 0) = ramificationIndex K L :=
    relIndex_lowerRamificationGroup_zero_fixingSubgroup hLM
  have hn : subgroupMeanAbscissa K (Algebra.galoisClosure K L) H
      (H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) (t + 1 : ℕ)) =
        tameDegree K L * ringChar 𝓀[K] ^ k := by
    rw [subgroupMeanAbscissa_sup_succ H t, he]
    rfl
  have hkw : k ≤ (visibleHerbrandInvariant L).w := Multiset.countP_le_card _ _
  have hx₁ : (1 : ℝ) ≤ (tameDegree K L * ringChar 𝓀[K] ^ k : ℕ) := by
    rw [← hn]
    exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  have hx₂ : ((tameDegree K L * ringChar 𝓀[K] ^ k : ℕ) : ℝ) ≤ ramificationIndex K L := by
    rw [← hn, ← subgroupMeanAbscissa_largestLowerJump L]
    exact Nat.cast_le.mpr (hS.le_of_le (Nat.succ_le_succ ht) le_rfl)
  have hfun : meanPolygonFunction L (tameDegree K L * ringChar 𝓀[K] ^ k : ℕ) =
      (subgroupMeanOrdinate K (Algebra.galoisClosure K L) H
        (H ⊔ lowerRamificationGroup K (Algebra.galoisClosure K L) (t + 1 : ℕ)) : ℝ) := by
    rw [meanPolygonFunction_eq L ⟨hx₁, hx₂⟩, ← hn,
      hS.vertexPolygon_eq ht ⟨Nat.cast_le.mpr (hS.le_succ t ht), le_rfl⟩]
    exact (hS.eq_add_mul t ht).symm
  have hmean : meanPolygonFunction L (tameDegree K L * ringChar 𝓀[K] ^ k : ℕ) /
      (tameDegree K L * ringChar 𝓀[K] ^ k : ℕ) = ((visibleHerbrandInvariant L).mean k : ℝ) :=
    polygonMean_eq_mean L hkw
  rw [div_eq_iff (by linarith), hfun] at hmean
  refine Rat.cast_injective (α := ℝ) ?_
  rw [hmean]
  push_cast
  ring1

variable {u} {v : ℚ}

/-- **The degree of `L^(u)` over the maximal unramified subextension**: for a finite separable
extension `L / K` inside `K̄` with ramification index `ε p ^ w` and maximal unramified subextension
`K_f`, and `u ≥ 0`, `[L^(u) : K_f] = ε p ^ k`, where `k` is the number of rams of `L / K` at most
`u`: the sum of the number of rams smaller than `u` and of the multiplicity of `u`. -/
lemma relfinrank_ramSubextension (hu : 0 ≤ u) :
    (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)).relfinrank
      (ramSubextension L u) = (visibleHerbrandInvariant L).ε *
        ringChar 𝓀[K] ^ ((visibleHerbrandInvariant L).ramCountLT u +
          (visibleHerbrandInvariant L).ramMultiplicity u) := by
  have he : (fixingSubgroup (Algebra.galoisClosure K L ≃ₐ[K] Algebra.galoisClosure K L)
      (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)).relIndex
        (lowerRamificationGroup K (Algebra.galoisClosure K L) 0) = ramificationIndex K L :=
    relIndex_lowerRamificationGroup_zero_fixingSubgroup (Algebra.le_galoisClosure L)
  refine (relfinrank_unramifiedExtension_le_lowerSubextension L _).trans ?_
  rw [subgroupMeanAbscissa_sup_succ, he]
  exact congrArg (fun k ↦ tameDegree K L * ringChar 𝓀[K] ^ k)
    (countP_le_herbrandOfSubgroup_findGreatest L hu)

/-- **The degree of `L` over `L^(u)`**: for a finite separable extension `L / K` inside `K̄` with
ramification index `ε p ^ w`, and `u ≥ 0`, `[L : L^(u)] = p ^ (w - k)`, where `k` is the number of
rams of `L / K` at most `u`. -/
lemma relfinrank_ramSubextension_le (hu : 0 ≤ u) : (ramSubextension L u).relfinrank L =
    ringChar 𝓀[K] ^ ((visibleHerbrandInvariant L).w - ((visibleHerbrandInvariant L).ramCountLT u +
      (visibleHerbrandInvariant L).ramMultiplicity u)) := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  have hkw : (visibleHerbrandInvariant L).ramCountLT u +
      (visibleHerbrandInvariant L).ramMultiplicity u ≤ (visibleHerbrandInvariant L).w :=
    (visibleHerbrandInvariant L).ramCountLT_add_ramMultiplicity_le u
  refine (relfinrank_lowerSubextension_le L _).trans <|
    Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos ((visibleHerbrandInvariant L).ramCountLT u +
      (visibleHerbrandInvariant L).ramMultiplicity u)) ?_
  rw [← pow_add, Nat.sub_add_cancel hkw, ← countP_le_herbrandOfSubgroup_findGreatest L hu]
  exact relIndex_mul_pow_countP _ _

/-- **The degree of `L^(u)` over `K`**: for a finite separable extension `L / K` inside `K̄` with
residue degree `f` and ramification index `ε p ^ w`, and `u ≥ 0`, `[L^(u) : K] = f ε p ^ k`, where
`k` is the number of rams of `L / K` at most `u`. -/
lemma finrank_ramSubextension (hu : 0 ≤ u) : Module.finrank K (ramSubextension L u) =
    inertiaDegree K L * ((visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^
      ((visibleHerbrandInvariant L).ramCountLT u +
        (visibleHerbrandInvariant L).ramMultiplicity u)) := by
  rw [← IntermediateField.finrank_bot_mul_relfinrank (unramifiedExtension_le_ramSubextension L u),
    finrank_unramifiedExtension inertiaDegree_pos.ne', relfinrank_ramSubextension L hu]

/-- **The height of `L^(u)`** (LMFDB `lf.heights`): for a finite separable extension `L / K` inside
`K̄` with Herbrand invariant `(r_1, …, r_w)_ε^f` and means `m_k`, and `u ≥ 0`, the height of
`L^(u) / K` is `ε p ^ k m_k`, where `k` is the number of rams of `L / K` at most `u`: the ordinate
of the vertex of abscissa `ε p ^ k` of the slope polygon of LMFDB `lf.means`. -/
lemma extensionHeight_ramSubextension (hu : 0 ≤ u) : extensionHeight K (ramSubextension L u) =
    ((visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^ ((visibleHerbrandInvariant L).ramCountLT u +
      (visibleHerbrandInvariant L).ramMultiplicity u) : ℕ) *
      (visibleHerbrandInvariant L).mean ((visibleHerbrandInvariant L).ramCountLT u +
        (visibleHerbrandInvariant L).ramMultiplicity u) := by
  rw [extensionHeight_eq_subgroupMeanOrdinate L (unramifiedExtension_le_ramSubextension L u)
    (ramSubextension_le L u), ← countP_le_herbrandOfSubgroup_findGreatest L hu]
  exact (congrArg (subgroupMeanOrdinate K (Algebra.galoisClosure K L) _)
    (fixingSubgroup_lowerSubextension L _)).trans
      (subgroupMeanOrdinate_sup_succ L _ (Nat.findGreatest_le _))

lemma ramSubextension_mono (h : u ≤ v) : ramSubextension L u ≤ ramSubextension L v :=
  lowerSubextension_mono L _ <| Nat.succ_le_succ <|
    Nat.findGreatest_mono_left (fun _ ht ↦ ht.trans h) _

lemma ramSubextension_eq_self (hu : 0 ≤ u) (hk : (visibleHerbrandInvariant L).w ≤
    (visibleHerbrandInvariant L).ramCountLT u + (visibleHerbrandInvariant L).ramMultiplicity u) :
    ramSubextension L u = L := by
  refine IntermediateField.eq_of_le_of_finrank_eq (ramSubextension_le L u) ?_
  rw [← IntermediateField.finrank_bot_mul_relfinrank (ramSubextension_le L u),
    relfinrank_ramSubextension_le L hu, Nat.sub_eq_zero_of_le hk, pow_zero, mul_one]

/-- **The subextensions `L^(u)` grow strictly at the rams**: for a finite separable extension
`L / K` inside `K̄`, `0 ≤ u < v` and `v` a ram of `L / K`, `L^(u)` is strictly contained in
`L^(v)`. -/
lemma ramSubextension_lt_ramSubextension (hu : 0 ≤ u) (huv : u < v) (hv : v ∈
    (Finset.Icc 1 (visibleHerbrandInvariant L).w).image (visibleHerbrandInvariant L).ram) :
    ramSubextension L u < ramSubextension L v := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  have hd : 0 < (visibleHerbrandInvariant L).ramMultiplicity v :=
    (visibleHerbrandInvariant L).ramMultiplicity_pos hv
  have hle : (visibleHerbrandInvariant L).ramCountLT u +
      (visibleHerbrandInvariant L).ramMultiplicity u ≤ (visibleHerbrandInvariant L).ramCountLT v :=
    ((visibleHerbrandInvariant L).card_filter_ram_le u).symm.trans_le <|
      Finset.card_le_card <| Finset.monotone_filter_right _ fun _ _ hj ↦ hj.trans_lt huv
  refine (ramSubextension_mono L huv.le).lt_of_ne fun heq ↦ ?_
  have hfin : Module.finrank K (ramSubextension L u) = Module.finrank K (ramSubextension L v) :=
    congrArg (fun E : IntermediateField K (AlgebraicClosure K) ↦ Module.finrank K E) heq
  rw [finrank_ramSubextension L hu, finrank_ramSubextension L (hu.trans huv.le)] at hfin
  have hpow : ringChar 𝓀[K] ^ ((visibleHerbrandInvariant L).ramCountLT u +
      (visibleHerbrandInvariant L).ramMultiplicity u) =
      ringChar 𝓀[K] ^ ((visibleHerbrandInvariant L).ramCountLT v +
        (visibleHerbrandInvariant L).ramMultiplicity v) :=
    Nat.eq_of_mul_eq_mul_left (visibleHerbrandInvariant L).ε_pos <|
      Nat.eq_of_mul_eq_mul_left inertiaDegree_pos hfin
  have hk : (visibleHerbrandInvariant L).ramCountLT u +
      (visibleHerbrandInvariant L).ramMultiplicity u =
      (visibleHerbrandInvariant L).ramCountLT v + (visibleHerbrandInvariant L).ramMultiplicity v :=
    Nat.pow_right_injective hp.two_le hpow
  omega

lemma unramifiedExtension_lt_ramSubextension (hu : 0 ≤ u)
    (h : 1 < (visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^
      ((visibleHerbrandInvariant L).ramCountLT u +
        (visibleHerbrandInvariant L).ramMultiplicity u)) :
    unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L) < ramSubextension L u := by
  refine (unramifiedExtension_le_ramSubextension L u).lt_of_ne fun heq ↦ h.ne' ?_
  have hfin : Module.finrank K (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)) =
      Module.finrank K (ramSubextension L u) :=
    congrArg (fun E : IntermediateField K (AlgebraicClosure K) ↦ Module.finrank K E) heq
  rw [finrank_unramifiedExtension inertiaDegree_pos.ne', finrank_ramSubextension L hu] at hfin
  exact Nat.eq_of_mul_eq_mul_left inertiaDegree_pos (hfin.symm.trans (mul_one _).symm)

variable {k : ℕ}

/-- **The intermediate fields at the strict increases of the rams** (LMFDB `lf.rams`): let `L / K`
be a finite separable extension inside `K̄` with Herbrand invariant `(r_1, …, r_w)_ε^f` and maximal
unramified subextension `K_f`, and `k ≤ w` a vertex, that is `k = w` or `r_k < r_{k + 1}`. Then the
intermediate field `L_k = L^(r_k)` of `L / K` has `[L_k : K_f] = ε p ^ k`. -/
lemma relfinrank_ramSubextension_ram (hk : k ≤ (visibleHerbrandInvariant L).w)
    (hv : (visibleHerbrandInvariant L).IsVertex k) :
    (unramifiedExtension K (AlgebraicClosure K) (inertiaDegree K L)).relfinrank
      (ramSubextension L ((visibleHerbrandInvariant L).ram k)) =
        (visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^ k := by
  rw [relfinrank_ramSubextension L ((visibleHerbrandInvariant L).ram_nonneg k),
    hv.ramCountLT_add_ramMultiplicity hk]

/-- **The degree over `L_k`**: for a vertex `k ≤ w` of the Herbrand invariant of a finite separable
extension `L / K` inside `K̄`, `[L : L_k] = p ^ (w - k)` for `L_k = L^(r_k)`. -/
lemma relfinrank_ramSubextension_ram_le (hk : k ≤ (visibleHerbrandInvariant L).w)
    (hv : (visibleHerbrandInvariant L).IsVertex k) :
    (ramSubextension L ((visibleHerbrandInvariant L).ram k)).relfinrank L =
      ringChar 𝓀[K] ^ ((visibleHerbrandInvariant L).w - k) := by
  rw [relfinrank_ramSubextension_le L ((visibleHerbrandInvariant L).ram_nonneg k),
    hv.ramCountLT_add_ramMultiplicity hk]

/-- **The heights of the intermediate fields at the vertices** (LMFDB `lf.heights`): for a vertex
`k ≤ w` of the Herbrand invariant `(r_1, …, r_w)_ε^f` of a finite separable extension `L / K`
inside `K̄`, the height of `L_k = L^(r_k)` over `K` is `ε p ^ k m_k`, for the mean `m_k`. -/
lemma extensionHeight_ramSubextension_ram (hk : k ≤ (visibleHerbrandInvariant L).w)
    (hv : (visibleHerbrandInvariant L).IsVertex k) :
    extensionHeight K (ramSubextension L ((visibleHerbrandInvariant L).ram k)) =
      ((visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^ k : ℕ) *
        (visibleHerbrandInvariant L).mean k := by
  rw [extensionHeight_ramSubextension L ((visibleHerbrandInvariant L).ram_nonneg k),
    hv.ramCountLT_add_ramMultiplicity hk]

/-- **The intermediate field at a strict increase of the rams** (LMFDB `lf.rams`, with the degree
corrected): if the rams `r_1 ≤ ⋯ ≤ r_w` of a finite separable extension `L / K` inside `K̄`, of
residue degree `f` and ramification index `ε p ^ w`, satisfy `r_i < r_{i + 1}`, then `L / K` has an
intermediate field `L_i`, namely `L^(r_i)`, with `[L_i : K] = f ε p ^ i`. LMFDB `lf.rams` states
`[L_i : K] = ε p ^ i`, which this gives for `f = 1`; for `f > 1` no intermediate field of degree
`ε p ^ i` over `K` need exist. -/
lemma finrank_ramSubextension_of_ram_lt
    (hk : (visibleHerbrandInvariant L).ram k < (visibleHerbrandInvariant L).ram (k + 1)) :
    Module.finrank K (ramSubextension L ((visibleHerbrandInvariant L).ram k)) =
      inertiaDegree K L * ((visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^ k) := by
  have hkw : k ≤ (visibleHerbrandInvariant L).w := not_lt.mp fun h ↦ hk.ne <|
    ((visibleHerbrandInvariant L).ram_of_le k h.le).trans
      ((visibleHerbrandInvariant L).ram_of_le (k + 1) (Nat.le_succ_of_le h.le)).symm
  have hv : (visibleHerbrandInvariant L).IsVertex k := .inr hk
  rw [finrank_ramSubextension L ((visibleHerbrandInvariant L).ram_nonneg k),
    hv.ramCountLT_add_ramMultiplicity hkw]

end IsNonarchimedeanLocalField
