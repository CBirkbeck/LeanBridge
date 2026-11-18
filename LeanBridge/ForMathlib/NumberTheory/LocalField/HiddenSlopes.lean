import LeanBridge.ForMathlib.NumberTheory.LocalField.SubextensionSlopes
import Mathlib.Algebra.Order.Sub.Unbundled.Hom

/-!
# The hidden slopes of an extension of `p`-adic fields

Let `L / K` be a finite separable extension of nonarchimedean local fields of residue
characteristic `p`, inside `K̄`, and let `L^Gal` be its Galois closure in `K̄`. LMFDB
`lf.hidden_slopes` calls the multiset `S^Gal` of the Swan slopes of `L^Gal / K` the Galois Swan
slopes of `L / K` (`IsNonarchimedeanLocalField.galoisSwanSlopes`), and the multiset `H` obtained by
subtracting the multiset `S` of the Swan slopes of `L / K` from `S^Gal` its hidden Swan slopes
(`IsNonarchimedeanLocalField.hiddenSwanSlopes`); the Galois Artin slopes and the hidden Artin slopes
are defined in the same way from the Artin slopes. LMFDB `lf.visible_slopes` calls the slopes of
`L / K` itself its visible slopes.

The slopes are the wild ones, each with its multiplicity
(`IsNonarchimedeanLocalField.hullWildSwanSlopes` and
`IsNonarchimedeanLocalField.hullWildArtinSlopes`, LMFDB `lf.slopes`): the visible Artin slopes of
LMFDB `lf.visible_slopes` are the slopes greater than one, and the LMFDB lists the Galois, visible
and hidden slopes of a field in this way, keeping the residue degrees and the tame degrees of
`L / K` and `L^Gal / K` apart from the slopes. The knowls state that `S^Gal` is the multiset sum of
`S` and `H`, and that the list of visible Artin slopes is a subset of the list of wild Artin slopes
of the Galois closure: `S` is a sub-multiset of `S^Gal`. This is the theorem on the slopes of a
subextension, applied to `L ⊆ L^Gal`. Let `G` be the group of `L^Gal / K`, with lower ramification
groups `G_i` and Herbrand function `φ`, and let `Γ = Gal(L^Gal / L)`, with lower ramification
groups `Γ_i = Γ ∩ G_i`. The Swan slope `φ(i)`, `i ≥ 1`, has multiplicity `v_p([G_i : G_{i + 1}])`
in `S^Gal` and `v_p([G_i : Γ_i] / [G_{i + 1} : Γ_{i + 1}])` in `S`, and
`[G_i : G_{i + 1}] = ([G_i : Γ_i] / [G_{i + 1} : Γ_{i + 1}]) [Γ_i : Γ_{i + 1}]`. So the hidden Swan
slopes are the `φ(i)`, `i ≥ 1`, each repeated `v_p([Γ_i : Γ_{i + 1}])` times
(`IsNonarchimedeanLocalField.hiddenSwanSlopesOfSubgroup`).

LMFDB `lf.slopes` calls the slope of every segment of its polygon an Artin slope, the slopes `0`
and `1` of the segments that are not wild included. With these slopes counted once each, `S` is
still a sub-multiset of `S^Gal`, so the statements of LMFDB `lf.hidden_slopes` hold for either
list.

## Main definitions

* `IsNonarchimedeanLocalField.galoisSwanSlopes` and `IsNonarchimedeanLocalField.galoisArtinSlopes`
  (LMFDB `lf.hidden_slopes`): the Galois Swan slopes `S^Gal` and the Galois Artin slopes.
* `IsNonarchimedeanLocalField.hiddenSwanSlopes` and `IsNonarchimedeanLocalField.hiddenArtinSlopes`
  (LMFDB `lf.hidden_slopes`, `lf.visible_slopes`): the hidden Swan slopes `H` and the hidden Artin
  slopes.
* `IsNonarchimedeanLocalField.hiddenSwanSlopesOfSubgroup`: the hidden Swan slopes of the fixed
  field of a subgroup of the group of a Galois extension.

## Main results

* `IsNonarchimedeanLocalField.swanSlopesOfSubgroup_add_hiddenSwanSlopesOfSubgroup`: the Swan slopes
  of a Galois extension `M / K` are those of the fixed field of a subgroup `Γ` together with the
  `φ(i)` repeated `v_p([Γ ∩ G_i : Γ ∩ G_{i + 1}])` times.
* `IsNonarchimedeanLocalField.galoisSwanSlopes_eq_swanSlopes` and
  `IsNonarchimedeanLocalField.galoisArtinSlopes_eq_wildArtinSlopes`: the Galois slopes are the
  slopes of the ramification filtration of the group of the Galois closure (LMFDB
  `lf.slope_content`).
* `IsNonarchimedeanLocalField.hullWildSwanSlopes_le_galoisSwanSlopes` and
  `IsNonarchimedeanLocalField.hullWildSwanSlopes_add_hiddenSwanSlopes` (LMFDB `lf.hidden_slopes`):
  `S` is a sub-multiset of `S^Gal`, and `S^Gal` is the multiset sum of `S` and `H`.
* `IsNonarchimedeanLocalField.hullWildArtinSlopes_le_galoisArtinSlopes` and
  `IsNonarchimedeanLocalField.hullWildArtinSlopes_add_hiddenArtinSlopes` (LMFDB
  `lf.hidden_slopes`): the same for the Artin slopes.
* `IsNonarchimedeanLocalField.map_add_one_galoisSwanSlopes` and
  `IsNonarchimedeanLocalField.map_add_one_hiddenSwanSlopes` (LMFDB `lf.hidden_slopes`): the Galois
  Artin slopes and the hidden Artin slopes are the corresponding Swan slopes plus `1`.
* `IsNonarchimedeanLocalField.hiddenSwanSlopes_eq_hiddenSwanSlopesOfSubgroup`: the hidden Swan
  slopes are the `φ(i)`, each repeated `v_p([Γ_i : Γ_{i + 1}])` times.
* `IsNonarchimedeanLocalField.hiddenSwanSlopes_of_normal`: a normal extension has no hidden slope.
* `IsNonarchimedeanLocalField.inertiaDegree_dvd_galoisUnramifiedDegree` and
  `IsNonarchimedeanLocalField.tameDegree_dvd_galoisTameDegree`: the residue degree and the tame
  degree divide the Galois unramified degree and the Galois tame degree.
* `IsNonarchimedeanLocalField.hullSwanSlopeMultiset_le_galoisClosure`,
  `IsNonarchimedeanLocalField.hullSwanSlopeMultiset_add_galoisClosure_sub` and
  `IsNonarchimedeanLocalField.map_add_one_hullSwanSlopeMultiset_sub` (LMFDB `lf.hidden_slopes`):
  the statements of the knowl for the multisets of all the slopes.
* `IsNonarchimedeanLocalField.hullSwanSlopeMultiset_galoisClosure_sub` (LMFDB
  `lf.hidden_slopes`): with all the slopes counted, the hidden Swan slopes are those above
  together with `-1` if `f = 1 < f^Gal` and with `0` if `ε = 1 < ε^Gal`.
* `IsNonarchimedeanLocalField.count_hullWildArtinSlopes`,
  `IsNonarchimedeanLocalField.count_hullWildArtinSlopes_of_mem_polygonEdgesWithSlope` and
  `IsNonarchimedeanLocalField.slopeMultiplicity_pos` (LMFDB `lf.visible_slopes`): the slope of a
  wild segment from `(n₁, c₁)` to `(n₂, c₂)`, with `n₂ / n₁ = p ^ k`, is listed `k` times, and
  `k ≥ 1`.
* `IsNonarchimedeanLocalField.hullWildArtinSlopes_eq_wildArtinSlopesOfIsGalois` (LMFDB
  `lf.visible_slopes`): the visible Artin slopes of a Galois extension are its wild Artin slopes.
* `IsNonarchimedeanLocalField.hullWildArtinSlopes_le_wildArtinSlopes` (LMFDB `lf.visible_slopes`):
  the visible Artin slopes form a sub-multiset of the wild Artin slopes of the Galois closure.
* `IsNonarchimedeanLocalField.hiddenArtinSlopes_eq_wildArtinSlopes_sub` and
  `IsNonarchimedeanLocalField.hiddenSwanSlopes_eq_swanSlopes_sub` (LMFDB `lf.visible_slopes`): the
  hidden slopes are the slopes of the Galois closure with the visible slopes removed.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  appendix.
* J. W. Jones and D. P. Roberts, *A database of local fields*, J. Symbolic Comput. 41 (2006).
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

lemma galoisClosure_eq_of_normal {F : Type*} [Field F]
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L] : Algebra.galoisClosure F L = L :=
  (galoisClosure_le_iff.mpr le_rfl).antisymm (le_galoisClosure L)

section Subgroup

variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsGalois K M] (H : Subgroup (M ≃ₐ[K] M))

/-- The **hidden Swan slopes** (LMFDB `lf.hidden_slopes`) of the fixed field `L = M^H` of a subgroup
`H` of the Galois group `G` of a finite Galois extension `M / K` of nonarchimedean local fields of
residue characteristic `p`, computed in `M`: the `φ_{M/K}(i)` for the integers `i ≥ 1`, each
repeated `log_p [H_i : H_{i + 1}]` times, where `H_i = H ∩ G_i` are the lower ramification groups of
`M / L`. They are the Swan slopes of `M / K` that are not Swan slopes of `L / K`
(`IsNonarchimedeanLocalField.swanSlopesOfSubgroup_add_hiddenSwanSlopesOfSubgroup`). -/
noncomputable def hiddenSwanSlopesOfSubgroup : Multiset ℝ :=
  ∑ i ∈ range (largestLowerJump K M).toNat, Multiset.replicate
    (padicValNat (ringChar 𝓀[K])
      ((H ⊓ lowerRamificationGroup K M (i + 2)).relIndex
        (H ⊓ lowerRamificationGroup K M (i + 1))))
    (herbrand K M ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩)

/-- **The Swan slopes of a Galois extension from those of a subextension**: for a subgroup `H` of
the Galois group `G` of a finite Galois extension `M / K` of nonarchimedean local fields, the Swan
slopes of `M / K` are the Swan slopes of `M^H / K` together with the `φ_{M/K}(i)`, `i ≥ 1`, each
repeated `log_p [H ∩ G_i : H ∩ G_{i + 1}]` times. -/
lemma swanSlopesOfSubgroup_add_hiddenSwanSlopesOfSubgroup :
    swanSlopesOfSubgroup K M H + hiddenSwanSlopesOfSubgroup K M H = swanSlopesOfIsGalois K M := by
  rw [← swanSlopesOfSubgroup_bot, swanSlopesOfSubgroup, hiddenSwanSlopesOfSubgroup,
    swanSlopesOfSubgroup, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have h : (H ⊓ lowerRamificationGroup K M (i + 2 : ℕ)).relIndex
      (H ⊓ lowerRamificationGroup K M (i + 1 : ℕ)) =
        (⊥ : Subgroup (M ≃ₐ[K] M)).relIndex (H ⊓ lowerRamificationGroup K M (i + 1 : ℕ)) /
          (⊥ : Subgroup (M ≃ₐ[K] M)).relIndex (H ⊓ lowerRamificationGroup K M (i + 2 : ℕ)) := by
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
      ← (H ⊓ lowerRamificationGroup K M (i + 2 : ℕ)).relIndex_mul_card
        (H ⊓ lowerRamificationGroup K M (i + 1 : ℕ)),
      inf_of_le_left (inf_le_inf_left H (lowerRamificationGroup_antitone K M (by omega))),
      Nat.mul_div_cancel _ Nat.card_pos]
  have key : padicValNat (ringChar 𝓀[K]) (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
      H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) +
        padicValNat (ringChar 𝓀[K]) ((H ⊓ lowerRamificationGroup K M (i + 2 : ℕ)).relIndex
          (H ⊓ lowerRamificationGroup K M (i + 1 : ℕ))) = padicValNat (ringChar 𝓀[K])
      ((⊥ : Subgroup (M ≃ₐ[K] M)).relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
        (⊥ : Subgroup (M ≃ₐ[K] M)).relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) := by
    rw [h]
    exact (padicValNat_relIndex_div_eq_add bot_le i).symm
  rw [← Multiset.replicate_add]
  exact congrArg (Multiset.replicate · _) key

end Subgroup

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (AlgebraicClosure K)) {q q' : ℝ × ℝ}

/-- The **Galois Swan slopes** `S^Gal` (LMFDB `lf.hidden_slopes`) of an extension `L / K` of
nonarchimedean local fields inside `K̄`: the multiset of the wild Swan slopes (LMFDB `lf.slopes`) of
`L^Gal / K`, for the Galois closure `L^Gal` of `L / K` in `K̄`. For `L / K` finite separable they
are the positive upper ramification breaks of the group of `L^Gal / K`, with multiplicities
(`IsNonarchimedeanLocalField.galoisSwanSlopes_eq_swanSlopes`). -/
noncomputable def galoisSwanSlopes : Multiset ℝ :=
  hullWildSwanSlopes (Algebra.galoisClosure K L)

/-- The **hidden Swan slopes** `H` (LMFDB `lf.hidden_slopes`, `lf.visible_slopes`) of an extension
`L / K` of nonarchimedean local fields inside `K̄`: the multiset obtained by subtracting the
multiset `S` of the wild Swan slopes of `L / K`, its visible Swan slopes, from the multiset `S^Gal`
of its Galois Swan slopes. -/
noncomputable def hiddenSwanSlopes : Multiset ℝ :=
  galoisSwanSlopes L - hullWildSwanSlopes L

/-- The **Galois Artin slopes** (LMFDB `lf.hidden_slopes`) of an extension `L / K` of
nonarchimedean local fields inside `K̄`: the multiset of the wild Artin slopes (LMFDB `lf.slopes`)
of `L^Gal / K`, for the Galois closure `L^Gal` of `L / K` in `K̄`. For `L / K` finite separable
they are the wild Artin slopes of the group of `L^Gal / K`
(`IsNonarchimedeanLocalField.galoisArtinSlopes_eq_wildArtinSlopes`). -/
noncomputable def galoisArtinSlopes : Multiset ℝ :=
  hullWildArtinSlopes (Algebra.galoisClosure K L)

/-- The **hidden Artin slopes** (LMFDB `lf.hidden_slopes`, `lf.visible_slopes`) of an extension
`L / K` of nonarchimedean local fields inside `K̄`: the multiset obtained by subtracting the
multiset of the wild Artin slopes of `L / K`, its visible Artin slopes, from the multiset of its
Galois Artin slopes. -/
noncomputable def hiddenArtinSlopes : Multiset ℝ :=
  galoisArtinSlopes L - hullWildArtinSlopes L

/-- **The Galois Artin slopes are the Galois Swan slopes plus `1`** (LMFDB `lf.hidden_slopes`):
adding `1` to each Galois Swan slope of an extension `L / K` inside `K̄` gives its Galois Artin
slopes. -/
lemma map_add_one_galoisSwanSlopes : (galoisSwanSlopes L).map (· + 1) = galoisArtinSlopes L :=
  map_add_one_hullWildSwanSlopes _

variable [Normal K L] in
/-- **A normal extension has no hidden slope**: for a normal extension `L / K` inside `K̄`, which is
its own Galois closure, the multiset of hidden Swan slopes is empty. -/
lemma hiddenSwanSlopes_of_normal : hiddenSwanSlopes L = 0 := by
  rw [hiddenSwanSlopes, galoisSwanSlopes, galoisClosure_eq_of_normal L]
  exact tsub_self _

variable [FiniteDimensional K L] in
/-- **The residue degree divides the Galois unramified degree** (LMFDB `lf.unramified_degree`): for
a finite extension `L / K` inside `K̄`, the residue degree of `L / K` divides that of its Galois
closure. -/
lemma inertiaDegree_dvd_galoisUnramifiedDegree : inertiaDegree K L ∣ galoisUnramifiedDegree K L :=
  inertiaDegree_dvd_of_le (le_galoisClosure L)

variable [FiniteDimensional K L] in
/-- **The tame degree divides the Galois tame degree** (LMFDB `lf.tame_degree`): for a finite
extension `L / K` inside `K̄`, the tame degree of `L / K` divides that of its Galois closure. -/
lemma tameDegree_dvd_galoisTameDegree : tameDegree K L ∣ galoisTameDegree K L :=
  tameDegree_dvd_of_le (le_galoisClosure L)

variable [FiniteDimensional K L] [IsGalois K L] in
/-- **The visible Artin slopes of a Galois extension are its wild Artin slopes** (LMFDB
`lf.visible_slopes`): for a finite Galois extension `L / K` of nonarchimedean local fields inside
`K̄`, the wild Artin slopes read off the lower convex hull of the points `(n_E, c_E)` of the
subextensions are the wild Artin slopes of the ramification filtration of `Gal(L / K)` (LMFDB
`lf.wild_slopes`). -/
lemma hullWildArtinSlopes_eq_wildArtinSlopesOfIsGalois :
    hullWildArtinSlopes L = wildArtinSlopesOfIsGalois K L :=
  (hullWildArtinSlopes_eq_visibleArtinSlopes L).trans
    (visibleArtinSlopes_eq_wildArtinSlopesOfIsGalois L)

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **The Galois Swan slopes are the Swan slopes of the Galois closure** (LMFDB `lf.hidden_slopes`,
`lf.slope_content`): the Galois Swan slopes of a finite separable extension `L / K` inside `K̄`,
read off the convex hull of the points of the subextensions of `L^Gal / K`, are the positive upper
ramification breaks of `Gal(L^Gal / K)`, with multiplicities
(`IsNonarchimedeanLocalField.swanSlopes`). -/
lemma galoisSwanSlopes_eq_swanSlopes : galoisSwanSlopes L = swanSlopes K L :=
  hullWildSwanSlopes_eq_swanSlopesOfIsGalois _

/-- **The Galois Artin slopes are the wild Artin slopes of the Galois closure** (LMFDB
`lf.hidden_slopes`, `lf.slope_content`): the Galois Artin slopes of a finite separable extension
`L / K` inside `K̄`, read off the convex hull of the points of the subextensions of `L^Gal / K`,
are the wild Artin slopes of `Gal(L^Gal / K)` (`IsNonarchimedeanLocalField.wildArtinSlopes`). -/
lemma galoisArtinSlopes_eq_wildArtinSlopes : galoisArtinSlopes L = wildArtinSlopes K L :=
  hullWildArtinSlopes_eq_wildArtinSlopesOfIsGalois _

/-- **The Swan slopes are Galois Swan slopes** (LMFDB `lf.hidden_slopes`): the multiset `S` of the
wild Swan slopes of a finite separable extension `L / K` inside `K̄` is a sub-multiset of the
multiset `S^Gal` of its Galois Swan slopes. -/
lemma hullWildSwanSlopes_le_galoisSwanSlopes : hullWildSwanSlopes L ≤ galoisSwanSlopes L :=
  hullWildSwanSlopes_le_of_le (le_galoisClosure L)

/-- **`S^Gal` is the multiset sum of `S` and `H`** (LMFDB `lf.hidden_slopes`): the Galois Swan
slopes of a finite separable extension `L / K` inside `K̄` are its wild Swan slopes together with
its hidden Swan slopes. -/
lemma hullWildSwanSlopes_add_hiddenSwanSlopes :
    hullWildSwanSlopes L + hiddenSwanSlopes L = galoisSwanSlopes L :=
  add_tsub_cancel_of_le (hullWildSwanSlopes_le_galoisSwanSlopes L)

/-- **The Artin slopes are Galois Artin slopes** (LMFDB `lf.hidden_slopes`): the multiset of the
wild Artin slopes of a finite separable extension `L / K` inside `K̄` is a sub-multiset of the
multiset of its Galois Artin slopes. -/
lemma hullWildArtinSlopes_le_galoisArtinSlopes : hullWildArtinSlopes L ≤ galoisArtinSlopes L :=
  hullWildArtinSlopes_le_of_le (le_galoisClosure L)

/-- **The Galois Artin slopes are the Artin slopes and the hidden Artin slopes** (LMFDB
`lf.hidden_slopes`): the Galois Artin slopes of a finite separable extension `L / K` inside `K̄`
are its wild Artin slopes together with its hidden Artin slopes. -/
lemma hullWildArtinSlopes_add_hiddenArtinSlopes :
    hullWildArtinSlopes L + hiddenArtinSlopes L = galoisArtinSlopes L :=
  add_tsub_cancel_of_le (hullWildArtinSlopes_le_galoisArtinSlopes L)

/-- **The hidden Artin slopes are the hidden Swan slopes plus `1`** (LMFDB `lf.hidden_slopes`):
adding `1` to each hidden Swan slope of a finite separable extension `L / K` inside `K̄` gives its
hidden Artin slopes. -/
lemma map_add_one_hiddenSwanSlopes : (hiddenSwanSlopes L).map (· + 1) = hiddenArtinSlopes L := by
  rw [hiddenArtinSlopes, hiddenSwanSlopes, ← map_add_one_galoisSwanSlopes,
    ← map_add_one_hullWildSwanSlopes L]
  exact (map_tsub_of_le (Multiset.mapAddMonoidHom (· + 1)) _ _
    (hullWildSwanSlopes_le_galoisSwanSlopes L)).symm

/-- **The hidden Swan slopes from the ramification groups** (LMFDB `lf.hidden_slopes`): the hidden
Swan slopes of a finite separable extension `L / K` inside `K̄`, with Galois closure `M`, are the
`φ_{M/K}(i)`, `i ≥ 1`, each repeated `log_p [H_i : H_{i + 1}]` times, where `H_i` are the lower
ramification groups of `M / L`. -/
lemma hiddenSwanSlopes_eq_hiddenSwanSlopesOfSubgroup : hiddenSwanSlopes L =
    hiddenSwanSlopesOfSubgroup K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) := by
  rw [hiddenSwanSlopes, galoisSwanSlopes, hullWildSwanSlopes_eq_swanSlopesOfIsGalois,
    hullWildSwanSlopes_eq_visibleSwanSlopes, visibleSwanSlopes_eq_swanSlopesOfSubgroup,
    ← swanSlopesOfSubgroup_add_hiddenSwanSlopesOfSubgroup]
  exact add_tsub_cancel_left _ _

/-- **All the Swan slopes are Swan slopes of the Galois closure** (LMFDB `lf.hidden_slopes`): for a
finite separable extension `L / K` inside `K̄`, the multiset of all the Swan slopes of `L / K`, the
slopes `-1` and `0` of the segments that are not wild included, is a sub-multiset of that of
`L^Gal / K`. -/
lemma hullSwanSlopeMultiset_le_galoisClosure :
    hullSwanSlopeMultiset L ≤ hullSwanSlopeMultiset (Algebra.galoisClosure K L) :=
  hullSwanSlopeMultiset_le_of_le (le_galoisClosure L)

/-- **`S^Gal` is the multiset sum of `S` and `H` when all the Swan slopes are counted** (LMFDB
`lf.hidden_slopes`): for a finite separable extension `L / K` inside `K̄`, the multiset of all the
Swan slopes of `L^Gal / K` is the sum of that of `L / K` and of their difference. So the sentence
of LMFDB `lf.hidden_slopes` also holds when its Swan slopes are all the Swan slopes of LMFDB
`lf.slopes`. -/
lemma hullSwanSlopeMultiset_add_galoisClosure_sub : hullSwanSlopeMultiset L +
    (hullSwanSlopeMultiset (Algebra.galoisClosure K L) - hullSwanSlopeMultiset L) =
      hullSwanSlopeMultiset (Algebra.galoisClosure K L) :=
  add_tsub_cancel_of_le (hullSwanSlopeMultiset_le_galoisClosure L)

/-- **The hidden slopes when all the Swan slopes are counted** (LMFDB `lf.hidden_slopes`): for a
finite separable extension `L / K` inside `K̄`, subtracting the multiset of all the Swan slopes of
`L / K` from that of `L^Gal / K` gives the hidden Swan slopes of `L / K` together with `-1` if
`L / K` has residue degree `1` and `L^Gal / K` does not, and with `0` if `L / K` has tame degree
`1` and `L^Gal / K` does not. The LMFDB's hidden slopes are the wild ones,
`IsNonarchimedeanLocalField.hiddenSwanSlopes`. -/
lemma hullSwanSlopeMultiset_galoisClosure_sub : hullSwanSlopeMultiset (Algebra.galoisClosure K L) -
    hullSwanSlopeMultiset L =
      (if inertiaDegree K L = 1 ∧ 1 < galoisUnramifiedDegree K L then {-1} else 0) +
        (if tameDegree K L = 1 ∧ 1 < galoisTameDegree K L then {0} else 0) + hiddenSwanSlopes L :=
  hullSwanSlopeMultiset_sub_of_le (le_galoisClosure L)

/-- **The hidden slopes among all the slopes** (LMFDB `lf.hidden_slopes`): for a finite separable
extension `L / K` inside `K̄`, subtracting the multiset of all the Artin slopes of `L / K` from that
of `L^Gal / K` gives the corresponding difference of the multisets of all the Swan slopes, plus
`1`. -/
lemma map_add_one_hullSwanSlopeMultiset_sub :
    (hullSwanSlopeMultiset (Algebra.galoisClosure K L) - hullSwanSlopeMultiset L).map (· + 1) =
      hullArtinSlopeMultiset (Algebra.galoisClosure K L) - hullArtinSlopeMultiset L := by
  rw [← map_add_one_hullSwanSlopeMultiset, ← map_add_one_hullSwanSlopeMultiset L]
  exact (map_tsub_of_le (Multiset.mapAddMonoidHom (· + 1)) _ _
    (hullSwanSlopeMultiset_le_galoisClosure L)).symm

/-- **A wild slope is listed as often as its multiplicity** (LMFDB `lf.visible_slopes`,
`lf.slopes`): an Artin slope `s > 1` of a finite separable extension `L / K` inside `K̄` occurs `k`
times in the list of its visible Artin slopes, where the segment of slope `s` runs from `(n₁, c₁)`
to `(n₂, c₂)` with `n₂ / n₁ = p ^ k` (`IsNonarchimedeanLocalField.div_eq_pow_slopeMultiplicity`). -/
lemma count_hullWildArtinSlopes {s : ℝ} (hs : s ∈ hullArtinSlopes L) (h1 : 1 < s) :
    (hullWildArtinSlopes L).count s = slopeMultiplicity (ringChar 𝓀[K]) (slopesPolygon L) s := by
  rcases mem_hullArtinSlopes_iff.mp hs with ⟨t, ⟨ht, hlt⟩, rfl⟩
  rw [hullWildArtinSlopes, slopesPolygon, subextensionPoints_eq,
    (isLowerHullVertices_subgroupSlopePoints _).wildSegmentSlopes_lowerConvexHull
      (strictMonoOn_subgroupSlope _ _),
    (isLowerHullVertices_subgroupSlopePoints _).slopeMultiplicity_lowerConvexHull
      (strictMonoOn_subgroupSlope _ _) ht hlt, Multiset.count_sum']
  refine (sum_eq_single_of_mem t (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ht), hlt, h1⟩)
    fun t' _ hne ↦ Multiset.count_eq_zero_of_notMem fun h ↦ hne ?_).trans
      (Multiset.count_replicate_self _ _)
  exact subgroupSlope_strictMono.injective <|
    Rat.cast_injective (Multiset.eq_of_mem_replicate h).symm

private lemma slope_mem_of_mem_polygonEdgesWithSlope {P : Set (ℝ × ℝ)} {T : Set ℝ} (hq : q.1 < q'.1)
    (hσ : segment ℝ q q' ∈ polygonEdgesWithSlope P T) : (q'.2 - q.2) / (q'.1 - q.1) ∈ T := by
  rcases hσ with ⟨-, r, r', hr, hrr, hT⟩
  rcases hrr ▸ left_mem_segment ℝ q q' with ⟨a, b, -, -, hab, e⟩
  rcases hrr ▸ right_mem_segment ℝ q q' with ⟨c, d, -, -, hcd, e'⟩
  have h : (r'.2 - r.2) / (r'.1 - r.1) = (q'.2 - q.2) / (q'.1 - q.1) := by
    rw [div_eq_div_iff (sub_pos.mpr hr).ne' (sub_pos.mpr hq).ne', ← e, ← e']
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd]
    linear_combination (r.1 * r'.2 - r.2 * r'.1) * (hcd - hab)
  exact h ▸ hT

/-- **The slope of a wild segment is listed as often as its multiplicity** (LMFDB
`lf.visible_slopes`): if a segment of slope greater than `1` of the slope polygon of a finite
separable extension `L / K` inside `K̄` runs from `(n₁, c₁)` to `(n₂, c₂)`, then its slope occurs
`k` times in the list of the visible Artin slopes of `L / K`, for the `k` with `n₂ / n₁ = p ^ k`
(`IsNonarchimedeanLocalField.div_eq_pow_slopeMultiplicity`). -/
lemma count_hullWildArtinSlopes_of_mem_polygonEdgesWithSlope (hq : q.1 < q'.1)
    (hσ : segment ℝ q q' ∈ polygonEdgesWithSlope (slopesPolygon L) (Set.Ioi 1)) :
    (hullWildArtinSlopes L).count ((q'.2 - q.2) / (q'.1 - q.1)) =
      slopeMultiplicity (ringChar 𝓀[K]) (slopesPolygon L) ((q'.2 - q.2) / (q'.1 - q.1)) := by
  have hsub : segment ℝ q q' ⊆ slopesPolygon L := hσ.1.2.1
  exact count_hullWildArtinSlopes L ⟨q, hsub (left_mem_segment ℝ q q'), q',
    hsub (right_mem_segment ℝ q q'), hq, hsub, rfl⟩ (slope_mem_of_mem_polygonEdgesWithSlope hq hσ)

/-- **A wild segment has positive multiplicity** (LMFDB `lf.visible_slopes`): if a segment of slope
greater than `1` of the slope polygon of a finite separable extension `L / K` inside `K̄` runs from
`(n₁, c₁)` to `(n₂, c₂)`, then the `k` with `n₂ / n₁ = p ^ k`
(`IsNonarchimedeanLocalField.div_eq_pow_slopeMultiplicity`), the number of times its slope is
listed, is positive. -/
lemma slopeMultiplicity_pos (hq : q.1 < q'.1)
    (hσ : segment ℝ q q' ∈ polygonEdgesWithSlope (slopesPolygon L) (Set.Ioi 1)) :
    0 < slopeMultiplicity (ringChar 𝓀[K]) (slopesPolygon L) ((q'.2 - q.2) / (q'.1 - q.1)) := by
  refine Nat.pos_of_ne_zero fun h0 ↦ ?_
  have h : q'.1 / q.1 = 1 := by
    rw [div_eq_pow_slopeMultiplicity L hq hσ, h0, pow_zero]
  have hq0 : q.1 ≠ 0 := fun h' ↦ zero_ne_one <| by rw [← h, h', div_zero]
  exact hq.ne' ((div_eq_one_iff_eq hq0).mp h)

/-- **The visible Artin slopes are wild Artin slopes of the Galois closure** (LMFDB
`lf.visible_slopes`): for a finite separable extension `L / K` of nonarchimedean local fields
inside `K̄`, the list of the visible Artin slopes of `L / K`, with multiplicities, is a sub-multiset
of the list of the wild Artin slopes of its Galois closure. -/
lemma hullWildArtinSlopes_le_wildArtinSlopes : hullWildArtinSlopes L ≤ wildArtinSlopes K L :=
  (hullWildArtinSlopes_le_galoisArtinSlopes L).trans_eq (galoisArtinSlopes_eq_wildArtinSlopes L)

/-- **The hidden Artin slopes from the Galois closure** (LMFDB `lf.visible_slopes`): the hidden
Artin slopes of a finite separable extension `L / K` inside `K̄` are obtained by removing, as
multisets, its visible Artin slopes from the wild Artin slopes of its Galois closure. -/
lemma hiddenArtinSlopes_eq_wildArtinSlopes_sub :
    hiddenArtinSlopes L = wildArtinSlopes K L - hullWildArtinSlopes L := by
  rw [hiddenArtinSlopes, galoisArtinSlopes_eq_wildArtinSlopes]

/-- **The hidden Swan slopes from the Galois closure** (LMFDB `lf.visible_slopes`): the hidden Swan
slopes of a finite separable extension `L / K` inside `K̄` are obtained by removing, as multisets,
its visible Swan slopes from the Swan slopes of its Galois closure. -/
lemma hiddenSwanSlopes_eq_swanSlopes_sub :
    hiddenSwanSlopes L = swanSlopes K L - hullWildSwanSlopes L := by
  rw [hiddenSwanSlopes, galoisSwanSlopes_eq_swanSlopes]

end IsNonarchimedeanLocalField
